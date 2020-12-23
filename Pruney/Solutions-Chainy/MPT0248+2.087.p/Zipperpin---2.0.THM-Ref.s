%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.oEFq3N9KXG

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:31:30 EST 2020

% Result     : Theorem 0.45s
% Output     : Refutation 0.45s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 381 expanded)
%              Number of leaves         :   18 ( 108 expanded)
%              Depth                    :   21
%              Number of atoms          :  671 (3899 expanded)
%              Number of equality atoms :  114 ( 699 expanded)
%              Maximal formula depth    :   13 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(t43_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( ( k1_tarski @ A )
          = ( k2_xboole_0 @ B @ C ) )
        & ~ ( ( B
              = ( k1_tarski @ A ) )
            & ( C
              = ( k1_tarski @ A ) ) )
        & ~ ( ( B = k1_xboole_0 )
            & ( C
              = ( k1_tarski @ A ) ) )
        & ~ ( ( B
              = ( k1_tarski @ A ) )
            & ( C = k1_xboole_0 ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ~ ( ( ( k1_tarski @ A )
            = ( k2_xboole_0 @ B @ C ) )
          & ~ ( ( B
                = ( k1_tarski @ A ) )
              & ( C
                = ( k1_tarski @ A ) ) )
          & ~ ( ( B = k1_xboole_0 )
              & ( C
                = ( k1_tarski @ A ) ) )
          & ~ ( ( B
                = ( k1_tarski @ A ) )
              & ( C = k1_xboole_0 ) ) ) ),
    inference('cnf.neg',[status(esa)],[t43_zfmisc_1])).

thf('0',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B_2 @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('1',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_tarski @ X8 @ X9 )
      | ( X8 != X9 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('2',plain,(
    ! [X9: $i] :
      ( r1_tarski @ X9 @ X9 ) ),
    inference(simplify,[status(thm)],['1'])).

thf(t10_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ) )).

thf('3',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( r1_tarski @ X11 @ X12 )
      | ( r1_tarski @ X11 @ ( k2_xboole_0 @ X13 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t10_xboole_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    r1_tarski @ sk_C_2 @ ( k1_tarski @ sk_A ) ),
    inference('sup+',[status(thm)],['0','4'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('6',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k2_xboole_0 @ X15 @ X14 )
        = X14 )
      | ~ ( r1_tarski @ X15 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('7',plain,
    ( ( k2_xboole_0 @ sk_C_2 @ ( k1_tarski @ sk_A ) )
    = ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('8',plain,(
    ! [X7: $i] :
      ( ( X7 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B_1 @ X7 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('9',plain,(
    ! [X16: $i,X17: $i] :
      ( r1_tarski @ X16 @ ( k2_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('10',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ( r2_hidden @ X3 @ X5 )
      | ~ ( r1_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B_1 @ X0 ) @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['8','11'])).

thf('13',plain,
    ( ( r2_hidden @ ( sk_B_1 @ sk_C_2 ) @ ( k1_tarski @ sk_A ) )
    | ( sk_C_2 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['7','12'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('14',plain,(
    ! [X18: $i,X20: $i,X21: $i] :
      ( ~ ( r2_hidden @ X21 @ X20 )
      | ( X21 = X18 )
      | ( X20
       != ( k1_tarski @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('15',plain,(
    ! [X18: $i,X21: $i] :
      ( ( X21 = X18 )
      | ~ ( r2_hidden @ X21 @ ( k1_tarski @ X18 ) ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,
    ( ( sk_C_2 = k1_xboole_0 )
    | ( ( sk_B_1 @ sk_C_2 )
      = sk_A ) ),
    inference('sup-',[status(thm)],['13','15'])).

thf('17',plain,(
    ! [X7: $i] :
      ( ( X7 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B_1 @ X7 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('18',plain,
    ( ( r2_hidden @ sk_A @ sk_C_2 )
    | ( sk_C_2 = k1_xboole_0 )
    | ( sk_C_2 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,
    ( ( sk_C_2 = k1_xboole_0 )
    | ( r2_hidden @ sk_A @ sk_C_2 ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('21',plain,(
    ! [X18: $i,X21: $i] :
      ( ( X21 = X18 )
      | ~ ( r2_hidden @ X21 @ ( k1_tarski @ X18 ) ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ( ( sk_C @ X1 @ ( k1_tarski @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ~ ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,
    ( ( sk_C_2 = k1_xboole_0 )
    | ( r1_tarski @ ( k1_tarski @ sk_A ) @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['19','25'])).

thf('27',plain,(
    r1_tarski @ sk_C_2 @ ( k1_tarski @ sk_A ) ),
    inference('sup+',[status(thm)],['0','4'])).

thf('28',plain,(
    ! [X8: $i,X10: $i] :
      ( ( X8 = X10 )
      | ~ ( r1_tarski @ X10 @ X8 )
      | ~ ( r1_tarski @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('29',plain,
    ( ~ ( r1_tarski @ ( k1_tarski @ sk_A ) @ sk_C_2 )
    | ( ( k1_tarski @ sk_A )
      = sk_C_2 ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,
    ( ( sk_B_2 != k1_xboole_0 )
    | ( sk_C_2
     != ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( sk_C_2
     != ( k1_tarski @ sk_A ) )
   <= ( sk_C_2
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['30'])).

thf('32',plain,
    ( ( sk_C_2
     != ( k1_tarski @ sk_A ) )
    | ( sk_B_2 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['30'])).

thf('33',plain,
    ( ( sk_B_2
     != ( k1_tarski @ sk_A ) )
    | ( sk_C_2
     != ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ( sk_C_2
     != ( k1_tarski @ sk_A ) )
    | ( sk_B_2
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['33'])).

thf('35',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B_2 @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B_1 @ X0 ) @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['8','11'])).

thf('37',plain,
    ( ( r2_hidden @ ( sk_B_1 @ sk_B_2 ) @ ( k1_tarski @ sk_A ) )
    | ( sk_B_2 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X18: $i,X21: $i] :
      ( ( X21 = X18 )
      | ~ ( r2_hidden @ X21 @ ( k1_tarski @ X18 ) ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('39',plain,
    ( ( sk_B_2 = k1_xboole_0 )
    | ( ( sk_B_1 @ sk_B_2 )
      = sk_A ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X7: $i] :
      ( ( X7 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B_1 @ X7 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('41',plain,
    ( ( r2_hidden @ sk_A @ sk_B_2 )
    | ( sk_B_2 = k1_xboole_0 )
    | ( sk_B_2 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('42',plain,
    ( ( sk_B_2 = k1_xboole_0 )
    | ( r2_hidden @ sk_A @ sk_B_2 ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('44',plain,
    ( ( sk_B_2 = k1_xboole_0 )
    | ( r1_tarski @ ( k1_tarski @ sk_A ) @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B_2 @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    ! [X16: $i,X17: $i] :
      ( r1_tarski @ X16 @ ( k2_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('47',plain,(
    r1_tarski @ sk_B_2 @ ( k1_tarski @ sk_A ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X8: $i,X10: $i] :
      ( ( X8 = X10 )
      | ~ ( r1_tarski @ X10 @ X8 )
      | ~ ( r1_tarski @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('49',plain,
    ( ~ ( r1_tarski @ ( k1_tarski @ sk_A ) @ sk_B_2 )
    | ( ( k1_tarski @ sk_A )
      = sk_B_2 ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,
    ( ( sk_B_2 = k1_xboole_0 )
    | ( ( k1_tarski @ sk_A )
      = sk_B_2 ) ),
    inference('sup-',[status(thm)],['44','49'])).

thf('51',plain,
    ( ( sk_B_2
     != ( k1_tarski @ sk_A ) )
    | ( sk_C_2 != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,
    ( ( sk_B_2
     != ( k1_tarski @ sk_A ) )
   <= ( sk_B_2
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['51'])).

thf('53',plain,
    ( ( ( sk_B_2 != sk_B_2 )
      | ( sk_B_2 = k1_xboole_0 ) )
   <= ( sk_B_2
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['50','52'])).

thf('54',plain,
    ( ( sk_B_2 = k1_xboole_0 )
   <= ( sk_B_2
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['53'])).

thf('55',plain,
    ( ( sk_B_2 != k1_xboole_0 )
   <= ( sk_B_2 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['30'])).

thf('56',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( sk_B_2 != k1_xboole_0 )
      & ( sk_B_2
       != ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,
    ( ( sk_B_2 = k1_xboole_0 )
    | ( sk_B_2
      = ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['56'])).

thf('58',plain,(
    sk_C_2
 != ( k1_tarski @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['32','34','57'])).

thf('59',plain,(
    sk_C_2
 != ( k1_tarski @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['31','58'])).

thf('60',plain,(
    ~ ( r1_tarski @ ( k1_tarski @ sk_A ) @ sk_C_2 ) ),
    inference('simplify_reflect-',[status(thm)],['29','59'])).

thf('61',plain,(
    sk_C_2 = k1_xboole_0 ),
    inference(clc,[status(thm)],['26','60'])).

thf('62',plain,
    ( ( sk_B_2
     != ( k1_tarski @ sk_A ) )
   <= ( sk_B_2
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['51'])).

thf('63',plain,
    ( ( sk_B_2 = k1_xboole_0 )
   <= ( sk_B_2
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['53'])).

thf('64',plain,
    ( ( k1_xboole_0
     != ( k1_tarski @ sk_A ) )
   <= ( sk_B_2
     != ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,
    ( ( sk_B_2 = k1_xboole_0 )
   <= ( sk_B_2
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['53'])).

thf('66',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B_2 @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,
    ( ( ( k1_tarski @ sk_A )
      = ( k2_xboole_0 @ k1_xboole_0 @ sk_C_2 ) )
   <= ( sk_B_2
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['65','66'])).

thf('68',plain,
    ( ( k1_xboole_0
     != ( k2_xboole_0 @ k1_xboole_0 @ sk_C_2 ) )
   <= ( sk_B_2
     != ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['64','67'])).

thf('69',plain,
    ( ( k1_xboole_0
     != ( k2_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) )
   <= ( sk_B_2
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['61','68'])).

thf('70',plain,(
    ! [X9: $i] :
      ( r1_tarski @ X9 @ X9 ) ),
    inference(simplify,[status(thm)],['1'])).

thf('71',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k2_xboole_0 @ X15 @ X14 )
        = X14 )
      | ~ ( r1_tarski @ X15 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( sk_B_2
     != ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['69','72'])).

thf('74',plain,
    ( $false
   <= ( sk_B_2
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['73'])).

thf('75',plain,(
    sk_C_2 = k1_xboole_0 ),
    inference(clc,[status(thm)],['26','60'])).

thf('76',plain,
    ( ( sk_C_2 != k1_xboole_0 )
   <= ( sk_C_2 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['51'])).

thf('77',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( sk_C_2 != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    sk_C_2 = k1_xboole_0 ),
    inference(simplify,[status(thm)],['77'])).

thf('79',plain,
    ( ( sk_B_2
     != ( k1_tarski @ sk_A ) )
    | ( sk_C_2 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['51'])).

thf('80',plain,(
    sk_B_2
 != ( k1_tarski @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['78','79'])).

thf('81',plain,(
    $false ),
    inference(simpl_trail,[status(thm)],['74','80'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.oEFq3N9KXG
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:25:53 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.45/0.65  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.45/0.65  % Solved by: fo/fo7.sh
% 0.45/0.65  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.45/0.65  % done 506 iterations in 0.197s
% 0.45/0.65  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.45/0.65  % SZS output start Refutation
% 0.45/0.65  thf(sk_B_2_type, type, sk_B_2: $i).
% 0.45/0.65  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.45/0.65  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.45/0.65  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.45/0.65  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.45/0.65  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.45/0.65  thf(sk_A_type, type, sk_A: $i).
% 0.45/0.65  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.45/0.65  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.45/0.65  thf(sk_B_1_type, type, sk_B_1: $i > $i).
% 0.45/0.65  thf(t43_zfmisc_1, conjecture,
% 0.45/0.65    (![A:$i,B:$i,C:$i]:
% 0.45/0.65     ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 0.45/0.65          ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.45/0.65          ( ~( ( ( B ) = ( k1_xboole_0 ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.45/0.65          ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 0.45/0.65  thf(zf_stmt_0, negated_conjecture,
% 0.45/0.65    (~( ![A:$i,B:$i,C:$i]:
% 0.45/0.65        ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 0.45/0.65             ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.45/0.65             ( ~( ( ( B ) = ( k1_xboole_0 ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.45/0.65             ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) )),
% 0.45/0.65    inference('cnf.neg', [status(esa)], [t43_zfmisc_1])).
% 0.45/0.65  thf('0', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_2 @ sk_C_2))),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf(d10_xboole_0, axiom,
% 0.45/0.65    (![A:$i,B:$i]:
% 0.45/0.65     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.45/0.65  thf('1', plain,
% 0.45/0.65      (![X8 : $i, X9 : $i]: ((r1_tarski @ X8 @ X9) | ((X8) != (X9)))),
% 0.45/0.65      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.45/0.65  thf('2', plain, (![X9 : $i]: (r1_tarski @ X9 @ X9)),
% 0.45/0.65      inference('simplify', [status(thm)], ['1'])).
% 0.45/0.65  thf(t10_xboole_1, axiom,
% 0.45/0.65    (![A:$i,B:$i,C:$i]:
% 0.45/0.65     ( ( r1_tarski @ A @ B ) => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ))).
% 0.45/0.65  thf('3', plain,
% 0.45/0.65      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.45/0.65         (~ (r1_tarski @ X11 @ X12)
% 0.45/0.65          | (r1_tarski @ X11 @ (k2_xboole_0 @ X13 @ X12)))),
% 0.45/0.65      inference('cnf', [status(esa)], [t10_xboole_1])).
% 0.45/0.65  thf('4', plain,
% 0.45/0.65      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 0.45/0.65      inference('sup-', [status(thm)], ['2', '3'])).
% 0.45/0.65  thf('5', plain, ((r1_tarski @ sk_C_2 @ (k1_tarski @ sk_A))),
% 0.45/0.65      inference('sup+', [status(thm)], ['0', '4'])).
% 0.45/0.65  thf(t12_xboole_1, axiom,
% 0.45/0.65    (![A:$i,B:$i]:
% 0.45/0.65     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.45/0.65  thf('6', plain,
% 0.45/0.65      (![X14 : $i, X15 : $i]:
% 0.45/0.65         (((k2_xboole_0 @ X15 @ X14) = (X14)) | ~ (r1_tarski @ X15 @ X14))),
% 0.45/0.65      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.45/0.65  thf('7', plain,
% 0.45/0.65      (((k2_xboole_0 @ sk_C_2 @ (k1_tarski @ sk_A)) = (k1_tarski @ sk_A))),
% 0.45/0.65      inference('sup-', [status(thm)], ['5', '6'])).
% 0.45/0.65  thf(t7_xboole_0, axiom,
% 0.45/0.65    (![A:$i]:
% 0.45/0.65     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.45/0.65          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.45/0.65  thf('8', plain,
% 0.45/0.65      (![X7 : $i]: (((X7) = (k1_xboole_0)) | (r2_hidden @ (sk_B_1 @ X7) @ X7))),
% 0.45/0.65      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.45/0.65  thf(t7_xboole_1, axiom,
% 0.45/0.65    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.45/0.65  thf('9', plain,
% 0.45/0.65      (![X16 : $i, X17 : $i]: (r1_tarski @ X16 @ (k2_xboole_0 @ X16 @ X17))),
% 0.45/0.65      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.45/0.65  thf(d3_tarski, axiom,
% 0.45/0.65    (![A:$i,B:$i]:
% 0.45/0.65     ( ( r1_tarski @ A @ B ) <=>
% 0.45/0.65       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.45/0.65  thf('10', plain,
% 0.45/0.65      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.45/0.65         (~ (r2_hidden @ X3 @ X4)
% 0.45/0.65          | (r2_hidden @ X3 @ X5)
% 0.45/0.65          | ~ (r1_tarski @ X4 @ X5))),
% 0.45/0.65      inference('cnf', [status(esa)], [d3_tarski])).
% 0.45/0.65  thf('11', plain,
% 0.45/0.65      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.65         ((r2_hidden @ X2 @ (k2_xboole_0 @ X1 @ X0)) | ~ (r2_hidden @ X2 @ X1))),
% 0.45/0.65      inference('sup-', [status(thm)], ['9', '10'])).
% 0.45/0.65  thf('12', plain,
% 0.45/0.65      (![X0 : $i, X1 : $i]:
% 0.45/0.65         (((X0) = (k1_xboole_0))
% 0.45/0.65          | (r2_hidden @ (sk_B_1 @ X0) @ (k2_xboole_0 @ X0 @ X1)))),
% 0.45/0.65      inference('sup-', [status(thm)], ['8', '11'])).
% 0.45/0.65  thf('13', plain,
% 0.45/0.65      (((r2_hidden @ (sk_B_1 @ sk_C_2) @ (k1_tarski @ sk_A))
% 0.45/0.65        | ((sk_C_2) = (k1_xboole_0)))),
% 0.45/0.65      inference('sup+', [status(thm)], ['7', '12'])).
% 0.45/0.65  thf(d1_tarski, axiom,
% 0.45/0.65    (![A:$i,B:$i]:
% 0.45/0.65     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.45/0.65       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.45/0.65  thf('14', plain,
% 0.45/0.65      (![X18 : $i, X20 : $i, X21 : $i]:
% 0.45/0.65         (~ (r2_hidden @ X21 @ X20)
% 0.45/0.65          | ((X21) = (X18))
% 0.45/0.65          | ((X20) != (k1_tarski @ X18)))),
% 0.45/0.65      inference('cnf', [status(esa)], [d1_tarski])).
% 0.45/0.65  thf('15', plain,
% 0.45/0.65      (![X18 : $i, X21 : $i]:
% 0.45/0.65         (((X21) = (X18)) | ~ (r2_hidden @ X21 @ (k1_tarski @ X18)))),
% 0.45/0.65      inference('simplify', [status(thm)], ['14'])).
% 0.45/0.65  thf('16', plain,
% 0.45/0.65      ((((sk_C_2) = (k1_xboole_0)) | ((sk_B_1 @ sk_C_2) = (sk_A)))),
% 0.45/0.65      inference('sup-', [status(thm)], ['13', '15'])).
% 0.45/0.65  thf('17', plain,
% 0.45/0.65      (![X7 : $i]: (((X7) = (k1_xboole_0)) | (r2_hidden @ (sk_B_1 @ X7) @ X7))),
% 0.45/0.65      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.45/0.65  thf('18', plain,
% 0.45/0.65      (((r2_hidden @ sk_A @ sk_C_2)
% 0.45/0.65        | ((sk_C_2) = (k1_xboole_0))
% 0.45/0.65        | ((sk_C_2) = (k1_xboole_0)))),
% 0.45/0.65      inference('sup+', [status(thm)], ['16', '17'])).
% 0.45/0.65  thf('19', plain,
% 0.45/0.65      ((((sk_C_2) = (k1_xboole_0)) | (r2_hidden @ sk_A @ sk_C_2))),
% 0.45/0.65      inference('simplify', [status(thm)], ['18'])).
% 0.45/0.65  thf('20', plain,
% 0.45/0.65      (![X4 : $i, X6 : $i]:
% 0.45/0.65         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 0.45/0.65      inference('cnf', [status(esa)], [d3_tarski])).
% 0.45/0.65  thf('21', plain,
% 0.45/0.65      (![X18 : $i, X21 : $i]:
% 0.45/0.65         (((X21) = (X18)) | ~ (r2_hidden @ X21 @ (k1_tarski @ X18)))),
% 0.45/0.65      inference('simplify', [status(thm)], ['14'])).
% 0.45/0.65  thf('22', plain,
% 0.45/0.65      (![X0 : $i, X1 : $i]:
% 0.45/0.65         ((r1_tarski @ (k1_tarski @ X0) @ X1)
% 0.45/0.65          | ((sk_C @ X1 @ (k1_tarski @ X0)) = (X0)))),
% 0.45/0.65      inference('sup-', [status(thm)], ['20', '21'])).
% 0.45/0.65  thf('23', plain,
% 0.45/0.65      (![X4 : $i, X6 : $i]:
% 0.45/0.65         ((r1_tarski @ X4 @ X6) | ~ (r2_hidden @ (sk_C @ X6 @ X4) @ X6))),
% 0.45/0.65      inference('cnf', [status(esa)], [d3_tarski])).
% 0.45/0.65  thf('24', plain,
% 0.45/0.65      (![X0 : $i, X1 : $i]:
% 0.45/0.65         (~ (r2_hidden @ X0 @ X1)
% 0.45/0.65          | (r1_tarski @ (k1_tarski @ X0) @ X1)
% 0.45/0.65          | (r1_tarski @ (k1_tarski @ X0) @ X1))),
% 0.45/0.65      inference('sup-', [status(thm)], ['22', '23'])).
% 0.45/0.65  thf('25', plain,
% 0.45/0.65      (![X0 : $i, X1 : $i]:
% 0.45/0.65         ((r1_tarski @ (k1_tarski @ X0) @ X1) | ~ (r2_hidden @ X0 @ X1))),
% 0.45/0.65      inference('simplify', [status(thm)], ['24'])).
% 0.45/0.65  thf('26', plain,
% 0.45/0.65      ((((sk_C_2) = (k1_xboole_0)) | (r1_tarski @ (k1_tarski @ sk_A) @ sk_C_2))),
% 0.45/0.65      inference('sup-', [status(thm)], ['19', '25'])).
% 0.45/0.65  thf('27', plain, ((r1_tarski @ sk_C_2 @ (k1_tarski @ sk_A))),
% 0.45/0.65      inference('sup+', [status(thm)], ['0', '4'])).
% 0.45/0.65  thf('28', plain,
% 0.45/0.65      (![X8 : $i, X10 : $i]:
% 0.45/0.65         (((X8) = (X10)) | ~ (r1_tarski @ X10 @ X8) | ~ (r1_tarski @ X8 @ X10))),
% 0.45/0.65      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.45/0.65  thf('29', plain,
% 0.45/0.65      ((~ (r1_tarski @ (k1_tarski @ sk_A) @ sk_C_2)
% 0.45/0.65        | ((k1_tarski @ sk_A) = (sk_C_2)))),
% 0.45/0.65      inference('sup-', [status(thm)], ['27', '28'])).
% 0.45/0.65  thf('30', plain,
% 0.45/0.65      ((((sk_B_2) != (k1_xboole_0)) | ((sk_C_2) != (k1_tarski @ sk_A)))),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('31', plain,
% 0.45/0.65      ((((sk_C_2) != (k1_tarski @ sk_A)))
% 0.45/0.65         <= (~ (((sk_C_2) = (k1_tarski @ sk_A))))),
% 0.45/0.65      inference('split', [status(esa)], ['30'])).
% 0.45/0.65  thf('32', plain,
% 0.45/0.65      (~ (((sk_C_2) = (k1_tarski @ sk_A))) | ~ (((sk_B_2) = (k1_xboole_0)))),
% 0.45/0.65      inference('split', [status(esa)], ['30'])).
% 0.45/0.65  thf('33', plain,
% 0.45/0.65      ((((sk_B_2) != (k1_tarski @ sk_A)) | ((sk_C_2) != (k1_tarski @ sk_A)))),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('34', plain,
% 0.45/0.65      (~ (((sk_C_2) = (k1_tarski @ sk_A))) | 
% 0.45/0.65       ~ (((sk_B_2) = (k1_tarski @ sk_A)))),
% 0.45/0.65      inference('split', [status(esa)], ['33'])).
% 0.45/0.65  thf('35', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_2 @ sk_C_2))),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('36', plain,
% 0.45/0.65      (![X0 : $i, X1 : $i]:
% 0.45/0.65         (((X0) = (k1_xboole_0))
% 0.45/0.65          | (r2_hidden @ (sk_B_1 @ X0) @ (k2_xboole_0 @ X0 @ X1)))),
% 0.45/0.65      inference('sup-', [status(thm)], ['8', '11'])).
% 0.45/0.65  thf('37', plain,
% 0.45/0.65      (((r2_hidden @ (sk_B_1 @ sk_B_2) @ (k1_tarski @ sk_A))
% 0.45/0.65        | ((sk_B_2) = (k1_xboole_0)))),
% 0.45/0.65      inference('sup+', [status(thm)], ['35', '36'])).
% 0.45/0.65  thf('38', plain,
% 0.45/0.65      (![X18 : $i, X21 : $i]:
% 0.45/0.65         (((X21) = (X18)) | ~ (r2_hidden @ X21 @ (k1_tarski @ X18)))),
% 0.45/0.65      inference('simplify', [status(thm)], ['14'])).
% 0.45/0.65  thf('39', plain,
% 0.45/0.65      ((((sk_B_2) = (k1_xboole_0)) | ((sk_B_1 @ sk_B_2) = (sk_A)))),
% 0.45/0.65      inference('sup-', [status(thm)], ['37', '38'])).
% 0.45/0.65  thf('40', plain,
% 0.45/0.65      (![X7 : $i]: (((X7) = (k1_xboole_0)) | (r2_hidden @ (sk_B_1 @ X7) @ X7))),
% 0.45/0.65      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.45/0.65  thf('41', plain,
% 0.45/0.65      (((r2_hidden @ sk_A @ sk_B_2)
% 0.45/0.65        | ((sk_B_2) = (k1_xboole_0))
% 0.45/0.65        | ((sk_B_2) = (k1_xboole_0)))),
% 0.45/0.65      inference('sup+', [status(thm)], ['39', '40'])).
% 0.45/0.65  thf('42', plain,
% 0.45/0.65      ((((sk_B_2) = (k1_xboole_0)) | (r2_hidden @ sk_A @ sk_B_2))),
% 0.45/0.65      inference('simplify', [status(thm)], ['41'])).
% 0.45/0.65  thf('43', plain,
% 0.45/0.65      (![X0 : $i, X1 : $i]:
% 0.45/0.65         ((r1_tarski @ (k1_tarski @ X0) @ X1) | ~ (r2_hidden @ X0 @ X1))),
% 0.45/0.65      inference('simplify', [status(thm)], ['24'])).
% 0.45/0.65  thf('44', plain,
% 0.45/0.65      ((((sk_B_2) = (k1_xboole_0)) | (r1_tarski @ (k1_tarski @ sk_A) @ sk_B_2))),
% 0.45/0.65      inference('sup-', [status(thm)], ['42', '43'])).
% 0.45/0.65  thf('45', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_2 @ sk_C_2))),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('46', plain,
% 0.45/0.65      (![X16 : $i, X17 : $i]: (r1_tarski @ X16 @ (k2_xboole_0 @ X16 @ X17))),
% 0.45/0.65      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.45/0.65  thf('47', plain, ((r1_tarski @ sk_B_2 @ (k1_tarski @ sk_A))),
% 0.45/0.65      inference('sup+', [status(thm)], ['45', '46'])).
% 0.45/0.65  thf('48', plain,
% 0.45/0.65      (![X8 : $i, X10 : $i]:
% 0.45/0.65         (((X8) = (X10)) | ~ (r1_tarski @ X10 @ X8) | ~ (r1_tarski @ X8 @ X10))),
% 0.45/0.65      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.45/0.65  thf('49', plain,
% 0.45/0.65      ((~ (r1_tarski @ (k1_tarski @ sk_A) @ sk_B_2)
% 0.45/0.65        | ((k1_tarski @ sk_A) = (sk_B_2)))),
% 0.45/0.65      inference('sup-', [status(thm)], ['47', '48'])).
% 0.45/0.65  thf('50', plain,
% 0.45/0.65      ((((sk_B_2) = (k1_xboole_0)) | ((k1_tarski @ sk_A) = (sk_B_2)))),
% 0.45/0.65      inference('sup-', [status(thm)], ['44', '49'])).
% 0.45/0.65  thf('51', plain,
% 0.45/0.65      ((((sk_B_2) != (k1_tarski @ sk_A)) | ((sk_C_2) != (k1_xboole_0)))),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('52', plain,
% 0.45/0.65      ((((sk_B_2) != (k1_tarski @ sk_A)))
% 0.45/0.65         <= (~ (((sk_B_2) = (k1_tarski @ sk_A))))),
% 0.45/0.65      inference('split', [status(esa)], ['51'])).
% 0.45/0.65  thf('53', plain,
% 0.45/0.65      (((((sk_B_2) != (sk_B_2)) | ((sk_B_2) = (k1_xboole_0))))
% 0.45/0.65         <= (~ (((sk_B_2) = (k1_tarski @ sk_A))))),
% 0.45/0.65      inference('sup-', [status(thm)], ['50', '52'])).
% 0.45/0.65  thf('54', plain,
% 0.45/0.65      ((((sk_B_2) = (k1_xboole_0))) <= (~ (((sk_B_2) = (k1_tarski @ sk_A))))),
% 0.45/0.65      inference('simplify', [status(thm)], ['53'])).
% 0.45/0.65  thf('55', plain,
% 0.45/0.65      ((((sk_B_2) != (k1_xboole_0))) <= (~ (((sk_B_2) = (k1_xboole_0))))),
% 0.45/0.65      inference('split', [status(esa)], ['30'])).
% 0.45/0.65  thf('56', plain,
% 0.45/0.65      ((((k1_xboole_0) != (k1_xboole_0)))
% 0.45/0.65         <= (~ (((sk_B_2) = (k1_xboole_0))) & 
% 0.45/0.65             ~ (((sk_B_2) = (k1_tarski @ sk_A))))),
% 0.45/0.65      inference('sup-', [status(thm)], ['54', '55'])).
% 0.45/0.65  thf('57', plain,
% 0.45/0.65      ((((sk_B_2) = (k1_xboole_0))) | (((sk_B_2) = (k1_tarski @ sk_A)))),
% 0.45/0.65      inference('simplify', [status(thm)], ['56'])).
% 0.45/0.65  thf('58', plain, (~ (((sk_C_2) = (k1_tarski @ sk_A)))),
% 0.45/0.65      inference('sat_resolution*', [status(thm)], ['32', '34', '57'])).
% 0.45/0.65  thf('59', plain, (((sk_C_2) != (k1_tarski @ sk_A))),
% 0.45/0.65      inference('simpl_trail', [status(thm)], ['31', '58'])).
% 0.45/0.65  thf('60', plain, (~ (r1_tarski @ (k1_tarski @ sk_A) @ sk_C_2)),
% 0.45/0.65      inference('simplify_reflect-', [status(thm)], ['29', '59'])).
% 0.45/0.65  thf('61', plain, (((sk_C_2) = (k1_xboole_0))),
% 0.45/0.65      inference('clc', [status(thm)], ['26', '60'])).
% 0.45/0.65  thf('62', plain,
% 0.45/0.65      ((((sk_B_2) != (k1_tarski @ sk_A)))
% 0.45/0.65         <= (~ (((sk_B_2) = (k1_tarski @ sk_A))))),
% 0.45/0.65      inference('split', [status(esa)], ['51'])).
% 0.45/0.65  thf('63', plain,
% 0.45/0.65      ((((sk_B_2) = (k1_xboole_0))) <= (~ (((sk_B_2) = (k1_tarski @ sk_A))))),
% 0.45/0.65      inference('simplify', [status(thm)], ['53'])).
% 0.45/0.65  thf('64', plain,
% 0.45/0.65      ((((k1_xboole_0) != (k1_tarski @ sk_A)))
% 0.45/0.65         <= (~ (((sk_B_2) = (k1_tarski @ sk_A))))),
% 0.45/0.65      inference('demod', [status(thm)], ['62', '63'])).
% 0.45/0.65  thf('65', plain,
% 0.45/0.65      ((((sk_B_2) = (k1_xboole_0))) <= (~ (((sk_B_2) = (k1_tarski @ sk_A))))),
% 0.45/0.65      inference('simplify', [status(thm)], ['53'])).
% 0.45/0.65  thf('66', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_2 @ sk_C_2))),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('67', plain,
% 0.45/0.65      ((((k1_tarski @ sk_A) = (k2_xboole_0 @ k1_xboole_0 @ sk_C_2)))
% 0.45/0.65         <= (~ (((sk_B_2) = (k1_tarski @ sk_A))))),
% 0.45/0.65      inference('sup+', [status(thm)], ['65', '66'])).
% 0.45/0.65  thf('68', plain,
% 0.45/0.65      ((((k1_xboole_0) != (k2_xboole_0 @ k1_xboole_0 @ sk_C_2)))
% 0.45/0.65         <= (~ (((sk_B_2) = (k1_tarski @ sk_A))))),
% 0.45/0.65      inference('demod', [status(thm)], ['64', '67'])).
% 0.45/0.65  thf('69', plain,
% 0.45/0.65      ((((k1_xboole_0) != (k2_xboole_0 @ k1_xboole_0 @ k1_xboole_0)))
% 0.45/0.65         <= (~ (((sk_B_2) = (k1_tarski @ sk_A))))),
% 0.45/0.65      inference('sup-', [status(thm)], ['61', '68'])).
% 0.45/0.65  thf('70', plain, (![X9 : $i]: (r1_tarski @ X9 @ X9)),
% 0.45/0.65      inference('simplify', [status(thm)], ['1'])).
% 0.45/0.65  thf('71', plain,
% 0.45/0.65      (![X14 : $i, X15 : $i]:
% 0.45/0.65         (((k2_xboole_0 @ X15 @ X14) = (X14)) | ~ (r1_tarski @ X15 @ X14))),
% 0.45/0.65      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.45/0.65  thf('72', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 0.45/0.65      inference('sup-', [status(thm)], ['70', '71'])).
% 0.45/0.65  thf('73', plain,
% 0.45/0.65      ((((k1_xboole_0) != (k1_xboole_0)))
% 0.45/0.65         <= (~ (((sk_B_2) = (k1_tarski @ sk_A))))),
% 0.45/0.65      inference('demod', [status(thm)], ['69', '72'])).
% 0.45/0.65  thf('74', plain, (($false) <= (~ (((sk_B_2) = (k1_tarski @ sk_A))))),
% 0.45/0.65      inference('simplify', [status(thm)], ['73'])).
% 0.45/0.65  thf('75', plain, (((sk_C_2) = (k1_xboole_0))),
% 0.45/0.65      inference('clc', [status(thm)], ['26', '60'])).
% 0.45/0.65  thf('76', plain,
% 0.45/0.65      ((((sk_C_2) != (k1_xboole_0))) <= (~ (((sk_C_2) = (k1_xboole_0))))),
% 0.45/0.65      inference('split', [status(esa)], ['51'])).
% 0.45/0.65  thf('77', plain,
% 0.45/0.65      ((((k1_xboole_0) != (k1_xboole_0))) <= (~ (((sk_C_2) = (k1_xboole_0))))),
% 0.45/0.65      inference('sup-', [status(thm)], ['75', '76'])).
% 0.45/0.65  thf('78', plain, ((((sk_C_2) = (k1_xboole_0)))),
% 0.45/0.65      inference('simplify', [status(thm)], ['77'])).
% 0.45/0.65  thf('79', plain,
% 0.45/0.65      (~ (((sk_B_2) = (k1_tarski @ sk_A))) | ~ (((sk_C_2) = (k1_xboole_0)))),
% 0.45/0.65      inference('split', [status(esa)], ['51'])).
% 0.45/0.65  thf('80', plain, (~ (((sk_B_2) = (k1_tarski @ sk_A)))),
% 0.45/0.65      inference('sat_resolution*', [status(thm)], ['78', '79'])).
% 0.45/0.65  thf('81', plain, ($false),
% 0.45/0.65      inference('simpl_trail', [status(thm)], ['74', '80'])).
% 0.45/0.65  
% 0.45/0.65  % SZS output end Refutation
% 0.45/0.65  
% 0.45/0.66  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
