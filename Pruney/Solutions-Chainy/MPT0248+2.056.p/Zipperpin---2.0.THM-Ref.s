%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.txa859dGFZ

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:31:25 EST 2020

% Result     : Theorem 3.51s
% Output     : Refutation 3.51s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 345 expanded)
%              Number of leaves         :   25 (  93 expanded)
%              Depth                    :   20
%              Number of atoms          :  655 (4237 expanded)
%              Number of equality atoms :  123 ( 970 expanded)
%              Maximal formula depth    :   13 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

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
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('1',plain,(
    ! [X20: $i,X24: $i] :
      ( ( X24
        = ( k1_tarski @ X20 ) )
      | ( ( sk_C @ X24 @ X20 )
        = X20 )
      | ( r2_hidden @ ( sk_C @ X24 @ X20 ) @ X24 ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf(d3_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            | ( r2_hidden @ D @ B ) ) ) ) )).

thf('2',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ( r2_hidden @ X2 @ X4 )
      | ( X4
       != ( k2_xboole_0 @ X5 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('3',plain,(
    ! [X2: $i,X3: $i,X5: $i] :
      ( ( r2_hidden @ X2 @ ( k2_xboole_0 @ X5 @ X3 ) )
      | ~ ( r2_hidden @ X2 @ X3 ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( sk_C @ X0 @ X1 )
        = X1 )
      | ( X0
        = ( k1_tarski @ X1 ) )
      | ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ ( k2_xboole_0 @ X2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['1','3'])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ sk_C_1 @ X0 ) @ ( k1_tarski @ sk_A ) )
      | ( sk_C_1
        = ( k1_tarski @ X0 ) )
      | ( ( sk_C @ sk_C_1 @ X0 )
        = X0 ) ) ),
    inference('sup+',[status(thm)],['0','4'])).

thf('6',plain,(
    ! [X20: $i,X22: $i,X23: $i] :
      ( ~ ( r2_hidden @ X23 @ X22 )
      | ( X23 = X20 )
      | ( X22
       != ( k1_tarski @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('7',plain,(
    ! [X20: $i,X23: $i] :
      ( ( X23 = X20 )
      | ~ ( r2_hidden @ X23 @ ( k1_tarski @ X20 ) ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( ( sk_C @ sk_C_1 @ X0 )
        = X0 )
      | ( sk_C_1
        = ( k1_tarski @ X0 ) )
      | ( ( sk_C @ sk_C_1 @ X0 )
        = sk_A ) ) ),
    inference('sup-',[status(thm)],['5','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( sk_A != X0 )
      | ( sk_C_1
        = ( k1_tarski @ X0 ) )
      | ( ( sk_C @ sk_C_1 @ X0 )
        = X0 ) ) ),
    inference(eq_fact,[status(thm)],['8'])).

thf('10',plain,
    ( ( ( sk_C @ sk_C_1 @ sk_A )
      = sk_A )
    | ( sk_C_1
      = ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,
    ( ( sk_B_1 != k1_xboole_0 )
    | ( sk_C_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ( sk_C_1
     != ( k1_tarski @ sk_A ) )
   <= ( sk_C_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['11'])).

thf('13',plain,
    ( ( sk_C_1
     != ( k1_tarski @ sk_A ) )
    | ( sk_B_1 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['11'])).

thf('14',plain,
    ( ( sk_B_1
     != ( k1_tarski @ sk_A ) )
    | ( sk_C_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ( sk_C_1
     != ( k1_tarski @ sk_A ) )
    | ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['14'])).

thf('16',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('17',plain,(
    ! [X18: $i,X19: $i] :
      ( r1_tarski @ X18 @ ( k2_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('18',plain,(
    r1_tarski @ sk_B_1 @ ( k1_tarski @ sk_A ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf(l3_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k1_tarski @ B ) )
    <=> ( ( A = k1_xboole_0 )
        | ( A
          = ( k1_tarski @ B ) ) ) ) )).

thf('19',plain,(
    ! [X53: $i,X54: $i] :
      ( ( X54
        = ( k1_tarski @ X53 ) )
      | ( X54 = k1_xboole_0 )
      | ~ ( r1_tarski @ X54 @ ( k1_tarski @ X53 ) ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('20',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( sk_B_1
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( sk_B_1
     != ( k1_tarski @ sk_A ) )
    | ( sk_C_1 != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,
    ( ( sk_B_1
     != ( k1_tarski @ sk_A ) )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['21'])).

thf('23',plain,
    ( ( ( sk_B_1 != sk_B_1 )
      | ( sk_B_1 = k1_xboole_0 ) )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['20','22'])).

thf('24',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,
    ( ( sk_B_1 != k1_xboole_0 )
   <= ( sk_B_1 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['11'])).

thf('26',plain,
    ( ( sk_B_1 != sk_B_1 )
   <= ( ( sk_B_1 != k1_xboole_0 )
      & ( sk_B_1
       != ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( sk_B_1
      = ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    sk_C_1
 != ( k1_tarski @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['13','15','27'])).

thf('29',plain,(
    sk_C_1
 != ( k1_tarski @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['12','28'])).

thf('30',plain,
    ( ( sk_C @ sk_C_1 @ sk_A )
    = sk_A ),
    inference('simplify_reflect-',[status(thm)],['10','29'])).

thf('31',plain,(
    ! [X20: $i,X24: $i] :
      ( ( X24
        = ( k1_tarski @ X20 ) )
      | ( ( sk_C @ X24 @ X20 )
       != X20 )
      | ~ ( r2_hidden @ ( sk_C @ X24 @ X20 ) @ X24 ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('32',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_C_1 )
    | ( ( sk_C @ sk_C_1 @ sk_A )
     != sk_A )
    | ( sk_C_1
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('34',plain,(
    ! [X8: $i] :
      ( ( X8 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X8 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('35',plain,(
    ! [X2: $i,X3: $i,X5: $i] :
      ( ( r2_hidden @ X2 @ ( k2_xboole_0 @ X5 @ X3 ) )
      | ~ ( r2_hidden @ X2 @ X3 ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,
    ( ( r2_hidden @ ( sk_B @ sk_C_1 ) @ ( k1_tarski @ sk_A ) )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['33','36'])).

thf('38',plain,
    ( ( sk_C_1 != k1_xboole_0 )
   <= ( sk_C_1 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['21'])).

thf('39',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('42',plain,(
    ! [X16: $i] :
      ( ( k3_xboole_0 @ X16 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('44',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ X13 )
      = ( k5_xboole_0 @ X12 @ ( k3_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('46',plain,(
    ! [X17: $i] :
      ( ( k5_xboole_0 @ X17 @ k1_xboole_0 )
      = X17 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['45','46'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('48',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r1_tarski @ X9 @ X10 )
      | ( ( k4_xboole_0 @ X9 @ X10 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_tarski @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(simplify,[status(thm)],['49'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('51',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k2_xboole_0 @ X15 @ X14 )
        = X14 )
      | ~ ( r1_tarski @ X15 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,
    ( ! [X0: $i] :
        ( ( k2_xboole_0 @ sk_B_1 @ X0 )
        = X0 )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['40','52'])).

thf('54',plain,
    ( ( ( k1_tarski @ sk_A )
      = sk_C_1 )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['39','53'])).

thf('55',plain,(
    sk_C_1
 != ( k1_tarski @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['12','28'])).

thf('56',plain,
    ( sk_B_1
    = ( k1_tarski @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['54','55'])).

thf('57',plain,
    ( ( sk_C_1 != k1_xboole_0 )
    | ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['21'])).

thf('58',plain,(
    sk_C_1 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['56','57'])).

thf('59',plain,(
    sk_C_1 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['38','58'])).

thf('60',plain,(
    r2_hidden @ ( sk_B @ sk_C_1 ) @ ( k1_tarski @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['37','59'])).

thf('61',plain,(
    ! [X20: $i,X23: $i] :
      ( ( X23 = X20 )
      | ~ ( r2_hidden @ X23 @ ( k1_tarski @ X20 ) ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('62',plain,
    ( ( sk_B @ sk_C_1 )
    = sk_A ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X8: $i] :
      ( ( X8 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X8 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('64',plain,
    ( ( r2_hidden @ sk_A @ sk_C_1 )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['62','63'])).

thf('65',plain,(
    sk_C_1 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['38','58'])).

thf('66',plain,(
    r2_hidden @ sk_A @ sk_C_1 ),
    inference('simplify_reflect-',[status(thm)],['64','65'])).

thf('67',plain,
    ( ( sk_C @ sk_C_1 @ sk_A )
    = sk_A ),
    inference('simplify_reflect-',[status(thm)],['10','29'])).

thf('68',plain,
    ( ( sk_A != sk_A )
    | ( sk_C_1
      = ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['32','66','67'])).

thf('69',plain,
    ( sk_C_1
    = ( k1_tarski @ sk_A ) ),
    inference(simplify,[status(thm)],['68'])).

thf('70',plain,(
    sk_C_1
 != ( k1_tarski @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['12','28'])).

thf('71',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['69','70'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.txa859dGFZ
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:29:17 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 3.51/3.74  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 3.51/3.74  % Solved by: fo/fo7.sh
% 3.51/3.74  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 3.51/3.74  % done 4427 iterations in 3.264s
% 3.51/3.74  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 3.51/3.74  % SZS output start Refutation
% 3.51/3.74  thf(sk_C_1_type, type, sk_C_1: $i).
% 3.51/3.74  thf(sk_B_type, type, sk_B: $i > $i).
% 3.51/3.74  thf(sk_B_1_type, type, sk_B_1: $i).
% 3.51/3.74  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 3.51/3.74  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 3.51/3.74  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 3.51/3.74  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 3.51/3.74  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 3.51/3.74  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 3.51/3.74  thf(sk_A_type, type, sk_A: $i).
% 3.51/3.74  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 3.51/3.74  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 3.51/3.74  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 3.51/3.74  thf(t43_zfmisc_1, conjecture,
% 3.51/3.74    (![A:$i,B:$i,C:$i]:
% 3.51/3.74     ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 3.51/3.74          ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 3.51/3.74          ( ~( ( ( B ) = ( k1_xboole_0 ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 3.51/3.74          ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 3.51/3.74  thf(zf_stmt_0, negated_conjecture,
% 3.51/3.74    (~( ![A:$i,B:$i,C:$i]:
% 3.51/3.74        ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 3.51/3.74             ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 3.51/3.74             ( ~( ( ( B ) = ( k1_xboole_0 ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 3.51/3.74             ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) )),
% 3.51/3.74    inference('cnf.neg', [status(esa)], [t43_zfmisc_1])).
% 3.51/3.74  thf('0', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_C_1))),
% 3.51/3.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.51/3.74  thf(d1_tarski, axiom,
% 3.51/3.74    (![A:$i,B:$i]:
% 3.51/3.74     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 3.51/3.74       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 3.51/3.74  thf('1', plain,
% 3.51/3.74      (![X20 : $i, X24 : $i]:
% 3.51/3.74         (((X24) = (k1_tarski @ X20))
% 3.51/3.74          | ((sk_C @ X24 @ X20) = (X20))
% 3.51/3.74          | (r2_hidden @ (sk_C @ X24 @ X20) @ X24))),
% 3.51/3.74      inference('cnf', [status(esa)], [d1_tarski])).
% 3.51/3.74  thf(d3_xboole_0, axiom,
% 3.51/3.74    (![A:$i,B:$i,C:$i]:
% 3.51/3.74     ( ( ( C ) = ( k2_xboole_0 @ A @ B ) ) <=>
% 3.51/3.74       ( ![D:$i]:
% 3.51/3.74         ( ( r2_hidden @ D @ C ) <=>
% 3.51/3.74           ( ( r2_hidden @ D @ A ) | ( r2_hidden @ D @ B ) ) ) ) ))).
% 3.51/3.74  thf('2', plain,
% 3.51/3.74      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 3.51/3.74         (~ (r2_hidden @ X2 @ X3)
% 3.51/3.74          | (r2_hidden @ X2 @ X4)
% 3.51/3.74          | ((X4) != (k2_xboole_0 @ X5 @ X3)))),
% 3.51/3.74      inference('cnf', [status(esa)], [d3_xboole_0])).
% 3.51/3.74  thf('3', plain,
% 3.51/3.74      (![X2 : $i, X3 : $i, X5 : $i]:
% 3.51/3.74         ((r2_hidden @ X2 @ (k2_xboole_0 @ X5 @ X3)) | ~ (r2_hidden @ X2 @ X3))),
% 3.51/3.74      inference('simplify', [status(thm)], ['2'])).
% 3.51/3.74  thf('4', plain,
% 3.51/3.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.51/3.74         (((sk_C @ X0 @ X1) = (X1))
% 3.51/3.74          | ((X0) = (k1_tarski @ X1))
% 3.51/3.74          | (r2_hidden @ (sk_C @ X0 @ X1) @ (k2_xboole_0 @ X2 @ X0)))),
% 3.51/3.74      inference('sup-', [status(thm)], ['1', '3'])).
% 3.51/3.74  thf('5', plain,
% 3.51/3.74      (![X0 : $i]:
% 3.51/3.74         ((r2_hidden @ (sk_C @ sk_C_1 @ X0) @ (k1_tarski @ sk_A))
% 3.51/3.74          | ((sk_C_1) = (k1_tarski @ X0))
% 3.51/3.74          | ((sk_C @ sk_C_1 @ X0) = (X0)))),
% 3.51/3.74      inference('sup+', [status(thm)], ['0', '4'])).
% 3.51/3.74  thf('6', plain,
% 3.51/3.74      (![X20 : $i, X22 : $i, X23 : $i]:
% 3.51/3.74         (~ (r2_hidden @ X23 @ X22)
% 3.51/3.74          | ((X23) = (X20))
% 3.51/3.74          | ((X22) != (k1_tarski @ X20)))),
% 3.51/3.74      inference('cnf', [status(esa)], [d1_tarski])).
% 3.51/3.74  thf('7', plain,
% 3.51/3.74      (![X20 : $i, X23 : $i]:
% 3.51/3.74         (((X23) = (X20)) | ~ (r2_hidden @ X23 @ (k1_tarski @ X20)))),
% 3.51/3.74      inference('simplify', [status(thm)], ['6'])).
% 3.51/3.74  thf('8', plain,
% 3.51/3.74      (![X0 : $i]:
% 3.51/3.74         (((sk_C @ sk_C_1 @ X0) = (X0))
% 3.51/3.74          | ((sk_C_1) = (k1_tarski @ X0))
% 3.51/3.74          | ((sk_C @ sk_C_1 @ X0) = (sk_A)))),
% 3.51/3.74      inference('sup-', [status(thm)], ['5', '7'])).
% 3.51/3.74  thf('9', plain,
% 3.51/3.74      (![X0 : $i]:
% 3.51/3.74         (((sk_A) != (X0))
% 3.51/3.74          | ((sk_C_1) = (k1_tarski @ X0))
% 3.51/3.74          | ((sk_C @ sk_C_1 @ X0) = (X0)))),
% 3.51/3.74      inference('eq_fact', [status(thm)], ['8'])).
% 3.51/3.74  thf('10', plain,
% 3.51/3.74      ((((sk_C @ sk_C_1 @ sk_A) = (sk_A)) | ((sk_C_1) = (k1_tarski @ sk_A)))),
% 3.51/3.74      inference('simplify', [status(thm)], ['9'])).
% 3.51/3.74  thf('11', plain,
% 3.51/3.74      ((((sk_B_1) != (k1_xboole_0)) | ((sk_C_1) != (k1_tarski @ sk_A)))),
% 3.51/3.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.51/3.74  thf('12', plain,
% 3.51/3.74      ((((sk_C_1) != (k1_tarski @ sk_A)))
% 3.51/3.74         <= (~ (((sk_C_1) = (k1_tarski @ sk_A))))),
% 3.51/3.74      inference('split', [status(esa)], ['11'])).
% 3.51/3.74  thf('13', plain,
% 3.51/3.74      (~ (((sk_C_1) = (k1_tarski @ sk_A))) | ~ (((sk_B_1) = (k1_xboole_0)))),
% 3.51/3.74      inference('split', [status(esa)], ['11'])).
% 3.51/3.74  thf('14', plain,
% 3.51/3.74      ((((sk_B_1) != (k1_tarski @ sk_A)) | ((sk_C_1) != (k1_tarski @ sk_A)))),
% 3.51/3.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.51/3.74  thf('15', plain,
% 3.51/3.74      (~ (((sk_C_1) = (k1_tarski @ sk_A))) | 
% 3.51/3.74       ~ (((sk_B_1) = (k1_tarski @ sk_A)))),
% 3.51/3.74      inference('split', [status(esa)], ['14'])).
% 3.51/3.74  thf('16', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_C_1))),
% 3.51/3.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.51/3.74  thf(t7_xboole_1, axiom,
% 3.51/3.74    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 3.51/3.74  thf('17', plain,
% 3.51/3.74      (![X18 : $i, X19 : $i]: (r1_tarski @ X18 @ (k2_xboole_0 @ X18 @ X19))),
% 3.51/3.74      inference('cnf', [status(esa)], [t7_xboole_1])).
% 3.51/3.74  thf('18', plain, ((r1_tarski @ sk_B_1 @ (k1_tarski @ sk_A))),
% 3.51/3.74      inference('sup+', [status(thm)], ['16', '17'])).
% 3.51/3.74  thf(l3_zfmisc_1, axiom,
% 3.51/3.74    (![A:$i,B:$i]:
% 3.51/3.74     ( ( r1_tarski @ A @ ( k1_tarski @ B ) ) <=>
% 3.51/3.74       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( A ) = ( k1_tarski @ B ) ) ) ))).
% 3.51/3.74  thf('19', plain,
% 3.51/3.74      (![X53 : $i, X54 : $i]:
% 3.51/3.74         (((X54) = (k1_tarski @ X53))
% 3.51/3.74          | ((X54) = (k1_xboole_0))
% 3.51/3.74          | ~ (r1_tarski @ X54 @ (k1_tarski @ X53)))),
% 3.51/3.74      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 3.51/3.74  thf('20', plain,
% 3.51/3.74      ((((sk_B_1) = (k1_xboole_0)) | ((sk_B_1) = (k1_tarski @ sk_A)))),
% 3.51/3.74      inference('sup-', [status(thm)], ['18', '19'])).
% 3.51/3.74  thf('21', plain,
% 3.51/3.74      ((((sk_B_1) != (k1_tarski @ sk_A)) | ((sk_C_1) != (k1_xboole_0)))),
% 3.51/3.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.51/3.74  thf('22', plain,
% 3.51/3.74      ((((sk_B_1) != (k1_tarski @ sk_A)))
% 3.51/3.74         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 3.51/3.74      inference('split', [status(esa)], ['21'])).
% 3.51/3.74  thf('23', plain,
% 3.51/3.74      (((((sk_B_1) != (sk_B_1)) | ((sk_B_1) = (k1_xboole_0))))
% 3.51/3.74         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 3.51/3.74      inference('sup-', [status(thm)], ['20', '22'])).
% 3.51/3.74  thf('24', plain,
% 3.51/3.74      ((((sk_B_1) = (k1_xboole_0))) <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 3.51/3.74      inference('simplify', [status(thm)], ['23'])).
% 3.51/3.74  thf('25', plain,
% 3.51/3.74      ((((sk_B_1) != (k1_xboole_0))) <= (~ (((sk_B_1) = (k1_xboole_0))))),
% 3.51/3.74      inference('split', [status(esa)], ['11'])).
% 3.51/3.74  thf('26', plain,
% 3.51/3.74      ((((sk_B_1) != (sk_B_1)))
% 3.51/3.74         <= (~ (((sk_B_1) = (k1_xboole_0))) & 
% 3.51/3.74             ~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 3.51/3.74      inference('sup-', [status(thm)], ['24', '25'])).
% 3.51/3.74  thf('27', plain,
% 3.51/3.74      ((((sk_B_1) = (k1_xboole_0))) | (((sk_B_1) = (k1_tarski @ sk_A)))),
% 3.51/3.74      inference('simplify', [status(thm)], ['26'])).
% 3.51/3.74  thf('28', plain, (~ (((sk_C_1) = (k1_tarski @ sk_A)))),
% 3.51/3.74      inference('sat_resolution*', [status(thm)], ['13', '15', '27'])).
% 3.51/3.74  thf('29', plain, (((sk_C_1) != (k1_tarski @ sk_A))),
% 3.51/3.74      inference('simpl_trail', [status(thm)], ['12', '28'])).
% 3.51/3.74  thf('30', plain, (((sk_C @ sk_C_1 @ sk_A) = (sk_A))),
% 3.51/3.74      inference('simplify_reflect-', [status(thm)], ['10', '29'])).
% 3.51/3.74  thf('31', plain,
% 3.51/3.74      (![X20 : $i, X24 : $i]:
% 3.51/3.74         (((X24) = (k1_tarski @ X20))
% 3.51/3.74          | ((sk_C @ X24 @ X20) != (X20))
% 3.51/3.74          | ~ (r2_hidden @ (sk_C @ X24 @ X20) @ X24))),
% 3.51/3.74      inference('cnf', [status(esa)], [d1_tarski])).
% 3.51/3.74  thf('32', plain,
% 3.51/3.74      ((~ (r2_hidden @ sk_A @ sk_C_1)
% 3.51/3.74        | ((sk_C @ sk_C_1 @ sk_A) != (sk_A))
% 3.51/3.74        | ((sk_C_1) = (k1_tarski @ sk_A)))),
% 3.51/3.74      inference('sup-', [status(thm)], ['30', '31'])).
% 3.51/3.74  thf('33', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_C_1))),
% 3.51/3.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.51/3.74  thf(t7_xboole_0, axiom,
% 3.51/3.74    (![A:$i]:
% 3.51/3.74     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 3.51/3.74          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 3.51/3.74  thf('34', plain,
% 3.51/3.74      (![X8 : $i]: (((X8) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X8) @ X8))),
% 3.51/3.74      inference('cnf', [status(esa)], [t7_xboole_0])).
% 3.51/3.74  thf('35', plain,
% 3.51/3.74      (![X2 : $i, X3 : $i, X5 : $i]:
% 3.51/3.74         ((r2_hidden @ X2 @ (k2_xboole_0 @ X5 @ X3)) | ~ (r2_hidden @ X2 @ X3))),
% 3.51/3.74      inference('simplify', [status(thm)], ['2'])).
% 3.51/3.74  thf('36', plain,
% 3.51/3.74      (![X0 : $i, X1 : $i]:
% 3.51/3.74         (((X0) = (k1_xboole_0))
% 3.51/3.74          | (r2_hidden @ (sk_B @ X0) @ (k2_xboole_0 @ X1 @ X0)))),
% 3.51/3.74      inference('sup-', [status(thm)], ['34', '35'])).
% 3.51/3.74  thf('37', plain,
% 3.51/3.74      (((r2_hidden @ (sk_B @ sk_C_1) @ (k1_tarski @ sk_A))
% 3.51/3.74        | ((sk_C_1) = (k1_xboole_0)))),
% 3.51/3.74      inference('sup+', [status(thm)], ['33', '36'])).
% 3.51/3.74  thf('38', plain,
% 3.51/3.74      ((((sk_C_1) != (k1_xboole_0))) <= (~ (((sk_C_1) = (k1_xboole_0))))),
% 3.51/3.74      inference('split', [status(esa)], ['21'])).
% 3.51/3.74  thf('39', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_C_1))),
% 3.51/3.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.51/3.74  thf('40', plain,
% 3.51/3.74      ((((sk_B_1) = (k1_xboole_0))) <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 3.51/3.74      inference('simplify', [status(thm)], ['23'])).
% 3.51/3.74  thf(commutativity_k3_xboole_0, axiom,
% 3.51/3.74    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 3.51/3.74  thf('41', plain,
% 3.51/3.74      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 3.51/3.74      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 3.51/3.74  thf(t2_boole, axiom,
% 3.51/3.74    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 3.51/3.74  thf('42', plain,
% 3.51/3.74      (![X16 : $i]: ((k3_xboole_0 @ X16 @ k1_xboole_0) = (k1_xboole_0))),
% 3.51/3.74      inference('cnf', [status(esa)], [t2_boole])).
% 3.51/3.74  thf('43', plain,
% 3.51/3.74      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 3.51/3.74      inference('sup+', [status(thm)], ['41', '42'])).
% 3.51/3.74  thf(t100_xboole_1, axiom,
% 3.51/3.74    (![A:$i,B:$i]:
% 3.51/3.74     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 3.51/3.74  thf('44', plain,
% 3.51/3.74      (![X12 : $i, X13 : $i]:
% 3.51/3.74         ((k4_xboole_0 @ X12 @ X13)
% 3.51/3.74           = (k5_xboole_0 @ X12 @ (k3_xboole_0 @ X12 @ X13)))),
% 3.51/3.74      inference('cnf', [status(esa)], [t100_xboole_1])).
% 3.51/3.74  thf('45', plain,
% 3.51/3.74      (![X0 : $i]:
% 3.51/3.74         ((k4_xboole_0 @ k1_xboole_0 @ X0)
% 3.51/3.74           = (k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0))),
% 3.51/3.74      inference('sup+', [status(thm)], ['43', '44'])).
% 3.51/3.74  thf(t5_boole, axiom,
% 3.51/3.74    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 3.51/3.74  thf('46', plain, (![X17 : $i]: ((k5_xboole_0 @ X17 @ k1_xboole_0) = (X17))),
% 3.51/3.74      inference('cnf', [status(esa)], [t5_boole])).
% 3.51/3.74  thf('47', plain,
% 3.51/3.74      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 3.51/3.74      inference('demod', [status(thm)], ['45', '46'])).
% 3.51/3.74  thf(l32_xboole_1, axiom,
% 3.51/3.74    (![A:$i,B:$i]:
% 3.51/3.74     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 3.51/3.74  thf('48', plain,
% 3.51/3.74      (![X9 : $i, X10 : $i]:
% 3.51/3.74         ((r1_tarski @ X9 @ X10) | ((k4_xboole_0 @ X9 @ X10) != (k1_xboole_0)))),
% 3.51/3.74      inference('cnf', [status(esa)], [l32_xboole_1])).
% 3.51/3.74  thf('49', plain,
% 3.51/3.74      (![X0 : $i]:
% 3.51/3.74         (((k1_xboole_0) != (k1_xboole_0)) | (r1_tarski @ k1_xboole_0 @ X0))),
% 3.51/3.74      inference('sup-', [status(thm)], ['47', '48'])).
% 3.51/3.74  thf('50', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 3.51/3.74      inference('simplify', [status(thm)], ['49'])).
% 3.51/3.74  thf(t12_xboole_1, axiom,
% 3.51/3.74    (![A:$i,B:$i]:
% 3.51/3.74     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 3.51/3.74  thf('51', plain,
% 3.51/3.74      (![X14 : $i, X15 : $i]:
% 3.51/3.74         (((k2_xboole_0 @ X15 @ X14) = (X14)) | ~ (r1_tarski @ X15 @ X14))),
% 3.51/3.74      inference('cnf', [status(esa)], [t12_xboole_1])).
% 3.51/3.74  thf('52', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 3.51/3.74      inference('sup-', [status(thm)], ['50', '51'])).
% 3.51/3.74  thf('53', plain,
% 3.51/3.74      ((![X0 : $i]: ((k2_xboole_0 @ sk_B_1 @ X0) = (X0)))
% 3.51/3.74         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 3.51/3.74      inference('sup+', [status(thm)], ['40', '52'])).
% 3.51/3.74  thf('54', plain,
% 3.51/3.74      ((((k1_tarski @ sk_A) = (sk_C_1)))
% 3.51/3.74         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 3.51/3.74      inference('sup+', [status(thm)], ['39', '53'])).
% 3.51/3.74  thf('55', plain, (((sk_C_1) != (k1_tarski @ sk_A))),
% 3.51/3.74      inference('simpl_trail', [status(thm)], ['12', '28'])).
% 3.51/3.74  thf('56', plain, ((((sk_B_1) = (k1_tarski @ sk_A)))),
% 3.51/3.74      inference('simplify_reflect-', [status(thm)], ['54', '55'])).
% 3.51/3.74  thf('57', plain,
% 3.51/3.74      (~ (((sk_C_1) = (k1_xboole_0))) | ~ (((sk_B_1) = (k1_tarski @ sk_A)))),
% 3.51/3.74      inference('split', [status(esa)], ['21'])).
% 3.51/3.74  thf('58', plain, (~ (((sk_C_1) = (k1_xboole_0)))),
% 3.51/3.74      inference('sat_resolution*', [status(thm)], ['56', '57'])).
% 3.51/3.74  thf('59', plain, (((sk_C_1) != (k1_xboole_0))),
% 3.51/3.74      inference('simpl_trail', [status(thm)], ['38', '58'])).
% 3.51/3.74  thf('60', plain, ((r2_hidden @ (sk_B @ sk_C_1) @ (k1_tarski @ sk_A))),
% 3.51/3.74      inference('simplify_reflect-', [status(thm)], ['37', '59'])).
% 3.51/3.74  thf('61', plain,
% 3.51/3.74      (![X20 : $i, X23 : $i]:
% 3.51/3.74         (((X23) = (X20)) | ~ (r2_hidden @ X23 @ (k1_tarski @ X20)))),
% 3.51/3.74      inference('simplify', [status(thm)], ['6'])).
% 3.51/3.74  thf('62', plain, (((sk_B @ sk_C_1) = (sk_A))),
% 3.51/3.74      inference('sup-', [status(thm)], ['60', '61'])).
% 3.51/3.74  thf('63', plain,
% 3.51/3.74      (![X8 : $i]: (((X8) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X8) @ X8))),
% 3.51/3.74      inference('cnf', [status(esa)], [t7_xboole_0])).
% 3.51/3.74  thf('64', plain,
% 3.51/3.74      (((r2_hidden @ sk_A @ sk_C_1) | ((sk_C_1) = (k1_xboole_0)))),
% 3.51/3.74      inference('sup+', [status(thm)], ['62', '63'])).
% 3.51/3.74  thf('65', plain, (((sk_C_1) != (k1_xboole_0))),
% 3.51/3.74      inference('simpl_trail', [status(thm)], ['38', '58'])).
% 3.51/3.74  thf('66', plain, ((r2_hidden @ sk_A @ sk_C_1)),
% 3.51/3.74      inference('simplify_reflect-', [status(thm)], ['64', '65'])).
% 3.51/3.74  thf('67', plain, (((sk_C @ sk_C_1 @ sk_A) = (sk_A))),
% 3.51/3.74      inference('simplify_reflect-', [status(thm)], ['10', '29'])).
% 3.51/3.74  thf('68', plain, ((((sk_A) != (sk_A)) | ((sk_C_1) = (k1_tarski @ sk_A)))),
% 3.51/3.74      inference('demod', [status(thm)], ['32', '66', '67'])).
% 3.51/3.74  thf('69', plain, (((sk_C_1) = (k1_tarski @ sk_A))),
% 3.51/3.74      inference('simplify', [status(thm)], ['68'])).
% 3.51/3.74  thf('70', plain, (((sk_C_1) != (k1_tarski @ sk_A))),
% 3.51/3.74      inference('simpl_trail', [status(thm)], ['12', '28'])).
% 3.51/3.74  thf('71', plain, ($false),
% 3.51/3.74      inference('simplify_reflect-', [status(thm)], ['69', '70'])).
% 3.51/3.74  
% 3.51/3.74  % SZS output end Refutation
% 3.51/3.74  
% 3.51/3.75  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
