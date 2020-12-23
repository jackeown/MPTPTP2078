%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.emfWD9H0qg

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:31:30 EST 2020

% Result     : Theorem 0.44s
% Output     : Refutation 0.44s
% Verified   : 
% Statistics : Number of formulae       :  110 ( 666 expanded)
%              Number of leaves         :   24 ( 187 expanded)
%              Depth                    :   24
%              Number of atoms          :  716 (7144 expanded)
%              Number of equality atoms :  119 (1379 expanded)
%              Maximal formula depth    :   13 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

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
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('1',plain,(
    ! [X74: $i,X75: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X74 @ X75 ) )
      = ( k2_xboole_0 @ X74 @ X75 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('2',plain,
    ( ( k1_tarski @ sk_A )
    = ( k3_tarski @ ( k2_tarski @ sk_B_1 @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('3',plain,(
    ! [X11: $i] :
      ( ( X11 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X11 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('4',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('5',plain,(
    ! [X22: $i,X23: $i] :
      ( r1_tarski @ X22 @ ( k2_xboole_0 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('6',plain,(
    r1_tarski @ sk_B_1 @ ( k1_tarski @ sk_A ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( r2_hidden @ ( sk_B @ sk_B_1 ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['3','8'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('10',plain,(
    ! [X30: $i,X32: $i,X33: $i] :
      ( ~ ( r2_hidden @ X33 @ X32 )
      | ( X33 = X30 )
      | ( X32
       != ( k1_tarski @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('11',plain,(
    ! [X30: $i,X33: $i] :
      ( ( X33 = X30 )
      | ~ ( r2_hidden @ X33 @ ( k1_tarski @ X30 ) ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( ( sk_B @ sk_B_1 )
      = sk_A ) ),
    inference('sup-',[status(thm)],['9','11'])).

thf('13',plain,(
    ! [X11: $i] :
      ( ( X11 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X11 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('14',plain,
    ( ( r2_hidden @ sk_A @ sk_B_1 )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( r2_hidden @ sk_A @ sk_B_1 ) ),
    inference(simplify,[status(thm)],['14'])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('16',plain,(
    ! [X71: $i,X73: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X71 ) @ X73 )
      | ~ ( r2_hidden @ X71 @ X73 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('17',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( r1_tarski @ ( k1_tarski @ sk_A ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    r1_tarski @ sk_B_1 @ ( k1_tarski @ sk_A ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('19',plain,(
    ! [X12: $i,X14: $i] :
      ( ( X12 = X14 )
      | ~ ( r1_tarski @ X14 @ X12 )
      | ~ ( r1_tarski @ X12 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('20',plain,
    ( ~ ( r1_tarski @ ( k1_tarski @ sk_A ) @ sk_B_1 )
    | ( ( k1_tarski @ sk_A )
      = sk_B_1 ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( ( k1_tarski @ sk_A )
      = sk_B_1 ) ),
    inference('sup-',[status(thm)],['17','20'])).

thf('22',plain,
    ( ( sk_B_1
     != ( k1_tarski @ sk_A ) )
    | ( sk_C_2 != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ( sk_B_1
     != ( k1_tarski @ sk_A ) )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['22'])).

thf('24',plain,
    ( ( ( sk_B_1 != sk_B_1 )
      | ( sk_B_1 = k1_xboole_0 ) )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['21','23'])).

thf('25',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,
    ( ( k1_tarski @ sk_A )
    = ( k3_tarski @ ( k2_tarski @ sk_B_1 @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('27',plain,
    ( ( k1_tarski @ sk_A )
    = ( k3_tarski @ ( k2_tarski @ sk_B_1 @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('28',plain,(
    ! [X11: $i] :
      ( ( X11 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X11 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(d3_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            | ( r2_hidden @ D @ B ) ) ) ) )).

thf('29',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X4 @ X5 )
      | ( r2_hidden @ X4 @ X6 )
      | ( X6
       != ( k2_xboole_0 @ X7 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('30',plain,(
    ! [X4: $i,X5: $i,X7: $i] :
      ( ( r2_hidden @ X4 @ ( k2_xboole_0 @ X7 @ X5 ) )
      | ~ ( r2_hidden @ X4 @ X5 ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,(
    ! [X74: $i,X75: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X74 @ X75 ) )
      = ( k2_xboole_0 @ X74 @ X75 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('32',plain,(
    ! [X4: $i,X5: $i,X7: $i] :
      ( ( r2_hidden @ X4 @ ( k3_tarski @ ( k2_tarski @ X7 @ X5 ) ) )
      | ~ ( r2_hidden @ X4 @ X5 ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['28','32'])).

thf('34',plain,
    ( ( r2_hidden @ ( sk_B @ sk_C_2 ) @ ( k1_tarski @ sk_A ) )
    | ( sk_C_2 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['27','33'])).

thf('35',plain,(
    ! [X30: $i,X33: $i] :
      ( ( X33 = X30 )
      | ~ ( r2_hidden @ X33 @ ( k1_tarski @ X30 ) ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('36',plain,
    ( ( sk_C_2 = k1_xboole_0 )
    | ( ( sk_B @ sk_C_2 )
      = sk_A ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X11: $i] :
      ( ( X11 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X11 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('38',plain,
    ( ( r2_hidden @ sk_A @ sk_C_2 )
    | ( sk_C_2 = k1_xboole_0 )
    | ( sk_C_2 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('39',plain,
    ( ( sk_C_2 = k1_xboole_0 )
    | ( r2_hidden @ sk_A @ sk_C_2 ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B_1 @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_B_1 ) @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X30: $i,X33: $i] :
      ( ( X33 = X30 )
      | ~ ( r2_hidden @ X33 @ ( k1_tarski @ X30 ) ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B_1 @ X0 )
      | ( ( sk_C @ X0 @ sk_B_1 )
        = sk_A ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('46',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ sk_A @ X0 )
      | ( r1_tarski @ sk_B_1 @ X0 )
      | ( r1_tarski @ sk_B_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B_1 @ X0 )
      | ~ ( r2_hidden @ sk_A @ X0 ) ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,
    ( ( sk_C_2 = k1_xboole_0 )
    | ( r1_tarski @ sk_B_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['39','47'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('49',plain,(
    ! [X17: $i,X18: $i] :
      ( ( ( k2_xboole_0 @ X18 @ X17 )
        = X17 )
      | ~ ( r1_tarski @ X18 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('50',plain,(
    ! [X74: $i,X75: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X74 @ X75 ) )
      = ( k2_xboole_0 @ X74 @ X75 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('51',plain,(
    ! [X17: $i,X18: $i] :
      ( ( ( k3_tarski @ ( k2_tarski @ X18 @ X17 ) )
        = X17 )
      | ~ ( r1_tarski @ X18 @ X17 ) ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,
    ( ( sk_C_2 = k1_xboole_0 )
    | ( ( k3_tarski @ ( k2_tarski @ sk_B_1 @ sk_C_2 ) )
      = sk_C_2 ) ),
    inference('sup-',[status(thm)],['48','51'])).

thf('53',plain,
    ( ( ( k1_tarski @ sk_A )
      = sk_C_2 )
    | ( sk_C_2 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['26','52'])).

thf('54',plain,
    ( ( sk_B_1 != k1_xboole_0 )
    | ( sk_C_2
     != ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( ( sk_C_2
     != ( k1_tarski @ sk_A ) )
   <= ( sk_C_2
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['54'])).

thf('56',plain,
    ( ( sk_C_2
     != ( k1_tarski @ sk_A ) )
    | ( sk_B_1 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['54'])).

thf('57',plain,
    ( ( sk_B_1
     != ( k1_tarski @ sk_A ) )
    | ( sk_C_2
     != ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,
    ( ( sk_C_2
     != ( k1_tarski @ sk_A ) )
    | ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['57'])).

thf('59',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('60',plain,
    ( ( sk_B_1 != k1_xboole_0 )
   <= ( sk_B_1 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['54'])).

thf('61',plain,
    ( ( sk_B_1 != sk_B_1 )
   <= ( ( sk_B_1 != k1_xboole_0 )
      & ( sk_B_1
       != ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( sk_B_1
      = ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['61'])).

thf('63',plain,(
    sk_C_2
 != ( k1_tarski @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['56','58','62'])).

thf('64',plain,(
    sk_C_2
 != ( k1_tarski @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['55','63'])).

thf('65',plain,(
    sk_C_2 = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['53','64'])).

thf('66',plain,
    ( ( sk_C_2 != k1_xboole_0 )
   <= ( sk_C_2 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['22'])).

thf('67',plain,
    ( ( sk_C_2 != sk_C_2 )
   <= ( sk_C_2 != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    sk_C_2 = k1_xboole_0 ),
    inference(simplify,[status(thm)],['67'])).

thf('69',plain,
    ( ( sk_B_1
     != ( k1_tarski @ sk_A ) )
    | ( sk_C_2 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['22'])).

thf('70',plain,(
    sk_B_1
 != ( k1_tarski @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['68','69'])).

thf('71',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['25','70'])).

thf('72',plain,(
    sk_C_2 = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['53','64'])).

thf('73',plain,(
    sk_C_2 = sk_B_1 ),
    inference('sup+',[status(thm)],['71','72'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('74',plain,(
    ! [X43: $i] :
      ( ( k2_tarski @ X43 @ X43 )
      = ( k1_tarski @ X43 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('75',plain,(
    ! [X43: $i] :
      ( ( k2_tarski @ X43 @ X43 )
      = ( k1_tarski @ X43 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(idempotence_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ A )
      = A ) )).

thf('76',plain,(
    ! [X10: $i] :
      ( ( k2_xboole_0 @ X10 @ X10 )
      = X10 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf('77',plain,(
    ! [X74: $i,X75: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X74 @ X75 ) )
      = ( k2_xboole_0 @ X74 @ X75 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('78',plain,(
    ! [X10: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X10 @ X10 ) )
      = X10 ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['75','78'])).

thf('80',plain,
    ( ( k1_tarski @ sk_A )
    = sk_B_1 ),
    inference(demod,[status(thm)],['2','73','74','79'])).

thf('81',plain,(
    sk_C_2
 != ( k1_tarski @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['55','63'])).

thf('82',plain,(
    sk_C_2 = sk_B_1 ),
    inference('sup+',[status(thm)],['71','72'])).

thf('83',plain,(
    sk_B_1
 != ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['81','82'])).

thf('84',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['80','83'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.emfWD9H0qg
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:46:31 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.44/0.65  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.44/0.65  % Solved by: fo/fo7.sh
% 0.44/0.65  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.44/0.65  % done 654 iterations in 0.184s
% 0.44/0.65  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.44/0.65  % SZS output start Refutation
% 0.44/0.65  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.44/0.65  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.44/0.65  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.44/0.65  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.44/0.65  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.44/0.65  thf(sk_A_type, type, sk_A: $i).
% 0.44/0.65  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.44/0.65  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.44/0.65  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.44/0.65  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.44/0.65  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.44/0.65  thf(sk_B_type, type, sk_B: $i > $i).
% 0.44/0.65  thf(t43_zfmisc_1, conjecture,
% 0.44/0.65    (![A:$i,B:$i,C:$i]:
% 0.44/0.65     ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 0.44/0.65          ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.44/0.65          ( ~( ( ( B ) = ( k1_xboole_0 ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.44/0.65          ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 0.44/0.65  thf(zf_stmt_0, negated_conjecture,
% 0.44/0.65    (~( ![A:$i,B:$i,C:$i]:
% 0.44/0.65        ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 0.44/0.65             ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.44/0.65             ( ~( ( ( B ) = ( k1_xboole_0 ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.44/0.65             ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) )),
% 0.44/0.65    inference('cnf.neg', [status(esa)], [t43_zfmisc_1])).
% 0.44/0.65  thf('0', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_C_2))),
% 0.44/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.65  thf(l51_zfmisc_1, axiom,
% 0.44/0.65    (![A:$i,B:$i]:
% 0.44/0.65     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.44/0.65  thf('1', plain,
% 0.44/0.65      (![X74 : $i, X75 : $i]:
% 0.44/0.65         ((k3_tarski @ (k2_tarski @ X74 @ X75)) = (k2_xboole_0 @ X74 @ X75))),
% 0.44/0.65      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.44/0.65  thf('2', plain,
% 0.44/0.65      (((k1_tarski @ sk_A) = (k3_tarski @ (k2_tarski @ sk_B_1 @ sk_C_2)))),
% 0.44/0.65      inference('demod', [status(thm)], ['0', '1'])).
% 0.44/0.65  thf(t7_xboole_0, axiom,
% 0.44/0.65    (![A:$i]:
% 0.44/0.65     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.44/0.65          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.44/0.65  thf('3', plain,
% 0.44/0.65      (![X11 : $i]:
% 0.44/0.65         (((X11) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X11) @ X11))),
% 0.44/0.65      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.44/0.65  thf('4', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_C_2))),
% 0.44/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.65  thf(t7_xboole_1, axiom,
% 0.44/0.65    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.44/0.65  thf('5', plain,
% 0.44/0.65      (![X22 : $i, X23 : $i]: (r1_tarski @ X22 @ (k2_xboole_0 @ X22 @ X23))),
% 0.44/0.65      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.44/0.65  thf('6', plain, ((r1_tarski @ sk_B_1 @ (k1_tarski @ sk_A))),
% 0.44/0.65      inference('sup+', [status(thm)], ['4', '5'])).
% 0.44/0.65  thf(d3_tarski, axiom,
% 0.44/0.65    (![A:$i,B:$i]:
% 0.44/0.65     ( ( r1_tarski @ A @ B ) <=>
% 0.44/0.65       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.44/0.65  thf('7', plain,
% 0.44/0.65      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.44/0.65         (~ (r2_hidden @ X0 @ X1)
% 0.44/0.65          | (r2_hidden @ X0 @ X2)
% 0.44/0.65          | ~ (r1_tarski @ X1 @ X2))),
% 0.44/0.65      inference('cnf', [status(esa)], [d3_tarski])).
% 0.44/0.65  thf('8', plain,
% 0.44/0.65      (![X0 : $i]:
% 0.44/0.65         ((r2_hidden @ X0 @ (k1_tarski @ sk_A)) | ~ (r2_hidden @ X0 @ sk_B_1))),
% 0.44/0.65      inference('sup-', [status(thm)], ['6', '7'])).
% 0.44/0.65  thf('9', plain,
% 0.44/0.65      ((((sk_B_1) = (k1_xboole_0))
% 0.44/0.65        | (r2_hidden @ (sk_B @ sk_B_1) @ (k1_tarski @ sk_A)))),
% 0.44/0.65      inference('sup-', [status(thm)], ['3', '8'])).
% 0.44/0.65  thf(d1_tarski, axiom,
% 0.44/0.65    (![A:$i,B:$i]:
% 0.44/0.65     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.44/0.65       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.44/0.65  thf('10', plain,
% 0.44/0.65      (![X30 : $i, X32 : $i, X33 : $i]:
% 0.44/0.65         (~ (r2_hidden @ X33 @ X32)
% 0.44/0.65          | ((X33) = (X30))
% 0.44/0.65          | ((X32) != (k1_tarski @ X30)))),
% 0.44/0.65      inference('cnf', [status(esa)], [d1_tarski])).
% 0.44/0.65  thf('11', plain,
% 0.44/0.65      (![X30 : $i, X33 : $i]:
% 0.44/0.65         (((X33) = (X30)) | ~ (r2_hidden @ X33 @ (k1_tarski @ X30)))),
% 0.44/0.65      inference('simplify', [status(thm)], ['10'])).
% 0.44/0.65  thf('12', plain, ((((sk_B_1) = (k1_xboole_0)) | ((sk_B @ sk_B_1) = (sk_A)))),
% 0.44/0.65      inference('sup-', [status(thm)], ['9', '11'])).
% 0.44/0.65  thf('13', plain,
% 0.44/0.65      (![X11 : $i]:
% 0.44/0.65         (((X11) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X11) @ X11))),
% 0.44/0.65      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.44/0.65  thf('14', plain,
% 0.44/0.65      (((r2_hidden @ sk_A @ sk_B_1)
% 0.44/0.65        | ((sk_B_1) = (k1_xboole_0))
% 0.44/0.65        | ((sk_B_1) = (k1_xboole_0)))),
% 0.44/0.65      inference('sup+', [status(thm)], ['12', '13'])).
% 0.44/0.65  thf('15', plain,
% 0.44/0.65      ((((sk_B_1) = (k1_xboole_0)) | (r2_hidden @ sk_A @ sk_B_1))),
% 0.44/0.65      inference('simplify', [status(thm)], ['14'])).
% 0.44/0.65  thf(l1_zfmisc_1, axiom,
% 0.44/0.65    (![A:$i,B:$i]:
% 0.44/0.65     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.44/0.65  thf('16', plain,
% 0.44/0.65      (![X71 : $i, X73 : $i]:
% 0.44/0.65         ((r1_tarski @ (k1_tarski @ X71) @ X73) | ~ (r2_hidden @ X71 @ X73))),
% 0.44/0.65      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.44/0.65  thf('17', plain,
% 0.44/0.65      ((((sk_B_1) = (k1_xboole_0)) | (r1_tarski @ (k1_tarski @ sk_A) @ sk_B_1))),
% 0.44/0.65      inference('sup-', [status(thm)], ['15', '16'])).
% 0.44/0.65  thf('18', plain, ((r1_tarski @ sk_B_1 @ (k1_tarski @ sk_A))),
% 0.44/0.65      inference('sup+', [status(thm)], ['4', '5'])).
% 0.44/0.65  thf(d10_xboole_0, axiom,
% 0.44/0.65    (![A:$i,B:$i]:
% 0.44/0.65     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.44/0.65  thf('19', plain,
% 0.44/0.65      (![X12 : $i, X14 : $i]:
% 0.44/0.65         (((X12) = (X14))
% 0.44/0.65          | ~ (r1_tarski @ X14 @ X12)
% 0.44/0.65          | ~ (r1_tarski @ X12 @ X14))),
% 0.44/0.65      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.44/0.65  thf('20', plain,
% 0.44/0.65      ((~ (r1_tarski @ (k1_tarski @ sk_A) @ sk_B_1)
% 0.44/0.65        | ((k1_tarski @ sk_A) = (sk_B_1)))),
% 0.44/0.65      inference('sup-', [status(thm)], ['18', '19'])).
% 0.44/0.65  thf('21', plain,
% 0.44/0.65      ((((sk_B_1) = (k1_xboole_0)) | ((k1_tarski @ sk_A) = (sk_B_1)))),
% 0.44/0.65      inference('sup-', [status(thm)], ['17', '20'])).
% 0.44/0.65  thf('22', plain,
% 0.44/0.65      ((((sk_B_1) != (k1_tarski @ sk_A)) | ((sk_C_2) != (k1_xboole_0)))),
% 0.44/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.65  thf('23', plain,
% 0.44/0.65      ((((sk_B_1) != (k1_tarski @ sk_A)))
% 0.44/0.65         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 0.44/0.65      inference('split', [status(esa)], ['22'])).
% 0.44/0.65  thf('24', plain,
% 0.44/0.65      (((((sk_B_1) != (sk_B_1)) | ((sk_B_1) = (k1_xboole_0))))
% 0.44/0.65         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 0.44/0.65      inference('sup-', [status(thm)], ['21', '23'])).
% 0.44/0.65  thf('25', plain,
% 0.44/0.65      ((((sk_B_1) = (k1_xboole_0))) <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 0.44/0.65      inference('simplify', [status(thm)], ['24'])).
% 0.44/0.65  thf('26', plain,
% 0.44/0.65      (((k1_tarski @ sk_A) = (k3_tarski @ (k2_tarski @ sk_B_1 @ sk_C_2)))),
% 0.44/0.65      inference('demod', [status(thm)], ['0', '1'])).
% 0.44/0.65  thf('27', plain,
% 0.44/0.65      (((k1_tarski @ sk_A) = (k3_tarski @ (k2_tarski @ sk_B_1 @ sk_C_2)))),
% 0.44/0.65      inference('demod', [status(thm)], ['0', '1'])).
% 0.44/0.65  thf('28', plain,
% 0.44/0.65      (![X11 : $i]:
% 0.44/0.65         (((X11) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X11) @ X11))),
% 0.44/0.65      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.44/0.65  thf(d3_xboole_0, axiom,
% 0.44/0.65    (![A:$i,B:$i,C:$i]:
% 0.44/0.65     ( ( ( C ) = ( k2_xboole_0 @ A @ B ) ) <=>
% 0.44/0.65       ( ![D:$i]:
% 0.44/0.65         ( ( r2_hidden @ D @ C ) <=>
% 0.44/0.65           ( ( r2_hidden @ D @ A ) | ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.44/0.65  thf('29', plain,
% 0.44/0.65      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.44/0.65         (~ (r2_hidden @ X4 @ X5)
% 0.44/0.65          | (r2_hidden @ X4 @ X6)
% 0.44/0.65          | ((X6) != (k2_xboole_0 @ X7 @ X5)))),
% 0.44/0.65      inference('cnf', [status(esa)], [d3_xboole_0])).
% 0.44/0.65  thf('30', plain,
% 0.44/0.65      (![X4 : $i, X5 : $i, X7 : $i]:
% 0.44/0.65         ((r2_hidden @ X4 @ (k2_xboole_0 @ X7 @ X5)) | ~ (r2_hidden @ X4 @ X5))),
% 0.44/0.65      inference('simplify', [status(thm)], ['29'])).
% 0.44/0.65  thf('31', plain,
% 0.44/0.65      (![X74 : $i, X75 : $i]:
% 0.44/0.65         ((k3_tarski @ (k2_tarski @ X74 @ X75)) = (k2_xboole_0 @ X74 @ X75))),
% 0.44/0.65      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.44/0.65  thf('32', plain,
% 0.44/0.65      (![X4 : $i, X5 : $i, X7 : $i]:
% 0.44/0.65         ((r2_hidden @ X4 @ (k3_tarski @ (k2_tarski @ X7 @ X5)))
% 0.44/0.65          | ~ (r2_hidden @ X4 @ X5))),
% 0.44/0.65      inference('demod', [status(thm)], ['30', '31'])).
% 0.44/0.65  thf('33', plain,
% 0.44/0.65      (![X0 : $i, X1 : $i]:
% 0.44/0.65         (((X0) = (k1_xboole_0))
% 0.44/0.65          | (r2_hidden @ (sk_B @ X0) @ (k3_tarski @ (k2_tarski @ X1 @ X0))))),
% 0.44/0.65      inference('sup-', [status(thm)], ['28', '32'])).
% 0.44/0.65  thf('34', plain,
% 0.44/0.65      (((r2_hidden @ (sk_B @ sk_C_2) @ (k1_tarski @ sk_A))
% 0.44/0.65        | ((sk_C_2) = (k1_xboole_0)))),
% 0.44/0.65      inference('sup+', [status(thm)], ['27', '33'])).
% 0.44/0.65  thf('35', plain,
% 0.44/0.65      (![X30 : $i, X33 : $i]:
% 0.44/0.65         (((X33) = (X30)) | ~ (r2_hidden @ X33 @ (k1_tarski @ X30)))),
% 0.44/0.65      inference('simplify', [status(thm)], ['10'])).
% 0.44/0.65  thf('36', plain, ((((sk_C_2) = (k1_xboole_0)) | ((sk_B @ sk_C_2) = (sk_A)))),
% 0.44/0.65      inference('sup-', [status(thm)], ['34', '35'])).
% 0.44/0.65  thf('37', plain,
% 0.44/0.65      (![X11 : $i]:
% 0.44/0.65         (((X11) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X11) @ X11))),
% 0.44/0.65      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.44/0.65  thf('38', plain,
% 0.44/0.65      (((r2_hidden @ sk_A @ sk_C_2)
% 0.44/0.65        | ((sk_C_2) = (k1_xboole_0))
% 0.44/0.65        | ((sk_C_2) = (k1_xboole_0)))),
% 0.44/0.65      inference('sup+', [status(thm)], ['36', '37'])).
% 0.44/0.65  thf('39', plain,
% 0.44/0.65      ((((sk_C_2) = (k1_xboole_0)) | (r2_hidden @ sk_A @ sk_C_2))),
% 0.44/0.65      inference('simplify', [status(thm)], ['38'])).
% 0.44/0.65  thf('40', plain,
% 0.44/0.65      (![X1 : $i, X3 : $i]:
% 0.44/0.65         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.44/0.65      inference('cnf', [status(esa)], [d3_tarski])).
% 0.44/0.65  thf('41', plain,
% 0.44/0.65      (![X0 : $i]:
% 0.44/0.65         ((r2_hidden @ X0 @ (k1_tarski @ sk_A)) | ~ (r2_hidden @ X0 @ sk_B_1))),
% 0.44/0.65      inference('sup-', [status(thm)], ['6', '7'])).
% 0.44/0.65  thf('42', plain,
% 0.44/0.65      (![X0 : $i]:
% 0.44/0.65         ((r1_tarski @ sk_B_1 @ X0)
% 0.44/0.65          | (r2_hidden @ (sk_C @ X0 @ sk_B_1) @ (k1_tarski @ sk_A)))),
% 0.44/0.65      inference('sup-', [status(thm)], ['40', '41'])).
% 0.44/0.65  thf('43', plain,
% 0.44/0.65      (![X30 : $i, X33 : $i]:
% 0.44/0.65         (((X33) = (X30)) | ~ (r2_hidden @ X33 @ (k1_tarski @ X30)))),
% 0.44/0.65      inference('simplify', [status(thm)], ['10'])).
% 0.44/0.65  thf('44', plain,
% 0.44/0.65      (![X0 : $i]:
% 0.44/0.65         ((r1_tarski @ sk_B_1 @ X0) | ((sk_C @ X0 @ sk_B_1) = (sk_A)))),
% 0.44/0.65      inference('sup-', [status(thm)], ['42', '43'])).
% 0.44/0.65  thf('45', plain,
% 0.44/0.65      (![X1 : $i, X3 : $i]:
% 0.44/0.65         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.44/0.65      inference('cnf', [status(esa)], [d3_tarski])).
% 0.44/0.65  thf('46', plain,
% 0.44/0.65      (![X0 : $i]:
% 0.44/0.65         (~ (r2_hidden @ sk_A @ X0)
% 0.44/0.65          | (r1_tarski @ sk_B_1 @ X0)
% 0.44/0.65          | (r1_tarski @ sk_B_1 @ X0))),
% 0.44/0.65      inference('sup-', [status(thm)], ['44', '45'])).
% 0.44/0.65  thf('47', plain,
% 0.44/0.65      (![X0 : $i]: ((r1_tarski @ sk_B_1 @ X0) | ~ (r2_hidden @ sk_A @ X0))),
% 0.44/0.65      inference('simplify', [status(thm)], ['46'])).
% 0.44/0.65  thf('48', plain,
% 0.44/0.65      ((((sk_C_2) = (k1_xboole_0)) | (r1_tarski @ sk_B_1 @ sk_C_2))),
% 0.44/0.65      inference('sup-', [status(thm)], ['39', '47'])).
% 0.44/0.65  thf(t12_xboole_1, axiom,
% 0.44/0.65    (![A:$i,B:$i]:
% 0.44/0.65     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.44/0.65  thf('49', plain,
% 0.44/0.65      (![X17 : $i, X18 : $i]:
% 0.44/0.65         (((k2_xboole_0 @ X18 @ X17) = (X17)) | ~ (r1_tarski @ X18 @ X17))),
% 0.44/0.65      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.44/0.65  thf('50', plain,
% 0.44/0.65      (![X74 : $i, X75 : $i]:
% 0.44/0.65         ((k3_tarski @ (k2_tarski @ X74 @ X75)) = (k2_xboole_0 @ X74 @ X75))),
% 0.44/0.65      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.44/0.65  thf('51', plain,
% 0.44/0.65      (![X17 : $i, X18 : $i]:
% 0.44/0.65         (((k3_tarski @ (k2_tarski @ X18 @ X17)) = (X17))
% 0.44/0.65          | ~ (r1_tarski @ X18 @ X17))),
% 0.44/0.65      inference('demod', [status(thm)], ['49', '50'])).
% 0.44/0.65  thf('52', plain,
% 0.44/0.65      ((((sk_C_2) = (k1_xboole_0))
% 0.44/0.65        | ((k3_tarski @ (k2_tarski @ sk_B_1 @ sk_C_2)) = (sk_C_2)))),
% 0.44/0.65      inference('sup-', [status(thm)], ['48', '51'])).
% 0.44/0.65  thf('53', plain,
% 0.44/0.65      ((((k1_tarski @ sk_A) = (sk_C_2)) | ((sk_C_2) = (k1_xboole_0)))),
% 0.44/0.65      inference('sup+', [status(thm)], ['26', '52'])).
% 0.44/0.65  thf('54', plain,
% 0.44/0.65      ((((sk_B_1) != (k1_xboole_0)) | ((sk_C_2) != (k1_tarski @ sk_A)))),
% 0.44/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.65  thf('55', plain,
% 0.44/0.65      ((((sk_C_2) != (k1_tarski @ sk_A)))
% 0.44/0.65         <= (~ (((sk_C_2) = (k1_tarski @ sk_A))))),
% 0.44/0.65      inference('split', [status(esa)], ['54'])).
% 0.44/0.65  thf('56', plain,
% 0.44/0.65      (~ (((sk_C_2) = (k1_tarski @ sk_A))) | ~ (((sk_B_1) = (k1_xboole_0)))),
% 0.44/0.65      inference('split', [status(esa)], ['54'])).
% 0.44/0.65  thf('57', plain,
% 0.44/0.65      ((((sk_B_1) != (k1_tarski @ sk_A)) | ((sk_C_2) != (k1_tarski @ sk_A)))),
% 0.44/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.65  thf('58', plain,
% 0.44/0.65      (~ (((sk_C_2) = (k1_tarski @ sk_A))) | 
% 0.44/0.65       ~ (((sk_B_1) = (k1_tarski @ sk_A)))),
% 0.44/0.65      inference('split', [status(esa)], ['57'])).
% 0.44/0.65  thf('59', plain,
% 0.44/0.65      ((((sk_B_1) = (k1_xboole_0))) <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 0.44/0.65      inference('simplify', [status(thm)], ['24'])).
% 0.44/0.65  thf('60', plain,
% 0.44/0.65      ((((sk_B_1) != (k1_xboole_0))) <= (~ (((sk_B_1) = (k1_xboole_0))))),
% 0.44/0.65      inference('split', [status(esa)], ['54'])).
% 0.44/0.65  thf('61', plain,
% 0.44/0.65      ((((sk_B_1) != (sk_B_1)))
% 0.44/0.65         <= (~ (((sk_B_1) = (k1_xboole_0))) & 
% 0.44/0.65             ~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 0.44/0.65      inference('sup-', [status(thm)], ['59', '60'])).
% 0.44/0.65  thf('62', plain,
% 0.44/0.65      ((((sk_B_1) = (k1_xboole_0))) | (((sk_B_1) = (k1_tarski @ sk_A)))),
% 0.44/0.65      inference('simplify', [status(thm)], ['61'])).
% 0.44/0.65  thf('63', plain, (~ (((sk_C_2) = (k1_tarski @ sk_A)))),
% 0.44/0.65      inference('sat_resolution*', [status(thm)], ['56', '58', '62'])).
% 0.44/0.65  thf('64', plain, (((sk_C_2) != (k1_tarski @ sk_A))),
% 0.44/0.65      inference('simpl_trail', [status(thm)], ['55', '63'])).
% 0.44/0.65  thf('65', plain, (((sk_C_2) = (k1_xboole_0))),
% 0.44/0.65      inference('simplify_reflect-', [status(thm)], ['53', '64'])).
% 0.44/0.65  thf('66', plain,
% 0.44/0.65      ((((sk_C_2) != (k1_xboole_0))) <= (~ (((sk_C_2) = (k1_xboole_0))))),
% 0.44/0.66      inference('split', [status(esa)], ['22'])).
% 0.44/0.66  thf('67', plain,
% 0.44/0.66      ((((sk_C_2) != (sk_C_2))) <= (~ (((sk_C_2) = (k1_xboole_0))))),
% 0.44/0.66      inference('sup-', [status(thm)], ['65', '66'])).
% 0.44/0.66  thf('68', plain, ((((sk_C_2) = (k1_xboole_0)))),
% 0.44/0.66      inference('simplify', [status(thm)], ['67'])).
% 0.44/0.66  thf('69', plain,
% 0.44/0.66      (~ (((sk_B_1) = (k1_tarski @ sk_A))) | ~ (((sk_C_2) = (k1_xboole_0)))),
% 0.44/0.66      inference('split', [status(esa)], ['22'])).
% 0.44/0.66  thf('70', plain, (~ (((sk_B_1) = (k1_tarski @ sk_A)))),
% 0.44/0.66      inference('sat_resolution*', [status(thm)], ['68', '69'])).
% 0.44/0.66  thf('71', plain, (((sk_B_1) = (k1_xboole_0))),
% 0.44/0.66      inference('simpl_trail', [status(thm)], ['25', '70'])).
% 0.44/0.66  thf('72', plain, (((sk_C_2) = (k1_xboole_0))),
% 0.44/0.66      inference('simplify_reflect-', [status(thm)], ['53', '64'])).
% 0.44/0.66  thf('73', plain, (((sk_C_2) = (sk_B_1))),
% 0.44/0.66      inference('sup+', [status(thm)], ['71', '72'])).
% 0.44/0.66  thf(t69_enumset1, axiom,
% 0.44/0.66    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.44/0.66  thf('74', plain,
% 0.44/0.66      (![X43 : $i]: ((k2_tarski @ X43 @ X43) = (k1_tarski @ X43))),
% 0.44/0.66      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.44/0.66  thf('75', plain,
% 0.44/0.66      (![X43 : $i]: ((k2_tarski @ X43 @ X43) = (k1_tarski @ X43))),
% 0.44/0.66      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.44/0.66  thf(idempotence_k2_xboole_0, axiom,
% 0.44/0.66    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ A ) = ( A ) ))).
% 0.44/0.66  thf('76', plain, (![X10 : $i]: ((k2_xboole_0 @ X10 @ X10) = (X10))),
% 0.44/0.66      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 0.44/0.66  thf('77', plain,
% 0.44/0.66      (![X74 : $i, X75 : $i]:
% 0.44/0.66         ((k3_tarski @ (k2_tarski @ X74 @ X75)) = (k2_xboole_0 @ X74 @ X75))),
% 0.44/0.66      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.44/0.66  thf('78', plain,
% 0.44/0.66      (![X10 : $i]: ((k3_tarski @ (k2_tarski @ X10 @ X10)) = (X10))),
% 0.44/0.66      inference('demod', [status(thm)], ['76', '77'])).
% 0.44/0.66  thf('79', plain, (![X0 : $i]: ((k3_tarski @ (k1_tarski @ X0)) = (X0))),
% 0.44/0.66      inference('sup+', [status(thm)], ['75', '78'])).
% 0.44/0.66  thf('80', plain, (((k1_tarski @ sk_A) = (sk_B_1))),
% 0.44/0.66      inference('demod', [status(thm)], ['2', '73', '74', '79'])).
% 0.44/0.66  thf('81', plain, (((sk_C_2) != (k1_tarski @ sk_A))),
% 0.44/0.66      inference('simpl_trail', [status(thm)], ['55', '63'])).
% 0.44/0.66  thf('82', plain, (((sk_C_2) = (sk_B_1))),
% 0.44/0.66      inference('sup+', [status(thm)], ['71', '72'])).
% 0.44/0.66  thf('83', plain, (((sk_B_1) != (k1_tarski @ sk_A))),
% 0.44/0.66      inference('demod', [status(thm)], ['81', '82'])).
% 0.44/0.66  thf('84', plain, ($false),
% 0.44/0.66      inference('simplify_reflect-', [status(thm)], ['80', '83'])).
% 0.44/0.66  
% 0.44/0.66  % SZS output end Refutation
% 0.44/0.66  
% 0.44/0.66  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
