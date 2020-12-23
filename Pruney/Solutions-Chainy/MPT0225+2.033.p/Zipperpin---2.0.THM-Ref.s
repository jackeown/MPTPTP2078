%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.gNVq0s60fM

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:29:49 EST 2020

% Result     : Theorem 0.37s
% Output     : Refutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 242 expanded)
%              Number of leaves         :   22 (  72 expanded)
%              Depth                    :   16
%              Number of atoms          :  681 (2315 expanded)
%              Number of equality atoms :   81 ( 293 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(l27_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( r2_hidden @ A @ B )
     => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) )).

thf('0',plain,(
    ! [X32: $i,X33: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X32 ) @ X33 )
      | ( r2_hidden @ X32 @ X33 ) ) ),
    inference(cnf,[status(esa)],[l27_zfmisc_1])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('1',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_xboole_0 @ X6 @ X7 )
      | ~ ( r1_xboole_0 @ X7 @ X6 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('3',plain,(
    ! [X16: $i] :
      ( ( X16 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X16 ) @ X16 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('4',plain,(
    ! [X12: $i,X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ X14 @ ( k3_xboole_0 @ X12 @ X15 ) )
      | ~ ( r1_xboole_0 @ X12 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( ( k3_xboole_0 @ X1 @ ( k1_tarski @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['2','5'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('7',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ X18 )
      = ( k5_xboole_0 @ X17 @ ( k3_xboole_0 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X1 @ ( k1_tarski @ X0 ) )
        = ( k5_xboole_0 @ X1 @ k1_xboole_0 ) )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('9',plain,(
    ! [X20: $i] :
      ( r1_xboole_0 @ X20 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ X18 )
      = ( k5_xboole_0 @ X17 @ ( k3_xboole_0 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('14',plain,(
    ! [X19: $i] :
      ( ( k4_xboole_0 @ X19 @ k1_xboole_0 )
      = X19 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('15',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X1 @ ( k1_tarski @ X0 ) )
        = X1 )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['8','15'])).

thf(t20_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k1_tarski @ A ) )
    <=> ( A != B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
          = ( k1_tarski @ A ) )
      <=> ( A != B ) ) ),
    inference('cnf.neg',[status(esa)],[t20_zfmisc_1])).

thf('17',plain,
    ( ( sk_A = sk_B_1 )
    | ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B_1 ) )
     != ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B_1 ) )
     != ( k1_tarski @ sk_A ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B_1 ) )
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['17'])).

thf('19',plain,
    ( ( sk_A != sk_B_1 )
    | ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B_1 ) )
      = ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ( sk_A != sk_B_1 )
    | ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B_1 ) )
      = ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['19'])).

thf('21',plain,
    ( ( sk_A = sk_B_1 )
   <= ( sk_A = sk_B_1 ) ),
    inference(split,[status(esa)],['17'])).

thf('22',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B_1 ) )
      = ( k1_tarski @ sk_A ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B_1 ) )
      = ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['19'])).

thf('23',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_B_1 ) @ ( k1_tarski @ sk_B_1 ) )
      = ( k1_tarski @ sk_A ) )
   <= ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B_1 ) )
        = ( k1_tarski @ sk_A ) )
      & ( sk_A = sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,
    ( ( sk_A = sk_B_1 )
   <= ( sk_A = sk_B_1 ) ),
    inference(split,[status(esa)],['17'])).

thf('25',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_B_1 ) @ ( k1_tarski @ sk_B_1 ) )
      = ( k1_tarski @ sk_B_1 ) )
   <= ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B_1 ) )
        = ( k1_tarski @ sk_A ) )
      & ( sk_A = sk_B_1 ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X16: $i] :
      ( ( X16 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X16 ) @ X16 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('27',plain,(
    ! [X16: $i] :
      ( ( X16 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X16 ) @ X16 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_hidden @ X0 @ X2 )
      | ( r2_hidden @ X0 @ X3 )
      | ( X3
       != ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X0 @ ( k3_xboole_0 @ X1 @ X2 ) )
      | ~ ( r2_hidden @ X0 @ X2 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( r2_hidden @ ( sk_B @ X0 ) @ X1 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['27','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ ( k3_xboole_0 @ X0 @ X0 ) )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['26','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_B @ X0 ) @ ( k3_xboole_0 @ X0 @ X0 ) )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ X18 )
      = ( k5_xboole_0 @ X17 @ ( k3_xboole_0 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf(t1_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k5_xboole_0 @ B @ C ) )
    <=> ~ ( ( r2_hidden @ A @ B )
        <=> ( r2_hidden @ A @ C ) ) ) )).

thf('34',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X8 @ X9 )
      | ~ ( r2_hidden @ X8 @ X10 )
      | ~ ( r2_hidden @ X8 @ ( k5_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_0])).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ( r2_hidden @ X4 @ X1 )
      | ( X3
       != ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('37',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ X1 )
      | ~ ( r2_hidden @ X4 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['35','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( r2_hidden @ ( sk_B @ X0 ) @ ( k4_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['32','38'])).

thf('40',plain,
    ( ( ~ ( r2_hidden @ ( sk_B @ ( k1_tarski @ sk_B_1 ) ) @ ( k1_tarski @ sk_B_1 ) )
      | ( ( k1_tarski @ sk_B_1 )
        = k1_xboole_0 ) )
   <= ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B_1 ) )
        = ( k1_tarski @ sk_A ) )
      & ( sk_A = sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['25','39'])).

thf('41',plain,(
    ! [X16: $i] :
      ( ( X16 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X16 ) @ X16 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('42',plain,
    ( ( ( k1_tarski @ sk_B_1 )
      = k1_xboole_0 )
   <= ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B_1 ) )
        = ( k1_tarski @ sk_A ) )
      & ( sk_A = sk_B_1 ) ) ),
    inference(clc,[status(thm)],['40','41'])).

thf(t16_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r1_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        & ( A = B ) ) )).

thf('43',plain,(
    ! [X34: $i,X35: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_tarski @ X34 ) @ ( k1_tarski @ X35 ) )
      | ( X34 != X35 ) ) ),
    inference(cnf,[status(esa)],[t16_zfmisc_1])).

thf('44',plain,(
    ! [X35: $i] :
      ~ ( r1_xboole_0 @ ( k1_tarski @ X35 ) @ ( k1_tarski @ X35 ) ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,
    ( ~ ( r1_xboole_0 @ ( k1_tarski @ sk_B_1 ) @ k1_xboole_0 )
   <= ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B_1 ) )
        = ( k1_tarski @ sk_A ) )
      & ( sk_A = sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['42','44'])).

thf('46',plain,
    ( ( ( k1_tarski @ sk_B_1 )
      = k1_xboole_0 )
   <= ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B_1 ) )
        = ( k1_tarski @ sk_A ) )
      & ( sk_A = sk_B_1 ) ) ),
    inference(clc,[status(thm)],['40','41'])).

thf('47',plain,(
    ! [X20: $i] :
      ( r1_xboole_0 @ X20 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('48',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_xboole_0 @ X6 @ X7 )
      | ~ ( r1_xboole_0 @ X7 @ X6 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('49',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B_1 ) )
     != ( k1_tarski @ sk_A ) )
    | ( sk_A != sk_B_1 ) ),
    inference(demod,[status(thm)],['45','46','49'])).

thf('51',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B_1 ) )
     != ( k1_tarski @ sk_A ) )
    | ( sk_A = sk_B_1 ) ),
    inference(split,[status(esa)],['17'])).

thf('52',plain,(
    ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B_1 ) )
 != ( k1_tarski @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['20','50','51'])).

thf('53',plain,(
    ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B_1 ) )
 != ( k1_tarski @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['18','52'])).

thf('54',plain,
    ( ( ( k1_tarski @ sk_A )
     != ( k1_tarski @ sk_A ) )
    | ( r2_hidden @ sk_B_1 @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['16','53'])).

thf('55',plain,(
    r2_hidden @ sk_B_1 @ ( k1_tarski @ sk_A ) ),
    inference(simplify,[status(thm)],['54'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('56',plain,(
    ! [X21: $i,X23: $i,X24: $i] :
      ( ~ ( r2_hidden @ X24 @ X23 )
      | ( X24 = X21 )
      | ( X23
       != ( k1_tarski @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('57',plain,(
    ! [X21: $i,X24: $i] :
      ( ( X24 = X21 )
      | ~ ( r2_hidden @ X24 @ ( k1_tarski @ X21 ) ) ) ),
    inference(simplify,[status(thm)],['56'])).

thf('58',plain,(
    sk_B_1 = sk_A ),
    inference('sup-',[status(thm)],['55','57'])).

thf('59',plain,
    ( ( sk_A != sk_B_1 )
   <= ( sk_A != sk_B_1 ) ),
    inference(split,[status(esa)],['19'])).

thf('60',plain,(
    sk_A != sk_B_1 ),
    inference('sat_resolution*',[status(thm)],['20','50'])).

thf('61',plain,(
    sk_A != sk_B_1 ),
    inference(simpl_trail,[status(thm)],['59','60'])).

thf('62',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['58','61'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.gNVq0s60fM
% 0.13/0.38  % Computer   : n018.cluster.edu
% 0.13/0.38  % Model      : x86_64 x86_64
% 0.13/0.38  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.38  % Memory     : 8042.1875MB
% 0.13/0.38  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.38  % CPULimit   : 60
% 0.13/0.38  % DateTime   : Tue Dec  1 20:22:57 EST 2020
% 0.23/0.38  % CPUTime    : 
% 0.23/0.38  % Running portfolio for 600 s
% 0.23/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.23/0.38  % Number of cores: 8
% 0.23/0.38  % Python version: Python 3.6.8
% 0.23/0.38  % Running in FO mode
% 0.37/0.58  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.37/0.58  % Solved by: fo/fo7.sh
% 0.37/0.58  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.37/0.58  % done 120 iterations in 0.091s
% 0.37/0.58  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.37/0.58  % SZS output start Refutation
% 0.37/0.58  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.37/0.58  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.37/0.58  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.37/0.58  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.37/0.58  thf(sk_A_type, type, sk_A: $i).
% 0.37/0.58  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.37/0.58  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.37/0.58  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.37/0.58  thf(sk_B_type, type, sk_B: $i > $i).
% 0.37/0.58  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.37/0.58  thf(l27_zfmisc_1, axiom,
% 0.37/0.58    (![A:$i,B:$i]:
% 0.37/0.58     ( ( ~( r2_hidden @ A @ B ) ) => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ))).
% 0.37/0.58  thf('0', plain,
% 0.37/0.58      (![X32 : $i, X33 : $i]:
% 0.37/0.58         ((r1_xboole_0 @ (k1_tarski @ X32) @ X33) | (r2_hidden @ X32 @ X33))),
% 0.37/0.58      inference('cnf', [status(esa)], [l27_zfmisc_1])).
% 0.37/0.58  thf(symmetry_r1_xboole_0, axiom,
% 0.37/0.58    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 0.37/0.58  thf('1', plain,
% 0.37/0.58      (![X6 : $i, X7 : $i]:
% 0.37/0.58         ((r1_xboole_0 @ X6 @ X7) | ~ (r1_xboole_0 @ X7 @ X6))),
% 0.37/0.58      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.37/0.58  thf('2', plain,
% 0.37/0.58      (![X0 : $i, X1 : $i]:
% 0.37/0.58         ((r2_hidden @ X1 @ X0) | (r1_xboole_0 @ X0 @ (k1_tarski @ X1)))),
% 0.37/0.58      inference('sup-', [status(thm)], ['0', '1'])).
% 0.37/0.58  thf(t7_xboole_0, axiom,
% 0.37/0.58    (![A:$i]:
% 0.37/0.58     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.37/0.58          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.37/0.58  thf('3', plain,
% 0.37/0.58      (![X16 : $i]:
% 0.37/0.58         (((X16) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X16) @ X16))),
% 0.37/0.58      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.37/0.58  thf(t4_xboole_0, axiom,
% 0.37/0.58    (![A:$i,B:$i]:
% 0.37/0.58     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.37/0.58            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.37/0.58       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.37/0.58            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.37/0.58  thf('4', plain,
% 0.37/0.58      (![X12 : $i, X14 : $i, X15 : $i]:
% 0.37/0.58         (~ (r2_hidden @ X14 @ (k3_xboole_0 @ X12 @ X15))
% 0.37/0.58          | ~ (r1_xboole_0 @ X12 @ X15))),
% 0.37/0.58      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.37/0.58  thf('5', plain,
% 0.37/0.58      (![X0 : $i, X1 : $i]:
% 0.37/0.58         (((k3_xboole_0 @ X1 @ X0) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.37/0.58      inference('sup-', [status(thm)], ['3', '4'])).
% 0.37/0.58  thf('6', plain,
% 0.37/0.58      (![X0 : $i, X1 : $i]:
% 0.37/0.58         ((r2_hidden @ X0 @ X1)
% 0.37/0.58          | ((k3_xboole_0 @ X1 @ (k1_tarski @ X0)) = (k1_xboole_0)))),
% 0.37/0.58      inference('sup-', [status(thm)], ['2', '5'])).
% 0.37/0.58  thf(t100_xboole_1, axiom,
% 0.37/0.58    (![A:$i,B:$i]:
% 0.37/0.58     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.37/0.58  thf('7', plain,
% 0.37/0.58      (![X17 : $i, X18 : $i]:
% 0.37/0.58         ((k4_xboole_0 @ X17 @ X18)
% 0.37/0.58           = (k5_xboole_0 @ X17 @ (k3_xboole_0 @ X17 @ X18)))),
% 0.37/0.58      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.37/0.58  thf('8', plain,
% 0.37/0.58      (![X0 : $i, X1 : $i]:
% 0.37/0.58         (((k4_xboole_0 @ X1 @ (k1_tarski @ X0))
% 0.37/0.58            = (k5_xboole_0 @ X1 @ k1_xboole_0))
% 0.37/0.58          | (r2_hidden @ X0 @ X1))),
% 0.37/0.58      inference('sup+', [status(thm)], ['6', '7'])).
% 0.37/0.58  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.37/0.58  thf('9', plain, (![X20 : $i]: (r1_xboole_0 @ X20 @ k1_xboole_0)),
% 0.37/0.58      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.37/0.58  thf('10', plain,
% 0.37/0.58      (![X0 : $i, X1 : $i]:
% 0.37/0.58         (((k3_xboole_0 @ X1 @ X0) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.37/0.58      inference('sup-', [status(thm)], ['3', '4'])).
% 0.37/0.58  thf('11', plain,
% 0.37/0.58      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.37/0.58      inference('sup-', [status(thm)], ['9', '10'])).
% 0.37/0.58  thf('12', plain,
% 0.37/0.58      (![X17 : $i, X18 : $i]:
% 0.37/0.58         ((k4_xboole_0 @ X17 @ X18)
% 0.37/0.58           = (k5_xboole_0 @ X17 @ (k3_xboole_0 @ X17 @ X18)))),
% 0.37/0.58      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.37/0.58  thf('13', plain,
% 0.37/0.58      (![X0 : $i]:
% 0.37/0.58         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.37/0.58      inference('sup+', [status(thm)], ['11', '12'])).
% 0.37/0.58  thf(t3_boole, axiom,
% 0.37/0.58    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.37/0.58  thf('14', plain, (![X19 : $i]: ((k4_xboole_0 @ X19 @ k1_xboole_0) = (X19))),
% 0.37/0.58      inference('cnf', [status(esa)], [t3_boole])).
% 0.37/0.58  thf('15', plain, (![X0 : $i]: ((X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.37/0.58      inference('demod', [status(thm)], ['13', '14'])).
% 0.37/0.58  thf('16', plain,
% 0.37/0.58      (![X0 : $i, X1 : $i]:
% 0.37/0.58         (((k4_xboole_0 @ X1 @ (k1_tarski @ X0)) = (X1))
% 0.37/0.58          | (r2_hidden @ X0 @ X1))),
% 0.37/0.58      inference('demod', [status(thm)], ['8', '15'])).
% 0.37/0.58  thf(t20_zfmisc_1, conjecture,
% 0.37/0.58    (![A:$i,B:$i]:
% 0.37/0.58     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.37/0.58         ( k1_tarski @ A ) ) <=>
% 0.37/0.58       ( ( A ) != ( B ) ) ))).
% 0.37/0.58  thf(zf_stmt_0, negated_conjecture,
% 0.37/0.58    (~( ![A:$i,B:$i]:
% 0.37/0.58        ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.37/0.58            ( k1_tarski @ A ) ) <=>
% 0.37/0.58          ( ( A ) != ( B ) ) ) )),
% 0.37/0.58    inference('cnf.neg', [status(esa)], [t20_zfmisc_1])).
% 0.37/0.58  thf('17', plain,
% 0.37/0.58      ((((sk_A) = (sk_B_1))
% 0.37/0.58        | ((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B_1))
% 0.37/0.58            != (k1_tarski @ sk_A)))),
% 0.37/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.58  thf('18', plain,
% 0.37/0.58      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B_1))
% 0.37/0.58          != (k1_tarski @ sk_A)))
% 0.37/0.58         <= (~
% 0.37/0.58             (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B_1))
% 0.37/0.58                = (k1_tarski @ sk_A))))),
% 0.37/0.58      inference('split', [status(esa)], ['17'])).
% 0.37/0.58  thf('19', plain,
% 0.37/0.58      ((((sk_A) != (sk_B_1))
% 0.37/0.58        | ((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B_1))
% 0.37/0.58            = (k1_tarski @ sk_A)))),
% 0.37/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.58  thf('20', plain,
% 0.37/0.58      (~ (((sk_A) = (sk_B_1))) | 
% 0.37/0.58       (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B_1))
% 0.37/0.58          = (k1_tarski @ sk_A)))),
% 0.37/0.58      inference('split', [status(esa)], ['19'])).
% 0.37/0.58  thf('21', plain, ((((sk_A) = (sk_B_1))) <= ((((sk_A) = (sk_B_1))))),
% 0.37/0.58      inference('split', [status(esa)], ['17'])).
% 0.37/0.58  thf('22', plain,
% 0.37/0.58      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B_1))
% 0.37/0.58          = (k1_tarski @ sk_A)))
% 0.37/0.58         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B_1))
% 0.37/0.58                = (k1_tarski @ sk_A))))),
% 0.37/0.58      inference('split', [status(esa)], ['19'])).
% 0.37/0.58  thf('23', plain,
% 0.37/0.58      ((((k4_xboole_0 @ (k1_tarski @ sk_B_1) @ (k1_tarski @ sk_B_1))
% 0.37/0.58          = (k1_tarski @ sk_A)))
% 0.37/0.58         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B_1))
% 0.37/0.58                = (k1_tarski @ sk_A))) & 
% 0.37/0.58             (((sk_A) = (sk_B_1))))),
% 0.37/0.58      inference('sup+', [status(thm)], ['21', '22'])).
% 0.37/0.58  thf('24', plain, ((((sk_A) = (sk_B_1))) <= ((((sk_A) = (sk_B_1))))),
% 0.37/0.58      inference('split', [status(esa)], ['17'])).
% 0.37/0.58  thf('25', plain,
% 0.37/0.58      ((((k4_xboole_0 @ (k1_tarski @ sk_B_1) @ (k1_tarski @ sk_B_1))
% 0.37/0.58          = (k1_tarski @ sk_B_1)))
% 0.37/0.58         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B_1))
% 0.37/0.58                = (k1_tarski @ sk_A))) & 
% 0.37/0.58             (((sk_A) = (sk_B_1))))),
% 0.37/0.58      inference('demod', [status(thm)], ['23', '24'])).
% 0.37/0.58  thf('26', plain,
% 0.37/0.58      (![X16 : $i]:
% 0.37/0.58         (((X16) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X16) @ X16))),
% 0.37/0.58      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.37/0.58  thf('27', plain,
% 0.37/0.58      (![X16 : $i]:
% 0.37/0.58         (((X16) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X16) @ X16))),
% 0.37/0.58      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.37/0.58  thf(d4_xboole_0, axiom,
% 0.37/0.58    (![A:$i,B:$i,C:$i]:
% 0.37/0.58     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 0.37/0.58       ( ![D:$i]:
% 0.37/0.58         ( ( r2_hidden @ D @ C ) <=>
% 0.37/0.58           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.37/0.58  thf('28', plain,
% 0.37/0.58      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.37/0.58         (~ (r2_hidden @ X0 @ X1)
% 0.37/0.58          | ~ (r2_hidden @ X0 @ X2)
% 0.37/0.58          | (r2_hidden @ X0 @ X3)
% 0.37/0.58          | ((X3) != (k3_xboole_0 @ X1 @ X2)))),
% 0.37/0.58      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.37/0.58  thf('29', plain,
% 0.37/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.37/0.58         ((r2_hidden @ X0 @ (k3_xboole_0 @ X1 @ X2))
% 0.37/0.58          | ~ (r2_hidden @ X0 @ X2)
% 0.37/0.58          | ~ (r2_hidden @ X0 @ X1))),
% 0.37/0.58      inference('simplify', [status(thm)], ['28'])).
% 0.37/0.58  thf('30', plain,
% 0.37/0.58      (![X0 : $i, X1 : $i]:
% 0.37/0.58         (((X0) = (k1_xboole_0))
% 0.37/0.58          | ~ (r2_hidden @ (sk_B @ X0) @ X1)
% 0.37/0.58          | (r2_hidden @ (sk_B @ X0) @ (k3_xboole_0 @ X1 @ X0)))),
% 0.37/0.58      inference('sup-', [status(thm)], ['27', '29'])).
% 0.37/0.58  thf('31', plain,
% 0.37/0.58      (![X0 : $i]:
% 0.37/0.58         (((X0) = (k1_xboole_0))
% 0.37/0.58          | (r2_hidden @ (sk_B @ X0) @ (k3_xboole_0 @ X0 @ X0))
% 0.37/0.58          | ((X0) = (k1_xboole_0)))),
% 0.37/0.58      inference('sup-', [status(thm)], ['26', '30'])).
% 0.37/0.58  thf('32', plain,
% 0.37/0.58      (![X0 : $i]:
% 0.37/0.58         ((r2_hidden @ (sk_B @ X0) @ (k3_xboole_0 @ X0 @ X0))
% 0.37/0.58          | ((X0) = (k1_xboole_0)))),
% 0.37/0.58      inference('simplify', [status(thm)], ['31'])).
% 0.37/0.58  thf('33', plain,
% 0.37/0.58      (![X17 : $i, X18 : $i]:
% 0.37/0.58         ((k4_xboole_0 @ X17 @ X18)
% 0.37/0.58           = (k5_xboole_0 @ X17 @ (k3_xboole_0 @ X17 @ X18)))),
% 0.37/0.58      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.37/0.58  thf(t1_xboole_0, axiom,
% 0.37/0.58    (![A:$i,B:$i,C:$i]:
% 0.37/0.58     ( ( r2_hidden @ A @ ( k5_xboole_0 @ B @ C ) ) <=>
% 0.37/0.58       ( ~( ( r2_hidden @ A @ B ) <=> ( r2_hidden @ A @ C ) ) ) ))).
% 0.37/0.58  thf('34', plain,
% 0.37/0.58      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.37/0.58         (~ (r2_hidden @ X8 @ X9)
% 0.37/0.58          | ~ (r2_hidden @ X8 @ X10)
% 0.37/0.58          | ~ (r2_hidden @ X8 @ (k5_xboole_0 @ X9 @ X10)))),
% 0.37/0.58      inference('cnf', [status(esa)], [t1_xboole_0])).
% 0.37/0.58  thf('35', plain,
% 0.37/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.37/0.58         (~ (r2_hidden @ X2 @ (k4_xboole_0 @ X1 @ X0))
% 0.37/0.58          | ~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 0.37/0.58          | ~ (r2_hidden @ X2 @ X1))),
% 0.37/0.58      inference('sup-', [status(thm)], ['33', '34'])).
% 0.37/0.58  thf('36', plain,
% 0.37/0.58      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.37/0.58         (~ (r2_hidden @ X4 @ X3)
% 0.37/0.58          | (r2_hidden @ X4 @ X1)
% 0.37/0.58          | ((X3) != (k3_xboole_0 @ X1 @ X2)))),
% 0.37/0.58      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.37/0.58  thf('37', plain,
% 0.37/0.58      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.37/0.58         ((r2_hidden @ X4 @ X1) | ~ (r2_hidden @ X4 @ (k3_xboole_0 @ X1 @ X2)))),
% 0.37/0.58      inference('simplify', [status(thm)], ['36'])).
% 0.37/0.58  thf('38', plain,
% 0.37/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.37/0.58         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 0.37/0.58          | ~ (r2_hidden @ X2 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.37/0.58      inference('clc', [status(thm)], ['35', '37'])).
% 0.37/0.58  thf('39', plain,
% 0.37/0.58      (![X0 : $i]:
% 0.37/0.58         (((X0) = (k1_xboole_0))
% 0.37/0.58          | ~ (r2_hidden @ (sk_B @ X0) @ (k4_xboole_0 @ X0 @ X0)))),
% 0.37/0.58      inference('sup-', [status(thm)], ['32', '38'])).
% 0.37/0.58  thf('40', plain,
% 0.37/0.58      (((~ (r2_hidden @ (sk_B @ (k1_tarski @ sk_B_1)) @ (k1_tarski @ sk_B_1))
% 0.37/0.58         | ((k1_tarski @ sk_B_1) = (k1_xboole_0))))
% 0.37/0.58         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B_1))
% 0.37/0.58                = (k1_tarski @ sk_A))) & 
% 0.37/0.58             (((sk_A) = (sk_B_1))))),
% 0.37/0.58      inference('sup-', [status(thm)], ['25', '39'])).
% 0.37/0.58  thf('41', plain,
% 0.37/0.58      (![X16 : $i]:
% 0.37/0.58         (((X16) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X16) @ X16))),
% 0.37/0.58      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.37/0.58  thf('42', plain,
% 0.37/0.58      ((((k1_tarski @ sk_B_1) = (k1_xboole_0)))
% 0.37/0.58         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B_1))
% 0.37/0.58                = (k1_tarski @ sk_A))) & 
% 0.37/0.58             (((sk_A) = (sk_B_1))))),
% 0.37/0.58      inference('clc', [status(thm)], ['40', '41'])).
% 0.37/0.58  thf(t16_zfmisc_1, axiom,
% 0.37/0.58    (![A:$i,B:$i]:
% 0.37/0.58     ( ~( ( r1_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) & 
% 0.37/0.58          ( ( A ) = ( B ) ) ) ))).
% 0.37/0.58  thf('43', plain,
% 0.37/0.58      (![X34 : $i, X35 : $i]:
% 0.37/0.58         (~ (r1_xboole_0 @ (k1_tarski @ X34) @ (k1_tarski @ X35))
% 0.37/0.58          | ((X34) != (X35)))),
% 0.37/0.58      inference('cnf', [status(esa)], [t16_zfmisc_1])).
% 0.37/0.58  thf('44', plain,
% 0.37/0.58      (![X35 : $i]: ~ (r1_xboole_0 @ (k1_tarski @ X35) @ (k1_tarski @ X35))),
% 0.37/0.58      inference('simplify', [status(thm)], ['43'])).
% 0.37/0.58  thf('45', plain,
% 0.37/0.58      ((~ (r1_xboole_0 @ (k1_tarski @ sk_B_1) @ k1_xboole_0))
% 0.37/0.58         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B_1))
% 0.37/0.58                = (k1_tarski @ sk_A))) & 
% 0.37/0.58             (((sk_A) = (sk_B_1))))),
% 0.37/0.58      inference('sup-', [status(thm)], ['42', '44'])).
% 0.37/0.58  thf('46', plain,
% 0.37/0.58      ((((k1_tarski @ sk_B_1) = (k1_xboole_0)))
% 0.37/0.58         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B_1))
% 0.37/0.58                = (k1_tarski @ sk_A))) & 
% 0.37/0.58             (((sk_A) = (sk_B_1))))),
% 0.37/0.58      inference('clc', [status(thm)], ['40', '41'])).
% 0.37/0.58  thf('47', plain, (![X20 : $i]: (r1_xboole_0 @ X20 @ k1_xboole_0)),
% 0.37/0.58      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.37/0.58  thf('48', plain,
% 0.37/0.58      (![X6 : $i, X7 : $i]:
% 0.37/0.58         ((r1_xboole_0 @ X6 @ X7) | ~ (r1_xboole_0 @ X7 @ X6))),
% 0.37/0.58      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.37/0.58  thf('49', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.37/0.58      inference('sup-', [status(thm)], ['47', '48'])).
% 0.37/0.58  thf('50', plain,
% 0.37/0.58      (~
% 0.37/0.58       (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B_1))
% 0.37/0.58          = (k1_tarski @ sk_A))) | 
% 0.37/0.58       ~ (((sk_A) = (sk_B_1)))),
% 0.37/0.58      inference('demod', [status(thm)], ['45', '46', '49'])).
% 0.37/0.58  thf('51', plain,
% 0.37/0.58      (~
% 0.37/0.58       (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B_1))
% 0.37/0.58          = (k1_tarski @ sk_A))) | 
% 0.37/0.58       (((sk_A) = (sk_B_1)))),
% 0.37/0.58      inference('split', [status(esa)], ['17'])).
% 0.37/0.58  thf('52', plain,
% 0.37/0.58      (~
% 0.37/0.58       (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B_1))
% 0.37/0.58          = (k1_tarski @ sk_A)))),
% 0.37/0.58      inference('sat_resolution*', [status(thm)], ['20', '50', '51'])).
% 0.37/0.58  thf('53', plain,
% 0.37/0.58      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B_1))
% 0.37/0.58         != (k1_tarski @ sk_A))),
% 0.37/0.58      inference('simpl_trail', [status(thm)], ['18', '52'])).
% 0.37/0.58  thf('54', plain,
% 0.37/0.58      ((((k1_tarski @ sk_A) != (k1_tarski @ sk_A))
% 0.37/0.58        | (r2_hidden @ sk_B_1 @ (k1_tarski @ sk_A)))),
% 0.37/0.58      inference('sup-', [status(thm)], ['16', '53'])).
% 0.37/0.58  thf('55', plain, ((r2_hidden @ sk_B_1 @ (k1_tarski @ sk_A))),
% 0.37/0.58      inference('simplify', [status(thm)], ['54'])).
% 0.37/0.58  thf(d1_tarski, axiom,
% 0.37/0.58    (![A:$i,B:$i]:
% 0.37/0.58     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.37/0.58       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.37/0.58  thf('56', plain,
% 0.37/0.58      (![X21 : $i, X23 : $i, X24 : $i]:
% 0.37/0.58         (~ (r2_hidden @ X24 @ X23)
% 0.37/0.58          | ((X24) = (X21))
% 0.37/0.58          | ((X23) != (k1_tarski @ X21)))),
% 0.37/0.58      inference('cnf', [status(esa)], [d1_tarski])).
% 0.37/0.58  thf('57', plain,
% 0.37/0.58      (![X21 : $i, X24 : $i]:
% 0.37/0.58         (((X24) = (X21)) | ~ (r2_hidden @ X24 @ (k1_tarski @ X21)))),
% 0.37/0.58      inference('simplify', [status(thm)], ['56'])).
% 0.37/0.58  thf('58', plain, (((sk_B_1) = (sk_A))),
% 0.37/0.58      inference('sup-', [status(thm)], ['55', '57'])).
% 0.37/0.58  thf('59', plain, ((((sk_A) != (sk_B_1))) <= (~ (((sk_A) = (sk_B_1))))),
% 0.37/0.58      inference('split', [status(esa)], ['19'])).
% 0.37/0.58  thf('60', plain, (~ (((sk_A) = (sk_B_1)))),
% 0.37/0.58      inference('sat_resolution*', [status(thm)], ['20', '50'])).
% 0.37/0.58  thf('61', plain, (((sk_A) != (sk_B_1))),
% 0.37/0.58      inference('simpl_trail', [status(thm)], ['59', '60'])).
% 0.37/0.58  thf('62', plain, ($false),
% 0.37/0.58      inference('simplify_reflect-', [status(thm)], ['58', '61'])).
% 0.37/0.58  
% 0.37/0.58  % SZS output end Refutation
% 0.37/0.58  
% 0.37/0.59  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
