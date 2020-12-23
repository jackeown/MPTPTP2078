%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.xvUTCHvBes

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:36:26 EST 2020

% Result     : Theorem 1.36s
% Output     : Refutation 1.36s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 134 expanded)
%              Number of leaves         :   25 (  51 expanded)
%              Depth                    :   20
%              Number of atoms          :  631 (1014 expanded)
%              Number of equality atoms :   48 (  72 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(t149_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k1_tarski @ D ) )
        & ( r2_hidden @ D @ C )
        & ( r1_xboole_0 @ C @ B ) )
     => ( r1_xboole_0 @ ( k2_xboole_0 @ A @ C ) @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k1_tarski @ D ) )
          & ( r2_hidden @ D @ C )
          & ( r1_xboole_0 @ C @ B ) )
       => ( r1_xboole_0 @ ( k2_xboole_0 @ A @ C ) @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t149_zfmisc_1])).

thf('0',plain,(
    ~ ( r1_xboole_0 @ ( k2_xboole_0 @ sk_A @ sk_C_1 ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r1_xboole_0 @ sk_C_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('2',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('3',plain,
    ( ( k3_xboole_0 @ sk_C_1 @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['1','2'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('5',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_C_1 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['3','4'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('6',plain,(
    ! [X16: $i] :
      ( ( k4_xboole_0 @ X16 @ k1_xboole_0 )
      = X16 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('7',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k3_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('9',plain,(
    ! [X22: $i] :
      ( r1_xboole_0 @ X22 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('10',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['8','11'])).

thf('13',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k3_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X16: $i] :
      ( ( k4_xboole_0 @ X16 @ k1_xboole_0 )
      = X16 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('16',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf(l27_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( r2_hidden @ A @ B )
     => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) )).

thf('17',plain,(
    ! [X34: $i,X35: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X34 ) @ X35 )
      | ( r2_hidden @ X34 @ X35 ) ) ),
    inference(cnf,[status(esa)],[l27_zfmisc_1])).

thf('18',plain,(
    r1_tarski @ ( k3_xboole_0 @ sk_A @ sk_B ) @ ( k1_tarski @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('20',plain,(
    r1_tarski @ ( k3_xboole_0 @ sk_B @ sk_A ) @ ( k1_tarski @ sk_D ) ),
    inference(demod,[status(thm)],['18','19'])).

thf(t63_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ B @ C ) )
     => ( r1_xboole_0 @ A @ C ) ) )).

thf('21',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( r1_tarski @ X19 @ X20 )
      | ~ ( r1_xboole_0 @ X20 @ X21 )
      | ( r1_xboole_0 @ X19 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t63_xboole_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ ( k3_xboole_0 @ sk_B @ sk_A ) @ X0 )
      | ~ ( r1_xboole_0 @ ( k1_tarski @ sk_D ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_D @ X0 )
      | ( r1_xboole_0 @ ( k3_xboole_0 @ sk_B @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['17','22'])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('24',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_xboole_0 @ X5 @ X6 )
      | ~ ( r1_xboole_0 @ X6 @ X5 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_D @ X0 )
      | ( r1_xboole_0 @ X0 @ ( k3_xboole_0 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf(t3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( ( r2_hidden @ C @ B )
              & ( r2_hidden @ C @ A ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( ( r2_hidden @ C @ A )
                & ( r2_hidden @ C @ B ) ) ) ) )).

thf('26',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_xboole_0 @ X7 @ X8 )
      | ( r2_hidden @ ( sk_C @ X8 @ X7 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('27',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_xboole_0 @ X7 @ X8 )
      | ( r2_hidden @ ( sk_C @ X8 @ X7 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('28',plain,(
    ! [X7: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X9 @ X7 )
      | ~ ( r2_hidden @ X9 @ X10 )
      | ~ ( r1_xboole_0 @ X7 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['26','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_D @ ( k3_xboole_0 @ sk_B @ sk_A ) )
      | ( r1_xboole_0 @ ( k3_xboole_0 @ sk_B @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['25','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('34',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_C_1 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['3','4'])).

thf(t16_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C )
      = ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('35',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X13 @ X14 ) @ X15 )
      = ( k3_xboole_0 @ X13 @ ( k3_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('37',plain,(
    ! [X2: $i,X4: $i] :
      ( ( r1_xboole_0 @ X2 @ X4 )
      | ( ( k3_xboole_0 @ X2 @ X4 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ X0 @ ( k3_xboole_0 @ X2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['35','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ sk_C_1 @ ( k3_xboole_0 @ X0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['34','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_xboole_0 @ sk_C_1 @ ( k3_xboole_0 @ X0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ sk_C_1 @ ( k3_xboole_0 @ X0 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,(
    r2_hidden @ sk_D @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    ! [X7: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X9 @ X7 )
      | ~ ( r2_hidden @ X9 @ X10 )
      | ~ ( r1_xboole_0 @ X7 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('46',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ sk_C_1 @ X0 )
      | ~ ( r2_hidden @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ sk_D @ ( k3_xboole_0 @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['43','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ sk_D @ ( k3_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['33','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ sk_B @ sk_A ) @ X0 ) ),
    inference(clc,[status(thm)],['32','48'])).

thf('50',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ sk_B @ sk_A ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('53',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X13 @ X14 ) @ X15 )
      = ( k3_xboole_0 @ X13 @ ( k3_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf('54',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X13 @ X14 ) @ X15 )
      = ( k3_xboole_0 @ X13 @ ( k3_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('57',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X2 @ X1 ) )
      = ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_B @ ( k3_xboole_0 @ X0 @ sk_A ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['51','54','57'])).

thf('59',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_A )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['16','58'])).

thf('60',plain,(
    ! [X2: $i,X4: $i] :
      ( ( r1_xboole_0 @ X2 @ X4 )
      | ( ( k3_xboole_0 @ X2 @ X4 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('61',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_xboole_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    r1_xboole_0 @ sk_B @ sk_A ),
    inference(simplify,[status(thm)],['61'])).

thf(t78_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) )
        = ( k3_xboole_0 @ A @ C ) ) ) )).

thf('63',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( r1_xboole_0 @ X23 @ X24 )
      | ( ( k3_xboole_0 @ X23 @ ( k2_xboole_0 @ X24 @ X25 ) )
        = ( k3_xboole_0 @ X23 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t78_xboole_1])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_A @ X0 ) )
      = ( k3_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( ( k3_xboole_0 @ sk_B @ X0 )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ ( k2_xboole_0 @ sk_A @ X0 ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_xboole_0 @ ( k2_xboole_0 @ sk_A @ sk_C_1 ) @ sk_B ) ),
    inference('sup-',[status(thm)],['5','66'])).

thf('68',plain,(
    r1_xboole_0 @ ( k2_xboole_0 @ sk_A @ sk_C_1 ) @ sk_B ),
    inference(simplify,[status(thm)],['67'])).

thf('69',plain,(
    $false ),
    inference(demod,[status(thm)],['0','68'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.xvUTCHvBes
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:19:16 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.36/1.60  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.36/1.60  % Solved by: fo/fo7.sh
% 1.36/1.60  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.36/1.60  % done 2551 iterations in 1.132s
% 1.36/1.60  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.36/1.60  % SZS output start Refutation
% 1.36/1.60  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 1.36/1.60  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.36/1.60  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 1.36/1.60  thf(sk_D_type, type, sk_D: $i).
% 1.36/1.60  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.36/1.60  thf(sk_A_type, type, sk_A: $i).
% 1.36/1.60  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.36/1.60  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.36/1.60  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.36/1.60  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 1.36/1.60  thf(sk_B_type, type, sk_B: $i).
% 1.36/1.60  thf(sk_C_1_type, type, sk_C_1: $i).
% 1.36/1.60  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.36/1.60  thf(t149_zfmisc_1, conjecture,
% 1.36/1.60    (![A:$i,B:$i,C:$i,D:$i]:
% 1.36/1.60     ( ( ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k1_tarski @ D ) ) & 
% 1.36/1.60         ( r2_hidden @ D @ C ) & ( r1_xboole_0 @ C @ B ) ) =>
% 1.36/1.60       ( r1_xboole_0 @ ( k2_xboole_0 @ A @ C ) @ B ) ))).
% 1.36/1.60  thf(zf_stmt_0, negated_conjecture,
% 1.36/1.60    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 1.36/1.60        ( ( ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k1_tarski @ D ) ) & 
% 1.36/1.60            ( r2_hidden @ D @ C ) & ( r1_xboole_0 @ C @ B ) ) =>
% 1.36/1.60          ( r1_xboole_0 @ ( k2_xboole_0 @ A @ C ) @ B ) ) )),
% 1.36/1.60    inference('cnf.neg', [status(esa)], [t149_zfmisc_1])).
% 1.36/1.60  thf('0', plain, (~ (r1_xboole_0 @ (k2_xboole_0 @ sk_A @ sk_C_1) @ sk_B)),
% 1.36/1.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.36/1.60  thf('1', plain, ((r1_xboole_0 @ sk_C_1 @ sk_B)),
% 1.36/1.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.36/1.60  thf(d7_xboole_0, axiom,
% 1.36/1.60    (![A:$i,B:$i]:
% 1.36/1.60     ( ( r1_xboole_0 @ A @ B ) <=>
% 1.36/1.60       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 1.36/1.60  thf('2', plain,
% 1.36/1.60      (![X2 : $i, X3 : $i]:
% 1.36/1.60         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 1.36/1.60      inference('cnf', [status(esa)], [d7_xboole_0])).
% 1.36/1.60  thf('3', plain, (((k3_xboole_0 @ sk_C_1 @ sk_B) = (k1_xboole_0))),
% 1.36/1.60      inference('sup-', [status(thm)], ['1', '2'])).
% 1.36/1.60  thf(commutativity_k3_xboole_0, axiom,
% 1.36/1.60    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 1.36/1.60  thf('4', plain,
% 1.36/1.60      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.36/1.60      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.36/1.60  thf('5', plain, (((k3_xboole_0 @ sk_B @ sk_C_1) = (k1_xboole_0))),
% 1.36/1.60      inference('demod', [status(thm)], ['3', '4'])).
% 1.36/1.60  thf(t3_boole, axiom,
% 1.36/1.60    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 1.36/1.60  thf('6', plain, (![X16 : $i]: ((k4_xboole_0 @ X16 @ k1_xboole_0) = (X16))),
% 1.36/1.60      inference('cnf', [status(esa)], [t3_boole])).
% 1.36/1.60  thf(t48_xboole_1, axiom,
% 1.36/1.60    (![A:$i,B:$i]:
% 1.36/1.60     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 1.36/1.60  thf('7', plain,
% 1.36/1.60      (![X17 : $i, X18 : $i]:
% 1.36/1.60         ((k4_xboole_0 @ X17 @ (k4_xboole_0 @ X17 @ X18))
% 1.36/1.60           = (k3_xboole_0 @ X17 @ X18))),
% 1.36/1.60      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.36/1.60  thf('8', plain,
% 1.36/1.60      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 1.36/1.60      inference('sup+', [status(thm)], ['6', '7'])).
% 1.36/1.60  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 1.36/1.60  thf('9', plain, (![X22 : $i]: (r1_xboole_0 @ X22 @ k1_xboole_0)),
% 1.36/1.60      inference('cnf', [status(esa)], [t65_xboole_1])).
% 1.36/1.60  thf('10', plain,
% 1.36/1.60      (![X2 : $i, X3 : $i]:
% 1.36/1.60         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 1.36/1.60      inference('cnf', [status(esa)], [d7_xboole_0])).
% 1.36/1.60  thf('11', plain,
% 1.36/1.60      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 1.36/1.60      inference('sup-', [status(thm)], ['9', '10'])).
% 1.36/1.60  thf('12', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 1.36/1.60      inference('demod', [status(thm)], ['8', '11'])).
% 1.36/1.60  thf('13', plain,
% 1.36/1.60      (![X17 : $i, X18 : $i]:
% 1.36/1.60         ((k4_xboole_0 @ X17 @ (k4_xboole_0 @ X17 @ X18))
% 1.36/1.60           = (k3_xboole_0 @ X17 @ X18))),
% 1.36/1.60      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.36/1.60  thf('14', plain,
% 1.36/1.60      (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k3_xboole_0 @ X0 @ X0))),
% 1.36/1.60      inference('sup+', [status(thm)], ['12', '13'])).
% 1.36/1.60  thf('15', plain, (![X16 : $i]: ((k4_xboole_0 @ X16 @ k1_xboole_0) = (X16))),
% 1.36/1.60      inference('cnf', [status(esa)], [t3_boole])).
% 1.36/1.60  thf('16', plain, (![X0 : $i]: ((X0) = (k3_xboole_0 @ X0 @ X0))),
% 1.36/1.60      inference('demod', [status(thm)], ['14', '15'])).
% 1.36/1.60  thf(l27_zfmisc_1, axiom,
% 1.36/1.60    (![A:$i,B:$i]:
% 1.36/1.60     ( ( ~( r2_hidden @ A @ B ) ) => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ))).
% 1.36/1.60  thf('17', plain,
% 1.36/1.60      (![X34 : $i, X35 : $i]:
% 1.36/1.60         ((r1_xboole_0 @ (k1_tarski @ X34) @ X35) | (r2_hidden @ X34 @ X35))),
% 1.36/1.60      inference('cnf', [status(esa)], [l27_zfmisc_1])).
% 1.36/1.60  thf('18', plain,
% 1.36/1.60      ((r1_tarski @ (k3_xboole_0 @ sk_A @ sk_B) @ (k1_tarski @ sk_D))),
% 1.36/1.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.36/1.60  thf('19', plain,
% 1.36/1.60      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.36/1.60      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.36/1.60  thf('20', plain,
% 1.36/1.60      ((r1_tarski @ (k3_xboole_0 @ sk_B @ sk_A) @ (k1_tarski @ sk_D))),
% 1.36/1.60      inference('demod', [status(thm)], ['18', '19'])).
% 1.36/1.60  thf(t63_xboole_1, axiom,
% 1.36/1.60    (![A:$i,B:$i,C:$i]:
% 1.36/1.60     ( ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ B @ C ) ) =>
% 1.36/1.60       ( r1_xboole_0 @ A @ C ) ))).
% 1.36/1.60  thf('21', plain,
% 1.36/1.60      (![X19 : $i, X20 : $i, X21 : $i]:
% 1.36/1.60         (~ (r1_tarski @ X19 @ X20)
% 1.36/1.60          | ~ (r1_xboole_0 @ X20 @ X21)
% 1.36/1.60          | (r1_xboole_0 @ X19 @ X21))),
% 1.36/1.60      inference('cnf', [status(esa)], [t63_xboole_1])).
% 1.36/1.60  thf('22', plain,
% 1.36/1.60      (![X0 : $i]:
% 1.36/1.60         ((r1_xboole_0 @ (k3_xboole_0 @ sk_B @ sk_A) @ X0)
% 1.36/1.60          | ~ (r1_xboole_0 @ (k1_tarski @ sk_D) @ X0))),
% 1.36/1.60      inference('sup-', [status(thm)], ['20', '21'])).
% 1.36/1.60  thf('23', plain,
% 1.36/1.60      (![X0 : $i]:
% 1.36/1.60         ((r2_hidden @ sk_D @ X0)
% 1.36/1.60          | (r1_xboole_0 @ (k3_xboole_0 @ sk_B @ sk_A) @ X0))),
% 1.36/1.60      inference('sup-', [status(thm)], ['17', '22'])).
% 1.36/1.60  thf(symmetry_r1_xboole_0, axiom,
% 1.36/1.60    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 1.36/1.60  thf('24', plain,
% 1.36/1.60      (![X5 : $i, X6 : $i]:
% 1.36/1.60         ((r1_xboole_0 @ X5 @ X6) | ~ (r1_xboole_0 @ X6 @ X5))),
% 1.36/1.60      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 1.36/1.60  thf('25', plain,
% 1.36/1.60      (![X0 : $i]:
% 1.36/1.60         ((r2_hidden @ sk_D @ X0)
% 1.36/1.60          | (r1_xboole_0 @ X0 @ (k3_xboole_0 @ sk_B @ sk_A)))),
% 1.36/1.60      inference('sup-', [status(thm)], ['23', '24'])).
% 1.36/1.60  thf(t3_xboole_0, axiom,
% 1.36/1.60    (![A:$i,B:$i]:
% 1.36/1.60     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 1.36/1.60            ( r1_xboole_0 @ A @ B ) ) ) & 
% 1.36/1.60       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 1.36/1.60            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 1.36/1.60  thf('26', plain,
% 1.36/1.60      (![X7 : $i, X8 : $i]:
% 1.36/1.60         ((r1_xboole_0 @ X7 @ X8) | (r2_hidden @ (sk_C @ X8 @ X7) @ X7))),
% 1.36/1.60      inference('cnf', [status(esa)], [t3_xboole_0])).
% 1.36/1.60  thf('27', plain,
% 1.36/1.60      (![X7 : $i, X8 : $i]:
% 1.36/1.60         ((r1_xboole_0 @ X7 @ X8) | (r2_hidden @ (sk_C @ X8 @ X7) @ X7))),
% 1.36/1.60      inference('cnf', [status(esa)], [t3_xboole_0])).
% 1.36/1.60  thf('28', plain,
% 1.36/1.60      (![X7 : $i, X9 : $i, X10 : $i]:
% 1.36/1.60         (~ (r2_hidden @ X9 @ X7)
% 1.36/1.60          | ~ (r2_hidden @ X9 @ X10)
% 1.36/1.60          | ~ (r1_xboole_0 @ X7 @ X10))),
% 1.36/1.60      inference('cnf', [status(esa)], [t3_xboole_0])).
% 1.36/1.60  thf('29', plain,
% 1.36/1.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.36/1.60         ((r1_xboole_0 @ X0 @ X1)
% 1.36/1.60          | ~ (r1_xboole_0 @ X0 @ X2)
% 1.36/1.60          | ~ (r2_hidden @ (sk_C @ X1 @ X0) @ X2))),
% 1.36/1.60      inference('sup-', [status(thm)], ['27', '28'])).
% 1.36/1.60  thf('30', plain,
% 1.36/1.60      (![X0 : $i, X1 : $i]:
% 1.36/1.60         ((r1_xboole_0 @ X0 @ X1)
% 1.36/1.60          | ~ (r1_xboole_0 @ X0 @ X0)
% 1.36/1.60          | (r1_xboole_0 @ X0 @ X1))),
% 1.36/1.60      inference('sup-', [status(thm)], ['26', '29'])).
% 1.36/1.60  thf('31', plain,
% 1.36/1.60      (![X0 : $i, X1 : $i]:
% 1.36/1.60         (~ (r1_xboole_0 @ X0 @ X0) | (r1_xboole_0 @ X0 @ X1))),
% 1.36/1.60      inference('simplify', [status(thm)], ['30'])).
% 1.36/1.60  thf('32', plain,
% 1.36/1.60      (![X0 : $i]:
% 1.36/1.60         ((r2_hidden @ sk_D @ (k3_xboole_0 @ sk_B @ sk_A))
% 1.36/1.60          | (r1_xboole_0 @ (k3_xboole_0 @ sk_B @ sk_A) @ X0))),
% 1.36/1.60      inference('sup-', [status(thm)], ['25', '31'])).
% 1.36/1.60  thf('33', plain,
% 1.36/1.60      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.36/1.60      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.36/1.60  thf('34', plain, (((k3_xboole_0 @ sk_B @ sk_C_1) = (k1_xboole_0))),
% 1.36/1.60      inference('demod', [status(thm)], ['3', '4'])).
% 1.36/1.60  thf(t16_xboole_1, axiom,
% 1.36/1.60    (![A:$i,B:$i,C:$i]:
% 1.36/1.60     ( ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) =
% 1.36/1.60       ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 1.36/1.60  thf('35', plain,
% 1.36/1.60      (![X13 : $i, X14 : $i, X15 : $i]:
% 1.36/1.60         ((k3_xboole_0 @ (k3_xboole_0 @ X13 @ X14) @ X15)
% 1.36/1.60           = (k3_xboole_0 @ X13 @ (k3_xboole_0 @ X14 @ X15)))),
% 1.36/1.60      inference('cnf', [status(esa)], [t16_xboole_1])).
% 1.36/1.60  thf('36', plain,
% 1.36/1.60      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.36/1.60      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.36/1.60  thf('37', plain,
% 1.36/1.60      (![X2 : $i, X4 : $i]:
% 1.36/1.60         ((r1_xboole_0 @ X2 @ X4) | ((k3_xboole_0 @ X2 @ X4) != (k1_xboole_0)))),
% 1.36/1.60      inference('cnf', [status(esa)], [d7_xboole_0])).
% 1.36/1.60  thf('38', plain,
% 1.36/1.60      (![X0 : $i, X1 : $i]:
% 1.36/1.60         (((k3_xboole_0 @ X1 @ X0) != (k1_xboole_0)) | (r1_xboole_0 @ X0 @ X1))),
% 1.36/1.60      inference('sup-', [status(thm)], ['36', '37'])).
% 1.36/1.60  thf('39', plain,
% 1.36/1.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.36/1.60         (((k3_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0)) != (k1_xboole_0))
% 1.36/1.60          | (r1_xboole_0 @ X0 @ (k3_xboole_0 @ X2 @ X1)))),
% 1.36/1.60      inference('sup-', [status(thm)], ['35', '38'])).
% 1.36/1.60  thf('40', plain,
% 1.36/1.60      (![X0 : $i]:
% 1.36/1.60         (((k3_xboole_0 @ X0 @ k1_xboole_0) != (k1_xboole_0))
% 1.36/1.60          | (r1_xboole_0 @ sk_C_1 @ (k3_xboole_0 @ X0 @ sk_B)))),
% 1.36/1.60      inference('sup-', [status(thm)], ['34', '39'])).
% 1.36/1.60  thf('41', plain,
% 1.36/1.60      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 1.36/1.60      inference('sup-', [status(thm)], ['9', '10'])).
% 1.36/1.60  thf('42', plain,
% 1.36/1.60      (![X0 : $i]:
% 1.36/1.60         (((k1_xboole_0) != (k1_xboole_0))
% 1.36/1.60          | (r1_xboole_0 @ sk_C_1 @ (k3_xboole_0 @ X0 @ sk_B)))),
% 1.36/1.60      inference('demod', [status(thm)], ['40', '41'])).
% 1.36/1.60  thf('43', plain,
% 1.36/1.60      (![X0 : $i]: (r1_xboole_0 @ sk_C_1 @ (k3_xboole_0 @ X0 @ sk_B))),
% 1.36/1.60      inference('simplify', [status(thm)], ['42'])).
% 1.36/1.60  thf('44', plain, ((r2_hidden @ sk_D @ sk_C_1)),
% 1.36/1.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.36/1.60  thf('45', plain,
% 1.36/1.60      (![X7 : $i, X9 : $i, X10 : $i]:
% 1.36/1.60         (~ (r2_hidden @ X9 @ X7)
% 1.36/1.60          | ~ (r2_hidden @ X9 @ X10)
% 1.36/1.60          | ~ (r1_xboole_0 @ X7 @ X10))),
% 1.36/1.60      inference('cnf', [status(esa)], [t3_xboole_0])).
% 1.36/1.60  thf('46', plain,
% 1.36/1.60      (![X0 : $i]: (~ (r1_xboole_0 @ sk_C_1 @ X0) | ~ (r2_hidden @ sk_D @ X0))),
% 1.36/1.60      inference('sup-', [status(thm)], ['44', '45'])).
% 1.36/1.60  thf('47', plain,
% 1.36/1.60      (![X0 : $i]: ~ (r2_hidden @ sk_D @ (k3_xboole_0 @ X0 @ sk_B))),
% 1.36/1.60      inference('sup-', [status(thm)], ['43', '46'])).
% 1.36/1.60  thf('48', plain,
% 1.36/1.60      (![X0 : $i]: ~ (r2_hidden @ sk_D @ (k3_xboole_0 @ sk_B @ X0))),
% 1.36/1.60      inference('sup-', [status(thm)], ['33', '47'])).
% 1.36/1.60  thf('49', plain,
% 1.36/1.60      (![X0 : $i]: (r1_xboole_0 @ (k3_xboole_0 @ sk_B @ sk_A) @ X0)),
% 1.36/1.60      inference('clc', [status(thm)], ['32', '48'])).
% 1.36/1.60  thf('50', plain,
% 1.36/1.60      (![X2 : $i, X3 : $i]:
% 1.36/1.60         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 1.36/1.60      inference('cnf', [status(esa)], [d7_xboole_0])).
% 1.36/1.60  thf('51', plain,
% 1.36/1.60      (![X0 : $i]:
% 1.36/1.60         ((k3_xboole_0 @ (k3_xboole_0 @ sk_B @ sk_A) @ X0) = (k1_xboole_0))),
% 1.36/1.60      inference('sup-', [status(thm)], ['49', '50'])).
% 1.36/1.60  thf('52', plain,
% 1.36/1.60      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.36/1.60      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.36/1.60  thf('53', plain,
% 1.36/1.60      (![X13 : $i, X14 : $i, X15 : $i]:
% 1.36/1.60         ((k3_xboole_0 @ (k3_xboole_0 @ X13 @ X14) @ X15)
% 1.36/1.60           = (k3_xboole_0 @ X13 @ (k3_xboole_0 @ X14 @ X15)))),
% 1.36/1.60      inference('cnf', [status(esa)], [t16_xboole_1])).
% 1.36/1.60  thf('54', plain,
% 1.36/1.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.36/1.60         ((k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 1.36/1.60           = (k3_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X2)))),
% 1.36/1.60      inference('sup+', [status(thm)], ['52', '53'])).
% 1.36/1.60  thf('55', plain,
% 1.36/1.60      (![X13 : $i, X14 : $i, X15 : $i]:
% 1.36/1.60         ((k3_xboole_0 @ (k3_xboole_0 @ X13 @ X14) @ X15)
% 1.36/1.60           = (k3_xboole_0 @ X13 @ (k3_xboole_0 @ X14 @ X15)))),
% 1.36/1.60      inference('cnf', [status(esa)], [t16_xboole_1])).
% 1.36/1.60  thf('56', plain,
% 1.36/1.60      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.36/1.60      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.36/1.60  thf('57', plain,
% 1.36/1.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.36/1.60         ((k3_xboole_0 @ X0 @ (k3_xboole_0 @ X2 @ X1))
% 1.36/1.60           = (k3_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0)))),
% 1.36/1.60      inference('sup+', [status(thm)], ['55', '56'])).
% 1.36/1.60  thf('58', plain,
% 1.36/1.60      (![X0 : $i]:
% 1.36/1.60         ((k3_xboole_0 @ sk_B @ (k3_xboole_0 @ X0 @ sk_A)) = (k1_xboole_0))),
% 1.36/1.60      inference('demod', [status(thm)], ['51', '54', '57'])).
% 1.36/1.60  thf('59', plain, (((k3_xboole_0 @ sk_B @ sk_A) = (k1_xboole_0))),
% 1.36/1.60      inference('sup+', [status(thm)], ['16', '58'])).
% 1.36/1.60  thf('60', plain,
% 1.36/1.60      (![X2 : $i, X4 : $i]:
% 1.36/1.60         ((r1_xboole_0 @ X2 @ X4) | ((k3_xboole_0 @ X2 @ X4) != (k1_xboole_0)))),
% 1.36/1.60      inference('cnf', [status(esa)], [d7_xboole_0])).
% 1.36/1.60  thf('61', plain,
% 1.36/1.60      ((((k1_xboole_0) != (k1_xboole_0)) | (r1_xboole_0 @ sk_B @ sk_A))),
% 1.36/1.60      inference('sup-', [status(thm)], ['59', '60'])).
% 1.36/1.60  thf('62', plain, ((r1_xboole_0 @ sk_B @ sk_A)),
% 1.36/1.60      inference('simplify', [status(thm)], ['61'])).
% 1.36/1.60  thf(t78_xboole_1, axiom,
% 1.36/1.60    (![A:$i,B:$i,C:$i]:
% 1.36/1.60     ( ( r1_xboole_0 @ A @ B ) =>
% 1.36/1.60       ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) =
% 1.36/1.60         ( k3_xboole_0 @ A @ C ) ) ))).
% 1.36/1.60  thf('63', plain,
% 1.36/1.60      (![X23 : $i, X24 : $i, X25 : $i]:
% 1.36/1.60         (~ (r1_xboole_0 @ X23 @ X24)
% 1.36/1.60          | ((k3_xboole_0 @ X23 @ (k2_xboole_0 @ X24 @ X25))
% 1.36/1.60              = (k3_xboole_0 @ X23 @ X25)))),
% 1.36/1.60      inference('cnf', [status(esa)], [t78_xboole_1])).
% 1.36/1.60  thf('64', plain,
% 1.36/1.60      (![X0 : $i]:
% 1.36/1.60         ((k3_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_A @ X0))
% 1.36/1.60           = (k3_xboole_0 @ sk_B @ X0))),
% 1.36/1.60      inference('sup-', [status(thm)], ['62', '63'])).
% 1.36/1.60  thf('65', plain,
% 1.36/1.60      (![X0 : $i, X1 : $i]:
% 1.36/1.60         (((k3_xboole_0 @ X1 @ X0) != (k1_xboole_0)) | (r1_xboole_0 @ X0 @ X1))),
% 1.36/1.60      inference('sup-', [status(thm)], ['36', '37'])).
% 1.36/1.60  thf('66', plain,
% 1.36/1.60      (![X0 : $i]:
% 1.36/1.60         (((k3_xboole_0 @ sk_B @ X0) != (k1_xboole_0))
% 1.36/1.60          | (r1_xboole_0 @ (k2_xboole_0 @ sk_A @ X0) @ sk_B))),
% 1.36/1.60      inference('sup-', [status(thm)], ['64', '65'])).
% 1.36/1.60  thf('67', plain,
% 1.36/1.60      ((((k1_xboole_0) != (k1_xboole_0))
% 1.36/1.60        | (r1_xboole_0 @ (k2_xboole_0 @ sk_A @ sk_C_1) @ sk_B))),
% 1.36/1.60      inference('sup-', [status(thm)], ['5', '66'])).
% 1.36/1.60  thf('68', plain, ((r1_xboole_0 @ (k2_xboole_0 @ sk_A @ sk_C_1) @ sk_B)),
% 1.36/1.60      inference('simplify', [status(thm)], ['67'])).
% 1.36/1.60  thf('69', plain, ($false), inference('demod', [status(thm)], ['0', '68'])).
% 1.36/1.60  
% 1.36/1.60  % SZS output end Refutation
% 1.36/1.60  
% 1.36/1.61  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
