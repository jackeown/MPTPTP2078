%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.qLHenUIRXy

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:37:51 EST 2020

% Result     : Theorem 6.74s
% Output     : Refutation 6.74s
% Verified   : 
% Statistics : Number of formulae       :  109 ( 144 expanded)
%              Number of leaves         :   30 (  53 expanded)
%              Depth                    :   15
%              Number of atoms          :  805 (1267 expanded)
%              Number of equality atoms :   47 (  62 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(t41_subset_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( r1_tarski @ ( k3_subset_1 @ A @ ( k4_subset_1 @ A @ B @ C ) ) @ ( k3_subset_1 @ A @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
       => ! [C: $i] :
            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
           => ( r1_tarski @ ( k3_subset_1 @ A @ ( k4_subset_1 @ A @ B @ C ) ) @ ( k3_subset_1 @ A @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t41_subset_1])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ ( k4_subset_1 @ sk_A @ sk_B @ sk_C_1 ) ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('3',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ X39 ) )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ X39 ) )
      | ( ( k4_subset_1 @ X39 @ X38 @ X40 )
        = ( k2_xboole_0 @ X38 @ X40 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ sk_A @ sk_B @ X0 )
        = ( k2_xboole_0 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,
    ( ( k4_subset_1 @ sk_A @ sk_B @ sk_C_1 )
    = ( k2_xboole_0 @ sk_B @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('7',plain,
    ( ( k4_subset_1 @ sk_A @ sk_B @ sk_C_1 )
    = ( k2_xboole_0 @ sk_C_1 @ sk_B ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,(
    ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ ( k2_xboole_0 @ sk_C_1 @ sk_B ) ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['0','7'])).

thf('9',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('10',plain,(
    ! [X31: $i,X32: $i] :
      ( ( ( k3_subset_1 @ X31 @ X32 )
        = ( k4_xboole_0 @ X31 @ X32 ) )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('11',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C_1 )
    = ( k4_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('12',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X14 @ X15 ) @ X16 )
      = ( k4_xboole_0 @ X14 @ ( k2_xboole_0 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ X0 )
      = ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_C_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    ! [X31: $i,X32: $i] :
      ( ( ( k3_subset_1 @ X31 @ X32 )
        = ( k4_xboole_0 @ X31 @ X32 ) )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('16',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('18',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X14 @ X15 ) @ X16 )
      = ( k4_xboole_0 @ X14 @ ( k2_xboole_0 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('19',plain,(
    ! [X10: $i,X11: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X10 @ X11 ) @ X10 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) @ ( k4_xboole_0 @ X2 @ X1 ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) @ ( k4_xboole_0 @ X2 @ X0 ) ) ),
    inference('sup+',[status(thm)],['17','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ X0 @ sk_B ) ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['16','21'])).

thf('23',plain,(
    r1_tarski @ ( k4_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ sk_B ) @ ( k3_subset_1 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['13','22'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('24',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_tarski @ X2 @ X3 )
      | ( X2 != X3 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('25',plain,(
    ! [X3: $i] :
      ( r1_tarski @ X3 @ X3 ) ),
    inference(simplify,[status(thm)],['24'])).

thf(t43_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) )
     => ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ) )).

thf('26',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X17 @ X18 ) @ X19 )
      | ~ ( r1_tarski @ X17 @ ( k2_xboole_0 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t43_xboole_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 ) @ X0 ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('29',plain,(
    ! [X33: $i,X34: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X33 @ X34 ) @ ( k1_zfmisc_1 @ X33 ) )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('30',plain,(
    m1_subset_1 @ ( k3_subset_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X31: $i,X32: $i] :
      ( ( ( k3_subset_1 @ X31 @ X32 )
        = ( k4_xboole_0 @ X31 @ X32 ) )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('32',plain,
    ( ( k3_subset_1 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = ( k4_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('34',plain,(
    ! [X36: $i,X37: $i] :
      ( ( ( k3_subset_1 @ X37 @ ( k3_subset_1 @ X37 @ X36 ) )
        = X36 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ X37 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('35',plain,
    ( ( k3_subset_1 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = sk_B ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,
    ( sk_B
    = ( k4_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['32','35'])).

thf(t106_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) )
     => ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ A @ C ) ) ) )).

thf('37',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( r1_tarski @ X5 @ X6 )
      | ~ ( r1_tarski @ X5 @ ( k4_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t106_xboole_1])).

thf('38',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_B )
      | ( r1_tarski @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ sk_B ) @ X0 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['27','38'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('40',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k2_xboole_0 @ X9 @ X8 )
        = X8 )
      | ~ ( r1_tarski @ X9 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ sk_B ) @ X0 ) @ sk_A )
      = sk_A ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ sk_A @ ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ sk_B ) @ X0 ) )
      = sk_A ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('45',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X28 @ X29 )
      | ( r2_hidden @ X28 @ X29 )
      | ( v1_xboole_0 @ X29 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('46',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('47',plain,(
    ! [X35: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('48',plain,(
    r2_hidden @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['46','47'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('49',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( r2_hidden @ X26 @ X25 )
      | ( r1_tarski @ X26 @ X24 )
      | ( X25
       != ( k1_zfmisc_1 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('50',plain,(
    ! [X24: $i,X26: $i] :
      ( ( r1_tarski @ X26 @ X24 )
      | ~ ( r2_hidden @ X26 @ ( k1_zfmisc_1 @ X24 ) ) ) ),
    inference(simplify,[status(thm)],['49'])).

thf('51',plain,(
    r1_tarski @ sk_C_1 @ sk_A ),
    inference('sup-',[status(thm)],['48','50'])).

thf('52',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k2_xboole_0 @ X9 @ X8 )
        = X8 )
      | ~ ( r1_tarski @ X9 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('53',plain,
    ( ( k2_xboole_0 @ sk_C_1 @ sk_A )
    = sk_A ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X14 @ X15 ) @ X16 )
      = ( k4_xboole_0 @ X14 @ ( k2_xboole_0 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('55',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k2_xboole_0 @ X12 @ ( k4_xboole_0 @ X13 @ X12 ) )
      = ( k2_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('56',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      = ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ sk_A @ ( k4_xboole_0 @ X0 @ sk_A ) )
      = ( k2_xboole_0 @ sk_A @ ( k4_xboole_0 @ X0 @ sk_C_1 ) ) ) ),
    inference('sup+',[status(thm)],['53','56'])).

thf('58',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k2_xboole_0 @ X12 @ ( k4_xboole_0 @ X13 @ X12 ) )
      = ( k2_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ sk_A @ X0 )
      = ( k2_xboole_0 @ sk_A @ ( k4_xboole_0 @ X0 @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,
    ( ( k2_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_C_1 @ sk_B ) )
    = sk_A ),
    inference('sup+',[status(thm)],['43','59'])).

thf('61',plain,(
    ! [X10: $i,X11: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X10 @ X11 ) @ X10 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(t44_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('62',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( r1_tarski @ X20 @ ( k2_xboole_0 @ X21 @ X22 ) )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ X20 @ X21 ) @ X22 ) ) ),
    inference(cnf,[status(esa)],[t44_xboole_1])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( r1_tarski @ X23 @ X24 )
      | ( r2_hidden @ X23 @ X25 )
      | ( X25
       != ( k1_zfmisc_1 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('65',plain,(
    ! [X23: $i,X24: $i] :
      ( ( r2_hidden @ X23 @ ( k1_zfmisc_1 @ X24 ) )
      | ~ ( r1_tarski @ X23 @ X24 ) ) ),
    inference(simplify,[status(thm)],['64'])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['63','65'])).

thf('67',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( r2_hidden @ X28 @ X29 )
      | ( m1_subset_1 @ X28 @ X29 )
      | ( v1_xboole_0 @ X29 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X35: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['68','69'])).

thf('71',plain,(
    m1_subset_1 @ ( k2_xboole_0 @ sk_C_1 @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['60','70'])).

thf('72',plain,(
    ! [X31: $i,X32: $i] :
      ( ( ( k3_subset_1 @ X31 @ X32 )
        = ( k4_xboole_0 @ X31 @ X32 ) )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('73',plain,
    ( ( k3_subset_1 @ sk_A @ ( k2_xboole_0 @ sk_C_1 @ sk_B ) )
    = ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_C_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ X0 )
      = ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_C_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('75',plain,
    ( ( k3_subset_1 @ sk_A @ ( k2_xboole_0 @ sk_C_1 @ sk_B ) )
    = ( k4_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ sk_B ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('76',plain,(
    r1_tarski @ ( k3_subset_1 @ sk_A @ ( k2_xboole_0 @ sk_C_1 @ sk_B ) ) @ ( k3_subset_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['23','75'])).

thf('77',plain,(
    $false ),
    inference(demod,[status(thm)],['8','76'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.qLHenUIRXy
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:05:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 6.74/6.97  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 6.74/6.97  % Solved by: fo/fo7.sh
% 6.74/6.97  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 6.74/6.97  % done 6804 iterations in 6.519s
% 6.74/6.97  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 6.74/6.97  % SZS output start Refutation
% 6.74/6.97  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 6.74/6.97  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 6.74/6.97  thf(sk_C_1_type, type, sk_C_1: $i).
% 6.74/6.97  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 6.74/6.97  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 6.74/6.97  thf(sk_A_type, type, sk_A: $i).
% 6.74/6.97  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 6.74/6.97  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 6.74/6.97  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 6.74/6.97  thf(sk_B_type, type, sk_B: $i).
% 6.74/6.97  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 6.74/6.97  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 6.74/6.97  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 6.74/6.97  thf(t41_subset_1, conjecture,
% 6.74/6.97    (![A:$i,B:$i]:
% 6.74/6.97     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 6.74/6.97       ( ![C:$i]:
% 6.74/6.97         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 6.74/6.97           ( r1_tarski @
% 6.74/6.97             ( k3_subset_1 @ A @ ( k4_subset_1 @ A @ B @ C ) ) @ 
% 6.74/6.97             ( k3_subset_1 @ A @ B ) ) ) ) ))).
% 6.74/6.97  thf(zf_stmt_0, negated_conjecture,
% 6.74/6.97    (~( ![A:$i,B:$i]:
% 6.74/6.97        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 6.74/6.97          ( ![C:$i]:
% 6.74/6.97            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 6.74/6.97              ( r1_tarski @
% 6.74/6.97                ( k3_subset_1 @ A @ ( k4_subset_1 @ A @ B @ C ) ) @ 
% 6.74/6.97                ( k3_subset_1 @ A @ B ) ) ) ) ) )),
% 6.74/6.97    inference('cnf.neg', [status(esa)], [t41_subset_1])).
% 6.74/6.97  thf('0', plain,
% 6.74/6.97      (~ (r1_tarski @ 
% 6.74/6.97          (k3_subset_1 @ sk_A @ (k4_subset_1 @ sk_A @ sk_B @ sk_C_1)) @ 
% 6.74/6.97          (k3_subset_1 @ sk_A @ sk_B))),
% 6.74/6.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.74/6.97  thf('1', plain, ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 6.74/6.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.74/6.97  thf('2', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 6.74/6.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.74/6.97  thf(redefinition_k4_subset_1, axiom,
% 6.74/6.97    (![A:$i,B:$i,C:$i]:
% 6.74/6.97     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 6.74/6.97         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 6.74/6.97       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 6.74/6.97  thf('3', plain,
% 6.74/6.97      (![X38 : $i, X39 : $i, X40 : $i]:
% 6.74/6.97         (~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ X39))
% 6.74/6.97          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ X39))
% 6.74/6.97          | ((k4_subset_1 @ X39 @ X38 @ X40) = (k2_xboole_0 @ X38 @ X40)))),
% 6.74/6.97      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 6.74/6.97  thf('4', plain,
% 6.74/6.97      (![X0 : $i]:
% 6.74/6.97         (((k4_subset_1 @ sk_A @ sk_B @ X0) = (k2_xboole_0 @ sk_B @ X0))
% 6.74/6.97          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A)))),
% 6.74/6.97      inference('sup-', [status(thm)], ['2', '3'])).
% 6.74/6.97  thf('5', plain,
% 6.74/6.97      (((k4_subset_1 @ sk_A @ sk_B @ sk_C_1) = (k2_xboole_0 @ sk_B @ sk_C_1))),
% 6.74/6.97      inference('sup-', [status(thm)], ['1', '4'])).
% 6.74/6.97  thf(commutativity_k2_xboole_0, axiom,
% 6.74/6.97    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 6.74/6.97  thf('6', plain,
% 6.74/6.97      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 6.74/6.97      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 6.74/6.97  thf('7', plain,
% 6.74/6.97      (((k4_subset_1 @ sk_A @ sk_B @ sk_C_1) = (k2_xboole_0 @ sk_C_1 @ sk_B))),
% 6.74/6.97      inference('demod', [status(thm)], ['5', '6'])).
% 6.74/6.97  thf('8', plain,
% 6.74/6.97      (~ (r1_tarski @ (k3_subset_1 @ sk_A @ (k2_xboole_0 @ sk_C_1 @ sk_B)) @ 
% 6.74/6.97          (k3_subset_1 @ sk_A @ sk_B))),
% 6.74/6.97      inference('demod', [status(thm)], ['0', '7'])).
% 6.74/6.97  thf('9', plain, ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 6.74/6.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.74/6.97  thf(d5_subset_1, axiom,
% 6.74/6.97    (![A:$i,B:$i]:
% 6.74/6.97     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 6.74/6.97       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 6.74/6.97  thf('10', plain,
% 6.74/6.97      (![X31 : $i, X32 : $i]:
% 6.74/6.97         (((k3_subset_1 @ X31 @ X32) = (k4_xboole_0 @ X31 @ X32))
% 6.74/6.97          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ X31)))),
% 6.74/6.97      inference('cnf', [status(esa)], [d5_subset_1])).
% 6.74/6.97  thf('11', plain,
% 6.74/6.97      (((k3_subset_1 @ sk_A @ sk_C_1) = (k4_xboole_0 @ sk_A @ sk_C_1))),
% 6.74/6.97      inference('sup-', [status(thm)], ['9', '10'])).
% 6.74/6.97  thf(t41_xboole_1, axiom,
% 6.74/6.97    (![A:$i,B:$i,C:$i]:
% 6.74/6.97     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 6.74/6.97       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 6.74/6.97  thf('12', plain,
% 6.74/6.97      (![X14 : $i, X15 : $i, X16 : $i]:
% 6.74/6.97         ((k4_xboole_0 @ (k4_xboole_0 @ X14 @ X15) @ X16)
% 6.74/6.97           = (k4_xboole_0 @ X14 @ (k2_xboole_0 @ X15 @ X16)))),
% 6.74/6.97      inference('cnf', [status(esa)], [t41_xboole_1])).
% 6.74/6.97  thf('13', plain,
% 6.74/6.97      (![X0 : $i]:
% 6.74/6.97         ((k4_xboole_0 @ (k3_subset_1 @ sk_A @ sk_C_1) @ X0)
% 6.74/6.97           = (k4_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_C_1 @ X0)))),
% 6.74/6.97      inference('sup+', [status(thm)], ['11', '12'])).
% 6.74/6.97  thf('14', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 6.74/6.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.74/6.97  thf('15', plain,
% 6.74/6.97      (![X31 : $i, X32 : $i]:
% 6.74/6.97         (((k3_subset_1 @ X31 @ X32) = (k4_xboole_0 @ X31 @ X32))
% 6.74/6.97          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ X31)))),
% 6.74/6.97      inference('cnf', [status(esa)], [d5_subset_1])).
% 6.74/6.97  thf('16', plain,
% 6.74/6.97      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 6.74/6.97      inference('sup-', [status(thm)], ['14', '15'])).
% 6.74/6.97  thf('17', plain,
% 6.74/6.97      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 6.74/6.97      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 6.74/6.97  thf('18', plain,
% 6.74/6.97      (![X14 : $i, X15 : $i, X16 : $i]:
% 6.74/6.97         ((k4_xboole_0 @ (k4_xboole_0 @ X14 @ X15) @ X16)
% 6.74/6.97           = (k4_xboole_0 @ X14 @ (k2_xboole_0 @ X15 @ X16)))),
% 6.74/6.97      inference('cnf', [status(esa)], [t41_xboole_1])).
% 6.74/6.97  thf(t36_xboole_1, axiom,
% 6.74/6.97    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 6.74/6.97  thf('19', plain,
% 6.74/6.97      (![X10 : $i, X11 : $i]: (r1_tarski @ (k4_xboole_0 @ X10 @ X11) @ X10)),
% 6.74/6.97      inference('cnf', [status(esa)], [t36_xboole_1])).
% 6.74/6.97  thf('20', plain,
% 6.74/6.97      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.74/6.97         (r1_tarski @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)) @ 
% 6.74/6.97          (k4_xboole_0 @ X2 @ X1))),
% 6.74/6.97      inference('sup+', [status(thm)], ['18', '19'])).
% 6.74/6.97  thf('21', plain,
% 6.74/6.97      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.74/6.97         (r1_tarski @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)) @ 
% 6.74/6.97          (k4_xboole_0 @ X2 @ X0))),
% 6.74/6.97      inference('sup+', [status(thm)], ['17', '20'])).
% 6.74/6.97  thf('22', plain,
% 6.74/6.97      (![X0 : $i]:
% 6.74/6.97         (r1_tarski @ (k4_xboole_0 @ sk_A @ (k2_xboole_0 @ X0 @ sk_B)) @ 
% 6.74/6.97          (k3_subset_1 @ sk_A @ sk_B))),
% 6.74/6.97      inference('sup+', [status(thm)], ['16', '21'])).
% 6.74/6.97  thf('23', plain,
% 6.74/6.97      ((r1_tarski @ (k4_xboole_0 @ (k3_subset_1 @ sk_A @ sk_C_1) @ sk_B) @ 
% 6.74/6.97        (k3_subset_1 @ sk_A @ sk_B))),
% 6.74/6.97      inference('sup+', [status(thm)], ['13', '22'])).
% 6.74/6.97  thf(d10_xboole_0, axiom,
% 6.74/6.97    (![A:$i,B:$i]:
% 6.74/6.97     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 6.74/6.97  thf('24', plain,
% 6.74/6.97      (![X2 : $i, X3 : $i]: ((r1_tarski @ X2 @ X3) | ((X2) != (X3)))),
% 6.74/6.97      inference('cnf', [status(esa)], [d10_xboole_0])).
% 6.74/6.97  thf('25', plain, (![X3 : $i]: (r1_tarski @ X3 @ X3)),
% 6.74/6.97      inference('simplify', [status(thm)], ['24'])).
% 6.74/6.97  thf(t43_xboole_1, axiom,
% 6.74/6.97    (![A:$i,B:$i,C:$i]:
% 6.74/6.97     ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) =>
% 6.74/6.97       ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ))).
% 6.74/6.97  thf('26', plain,
% 6.74/6.97      (![X17 : $i, X18 : $i, X19 : $i]:
% 6.74/6.97         ((r1_tarski @ (k4_xboole_0 @ X17 @ X18) @ X19)
% 6.74/6.97          | ~ (r1_tarski @ X17 @ (k2_xboole_0 @ X18 @ X19)))),
% 6.74/6.97      inference('cnf', [status(esa)], [t43_xboole_1])).
% 6.74/6.97  thf('27', plain,
% 6.74/6.97      (![X0 : $i, X1 : $i]:
% 6.74/6.97         (r1_tarski @ (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1) @ X0)),
% 6.74/6.97      inference('sup-', [status(thm)], ['25', '26'])).
% 6.74/6.97  thf('28', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 6.74/6.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.74/6.97  thf(dt_k3_subset_1, axiom,
% 6.74/6.97    (![A:$i,B:$i]:
% 6.74/6.97     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 6.74/6.97       ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 6.74/6.97  thf('29', plain,
% 6.74/6.97      (![X33 : $i, X34 : $i]:
% 6.74/6.97         ((m1_subset_1 @ (k3_subset_1 @ X33 @ X34) @ (k1_zfmisc_1 @ X33))
% 6.74/6.97          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ X33)))),
% 6.74/6.97      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 6.74/6.97  thf('30', plain,
% 6.74/6.97      ((m1_subset_1 @ (k3_subset_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_A))),
% 6.74/6.97      inference('sup-', [status(thm)], ['28', '29'])).
% 6.74/6.97  thf('31', plain,
% 6.74/6.97      (![X31 : $i, X32 : $i]:
% 6.74/6.97         (((k3_subset_1 @ X31 @ X32) = (k4_xboole_0 @ X31 @ X32))
% 6.74/6.97          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ X31)))),
% 6.74/6.97      inference('cnf', [status(esa)], [d5_subset_1])).
% 6.74/6.97  thf('32', plain,
% 6.74/6.97      (((k3_subset_1 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B))
% 6.74/6.97         = (k4_xboole_0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B)))),
% 6.74/6.97      inference('sup-', [status(thm)], ['30', '31'])).
% 6.74/6.97  thf('33', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 6.74/6.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.74/6.97  thf(involutiveness_k3_subset_1, axiom,
% 6.74/6.97    (![A:$i,B:$i]:
% 6.74/6.97     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 6.74/6.97       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 6.74/6.97  thf('34', plain,
% 6.74/6.97      (![X36 : $i, X37 : $i]:
% 6.74/6.97         (((k3_subset_1 @ X37 @ (k3_subset_1 @ X37 @ X36)) = (X36))
% 6.74/6.97          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ X37)))),
% 6.74/6.97      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 6.74/6.97  thf('35', plain,
% 6.74/6.97      (((k3_subset_1 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B)) = (sk_B))),
% 6.74/6.97      inference('sup-', [status(thm)], ['33', '34'])).
% 6.74/6.97  thf('36', plain,
% 6.74/6.97      (((sk_B) = (k4_xboole_0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B)))),
% 6.74/6.97      inference('demod', [status(thm)], ['32', '35'])).
% 6.74/6.97  thf(t106_xboole_1, axiom,
% 6.74/6.97    (![A:$i,B:$i,C:$i]:
% 6.74/6.97     ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) =>
% 6.74/6.97       ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ))).
% 6.74/6.97  thf('37', plain,
% 6.74/6.97      (![X5 : $i, X6 : $i, X7 : $i]:
% 6.74/6.97         ((r1_tarski @ X5 @ X6) | ~ (r1_tarski @ X5 @ (k4_xboole_0 @ X6 @ X7)))),
% 6.74/6.97      inference('cnf', [status(esa)], [t106_xboole_1])).
% 6.74/6.97  thf('38', plain,
% 6.74/6.97      (![X0 : $i]: (~ (r1_tarski @ X0 @ sk_B) | (r1_tarski @ X0 @ sk_A))),
% 6.74/6.97      inference('sup-', [status(thm)], ['36', '37'])).
% 6.74/6.97  thf('39', plain,
% 6.74/6.97      (![X0 : $i]:
% 6.74/6.97         (r1_tarski @ (k4_xboole_0 @ (k2_xboole_0 @ X0 @ sk_B) @ X0) @ sk_A)),
% 6.74/6.97      inference('sup-', [status(thm)], ['27', '38'])).
% 6.74/6.97  thf(t12_xboole_1, axiom,
% 6.74/6.97    (![A:$i,B:$i]:
% 6.74/6.97     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 6.74/6.97  thf('40', plain,
% 6.74/6.97      (![X8 : $i, X9 : $i]:
% 6.74/6.97         (((k2_xboole_0 @ X9 @ X8) = (X8)) | ~ (r1_tarski @ X9 @ X8))),
% 6.74/6.97      inference('cnf', [status(esa)], [t12_xboole_1])).
% 6.74/6.97  thf('41', plain,
% 6.74/6.97      (![X0 : $i]:
% 6.74/6.97         ((k2_xboole_0 @ (k4_xboole_0 @ (k2_xboole_0 @ X0 @ sk_B) @ X0) @ sk_A)
% 6.74/6.97           = (sk_A))),
% 6.74/6.97      inference('sup-', [status(thm)], ['39', '40'])).
% 6.74/6.97  thf('42', plain,
% 6.74/6.97      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 6.74/6.97      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 6.74/6.97  thf('43', plain,
% 6.74/6.97      (![X0 : $i]:
% 6.74/6.97         ((k2_xboole_0 @ sk_A @ (k4_xboole_0 @ (k2_xboole_0 @ X0 @ sk_B) @ X0))
% 6.74/6.97           = (sk_A))),
% 6.74/6.97      inference('demod', [status(thm)], ['41', '42'])).
% 6.74/6.97  thf('44', plain, ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 6.74/6.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.74/6.97  thf(d2_subset_1, axiom,
% 6.74/6.97    (![A:$i,B:$i]:
% 6.74/6.97     ( ( ( v1_xboole_0 @ A ) =>
% 6.74/6.97         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 6.74/6.97       ( ( ~( v1_xboole_0 @ A ) ) =>
% 6.74/6.97         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 6.74/6.97  thf('45', plain,
% 6.74/6.97      (![X28 : $i, X29 : $i]:
% 6.74/6.97         (~ (m1_subset_1 @ X28 @ X29)
% 6.74/6.97          | (r2_hidden @ X28 @ X29)
% 6.74/6.97          | (v1_xboole_0 @ X29))),
% 6.74/6.97      inference('cnf', [status(esa)], [d2_subset_1])).
% 6.74/6.97  thf('46', plain,
% 6.74/6.97      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 6.74/6.97        | (r2_hidden @ sk_C_1 @ (k1_zfmisc_1 @ sk_A)))),
% 6.74/6.97      inference('sup-', [status(thm)], ['44', '45'])).
% 6.74/6.97  thf(fc1_subset_1, axiom,
% 6.74/6.97    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 6.74/6.97  thf('47', plain, (![X35 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X35))),
% 6.74/6.97      inference('cnf', [status(esa)], [fc1_subset_1])).
% 6.74/6.97  thf('48', plain, ((r2_hidden @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 6.74/6.97      inference('clc', [status(thm)], ['46', '47'])).
% 6.74/6.97  thf(d1_zfmisc_1, axiom,
% 6.74/6.97    (![A:$i,B:$i]:
% 6.74/6.97     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 6.74/6.97       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 6.74/6.97  thf('49', plain,
% 6.74/6.97      (![X24 : $i, X25 : $i, X26 : $i]:
% 6.74/6.97         (~ (r2_hidden @ X26 @ X25)
% 6.74/6.97          | (r1_tarski @ X26 @ X24)
% 6.74/6.97          | ((X25) != (k1_zfmisc_1 @ X24)))),
% 6.74/6.97      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 6.74/6.97  thf('50', plain,
% 6.74/6.97      (![X24 : $i, X26 : $i]:
% 6.74/6.97         ((r1_tarski @ X26 @ X24) | ~ (r2_hidden @ X26 @ (k1_zfmisc_1 @ X24)))),
% 6.74/6.97      inference('simplify', [status(thm)], ['49'])).
% 6.74/6.97  thf('51', plain, ((r1_tarski @ sk_C_1 @ sk_A)),
% 6.74/6.97      inference('sup-', [status(thm)], ['48', '50'])).
% 6.74/6.97  thf('52', plain,
% 6.74/6.97      (![X8 : $i, X9 : $i]:
% 6.74/6.97         (((k2_xboole_0 @ X9 @ X8) = (X8)) | ~ (r1_tarski @ X9 @ X8))),
% 6.74/6.97      inference('cnf', [status(esa)], [t12_xboole_1])).
% 6.74/6.97  thf('53', plain, (((k2_xboole_0 @ sk_C_1 @ sk_A) = (sk_A))),
% 6.74/6.97      inference('sup-', [status(thm)], ['51', '52'])).
% 6.74/6.97  thf('54', plain,
% 6.74/6.97      (![X14 : $i, X15 : $i, X16 : $i]:
% 6.74/6.97         ((k4_xboole_0 @ (k4_xboole_0 @ X14 @ X15) @ X16)
% 6.74/6.97           = (k4_xboole_0 @ X14 @ (k2_xboole_0 @ X15 @ X16)))),
% 6.74/6.97      inference('cnf', [status(esa)], [t41_xboole_1])).
% 6.74/6.97  thf(t39_xboole_1, axiom,
% 6.74/6.97    (![A:$i,B:$i]:
% 6.74/6.97     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 6.74/6.97  thf('55', plain,
% 6.74/6.97      (![X12 : $i, X13 : $i]:
% 6.74/6.97         ((k2_xboole_0 @ X12 @ (k4_xboole_0 @ X13 @ X12))
% 6.74/6.97           = (k2_xboole_0 @ X12 @ X13))),
% 6.74/6.97      inference('cnf', [status(esa)], [t39_xboole_1])).
% 6.74/6.97  thf('56', plain,
% 6.74/6.97      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.74/6.97         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))
% 6.74/6.97           = (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ X1)))),
% 6.74/6.97      inference('sup+', [status(thm)], ['54', '55'])).
% 6.74/6.97  thf('57', plain,
% 6.74/6.97      (![X0 : $i]:
% 6.74/6.97         ((k2_xboole_0 @ sk_A @ (k4_xboole_0 @ X0 @ sk_A))
% 6.74/6.97           = (k2_xboole_0 @ sk_A @ (k4_xboole_0 @ X0 @ sk_C_1)))),
% 6.74/6.97      inference('sup+', [status(thm)], ['53', '56'])).
% 6.74/6.97  thf('58', plain,
% 6.74/6.97      (![X12 : $i, X13 : $i]:
% 6.74/6.97         ((k2_xboole_0 @ X12 @ (k4_xboole_0 @ X13 @ X12))
% 6.74/6.97           = (k2_xboole_0 @ X12 @ X13))),
% 6.74/6.97      inference('cnf', [status(esa)], [t39_xboole_1])).
% 6.74/6.97  thf('59', plain,
% 6.74/6.97      (![X0 : $i]:
% 6.74/6.97         ((k2_xboole_0 @ sk_A @ X0)
% 6.74/6.97           = (k2_xboole_0 @ sk_A @ (k4_xboole_0 @ X0 @ sk_C_1)))),
% 6.74/6.97      inference('demod', [status(thm)], ['57', '58'])).
% 6.74/6.97  thf('60', plain,
% 6.74/6.97      (((k2_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_C_1 @ sk_B)) = (sk_A))),
% 6.74/6.97      inference('sup+', [status(thm)], ['43', '59'])).
% 6.74/6.97  thf('61', plain,
% 6.74/6.97      (![X10 : $i, X11 : $i]: (r1_tarski @ (k4_xboole_0 @ X10 @ X11) @ X10)),
% 6.74/6.97      inference('cnf', [status(esa)], [t36_xboole_1])).
% 6.74/6.97  thf(t44_xboole_1, axiom,
% 6.74/6.97    (![A:$i,B:$i,C:$i]:
% 6.74/6.97     ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) =>
% 6.74/6.97       ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 6.74/6.97  thf('62', plain,
% 6.74/6.97      (![X20 : $i, X21 : $i, X22 : $i]:
% 6.74/6.97         ((r1_tarski @ X20 @ (k2_xboole_0 @ X21 @ X22))
% 6.74/6.97          | ~ (r1_tarski @ (k4_xboole_0 @ X20 @ X21) @ X22))),
% 6.74/6.97      inference('cnf', [status(esa)], [t44_xboole_1])).
% 6.74/6.97  thf('63', plain,
% 6.74/6.97      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 6.74/6.97      inference('sup-', [status(thm)], ['61', '62'])).
% 6.74/6.97  thf('64', plain,
% 6.74/6.97      (![X23 : $i, X24 : $i, X25 : $i]:
% 6.74/6.97         (~ (r1_tarski @ X23 @ X24)
% 6.74/6.97          | (r2_hidden @ X23 @ X25)
% 6.74/6.97          | ((X25) != (k1_zfmisc_1 @ X24)))),
% 6.74/6.97      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 6.74/6.97  thf('65', plain,
% 6.74/6.97      (![X23 : $i, X24 : $i]:
% 6.74/6.97         ((r2_hidden @ X23 @ (k1_zfmisc_1 @ X24)) | ~ (r1_tarski @ X23 @ X24))),
% 6.74/6.97      inference('simplify', [status(thm)], ['64'])).
% 6.74/6.97  thf('66', plain,
% 6.74/6.97      (![X0 : $i, X1 : $i]:
% 6.74/6.97         (r2_hidden @ X0 @ (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))),
% 6.74/6.97      inference('sup-', [status(thm)], ['63', '65'])).
% 6.74/6.97  thf('67', plain,
% 6.74/6.97      (![X28 : $i, X29 : $i]:
% 6.74/6.97         (~ (r2_hidden @ X28 @ X29)
% 6.74/6.97          | (m1_subset_1 @ X28 @ X29)
% 6.74/6.97          | (v1_xboole_0 @ X29))),
% 6.74/6.97      inference('cnf', [status(esa)], [d2_subset_1])).
% 6.74/6.97  thf('68', plain,
% 6.74/6.97      (![X0 : $i, X1 : $i]:
% 6.74/6.97         ((v1_xboole_0 @ (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))
% 6.74/6.97          | (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0))))),
% 6.74/6.97      inference('sup-', [status(thm)], ['66', '67'])).
% 6.74/6.97  thf('69', plain, (![X35 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X35))),
% 6.74/6.97      inference('cnf', [status(esa)], [fc1_subset_1])).
% 6.74/6.97  thf('70', plain,
% 6.74/6.97      (![X0 : $i, X1 : $i]:
% 6.74/6.97         (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))),
% 6.74/6.97      inference('clc', [status(thm)], ['68', '69'])).
% 6.74/6.97  thf('71', plain,
% 6.74/6.97      ((m1_subset_1 @ (k2_xboole_0 @ sk_C_1 @ sk_B) @ (k1_zfmisc_1 @ sk_A))),
% 6.74/6.97      inference('sup+', [status(thm)], ['60', '70'])).
% 6.74/6.97  thf('72', plain,
% 6.74/6.97      (![X31 : $i, X32 : $i]:
% 6.74/6.97         (((k3_subset_1 @ X31 @ X32) = (k4_xboole_0 @ X31 @ X32))
% 6.74/6.97          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ X31)))),
% 6.74/6.97      inference('cnf', [status(esa)], [d5_subset_1])).
% 6.74/6.97  thf('73', plain,
% 6.74/6.97      (((k3_subset_1 @ sk_A @ (k2_xboole_0 @ sk_C_1 @ sk_B))
% 6.74/6.97         = (k4_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_C_1 @ sk_B)))),
% 6.74/6.97      inference('sup-', [status(thm)], ['71', '72'])).
% 6.74/6.97  thf('74', plain,
% 6.74/6.97      (![X0 : $i]:
% 6.74/6.97         ((k4_xboole_0 @ (k3_subset_1 @ sk_A @ sk_C_1) @ X0)
% 6.74/6.97           = (k4_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_C_1 @ X0)))),
% 6.74/6.97      inference('sup+', [status(thm)], ['11', '12'])).
% 6.74/6.97  thf('75', plain,
% 6.74/6.97      (((k3_subset_1 @ sk_A @ (k2_xboole_0 @ sk_C_1 @ sk_B))
% 6.74/6.97         = (k4_xboole_0 @ (k3_subset_1 @ sk_A @ sk_C_1) @ sk_B))),
% 6.74/6.97      inference('demod', [status(thm)], ['73', '74'])).
% 6.74/6.97  thf('76', plain,
% 6.74/6.97      ((r1_tarski @ (k3_subset_1 @ sk_A @ (k2_xboole_0 @ sk_C_1 @ sk_B)) @ 
% 6.74/6.97        (k3_subset_1 @ sk_A @ sk_B))),
% 6.74/6.97      inference('demod', [status(thm)], ['23', '75'])).
% 6.74/6.97  thf('77', plain, ($false), inference('demod', [status(thm)], ['8', '76'])).
% 6.74/6.97  
% 6.74/6.97  % SZS output end Refutation
% 6.74/6.97  
% 6.74/6.98  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
