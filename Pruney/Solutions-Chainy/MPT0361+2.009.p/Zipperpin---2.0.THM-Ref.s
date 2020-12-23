%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ICw5KHzIWB

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:37:51 EST 2020

% Result     : Theorem 30.99s
% Output     : Refutation 30.99s
% Verified   : 
% Statistics : Number of formulae       :  109 ( 264 expanded)
%              Number of leaves         :   26 (  90 expanded)
%              Depth                    :   17
%              Number of atoms          :  767 (2097 expanded)
%              Number of equality atoms :   40 (  99 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

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
    ! [X32: $i,X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ X33 ) )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ X33 ) )
      | ( ( k4_subset_1 @ X33 @ X32 @ X34 )
        = ( k2_xboole_0 @ X32 @ X34 ) ) ) ),
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

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('10',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X26 @ X27 )
      | ( r2_hidden @ X26 @ X27 )
      | ( v1_xboole_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('11',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('12',plain,(
    ! [X31: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('13',plain,(
    r2_hidden @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['11','12'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('14',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( r2_hidden @ X24 @ X23 )
      | ( r1_tarski @ X24 @ X22 )
      | ( X23
       != ( k1_zfmisc_1 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('15',plain,(
    ! [X22: $i,X24: $i] :
      ( ( r1_tarski @ X24 @ X22 )
      | ~ ( r2_hidden @ X24 @ ( k1_zfmisc_1 @ X22 ) ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    r1_tarski @ sk_C_1 @ sk_A ),
    inference('sup-',[status(thm)],['13','15'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('17',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k2_xboole_0 @ X9 @ X8 )
        = X8 )
      | ~ ( r1_tarski @ X9 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('18',plain,
    ( ( k2_xboole_0 @ sk_C_1 @ sk_A )
    = sk_A ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X26 @ X27 )
      | ( r2_hidden @ X26 @ X27 )
      | ( v1_xboole_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('21',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X31: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('23',plain,(
    r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X22: $i,X24: $i] :
      ( ( r1_tarski @ X24 @ X22 )
      | ~ ( r2_hidden @ X24 @ ( k1_zfmisc_1 @ X22 ) ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('25',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k2_xboole_0 @ X9 @ X8 )
        = X8 )
      | ~ ( r1_tarski @ X9 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('27',plain,
    ( ( k2_xboole_0 @ sk_B @ sk_A )
    = sk_A ),
    inference('sup-',[status(thm)],['25','26'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('28',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_tarski @ X2 @ X3 )
      | ( X2 != X3 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('29',plain,(
    ! [X3: $i] :
      ( r1_tarski @ X3 @ X3 ) ),
    inference(simplify,[status(thm)],['28'])).

thf(t43_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) )
     => ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ) )).

thf('30',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X13 @ X14 ) @ X15 )
      | ~ ( r1_tarski @ X13 @ ( k2_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t43_xboole_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 ) @ X0 ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k2_xboole_0 @ X9 @ X8 )
        = X8 )
      | ~ ( r1_tarski @ X9 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 ) @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['33','34'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('36',plain,(
    ! [X19: $i,X20: $i] :
      ( r1_tarski @ X19 @ ( k2_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('37',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( r1_tarski @ X21 @ X22 )
      | ( r2_hidden @ X21 @ X23 )
      | ( X23
       != ( k1_zfmisc_1 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('38',plain,(
    ! [X21: $i,X22: $i] :
      ( ( r2_hidden @ X21 @ ( k1_zfmisc_1 @ X22 ) )
      | ~ ( r1_tarski @ X21 @ X22 ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X1 @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['36','38'])).

thf('40',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( r2_hidden @ X26 @ X27 )
      | ( m1_subset_1 @ X26 @ X27 )
      | ( v1_xboole_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      | ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X31: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['41','42'])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('44',plain,(
    ! [X29: $i,X30: $i] :
      ( ( ( k3_subset_1 @ X29 @ X30 )
        = ( k4_xboole_0 @ X29 @ X30 ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_subset_1 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['35','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('49',plain,(
    ! [X19: $i,X20: $i] :
      ( r1_tarski @ X19 @ ( k2_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf(t10_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ) )).

thf('51',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r1_tarski @ X5 @ X6 )
      | ( r1_tarski @ X5 @ ( k2_xboole_0 @ X7 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t10_xboole_1])).

thf('52',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ X1 @ ( k2_xboole_0 @ ( k2_xboole_0 @ X2 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['47','52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k3_subset_1 @ ( k2_xboole_0 @ X2 @ X0 ) @ X2 ) @ ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['46','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k3_subset_1 @ ( k2_xboole_0 @ X0 @ sk_B ) @ X0 ) @ sk_A ) ),
    inference('sup+',[status(thm)],['27','54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf(t44_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('57',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( r1_tarski @ X16 @ ( k2_xboole_0 @ X17 @ X18 ) )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ X16 @ X17 ) @ X18 ) ) ),
    inference(cnf,[status(esa)],[t44_xboole_1])).

thf('58',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ ( k3_subset_1 @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 ) @ X2 )
      | ( r1_tarski @ ( k2_xboole_0 @ X0 @ X1 ) @ ( k2_xboole_0 @ X0 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ X0 @ sk_B ) @ ( k2_xboole_0 @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['55','58'])).

thf('60',plain,(
    r1_tarski @ ( k2_xboole_0 @ sk_C_1 @ sk_B ) @ sk_A ),
    inference('sup+',[status(thm)],['18','59'])).

thf('61',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k2_xboole_0 @ X9 @ X8 )
        = X8 )
      | ~ ( r1_tarski @ X9 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('62',plain,
    ( ( k2_xboole_0 @ ( k2_xboole_0 @ sk_C_1 @ sk_B ) @ sk_A )
    = sk_A ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('64',plain,
    ( ( k2_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_C_1 @ sk_B ) )
    = sk_A ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['41','42'])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X29: $i,X30: $i] :
      ( ( ( k3_subset_1 @ X29 @ X30 )
        = ( k4_xboole_0 @ X29 @ X30 ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,
    ( ( k3_subset_1 @ ( k2_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_C_1 @ sk_B ) ) @ ( k2_xboole_0 @ sk_C_1 @ sk_B ) )
    = ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_C_1 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['64','69'])).

thf('71',plain,
    ( ( k2_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_C_1 @ sk_B ) )
    = sk_A ),
    inference(demod,[status(thm)],['62','63'])).

thf('72',plain,
    ( ( k3_subset_1 @ sk_A @ ( k2_xboole_0 @ sk_C_1 @ sk_B ) )
    = ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_C_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['70','71'])).

thf('73',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    ! [X29: $i,X30: $i] :
      ( ( ( k3_subset_1 @ X29 @ X30 )
        = ( k4_xboole_0 @ X29 @ X30 ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('75',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf(t34_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ ( k4_xboole_0 @ C @ B ) @ ( k4_xboole_0 @ C @ A ) ) ) )).

thf('77',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( r1_tarski @ X10 @ X11 )
      | ( r1_tarski @ ( k4_xboole_0 @ X12 @ X11 ) @ ( k4_xboole_0 @ X12 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t34_xboole_1])).

thf('78',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) @ ( k4_xboole_0 @ X2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ X0 @ sk_B ) ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['75','78'])).

thf('80',plain,(
    r1_tarski @ ( k3_subset_1 @ sk_A @ ( k2_xboole_0 @ sk_C_1 @ sk_B ) ) @ ( k3_subset_1 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['72','79'])).

thf('81',plain,(
    $false ),
    inference(demod,[status(thm)],['8','80'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ICw5KHzIWB
% 0.14/0.35  % Computer   : n006.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 11:04:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.36  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 30.99/31.19  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 30.99/31.19  % Solved by: fo/fo7.sh
% 30.99/31.19  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 30.99/31.19  % done 29416 iterations in 30.716s
% 30.99/31.19  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 30.99/31.19  % SZS output start Refutation
% 30.99/31.19  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 30.99/31.19  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 30.99/31.19  thf(sk_A_type, type, sk_A: $i).
% 30.99/31.19  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 30.99/31.19  thf(sk_C_1_type, type, sk_C_1: $i).
% 30.99/31.19  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 30.99/31.19  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 30.99/31.19  thf(sk_B_type, type, sk_B: $i).
% 30.99/31.19  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 30.99/31.19  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 30.99/31.19  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 30.99/31.19  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 30.99/31.19  thf(t41_subset_1, conjecture,
% 30.99/31.19    (![A:$i,B:$i]:
% 30.99/31.19     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 30.99/31.19       ( ![C:$i]:
% 30.99/31.19         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 30.99/31.19           ( r1_tarski @
% 30.99/31.19             ( k3_subset_1 @ A @ ( k4_subset_1 @ A @ B @ C ) ) @ 
% 30.99/31.19             ( k3_subset_1 @ A @ B ) ) ) ) ))).
% 30.99/31.19  thf(zf_stmt_0, negated_conjecture,
% 30.99/31.19    (~( ![A:$i,B:$i]:
% 30.99/31.19        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 30.99/31.19          ( ![C:$i]:
% 30.99/31.19            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 30.99/31.19              ( r1_tarski @
% 30.99/31.19                ( k3_subset_1 @ A @ ( k4_subset_1 @ A @ B @ C ) ) @ 
% 30.99/31.19                ( k3_subset_1 @ A @ B ) ) ) ) ) )),
% 30.99/31.19    inference('cnf.neg', [status(esa)], [t41_subset_1])).
% 30.99/31.19  thf('0', plain,
% 30.99/31.19      (~ (r1_tarski @ 
% 30.99/31.19          (k3_subset_1 @ sk_A @ (k4_subset_1 @ sk_A @ sk_B @ sk_C_1)) @ 
% 30.99/31.19          (k3_subset_1 @ sk_A @ sk_B))),
% 30.99/31.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.99/31.19  thf('1', plain, ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 30.99/31.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.99/31.19  thf('2', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 30.99/31.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.99/31.19  thf(redefinition_k4_subset_1, axiom,
% 30.99/31.19    (![A:$i,B:$i,C:$i]:
% 30.99/31.19     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 30.99/31.19         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 30.99/31.19       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 30.99/31.19  thf('3', plain,
% 30.99/31.19      (![X32 : $i, X33 : $i, X34 : $i]:
% 30.99/31.19         (~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ X33))
% 30.99/31.19          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ X33))
% 30.99/31.19          | ((k4_subset_1 @ X33 @ X32 @ X34) = (k2_xboole_0 @ X32 @ X34)))),
% 30.99/31.19      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 30.99/31.19  thf('4', plain,
% 30.99/31.19      (![X0 : $i]:
% 30.99/31.19         (((k4_subset_1 @ sk_A @ sk_B @ X0) = (k2_xboole_0 @ sk_B @ X0))
% 30.99/31.19          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A)))),
% 30.99/31.19      inference('sup-', [status(thm)], ['2', '3'])).
% 30.99/31.19  thf('5', plain,
% 30.99/31.19      (((k4_subset_1 @ sk_A @ sk_B @ sk_C_1) = (k2_xboole_0 @ sk_B @ sk_C_1))),
% 30.99/31.19      inference('sup-', [status(thm)], ['1', '4'])).
% 30.99/31.19  thf(commutativity_k2_xboole_0, axiom,
% 30.99/31.19    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 30.99/31.19  thf('6', plain,
% 30.99/31.19      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 30.99/31.19      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 30.99/31.19  thf('7', plain,
% 30.99/31.19      (((k4_subset_1 @ sk_A @ sk_B @ sk_C_1) = (k2_xboole_0 @ sk_C_1 @ sk_B))),
% 30.99/31.19      inference('demod', [status(thm)], ['5', '6'])).
% 30.99/31.19  thf('8', plain,
% 30.99/31.19      (~ (r1_tarski @ (k3_subset_1 @ sk_A @ (k2_xboole_0 @ sk_C_1 @ sk_B)) @ 
% 30.99/31.19          (k3_subset_1 @ sk_A @ sk_B))),
% 30.99/31.19      inference('demod', [status(thm)], ['0', '7'])).
% 30.99/31.19  thf('9', plain, ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 30.99/31.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.99/31.19  thf(d2_subset_1, axiom,
% 30.99/31.19    (![A:$i,B:$i]:
% 30.99/31.19     ( ( ( v1_xboole_0 @ A ) =>
% 30.99/31.19         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 30.99/31.19       ( ( ~( v1_xboole_0 @ A ) ) =>
% 30.99/31.19         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 30.99/31.19  thf('10', plain,
% 30.99/31.19      (![X26 : $i, X27 : $i]:
% 30.99/31.19         (~ (m1_subset_1 @ X26 @ X27)
% 30.99/31.19          | (r2_hidden @ X26 @ X27)
% 30.99/31.19          | (v1_xboole_0 @ X27))),
% 30.99/31.19      inference('cnf', [status(esa)], [d2_subset_1])).
% 30.99/31.19  thf('11', plain,
% 30.99/31.19      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 30.99/31.19        | (r2_hidden @ sk_C_1 @ (k1_zfmisc_1 @ sk_A)))),
% 30.99/31.19      inference('sup-', [status(thm)], ['9', '10'])).
% 30.99/31.19  thf(fc1_subset_1, axiom,
% 30.99/31.19    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 30.99/31.19  thf('12', plain, (![X31 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X31))),
% 30.99/31.19      inference('cnf', [status(esa)], [fc1_subset_1])).
% 30.99/31.19  thf('13', plain, ((r2_hidden @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 30.99/31.19      inference('clc', [status(thm)], ['11', '12'])).
% 30.99/31.19  thf(d1_zfmisc_1, axiom,
% 30.99/31.19    (![A:$i,B:$i]:
% 30.99/31.19     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 30.99/31.19       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 30.99/31.19  thf('14', plain,
% 30.99/31.19      (![X22 : $i, X23 : $i, X24 : $i]:
% 30.99/31.19         (~ (r2_hidden @ X24 @ X23)
% 30.99/31.19          | (r1_tarski @ X24 @ X22)
% 30.99/31.19          | ((X23) != (k1_zfmisc_1 @ X22)))),
% 30.99/31.19      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 30.99/31.19  thf('15', plain,
% 30.99/31.19      (![X22 : $i, X24 : $i]:
% 30.99/31.19         ((r1_tarski @ X24 @ X22) | ~ (r2_hidden @ X24 @ (k1_zfmisc_1 @ X22)))),
% 30.99/31.19      inference('simplify', [status(thm)], ['14'])).
% 30.99/31.19  thf('16', plain, ((r1_tarski @ sk_C_1 @ sk_A)),
% 30.99/31.19      inference('sup-', [status(thm)], ['13', '15'])).
% 30.99/31.19  thf(t12_xboole_1, axiom,
% 30.99/31.19    (![A:$i,B:$i]:
% 30.99/31.19     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 30.99/31.19  thf('17', plain,
% 30.99/31.19      (![X8 : $i, X9 : $i]:
% 30.99/31.19         (((k2_xboole_0 @ X9 @ X8) = (X8)) | ~ (r1_tarski @ X9 @ X8))),
% 30.99/31.19      inference('cnf', [status(esa)], [t12_xboole_1])).
% 30.99/31.19  thf('18', plain, (((k2_xboole_0 @ sk_C_1 @ sk_A) = (sk_A))),
% 30.99/31.19      inference('sup-', [status(thm)], ['16', '17'])).
% 30.99/31.19  thf('19', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 30.99/31.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.99/31.19  thf('20', plain,
% 30.99/31.19      (![X26 : $i, X27 : $i]:
% 30.99/31.19         (~ (m1_subset_1 @ X26 @ X27)
% 30.99/31.19          | (r2_hidden @ X26 @ X27)
% 30.99/31.19          | (v1_xboole_0 @ X27))),
% 30.99/31.19      inference('cnf', [status(esa)], [d2_subset_1])).
% 30.99/31.19  thf('21', plain,
% 30.99/31.19      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 30.99/31.19        | (r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A)))),
% 30.99/31.19      inference('sup-', [status(thm)], ['19', '20'])).
% 30.99/31.19  thf('22', plain, (![X31 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X31))),
% 30.99/31.19      inference('cnf', [status(esa)], [fc1_subset_1])).
% 30.99/31.19  thf('23', plain, ((r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 30.99/31.19      inference('clc', [status(thm)], ['21', '22'])).
% 30.99/31.19  thf('24', plain,
% 30.99/31.19      (![X22 : $i, X24 : $i]:
% 30.99/31.19         ((r1_tarski @ X24 @ X22) | ~ (r2_hidden @ X24 @ (k1_zfmisc_1 @ X22)))),
% 30.99/31.19      inference('simplify', [status(thm)], ['14'])).
% 30.99/31.19  thf('25', plain, ((r1_tarski @ sk_B @ sk_A)),
% 30.99/31.19      inference('sup-', [status(thm)], ['23', '24'])).
% 30.99/31.19  thf('26', plain,
% 30.99/31.19      (![X8 : $i, X9 : $i]:
% 30.99/31.19         (((k2_xboole_0 @ X9 @ X8) = (X8)) | ~ (r1_tarski @ X9 @ X8))),
% 30.99/31.19      inference('cnf', [status(esa)], [t12_xboole_1])).
% 30.99/31.19  thf('27', plain, (((k2_xboole_0 @ sk_B @ sk_A) = (sk_A))),
% 30.99/31.19      inference('sup-', [status(thm)], ['25', '26'])).
% 30.99/31.19  thf(d10_xboole_0, axiom,
% 30.99/31.19    (![A:$i,B:$i]:
% 30.99/31.19     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 30.99/31.19  thf('28', plain,
% 30.99/31.19      (![X2 : $i, X3 : $i]: ((r1_tarski @ X2 @ X3) | ((X2) != (X3)))),
% 30.99/31.19      inference('cnf', [status(esa)], [d10_xboole_0])).
% 30.99/31.19  thf('29', plain, (![X3 : $i]: (r1_tarski @ X3 @ X3)),
% 30.99/31.20      inference('simplify', [status(thm)], ['28'])).
% 30.99/31.20  thf(t43_xboole_1, axiom,
% 30.99/31.20    (![A:$i,B:$i,C:$i]:
% 30.99/31.20     ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) =>
% 30.99/31.20       ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ))).
% 30.99/31.20  thf('30', plain,
% 30.99/31.20      (![X13 : $i, X14 : $i, X15 : $i]:
% 30.99/31.20         ((r1_tarski @ (k4_xboole_0 @ X13 @ X14) @ X15)
% 30.99/31.20          | ~ (r1_tarski @ X13 @ (k2_xboole_0 @ X14 @ X15)))),
% 30.99/31.20      inference('cnf', [status(esa)], [t43_xboole_1])).
% 30.99/31.20  thf('31', plain,
% 30.99/31.20      (![X0 : $i, X1 : $i]:
% 30.99/31.20         (r1_tarski @ (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1) @ X0)),
% 30.99/31.20      inference('sup-', [status(thm)], ['29', '30'])).
% 30.99/31.20  thf('32', plain,
% 30.99/31.20      (![X8 : $i, X9 : $i]:
% 30.99/31.20         (((k2_xboole_0 @ X9 @ X8) = (X8)) | ~ (r1_tarski @ X9 @ X8))),
% 30.99/31.20      inference('cnf', [status(esa)], [t12_xboole_1])).
% 30.99/31.20  thf('33', plain,
% 30.99/31.20      (![X0 : $i, X1 : $i]:
% 30.99/31.20         ((k2_xboole_0 @ (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1) @ X0)
% 30.99/31.20           = (X0))),
% 30.99/31.20      inference('sup-', [status(thm)], ['31', '32'])).
% 30.99/31.20  thf('34', plain,
% 30.99/31.20      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 30.99/31.20      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 30.99/31.20  thf('35', plain,
% 30.99/31.20      (![X0 : $i, X1 : $i]:
% 30.99/31.20         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1))
% 30.99/31.20           = (X0))),
% 30.99/31.20      inference('demod', [status(thm)], ['33', '34'])).
% 30.99/31.20  thf(t7_xboole_1, axiom,
% 30.99/31.20    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 30.99/31.20  thf('36', plain,
% 30.99/31.20      (![X19 : $i, X20 : $i]: (r1_tarski @ X19 @ (k2_xboole_0 @ X19 @ X20))),
% 30.99/31.20      inference('cnf', [status(esa)], [t7_xboole_1])).
% 30.99/31.20  thf('37', plain,
% 30.99/31.20      (![X21 : $i, X22 : $i, X23 : $i]:
% 30.99/31.20         (~ (r1_tarski @ X21 @ X22)
% 30.99/31.20          | (r2_hidden @ X21 @ X23)
% 30.99/31.20          | ((X23) != (k1_zfmisc_1 @ X22)))),
% 30.99/31.20      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 30.99/31.20  thf('38', plain,
% 30.99/31.20      (![X21 : $i, X22 : $i]:
% 30.99/31.20         ((r2_hidden @ X21 @ (k1_zfmisc_1 @ X22)) | ~ (r1_tarski @ X21 @ X22))),
% 30.99/31.20      inference('simplify', [status(thm)], ['37'])).
% 30.99/31.20  thf('39', plain,
% 30.99/31.20      (![X0 : $i, X1 : $i]:
% 30.99/31.20         (r2_hidden @ X1 @ (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))),
% 30.99/31.20      inference('sup-', [status(thm)], ['36', '38'])).
% 30.99/31.20  thf('40', plain,
% 30.99/31.20      (![X26 : $i, X27 : $i]:
% 30.99/31.20         (~ (r2_hidden @ X26 @ X27)
% 30.99/31.20          | (m1_subset_1 @ X26 @ X27)
% 30.99/31.20          | (v1_xboole_0 @ X27))),
% 30.99/31.20      inference('cnf', [status(esa)], [d2_subset_1])).
% 30.99/31.20  thf('41', plain,
% 30.99/31.20      (![X0 : $i, X1 : $i]:
% 30.99/31.20         ((v1_xboole_0 @ (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))
% 30.99/31.20          | (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0))))),
% 30.99/31.20      inference('sup-', [status(thm)], ['39', '40'])).
% 30.99/31.20  thf('42', plain, (![X31 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X31))),
% 30.99/31.20      inference('cnf', [status(esa)], [fc1_subset_1])).
% 30.99/31.20  thf('43', plain,
% 30.99/31.20      (![X0 : $i, X1 : $i]:
% 30.99/31.20         (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))),
% 30.99/31.20      inference('clc', [status(thm)], ['41', '42'])).
% 30.99/31.20  thf(d5_subset_1, axiom,
% 30.99/31.20    (![A:$i,B:$i]:
% 30.99/31.20     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 30.99/31.20       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 30.99/31.20  thf('44', plain,
% 30.99/31.20      (![X29 : $i, X30 : $i]:
% 30.99/31.20         (((k3_subset_1 @ X29 @ X30) = (k4_xboole_0 @ X29 @ X30))
% 30.99/31.20          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ X29)))),
% 30.99/31.20      inference('cnf', [status(esa)], [d5_subset_1])).
% 30.99/31.20  thf('45', plain,
% 30.99/31.20      (![X0 : $i, X1 : $i]:
% 30.99/31.20         ((k3_subset_1 @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 30.99/31.20           = (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1))),
% 30.99/31.20      inference('sup-', [status(thm)], ['43', '44'])).
% 30.99/31.20  thf('46', plain,
% 30.99/31.20      (![X0 : $i, X1 : $i]:
% 30.99/31.20         ((k2_xboole_0 @ X0 @ (k3_subset_1 @ (k2_xboole_0 @ X1 @ X0) @ X1))
% 30.99/31.20           = (X0))),
% 30.99/31.20      inference('demod', [status(thm)], ['35', '45'])).
% 30.99/31.20  thf('47', plain,
% 30.99/31.20      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 30.99/31.20      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 30.99/31.20  thf('48', plain,
% 30.99/31.20      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 30.99/31.20      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 30.99/31.20  thf('49', plain,
% 30.99/31.20      (![X19 : $i, X20 : $i]: (r1_tarski @ X19 @ (k2_xboole_0 @ X19 @ X20))),
% 30.99/31.20      inference('cnf', [status(esa)], [t7_xboole_1])).
% 30.99/31.20  thf('50', plain,
% 30.99/31.20      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 30.99/31.20      inference('sup+', [status(thm)], ['48', '49'])).
% 30.99/31.20  thf(t10_xboole_1, axiom,
% 30.99/31.20    (![A:$i,B:$i,C:$i]:
% 30.99/31.20     ( ( r1_tarski @ A @ B ) => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ))).
% 30.99/31.20  thf('51', plain,
% 30.99/31.20      (![X5 : $i, X6 : $i, X7 : $i]:
% 30.99/31.20         (~ (r1_tarski @ X5 @ X6) | (r1_tarski @ X5 @ (k2_xboole_0 @ X7 @ X6)))),
% 30.99/31.20      inference('cnf', [status(esa)], [t10_xboole_1])).
% 30.99/31.20  thf('52', plain,
% 30.99/31.20      (![X0 : $i, X1 : $i, X2 : $i]:
% 30.99/31.20         (r1_tarski @ X0 @ (k2_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))),
% 30.99/31.20      inference('sup-', [status(thm)], ['50', '51'])).
% 30.99/31.20  thf('53', plain,
% 30.99/31.20      (![X0 : $i, X1 : $i, X2 : $i]:
% 30.99/31.20         (r1_tarski @ X1 @ (k2_xboole_0 @ (k2_xboole_0 @ X2 @ X1) @ X0))),
% 30.99/31.20      inference('sup+', [status(thm)], ['47', '52'])).
% 30.99/31.20  thf('54', plain,
% 30.99/31.20      (![X0 : $i, X1 : $i, X2 : $i]:
% 30.99/31.20         (r1_tarski @ (k3_subset_1 @ (k2_xboole_0 @ X2 @ X0) @ X2) @ 
% 30.99/31.20          (k2_xboole_0 @ X0 @ X1))),
% 30.99/31.20      inference('sup+', [status(thm)], ['46', '53'])).
% 30.99/31.20  thf('55', plain,
% 30.99/31.20      (![X0 : $i]:
% 30.99/31.20         (r1_tarski @ (k3_subset_1 @ (k2_xboole_0 @ X0 @ sk_B) @ X0) @ sk_A)),
% 30.99/31.20      inference('sup+', [status(thm)], ['27', '54'])).
% 30.99/31.20  thf('56', plain,
% 30.99/31.20      (![X0 : $i, X1 : $i]:
% 30.99/31.20         ((k3_subset_1 @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 30.99/31.20           = (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1))),
% 30.99/31.20      inference('sup-', [status(thm)], ['43', '44'])).
% 30.99/31.20  thf(t44_xboole_1, axiom,
% 30.99/31.20    (![A:$i,B:$i,C:$i]:
% 30.99/31.20     ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) =>
% 30.99/31.20       ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 30.99/31.20  thf('57', plain,
% 30.99/31.20      (![X16 : $i, X17 : $i, X18 : $i]:
% 30.99/31.20         ((r1_tarski @ X16 @ (k2_xboole_0 @ X17 @ X18))
% 30.99/31.20          | ~ (r1_tarski @ (k4_xboole_0 @ X16 @ X17) @ X18))),
% 30.99/31.20      inference('cnf', [status(esa)], [t44_xboole_1])).
% 30.99/31.20  thf('58', plain,
% 30.99/31.20      (![X0 : $i, X1 : $i, X2 : $i]:
% 30.99/31.20         (~ (r1_tarski @ (k3_subset_1 @ (k2_xboole_0 @ X0 @ X1) @ X0) @ X2)
% 30.99/31.20          | (r1_tarski @ (k2_xboole_0 @ X0 @ X1) @ (k2_xboole_0 @ X0 @ X2)))),
% 30.99/31.20      inference('sup-', [status(thm)], ['56', '57'])).
% 30.99/31.20  thf('59', plain,
% 30.99/31.20      (![X0 : $i]:
% 30.99/31.20         (r1_tarski @ (k2_xboole_0 @ X0 @ sk_B) @ (k2_xboole_0 @ X0 @ sk_A))),
% 30.99/31.20      inference('sup-', [status(thm)], ['55', '58'])).
% 30.99/31.20  thf('60', plain, ((r1_tarski @ (k2_xboole_0 @ sk_C_1 @ sk_B) @ sk_A)),
% 30.99/31.20      inference('sup+', [status(thm)], ['18', '59'])).
% 30.99/31.20  thf('61', plain,
% 30.99/31.20      (![X8 : $i, X9 : $i]:
% 30.99/31.20         (((k2_xboole_0 @ X9 @ X8) = (X8)) | ~ (r1_tarski @ X9 @ X8))),
% 30.99/31.20      inference('cnf', [status(esa)], [t12_xboole_1])).
% 30.99/31.20  thf('62', plain,
% 30.99/31.20      (((k2_xboole_0 @ (k2_xboole_0 @ sk_C_1 @ sk_B) @ sk_A) = (sk_A))),
% 30.99/31.20      inference('sup-', [status(thm)], ['60', '61'])).
% 30.99/31.20  thf('63', plain,
% 30.99/31.20      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 30.99/31.20      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 30.99/31.20  thf('64', plain,
% 30.99/31.20      (((k2_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_C_1 @ sk_B)) = (sk_A))),
% 30.99/31.20      inference('demod', [status(thm)], ['62', '63'])).
% 30.99/31.20  thf('65', plain,
% 30.99/31.20      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 30.99/31.20      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 30.99/31.20  thf('66', plain,
% 30.99/31.20      (![X0 : $i, X1 : $i]:
% 30.99/31.20         (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))),
% 30.99/31.20      inference('clc', [status(thm)], ['41', '42'])).
% 30.99/31.20  thf('67', plain,
% 30.99/31.20      (![X0 : $i, X1 : $i]:
% 30.99/31.20         (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))),
% 30.99/31.20      inference('sup+', [status(thm)], ['65', '66'])).
% 30.99/31.20  thf('68', plain,
% 30.99/31.20      (![X29 : $i, X30 : $i]:
% 30.99/31.20         (((k3_subset_1 @ X29 @ X30) = (k4_xboole_0 @ X29 @ X30))
% 30.99/31.20          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ X29)))),
% 30.99/31.20      inference('cnf', [status(esa)], [d5_subset_1])).
% 30.99/31.20  thf('69', plain,
% 30.99/31.20      (![X0 : $i, X1 : $i]:
% 30.99/31.20         ((k3_subset_1 @ (k2_xboole_0 @ X1 @ X0) @ X0)
% 30.99/31.20           = (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X0))),
% 30.99/31.20      inference('sup-', [status(thm)], ['67', '68'])).
% 30.99/31.20  thf('70', plain,
% 30.99/31.20      (((k3_subset_1 @ (k2_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_C_1 @ sk_B)) @ 
% 30.99/31.20         (k2_xboole_0 @ sk_C_1 @ sk_B))
% 30.99/31.20         = (k4_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_C_1 @ sk_B)))),
% 30.99/31.20      inference('sup+', [status(thm)], ['64', '69'])).
% 30.99/31.20  thf('71', plain,
% 30.99/31.20      (((k2_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_C_1 @ sk_B)) = (sk_A))),
% 30.99/31.20      inference('demod', [status(thm)], ['62', '63'])).
% 30.99/31.20  thf('72', plain,
% 30.99/31.20      (((k3_subset_1 @ sk_A @ (k2_xboole_0 @ sk_C_1 @ sk_B))
% 30.99/31.20         = (k4_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_C_1 @ sk_B)))),
% 30.99/31.20      inference('demod', [status(thm)], ['70', '71'])).
% 30.99/31.20  thf('73', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 30.99/31.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.99/31.20  thf('74', plain,
% 30.99/31.20      (![X29 : $i, X30 : $i]:
% 30.99/31.20         (((k3_subset_1 @ X29 @ X30) = (k4_xboole_0 @ X29 @ X30))
% 30.99/31.20          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ X29)))),
% 30.99/31.20      inference('cnf', [status(esa)], [d5_subset_1])).
% 30.99/31.20  thf('75', plain,
% 30.99/31.20      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 30.99/31.20      inference('sup-', [status(thm)], ['73', '74'])).
% 30.99/31.20  thf('76', plain,
% 30.99/31.20      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 30.99/31.20      inference('sup+', [status(thm)], ['48', '49'])).
% 30.99/31.20  thf(t34_xboole_1, axiom,
% 30.99/31.20    (![A:$i,B:$i,C:$i]:
% 30.99/31.20     ( ( r1_tarski @ A @ B ) =>
% 30.99/31.20       ( r1_tarski @ ( k4_xboole_0 @ C @ B ) @ ( k4_xboole_0 @ C @ A ) ) ))).
% 30.99/31.20  thf('77', plain,
% 30.99/31.20      (![X10 : $i, X11 : $i, X12 : $i]:
% 30.99/31.20         (~ (r1_tarski @ X10 @ X11)
% 30.99/31.20          | (r1_tarski @ (k4_xboole_0 @ X12 @ X11) @ (k4_xboole_0 @ X12 @ X10)))),
% 30.99/31.20      inference('cnf', [status(esa)], [t34_xboole_1])).
% 30.99/31.20  thf('78', plain,
% 30.99/31.20      (![X0 : $i, X1 : $i, X2 : $i]:
% 30.99/31.20         (r1_tarski @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)) @ 
% 30.99/31.20          (k4_xboole_0 @ X2 @ X0))),
% 30.99/31.20      inference('sup-', [status(thm)], ['76', '77'])).
% 30.99/31.20  thf('79', plain,
% 30.99/31.20      (![X0 : $i]:
% 30.99/31.20         (r1_tarski @ (k4_xboole_0 @ sk_A @ (k2_xboole_0 @ X0 @ sk_B)) @ 
% 30.99/31.20          (k3_subset_1 @ sk_A @ sk_B))),
% 30.99/31.20      inference('sup+', [status(thm)], ['75', '78'])).
% 30.99/31.20  thf('80', plain,
% 30.99/31.20      ((r1_tarski @ (k3_subset_1 @ sk_A @ (k2_xboole_0 @ sk_C_1 @ sk_B)) @ 
% 30.99/31.20        (k3_subset_1 @ sk_A @ sk_B))),
% 30.99/31.20      inference('sup+', [status(thm)], ['72', '79'])).
% 30.99/31.20  thf('81', plain, ($false), inference('demod', [status(thm)], ['8', '80'])).
% 30.99/31.20  
% 30.99/31.20  % SZS output end Refutation
% 30.99/31.20  
% 30.99/31.20  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
