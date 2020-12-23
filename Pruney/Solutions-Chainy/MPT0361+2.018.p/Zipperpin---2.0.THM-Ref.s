%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.wLlkBPaMJF

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:37:52 EST 2020

% Result     : Theorem 8.55s
% Output     : Refutation 8.55s
% Verified   : 
% Statistics : Number of formulae       :  134 ( 294 expanded)
%              Number of leaves         :   26 ( 102 expanded)
%              Depth                    :   20
%              Number of atoms          :  965 (2412 expanded)
%              Number of equality atoms :   55 ( 132 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

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
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ X32 ) )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ X32 ) )
      | ( ( k4_subset_1 @ X32 @ X31 @ X33 )
        = ( k2_xboole_0 @ X31 @ X33 ) ) ) ),
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

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('9',plain,(
    ! [X7: $i,X8: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X7 @ X8 ) @ X7 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('10',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k2_xboole_0 @ X3 @ X2 )
        = X2 )
      | ~ ( r1_tarski @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['11','12'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('14',plain,(
    ! [X18: $i,X19: $i] :
      ( r1_tarski @ X18 @ ( k2_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,(
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

thf('17',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X25 @ X26 )
      | ( r2_hidden @ X25 @ X26 )
      | ( v1_xboole_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('18',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('19',plain,(
    ! [X30: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('20',plain,(
    r2_hidden @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['18','19'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('21',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( r2_hidden @ X23 @ X22 )
      | ( r1_tarski @ X23 @ X21 )
      | ( X22
       != ( k1_zfmisc_1 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('22',plain,(
    ! [X21: $i,X23: $i] :
      ( ( r1_tarski @ X23 @ X21 )
      | ~ ( r2_hidden @ X23 @ ( k1_zfmisc_1 @ X21 ) ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    r1_tarski @ sk_C_1 @ sk_A ),
    inference('sup-',[status(thm)],['20','22'])).

thf('24',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k2_xboole_0 @ X3 @ X2 )
        = X2 )
      | ~ ( r1_tarski @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('25',plain,
    ( ( k2_xboole_0 @ sk_C_1 @ sk_A )
    = sk_A ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('27',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X25 @ X26 )
      | ( r2_hidden @ X25 @ X26 )
      | ( v1_xboole_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('29',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X30: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('31',plain,(
    r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X21: $i,X23: $i] :
      ( ( r1_tarski @ X23 @ X21 )
      | ~ ( r2_hidden @ X23 @ ( k1_zfmisc_1 @ X21 ) ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('33',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k2_xboole_0 @ X3 @ X2 )
        = X2 )
      | ~ ( r1_tarski @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('35',plain,
    ( ( k2_xboole_0 @ sk_B @ sk_A )
    = sk_A ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('37',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X9 @ X10 ) @ X11 )
      = ( k4_xboole_0 @ X9 @ ( k2_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X0 ) @ X1 )
      = ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ sk_A ) @ sk_B )
      = ( k4_xboole_0 @ X0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['35','38'])).

thf('40',plain,(
    ! [X7: $i,X8: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X7 @ X8 ) @ X7 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(t43_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) )
     => ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ) )).

thf('41',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X12 @ X13 ) @ X14 )
      | ~ ( r1_tarski @ X12 @ ( k2_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t43_xboole_1])).

thf('42',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 ) @ X1 ) @ X0 ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ ( k2_xboole_0 @ sk_B @ X0 ) @ sk_A ) @ X0 ) ),
    inference('sup+',[status(thm)],['39','42'])).

thf('44',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k2_xboole_0 @ X3 @ X2 )
        = X2 )
      | ~ ( r1_tarski @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ ( k2_xboole_0 @ sk_B @ X0 ) @ sk_A ) @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ ( k2_xboole_0 @ sk_B @ X0 ) @ sk_A ) )
      = X0 ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('49',plain,(
    ! [X18: $i,X19: $i] :
      ( r1_tarski @ X18 @ ( k2_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf(t44_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('51',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( r1_tarski @ X15 @ ( k2_xboole_0 @ X16 @ X17 ) )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ X15 @ X16 ) @ X17 ) ) ),
    inference(cnf,[status(esa)],[t44_xboole_1])).

thf('52',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ X1 @ ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('53',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( r1_tarski @ X4 @ X5 )
      | ~ ( r1_tarski @ X5 @ X6 )
      | ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('54',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) @ X3 ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_xboole_0 @ sk_A @ X0 ) @ X1 )
      | ( r1_tarski @ ( k2_xboole_0 @ sk_B @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['47','54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_xboole_0 @ X0 @ sk_A ) @ X1 )
      | ( r1_tarski @ ( k2_xboole_0 @ sk_B @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['26','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ sk_A @ X0 )
      | ( r1_tarski @ ( k2_xboole_0 @ sk_B @ sk_C_1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['25','56'])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('59',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ sk_A @ X0 )
      | ( r1_tarski @ ( k2_xboole_0 @ sk_C_1 @ sk_B ) @ X0 ) ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,(
    r1_tarski @ ( k2_xboole_0 @ sk_C_1 @ sk_B ) @ sk_A ),
    inference('sup-',[status(thm)],['15','59'])).

thf('61',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k2_xboole_0 @ X3 @ X2 )
        = X2 )
      | ~ ( r1_tarski @ X3 @ X2 ) ) ),
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
    ! [X18: $i,X19: $i] :
      ( r1_tarski @ X18 @ ( k2_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('67',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( r1_tarski @ X20 @ X21 )
      | ( r2_hidden @ X20 @ X22 )
      | ( X22
       != ( k1_zfmisc_1 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('68',plain,(
    ! [X20: $i,X21: $i] :
      ( ( r2_hidden @ X20 @ ( k1_zfmisc_1 @ X21 ) )
      | ~ ( r1_tarski @ X20 @ X21 ) ) ),
    inference(simplify,[status(thm)],['67'])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X1 @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['66','68'])).

thf('70',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( r2_hidden @ X25 @ X26 )
      | ( m1_subset_1 @ X25 @ X26 )
      | ( v1_xboole_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      | ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X30: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['65','73'])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('75',plain,(
    ! [X28: $i,X29: $i] :
      ( ( ( k3_subset_1 @ X28 @ X29 )
        = ( k4_xboole_0 @ X28 @ X29 ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,
    ( ( k3_subset_1 @ ( k2_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_C_1 @ sk_B ) ) @ ( k2_xboole_0 @ sk_C_1 @ sk_B ) )
    = ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_C_1 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['64','76'])).

thf('78',plain,
    ( ( k2_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_C_1 @ sk_B ) )
    = sk_A ),
    inference(demod,[status(thm)],['62','63'])).

thf('79',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X0 ) @ X1 )
      = ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('80',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    ! [X28: $i,X29: $i] :
      ( ( ( k3_subset_1 @ X28 @ X29 )
        = ( k4_xboole_0 @ X28 @ X29 ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('82',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    ! [X28: $i,X29: $i] :
      ( ( ( k3_subset_1 @ X28 @ X29 )
        = ( k4_xboole_0 @ X28 @ X29 ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('85',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C_1 )
    = ( k4_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('87',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X0 ) @ X1 )
      = ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('88',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X9 @ X10 ) @ X11 )
      = ( k4_xboole_0 @ X9 @ ( k2_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('89',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X0 ) @ X1 )
      = ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_B ) @ X0 )
      = ( k4_xboole_0 @ ( k4_xboole_0 @ sk_A @ X0 ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['86','89'])).

thf('91',plain,
    ( ( k4_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_C_1 )
    = ( k4_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ sk_B ) ),
    inference('sup+',[status(thm)],['85','90'])).

thf('92',plain,
    ( ( k3_subset_1 @ sk_A @ ( k2_xboole_0 @ sk_C_1 @ sk_B ) )
    = ( k4_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ sk_B ) ),
    inference(demod,[status(thm)],['77','78','79','82','91'])).

thf('93',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('94',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('95',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( r1_tarski @ X15 @ ( k2_xboole_0 @ X16 @ X17 ) )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ X15 @ X16 ) @ X17 ) ) ),
    inference(cnf,[status(esa)],[t44_xboole_1])).

thf('96',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X1 @ ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,(
    r1_tarski @ sk_A @ ( k2_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['93','96'])).

thf('98',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C_1 )
    = ( k4_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('99',plain,(
    ! [X7: $i,X8: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X7 @ X8 ) @ X7 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('100',plain,(
    r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ sk_A ),
    inference('sup+',[status(thm)],['98','99'])).

thf('101',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( r1_tarski @ X4 @ X5 )
      | ~ ( r1_tarski @ X5 @ X6 )
      | ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('102',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ X0 )
      | ~ ( r1_tarski @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,(
    r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k2_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['97','102'])).

thf('104',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X12 @ X13 ) @ X14 )
      | ~ ( r1_tarski @ X12 @ ( k2_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t43_xboole_1])).

thf('105',plain,(
    r1_tarski @ ( k4_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ sk_B ) @ ( k3_subset_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,(
    $false ),
    inference(demod,[status(thm)],['8','92','105'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.wLlkBPaMJF
% 0.14/0.35  % Computer   : n006.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 10:06:08 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 8.55/8.75  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 8.55/8.75  % Solved by: fo/fo7.sh
% 8.55/8.75  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 8.55/8.75  % done 10896 iterations in 8.254s
% 8.55/8.75  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 8.55/8.75  % SZS output start Refutation
% 8.55/8.75  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 8.55/8.75  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 8.55/8.75  thf(sk_B_type, type, sk_B: $i).
% 8.55/8.75  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 8.55/8.75  thf(sk_A_type, type, sk_A: $i).
% 8.55/8.75  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 8.55/8.75  thf(sk_C_1_type, type, sk_C_1: $i).
% 8.55/8.75  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 8.55/8.75  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 8.55/8.75  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 8.55/8.75  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 8.55/8.75  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 8.55/8.75  thf(t41_subset_1, conjecture,
% 8.55/8.75    (![A:$i,B:$i]:
% 8.55/8.75     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 8.55/8.75       ( ![C:$i]:
% 8.55/8.75         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 8.55/8.75           ( r1_tarski @
% 8.55/8.75             ( k3_subset_1 @ A @ ( k4_subset_1 @ A @ B @ C ) ) @ 
% 8.55/8.75             ( k3_subset_1 @ A @ B ) ) ) ) ))).
% 8.55/8.75  thf(zf_stmt_0, negated_conjecture,
% 8.55/8.75    (~( ![A:$i,B:$i]:
% 8.55/8.75        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 8.55/8.75          ( ![C:$i]:
% 8.55/8.75            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 8.55/8.75              ( r1_tarski @
% 8.55/8.75                ( k3_subset_1 @ A @ ( k4_subset_1 @ A @ B @ C ) ) @ 
% 8.55/8.75                ( k3_subset_1 @ A @ B ) ) ) ) ) )),
% 8.55/8.75    inference('cnf.neg', [status(esa)], [t41_subset_1])).
% 8.55/8.75  thf('0', plain,
% 8.55/8.75      (~ (r1_tarski @ 
% 8.55/8.75          (k3_subset_1 @ sk_A @ (k4_subset_1 @ sk_A @ sk_B @ sk_C_1)) @ 
% 8.55/8.75          (k3_subset_1 @ sk_A @ sk_B))),
% 8.55/8.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.55/8.75  thf('1', plain, ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 8.55/8.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.55/8.75  thf('2', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 8.55/8.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.55/8.75  thf(redefinition_k4_subset_1, axiom,
% 8.55/8.75    (![A:$i,B:$i,C:$i]:
% 8.55/8.75     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 8.55/8.75         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 8.55/8.75       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 8.55/8.75  thf('3', plain,
% 8.55/8.75      (![X31 : $i, X32 : $i, X33 : $i]:
% 8.55/8.75         (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ X32))
% 8.55/8.75          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ X32))
% 8.55/8.75          | ((k4_subset_1 @ X32 @ X31 @ X33) = (k2_xboole_0 @ X31 @ X33)))),
% 8.55/8.75      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 8.55/8.75  thf('4', plain,
% 8.55/8.75      (![X0 : $i]:
% 8.55/8.75         (((k4_subset_1 @ sk_A @ sk_B @ X0) = (k2_xboole_0 @ sk_B @ X0))
% 8.55/8.75          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A)))),
% 8.55/8.75      inference('sup-', [status(thm)], ['2', '3'])).
% 8.55/8.75  thf('5', plain,
% 8.55/8.75      (((k4_subset_1 @ sk_A @ sk_B @ sk_C_1) = (k2_xboole_0 @ sk_B @ sk_C_1))),
% 8.55/8.75      inference('sup-', [status(thm)], ['1', '4'])).
% 8.55/8.75  thf(commutativity_k2_xboole_0, axiom,
% 8.55/8.75    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 8.55/8.75  thf('6', plain,
% 8.55/8.75      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 8.55/8.75      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 8.55/8.75  thf('7', plain,
% 8.55/8.75      (((k4_subset_1 @ sk_A @ sk_B @ sk_C_1) = (k2_xboole_0 @ sk_C_1 @ sk_B))),
% 8.55/8.75      inference('demod', [status(thm)], ['5', '6'])).
% 8.55/8.75  thf('8', plain,
% 8.55/8.75      (~ (r1_tarski @ (k3_subset_1 @ sk_A @ (k2_xboole_0 @ sk_C_1 @ sk_B)) @ 
% 8.55/8.75          (k3_subset_1 @ sk_A @ sk_B))),
% 8.55/8.75      inference('demod', [status(thm)], ['0', '7'])).
% 8.55/8.75  thf(t36_xboole_1, axiom,
% 8.55/8.75    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 8.55/8.75  thf('9', plain,
% 8.55/8.75      (![X7 : $i, X8 : $i]: (r1_tarski @ (k4_xboole_0 @ X7 @ X8) @ X7)),
% 8.55/8.75      inference('cnf', [status(esa)], [t36_xboole_1])).
% 8.55/8.75  thf(t12_xboole_1, axiom,
% 8.55/8.75    (![A:$i,B:$i]:
% 8.55/8.75     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 8.55/8.75  thf('10', plain,
% 8.55/8.75      (![X2 : $i, X3 : $i]:
% 8.55/8.75         (((k2_xboole_0 @ X3 @ X2) = (X2)) | ~ (r1_tarski @ X3 @ X2))),
% 8.55/8.75      inference('cnf', [status(esa)], [t12_xboole_1])).
% 8.55/8.75  thf('11', plain,
% 8.55/8.75      (![X0 : $i, X1 : $i]:
% 8.55/8.75         ((k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0) = (X0))),
% 8.55/8.75      inference('sup-', [status(thm)], ['9', '10'])).
% 8.55/8.75  thf('12', plain,
% 8.55/8.75      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 8.55/8.75      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 8.55/8.75  thf('13', plain,
% 8.55/8.75      (![X0 : $i, X1 : $i]:
% 8.55/8.75         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)) = (X0))),
% 8.55/8.75      inference('demod', [status(thm)], ['11', '12'])).
% 8.55/8.75  thf(t7_xboole_1, axiom,
% 8.55/8.75    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 8.55/8.75  thf('14', plain,
% 8.55/8.75      (![X18 : $i, X19 : $i]: (r1_tarski @ X18 @ (k2_xboole_0 @ X18 @ X19))),
% 8.55/8.75      inference('cnf', [status(esa)], [t7_xboole_1])).
% 8.55/8.75  thf('15', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 8.55/8.75      inference('sup+', [status(thm)], ['13', '14'])).
% 8.55/8.75  thf('16', plain, ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 8.55/8.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.55/8.75  thf(d2_subset_1, axiom,
% 8.55/8.75    (![A:$i,B:$i]:
% 8.55/8.75     ( ( ( v1_xboole_0 @ A ) =>
% 8.55/8.75         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 8.55/8.75       ( ( ~( v1_xboole_0 @ A ) ) =>
% 8.55/8.75         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 8.55/8.75  thf('17', plain,
% 8.55/8.75      (![X25 : $i, X26 : $i]:
% 8.55/8.75         (~ (m1_subset_1 @ X25 @ X26)
% 8.55/8.75          | (r2_hidden @ X25 @ X26)
% 8.55/8.75          | (v1_xboole_0 @ X26))),
% 8.55/8.75      inference('cnf', [status(esa)], [d2_subset_1])).
% 8.55/8.75  thf('18', plain,
% 8.55/8.75      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 8.55/8.75        | (r2_hidden @ sk_C_1 @ (k1_zfmisc_1 @ sk_A)))),
% 8.55/8.75      inference('sup-', [status(thm)], ['16', '17'])).
% 8.55/8.75  thf(fc1_subset_1, axiom,
% 8.55/8.75    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 8.55/8.75  thf('19', plain, (![X30 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X30))),
% 8.55/8.75      inference('cnf', [status(esa)], [fc1_subset_1])).
% 8.55/8.75  thf('20', plain, ((r2_hidden @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 8.55/8.75      inference('clc', [status(thm)], ['18', '19'])).
% 8.55/8.75  thf(d1_zfmisc_1, axiom,
% 8.55/8.75    (![A:$i,B:$i]:
% 8.55/8.75     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 8.55/8.75       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 8.55/8.75  thf('21', plain,
% 8.55/8.75      (![X21 : $i, X22 : $i, X23 : $i]:
% 8.55/8.75         (~ (r2_hidden @ X23 @ X22)
% 8.55/8.75          | (r1_tarski @ X23 @ X21)
% 8.55/8.75          | ((X22) != (k1_zfmisc_1 @ X21)))),
% 8.55/8.75      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 8.55/8.75  thf('22', plain,
% 8.55/8.75      (![X21 : $i, X23 : $i]:
% 8.55/8.75         ((r1_tarski @ X23 @ X21) | ~ (r2_hidden @ X23 @ (k1_zfmisc_1 @ X21)))),
% 8.55/8.75      inference('simplify', [status(thm)], ['21'])).
% 8.55/8.75  thf('23', plain, ((r1_tarski @ sk_C_1 @ sk_A)),
% 8.55/8.75      inference('sup-', [status(thm)], ['20', '22'])).
% 8.55/8.75  thf('24', plain,
% 8.55/8.75      (![X2 : $i, X3 : $i]:
% 8.55/8.75         (((k2_xboole_0 @ X3 @ X2) = (X2)) | ~ (r1_tarski @ X3 @ X2))),
% 8.55/8.75      inference('cnf', [status(esa)], [t12_xboole_1])).
% 8.55/8.75  thf('25', plain, (((k2_xboole_0 @ sk_C_1 @ sk_A) = (sk_A))),
% 8.55/8.75      inference('sup-', [status(thm)], ['23', '24'])).
% 8.55/8.75  thf('26', plain,
% 8.55/8.75      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 8.55/8.75      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 8.55/8.75  thf('27', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 8.55/8.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.55/8.75  thf('28', plain,
% 8.55/8.75      (![X25 : $i, X26 : $i]:
% 8.55/8.75         (~ (m1_subset_1 @ X25 @ X26)
% 8.55/8.75          | (r2_hidden @ X25 @ X26)
% 8.55/8.75          | (v1_xboole_0 @ X26))),
% 8.55/8.75      inference('cnf', [status(esa)], [d2_subset_1])).
% 8.55/8.75  thf('29', plain,
% 8.55/8.75      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 8.55/8.75        | (r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A)))),
% 8.55/8.75      inference('sup-', [status(thm)], ['27', '28'])).
% 8.55/8.75  thf('30', plain, (![X30 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X30))),
% 8.55/8.75      inference('cnf', [status(esa)], [fc1_subset_1])).
% 8.55/8.75  thf('31', plain, ((r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 8.55/8.75      inference('clc', [status(thm)], ['29', '30'])).
% 8.55/8.75  thf('32', plain,
% 8.55/8.75      (![X21 : $i, X23 : $i]:
% 8.55/8.75         ((r1_tarski @ X23 @ X21) | ~ (r2_hidden @ X23 @ (k1_zfmisc_1 @ X21)))),
% 8.55/8.75      inference('simplify', [status(thm)], ['21'])).
% 8.55/8.75  thf('33', plain, ((r1_tarski @ sk_B @ sk_A)),
% 8.55/8.75      inference('sup-', [status(thm)], ['31', '32'])).
% 8.55/8.75  thf('34', plain,
% 8.55/8.75      (![X2 : $i, X3 : $i]:
% 8.55/8.75         (((k2_xboole_0 @ X3 @ X2) = (X2)) | ~ (r1_tarski @ X3 @ X2))),
% 8.55/8.75      inference('cnf', [status(esa)], [t12_xboole_1])).
% 8.55/8.75  thf('35', plain, (((k2_xboole_0 @ sk_B @ sk_A) = (sk_A))),
% 8.55/8.75      inference('sup-', [status(thm)], ['33', '34'])).
% 8.55/8.75  thf('36', plain,
% 8.55/8.75      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 8.55/8.75      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 8.55/8.75  thf(t41_xboole_1, axiom,
% 8.55/8.75    (![A:$i,B:$i,C:$i]:
% 8.55/8.75     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 8.55/8.75       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 8.55/8.75  thf('37', plain,
% 8.55/8.75      (![X9 : $i, X10 : $i, X11 : $i]:
% 8.55/8.75         ((k4_xboole_0 @ (k4_xboole_0 @ X9 @ X10) @ X11)
% 8.55/8.75           = (k4_xboole_0 @ X9 @ (k2_xboole_0 @ X10 @ X11)))),
% 8.55/8.75      inference('cnf', [status(esa)], [t41_xboole_1])).
% 8.55/8.75  thf('38', plain,
% 8.55/8.75      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.55/8.75         ((k4_xboole_0 @ (k4_xboole_0 @ X2 @ X0) @ X1)
% 8.55/8.75           = (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))),
% 8.55/8.75      inference('sup+', [status(thm)], ['36', '37'])).
% 8.55/8.75  thf('39', plain,
% 8.55/8.75      (![X0 : $i]:
% 8.55/8.75         ((k4_xboole_0 @ (k4_xboole_0 @ X0 @ sk_A) @ sk_B)
% 8.55/8.75           = (k4_xboole_0 @ X0 @ sk_A))),
% 8.55/8.75      inference('sup+', [status(thm)], ['35', '38'])).
% 8.55/8.75  thf('40', plain,
% 8.55/8.75      (![X7 : $i, X8 : $i]: (r1_tarski @ (k4_xboole_0 @ X7 @ X8) @ X7)),
% 8.55/8.75      inference('cnf', [status(esa)], [t36_xboole_1])).
% 8.55/8.75  thf(t43_xboole_1, axiom,
% 8.55/8.75    (![A:$i,B:$i,C:$i]:
% 8.55/8.75     ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) =>
% 8.55/8.75       ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ))).
% 8.55/8.75  thf('41', plain,
% 8.55/8.75      (![X12 : $i, X13 : $i, X14 : $i]:
% 8.55/8.75         ((r1_tarski @ (k4_xboole_0 @ X12 @ X13) @ X14)
% 8.55/8.75          | ~ (r1_tarski @ X12 @ (k2_xboole_0 @ X13 @ X14)))),
% 8.55/8.75      inference('cnf', [status(esa)], [t43_xboole_1])).
% 8.55/8.75  thf('42', plain,
% 8.55/8.75      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.55/8.75         (r1_tarski @ 
% 8.55/8.75          (k4_xboole_0 @ (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X2) @ X1) @ 
% 8.55/8.75          X0)),
% 8.55/8.75      inference('sup-', [status(thm)], ['40', '41'])).
% 8.55/8.75  thf('43', plain,
% 8.55/8.75      (![X0 : $i]:
% 8.55/8.75         (r1_tarski @ (k4_xboole_0 @ (k2_xboole_0 @ sk_B @ X0) @ sk_A) @ X0)),
% 8.55/8.75      inference('sup+', [status(thm)], ['39', '42'])).
% 8.55/8.75  thf('44', plain,
% 8.55/8.75      (![X2 : $i, X3 : $i]:
% 8.55/8.75         (((k2_xboole_0 @ X3 @ X2) = (X2)) | ~ (r1_tarski @ X3 @ X2))),
% 8.55/8.75      inference('cnf', [status(esa)], [t12_xboole_1])).
% 8.55/8.75  thf('45', plain,
% 8.55/8.75      (![X0 : $i]:
% 8.55/8.75         ((k2_xboole_0 @ (k4_xboole_0 @ (k2_xboole_0 @ sk_B @ X0) @ sk_A) @ X0)
% 8.55/8.75           = (X0))),
% 8.55/8.75      inference('sup-', [status(thm)], ['43', '44'])).
% 8.55/8.75  thf('46', plain,
% 8.55/8.75      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 8.55/8.75      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 8.55/8.75  thf('47', plain,
% 8.55/8.75      (![X0 : $i]:
% 8.55/8.75         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ (k2_xboole_0 @ sk_B @ X0) @ sk_A))
% 8.55/8.75           = (X0))),
% 8.55/8.75      inference('demod', [status(thm)], ['45', '46'])).
% 8.55/8.75  thf('48', plain,
% 8.55/8.75      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 8.55/8.75      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 8.55/8.75  thf('49', plain,
% 8.55/8.75      (![X18 : $i, X19 : $i]: (r1_tarski @ X18 @ (k2_xboole_0 @ X18 @ X19))),
% 8.55/8.75      inference('cnf', [status(esa)], [t7_xboole_1])).
% 8.55/8.75  thf('50', plain,
% 8.55/8.75      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 8.55/8.75      inference('sup+', [status(thm)], ['48', '49'])).
% 8.55/8.75  thf(t44_xboole_1, axiom,
% 8.55/8.75    (![A:$i,B:$i,C:$i]:
% 8.55/8.75     ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) =>
% 8.55/8.75       ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 8.55/8.75  thf('51', plain,
% 8.55/8.75      (![X15 : $i, X16 : $i, X17 : $i]:
% 8.55/8.75         ((r1_tarski @ X15 @ (k2_xboole_0 @ X16 @ X17))
% 8.55/8.75          | ~ (r1_tarski @ (k4_xboole_0 @ X15 @ X16) @ X17))),
% 8.55/8.75      inference('cnf', [status(esa)], [t44_xboole_1])).
% 8.55/8.75  thf('52', plain,
% 8.55/8.75      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.55/8.75         (r1_tarski @ X1 @ 
% 8.55/8.75          (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0))))),
% 8.55/8.75      inference('sup-', [status(thm)], ['50', '51'])).
% 8.55/8.75  thf(t1_xboole_1, axiom,
% 8.55/8.75    (![A:$i,B:$i,C:$i]:
% 8.55/8.75     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 8.55/8.75       ( r1_tarski @ A @ C ) ))).
% 8.55/8.75  thf('53', plain,
% 8.55/8.75      (![X4 : $i, X5 : $i, X6 : $i]:
% 8.55/8.75         (~ (r1_tarski @ X4 @ X5)
% 8.55/8.75          | ~ (r1_tarski @ X5 @ X6)
% 8.55/8.75          | (r1_tarski @ X4 @ X6))),
% 8.55/8.75      inference('cnf', [status(esa)], [t1_xboole_1])).
% 8.55/8.75  thf('54', plain,
% 8.55/8.75      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 8.55/8.75         ((r1_tarski @ X1 @ X3)
% 8.55/8.75          | ~ (r1_tarski @ 
% 8.55/8.75               (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0))) @ 
% 8.55/8.75               X3))),
% 8.55/8.75      inference('sup-', [status(thm)], ['52', '53'])).
% 8.55/8.75  thf('55', plain,
% 8.55/8.75      (![X0 : $i, X1 : $i]:
% 8.55/8.75         (~ (r1_tarski @ (k2_xboole_0 @ sk_A @ X0) @ X1)
% 8.55/8.75          | (r1_tarski @ (k2_xboole_0 @ sk_B @ X0) @ X1))),
% 8.55/8.75      inference('sup-', [status(thm)], ['47', '54'])).
% 8.55/8.75  thf('56', plain,
% 8.55/8.75      (![X0 : $i, X1 : $i]:
% 8.55/8.75         (~ (r1_tarski @ (k2_xboole_0 @ X0 @ sk_A) @ X1)
% 8.55/8.75          | (r1_tarski @ (k2_xboole_0 @ sk_B @ X0) @ X1))),
% 8.55/8.75      inference('sup-', [status(thm)], ['26', '55'])).
% 8.55/8.75  thf('57', plain,
% 8.55/8.75      (![X0 : $i]:
% 8.55/8.75         (~ (r1_tarski @ sk_A @ X0)
% 8.55/8.75          | (r1_tarski @ (k2_xboole_0 @ sk_B @ sk_C_1) @ X0))),
% 8.55/8.75      inference('sup-', [status(thm)], ['25', '56'])).
% 8.55/8.75  thf('58', plain,
% 8.55/8.75      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 8.55/8.75      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 8.55/8.75  thf('59', plain,
% 8.55/8.75      (![X0 : $i]:
% 8.55/8.75         (~ (r1_tarski @ sk_A @ X0)
% 8.55/8.75          | (r1_tarski @ (k2_xboole_0 @ sk_C_1 @ sk_B) @ X0))),
% 8.55/8.75      inference('demod', [status(thm)], ['57', '58'])).
% 8.55/8.75  thf('60', plain, ((r1_tarski @ (k2_xboole_0 @ sk_C_1 @ sk_B) @ sk_A)),
% 8.55/8.75      inference('sup-', [status(thm)], ['15', '59'])).
% 8.55/8.75  thf('61', plain,
% 8.55/8.75      (![X2 : $i, X3 : $i]:
% 8.55/8.75         (((k2_xboole_0 @ X3 @ X2) = (X2)) | ~ (r1_tarski @ X3 @ X2))),
% 8.55/8.75      inference('cnf', [status(esa)], [t12_xboole_1])).
% 8.55/8.75  thf('62', plain,
% 8.55/8.75      (((k2_xboole_0 @ (k2_xboole_0 @ sk_C_1 @ sk_B) @ sk_A) = (sk_A))),
% 8.55/8.75      inference('sup-', [status(thm)], ['60', '61'])).
% 8.55/8.75  thf('63', plain,
% 8.55/8.75      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 8.55/8.75      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 8.55/8.75  thf('64', plain,
% 8.55/8.75      (((k2_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_C_1 @ sk_B)) = (sk_A))),
% 8.55/8.75      inference('demod', [status(thm)], ['62', '63'])).
% 8.55/8.75  thf('65', plain,
% 8.55/8.75      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 8.55/8.75      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 8.55/8.75  thf('66', plain,
% 8.55/8.75      (![X18 : $i, X19 : $i]: (r1_tarski @ X18 @ (k2_xboole_0 @ X18 @ X19))),
% 8.55/8.75      inference('cnf', [status(esa)], [t7_xboole_1])).
% 8.55/8.75  thf('67', plain,
% 8.55/8.75      (![X20 : $i, X21 : $i, X22 : $i]:
% 8.55/8.75         (~ (r1_tarski @ X20 @ X21)
% 8.55/8.75          | (r2_hidden @ X20 @ X22)
% 8.55/8.75          | ((X22) != (k1_zfmisc_1 @ X21)))),
% 8.55/8.75      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 8.55/8.75  thf('68', plain,
% 8.55/8.75      (![X20 : $i, X21 : $i]:
% 8.55/8.75         ((r2_hidden @ X20 @ (k1_zfmisc_1 @ X21)) | ~ (r1_tarski @ X20 @ X21))),
% 8.55/8.75      inference('simplify', [status(thm)], ['67'])).
% 8.55/8.75  thf('69', plain,
% 8.55/8.75      (![X0 : $i, X1 : $i]:
% 8.55/8.75         (r2_hidden @ X1 @ (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))),
% 8.55/8.75      inference('sup-', [status(thm)], ['66', '68'])).
% 8.55/8.75  thf('70', plain,
% 8.55/8.75      (![X25 : $i, X26 : $i]:
% 8.55/8.75         (~ (r2_hidden @ X25 @ X26)
% 8.55/8.75          | (m1_subset_1 @ X25 @ X26)
% 8.55/8.75          | (v1_xboole_0 @ X26))),
% 8.55/8.75      inference('cnf', [status(esa)], [d2_subset_1])).
% 8.55/8.75  thf('71', plain,
% 8.55/8.75      (![X0 : $i, X1 : $i]:
% 8.55/8.75         ((v1_xboole_0 @ (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))
% 8.55/8.75          | (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0))))),
% 8.55/8.75      inference('sup-', [status(thm)], ['69', '70'])).
% 8.55/8.75  thf('72', plain, (![X30 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X30))),
% 8.55/8.75      inference('cnf', [status(esa)], [fc1_subset_1])).
% 8.55/8.75  thf('73', plain,
% 8.55/8.75      (![X0 : $i, X1 : $i]:
% 8.55/8.75         (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))),
% 8.55/8.75      inference('clc', [status(thm)], ['71', '72'])).
% 8.55/8.75  thf('74', plain,
% 8.55/8.75      (![X0 : $i, X1 : $i]:
% 8.55/8.75         (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))),
% 8.55/8.75      inference('sup+', [status(thm)], ['65', '73'])).
% 8.55/8.75  thf(d5_subset_1, axiom,
% 8.55/8.75    (![A:$i,B:$i]:
% 8.55/8.75     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 8.55/8.75       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 8.55/8.75  thf('75', plain,
% 8.55/8.75      (![X28 : $i, X29 : $i]:
% 8.55/8.75         (((k3_subset_1 @ X28 @ X29) = (k4_xboole_0 @ X28 @ X29))
% 8.55/8.75          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ X28)))),
% 8.55/8.75      inference('cnf', [status(esa)], [d5_subset_1])).
% 8.55/8.75  thf('76', plain,
% 8.55/8.75      (![X0 : $i, X1 : $i]:
% 8.55/8.75         ((k3_subset_1 @ (k2_xboole_0 @ X1 @ X0) @ X0)
% 8.55/8.75           = (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X0))),
% 8.55/8.75      inference('sup-', [status(thm)], ['74', '75'])).
% 8.55/8.75  thf('77', plain,
% 8.55/8.75      (((k3_subset_1 @ (k2_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_C_1 @ sk_B)) @ 
% 8.55/8.75         (k2_xboole_0 @ sk_C_1 @ sk_B))
% 8.55/8.75         = (k4_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_C_1 @ sk_B)))),
% 8.55/8.75      inference('sup+', [status(thm)], ['64', '76'])).
% 8.55/8.75  thf('78', plain,
% 8.55/8.75      (((k2_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_C_1 @ sk_B)) = (sk_A))),
% 8.55/8.75      inference('demod', [status(thm)], ['62', '63'])).
% 8.55/8.75  thf('79', plain,
% 8.55/8.75      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.55/8.75         ((k4_xboole_0 @ (k4_xboole_0 @ X2 @ X0) @ X1)
% 8.55/8.75           = (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))),
% 8.55/8.75      inference('sup+', [status(thm)], ['36', '37'])).
% 8.55/8.75  thf('80', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 8.55/8.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.55/8.75  thf('81', plain,
% 8.55/8.75      (![X28 : $i, X29 : $i]:
% 8.55/8.75         (((k3_subset_1 @ X28 @ X29) = (k4_xboole_0 @ X28 @ X29))
% 8.55/8.75          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ X28)))),
% 8.55/8.75      inference('cnf', [status(esa)], [d5_subset_1])).
% 8.55/8.75  thf('82', plain,
% 8.55/8.75      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 8.55/8.75      inference('sup-', [status(thm)], ['80', '81'])).
% 8.55/8.75  thf('83', plain, ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 8.55/8.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.55/8.75  thf('84', plain,
% 8.55/8.75      (![X28 : $i, X29 : $i]:
% 8.55/8.75         (((k3_subset_1 @ X28 @ X29) = (k4_xboole_0 @ X28 @ X29))
% 8.55/8.75          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ X28)))),
% 8.55/8.75      inference('cnf', [status(esa)], [d5_subset_1])).
% 8.55/8.75  thf('85', plain,
% 8.55/8.75      (((k3_subset_1 @ sk_A @ sk_C_1) = (k4_xboole_0 @ sk_A @ sk_C_1))),
% 8.55/8.75      inference('sup-', [status(thm)], ['83', '84'])).
% 8.55/8.75  thf('86', plain,
% 8.55/8.75      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 8.55/8.75      inference('sup-', [status(thm)], ['80', '81'])).
% 8.55/8.75  thf('87', plain,
% 8.55/8.75      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.55/8.75         ((k4_xboole_0 @ (k4_xboole_0 @ X2 @ X0) @ X1)
% 8.55/8.75           = (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))),
% 8.55/8.75      inference('sup+', [status(thm)], ['36', '37'])).
% 8.55/8.75  thf('88', plain,
% 8.55/8.75      (![X9 : $i, X10 : $i, X11 : $i]:
% 8.55/8.75         ((k4_xboole_0 @ (k4_xboole_0 @ X9 @ X10) @ X11)
% 8.55/8.75           = (k4_xboole_0 @ X9 @ (k2_xboole_0 @ X10 @ X11)))),
% 8.55/8.75      inference('cnf', [status(esa)], [t41_xboole_1])).
% 8.55/8.75  thf('89', plain,
% 8.55/8.75      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.55/8.75         ((k4_xboole_0 @ (k4_xboole_0 @ X2 @ X0) @ X1)
% 8.55/8.75           = (k4_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0))),
% 8.55/8.75      inference('sup+', [status(thm)], ['87', '88'])).
% 8.55/8.75  thf('90', plain,
% 8.55/8.75      (![X0 : $i]:
% 8.55/8.75         ((k4_xboole_0 @ (k3_subset_1 @ sk_A @ sk_B) @ X0)
% 8.55/8.75           = (k4_xboole_0 @ (k4_xboole_0 @ sk_A @ X0) @ sk_B))),
% 8.55/8.75      inference('sup+', [status(thm)], ['86', '89'])).
% 8.55/8.75  thf('91', plain,
% 8.55/8.75      (((k4_xboole_0 @ (k3_subset_1 @ sk_A @ sk_B) @ sk_C_1)
% 8.55/8.75         = (k4_xboole_0 @ (k3_subset_1 @ sk_A @ sk_C_1) @ sk_B))),
% 8.55/8.75      inference('sup+', [status(thm)], ['85', '90'])).
% 8.55/8.75  thf('92', plain,
% 8.55/8.75      (((k3_subset_1 @ sk_A @ (k2_xboole_0 @ sk_C_1 @ sk_B))
% 8.55/8.75         = (k4_xboole_0 @ (k3_subset_1 @ sk_A @ sk_C_1) @ sk_B))),
% 8.55/8.75      inference('demod', [status(thm)], ['77', '78', '79', '82', '91'])).
% 8.55/8.75  thf('93', plain,
% 8.55/8.75      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 8.55/8.75      inference('sup-', [status(thm)], ['80', '81'])).
% 8.55/8.75  thf('94', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 8.55/8.75      inference('sup+', [status(thm)], ['13', '14'])).
% 8.55/8.75  thf('95', plain,
% 8.55/8.75      (![X15 : $i, X16 : $i, X17 : $i]:
% 8.55/8.75         ((r1_tarski @ X15 @ (k2_xboole_0 @ X16 @ X17))
% 8.55/8.75          | ~ (r1_tarski @ (k4_xboole_0 @ X15 @ X16) @ X17))),
% 8.55/8.75      inference('cnf', [status(esa)], [t44_xboole_1])).
% 8.55/8.75  thf('96', plain,
% 8.55/8.75      (![X0 : $i, X1 : $i]:
% 8.55/8.75         (r1_tarski @ X1 @ (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 8.55/8.75      inference('sup-', [status(thm)], ['94', '95'])).
% 8.55/8.75  thf('97', plain,
% 8.55/8.75      ((r1_tarski @ sk_A @ (k2_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)))),
% 8.55/8.75      inference('sup+', [status(thm)], ['93', '96'])).
% 8.55/8.75  thf('98', plain,
% 8.55/8.75      (((k3_subset_1 @ sk_A @ sk_C_1) = (k4_xboole_0 @ sk_A @ sk_C_1))),
% 8.55/8.75      inference('sup-', [status(thm)], ['83', '84'])).
% 8.55/8.75  thf('99', plain,
% 8.55/8.75      (![X7 : $i, X8 : $i]: (r1_tarski @ (k4_xboole_0 @ X7 @ X8) @ X7)),
% 8.55/8.75      inference('cnf', [status(esa)], [t36_xboole_1])).
% 8.55/8.75  thf('100', plain, ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ sk_A)),
% 8.55/8.75      inference('sup+', [status(thm)], ['98', '99'])).
% 8.55/8.75  thf('101', plain,
% 8.55/8.75      (![X4 : $i, X5 : $i, X6 : $i]:
% 8.55/8.75         (~ (r1_tarski @ X4 @ X5)
% 8.55/8.75          | ~ (r1_tarski @ X5 @ X6)
% 8.55/8.75          | (r1_tarski @ X4 @ X6))),
% 8.55/8.75      inference('cnf', [status(esa)], [t1_xboole_1])).
% 8.55/8.75  thf('102', plain,
% 8.55/8.75      (![X0 : $i]:
% 8.55/8.75         ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ X0)
% 8.55/8.75          | ~ (r1_tarski @ sk_A @ X0))),
% 8.55/8.75      inference('sup-', [status(thm)], ['100', '101'])).
% 8.55/8.75  thf('103', plain,
% 8.55/8.75      ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 8.55/8.75        (k2_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)))),
% 8.55/8.75      inference('sup-', [status(thm)], ['97', '102'])).
% 8.55/8.75  thf('104', plain,
% 8.55/8.75      (![X12 : $i, X13 : $i, X14 : $i]:
% 8.55/8.75         ((r1_tarski @ (k4_xboole_0 @ X12 @ X13) @ X14)
% 8.55/8.75          | ~ (r1_tarski @ X12 @ (k2_xboole_0 @ X13 @ X14)))),
% 8.55/8.75      inference('cnf', [status(esa)], [t43_xboole_1])).
% 8.55/8.75  thf('105', plain,
% 8.55/8.75      ((r1_tarski @ (k4_xboole_0 @ (k3_subset_1 @ sk_A @ sk_C_1) @ sk_B) @ 
% 8.55/8.75        (k3_subset_1 @ sk_A @ sk_B))),
% 8.55/8.75      inference('sup-', [status(thm)], ['103', '104'])).
% 8.55/8.75  thf('106', plain, ($false),
% 8.55/8.75      inference('demod', [status(thm)], ['8', '92', '105'])).
% 8.55/8.75  
% 8.55/8.75  % SZS output end Refutation
% 8.55/8.75  
% 8.55/8.76  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
