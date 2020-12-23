%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.V08XHs24Zp

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:37:43 EST 2020

% Result     : Theorem 0.47s
% Output     : Refutation 0.47s
% Verified   : 
% Statistics : Number of formulae       :  107 ( 224 expanded)
%              Number of leaves         :   33 (  82 expanded)
%              Depth                    :   16
%              Number of atoms          :  690 (1707 expanded)
%              Number of equality atoms :   58 ( 139 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(t40_subset_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( ( r1_tarski @ B @ C )
          & ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) ) )
       => ( B = k1_xboole_0 ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
       => ( ( ( r1_tarski @ B @ C )
            & ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) ) )
         => ( B = k1_xboole_0 ) ) ) ),
    inference('cnf.neg',[status(esa)],[t40_subset_1])).

thf('0',plain,(
    r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('2',plain,(
    ! [X36: $i,X37: $i] :
      ( ( ( k3_subset_1 @ X36 @ X37 )
        = ( k4_xboole_0 @ X36 @ X37 ) )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('3',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C )
    = ( k4_xboole_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    r1_tarski @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['0','3'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('5',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ X9 )
      = ( k5_xboole_0 @ X8 @ ( k3_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf(t107_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k5_xboole_0 @ B @ C ) )
    <=> ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) )
        & ( r1_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) ) )).

thf('6',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( r1_xboole_0 @ X10 @ ( k3_xboole_0 @ X11 @ X12 ) )
      | ~ ( r1_tarski @ X10 @ ( k5_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t107_xboole_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) )
      | ( r1_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    r1_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['4','7'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('9',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_tarski @ X5 @ X6 )
      | ( X5 != X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('10',plain,(
    ! [X6: $i] :
      ( r1_tarski @ X6 @ X6 ) ),
    inference(simplify,[status(thm)],['9'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('11',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k2_xboole_0 @ X15 @ X14 )
        = X14 )
      | ~ ( r1_tarski @ X15 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(t95_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ) )).

thf('13',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k3_xboole_0 @ X24 @ X25 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X24 @ X25 ) @ ( k2_xboole_0 @ X24 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t95_xboole_1])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('14',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X20 @ X21 ) @ X22 )
      = ( k5_xboole_0 @ X20 @ ( k5_xboole_0 @ X21 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('15',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k3_xboole_0 @ X24 @ X25 )
      = ( k5_xboole_0 @ X24 @ ( k5_xboole_0 @ X25 @ ( k2_xboole_0 @ X24 @ X25 ) ) ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['12','15'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('17',plain,(
    ! [X23: $i] :
      ( ( k5_xboole_0 @ X23 @ X23 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('19',plain,(
    ! [X19: $i] :
      ( ( k5_xboole_0 @ X19 @ k1_xboole_0 )
      = X19 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X10: $i,X11: $i,X13: $i] :
      ( ( r1_tarski @ X10 @ ( k5_xboole_0 @ X11 @ X13 ) )
      | ~ ( r1_xboole_0 @ X10 @ ( k3_xboole_0 @ X11 @ X13 ) )
      | ~ ( r1_tarski @ X10 @ ( k2_xboole_0 @ X11 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t107_xboole_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_tarski @ X1 @ ( k2_xboole_0 @ X0 @ X0 ) )
      | ( r1_tarski @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('24',plain,(
    ! [X23: $i] :
      ( ( k5_xboole_0 @ X23 @ X23 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_tarski @ X1 @ X0 )
      | ( r1_tarski @ X1 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['22','23','24'])).

thf('26',plain,
    ( ( r1_tarski @ sk_B @ k1_xboole_0 )
    | ~ ( r1_tarski @ sk_B @ ( k3_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_A @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['8','25'])).

thf('27',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('28',plain,(
    ! [X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X33 @ X34 )
      | ( r2_hidden @ X33 @ X34 )
      | ( v1_xboole_0 @ X34 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('29',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_C @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('30',plain,(
    ! [X38: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('31',plain,(
    r2_hidden @ sk_C @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['29','30'])).

thf(l49_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( r1_tarski @ A @ ( k3_tarski @ B ) ) ) )).

thf('32',plain,(
    ! [X28: $i,X29: $i] :
      ( ( r1_tarski @ X28 @ ( k3_tarski @ X29 ) )
      | ~ ( r2_hidden @ X28 @ X29 ) ) ),
    inference(cnf,[status(esa)],[l49_zfmisc_1])).

thf('33',plain,(
    r1_tarski @ sk_C @ ( k3_tarski @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf(t99_zfmisc_1,axiom,(
    ! [A: $i] :
      ( ( k3_tarski @ ( k1_zfmisc_1 @ A ) )
      = A ) )).

thf('34',plain,(
    ! [X32: $i] :
      ( ( k3_tarski @ ( k1_zfmisc_1 @ X32 ) )
      = X32 ) ),
    inference(cnf,[status(esa)],[t99_zfmisc_1])).

thf('35',plain,(
    r1_tarski @ sk_C @ sk_A ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X6: $i] :
      ( r1_tarski @ X6 @ X6 ) ),
    inference(simplify,[status(thm)],['9'])).

thf(t14_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ C @ B )
        & ! [D: $i] :
            ( ( ( r1_tarski @ A @ D )
              & ( r1_tarski @ C @ D ) )
           => ( r1_tarski @ B @ D ) ) )
     => ( B
        = ( k2_xboole_0 @ A @ C ) ) ) )).

thf('37',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( r1_tarski @ X16 @ X17 )
      | ~ ( r1_tarski @ X18 @ X17 )
      | ( r1_tarski @ X16 @ ( sk_D @ X18 @ X17 @ X16 ) )
      | ( X17
        = ( k2_xboole_0 @ X16 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t14_xboole_1])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k2_xboole_0 @ X0 @ X1 ) )
      | ( r1_tarski @ X0 @ ( sk_D @ X1 @ X0 @ X0 ) )
      | ~ ( r1_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,
    ( ( r1_tarski @ sk_A @ ( sk_D @ sk_C @ sk_A @ sk_A ) )
    | ( sk_A
      = ( k2_xboole_0 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['35','38'])).

thf('40',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( r1_tarski @ X16 @ X17 )
      | ~ ( r1_tarski @ X18 @ X17 )
      | ~ ( r1_tarski @ X17 @ ( sk_D @ X18 @ X17 @ X16 ) )
      | ( X17
        = ( k2_xboole_0 @ X16 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t14_xboole_1])).

thf('41',plain,
    ( ( sk_A
      = ( k2_xboole_0 @ sk_A @ sk_C ) )
    | ( sk_A
      = ( k2_xboole_0 @ sk_A @ sk_C ) )
    | ~ ( r1_tarski @ sk_C @ sk_A )
    | ~ ( r1_tarski @ sk_A @ sk_A ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    r1_tarski @ sk_C @ sk_A ),
    inference(demod,[status(thm)],['33','34'])).

thf('43',plain,(
    ! [X6: $i] :
      ( r1_tarski @ X6 @ X6 ) ),
    inference(simplify,[status(thm)],['9'])).

thf('44',plain,
    ( ( sk_A
      = ( k2_xboole_0 @ sk_A @ sk_C ) )
    | ( sk_A
      = ( k2_xboole_0 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['41','42','43'])).

thf('45',plain,
    ( sk_A
    = ( k2_xboole_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k3_xboole_0 @ X24 @ X25 )
      = ( k5_xboole_0 @ X24 @ ( k5_xboole_0 @ X25 @ ( k2_xboole_0 @ X24 @ X25 ) ) ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('47',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_C )
    = ( k5_xboole_0 @ sk_A @ ( k5_xboole_0 @ sk_C @ sk_A ) ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('49',plain,(
    ! [X23: $i] :
      ( ( k5_xboole_0 @ X23 @ X23 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('50',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X20 @ X21 ) @ X22 )
      = ( k5_xboole_0 @ X20 @ ( k5_xboole_0 @ X21 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('53',plain,(
    ! [X19: $i] :
      ( ( k5_xboole_0 @ X19 @ k1_xboole_0 )
      = X19 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['51','54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['48','55'])).

thf('57',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_C )
    = sk_C ),
    inference(demod,[status(thm)],['47','56'])).

thf('58',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_C )
    = sk_C ),
    inference(demod,[status(thm)],['47','56'])).

thf('59',plain,(
    r1_tarski @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    r1_tarski @ sk_B @ k1_xboole_0 ),
    inference(demod,[status(thm)],['26','57','58','59'])).

thf('61',plain,(
    ! [X5: $i,X7: $i] :
      ( ( X5 = X7 )
      | ~ ( r1_tarski @ X7 @ X5 )
      | ~ ( r1_tarski @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('62',plain,
    ( ~ ( r1_tarski @ k1_xboole_0 @ sk_B )
    | ( k1_xboole_0 = sk_B ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X6: $i] :
      ( r1_tarski @ X6 @ X6 ) ),
    inference(simplify,[status(thm)],['9'])).

thf('64',plain,(
    ! [X23: $i] :
      ( ( k5_xboole_0 @ X23 @ X23 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('65',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( r1_tarski @ X10 @ ( k2_xboole_0 @ X11 @ X12 ) )
      | ~ ( r1_tarski @ X10 @ ( k5_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t107_xboole_1])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ k1_xboole_0 )
      | ( r1_tarski @ X1 @ ( k2_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ k1_xboole_0 )
      | ( r1_tarski @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['63','68'])).

thf('70',plain,(
    k1_xboole_0 = sk_B ),
    inference(demod,[status(thm)],['62','69'])).

thf('71',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['70','71'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.V08XHs24Zp
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 19:11:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.35  % Running portfolio for 600 s
% 0.20/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.20/0.35  % Number of cores: 8
% 0.20/0.35  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 0.47/0.70  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.47/0.70  % Solved by: fo/fo7.sh
% 0.47/0.70  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.47/0.70  % done 727 iterations in 0.244s
% 0.47/0.70  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.47/0.70  % SZS output start Refutation
% 0.47/0.70  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.47/0.70  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.47/0.70  thf(sk_B_type, type, sk_B: $i).
% 0.47/0.70  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.47/0.70  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.47/0.70  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.47/0.70  thf(sk_C_type, type, sk_C: $i).
% 0.47/0.70  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.47/0.70  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.47/0.70  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.47/0.70  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.47/0.70  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.47/0.70  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.47/0.70  thf(sk_A_type, type, sk_A: $i).
% 0.47/0.70  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.47/0.70  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.47/0.70  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.47/0.70  thf(t40_subset_1, conjecture,
% 0.47/0.70    (![A:$i,B:$i,C:$i]:
% 0.47/0.70     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.47/0.70       ( ( ( r1_tarski @ B @ C ) & ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) ) ) =>
% 0.47/0.70         ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.47/0.70  thf(zf_stmt_0, negated_conjecture,
% 0.47/0.70    (~( ![A:$i,B:$i,C:$i]:
% 0.47/0.70        ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.47/0.70          ( ( ( r1_tarski @ B @ C ) & 
% 0.47/0.70              ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) ) ) =>
% 0.47/0.70            ( ( B ) = ( k1_xboole_0 ) ) ) ) )),
% 0.47/0.70    inference('cnf.neg', [status(esa)], [t40_subset_1])).
% 0.47/0.70  thf('0', plain, ((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_C))),
% 0.47/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.70  thf('1', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 0.47/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.70  thf(d5_subset_1, axiom,
% 0.47/0.70    (![A:$i,B:$i]:
% 0.47/0.70     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.47/0.70       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.47/0.70  thf('2', plain,
% 0.47/0.70      (![X36 : $i, X37 : $i]:
% 0.47/0.70         (((k3_subset_1 @ X36 @ X37) = (k4_xboole_0 @ X36 @ X37))
% 0.47/0.70          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ X36)))),
% 0.47/0.70      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.47/0.70  thf('3', plain,
% 0.47/0.70      (((k3_subset_1 @ sk_A @ sk_C) = (k4_xboole_0 @ sk_A @ sk_C))),
% 0.47/0.70      inference('sup-', [status(thm)], ['1', '2'])).
% 0.47/0.70  thf('4', plain, ((r1_tarski @ sk_B @ (k4_xboole_0 @ sk_A @ sk_C))),
% 0.47/0.70      inference('demod', [status(thm)], ['0', '3'])).
% 0.47/0.70  thf(t100_xboole_1, axiom,
% 0.47/0.70    (![A:$i,B:$i]:
% 0.47/0.70     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.47/0.70  thf('5', plain,
% 0.47/0.70      (![X8 : $i, X9 : $i]:
% 0.47/0.70         ((k4_xboole_0 @ X8 @ X9)
% 0.47/0.70           = (k5_xboole_0 @ X8 @ (k3_xboole_0 @ X8 @ X9)))),
% 0.47/0.70      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.47/0.70  thf(t107_xboole_1, axiom,
% 0.47/0.70    (![A:$i,B:$i,C:$i]:
% 0.47/0.70     ( ( r1_tarski @ A @ ( k5_xboole_0 @ B @ C ) ) <=>
% 0.47/0.70       ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) & 
% 0.47/0.70         ( r1_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) ))).
% 0.47/0.70  thf('6', plain,
% 0.47/0.70      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.47/0.70         ((r1_xboole_0 @ X10 @ (k3_xboole_0 @ X11 @ X12))
% 0.47/0.70          | ~ (r1_tarski @ X10 @ (k5_xboole_0 @ X11 @ X12)))),
% 0.47/0.70      inference('cnf', [status(esa)], [t107_xboole_1])).
% 0.47/0.70  thf('7', plain,
% 0.47/0.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.47/0.70         (~ (r1_tarski @ X2 @ (k4_xboole_0 @ X1 @ X0))
% 0.47/0.70          | (r1_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))))),
% 0.47/0.70      inference('sup-', [status(thm)], ['5', '6'])).
% 0.47/0.70  thf('8', plain,
% 0.47/0.70      ((r1_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_A @ sk_C)))),
% 0.47/0.70      inference('sup-', [status(thm)], ['4', '7'])).
% 0.47/0.70  thf(d10_xboole_0, axiom,
% 0.47/0.70    (![A:$i,B:$i]:
% 0.47/0.70     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.47/0.70  thf('9', plain,
% 0.47/0.70      (![X5 : $i, X6 : $i]: ((r1_tarski @ X5 @ X6) | ((X5) != (X6)))),
% 0.47/0.70      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.47/0.70  thf('10', plain, (![X6 : $i]: (r1_tarski @ X6 @ X6)),
% 0.47/0.70      inference('simplify', [status(thm)], ['9'])).
% 0.47/0.70  thf(t12_xboole_1, axiom,
% 0.47/0.70    (![A:$i,B:$i]:
% 0.47/0.70     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.47/0.70  thf('11', plain,
% 0.47/0.70      (![X14 : $i, X15 : $i]:
% 0.47/0.70         (((k2_xboole_0 @ X15 @ X14) = (X14)) | ~ (r1_tarski @ X15 @ X14))),
% 0.47/0.70      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.47/0.70  thf('12', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 0.47/0.70      inference('sup-', [status(thm)], ['10', '11'])).
% 0.47/0.70  thf(t95_xboole_1, axiom,
% 0.47/0.70    (![A:$i,B:$i]:
% 0.47/0.70     ( ( k3_xboole_0 @ A @ B ) =
% 0.47/0.70       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ))).
% 0.47/0.70  thf('13', plain,
% 0.47/0.70      (![X24 : $i, X25 : $i]:
% 0.47/0.70         ((k3_xboole_0 @ X24 @ X25)
% 0.47/0.70           = (k5_xboole_0 @ (k5_xboole_0 @ X24 @ X25) @ 
% 0.47/0.70              (k2_xboole_0 @ X24 @ X25)))),
% 0.47/0.70      inference('cnf', [status(esa)], [t95_xboole_1])).
% 0.47/0.70  thf(t91_xboole_1, axiom,
% 0.47/0.70    (![A:$i,B:$i,C:$i]:
% 0.47/0.70     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.47/0.70       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.47/0.70  thf('14', plain,
% 0.47/0.70      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.47/0.70         ((k5_xboole_0 @ (k5_xboole_0 @ X20 @ X21) @ X22)
% 0.47/0.70           = (k5_xboole_0 @ X20 @ (k5_xboole_0 @ X21 @ X22)))),
% 0.47/0.70      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.47/0.70  thf('15', plain,
% 0.47/0.70      (![X24 : $i, X25 : $i]:
% 0.47/0.70         ((k3_xboole_0 @ X24 @ X25)
% 0.47/0.70           = (k5_xboole_0 @ X24 @ 
% 0.47/0.70              (k5_xboole_0 @ X25 @ (k2_xboole_0 @ X24 @ X25))))),
% 0.47/0.70      inference('demod', [status(thm)], ['13', '14'])).
% 0.47/0.70  thf('16', plain,
% 0.47/0.70      (![X0 : $i]:
% 0.47/0.70         ((k3_xboole_0 @ X0 @ X0)
% 0.47/0.70           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X0)))),
% 0.47/0.70      inference('sup+', [status(thm)], ['12', '15'])).
% 0.47/0.70  thf(t92_xboole_1, axiom,
% 0.47/0.70    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.47/0.70  thf('17', plain, (![X23 : $i]: ((k5_xboole_0 @ X23 @ X23) = (k1_xboole_0))),
% 0.47/0.70      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.47/0.70  thf('18', plain,
% 0.47/0.70      (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.47/0.70      inference('demod', [status(thm)], ['16', '17'])).
% 0.47/0.70  thf(t5_boole, axiom,
% 0.47/0.70    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.47/0.70  thf('19', plain, (![X19 : $i]: ((k5_xboole_0 @ X19 @ k1_xboole_0) = (X19))),
% 0.47/0.70      inference('cnf', [status(esa)], [t5_boole])).
% 0.47/0.70  thf('20', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.47/0.70      inference('demod', [status(thm)], ['18', '19'])).
% 0.47/0.70  thf('21', plain,
% 0.47/0.70      (![X10 : $i, X11 : $i, X13 : $i]:
% 0.47/0.70         ((r1_tarski @ X10 @ (k5_xboole_0 @ X11 @ X13))
% 0.47/0.70          | ~ (r1_xboole_0 @ X10 @ (k3_xboole_0 @ X11 @ X13))
% 0.47/0.70          | ~ (r1_tarski @ X10 @ (k2_xboole_0 @ X11 @ X13)))),
% 0.47/0.70      inference('cnf', [status(esa)], [t107_xboole_1])).
% 0.47/0.70  thf('22', plain,
% 0.47/0.70      (![X0 : $i, X1 : $i]:
% 0.47/0.70         (~ (r1_xboole_0 @ X1 @ X0)
% 0.47/0.70          | ~ (r1_tarski @ X1 @ (k2_xboole_0 @ X0 @ X0))
% 0.47/0.70          | (r1_tarski @ X1 @ (k5_xboole_0 @ X0 @ X0)))),
% 0.47/0.70      inference('sup-', [status(thm)], ['20', '21'])).
% 0.47/0.70  thf('23', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 0.47/0.70      inference('sup-', [status(thm)], ['10', '11'])).
% 0.47/0.70  thf('24', plain, (![X23 : $i]: ((k5_xboole_0 @ X23 @ X23) = (k1_xboole_0))),
% 0.47/0.70      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.47/0.70  thf('25', plain,
% 0.47/0.70      (![X0 : $i, X1 : $i]:
% 0.47/0.70         (~ (r1_xboole_0 @ X1 @ X0)
% 0.47/0.70          | ~ (r1_tarski @ X1 @ X0)
% 0.47/0.70          | (r1_tarski @ X1 @ k1_xboole_0))),
% 0.47/0.70      inference('demod', [status(thm)], ['22', '23', '24'])).
% 0.47/0.70  thf('26', plain,
% 0.47/0.70      (((r1_tarski @ sk_B @ k1_xboole_0)
% 0.47/0.70        | ~ (r1_tarski @ sk_B @ 
% 0.47/0.70             (k3_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_A @ sk_C))))),
% 0.47/0.70      inference('sup-', [status(thm)], ['8', '25'])).
% 0.47/0.70  thf('27', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 0.47/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.70  thf(d2_subset_1, axiom,
% 0.47/0.70    (![A:$i,B:$i]:
% 0.47/0.70     ( ( ( v1_xboole_0 @ A ) =>
% 0.47/0.70         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.47/0.70       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.47/0.70         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.47/0.70  thf('28', plain,
% 0.47/0.70      (![X33 : $i, X34 : $i]:
% 0.47/0.70         (~ (m1_subset_1 @ X33 @ X34)
% 0.47/0.70          | (r2_hidden @ X33 @ X34)
% 0.47/0.70          | (v1_xboole_0 @ X34))),
% 0.47/0.70      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.47/0.70  thf('29', plain,
% 0.47/0.70      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 0.47/0.70        | (r2_hidden @ sk_C @ (k1_zfmisc_1 @ sk_A)))),
% 0.47/0.70      inference('sup-', [status(thm)], ['27', '28'])).
% 0.47/0.70  thf(fc1_subset_1, axiom,
% 0.47/0.70    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.47/0.70  thf('30', plain, (![X38 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X38))),
% 0.47/0.70      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.47/0.70  thf('31', plain, ((r2_hidden @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 0.47/0.70      inference('clc', [status(thm)], ['29', '30'])).
% 0.47/0.70  thf(l49_zfmisc_1, axiom,
% 0.47/0.70    (![A:$i,B:$i]:
% 0.47/0.70     ( ( r2_hidden @ A @ B ) => ( r1_tarski @ A @ ( k3_tarski @ B ) ) ))).
% 0.47/0.70  thf('32', plain,
% 0.47/0.70      (![X28 : $i, X29 : $i]:
% 0.47/0.70         ((r1_tarski @ X28 @ (k3_tarski @ X29)) | ~ (r2_hidden @ X28 @ X29))),
% 0.47/0.70      inference('cnf', [status(esa)], [l49_zfmisc_1])).
% 0.47/0.70  thf('33', plain, ((r1_tarski @ sk_C @ (k3_tarski @ (k1_zfmisc_1 @ sk_A)))),
% 0.47/0.70      inference('sup-', [status(thm)], ['31', '32'])).
% 0.47/0.70  thf(t99_zfmisc_1, axiom,
% 0.47/0.70    (![A:$i]: ( ( k3_tarski @ ( k1_zfmisc_1 @ A ) ) = ( A ) ))).
% 0.47/0.70  thf('34', plain, (![X32 : $i]: ((k3_tarski @ (k1_zfmisc_1 @ X32)) = (X32))),
% 0.47/0.70      inference('cnf', [status(esa)], [t99_zfmisc_1])).
% 0.47/0.70  thf('35', plain, ((r1_tarski @ sk_C @ sk_A)),
% 0.47/0.70      inference('demod', [status(thm)], ['33', '34'])).
% 0.47/0.70  thf('36', plain, (![X6 : $i]: (r1_tarski @ X6 @ X6)),
% 0.47/0.70      inference('simplify', [status(thm)], ['9'])).
% 0.47/0.70  thf(t14_xboole_1, axiom,
% 0.47/0.70    (![A:$i,B:$i,C:$i]:
% 0.47/0.70     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ B ) & 
% 0.47/0.70         ( ![D:$i]:
% 0.47/0.70           ( ( ( r1_tarski @ A @ D ) & ( r1_tarski @ C @ D ) ) =>
% 0.47/0.70             ( r1_tarski @ B @ D ) ) ) ) =>
% 0.47/0.70       ( ( B ) = ( k2_xboole_0 @ A @ C ) ) ))).
% 0.47/0.70  thf('37', plain,
% 0.47/0.70      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.47/0.70         (~ (r1_tarski @ X16 @ X17)
% 0.47/0.70          | ~ (r1_tarski @ X18 @ X17)
% 0.47/0.70          | (r1_tarski @ X16 @ (sk_D @ X18 @ X17 @ X16))
% 0.47/0.70          | ((X17) = (k2_xboole_0 @ X16 @ X18)))),
% 0.47/0.70      inference('cnf', [status(esa)], [t14_xboole_1])).
% 0.47/0.70  thf('38', plain,
% 0.47/0.70      (![X0 : $i, X1 : $i]:
% 0.47/0.70         (((X0) = (k2_xboole_0 @ X0 @ X1))
% 0.47/0.70          | (r1_tarski @ X0 @ (sk_D @ X1 @ X0 @ X0))
% 0.47/0.70          | ~ (r1_tarski @ X1 @ X0))),
% 0.47/0.70      inference('sup-', [status(thm)], ['36', '37'])).
% 0.47/0.70  thf('39', plain,
% 0.47/0.70      (((r1_tarski @ sk_A @ (sk_D @ sk_C @ sk_A @ sk_A))
% 0.47/0.70        | ((sk_A) = (k2_xboole_0 @ sk_A @ sk_C)))),
% 0.47/0.70      inference('sup-', [status(thm)], ['35', '38'])).
% 0.47/0.70  thf('40', plain,
% 0.47/0.70      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.47/0.70         (~ (r1_tarski @ X16 @ X17)
% 0.47/0.70          | ~ (r1_tarski @ X18 @ X17)
% 0.47/0.70          | ~ (r1_tarski @ X17 @ (sk_D @ X18 @ X17 @ X16))
% 0.47/0.70          | ((X17) = (k2_xboole_0 @ X16 @ X18)))),
% 0.47/0.70      inference('cnf', [status(esa)], [t14_xboole_1])).
% 0.47/0.70  thf('41', plain,
% 0.47/0.70      ((((sk_A) = (k2_xboole_0 @ sk_A @ sk_C))
% 0.47/0.70        | ((sk_A) = (k2_xboole_0 @ sk_A @ sk_C))
% 0.47/0.70        | ~ (r1_tarski @ sk_C @ sk_A)
% 0.47/0.70        | ~ (r1_tarski @ sk_A @ sk_A))),
% 0.47/0.70      inference('sup-', [status(thm)], ['39', '40'])).
% 0.47/0.70  thf('42', plain, ((r1_tarski @ sk_C @ sk_A)),
% 0.47/0.70      inference('demod', [status(thm)], ['33', '34'])).
% 0.47/0.70  thf('43', plain, (![X6 : $i]: (r1_tarski @ X6 @ X6)),
% 0.47/0.70      inference('simplify', [status(thm)], ['9'])).
% 0.47/0.70  thf('44', plain,
% 0.47/0.70      ((((sk_A) = (k2_xboole_0 @ sk_A @ sk_C))
% 0.47/0.70        | ((sk_A) = (k2_xboole_0 @ sk_A @ sk_C)))),
% 0.47/0.70      inference('demod', [status(thm)], ['41', '42', '43'])).
% 0.47/0.70  thf('45', plain, (((sk_A) = (k2_xboole_0 @ sk_A @ sk_C))),
% 0.47/0.70      inference('simplify', [status(thm)], ['44'])).
% 0.47/0.70  thf('46', plain,
% 0.47/0.70      (![X24 : $i, X25 : $i]:
% 0.47/0.70         ((k3_xboole_0 @ X24 @ X25)
% 0.47/0.70           = (k5_xboole_0 @ X24 @ 
% 0.47/0.70              (k5_xboole_0 @ X25 @ (k2_xboole_0 @ X24 @ X25))))),
% 0.47/0.70      inference('demod', [status(thm)], ['13', '14'])).
% 0.47/0.70  thf('47', plain,
% 0.47/0.70      (((k3_xboole_0 @ sk_A @ sk_C)
% 0.47/0.70         = (k5_xboole_0 @ sk_A @ (k5_xboole_0 @ sk_C @ sk_A)))),
% 0.47/0.70      inference('sup+', [status(thm)], ['45', '46'])).
% 0.47/0.70  thf(commutativity_k5_xboole_0, axiom,
% 0.47/0.70    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 0.47/0.70  thf('48', plain,
% 0.47/0.70      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.47/0.70      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.47/0.70  thf('49', plain, (![X23 : $i]: ((k5_xboole_0 @ X23 @ X23) = (k1_xboole_0))),
% 0.47/0.70      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.47/0.70  thf('50', plain,
% 0.47/0.70      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.47/0.70         ((k5_xboole_0 @ (k5_xboole_0 @ X20 @ X21) @ X22)
% 0.47/0.70           = (k5_xboole_0 @ X20 @ (k5_xboole_0 @ X21 @ X22)))),
% 0.47/0.70      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.47/0.70  thf('51', plain,
% 0.47/0.70      (![X0 : $i, X1 : $i]:
% 0.47/0.70         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 0.47/0.70           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.47/0.70      inference('sup+', [status(thm)], ['49', '50'])).
% 0.47/0.70  thf('52', plain,
% 0.47/0.70      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.47/0.70      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.47/0.70  thf('53', plain, (![X19 : $i]: ((k5_xboole_0 @ X19 @ k1_xboole_0) = (X19))),
% 0.47/0.70      inference('cnf', [status(esa)], [t5_boole])).
% 0.47/0.70  thf('54', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.47/0.70      inference('sup+', [status(thm)], ['52', '53'])).
% 0.47/0.70  thf('55', plain,
% 0.47/0.70      (![X0 : $i, X1 : $i]:
% 0.47/0.70         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.47/0.70      inference('demod', [status(thm)], ['51', '54'])).
% 0.47/0.70  thf('56', plain,
% 0.47/0.70      (![X0 : $i, X1 : $i]:
% 0.47/0.70         ((X1) = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.47/0.70      inference('sup+', [status(thm)], ['48', '55'])).
% 0.47/0.70  thf('57', plain, (((k3_xboole_0 @ sk_A @ sk_C) = (sk_C))),
% 0.47/0.70      inference('demod', [status(thm)], ['47', '56'])).
% 0.47/0.70  thf('58', plain, (((k3_xboole_0 @ sk_A @ sk_C) = (sk_C))),
% 0.47/0.70      inference('demod', [status(thm)], ['47', '56'])).
% 0.47/0.70  thf('59', plain, ((r1_tarski @ sk_B @ sk_C)),
% 0.47/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.70  thf('60', plain, ((r1_tarski @ sk_B @ k1_xboole_0)),
% 0.47/0.70      inference('demod', [status(thm)], ['26', '57', '58', '59'])).
% 0.47/0.70  thf('61', plain,
% 0.47/0.70      (![X5 : $i, X7 : $i]:
% 0.47/0.70         (((X5) = (X7)) | ~ (r1_tarski @ X7 @ X5) | ~ (r1_tarski @ X5 @ X7))),
% 0.47/0.70      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.47/0.70  thf('62', plain,
% 0.47/0.70      ((~ (r1_tarski @ k1_xboole_0 @ sk_B) | ((k1_xboole_0) = (sk_B)))),
% 0.47/0.70      inference('sup-', [status(thm)], ['60', '61'])).
% 0.47/0.70  thf('63', plain, (![X6 : $i]: (r1_tarski @ X6 @ X6)),
% 0.47/0.70      inference('simplify', [status(thm)], ['9'])).
% 0.47/0.70  thf('64', plain, (![X23 : $i]: ((k5_xboole_0 @ X23 @ X23) = (k1_xboole_0))),
% 0.47/0.70      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.47/0.70  thf('65', plain,
% 0.47/0.70      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.47/0.70         ((r1_tarski @ X10 @ (k2_xboole_0 @ X11 @ X12))
% 0.47/0.70          | ~ (r1_tarski @ X10 @ (k5_xboole_0 @ X11 @ X12)))),
% 0.47/0.70      inference('cnf', [status(esa)], [t107_xboole_1])).
% 0.47/0.70  thf('66', plain,
% 0.47/0.70      (![X0 : $i, X1 : $i]:
% 0.47/0.70         (~ (r1_tarski @ X1 @ k1_xboole_0)
% 0.47/0.70          | (r1_tarski @ X1 @ (k2_xboole_0 @ X0 @ X0)))),
% 0.47/0.70      inference('sup-', [status(thm)], ['64', '65'])).
% 0.47/0.70  thf('67', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 0.47/0.70      inference('sup-', [status(thm)], ['10', '11'])).
% 0.47/0.70  thf('68', plain,
% 0.47/0.70      (![X0 : $i, X1 : $i]:
% 0.47/0.70         (~ (r1_tarski @ X1 @ k1_xboole_0) | (r1_tarski @ X1 @ X0))),
% 0.47/0.70      inference('demod', [status(thm)], ['66', '67'])).
% 0.47/0.70  thf('69', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.47/0.70      inference('sup-', [status(thm)], ['63', '68'])).
% 0.47/0.70  thf('70', plain, (((k1_xboole_0) = (sk_B))),
% 0.47/0.70      inference('demod', [status(thm)], ['62', '69'])).
% 0.47/0.70  thf('71', plain, (((sk_B) != (k1_xboole_0))),
% 0.47/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.70  thf('72', plain, ($false),
% 0.47/0.70      inference('simplify_reflect-', [status(thm)], ['70', '71'])).
% 0.47/0.70  
% 0.47/0.70  % SZS output end Refutation
% 0.47/0.70  
% 0.47/0.70  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
