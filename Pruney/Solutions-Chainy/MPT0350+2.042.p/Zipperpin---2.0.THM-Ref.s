%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.R7AQvuIgUG

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:36:50 EST 2020

% Result     : Theorem 1.90s
% Output     : Refutation 1.90s
% Verified   : 
% Statistics : Number of formulae       :  119 ( 180 expanded)
%              Number of leaves         :   40 (  70 expanded)
%              Depth                    :   13
%              Number of atoms          :  831 (1378 expanded)
%              Number of equality atoms :   73 ( 121 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t25_subset_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k4_subset_1 @ A @ B @ ( k3_subset_1 @ A @ B ) )
        = ( k2_subset_1 @ A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
       => ( ( k4_subset_1 @ A @ B @ ( k3_subset_1 @ A @ B ) )
          = ( k2_subset_1 @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t25_subset_1])).

thf('0',plain,(
    m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('1',plain,(
    ! [X71: $i,X72: $i] :
      ( ( ( k3_subset_1 @ X71 @ X72 )
        = ( k4_xboole_0 @ X71 @ X72 ) )
      | ~ ( m1_subset_1 @ X72 @ ( k1_zfmisc_1 @ X71 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('2',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B_2 )
    = ( k4_xboole_0 @ sk_A @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('3',plain,(
    ! [X19: $i,X20: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X19 @ X20 ) @ X19 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('4',plain,(
    r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B_2 ) @ sk_A ),
    inference('sup+',[status(thm)],['2','3'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('5',plain,(
    ! [X60: $i,X61: $i,X62: $i] :
      ( ~ ( r1_tarski @ X60 @ X61 )
      | ( r2_hidden @ X60 @ X62 )
      | ( X62
       != ( k1_zfmisc_1 @ X61 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('6',plain,(
    ! [X60: $i,X61: $i] :
      ( ( r2_hidden @ X60 @ ( k1_zfmisc_1 @ X61 ) )
      | ~ ( r1_tarski @ X60 @ X61 ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,(
    r2_hidden @ ( k3_subset_1 @ sk_A @ sk_B_2 ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['4','6'])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('8',plain,(
    ! [X67: $i,X68: $i] :
      ( ~ ( r2_hidden @ X67 @ X68 )
      | ( m1_subset_1 @ X67 @ X68 )
      | ( v1_xboole_0 @ X68 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('9',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X4 @ X5 )
      | ~ ( v1_xboole_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('10',plain,(
    ! [X67: $i,X68: $i] :
      ( ( m1_subset_1 @ X67 @ X68 )
      | ~ ( r2_hidden @ X67 @ X68 ) ) ),
    inference(clc,[status(thm)],['8','9'])).

thf('11',plain,(
    m1_subset_1 @ ( k3_subset_1 @ sk_A @ sk_B_2 ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['7','10'])).

thf('12',plain,(
    m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('13',plain,(
    ! [X74: $i,X75: $i,X76: $i] :
      ( ~ ( m1_subset_1 @ X74 @ ( k1_zfmisc_1 @ X75 ) )
      | ~ ( m1_subset_1 @ X76 @ ( k1_zfmisc_1 @ X75 ) )
      | ( ( k4_subset_1 @ X75 @ X74 @ X76 )
        = ( k2_xboole_0 @ X74 @ X76 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('14',plain,(
    ! [X65: $i,X66: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X65 @ X66 ) )
      = ( k2_xboole_0 @ X65 @ X66 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('15',plain,(
    ! [X74: $i,X75: $i,X76: $i] :
      ( ~ ( m1_subset_1 @ X74 @ ( k1_zfmisc_1 @ X75 ) )
      | ~ ( m1_subset_1 @ X76 @ ( k1_zfmisc_1 @ X75 ) )
      | ( ( k4_subset_1 @ X75 @ X74 @ X76 )
        = ( k3_tarski @ ( k2_tarski @ X74 @ X76 ) ) ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ sk_A @ sk_B_2 @ X0 )
        = ( k3_tarski @ ( k2_tarski @ sk_B_2 @ X0 ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['12','15'])).

thf('17',plain,
    ( ( k4_subset_1 @ sk_A @ sk_B_2 @ ( k3_subset_1 @ sk_A @ sk_B_2 ) )
    = ( k3_tarski @ ( k2_tarski @ sk_B_2 @ ( k3_subset_1 @ sk_A @ sk_B_2 ) ) ) ),
    inference('sup-',[status(thm)],['11','16'])).

thf('18',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B_2 )
    = ( k4_xboole_0 @ sk_A @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('19',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k4_xboole_0 @ X23 @ ( k4_xboole_0 @ X23 @ X24 ) )
      = ( k3_xboole_0 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('20',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B_2 ) )
    = ( k3_xboole_0 @ sk_A @ sk_B_2 ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('22',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B_2 ) )
    = ( k3_xboole_0 @ sk_B_2 @ sk_A ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B_2 ) @ sk_A ),
    inference('sup+',[status(thm)],['2','3'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('24',plain,(
    ! [X17: $i,X18: $i] :
      ( ( ( k3_xboole_0 @ X17 @ X18 )
        = X17 )
      | ~ ( r1_tarski @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('25',plain,
    ( ( k3_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_B_2 ) @ sk_A )
    = ( k3_subset_1 @ sk_A @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('27',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B_2 ) )
    = ( k3_subset_1 @ sk_A @ sk_B_2 ) ),
    inference(demod,[status(thm)],['25','26'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('28',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ X16 )
      = ( k5_xboole_0 @ X15 @ ( k3_xboole_0 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('29',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B_2 ) )
    = ( k5_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B_2 ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,
    ( ( k3_xboole_0 @ sk_B_2 @ sk_A )
    = ( k5_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B_2 ) ) ),
    inference('sup+',[status(thm)],['22','29'])).

thf('31',plain,(
    m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    ! [X67: $i,X68: $i] :
      ( ~ ( m1_subset_1 @ X67 @ X68 )
      | ( r2_hidden @ X67 @ X68 )
      | ( v1_xboole_0 @ X68 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('33',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_B_2 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('34',plain,(
    ! [X73: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X73 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('35',plain,(
    r2_hidden @ sk_B_2 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X61: $i,X62: $i,X63: $i] :
      ( ~ ( r2_hidden @ X63 @ X62 )
      | ( r1_tarski @ X63 @ X61 )
      | ( X62
       != ( k1_zfmisc_1 @ X61 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('37',plain,(
    ! [X61: $i,X63: $i] :
      ( ( r1_tarski @ X63 @ X61 )
      | ~ ( r2_hidden @ X63 @ ( k1_zfmisc_1 @ X61 ) ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,(
    r1_tarski @ sk_B_2 @ sk_A ),
    inference('sup-',[status(thm)],['35','37'])).

thf('39',plain,(
    ! [X17: $i,X18: $i] :
      ( ( ( k3_xboole_0 @ X17 @ X18 )
        = X17 )
      | ~ ( r1_tarski @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('40',plain,
    ( ( k3_xboole_0 @ sk_B_2 @ sk_A )
    = sk_B_2 ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,
    ( sk_B_2
    = ( k5_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B_2 ) ) ),
    inference(demod,[status(thm)],['30','40'])).

thf(t93_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('42',plain,(
    ! [X29: $i,X30: $i] :
      ( ( k2_xboole_0 @ X29 @ X30 )
      = ( k2_xboole_0 @ ( k5_xboole_0 @ X29 @ X30 ) @ ( k3_xboole_0 @ X29 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[t93_xboole_1])).

thf('43',plain,(
    ! [X65: $i,X66: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X65 @ X66 ) )
      = ( k2_xboole_0 @ X65 @ X66 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('44',plain,(
    ! [X65: $i,X66: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X65 @ X66 ) )
      = ( k2_xboole_0 @ X65 @ X66 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('45',plain,(
    ! [X29: $i,X30: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X29 @ X30 ) )
      = ( k3_tarski @ ( k2_tarski @ ( k5_xboole_0 @ X29 @ X30 ) @ ( k3_xboole_0 @ X29 @ X30 ) ) ) ) ),
    inference(demod,[status(thm)],['42','43','44'])).

thf('46',plain,
    ( ( k3_tarski @ ( k2_tarski @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B_2 ) ) )
    = ( k3_tarski @ ( k2_tarski @ sk_B_2 @ ( k3_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B_2 ) ) ) ) ),
    inference('sup+',[status(thm)],['41','45'])).

thf('47',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B_2 ) )
    = ( k3_subset_1 @ sk_A @ sk_B_2 ) ),
    inference(demod,[status(thm)],['25','26'])).

thf(t94_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('48',plain,(
    ! [X31: $i,X32: $i] :
      ( ( k2_xboole_0 @ X31 @ X32 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X31 @ X32 ) @ ( k3_xboole_0 @ X31 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[t94_xboole_1])).

thf('49',plain,(
    ! [X65: $i,X66: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X65 @ X66 ) )
      = ( k2_xboole_0 @ X65 @ X66 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('50',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X26 @ X27 ) @ X28 )
      = ( k5_xboole_0 @ X26 @ ( k5_xboole_0 @ X27 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('51',plain,(
    ! [X31: $i,X32: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X31 @ X32 ) )
      = ( k5_xboole_0 @ X31 @ ( k5_xboole_0 @ X32 @ ( k3_xboole_0 @ X31 @ X32 ) ) ) ) ),
    inference(demod,[status(thm)],['48','49','50'])).

thf('52',plain,
    ( ( k3_tarski @ ( k2_tarski @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B_2 ) ) )
    = ( k5_xboole_0 @ sk_A @ ( k5_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_B_2 ) @ ( k3_subset_1 @ sk_A @ sk_B_2 ) ) ) ),
    inference('sup+',[status(thm)],['47','51'])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('53',plain,(
    ! [X14: $i] :
      ( ( X14 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B_1 @ X14 ) @ X14 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('54',plain,(
    ! [X13: $i] :
      ( ( k3_xboole_0 @ X13 @ X13 )
      = X13 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('55',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ X16 )
      = ( k5_xboole_0 @ X15 @ ( k3_xboole_0 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['54','55'])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('57',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X11 @ X10 )
      | ( r2_hidden @ X11 @ X8 )
      | ( X10
       != ( k4_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('58',plain,(
    ! [X8: $i,X9: $i,X11: $i] :
      ( ( r2_hidden @ X11 @ X8 )
      | ~ ( r2_hidden @ X11 @ ( k4_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(simplify,[status(thm)],['57'])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['56','58'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['54','55'])).

thf('61',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X11 @ X10 )
      | ~ ( r2_hidden @ X11 @ X9 )
      | ( X10
       != ( k4_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('62',plain,(
    ! [X8: $i,X9: $i,X11: $i] :
      ( ~ ( r2_hidden @ X11 @ X9 )
      | ~ ( r2_hidden @ X11 @ ( k4_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(simplify,[status(thm)],['61'])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['60','62'])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_hidden @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(clc,[status(thm)],['59','63'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['53','64'])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

thf('66',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('67',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('68',plain,(
    ! [X25: $i] :
      ( ( k5_xboole_0 @ X25 @ k1_xboole_0 )
      = X25 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['67','68'])).

thf('70',plain,
    ( ( k3_tarski @ ( k2_tarski @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B_2 ) ) )
    = sk_A ),
    inference(demod,[status(thm)],['52','65','66','69'])).

thf('71',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B_2 ) )
    = ( k3_subset_1 @ sk_A @ sk_B_2 ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('72',plain,
    ( sk_A
    = ( k3_tarski @ ( k2_tarski @ sk_B_2 @ ( k3_subset_1 @ sk_A @ sk_B_2 ) ) ) ),
    inference(demod,[status(thm)],['46','70','71'])).

thf('73',plain,
    ( ( k4_subset_1 @ sk_A @ sk_B_2 @ ( k3_subset_1 @ sk_A @ sk_B_2 ) )
    = sk_A ),
    inference(demod,[status(thm)],['17','72'])).

thf('74',plain,(
    ( k4_subset_1 @ sk_A @ sk_B_2 @ ( k3_subset_1 @ sk_A @ sk_B_2 ) )
 != ( k2_subset_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('75',plain,(
    ! [X70: $i] :
      ( ( k2_subset_1 @ X70 )
      = X70 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('76',plain,(
    ( k4_subset_1 @ sk_A @ sk_B_2 @ ( k3_subset_1 @ sk_A @ sk_B_2 ) )
 != sk_A ),
    inference(demod,[status(thm)],['74','75'])).

thf('77',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['73','76'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.R7AQvuIgUG
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:12:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.90/2.10  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.90/2.10  % Solved by: fo/fo7.sh
% 1.90/2.10  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.90/2.10  % done 3374 iterations in 1.646s
% 1.90/2.10  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.90/2.10  % SZS output start Refutation
% 1.90/2.10  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 1.90/2.10  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 1.90/2.10  thf(sk_B_1_type, type, sk_B_1: $i > $i).
% 1.90/2.10  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.90/2.10  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 1.90/2.10  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.90/2.10  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.90/2.10  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.90/2.10  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 1.90/2.10  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 1.90/2.10  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 1.90/2.10  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.90/2.10  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.90/2.10  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.90/2.10  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.90/2.10  thf(sk_B_2_type, type, sk_B_2: $i).
% 1.90/2.10  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.90/2.10  thf(sk_A_type, type, sk_A: $i).
% 1.90/2.10  thf(t25_subset_1, conjecture,
% 1.90/2.10    (![A:$i,B:$i]:
% 1.90/2.10     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.90/2.10       ( ( k4_subset_1 @ A @ B @ ( k3_subset_1 @ A @ B ) ) =
% 1.90/2.10         ( k2_subset_1 @ A ) ) ))).
% 1.90/2.10  thf(zf_stmt_0, negated_conjecture,
% 1.90/2.10    (~( ![A:$i,B:$i]:
% 1.90/2.10        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.90/2.10          ( ( k4_subset_1 @ A @ B @ ( k3_subset_1 @ A @ B ) ) =
% 1.90/2.10            ( k2_subset_1 @ A ) ) ) )),
% 1.90/2.10    inference('cnf.neg', [status(esa)], [t25_subset_1])).
% 1.90/2.10  thf('0', plain, ((m1_subset_1 @ sk_B_2 @ (k1_zfmisc_1 @ sk_A))),
% 1.90/2.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.90/2.10  thf(d5_subset_1, axiom,
% 1.90/2.10    (![A:$i,B:$i]:
% 1.90/2.10     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.90/2.10       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 1.90/2.10  thf('1', plain,
% 1.90/2.10      (![X71 : $i, X72 : $i]:
% 1.90/2.10         (((k3_subset_1 @ X71 @ X72) = (k4_xboole_0 @ X71 @ X72))
% 1.90/2.10          | ~ (m1_subset_1 @ X72 @ (k1_zfmisc_1 @ X71)))),
% 1.90/2.10      inference('cnf', [status(esa)], [d5_subset_1])).
% 1.90/2.10  thf('2', plain,
% 1.90/2.10      (((k3_subset_1 @ sk_A @ sk_B_2) = (k4_xboole_0 @ sk_A @ sk_B_2))),
% 1.90/2.10      inference('sup-', [status(thm)], ['0', '1'])).
% 1.90/2.10  thf(t36_xboole_1, axiom,
% 1.90/2.10    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 1.90/2.10  thf('3', plain,
% 1.90/2.10      (![X19 : $i, X20 : $i]: (r1_tarski @ (k4_xboole_0 @ X19 @ X20) @ X19)),
% 1.90/2.10      inference('cnf', [status(esa)], [t36_xboole_1])).
% 1.90/2.10  thf('4', plain, ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B_2) @ sk_A)),
% 1.90/2.10      inference('sup+', [status(thm)], ['2', '3'])).
% 1.90/2.10  thf(d1_zfmisc_1, axiom,
% 1.90/2.10    (![A:$i,B:$i]:
% 1.90/2.10     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 1.90/2.10       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 1.90/2.10  thf('5', plain,
% 1.90/2.10      (![X60 : $i, X61 : $i, X62 : $i]:
% 1.90/2.10         (~ (r1_tarski @ X60 @ X61)
% 1.90/2.10          | (r2_hidden @ X60 @ X62)
% 1.90/2.10          | ((X62) != (k1_zfmisc_1 @ X61)))),
% 1.90/2.10      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 1.90/2.10  thf('6', plain,
% 1.90/2.10      (![X60 : $i, X61 : $i]:
% 1.90/2.10         ((r2_hidden @ X60 @ (k1_zfmisc_1 @ X61)) | ~ (r1_tarski @ X60 @ X61))),
% 1.90/2.10      inference('simplify', [status(thm)], ['5'])).
% 1.90/2.10  thf('7', plain,
% 1.90/2.10      ((r2_hidden @ (k3_subset_1 @ sk_A @ sk_B_2) @ (k1_zfmisc_1 @ sk_A))),
% 1.90/2.10      inference('sup-', [status(thm)], ['4', '6'])).
% 1.90/2.10  thf(d2_subset_1, axiom,
% 1.90/2.10    (![A:$i,B:$i]:
% 1.90/2.10     ( ( ( v1_xboole_0 @ A ) =>
% 1.90/2.10         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 1.90/2.10       ( ( ~( v1_xboole_0 @ A ) ) =>
% 1.90/2.10         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 1.90/2.10  thf('8', plain,
% 1.90/2.10      (![X67 : $i, X68 : $i]:
% 1.90/2.10         (~ (r2_hidden @ X67 @ X68)
% 1.90/2.10          | (m1_subset_1 @ X67 @ X68)
% 1.90/2.10          | (v1_xboole_0 @ X68))),
% 1.90/2.10      inference('cnf', [status(esa)], [d2_subset_1])).
% 1.90/2.10  thf(d1_xboole_0, axiom,
% 1.90/2.10    (![A:$i]:
% 1.90/2.10     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 1.90/2.10  thf('9', plain,
% 1.90/2.10      (![X4 : $i, X5 : $i]: (~ (r2_hidden @ X4 @ X5) | ~ (v1_xboole_0 @ X5))),
% 1.90/2.10      inference('cnf', [status(esa)], [d1_xboole_0])).
% 1.90/2.10  thf('10', plain,
% 1.90/2.10      (![X67 : $i, X68 : $i]:
% 1.90/2.10         ((m1_subset_1 @ X67 @ X68) | ~ (r2_hidden @ X67 @ X68))),
% 1.90/2.10      inference('clc', [status(thm)], ['8', '9'])).
% 1.90/2.10  thf('11', plain,
% 1.90/2.10      ((m1_subset_1 @ (k3_subset_1 @ sk_A @ sk_B_2) @ (k1_zfmisc_1 @ sk_A))),
% 1.90/2.10      inference('sup-', [status(thm)], ['7', '10'])).
% 1.90/2.10  thf('12', plain, ((m1_subset_1 @ sk_B_2 @ (k1_zfmisc_1 @ sk_A))),
% 1.90/2.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.90/2.10  thf(redefinition_k4_subset_1, axiom,
% 1.90/2.10    (![A:$i,B:$i,C:$i]:
% 1.90/2.10     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 1.90/2.10         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 1.90/2.10       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 1.90/2.10  thf('13', plain,
% 1.90/2.10      (![X74 : $i, X75 : $i, X76 : $i]:
% 1.90/2.10         (~ (m1_subset_1 @ X74 @ (k1_zfmisc_1 @ X75))
% 1.90/2.10          | ~ (m1_subset_1 @ X76 @ (k1_zfmisc_1 @ X75))
% 1.90/2.10          | ((k4_subset_1 @ X75 @ X74 @ X76) = (k2_xboole_0 @ X74 @ X76)))),
% 1.90/2.10      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 1.90/2.10  thf(l51_zfmisc_1, axiom,
% 1.90/2.10    (![A:$i,B:$i]:
% 1.90/2.10     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 1.90/2.10  thf('14', plain,
% 1.90/2.10      (![X65 : $i, X66 : $i]:
% 1.90/2.10         ((k3_tarski @ (k2_tarski @ X65 @ X66)) = (k2_xboole_0 @ X65 @ X66))),
% 1.90/2.10      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 1.90/2.10  thf('15', plain,
% 1.90/2.10      (![X74 : $i, X75 : $i, X76 : $i]:
% 1.90/2.10         (~ (m1_subset_1 @ X74 @ (k1_zfmisc_1 @ X75))
% 1.90/2.10          | ~ (m1_subset_1 @ X76 @ (k1_zfmisc_1 @ X75))
% 1.90/2.10          | ((k4_subset_1 @ X75 @ X74 @ X76)
% 1.90/2.10              = (k3_tarski @ (k2_tarski @ X74 @ X76))))),
% 1.90/2.10      inference('demod', [status(thm)], ['13', '14'])).
% 1.90/2.10  thf('16', plain,
% 1.90/2.10      (![X0 : $i]:
% 1.90/2.10         (((k4_subset_1 @ sk_A @ sk_B_2 @ X0)
% 1.90/2.10            = (k3_tarski @ (k2_tarski @ sk_B_2 @ X0)))
% 1.90/2.10          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A)))),
% 1.90/2.10      inference('sup-', [status(thm)], ['12', '15'])).
% 1.90/2.10  thf('17', plain,
% 1.90/2.10      (((k4_subset_1 @ sk_A @ sk_B_2 @ (k3_subset_1 @ sk_A @ sk_B_2))
% 1.90/2.10         = (k3_tarski @ (k2_tarski @ sk_B_2 @ (k3_subset_1 @ sk_A @ sk_B_2))))),
% 1.90/2.10      inference('sup-', [status(thm)], ['11', '16'])).
% 1.90/2.10  thf('18', plain,
% 1.90/2.10      (((k3_subset_1 @ sk_A @ sk_B_2) = (k4_xboole_0 @ sk_A @ sk_B_2))),
% 1.90/2.10      inference('sup-', [status(thm)], ['0', '1'])).
% 1.90/2.10  thf(t48_xboole_1, axiom,
% 1.90/2.10    (![A:$i,B:$i]:
% 1.90/2.10     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 1.90/2.10  thf('19', plain,
% 1.90/2.10      (![X23 : $i, X24 : $i]:
% 1.90/2.10         ((k4_xboole_0 @ X23 @ (k4_xboole_0 @ X23 @ X24))
% 1.90/2.10           = (k3_xboole_0 @ X23 @ X24))),
% 1.90/2.10      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.90/2.10  thf('20', plain,
% 1.90/2.10      (((k4_xboole_0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B_2))
% 1.90/2.10         = (k3_xboole_0 @ sk_A @ sk_B_2))),
% 1.90/2.10      inference('sup+', [status(thm)], ['18', '19'])).
% 1.90/2.10  thf(commutativity_k3_xboole_0, axiom,
% 1.90/2.10    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 1.90/2.10  thf('21', plain,
% 1.90/2.10      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.90/2.10      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.90/2.10  thf('22', plain,
% 1.90/2.10      (((k4_xboole_0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B_2))
% 1.90/2.10         = (k3_xboole_0 @ sk_B_2 @ sk_A))),
% 1.90/2.10      inference('demod', [status(thm)], ['20', '21'])).
% 1.90/2.10  thf('23', plain, ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B_2) @ sk_A)),
% 1.90/2.10      inference('sup+', [status(thm)], ['2', '3'])).
% 1.90/2.10  thf(t28_xboole_1, axiom,
% 1.90/2.10    (![A:$i,B:$i]:
% 1.90/2.10     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 1.90/2.10  thf('24', plain,
% 1.90/2.10      (![X17 : $i, X18 : $i]:
% 1.90/2.10         (((k3_xboole_0 @ X17 @ X18) = (X17)) | ~ (r1_tarski @ X17 @ X18))),
% 1.90/2.10      inference('cnf', [status(esa)], [t28_xboole_1])).
% 1.90/2.10  thf('25', plain,
% 1.90/2.10      (((k3_xboole_0 @ (k3_subset_1 @ sk_A @ sk_B_2) @ sk_A)
% 1.90/2.10         = (k3_subset_1 @ sk_A @ sk_B_2))),
% 1.90/2.10      inference('sup-', [status(thm)], ['23', '24'])).
% 1.90/2.10  thf('26', plain,
% 1.90/2.10      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.90/2.10      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.90/2.10  thf('27', plain,
% 1.90/2.10      (((k3_xboole_0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B_2))
% 1.90/2.10         = (k3_subset_1 @ sk_A @ sk_B_2))),
% 1.90/2.10      inference('demod', [status(thm)], ['25', '26'])).
% 1.90/2.10  thf(t100_xboole_1, axiom,
% 1.90/2.10    (![A:$i,B:$i]:
% 1.90/2.10     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 1.90/2.10  thf('28', plain,
% 1.90/2.10      (![X15 : $i, X16 : $i]:
% 1.90/2.10         ((k4_xboole_0 @ X15 @ X16)
% 1.90/2.10           = (k5_xboole_0 @ X15 @ (k3_xboole_0 @ X15 @ X16)))),
% 1.90/2.10      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.90/2.10  thf('29', plain,
% 1.90/2.10      (((k4_xboole_0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B_2))
% 1.90/2.10         = (k5_xboole_0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B_2)))),
% 1.90/2.10      inference('sup+', [status(thm)], ['27', '28'])).
% 1.90/2.10  thf('30', plain,
% 1.90/2.10      (((k3_xboole_0 @ sk_B_2 @ sk_A)
% 1.90/2.10         = (k5_xboole_0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B_2)))),
% 1.90/2.10      inference('sup+', [status(thm)], ['22', '29'])).
% 1.90/2.10  thf('31', plain, ((m1_subset_1 @ sk_B_2 @ (k1_zfmisc_1 @ sk_A))),
% 1.90/2.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.90/2.10  thf('32', plain,
% 1.90/2.10      (![X67 : $i, X68 : $i]:
% 1.90/2.10         (~ (m1_subset_1 @ X67 @ X68)
% 1.90/2.10          | (r2_hidden @ X67 @ X68)
% 1.90/2.10          | (v1_xboole_0 @ X68))),
% 1.90/2.10      inference('cnf', [status(esa)], [d2_subset_1])).
% 1.90/2.10  thf('33', plain,
% 1.90/2.10      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 1.90/2.10        | (r2_hidden @ sk_B_2 @ (k1_zfmisc_1 @ sk_A)))),
% 1.90/2.10      inference('sup-', [status(thm)], ['31', '32'])).
% 1.90/2.10  thf(fc1_subset_1, axiom,
% 1.90/2.10    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 1.90/2.10  thf('34', plain, (![X73 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X73))),
% 1.90/2.10      inference('cnf', [status(esa)], [fc1_subset_1])).
% 1.90/2.10  thf('35', plain, ((r2_hidden @ sk_B_2 @ (k1_zfmisc_1 @ sk_A))),
% 1.90/2.10      inference('clc', [status(thm)], ['33', '34'])).
% 1.90/2.10  thf('36', plain,
% 1.90/2.10      (![X61 : $i, X62 : $i, X63 : $i]:
% 1.90/2.10         (~ (r2_hidden @ X63 @ X62)
% 1.90/2.10          | (r1_tarski @ X63 @ X61)
% 1.90/2.10          | ((X62) != (k1_zfmisc_1 @ X61)))),
% 1.90/2.10      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 1.90/2.10  thf('37', plain,
% 1.90/2.10      (![X61 : $i, X63 : $i]:
% 1.90/2.10         ((r1_tarski @ X63 @ X61) | ~ (r2_hidden @ X63 @ (k1_zfmisc_1 @ X61)))),
% 1.90/2.10      inference('simplify', [status(thm)], ['36'])).
% 1.90/2.10  thf('38', plain, ((r1_tarski @ sk_B_2 @ sk_A)),
% 1.90/2.10      inference('sup-', [status(thm)], ['35', '37'])).
% 1.90/2.10  thf('39', plain,
% 1.90/2.10      (![X17 : $i, X18 : $i]:
% 1.90/2.10         (((k3_xboole_0 @ X17 @ X18) = (X17)) | ~ (r1_tarski @ X17 @ X18))),
% 1.90/2.10      inference('cnf', [status(esa)], [t28_xboole_1])).
% 1.90/2.10  thf('40', plain, (((k3_xboole_0 @ sk_B_2 @ sk_A) = (sk_B_2))),
% 1.90/2.10      inference('sup-', [status(thm)], ['38', '39'])).
% 1.90/2.10  thf('41', plain,
% 1.90/2.10      (((sk_B_2) = (k5_xboole_0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B_2)))),
% 1.90/2.10      inference('demod', [status(thm)], ['30', '40'])).
% 1.90/2.10  thf(t93_xboole_1, axiom,
% 1.90/2.10    (![A:$i,B:$i]:
% 1.90/2.10     ( ( k2_xboole_0 @ A @ B ) =
% 1.90/2.10       ( k2_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ))).
% 1.90/2.10  thf('42', plain,
% 1.90/2.10      (![X29 : $i, X30 : $i]:
% 1.90/2.10         ((k2_xboole_0 @ X29 @ X30)
% 1.90/2.10           = (k2_xboole_0 @ (k5_xboole_0 @ X29 @ X30) @ 
% 1.90/2.10              (k3_xboole_0 @ X29 @ X30)))),
% 1.90/2.10      inference('cnf', [status(esa)], [t93_xboole_1])).
% 1.90/2.10  thf('43', plain,
% 1.90/2.10      (![X65 : $i, X66 : $i]:
% 1.90/2.10         ((k3_tarski @ (k2_tarski @ X65 @ X66)) = (k2_xboole_0 @ X65 @ X66))),
% 1.90/2.10      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 1.90/2.10  thf('44', plain,
% 1.90/2.10      (![X65 : $i, X66 : $i]:
% 1.90/2.10         ((k3_tarski @ (k2_tarski @ X65 @ X66)) = (k2_xboole_0 @ X65 @ X66))),
% 1.90/2.10      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 1.90/2.10  thf('45', plain,
% 1.90/2.10      (![X29 : $i, X30 : $i]:
% 1.90/2.10         ((k3_tarski @ (k2_tarski @ X29 @ X30))
% 1.90/2.10           = (k3_tarski @ 
% 1.90/2.10              (k2_tarski @ (k5_xboole_0 @ X29 @ X30) @ 
% 1.90/2.10               (k3_xboole_0 @ X29 @ X30))))),
% 1.90/2.10      inference('demod', [status(thm)], ['42', '43', '44'])).
% 1.90/2.10  thf('46', plain,
% 1.90/2.10      (((k3_tarski @ (k2_tarski @ sk_A @ (k3_subset_1 @ sk_A @ sk_B_2)))
% 1.90/2.10         = (k3_tarski @ 
% 1.90/2.10            (k2_tarski @ sk_B_2 @ 
% 1.90/2.10             (k3_xboole_0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B_2)))))),
% 1.90/2.10      inference('sup+', [status(thm)], ['41', '45'])).
% 1.90/2.10  thf('47', plain,
% 1.90/2.10      (((k3_xboole_0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B_2))
% 1.90/2.10         = (k3_subset_1 @ sk_A @ sk_B_2))),
% 1.90/2.10      inference('demod', [status(thm)], ['25', '26'])).
% 1.90/2.10  thf(t94_xboole_1, axiom,
% 1.90/2.10    (![A:$i,B:$i]:
% 1.90/2.10     ( ( k2_xboole_0 @ A @ B ) =
% 1.90/2.10       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ))).
% 1.90/2.10  thf('48', plain,
% 1.90/2.10      (![X31 : $i, X32 : $i]:
% 1.90/2.10         ((k2_xboole_0 @ X31 @ X32)
% 1.90/2.10           = (k5_xboole_0 @ (k5_xboole_0 @ X31 @ X32) @ 
% 1.90/2.10              (k3_xboole_0 @ X31 @ X32)))),
% 1.90/2.10      inference('cnf', [status(esa)], [t94_xboole_1])).
% 1.90/2.10  thf('49', plain,
% 1.90/2.10      (![X65 : $i, X66 : $i]:
% 1.90/2.10         ((k3_tarski @ (k2_tarski @ X65 @ X66)) = (k2_xboole_0 @ X65 @ X66))),
% 1.90/2.10      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 1.90/2.10  thf(t91_xboole_1, axiom,
% 1.90/2.10    (![A:$i,B:$i,C:$i]:
% 1.90/2.10     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 1.90/2.10       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 1.90/2.10  thf('50', plain,
% 1.90/2.10      (![X26 : $i, X27 : $i, X28 : $i]:
% 1.90/2.10         ((k5_xboole_0 @ (k5_xboole_0 @ X26 @ X27) @ X28)
% 1.90/2.10           = (k5_xboole_0 @ X26 @ (k5_xboole_0 @ X27 @ X28)))),
% 1.90/2.10      inference('cnf', [status(esa)], [t91_xboole_1])).
% 1.90/2.10  thf('51', plain,
% 1.90/2.10      (![X31 : $i, X32 : $i]:
% 1.90/2.10         ((k3_tarski @ (k2_tarski @ X31 @ X32))
% 1.90/2.10           = (k5_xboole_0 @ X31 @ 
% 1.90/2.10              (k5_xboole_0 @ X32 @ (k3_xboole_0 @ X31 @ X32))))),
% 1.90/2.10      inference('demod', [status(thm)], ['48', '49', '50'])).
% 1.90/2.10  thf('52', plain,
% 1.90/2.10      (((k3_tarski @ (k2_tarski @ sk_A @ (k3_subset_1 @ sk_A @ sk_B_2)))
% 1.90/2.10         = (k5_xboole_0 @ sk_A @ 
% 1.90/2.10            (k5_xboole_0 @ (k3_subset_1 @ sk_A @ sk_B_2) @ 
% 1.90/2.10             (k3_subset_1 @ sk_A @ sk_B_2))))),
% 1.90/2.10      inference('sup+', [status(thm)], ['47', '51'])).
% 1.90/2.10  thf(t7_xboole_0, axiom,
% 1.90/2.10    (![A:$i]:
% 1.90/2.10     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 1.90/2.10          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 1.90/2.10  thf('53', plain,
% 1.90/2.10      (![X14 : $i]:
% 1.90/2.10         (((X14) = (k1_xboole_0)) | (r2_hidden @ (sk_B_1 @ X14) @ X14))),
% 1.90/2.10      inference('cnf', [status(esa)], [t7_xboole_0])).
% 1.90/2.10  thf(idempotence_k3_xboole_0, axiom,
% 1.90/2.10    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 1.90/2.10  thf('54', plain, (![X13 : $i]: ((k3_xboole_0 @ X13 @ X13) = (X13))),
% 1.90/2.10      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 1.90/2.10  thf('55', plain,
% 1.90/2.10      (![X15 : $i, X16 : $i]:
% 1.90/2.10         ((k4_xboole_0 @ X15 @ X16)
% 1.90/2.10           = (k5_xboole_0 @ X15 @ (k3_xboole_0 @ X15 @ X16)))),
% 1.90/2.10      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.90/2.10  thf('56', plain,
% 1.90/2.10      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 1.90/2.10      inference('sup+', [status(thm)], ['54', '55'])).
% 1.90/2.10  thf(d5_xboole_0, axiom,
% 1.90/2.10    (![A:$i,B:$i,C:$i]:
% 1.90/2.10     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 1.90/2.10       ( ![D:$i]:
% 1.90/2.10         ( ( r2_hidden @ D @ C ) <=>
% 1.90/2.10           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 1.90/2.10  thf('57', plain,
% 1.90/2.10      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 1.90/2.10         (~ (r2_hidden @ X11 @ X10)
% 1.90/2.10          | (r2_hidden @ X11 @ X8)
% 1.90/2.10          | ((X10) != (k4_xboole_0 @ X8 @ X9)))),
% 1.90/2.10      inference('cnf', [status(esa)], [d5_xboole_0])).
% 1.90/2.10  thf('58', plain,
% 1.90/2.10      (![X8 : $i, X9 : $i, X11 : $i]:
% 1.90/2.10         ((r2_hidden @ X11 @ X8)
% 1.90/2.10          | ~ (r2_hidden @ X11 @ (k4_xboole_0 @ X8 @ X9)))),
% 1.90/2.10      inference('simplify', [status(thm)], ['57'])).
% 1.90/2.10  thf('59', plain,
% 1.90/2.10      (![X0 : $i, X1 : $i]:
% 1.90/2.10         (~ (r2_hidden @ X1 @ (k5_xboole_0 @ X0 @ X0)) | (r2_hidden @ X1 @ X0))),
% 1.90/2.10      inference('sup-', [status(thm)], ['56', '58'])).
% 1.90/2.10  thf('60', plain,
% 1.90/2.10      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 1.90/2.10      inference('sup+', [status(thm)], ['54', '55'])).
% 1.90/2.10  thf('61', plain,
% 1.90/2.10      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 1.90/2.10         (~ (r2_hidden @ X11 @ X10)
% 1.90/2.10          | ~ (r2_hidden @ X11 @ X9)
% 1.90/2.10          | ((X10) != (k4_xboole_0 @ X8 @ X9)))),
% 1.90/2.10      inference('cnf', [status(esa)], [d5_xboole_0])).
% 1.90/2.10  thf('62', plain,
% 1.90/2.10      (![X8 : $i, X9 : $i, X11 : $i]:
% 1.90/2.10         (~ (r2_hidden @ X11 @ X9)
% 1.90/2.10          | ~ (r2_hidden @ X11 @ (k4_xboole_0 @ X8 @ X9)))),
% 1.90/2.10      inference('simplify', [status(thm)], ['61'])).
% 1.90/2.10  thf('63', plain,
% 1.90/2.10      (![X0 : $i, X1 : $i]:
% 1.90/2.10         (~ (r2_hidden @ X1 @ (k5_xboole_0 @ X0 @ X0))
% 1.90/2.10          | ~ (r2_hidden @ X1 @ X0))),
% 1.90/2.10      inference('sup-', [status(thm)], ['60', '62'])).
% 1.90/2.10  thf('64', plain,
% 1.90/2.10      (![X0 : $i, X1 : $i]: ~ (r2_hidden @ X1 @ (k5_xboole_0 @ X0 @ X0))),
% 1.90/2.10      inference('clc', [status(thm)], ['59', '63'])).
% 1.90/2.10  thf('65', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 1.90/2.10      inference('sup-', [status(thm)], ['53', '64'])).
% 1.90/2.10  thf(commutativity_k5_xboole_0, axiom,
% 1.90/2.10    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 1.90/2.10  thf('66', plain,
% 1.90/2.10      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 1.90/2.10      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 1.90/2.10  thf('67', plain,
% 1.90/2.10      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 1.90/2.10      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 1.90/2.10  thf(t5_boole, axiom,
% 1.90/2.10    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 1.90/2.10  thf('68', plain, (![X25 : $i]: ((k5_xboole_0 @ X25 @ k1_xboole_0) = (X25))),
% 1.90/2.10      inference('cnf', [status(esa)], [t5_boole])).
% 1.90/2.10  thf('69', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 1.90/2.10      inference('sup+', [status(thm)], ['67', '68'])).
% 1.90/2.10  thf('70', plain,
% 1.90/2.10      (((k3_tarski @ (k2_tarski @ sk_A @ (k3_subset_1 @ sk_A @ sk_B_2)))
% 1.90/2.10         = (sk_A))),
% 1.90/2.10      inference('demod', [status(thm)], ['52', '65', '66', '69'])).
% 1.90/2.10  thf('71', plain,
% 1.90/2.10      (((k3_xboole_0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B_2))
% 1.90/2.10         = (k3_subset_1 @ sk_A @ sk_B_2))),
% 1.90/2.10      inference('demod', [status(thm)], ['25', '26'])).
% 1.90/2.10  thf('72', plain,
% 1.90/2.10      (((sk_A)
% 1.90/2.10         = (k3_tarski @ (k2_tarski @ sk_B_2 @ (k3_subset_1 @ sk_A @ sk_B_2))))),
% 1.90/2.10      inference('demod', [status(thm)], ['46', '70', '71'])).
% 1.90/2.10  thf('73', plain,
% 1.90/2.10      (((k4_subset_1 @ sk_A @ sk_B_2 @ (k3_subset_1 @ sk_A @ sk_B_2)) = (sk_A))),
% 1.90/2.10      inference('demod', [status(thm)], ['17', '72'])).
% 1.90/2.10  thf('74', plain,
% 1.90/2.10      (((k4_subset_1 @ sk_A @ sk_B_2 @ (k3_subset_1 @ sk_A @ sk_B_2))
% 1.90/2.10         != (k2_subset_1 @ sk_A))),
% 1.90/2.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.90/2.10  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 1.90/2.10  thf('75', plain, (![X70 : $i]: ((k2_subset_1 @ X70) = (X70))),
% 1.90/2.10      inference('cnf', [status(esa)], [d4_subset_1])).
% 1.90/2.10  thf('76', plain,
% 1.90/2.10      (((k4_subset_1 @ sk_A @ sk_B_2 @ (k3_subset_1 @ sk_A @ sk_B_2)) != (sk_A))),
% 1.90/2.10      inference('demod', [status(thm)], ['74', '75'])).
% 1.90/2.10  thf('77', plain, ($false),
% 1.90/2.10      inference('simplify_reflect-', [status(thm)], ['73', '76'])).
% 1.90/2.10  
% 1.90/2.10  % SZS output end Refutation
% 1.90/2.10  
% 1.90/2.11  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
