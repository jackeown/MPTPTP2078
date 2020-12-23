%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.vCezk9dCcc

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:36:52 EST 2020

% Result     : Theorem 0.40s
% Output     : Refutation 0.40s
% Verified   : 
% Statistics : Number of formulae       :  114 ( 139 expanded)
%              Number of leaves         :   39 (  57 expanded)
%              Depth                    :   12
%              Number of atoms          :  733 ( 975 expanded)
%              Number of equality atoms :   73 (  96 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

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
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('1',plain,(
    ! [X67: $i,X68: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X67 @ X68 ) @ ( k1_zfmisc_1 @ X67 ) )
      | ~ ( m1_subset_1 @ X68 @ ( k1_zfmisc_1 @ X67 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('2',plain,(
    m1_subset_1 @ ( k3_subset_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('4',plain,(
    ! [X70: $i,X71: $i,X72: $i] :
      ( ~ ( m1_subset_1 @ X70 @ ( k1_zfmisc_1 @ X71 ) )
      | ~ ( m1_subset_1 @ X72 @ ( k1_zfmisc_1 @ X71 ) )
      | ( ( k4_subset_1 @ X71 @ X70 @ X72 )
        = ( k2_xboole_0 @ X70 @ X72 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('5',plain,(
    ! [X59: $i,X60: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X59 @ X60 ) )
      = ( k2_xboole_0 @ X59 @ X60 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('6',plain,(
    ! [X70: $i,X71: $i,X72: $i] :
      ( ~ ( m1_subset_1 @ X70 @ ( k1_zfmisc_1 @ X71 ) )
      | ~ ( m1_subset_1 @ X72 @ ( k1_zfmisc_1 @ X71 ) )
      | ( ( k4_subset_1 @ X71 @ X70 @ X72 )
        = ( k3_tarski @ ( k2_tarski @ X70 @ X72 ) ) ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ sk_A @ sk_B @ X0 )
        = ( k3_tarski @ ( k2_tarski @ sk_B @ X0 ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['3','6'])).

thf('8',plain,
    ( ( k4_subset_1 @ sk_A @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = ( k3_tarski @ ( k2_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['2','7'])).

thf('9',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('10',plain,(
    ! [X65: $i,X66: $i] :
      ( ( ( k3_subset_1 @ X65 @ X66 )
        = ( k4_xboole_0 @ X65 @ X66 ) )
      | ~ ( m1_subset_1 @ X66 @ ( k1_zfmisc_1 @ X65 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('11',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf(t79_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ) )).

thf('12',plain,(
    ! [X21: $i,X22: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X21 @ X22 ) @ X22 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf('13',plain,(
    r1_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ),
    inference('sup+',[status(thm)],['11','12'])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('14',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k3_xboole_0 @ X4 @ X5 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('15',plain,
    ( ( k3_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['13','14'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('17',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['15','16'])).

thf(l98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('18',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k5_xboole_0 @ X7 @ X8 )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X7 @ X8 ) @ ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[l98_xboole_1])).

thf('19',plain,(
    ! [X59: $i,X60: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X59 @ X60 ) )
      = ( k2_xboole_0 @ X59 @ X60 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('20',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k5_xboole_0 @ X7 @ X8 )
      = ( k4_xboole_0 @ ( k3_tarski @ ( k2_tarski @ X7 @ X8 ) ) @ ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,
    ( ( k5_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = ( k4_xboole_0 @ ( k3_tarski @ ( k2_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) ) @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['17','20'])).

thf('22',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('23',plain,(
    ! [X61: $i,X62: $i] :
      ( ~ ( m1_subset_1 @ X61 @ X62 )
      | ( r2_hidden @ X61 @ X62 )
      | ( v1_xboole_0 @ X62 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('24',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('25',plain,(
    ! [X69: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X69 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('26',plain,(
    r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['24','25'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('27',plain,(
    ! [X55: $i,X56: $i,X57: $i] :
      ( ~ ( r2_hidden @ X57 @ X56 )
      | ( r1_tarski @ X57 @ X55 )
      | ( X56
       != ( k1_zfmisc_1 @ X55 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('28',plain,(
    ! [X55: $i,X57: $i] :
      ( ( r1_tarski @ X57 @ X55 )
      | ~ ( r2_hidden @ X57 @ ( k1_zfmisc_1 @ X55 ) ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['26','28'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('30',plain,(
    ! [X18: $i,X19: $i] :
      ( ( ( k3_xboole_0 @ X18 @ X19 )
        = X18 )
      | ~ ( r1_tarski @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('31',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_A )
    = sk_B ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('33',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ X10 )
      = ( k5_xboole_0 @ X9 @ ( k3_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('35',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = ( k5_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['31','34'])).

thf('36',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

thf('37',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('38',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k5_xboole_0 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['35','36','37'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('39',plain,(
    ! [X26: $i] :
      ( ( k5_xboole_0 @ X26 @ X26 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('40',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X23 @ X24 ) @ X25 )
      = ( k5_xboole_0 @ X23 @ ( k5_xboole_0 @ X24 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('43',plain,(
    ! [X20: $i] :
      ( ( k5_xboole_0 @ X20 @ k1_xboole_0 )
      = X20 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['41','44'])).

thf('46',plain,
    ( sk_A
    = ( k5_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['38','45'])).

thf(t21_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = A ) )).

thf('47',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k3_xboole_0 @ X16 @ ( k2_xboole_0 @ X16 @ X17 ) )
      = X16 ) ),
    inference(cnf,[status(esa)],[t21_xboole_1])).

thf('48',plain,(
    ! [X59: $i,X60: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X59 @ X60 ) )
      = ( k2_xboole_0 @ X59 @ X60 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('49',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k3_xboole_0 @ X16 @ ( k3_tarski @ ( k2_tarski @ X16 @ X17 ) ) )
      = X16 ) ),
    inference(demod,[status(thm)],['47','48'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('50',plain,(
    ! [X14: $i,X15: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X14 @ X15 ) @ X14 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('51',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X18: $i,X19: $i] :
      ( ( ( k3_xboole_0 @ X18 @ X19 )
        = X18 )
      | ~ ( r1_tarski @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ X10 )
      = ( k5_xboole_0 @ X9 @ ( k3_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X26: $i] :
      ( ( k5_xboole_0 @ X26 @ X26 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X21: $i,X22: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X21 @ X22 ) @ X22 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf('59',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k3_xboole_0 @ X4 @ X5 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ X10 )
      = ( k5_xboole_0 @ X9 @ ( k3_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X20: $i] :
      ( ( k5_xboole_0 @ X20 @ k1_xboole_0 )
      = X20 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['57','66'])).

thf('68',plain,
    ( sk_A
    = ( k3_tarski @ ( k2_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['21','46','67'])).

thf('69',plain,
    ( ( k4_subset_1 @ sk_A @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = sk_A ),
    inference(demod,[status(thm)],['8','68'])).

thf('70',plain,(
    ( k4_subset_1 @ sk_A @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
 != ( k2_subset_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('71',plain,(
    ! [X64: $i] :
      ( ( k2_subset_1 @ X64 )
      = X64 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('72',plain,(
    ( k4_subset_1 @ sk_A @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
 != sk_A ),
    inference(demod,[status(thm)],['70','71'])).

thf('73',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['69','72'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.vCezk9dCcc
% 0.14/0.34  % Computer   : n024.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:53:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.40/0.63  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.40/0.63  % Solved by: fo/fo7.sh
% 0.40/0.63  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.40/0.63  % done 498 iterations in 0.173s
% 0.40/0.63  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.40/0.63  % SZS output start Refutation
% 0.40/0.63  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.40/0.63  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.40/0.63  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.40/0.63  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.40/0.63  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.40/0.63  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.40/0.63  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.40/0.63  thf(sk_A_type, type, sk_A: $i).
% 0.40/0.63  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.40/0.63  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.40/0.63  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.40/0.63  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.40/0.63  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.40/0.63  thf(sk_B_type, type, sk_B: $i).
% 0.40/0.63  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.40/0.63  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 0.40/0.63  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.40/0.63  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.40/0.63  thf(t25_subset_1, conjecture,
% 0.40/0.63    (![A:$i,B:$i]:
% 0.40/0.63     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.40/0.63       ( ( k4_subset_1 @ A @ B @ ( k3_subset_1 @ A @ B ) ) =
% 0.40/0.63         ( k2_subset_1 @ A ) ) ))).
% 0.40/0.63  thf(zf_stmt_0, negated_conjecture,
% 0.40/0.63    (~( ![A:$i,B:$i]:
% 0.40/0.63        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.40/0.63          ( ( k4_subset_1 @ A @ B @ ( k3_subset_1 @ A @ B ) ) =
% 0.40/0.63            ( k2_subset_1 @ A ) ) ) )),
% 0.40/0.63    inference('cnf.neg', [status(esa)], [t25_subset_1])).
% 0.40/0.63  thf('0', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.40/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.63  thf(dt_k3_subset_1, axiom,
% 0.40/0.63    (![A:$i,B:$i]:
% 0.40/0.63     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.40/0.63       ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.40/0.63  thf('1', plain,
% 0.40/0.63      (![X67 : $i, X68 : $i]:
% 0.40/0.63         ((m1_subset_1 @ (k3_subset_1 @ X67 @ X68) @ (k1_zfmisc_1 @ X67))
% 0.40/0.63          | ~ (m1_subset_1 @ X68 @ (k1_zfmisc_1 @ X67)))),
% 0.40/0.63      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 0.40/0.63  thf('2', plain,
% 0.40/0.63      ((m1_subset_1 @ (k3_subset_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_A))),
% 0.40/0.63      inference('sup-', [status(thm)], ['0', '1'])).
% 0.40/0.63  thf('3', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.40/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.63  thf(redefinition_k4_subset_1, axiom,
% 0.40/0.63    (![A:$i,B:$i,C:$i]:
% 0.40/0.63     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 0.40/0.63         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.40/0.63       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 0.40/0.63  thf('4', plain,
% 0.40/0.63      (![X70 : $i, X71 : $i, X72 : $i]:
% 0.40/0.63         (~ (m1_subset_1 @ X70 @ (k1_zfmisc_1 @ X71))
% 0.40/0.63          | ~ (m1_subset_1 @ X72 @ (k1_zfmisc_1 @ X71))
% 0.40/0.63          | ((k4_subset_1 @ X71 @ X70 @ X72) = (k2_xboole_0 @ X70 @ X72)))),
% 0.40/0.63      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 0.40/0.63  thf(l51_zfmisc_1, axiom,
% 0.40/0.63    (![A:$i,B:$i]:
% 0.40/0.63     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.40/0.63  thf('5', plain,
% 0.40/0.63      (![X59 : $i, X60 : $i]:
% 0.40/0.63         ((k3_tarski @ (k2_tarski @ X59 @ X60)) = (k2_xboole_0 @ X59 @ X60))),
% 0.40/0.63      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.40/0.63  thf('6', plain,
% 0.40/0.63      (![X70 : $i, X71 : $i, X72 : $i]:
% 0.40/0.63         (~ (m1_subset_1 @ X70 @ (k1_zfmisc_1 @ X71))
% 0.40/0.63          | ~ (m1_subset_1 @ X72 @ (k1_zfmisc_1 @ X71))
% 0.40/0.63          | ((k4_subset_1 @ X71 @ X70 @ X72)
% 0.40/0.63              = (k3_tarski @ (k2_tarski @ X70 @ X72))))),
% 0.40/0.63      inference('demod', [status(thm)], ['4', '5'])).
% 0.40/0.63  thf('7', plain,
% 0.40/0.63      (![X0 : $i]:
% 0.40/0.63         (((k4_subset_1 @ sk_A @ sk_B @ X0)
% 0.40/0.63            = (k3_tarski @ (k2_tarski @ sk_B @ X0)))
% 0.40/0.63          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A)))),
% 0.40/0.63      inference('sup-', [status(thm)], ['3', '6'])).
% 0.40/0.63  thf('8', plain,
% 0.40/0.63      (((k4_subset_1 @ sk_A @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))
% 0.40/0.63         = (k3_tarski @ (k2_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))))),
% 0.40/0.63      inference('sup-', [status(thm)], ['2', '7'])).
% 0.40/0.63  thf('9', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.40/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.63  thf(d5_subset_1, axiom,
% 0.40/0.63    (![A:$i,B:$i]:
% 0.40/0.63     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.40/0.63       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.40/0.63  thf('10', plain,
% 0.40/0.63      (![X65 : $i, X66 : $i]:
% 0.40/0.63         (((k3_subset_1 @ X65 @ X66) = (k4_xboole_0 @ X65 @ X66))
% 0.40/0.63          | ~ (m1_subset_1 @ X66 @ (k1_zfmisc_1 @ X65)))),
% 0.40/0.63      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.40/0.63  thf('11', plain,
% 0.40/0.63      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.40/0.63      inference('sup-', [status(thm)], ['9', '10'])).
% 0.40/0.63  thf(t79_xboole_1, axiom,
% 0.40/0.63    (![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ))).
% 0.40/0.63  thf('12', plain,
% 0.40/0.63      (![X21 : $i, X22 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X21 @ X22) @ X22)),
% 0.40/0.63      inference('cnf', [status(esa)], [t79_xboole_1])).
% 0.40/0.63  thf('13', plain, ((r1_xboole_0 @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)),
% 0.40/0.63      inference('sup+', [status(thm)], ['11', '12'])).
% 0.40/0.63  thf(d7_xboole_0, axiom,
% 0.40/0.63    (![A:$i,B:$i]:
% 0.40/0.63     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.40/0.63       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.40/0.63  thf('14', plain,
% 0.40/0.63      (![X4 : $i, X5 : $i]:
% 0.40/0.63         (((k3_xboole_0 @ X4 @ X5) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X4 @ X5))),
% 0.40/0.63      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.40/0.63  thf('15', plain,
% 0.40/0.63      (((k3_xboole_0 @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B) = (k1_xboole_0))),
% 0.40/0.63      inference('sup-', [status(thm)], ['13', '14'])).
% 0.40/0.63  thf(commutativity_k3_xboole_0, axiom,
% 0.40/0.63    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.40/0.63  thf('16', plain,
% 0.40/0.63      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.40/0.63      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.40/0.63  thf('17', plain,
% 0.40/0.63      (((k3_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)) = (k1_xboole_0))),
% 0.40/0.63      inference('demod', [status(thm)], ['15', '16'])).
% 0.40/0.63  thf(l98_xboole_1, axiom,
% 0.40/0.63    (![A:$i,B:$i]:
% 0.40/0.63     ( ( k5_xboole_0 @ A @ B ) =
% 0.40/0.63       ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.40/0.63  thf('18', plain,
% 0.40/0.63      (![X7 : $i, X8 : $i]:
% 0.40/0.63         ((k5_xboole_0 @ X7 @ X8)
% 0.40/0.63           = (k4_xboole_0 @ (k2_xboole_0 @ X7 @ X8) @ (k3_xboole_0 @ X7 @ X8)))),
% 0.40/0.63      inference('cnf', [status(esa)], [l98_xboole_1])).
% 0.40/0.63  thf('19', plain,
% 0.40/0.63      (![X59 : $i, X60 : $i]:
% 0.40/0.63         ((k3_tarski @ (k2_tarski @ X59 @ X60)) = (k2_xboole_0 @ X59 @ X60))),
% 0.40/0.63      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.40/0.63  thf('20', plain,
% 0.40/0.63      (![X7 : $i, X8 : $i]:
% 0.40/0.63         ((k5_xboole_0 @ X7 @ X8)
% 0.40/0.63           = (k4_xboole_0 @ (k3_tarski @ (k2_tarski @ X7 @ X8)) @ 
% 0.40/0.63              (k3_xboole_0 @ X7 @ X8)))),
% 0.40/0.63      inference('demod', [status(thm)], ['18', '19'])).
% 0.40/0.63  thf('21', plain,
% 0.40/0.63      (((k5_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))
% 0.40/0.63         = (k4_xboole_0 @ 
% 0.40/0.63            (k3_tarski @ (k2_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))) @ 
% 0.40/0.63            k1_xboole_0))),
% 0.40/0.63      inference('sup+', [status(thm)], ['17', '20'])).
% 0.40/0.63  thf('22', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.40/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.63  thf(d2_subset_1, axiom,
% 0.40/0.63    (![A:$i,B:$i]:
% 0.40/0.63     ( ( ( v1_xboole_0 @ A ) =>
% 0.40/0.63         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.40/0.63       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.40/0.63         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.40/0.63  thf('23', plain,
% 0.40/0.63      (![X61 : $i, X62 : $i]:
% 0.40/0.63         (~ (m1_subset_1 @ X61 @ X62)
% 0.40/0.63          | (r2_hidden @ X61 @ X62)
% 0.40/0.63          | (v1_xboole_0 @ X62))),
% 0.40/0.63      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.40/0.63  thf('24', plain,
% 0.40/0.63      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 0.40/0.63        | (r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A)))),
% 0.40/0.63      inference('sup-', [status(thm)], ['22', '23'])).
% 0.40/0.63  thf(fc1_subset_1, axiom,
% 0.40/0.63    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.40/0.63  thf('25', plain, (![X69 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X69))),
% 0.40/0.63      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.40/0.63  thf('26', plain, ((r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.40/0.63      inference('clc', [status(thm)], ['24', '25'])).
% 0.40/0.63  thf(d1_zfmisc_1, axiom,
% 0.40/0.63    (![A:$i,B:$i]:
% 0.40/0.63     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.40/0.63       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.40/0.63  thf('27', plain,
% 0.40/0.63      (![X55 : $i, X56 : $i, X57 : $i]:
% 0.40/0.63         (~ (r2_hidden @ X57 @ X56)
% 0.40/0.63          | (r1_tarski @ X57 @ X55)
% 0.40/0.63          | ((X56) != (k1_zfmisc_1 @ X55)))),
% 0.40/0.63      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.40/0.63  thf('28', plain,
% 0.40/0.63      (![X55 : $i, X57 : $i]:
% 0.40/0.63         ((r1_tarski @ X57 @ X55) | ~ (r2_hidden @ X57 @ (k1_zfmisc_1 @ X55)))),
% 0.40/0.63      inference('simplify', [status(thm)], ['27'])).
% 0.40/0.63  thf('29', plain, ((r1_tarski @ sk_B @ sk_A)),
% 0.40/0.63      inference('sup-', [status(thm)], ['26', '28'])).
% 0.40/0.63  thf(t28_xboole_1, axiom,
% 0.40/0.63    (![A:$i,B:$i]:
% 0.40/0.63     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.40/0.63  thf('30', plain,
% 0.40/0.63      (![X18 : $i, X19 : $i]:
% 0.40/0.63         (((k3_xboole_0 @ X18 @ X19) = (X18)) | ~ (r1_tarski @ X18 @ X19))),
% 0.40/0.63      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.40/0.63  thf('31', plain, (((k3_xboole_0 @ sk_B @ sk_A) = (sk_B))),
% 0.40/0.63      inference('sup-', [status(thm)], ['29', '30'])).
% 0.40/0.63  thf('32', plain,
% 0.40/0.63      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.40/0.63      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.40/0.63  thf(t100_xboole_1, axiom,
% 0.40/0.63    (![A:$i,B:$i]:
% 0.40/0.63     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.40/0.63  thf('33', plain,
% 0.40/0.63      (![X9 : $i, X10 : $i]:
% 0.40/0.63         ((k4_xboole_0 @ X9 @ X10)
% 0.40/0.63           = (k5_xboole_0 @ X9 @ (k3_xboole_0 @ X9 @ X10)))),
% 0.40/0.63      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.40/0.63  thf('34', plain,
% 0.40/0.63      (![X0 : $i, X1 : $i]:
% 0.40/0.63         ((k4_xboole_0 @ X0 @ X1)
% 0.40/0.63           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.40/0.63      inference('sup+', [status(thm)], ['32', '33'])).
% 0.40/0.63  thf('35', plain,
% 0.40/0.63      (((k4_xboole_0 @ sk_A @ sk_B) = (k5_xboole_0 @ sk_A @ sk_B))),
% 0.40/0.63      inference('sup+', [status(thm)], ['31', '34'])).
% 0.40/0.63  thf('36', plain,
% 0.40/0.63      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.40/0.63      inference('sup-', [status(thm)], ['9', '10'])).
% 0.40/0.63  thf(commutativity_k5_xboole_0, axiom,
% 0.40/0.63    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 0.40/0.63  thf('37', plain,
% 0.40/0.63      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.40/0.63      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.40/0.63  thf('38', plain,
% 0.40/0.63      (((k3_subset_1 @ sk_A @ sk_B) = (k5_xboole_0 @ sk_B @ sk_A))),
% 0.40/0.63      inference('demod', [status(thm)], ['35', '36', '37'])).
% 0.40/0.63  thf(t92_xboole_1, axiom,
% 0.40/0.63    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.40/0.63  thf('39', plain, (![X26 : $i]: ((k5_xboole_0 @ X26 @ X26) = (k1_xboole_0))),
% 0.40/0.63      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.40/0.63  thf(t91_xboole_1, axiom,
% 0.40/0.63    (![A:$i,B:$i,C:$i]:
% 0.40/0.63     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.40/0.63       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.40/0.63  thf('40', plain,
% 0.40/0.63      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.40/0.63         ((k5_xboole_0 @ (k5_xboole_0 @ X23 @ X24) @ X25)
% 0.40/0.63           = (k5_xboole_0 @ X23 @ (k5_xboole_0 @ X24 @ X25)))),
% 0.40/0.63      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.40/0.63  thf('41', plain,
% 0.40/0.63      (![X0 : $i, X1 : $i]:
% 0.40/0.63         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 0.40/0.63           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.40/0.63      inference('sup+', [status(thm)], ['39', '40'])).
% 0.40/0.63  thf('42', plain,
% 0.40/0.63      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.40/0.63      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.40/0.63  thf(t5_boole, axiom,
% 0.40/0.63    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.40/0.63  thf('43', plain, (![X20 : $i]: ((k5_xboole_0 @ X20 @ k1_xboole_0) = (X20))),
% 0.40/0.63      inference('cnf', [status(esa)], [t5_boole])).
% 0.40/0.63  thf('44', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.40/0.63      inference('sup+', [status(thm)], ['42', '43'])).
% 0.40/0.63  thf('45', plain,
% 0.40/0.63      (![X0 : $i, X1 : $i]:
% 0.40/0.63         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.40/0.63      inference('demod', [status(thm)], ['41', '44'])).
% 0.40/0.63  thf('46', plain,
% 0.40/0.63      (((sk_A) = (k5_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)))),
% 0.40/0.63      inference('sup+', [status(thm)], ['38', '45'])).
% 0.40/0.63  thf(t21_xboole_1, axiom,
% 0.40/0.63    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( A ) ))).
% 0.40/0.63  thf('47', plain,
% 0.40/0.63      (![X16 : $i, X17 : $i]:
% 0.40/0.63         ((k3_xboole_0 @ X16 @ (k2_xboole_0 @ X16 @ X17)) = (X16))),
% 0.40/0.63      inference('cnf', [status(esa)], [t21_xboole_1])).
% 0.40/0.63  thf('48', plain,
% 0.40/0.63      (![X59 : $i, X60 : $i]:
% 0.40/0.63         ((k3_tarski @ (k2_tarski @ X59 @ X60)) = (k2_xboole_0 @ X59 @ X60))),
% 0.40/0.63      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.40/0.63  thf('49', plain,
% 0.40/0.63      (![X16 : $i, X17 : $i]:
% 0.40/0.63         ((k3_xboole_0 @ X16 @ (k3_tarski @ (k2_tarski @ X16 @ X17))) = (X16))),
% 0.40/0.63      inference('demod', [status(thm)], ['47', '48'])).
% 0.40/0.63  thf(t17_xboole_1, axiom,
% 0.40/0.63    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.40/0.63  thf('50', plain,
% 0.40/0.63      (![X14 : $i, X15 : $i]: (r1_tarski @ (k3_xboole_0 @ X14 @ X15) @ X14)),
% 0.40/0.63      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.40/0.63  thf('51', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.40/0.63      inference('sup+', [status(thm)], ['49', '50'])).
% 0.40/0.63  thf('52', plain,
% 0.40/0.63      (![X18 : $i, X19 : $i]:
% 0.40/0.63         (((k3_xboole_0 @ X18 @ X19) = (X18)) | ~ (r1_tarski @ X18 @ X19))),
% 0.40/0.63      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.40/0.63  thf('53', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.40/0.63      inference('sup-', [status(thm)], ['51', '52'])).
% 0.40/0.63  thf('54', plain,
% 0.40/0.63      (![X9 : $i, X10 : $i]:
% 0.40/0.63         ((k4_xboole_0 @ X9 @ X10)
% 0.40/0.63           = (k5_xboole_0 @ X9 @ (k3_xboole_0 @ X9 @ X10)))),
% 0.40/0.63      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.40/0.63  thf('55', plain,
% 0.40/0.63      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.40/0.63      inference('sup+', [status(thm)], ['53', '54'])).
% 0.40/0.63  thf('56', plain, (![X26 : $i]: ((k5_xboole_0 @ X26 @ X26) = (k1_xboole_0))),
% 0.40/0.63      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.40/0.63  thf('57', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.40/0.63      inference('sup+', [status(thm)], ['55', '56'])).
% 0.40/0.63  thf('58', plain,
% 0.40/0.63      (![X21 : $i, X22 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X21 @ X22) @ X22)),
% 0.40/0.63      inference('cnf', [status(esa)], [t79_xboole_1])).
% 0.40/0.63  thf('59', plain,
% 0.40/0.63      (![X4 : $i, X5 : $i]:
% 0.40/0.63         (((k3_xboole_0 @ X4 @ X5) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X4 @ X5))),
% 0.40/0.63      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.40/0.63  thf('60', plain,
% 0.40/0.63      (![X0 : $i, X1 : $i]:
% 0.40/0.63         ((k3_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0) = (k1_xboole_0))),
% 0.40/0.63      inference('sup-', [status(thm)], ['58', '59'])).
% 0.40/0.63  thf('61', plain,
% 0.40/0.63      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.40/0.63      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.40/0.63  thf('62', plain,
% 0.40/0.63      (![X0 : $i, X1 : $i]:
% 0.40/0.63         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 0.40/0.63      inference('demod', [status(thm)], ['60', '61'])).
% 0.40/0.63  thf('63', plain,
% 0.40/0.63      (![X9 : $i, X10 : $i]:
% 0.40/0.63         ((k4_xboole_0 @ X9 @ X10)
% 0.40/0.63           = (k5_xboole_0 @ X9 @ (k3_xboole_0 @ X9 @ X10)))),
% 0.40/0.63      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.40/0.63  thf('64', plain,
% 0.40/0.63      (![X0 : $i, X1 : $i]:
% 0.40/0.63         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))
% 0.40/0.63           = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.40/0.63      inference('sup+', [status(thm)], ['62', '63'])).
% 0.40/0.63  thf('65', plain, (![X20 : $i]: ((k5_xboole_0 @ X20 @ k1_xboole_0) = (X20))),
% 0.40/0.63      inference('cnf', [status(esa)], [t5_boole])).
% 0.40/0.63  thf('66', plain,
% 0.40/0.63      (![X0 : $i, X1 : $i]:
% 0.40/0.63         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (X0))),
% 0.40/0.63      inference('demod', [status(thm)], ['64', '65'])).
% 0.40/0.63  thf('67', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.40/0.63      inference('sup+', [status(thm)], ['57', '66'])).
% 0.40/0.63  thf('68', plain,
% 0.40/0.63      (((sk_A) = (k3_tarski @ (k2_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))))),
% 0.40/0.63      inference('demod', [status(thm)], ['21', '46', '67'])).
% 0.40/0.63  thf('69', plain,
% 0.40/0.63      (((k4_subset_1 @ sk_A @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)) = (sk_A))),
% 0.40/0.63      inference('demod', [status(thm)], ['8', '68'])).
% 0.40/0.63  thf('70', plain,
% 0.40/0.63      (((k4_subset_1 @ sk_A @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))
% 0.40/0.63         != (k2_subset_1 @ sk_A))),
% 0.40/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.63  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.40/0.63  thf('71', plain, (![X64 : $i]: ((k2_subset_1 @ X64) = (X64))),
% 0.40/0.63      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.40/0.63  thf('72', plain,
% 0.40/0.63      (((k4_subset_1 @ sk_A @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)) != (sk_A))),
% 0.40/0.63      inference('demod', [status(thm)], ['70', '71'])).
% 0.40/0.63  thf('73', plain, ($false),
% 0.40/0.63      inference('simplify_reflect-', [status(thm)], ['69', '72'])).
% 0.40/0.63  
% 0.40/0.63  % SZS output end Refutation
% 0.40/0.63  
% 0.51/0.64  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
