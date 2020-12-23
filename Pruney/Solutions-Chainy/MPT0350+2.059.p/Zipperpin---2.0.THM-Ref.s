%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ukKClznjh1

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:36:53 EST 2020

% Result     : Theorem 0.37s
% Output     : Refutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :  139 ( 278 expanded)
%              Number of leaves         :   36 ( 102 expanded)
%              Depth                    :   18
%              Number of atoms          : 1001 (2195 expanded)
%              Number of equality atoms :   98 ( 206 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

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
    ! [X59: $i,X60: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X59 @ X60 ) @ ( k1_zfmisc_1 @ X59 ) )
      | ~ ( m1_subset_1 @ X60 @ ( k1_zfmisc_1 @ X59 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('2',plain,(
    m1_subset_1 @ ( k3_subset_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('4',plain,(
    ! [X57: $i,X58: $i] :
      ( ( ( k3_subset_1 @ X57 @ X58 )
        = ( k4_xboole_0 @ X57 @ X58 ) )
      | ~ ( m1_subset_1 @ X58 @ ( k1_zfmisc_1 @ X57 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('5',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    m1_subset_1 @ ( k4_xboole_0 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(demod,[status(thm)],['2','5'])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('7',plain,(
    ! [X53: $i,X54: $i] :
      ( ~ ( m1_subset_1 @ X53 @ X54 )
      | ( r2_hidden @ X53 @ X54 )
      | ( v1_xboole_0 @ X54 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('8',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ ( k4_xboole_0 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('9',plain,(
    ! [X61: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X61 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('10',plain,(
    r2_hidden @ ( k4_xboole_0 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['8','9'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('11',plain,(
    ! [X47: $i,X48: $i,X49: $i] :
      ( ~ ( r2_hidden @ X49 @ X48 )
      | ( r1_tarski @ X49 @ X47 )
      | ( X48
       != ( k1_zfmisc_1 @ X47 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('12',plain,(
    ! [X47: $i,X49: $i] :
      ( ( r1_tarski @ X49 @ X47 )
      | ~ ( r2_hidden @ X49 @ ( k1_zfmisc_1 @ X47 ) ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    r1_tarski @ ( k4_xboole_0 @ sk_A @ sk_B ) @ sk_A ),
    inference('sup-',[status(thm)],['10','12'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('14',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k3_xboole_0 @ X10 @ X11 )
        = X10 )
      | ~ ( r1_tarski @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('15',plain,
    ( ( k3_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B ) @ sk_A )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
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
    ( ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_A @ sk_B ) )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['15','16'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('18',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ X6 )
      = ( k5_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf(t112_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ C @ B ) )
      = ( k3_xboole_0 @ ( k5_xboole_0 @ A @ C ) @ B ) ) )).

thf('19',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ X7 @ X9 ) @ ( k3_xboole_0 @ X8 @ X9 ) )
      = ( k3_xboole_0 @ ( k5_xboole_0 @ X7 @ X8 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[t112_xboole_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k3_xboole_0 @ ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ X6 )
      = ( k5_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['20','21','22'])).

thf('24',plain,
    ( ( k4_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B ) @ ( k4_xboole_0 @ sk_A @ sk_B ) )
    = ( k3_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B ) @ ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['17','23'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('25',plain,(
    ! [X4: $i] :
      ( ( k3_xboole_0 @ X4 @ X4 )
      = X4 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('26',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ X6 )
      = ( k5_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('28',plain,(
    ! [X16: $i] :
      ( ( k5_xboole_0 @ X16 @ X16 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    ! [X53: $i,X54: $i] :
      ( ~ ( m1_subset_1 @ X53 @ X54 )
      | ( r2_hidden @ X53 @ X54 )
      | ( v1_xboole_0 @ X54 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('32',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X61: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X61 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('34',plain,(
    r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X47: $i,X49: $i] :
      ( ( r1_tarski @ X49 @ X47 )
      | ~ ( r2_hidden @ X49 @ ( k1_zfmisc_1 @ X47 ) ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('36',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k3_xboole_0 @ X10 @ X11 )
        = X10 )
      | ~ ( r1_tarski @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('38',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_A )
    = sk_B ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('40',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ X6 )
      = ( k5_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('42',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = ( k5_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['38','41'])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

thf('43',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('44',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = ( k5_xboole_0 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('46',plain,(
    ! [X16: $i] :
      ( ( k5_xboole_0 @ X16 @ X16 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('47',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X13 @ X14 ) @ X15 )
      = ( k5_xboole_0 @ X13 @ ( k5_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('50',plain,(
    ! [X12: $i] :
      ( ( k5_xboole_0 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['48','51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['45','52'])).

thf('54',plain,
    ( sk_B
    = ( k5_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['44','53'])).

thf('55',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_A @ sk_B ) )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('56',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ X6 )
      = ( k5_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('57',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_A @ sk_B ) )
    = ( k5_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['55','56'])).

thf('58',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_A @ sk_B ) )
    = sk_B ),
    inference('sup+',[status(thm)],['54','57'])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('60',plain,
    ( k1_xboole_0
    = ( k3_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['24','29','58','59'])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['45','52'])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('66',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = ( k5_xboole_0 @ ( k4_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B ) @ sk_B ) @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['60','65'])).

thf('67',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf('69',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(demod,[status(thm)],['66','67','68'])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t94_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('71',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k2_xboole_0 @ X17 @ X18 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X17 @ X18 ) @ ( k3_xboole_0 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t94_xboole_1])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('72',plain,(
    ! [X51: $i,X52: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X51 @ X52 ) )
      = ( k2_xboole_0 @ X51 @ X52 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('73',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X13 @ X14 ) @ X15 )
      = ( k5_xboole_0 @ X13 @ ( k5_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('74',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X17 @ X18 ) )
      = ( k5_xboole_0 @ X17 @ ( k5_xboole_0 @ X18 @ ( k3_xboole_0 @ X17 @ X18 ) ) ) ) ),
    inference(demod,[status(thm)],['71','72','73'])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X0 @ X1 ) )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['70','74'])).

thf('76',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ X6 )
      = ( k5_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X0 @ X1 ) )
      = ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['75','76'])).

thf('78',plain,
    ( ( k3_tarski @ ( k2_tarski @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_B ) ) )
    = ( k5_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['69','77'])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X0 @ X1 ) )
      = ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['75','76'])).

thf('80',plain,
    ( ( k3_tarski @ ( k2_tarski @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_B ) ) )
    = ( k3_tarski @ ( k2_tarski @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['78','79'])).

thf('81',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_A )
    = sk_B ),
    inference('sup-',[status(thm)],['36','37'])).

thf('82',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X17 @ X18 ) )
      = ( k5_xboole_0 @ X17 @ ( k5_xboole_0 @ X18 @ ( k3_xboole_0 @ X17 @ X18 ) ) ) ) ),
    inference(demod,[status(thm)],['71','72','73'])).

thf('83',plain,
    ( ( k3_tarski @ ( k2_tarski @ sk_B @ sk_A ) )
    = ( k5_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('85',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['48','51'])).

thf('86',plain,
    ( ( k3_tarski @ ( k2_tarski @ sk_B @ sk_A ) )
    = sk_A ),
    inference(demod,[status(thm)],['83','84','85'])).

thf('87',plain,
    ( ( k3_tarski @ ( k2_tarski @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_B ) ) )
    = sk_A ),
    inference(demod,[status(thm)],['80','86'])).

thf('88',plain,(
    ( k4_subset_1 @ sk_A @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
 != ( k2_subset_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('89',plain,(
    ! [X56: $i] :
      ( ( k2_subset_1 @ X56 )
      = X56 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('90',plain,(
    ( k4_subset_1 @ sk_A @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
 != sk_A ),
    inference(demod,[status(thm)],['88','89'])).

thf('91',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('92',plain,(
    ( k4_subset_1 @ sk_A @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_B ) )
 != sk_A ),
    inference(demod,[status(thm)],['90','91'])).

thf('93',plain,(
    m1_subset_1 @ ( k4_xboole_0 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(demod,[status(thm)],['2','5'])).

thf('94',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('95',plain,(
    ! [X62: $i,X63: $i,X64: $i] :
      ( ~ ( m1_subset_1 @ X62 @ ( k1_zfmisc_1 @ X63 ) )
      | ~ ( m1_subset_1 @ X64 @ ( k1_zfmisc_1 @ X63 ) )
      | ( ( k4_subset_1 @ X63 @ X62 @ X64 )
        = ( k2_xboole_0 @ X62 @ X64 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('96',plain,(
    ! [X51: $i,X52: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X51 @ X52 ) )
      = ( k2_xboole_0 @ X51 @ X52 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('97',plain,(
    ! [X62: $i,X63: $i,X64: $i] :
      ( ~ ( m1_subset_1 @ X62 @ ( k1_zfmisc_1 @ X63 ) )
      | ~ ( m1_subset_1 @ X64 @ ( k1_zfmisc_1 @ X63 ) )
      | ( ( k4_subset_1 @ X63 @ X62 @ X64 )
        = ( k3_tarski @ ( k2_tarski @ X62 @ X64 ) ) ) ) ),
    inference(demod,[status(thm)],['95','96'])).

thf('98',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ sk_A @ sk_B @ X0 )
        = ( k3_tarski @ ( k2_tarski @ sk_B @ X0 ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['94','97'])).

thf('99',plain,
    ( ( k4_subset_1 @ sk_A @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_B ) )
    = ( k3_tarski @ ( k2_tarski @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['93','98'])).

thf('100',plain,(
    ( k3_tarski @ ( k2_tarski @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_B ) ) )
 != sk_A ),
    inference(demod,[status(thm)],['92','99'])).

thf('101',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['87','100'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ukKClznjh1
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:01:46 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.37/0.55  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.37/0.55  % Solved by: fo/fo7.sh
% 0.37/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.37/0.55  % done 331 iterations in 0.102s
% 0.37/0.55  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.37/0.55  % SZS output start Refutation
% 0.37/0.55  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.37/0.55  thf(sk_B_type, type, sk_B: $i).
% 0.37/0.55  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.37/0.55  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.37/0.55  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.37/0.55  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.37/0.55  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.37/0.55  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 0.37/0.55  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.37/0.55  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.37/0.55  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.37/0.55  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.37/0.55  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.37/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.37/0.55  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.37/0.55  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.37/0.55  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.37/0.55  thf(t25_subset_1, conjecture,
% 0.37/0.55    (![A:$i,B:$i]:
% 0.37/0.55     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.37/0.55       ( ( k4_subset_1 @ A @ B @ ( k3_subset_1 @ A @ B ) ) =
% 0.37/0.55         ( k2_subset_1 @ A ) ) ))).
% 0.37/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.37/0.55    (~( ![A:$i,B:$i]:
% 0.37/0.55        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.37/0.55          ( ( k4_subset_1 @ A @ B @ ( k3_subset_1 @ A @ B ) ) =
% 0.37/0.55            ( k2_subset_1 @ A ) ) ) )),
% 0.37/0.55    inference('cnf.neg', [status(esa)], [t25_subset_1])).
% 0.37/0.55  thf('0', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf(dt_k3_subset_1, axiom,
% 0.37/0.55    (![A:$i,B:$i]:
% 0.37/0.55     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.37/0.55       ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.37/0.55  thf('1', plain,
% 0.37/0.55      (![X59 : $i, X60 : $i]:
% 0.37/0.55         ((m1_subset_1 @ (k3_subset_1 @ X59 @ X60) @ (k1_zfmisc_1 @ X59))
% 0.37/0.55          | ~ (m1_subset_1 @ X60 @ (k1_zfmisc_1 @ X59)))),
% 0.37/0.55      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 0.37/0.55  thf('2', plain,
% 0.37/0.55      ((m1_subset_1 @ (k3_subset_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_A))),
% 0.37/0.55      inference('sup-', [status(thm)], ['0', '1'])).
% 0.37/0.55  thf('3', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf(d5_subset_1, axiom,
% 0.37/0.55    (![A:$i,B:$i]:
% 0.37/0.55     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.37/0.55       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.37/0.55  thf('4', plain,
% 0.37/0.55      (![X57 : $i, X58 : $i]:
% 0.37/0.55         (((k3_subset_1 @ X57 @ X58) = (k4_xboole_0 @ X57 @ X58))
% 0.37/0.55          | ~ (m1_subset_1 @ X58 @ (k1_zfmisc_1 @ X57)))),
% 0.37/0.55      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.37/0.55  thf('5', plain,
% 0.37/0.55      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.37/0.55      inference('sup-', [status(thm)], ['3', '4'])).
% 0.37/0.55  thf('6', plain,
% 0.37/0.55      ((m1_subset_1 @ (k4_xboole_0 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_A))),
% 0.37/0.55      inference('demod', [status(thm)], ['2', '5'])).
% 0.37/0.55  thf(d2_subset_1, axiom,
% 0.37/0.55    (![A:$i,B:$i]:
% 0.37/0.55     ( ( ( v1_xboole_0 @ A ) =>
% 0.37/0.55         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.37/0.55       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.37/0.55         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.37/0.55  thf('7', plain,
% 0.37/0.55      (![X53 : $i, X54 : $i]:
% 0.37/0.55         (~ (m1_subset_1 @ X53 @ X54)
% 0.37/0.55          | (r2_hidden @ X53 @ X54)
% 0.37/0.55          | (v1_xboole_0 @ X54))),
% 0.37/0.55      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.37/0.55  thf('8', plain,
% 0.37/0.55      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 0.37/0.55        | (r2_hidden @ (k4_xboole_0 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_A)))),
% 0.37/0.55      inference('sup-', [status(thm)], ['6', '7'])).
% 0.37/0.55  thf(fc1_subset_1, axiom,
% 0.37/0.55    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.37/0.55  thf('9', plain, (![X61 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X61))),
% 0.37/0.55      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.37/0.55  thf('10', plain,
% 0.37/0.55      ((r2_hidden @ (k4_xboole_0 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_A))),
% 0.37/0.55      inference('clc', [status(thm)], ['8', '9'])).
% 0.37/0.55  thf(d1_zfmisc_1, axiom,
% 0.37/0.55    (![A:$i,B:$i]:
% 0.37/0.55     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.37/0.56       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.37/0.56  thf('11', plain,
% 0.37/0.56      (![X47 : $i, X48 : $i, X49 : $i]:
% 0.37/0.56         (~ (r2_hidden @ X49 @ X48)
% 0.37/0.56          | (r1_tarski @ X49 @ X47)
% 0.37/0.56          | ((X48) != (k1_zfmisc_1 @ X47)))),
% 0.37/0.56      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.37/0.56  thf('12', plain,
% 0.37/0.56      (![X47 : $i, X49 : $i]:
% 0.37/0.56         ((r1_tarski @ X49 @ X47) | ~ (r2_hidden @ X49 @ (k1_zfmisc_1 @ X47)))),
% 0.37/0.56      inference('simplify', [status(thm)], ['11'])).
% 0.37/0.56  thf('13', plain, ((r1_tarski @ (k4_xboole_0 @ sk_A @ sk_B) @ sk_A)),
% 0.37/0.56      inference('sup-', [status(thm)], ['10', '12'])).
% 0.37/0.56  thf(t28_xboole_1, axiom,
% 0.37/0.56    (![A:$i,B:$i]:
% 0.37/0.56     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.37/0.56  thf('14', plain,
% 0.37/0.56      (![X10 : $i, X11 : $i]:
% 0.37/0.56         (((k3_xboole_0 @ X10 @ X11) = (X10)) | ~ (r1_tarski @ X10 @ X11))),
% 0.37/0.56      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.37/0.56  thf('15', plain,
% 0.37/0.56      (((k3_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B) @ sk_A)
% 0.37/0.56         = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.37/0.56      inference('sup-', [status(thm)], ['13', '14'])).
% 0.37/0.56  thf(commutativity_k3_xboole_0, axiom,
% 0.37/0.56    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.37/0.56  thf('16', plain,
% 0.37/0.56      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.37/0.56      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.37/0.56  thf('17', plain,
% 0.37/0.56      (((k3_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_A @ sk_B))
% 0.37/0.56         = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.37/0.56      inference('demod', [status(thm)], ['15', '16'])).
% 0.37/0.56  thf(t100_xboole_1, axiom,
% 0.37/0.56    (![A:$i,B:$i]:
% 0.37/0.56     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.37/0.56  thf('18', plain,
% 0.37/0.56      (![X5 : $i, X6 : $i]:
% 0.37/0.56         ((k4_xboole_0 @ X5 @ X6)
% 0.37/0.56           = (k5_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6)))),
% 0.37/0.56      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.37/0.56  thf(t112_xboole_1, axiom,
% 0.37/0.56    (![A:$i,B:$i,C:$i]:
% 0.37/0.56     ( ( k5_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ C @ B ) ) =
% 0.37/0.56       ( k3_xboole_0 @ ( k5_xboole_0 @ A @ C ) @ B ) ))).
% 0.37/0.56  thf('19', plain,
% 0.37/0.56      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.37/0.56         ((k5_xboole_0 @ (k3_xboole_0 @ X7 @ X9) @ (k3_xboole_0 @ X8 @ X9))
% 0.37/0.56           = (k3_xboole_0 @ (k5_xboole_0 @ X7 @ X8) @ X9))),
% 0.37/0.56      inference('cnf', [status(esa)], [t112_xboole_1])).
% 0.37/0.56  thf('20', plain,
% 0.37/0.56      (![X0 : $i, X1 : $i]:
% 0.37/0.56         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0)
% 0.37/0.56           = (k3_xboole_0 @ (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)) @ X0))),
% 0.37/0.56      inference('sup+', [status(thm)], ['18', '19'])).
% 0.37/0.56  thf('21', plain,
% 0.37/0.56      (![X5 : $i, X6 : $i]:
% 0.37/0.56         ((k4_xboole_0 @ X5 @ X6)
% 0.37/0.56           = (k5_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6)))),
% 0.37/0.56      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.37/0.56  thf('22', plain,
% 0.37/0.56      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.37/0.56      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.37/0.56  thf('23', plain,
% 0.37/0.56      (![X0 : $i, X1 : $i]:
% 0.37/0.56         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0)
% 0.37/0.56           = (k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.37/0.56      inference('demod', [status(thm)], ['20', '21', '22'])).
% 0.37/0.56  thf('24', plain,
% 0.37/0.56      (((k4_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B) @ 
% 0.37/0.56         (k4_xboole_0 @ sk_A @ sk_B))
% 0.37/0.56         = (k3_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B) @ 
% 0.37/0.56            (k4_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_A @ sk_B))))),
% 0.37/0.56      inference('sup+', [status(thm)], ['17', '23'])).
% 0.37/0.56  thf(idempotence_k3_xboole_0, axiom,
% 0.37/0.56    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.37/0.56  thf('25', plain, (![X4 : $i]: ((k3_xboole_0 @ X4 @ X4) = (X4))),
% 0.37/0.56      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.37/0.56  thf('26', plain,
% 0.37/0.56      (![X5 : $i, X6 : $i]:
% 0.37/0.56         ((k4_xboole_0 @ X5 @ X6)
% 0.37/0.56           = (k5_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6)))),
% 0.37/0.56      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.37/0.56  thf('27', plain,
% 0.37/0.56      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.37/0.56      inference('sup+', [status(thm)], ['25', '26'])).
% 0.37/0.56  thf(t92_xboole_1, axiom,
% 0.37/0.56    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.37/0.56  thf('28', plain, (![X16 : $i]: ((k5_xboole_0 @ X16 @ X16) = (k1_xboole_0))),
% 0.37/0.56      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.37/0.56  thf('29', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.37/0.56      inference('sup+', [status(thm)], ['27', '28'])).
% 0.37/0.56  thf('30', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('31', plain,
% 0.37/0.56      (![X53 : $i, X54 : $i]:
% 0.37/0.56         (~ (m1_subset_1 @ X53 @ X54)
% 0.37/0.56          | (r2_hidden @ X53 @ X54)
% 0.37/0.56          | (v1_xboole_0 @ X54))),
% 0.37/0.56      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.37/0.56  thf('32', plain,
% 0.37/0.56      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 0.37/0.56        | (r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A)))),
% 0.37/0.56      inference('sup-', [status(thm)], ['30', '31'])).
% 0.37/0.56  thf('33', plain, (![X61 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X61))),
% 0.37/0.56      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.37/0.56  thf('34', plain, ((r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.37/0.56      inference('clc', [status(thm)], ['32', '33'])).
% 0.37/0.56  thf('35', plain,
% 0.37/0.56      (![X47 : $i, X49 : $i]:
% 0.37/0.56         ((r1_tarski @ X49 @ X47) | ~ (r2_hidden @ X49 @ (k1_zfmisc_1 @ X47)))),
% 0.37/0.56      inference('simplify', [status(thm)], ['11'])).
% 0.37/0.56  thf('36', plain, ((r1_tarski @ sk_B @ sk_A)),
% 0.37/0.56      inference('sup-', [status(thm)], ['34', '35'])).
% 0.37/0.56  thf('37', plain,
% 0.37/0.56      (![X10 : $i, X11 : $i]:
% 0.37/0.56         (((k3_xboole_0 @ X10 @ X11) = (X10)) | ~ (r1_tarski @ X10 @ X11))),
% 0.37/0.56      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.37/0.56  thf('38', plain, (((k3_xboole_0 @ sk_B @ sk_A) = (sk_B))),
% 0.37/0.56      inference('sup-', [status(thm)], ['36', '37'])).
% 0.37/0.56  thf('39', plain,
% 0.37/0.56      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.37/0.56      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.37/0.56  thf('40', plain,
% 0.37/0.56      (![X5 : $i, X6 : $i]:
% 0.37/0.56         ((k4_xboole_0 @ X5 @ X6)
% 0.37/0.56           = (k5_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6)))),
% 0.37/0.56      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.37/0.56  thf('41', plain,
% 0.37/0.56      (![X0 : $i, X1 : $i]:
% 0.37/0.56         ((k4_xboole_0 @ X0 @ X1)
% 0.37/0.56           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.37/0.56      inference('sup+', [status(thm)], ['39', '40'])).
% 0.37/0.56  thf('42', plain,
% 0.37/0.56      (((k4_xboole_0 @ sk_A @ sk_B) = (k5_xboole_0 @ sk_A @ sk_B))),
% 0.37/0.56      inference('sup+', [status(thm)], ['38', '41'])).
% 0.37/0.56  thf(commutativity_k5_xboole_0, axiom,
% 0.37/0.56    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 0.37/0.56  thf('43', plain,
% 0.37/0.56      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.37/0.56      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.37/0.56  thf('44', plain,
% 0.37/0.56      (((k4_xboole_0 @ sk_A @ sk_B) = (k5_xboole_0 @ sk_B @ sk_A))),
% 0.37/0.56      inference('demod', [status(thm)], ['42', '43'])).
% 0.37/0.56  thf('45', plain,
% 0.37/0.56      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.37/0.56      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.37/0.56  thf('46', plain, (![X16 : $i]: ((k5_xboole_0 @ X16 @ X16) = (k1_xboole_0))),
% 0.37/0.56      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.37/0.56  thf(t91_xboole_1, axiom,
% 0.37/0.56    (![A:$i,B:$i,C:$i]:
% 0.37/0.56     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.37/0.56       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.37/0.56  thf('47', plain,
% 0.37/0.56      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.37/0.56         ((k5_xboole_0 @ (k5_xboole_0 @ X13 @ X14) @ X15)
% 0.37/0.56           = (k5_xboole_0 @ X13 @ (k5_xboole_0 @ X14 @ X15)))),
% 0.37/0.56      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.37/0.56  thf('48', plain,
% 0.37/0.56      (![X0 : $i, X1 : $i]:
% 0.37/0.56         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 0.37/0.56           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.37/0.56      inference('sup+', [status(thm)], ['46', '47'])).
% 0.37/0.56  thf('49', plain,
% 0.37/0.56      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.37/0.56      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.37/0.56  thf(t5_boole, axiom,
% 0.37/0.56    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.37/0.56  thf('50', plain, (![X12 : $i]: ((k5_xboole_0 @ X12 @ k1_xboole_0) = (X12))),
% 0.37/0.56      inference('cnf', [status(esa)], [t5_boole])).
% 0.37/0.56  thf('51', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.37/0.56      inference('sup+', [status(thm)], ['49', '50'])).
% 0.37/0.56  thf('52', plain,
% 0.37/0.56      (![X0 : $i, X1 : $i]:
% 0.37/0.56         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.37/0.56      inference('demod', [status(thm)], ['48', '51'])).
% 0.37/0.56  thf('53', plain,
% 0.37/0.56      (![X0 : $i, X1 : $i]:
% 0.37/0.56         ((X1) = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.37/0.56      inference('sup+', [status(thm)], ['45', '52'])).
% 0.37/0.56  thf('54', plain,
% 0.37/0.56      (((sk_B) = (k5_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_A @ sk_B)))),
% 0.37/0.56      inference('sup+', [status(thm)], ['44', '53'])).
% 0.37/0.56  thf('55', plain,
% 0.37/0.56      (((k3_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_A @ sk_B))
% 0.37/0.56         = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.37/0.56      inference('demod', [status(thm)], ['15', '16'])).
% 0.37/0.56  thf('56', plain,
% 0.37/0.56      (![X5 : $i, X6 : $i]:
% 0.37/0.56         ((k4_xboole_0 @ X5 @ X6)
% 0.37/0.56           = (k5_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6)))),
% 0.37/0.56      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.37/0.56  thf('57', plain,
% 0.37/0.56      (((k4_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_A @ sk_B))
% 0.37/0.56         = (k5_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_A @ sk_B)))),
% 0.37/0.56      inference('sup+', [status(thm)], ['55', '56'])).
% 0.37/0.56  thf('58', plain,
% 0.37/0.56      (((k4_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_A @ sk_B)) = (sk_B))),
% 0.37/0.56      inference('sup+', [status(thm)], ['54', '57'])).
% 0.37/0.56  thf('59', plain,
% 0.37/0.56      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.37/0.56      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.37/0.56  thf('60', plain,
% 0.37/0.56      (((k1_xboole_0) = (k3_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_A @ sk_B)))),
% 0.37/0.56      inference('demod', [status(thm)], ['24', '29', '58', '59'])).
% 0.37/0.56  thf('61', plain,
% 0.37/0.56      (![X0 : $i, X1 : $i]:
% 0.37/0.56         ((k4_xboole_0 @ X0 @ X1)
% 0.37/0.56           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.37/0.56      inference('sup+', [status(thm)], ['39', '40'])).
% 0.37/0.56  thf('62', plain,
% 0.37/0.56      (![X0 : $i, X1 : $i]:
% 0.37/0.56         ((X1) = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.37/0.56      inference('sup+', [status(thm)], ['45', '52'])).
% 0.37/0.56  thf('63', plain,
% 0.37/0.56      (![X0 : $i, X1 : $i]:
% 0.37/0.56         ((X1)
% 0.37/0.56           = (k5_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ (k4_xboole_0 @ X1 @ X0)))),
% 0.37/0.56      inference('sup+', [status(thm)], ['61', '62'])).
% 0.37/0.56  thf('64', plain,
% 0.37/0.56      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.37/0.56      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.37/0.56  thf('65', plain,
% 0.37/0.56      (![X0 : $i, X1 : $i]:
% 0.37/0.56         ((X1)
% 0.37/0.56           = (k5_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X0 @ X1)))),
% 0.37/0.56      inference('demod', [status(thm)], ['63', '64'])).
% 0.37/0.56  thf('66', plain,
% 0.37/0.56      (((k4_xboole_0 @ sk_A @ sk_B)
% 0.37/0.56         = (k5_xboole_0 @ (k4_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B) @ sk_B) @ 
% 0.37/0.56            k1_xboole_0))),
% 0.37/0.56      inference('sup+', [status(thm)], ['60', '65'])).
% 0.37/0.56  thf('67', plain,
% 0.37/0.56      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.37/0.56      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.37/0.56  thf('68', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.37/0.56      inference('sup+', [status(thm)], ['49', '50'])).
% 0.37/0.56  thf('69', plain,
% 0.37/0.56      (((k4_xboole_0 @ sk_A @ sk_B)
% 0.37/0.56         = (k4_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B) @ sk_B))),
% 0.37/0.56      inference('demod', [status(thm)], ['66', '67', '68'])).
% 0.37/0.56  thf('70', plain,
% 0.37/0.56      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.37/0.56      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.37/0.56  thf(t94_xboole_1, axiom,
% 0.37/0.56    (![A:$i,B:$i]:
% 0.37/0.56     ( ( k2_xboole_0 @ A @ B ) =
% 0.37/0.56       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.37/0.56  thf('71', plain,
% 0.37/0.56      (![X17 : $i, X18 : $i]:
% 0.37/0.56         ((k2_xboole_0 @ X17 @ X18)
% 0.37/0.56           = (k5_xboole_0 @ (k5_xboole_0 @ X17 @ X18) @ 
% 0.37/0.56              (k3_xboole_0 @ X17 @ X18)))),
% 0.37/0.56      inference('cnf', [status(esa)], [t94_xboole_1])).
% 0.37/0.56  thf(l51_zfmisc_1, axiom,
% 0.37/0.56    (![A:$i,B:$i]:
% 0.37/0.56     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.37/0.56  thf('72', plain,
% 0.37/0.56      (![X51 : $i, X52 : $i]:
% 0.37/0.56         ((k3_tarski @ (k2_tarski @ X51 @ X52)) = (k2_xboole_0 @ X51 @ X52))),
% 0.37/0.56      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.37/0.56  thf('73', plain,
% 0.37/0.56      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.37/0.56         ((k5_xboole_0 @ (k5_xboole_0 @ X13 @ X14) @ X15)
% 0.37/0.56           = (k5_xboole_0 @ X13 @ (k5_xboole_0 @ X14 @ X15)))),
% 0.37/0.56      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.37/0.56  thf('74', plain,
% 0.37/0.56      (![X17 : $i, X18 : $i]:
% 0.37/0.56         ((k3_tarski @ (k2_tarski @ X17 @ X18))
% 0.37/0.56           = (k5_xboole_0 @ X17 @ 
% 0.37/0.56              (k5_xboole_0 @ X18 @ (k3_xboole_0 @ X17 @ X18))))),
% 0.37/0.56      inference('demod', [status(thm)], ['71', '72', '73'])).
% 0.37/0.56  thf('75', plain,
% 0.37/0.56      (![X0 : $i, X1 : $i]:
% 0.37/0.56         ((k3_tarski @ (k2_tarski @ X0 @ X1))
% 0.37/0.56           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))))),
% 0.37/0.56      inference('sup+', [status(thm)], ['70', '74'])).
% 0.37/0.56  thf('76', plain,
% 0.37/0.56      (![X5 : $i, X6 : $i]:
% 0.37/0.56         ((k4_xboole_0 @ X5 @ X6)
% 0.37/0.56           = (k5_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6)))),
% 0.37/0.56      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.37/0.56  thf('77', plain,
% 0.37/0.56      (![X0 : $i, X1 : $i]:
% 0.37/0.56         ((k3_tarski @ (k2_tarski @ X0 @ X1))
% 0.37/0.56           = (k5_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.37/0.56      inference('demod', [status(thm)], ['75', '76'])).
% 0.37/0.56  thf('78', plain,
% 0.37/0.56      (((k3_tarski @ (k2_tarski @ sk_B @ (k4_xboole_0 @ sk_A @ sk_B)))
% 0.37/0.56         = (k5_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_A @ sk_B)))),
% 0.37/0.56      inference('sup+', [status(thm)], ['69', '77'])).
% 0.37/0.56  thf('79', plain,
% 0.37/0.56      (![X0 : $i, X1 : $i]:
% 0.37/0.56         ((k3_tarski @ (k2_tarski @ X0 @ X1))
% 0.37/0.56           = (k5_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.37/0.56      inference('demod', [status(thm)], ['75', '76'])).
% 0.37/0.56  thf('80', plain,
% 0.37/0.56      (((k3_tarski @ (k2_tarski @ sk_B @ (k4_xboole_0 @ sk_A @ sk_B)))
% 0.37/0.56         = (k3_tarski @ (k2_tarski @ sk_B @ sk_A)))),
% 0.37/0.56      inference('demod', [status(thm)], ['78', '79'])).
% 0.37/0.56  thf('81', plain, (((k3_xboole_0 @ sk_B @ sk_A) = (sk_B))),
% 0.37/0.56      inference('sup-', [status(thm)], ['36', '37'])).
% 0.37/0.56  thf('82', plain,
% 0.37/0.56      (![X17 : $i, X18 : $i]:
% 0.37/0.56         ((k3_tarski @ (k2_tarski @ X17 @ X18))
% 0.37/0.56           = (k5_xboole_0 @ X17 @ 
% 0.37/0.56              (k5_xboole_0 @ X18 @ (k3_xboole_0 @ X17 @ X18))))),
% 0.37/0.56      inference('demod', [status(thm)], ['71', '72', '73'])).
% 0.37/0.56  thf('83', plain,
% 0.37/0.56      (((k3_tarski @ (k2_tarski @ sk_B @ sk_A))
% 0.37/0.56         = (k5_xboole_0 @ sk_B @ (k5_xboole_0 @ sk_A @ sk_B)))),
% 0.37/0.56      inference('sup+', [status(thm)], ['81', '82'])).
% 0.37/0.56  thf('84', plain,
% 0.37/0.56      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.37/0.56      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.37/0.56  thf('85', plain,
% 0.37/0.56      (![X0 : $i, X1 : $i]:
% 0.37/0.56         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.37/0.56      inference('demod', [status(thm)], ['48', '51'])).
% 0.37/0.56  thf('86', plain, (((k3_tarski @ (k2_tarski @ sk_B @ sk_A)) = (sk_A))),
% 0.37/0.56      inference('demod', [status(thm)], ['83', '84', '85'])).
% 0.37/0.56  thf('87', plain,
% 0.37/0.56      (((k3_tarski @ (k2_tarski @ sk_B @ (k4_xboole_0 @ sk_A @ sk_B))) = (sk_A))),
% 0.37/0.56      inference('demod', [status(thm)], ['80', '86'])).
% 0.37/0.56  thf('88', plain,
% 0.37/0.56      (((k4_subset_1 @ sk_A @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))
% 0.37/0.56         != (k2_subset_1 @ sk_A))),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.37/0.56  thf('89', plain, (![X56 : $i]: ((k2_subset_1 @ X56) = (X56))),
% 0.37/0.56      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.37/0.56  thf('90', plain,
% 0.37/0.56      (((k4_subset_1 @ sk_A @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)) != (sk_A))),
% 0.37/0.56      inference('demod', [status(thm)], ['88', '89'])).
% 0.37/0.56  thf('91', plain,
% 0.37/0.56      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.37/0.56      inference('sup-', [status(thm)], ['3', '4'])).
% 0.37/0.56  thf('92', plain,
% 0.37/0.56      (((k4_subset_1 @ sk_A @ sk_B @ (k4_xboole_0 @ sk_A @ sk_B)) != (sk_A))),
% 0.37/0.56      inference('demod', [status(thm)], ['90', '91'])).
% 0.37/0.56  thf('93', plain,
% 0.37/0.56      ((m1_subset_1 @ (k4_xboole_0 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_A))),
% 0.37/0.56      inference('demod', [status(thm)], ['2', '5'])).
% 0.37/0.56  thf('94', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf(redefinition_k4_subset_1, axiom,
% 0.37/0.56    (![A:$i,B:$i,C:$i]:
% 0.37/0.56     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 0.37/0.56         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.37/0.56       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 0.37/0.56  thf('95', plain,
% 0.37/0.56      (![X62 : $i, X63 : $i, X64 : $i]:
% 0.37/0.56         (~ (m1_subset_1 @ X62 @ (k1_zfmisc_1 @ X63))
% 0.37/0.56          | ~ (m1_subset_1 @ X64 @ (k1_zfmisc_1 @ X63))
% 0.37/0.56          | ((k4_subset_1 @ X63 @ X62 @ X64) = (k2_xboole_0 @ X62 @ X64)))),
% 0.37/0.56      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 0.37/0.56  thf('96', plain,
% 0.37/0.56      (![X51 : $i, X52 : $i]:
% 0.37/0.56         ((k3_tarski @ (k2_tarski @ X51 @ X52)) = (k2_xboole_0 @ X51 @ X52))),
% 0.37/0.56      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.37/0.56  thf('97', plain,
% 0.37/0.56      (![X62 : $i, X63 : $i, X64 : $i]:
% 0.37/0.56         (~ (m1_subset_1 @ X62 @ (k1_zfmisc_1 @ X63))
% 0.37/0.56          | ~ (m1_subset_1 @ X64 @ (k1_zfmisc_1 @ X63))
% 0.37/0.56          | ((k4_subset_1 @ X63 @ X62 @ X64)
% 0.37/0.56              = (k3_tarski @ (k2_tarski @ X62 @ X64))))),
% 0.37/0.56      inference('demod', [status(thm)], ['95', '96'])).
% 0.37/0.56  thf('98', plain,
% 0.37/0.56      (![X0 : $i]:
% 0.37/0.56         (((k4_subset_1 @ sk_A @ sk_B @ X0)
% 0.37/0.56            = (k3_tarski @ (k2_tarski @ sk_B @ X0)))
% 0.37/0.56          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A)))),
% 0.37/0.56      inference('sup-', [status(thm)], ['94', '97'])).
% 0.37/0.56  thf('99', plain,
% 0.37/0.56      (((k4_subset_1 @ sk_A @ sk_B @ (k4_xboole_0 @ sk_A @ sk_B))
% 0.37/0.56         = (k3_tarski @ (k2_tarski @ sk_B @ (k4_xboole_0 @ sk_A @ sk_B))))),
% 0.37/0.56      inference('sup-', [status(thm)], ['93', '98'])).
% 0.37/0.56  thf('100', plain,
% 0.37/0.56      (((k3_tarski @ (k2_tarski @ sk_B @ (k4_xboole_0 @ sk_A @ sk_B)))
% 0.37/0.56         != (sk_A))),
% 0.37/0.56      inference('demod', [status(thm)], ['92', '99'])).
% 0.37/0.56  thf('101', plain, ($false),
% 0.37/0.56      inference('simplify_reflect-', [status(thm)], ['87', '100'])).
% 0.37/0.56  
% 0.37/0.56  % SZS output end Refutation
% 0.37/0.56  
% 0.37/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
