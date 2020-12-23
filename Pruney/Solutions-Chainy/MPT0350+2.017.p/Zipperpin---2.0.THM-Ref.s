%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.cyRJ1eLdaF

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:36:47 EST 2020

% Result     : Theorem 0.40s
% Output     : Refutation 0.40s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 101 expanded)
%              Number of leaves         :   27 (  41 expanded)
%              Depth                    :   13
%              Number of atoms          :  549 ( 817 expanded)
%              Number of equality atoms :   42 (  61 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

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

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('12',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k2_xboole_0 @ X11 @ ( k4_xboole_0 @ X12 @ X11 ) )
      = ( k2_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('13',plain,(
    ! [X59: $i,X60: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X59 @ X60 ) )
      = ( k2_xboole_0 @ X59 @ X60 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('14',plain,(
    ! [X59: $i,X60: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X59 @ X60 ) )
      = ( k2_xboole_0 @ X59 @ X60 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('15',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X11 @ ( k4_xboole_0 @ X12 @ X11 ) ) )
      = ( k3_tarski @ ( k2_tarski @ X11 @ X12 ) ) ) ),
    inference(demod,[status(thm)],['12','13','14'])).

thf('16',plain,
    ( ( k3_tarski @ ( k2_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) )
    = ( k3_tarski @ ( k2_tarski @ sk_B @ sk_A ) ) ),
    inference('sup+',[status(thm)],['11','15'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('17',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ( X3 != X4 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('18',plain,(
    ! [X4: $i] :
      ( r1_tarski @ X4 @ X4 ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
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

thf('20',plain,(
    ! [X61: $i,X62: $i] :
      ( ~ ( m1_subset_1 @ X61 @ X62 )
      | ( r2_hidden @ X61 @ X62 )
      | ( v1_xboole_0 @ X62 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('21',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('22',plain,(
    ! [X69: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X69 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('23',plain,(
    r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['21','22'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('24',plain,(
    ! [X55: $i,X56: $i,X57: $i] :
      ( ~ ( r2_hidden @ X57 @ X56 )
      | ( r1_tarski @ X57 @ X55 )
      | ( X56
       != ( k1_zfmisc_1 @ X55 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('25',plain,(
    ! [X55: $i,X57: $i] :
      ( ( r1_tarski @ X57 @ X55 )
      | ~ ( r2_hidden @ X57 @ ( k1_zfmisc_1 @ X55 ) ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['23','25'])).

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

thf('27',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r1_tarski @ X8 @ X9 )
      | ~ ( r1_tarski @ X10 @ X9 )
      | ( r1_tarski @ X10 @ ( sk_D @ X10 @ X9 @ X8 ) )
      | ( X9
        = ( k2_xboole_0 @ X8 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t14_xboole_1])).

thf('28',plain,(
    ! [X59: $i,X60: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X59 @ X60 ) )
      = ( k2_xboole_0 @ X59 @ X60 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('29',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r1_tarski @ X8 @ X9 )
      | ~ ( r1_tarski @ X10 @ X9 )
      | ( r1_tarski @ X10 @ ( sk_D @ X10 @ X9 @ X8 ) )
      | ( X9
        = ( k3_tarski @ ( k2_tarski @ X8 @ X10 ) ) ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( sk_A
        = ( k3_tarski @ ( k2_tarski @ sk_B @ X0 ) ) )
      | ( r1_tarski @ X0 @ ( sk_D @ X0 @ sk_A @ sk_B ) )
      | ~ ( r1_tarski @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['26','29'])).

thf('31',plain,
    ( ( r1_tarski @ sk_A @ ( sk_D @ sk_A @ sk_A @ sk_B ) )
    | ( sk_A
      = ( k3_tarski @ ( k2_tarski @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['18','30'])).

thf('32',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r1_tarski @ X8 @ X9 )
      | ~ ( r1_tarski @ X10 @ X9 )
      | ~ ( r1_tarski @ X9 @ ( sk_D @ X10 @ X9 @ X8 ) )
      | ( X9
        = ( k2_xboole_0 @ X8 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t14_xboole_1])).

thf('33',plain,(
    ! [X59: $i,X60: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X59 @ X60 ) )
      = ( k2_xboole_0 @ X59 @ X60 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('34',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r1_tarski @ X8 @ X9 )
      | ~ ( r1_tarski @ X10 @ X9 )
      | ~ ( r1_tarski @ X9 @ ( sk_D @ X10 @ X9 @ X8 ) )
      | ( X9
        = ( k3_tarski @ ( k2_tarski @ X8 @ X10 ) ) ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,
    ( ( sk_A
      = ( k3_tarski @ ( k2_tarski @ sk_B @ sk_A ) ) )
    | ( sk_A
      = ( k3_tarski @ ( k2_tarski @ sk_B @ sk_A ) ) )
    | ~ ( r1_tarski @ sk_A @ sk_A )
    | ~ ( r1_tarski @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['31','34'])).

thf('36',plain,(
    ! [X4: $i] :
      ( r1_tarski @ X4 @ X4 ) ),
    inference(simplify,[status(thm)],['17'])).

thf('37',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['23','25'])).

thf('38',plain,
    ( ( sk_A
      = ( k3_tarski @ ( k2_tarski @ sk_B @ sk_A ) ) )
    | ( sk_A
      = ( k3_tarski @ ( k2_tarski @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['35','36','37'])).

thf('39',plain,
    ( sk_A
    = ( k3_tarski @ ( k2_tarski @ sk_B @ sk_A ) ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,
    ( ( k3_tarski @ ( k2_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) )
    = sk_A ),
    inference(demod,[status(thm)],['16','39'])).

thf('41',plain,
    ( ( k4_subset_1 @ sk_A @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = sk_A ),
    inference(demod,[status(thm)],['8','40'])).

thf('42',plain,(
    ( k4_subset_1 @ sk_A @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
 != ( k2_subset_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('43',plain,(
    ! [X64: $i] :
      ( ( k2_subset_1 @ X64 )
      = X64 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('44',plain,(
    ( k4_subset_1 @ sk_A @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
 != sk_A ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['41','44'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.cyRJ1eLdaF
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:47:26 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.40/0.59  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.40/0.59  % Solved by: fo/fo7.sh
% 0.40/0.59  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.40/0.59  % done 269 iterations in 0.139s
% 0.40/0.59  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.40/0.59  % SZS output start Refutation
% 0.40/0.59  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.40/0.59  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.40/0.59  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.40/0.59  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.40/0.59  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.40/0.59  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.40/0.59  thf(sk_B_type, type, sk_B: $i).
% 0.40/0.59  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.40/0.59  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.40/0.59  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.40/0.59  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.40/0.59  thf(sk_A_type, type, sk_A: $i).
% 0.40/0.59  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.40/0.59  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.40/0.59  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 0.40/0.59  thf(t25_subset_1, conjecture,
% 0.40/0.59    (![A:$i,B:$i]:
% 0.40/0.59     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.40/0.59       ( ( k4_subset_1 @ A @ B @ ( k3_subset_1 @ A @ B ) ) =
% 0.40/0.59         ( k2_subset_1 @ A ) ) ))).
% 0.40/0.59  thf(zf_stmt_0, negated_conjecture,
% 0.40/0.59    (~( ![A:$i,B:$i]:
% 0.40/0.59        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.40/0.59          ( ( k4_subset_1 @ A @ B @ ( k3_subset_1 @ A @ B ) ) =
% 0.40/0.59            ( k2_subset_1 @ A ) ) ) )),
% 0.40/0.59    inference('cnf.neg', [status(esa)], [t25_subset_1])).
% 0.40/0.59  thf('0', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf(dt_k3_subset_1, axiom,
% 0.40/0.59    (![A:$i,B:$i]:
% 0.40/0.59     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.40/0.59       ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.40/0.59  thf('1', plain,
% 0.40/0.59      (![X67 : $i, X68 : $i]:
% 0.40/0.59         ((m1_subset_1 @ (k3_subset_1 @ X67 @ X68) @ (k1_zfmisc_1 @ X67))
% 0.40/0.59          | ~ (m1_subset_1 @ X68 @ (k1_zfmisc_1 @ X67)))),
% 0.40/0.59      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 0.40/0.59  thf('2', plain,
% 0.40/0.59      ((m1_subset_1 @ (k3_subset_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_A))),
% 0.40/0.59      inference('sup-', [status(thm)], ['0', '1'])).
% 0.40/0.59  thf('3', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf(redefinition_k4_subset_1, axiom,
% 0.40/0.59    (![A:$i,B:$i,C:$i]:
% 0.40/0.59     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 0.40/0.59         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.40/0.59       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 0.40/0.59  thf('4', plain,
% 0.40/0.59      (![X70 : $i, X71 : $i, X72 : $i]:
% 0.40/0.59         (~ (m1_subset_1 @ X70 @ (k1_zfmisc_1 @ X71))
% 0.40/0.59          | ~ (m1_subset_1 @ X72 @ (k1_zfmisc_1 @ X71))
% 0.40/0.59          | ((k4_subset_1 @ X71 @ X70 @ X72) = (k2_xboole_0 @ X70 @ X72)))),
% 0.40/0.59      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 0.40/0.59  thf(l51_zfmisc_1, axiom,
% 0.40/0.59    (![A:$i,B:$i]:
% 0.40/0.59     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.40/0.59  thf('5', plain,
% 0.40/0.59      (![X59 : $i, X60 : $i]:
% 0.40/0.59         ((k3_tarski @ (k2_tarski @ X59 @ X60)) = (k2_xboole_0 @ X59 @ X60))),
% 0.40/0.59      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.40/0.59  thf('6', plain,
% 0.40/0.59      (![X70 : $i, X71 : $i, X72 : $i]:
% 0.40/0.59         (~ (m1_subset_1 @ X70 @ (k1_zfmisc_1 @ X71))
% 0.40/0.59          | ~ (m1_subset_1 @ X72 @ (k1_zfmisc_1 @ X71))
% 0.40/0.59          | ((k4_subset_1 @ X71 @ X70 @ X72)
% 0.40/0.59              = (k3_tarski @ (k2_tarski @ X70 @ X72))))),
% 0.40/0.59      inference('demod', [status(thm)], ['4', '5'])).
% 0.40/0.59  thf('7', plain,
% 0.40/0.59      (![X0 : $i]:
% 0.40/0.59         (((k4_subset_1 @ sk_A @ sk_B @ X0)
% 0.40/0.59            = (k3_tarski @ (k2_tarski @ sk_B @ X0)))
% 0.40/0.59          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A)))),
% 0.40/0.59      inference('sup-', [status(thm)], ['3', '6'])).
% 0.40/0.59  thf('8', plain,
% 0.40/0.59      (((k4_subset_1 @ sk_A @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))
% 0.40/0.59         = (k3_tarski @ (k2_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))))),
% 0.40/0.59      inference('sup-', [status(thm)], ['2', '7'])).
% 0.40/0.59  thf('9', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf(d5_subset_1, axiom,
% 0.40/0.59    (![A:$i,B:$i]:
% 0.40/0.59     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.40/0.59       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.40/0.59  thf('10', plain,
% 0.40/0.59      (![X65 : $i, X66 : $i]:
% 0.40/0.59         (((k3_subset_1 @ X65 @ X66) = (k4_xboole_0 @ X65 @ X66))
% 0.40/0.59          | ~ (m1_subset_1 @ X66 @ (k1_zfmisc_1 @ X65)))),
% 0.40/0.59      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.40/0.59  thf('11', plain,
% 0.40/0.59      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.40/0.59      inference('sup-', [status(thm)], ['9', '10'])).
% 0.40/0.59  thf(t39_xboole_1, axiom,
% 0.40/0.59    (![A:$i,B:$i]:
% 0.40/0.59     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.40/0.59  thf('12', plain,
% 0.40/0.59      (![X11 : $i, X12 : $i]:
% 0.40/0.59         ((k2_xboole_0 @ X11 @ (k4_xboole_0 @ X12 @ X11))
% 0.40/0.59           = (k2_xboole_0 @ X11 @ X12))),
% 0.40/0.59      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.40/0.59  thf('13', plain,
% 0.40/0.59      (![X59 : $i, X60 : $i]:
% 0.40/0.59         ((k3_tarski @ (k2_tarski @ X59 @ X60)) = (k2_xboole_0 @ X59 @ X60))),
% 0.40/0.59      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.40/0.59  thf('14', plain,
% 0.40/0.59      (![X59 : $i, X60 : $i]:
% 0.40/0.59         ((k3_tarski @ (k2_tarski @ X59 @ X60)) = (k2_xboole_0 @ X59 @ X60))),
% 0.40/0.59      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.40/0.59  thf('15', plain,
% 0.40/0.59      (![X11 : $i, X12 : $i]:
% 0.40/0.59         ((k3_tarski @ (k2_tarski @ X11 @ (k4_xboole_0 @ X12 @ X11)))
% 0.40/0.59           = (k3_tarski @ (k2_tarski @ X11 @ X12)))),
% 0.40/0.59      inference('demod', [status(thm)], ['12', '13', '14'])).
% 0.40/0.59  thf('16', plain,
% 0.40/0.59      (((k3_tarski @ (k2_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)))
% 0.40/0.59         = (k3_tarski @ (k2_tarski @ sk_B @ sk_A)))),
% 0.40/0.59      inference('sup+', [status(thm)], ['11', '15'])).
% 0.40/0.59  thf(d10_xboole_0, axiom,
% 0.40/0.59    (![A:$i,B:$i]:
% 0.40/0.59     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.40/0.59  thf('17', plain,
% 0.40/0.59      (![X3 : $i, X4 : $i]: ((r1_tarski @ X3 @ X4) | ((X3) != (X4)))),
% 0.40/0.59      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.40/0.59  thf('18', plain, (![X4 : $i]: (r1_tarski @ X4 @ X4)),
% 0.40/0.59      inference('simplify', [status(thm)], ['17'])).
% 0.40/0.59  thf('19', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf(d2_subset_1, axiom,
% 0.40/0.59    (![A:$i,B:$i]:
% 0.40/0.59     ( ( ( v1_xboole_0 @ A ) =>
% 0.40/0.59         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.40/0.59       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.40/0.59         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.40/0.59  thf('20', plain,
% 0.40/0.59      (![X61 : $i, X62 : $i]:
% 0.40/0.59         (~ (m1_subset_1 @ X61 @ X62)
% 0.40/0.59          | (r2_hidden @ X61 @ X62)
% 0.40/0.59          | (v1_xboole_0 @ X62))),
% 0.40/0.59      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.40/0.59  thf('21', plain,
% 0.40/0.59      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 0.40/0.59        | (r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A)))),
% 0.40/0.59      inference('sup-', [status(thm)], ['19', '20'])).
% 0.40/0.59  thf(fc1_subset_1, axiom,
% 0.40/0.59    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.40/0.59  thf('22', plain, (![X69 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X69))),
% 0.40/0.59      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.40/0.59  thf('23', plain, ((r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.40/0.59      inference('clc', [status(thm)], ['21', '22'])).
% 0.40/0.59  thf(d1_zfmisc_1, axiom,
% 0.40/0.59    (![A:$i,B:$i]:
% 0.40/0.59     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.40/0.59       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.40/0.59  thf('24', plain,
% 0.40/0.59      (![X55 : $i, X56 : $i, X57 : $i]:
% 0.40/0.59         (~ (r2_hidden @ X57 @ X56)
% 0.40/0.59          | (r1_tarski @ X57 @ X55)
% 0.40/0.59          | ((X56) != (k1_zfmisc_1 @ X55)))),
% 0.40/0.59      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.40/0.59  thf('25', plain,
% 0.40/0.59      (![X55 : $i, X57 : $i]:
% 0.40/0.59         ((r1_tarski @ X57 @ X55) | ~ (r2_hidden @ X57 @ (k1_zfmisc_1 @ X55)))),
% 0.40/0.59      inference('simplify', [status(thm)], ['24'])).
% 0.40/0.59  thf('26', plain, ((r1_tarski @ sk_B @ sk_A)),
% 0.40/0.59      inference('sup-', [status(thm)], ['23', '25'])).
% 0.40/0.59  thf(t14_xboole_1, axiom,
% 0.40/0.59    (![A:$i,B:$i,C:$i]:
% 0.40/0.59     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ B ) & 
% 0.40/0.59         ( ![D:$i]:
% 0.40/0.59           ( ( ( r1_tarski @ A @ D ) & ( r1_tarski @ C @ D ) ) =>
% 0.40/0.59             ( r1_tarski @ B @ D ) ) ) ) =>
% 0.40/0.59       ( ( B ) = ( k2_xboole_0 @ A @ C ) ) ))).
% 0.40/0.59  thf('27', plain,
% 0.40/0.59      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.40/0.59         (~ (r1_tarski @ X8 @ X9)
% 0.40/0.59          | ~ (r1_tarski @ X10 @ X9)
% 0.40/0.59          | (r1_tarski @ X10 @ (sk_D @ X10 @ X9 @ X8))
% 0.40/0.59          | ((X9) = (k2_xboole_0 @ X8 @ X10)))),
% 0.40/0.59      inference('cnf', [status(esa)], [t14_xboole_1])).
% 0.40/0.59  thf('28', plain,
% 0.40/0.59      (![X59 : $i, X60 : $i]:
% 0.40/0.59         ((k3_tarski @ (k2_tarski @ X59 @ X60)) = (k2_xboole_0 @ X59 @ X60))),
% 0.40/0.59      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.40/0.59  thf('29', plain,
% 0.40/0.59      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.40/0.59         (~ (r1_tarski @ X8 @ X9)
% 0.40/0.59          | ~ (r1_tarski @ X10 @ X9)
% 0.40/0.59          | (r1_tarski @ X10 @ (sk_D @ X10 @ X9 @ X8))
% 0.40/0.59          | ((X9) = (k3_tarski @ (k2_tarski @ X8 @ X10))))),
% 0.40/0.59      inference('demod', [status(thm)], ['27', '28'])).
% 0.40/0.59  thf('30', plain,
% 0.40/0.59      (![X0 : $i]:
% 0.40/0.59         (((sk_A) = (k3_tarski @ (k2_tarski @ sk_B @ X0)))
% 0.40/0.59          | (r1_tarski @ X0 @ (sk_D @ X0 @ sk_A @ sk_B))
% 0.40/0.59          | ~ (r1_tarski @ X0 @ sk_A))),
% 0.40/0.59      inference('sup-', [status(thm)], ['26', '29'])).
% 0.40/0.59  thf('31', plain,
% 0.40/0.59      (((r1_tarski @ sk_A @ (sk_D @ sk_A @ sk_A @ sk_B))
% 0.40/0.59        | ((sk_A) = (k3_tarski @ (k2_tarski @ sk_B @ sk_A))))),
% 0.40/0.59      inference('sup-', [status(thm)], ['18', '30'])).
% 0.40/0.59  thf('32', plain,
% 0.40/0.59      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.40/0.59         (~ (r1_tarski @ X8 @ X9)
% 0.40/0.59          | ~ (r1_tarski @ X10 @ X9)
% 0.40/0.59          | ~ (r1_tarski @ X9 @ (sk_D @ X10 @ X9 @ X8))
% 0.40/0.59          | ((X9) = (k2_xboole_0 @ X8 @ X10)))),
% 0.40/0.59      inference('cnf', [status(esa)], [t14_xboole_1])).
% 0.40/0.59  thf('33', plain,
% 0.40/0.59      (![X59 : $i, X60 : $i]:
% 0.40/0.59         ((k3_tarski @ (k2_tarski @ X59 @ X60)) = (k2_xboole_0 @ X59 @ X60))),
% 0.40/0.59      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.40/0.59  thf('34', plain,
% 0.40/0.59      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.40/0.59         (~ (r1_tarski @ X8 @ X9)
% 0.40/0.59          | ~ (r1_tarski @ X10 @ X9)
% 0.40/0.59          | ~ (r1_tarski @ X9 @ (sk_D @ X10 @ X9 @ X8))
% 0.40/0.59          | ((X9) = (k3_tarski @ (k2_tarski @ X8 @ X10))))),
% 0.40/0.59      inference('demod', [status(thm)], ['32', '33'])).
% 0.40/0.59  thf('35', plain,
% 0.40/0.59      ((((sk_A) = (k3_tarski @ (k2_tarski @ sk_B @ sk_A)))
% 0.40/0.59        | ((sk_A) = (k3_tarski @ (k2_tarski @ sk_B @ sk_A)))
% 0.40/0.59        | ~ (r1_tarski @ sk_A @ sk_A)
% 0.40/0.59        | ~ (r1_tarski @ sk_B @ sk_A))),
% 0.40/0.59      inference('sup-', [status(thm)], ['31', '34'])).
% 0.40/0.59  thf('36', plain, (![X4 : $i]: (r1_tarski @ X4 @ X4)),
% 0.40/0.59      inference('simplify', [status(thm)], ['17'])).
% 0.40/0.59  thf('37', plain, ((r1_tarski @ sk_B @ sk_A)),
% 0.40/0.59      inference('sup-', [status(thm)], ['23', '25'])).
% 0.40/0.59  thf('38', plain,
% 0.40/0.59      ((((sk_A) = (k3_tarski @ (k2_tarski @ sk_B @ sk_A)))
% 0.40/0.59        | ((sk_A) = (k3_tarski @ (k2_tarski @ sk_B @ sk_A))))),
% 0.40/0.59      inference('demod', [status(thm)], ['35', '36', '37'])).
% 0.40/0.59  thf('39', plain, (((sk_A) = (k3_tarski @ (k2_tarski @ sk_B @ sk_A)))),
% 0.40/0.59      inference('simplify', [status(thm)], ['38'])).
% 0.40/0.59  thf('40', plain,
% 0.40/0.59      (((k3_tarski @ (k2_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))) = (sk_A))),
% 0.40/0.59      inference('demod', [status(thm)], ['16', '39'])).
% 0.40/0.59  thf('41', plain,
% 0.40/0.59      (((k4_subset_1 @ sk_A @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)) = (sk_A))),
% 0.40/0.59      inference('demod', [status(thm)], ['8', '40'])).
% 0.40/0.59  thf('42', plain,
% 0.40/0.59      (((k4_subset_1 @ sk_A @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))
% 0.40/0.59         != (k2_subset_1 @ sk_A))),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.40/0.59  thf('43', plain, (![X64 : $i]: ((k2_subset_1 @ X64) = (X64))),
% 0.40/0.59      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.40/0.59  thf('44', plain,
% 0.40/0.59      (((k4_subset_1 @ sk_A @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)) != (sk_A))),
% 0.40/0.59      inference('demod', [status(thm)], ['42', '43'])).
% 0.40/0.59  thf('45', plain, ($false),
% 0.40/0.59      inference('simplify_reflect-', [status(thm)], ['41', '44'])).
% 0.40/0.59  
% 0.40/0.59  % SZS output end Refutation
% 0.40/0.59  
% 0.40/0.60  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
