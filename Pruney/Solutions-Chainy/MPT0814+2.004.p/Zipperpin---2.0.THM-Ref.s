%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.PmSxRxd4JF

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:48:38 EST 2020

% Result     : Theorem 0.54s
% Output     : Refutation 0.54s
% Verified   : 
% Statistics : Number of formulae       :   52 ( 171 expanded)
%              Number of leaves         :   19 (  58 expanded)
%              Depth                    :   13
%              Number of atoms          :  303 (1626 expanded)
%              Number of equality atoms :   10 (  54 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_D_2_type,type,(
    sk_D_2: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i > $i )).

thf(t6_relset_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) )
     => ~ ( ( r2_hidden @ A @ D )
          & ! [E: $i,F: $i] :
              ~ ( ( A
                  = ( k4_tarski @ E @ F ) )
                & ( r2_hidden @ E @ B )
                & ( r2_hidden @ F @ C ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) )
       => ~ ( ( r2_hidden @ A @ D )
            & ! [E: $i,F: $i] :
                ~ ( ( A
                    = ( k4_tarski @ E @ F ) )
                  & ( r2_hidden @ E @ B )
                  & ( r2_hidden @ F @ C ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t6_relset_1])).

thf('0',plain,(
    r2_hidden @ sk_A @ sk_D_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('2',plain,(
    ! [X67: $i,X68: $i,X69: $i] :
      ( ~ ( r2_hidden @ X67 @ X68 )
      | ~ ( m1_subset_1 @ X68 @ ( k1_zfmisc_1 @ X69 ) )
      | ( m1_subset_1 @ X67 @ X69 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) )
      | ~ ( r2_hidden @ X0 @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    m1_subset_1 @ sk_A @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['0','3'])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('5',plain,(
    ! [X62: $i,X63: $i] :
      ( ( r2_hidden @ X62 @ X63 )
      | ( v1_xboole_0 @ X63 )
      | ~ ( m1_subset_1 @ X62 @ X63 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('6',plain,
    ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) )
    | ( r2_hidden @ sk_A @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_subset_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_xboole_0 @ B ) ) ) )).

thf('8',plain,(
    ! [X58: $i,X59: $i] :
      ( ~ ( m1_subset_1 @ X58 @ ( k1_zfmisc_1 @ X59 ) )
      | ( v1_xboole_0 @ X58 )
      | ~ ( v1_xboole_0 @ X59 ) ) ),
    inference(cnf,[status(esa)],[cc1_subset_1])).

thf('9',plain,
    ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) )
    | ( v1_xboole_0 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    r2_hidden @ sk_A @ sk_D_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_boole,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( v1_xboole_0 @ B ) ) )).

thf('11',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ X14 @ X15 )
      | ~ ( v1_xboole_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t7_boole])).

thf('12',plain,(
    ~ ( v1_xboole_0 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(clc,[status(thm)],['9','12'])).

thf('14',plain,(
    r2_hidden @ sk_A @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ),
    inference(clc,[status(thm)],['6','13'])).

thf(l139_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) )
        & ! [D: $i,E: $i] :
            ( ( k4_tarski @ D @ E )
           != A ) ) )).

thf('15',plain,(
    ! [X48: $i,X49: $i,X50: $i] :
      ( ( ( k4_tarski @ ( sk_D_1 @ X48 ) @ ( sk_E @ X48 ) )
        = X48 )
      | ~ ( r2_hidden @ X48 @ ( k2_zfmisc_1 @ X49 @ X50 ) ) ) ),
    inference(cnf,[status(esa)],[l139_zfmisc_1])).

thf('16',plain,
    ( ( k4_tarski @ ( sk_D_1 @ sk_A ) @ ( sk_E @ sk_A ) )
    = sk_A ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    r2_hidden @ sk_A @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ),
    inference(clc,[status(thm)],['6','13'])).

thf('18',plain,
    ( ( k4_tarski @ ( sk_D_1 @ sk_A ) @ ( sk_E @ sk_A ) )
    = sk_A ),
    inference('sup-',[status(thm)],['14','15'])).

thf(t106_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ D ) ) ) )).

thf('19',plain,(
    ! [X53: $i,X54: $i,X55: $i,X56: $i] :
      ( ( r2_hidden @ X53 @ X54 )
      | ~ ( r2_hidden @ ( k4_tarski @ X53 @ X55 ) @ ( k2_zfmisc_1 @ X54 @ X56 ) ) ) ),
    inference(cnf,[status(esa)],[t106_zfmisc_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ sk_A @ ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ( r2_hidden @ ( sk_D_1 @ sk_A ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    r2_hidden @ ( sk_D_1 @ sk_A ) @ sk_B ),
    inference('sup-',[status(thm)],['17','20'])).

thf('22',plain,(
    ! [X70: $i,X71: $i] :
      ( ~ ( r2_hidden @ X70 @ sk_B )
      | ~ ( r2_hidden @ X71 @ sk_C )
      | ( sk_A
       != ( k4_tarski @ X70 @ X71 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( sk_A
       != ( k4_tarski @ ( sk_D_1 @ sk_A ) @ X0 ) )
      | ~ ( r2_hidden @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,
    ( ( sk_A != sk_A )
    | ~ ( r2_hidden @ ( sk_E @ sk_A ) @ sk_C ) ),
    inference('sup-',[status(thm)],['16','23'])).

thf('25',plain,(
    ~ ( r2_hidden @ ( sk_E @ sk_A ) @ sk_C ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    r2_hidden @ sk_A @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ),
    inference(clc,[status(thm)],['6','13'])).

thf('27',plain,
    ( ( k4_tarski @ ( sk_D_1 @ sk_A ) @ ( sk_E @ sk_A ) )
    = sk_A ),
    inference('sup-',[status(thm)],['14','15'])).

thf('28',plain,(
    ! [X53: $i,X54: $i,X55: $i,X56: $i] :
      ( ( r2_hidden @ X55 @ X56 )
      | ~ ( r2_hidden @ ( k4_tarski @ X53 @ X55 ) @ ( k2_zfmisc_1 @ X54 @ X56 ) ) ) ),
    inference(cnf,[status(esa)],[t106_zfmisc_1])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ sk_A @ ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ( r2_hidden @ ( sk_E @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    r2_hidden @ ( sk_E @ sk_A ) @ sk_C ),
    inference('sup-',[status(thm)],['26','29'])).

thf('31',plain,(
    $false ),
    inference(demod,[status(thm)],['25','30'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.PmSxRxd4JF
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:18:01 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.54/0.76  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.54/0.76  % Solved by: fo/fo7.sh
% 0.54/0.76  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.54/0.76  % done 292 iterations in 0.302s
% 0.54/0.76  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.54/0.76  % SZS output start Refutation
% 0.54/0.76  thf(sk_A_type, type, sk_A: $i).
% 0.54/0.76  thf(sk_B_type, type, sk_B: $i).
% 0.54/0.76  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.54/0.76  thf(sk_C_type, type, sk_C: $i).
% 0.54/0.76  thf(sk_D_2_type, type, sk_D_2: $i).
% 0.54/0.76  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.54/0.76  thf(sk_D_1_type, type, sk_D_1: $i > $i).
% 0.54/0.76  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.54/0.76  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.54/0.76  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.54/0.76  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.54/0.76  thf(sk_E_type, type, sk_E: $i > $i).
% 0.54/0.76  thf(t6_relset_1, conjecture,
% 0.54/0.76    (![A:$i,B:$i,C:$i,D:$i]:
% 0.54/0.76     ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) =>
% 0.54/0.76       ( ~( ( r2_hidden @ A @ D ) & 
% 0.54/0.76            ( ![E:$i,F:$i]:
% 0.54/0.76              ( ~( ( ( A ) = ( k4_tarski @ E @ F ) ) & ( r2_hidden @ E @ B ) & 
% 0.54/0.76                   ( r2_hidden @ F @ C ) ) ) ) ) ) ))).
% 0.54/0.76  thf(zf_stmt_0, negated_conjecture,
% 0.54/0.76    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.54/0.76        ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) =>
% 0.54/0.76          ( ~( ( r2_hidden @ A @ D ) & 
% 0.54/0.76               ( ![E:$i,F:$i]:
% 0.54/0.76                 ( ~( ( ( A ) = ( k4_tarski @ E @ F ) ) & 
% 0.54/0.76                      ( r2_hidden @ E @ B ) & ( r2_hidden @ F @ C ) ) ) ) ) ) ) )),
% 0.54/0.76    inference('cnf.neg', [status(esa)], [t6_relset_1])).
% 0.54/0.76  thf('0', plain, ((r2_hidden @ sk_A @ sk_D_2)),
% 0.54/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.76  thf('1', plain,
% 0.54/0.76      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 0.54/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.76  thf(t4_subset, axiom,
% 0.54/0.76    (![A:$i,B:$i,C:$i]:
% 0.54/0.76     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 0.54/0.76       ( m1_subset_1 @ A @ C ) ))).
% 0.54/0.76  thf('2', plain,
% 0.54/0.76      (![X67 : $i, X68 : $i, X69 : $i]:
% 0.54/0.76         (~ (r2_hidden @ X67 @ X68)
% 0.54/0.76          | ~ (m1_subset_1 @ X68 @ (k1_zfmisc_1 @ X69))
% 0.54/0.76          | (m1_subset_1 @ X67 @ X69))),
% 0.54/0.76      inference('cnf', [status(esa)], [t4_subset])).
% 0.54/0.76  thf('3', plain,
% 0.54/0.76      (![X0 : $i]:
% 0.54/0.76         ((m1_subset_1 @ X0 @ (k2_zfmisc_1 @ sk_B @ sk_C))
% 0.54/0.76          | ~ (r2_hidden @ X0 @ sk_D_2))),
% 0.54/0.76      inference('sup-', [status(thm)], ['1', '2'])).
% 0.54/0.76  thf('4', plain, ((m1_subset_1 @ sk_A @ (k2_zfmisc_1 @ sk_B @ sk_C))),
% 0.54/0.76      inference('sup-', [status(thm)], ['0', '3'])).
% 0.54/0.76  thf(t2_subset, axiom,
% 0.54/0.76    (![A:$i,B:$i]:
% 0.54/0.76     ( ( m1_subset_1 @ A @ B ) =>
% 0.54/0.76       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.54/0.76  thf('5', plain,
% 0.54/0.76      (![X62 : $i, X63 : $i]:
% 0.54/0.76         ((r2_hidden @ X62 @ X63)
% 0.54/0.76          | (v1_xboole_0 @ X63)
% 0.54/0.76          | ~ (m1_subset_1 @ X62 @ X63))),
% 0.54/0.76      inference('cnf', [status(esa)], [t2_subset])).
% 0.54/0.76  thf('6', plain,
% 0.54/0.76      (((v1_xboole_0 @ (k2_zfmisc_1 @ sk_B @ sk_C))
% 0.54/0.76        | (r2_hidden @ sk_A @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 0.54/0.76      inference('sup-', [status(thm)], ['4', '5'])).
% 0.54/0.76  thf('7', plain,
% 0.54/0.76      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 0.54/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.76  thf(cc1_subset_1, axiom,
% 0.54/0.76    (![A:$i]:
% 0.54/0.76     ( ( v1_xboole_0 @ A ) =>
% 0.54/0.76       ( ![B:$i]:
% 0.54/0.76         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_xboole_0 @ B ) ) ) ))).
% 0.54/0.76  thf('8', plain,
% 0.54/0.76      (![X58 : $i, X59 : $i]:
% 0.54/0.76         (~ (m1_subset_1 @ X58 @ (k1_zfmisc_1 @ X59))
% 0.54/0.76          | (v1_xboole_0 @ X58)
% 0.54/0.76          | ~ (v1_xboole_0 @ X59))),
% 0.54/0.76      inference('cnf', [status(esa)], [cc1_subset_1])).
% 0.54/0.76  thf('9', plain,
% 0.54/0.76      ((~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_B @ sk_C)) | (v1_xboole_0 @ sk_D_2))),
% 0.54/0.76      inference('sup-', [status(thm)], ['7', '8'])).
% 0.54/0.76  thf('10', plain, ((r2_hidden @ sk_A @ sk_D_2)),
% 0.54/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.76  thf(t7_boole, axiom,
% 0.54/0.76    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( v1_xboole_0 @ B ) ) ))).
% 0.54/0.76  thf('11', plain,
% 0.54/0.76      (![X14 : $i, X15 : $i]:
% 0.54/0.76         (~ (r2_hidden @ X14 @ X15) | ~ (v1_xboole_0 @ X15))),
% 0.54/0.76      inference('cnf', [status(esa)], [t7_boole])).
% 0.54/0.76  thf('12', plain, (~ (v1_xboole_0 @ sk_D_2)),
% 0.54/0.76      inference('sup-', [status(thm)], ['10', '11'])).
% 0.54/0.76  thf('13', plain, (~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_B @ sk_C))),
% 0.54/0.76      inference('clc', [status(thm)], ['9', '12'])).
% 0.54/0.76  thf('14', plain, ((r2_hidden @ sk_A @ (k2_zfmisc_1 @ sk_B @ sk_C))),
% 0.54/0.76      inference('clc', [status(thm)], ['6', '13'])).
% 0.54/0.76  thf(l139_zfmisc_1, axiom,
% 0.54/0.76    (![A:$i,B:$i,C:$i]:
% 0.54/0.76     ( ~( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) ) & 
% 0.54/0.76          ( ![D:$i,E:$i]: ( ( k4_tarski @ D @ E ) != ( A ) ) ) ) ))).
% 0.54/0.76  thf('15', plain,
% 0.54/0.76      (![X48 : $i, X49 : $i, X50 : $i]:
% 0.54/0.76         (((k4_tarski @ (sk_D_1 @ X48) @ (sk_E @ X48)) = (X48))
% 0.54/0.76          | ~ (r2_hidden @ X48 @ (k2_zfmisc_1 @ X49 @ X50)))),
% 0.54/0.76      inference('cnf', [status(esa)], [l139_zfmisc_1])).
% 0.54/0.76  thf('16', plain, (((k4_tarski @ (sk_D_1 @ sk_A) @ (sk_E @ sk_A)) = (sk_A))),
% 0.54/0.76      inference('sup-', [status(thm)], ['14', '15'])).
% 0.54/0.76  thf('17', plain, ((r2_hidden @ sk_A @ (k2_zfmisc_1 @ sk_B @ sk_C))),
% 0.54/0.76      inference('clc', [status(thm)], ['6', '13'])).
% 0.54/0.76  thf('18', plain, (((k4_tarski @ (sk_D_1 @ sk_A) @ (sk_E @ sk_A)) = (sk_A))),
% 0.54/0.76      inference('sup-', [status(thm)], ['14', '15'])).
% 0.54/0.76  thf(t106_zfmisc_1, axiom,
% 0.54/0.76    (![A:$i,B:$i,C:$i,D:$i]:
% 0.54/0.76     ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) <=>
% 0.54/0.76       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ D ) ) ))).
% 0.54/0.76  thf('19', plain,
% 0.54/0.76      (![X53 : $i, X54 : $i, X55 : $i, X56 : $i]:
% 0.54/0.76         ((r2_hidden @ X53 @ X54)
% 0.54/0.76          | ~ (r2_hidden @ (k4_tarski @ X53 @ X55) @ (k2_zfmisc_1 @ X54 @ X56)))),
% 0.54/0.76      inference('cnf', [status(esa)], [t106_zfmisc_1])).
% 0.54/0.76  thf('20', plain,
% 0.54/0.76      (![X0 : $i, X1 : $i]:
% 0.54/0.76         (~ (r2_hidden @ sk_A @ (k2_zfmisc_1 @ X1 @ X0))
% 0.54/0.76          | (r2_hidden @ (sk_D_1 @ sk_A) @ X1))),
% 0.54/0.76      inference('sup-', [status(thm)], ['18', '19'])).
% 0.54/0.76  thf('21', plain, ((r2_hidden @ (sk_D_1 @ sk_A) @ sk_B)),
% 0.54/0.76      inference('sup-', [status(thm)], ['17', '20'])).
% 0.54/0.76  thf('22', plain,
% 0.54/0.76      (![X70 : $i, X71 : $i]:
% 0.54/0.76         (~ (r2_hidden @ X70 @ sk_B)
% 0.54/0.76          | ~ (r2_hidden @ X71 @ sk_C)
% 0.54/0.76          | ((sk_A) != (k4_tarski @ X70 @ X71)))),
% 0.54/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.76  thf('23', plain,
% 0.54/0.76      (![X0 : $i]:
% 0.54/0.76         (((sk_A) != (k4_tarski @ (sk_D_1 @ sk_A) @ X0))
% 0.54/0.76          | ~ (r2_hidden @ X0 @ sk_C))),
% 0.54/0.76      inference('sup-', [status(thm)], ['21', '22'])).
% 0.54/0.76  thf('24', plain,
% 0.54/0.76      ((((sk_A) != (sk_A)) | ~ (r2_hidden @ (sk_E @ sk_A) @ sk_C))),
% 0.54/0.76      inference('sup-', [status(thm)], ['16', '23'])).
% 0.54/0.76  thf('25', plain, (~ (r2_hidden @ (sk_E @ sk_A) @ sk_C)),
% 0.54/0.76      inference('simplify', [status(thm)], ['24'])).
% 0.54/0.76  thf('26', plain, ((r2_hidden @ sk_A @ (k2_zfmisc_1 @ sk_B @ sk_C))),
% 0.54/0.76      inference('clc', [status(thm)], ['6', '13'])).
% 0.54/0.76  thf('27', plain, (((k4_tarski @ (sk_D_1 @ sk_A) @ (sk_E @ sk_A)) = (sk_A))),
% 0.54/0.76      inference('sup-', [status(thm)], ['14', '15'])).
% 0.54/0.76  thf('28', plain,
% 0.54/0.76      (![X53 : $i, X54 : $i, X55 : $i, X56 : $i]:
% 0.54/0.76         ((r2_hidden @ X55 @ X56)
% 0.54/0.76          | ~ (r2_hidden @ (k4_tarski @ X53 @ X55) @ (k2_zfmisc_1 @ X54 @ X56)))),
% 0.54/0.76      inference('cnf', [status(esa)], [t106_zfmisc_1])).
% 0.54/0.76  thf('29', plain,
% 0.54/0.76      (![X0 : $i, X1 : $i]:
% 0.54/0.76         (~ (r2_hidden @ sk_A @ (k2_zfmisc_1 @ X1 @ X0))
% 0.54/0.76          | (r2_hidden @ (sk_E @ sk_A) @ X0))),
% 0.54/0.76      inference('sup-', [status(thm)], ['27', '28'])).
% 0.54/0.76  thf('30', plain, ((r2_hidden @ (sk_E @ sk_A) @ sk_C)),
% 0.54/0.76      inference('sup-', [status(thm)], ['26', '29'])).
% 0.54/0.76  thf('31', plain, ($false), inference('demod', [status(thm)], ['25', '30'])).
% 0.54/0.76  
% 0.54/0.76  % SZS output end Refutation
% 0.54/0.76  
% 0.60/0.77  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
