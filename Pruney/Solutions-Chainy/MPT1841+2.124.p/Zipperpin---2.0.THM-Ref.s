%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.OvPGKbSWxv

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:11:45 EST 2020

% Result     : Theorem 0.25s
% Output     : Refutation 0.25s
% Verified   : 
% Statistics : Number of formulae       :   65 (  86 expanded)
%              Number of leaves         :   28 (  37 expanded)
%              Depth                    :   10
%              Number of atoms          :  407 ( 634 expanded)
%              Number of equality atoms :   19 (  22 expanded)
%              Maximal formula depth    :   19 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(k5_enumset1_type,type,(
    k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k6_enumset1_type,type,(
    k6_enumset1: $i > $i > $i > $i > $i > $i > $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k4_enumset1_type,type,(
    k4_enumset1: $i > $i > $i > $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(v1_zfmisc_1_type,type,(
    v1_zfmisc_1: $i > $o )).

thf(t6_tex_2,conjecture,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ A )
         => ~ ( ( v1_subset_1 @ ( k6_domain_1 @ A @ B ) @ A )
              & ( v1_zfmisc_1 @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ~ ( v1_xboole_0 @ A )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ A )
           => ~ ( ( v1_subset_1 @ ( k6_domain_1 @ A @ B ) @ A )
                & ( v1_zfmisc_1 @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t6_tex_2])).

thf('0',plain,(
    m1_subset_1 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( m1_subset_1 @ ( k6_domain_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('1',plain,(
    ! [X36: $i,X37: $i] :
      ( ( v1_xboole_0 @ X36 )
      | ~ ( m1_subset_1 @ X37 @ X36 )
      | ( m1_subset_1 @ ( k6_domain_1 @ X36 @ X37 ) @ ( k1_zfmisc_1 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_domain_1])).

thf('2',plain,
    ( ( m1_subset_1 @ ( k6_domain_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    m1_subset_1 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( ( k6_domain_1 @ A @ B )
        = ( k1_tarski @ B ) ) ) )).

thf('4',plain,(
    ! [X38: $i,X39: $i] :
      ( ( v1_xboole_0 @ X38 )
      | ~ ( m1_subset_1 @ X39 @ X38 )
      | ( ( k6_domain_1 @ X38 @ X39 )
        = ( k1_tarski @ X39 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('5',plain,
    ( ( ( k6_domain_1 @ sk_A @ sk_B )
      = ( k1_tarski @ sk_B ) )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( k6_domain_1 @ sk_A @ sk_B )
    = ( k1_tarski @ sk_B ) ),
    inference(clc,[status(thm)],['5','6'])).

thf('8',plain,
    ( ( m1_subset_1 @ ( k1_tarski @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) )
    | ( v1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['2','7'])).

thf('9',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    m1_subset_1 @ ( k1_tarski @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['8','9'])).

thf(cc2_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( v1_zfmisc_1 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( ~ ( v1_xboole_0 @ B )
           => ~ ( v1_subset_1 @ B @ A ) ) ) ) )).

thf('11',plain,(
    ! [X40: $i,X41: $i] :
      ( ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ X41 ) )
      | ~ ( v1_subset_1 @ X40 @ X41 )
      | ( v1_xboole_0 @ X40 )
      | ~ ( v1_zfmisc_1 @ X41 )
      | ( v1_xboole_0 @ X41 ) ) ),
    inference(cnf,[status(esa)],[cc2_tex_2])).

thf('12',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ~ ( v1_zfmisc_1 @ sk_A )
    | ( v1_xboole_0 @ ( k1_tarski @ sk_B ) )
    | ~ ( v1_subset_1 @ ( k1_tarski @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    v1_zfmisc_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    v1_subset_1 @ ( k6_domain_1 @ sk_A @ sk_B ) @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ( k6_domain_1 @ sk_A @ sk_B )
    = ( k1_tarski @ sk_B ) ),
    inference(clc,[status(thm)],['5','6'])).

thf('16',plain,(
    v1_subset_1 @ ( k1_tarski @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ ( k1_tarski @ sk_B ) ) ),
    inference(demod,[status(thm)],['12','13','16'])).

thf('18',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    v1_xboole_0 @ ( k1_tarski @ sk_B ) ),
    inference(clc,[status(thm)],['17','18'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k2_tarski @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('21',plain,(
    ! [X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X1 @ X1 @ X2 )
      = ( k2_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('22',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( k2_enumset1 @ X3 @ X3 @ X4 @ X5 )
      = ( k1_enumset1 @ X3 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf(t72_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k3_enumset1 @ A @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ B @ C @ D ) ) )).

thf('23',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( k3_enumset1 @ X6 @ X6 @ X7 @ X8 @ X9 )
      = ( k2_enumset1 @ X6 @ X7 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf(t73_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E )
      = ( k3_enumset1 @ A @ B @ C @ D @ E ) ) )).

thf('24',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( k4_enumset1 @ X10 @ X10 @ X11 @ X12 @ X13 @ X14 )
      = ( k3_enumset1 @ X10 @ X11 @ X12 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf(t74_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F )
      = ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ) )).

thf('25',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ( k5_enumset1 @ X15 @ X15 @ X16 @ X17 @ X18 @ X19 @ X20 )
      = ( k4_enumset1 @ X15 @ X16 @ X17 @ X18 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t74_enumset1])).

thf(t75_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i] :
      ( ( k6_enumset1 @ A @ A @ B @ C @ D @ E @ F @ G )
      = ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) ) )).

thf('26',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ( k6_enumset1 @ X21 @ X21 @ X22 @ X23 @ X24 @ X25 @ X26 @ X27 )
      = ( k5_enumset1 @ X21 @ X22 @ X23 @ X24 @ X25 @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t75_enumset1])).

thf(fc7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i] :
      ~ ( v1_xboole_0 @ ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H ) ) )).

thf('27',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i,X32: $i,X33: $i,X34: $i,X35: $i] :
      ~ ( v1_xboole_0 @ ( k6_enumset1 @ X28 @ X29 @ X30 @ X31 @ X32 @ X33 @ X34 @ X35 ) ) ),
    inference(cnf,[status(esa)],[fc7_subset_1])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ~ ( v1_xboole_0 @ ( k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ~ ( v1_xboole_0 @ ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['25','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ~ ( v1_xboole_0 @ ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['24','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ~ ( v1_xboole_0 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['23','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ~ ( v1_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['22','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( v1_xboole_0 @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['21','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','33'])).

thf('35',plain,(
    $false ),
    inference('sup-',[status(thm)],['19','34'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.16  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.OvPGKbSWxv
% 0.16/0.39  % Computer   : n024.cluster.edu
% 0.16/0.39  % Model      : x86_64 x86_64
% 0.16/0.39  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.39  % Memory     : 8042.1875MB
% 0.16/0.39  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.39  % CPULimit   : 60
% 0.16/0.39  % DateTime   : Tue Dec  1 12:56:36 EST 2020
% 0.16/0.39  % CPUTime    : 
% 0.16/0.39  % Running portfolio for 600 s
% 0.16/0.39  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.16/0.40  % Number of cores: 8
% 0.16/0.40  % Python version: Python 3.6.8
% 0.16/0.40  % Running in FO mode
% 0.25/0.53  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.25/0.53  % Solved by: fo/fo7.sh
% 0.25/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.25/0.53  % done 37 iterations in 0.025s
% 0.25/0.53  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.25/0.53  % SZS output start Refutation
% 0.25/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.25/0.53  thf(k5_enumset1_type, type, k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i).
% 0.25/0.53  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.25/0.53  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.25/0.53  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.25/0.53  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.25/0.53  thf(k6_enumset1_type, type, k6_enumset1: $i > $i > $i > $i > $i > $i > $i > 
% 0.25/0.53                                           $i > $i).
% 0.25/0.53  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.25/0.53  thf(k4_enumset1_type, type, k4_enumset1: $i > $i > $i > $i > $i > $i > $i).
% 0.25/0.53  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.25/0.53  thf(sk_B_type, type, sk_B: $i).
% 0.25/0.53  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.25/0.53  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.25/0.53  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 0.25/0.53  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 0.25/0.53  thf(v1_zfmisc_1_type, type, v1_zfmisc_1: $i > $o).
% 0.25/0.53  thf(t6_tex_2, conjecture,
% 0.25/0.53    (![A:$i]:
% 0.25/0.53     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.25/0.53       ( ![B:$i]:
% 0.25/0.53         ( ( m1_subset_1 @ B @ A ) =>
% 0.25/0.53           ( ~( ( v1_subset_1 @ ( k6_domain_1 @ A @ B ) @ A ) & 
% 0.25/0.53                ( v1_zfmisc_1 @ A ) ) ) ) ) ))).
% 0.25/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.25/0.53    (~( ![A:$i]:
% 0.25/0.53        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.25/0.53          ( ![B:$i]:
% 0.25/0.53            ( ( m1_subset_1 @ B @ A ) =>
% 0.25/0.53              ( ~( ( v1_subset_1 @ ( k6_domain_1 @ A @ B ) @ A ) & 
% 0.25/0.53                   ( v1_zfmisc_1 @ A ) ) ) ) ) ) )),
% 0.25/0.53    inference('cnf.neg', [status(esa)], [t6_tex_2])).
% 0.25/0.53  thf('0', plain, ((m1_subset_1 @ sk_B @ sk_A)),
% 0.25/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.53  thf(dt_k6_domain_1, axiom,
% 0.25/0.53    (![A:$i,B:$i]:
% 0.25/0.53     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.25/0.53       ( m1_subset_1 @ ( k6_domain_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.25/0.53  thf('1', plain,
% 0.25/0.53      (![X36 : $i, X37 : $i]:
% 0.25/0.53         ((v1_xboole_0 @ X36)
% 0.25/0.53          | ~ (m1_subset_1 @ X37 @ X36)
% 0.25/0.53          | (m1_subset_1 @ (k6_domain_1 @ X36 @ X37) @ (k1_zfmisc_1 @ X36)))),
% 0.25/0.53      inference('cnf', [status(esa)], [dt_k6_domain_1])).
% 0.25/0.53  thf('2', plain,
% 0.25/0.53      (((m1_subset_1 @ (k6_domain_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_A))
% 0.25/0.53        | (v1_xboole_0 @ sk_A))),
% 0.25/0.53      inference('sup-', [status(thm)], ['0', '1'])).
% 0.25/0.53  thf('3', plain, ((m1_subset_1 @ sk_B @ sk_A)),
% 0.25/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.53  thf(redefinition_k6_domain_1, axiom,
% 0.25/0.53    (![A:$i,B:$i]:
% 0.25/0.53     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.25/0.53       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 0.25/0.53  thf('4', plain,
% 0.25/0.53      (![X38 : $i, X39 : $i]:
% 0.25/0.53         ((v1_xboole_0 @ X38)
% 0.25/0.53          | ~ (m1_subset_1 @ X39 @ X38)
% 0.25/0.53          | ((k6_domain_1 @ X38 @ X39) = (k1_tarski @ X39)))),
% 0.25/0.53      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.25/0.53  thf('5', plain,
% 0.25/0.53      ((((k6_domain_1 @ sk_A @ sk_B) = (k1_tarski @ sk_B))
% 0.25/0.53        | (v1_xboole_0 @ sk_A))),
% 0.25/0.53      inference('sup-', [status(thm)], ['3', '4'])).
% 0.25/0.53  thf('6', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.25/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.53  thf('7', plain, (((k6_domain_1 @ sk_A @ sk_B) = (k1_tarski @ sk_B))),
% 0.25/0.53      inference('clc', [status(thm)], ['5', '6'])).
% 0.25/0.53  thf('8', plain,
% 0.25/0.53      (((m1_subset_1 @ (k1_tarski @ sk_B) @ (k1_zfmisc_1 @ sk_A))
% 0.25/0.53        | (v1_xboole_0 @ sk_A))),
% 0.25/0.53      inference('demod', [status(thm)], ['2', '7'])).
% 0.25/0.53  thf('9', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.25/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.53  thf('10', plain, ((m1_subset_1 @ (k1_tarski @ sk_B) @ (k1_zfmisc_1 @ sk_A))),
% 0.25/0.53      inference('clc', [status(thm)], ['8', '9'])).
% 0.25/0.53  thf(cc2_tex_2, axiom,
% 0.25/0.53    (![A:$i]:
% 0.25/0.53     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_zfmisc_1 @ A ) ) =>
% 0.25/0.53       ( ![B:$i]:
% 0.25/0.53         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.25/0.53           ( ( ~( v1_xboole_0 @ B ) ) => ( ~( v1_subset_1 @ B @ A ) ) ) ) ) ))).
% 0.25/0.53  thf('11', plain,
% 0.25/0.53      (![X40 : $i, X41 : $i]:
% 0.25/0.53         (~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ X41))
% 0.25/0.53          | ~ (v1_subset_1 @ X40 @ X41)
% 0.25/0.53          | (v1_xboole_0 @ X40)
% 0.25/0.53          | ~ (v1_zfmisc_1 @ X41)
% 0.25/0.53          | (v1_xboole_0 @ X41))),
% 0.25/0.53      inference('cnf', [status(esa)], [cc2_tex_2])).
% 0.25/0.53  thf('12', plain,
% 0.25/0.53      (((v1_xboole_0 @ sk_A)
% 0.25/0.53        | ~ (v1_zfmisc_1 @ sk_A)
% 0.25/0.53        | (v1_xboole_0 @ (k1_tarski @ sk_B))
% 0.25/0.53        | ~ (v1_subset_1 @ (k1_tarski @ sk_B) @ sk_A))),
% 0.25/0.53      inference('sup-', [status(thm)], ['10', '11'])).
% 0.25/0.53  thf('13', plain, ((v1_zfmisc_1 @ sk_A)),
% 0.25/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.53  thf('14', plain, ((v1_subset_1 @ (k6_domain_1 @ sk_A @ sk_B) @ sk_A)),
% 0.25/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.53  thf('15', plain, (((k6_domain_1 @ sk_A @ sk_B) = (k1_tarski @ sk_B))),
% 0.25/0.53      inference('clc', [status(thm)], ['5', '6'])).
% 0.25/0.53  thf('16', plain, ((v1_subset_1 @ (k1_tarski @ sk_B) @ sk_A)),
% 0.25/0.53      inference('demod', [status(thm)], ['14', '15'])).
% 0.25/0.53  thf('17', plain,
% 0.25/0.53      (((v1_xboole_0 @ sk_A) | (v1_xboole_0 @ (k1_tarski @ sk_B)))),
% 0.25/0.53      inference('demod', [status(thm)], ['12', '13', '16'])).
% 0.25/0.53  thf('18', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.25/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.53  thf('19', plain, ((v1_xboole_0 @ (k1_tarski @ sk_B))),
% 0.25/0.53      inference('clc', [status(thm)], ['17', '18'])).
% 0.25/0.53  thf(t69_enumset1, axiom,
% 0.25/0.53    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.25/0.53  thf('20', plain, (![X0 : $i]: ((k2_tarski @ X0 @ X0) = (k1_tarski @ X0))),
% 0.25/0.53      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.25/0.53  thf(t70_enumset1, axiom,
% 0.25/0.53    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.25/0.53  thf('21', plain,
% 0.25/0.53      (![X1 : $i, X2 : $i]:
% 0.25/0.53         ((k1_enumset1 @ X1 @ X1 @ X2) = (k2_tarski @ X1 @ X2))),
% 0.25/0.53      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.25/0.53  thf(t71_enumset1, axiom,
% 0.25/0.53    (![A:$i,B:$i,C:$i]:
% 0.25/0.53     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.25/0.53  thf('22', plain,
% 0.25/0.53      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.25/0.53         ((k2_enumset1 @ X3 @ X3 @ X4 @ X5) = (k1_enumset1 @ X3 @ X4 @ X5))),
% 0.25/0.53      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.25/0.53  thf(t72_enumset1, axiom,
% 0.25/0.53    (![A:$i,B:$i,C:$i,D:$i]:
% 0.25/0.53     ( ( k3_enumset1 @ A @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ C @ D ) ))).
% 0.25/0.53  thf('23', plain,
% 0.25/0.53      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.25/0.53         ((k3_enumset1 @ X6 @ X6 @ X7 @ X8 @ X9)
% 0.25/0.53           = (k2_enumset1 @ X6 @ X7 @ X8 @ X9))),
% 0.25/0.53      inference('cnf', [status(esa)], [t72_enumset1])).
% 0.25/0.53  thf(t73_enumset1, axiom,
% 0.25/0.53    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.25/0.53     ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E ) =
% 0.25/0.53       ( k3_enumset1 @ A @ B @ C @ D @ E ) ))).
% 0.25/0.53  thf('24', plain,
% 0.25/0.53      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.25/0.53         ((k4_enumset1 @ X10 @ X10 @ X11 @ X12 @ X13 @ X14)
% 0.25/0.53           = (k3_enumset1 @ X10 @ X11 @ X12 @ X13 @ X14))),
% 0.25/0.53      inference('cnf', [status(esa)], [t73_enumset1])).
% 0.25/0.53  thf(t74_enumset1, axiom,
% 0.25/0.53    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.25/0.53     ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F ) =
% 0.25/0.53       ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ))).
% 0.25/0.53  thf('25', plain,
% 0.25/0.53      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.25/0.53         ((k5_enumset1 @ X15 @ X15 @ X16 @ X17 @ X18 @ X19 @ X20)
% 0.25/0.53           = (k4_enumset1 @ X15 @ X16 @ X17 @ X18 @ X19 @ X20))),
% 0.25/0.54      inference('cnf', [status(esa)], [t74_enumset1])).
% 0.25/0.54  thf(t75_enumset1, axiom,
% 0.25/0.54    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i]:
% 0.25/0.54     ( ( k6_enumset1 @ A @ A @ B @ C @ D @ E @ F @ G ) =
% 0.25/0.54       ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) ))).
% 0.25/0.54  thf('26', plain,
% 0.25/0.54      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 0.25/0.54         ((k6_enumset1 @ X21 @ X21 @ X22 @ X23 @ X24 @ X25 @ X26 @ X27)
% 0.25/0.54           = (k5_enumset1 @ X21 @ X22 @ X23 @ X24 @ X25 @ X26 @ X27))),
% 0.25/0.54      inference('cnf', [status(esa)], [t75_enumset1])).
% 0.25/0.54  thf(fc7_subset_1, axiom,
% 0.25/0.54    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i]:
% 0.25/0.54     ( ~( v1_xboole_0 @ ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H ) ) ))).
% 0.25/0.54  thf('27', plain,
% 0.25/0.54      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i, X34 : $i, 
% 0.25/0.54         X35 : $i]:
% 0.25/0.54         ~ (v1_xboole_0 @ 
% 0.25/0.54            (k6_enumset1 @ X28 @ X29 @ X30 @ X31 @ X32 @ X33 @ X34 @ X35))),
% 0.25/0.54      inference('cnf', [status(esa)], [fc7_subset_1])).
% 0.25/0.54  thf('28', plain,
% 0.25/0.54      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.25/0.54         ~ (v1_xboole_0 @ (k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 0.25/0.54      inference('sup-', [status(thm)], ['26', '27'])).
% 0.25/0.54  thf('29', plain,
% 0.25/0.54      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.25/0.54         ~ (v1_xboole_0 @ (k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 0.25/0.54      inference('sup-', [status(thm)], ['25', '28'])).
% 0.25/0.54  thf('30', plain,
% 0.25/0.54      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.25/0.54         ~ (v1_xboole_0 @ (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 0.25/0.54      inference('sup-', [status(thm)], ['24', '29'])).
% 0.25/0.54  thf('31', plain,
% 0.25/0.54      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.25/0.54         ~ (v1_xboole_0 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 0.25/0.54      inference('sup-', [status(thm)], ['23', '30'])).
% 0.25/0.54  thf('32', plain,
% 0.25/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.25/0.54         ~ (v1_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0))),
% 0.25/0.54      inference('sup-', [status(thm)], ['22', '31'])).
% 0.25/0.54  thf('33', plain,
% 0.25/0.54      (![X0 : $i, X1 : $i]: ~ (v1_xboole_0 @ (k2_tarski @ X1 @ X0))),
% 0.25/0.54      inference('sup-', [status(thm)], ['21', '32'])).
% 0.25/0.54  thf('34', plain, (![X0 : $i]: ~ (v1_xboole_0 @ (k1_tarski @ X0))),
% 0.25/0.54      inference('sup-', [status(thm)], ['20', '33'])).
% 0.25/0.54  thf('35', plain, ($false), inference('sup-', [status(thm)], ['19', '34'])).
% 0.25/0.54  
% 0.25/0.54  % SZS output end Refutation
% 0.25/0.54  
% 0.25/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
