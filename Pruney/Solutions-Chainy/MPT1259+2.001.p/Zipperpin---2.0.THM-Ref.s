%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.vW1fFEhk6W

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:19 EST 2020

% Result     : Theorem 1.29s
% Output     : Refutation 1.29s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 122 expanded)
%              Number of leaves         :   22 (  46 expanded)
%              Depth                    :   10
%              Number of atoms          :  522 (1556 expanded)
%              Number of equality atoms :   22 (  58 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(t75_tops_1,conjecture,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_tops_1 @ A @ ( k2_tops_1 @ A @ ( k2_tops_1 @ A @ B ) ) )
            = ( k2_tops_1 @ A @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( ( k2_tops_1 @ A @ ( k2_tops_1 @ A @ ( k2_tops_1 @ A @ B ) ) )
              = ( k2_tops_1 @ A @ ( k2_tops_1 @ A @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t75_tops_1])).

thf('0',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('1',plain,(
    ! [X46: $i,X47: $i] :
      ( ~ ( l1_pre_topc @ X46 )
      | ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X46 ) ) )
      | ( m1_subset_1 @ ( k2_tops_1 @ X46 @ X47 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X46 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_1])).

thf('2',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X46: $i,X47: $i] :
      ( ~ ( l1_pre_topc @ X46 )
      | ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X46 ) ) )
      | ( m1_subset_1 @ ( k2_tops_1 @ X46 @ X47 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X46 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_1])).

thf('6',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf(l78_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_tops_1 @ A @ B )
            = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ ( k1_tops_1 @ A @ B ) ) ) ) ) )).

thf('9',plain,(
    ! [X50: $i,X51: $i] :
      ( ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X51 ) ) )
      | ( ( k2_tops_1 @ X51 @ X50 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X51 ) @ ( k2_pre_topc @ X51 @ X50 ) @ ( k1_tops_1 @ X51 @ X50 ) ) )
      | ~ ( l1_pre_topc @ X51 ) ) ),
    inference(cnf,[status(esa)],[l78_tops_1])).

thf('10',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) @ ( k1_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
    = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) @ ( k1_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf(t52_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( ( v4_pre_topc @ B @ A )
             => ( ( k2_pre_topc @ A @ B )
                = B ) )
            & ( ( ( v2_pre_topc @ A )
                & ( ( k2_pre_topc @ A @ B )
                  = B ) )
             => ( v4_pre_topc @ B @ A ) ) ) ) ) )).

thf('14',plain,(
    ! [X44: $i,X45: $i] :
      ( ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X45 ) ) )
      | ~ ( v4_pre_topc @ X44 @ X45 )
      | ( ( k2_pre_topc @ X45 @ X44 )
        = X44 )
      | ~ ( l1_pre_topc @ X45 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('15',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
      = ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
    | ~ ( v4_pre_topc @ ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(fc11_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v4_pre_topc @ ( k2_tops_1 @ A @ B ) @ A ) ) )).

thf('18',plain,(
    ! [X48: $i,X49: $i] :
      ( ~ ( l1_pre_topc @ X48 )
      | ~ ( v2_pre_topc @ X48 )
      | ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X48 ) ) )
      | ( v4_pre_topc @ ( k2_tops_1 @ X48 @ X49 ) @ X48 ) ) ),
    inference(cnf,[status(esa)],[fc11_tops_1])).

thf('19',plain,
    ( ( v4_pre_topc @ ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    v4_pre_topc @ ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) @ sk_A ),
    inference(demod,[status(thm)],['19','20','21'])).

thf('23',plain,
    ( ( k2_pre_topc @ sk_A @ ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
    = ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['15','16','22'])).

thf('24',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l80_tops_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k1_tops_1 @ A @ ( k2_tops_1 @ A @ ( k2_tops_1 @ A @ B ) ) )
            = k1_xboole_0 ) ) ) )).

thf('25',plain,(
    ! [X52: $i,X53: $i] :
      ( ~ ( m1_subset_1 @ X52 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X53 ) ) )
      | ( ( k1_tops_1 @ X53 @ ( k2_tops_1 @ X53 @ ( k2_tops_1 @ X53 @ X52 ) ) )
        = k1_xboole_0 )
      | ~ ( l1_pre_topc @ X53 )
      | ~ ( v2_pre_topc @ X53 ) ) ),
    inference(cnf,[status(esa)],[l80_tops_1])).

thf('26',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ( k1_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['26','27','28'])).

thf('30',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('31',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ X34 ) )
      | ( ( k7_subset_1 @ X34 @ X33 @ X35 )
        = ( k4_xboole_0 @ X33 @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) @ X0 )
      = ( k4_xboole_0 @ ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('33',plain,(
    ! [X18: $i] :
      ( ( k4_xboole_0 @ X18 @ k1_xboole_0 )
      = X18 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('34',plain,
    ( ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
    = ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['12','23','29','32','33'])).

thf('35',plain,(
    ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
 != ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['34','35'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.vW1fFEhk6W
% 0.13/0.35  % Computer   : n008.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 11:49:30 EST 2020
% 0.20/0.35  % CPUTime    : 
% 0.20/0.35  % Running portfolio for 600 s
% 0.20/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.20/0.35  % Number of cores: 8
% 0.20/0.35  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 1.29/1.53  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.29/1.53  % Solved by: fo/fo7.sh
% 1.29/1.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.29/1.53  % done 3279 iterations in 1.066s
% 1.29/1.53  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.29/1.53  % SZS output start Refutation
% 1.29/1.53  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.29/1.53  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 1.29/1.53  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 1.29/1.53  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 1.29/1.53  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 1.29/1.53  thf(sk_A_type, type, sk_A: $i).
% 1.29/1.53  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.29/1.53  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 1.29/1.53  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 1.29/1.53  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.29/1.53  thf(sk_B_type, type, sk_B: $i).
% 1.29/1.53  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 1.29/1.53  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.29/1.53  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 1.29/1.53  thf(t75_tops_1, conjecture,
% 1.29/1.53    (![A:$i]:
% 1.29/1.53     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.29/1.53       ( ![B:$i]:
% 1.29/1.53         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.29/1.53           ( ( k2_tops_1 @ A @ ( k2_tops_1 @ A @ ( k2_tops_1 @ A @ B ) ) ) =
% 1.29/1.53             ( k2_tops_1 @ A @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 1.29/1.53  thf(zf_stmt_0, negated_conjecture,
% 1.29/1.53    (~( ![A:$i]:
% 1.29/1.53        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.29/1.53          ( ![B:$i]:
% 1.29/1.53            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.29/1.53              ( ( k2_tops_1 @ A @ ( k2_tops_1 @ A @ ( k2_tops_1 @ A @ B ) ) ) =
% 1.29/1.53                ( k2_tops_1 @ A @ ( k2_tops_1 @ A @ B ) ) ) ) ) ) )),
% 1.29/1.53    inference('cnf.neg', [status(esa)], [t75_tops_1])).
% 1.29/1.53  thf('0', plain,
% 1.29/1.53      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.29/1.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.53  thf(dt_k2_tops_1, axiom,
% 1.29/1.53    (![A:$i,B:$i]:
% 1.29/1.53     ( ( ( l1_pre_topc @ A ) & 
% 1.29/1.53         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 1.29/1.53       ( m1_subset_1 @
% 1.29/1.53         ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 1.29/1.53  thf('1', plain,
% 1.29/1.53      (![X46 : $i, X47 : $i]:
% 1.29/1.53         (~ (l1_pre_topc @ X46)
% 1.29/1.53          | ~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ (u1_struct_0 @ X46)))
% 1.29/1.53          | (m1_subset_1 @ (k2_tops_1 @ X46 @ X47) @ 
% 1.29/1.53             (k1_zfmisc_1 @ (u1_struct_0 @ X46))))),
% 1.29/1.53      inference('cnf', [status(esa)], [dt_k2_tops_1])).
% 1.29/1.53  thf('2', plain,
% 1.29/1.53      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 1.29/1.53         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.29/1.53        | ~ (l1_pre_topc @ sk_A))),
% 1.29/1.53      inference('sup-', [status(thm)], ['0', '1'])).
% 1.29/1.53  thf('3', plain, ((l1_pre_topc @ sk_A)),
% 1.29/1.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.53  thf('4', plain,
% 1.29/1.53      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 1.29/1.53        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.29/1.53      inference('demod', [status(thm)], ['2', '3'])).
% 1.29/1.53  thf('5', plain,
% 1.29/1.53      (![X46 : $i, X47 : $i]:
% 1.29/1.53         (~ (l1_pre_topc @ X46)
% 1.29/1.53          | ~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ (u1_struct_0 @ X46)))
% 1.29/1.53          | (m1_subset_1 @ (k2_tops_1 @ X46 @ X47) @ 
% 1.29/1.53             (k1_zfmisc_1 @ (u1_struct_0 @ X46))))),
% 1.29/1.53      inference('cnf', [status(esa)], [dt_k2_tops_1])).
% 1.29/1.53  thf('6', plain,
% 1.29/1.53      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)) @ 
% 1.29/1.53         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.29/1.53        | ~ (l1_pre_topc @ sk_A))),
% 1.29/1.53      inference('sup-', [status(thm)], ['4', '5'])).
% 1.29/1.53  thf('7', plain, ((l1_pre_topc @ sk_A)),
% 1.29/1.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.53  thf('8', plain,
% 1.29/1.53      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)) @ 
% 1.29/1.53        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.29/1.53      inference('demod', [status(thm)], ['6', '7'])).
% 1.29/1.53  thf(l78_tops_1, axiom,
% 1.29/1.53    (![A:$i]:
% 1.29/1.53     ( ( l1_pre_topc @ A ) =>
% 1.29/1.53       ( ![B:$i]:
% 1.29/1.53         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.29/1.53           ( ( k2_tops_1 @ A @ B ) =
% 1.29/1.53             ( k7_subset_1 @
% 1.29/1.53               ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 1.29/1.53               ( k1_tops_1 @ A @ B ) ) ) ) ) ))).
% 1.29/1.53  thf('9', plain,
% 1.29/1.53      (![X50 : $i, X51 : $i]:
% 1.29/1.53         (~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ (u1_struct_0 @ X51)))
% 1.29/1.53          | ((k2_tops_1 @ X51 @ X50)
% 1.29/1.53              = (k7_subset_1 @ (u1_struct_0 @ X51) @ 
% 1.29/1.53                 (k2_pre_topc @ X51 @ X50) @ (k1_tops_1 @ X51 @ X50)))
% 1.29/1.53          | ~ (l1_pre_topc @ X51))),
% 1.29/1.53      inference('cnf', [status(esa)], [l78_tops_1])).
% 1.29/1.53  thf('10', plain,
% 1.29/1.53      ((~ (l1_pre_topc @ sk_A)
% 1.29/1.53        | ((k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)))
% 1.29/1.53            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.29/1.53               (k2_pre_topc @ sk_A @ 
% 1.29/1.53                (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B))) @ 
% 1.29/1.53               (k1_tops_1 @ sk_A @ 
% 1.29/1.53                (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B))))))),
% 1.29/1.53      inference('sup-', [status(thm)], ['8', '9'])).
% 1.29/1.53  thf('11', plain, ((l1_pre_topc @ sk_A)),
% 1.29/1.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.53  thf('12', plain,
% 1.29/1.53      (((k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)))
% 1.29/1.53         = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.29/1.53            (k2_pre_topc @ sk_A @ 
% 1.29/1.53             (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B))) @ 
% 1.29/1.53            (k1_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)))))),
% 1.29/1.53      inference('demod', [status(thm)], ['10', '11'])).
% 1.29/1.53  thf('13', plain,
% 1.29/1.53      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)) @ 
% 1.29/1.53        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.29/1.53      inference('demod', [status(thm)], ['6', '7'])).
% 1.29/1.53  thf(t52_pre_topc, axiom,
% 1.29/1.53    (![A:$i]:
% 1.29/1.53     ( ( l1_pre_topc @ A ) =>
% 1.29/1.53       ( ![B:$i]:
% 1.29/1.53         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.29/1.53           ( ( ( v4_pre_topc @ B @ A ) => ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) & 
% 1.29/1.53             ( ( ( v2_pre_topc @ A ) & ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) =>
% 1.29/1.53               ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 1.29/1.53  thf('14', plain,
% 1.29/1.53      (![X44 : $i, X45 : $i]:
% 1.29/1.53         (~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (u1_struct_0 @ X45)))
% 1.29/1.53          | ~ (v4_pre_topc @ X44 @ X45)
% 1.29/1.53          | ((k2_pre_topc @ X45 @ X44) = (X44))
% 1.29/1.53          | ~ (l1_pre_topc @ X45))),
% 1.29/1.53      inference('cnf', [status(esa)], [t52_pre_topc])).
% 1.29/1.53  thf('15', plain,
% 1.29/1.53      ((~ (l1_pre_topc @ sk_A)
% 1.29/1.53        | ((k2_pre_topc @ sk_A @ (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)))
% 1.29/1.53            = (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)))
% 1.29/1.53        | ~ (v4_pre_topc @ (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)) @ 
% 1.29/1.53             sk_A))),
% 1.29/1.53      inference('sup-', [status(thm)], ['13', '14'])).
% 1.29/1.53  thf('16', plain, ((l1_pre_topc @ sk_A)),
% 1.29/1.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.53  thf('17', plain,
% 1.29/1.53      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 1.29/1.53        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.29/1.53      inference('demod', [status(thm)], ['2', '3'])).
% 1.29/1.53  thf(fc11_tops_1, axiom,
% 1.29/1.53    (![A:$i,B:$i]:
% 1.29/1.53     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 1.29/1.53         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 1.29/1.53       ( v4_pre_topc @ ( k2_tops_1 @ A @ B ) @ A ) ))).
% 1.29/1.53  thf('18', plain,
% 1.29/1.53      (![X48 : $i, X49 : $i]:
% 1.29/1.53         (~ (l1_pre_topc @ X48)
% 1.29/1.53          | ~ (v2_pre_topc @ X48)
% 1.29/1.53          | ~ (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ (u1_struct_0 @ X48)))
% 1.29/1.53          | (v4_pre_topc @ (k2_tops_1 @ X48 @ X49) @ X48))),
% 1.29/1.53      inference('cnf', [status(esa)], [fc11_tops_1])).
% 1.29/1.53  thf('19', plain,
% 1.29/1.53      (((v4_pre_topc @ (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)) @ sk_A)
% 1.29/1.53        | ~ (v2_pre_topc @ sk_A)
% 1.29/1.53        | ~ (l1_pre_topc @ sk_A))),
% 1.29/1.53      inference('sup-', [status(thm)], ['17', '18'])).
% 1.29/1.53  thf('20', plain, ((v2_pre_topc @ sk_A)),
% 1.29/1.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.53  thf('21', plain, ((l1_pre_topc @ sk_A)),
% 1.29/1.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.53  thf('22', plain,
% 1.29/1.53      ((v4_pre_topc @ (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)) @ sk_A)),
% 1.29/1.53      inference('demod', [status(thm)], ['19', '20', '21'])).
% 1.29/1.53  thf('23', plain,
% 1.29/1.53      (((k2_pre_topc @ sk_A @ (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)))
% 1.29/1.53         = (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)))),
% 1.29/1.53      inference('demod', [status(thm)], ['15', '16', '22'])).
% 1.29/1.53  thf('24', plain,
% 1.29/1.53      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.29/1.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.53  thf(l80_tops_1, axiom,
% 1.29/1.53    (![A:$i]:
% 1.29/1.53     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.29/1.53       ( ![B:$i]:
% 1.29/1.53         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.29/1.53           ( ( k1_tops_1 @ A @ ( k2_tops_1 @ A @ ( k2_tops_1 @ A @ B ) ) ) =
% 1.29/1.53             ( k1_xboole_0 ) ) ) ) ))).
% 1.29/1.53  thf('25', plain,
% 1.29/1.53      (![X52 : $i, X53 : $i]:
% 1.29/1.53         (~ (m1_subset_1 @ X52 @ (k1_zfmisc_1 @ (u1_struct_0 @ X53)))
% 1.29/1.53          | ((k1_tops_1 @ X53 @ (k2_tops_1 @ X53 @ (k2_tops_1 @ X53 @ X52)))
% 1.29/1.53              = (k1_xboole_0))
% 1.29/1.53          | ~ (l1_pre_topc @ X53)
% 1.29/1.53          | ~ (v2_pre_topc @ X53))),
% 1.29/1.53      inference('cnf', [status(esa)], [l80_tops_1])).
% 1.29/1.53  thf('26', plain,
% 1.29/1.53      ((~ (v2_pre_topc @ sk_A)
% 1.29/1.53        | ~ (l1_pre_topc @ sk_A)
% 1.29/1.53        | ((k1_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)))
% 1.29/1.53            = (k1_xboole_0)))),
% 1.29/1.53      inference('sup-', [status(thm)], ['24', '25'])).
% 1.29/1.53  thf('27', plain, ((v2_pre_topc @ sk_A)),
% 1.29/1.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.53  thf('28', plain, ((l1_pre_topc @ sk_A)),
% 1.29/1.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.53  thf('29', plain,
% 1.29/1.53      (((k1_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)))
% 1.29/1.53         = (k1_xboole_0))),
% 1.29/1.53      inference('demod', [status(thm)], ['26', '27', '28'])).
% 1.29/1.53  thf('30', plain,
% 1.29/1.53      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)) @ 
% 1.29/1.53        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.29/1.53      inference('demod', [status(thm)], ['6', '7'])).
% 1.29/1.53  thf(redefinition_k7_subset_1, axiom,
% 1.29/1.53    (![A:$i,B:$i,C:$i]:
% 1.29/1.53     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.29/1.53       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 1.29/1.53  thf('31', plain,
% 1.29/1.53      (![X33 : $i, X34 : $i, X35 : $i]:
% 1.29/1.53         (~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ X34))
% 1.29/1.53          | ((k7_subset_1 @ X34 @ X33 @ X35) = (k4_xboole_0 @ X33 @ X35)))),
% 1.29/1.53      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 1.29/1.53  thf('32', plain,
% 1.29/1.53      (![X0 : $i]:
% 1.29/1.53         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.29/1.53           (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)) @ X0)
% 1.29/1.53           = (k4_xboole_0 @ (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)) @ X0))),
% 1.29/1.53      inference('sup-', [status(thm)], ['30', '31'])).
% 1.29/1.53  thf(t3_boole, axiom,
% 1.29/1.53    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 1.29/1.53  thf('33', plain, (![X18 : $i]: ((k4_xboole_0 @ X18 @ k1_xboole_0) = (X18))),
% 1.29/1.53      inference('cnf', [status(esa)], [t3_boole])).
% 1.29/1.53  thf('34', plain,
% 1.29/1.53      (((k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)))
% 1.29/1.53         = (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)))),
% 1.29/1.53      inference('demod', [status(thm)], ['12', '23', '29', '32', '33'])).
% 1.29/1.53  thf('35', plain,
% 1.29/1.53      (((k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)))
% 1.29/1.53         != (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)))),
% 1.29/1.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.53  thf('36', plain, ($false),
% 1.29/1.53      inference('simplify_reflect-', [status(thm)], ['34', '35'])).
% 1.29/1.53  
% 1.29/1.53  % SZS output end Refutation
% 1.29/1.53  
% 1.35/1.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
