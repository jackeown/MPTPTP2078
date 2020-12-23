%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.gUdHvXh4ma

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:21 EST 2020

% Result     : Theorem 0.24s
% Output     : Refutation 0.24s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 123 expanded)
%              Number of leaves         :   22 (  46 expanded)
%              Depth                    :   12
%              Number of atoms          :  538 (1572 expanded)
%              Number of equality atoms :   23 (  59 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

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
    ! [X9: $i,X10: $i] :
      ( ~ ( l1_pre_topc @ X9 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ( m1_subset_1 @ ( k2_tops_1 @ X9 @ X10 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) ) ) ),
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
    ! [X9: $i,X10: $i] :
      ( ~ ( l1_pre_topc @ X9 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ( m1_subset_1 @ ( k2_tops_1 @ X9 @ X10 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) ) ) ),
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
    ! [X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ( ( k2_tops_1 @ X14 @ X13 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X14 ) @ ( k2_pre_topc @ X14 @ X13 ) @ ( k1_tops_1 @ X14 @ X13 ) ) )
      | ~ ( l1_pre_topc @ X14 ) ) ),
    inference(cnf,[status(esa)],[l78_tops_1])).

thf('10',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) @ ( k1_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
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

thf('13',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ~ ( v4_pre_topc @ X7 @ X8 )
      | ( ( k2_pre_topc @ X8 @ X7 )
        = X7 )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('14',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
      = ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
    | ~ ( v4_pre_topc @ ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
      = ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
    | ~ ( v4_pre_topc @ ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) @ sk_A ) ),
    inference(demod,[status(thm)],['14','15'])).

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
    ! [X11: $i,X12: $i] :
      ( ~ ( l1_pre_topc @ X11 )
      | ~ ( v2_pre_topc @ X11 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ( v4_pre_topc @ ( k2_tops_1 @ X11 @ X12 ) @ X11 ) ) ),
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
    inference(demod,[status(thm)],['16','22'])).

thf('24',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('25',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) )
      | ( ( k7_subset_1 @ X5 @ X4 @ X6 )
        = ( k4_xboole_0 @ X4 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) @ X0 )
      = ( k4_xboole_0 @ ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,
    ( ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
    = ( k4_xboole_0 @ ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) @ ( k1_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['10','11','23','26'])).

thf('28',plain,(
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

thf('29',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ( ( k1_tops_1 @ X16 @ ( k2_tops_1 @ X16 @ ( k2_tops_1 @ X16 @ X15 ) ) )
        = k1_xboole_0 )
      | ~ ( l1_pre_topc @ X16 )
      | ~ ( v2_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[l80_tops_1])).

thf('30',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ( k1_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['30','31','32'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('34',plain,(
    ! [X3: $i] :
      ( ( k4_xboole_0 @ X3 @ k1_xboole_0 )
      = X3 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('35',plain,
    ( ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
    = ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['27','33','34'])).

thf('36',plain,(
    ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
 != ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['35','36'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.14/0.15  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.16  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.gUdHvXh4ma
% 0.16/0.38  % Computer   : n010.cluster.edu
% 0.16/0.38  % Model      : x86_64 x86_64
% 0.16/0.38  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.38  % Memory     : 8042.1875MB
% 0.16/0.38  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.38  % CPULimit   : 60
% 0.16/0.38  % DateTime   : Tue Dec  1 11:53:30 EST 2020
% 0.16/0.38  % CPUTime    : 
% 0.16/0.38  % Running portfolio for 600 s
% 0.16/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.16/0.38  % Number of cores: 8
% 0.16/0.38  % Python version: Python 3.6.8
% 0.16/0.39  % Running in FO mode
% 0.24/0.53  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.24/0.53  % Solved by: fo/fo7.sh
% 0.24/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.24/0.53  % done 60 iterations in 0.039s
% 0.24/0.53  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.24/0.53  % SZS output start Refutation
% 0.24/0.53  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.24/0.53  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.24/0.53  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.24/0.53  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.24/0.53  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.24/0.53  thf(sk_B_type, type, sk_B: $i).
% 0.24/0.53  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.24/0.53  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.24/0.53  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 0.24/0.53  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.24/0.53  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 0.24/0.53  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.24/0.53  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.24/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.24/0.53  thf(t75_tops_1, conjecture,
% 0.24/0.53    (![A:$i]:
% 0.24/0.53     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.24/0.53       ( ![B:$i]:
% 0.24/0.53         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.24/0.53           ( ( k2_tops_1 @ A @ ( k2_tops_1 @ A @ ( k2_tops_1 @ A @ B ) ) ) =
% 0.24/0.53             ( k2_tops_1 @ A @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.24/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.24/0.53    (~( ![A:$i]:
% 0.24/0.53        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.24/0.53          ( ![B:$i]:
% 0.24/0.53            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.24/0.53              ( ( k2_tops_1 @ A @ ( k2_tops_1 @ A @ ( k2_tops_1 @ A @ B ) ) ) =
% 0.24/0.53                ( k2_tops_1 @ A @ ( k2_tops_1 @ A @ B ) ) ) ) ) ) )),
% 0.24/0.53    inference('cnf.neg', [status(esa)], [t75_tops_1])).
% 0.24/0.53  thf('0', plain,
% 0.24/0.53      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.24/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.53  thf(dt_k2_tops_1, axiom,
% 0.24/0.53    (![A:$i,B:$i]:
% 0.24/0.53     ( ( ( l1_pre_topc @ A ) & 
% 0.24/0.53         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.24/0.53       ( m1_subset_1 @
% 0.24/0.53         ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.24/0.53  thf('1', plain,
% 0.24/0.53      (![X9 : $i, X10 : $i]:
% 0.24/0.53         (~ (l1_pre_topc @ X9)
% 0.24/0.53          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.24/0.53          | (m1_subset_1 @ (k2_tops_1 @ X9 @ X10) @ 
% 0.24/0.53             (k1_zfmisc_1 @ (u1_struct_0 @ X9))))),
% 0.24/0.53      inference('cnf', [status(esa)], [dt_k2_tops_1])).
% 0.24/0.53  thf('2', plain,
% 0.24/0.53      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.24/0.53         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.24/0.53        | ~ (l1_pre_topc @ sk_A))),
% 0.24/0.53      inference('sup-', [status(thm)], ['0', '1'])).
% 0.24/0.53  thf('3', plain, ((l1_pre_topc @ sk_A)),
% 0.24/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.53  thf('4', plain,
% 0.24/0.53      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.24/0.53        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.24/0.53      inference('demod', [status(thm)], ['2', '3'])).
% 0.24/0.53  thf('5', plain,
% 0.24/0.53      (![X9 : $i, X10 : $i]:
% 0.24/0.53         (~ (l1_pre_topc @ X9)
% 0.24/0.53          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.24/0.53          | (m1_subset_1 @ (k2_tops_1 @ X9 @ X10) @ 
% 0.24/0.53             (k1_zfmisc_1 @ (u1_struct_0 @ X9))))),
% 0.24/0.53      inference('cnf', [status(esa)], [dt_k2_tops_1])).
% 0.24/0.53  thf('6', plain,
% 0.24/0.53      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)) @ 
% 0.24/0.53         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.24/0.53        | ~ (l1_pre_topc @ sk_A))),
% 0.24/0.53      inference('sup-', [status(thm)], ['4', '5'])).
% 0.24/0.53  thf('7', plain, ((l1_pre_topc @ sk_A)),
% 0.24/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.53  thf('8', plain,
% 0.24/0.53      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)) @ 
% 0.24/0.53        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.24/0.53      inference('demod', [status(thm)], ['6', '7'])).
% 0.24/0.53  thf(l78_tops_1, axiom,
% 0.24/0.53    (![A:$i]:
% 0.24/0.53     ( ( l1_pre_topc @ A ) =>
% 0.24/0.53       ( ![B:$i]:
% 0.24/0.53         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.24/0.53           ( ( k2_tops_1 @ A @ B ) =
% 0.24/0.53             ( k7_subset_1 @
% 0.24/0.53               ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 0.24/0.53               ( k1_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.24/0.53  thf('9', plain,
% 0.24/0.53      (![X13 : $i, X14 : $i]:
% 0.24/0.53         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.24/0.53          | ((k2_tops_1 @ X14 @ X13)
% 0.24/0.53              = (k7_subset_1 @ (u1_struct_0 @ X14) @ 
% 0.24/0.53                 (k2_pre_topc @ X14 @ X13) @ (k1_tops_1 @ X14 @ X13)))
% 0.24/0.53          | ~ (l1_pre_topc @ X14))),
% 0.24/0.53      inference('cnf', [status(esa)], [l78_tops_1])).
% 0.24/0.53  thf('10', plain,
% 0.24/0.53      ((~ (l1_pre_topc @ sk_A)
% 0.24/0.53        | ((k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)))
% 0.24/0.53            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.24/0.53               (k2_pre_topc @ sk_A @ 
% 0.24/0.53                (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B))) @ 
% 0.24/0.53               (k1_tops_1 @ sk_A @ 
% 0.24/0.53                (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B))))))),
% 0.24/0.53      inference('sup-', [status(thm)], ['8', '9'])).
% 0.24/0.53  thf('11', plain, ((l1_pre_topc @ sk_A)),
% 0.24/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.53  thf('12', plain,
% 0.24/0.53      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)) @ 
% 0.24/0.53        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.24/0.53      inference('demod', [status(thm)], ['6', '7'])).
% 0.24/0.53  thf(t52_pre_topc, axiom,
% 0.24/0.53    (![A:$i]:
% 0.24/0.53     ( ( l1_pre_topc @ A ) =>
% 0.24/0.53       ( ![B:$i]:
% 0.24/0.53         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.24/0.53           ( ( ( v4_pre_topc @ B @ A ) => ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) & 
% 0.24/0.53             ( ( ( v2_pre_topc @ A ) & ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) =>
% 0.24/0.53               ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 0.24/0.53  thf('13', plain,
% 0.24/0.53      (![X7 : $i, X8 : $i]:
% 0.24/0.53         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 0.24/0.53          | ~ (v4_pre_topc @ X7 @ X8)
% 0.24/0.53          | ((k2_pre_topc @ X8 @ X7) = (X7))
% 0.24/0.53          | ~ (l1_pre_topc @ X8))),
% 0.24/0.53      inference('cnf', [status(esa)], [t52_pre_topc])).
% 0.24/0.53  thf('14', plain,
% 0.24/0.53      ((~ (l1_pre_topc @ sk_A)
% 0.24/0.53        | ((k2_pre_topc @ sk_A @ (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)))
% 0.24/0.53            = (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)))
% 0.24/0.53        | ~ (v4_pre_topc @ (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)) @ 
% 0.24/0.53             sk_A))),
% 0.24/0.53      inference('sup-', [status(thm)], ['12', '13'])).
% 0.24/0.53  thf('15', plain, ((l1_pre_topc @ sk_A)),
% 0.24/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.53  thf('16', plain,
% 0.24/0.53      ((((k2_pre_topc @ sk_A @ (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)))
% 0.24/0.53          = (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)))
% 0.24/0.53        | ~ (v4_pre_topc @ (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)) @ 
% 0.24/0.53             sk_A))),
% 0.24/0.53      inference('demod', [status(thm)], ['14', '15'])).
% 0.24/0.53  thf('17', plain,
% 0.24/0.53      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.24/0.53        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.24/0.53      inference('demod', [status(thm)], ['2', '3'])).
% 0.24/0.53  thf(fc11_tops_1, axiom,
% 0.24/0.53    (![A:$i,B:$i]:
% 0.24/0.53     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 0.24/0.53         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.24/0.53       ( v4_pre_topc @ ( k2_tops_1 @ A @ B ) @ A ) ))).
% 0.24/0.53  thf('18', plain,
% 0.24/0.53      (![X11 : $i, X12 : $i]:
% 0.24/0.53         (~ (l1_pre_topc @ X11)
% 0.24/0.53          | ~ (v2_pre_topc @ X11)
% 0.24/0.53          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.24/0.53          | (v4_pre_topc @ (k2_tops_1 @ X11 @ X12) @ X11))),
% 0.24/0.53      inference('cnf', [status(esa)], [fc11_tops_1])).
% 0.24/0.53  thf('19', plain,
% 0.24/0.53      (((v4_pre_topc @ (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)) @ sk_A)
% 0.24/0.53        | ~ (v2_pre_topc @ sk_A)
% 0.24/0.53        | ~ (l1_pre_topc @ sk_A))),
% 0.24/0.53      inference('sup-', [status(thm)], ['17', '18'])).
% 0.24/0.53  thf('20', plain, ((v2_pre_topc @ sk_A)),
% 0.24/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.53  thf('21', plain, ((l1_pre_topc @ sk_A)),
% 0.24/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.53  thf('22', plain,
% 0.24/0.53      ((v4_pre_topc @ (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)) @ sk_A)),
% 0.24/0.53      inference('demod', [status(thm)], ['19', '20', '21'])).
% 0.24/0.53  thf('23', plain,
% 0.24/0.53      (((k2_pre_topc @ sk_A @ (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)))
% 0.24/0.53         = (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.24/0.53      inference('demod', [status(thm)], ['16', '22'])).
% 0.24/0.53  thf('24', plain,
% 0.24/0.53      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)) @ 
% 0.24/0.53        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.24/0.53      inference('demod', [status(thm)], ['6', '7'])).
% 0.24/0.53  thf(redefinition_k7_subset_1, axiom,
% 0.24/0.53    (![A:$i,B:$i,C:$i]:
% 0.24/0.53     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.24/0.53       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 0.24/0.53  thf('25', plain,
% 0.24/0.53      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.24/0.53         (~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5))
% 0.24/0.53          | ((k7_subset_1 @ X5 @ X4 @ X6) = (k4_xboole_0 @ X4 @ X6)))),
% 0.24/0.53      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 0.24/0.53  thf('26', plain,
% 0.24/0.53      (![X0 : $i]:
% 0.24/0.53         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.24/0.53           (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)) @ X0)
% 0.24/0.53           = (k4_xboole_0 @ (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)) @ X0))),
% 0.24/0.53      inference('sup-', [status(thm)], ['24', '25'])).
% 0.24/0.53  thf('27', plain,
% 0.24/0.53      (((k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)))
% 0.24/0.53         = (k4_xboole_0 @ (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)) @ 
% 0.24/0.53            (k1_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)))))),
% 0.24/0.53      inference('demod', [status(thm)], ['10', '11', '23', '26'])).
% 0.24/0.53  thf('28', plain,
% 0.24/0.53      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.24/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.53  thf(l80_tops_1, axiom,
% 0.24/0.53    (![A:$i]:
% 0.24/0.53     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.24/0.53       ( ![B:$i]:
% 0.24/0.53         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.24/0.53           ( ( k1_tops_1 @ A @ ( k2_tops_1 @ A @ ( k2_tops_1 @ A @ B ) ) ) =
% 0.24/0.53             ( k1_xboole_0 ) ) ) ) ))).
% 0.24/0.53  thf('29', plain,
% 0.24/0.53      (![X15 : $i, X16 : $i]:
% 0.24/0.53         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.24/0.53          | ((k1_tops_1 @ X16 @ (k2_tops_1 @ X16 @ (k2_tops_1 @ X16 @ X15)))
% 0.24/0.53              = (k1_xboole_0))
% 0.24/0.53          | ~ (l1_pre_topc @ X16)
% 0.24/0.53          | ~ (v2_pre_topc @ X16))),
% 0.24/0.53      inference('cnf', [status(esa)], [l80_tops_1])).
% 0.24/0.53  thf('30', plain,
% 0.24/0.53      ((~ (v2_pre_topc @ sk_A)
% 0.24/0.53        | ~ (l1_pre_topc @ sk_A)
% 0.24/0.53        | ((k1_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)))
% 0.24/0.53            = (k1_xboole_0)))),
% 0.24/0.53      inference('sup-', [status(thm)], ['28', '29'])).
% 0.24/0.53  thf('31', plain, ((v2_pre_topc @ sk_A)),
% 0.24/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.53  thf('32', plain, ((l1_pre_topc @ sk_A)),
% 0.24/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.53  thf('33', plain,
% 0.24/0.53      (((k1_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)))
% 0.24/0.53         = (k1_xboole_0))),
% 0.24/0.53      inference('demod', [status(thm)], ['30', '31', '32'])).
% 0.24/0.53  thf(t3_boole, axiom,
% 0.24/0.53    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.24/0.53  thf('34', plain, (![X3 : $i]: ((k4_xboole_0 @ X3 @ k1_xboole_0) = (X3))),
% 0.24/0.53      inference('cnf', [status(esa)], [t3_boole])).
% 0.24/0.53  thf('35', plain,
% 0.24/0.53      (((k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)))
% 0.24/0.53         = (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.24/0.53      inference('demod', [status(thm)], ['27', '33', '34'])).
% 0.24/0.53  thf('36', plain,
% 0.24/0.53      (((k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)))
% 0.24/0.53         != (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.24/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.53  thf('37', plain, ($false),
% 0.24/0.53      inference('simplify_reflect-', [status(thm)], ['35', '36'])).
% 0.24/0.53  
% 0.24/0.53  % SZS output end Refutation
% 0.24/0.53  
% 0.24/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
