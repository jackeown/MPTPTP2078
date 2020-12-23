%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.FEtNXXf5sT

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:19 EST 2020

% Result     : Theorem 2.03s
% Output     : Refutation 2.03s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 123 expanded)
%              Number of leaves         :   22 (  46 expanded)
%              Depth                    :   11
%              Number of atoms          :  542 (1576 expanded)
%              Number of equality atoms :   23 (  59 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

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
    ! [X32: $i,X33: $i] :
      ( ~ ( l1_pre_topc @ X32 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X32 ) ) )
      | ( m1_subset_1 @ ( k2_tops_1 @ X32 @ X33 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X32 ) ) ) ) ),
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
    ! [X32: $i,X33: $i] :
      ( ~ ( l1_pre_topc @ X32 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X32 ) ) )
      | ( m1_subset_1 @ ( k2_tops_1 @ X32 @ X33 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X32 ) ) ) ) ),
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
    ! [X36: $i,X37: $i] :
      ( ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X37 ) ) )
      | ( ( k2_tops_1 @ X37 @ X36 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X37 ) @ ( k2_pre_topc @ X37 @ X36 ) @ ( k1_tops_1 @ X37 @ X36 ) ) )
      | ~ ( l1_pre_topc @ X37 ) ) ),
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
    ! [X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X31 ) ) )
      | ~ ( v4_pre_topc @ X30 @ X31 )
      | ( ( k2_pre_topc @ X31 @ X30 )
        = X30 )
      | ~ ( l1_pre_topc @ X31 ) ) ),
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

thf('17',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
      = ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
    | ~ ( v4_pre_topc @ ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) @ sk_A ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(fc11_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v4_pre_topc @ ( k2_tops_1 @ A @ B ) @ A ) ) )).

thf('19',plain,(
    ! [X34: $i,X35: $i] :
      ( ~ ( l1_pre_topc @ X34 )
      | ~ ( v2_pre_topc @ X34 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X34 ) ) )
      | ( v4_pre_topc @ ( k2_tops_1 @ X34 @ X35 ) @ X34 ) ) ),
    inference(cnf,[status(esa)],[fc11_tops_1])).

thf('20',plain,
    ( ( v4_pre_topc @ ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    v4_pre_topc @ ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) @ sk_A ),
    inference(demod,[status(thm)],['20','21','22'])).

thf('24',plain,
    ( ( k2_pre_topc @ sk_A @ ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
    = ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['17','23'])).

thf('25',plain,(
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

thf('26',plain,(
    ! [X38: $i,X39: $i] :
      ( ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X39 ) ) )
      | ( ( k1_tops_1 @ X39 @ ( k2_tops_1 @ X39 @ ( k2_tops_1 @ X39 @ X38 ) ) )
        = k1_xboole_0 )
      | ~ ( l1_pre_topc @ X39 )
      | ~ ( v2_pre_topc @ X39 ) ) ),
    inference(cnf,[status(esa)],[l80_tops_1])).

thf('27',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ( k1_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['27','28','29'])).

thf('31',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('32',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ X23 ) )
      | ( ( k7_subset_1 @ X23 @ X22 @ X24 )
        = ( k4_xboole_0 @ X22 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) @ X0 )
      = ( k4_xboole_0 @ ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('34',plain,(
    ! [X10: $i] :
      ( ( k4_xboole_0 @ X10 @ k1_xboole_0 )
      = X10 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('35',plain,
    ( ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
    = ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['12','24','30','33','34'])).

thf('36',plain,(
    ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
 != ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['35','36'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.FEtNXXf5sT
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 17:40:41 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 2.03/2.24  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 2.03/2.24  % Solved by: fo/fo7.sh
% 2.03/2.24  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.03/2.24  % done 2253 iterations in 1.783s
% 2.03/2.24  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 2.03/2.24  % SZS output start Refutation
% 2.03/2.24  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 2.03/2.24  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 2.03/2.24  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 2.03/2.24  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 2.03/2.24  thf(sk_A_type, type, sk_A: $i).
% 2.03/2.24  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 2.03/2.24  thf(sk_B_type, type, sk_B: $i).
% 2.03/2.24  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 2.03/2.24  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 2.03/2.24  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 2.03/2.24  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 2.03/2.24  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 2.03/2.24  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 2.03/2.24  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 2.03/2.24  thf(t75_tops_1, conjecture,
% 2.03/2.24    (![A:$i]:
% 2.03/2.24     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 2.03/2.24       ( ![B:$i]:
% 2.03/2.24         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.03/2.24           ( ( k2_tops_1 @ A @ ( k2_tops_1 @ A @ ( k2_tops_1 @ A @ B ) ) ) =
% 2.03/2.24             ( k2_tops_1 @ A @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 2.03/2.24  thf(zf_stmt_0, negated_conjecture,
% 2.03/2.24    (~( ![A:$i]:
% 2.03/2.24        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 2.03/2.24          ( ![B:$i]:
% 2.03/2.24            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.03/2.24              ( ( k2_tops_1 @ A @ ( k2_tops_1 @ A @ ( k2_tops_1 @ A @ B ) ) ) =
% 2.03/2.24                ( k2_tops_1 @ A @ ( k2_tops_1 @ A @ B ) ) ) ) ) ) )),
% 2.03/2.24    inference('cnf.neg', [status(esa)], [t75_tops_1])).
% 2.03/2.24  thf('0', plain,
% 2.03/2.24      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.03/2.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.03/2.24  thf(dt_k2_tops_1, axiom,
% 2.03/2.24    (![A:$i,B:$i]:
% 2.03/2.24     ( ( ( l1_pre_topc @ A ) & 
% 2.03/2.24         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 2.03/2.24       ( m1_subset_1 @
% 2.03/2.24         ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 2.03/2.24  thf('1', plain,
% 2.03/2.24      (![X32 : $i, X33 : $i]:
% 2.03/2.24         (~ (l1_pre_topc @ X32)
% 2.03/2.24          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (u1_struct_0 @ X32)))
% 2.03/2.24          | (m1_subset_1 @ (k2_tops_1 @ X32 @ X33) @ 
% 2.03/2.24             (k1_zfmisc_1 @ (u1_struct_0 @ X32))))),
% 2.03/2.24      inference('cnf', [status(esa)], [dt_k2_tops_1])).
% 2.03/2.24  thf('2', plain,
% 2.03/2.24      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 2.03/2.24         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 2.03/2.24        | ~ (l1_pre_topc @ sk_A))),
% 2.03/2.24      inference('sup-', [status(thm)], ['0', '1'])).
% 2.03/2.24  thf('3', plain, ((l1_pre_topc @ sk_A)),
% 2.03/2.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.03/2.24  thf('4', plain,
% 2.03/2.24      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 2.03/2.24        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.03/2.24      inference('demod', [status(thm)], ['2', '3'])).
% 2.03/2.24  thf('5', plain,
% 2.03/2.24      (![X32 : $i, X33 : $i]:
% 2.03/2.24         (~ (l1_pre_topc @ X32)
% 2.03/2.24          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (u1_struct_0 @ X32)))
% 2.03/2.24          | (m1_subset_1 @ (k2_tops_1 @ X32 @ X33) @ 
% 2.03/2.24             (k1_zfmisc_1 @ (u1_struct_0 @ X32))))),
% 2.03/2.24      inference('cnf', [status(esa)], [dt_k2_tops_1])).
% 2.03/2.24  thf('6', plain,
% 2.03/2.24      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)) @ 
% 2.03/2.24         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 2.03/2.24        | ~ (l1_pre_topc @ sk_A))),
% 2.03/2.24      inference('sup-', [status(thm)], ['4', '5'])).
% 2.03/2.24  thf('7', plain, ((l1_pre_topc @ sk_A)),
% 2.03/2.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.03/2.24  thf('8', plain,
% 2.03/2.24      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)) @ 
% 2.03/2.24        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.03/2.24      inference('demod', [status(thm)], ['6', '7'])).
% 2.03/2.24  thf(l78_tops_1, axiom,
% 2.03/2.24    (![A:$i]:
% 2.03/2.24     ( ( l1_pre_topc @ A ) =>
% 2.03/2.24       ( ![B:$i]:
% 2.03/2.24         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.03/2.24           ( ( k2_tops_1 @ A @ B ) =
% 2.03/2.24             ( k7_subset_1 @
% 2.03/2.24               ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 2.03/2.24               ( k1_tops_1 @ A @ B ) ) ) ) ) ))).
% 2.03/2.24  thf('9', plain,
% 2.03/2.24      (![X36 : $i, X37 : $i]:
% 2.03/2.24         (~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (u1_struct_0 @ X37)))
% 2.03/2.24          | ((k2_tops_1 @ X37 @ X36)
% 2.03/2.24              = (k7_subset_1 @ (u1_struct_0 @ X37) @ 
% 2.03/2.24                 (k2_pre_topc @ X37 @ X36) @ (k1_tops_1 @ X37 @ X36)))
% 2.03/2.24          | ~ (l1_pre_topc @ X37))),
% 2.03/2.24      inference('cnf', [status(esa)], [l78_tops_1])).
% 2.03/2.24  thf('10', plain,
% 2.03/2.24      ((~ (l1_pre_topc @ sk_A)
% 2.03/2.24        | ((k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)))
% 2.03/2.24            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 2.03/2.24               (k2_pre_topc @ sk_A @ 
% 2.03/2.24                (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B))) @ 
% 2.03/2.24               (k1_tops_1 @ sk_A @ 
% 2.03/2.24                (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B))))))),
% 2.03/2.24      inference('sup-', [status(thm)], ['8', '9'])).
% 2.03/2.24  thf('11', plain, ((l1_pre_topc @ sk_A)),
% 2.03/2.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.03/2.24  thf('12', plain,
% 2.03/2.24      (((k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)))
% 2.03/2.24         = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 2.03/2.24            (k2_pre_topc @ sk_A @ 
% 2.03/2.24             (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B))) @ 
% 2.03/2.24            (k1_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)))))),
% 2.03/2.24      inference('demod', [status(thm)], ['10', '11'])).
% 2.03/2.24  thf('13', plain,
% 2.03/2.24      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)) @ 
% 2.03/2.24        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.03/2.24      inference('demod', [status(thm)], ['6', '7'])).
% 2.03/2.24  thf(t52_pre_topc, axiom,
% 2.03/2.24    (![A:$i]:
% 2.03/2.24     ( ( l1_pre_topc @ A ) =>
% 2.03/2.24       ( ![B:$i]:
% 2.03/2.24         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.03/2.24           ( ( ( v4_pre_topc @ B @ A ) => ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) & 
% 2.03/2.24             ( ( ( v2_pre_topc @ A ) & ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) =>
% 2.03/2.24               ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 2.03/2.24  thf('14', plain,
% 2.03/2.24      (![X30 : $i, X31 : $i]:
% 2.03/2.24         (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ X31)))
% 2.03/2.24          | ~ (v4_pre_topc @ X30 @ X31)
% 2.03/2.24          | ((k2_pre_topc @ X31 @ X30) = (X30))
% 2.03/2.24          | ~ (l1_pre_topc @ X31))),
% 2.03/2.24      inference('cnf', [status(esa)], [t52_pre_topc])).
% 2.03/2.24  thf('15', plain,
% 2.03/2.24      ((~ (l1_pre_topc @ sk_A)
% 2.03/2.24        | ((k2_pre_topc @ sk_A @ (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)))
% 2.03/2.24            = (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)))
% 2.03/2.24        | ~ (v4_pre_topc @ (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)) @ 
% 2.03/2.24             sk_A))),
% 2.03/2.24      inference('sup-', [status(thm)], ['13', '14'])).
% 2.03/2.24  thf('16', plain, ((l1_pre_topc @ sk_A)),
% 2.03/2.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.03/2.24  thf('17', plain,
% 2.03/2.24      ((((k2_pre_topc @ sk_A @ (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)))
% 2.03/2.24          = (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)))
% 2.03/2.24        | ~ (v4_pre_topc @ (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)) @ 
% 2.03/2.24             sk_A))),
% 2.03/2.24      inference('demod', [status(thm)], ['15', '16'])).
% 2.03/2.24  thf('18', plain,
% 2.03/2.24      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 2.03/2.24        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.03/2.24      inference('demod', [status(thm)], ['2', '3'])).
% 2.03/2.24  thf(fc11_tops_1, axiom,
% 2.03/2.24    (![A:$i,B:$i]:
% 2.03/2.24     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 2.03/2.24         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 2.03/2.24       ( v4_pre_topc @ ( k2_tops_1 @ A @ B ) @ A ) ))).
% 2.03/2.24  thf('19', plain,
% 2.03/2.24      (![X34 : $i, X35 : $i]:
% 2.03/2.24         (~ (l1_pre_topc @ X34)
% 2.03/2.24          | ~ (v2_pre_topc @ X34)
% 2.03/2.24          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (u1_struct_0 @ X34)))
% 2.03/2.24          | (v4_pre_topc @ (k2_tops_1 @ X34 @ X35) @ X34))),
% 2.03/2.24      inference('cnf', [status(esa)], [fc11_tops_1])).
% 2.03/2.24  thf('20', plain,
% 2.03/2.24      (((v4_pre_topc @ (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)) @ sk_A)
% 2.03/2.24        | ~ (v2_pre_topc @ sk_A)
% 2.03/2.24        | ~ (l1_pre_topc @ sk_A))),
% 2.03/2.24      inference('sup-', [status(thm)], ['18', '19'])).
% 2.03/2.24  thf('21', plain, ((v2_pre_topc @ sk_A)),
% 2.03/2.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.03/2.24  thf('22', plain, ((l1_pre_topc @ sk_A)),
% 2.03/2.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.03/2.24  thf('23', plain,
% 2.03/2.24      ((v4_pre_topc @ (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)) @ sk_A)),
% 2.03/2.24      inference('demod', [status(thm)], ['20', '21', '22'])).
% 2.03/2.24  thf('24', plain,
% 2.03/2.24      (((k2_pre_topc @ sk_A @ (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)))
% 2.03/2.24         = (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)))),
% 2.03/2.24      inference('demod', [status(thm)], ['17', '23'])).
% 2.03/2.24  thf('25', plain,
% 2.03/2.24      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.03/2.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.03/2.24  thf(l80_tops_1, axiom,
% 2.03/2.24    (![A:$i]:
% 2.03/2.24     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 2.03/2.24       ( ![B:$i]:
% 2.03/2.24         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.03/2.24           ( ( k1_tops_1 @ A @ ( k2_tops_1 @ A @ ( k2_tops_1 @ A @ B ) ) ) =
% 2.03/2.24             ( k1_xboole_0 ) ) ) ) ))).
% 2.03/2.24  thf('26', plain,
% 2.03/2.24      (![X38 : $i, X39 : $i]:
% 2.03/2.24         (~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (u1_struct_0 @ X39)))
% 2.03/2.24          | ((k1_tops_1 @ X39 @ (k2_tops_1 @ X39 @ (k2_tops_1 @ X39 @ X38)))
% 2.03/2.24              = (k1_xboole_0))
% 2.03/2.24          | ~ (l1_pre_topc @ X39)
% 2.03/2.24          | ~ (v2_pre_topc @ X39))),
% 2.03/2.24      inference('cnf', [status(esa)], [l80_tops_1])).
% 2.03/2.24  thf('27', plain,
% 2.03/2.24      ((~ (v2_pre_topc @ sk_A)
% 2.03/2.24        | ~ (l1_pre_topc @ sk_A)
% 2.03/2.24        | ((k1_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)))
% 2.03/2.24            = (k1_xboole_0)))),
% 2.03/2.24      inference('sup-', [status(thm)], ['25', '26'])).
% 2.03/2.24  thf('28', plain, ((v2_pre_topc @ sk_A)),
% 2.03/2.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.03/2.24  thf('29', plain, ((l1_pre_topc @ sk_A)),
% 2.03/2.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.03/2.24  thf('30', plain,
% 2.03/2.24      (((k1_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)))
% 2.03/2.24         = (k1_xboole_0))),
% 2.03/2.24      inference('demod', [status(thm)], ['27', '28', '29'])).
% 2.03/2.24  thf('31', plain,
% 2.03/2.24      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)) @ 
% 2.03/2.24        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.03/2.24      inference('demod', [status(thm)], ['6', '7'])).
% 2.03/2.24  thf(redefinition_k7_subset_1, axiom,
% 2.03/2.24    (![A:$i,B:$i,C:$i]:
% 2.03/2.24     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 2.03/2.24       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 2.03/2.24  thf('32', plain,
% 2.03/2.24      (![X22 : $i, X23 : $i, X24 : $i]:
% 2.03/2.24         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ X23))
% 2.03/2.24          | ((k7_subset_1 @ X23 @ X22 @ X24) = (k4_xboole_0 @ X22 @ X24)))),
% 2.03/2.24      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 2.03/2.24  thf('33', plain,
% 2.03/2.24      (![X0 : $i]:
% 2.03/2.24         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 2.03/2.24           (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)) @ X0)
% 2.03/2.24           = (k4_xboole_0 @ (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)) @ X0))),
% 2.03/2.24      inference('sup-', [status(thm)], ['31', '32'])).
% 2.03/2.24  thf(t3_boole, axiom,
% 2.03/2.24    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 2.03/2.24  thf('34', plain, (![X10 : $i]: ((k4_xboole_0 @ X10 @ k1_xboole_0) = (X10))),
% 2.03/2.24      inference('cnf', [status(esa)], [t3_boole])).
% 2.03/2.24  thf('35', plain,
% 2.03/2.24      (((k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)))
% 2.03/2.24         = (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)))),
% 2.03/2.24      inference('demod', [status(thm)], ['12', '24', '30', '33', '34'])).
% 2.03/2.24  thf('36', plain,
% 2.03/2.24      (((k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)))
% 2.03/2.24         != (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)))),
% 2.03/2.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.03/2.24  thf('37', plain, ($false),
% 2.03/2.24      inference('simplify_reflect-', [status(thm)], ['35', '36'])).
% 2.03/2.24  
% 2.03/2.24  % SZS output end Refutation
% 2.03/2.24  
% 2.03/2.25  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
