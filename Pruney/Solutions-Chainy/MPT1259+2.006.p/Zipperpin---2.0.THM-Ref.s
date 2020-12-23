%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.LlCi4MH2Lt

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:20 EST 2020

% Result     : Theorem 0.88s
% Output     : Refutation 0.88s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 122 expanded)
%              Number of leaves         :   22 (  46 expanded)
%              Depth                    :   10
%              Number of atoms          :  522 (1556 expanded)
%              Number of equality atoms :   22 (  58 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

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
    ! [X30: $i,X31: $i] :
      ( ~ ( l1_pre_topc @ X30 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X30 ) ) )
      | ( m1_subset_1 @ ( k2_tops_1 @ X30 @ X31 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X30 ) ) ) ) ),
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
    ! [X30: $i,X31: $i] :
      ( ~ ( l1_pre_topc @ X30 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X30 ) ) )
      | ( m1_subset_1 @ ( k2_tops_1 @ X30 @ X31 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X30 ) ) ) ) ),
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
    ! [X34: $i,X35: $i] :
      ( ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X35 ) ) )
      | ( ( k2_tops_1 @ X35 @ X34 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X35 ) @ ( k2_pre_topc @ X35 @ X34 ) @ ( k1_tops_1 @ X35 @ X34 ) ) )
      | ~ ( l1_pre_topc @ X35 ) ) ),
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
    ! [X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) )
      | ~ ( v4_pre_topc @ X28 @ X29 )
      | ( ( k2_pre_topc @ X29 @ X28 )
        = X28 )
      | ~ ( l1_pre_topc @ X29 ) ) ),
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
    ! [X32: $i,X33: $i] :
      ( ~ ( l1_pre_topc @ X32 )
      | ~ ( v2_pre_topc @ X32 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X32 ) ) )
      | ( v4_pre_topc @ ( k2_tops_1 @ X32 @ X33 ) @ X32 ) ) ),
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
    ! [X36: $i,X37: $i] :
      ( ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X37 ) ) )
      | ( ( k1_tops_1 @ X37 @ ( k2_tops_1 @ X37 @ ( k2_tops_1 @ X37 @ X36 ) ) )
        = k1_xboole_0 )
      | ~ ( l1_pre_topc @ X37 )
      | ~ ( v2_pre_topc @ X37 ) ) ),
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
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X21 ) )
      | ( ( k7_subset_1 @ X21 @ X20 @ X22 )
        = ( k4_xboole_0 @ X20 @ X22 ) ) ) ),
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
    ! [X9: $i] :
      ( ( k4_xboole_0 @ X9 @ k1_xboole_0 )
      = X9 ) ),
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
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.LlCi4MH2Lt
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:32:40 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.88/1.13  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.88/1.13  % Solved by: fo/fo7.sh
% 0.88/1.13  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.88/1.13  % done 2177 iterations in 0.662s
% 0.88/1.13  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.88/1.13  % SZS output start Refutation
% 0.88/1.13  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.88/1.13  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.88/1.13  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.88/1.13  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.88/1.13  thf(sk_A_type, type, sk_A: $i).
% 0.88/1.13  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.88/1.13  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.88/1.13  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 0.88/1.13  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.88/1.13  thf(sk_B_type, type, sk_B: $i).
% 0.88/1.13  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 0.88/1.13  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.88/1.13  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.88/1.13  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.88/1.13  thf(t75_tops_1, conjecture,
% 0.88/1.13    (![A:$i]:
% 0.88/1.13     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.88/1.13       ( ![B:$i]:
% 0.88/1.13         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.88/1.13           ( ( k2_tops_1 @ A @ ( k2_tops_1 @ A @ ( k2_tops_1 @ A @ B ) ) ) =
% 0.88/1.13             ( k2_tops_1 @ A @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.88/1.13  thf(zf_stmt_0, negated_conjecture,
% 0.88/1.13    (~( ![A:$i]:
% 0.88/1.13        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.88/1.13          ( ![B:$i]:
% 0.88/1.13            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.88/1.13              ( ( k2_tops_1 @ A @ ( k2_tops_1 @ A @ ( k2_tops_1 @ A @ B ) ) ) =
% 0.88/1.13                ( k2_tops_1 @ A @ ( k2_tops_1 @ A @ B ) ) ) ) ) ) )),
% 0.88/1.13    inference('cnf.neg', [status(esa)], [t75_tops_1])).
% 0.88/1.13  thf('0', plain,
% 0.88/1.13      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.88/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.88/1.13  thf(dt_k2_tops_1, axiom,
% 0.88/1.13    (![A:$i,B:$i]:
% 0.88/1.13     ( ( ( l1_pre_topc @ A ) & 
% 0.88/1.13         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.88/1.13       ( m1_subset_1 @
% 0.88/1.13         ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.88/1.13  thf('1', plain,
% 0.88/1.13      (![X30 : $i, X31 : $i]:
% 0.88/1.13         (~ (l1_pre_topc @ X30)
% 0.88/1.13          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (u1_struct_0 @ X30)))
% 0.88/1.13          | (m1_subset_1 @ (k2_tops_1 @ X30 @ X31) @ 
% 0.88/1.13             (k1_zfmisc_1 @ (u1_struct_0 @ X30))))),
% 0.88/1.13      inference('cnf', [status(esa)], [dt_k2_tops_1])).
% 0.88/1.13  thf('2', plain,
% 0.88/1.13      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.88/1.13         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.88/1.13        | ~ (l1_pre_topc @ sk_A))),
% 0.88/1.13      inference('sup-', [status(thm)], ['0', '1'])).
% 0.88/1.13  thf('3', plain, ((l1_pre_topc @ sk_A)),
% 0.88/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.88/1.13  thf('4', plain,
% 0.88/1.13      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.88/1.13        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.88/1.13      inference('demod', [status(thm)], ['2', '3'])).
% 0.88/1.13  thf('5', plain,
% 0.88/1.13      (![X30 : $i, X31 : $i]:
% 0.88/1.13         (~ (l1_pre_topc @ X30)
% 0.88/1.13          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (u1_struct_0 @ X30)))
% 0.88/1.13          | (m1_subset_1 @ (k2_tops_1 @ X30 @ X31) @ 
% 0.88/1.13             (k1_zfmisc_1 @ (u1_struct_0 @ X30))))),
% 0.88/1.13      inference('cnf', [status(esa)], [dt_k2_tops_1])).
% 0.88/1.13  thf('6', plain,
% 0.88/1.13      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)) @ 
% 0.88/1.13         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.88/1.13        | ~ (l1_pre_topc @ sk_A))),
% 0.88/1.13      inference('sup-', [status(thm)], ['4', '5'])).
% 0.88/1.13  thf('7', plain, ((l1_pre_topc @ sk_A)),
% 0.88/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.88/1.13  thf('8', plain,
% 0.88/1.13      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)) @ 
% 0.88/1.13        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.88/1.13      inference('demod', [status(thm)], ['6', '7'])).
% 0.88/1.13  thf(l78_tops_1, axiom,
% 0.88/1.13    (![A:$i]:
% 0.88/1.13     ( ( l1_pre_topc @ A ) =>
% 0.88/1.13       ( ![B:$i]:
% 0.88/1.13         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.88/1.13           ( ( k2_tops_1 @ A @ B ) =
% 0.88/1.13             ( k7_subset_1 @
% 0.88/1.13               ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 0.88/1.13               ( k1_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.88/1.13  thf('9', plain,
% 0.88/1.13      (![X34 : $i, X35 : $i]:
% 0.88/1.13         (~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (u1_struct_0 @ X35)))
% 0.88/1.13          | ((k2_tops_1 @ X35 @ X34)
% 0.88/1.13              = (k7_subset_1 @ (u1_struct_0 @ X35) @ 
% 0.88/1.13                 (k2_pre_topc @ X35 @ X34) @ (k1_tops_1 @ X35 @ X34)))
% 0.88/1.13          | ~ (l1_pre_topc @ X35))),
% 0.88/1.13      inference('cnf', [status(esa)], [l78_tops_1])).
% 0.88/1.13  thf('10', plain,
% 0.88/1.13      ((~ (l1_pre_topc @ sk_A)
% 0.88/1.13        | ((k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)))
% 0.88/1.13            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.88/1.13               (k2_pre_topc @ sk_A @ 
% 0.88/1.13                (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B))) @ 
% 0.88/1.13               (k1_tops_1 @ sk_A @ 
% 0.88/1.13                (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B))))))),
% 0.88/1.13      inference('sup-', [status(thm)], ['8', '9'])).
% 0.88/1.13  thf('11', plain, ((l1_pre_topc @ sk_A)),
% 0.88/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.88/1.13  thf('12', plain,
% 0.88/1.13      (((k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)))
% 0.88/1.13         = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.88/1.13            (k2_pre_topc @ sk_A @ 
% 0.88/1.13             (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B))) @ 
% 0.88/1.13            (k1_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)))))),
% 0.88/1.13      inference('demod', [status(thm)], ['10', '11'])).
% 0.88/1.13  thf('13', plain,
% 0.88/1.13      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)) @ 
% 0.88/1.13        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.88/1.13      inference('demod', [status(thm)], ['6', '7'])).
% 0.88/1.13  thf(t52_pre_topc, axiom,
% 0.88/1.13    (![A:$i]:
% 0.88/1.13     ( ( l1_pre_topc @ A ) =>
% 0.88/1.13       ( ![B:$i]:
% 0.88/1.13         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.88/1.13           ( ( ( v4_pre_topc @ B @ A ) => ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) & 
% 0.88/1.13             ( ( ( v2_pre_topc @ A ) & ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) =>
% 0.88/1.13               ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 0.88/1.13  thf('14', plain,
% 0.88/1.13      (![X28 : $i, X29 : $i]:
% 0.88/1.13         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (u1_struct_0 @ X29)))
% 0.88/1.13          | ~ (v4_pre_topc @ X28 @ X29)
% 0.88/1.13          | ((k2_pre_topc @ X29 @ X28) = (X28))
% 0.88/1.13          | ~ (l1_pre_topc @ X29))),
% 0.88/1.13      inference('cnf', [status(esa)], [t52_pre_topc])).
% 0.88/1.13  thf('15', plain,
% 0.88/1.13      ((~ (l1_pre_topc @ sk_A)
% 0.88/1.13        | ((k2_pre_topc @ sk_A @ (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)))
% 0.88/1.13            = (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)))
% 0.88/1.13        | ~ (v4_pre_topc @ (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)) @ 
% 0.88/1.13             sk_A))),
% 0.88/1.13      inference('sup-', [status(thm)], ['13', '14'])).
% 0.88/1.13  thf('16', plain, ((l1_pre_topc @ sk_A)),
% 0.88/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.88/1.13  thf('17', plain,
% 0.88/1.13      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.88/1.13        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.88/1.13      inference('demod', [status(thm)], ['2', '3'])).
% 0.88/1.13  thf(fc11_tops_1, axiom,
% 0.88/1.13    (![A:$i,B:$i]:
% 0.88/1.13     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 0.88/1.13         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.88/1.13       ( v4_pre_topc @ ( k2_tops_1 @ A @ B ) @ A ) ))).
% 0.88/1.13  thf('18', plain,
% 0.88/1.13      (![X32 : $i, X33 : $i]:
% 0.88/1.13         (~ (l1_pre_topc @ X32)
% 0.88/1.13          | ~ (v2_pre_topc @ X32)
% 0.88/1.13          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (u1_struct_0 @ X32)))
% 0.88/1.13          | (v4_pre_topc @ (k2_tops_1 @ X32 @ X33) @ X32))),
% 0.88/1.13      inference('cnf', [status(esa)], [fc11_tops_1])).
% 0.88/1.13  thf('19', plain,
% 0.88/1.13      (((v4_pre_topc @ (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)) @ sk_A)
% 0.88/1.13        | ~ (v2_pre_topc @ sk_A)
% 0.88/1.13        | ~ (l1_pre_topc @ sk_A))),
% 0.88/1.13      inference('sup-', [status(thm)], ['17', '18'])).
% 0.88/1.13  thf('20', plain, ((v2_pre_topc @ sk_A)),
% 0.88/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.88/1.13  thf('21', plain, ((l1_pre_topc @ sk_A)),
% 0.88/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.88/1.13  thf('22', plain,
% 0.88/1.13      ((v4_pre_topc @ (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)) @ sk_A)),
% 0.88/1.13      inference('demod', [status(thm)], ['19', '20', '21'])).
% 0.88/1.13  thf('23', plain,
% 0.88/1.13      (((k2_pre_topc @ sk_A @ (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)))
% 0.88/1.13         = (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.88/1.13      inference('demod', [status(thm)], ['15', '16', '22'])).
% 0.88/1.13  thf('24', plain,
% 0.88/1.13      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.88/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.88/1.13  thf(l80_tops_1, axiom,
% 0.88/1.13    (![A:$i]:
% 0.88/1.13     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.88/1.13       ( ![B:$i]:
% 0.88/1.13         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.88/1.13           ( ( k1_tops_1 @ A @ ( k2_tops_1 @ A @ ( k2_tops_1 @ A @ B ) ) ) =
% 0.88/1.13             ( k1_xboole_0 ) ) ) ) ))).
% 0.88/1.13  thf('25', plain,
% 0.88/1.13      (![X36 : $i, X37 : $i]:
% 0.88/1.13         (~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (u1_struct_0 @ X37)))
% 0.88/1.13          | ((k1_tops_1 @ X37 @ (k2_tops_1 @ X37 @ (k2_tops_1 @ X37 @ X36)))
% 0.88/1.13              = (k1_xboole_0))
% 0.88/1.13          | ~ (l1_pre_topc @ X37)
% 0.88/1.13          | ~ (v2_pre_topc @ X37))),
% 0.88/1.13      inference('cnf', [status(esa)], [l80_tops_1])).
% 0.88/1.13  thf('26', plain,
% 0.88/1.13      ((~ (v2_pre_topc @ sk_A)
% 0.88/1.13        | ~ (l1_pre_topc @ sk_A)
% 0.88/1.13        | ((k1_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)))
% 0.88/1.13            = (k1_xboole_0)))),
% 0.88/1.13      inference('sup-', [status(thm)], ['24', '25'])).
% 0.88/1.13  thf('27', plain, ((v2_pre_topc @ sk_A)),
% 0.88/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.88/1.13  thf('28', plain, ((l1_pre_topc @ sk_A)),
% 0.88/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.88/1.13  thf('29', plain,
% 0.88/1.13      (((k1_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)))
% 0.88/1.13         = (k1_xboole_0))),
% 0.88/1.13      inference('demod', [status(thm)], ['26', '27', '28'])).
% 0.88/1.13  thf('30', plain,
% 0.88/1.13      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)) @ 
% 0.88/1.13        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.88/1.13      inference('demod', [status(thm)], ['6', '7'])).
% 0.88/1.13  thf(redefinition_k7_subset_1, axiom,
% 0.88/1.13    (![A:$i,B:$i,C:$i]:
% 0.88/1.13     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.88/1.13       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 0.88/1.13  thf('31', plain,
% 0.88/1.13      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.88/1.13         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X21))
% 0.88/1.13          | ((k7_subset_1 @ X21 @ X20 @ X22) = (k4_xboole_0 @ X20 @ X22)))),
% 0.88/1.13      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 0.88/1.13  thf('32', plain,
% 0.88/1.13      (![X0 : $i]:
% 0.88/1.13         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.88/1.13           (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)) @ X0)
% 0.88/1.13           = (k4_xboole_0 @ (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)) @ X0))),
% 0.88/1.13      inference('sup-', [status(thm)], ['30', '31'])).
% 0.88/1.13  thf(t3_boole, axiom,
% 0.88/1.13    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.88/1.13  thf('33', plain, (![X9 : $i]: ((k4_xboole_0 @ X9 @ k1_xboole_0) = (X9))),
% 0.88/1.13      inference('cnf', [status(esa)], [t3_boole])).
% 0.88/1.13  thf('34', plain,
% 0.88/1.13      (((k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)))
% 0.88/1.13         = (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.88/1.13      inference('demod', [status(thm)], ['12', '23', '29', '32', '33'])).
% 0.88/1.13  thf('35', plain,
% 0.88/1.13      (((k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)))
% 0.88/1.13         != (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.88/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.88/1.13  thf('36', plain, ($false),
% 0.88/1.13      inference('simplify_reflect-', [status(thm)], ['34', '35'])).
% 0.88/1.13  
% 0.88/1.13  % SZS output end Refutation
% 0.88/1.13  
% 0.88/1.14  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
