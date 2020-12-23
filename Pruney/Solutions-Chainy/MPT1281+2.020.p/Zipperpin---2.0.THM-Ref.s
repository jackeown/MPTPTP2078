%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Ihix5c2QOd

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:04:47 EST 2020

% Result     : Theorem 2.53s
% Output     : Refutation 2.53s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 108 expanded)
%              Number of leaves         :   24 (  42 expanded)
%              Depth                    :   10
%              Number of atoms          :  551 (1223 expanded)
%              Number of equality atoms :   22 (  23 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v5_tops_1_type,type,(
    v5_tops_1: $i > $i > $o )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t103_tops_1,conjecture,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v5_tops_1 @ B @ A )
           => ( r1_tarski @ ( k2_tops_1 @ A @ B ) @ ( k2_pre_topc @ A @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_pre_topc @ A )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( ( v5_tops_1 @ B @ A )
             => ( r1_tarski @ ( k2_tops_1 @ A @ B ) @ ( k2_pre_topc @ A @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t103_tops_1])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k1_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('2',plain,(
    ! [X45: $i,X46: $i] :
      ( ~ ( l1_pre_topc @ X45 )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X45 ) ) )
      | ( m1_subset_1 @ ( k1_tops_1 @ X45 @ X46 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X45 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tops_1])).

thf('3',plain,
    ( ( m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('7',plain,(
    ! [X47: $i,X48: $i] :
      ( ~ ( l1_pre_topc @ X47 )
      | ~ ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X47 ) ) )
      | ( m1_subset_1 @ ( k2_tops_1 @ X47 @ X48 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X47 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_1])).

thf('8',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('11',plain,(
    ! [X39: $i,X40: $i,X41: $i] :
      ( ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ X40 ) )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ X40 ) )
      | ( ( k4_subset_1 @ X40 @ X39 @ X41 )
        = ( k2_xboole_0 @ X39 @ X41 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('12',plain,(
    ! [X32: $i,X33: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X32 @ X33 ) )
      = ( k2_xboole_0 @ X32 @ X33 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('13',plain,(
    ! [X39: $i,X40: $i,X41: $i] :
      ( ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ X40 ) )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ X40 ) )
      | ( ( k4_subset_1 @ X40 @ X39 @ X41 )
        = ( k3_tarski @ ( k2_tarski @ X39 @ X41 ) ) ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_1 @ sk_A @ sk_B ) @ X0 )
        = ( k3_tarski @ ( k2_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ X0 ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['10','13'])).

thf('15',plain,
    ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k3_tarski @ ( k2_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['5','14'])).

thf('16',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('17',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf(commutativity_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k4_subset_1 @ A @ C @ B ) ) ) )).

thf('18',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ X35 ) )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ X35 ) )
      | ( ( k4_subset_1 @ X35 @ X34 @ X36 )
        = ( k4_subset_1 @ X35 @ X36 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k4_subset_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B ) @ X0 )
        = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,
    ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['16','19'])).

thf('21',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf(t65_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_pre_topc @ A @ B )
            = ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('22',plain,(
    ! [X51: $i,X52: $i] :
      ( ~ ( m1_subset_1 @ X51 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X52 ) ) )
      | ( ( k2_pre_topc @ X52 @ X51 )
        = ( k4_subset_1 @ ( u1_struct_0 @ X52 ) @ X51 @ ( k2_tops_1 @ X52 @ X51 ) ) )
      | ~ ( l1_pre_topc @ X52 ) ) ),
    inference(cnf,[status(esa)],[t65_tops_1])).

thf('23',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) )
      = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t102_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v5_tops_1 @ B @ A )
           => ( ( k2_tops_1 @ A @ ( k1_tops_1 @ A @ B ) )
              = ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('26',plain,(
    ! [X49: $i,X50: $i] :
      ( ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X50 ) ) )
      | ( ( k2_tops_1 @ X50 @ ( k1_tops_1 @ X50 @ X49 ) )
        = ( k2_tops_1 @ X50 @ X49 ) )
      | ~ ( v5_tops_1 @ X49 @ X50 )
      | ~ ( l1_pre_topc @ X50 ) ) ),
    inference(cnf,[status(esa)],[t102_tops_1])).

thf('27',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v5_tops_1 @ sk_B @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) )
      = ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    v5_tops_1 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ( k2_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k2_tops_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['27','28','29'])).

thf('31',plain,
    ( ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['23','24','30'])).

thf('32',plain,
    ( ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['20','31'])).

thf('33',plain,
    ( ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k3_tarski @ ( k2_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['15','32'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('34',plain,(
    ! [X3: $i,X4: $i] :
      ( r1_tarski @ X3 @ ( k2_xboole_0 @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('35',plain,(
    ! [X32: $i,X33: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X32 @ X33 ) )
      = ( k2_xboole_0 @ X32 @ X33 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('36',plain,(
    ! [X3: $i,X4: $i] :
      ( r1_tarski @ X3 @ ( k3_tarski @ ( k2_tarski @ X3 @ X4 ) ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,(
    r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['33','36'])).

thf('38',plain,(
    $false ),
    inference(demod,[status(thm)],['0','37'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Ihix5c2QOd
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:51:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 2.53/2.70  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 2.53/2.70  % Solved by: fo/fo7.sh
% 2.53/2.70  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.53/2.70  % done 2061 iterations in 2.248s
% 2.53/2.70  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 2.53/2.70  % SZS output start Refutation
% 2.53/2.70  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 2.53/2.70  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 2.53/2.70  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 2.53/2.70  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 2.53/2.70  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 2.53/2.70  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 2.53/2.70  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 2.53/2.70  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 2.53/2.70  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 2.53/2.70  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 2.53/2.70  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 2.53/2.70  thf(sk_A_type, type, sk_A: $i).
% 2.53/2.70  thf(v5_tops_1_type, type, v5_tops_1: $i > $i > $o).
% 2.53/2.70  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 2.53/2.70  thf(sk_B_type, type, sk_B: $i).
% 2.53/2.70  thf(t103_tops_1, conjecture,
% 2.53/2.70    (![A:$i]:
% 2.53/2.70     ( ( l1_pre_topc @ A ) =>
% 2.53/2.70       ( ![B:$i]:
% 2.53/2.70         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.53/2.70           ( ( v5_tops_1 @ B @ A ) =>
% 2.53/2.70             ( r1_tarski @
% 2.53/2.70               ( k2_tops_1 @ A @ B ) @ 
% 2.53/2.70               ( k2_pre_topc @ A @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ))).
% 2.53/2.70  thf(zf_stmt_0, negated_conjecture,
% 2.53/2.70    (~( ![A:$i]:
% 2.53/2.70        ( ( l1_pre_topc @ A ) =>
% 2.53/2.70          ( ![B:$i]:
% 2.53/2.70            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.53/2.70              ( ( v5_tops_1 @ B @ A ) =>
% 2.53/2.70                ( r1_tarski @
% 2.53/2.70                  ( k2_tops_1 @ A @ B ) @ 
% 2.53/2.70                  ( k2_pre_topc @ A @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ) )),
% 2.53/2.70    inference('cnf.neg', [status(esa)], [t103_tops_1])).
% 2.53/2.70  thf('0', plain,
% 2.53/2.70      (~ (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 2.53/2.70          (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))),
% 2.53/2.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.53/2.70  thf('1', plain,
% 2.53/2.70      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.53/2.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.53/2.70  thf(dt_k1_tops_1, axiom,
% 2.53/2.70    (![A:$i,B:$i]:
% 2.53/2.70     ( ( ( l1_pre_topc @ A ) & 
% 2.53/2.70         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 2.53/2.70       ( m1_subset_1 @
% 2.53/2.70         ( k1_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 2.53/2.70  thf('2', plain,
% 2.53/2.70      (![X45 : $i, X46 : $i]:
% 2.53/2.70         (~ (l1_pre_topc @ X45)
% 2.53/2.70          | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (u1_struct_0 @ X45)))
% 2.53/2.70          | (m1_subset_1 @ (k1_tops_1 @ X45 @ X46) @ 
% 2.53/2.70             (k1_zfmisc_1 @ (u1_struct_0 @ X45))))),
% 2.53/2.70      inference('cnf', [status(esa)], [dt_k1_tops_1])).
% 2.53/2.70  thf('3', plain,
% 2.53/2.70      (((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 2.53/2.70         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 2.53/2.70        | ~ (l1_pre_topc @ sk_A))),
% 2.53/2.70      inference('sup-', [status(thm)], ['1', '2'])).
% 2.53/2.70  thf('4', plain, ((l1_pre_topc @ sk_A)),
% 2.53/2.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.53/2.70  thf('5', plain,
% 2.53/2.70      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 2.53/2.70        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.53/2.70      inference('demod', [status(thm)], ['3', '4'])).
% 2.53/2.70  thf('6', plain,
% 2.53/2.70      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.53/2.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.53/2.70  thf(dt_k2_tops_1, axiom,
% 2.53/2.70    (![A:$i,B:$i]:
% 2.53/2.70     ( ( ( l1_pre_topc @ A ) & 
% 2.53/2.70         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 2.53/2.70       ( m1_subset_1 @
% 2.53/2.70         ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 2.53/2.70  thf('7', plain,
% 2.53/2.70      (![X47 : $i, X48 : $i]:
% 2.53/2.70         (~ (l1_pre_topc @ X47)
% 2.53/2.70          | ~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ (u1_struct_0 @ X47)))
% 2.53/2.70          | (m1_subset_1 @ (k2_tops_1 @ X47 @ X48) @ 
% 2.53/2.70             (k1_zfmisc_1 @ (u1_struct_0 @ X47))))),
% 2.53/2.70      inference('cnf', [status(esa)], [dt_k2_tops_1])).
% 2.53/2.70  thf('8', plain,
% 2.53/2.70      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 2.53/2.70         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 2.53/2.70        | ~ (l1_pre_topc @ sk_A))),
% 2.53/2.70      inference('sup-', [status(thm)], ['6', '7'])).
% 2.53/2.70  thf('9', plain, ((l1_pre_topc @ sk_A)),
% 2.53/2.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.53/2.70  thf('10', plain,
% 2.53/2.70      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 2.53/2.70        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.53/2.70      inference('demod', [status(thm)], ['8', '9'])).
% 2.53/2.70  thf(redefinition_k4_subset_1, axiom,
% 2.53/2.70    (![A:$i,B:$i,C:$i]:
% 2.53/2.70     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 2.53/2.70         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 2.53/2.70       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 2.53/2.70  thf('11', plain,
% 2.53/2.70      (![X39 : $i, X40 : $i, X41 : $i]:
% 2.53/2.70         (~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ X40))
% 2.53/2.70          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ X40))
% 2.53/2.70          | ((k4_subset_1 @ X40 @ X39 @ X41) = (k2_xboole_0 @ X39 @ X41)))),
% 2.53/2.70      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 2.53/2.70  thf(l51_zfmisc_1, axiom,
% 2.53/2.70    (![A:$i,B:$i]:
% 2.53/2.70     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 2.53/2.70  thf('12', plain,
% 2.53/2.70      (![X32 : $i, X33 : $i]:
% 2.53/2.70         ((k3_tarski @ (k2_tarski @ X32 @ X33)) = (k2_xboole_0 @ X32 @ X33))),
% 2.53/2.70      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 2.53/2.70  thf('13', plain,
% 2.53/2.70      (![X39 : $i, X40 : $i, X41 : $i]:
% 2.53/2.70         (~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ X40))
% 2.53/2.70          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ X40))
% 2.53/2.70          | ((k4_subset_1 @ X40 @ X39 @ X41)
% 2.53/2.70              = (k3_tarski @ (k2_tarski @ X39 @ X41))))),
% 2.53/2.70      inference('demod', [status(thm)], ['11', '12'])).
% 2.53/2.70  thf('14', plain,
% 2.53/2.70      (![X0 : $i]:
% 2.53/2.70         (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_tops_1 @ sk_A @ sk_B) @ X0)
% 2.53/2.70            = (k3_tarski @ (k2_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ X0)))
% 2.53/2.70          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 2.53/2.70      inference('sup-', [status(thm)], ['10', '13'])).
% 2.53/2.70  thf('15', plain,
% 2.53/2.70      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 2.53/2.70         (k1_tops_1 @ sk_A @ sk_B))
% 2.53/2.70         = (k3_tarski @ 
% 2.53/2.70            (k2_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ sk_B))))),
% 2.53/2.70      inference('sup-', [status(thm)], ['5', '14'])).
% 2.53/2.70  thf('16', plain,
% 2.53/2.70      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 2.53/2.70        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.53/2.70      inference('demod', [status(thm)], ['8', '9'])).
% 2.53/2.70  thf('17', plain,
% 2.53/2.70      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 2.53/2.70        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.53/2.70      inference('demod', [status(thm)], ['3', '4'])).
% 2.53/2.70  thf(commutativity_k4_subset_1, axiom,
% 2.53/2.70    (![A:$i,B:$i,C:$i]:
% 2.53/2.70     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 2.53/2.70         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 2.53/2.70       ( ( k4_subset_1 @ A @ B @ C ) = ( k4_subset_1 @ A @ C @ B ) ) ))).
% 2.53/2.70  thf('18', plain,
% 2.53/2.70      (![X34 : $i, X35 : $i, X36 : $i]:
% 2.53/2.70         (~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ X35))
% 2.53/2.70          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ X35))
% 2.53/2.70          | ((k4_subset_1 @ X35 @ X34 @ X36) = (k4_subset_1 @ X35 @ X36 @ X34)))),
% 2.53/2.70      inference('cnf', [status(esa)], [commutativity_k4_subset_1])).
% 2.53/2.70  thf('19', plain,
% 2.53/2.70      (![X0 : $i]:
% 2.53/2.70         (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B) @ X0)
% 2.53/2.70            = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ 
% 2.53/2.70               (k1_tops_1 @ sk_A @ sk_B)))
% 2.53/2.70          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 2.53/2.70      inference('sup-', [status(thm)], ['17', '18'])).
% 2.53/2.70  thf('20', plain,
% 2.53/2.70      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 2.53/2.70         (k2_tops_1 @ sk_A @ sk_B))
% 2.53/2.70         = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 2.53/2.70            (k1_tops_1 @ sk_A @ sk_B)))),
% 2.53/2.70      inference('sup-', [status(thm)], ['16', '19'])).
% 2.53/2.70  thf('21', plain,
% 2.53/2.70      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 2.53/2.70        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.53/2.70      inference('demod', [status(thm)], ['3', '4'])).
% 2.53/2.70  thf(t65_tops_1, axiom,
% 2.53/2.70    (![A:$i]:
% 2.53/2.70     ( ( l1_pre_topc @ A ) =>
% 2.53/2.70       ( ![B:$i]:
% 2.53/2.70         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.53/2.70           ( ( k2_pre_topc @ A @ B ) =
% 2.53/2.70             ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 2.53/2.70  thf('22', plain,
% 2.53/2.70      (![X51 : $i, X52 : $i]:
% 2.53/2.70         (~ (m1_subset_1 @ X51 @ (k1_zfmisc_1 @ (u1_struct_0 @ X52)))
% 2.53/2.70          | ((k2_pre_topc @ X52 @ X51)
% 2.53/2.70              = (k4_subset_1 @ (u1_struct_0 @ X52) @ X51 @ 
% 2.53/2.70                 (k2_tops_1 @ X52 @ X51)))
% 2.53/2.70          | ~ (l1_pre_topc @ X52))),
% 2.53/2.70      inference('cnf', [status(esa)], [t65_tops_1])).
% 2.53/2.70  thf('23', plain,
% 2.53/2.70      ((~ (l1_pre_topc @ sk_A)
% 2.53/2.70        | ((k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))
% 2.53/2.70            = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 2.53/2.70               (k1_tops_1 @ sk_A @ sk_B) @ 
% 2.53/2.70               (k2_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))))),
% 2.53/2.70      inference('sup-', [status(thm)], ['21', '22'])).
% 2.53/2.70  thf('24', plain, ((l1_pre_topc @ sk_A)),
% 2.53/2.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.53/2.70  thf('25', plain,
% 2.53/2.70      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.53/2.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.53/2.70  thf(t102_tops_1, axiom,
% 2.53/2.70    (![A:$i]:
% 2.53/2.70     ( ( l1_pre_topc @ A ) =>
% 2.53/2.70       ( ![B:$i]:
% 2.53/2.70         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.53/2.70           ( ( v5_tops_1 @ B @ A ) =>
% 2.53/2.70             ( ( k2_tops_1 @ A @ ( k1_tops_1 @ A @ B ) ) =
% 2.53/2.70               ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 2.53/2.70  thf('26', plain,
% 2.53/2.70      (![X49 : $i, X50 : $i]:
% 2.53/2.70         (~ (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ (u1_struct_0 @ X50)))
% 2.53/2.70          | ((k2_tops_1 @ X50 @ (k1_tops_1 @ X50 @ X49))
% 2.53/2.70              = (k2_tops_1 @ X50 @ X49))
% 2.53/2.70          | ~ (v5_tops_1 @ X49 @ X50)
% 2.53/2.70          | ~ (l1_pre_topc @ X50))),
% 2.53/2.70      inference('cnf', [status(esa)], [t102_tops_1])).
% 2.53/2.70  thf('27', plain,
% 2.53/2.70      ((~ (l1_pre_topc @ sk_A)
% 2.53/2.70        | ~ (v5_tops_1 @ sk_B @ sk_A)
% 2.53/2.70        | ((k2_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))
% 2.53/2.70            = (k2_tops_1 @ sk_A @ sk_B)))),
% 2.53/2.70      inference('sup-', [status(thm)], ['25', '26'])).
% 2.53/2.70  thf('28', plain, ((l1_pre_topc @ sk_A)),
% 2.53/2.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.53/2.70  thf('29', plain, ((v5_tops_1 @ sk_B @ sk_A)),
% 2.53/2.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.53/2.70  thf('30', plain,
% 2.53/2.70      (((k2_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))
% 2.53/2.70         = (k2_tops_1 @ sk_A @ sk_B))),
% 2.53/2.70      inference('demod', [status(thm)], ['27', '28', '29'])).
% 2.53/2.70  thf('31', plain,
% 2.53/2.70      (((k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))
% 2.53/2.70         = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 2.53/2.70            (k2_tops_1 @ sk_A @ sk_B)))),
% 2.53/2.70      inference('demod', [status(thm)], ['23', '24', '30'])).
% 2.53/2.70  thf('32', plain,
% 2.53/2.70      (((k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))
% 2.53/2.70         = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 2.53/2.70            (k1_tops_1 @ sk_A @ sk_B)))),
% 2.53/2.70      inference('sup+', [status(thm)], ['20', '31'])).
% 2.53/2.70  thf('33', plain,
% 2.53/2.70      (((k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))
% 2.53/2.70         = (k3_tarski @ 
% 2.53/2.70            (k2_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ sk_B))))),
% 2.53/2.70      inference('sup+', [status(thm)], ['15', '32'])).
% 2.53/2.70  thf(t7_xboole_1, axiom,
% 2.53/2.70    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 2.53/2.70  thf('34', plain,
% 2.53/2.70      (![X3 : $i, X4 : $i]: (r1_tarski @ X3 @ (k2_xboole_0 @ X3 @ X4))),
% 2.53/2.70      inference('cnf', [status(esa)], [t7_xboole_1])).
% 2.53/2.70  thf('35', plain,
% 2.53/2.70      (![X32 : $i, X33 : $i]:
% 2.53/2.70         ((k3_tarski @ (k2_tarski @ X32 @ X33)) = (k2_xboole_0 @ X32 @ X33))),
% 2.53/2.70      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 2.53/2.70  thf('36', plain,
% 2.53/2.70      (![X3 : $i, X4 : $i]:
% 2.53/2.70         (r1_tarski @ X3 @ (k3_tarski @ (k2_tarski @ X3 @ X4)))),
% 2.53/2.70      inference('demod', [status(thm)], ['34', '35'])).
% 2.53/2.70  thf('37', plain,
% 2.53/2.70      ((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 2.53/2.70        (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))),
% 2.53/2.70      inference('sup+', [status(thm)], ['33', '36'])).
% 2.53/2.70  thf('38', plain, ($false), inference('demod', [status(thm)], ['0', '37'])).
% 2.53/2.70  
% 2.53/2.70  % SZS output end Refutation
% 2.53/2.70  
% 2.53/2.71  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
