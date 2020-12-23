%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.KIMEih4Kzp

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:04:45 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 105 expanded)
%              Number of leaves         :   29 (  44 expanded)
%              Depth                    :    8
%              Number of atoms          :  485 (1043 expanded)
%              Number of equality atoms :   27 (  31 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v5_tops_1_type,type,(
    v5_tops_1: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

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

thf(d7_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v5_tops_1 @ B @ A )
          <=> ( B
              = ( k2_pre_topc @ A @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) )).

thf('2',plain,(
    ! [X46: $i,X47: $i] :
      ( ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X47 ) ) )
      | ~ ( v5_tops_1 @ X46 @ X47 )
      | ( X46
        = ( k2_pre_topc @ X47 @ ( k1_tops_1 @ X47 @ X46 ) ) )
      | ~ ( l1_pre_topc @ X47 ) ) ),
    inference(cnf,[status(esa)],[d7_tops_1])).

thf('3',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( sk_B
      = ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ~ ( v5_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    v5_tops_1 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( sk_B
    = ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['3','4','5'])).

thf('7',plain,(
    ~ ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(demod,[status(thm)],['0','6'])).

thf('8',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k1_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('9',plain,(
    ! [X48: $i,X49: $i] :
      ( ~ ( l1_pre_topc @ X48 )
      | ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X48 ) ) )
      | ( m1_subset_1 @ ( k1_tops_1 @ X48 @ X49 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X48 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tops_1])).

thf('10',plain,
    ( ( m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf(l78_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_tops_1 @ A @ B )
            = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ ( k1_tops_1 @ A @ B ) ) ) ) ) )).

thf('13',plain,(
    ! [X50: $i,X51: $i] :
      ( ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X51 ) ) )
      | ( ( k2_tops_1 @ X51 @ X50 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X51 ) @ ( k2_pre_topc @ X51 @ X50 ) @ ( k1_tops_1 @ X51 @ X50 ) ) )
      | ~ ( l1_pre_topc @ X51 ) ) ),
    inference(cnf,[status(esa)],[l78_tops_1])).

thf('14',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) @ ( k1_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
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

thf('17',plain,(
    ! [X52: $i,X53: $i] :
      ( ~ ( m1_subset_1 @ X52 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X53 ) ) )
      | ( ( k2_tops_1 @ X53 @ ( k1_tops_1 @ X53 @ X52 ) )
        = ( k2_tops_1 @ X53 @ X52 ) )
      | ~ ( v5_tops_1 @ X52 @ X53 )
      | ~ ( l1_pre_topc @ X53 ) ) ),
    inference(cnf,[status(esa)],[t102_tops_1])).

thf('18',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v5_tops_1 @ sk_B @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) )
      = ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    v5_tops_1 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ( k2_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k2_tops_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['18','19','20'])).

thf('22',plain,
    ( sk_B
    = ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['3','4','5'])).

thf('23',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('24',plain,(
    ! [X41: $i,X42: $i,X43: $i] :
      ( ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ X42 ) )
      | ( ( k7_subset_1 @ X42 @ X41 @ X43 )
        = ( k4_xboole_0 @ X41 @ X43 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['14','15','21','22','25'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('27',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k2_tarski @ X11 @ X10 )
      = ( k2_tarski @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('28',plain,(
    ! [X39: $i,X40: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X39 @ X40 ) )
      = ( k2_xboole_0 @ X39 @ X40 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X39: $i,X40: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X39 @ X40 ) )
      = ( k2_xboole_0 @ X39 @ X40 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('32',plain,(
    ! [X7: $i] :
      ( r1_tarski @ k1_xboole_0 @ X7 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('33',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k2_xboole_0 @ X6 @ X5 )
        = X5 )
      | ~ ( r1_tarski @ X6 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['31','34'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('36',plain,(
    ! [X8: $i,X9: $i] :
      ( r1_tarski @ X8 @ ( k2_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf(t109_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ ( k4_xboole_0 @ A @ C ) @ B ) ) )).

thf('37',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r1_tarski @ X2 @ X3 )
      | ( r1_tarski @ ( k4_xboole_0 @ X2 @ X4 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[t109_xboole_1])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X1 @ X2 ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference('sup+',[status(thm)],['35','38'])).

thf('40',plain,(
    r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ),
    inference('sup+',[status(thm)],['26','39'])).

thf('41',plain,(
    $false ),
    inference(demod,[status(thm)],['7','40'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.KIMEih4Kzp
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 21:19:46 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.51  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.51  % Solved by: fo/fo7.sh
% 0.20/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.51  % done 107 iterations in 0.057s
% 0.20/0.51  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.51  % SZS output start Refutation
% 0.20/0.51  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.51  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.51  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.20/0.51  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.20/0.51  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.20/0.51  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.20/0.51  thf(v5_tops_1_type, type, v5_tops_1: $i > $i > $o).
% 0.20/0.51  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.51  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.20/0.51  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.51  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 0.20/0.51  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 0.20/0.51  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.20/0.51  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.51  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.20/0.51  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.51  thf(t103_tops_1, conjecture,
% 0.20/0.51    (![A:$i]:
% 0.20/0.51     ( ( l1_pre_topc @ A ) =>
% 0.20/0.51       ( ![B:$i]:
% 0.20/0.51         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.51           ( ( v5_tops_1 @ B @ A ) =>
% 0.20/0.51             ( r1_tarski @
% 0.20/0.51               ( k2_tops_1 @ A @ B ) @ 
% 0.20/0.51               ( k2_pre_topc @ A @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ))).
% 0.20/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.51    (~( ![A:$i]:
% 0.20/0.51        ( ( l1_pre_topc @ A ) =>
% 0.20/0.51          ( ![B:$i]:
% 0.20/0.51            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.51              ( ( v5_tops_1 @ B @ A ) =>
% 0.20/0.51                ( r1_tarski @
% 0.20/0.51                  ( k2_tops_1 @ A @ B ) @ 
% 0.20/0.51                  ( k2_pre_topc @ A @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ) )),
% 0.20/0.51    inference('cnf.neg', [status(esa)], [t103_tops_1])).
% 0.20/0.51  thf('0', plain,
% 0.20/0.51      (~ (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.20/0.51          (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('1', plain,
% 0.20/0.51      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf(d7_tops_1, axiom,
% 0.20/0.51    (![A:$i]:
% 0.20/0.51     ( ( l1_pre_topc @ A ) =>
% 0.20/0.51       ( ![B:$i]:
% 0.20/0.51         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.51           ( ( v5_tops_1 @ B @ A ) <=>
% 0.20/0.51             ( ( B ) = ( k2_pre_topc @ A @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ))).
% 0.20/0.51  thf('2', plain,
% 0.20/0.51      (![X46 : $i, X47 : $i]:
% 0.20/0.51         (~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (u1_struct_0 @ X47)))
% 0.20/0.51          | ~ (v5_tops_1 @ X46 @ X47)
% 0.20/0.51          | ((X46) = (k2_pre_topc @ X47 @ (k1_tops_1 @ X47 @ X46)))
% 0.20/0.51          | ~ (l1_pre_topc @ X47))),
% 0.20/0.51      inference('cnf', [status(esa)], [d7_tops_1])).
% 0.20/0.51  thf('3', plain,
% 0.20/0.51      ((~ (l1_pre_topc @ sk_A)
% 0.20/0.51        | ((sk_B) = (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))
% 0.20/0.51        | ~ (v5_tops_1 @ sk_B @ sk_A))),
% 0.20/0.51      inference('sup-', [status(thm)], ['1', '2'])).
% 0.20/0.51  thf('4', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('5', plain, ((v5_tops_1 @ sk_B @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('6', plain,
% 0.20/0.51      (((sk_B) = (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))),
% 0.20/0.51      inference('demod', [status(thm)], ['3', '4', '5'])).
% 0.20/0.51  thf('7', plain, (~ (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)),
% 0.20/0.51      inference('demod', [status(thm)], ['0', '6'])).
% 0.20/0.51  thf('8', plain,
% 0.20/0.51      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf(dt_k1_tops_1, axiom,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( ( l1_pre_topc @ A ) & 
% 0.20/0.51         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.20/0.51       ( m1_subset_1 @
% 0.20/0.51         ( k1_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.20/0.51  thf('9', plain,
% 0.20/0.51      (![X48 : $i, X49 : $i]:
% 0.20/0.51         (~ (l1_pre_topc @ X48)
% 0.20/0.51          | ~ (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ (u1_struct_0 @ X48)))
% 0.20/0.51          | (m1_subset_1 @ (k1_tops_1 @ X48 @ X49) @ 
% 0.20/0.51             (k1_zfmisc_1 @ (u1_struct_0 @ X48))))),
% 0.20/0.51      inference('cnf', [status(esa)], [dt_k1_tops_1])).
% 0.20/0.51  thf('10', plain,
% 0.20/0.51      (((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 0.20/0.51         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.51        | ~ (l1_pre_topc @ sk_A))),
% 0.20/0.51      inference('sup-', [status(thm)], ['8', '9'])).
% 0.20/0.51  thf('11', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('12', plain,
% 0.20/0.51      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 0.20/0.51        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.51      inference('demod', [status(thm)], ['10', '11'])).
% 0.20/0.51  thf(l78_tops_1, axiom,
% 0.20/0.51    (![A:$i]:
% 0.20/0.51     ( ( l1_pre_topc @ A ) =>
% 0.20/0.51       ( ![B:$i]:
% 0.20/0.51         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.51           ( ( k2_tops_1 @ A @ B ) =
% 0.20/0.51             ( k7_subset_1 @
% 0.20/0.51               ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 0.20/0.51               ( k1_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.20/0.51  thf('13', plain,
% 0.20/0.51      (![X50 : $i, X51 : $i]:
% 0.20/0.51         (~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ (u1_struct_0 @ X51)))
% 0.20/0.51          | ((k2_tops_1 @ X51 @ X50)
% 0.20/0.51              = (k7_subset_1 @ (u1_struct_0 @ X51) @ 
% 0.20/0.51                 (k2_pre_topc @ X51 @ X50) @ (k1_tops_1 @ X51 @ X50)))
% 0.20/0.51          | ~ (l1_pre_topc @ X51))),
% 0.20/0.51      inference('cnf', [status(esa)], [l78_tops_1])).
% 0.20/0.51  thf('14', plain,
% 0.20/0.51      ((~ (l1_pre_topc @ sk_A)
% 0.20/0.51        | ((k2_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))
% 0.20/0.51            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.51               (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)) @ 
% 0.20/0.51               (k1_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.20/0.51      inference('sup-', [status(thm)], ['12', '13'])).
% 0.20/0.51  thf('15', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('16', plain,
% 0.20/0.51      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf(t102_tops_1, axiom,
% 0.20/0.51    (![A:$i]:
% 0.20/0.51     ( ( l1_pre_topc @ A ) =>
% 0.20/0.51       ( ![B:$i]:
% 0.20/0.51         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.51           ( ( v5_tops_1 @ B @ A ) =>
% 0.20/0.51             ( ( k2_tops_1 @ A @ ( k1_tops_1 @ A @ B ) ) =
% 0.20/0.51               ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.20/0.51  thf('17', plain,
% 0.20/0.51      (![X52 : $i, X53 : $i]:
% 0.20/0.51         (~ (m1_subset_1 @ X52 @ (k1_zfmisc_1 @ (u1_struct_0 @ X53)))
% 0.20/0.51          | ((k2_tops_1 @ X53 @ (k1_tops_1 @ X53 @ X52))
% 0.20/0.51              = (k2_tops_1 @ X53 @ X52))
% 0.20/0.51          | ~ (v5_tops_1 @ X52 @ X53)
% 0.20/0.51          | ~ (l1_pre_topc @ X53))),
% 0.20/0.51      inference('cnf', [status(esa)], [t102_tops_1])).
% 0.20/0.51  thf('18', plain,
% 0.20/0.51      ((~ (l1_pre_topc @ sk_A)
% 0.20/0.51        | ~ (v5_tops_1 @ sk_B @ sk_A)
% 0.20/0.51        | ((k2_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))
% 0.20/0.51            = (k2_tops_1 @ sk_A @ sk_B)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['16', '17'])).
% 0.20/0.51  thf('19', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('20', plain, ((v5_tops_1 @ sk_B @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('21', plain,
% 0.20/0.51      (((k2_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))
% 0.20/0.51         = (k2_tops_1 @ sk_A @ sk_B))),
% 0.20/0.51      inference('demod', [status(thm)], ['18', '19', '20'])).
% 0.20/0.51  thf('22', plain,
% 0.20/0.51      (((sk_B) = (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))),
% 0.20/0.51      inference('demod', [status(thm)], ['3', '4', '5'])).
% 0.20/0.51  thf('23', plain,
% 0.20/0.51      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf(redefinition_k7_subset_1, axiom,
% 0.20/0.51    (![A:$i,B:$i,C:$i]:
% 0.20/0.51     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.51       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 0.20/0.51  thf('24', plain,
% 0.20/0.51      (![X41 : $i, X42 : $i, X43 : $i]:
% 0.20/0.51         (~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ X42))
% 0.20/0.51          | ((k7_subset_1 @ X42 @ X41 @ X43) = (k4_xboole_0 @ X41 @ X43)))),
% 0.20/0.51      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 0.20/0.51  thf('25', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.20/0.51           = (k4_xboole_0 @ sk_B @ X0))),
% 0.20/0.51      inference('sup-', [status(thm)], ['23', '24'])).
% 0.20/0.51  thf('26', plain,
% 0.20/0.51      (((k2_tops_1 @ sk_A @ sk_B)
% 0.20/0.51         = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))))),
% 0.20/0.51      inference('demod', [status(thm)], ['14', '15', '21', '22', '25'])).
% 0.20/0.51  thf(commutativity_k2_tarski, axiom,
% 0.20/0.51    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.20/0.51  thf('27', plain,
% 0.20/0.51      (![X10 : $i, X11 : $i]:
% 0.20/0.51         ((k2_tarski @ X11 @ X10) = (k2_tarski @ X10 @ X11))),
% 0.20/0.51      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.20/0.51  thf(l51_zfmisc_1, axiom,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.20/0.51  thf('28', plain,
% 0.20/0.51      (![X39 : $i, X40 : $i]:
% 0.20/0.51         ((k3_tarski @ (k2_tarski @ X39 @ X40)) = (k2_xboole_0 @ X39 @ X40))),
% 0.20/0.51      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.20/0.51  thf('29', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]:
% 0.20/0.51         ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 0.20/0.51      inference('sup+', [status(thm)], ['27', '28'])).
% 0.20/0.51  thf('30', plain,
% 0.20/0.51      (![X39 : $i, X40 : $i]:
% 0.20/0.51         ((k3_tarski @ (k2_tarski @ X39 @ X40)) = (k2_xboole_0 @ X39 @ X40))),
% 0.20/0.51      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.20/0.51  thf('31', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.20/0.51      inference('sup+', [status(thm)], ['29', '30'])).
% 0.20/0.51  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.20/0.51  thf('32', plain, (![X7 : $i]: (r1_tarski @ k1_xboole_0 @ X7)),
% 0.20/0.51      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.20/0.51  thf(t12_xboole_1, axiom,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.20/0.51  thf('33', plain,
% 0.20/0.51      (![X5 : $i, X6 : $i]:
% 0.20/0.51         (((k2_xboole_0 @ X6 @ X5) = (X5)) | ~ (r1_tarski @ X6 @ X5))),
% 0.20/0.51      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.20/0.51  thf('34', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.20/0.51      inference('sup-', [status(thm)], ['32', '33'])).
% 0.20/0.51  thf('35', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.20/0.51      inference('sup+', [status(thm)], ['31', '34'])).
% 0.20/0.51  thf(t7_xboole_1, axiom,
% 0.20/0.51    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.20/0.51  thf('36', plain,
% 0.20/0.51      (![X8 : $i, X9 : $i]: (r1_tarski @ X8 @ (k2_xboole_0 @ X8 @ X9))),
% 0.20/0.51      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.20/0.51  thf(t109_xboole_1, axiom,
% 0.20/0.51    (![A:$i,B:$i,C:$i]:
% 0.20/0.51     ( ( r1_tarski @ A @ B ) => ( r1_tarski @ ( k4_xboole_0 @ A @ C ) @ B ) ))).
% 0.20/0.51  thf('37', plain,
% 0.20/0.51      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.20/0.51         (~ (r1_tarski @ X2 @ X3) | (r1_tarski @ (k4_xboole_0 @ X2 @ X4) @ X3))),
% 0.20/0.51      inference('cnf', [status(esa)], [t109_xboole_1])).
% 0.20/0.51  thf('38', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.51         (r1_tarski @ (k4_xboole_0 @ X1 @ X2) @ (k2_xboole_0 @ X1 @ X0))),
% 0.20/0.51      inference('sup-', [status(thm)], ['36', '37'])).
% 0.20/0.51  thf('39', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]: (r1_tarski @ (k4_xboole_0 @ X0 @ X1) @ X0)),
% 0.20/0.51      inference('sup+', [status(thm)], ['35', '38'])).
% 0.20/0.51  thf('40', plain, ((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)),
% 0.20/0.51      inference('sup+', [status(thm)], ['26', '39'])).
% 0.20/0.51  thf('41', plain, ($false), inference('demod', [status(thm)], ['7', '40'])).
% 0.20/0.51  
% 0.20/0.51  % SZS output end Refutation
% 0.20/0.51  
% 0.20/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
