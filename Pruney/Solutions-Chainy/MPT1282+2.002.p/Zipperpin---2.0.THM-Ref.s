%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.MvRb8Pts4u

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:04:51 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 202 expanded)
%              Number of leaves         :   20 (  66 expanded)
%              Depth                    :   12
%              Number of atoms          :  667 (3521 expanded)
%              Number of equality atoms :   38 ( 195 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v6_tops_1_type,type,(
    v6_tops_1: $i > $i > $o )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(t104_tops_1,conjecture,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v6_tops_1 @ B @ A )
           => ( ( ( k2_tops_1 @ A @ B )
                = ( k2_tops_1 @ A @ ( k2_pre_topc @ A @ B ) ) )
              & ( ( k2_tops_1 @ A @ ( k2_pre_topc @ A @ B ) )
                = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ B ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_pre_topc @ A )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( ( v6_tops_1 @ B @ A )
             => ( ( ( k2_tops_1 @ A @ B )
                  = ( k2_tops_1 @ A @ ( k2_pre_topc @ A @ B ) ) )
                & ( ( k2_tops_1 @ A @ ( k2_pre_topc @ A @ B ) )
                  = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ B ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t104_tops_1])).

thf('0',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('1',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( l1_pre_topc @ X3 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X3 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X3 @ X4 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X3 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('2',plain,
    ( ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(l78_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_tops_1 @ A @ B )
            = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ ( k1_tops_1 @ A @ B ) ) ) ) ) )).

thf('5',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ( ( k2_tops_1 @ X10 @ X9 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X10 ) @ ( k2_pre_topc @ X10 @ X9 ) @ ( k1_tops_1 @ X10 @ X9 ) ) )
      | ~ ( l1_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[l78_tops_1])).

thf('6',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t72_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_tarski @ ( k2_tops_1 @ A @ ( k2_pre_topc @ A @ B ) ) @ ( k2_tops_1 @ A @ B ) ) ) ) )).

thf('9',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ( r1_tarski @ ( k2_tops_1 @ X14 @ ( k2_pre_topc @ X14 @ X13 ) ) @ ( k2_tops_1 @ X14 @ X13 ) )
      | ~ ( l1_pre_topc @ X14 ) ) ),
    inference(cnf,[status(esa)],[t72_tops_1])).

thf('10',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ ( k2_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    r1_tarski @ ( k2_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ ( k2_tops_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['10','11'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('13',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('14',plain,
    ( ~ ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) )
    | ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k2_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(t71_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_tarski @ ( k2_tops_1 @ A @ ( k1_tops_1 @ A @ B ) ) @ ( k2_tops_1 @ A @ B ) ) ) ) )).

thf('16',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ( r1_tarski @ ( k2_tops_1 @ X12 @ ( k1_tops_1 @ X12 @ X11 ) ) @ ( k2_tops_1 @ X12 @ X11 ) )
      | ~ ( l1_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[t71_tops_1])).

thf('17',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ ( k2_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) @ ( k2_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d8_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v6_tops_1 @ B @ A )
          <=> ( B
              = ( k1_tops_1 @ A @ ( k2_pre_topc @ A @ B ) ) ) ) ) ) )).

thf('20',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ~ ( v6_tops_1 @ X7 @ X8 )
      | ( X7
        = ( k1_tops_1 @ X8 @ ( k2_pre_topc @ X8 @ X7 ) ) )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[d8_tops_1])).

thf('21',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( sk_B
      = ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) )
    | ~ ( v6_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    v6_tops_1 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( sk_B
    = ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['21','22','23'])).

thf('25',plain,(
    r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['17','18','24'])).

thf('26',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k2_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['14','25'])).

thf('27',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(projectivity_k2_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( ( k2_pre_topc @ A @ ( k2_pre_topc @ A @ B ) )
        = ( k2_pre_topc @ A @ B ) ) ) )).

thf('28',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( l1_pre_topc @ X5 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) )
      | ( ( k2_pre_topc @ X5 @ ( k2_pre_topc @ X5 @ X6 ) )
        = ( k2_pre_topc @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[projectivity_k2_pre_topc])).

thf('29',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) )
      = ( k2_pre_topc @ sk_A @ sk_B ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( k2_pre_topc @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) )
    = ( k2_pre_topc @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,
    ( sk_B
    = ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['21','22','23'])).

thf('33',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ),
    inference(demod,[status(thm)],['6','7','26','31','32'])).

thf('34',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k2_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) )
    | ( ( k2_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( ( k2_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference(split,[status(esa)],['34'])).

thf('36',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k2_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['14','25'])).

thf('37',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k2_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['14','25'])).

thf('39',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k2_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k2_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['34'])).

thf('40',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k2_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k2_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,
    ( ( ( k2_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
    | ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k2_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['34'])).

thf('43',plain,(
    ( k2_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) )
 != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['41','42'])).

thf('44',plain,(
    ( k2_tops_1 @ sk_A @ sk_B )
 != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['37','43'])).

thf('45',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['33','44'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.MvRb8Pts4u
% 0.14/0.36  % Computer   : n015.cluster.edu
% 0.14/0.36  % Model      : x86_64 x86_64
% 0.14/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.36  % Memory     : 8042.1875MB
% 0.14/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % DateTime   : Tue Dec  1 16:53:23 EST 2020
% 0.14/0.37  % CPUTime    : 
% 0.14/0.37  % Running portfolio for 600 s
% 0.14/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.37  % Number of cores: 8
% 0.14/0.37  % Python version: Python 3.6.8
% 0.14/0.37  % Running in FO mode
% 0.23/0.50  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.23/0.50  % Solved by: fo/fo7.sh
% 0.23/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.23/0.50  % done 52 iterations in 0.028s
% 0.23/0.50  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.23/0.50  % SZS output start Refutation
% 0.23/0.50  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 0.23/0.50  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.23/0.50  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.23/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.23/0.50  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 0.23/0.50  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.23/0.50  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.23/0.50  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.23/0.50  thf(sk_B_type, type, sk_B: $i).
% 0.23/0.50  thf(v6_tops_1_type, type, v6_tops_1: $i > $i > $o).
% 0.23/0.50  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.23/0.50  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.23/0.50  thf(t104_tops_1, conjecture,
% 0.23/0.50    (![A:$i]:
% 0.23/0.50     ( ( l1_pre_topc @ A ) =>
% 0.23/0.50       ( ![B:$i]:
% 0.23/0.50         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.23/0.50           ( ( v6_tops_1 @ B @ A ) =>
% 0.23/0.50             ( ( ( k2_tops_1 @ A @ B ) =
% 0.23/0.50                 ( k2_tops_1 @ A @ ( k2_pre_topc @ A @ B ) ) ) & 
% 0.23/0.50               ( ( k2_tops_1 @ A @ ( k2_pre_topc @ A @ B ) ) =
% 0.23/0.50                 ( k7_subset_1 @
% 0.23/0.50                   ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ B ) ) ) ) ) ) ))).
% 0.23/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.23/0.50    (~( ![A:$i]:
% 0.23/0.50        ( ( l1_pre_topc @ A ) =>
% 0.23/0.50          ( ![B:$i]:
% 0.23/0.50            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.23/0.50              ( ( v6_tops_1 @ B @ A ) =>
% 0.23/0.50                ( ( ( k2_tops_1 @ A @ B ) =
% 0.23/0.50                    ( k2_tops_1 @ A @ ( k2_pre_topc @ A @ B ) ) ) & 
% 0.23/0.50                  ( ( k2_tops_1 @ A @ ( k2_pre_topc @ A @ B ) ) =
% 0.23/0.50                    ( k7_subset_1 @
% 0.23/0.50                      ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ B ) ) ) ) ) ) ) )),
% 0.23/0.50    inference('cnf.neg', [status(esa)], [t104_tops_1])).
% 0.23/0.50  thf('0', plain,
% 0.23/0.50      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.23/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.50  thf(dt_k2_pre_topc, axiom,
% 0.23/0.50    (![A:$i,B:$i]:
% 0.23/0.50     ( ( ( l1_pre_topc @ A ) & 
% 0.23/0.50         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.23/0.50       ( m1_subset_1 @
% 0.23/0.50         ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.23/0.50  thf('1', plain,
% 0.23/0.50      (![X3 : $i, X4 : $i]:
% 0.23/0.50         (~ (l1_pre_topc @ X3)
% 0.23/0.50          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (u1_struct_0 @ X3)))
% 0.23/0.50          | (m1_subset_1 @ (k2_pre_topc @ X3 @ X4) @ 
% 0.23/0.50             (k1_zfmisc_1 @ (u1_struct_0 @ X3))))),
% 0.23/0.50      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 0.23/0.50  thf('2', plain,
% 0.23/0.50      (((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.23/0.50         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.23/0.50        | ~ (l1_pre_topc @ sk_A))),
% 0.23/0.50      inference('sup-', [status(thm)], ['0', '1'])).
% 0.23/0.50  thf('3', plain, ((l1_pre_topc @ sk_A)),
% 0.23/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.50  thf('4', plain,
% 0.23/0.50      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.23/0.50        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.23/0.50      inference('demod', [status(thm)], ['2', '3'])).
% 0.23/0.50  thf(l78_tops_1, axiom,
% 0.23/0.50    (![A:$i]:
% 0.23/0.50     ( ( l1_pre_topc @ A ) =>
% 0.23/0.50       ( ![B:$i]:
% 0.23/0.50         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.23/0.50           ( ( k2_tops_1 @ A @ B ) =
% 0.23/0.50             ( k7_subset_1 @
% 0.23/0.50               ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 0.23/0.50               ( k1_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.23/0.50  thf('5', plain,
% 0.23/0.50      (![X9 : $i, X10 : $i]:
% 0.23/0.50         (~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 0.23/0.50          | ((k2_tops_1 @ X10 @ X9)
% 0.23/0.50              = (k7_subset_1 @ (u1_struct_0 @ X10) @ 
% 0.23/0.50                 (k2_pre_topc @ X10 @ X9) @ (k1_tops_1 @ X10 @ X9)))
% 0.23/0.50          | ~ (l1_pre_topc @ X10))),
% 0.23/0.50      inference('cnf', [status(esa)], [l78_tops_1])).
% 0.23/0.50  thf('6', plain,
% 0.23/0.50      ((~ (l1_pre_topc @ sk_A)
% 0.23/0.50        | ((k2_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B))
% 0.23/0.50            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.23/0.50               (k2_pre_topc @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)) @ 
% 0.23/0.50               (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)))))),
% 0.23/0.50      inference('sup-', [status(thm)], ['4', '5'])).
% 0.23/0.50  thf('7', plain, ((l1_pre_topc @ sk_A)),
% 0.23/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.50  thf('8', plain,
% 0.23/0.50      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.23/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.50  thf(t72_tops_1, axiom,
% 0.23/0.50    (![A:$i]:
% 0.23/0.50     ( ( l1_pre_topc @ A ) =>
% 0.23/0.50       ( ![B:$i]:
% 0.23/0.50         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.23/0.50           ( r1_tarski @
% 0.23/0.50             ( k2_tops_1 @ A @ ( k2_pre_topc @ A @ B ) ) @ 
% 0.23/0.50             ( k2_tops_1 @ A @ B ) ) ) ) ))).
% 0.23/0.50  thf('9', plain,
% 0.23/0.50      (![X13 : $i, X14 : $i]:
% 0.23/0.50         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.23/0.50          | (r1_tarski @ (k2_tops_1 @ X14 @ (k2_pre_topc @ X14 @ X13)) @ 
% 0.23/0.50             (k2_tops_1 @ X14 @ X13))
% 0.23/0.50          | ~ (l1_pre_topc @ X14))),
% 0.23/0.50      inference('cnf', [status(esa)], [t72_tops_1])).
% 0.23/0.50  thf('10', plain,
% 0.23/0.50      ((~ (l1_pre_topc @ sk_A)
% 0.23/0.50        | (r1_tarski @ (k2_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)) @ 
% 0.23/0.50           (k2_tops_1 @ sk_A @ sk_B)))),
% 0.23/0.50      inference('sup-', [status(thm)], ['8', '9'])).
% 0.23/0.50  thf('11', plain, ((l1_pre_topc @ sk_A)),
% 0.23/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.50  thf('12', plain,
% 0.23/0.50      ((r1_tarski @ (k2_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)) @ 
% 0.23/0.50        (k2_tops_1 @ sk_A @ sk_B))),
% 0.23/0.50      inference('demod', [status(thm)], ['10', '11'])).
% 0.23/0.50  thf(d10_xboole_0, axiom,
% 0.23/0.50    (![A:$i,B:$i]:
% 0.23/0.50     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.23/0.50  thf('13', plain,
% 0.23/0.50      (![X0 : $i, X2 : $i]:
% 0.23/0.50         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.23/0.50      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.23/0.50  thf('14', plain,
% 0.23/0.50      ((~ (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.23/0.50           (k2_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)))
% 0.23/0.50        | ((k2_tops_1 @ sk_A @ sk_B)
% 0.23/0.50            = (k2_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B))))),
% 0.23/0.50      inference('sup-', [status(thm)], ['12', '13'])).
% 0.23/0.50  thf('15', plain,
% 0.23/0.50      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.23/0.50        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.23/0.50      inference('demod', [status(thm)], ['2', '3'])).
% 0.23/0.50  thf(t71_tops_1, axiom,
% 0.23/0.50    (![A:$i]:
% 0.23/0.50     ( ( l1_pre_topc @ A ) =>
% 0.23/0.50       ( ![B:$i]:
% 0.23/0.50         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.23/0.50           ( r1_tarski @
% 0.23/0.50             ( k2_tops_1 @ A @ ( k1_tops_1 @ A @ B ) ) @ ( k2_tops_1 @ A @ B ) ) ) ) ))).
% 0.23/0.50  thf('16', plain,
% 0.23/0.50      (![X11 : $i, X12 : $i]:
% 0.23/0.50         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.23/0.50          | (r1_tarski @ (k2_tops_1 @ X12 @ (k1_tops_1 @ X12 @ X11)) @ 
% 0.23/0.50             (k2_tops_1 @ X12 @ X11))
% 0.23/0.50          | ~ (l1_pre_topc @ X12))),
% 0.23/0.50      inference('cnf', [status(esa)], [t71_tops_1])).
% 0.23/0.50  thf('17', plain,
% 0.23/0.50      ((~ (l1_pre_topc @ sk_A)
% 0.23/0.50        | (r1_tarski @ 
% 0.23/0.50           (k2_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B))) @ 
% 0.23/0.50           (k2_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B))))),
% 0.23/0.50      inference('sup-', [status(thm)], ['15', '16'])).
% 0.23/0.50  thf('18', plain, ((l1_pre_topc @ sk_A)),
% 0.23/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.50  thf('19', plain,
% 0.23/0.50      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.23/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.50  thf(d8_tops_1, axiom,
% 0.23/0.50    (![A:$i]:
% 0.23/0.50     ( ( l1_pre_topc @ A ) =>
% 0.23/0.50       ( ![B:$i]:
% 0.23/0.50         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.23/0.50           ( ( v6_tops_1 @ B @ A ) <=>
% 0.23/0.50             ( ( B ) = ( k1_tops_1 @ A @ ( k2_pre_topc @ A @ B ) ) ) ) ) ) ))).
% 0.23/0.50  thf('20', plain,
% 0.23/0.50      (![X7 : $i, X8 : $i]:
% 0.23/0.50         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 0.23/0.50          | ~ (v6_tops_1 @ X7 @ X8)
% 0.23/0.50          | ((X7) = (k1_tops_1 @ X8 @ (k2_pre_topc @ X8 @ X7)))
% 0.23/0.50          | ~ (l1_pre_topc @ X8))),
% 0.23/0.50      inference('cnf', [status(esa)], [d8_tops_1])).
% 0.23/0.50  thf('21', plain,
% 0.23/0.50      ((~ (l1_pre_topc @ sk_A)
% 0.23/0.50        | ((sk_B) = (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)))
% 0.23/0.50        | ~ (v6_tops_1 @ sk_B @ sk_A))),
% 0.23/0.50      inference('sup-', [status(thm)], ['19', '20'])).
% 0.23/0.50  thf('22', plain, ((l1_pre_topc @ sk_A)),
% 0.23/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.50  thf('23', plain, ((v6_tops_1 @ sk_B @ sk_A)),
% 0.23/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.50  thf('24', plain,
% 0.23/0.50      (((sk_B) = (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)))),
% 0.23/0.50      inference('demod', [status(thm)], ['21', '22', '23'])).
% 0.23/0.50  thf('25', plain,
% 0.23/0.50      ((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.23/0.50        (k2_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)))),
% 0.23/0.50      inference('demod', [status(thm)], ['17', '18', '24'])).
% 0.23/0.50  thf('26', plain,
% 0.23/0.50      (((k2_tops_1 @ sk_A @ sk_B)
% 0.23/0.50         = (k2_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)))),
% 0.23/0.50      inference('demod', [status(thm)], ['14', '25'])).
% 0.23/0.50  thf('27', plain,
% 0.23/0.50      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.23/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.50  thf(projectivity_k2_pre_topc, axiom,
% 0.23/0.50    (![A:$i,B:$i]:
% 0.23/0.50     ( ( ( l1_pre_topc @ A ) & 
% 0.23/0.50         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.23/0.50       ( ( k2_pre_topc @ A @ ( k2_pre_topc @ A @ B ) ) =
% 0.23/0.50         ( k2_pre_topc @ A @ B ) ) ))).
% 0.23/0.50  thf('28', plain,
% 0.23/0.50      (![X5 : $i, X6 : $i]:
% 0.23/0.50         (~ (l1_pre_topc @ X5)
% 0.23/0.50          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (u1_struct_0 @ X5)))
% 0.23/0.50          | ((k2_pre_topc @ X5 @ (k2_pre_topc @ X5 @ X6))
% 0.23/0.50              = (k2_pre_topc @ X5 @ X6)))),
% 0.23/0.50      inference('cnf', [status(esa)], [projectivity_k2_pre_topc])).
% 0.23/0.50  thf('29', plain,
% 0.23/0.50      ((((k2_pre_topc @ sk_A @ (k2_pre_topc @ sk_A @ sk_B))
% 0.23/0.50          = (k2_pre_topc @ sk_A @ sk_B))
% 0.23/0.50        | ~ (l1_pre_topc @ sk_A))),
% 0.23/0.50      inference('sup-', [status(thm)], ['27', '28'])).
% 0.23/0.50  thf('30', plain, ((l1_pre_topc @ sk_A)),
% 0.23/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.50  thf('31', plain,
% 0.23/0.50      (((k2_pre_topc @ sk_A @ (k2_pre_topc @ sk_A @ sk_B))
% 0.23/0.50         = (k2_pre_topc @ sk_A @ sk_B))),
% 0.23/0.50      inference('demod', [status(thm)], ['29', '30'])).
% 0.23/0.50  thf('32', plain,
% 0.23/0.50      (((sk_B) = (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)))),
% 0.23/0.50      inference('demod', [status(thm)], ['21', '22', '23'])).
% 0.23/0.50  thf('33', plain,
% 0.23/0.50      (((k2_tops_1 @ sk_A @ sk_B)
% 0.23/0.50         = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.23/0.50            sk_B))),
% 0.23/0.50      inference('demod', [status(thm)], ['6', '7', '26', '31', '32'])).
% 0.23/0.50  thf('34', plain,
% 0.23/0.50      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.23/0.50          != (k2_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)))
% 0.23/0.50        | ((k2_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B))
% 0.23/0.50            != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.23/0.50                (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))),
% 0.23/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.50  thf('35', plain,
% 0.23/0.50      ((((k2_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B))
% 0.23/0.50          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.23/0.50              (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))
% 0.23/0.50         <= (~
% 0.23/0.50             (((k2_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B))
% 0.23/0.50                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.23/0.50                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 0.23/0.50      inference('split', [status(esa)], ['34'])).
% 0.23/0.50  thf('36', plain,
% 0.23/0.50      (((k2_tops_1 @ sk_A @ sk_B)
% 0.23/0.50         = (k2_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)))),
% 0.23/0.50      inference('demod', [status(thm)], ['14', '25'])).
% 0.23/0.50  thf('37', plain,
% 0.23/0.50      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.23/0.50          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.23/0.50              (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))
% 0.23/0.50         <= (~
% 0.23/0.50             (((k2_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B))
% 0.23/0.50                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.23/0.50                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 0.23/0.50      inference('demod', [status(thm)], ['35', '36'])).
% 0.23/0.50  thf('38', plain,
% 0.23/0.50      (((k2_tops_1 @ sk_A @ sk_B)
% 0.23/0.50         = (k2_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)))),
% 0.23/0.50      inference('demod', [status(thm)], ['14', '25'])).
% 0.23/0.50  thf('39', plain,
% 0.23/0.50      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.23/0.50          != (k2_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B))))
% 0.23/0.50         <= (~
% 0.23/0.50             (((k2_tops_1 @ sk_A @ sk_B)
% 0.23/0.50                = (k2_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)))))),
% 0.23/0.50      inference('split', [status(esa)], ['34'])).
% 0.23/0.50  thf('40', plain,
% 0.23/0.50      ((((k2_tops_1 @ sk_A @ sk_B) != (k2_tops_1 @ sk_A @ sk_B)))
% 0.23/0.50         <= (~
% 0.23/0.50             (((k2_tops_1 @ sk_A @ sk_B)
% 0.23/0.50                = (k2_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)))))),
% 0.23/0.50      inference('sup-', [status(thm)], ['38', '39'])).
% 0.23/0.50  thf('41', plain,
% 0.23/0.50      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.23/0.50          = (k2_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B))))),
% 0.23/0.50      inference('simplify', [status(thm)], ['40'])).
% 0.23/0.50  thf('42', plain,
% 0.23/0.50      (~
% 0.23/0.50       (((k2_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B))
% 0.23/0.50          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.23/0.50             (k2_pre_topc @ sk_A @ sk_B) @ sk_B))) | 
% 0.23/0.50       ~
% 0.23/0.50       (((k2_tops_1 @ sk_A @ sk_B)
% 0.23/0.50          = (k2_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B))))),
% 0.23/0.50      inference('split', [status(esa)], ['34'])).
% 0.23/0.50  thf('43', plain,
% 0.23/0.50      (~
% 0.23/0.50       (((k2_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B))
% 0.23/0.50          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.23/0.50             (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))),
% 0.23/0.50      inference('sat_resolution*', [status(thm)], ['41', '42'])).
% 0.23/0.50  thf('44', plain,
% 0.23/0.50      (((k2_tops_1 @ sk_A @ sk_B)
% 0.23/0.50         != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.23/0.50             (k2_pre_topc @ sk_A @ sk_B) @ sk_B))),
% 0.23/0.50      inference('simpl_trail', [status(thm)], ['37', '43'])).
% 0.23/0.50  thf('45', plain, ($false),
% 0.23/0.50      inference('simplify_reflect-', [status(thm)], ['33', '44'])).
% 0.23/0.50  
% 0.23/0.50  % SZS output end Refutation
% 0.23/0.50  
% 0.23/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
