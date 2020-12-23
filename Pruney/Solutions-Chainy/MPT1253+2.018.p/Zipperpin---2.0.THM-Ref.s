%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.vOJaAedgb1

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:15 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 154 expanded)
%              Number of leaves         :   22 (  55 expanded)
%              Depth                    :   12
%              Number of atoms          :  566 (1700 expanded)
%              Number of equality atoms :   20 (  33 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(t69_tops_1,conjecture,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v4_pre_topc @ B @ A )
           => ( r1_tarski @ ( k2_tops_1 @ A @ B ) @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_pre_topc @ A )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( ( v4_pre_topc @ B @ A )
             => ( r1_tarski @ ( k2_tops_1 @ A @ B ) @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t69_tops_1])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('2',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( l1_pre_topc @ X13 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ( m1_subset_1 @ ( k2_tops_1 @ X13 @ X14 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_1])).

thf('3',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t41_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( r1_tarski @ ( k3_subset_1 @ A @ ( k4_subset_1 @ A @ B @ C ) ) @ ( k3_subset_1 @ A @ B ) ) ) ) )).

thf('7',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) )
      | ( r1_tarski @ ( k3_subset_1 @ X9 @ ( k4_subset_1 @ X9 @ X10 @ X8 ) ) @ ( k3_subset_1 @ X9 @ X10 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t41_subset_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_B ) ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    r1_tarski @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ) ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['5','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('12',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X3 ) )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X3 ) )
      | ( ( k4_subset_1 @ X3 @ X2 @ X4 )
        = ( k2_xboole_0 @ X2 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_1 @ sk_A @ sk_B ) @ X0 )
        = ( k2_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,
    ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
    = ( k2_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['10','13'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('16',plain,
    ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
    = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,(
    r1_tarski @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['9','16'])).

thf(t31_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ( r1_tarski @ B @ C )
          <=> ( r1_tarski @ ( k3_subset_1 @ A @ C ) @ ( k3_subset_1 @ A @ B ) ) ) ) ) )).

thf('18',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X6 ) )
      | ~ ( r1_tarski @ ( k3_subset_1 @ X6 @ X5 ) @ ( k3_subset_1 @ X6 @ X7 ) )
      | ( r1_tarski @ X7 @ X5 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t31_subset_1])).

thf('19',plain,
    ( ~ ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
    | ~ ( m1_subset_1 @ ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('21',plain,
    ( ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
    | ~ ( m1_subset_1 @ ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t65_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_pre_topc @ A @ B )
            = ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('23',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ( ( k2_pre_topc @ X16 @ X15 )
        = ( k4_subset_1 @ ( u1_struct_0 @ X16 ) @ X15 @ ( k2_tops_1 @ X16 @ X15 ) ) )
      | ~ ( l1_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[t65_tops_1])).

thf('24',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
      = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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

thf('27',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ~ ( v4_pre_topc @ X11 @ X12 )
      | ( ( k2_pre_topc @ X12 @ X11 )
        = X11 )
      | ~ ( l1_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('28',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
      = sk_B )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    v4_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = sk_B ),
    inference(demod,[status(thm)],['28','29','30'])).

thf('32',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('33',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X3 ) )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X3 ) )
      | ( ( k4_subset_1 @ X3 @ X2 @ X4 )
        = ( k2_xboole_0 @ X2 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
        = ( k2_xboole_0 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,
    ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['32','35'])).

thf('37',plain,
    ( sk_B
    = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['24','25','31','36'])).

thf('38',plain,
    ( sk_B
    = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['24','25','31','36'])).

thf('39',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ),
    inference(demod,[status(thm)],['21','37','38','39'])).

thf('41',plain,(
    $false ),
    inference(demod,[status(thm)],['0','40'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.vOJaAedgb1
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:33:00 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.52  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.52  % Solved by: fo/fo7.sh
% 0.20/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.52  % done 70 iterations in 0.063s
% 0.20/0.52  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.52  % SZS output start Refutation
% 0.20/0.52  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 0.20/0.52  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 0.20/0.52  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.20/0.52  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.20/0.52  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.52  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.52  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.52  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.52  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.20/0.52  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.20/0.52  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.52  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.20/0.52  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.20/0.52  thf(t69_tops_1, conjecture,
% 0.20/0.52    (![A:$i]:
% 0.20/0.52     ( ( l1_pre_topc @ A ) =>
% 0.20/0.52       ( ![B:$i]:
% 0.20/0.52         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.52           ( ( v4_pre_topc @ B @ A ) =>
% 0.20/0.52             ( r1_tarski @ ( k2_tops_1 @ A @ B ) @ B ) ) ) ) ))).
% 0.20/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.52    (~( ![A:$i]:
% 0.20/0.52        ( ( l1_pre_topc @ A ) =>
% 0.20/0.52          ( ![B:$i]:
% 0.20/0.52            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.52              ( ( v4_pre_topc @ B @ A ) =>
% 0.20/0.52                ( r1_tarski @ ( k2_tops_1 @ A @ B ) @ B ) ) ) ) ) )),
% 0.20/0.52    inference('cnf.neg', [status(esa)], [t69_tops_1])).
% 0.20/0.52  thf('0', plain, (~ (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('1', plain,
% 0.20/0.52      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf(dt_k2_tops_1, axiom,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( ( l1_pre_topc @ A ) & 
% 0.20/0.52         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.20/0.52       ( m1_subset_1 @
% 0.20/0.52         ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.20/0.52  thf('2', plain,
% 0.20/0.52      (![X13 : $i, X14 : $i]:
% 0.20/0.52         (~ (l1_pre_topc @ X13)
% 0.20/0.52          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.20/0.52          | (m1_subset_1 @ (k2_tops_1 @ X13 @ X14) @ 
% 0.20/0.52             (k1_zfmisc_1 @ (u1_struct_0 @ X13))))),
% 0.20/0.52      inference('cnf', [status(esa)], [dt_k2_tops_1])).
% 0.20/0.52  thf('3', plain,
% 0.20/0.52      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.20/0.52         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.52        | ~ (l1_pre_topc @ sk_A))),
% 0.20/0.52      inference('sup-', [status(thm)], ['1', '2'])).
% 0.20/0.52  thf('4', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('5', plain,
% 0.20/0.52      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.20/0.52        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.52      inference('demod', [status(thm)], ['3', '4'])).
% 0.20/0.52  thf('6', plain,
% 0.20/0.52      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf(t41_subset_1, axiom,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.52       ( ![C:$i]:
% 0.20/0.52         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.52           ( r1_tarski @
% 0.20/0.52             ( k3_subset_1 @ A @ ( k4_subset_1 @ A @ B @ C ) ) @ 
% 0.20/0.52             ( k3_subset_1 @ A @ B ) ) ) ) ))).
% 0.20/0.52  thf('7', plain,
% 0.20/0.52      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.20/0.52         (~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9))
% 0.20/0.52          | (r1_tarski @ (k3_subset_1 @ X9 @ (k4_subset_1 @ X9 @ X10 @ X8)) @ 
% 0.20/0.52             (k3_subset_1 @ X9 @ X10))
% 0.20/0.52          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X9)))),
% 0.20/0.52      inference('cnf', [status(esa)], [t41_subset_1])).
% 0.20/0.52  thf('8', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.52          | (r1_tarski @ 
% 0.20/0.52             (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.52              (k4_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_B)) @ 
% 0.20/0.52             (k3_subset_1 @ (u1_struct_0 @ sk_A) @ X0)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['6', '7'])).
% 0.20/0.52  thf('9', plain,
% 0.20/0.52      ((r1_tarski @ 
% 0.20/0.52        (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.52         (k4_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)) @ 
% 0.20/0.52        (k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['5', '8'])).
% 0.20/0.52  thf('10', plain,
% 0.20/0.52      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('11', plain,
% 0.20/0.52      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.20/0.52        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.52      inference('demod', [status(thm)], ['3', '4'])).
% 0.20/0.52  thf(redefinition_k4_subset_1, axiom,
% 0.20/0.52    (![A:$i,B:$i,C:$i]:
% 0.20/0.52     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 0.20/0.52         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.20/0.52       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 0.20/0.52  thf('12', plain,
% 0.20/0.52      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.20/0.52         (~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X3))
% 0.20/0.52          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X3))
% 0.20/0.52          | ((k4_subset_1 @ X3 @ X2 @ X4) = (k2_xboole_0 @ X2 @ X4)))),
% 0.20/0.52      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 0.20/0.52  thf('13', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_tops_1 @ sk_A @ sk_B) @ X0)
% 0.20/0.52            = (k2_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ X0))
% 0.20/0.52          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.52      inference('sup-', [status(thm)], ['11', '12'])).
% 0.20/0.52  thf('14', plain,
% 0.20/0.52      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)
% 0.20/0.52         = (k2_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))),
% 0.20/0.52      inference('sup-', [status(thm)], ['10', '13'])).
% 0.20/0.52  thf(commutativity_k2_xboole_0, axiom,
% 0.20/0.52    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.20/0.52  thf('15', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.20/0.52      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.20/0.52  thf('16', plain,
% 0.20/0.52      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)
% 0.20/0.52         = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.20/0.52      inference('demod', [status(thm)], ['14', '15'])).
% 0.20/0.52  thf('17', plain,
% 0.20/0.52      ((r1_tarski @ 
% 0.20/0.52        (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.52         (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))) @ 
% 0.20/0.52        (k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.20/0.52      inference('demod', [status(thm)], ['9', '16'])).
% 0.20/0.52  thf(t31_subset_1, axiom,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.52       ( ![C:$i]:
% 0.20/0.52         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.52           ( ( r1_tarski @ B @ C ) <=>
% 0.20/0.52             ( r1_tarski @ ( k3_subset_1 @ A @ C ) @ ( k3_subset_1 @ A @ B ) ) ) ) ) ))).
% 0.20/0.52  thf('18', plain,
% 0.20/0.52      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.20/0.52         (~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6))
% 0.20/0.52          | ~ (r1_tarski @ (k3_subset_1 @ X6 @ X5) @ (k3_subset_1 @ X6 @ X7))
% 0.20/0.52          | (r1_tarski @ X7 @ X5)
% 0.20/0.52          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X6)))),
% 0.20/0.52      inference('cnf', [status(esa)], [t31_subset_1])).
% 0.20/0.52  thf('19', plain,
% 0.20/0.52      ((~ (m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.20/0.52           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.52        | (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.20/0.52           (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))
% 0.20/0.52        | ~ (m1_subset_1 @ (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)) @ 
% 0.20/0.52             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.52      inference('sup-', [status(thm)], ['17', '18'])).
% 0.20/0.52  thf('20', plain,
% 0.20/0.52      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.20/0.52        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.52      inference('demod', [status(thm)], ['3', '4'])).
% 0.20/0.52  thf('21', plain,
% 0.20/0.52      (((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.20/0.52         (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))
% 0.20/0.52        | ~ (m1_subset_1 @ (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)) @ 
% 0.20/0.52             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.52      inference('demod', [status(thm)], ['19', '20'])).
% 0.20/0.52  thf('22', plain,
% 0.20/0.52      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf(t65_tops_1, axiom,
% 0.20/0.52    (![A:$i]:
% 0.20/0.52     ( ( l1_pre_topc @ A ) =>
% 0.20/0.52       ( ![B:$i]:
% 0.20/0.52         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.52           ( ( k2_pre_topc @ A @ B ) =
% 0.20/0.52             ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.20/0.52  thf('23', plain,
% 0.20/0.52      (![X15 : $i, X16 : $i]:
% 0.20/0.52         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.20/0.52          | ((k2_pre_topc @ X16 @ X15)
% 0.20/0.52              = (k4_subset_1 @ (u1_struct_0 @ X16) @ X15 @ 
% 0.20/0.52                 (k2_tops_1 @ X16 @ X15)))
% 0.20/0.52          | ~ (l1_pre_topc @ X16))),
% 0.20/0.52      inference('cnf', [status(esa)], [t65_tops_1])).
% 0.20/0.52  thf('24', plain,
% 0.20/0.52      ((~ (l1_pre_topc @ sk_A)
% 0.20/0.52        | ((k2_pre_topc @ sk_A @ sk_B)
% 0.20/0.52            = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.20/0.52               (k2_tops_1 @ sk_A @ sk_B))))),
% 0.20/0.52      inference('sup-', [status(thm)], ['22', '23'])).
% 0.20/0.52  thf('25', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('26', plain,
% 0.20/0.52      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf(t52_pre_topc, axiom,
% 0.20/0.52    (![A:$i]:
% 0.20/0.52     ( ( l1_pre_topc @ A ) =>
% 0.20/0.52       ( ![B:$i]:
% 0.20/0.52         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.52           ( ( ( v4_pre_topc @ B @ A ) => ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) & 
% 0.20/0.52             ( ( ( v2_pre_topc @ A ) & ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) =>
% 0.20/0.52               ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 0.20/0.52  thf('27', plain,
% 0.20/0.52      (![X11 : $i, X12 : $i]:
% 0.20/0.52         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.20/0.52          | ~ (v4_pre_topc @ X11 @ X12)
% 0.20/0.52          | ((k2_pre_topc @ X12 @ X11) = (X11))
% 0.20/0.52          | ~ (l1_pre_topc @ X12))),
% 0.20/0.52      inference('cnf', [status(esa)], [t52_pre_topc])).
% 0.20/0.52  thf('28', plain,
% 0.20/0.52      ((~ (l1_pre_topc @ sk_A)
% 0.20/0.52        | ((k2_pre_topc @ sk_A @ sk_B) = (sk_B))
% 0.20/0.52        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.20/0.52      inference('sup-', [status(thm)], ['26', '27'])).
% 0.20/0.52  thf('29', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('30', plain, ((v4_pre_topc @ sk_B @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('31', plain, (((k2_pre_topc @ sk_A @ sk_B) = (sk_B))),
% 0.20/0.52      inference('demod', [status(thm)], ['28', '29', '30'])).
% 0.20/0.52  thf('32', plain,
% 0.20/0.52      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.20/0.52        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.52      inference('demod', [status(thm)], ['3', '4'])).
% 0.20/0.52  thf('33', plain,
% 0.20/0.52      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('34', plain,
% 0.20/0.52      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.20/0.52         (~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X3))
% 0.20/0.52          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X3))
% 0.20/0.52          | ((k4_subset_1 @ X3 @ X2 @ X4) = (k2_xboole_0 @ X2 @ X4)))),
% 0.20/0.52      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 0.20/0.52  thf('35', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.20/0.52            = (k2_xboole_0 @ sk_B @ X0))
% 0.20/0.52          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.52      inference('sup-', [status(thm)], ['33', '34'])).
% 0.20/0.52  thf('36', plain,
% 0.20/0.52      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.20/0.52         = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['32', '35'])).
% 0.20/0.52  thf('37', plain,
% 0.20/0.52      (((sk_B) = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.20/0.52      inference('demod', [status(thm)], ['24', '25', '31', '36'])).
% 0.20/0.52  thf('38', plain,
% 0.20/0.52      (((sk_B) = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.20/0.52      inference('demod', [status(thm)], ['24', '25', '31', '36'])).
% 0.20/0.52  thf('39', plain,
% 0.20/0.52      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('40', plain, ((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)),
% 0.20/0.52      inference('demod', [status(thm)], ['21', '37', '38', '39'])).
% 0.20/0.52  thf('41', plain, ($false), inference('demod', [status(thm)], ['0', '40'])).
% 0.20/0.52  
% 0.20/0.52  % SZS output end Refutation
% 0.20/0.52  
% 0.20/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
