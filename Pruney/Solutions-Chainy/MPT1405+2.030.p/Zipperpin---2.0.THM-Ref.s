%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.MHAg2ctPhy

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:07:18 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   66 (  97 expanded)
%              Number of leaves         :   24 (  39 expanded)
%              Depth                    :   12
%              Number of atoms          :  493 ( 905 expanded)
%              Number of equality atoms :    6 (   6 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(m2_connsp_2_type,type,(
    m2_connsp_2: $i > $i > $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(dt_k2_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( m1_subset_1 @ ( k2_struct_0 @ A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('0',plain,(
    ! [X8: $i] :
      ( ( m1_subset_1 @ ( k2_struct_0 @ X8 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ~ ( l1_struct_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_struct_0])).

thf(t35_connsp_2,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( m2_connsp_2 @ ( k2_struct_0 @ A ) @ A @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( m2_connsp_2 @ ( k2_struct_0 @ A ) @ A @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t35_connsp_2])).

thf('1',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('4',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t41_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( r1_tarski @ ( k3_subset_1 @ A @ ( k4_subset_1 @ A @ B @ C ) ) @ ( k3_subset_1 @ A @ B ) ) ) ) )).

thf('5',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X6 ) )
      | ( r1_tarski @ ( k3_subset_1 @ X6 @ ( k4_subset_1 @ X6 @ X7 @ X5 ) ) @ ( k3_subset_1 @ X6 @ X7 ) )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t41_subset_1])).

thf('6',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    r1_tarski @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['1','6'])).

thf('8',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t18_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) )
            = ( k2_struct_0 @ A ) ) ) ) )).

thf('9',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ( ( k4_subset_1 @ ( u1_struct_0 @ X11 ) @ X10 @ ( k3_subset_1 @ ( u1_struct_0 @ X11 ) @ X10 ) )
        = ( k2_struct_0 @ X11 ) )
      | ~ ( l1_struct_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t18_pre_topc])).

thf('10',plain,
    ( ~ ( l1_struct_0 @ sk_A )
    | ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      = ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('12',plain,(
    ! [X9: $i] :
      ( ( l1_struct_0 @ X9 )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('13',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,
    ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['10','13'])).

thf('15',plain,(
    r1_tarski @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['7','14'])).

thf(t31_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ( r1_tarski @ B @ C )
          <=> ( r1_tarski @ ( k3_subset_1 @ A @ C ) @ ( k3_subset_1 @ A @ B ) ) ) ) ) )).

thf('16',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X3 ) )
      | ~ ( r1_tarski @ ( k3_subset_1 @ X3 @ X2 ) @ ( k3_subset_1 @ X3 @ X4 ) )
      | ( r1_tarski @ X4 @ X2 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t31_subset_1])).

thf('17',plain,
    ( ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( r1_tarski @ sk_B @ ( k2_struct_0 @ sk_A ) )
    | ~ ( m1_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( r1_tarski @ sk_B @ ( k2_struct_0 @ sk_A ) )
    | ~ ( m1_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf(t43_tops_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( ( k1_tops_1 @ A @ ( k2_struct_0 @ A ) )
        = ( k2_struct_0 @ A ) ) ) )).

thf('20',plain,(
    ! [X12: $i] :
      ( ( ( k1_tops_1 @ X12 @ ( k2_struct_0 @ X12 ) )
        = ( k2_struct_0 @ X12 ) )
      | ~ ( l1_pre_topc @ X12 )
      | ~ ( v2_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[t43_tops_1])).

thf('21',plain,(
    ! [X8: $i] :
      ( ( m1_subset_1 @ ( k2_struct_0 @ X8 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ~ ( l1_struct_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_struct_0])).

thf('22',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_connsp_2,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( m2_connsp_2 @ C @ A @ B )
              <=> ( r1_tarski @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) )).

thf('23',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( r1_tarski @ X13 @ ( k1_tops_1 @ X14 @ X15 ) )
      | ( m2_connsp_2 @ X15 @ X14 @ X13 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( l1_pre_topc @ X14 )
      | ~ ( v2_pre_topc @ X14 ) ) ),
    inference(cnf,[status(esa)],[d2_connsp_2])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( m2_connsp_2 @ X0 @ sk_A @ sk_B )
      | ~ ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( m2_connsp_2 @ X0 @ sk_A @ sk_B )
      | ~ ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ X0 ) ) ) ),
    inference(demod,[status(thm)],['24','25','26'])).

thf('28',plain,
    ( ~ ( l1_struct_0 @ sk_A )
    | ~ ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ ( k2_struct_0 @ sk_A ) ) )
    | ( m2_connsp_2 @ ( k2_struct_0 @ sk_A ) @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['21','27'])).

thf('29',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['11','12'])).

thf('30',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ ( k2_struct_0 @ sk_A ) ) )
    | ( m2_connsp_2 @ ( k2_struct_0 @ sk_A ) @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,(
    ~ ( m2_connsp_2 @ ( k2_struct_0 @ sk_A ) @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    ~ ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['30','31'])).

thf('33',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k2_struct_0 @ sk_A ) )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['20','32'])).

thf('34',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    ~ ( r1_tarski @ sk_B @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['33','34','35'])).

thf('37',plain,(
    ~ ( m1_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['19','36'])).

thf('38',plain,(
    ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['0','37'])).

thf('39',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['11','12'])).

thf('40',plain,(
    $false ),
    inference(demod,[status(thm)],['38','39'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.MHAg2ctPhy
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:46:29 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.54  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.54  % Solved by: fo/fo7.sh
% 0.21/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.54  % done 82 iterations in 0.076s
% 0.21/0.54  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.54  % SZS output start Refutation
% 0.21/0.54  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.21/0.54  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.21/0.54  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.54  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.21/0.54  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 0.21/0.54  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.54  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.21/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.54  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.54  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.54  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.21/0.54  thf(m2_connsp_2_type, type, m2_connsp_2: $i > $i > $i > $o).
% 0.21/0.54  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.21/0.54  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.54  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.21/0.54  thf(dt_k2_struct_0, axiom,
% 0.21/0.54    (![A:$i]:
% 0.21/0.54     ( ( l1_struct_0 @ A ) =>
% 0.21/0.54       ( m1_subset_1 @
% 0.21/0.54         ( k2_struct_0 @ A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.21/0.54  thf('0', plain,
% 0.21/0.54      (![X8 : $i]:
% 0.21/0.54         ((m1_subset_1 @ (k2_struct_0 @ X8) @ 
% 0.21/0.54           (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 0.21/0.54          | ~ (l1_struct_0 @ X8))),
% 0.21/0.54      inference('cnf', [status(esa)], [dt_k2_struct_0])).
% 0.21/0.54  thf(t35_connsp_2, conjecture,
% 0.21/0.54    (![A:$i]:
% 0.21/0.54     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.54       ( ![B:$i]:
% 0.21/0.54         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.54           ( m2_connsp_2 @ ( k2_struct_0 @ A ) @ A @ B ) ) ) ))).
% 0.21/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.54    (~( ![A:$i]:
% 0.21/0.54        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.21/0.54            ( l1_pre_topc @ A ) ) =>
% 0.21/0.54          ( ![B:$i]:
% 0.21/0.54            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.54              ( m2_connsp_2 @ ( k2_struct_0 @ A ) @ A @ B ) ) ) ) )),
% 0.21/0.54    inference('cnf.neg', [status(esa)], [t35_connsp_2])).
% 0.21/0.54  thf('1', plain,
% 0.21/0.54      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('2', plain,
% 0.21/0.54      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf(dt_k3_subset_1, axiom,
% 0.21/0.54    (![A:$i,B:$i]:
% 0.21/0.54     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.54       ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.21/0.54  thf('3', plain,
% 0.21/0.54      (![X0 : $i, X1 : $i]:
% 0.21/0.54         ((m1_subset_1 @ (k3_subset_1 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))
% 0.21/0.54          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0)))),
% 0.21/0.54      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 0.21/0.54  thf('4', plain,
% 0.21/0.54      ((m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.21/0.54        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['2', '3'])).
% 0.21/0.54  thf(t41_subset_1, axiom,
% 0.21/0.54    (![A:$i,B:$i]:
% 0.21/0.54     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.54       ( ![C:$i]:
% 0.21/0.54         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.54           ( r1_tarski @
% 0.21/0.54             ( k3_subset_1 @ A @ ( k4_subset_1 @ A @ B @ C ) ) @ 
% 0.21/0.54             ( k3_subset_1 @ A @ B ) ) ) ) ))).
% 0.21/0.54  thf('5', plain,
% 0.21/0.54      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.21/0.54         (~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6))
% 0.21/0.54          | (r1_tarski @ (k3_subset_1 @ X6 @ (k4_subset_1 @ X6 @ X7 @ X5)) @ 
% 0.21/0.54             (k3_subset_1 @ X6 @ X7))
% 0.21/0.54          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X6)))),
% 0.21/0.54      inference('cnf', [status(esa)], [t41_subset_1])).
% 0.21/0.54  thf('6', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.54          | (r1_tarski @ 
% 0.21/0.54             (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.54              (k4_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ 
% 0.21/0.54               (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))) @ 
% 0.21/0.54             (k3_subset_1 @ (u1_struct_0 @ sk_A) @ X0)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['4', '5'])).
% 0.21/0.54  thf('7', plain,
% 0.21/0.54      ((r1_tarski @ 
% 0.21/0.54        (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.54         (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.21/0.54          (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))) @ 
% 0.21/0.54        (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 0.21/0.54      inference('sup-', [status(thm)], ['1', '6'])).
% 0.21/0.54  thf('8', plain,
% 0.21/0.54      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf(t18_pre_topc, axiom,
% 0.21/0.54    (![A:$i]:
% 0.21/0.54     ( ( l1_struct_0 @ A ) =>
% 0.21/0.54       ( ![B:$i]:
% 0.21/0.54         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.54           ( ( k4_subset_1 @
% 0.21/0.54               ( u1_struct_0 @ A ) @ B @ 
% 0.21/0.54               ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) =
% 0.21/0.54             ( k2_struct_0 @ A ) ) ) ) ))).
% 0.21/0.54  thf('9', plain,
% 0.21/0.54      (![X10 : $i, X11 : $i]:
% 0.21/0.54         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.21/0.54          | ((k4_subset_1 @ (u1_struct_0 @ X11) @ X10 @ 
% 0.21/0.54              (k3_subset_1 @ (u1_struct_0 @ X11) @ X10)) = (k2_struct_0 @ X11))
% 0.21/0.54          | ~ (l1_struct_0 @ X11))),
% 0.21/0.54      inference('cnf', [status(esa)], [t18_pre_topc])).
% 0.21/0.54  thf('10', plain,
% 0.21/0.54      ((~ (l1_struct_0 @ sk_A)
% 0.21/0.54        | ((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.21/0.54            (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)) = (k2_struct_0 @ sk_A)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['8', '9'])).
% 0.21/0.54  thf('11', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf(dt_l1_pre_topc, axiom,
% 0.21/0.54    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.21/0.54  thf('12', plain, (![X9 : $i]: ((l1_struct_0 @ X9) | ~ (l1_pre_topc @ X9))),
% 0.21/0.54      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.21/0.54  thf('13', plain, ((l1_struct_0 @ sk_A)),
% 0.21/0.54      inference('sup-', [status(thm)], ['11', '12'])).
% 0.21/0.54  thf('14', plain,
% 0.21/0.54      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.21/0.54         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)) = (k2_struct_0 @ sk_A))),
% 0.21/0.54      inference('demod', [status(thm)], ['10', '13'])).
% 0.21/0.54  thf('15', plain,
% 0.21/0.54      ((r1_tarski @ 
% 0.21/0.54        (k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A)) @ 
% 0.21/0.54        (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 0.21/0.54      inference('demod', [status(thm)], ['7', '14'])).
% 0.21/0.54  thf(t31_subset_1, axiom,
% 0.21/0.54    (![A:$i,B:$i]:
% 0.21/0.54     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.54       ( ![C:$i]:
% 0.21/0.54         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.54           ( ( r1_tarski @ B @ C ) <=>
% 0.21/0.54             ( r1_tarski @ ( k3_subset_1 @ A @ C ) @ ( k3_subset_1 @ A @ B ) ) ) ) ) ))).
% 0.21/0.54  thf('16', plain,
% 0.21/0.54      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.21/0.54         (~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X3))
% 0.21/0.54          | ~ (r1_tarski @ (k3_subset_1 @ X3 @ X2) @ (k3_subset_1 @ X3 @ X4))
% 0.21/0.54          | (r1_tarski @ X4 @ X2)
% 0.21/0.54          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X3)))),
% 0.21/0.54      inference('cnf', [status(esa)], [t31_subset_1])).
% 0.21/0.54  thf('17', plain,
% 0.21/0.54      ((~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.54        | (r1_tarski @ sk_B @ (k2_struct_0 @ sk_A))
% 0.21/0.54        | ~ (m1_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 0.21/0.54             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.21/0.54      inference('sup-', [status(thm)], ['15', '16'])).
% 0.21/0.54  thf('18', plain,
% 0.21/0.54      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('19', plain,
% 0.21/0.54      (((r1_tarski @ sk_B @ (k2_struct_0 @ sk_A))
% 0.21/0.54        | ~ (m1_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 0.21/0.54             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.21/0.54      inference('demod', [status(thm)], ['17', '18'])).
% 0.21/0.54  thf(t43_tops_1, axiom,
% 0.21/0.54    (![A:$i]:
% 0.21/0.54     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.54       ( ( k1_tops_1 @ A @ ( k2_struct_0 @ A ) ) = ( k2_struct_0 @ A ) ) ))).
% 0.21/0.54  thf('20', plain,
% 0.21/0.54      (![X12 : $i]:
% 0.21/0.54         (((k1_tops_1 @ X12 @ (k2_struct_0 @ X12)) = (k2_struct_0 @ X12))
% 0.21/0.54          | ~ (l1_pre_topc @ X12)
% 0.21/0.54          | ~ (v2_pre_topc @ X12))),
% 0.21/0.54      inference('cnf', [status(esa)], [t43_tops_1])).
% 0.21/0.54  thf('21', plain,
% 0.21/0.54      (![X8 : $i]:
% 0.21/0.54         ((m1_subset_1 @ (k2_struct_0 @ X8) @ 
% 0.21/0.54           (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 0.21/0.54          | ~ (l1_struct_0 @ X8))),
% 0.21/0.54      inference('cnf', [status(esa)], [dt_k2_struct_0])).
% 0.21/0.54  thf('22', plain,
% 0.21/0.54      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf(d2_connsp_2, axiom,
% 0.21/0.54    (![A:$i]:
% 0.21/0.54     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.54       ( ![B:$i]:
% 0.21/0.54         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.54           ( ![C:$i]:
% 0.21/0.54             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.54               ( ( m2_connsp_2 @ C @ A @ B ) <=>
% 0.21/0.54                 ( r1_tarski @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 0.21/0.54  thf('23', plain,
% 0.21/0.54      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.21/0.54         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.21/0.54          | ~ (r1_tarski @ X13 @ (k1_tops_1 @ X14 @ X15))
% 0.21/0.54          | (m2_connsp_2 @ X15 @ X14 @ X13)
% 0.21/0.54          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.21/0.54          | ~ (l1_pre_topc @ X14)
% 0.21/0.54          | ~ (v2_pre_topc @ X14))),
% 0.21/0.54      inference('cnf', [status(esa)], [d2_connsp_2])).
% 0.21/0.54  thf('24', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         (~ (v2_pre_topc @ sk_A)
% 0.21/0.54          | ~ (l1_pre_topc @ sk_A)
% 0.21/0.54          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.54          | (m2_connsp_2 @ X0 @ sk_A @ sk_B)
% 0.21/0.54          | ~ (r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ X0)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['22', '23'])).
% 0.21/0.54  thf('25', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('26', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('27', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.54          | (m2_connsp_2 @ X0 @ sk_A @ sk_B)
% 0.21/0.54          | ~ (r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ X0)))),
% 0.21/0.54      inference('demod', [status(thm)], ['24', '25', '26'])).
% 0.21/0.54  thf('28', plain,
% 0.21/0.54      ((~ (l1_struct_0 @ sk_A)
% 0.21/0.54        | ~ (r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ (k2_struct_0 @ sk_A)))
% 0.21/0.54        | (m2_connsp_2 @ (k2_struct_0 @ sk_A) @ sk_A @ sk_B))),
% 0.21/0.54      inference('sup-', [status(thm)], ['21', '27'])).
% 0.21/0.54  thf('29', plain, ((l1_struct_0 @ sk_A)),
% 0.21/0.54      inference('sup-', [status(thm)], ['11', '12'])).
% 0.21/0.54  thf('30', plain,
% 0.21/0.54      ((~ (r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ (k2_struct_0 @ sk_A)))
% 0.21/0.54        | (m2_connsp_2 @ (k2_struct_0 @ sk_A) @ sk_A @ sk_B))),
% 0.21/0.54      inference('demod', [status(thm)], ['28', '29'])).
% 0.21/0.54  thf('31', plain, (~ (m2_connsp_2 @ (k2_struct_0 @ sk_A) @ sk_A @ sk_B)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('32', plain,
% 0.21/0.54      (~ (r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ (k2_struct_0 @ sk_A)))),
% 0.21/0.54      inference('clc', [status(thm)], ['30', '31'])).
% 0.21/0.54  thf('33', plain,
% 0.21/0.54      ((~ (r1_tarski @ sk_B @ (k2_struct_0 @ sk_A))
% 0.21/0.54        | ~ (v2_pre_topc @ sk_A)
% 0.21/0.54        | ~ (l1_pre_topc @ sk_A))),
% 0.21/0.54      inference('sup-', [status(thm)], ['20', '32'])).
% 0.21/0.54  thf('34', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('35', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('36', plain, (~ (r1_tarski @ sk_B @ (k2_struct_0 @ sk_A))),
% 0.21/0.54      inference('demod', [status(thm)], ['33', '34', '35'])).
% 0.21/0.54  thf('37', plain,
% 0.21/0.54      (~ (m1_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 0.21/0.54          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.54      inference('clc', [status(thm)], ['19', '36'])).
% 0.21/0.54  thf('38', plain, (~ (l1_struct_0 @ sk_A)),
% 0.21/0.54      inference('sup-', [status(thm)], ['0', '37'])).
% 0.21/0.54  thf('39', plain, ((l1_struct_0 @ sk_A)),
% 0.21/0.54      inference('sup-', [status(thm)], ['11', '12'])).
% 0.21/0.54  thf('40', plain, ($false), inference('demod', [status(thm)], ['38', '39'])).
% 0.21/0.54  
% 0.21/0.54  % SZS output end Refutation
% 0.21/0.54  
% 0.21/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
