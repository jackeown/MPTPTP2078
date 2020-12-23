%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.y2XGyzVIuq

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:04:08 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 105 expanded)
%              Number of leaves         :   25 (  43 expanded)
%              Depth                    :    9
%              Number of atoms          :  522 (1393 expanded)
%              Number of equality atoms :   30 (  60 expanded)
%              Maximal formula depth    :   16 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(v1_tops_1_type,type,(
    v1_tops_1: $i > $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('0',plain,(
    ! [X11: $i] :
      ( ( ( k2_struct_0 @ X11 )
        = ( u1_struct_0 @ X11 ) )
      | ~ ( l1_struct_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(t81_tops_1,conjecture,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v1_tops_1 @ B @ A )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
               => ( ( v3_pre_topc @ C @ A )
                 => ( ( k2_pre_topc @ A @ C )
                    = ( k2_pre_topc @ A @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ C @ B ) ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( ( v1_tops_1 @ B @ A )
             => ! [C: $i] :
                  ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                 => ( ( v3_pre_topc @ C @ A )
                   => ( ( k2_pre_topc @ A @ C )
                      = ( k2_pre_topc @ A @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ C @ B ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t81_tops_1])).

thf('1',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t41_tops_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( v3_pre_topc @ B @ A )
               => ( ( k2_pre_topc @ A @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_pre_topc @ A @ C ) ) )
                  = ( k2_pre_topc @ A @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) ) ) ) ) ) ) )).

thf('3',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( v3_pre_topc @ X15 @ X16 )
      | ( ( k2_pre_topc @ X16 @ ( k9_subset_1 @ ( u1_struct_0 @ X16 ) @ X15 @ ( k2_pre_topc @ X16 @ X17 ) ) )
        = ( k2_pre_topc @ X16 @ ( k9_subset_1 @ ( u1_struct_0 @ X16 ) @ X15 @ X17 ) ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( l1_pre_topc @ X16 )
      | ~ ( v2_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[t41_tops_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( ( k2_pre_topc @ sk_A @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k2_pre_topc @ sk_A @ X0 ) ) )
        = ( k2_pre_topc @ sk_A @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ X0 ) ) )
      | ~ ( v3_pre_topc @ sk_C @ sk_A ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    v3_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( ( k2_pre_topc @ sk_A @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k2_pre_topc @ sk_A @ X0 ) ) )
        = ( k2_pre_topc @ sk_A @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['4','5','6','7'])).

thf('9',plain,
    ( ( k2_pre_topc @ sk_A @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) )
    = ( k2_pre_topc @ sk_A @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ sk_B ) ) ),
    inference('sup-',[status(thm)],['1','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v1_tops_1 @ B @ A )
          <=> ( ( k2_pre_topc @ A @ B )
              = ( k2_struct_0 @ A ) ) ) ) ) )).

thf('11',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( v1_tops_1 @ X13 @ X14 )
      | ( ( k2_pre_topc @ X14 @ X13 )
        = ( k2_struct_0 @ X14 ) )
      | ~ ( l1_pre_topc @ X14 ) ) ),
    inference(cnf,[status(esa)],[d3_tops_1])).

thf('12',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
      = ( k2_struct_0 @ sk_A ) )
    | ~ ( v1_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    v1_tops_1 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['12','13','14'])).

thf('16',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k3_xboole_0 @ B @ C ) ) ) )).

thf('17',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( ( k9_subset_1 @ X7 @ X5 @ X6 )
        = ( k3_xboole_0 @ X5 @ X6 ) )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_B )
      = ( k3_xboole_0 @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( ( k2_pre_topc @ sk_A @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k2_struct_0 @ sk_A ) ) )
    = ( k2_pre_topc @ sk_A @ ( k3_xboole_0 @ sk_C @ sk_B ) ) ),
    inference(demod,[status(thm)],['9','15','18'])).

thf('20',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( k9_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_C @ ( k2_struct_0 @ sk_A ) ) )
      = ( k2_pre_topc @ sk_A @ ( k3_xboole_0 @ sk_C @ sk_B ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['0','19'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('22',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['21'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('23',plain,(
    ! [X8: $i,X10: $i] :
      ( ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X10 ) )
      | ~ ( r1_tarski @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('24',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( ( k9_subset_1 @ X7 @ X5 @ X6 )
        = ( k3_xboole_0 @ X5 @ X6 ) )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_subset_1 @ X0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X11: $i] :
      ( ( ( k2_struct_0 @ X11 )
        = ( u1_struct_0 @ X11 ) )
      | ~ ( l1_struct_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('28',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('31',plain,(
    ! [X12: $i] :
      ( ( l1_struct_0 @ X12 )
      | ~ ( l1_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('32',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['29','32'])).

thf('34',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_tarski @ X8 @ X9 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('35',plain,(
    r1_tarski @ sk_C @ ( k2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('36',plain,(
    ! [X3: $i,X4: $i] :
      ( ( ( k3_xboole_0 @ X3 @ X4 )
        = X3 )
      | ~ ( r1_tarski @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('37',plain,
    ( ( k3_xboole_0 @ sk_C @ ( k2_struct_0 @ sk_A ) )
    = sk_C ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['30','31'])).

thf('39',plain,
    ( ( k2_pre_topc @ sk_A @ sk_C )
    = ( k2_pre_topc @ sk_A @ ( k3_xboole_0 @ sk_C @ sk_B ) ) ),
    inference(demod,[status(thm)],['20','26','37','38'])).

thf('40',plain,(
    ( k2_pre_topc @ sk_A @ sk_C )
 != ( k2_pre_topc @ sk_A @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_B )
      = ( k3_xboole_0 @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('42',plain,(
    ( k2_pre_topc @ sk_A @ sk_C )
 != ( k2_pre_topc @ sk_A @ ( k3_xboole_0 @ sk_C @ sk_B ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['39','42'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.y2XGyzVIuq
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:10:33 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.22/0.49  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.49  % Solved by: fo/fo7.sh
% 0.22/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.49  % done 83 iterations in 0.025s
% 0.22/0.49  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.49  % SZS output start Refutation
% 0.22/0.49  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.22/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.49  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.22/0.49  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.22/0.49  thf(sk_C_type, type, sk_C: $i).
% 0.22/0.49  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.22/0.49  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.22/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.49  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.49  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.22/0.49  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.22/0.49  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.22/0.49  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.22/0.49  thf(v1_tops_1_type, type, v1_tops_1: $i > $i > $o).
% 0.22/0.49  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.22/0.49  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.22/0.49  thf(d3_struct_0, axiom,
% 0.22/0.49    (![A:$i]:
% 0.22/0.49     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.22/0.49  thf('0', plain,
% 0.22/0.49      (![X11 : $i]:
% 0.22/0.49         (((k2_struct_0 @ X11) = (u1_struct_0 @ X11)) | ~ (l1_struct_0 @ X11))),
% 0.22/0.49      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.22/0.49  thf(t81_tops_1, conjecture,
% 0.22/0.49    (![A:$i]:
% 0.22/0.49     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.22/0.49       ( ![B:$i]:
% 0.22/0.49         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.49           ( ( v1_tops_1 @ B @ A ) =>
% 0.22/0.49             ( ![C:$i]:
% 0.22/0.49               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.49                 ( ( v3_pre_topc @ C @ A ) =>
% 0.22/0.49                   ( ( k2_pre_topc @ A @ C ) =
% 0.22/0.49                     ( k2_pre_topc @
% 0.22/0.49                       A @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ C @ B ) ) ) ) ) ) ) ) ) ))).
% 0.22/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.49    (~( ![A:$i]:
% 0.22/0.49        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.22/0.49          ( ![B:$i]:
% 0.22/0.49            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.49              ( ( v1_tops_1 @ B @ A ) =>
% 0.22/0.49                ( ![C:$i]:
% 0.22/0.49                  ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.49                    ( ( v3_pre_topc @ C @ A ) =>
% 0.22/0.49                      ( ( k2_pre_topc @ A @ C ) =
% 0.22/0.49                        ( k2_pre_topc @
% 0.22/0.49                          A @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ C @ B ) ) ) ) ) ) ) ) ) ) )),
% 0.22/0.49    inference('cnf.neg', [status(esa)], [t81_tops_1])).
% 0.22/0.49  thf('1', plain,
% 0.22/0.49      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('2', plain,
% 0.22/0.49      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf(t41_tops_1, axiom,
% 0.22/0.49    (![A:$i]:
% 0.22/0.49     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.22/0.49       ( ![B:$i]:
% 0.22/0.49         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.49           ( ![C:$i]:
% 0.22/0.49             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.49               ( ( v3_pre_topc @ B @ A ) =>
% 0.22/0.49                 ( ( k2_pre_topc @
% 0.22/0.49                     A @ 
% 0.22/0.49                     ( k9_subset_1 @
% 0.22/0.49                       ( u1_struct_0 @ A ) @ B @ ( k2_pre_topc @ A @ C ) ) ) =
% 0.22/0.49                   ( k2_pre_topc @
% 0.22/0.49                     A @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) ) ) ) ) ) ) ) ))).
% 0.22/0.49  thf('3', plain,
% 0.22/0.49      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.22/0.49         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.22/0.49          | ~ (v3_pre_topc @ X15 @ X16)
% 0.22/0.49          | ((k2_pre_topc @ X16 @ 
% 0.22/0.49              (k9_subset_1 @ (u1_struct_0 @ X16) @ X15 @ 
% 0.22/0.49               (k2_pre_topc @ X16 @ X17)))
% 0.22/0.49              = (k2_pre_topc @ X16 @ 
% 0.22/0.49                 (k9_subset_1 @ (u1_struct_0 @ X16) @ X15 @ X17)))
% 0.22/0.49          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.22/0.49          | ~ (l1_pre_topc @ X16)
% 0.22/0.49          | ~ (v2_pre_topc @ X16))),
% 0.22/0.49      inference('cnf', [status(esa)], [t41_tops_1])).
% 0.22/0.49  thf('4', plain,
% 0.22/0.49      (![X0 : $i]:
% 0.22/0.49         (~ (v2_pre_topc @ sk_A)
% 0.22/0.49          | ~ (l1_pre_topc @ sk_A)
% 0.22/0.49          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.22/0.49          | ((k2_pre_topc @ sk_A @ 
% 0.22/0.49              (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 0.22/0.49               (k2_pre_topc @ sk_A @ X0)))
% 0.22/0.49              = (k2_pre_topc @ sk_A @ 
% 0.22/0.49                 (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ X0)))
% 0.22/0.49          | ~ (v3_pre_topc @ sk_C @ sk_A))),
% 0.22/0.49      inference('sup-', [status(thm)], ['2', '3'])).
% 0.22/0.49  thf('5', plain, ((v2_pre_topc @ sk_A)),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('6', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('7', plain, ((v3_pre_topc @ sk_C @ sk_A)),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('8', plain,
% 0.22/0.49      (![X0 : $i]:
% 0.22/0.49         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.22/0.49          | ((k2_pre_topc @ sk_A @ 
% 0.22/0.49              (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 0.22/0.49               (k2_pre_topc @ sk_A @ X0)))
% 0.22/0.49              = (k2_pre_topc @ sk_A @ 
% 0.22/0.49                 (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ X0))))),
% 0.22/0.49      inference('demod', [status(thm)], ['4', '5', '6', '7'])).
% 0.22/0.49  thf('9', plain,
% 0.22/0.49      (((k2_pre_topc @ sk_A @ 
% 0.22/0.49         (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 0.22/0.49          (k2_pre_topc @ sk_A @ sk_B)))
% 0.22/0.49         = (k2_pre_topc @ sk_A @ 
% 0.22/0.49            (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ sk_B)))),
% 0.22/0.49      inference('sup-', [status(thm)], ['1', '8'])).
% 0.22/0.49  thf('10', plain,
% 0.22/0.49      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf(d3_tops_1, axiom,
% 0.22/0.49    (![A:$i]:
% 0.22/0.49     ( ( l1_pre_topc @ A ) =>
% 0.22/0.49       ( ![B:$i]:
% 0.22/0.49         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.49           ( ( v1_tops_1 @ B @ A ) <=>
% 0.22/0.49             ( ( k2_pre_topc @ A @ B ) = ( k2_struct_0 @ A ) ) ) ) ) ))).
% 0.22/0.49  thf('11', plain,
% 0.22/0.49      (![X13 : $i, X14 : $i]:
% 0.22/0.49         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.22/0.49          | ~ (v1_tops_1 @ X13 @ X14)
% 0.22/0.49          | ((k2_pre_topc @ X14 @ X13) = (k2_struct_0 @ X14))
% 0.22/0.49          | ~ (l1_pre_topc @ X14))),
% 0.22/0.49      inference('cnf', [status(esa)], [d3_tops_1])).
% 0.22/0.49  thf('12', plain,
% 0.22/0.49      ((~ (l1_pre_topc @ sk_A)
% 0.22/0.49        | ((k2_pre_topc @ sk_A @ sk_B) = (k2_struct_0 @ sk_A))
% 0.22/0.49        | ~ (v1_tops_1 @ sk_B @ sk_A))),
% 0.22/0.49      inference('sup-', [status(thm)], ['10', '11'])).
% 0.22/0.49  thf('13', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('14', plain, ((v1_tops_1 @ sk_B @ sk_A)),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('15', plain, (((k2_pre_topc @ sk_A @ sk_B) = (k2_struct_0 @ sk_A))),
% 0.22/0.49      inference('demod', [status(thm)], ['12', '13', '14'])).
% 0.22/0.49  thf('16', plain,
% 0.22/0.49      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf(redefinition_k9_subset_1, axiom,
% 0.22/0.49    (![A:$i,B:$i,C:$i]:
% 0.22/0.49     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.22/0.49       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 0.22/0.49  thf('17', plain,
% 0.22/0.49      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.22/0.49         (((k9_subset_1 @ X7 @ X5 @ X6) = (k3_xboole_0 @ X5 @ X6))
% 0.22/0.49          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7)))),
% 0.22/0.49      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 0.22/0.49  thf('18', plain,
% 0.22/0.49      (![X0 : $i]:
% 0.22/0.49         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_B)
% 0.22/0.49           = (k3_xboole_0 @ X0 @ sk_B))),
% 0.22/0.49      inference('sup-', [status(thm)], ['16', '17'])).
% 0.22/0.49  thf('19', plain,
% 0.22/0.49      (((k2_pre_topc @ sk_A @ 
% 0.22/0.49         (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ (k2_struct_0 @ sk_A)))
% 0.22/0.49         = (k2_pre_topc @ sk_A @ (k3_xboole_0 @ sk_C @ sk_B)))),
% 0.22/0.49      inference('demod', [status(thm)], ['9', '15', '18'])).
% 0.22/0.49  thf('20', plain,
% 0.22/0.49      ((((k2_pre_topc @ sk_A @ 
% 0.22/0.49          (k9_subset_1 @ (k2_struct_0 @ sk_A) @ sk_C @ (k2_struct_0 @ sk_A)))
% 0.22/0.49          = (k2_pre_topc @ sk_A @ (k3_xboole_0 @ sk_C @ sk_B)))
% 0.22/0.49        | ~ (l1_struct_0 @ sk_A))),
% 0.22/0.49      inference('sup+', [status(thm)], ['0', '19'])).
% 0.22/0.49  thf(d10_xboole_0, axiom,
% 0.22/0.49    (![A:$i,B:$i]:
% 0.22/0.49     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.22/0.49  thf('21', plain,
% 0.22/0.49      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.22/0.49      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.22/0.49  thf('22', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.22/0.49      inference('simplify', [status(thm)], ['21'])).
% 0.22/0.49  thf(t3_subset, axiom,
% 0.22/0.49    (![A:$i,B:$i]:
% 0.22/0.49     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.22/0.49  thf('23', plain,
% 0.22/0.49      (![X8 : $i, X10 : $i]:
% 0.22/0.49         ((m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X10)) | ~ (r1_tarski @ X8 @ X10))),
% 0.22/0.49      inference('cnf', [status(esa)], [t3_subset])).
% 0.22/0.49  thf('24', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.22/0.49      inference('sup-', [status(thm)], ['22', '23'])).
% 0.22/0.49  thf('25', plain,
% 0.22/0.49      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.22/0.49         (((k9_subset_1 @ X7 @ X5 @ X6) = (k3_xboole_0 @ X5 @ X6))
% 0.22/0.49          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7)))),
% 0.22/0.49      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 0.22/0.49  thf('26', plain,
% 0.22/0.49      (![X0 : $i, X1 : $i]:
% 0.22/0.49         ((k9_subset_1 @ X0 @ X1 @ X0) = (k3_xboole_0 @ X1 @ X0))),
% 0.22/0.49      inference('sup-', [status(thm)], ['24', '25'])).
% 0.22/0.49  thf('27', plain,
% 0.22/0.49      (![X11 : $i]:
% 0.22/0.49         (((k2_struct_0 @ X11) = (u1_struct_0 @ X11)) | ~ (l1_struct_0 @ X11))),
% 0.22/0.49      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.22/0.49  thf('28', plain,
% 0.22/0.49      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('29', plain,
% 0.22/0.49      (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))
% 0.22/0.49        | ~ (l1_struct_0 @ sk_A))),
% 0.22/0.49      inference('sup+', [status(thm)], ['27', '28'])).
% 0.22/0.49  thf('30', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf(dt_l1_pre_topc, axiom,
% 0.22/0.49    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.22/0.49  thf('31', plain,
% 0.22/0.49      (![X12 : $i]: ((l1_struct_0 @ X12) | ~ (l1_pre_topc @ X12))),
% 0.22/0.49      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.22/0.49  thf('32', plain, ((l1_struct_0 @ sk_A)),
% 0.22/0.49      inference('sup-', [status(thm)], ['30', '31'])).
% 0.22/0.49  thf('33', plain,
% 0.22/0.49      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))),
% 0.22/0.49      inference('demod', [status(thm)], ['29', '32'])).
% 0.22/0.49  thf('34', plain,
% 0.22/0.49      (![X8 : $i, X9 : $i]:
% 0.22/0.49         ((r1_tarski @ X8 @ X9) | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9)))),
% 0.22/0.49      inference('cnf', [status(esa)], [t3_subset])).
% 0.22/0.49  thf('35', plain, ((r1_tarski @ sk_C @ (k2_struct_0 @ sk_A))),
% 0.22/0.49      inference('sup-', [status(thm)], ['33', '34'])).
% 0.22/0.49  thf(t28_xboole_1, axiom,
% 0.22/0.49    (![A:$i,B:$i]:
% 0.22/0.49     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.22/0.49  thf('36', plain,
% 0.22/0.49      (![X3 : $i, X4 : $i]:
% 0.22/0.49         (((k3_xboole_0 @ X3 @ X4) = (X3)) | ~ (r1_tarski @ X3 @ X4))),
% 0.22/0.49      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.22/0.49  thf('37', plain, (((k3_xboole_0 @ sk_C @ (k2_struct_0 @ sk_A)) = (sk_C))),
% 0.22/0.49      inference('sup-', [status(thm)], ['35', '36'])).
% 0.22/0.49  thf('38', plain, ((l1_struct_0 @ sk_A)),
% 0.22/0.49      inference('sup-', [status(thm)], ['30', '31'])).
% 0.22/0.49  thf('39', plain,
% 0.22/0.49      (((k2_pre_topc @ sk_A @ sk_C)
% 0.22/0.49         = (k2_pre_topc @ sk_A @ (k3_xboole_0 @ sk_C @ sk_B)))),
% 0.22/0.49      inference('demod', [status(thm)], ['20', '26', '37', '38'])).
% 0.22/0.49  thf('40', plain,
% 0.22/0.49      (((k2_pre_topc @ sk_A @ sk_C)
% 0.22/0.49         != (k2_pre_topc @ sk_A @ 
% 0.22/0.49             (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ sk_B)))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('41', plain,
% 0.22/0.49      (![X0 : $i]:
% 0.22/0.49         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_B)
% 0.22/0.49           = (k3_xboole_0 @ X0 @ sk_B))),
% 0.22/0.49      inference('sup-', [status(thm)], ['16', '17'])).
% 0.22/0.49  thf('42', plain,
% 0.22/0.49      (((k2_pre_topc @ sk_A @ sk_C)
% 0.22/0.49         != (k2_pre_topc @ sk_A @ (k3_xboole_0 @ sk_C @ sk_B)))),
% 0.22/0.49      inference('demod', [status(thm)], ['40', '41'])).
% 0.22/0.49  thf('43', plain, ($false),
% 0.22/0.49      inference('simplify_reflect-', [status(thm)], ['39', '42'])).
% 0.22/0.49  
% 0.22/0.49  % SZS output end Refutation
% 0.22/0.49  
% 0.22/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
