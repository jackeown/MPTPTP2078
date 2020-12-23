%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.VX0TS5sEEw

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:04:10 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   61 (  95 expanded)
%              Number of leaves         :   20 (  38 expanded)
%              Depth                    :   10
%              Number of atoms          :  482 (1386 expanded)
%              Number of equality atoms :   23 (  28 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(v1_tops_1_type,type,(
    v1_tops_1: $i > $i > $o )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(t82_tops_1,conjecture,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( ( v1_tops_1 @ B @ A )
                  & ( v1_tops_1 @ C @ A )
                  & ( v3_pre_topc @ C @ A ) )
               => ( v1_tops_1 @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
               => ( ( ( v1_tops_1 @ B @ A )
                    & ( v1_tops_1 @ C @ A )
                    & ( v3_pre_topc @ C @ A ) )
                 => ( v1_tops_1 @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t82_tops_1])).

thf('0',plain,(
    ~ ( v1_tops_1 @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C ) @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k3_xboole_0 @ B @ C ) ) ) )).

thf('2',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( ( k9_subset_1 @ X7 @ X5 @ X6 )
        = ( k3_xboole_0 @ X5 @ X6 ) )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_C )
      = ( k3_xboole_0 @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ~ ( v1_tops_1 @ ( k3_xboole_0 @ sk_B @ sk_C ) @ sk_A ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t81_tops_1,axiom,(
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

thf('7',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ~ ( v3_pre_topc @ X14 @ X13 )
      | ( ( k2_pre_topc @ X13 @ X14 )
        = ( k2_pre_topc @ X13 @ ( k9_subset_1 @ ( u1_struct_0 @ X13 ) @ X14 @ X12 ) ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ~ ( v1_tops_1 @ X12 @ X13 )
      | ~ ( l1_pre_topc @ X13 )
      | ~ ( v2_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[t81_tops_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v1_tops_1 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( ( k2_pre_topc @ sk_A @ X0 )
        = ( k2_pre_topc @ sk_A @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_B ) ) )
      | ~ ( v3_pre_topc @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    v1_tops_1 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( ( k9_subset_1 @ X7 @ X5 @ X6 )
        = ( k3_xboole_0 @ X5 @ X6 ) )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_B )
      = ( k3_xboole_0 @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( ( k2_pre_topc @ sk_A @ X0 )
        = ( k2_pre_topc @ sk_A @ ( k3_xboole_0 @ X0 @ sk_B ) ) )
      | ~ ( v3_pre_topc @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['8','9','10','11','14'])).

thf('16',plain,
    ( ~ ( v3_pre_topc @ sk_C @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_C )
      = ( k2_pre_topc @ sk_A @ ( k3_xboole_0 @ sk_C @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['5','15'])).

thf('17',plain,(
    v3_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v1_tops_1 @ B @ A )
          <=> ( ( k2_pre_topc @ A @ B )
              = ( k2_struct_0 @ A ) ) ) ) ) )).

thf('19',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ~ ( v1_tops_1 @ X10 @ X11 )
      | ( ( k2_pre_topc @ X11 @ X10 )
        = ( k2_struct_0 @ X11 ) )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[d3_tops_1])).

thf('20',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_C )
      = ( k2_struct_0 @ sk_A ) )
    | ~ ( v1_tops_1 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    v1_tops_1 @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ( k2_pre_topc @ sk_A @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['20','21','22'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('25',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( k2_pre_topc @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['16','17','23','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('27',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k9_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('28',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( m1_subset_1 @ ( k9_subset_1 @ X2 @ X3 @ X4 ) @ ( k1_zfmisc_1 @ X2 ) )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k9_subset_1])).

thf('29',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_B )
      = ( k3_xboole_0 @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('31',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['26','31'])).

thf('33',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ( ( k2_pre_topc @ X11 @ X10 )
       != ( k2_struct_0 @ X11 ) )
      | ( v1_tops_1 @ X10 @ X11 )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[d3_tops_1])).

thf('34',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ( v1_tops_1 @ ( k3_xboole_0 @ sk_B @ X0 ) @ sk_A )
      | ( ( k2_pre_topc @ sk_A @ ( k3_xboole_0 @ sk_B @ X0 ) )
       != ( k2_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( v1_tops_1 @ ( k3_xboole_0 @ sk_B @ X0 ) @ sk_A )
      | ( ( k2_pre_topc @ sk_A @ ( k3_xboole_0 @ sk_B @ X0 ) )
       != ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,
    ( ( ( k2_struct_0 @ sk_A )
     != ( k2_struct_0 @ sk_A ) )
    | ( v1_tops_1 @ ( k3_xboole_0 @ sk_B @ sk_C ) @ sk_A ) ),
    inference('sup-',[status(thm)],['25','36'])).

thf('38',plain,(
    v1_tops_1 @ ( k3_xboole_0 @ sk_B @ sk_C ) @ sk_A ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,(
    $false ),
    inference(demod,[status(thm)],['4','38'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.VX0TS5sEEw
% 0.14/0.35  % Computer   : n008.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 10:25:00 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.22/0.51  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.51  % Solved by: fo/fo7.sh
% 0.22/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.51  % done 92 iterations in 0.045s
% 0.22/0.51  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.51  % SZS output start Refutation
% 0.22/0.51  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.22/0.51  thf(v1_tops_1_type, type, v1_tops_1: $i > $i > $o).
% 0.22/0.51  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.22/0.51  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.22/0.51  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.22/0.51  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.22/0.51  thf(sk_C_type, type, sk_C: $i).
% 0.22/0.51  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.22/0.51  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.22/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.51  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.51  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.22/0.51  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.22/0.51  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.22/0.51  thf(t82_tops_1, conjecture,
% 0.22/0.51    (![A:$i]:
% 0.22/0.51     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.22/0.51       ( ![B:$i]:
% 0.22/0.51         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.51           ( ![C:$i]:
% 0.22/0.51             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.51               ( ( ( v1_tops_1 @ B @ A ) & ( v1_tops_1 @ C @ A ) & 
% 0.22/0.51                   ( v3_pre_topc @ C @ A ) ) =>
% 0.22/0.51                 ( v1_tops_1 @
% 0.22/0.51                   ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ A ) ) ) ) ) ) ))).
% 0.22/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.51    (~( ![A:$i]:
% 0.22/0.51        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.22/0.51          ( ![B:$i]:
% 0.22/0.51            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.51              ( ![C:$i]:
% 0.22/0.51                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.51                  ( ( ( v1_tops_1 @ B @ A ) & ( v1_tops_1 @ C @ A ) & 
% 0.22/0.51                      ( v3_pre_topc @ C @ A ) ) =>
% 0.22/0.51                    ( v1_tops_1 @
% 0.22/0.51                      ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ A ) ) ) ) ) ) ) )),
% 0.22/0.51    inference('cnf.neg', [status(esa)], [t82_tops_1])).
% 0.22/0.51  thf('0', plain,
% 0.22/0.51      (~ (v1_tops_1 @ (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C) @ sk_A)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('1', plain,
% 0.22/0.51      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf(redefinition_k9_subset_1, axiom,
% 0.22/0.51    (![A:$i,B:$i,C:$i]:
% 0.22/0.51     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.22/0.51       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 0.22/0.51  thf('2', plain,
% 0.22/0.51      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.22/0.51         (((k9_subset_1 @ X7 @ X5 @ X6) = (k3_xboole_0 @ X5 @ X6))
% 0.22/0.51          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7)))),
% 0.22/0.51      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 0.22/0.51  thf('3', plain,
% 0.22/0.51      (![X0 : $i]:
% 0.22/0.51         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_C)
% 0.22/0.51           = (k3_xboole_0 @ X0 @ sk_C))),
% 0.22/0.51      inference('sup-', [status(thm)], ['1', '2'])).
% 0.22/0.51  thf('4', plain, (~ (v1_tops_1 @ (k3_xboole_0 @ sk_B @ sk_C) @ sk_A)),
% 0.22/0.51      inference('demod', [status(thm)], ['0', '3'])).
% 0.22/0.51  thf('5', plain,
% 0.22/0.51      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('6', plain,
% 0.22/0.51      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf(t81_tops_1, axiom,
% 0.22/0.51    (![A:$i]:
% 0.22/0.51     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.22/0.51       ( ![B:$i]:
% 0.22/0.51         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.51           ( ( v1_tops_1 @ B @ A ) =>
% 0.22/0.51             ( ![C:$i]:
% 0.22/0.51               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.51                 ( ( v3_pre_topc @ C @ A ) =>
% 0.22/0.51                   ( ( k2_pre_topc @ A @ C ) =
% 0.22/0.51                     ( k2_pre_topc @
% 0.22/0.51                       A @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ C @ B ) ) ) ) ) ) ) ) ) ))).
% 0.22/0.51  thf('7', plain,
% 0.22/0.51      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.22/0.51         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.22/0.51          | ~ (v3_pre_topc @ X14 @ X13)
% 0.22/0.51          | ((k2_pre_topc @ X13 @ X14)
% 0.22/0.51              = (k2_pre_topc @ X13 @ 
% 0.22/0.51                 (k9_subset_1 @ (u1_struct_0 @ X13) @ X14 @ X12)))
% 0.22/0.51          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.22/0.51          | ~ (v1_tops_1 @ X12 @ X13)
% 0.22/0.51          | ~ (l1_pre_topc @ X13)
% 0.22/0.51          | ~ (v2_pre_topc @ X13))),
% 0.22/0.51      inference('cnf', [status(esa)], [t81_tops_1])).
% 0.22/0.51  thf('8', plain,
% 0.22/0.51      (![X0 : $i]:
% 0.22/0.51         (~ (v2_pre_topc @ sk_A)
% 0.22/0.51          | ~ (l1_pre_topc @ sk_A)
% 0.22/0.51          | ~ (v1_tops_1 @ sk_B @ sk_A)
% 0.22/0.51          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.22/0.51          | ((k2_pre_topc @ sk_A @ X0)
% 0.22/0.51              = (k2_pre_topc @ sk_A @ 
% 0.22/0.51                 (k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_B)))
% 0.22/0.51          | ~ (v3_pre_topc @ X0 @ sk_A))),
% 0.22/0.51      inference('sup-', [status(thm)], ['6', '7'])).
% 0.22/0.51  thf('9', plain, ((v2_pre_topc @ sk_A)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('10', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('11', plain, ((v1_tops_1 @ sk_B @ sk_A)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('12', plain,
% 0.22/0.51      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('13', plain,
% 0.22/0.51      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.22/0.51         (((k9_subset_1 @ X7 @ X5 @ X6) = (k3_xboole_0 @ X5 @ X6))
% 0.22/0.51          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7)))),
% 0.22/0.51      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 0.22/0.51  thf('14', plain,
% 0.22/0.51      (![X0 : $i]:
% 0.22/0.51         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_B)
% 0.22/0.51           = (k3_xboole_0 @ X0 @ sk_B))),
% 0.22/0.51      inference('sup-', [status(thm)], ['12', '13'])).
% 0.22/0.51  thf('15', plain,
% 0.22/0.51      (![X0 : $i]:
% 0.22/0.51         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.22/0.51          | ((k2_pre_topc @ sk_A @ X0)
% 0.22/0.51              = (k2_pre_topc @ sk_A @ (k3_xboole_0 @ X0 @ sk_B)))
% 0.22/0.51          | ~ (v3_pre_topc @ X0 @ sk_A))),
% 0.22/0.51      inference('demod', [status(thm)], ['8', '9', '10', '11', '14'])).
% 0.22/0.51  thf('16', plain,
% 0.22/0.51      ((~ (v3_pre_topc @ sk_C @ sk_A)
% 0.22/0.51        | ((k2_pre_topc @ sk_A @ sk_C)
% 0.22/0.51            = (k2_pre_topc @ sk_A @ (k3_xboole_0 @ sk_C @ sk_B))))),
% 0.22/0.51      inference('sup-', [status(thm)], ['5', '15'])).
% 0.22/0.51  thf('17', plain, ((v3_pre_topc @ sk_C @ sk_A)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('18', plain,
% 0.22/0.51      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf(d3_tops_1, axiom,
% 0.22/0.51    (![A:$i]:
% 0.22/0.51     ( ( l1_pre_topc @ A ) =>
% 0.22/0.51       ( ![B:$i]:
% 0.22/0.51         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.51           ( ( v1_tops_1 @ B @ A ) <=>
% 0.22/0.51             ( ( k2_pre_topc @ A @ B ) = ( k2_struct_0 @ A ) ) ) ) ) ))).
% 0.22/0.51  thf('19', plain,
% 0.22/0.51      (![X10 : $i, X11 : $i]:
% 0.22/0.51         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.22/0.51          | ~ (v1_tops_1 @ X10 @ X11)
% 0.22/0.51          | ((k2_pre_topc @ X11 @ X10) = (k2_struct_0 @ X11))
% 0.22/0.51          | ~ (l1_pre_topc @ X11))),
% 0.22/0.51      inference('cnf', [status(esa)], [d3_tops_1])).
% 0.22/0.51  thf('20', plain,
% 0.22/0.51      ((~ (l1_pre_topc @ sk_A)
% 0.22/0.51        | ((k2_pre_topc @ sk_A @ sk_C) = (k2_struct_0 @ sk_A))
% 0.22/0.51        | ~ (v1_tops_1 @ sk_C @ sk_A))),
% 0.22/0.51      inference('sup-', [status(thm)], ['18', '19'])).
% 0.22/0.51  thf('21', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('22', plain, ((v1_tops_1 @ sk_C @ sk_A)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('23', plain, (((k2_pre_topc @ sk_A @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.22/0.51      inference('demod', [status(thm)], ['20', '21', '22'])).
% 0.22/0.51  thf(commutativity_k3_xboole_0, axiom,
% 0.22/0.51    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.22/0.51  thf('24', plain,
% 0.22/0.51      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.22/0.51      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.22/0.51  thf('25', plain,
% 0.22/0.51      (((k2_struct_0 @ sk_A)
% 0.22/0.51         = (k2_pre_topc @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C)))),
% 0.22/0.51      inference('demod', [status(thm)], ['16', '17', '23', '24'])).
% 0.22/0.51  thf('26', plain,
% 0.22/0.51      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.22/0.51      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.22/0.51  thf('27', plain,
% 0.22/0.51      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf(dt_k9_subset_1, axiom,
% 0.22/0.51    (![A:$i,B:$i,C:$i]:
% 0.22/0.51     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.22/0.51       ( m1_subset_1 @ ( k9_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.22/0.51  thf('28', plain,
% 0.22/0.51      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.22/0.51         ((m1_subset_1 @ (k9_subset_1 @ X2 @ X3 @ X4) @ (k1_zfmisc_1 @ X2))
% 0.22/0.51          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X2)))),
% 0.22/0.51      inference('cnf', [status(esa)], [dt_k9_subset_1])).
% 0.22/0.51  thf('29', plain,
% 0.22/0.51      (![X0 : $i]:
% 0.22/0.51         (m1_subset_1 @ (k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_B) @ 
% 0.22/0.51          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.51      inference('sup-', [status(thm)], ['27', '28'])).
% 0.22/0.51  thf('30', plain,
% 0.22/0.51      (![X0 : $i]:
% 0.22/0.51         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_B)
% 0.22/0.51           = (k3_xboole_0 @ X0 @ sk_B))),
% 0.22/0.51      inference('sup-', [status(thm)], ['12', '13'])).
% 0.22/0.51  thf('31', plain,
% 0.22/0.51      (![X0 : $i]:
% 0.22/0.51         (m1_subset_1 @ (k3_xboole_0 @ X0 @ sk_B) @ 
% 0.22/0.51          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.51      inference('demod', [status(thm)], ['29', '30'])).
% 0.22/0.51  thf('32', plain,
% 0.22/0.51      (![X0 : $i]:
% 0.22/0.51         (m1_subset_1 @ (k3_xboole_0 @ sk_B @ X0) @ 
% 0.22/0.51          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.51      inference('sup+', [status(thm)], ['26', '31'])).
% 0.22/0.51  thf('33', plain,
% 0.22/0.51      (![X10 : $i, X11 : $i]:
% 0.22/0.51         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.22/0.51          | ((k2_pre_topc @ X11 @ X10) != (k2_struct_0 @ X11))
% 0.22/0.51          | (v1_tops_1 @ X10 @ X11)
% 0.22/0.51          | ~ (l1_pre_topc @ X11))),
% 0.22/0.51      inference('cnf', [status(esa)], [d3_tops_1])).
% 0.22/0.51  thf('34', plain,
% 0.22/0.51      (![X0 : $i]:
% 0.22/0.51         (~ (l1_pre_topc @ sk_A)
% 0.22/0.51          | (v1_tops_1 @ (k3_xboole_0 @ sk_B @ X0) @ sk_A)
% 0.22/0.51          | ((k2_pre_topc @ sk_A @ (k3_xboole_0 @ sk_B @ X0))
% 0.22/0.51              != (k2_struct_0 @ sk_A)))),
% 0.22/0.51      inference('sup-', [status(thm)], ['32', '33'])).
% 0.22/0.51  thf('35', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('36', plain,
% 0.22/0.51      (![X0 : $i]:
% 0.22/0.51         ((v1_tops_1 @ (k3_xboole_0 @ sk_B @ X0) @ sk_A)
% 0.22/0.51          | ((k2_pre_topc @ sk_A @ (k3_xboole_0 @ sk_B @ X0))
% 0.22/0.51              != (k2_struct_0 @ sk_A)))),
% 0.22/0.51      inference('demod', [status(thm)], ['34', '35'])).
% 0.22/0.51  thf('37', plain,
% 0.22/0.51      ((((k2_struct_0 @ sk_A) != (k2_struct_0 @ sk_A))
% 0.22/0.51        | (v1_tops_1 @ (k3_xboole_0 @ sk_B @ sk_C) @ sk_A))),
% 0.22/0.51      inference('sup-', [status(thm)], ['25', '36'])).
% 0.22/0.51  thf('38', plain, ((v1_tops_1 @ (k3_xboole_0 @ sk_B @ sk_C) @ sk_A)),
% 0.22/0.51      inference('simplify', [status(thm)], ['37'])).
% 0.22/0.51  thf('39', plain, ($false), inference('demod', [status(thm)], ['4', '38'])).
% 0.22/0.51  
% 0.22/0.51  % SZS output end Refutation
% 0.22/0.51  
% 0.22/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
