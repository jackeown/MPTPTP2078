%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.CfxEXS9FLG

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:05:35 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 160 expanded)
%              Number of leaves         :   26 (  59 expanded)
%              Depth                    :   14
%              Number of atoms          :  517 (1673 expanded)
%              Number of equality atoms :   22 (  74 expanded)
%              Maximal formula depth    :   16 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(t34_tops_2,conjecture,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_pre_topc @ C @ A )
             => ( ( v4_pre_topc @ B @ A )
               => ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ C ) ) )
                   => ( ( D = B )
                     => ( v4_pre_topc @ D @ C ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_pre_topc @ A )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ! [C: $i] :
                ( ( m1_pre_topc @ C @ A )
               => ( ( v4_pre_topc @ B @ A )
                 => ! [D: $i] :
                      ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ C ) ) )
                     => ( ( D = B )
                       => ( v4_pre_topc @ D @ C ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t34_tops_2])).

thf('0',plain,(
    ~ ( v4_pre_topc @ sk_D_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    sk_D_1 = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    ~ ( v4_pre_topc @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('3',plain,(
    ! [X10: $i] :
      ( ( ( k2_struct_0 @ X10 )
        = ( u1_struct_0 @ X10 ) )
      | ~ ( l1_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('4',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    ! [X10: $i] :
      ( ( ( k2_struct_0 @ X10 )
        = ( u1_struct_0 @ X10 ) )
      | ~ ( l1_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('6',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    sk_D_1 = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('9',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_tarski @ X7 @ X8 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('10',plain,(
    r1_tarski @ sk_B @ ( u1_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = X0 )
      | ~ ( r1_tarski @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('12',plain,
    ( ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_C ) )
    = sk_B ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,
    ( ( ( k3_xboole_0 @ sk_B @ ( k2_struct_0 @ sk_C ) )
      = sk_B )
    | ~ ( l1_struct_0 @ sk_C ) ),
    inference('sup+',[status(thm)],['5','12'])).

thf('14',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('15',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( m1_pre_topc @ X12 @ X13 )
      | ( l1_pre_topc @ X12 )
      | ~ ( l1_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('16',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_C ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['16','17'])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('19',plain,(
    ! [X11: $i] :
      ( ( l1_struct_0 @ X11 )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('20',plain,(
    l1_struct_0 @ sk_C ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k2_struct_0 @ sk_C ) )
    = sk_B ),
    inference(demod,[status(thm)],['13','20'])).

thf('22',plain,(
    ! [X10: $i] :
      ( ( ( k2_struct_0 @ X10 )
        = ( u1_struct_0 @ X10 ) )
      | ~ ( l1_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(t43_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) )
             => ( ( v4_pre_topc @ C @ B )
              <=> ? [D: $i] :
                    ( ( ( k9_subset_1 @ ( u1_struct_0 @ B ) @ D @ ( k2_struct_0 @ B ) )
                      = C )
                    & ( v4_pre_topc @ D @ A )
                    & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ) )).

thf('23',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_pre_topc @ X14 @ X15 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X14 ) @ X17 @ ( k2_struct_0 @ X14 ) )
       != X16 )
      | ~ ( v4_pre_topc @ X17 @ X15 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ( v4_pre_topc @ X16 @ X14 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( l1_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[t43_pre_topc])).

thf('24',plain,(
    ! [X14: $i,X15: $i,X17: $i] :
      ( ~ ( l1_pre_topc @ X15 )
      | ~ ( m1_subset_1 @ ( k9_subset_1 @ ( u1_struct_0 @ X14 ) @ X17 @ ( k2_struct_0 @ X14 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ( v4_pre_topc @ ( k9_subset_1 @ ( u1_struct_0 @ X14 ) @ X17 @ ( k2_struct_0 @ X14 ) ) @ X14 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ~ ( v4_pre_topc @ X17 @ X15 )
      | ~ ( m1_pre_topc @ X14 @ X15 ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ ( k9_subset_1 @ ( k2_struct_0 @ X0 ) @ X1 @ ( k2_struct_0 @ X0 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X2 )
      | ~ ( v4_pre_topc @ X1 @ X2 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X2 ) ) )
      | ( v4_pre_topc @ ( k9_subset_1 @ ( u1_struct_0 @ X0 ) @ X1 @ ( k2_struct_0 @ X0 ) ) @ X0 )
      | ~ ( l1_pre_topc @ X2 ) ) ),
    inference('sup-',[status(thm)],['22','24'])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('26',plain,(
    ! [X3: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X3 ) @ ( k1_zfmisc_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('27',plain,(
    ! [X2: $i] :
      ( ( k2_subset_1 @ X2 )
      = X2 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('28',plain,(
    ! [X3: $i] :
      ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X3 ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf(redefinition_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k3_xboole_0 @ B @ C ) ) ) )).

thf('29',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( ( k9_subset_1 @ X6 @ X4 @ X5 )
        = ( k3_xboole_0 @ X4 @ X5 ) )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_subset_1 @ X0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ ( k3_xboole_0 @ X1 @ ( k2_struct_0 @ X0 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X2 )
      | ~ ( v4_pre_topc @ X1 @ X2 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X2 ) ) )
      | ( v4_pre_topc @ ( k9_subset_1 @ ( u1_struct_0 @ X0 ) @ X1 @ ( k2_struct_0 @ X0 ) ) @ X0 )
      | ~ ( l1_pre_topc @ X2 ) ) ),
    inference(demod,[status(thm)],['25','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ( v4_pre_topc @ ( k9_subset_1 @ ( u1_struct_0 @ sk_C ) @ sk_B @ ( k2_struct_0 @ sk_C ) ) @ sk_C )
      | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( v4_pre_topc @ sk_B @ X0 )
      | ~ ( m1_pre_topc @ sk_C @ X0 )
      | ~ ( l1_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['21','31'])).

thf('33',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('34',plain,(
    l1_struct_0 @ sk_C ),
    inference('sup-',[status(thm)],['18','19'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v4_pre_topc @ ( k9_subset_1 @ ( u1_struct_0 @ sk_C ) @ sk_B @ ( k2_struct_0 @ sk_C ) ) @ sk_C )
      | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( v4_pre_topc @ sk_B @ X0 )
      | ~ ( m1_pre_topc @ sk_C @ X0 ) ) ),
    inference(demod,[status(thm)],['32','33','34'])).

thf('36',plain,
    ( ~ ( m1_pre_topc @ sk_C @ sk_A )
    | ~ ( v4_pre_topc @ sk_B @ sk_A )
    | ( v4_pre_topc @ ( k9_subset_1 @ ( u1_struct_0 @ sk_C ) @ sk_B @ ( k2_struct_0 @ sk_C ) ) @ sk_C )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['4','35'])).

thf('37',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    v4_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    v4_pre_topc @ ( k9_subset_1 @ ( u1_struct_0 @ sk_C ) @ sk_B @ ( k2_struct_0 @ sk_C ) ) @ sk_C ),
    inference(demod,[status(thm)],['36','37','38','39'])).

thf('41',plain,
    ( ( v4_pre_topc @ ( k9_subset_1 @ ( k2_struct_0 @ sk_C ) @ sk_B @ ( k2_struct_0 @ sk_C ) ) @ sk_C )
    | ~ ( l1_struct_0 @ sk_C ) ),
    inference('sup+',[status(thm)],['3','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_subset_1 @ X0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('43',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k2_struct_0 @ sk_C ) )
    = sk_B ),
    inference(demod,[status(thm)],['13','20'])).

thf('44',plain,(
    l1_struct_0 @ sk_C ),
    inference('sup-',[status(thm)],['18','19'])).

thf('45',plain,(
    v4_pre_topc @ sk_B @ sk_C ),
    inference(demod,[status(thm)],['41','42','43','44'])).

thf('46',plain,(
    $false ),
    inference(demod,[status(thm)],['2','45'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.CfxEXS9FLG
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 19:31:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.20/0.51  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.51  % Solved by: fo/fo7.sh
% 0.20/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.51  % done 83 iterations in 0.044s
% 0.20/0.51  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.51  % SZS output start Refutation
% 0.20/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.51  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.51  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.20/0.51  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.20/0.51  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.20/0.51  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.20/0.51  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.20/0.51  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.20/0.51  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.51  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.51  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.51  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.20/0.51  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.20/0.51  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.51  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.20/0.51  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.51  thf(t34_tops_2, conjecture,
% 0.20/0.51    (![A:$i]:
% 0.20/0.51     ( ( l1_pre_topc @ A ) =>
% 0.20/0.51       ( ![B:$i]:
% 0.20/0.51         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.51           ( ![C:$i]:
% 0.20/0.51             ( ( m1_pre_topc @ C @ A ) =>
% 0.20/0.51               ( ( v4_pre_topc @ B @ A ) =>
% 0.20/0.51                 ( ![D:$i]:
% 0.20/0.51                   ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ C ) ) ) =>
% 0.20/0.51                     ( ( ( D ) = ( B ) ) => ( v4_pre_topc @ D @ C ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.51    (~( ![A:$i]:
% 0.20/0.51        ( ( l1_pre_topc @ A ) =>
% 0.20/0.51          ( ![B:$i]:
% 0.20/0.51            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.51              ( ![C:$i]:
% 0.20/0.51                ( ( m1_pre_topc @ C @ A ) =>
% 0.20/0.51                  ( ( v4_pre_topc @ B @ A ) =>
% 0.20/0.51                    ( ![D:$i]:
% 0.20/0.51                      ( ( m1_subset_1 @
% 0.20/0.51                          D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ C ) ) ) =>
% 0.20/0.51                        ( ( ( D ) = ( B ) ) => ( v4_pre_topc @ D @ C ) ) ) ) ) ) ) ) ) ) )),
% 0.20/0.51    inference('cnf.neg', [status(esa)], [t34_tops_2])).
% 0.20/0.51  thf('0', plain, (~ (v4_pre_topc @ sk_D_1 @ sk_C)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('1', plain, (((sk_D_1) = (sk_B))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('2', plain, (~ (v4_pre_topc @ sk_B @ sk_C)),
% 0.20/0.51      inference('demod', [status(thm)], ['0', '1'])).
% 0.20/0.51  thf(d3_struct_0, axiom,
% 0.20/0.51    (![A:$i]:
% 0.20/0.51     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.20/0.51  thf('3', plain,
% 0.20/0.51      (![X10 : $i]:
% 0.20/0.51         (((k2_struct_0 @ X10) = (u1_struct_0 @ X10)) | ~ (l1_struct_0 @ X10))),
% 0.20/0.51      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.20/0.51  thf('4', plain,
% 0.20/0.51      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('5', plain,
% 0.20/0.51      (![X10 : $i]:
% 0.20/0.51         (((k2_struct_0 @ X10) = (u1_struct_0 @ X10)) | ~ (l1_struct_0 @ X10))),
% 0.20/0.51      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.20/0.51  thf('6', plain,
% 0.20/0.51      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_C)))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('7', plain, (((sk_D_1) = (sk_B))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('8', plain,
% 0.20/0.51      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_C)))),
% 0.20/0.51      inference('demod', [status(thm)], ['6', '7'])).
% 0.20/0.51  thf(t3_subset, axiom,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.20/0.51  thf('9', plain,
% 0.20/0.51      (![X7 : $i, X8 : $i]:
% 0.20/0.51         ((r1_tarski @ X7 @ X8) | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8)))),
% 0.20/0.51      inference('cnf', [status(esa)], [t3_subset])).
% 0.20/0.51  thf('10', plain, ((r1_tarski @ sk_B @ (u1_struct_0 @ sk_C))),
% 0.20/0.51      inference('sup-', [status(thm)], ['8', '9'])).
% 0.20/0.51  thf(t28_xboole_1, axiom,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.20/0.51  thf('11', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]:
% 0.20/0.51         (((k3_xboole_0 @ X0 @ X1) = (X0)) | ~ (r1_tarski @ X0 @ X1))),
% 0.20/0.51      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.20/0.51  thf('12', plain, (((k3_xboole_0 @ sk_B @ (u1_struct_0 @ sk_C)) = (sk_B))),
% 0.20/0.51      inference('sup-', [status(thm)], ['10', '11'])).
% 0.20/0.51  thf('13', plain,
% 0.20/0.51      ((((k3_xboole_0 @ sk_B @ (k2_struct_0 @ sk_C)) = (sk_B))
% 0.20/0.51        | ~ (l1_struct_0 @ sk_C))),
% 0.20/0.51      inference('sup+', [status(thm)], ['5', '12'])).
% 0.20/0.51  thf('14', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf(dt_m1_pre_topc, axiom,
% 0.20/0.51    (![A:$i]:
% 0.20/0.51     ( ( l1_pre_topc @ A ) =>
% 0.20/0.51       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.20/0.51  thf('15', plain,
% 0.20/0.51      (![X12 : $i, X13 : $i]:
% 0.20/0.51         (~ (m1_pre_topc @ X12 @ X13)
% 0.20/0.51          | (l1_pre_topc @ X12)
% 0.20/0.51          | ~ (l1_pre_topc @ X13))),
% 0.20/0.51      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.20/0.51  thf('16', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_C))),
% 0.20/0.51      inference('sup-', [status(thm)], ['14', '15'])).
% 0.20/0.51  thf('17', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('18', plain, ((l1_pre_topc @ sk_C)),
% 0.20/0.51      inference('demod', [status(thm)], ['16', '17'])).
% 0.20/0.51  thf(dt_l1_pre_topc, axiom,
% 0.20/0.51    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.20/0.51  thf('19', plain,
% 0.20/0.51      (![X11 : $i]: ((l1_struct_0 @ X11) | ~ (l1_pre_topc @ X11))),
% 0.20/0.51      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.20/0.51  thf('20', plain, ((l1_struct_0 @ sk_C)),
% 0.20/0.51      inference('sup-', [status(thm)], ['18', '19'])).
% 0.20/0.51  thf('21', plain, (((k3_xboole_0 @ sk_B @ (k2_struct_0 @ sk_C)) = (sk_B))),
% 0.20/0.51      inference('demod', [status(thm)], ['13', '20'])).
% 0.20/0.51  thf('22', plain,
% 0.20/0.51      (![X10 : $i]:
% 0.20/0.51         (((k2_struct_0 @ X10) = (u1_struct_0 @ X10)) | ~ (l1_struct_0 @ X10))),
% 0.20/0.51      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.20/0.51  thf(t43_pre_topc, axiom,
% 0.20/0.51    (![A:$i]:
% 0.20/0.51     ( ( l1_pre_topc @ A ) =>
% 0.20/0.51       ( ![B:$i]:
% 0.20/0.51         ( ( m1_pre_topc @ B @ A ) =>
% 0.20/0.51           ( ![C:$i]:
% 0.20/0.51             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.20/0.51               ( ( v4_pre_topc @ C @ B ) <=>
% 0.20/0.51                 ( ?[D:$i]:
% 0.20/0.51                   ( ( ( k9_subset_1 @
% 0.20/0.51                         ( u1_struct_0 @ B ) @ D @ ( k2_struct_0 @ B ) ) =
% 0.20/0.51                       ( C ) ) & 
% 0.20/0.51                     ( v4_pre_topc @ D @ A ) & 
% 0.20/0.51                     ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.51  thf('23', plain,
% 0.20/0.51      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.20/0.51         (~ (m1_pre_topc @ X14 @ X15)
% 0.20/0.51          | ((k9_subset_1 @ (u1_struct_0 @ X14) @ X17 @ (k2_struct_0 @ X14))
% 0.20/0.51              != (X16))
% 0.20/0.51          | ~ (v4_pre_topc @ X17 @ X15)
% 0.20/0.51          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.20/0.51          | (v4_pre_topc @ X16 @ X14)
% 0.20/0.51          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.20/0.51          | ~ (l1_pre_topc @ X15))),
% 0.20/0.51      inference('cnf', [status(esa)], [t43_pre_topc])).
% 0.20/0.51  thf('24', plain,
% 0.20/0.51      (![X14 : $i, X15 : $i, X17 : $i]:
% 0.20/0.51         (~ (l1_pre_topc @ X15)
% 0.20/0.51          | ~ (m1_subset_1 @ 
% 0.20/0.51               (k9_subset_1 @ (u1_struct_0 @ X14) @ X17 @ (k2_struct_0 @ X14)) @ 
% 0.20/0.51               (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.20/0.51          | (v4_pre_topc @ 
% 0.20/0.51             (k9_subset_1 @ (u1_struct_0 @ X14) @ X17 @ (k2_struct_0 @ X14)) @ 
% 0.20/0.51             X14)
% 0.20/0.51          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.20/0.51          | ~ (v4_pre_topc @ X17 @ X15)
% 0.20/0.51          | ~ (m1_pre_topc @ X14 @ X15))),
% 0.20/0.51      inference('simplify', [status(thm)], ['23'])).
% 0.20/0.51  thf('25', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.51         (~ (m1_subset_1 @ 
% 0.20/0.51             (k9_subset_1 @ (k2_struct_0 @ X0) @ X1 @ (k2_struct_0 @ X0)) @ 
% 0.20/0.51             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.20/0.51          | ~ (l1_struct_0 @ X0)
% 0.20/0.51          | ~ (m1_pre_topc @ X0 @ X2)
% 0.20/0.51          | ~ (v4_pre_topc @ X1 @ X2)
% 0.20/0.51          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X2)))
% 0.20/0.51          | (v4_pre_topc @ 
% 0.20/0.51             (k9_subset_1 @ (u1_struct_0 @ X0) @ X1 @ (k2_struct_0 @ X0)) @ X0)
% 0.20/0.51          | ~ (l1_pre_topc @ X2))),
% 0.20/0.51      inference('sup-', [status(thm)], ['22', '24'])).
% 0.20/0.51  thf(dt_k2_subset_1, axiom,
% 0.20/0.51    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.20/0.51  thf('26', plain,
% 0.20/0.51      (![X3 : $i]: (m1_subset_1 @ (k2_subset_1 @ X3) @ (k1_zfmisc_1 @ X3))),
% 0.20/0.51      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 0.20/0.51  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.20/0.51  thf('27', plain, (![X2 : $i]: ((k2_subset_1 @ X2) = (X2))),
% 0.20/0.51      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.20/0.51  thf('28', plain, (![X3 : $i]: (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X3))),
% 0.20/0.51      inference('demod', [status(thm)], ['26', '27'])).
% 0.20/0.51  thf(redefinition_k9_subset_1, axiom,
% 0.20/0.51    (![A:$i,B:$i,C:$i]:
% 0.20/0.51     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.51       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 0.20/0.51  thf('29', plain,
% 0.20/0.51      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.20/0.51         (((k9_subset_1 @ X6 @ X4 @ X5) = (k3_xboole_0 @ X4 @ X5))
% 0.20/0.51          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6)))),
% 0.20/0.51      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 0.20/0.51  thf('30', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]:
% 0.20/0.51         ((k9_subset_1 @ X0 @ X1 @ X0) = (k3_xboole_0 @ X1 @ X0))),
% 0.20/0.51      inference('sup-', [status(thm)], ['28', '29'])).
% 0.20/0.51  thf('31', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.51         (~ (m1_subset_1 @ (k3_xboole_0 @ X1 @ (k2_struct_0 @ X0)) @ 
% 0.20/0.51             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.20/0.51          | ~ (l1_struct_0 @ X0)
% 0.20/0.51          | ~ (m1_pre_topc @ X0 @ X2)
% 0.20/0.51          | ~ (v4_pre_topc @ X1 @ X2)
% 0.20/0.51          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X2)))
% 0.20/0.51          | (v4_pre_topc @ 
% 0.20/0.51             (k9_subset_1 @ (u1_struct_0 @ X0) @ X1 @ (k2_struct_0 @ X0)) @ X0)
% 0.20/0.51          | ~ (l1_pre_topc @ X2))),
% 0.20/0.51      inference('demod', [status(thm)], ['25', '30'])).
% 0.20/0.51  thf('32', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         (~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_C)))
% 0.20/0.51          | ~ (l1_pre_topc @ X0)
% 0.20/0.51          | (v4_pre_topc @ 
% 0.20/0.51             (k9_subset_1 @ (u1_struct_0 @ sk_C) @ sk_B @ (k2_struct_0 @ sk_C)) @ 
% 0.20/0.51             sk_C)
% 0.20/0.51          | ~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.20/0.51          | ~ (v4_pre_topc @ sk_B @ X0)
% 0.20/0.51          | ~ (m1_pre_topc @ sk_C @ X0)
% 0.20/0.51          | ~ (l1_struct_0 @ sk_C))),
% 0.20/0.51      inference('sup-', [status(thm)], ['21', '31'])).
% 0.20/0.51  thf('33', plain,
% 0.20/0.51      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_C)))),
% 0.20/0.51      inference('demod', [status(thm)], ['6', '7'])).
% 0.20/0.51  thf('34', plain, ((l1_struct_0 @ sk_C)),
% 0.20/0.51      inference('sup-', [status(thm)], ['18', '19'])).
% 0.20/0.51  thf('35', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         (~ (l1_pre_topc @ X0)
% 0.20/0.51          | (v4_pre_topc @ 
% 0.20/0.51             (k9_subset_1 @ (u1_struct_0 @ sk_C) @ sk_B @ (k2_struct_0 @ sk_C)) @ 
% 0.20/0.51             sk_C)
% 0.20/0.51          | ~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.20/0.51          | ~ (v4_pre_topc @ sk_B @ X0)
% 0.20/0.51          | ~ (m1_pre_topc @ sk_C @ X0))),
% 0.20/0.51      inference('demod', [status(thm)], ['32', '33', '34'])).
% 0.20/0.51  thf('36', plain,
% 0.20/0.51      ((~ (m1_pre_topc @ sk_C @ sk_A)
% 0.20/0.51        | ~ (v4_pre_topc @ sk_B @ sk_A)
% 0.20/0.51        | (v4_pre_topc @ 
% 0.20/0.51           (k9_subset_1 @ (u1_struct_0 @ sk_C) @ sk_B @ (k2_struct_0 @ sk_C)) @ 
% 0.20/0.51           sk_C)
% 0.20/0.51        | ~ (l1_pre_topc @ sk_A))),
% 0.20/0.51      inference('sup-', [status(thm)], ['4', '35'])).
% 0.20/0.51  thf('37', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('38', plain, ((v4_pre_topc @ sk_B @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('39', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('40', plain,
% 0.20/0.51      ((v4_pre_topc @ 
% 0.20/0.51        (k9_subset_1 @ (u1_struct_0 @ sk_C) @ sk_B @ (k2_struct_0 @ sk_C)) @ 
% 0.20/0.51        sk_C)),
% 0.20/0.51      inference('demod', [status(thm)], ['36', '37', '38', '39'])).
% 0.20/0.51  thf('41', plain,
% 0.20/0.51      (((v4_pre_topc @ 
% 0.20/0.51         (k9_subset_1 @ (k2_struct_0 @ sk_C) @ sk_B @ (k2_struct_0 @ sk_C)) @ 
% 0.20/0.51         sk_C)
% 0.20/0.51        | ~ (l1_struct_0 @ sk_C))),
% 0.20/0.51      inference('sup+', [status(thm)], ['3', '40'])).
% 0.20/0.51  thf('42', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]:
% 0.20/0.51         ((k9_subset_1 @ X0 @ X1 @ X0) = (k3_xboole_0 @ X1 @ X0))),
% 0.20/0.51      inference('sup-', [status(thm)], ['28', '29'])).
% 0.20/0.51  thf('43', plain, (((k3_xboole_0 @ sk_B @ (k2_struct_0 @ sk_C)) = (sk_B))),
% 0.20/0.51      inference('demod', [status(thm)], ['13', '20'])).
% 0.20/0.51  thf('44', plain, ((l1_struct_0 @ sk_C)),
% 0.20/0.51      inference('sup-', [status(thm)], ['18', '19'])).
% 0.20/0.51  thf('45', plain, ((v4_pre_topc @ sk_B @ sk_C)),
% 0.20/0.51      inference('demod', [status(thm)], ['41', '42', '43', '44'])).
% 0.20/0.51  thf('46', plain, ($false), inference('demod', [status(thm)], ['2', '45'])).
% 0.20/0.51  
% 0.20/0.51  % SZS output end Refutation
% 0.20/0.51  
% 0.20/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
