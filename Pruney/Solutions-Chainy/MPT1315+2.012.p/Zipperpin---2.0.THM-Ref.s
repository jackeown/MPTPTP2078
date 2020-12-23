%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.zj6X1mpUU1

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:05:35 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 161 expanded)
%              Number of leaves         :   24 (  58 expanded)
%              Depth                    :   15
%              Number of atoms          :  522 (1697 expanded)
%              Number of equality atoms :   20 (  70 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

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
    ! [X11: $i] :
      ( ( ( k2_struct_0 @ X11 )
        = ( u1_struct_0 @ X11 ) )
      | ~ ( l1_struct_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('4',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    ! [X11: $i] :
      ( ( ( k2_struct_0 @ X11 )
        = ( u1_struct_0 @ X11 ) )
      | ~ ( l1_struct_0 @ X11 ) ) ),
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

thf('9',plain,
    ( ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_C ) ) )
    | ~ ( l1_struct_0 @ sk_C ) ),
    inference('sup+',[status(thm)],['5','8'])).

thf('10',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('11',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( m1_pre_topc @ X13 @ X14 )
      | ( l1_pre_topc @ X13 )
      | ~ ( l1_pre_topc @ X14 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('12',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_C ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['12','13'])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('15',plain,(
    ! [X12: $i] :
      ( ( l1_struct_0 @ X12 )
      | ~ ( l1_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('16',plain,(
    l1_struct_0 @ sk_C ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['9','16'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('18',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_tarski @ X8 @ X9 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('19',plain,(
    r1_tarski @ sk_B @ ( k2_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('20',plain,(
    ! [X3: $i,X4: $i] :
      ( ( ( k3_xboole_0 @ X3 @ X4 )
        = X3 )
      | ~ ( r1_tarski @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('21',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k2_struct_0 @ sk_C ) )
    = sk_B ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X11: $i] :
      ( ( ( k2_struct_0 @ X11 )
        = ( u1_struct_0 @ X11 ) )
      | ~ ( l1_struct_0 @ X11 ) ) ),
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
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_pre_topc @ X15 @ X16 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X15 ) @ X18 @ ( k2_struct_0 @ X15 ) )
       != X17 )
      | ~ ( v4_pre_topc @ X18 @ X16 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ( v4_pre_topc @ X17 @ X15 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ~ ( l1_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[t43_pre_topc])).

thf('24',plain,(
    ! [X15: $i,X16: $i,X18: $i] :
      ( ~ ( l1_pre_topc @ X16 )
      | ~ ( m1_subset_1 @ ( k9_subset_1 @ ( u1_struct_0 @ X15 ) @ X18 @ ( k2_struct_0 @ X15 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ( v4_pre_topc @ ( k9_subset_1 @ ( u1_struct_0 @ X15 ) @ X18 @ ( k2_struct_0 @ X15 ) ) @ X15 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( v4_pre_topc @ X18 @ X16 )
      | ~ ( m1_pre_topc @ X15 @ X16 ) ) ),
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

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('27',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    ! [X8: $i,X10: $i] :
      ( ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X10 ) )
      | ~ ( r1_tarski @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('29',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf(redefinition_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k3_xboole_0 @ B @ C ) ) ) )).

thf('30',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( ( k9_subset_1 @ X7 @ X5 @ X6 )
        = ( k3_xboole_0 @ X5 @ X6 ) )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_subset_1 @ X0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ ( k3_xboole_0 @ X1 @ ( k2_struct_0 @ X0 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X2 )
      | ~ ( v4_pre_topc @ X1 @ X2 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X2 ) ) )
      | ( v4_pre_topc @ ( k9_subset_1 @ ( u1_struct_0 @ X0 ) @ X1 @ ( k2_struct_0 @ X0 ) ) @ X0 )
      | ~ ( l1_pre_topc @ X2 ) ) ),
    inference(demod,[status(thm)],['25','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ( v4_pre_topc @ ( k9_subset_1 @ ( u1_struct_0 @ sk_C ) @ sk_B @ ( k2_struct_0 @ sk_C ) ) @ sk_C )
      | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( v4_pre_topc @ sk_B @ X0 )
      | ~ ( m1_pre_topc @ sk_C @ X0 )
      | ~ ( l1_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['21','32'])).

thf('34',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('35',plain,(
    l1_struct_0 @ sk_C ),
    inference('sup-',[status(thm)],['14','15'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v4_pre_topc @ ( k9_subset_1 @ ( u1_struct_0 @ sk_C ) @ sk_B @ ( k2_struct_0 @ sk_C ) ) @ sk_C )
      | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( v4_pre_topc @ sk_B @ X0 )
      | ~ ( m1_pre_topc @ sk_C @ X0 ) ) ),
    inference(demod,[status(thm)],['33','34','35'])).

thf('37',plain,
    ( ~ ( m1_pre_topc @ sk_C @ sk_A )
    | ~ ( v4_pre_topc @ sk_B @ sk_A )
    | ( v4_pre_topc @ ( k9_subset_1 @ ( u1_struct_0 @ sk_C ) @ sk_B @ ( k2_struct_0 @ sk_C ) ) @ sk_C )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['4','36'])).

thf('38',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    v4_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    v4_pre_topc @ ( k9_subset_1 @ ( u1_struct_0 @ sk_C ) @ sk_B @ ( k2_struct_0 @ sk_C ) ) @ sk_C ),
    inference(demod,[status(thm)],['37','38','39','40'])).

thf('42',plain,
    ( ( v4_pre_topc @ ( k9_subset_1 @ ( k2_struct_0 @ sk_C ) @ sk_B @ ( k2_struct_0 @ sk_C ) ) @ sk_C )
    | ~ ( l1_struct_0 @ sk_C ) ),
    inference('sup+',[status(thm)],['3','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_subset_1 @ X0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('44',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k2_struct_0 @ sk_C ) )
    = sk_B ),
    inference('sup-',[status(thm)],['19','20'])).

thf('45',plain,(
    l1_struct_0 @ sk_C ),
    inference('sup-',[status(thm)],['14','15'])).

thf('46',plain,(
    v4_pre_topc @ sk_B @ sk_C ),
    inference(demod,[status(thm)],['42','43','44','45'])).

thf('47',plain,(
    $false ),
    inference(demod,[status(thm)],['2','46'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.zj6X1mpUU1
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:30:11 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.50  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.50  % Solved by: fo/fo7.sh
% 0.21/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.50  % done 96 iterations in 0.047s
% 0.21/0.50  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.50  % SZS output start Refutation
% 0.21/0.50  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.21/0.50  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.50  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.50  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.50  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.21/0.50  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.21/0.50  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.50  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.50  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.21/0.50  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.21/0.50  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.21/0.50  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.50  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.21/0.50  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.21/0.50  thf(t34_tops_2, conjecture,
% 0.21/0.50    (![A:$i]:
% 0.21/0.50     ( ( l1_pre_topc @ A ) =>
% 0.21/0.50       ( ![B:$i]:
% 0.21/0.50         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.50           ( ![C:$i]:
% 0.21/0.50             ( ( m1_pre_topc @ C @ A ) =>
% 0.21/0.50               ( ( v4_pre_topc @ B @ A ) =>
% 0.21/0.50                 ( ![D:$i]:
% 0.21/0.50                   ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ C ) ) ) =>
% 0.21/0.50                     ( ( ( D ) = ( B ) ) => ( v4_pre_topc @ D @ C ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.50    (~( ![A:$i]:
% 0.21/0.50        ( ( l1_pre_topc @ A ) =>
% 0.21/0.50          ( ![B:$i]:
% 0.21/0.50            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.50              ( ![C:$i]:
% 0.21/0.50                ( ( m1_pre_topc @ C @ A ) =>
% 0.21/0.50                  ( ( v4_pre_topc @ B @ A ) =>
% 0.21/0.50                    ( ![D:$i]:
% 0.21/0.50                      ( ( m1_subset_1 @
% 0.21/0.50                          D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ C ) ) ) =>
% 0.21/0.50                        ( ( ( D ) = ( B ) ) => ( v4_pre_topc @ D @ C ) ) ) ) ) ) ) ) ) ) )),
% 0.21/0.50    inference('cnf.neg', [status(esa)], [t34_tops_2])).
% 0.21/0.50  thf('0', plain, (~ (v4_pre_topc @ sk_D_1 @ sk_C)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('1', plain, (((sk_D_1) = (sk_B))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('2', plain, (~ (v4_pre_topc @ sk_B @ sk_C)),
% 0.21/0.50      inference('demod', [status(thm)], ['0', '1'])).
% 0.21/0.50  thf(d3_struct_0, axiom,
% 0.21/0.50    (![A:$i]:
% 0.21/0.50     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.21/0.50  thf('3', plain,
% 0.21/0.50      (![X11 : $i]:
% 0.21/0.50         (((k2_struct_0 @ X11) = (u1_struct_0 @ X11)) | ~ (l1_struct_0 @ X11))),
% 0.21/0.50      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.21/0.50  thf('4', plain,
% 0.21/0.50      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('5', plain,
% 0.21/0.50      (![X11 : $i]:
% 0.21/0.50         (((k2_struct_0 @ X11) = (u1_struct_0 @ X11)) | ~ (l1_struct_0 @ X11))),
% 0.21/0.50      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.21/0.50  thf('6', plain,
% 0.21/0.50      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_C)))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('7', plain, (((sk_D_1) = (sk_B))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('8', plain,
% 0.21/0.50      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_C)))),
% 0.21/0.50      inference('demod', [status(thm)], ['6', '7'])).
% 0.21/0.50  thf('9', plain,
% 0.21/0.50      (((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_C)))
% 0.21/0.50        | ~ (l1_struct_0 @ sk_C))),
% 0.21/0.50      inference('sup+', [status(thm)], ['5', '8'])).
% 0.21/0.50  thf('10', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf(dt_m1_pre_topc, axiom,
% 0.21/0.50    (![A:$i]:
% 0.21/0.50     ( ( l1_pre_topc @ A ) =>
% 0.21/0.50       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.21/0.50  thf('11', plain,
% 0.21/0.50      (![X13 : $i, X14 : $i]:
% 0.21/0.50         (~ (m1_pre_topc @ X13 @ X14)
% 0.21/0.50          | (l1_pre_topc @ X13)
% 0.21/0.50          | ~ (l1_pre_topc @ X14))),
% 0.21/0.50      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.21/0.50  thf('12', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_C))),
% 0.21/0.50      inference('sup-', [status(thm)], ['10', '11'])).
% 0.21/0.50  thf('13', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('14', plain, ((l1_pre_topc @ sk_C)),
% 0.21/0.50      inference('demod', [status(thm)], ['12', '13'])).
% 0.21/0.50  thf(dt_l1_pre_topc, axiom,
% 0.21/0.50    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.21/0.50  thf('15', plain,
% 0.21/0.50      (![X12 : $i]: ((l1_struct_0 @ X12) | ~ (l1_pre_topc @ X12))),
% 0.21/0.50      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.21/0.50  thf('16', plain, ((l1_struct_0 @ sk_C)),
% 0.21/0.50      inference('sup-', [status(thm)], ['14', '15'])).
% 0.21/0.50  thf('17', plain,
% 0.21/0.50      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_C)))),
% 0.21/0.50      inference('demod', [status(thm)], ['9', '16'])).
% 0.21/0.50  thf(t3_subset, axiom,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.21/0.50  thf('18', plain,
% 0.21/0.50      (![X8 : $i, X9 : $i]:
% 0.21/0.50         ((r1_tarski @ X8 @ X9) | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9)))),
% 0.21/0.50      inference('cnf', [status(esa)], [t3_subset])).
% 0.21/0.50  thf('19', plain, ((r1_tarski @ sk_B @ (k2_struct_0 @ sk_C))),
% 0.21/0.50      inference('sup-', [status(thm)], ['17', '18'])).
% 0.21/0.50  thf(t28_xboole_1, axiom,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.21/0.50  thf('20', plain,
% 0.21/0.50      (![X3 : $i, X4 : $i]:
% 0.21/0.50         (((k3_xboole_0 @ X3 @ X4) = (X3)) | ~ (r1_tarski @ X3 @ X4))),
% 0.21/0.50      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.21/0.50  thf('21', plain, (((k3_xboole_0 @ sk_B @ (k2_struct_0 @ sk_C)) = (sk_B))),
% 0.21/0.50      inference('sup-', [status(thm)], ['19', '20'])).
% 0.21/0.50  thf('22', plain,
% 0.21/0.50      (![X11 : $i]:
% 0.21/0.50         (((k2_struct_0 @ X11) = (u1_struct_0 @ X11)) | ~ (l1_struct_0 @ X11))),
% 0.21/0.50      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.21/0.50  thf(t43_pre_topc, axiom,
% 0.21/0.50    (![A:$i]:
% 0.21/0.50     ( ( l1_pre_topc @ A ) =>
% 0.21/0.50       ( ![B:$i]:
% 0.21/0.50         ( ( m1_pre_topc @ B @ A ) =>
% 0.21/0.50           ( ![C:$i]:
% 0.21/0.50             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.21/0.50               ( ( v4_pre_topc @ C @ B ) <=>
% 0.21/0.50                 ( ?[D:$i]:
% 0.21/0.50                   ( ( ( k9_subset_1 @
% 0.21/0.50                         ( u1_struct_0 @ B ) @ D @ ( k2_struct_0 @ B ) ) =
% 0.21/0.50                       ( C ) ) & 
% 0.21/0.50                     ( v4_pre_topc @ D @ A ) & 
% 0.21/0.50                     ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.50  thf('23', plain,
% 0.21/0.50      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.21/0.50         (~ (m1_pre_topc @ X15 @ X16)
% 0.21/0.50          | ((k9_subset_1 @ (u1_struct_0 @ X15) @ X18 @ (k2_struct_0 @ X15))
% 0.21/0.50              != (X17))
% 0.21/0.50          | ~ (v4_pre_topc @ X18 @ X16)
% 0.21/0.50          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.21/0.50          | (v4_pre_topc @ X17 @ X15)
% 0.21/0.50          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.21/0.50          | ~ (l1_pre_topc @ X16))),
% 0.21/0.50      inference('cnf', [status(esa)], [t43_pre_topc])).
% 0.21/0.50  thf('24', plain,
% 0.21/0.50      (![X15 : $i, X16 : $i, X18 : $i]:
% 0.21/0.50         (~ (l1_pre_topc @ X16)
% 0.21/0.50          | ~ (m1_subset_1 @ 
% 0.21/0.50               (k9_subset_1 @ (u1_struct_0 @ X15) @ X18 @ (k2_struct_0 @ X15)) @ 
% 0.21/0.50               (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.21/0.50          | (v4_pre_topc @ 
% 0.21/0.50             (k9_subset_1 @ (u1_struct_0 @ X15) @ X18 @ (k2_struct_0 @ X15)) @ 
% 0.21/0.50             X15)
% 0.21/0.50          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.21/0.50          | ~ (v4_pre_topc @ X18 @ X16)
% 0.21/0.50          | ~ (m1_pre_topc @ X15 @ X16))),
% 0.21/0.50      inference('simplify', [status(thm)], ['23'])).
% 0.21/0.50  thf('25', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.50         (~ (m1_subset_1 @ 
% 0.21/0.50             (k9_subset_1 @ (k2_struct_0 @ X0) @ X1 @ (k2_struct_0 @ X0)) @ 
% 0.21/0.50             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.21/0.50          | ~ (l1_struct_0 @ X0)
% 0.21/0.50          | ~ (m1_pre_topc @ X0 @ X2)
% 0.21/0.50          | ~ (v4_pre_topc @ X1 @ X2)
% 0.21/0.50          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X2)))
% 0.21/0.50          | (v4_pre_topc @ 
% 0.21/0.50             (k9_subset_1 @ (u1_struct_0 @ X0) @ X1 @ (k2_struct_0 @ X0)) @ X0)
% 0.21/0.50          | ~ (l1_pre_topc @ X2))),
% 0.21/0.50      inference('sup-', [status(thm)], ['22', '24'])).
% 0.21/0.50  thf(d10_xboole_0, axiom,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.21/0.50  thf('26', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.21/0.50      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.21/0.50  thf('27', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.21/0.50      inference('simplify', [status(thm)], ['26'])).
% 0.21/0.50  thf('28', plain,
% 0.21/0.50      (![X8 : $i, X10 : $i]:
% 0.21/0.50         ((m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X10)) | ~ (r1_tarski @ X8 @ X10))),
% 0.21/0.50      inference('cnf', [status(esa)], [t3_subset])).
% 0.21/0.50  thf('29', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.21/0.50      inference('sup-', [status(thm)], ['27', '28'])).
% 0.21/0.50  thf(redefinition_k9_subset_1, axiom,
% 0.21/0.50    (![A:$i,B:$i,C:$i]:
% 0.21/0.50     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.50       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 0.21/0.50  thf('30', plain,
% 0.21/0.50      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.21/0.50         (((k9_subset_1 @ X7 @ X5 @ X6) = (k3_xboole_0 @ X5 @ X6))
% 0.21/0.50          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7)))),
% 0.21/0.50      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 0.21/0.50  thf('31', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]:
% 0.21/0.50         ((k9_subset_1 @ X0 @ X1 @ X0) = (k3_xboole_0 @ X1 @ X0))),
% 0.21/0.50      inference('sup-', [status(thm)], ['29', '30'])).
% 0.21/0.50  thf('32', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.50         (~ (m1_subset_1 @ (k3_xboole_0 @ X1 @ (k2_struct_0 @ X0)) @ 
% 0.21/0.50             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.21/0.50          | ~ (l1_struct_0 @ X0)
% 0.21/0.50          | ~ (m1_pre_topc @ X0 @ X2)
% 0.21/0.50          | ~ (v4_pre_topc @ X1 @ X2)
% 0.21/0.50          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X2)))
% 0.21/0.50          | (v4_pre_topc @ 
% 0.21/0.50             (k9_subset_1 @ (u1_struct_0 @ X0) @ X1 @ (k2_struct_0 @ X0)) @ X0)
% 0.21/0.50          | ~ (l1_pre_topc @ X2))),
% 0.21/0.50      inference('demod', [status(thm)], ['25', '31'])).
% 0.21/0.50  thf('33', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         (~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_C)))
% 0.21/0.50          | ~ (l1_pre_topc @ X0)
% 0.21/0.50          | (v4_pre_topc @ 
% 0.21/0.50             (k9_subset_1 @ (u1_struct_0 @ sk_C) @ sk_B @ (k2_struct_0 @ sk_C)) @ 
% 0.21/0.50             sk_C)
% 0.21/0.50          | ~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.21/0.50          | ~ (v4_pre_topc @ sk_B @ X0)
% 0.21/0.50          | ~ (m1_pre_topc @ sk_C @ X0)
% 0.21/0.50          | ~ (l1_struct_0 @ sk_C))),
% 0.21/0.50      inference('sup-', [status(thm)], ['21', '32'])).
% 0.21/0.50  thf('34', plain,
% 0.21/0.50      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_C)))),
% 0.21/0.50      inference('demod', [status(thm)], ['6', '7'])).
% 0.21/0.50  thf('35', plain, ((l1_struct_0 @ sk_C)),
% 0.21/0.50      inference('sup-', [status(thm)], ['14', '15'])).
% 0.21/0.50  thf('36', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         (~ (l1_pre_topc @ X0)
% 0.21/0.50          | (v4_pre_topc @ 
% 0.21/0.50             (k9_subset_1 @ (u1_struct_0 @ sk_C) @ sk_B @ (k2_struct_0 @ sk_C)) @ 
% 0.21/0.50             sk_C)
% 0.21/0.50          | ~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.21/0.50          | ~ (v4_pre_topc @ sk_B @ X0)
% 0.21/0.50          | ~ (m1_pre_topc @ sk_C @ X0))),
% 0.21/0.50      inference('demod', [status(thm)], ['33', '34', '35'])).
% 0.21/0.50  thf('37', plain,
% 0.21/0.50      ((~ (m1_pre_topc @ sk_C @ sk_A)
% 0.21/0.50        | ~ (v4_pre_topc @ sk_B @ sk_A)
% 0.21/0.50        | (v4_pre_topc @ 
% 0.21/0.50           (k9_subset_1 @ (u1_struct_0 @ sk_C) @ sk_B @ (k2_struct_0 @ sk_C)) @ 
% 0.21/0.50           sk_C)
% 0.21/0.50        | ~ (l1_pre_topc @ sk_A))),
% 0.21/0.50      inference('sup-', [status(thm)], ['4', '36'])).
% 0.21/0.50  thf('38', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('39', plain, ((v4_pre_topc @ sk_B @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('40', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('41', plain,
% 0.21/0.50      ((v4_pre_topc @ 
% 0.21/0.50        (k9_subset_1 @ (u1_struct_0 @ sk_C) @ sk_B @ (k2_struct_0 @ sk_C)) @ 
% 0.21/0.50        sk_C)),
% 0.21/0.50      inference('demod', [status(thm)], ['37', '38', '39', '40'])).
% 0.21/0.50  thf('42', plain,
% 0.21/0.50      (((v4_pre_topc @ 
% 0.21/0.50         (k9_subset_1 @ (k2_struct_0 @ sk_C) @ sk_B @ (k2_struct_0 @ sk_C)) @ 
% 0.21/0.50         sk_C)
% 0.21/0.50        | ~ (l1_struct_0 @ sk_C))),
% 0.21/0.50      inference('sup+', [status(thm)], ['3', '41'])).
% 0.21/0.50  thf('43', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]:
% 0.21/0.50         ((k9_subset_1 @ X0 @ X1 @ X0) = (k3_xboole_0 @ X1 @ X0))),
% 0.21/0.50      inference('sup-', [status(thm)], ['29', '30'])).
% 0.21/0.50  thf('44', plain, (((k3_xboole_0 @ sk_B @ (k2_struct_0 @ sk_C)) = (sk_B))),
% 0.21/0.50      inference('sup-', [status(thm)], ['19', '20'])).
% 0.21/0.50  thf('45', plain, ((l1_struct_0 @ sk_C)),
% 0.21/0.50      inference('sup-', [status(thm)], ['14', '15'])).
% 0.21/0.50  thf('46', plain, ((v4_pre_topc @ sk_B @ sk_C)),
% 0.21/0.50      inference('demod', [status(thm)], ['42', '43', '44', '45'])).
% 0.21/0.50  thf('47', plain, ($false), inference('demod', [status(thm)], ['2', '46'])).
% 0.21/0.50  
% 0.21/0.50  % SZS output end Refutation
% 0.21/0.50  
% 0.21/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
