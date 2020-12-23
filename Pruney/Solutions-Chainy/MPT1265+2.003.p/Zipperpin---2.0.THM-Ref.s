%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ub0ZMtO1kF

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:04:10 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 105 expanded)
%              Number of leaves         :   27 (  44 expanded)
%              Depth                    :   10
%              Number of atoms          :  561 (1437 expanded)
%              Number of equality atoms :   31 (  34 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v1_tops_1_type,type,(
    v1_tops_1: $i > $i > $o )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

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
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( ( k9_subset_1 @ X12 @ X10 @ X11 )
        = ( k3_xboole_0 @ X10 @ X11 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
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
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( v3_pre_topc @ X19 @ X18 )
      | ( ( k2_pre_topc @ X18 @ X19 )
        = ( k2_pre_topc @ X18 @ ( k9_subset_1 @ ( u1_struct_0 @ X18 ) @ X19 @ X17 ) ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( v1_tops_1 @ X17 @ X18 )
      | ~ ( l1_pre_topc @ X18 )
      | ~ ( v2_pre_topc @ X18 ) ) ),
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
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( ( k9_subset_1 @ X12 @ X10 @ X11 )
        = ( k3_xboole_0 @ X10 @ X11 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
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
    ! [X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( v1_tops_1 @ X15 @ X16 )
      | ( ( k2_pre_topc @ X16 @ X15 )
        = ( k2_struct_0 @ X16 ) )
      | ~ ( l1_pre_topc @ X16 ) ) ),
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

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('24',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k2_tarski @ X3 @ X2 )
      = ( k2_tarski @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('25',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X13 @ X14 ) )
      = ( k3_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X13 @ X14 ) )
      = ( k3_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( k2_pre_topc @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['16','17','23','28'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('31',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k7_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('32',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) )
      | ( m1_subset_1 @ ( k7_subset_1 @ X5 @ X4 @ X6 ) @ ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_subset_1])).

thf('33',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('35',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) )
      | ( ( k7_subset_1 @ X8 @ X7 @ X9 )
        = ( k4_xboole_0 @ X7 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['33','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['30','37'])).

thf('39',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ( ( k2_pre_topc @ X16 @ X15 )
       != ( k2_struct_0 @ X16 ) )
      | ( v1_tops_1 @ X15 @ X16 )
      | ~ ( l1_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[d3_tops_1])).

thf('40',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ( v1_tops_1 @ ( k3_xboole_0 @ sk_B @ X0 ) @ sk_A )
      | ( ( k2_pre_topc @ sk_A @ ( k3_xboole_0 @ sk_B @ X0 ) )
       != ( k2_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( v1_tops_1 @ ( k3_xboole_0 @ sk_B @ X0 ) @ sk_A )
      | ( ( k2_pre_topc @ sk_A @ ( k3_xboole_0 @ sk_B @ X0 ) )
       != ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,
    ( ( ( k2_struct_0 @ sk_A )
     != ( k2_struct_0 @ sk_A ) )
    | ( v1_tops_1 @ ( k3_xboole_0 @ sk_B @ sk_C ) @ sk_A ) ),
    inference('sup-',[status(thm)],['29','42'])).

thf('44',plain,(
    v1_tops_1 @ ( k3_xboole_0 @ sk_B @ sk_C ) @ sk_A ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,(
    $false ),
    inference(demod,[status(thm)],['4','44'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ub0ZMtO1kF
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:17:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.47  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.47  % Solved by: fo/fo7.sh
% 0.21/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.47  % done 116 iterations in 0.037s
% 0.21/0.47  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.47  % SZS output start Refutation
% 0.21/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.47  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.21/0.47  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.21/0.47  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.47  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.21/0.47  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.47  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.47  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.21/0.47  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.21/0.47  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.21/0.47  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.47  thf(v1_tops_1_type, type, v1_tops_1: $i > $i > $o).
% 0.21/0.47  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.21/0.47  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.21/0.47  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.47  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.21/0.47  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.21/0.47  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 0.21/0.47  thf(t82_tops_1, conjecture,
% 0.21/0.47    (![A:$i]:
% 0.21/0.47     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.47       ( ![B:$i]:
% 0.21/0.47         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.47           ( ![C:$i]:
% 0.21/0.47             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.47               ( ( ( v1_tops_1 @ B @ A ) & ( v1_tops_1 @ C @ A ) & 
% 0.21/0.47                   ( v3_pre_topc @ C @ A ) ) =>
% 0.21/0.47                 ( v1_tops_1 @
% 0.21/0.47                   ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ A ) ) ) ) ) ) ))).
% 0.21/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.47    (~( ![A:$i]:
% 0.21/0.47        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.47          ( ![B:$i]:
% 0.21/0.47            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.47              ( ![C:$i]:
% 0.21/0.47                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.47                  ( ( ( v1_tops_1 @ B @ A ) & ( v1_tops_1 @ C @ A ) & 
% 0.21/0.47                      ( v3_pre_topc @ C @ A ) ) =>
% 0.21/0.47                    ( v1_tops_1 @
% 0.21/0.47                      ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ A ) ) ) ) ) ) ) )),
% 0.21/0.47    inference('cnf.neg', [status(esa)], [t82_tops_1])).
% 0.21/0.47  thf('0', plain,
% 0.21/0.47      (~ (v1_tops_1 @ (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C) @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('1', plain,
% 0.21/0.47      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf(redefinition_k9_subset_1, axiom,
% 0.21/0.47    (![A:$i,B:$i,C:$i]:
% 0.21/0.47     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.47       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 0.21/0.47  thf('2', plain,
% 0.21/0.47      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.21/0.47         (((k9_subset_1 @ X12 @ X10 @ X11) = (k3_xboole_0 @ X10 @ X11))
% 0.21/0.47          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12)))),
% 0.21/0.47      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 0.21/0.47  thf('3', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_C)
% 0.21/0.47           = (k3_xboole_0 @ X0 @ sk_C))),
% 0.21/0.47      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.47  thf('4', plain, (~ (v1_tops_1 @ (k3_xboole_0 @ sk_B @ sk_C) @ sk_A)),
% 0.21/0.47      inference('demod', [status(thm)], ['0', '3'])).
% 0.21/0.47  thf('5', plain,
% 0.21/0.47      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('6', plain,
% 0.21/0.47      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf(t81_tops_1, axiom,
% 0.21/0.47    (![A:$i]:
% 0.21/0.47     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.47       ( ![B:$i]:
% 0.21/0.47         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.47           ( ( v1_tops_1 @ B @ A ) =>
% 0.21/0.47             ( ![C:$i]:
% 0.21/0.47               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.47                 ( ( v3_pre_topc @ C @ A ) =>
% 0.21/0.47                   ( ( k2_pre_topc @ A @ C ) =
% 0.21/0.47                     ( k2_pre_topc @
% 0.21/0.47                       A @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ C @ B ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.47  thf('7', plain,
% 0.21/0.47      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.21/0.47         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.21/0.47          | ~ (v3_pre_topc @ X19 @ X18)
% 0.21/0.47          | ((k2_pre_topc @ X18 @ X19)
% 0.21/0.47              = (k2_pre_topc @ X18 @ 
% 0.21/0.47                 (k9_subset_1 @ (u1_struct_0 @ X18) @ X19 @ X17)))
% 0.21/0.47          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.21/0.47          | ~ (v1_tops_1 @ X17 @ X18)
% 0.21/0.47          | ~ (l1_pre_topc @ X18)
% 0.21/0.47          | ~ (v2_pre_topc @ X18))),
% 0.21/0.47      inference('cnf', [status(esa)], [t81_tops_1])).
% 0.21/0.47  thf('8', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         (~ (v2_pre_topc @ sk_A)
% 0.21/0.47          | ~ (l1_pre_topc @ sk_A)
% 0.21/0.47          | ~ (v1_tops_1 @ sk_B @ sk_A)
% 0.21/0.47          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.47          | ((k2_pre_topc @ sk_A @ X0)
% 0.21/0.47              = (k2_pre_topc @ sk_A @ 
% 0.21/0.47                 (k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_B)))
% 0.21/0.47          | ~ (v3_pre_topc @ X0 @ sk_A))),
% 0.21/0.47      inference('sup-', [status(thm)], ['6', '7'])).
% 0.21/0.47  thf('9', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('10', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('11', plain, ((v1_tops_1 @ sk_B @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('12', plain,
% 0.21/0.47      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('13', plain,
% 0.21/0.47      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.21/0.47         (((k9_subset_1 @ X12 @ X10 @ X11) = (k3_xboole_0 @ X10 @ X11))
% 0.21/0.47          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12)))),
% 0.21/0.47      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 0.21/0.47  thf('14', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_B)
% 0.21/0.47           = (k3_xboole_0 @ X0 @ sk_B))),
% 0.21/0.47      inference('sup-', [status(thm)], ['12', '13'])).
% 0.21/0.47  thf('15', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.47          | ((k2_pre_topc @ sk_A @ X0)
% 0.21/0.47              = (k2_pre_topc @ sk_A @ (k3_xboole_0 @ X0 @ sk_B)))
% 0.21/0.47          | ~ (v3_pre_topc @ X0 @ sk_A))),
% 0.21/0.47      inference('demod', [status(thm)], ['8', '9', '10', '11', '14'])).
% 0.21/0.47  thf('16', plain,
% 0.21/0.47      ((~ (v3_pre_topc @ sk_C @ sk_A)
% 0.21/0.47        | ((k2_pre_topc @ sk_A @ sk_C)
% 0.21/0.47            = (k2_pre_topc @ sk_A @ (k3_xboole_0 @ sk_C @ sk_B))))),
% 0.21/0.47      inference('sup-', [status(thm)], ['5', '15'])).
% 0.21/0.47  thf('17', plain, ((v3_pre_topc @ sk_C @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('18', plain,
% 0.21/0.47      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf(d3_tops_1, axiom,
% 0.21/0.47    (![A:$i]:
% 0.21/0.47     ( ( l1_pre_topc @ A ) =>
% 0.21/0.47       ( ![B:$i]:
% 0.21/0.47         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.47           ( ( v1_tops_1 @ B @ A ) <=>
% 0.21/0.47             ( ( k2_pre_topc @ A @ B ) = ( k2_struct_0 @ A ) ) ) ) ) ))).
% 0.21/0.47  thf('19', plain,
% 0.21/0.47      (![X15 : $i, X16 : $i]:
% 0.21/0.47         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.21/0.47          | ~ (v1_tops_1 @ X15 @ X16)
% 0.21/0.47          | ((k2_pre_topc @ X16 @ X15) = (k2_struct_0 @ X16))
% 0.21/0.47          | ~ (l1_pre_topc @ X16))),
% 0.21/0.47      inference('cnf', [status(esa)], [d3_tops_1])).
% 0.21/0.47  thf('20', plain,
% 0.21/0.47      ((~ (l1_pre_topc @ sk_A)
% 0.21/0.47        | ((k2_pre_topc @ sk_A @ sk_C) = (k2_struct_0 @ sk_A))
% 0.21/0.47        | ~ (v1_tops_1 @ sk_C @ sk_A))),
% 0.21/0.47      inference('sup-', [status(thm)], ['18', '19'])).
% 0.21/0.47  thf('21', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('22', plain, ((v1_tops_1 @ sk_C @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('23', plain, (((k2_pre_topc @ sk_A @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.21/0.47      inference('demod', [status(thm)], ['20', '21', '22'])).
% 0.21/0.47  thf(commutativity_k2_tarski, axiom,
% 0.21/0.47    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.21/0.47  thf('24', plain,
% 0.21/0.47      (![X2 : $i, X3 : $i]: ((k2_tarski @ X3 @ X2) = (k2_tarski @ X2 @ X3))),
% 0.21/0.47      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.21/0.47  thf(t12_setfam_1, axiom,
% 0.21/0.47    (![A:$i,B:$i]:
% 0.21/0.47     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.21/0.47  thf('25', plain,
% 0.21/0.47      (![X13 : $i, X14 : $i]:
% 0.21/0.47         ((k1_setfam_1 @ (k2_tarski @ X13 @ X14)) = (k3_xboole_0 @ X13 @ X14))),
% 0.21/0.47      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.21/0.47  thf('26', plain,
% 0.21/0.47      (![X0 : $i, X1 : $i]:
% 0.21/0.47         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X0 @ X1))),
% 0.21/0.47      inference('sup+', [status(thm)], ['24', '25'])).
% 0.21/0.47  thf('27', plain,
% 0.21/0.47      (![X13 : $i, X14 : $i]:
% 0.21/0.47         ((k1_setfam_1 @ (k2_tarski @ X13 @ X14)) = (k3_xboole_0 @ X13 @ X14))),
% 0.21/0.47      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.21/0.47  thf('28', plain,
% 0.21/0.47      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.21/0.47      inference('sup+', [status(thm)], ['26', '27'])).
% 0.21/0.47  thf('29', plain,
% 0.21/0.47      (((k2_struct_0 @ sk_A)
% 0.21/0.47         = (k2_pre_topc @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C)))),
% 0.21/0.47      inference('demod', [status(thm)], ['16', '17', '23', '28'])).
% 0.21/0.47  thf(t48_xboole_1, axiom,
% 0.21/0.47    (![A:$i,B:$i]:
% 0.21/0.47     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.21/0.47  thf('30', plain,
% 0.21/0.47      (![X0 : $i, X1 : $i]:
% 0.21/0.47         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 0.21/0.47           = (k3_xboole_0 @ X0 @ X1))),
% 0.21/0.47      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.21/0.47  thf('31', plain,
% 0.21/0.47      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf(dt_k7_subset_1, axiom,
% 0.21/0.47    (![A:$i,B:$i,C:$i]:
% 0.21/0.47     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.47       ( m1_subset_1 @ ( k7_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.21/0.47  thf('32', plain,
% 0.21/0.47      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.21/0.47         (~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5))
% 0.21/0.47          | (m1_subset_1 @ (k7_subset_1 @ X5 @ X4 @ X6) @ (k1_zfmisc_1 @ X5)))),
% 0.21/0.47      inference('cnf', [status(esa)], [dt_k7_subset_1])).
% 0.21/0.47  thf('33', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         (m1_subset_1 @ (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0) @ 
% 0.21/0.47          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.47      inference('sup-', [status(thm)], ['31', '32'])).
% 0.21/0.47  thf('34', plain,
% 0.21/0.47      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf(redefinition_k7_subset_1, axiom,
% 0.21/0.47    (![A:$i,B:$i,C:$i]:
% 0.21/0.47     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.47       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 0.21/0.47  thf('35', plain,
% 0.21/0.47      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.21/0.47         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8))
% 0.21/0.47          | ((k7_subset_1 @ X8 @ X7 @ X9) = (k4_xboole_0 @ X7 @ X9)))),
% 0.21/0.47      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 0.21/0.47  thf('36', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.21/0.47           = (k4_xboole_0 @ sk_B @ X0))),
% 0.21/0.47      inference('sup-', [status(thm)], ['34', '35'])).
% 0.21/0.47  thf('37', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         (m1_subset_1 @ (k4_xboole_0 @ sk_B @ X0) @ 
% 0.21/0.47          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.47      inference('demod', [status(thm)], ['33', '36'])).
% 0.21/0.47  thf('38', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         (m1_subset_1 @ (k3_xboole_0 @ sk_B @ X0) @ 
% 0.21/0.47          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.47      inference('sup+', [status(thm)], ['30', '37'])).
% 0.21/0.47  thf('39', plain,
% 0.21/0.47      (![X15 : $i, X16 : $i]:
% 0.21/0.47         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.21/0.47          | ((k2_pre_topc @ X16 @ X15) != (k2_struct_0 @ X16))
% 0.21/0.47          | (v1_tops_1 @ X15 @ X16)
% 0.21/0.47          | ~ (l1_pre_topc @ X16))),
% 0.21/0.47      inference('cnf', [status(esa)], [d3_tops_1])).
% 0.21/0.47  thf('40', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         (~ (l1_pre_topc @ sk_A)
% 0.21/0.47          | (v1_tops_1 @ (k3_xboole_0 @ sk_B @ X0) @ sk_A)
% 0.21/0.47          | ((k2_pre_topc @ sk_A @ (k3_xboole_0 @ sk_B @ X0))
% 0.21/0.47              != (k2_struct_0 @ sk_A)))),
% 0.21/0.47      inference('sup-', [status(thm)], ['38', '39'])).
% 0.21/0.47  thf('41', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('42', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         ((v1_tops_1 @ (k3_xboole_0 @ sk_B @ X0) @ sk_A)
% 0.21/0.47          | ((k2_pre_topc @ sk_A @ (k3_xboole_0 @ sk_B @ X0))
% 0.21/0.47              != (k2_struct_0 @ sk_A)))),
% 0.21/0.47      inference('demod', [status(thm)], ['40', '41'])).
% 0.21/0.47  thf('43', plain,
% 0.21/0.47      ((((k2_struct_0 @ sk_A) != (k2_struct_0 @ sk_A))
% 0.21/0.47        | (v1_tops_1 @ (k3_xboole_0 @ sk_B @ sk_C) @ sk_A))),
% 0.21/0.47      inference('sup-', [status(thm)], ['29', '42'])).
% 0.21/0.47  thf('44', plain, ((v1_tops_1 @ (k3_xboole_0 @ sk_B @ sk_C) @ sk_A)),
% 0.21/0.47      inference('simplify', [status(thm)], ['43'])).
% 0.21/0.47  thf('45', plain, ($false), inference('demod', [status(thm)], ['4', '44'])).
% 0.21/0.47  
% 0.21/0.47  % SZS output end Refutation
% 0.21/0.47  
% 0.21/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
