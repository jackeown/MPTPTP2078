%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.gz2IU1i6wL

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:14:38 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 106 expanded)
%              Number of leaves         :   43 (  56 expanded)
%              Depth                    :    9
%              Number of atoms          :  536 ( 940 expanded)
%              Number of equality atoms :   16 (  20 expanded)
%              Maximal formula depth    :   17 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_yellow_1_type,type,(
    k3_yellow_1: $i > $i )).

thf(v1_orders_2_type,type,(
    v1_orders_2: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v10_lattices_type,type,(
    v10_lattices: $i > $o )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(k3_yellow_0_type,type,(
    k3_yellow_0: $i > $i )).

thf(v1_yellow_0_type,type,(
    v1_yellow_0: $i > $o )).

thf(v13_lattices_type,type,(
    v13_lattices: $i > $o )).

thf(v2_waybel_0_type,type,(
    v2_waybel_0: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

thf(k3_lattice3_type,type,(
    k3_lattice3: $i > $i )).

thf(v13_waybel_0_type,type,(
    v13_waybel_0: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(k1_lattice3_type,type,(
    k1_lattice3: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k5_lattices_type,type,(
    k5_lattices: $i > $i )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v3_lattices_type,type,(
    v3_lattices: $i > $o )).

thf(k9_setfam_1_type,type,(
    k9_setfam_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(l3_lattices_type,type,(
    l3_lattices: $i > $o )).

thf(t2_yellow19,conjecture,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( ~ ( v1_xboole_0 @ B )
            & ( v1_subset_1 @ B @ ( u1_struct_0 @ ( k3_yellow_1 @ A ) ) )
            & ( v2_waybel_0 @ B @ ( k3_yellow_1 @ A ) )
            & ( v13_waybel_0 @ B @ ( k3_yellow_1 @ A ) )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ A ) ) ) ) )
         => ! [C: $i] :
              ~ ( ( r2_hidden @ C @ B )
                & ( v1_xboole_0 @ C ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ~ ( v1_xboole_0 @ A )
       => ! [B: $i] :
            ( ( ~ ( v1_xboole_0 @ B )
              & ( v1_subset_1 @ B @ ( u1_struct_0 @ ( k3_yellow_1 @ A ) ) )
              & ( v2_waybel_0 @ B @ ( k3_yellow_1 @ A ) )
              & ( v13_waybel_0 @ B @ ( k3_yellow_1 @ A ) )
              & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ A ) ) ) ) )
           => ! [C: $i] :
                ~ ( ( r2_hidden @ C @ B )
                  & ( v1_xboole_0 @ C ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t2_yellow19])).

thf('0',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k9_setfam_1,axiom,(
    ! [A: $i] :
      ( ( k9_setfam_1 @ A )
      = ( k1_zfmisc_1 @ A ) ) )).

thf('1',plain,(
    ! [X3: $i] :
      ( ( k9_setfam_1 @ X3 )
      = ( k1_zfmisc_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('2',plain,(
    m1_subset_1 @ sk_B @ ( k9_setfam_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(t4_waybel_7,axiom,(
    ! [A: $i] :
      ( ( u1_struct_0 @ ( k3_yellow_1 @ A ) )
      = ( k9_setfam_1 @ A ) ) )).

thf('3',plain,(
    ! [X22: $i] :
      ( ( u1_struct_0 @ ( k3_yellow_1 @ X22 ) )
      = ( k9_setfam_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t4_waybel_7])).

thf('4',plain,(
    m1_subset_1 @ sk_B @ ( k9_setfam_1 @ ( k9_setfam_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X22: $i] :
      ( ( u1_struct_0 @ ( k3_yellow_1 @ X22 ) )
      = ( k9_setfam_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t4_waybel_7])).

thf(t8_waybel_7,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( v1_yellow_0 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v1_xboole_0 @ B )
            & ( v2_waybel_0 @ B @ A )
            & ( v13_waybel_0 @ B @ A )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
         => ( ( v1_subset_1 @ B @ ( u1_struct_0 @ A ) )
          <=> ~ ( r2_hidden @ ( k3_yellow_0 @ A ) @ B ) ) ) ) )).

thf('6',plain,(
    ! [X23: $i,X24: $i] :
      ( ( v1_xboole_0 @ X23 )
      | ~ ( v2_waybel_0 @ X23 @ X24 )
      | ~ ( v13_waybel_0 @ X23 @ X24 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ~ ( v1_subset_1 @ X23 @ ( u1_struct_0 @ X24 ) )
      | ~ ( r2_hidden @ ( k3_yellow_0 @ X24 ) @ X23 )
      | ~ ( l1_orders_2 @ X24 )
      | ~ ( v1_yellow_0 @ X24 )
      | ~ ( v5_orders_2 @ X24 )
      | ~ ( v4_orders_2 @ X24 )
      | ~ ( v3_orders_2 @ X24 )
      | ( v2_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t8_waybel_7])).

thf('7',plain,(
    ! [X3: $i] :
      ( ( k9_setfam_1 @ X3 )
      = ( k1_zfmisc_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('8',plain,(
    ! [X23: $i,X24: $i] :
      ( ( v1_xboole_0 @ X23 )
      | ~ ( v2_waybel_0 @ X23 @ X24 )
      | ~ ( v13_waybel_0 @ X23 @ X24 )
      | ~ ( m1_subset_1 @ X23 @ ( k9_setfam_1 @ ( u1_struct_0 @ X24 ) ) )
      | ~ ( v1_subset_1 @ X23 @ ( u1_struct_0 @ X24 ) )
      | ~ ( r2_hidden @ ( k3_yellow_0 @ X24 ) @ X23 )
      | ~ ( l1_orders_2 @ X24 )
      | ~ ( v1_yellow_0 @ X24 )
      | ~ ( v5_orders_2 @ X24 )
      | ~ ( v4_orders_2 @ X24 )
      | ~ ( v3_orders_2 @ X24 )
      | ( v2_struct_0 @ X24 ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k9_setfam_1 @ ( k9_setfam_1 @ X0 ) ) )
      | ( v2_struct_0 @ ( k3_yellow_1 @ X0 ) )
      | ~ ( v3_orders_2 @ ( k3_yellow_1 @ X0 ) )
      | ~ ( v4_orders_2 @ ( k3_yellow_1 @ X0 ) )
      | ~ ( v5_orders_2 @ ( k3_yellow_1 @ X0 ) )
      | ~ ( v1_yellow_0 @ ( k3_yellow_1 @ X0 ) )
      | ~ ( l1_orders_2 @ ( k3_yellow_1 @ X0 ) )
      | ~ ( r2_hidden @ ( k3_yellow_0 @ ( k3_yellow_1 @ X0 ) ) @ X1 )
      | ~ ( v1_subset_1 @ X1 @ ( u1_struct_0 @ ( k3_yellow_1 @ X0 ) ) )
      | ~ ( v13_waybel_0 @ X1 @ ( k3_yellow_1 @ X0 ) )
      | ~ ( v2_waybel_0 @ X1 @ ( k3_yellow_1 @ X0 ) )
      | ( v1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['5','8'])).

thf(fc7_yellow_1,axiom,(
    ! [A: $i] :
      ( ( v5_orders_2 @ ( k3_yellow_1 @ A ) )
      & ( v4_orders_2 @ ( k3_yellow_1 @ A ) )
      & ( v3_orders_2 @ ( k3_yellow_1 @ A ) )
      & ( v1_orders_2 @ ( k3_yellow_1 @ A ) )
      & ~ ( v2_struct_0 @ ( k3_yellow_1 @ A ) ) ) )).

thf('10',plain,(
    ! [X18: $i] :
      ( v3_orders_2 @ ( k3_yellow_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[fc7_yellow_1])).

thf('11',plain,(
    ! [X19: $i] :
      ( v4_orders_2 @ ( k3_yellow_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[fc7_yellow_1])).

thf('12',plain,(
    ! [X20: $i] :
      ( v5_orders_2 @ ( k3_yellow_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[fc7_yellow_1])).

thf(dt_k3_yellow_1,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ ( k3_yellow_1 @ A ) )
      & ( v1_orders_2 @ ( k3_yellow_1 @ A ) ) ) )).

thf('13',plain,(
    ! [X14: $i] :
      ( l1_orders_2 @ ( k3_yellow_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[dt_k3_yellow_1])).

thf(t18_yellow_1,axiom,(
    ! [A: $i] :
      ( ( k3_yellow_0 @ ( k3_yellow_1 @ A ) )
      = k1_xboole_0 ) )).

thf('14',plain,(
    ! [X21: $i] :
      ( ( k3_yellow_0 @ ( k3_yellow_1 @ X21 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t18_yellow_1])).

thf('15',plain,(
    ! [X22: $i] :
      ( ( u1_struct_0 @ ( k3_yellow_1 @ X22 ) )
      = ( k9_setfam_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t4_waybel_7])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k9_setfam_1 @ ( k9_setfam_1 @ X0 ) ) )
      | ( v2_struct_0 @ ( k3_yellow_1 @ X0 ) )
      | ~ ( v1_yellow_0 @ ( k3_yellow_1 @ X0 ) )
      | ~ ( r2_hidden @ k1_xboole_0 @ X1 )
      | ~ ( v1_subset_1 @ X1 @ ( k9_setfam_1 @ X0 ) )
      | ~ ( v13_waybel_0 @ X1 @ ( k3_yellow_1 @ X0 ) )
      | ~ ( v2_waybel_0 @ X1 @ ( k3_yellow_1 @ X0 ) )
      | ( v1_xboole_0 @ X1 ) ) ),
    inference(demod,[status(thm)],['9','10','11','12','13','14','15'])).

thf(d2_yellow_1,axiom,(
    ! [A: $i] :
      ( ( k3_yellow_1 @ A )
      = ( k3_lattice3 @ ( k1_lattice3 @ A ) ) ) )).

thf('17',plain,(
    ! [X12: $i] :
      ( ( k3_yellow_1 @ X12 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf(fc3_yellow_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v10_lattices @ A )
        & ( v13_lattices @ A )
        & ( l3_lattices @ A ) )
     => ( ( v1_orders_2 @ ( k3_lattice3 @ A ) )
        & ( v3_orders_2 @ ( k3_lattice3 @ A ) )
        & ( v4_orders_2 @ ( k3_lattice3 @ A ) )
        & ( v5_orders_2 @ ( k3_lattice3 @ A ) )
        & ( v1_yellow_0 @ ( k3_lattice3 @ A ) ) ) ) )).

thf('18',plain,(
    ! [X15: $i] :
      ( ( v1_yellow_0 @ ( k3_lattice3 @ X15 ) )
      | ~ ( l3_lattices @ X15 )
      | ~ ( v13_lattices @ X15 )
      | ~ ( v10_lattices @ X15 )
      | ( v2_struct_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[fc3_yellow_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( v1_yellow_0 @ ( k3_yellow_1 @ X0 ) )
      | ( v2_struct_0 @ ( k1_lattice3 @ X0 ) )
      | ~ ( v10_lattices @ ( k1_lattice3 @ X0 ) )
      | ~ ( v13_lattices @ ( k1_lattice3 @ X0 ) )
      | ~ ( l3_lattices @ ( k1_lattice3 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf(fc2_lattice3,axiom,(
    ! [A: $i] :
      ( ( v10_lattices @ ( k1_lattice3 @ A ) )
      & ( v3_lattices @ ( k1_lattice3 @ A ) ) ) )).

thf('20',plain,(
    ! [X9: $i] :
      ( v10_lattices @ ( k1_lattice3 @ X9 ) ) ),
    inference(cnf,[status(esa)],[fc2_lattice3])).

thf(t3_lattice3,axiom,(
    ! [A: $i] :
      ( ( ( k5_lattices @ ( k1_lattice3 @ A ) )
        = k1_xboole_0 )
      & ( v13_lattices @ ( k1_lattice3 @ A ) ) ) )).

thf('21',plain,(
    ! [X10: $i] :
      ( v13_lattices @ ( k1_lattice3 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t3_lattice3])).

thf(dt_k1_lattice3,axiom,(
    ! [A: $i] :
      ( ( l3_lattices @ ( k1_lattice3 @ A ) )
      & ( v3_lattices @ ( k1_lattice3 @ A ) ) ) )).

thf('22',plain,(
    ! [X5: $i] :
      ( l3_lattices @ ( k1_lattice3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_lattice3])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( v1_yellow_0 @ ( k3_yellow_1 @ X0 ) )
      | ( v2_struct_0 @ ( k1_lattice3 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['19','20','21','22'])).

thf(fc1_lattice3,axiom,(
    ! [A: $i] :
      ( ( v3_lattices @ ( k1_lattice3 @ A ) )
      & ~ ( v2_struct_0 @ ( k1_lattice3 @ A ) ) ) )).

thf('24',plain,(
    ! [X6: $i] :
      ~ ( v2_struct_0 @ ( k1_lattice3 @ X6 ) ) ),
    inference(cnf,[status(esa)],[fc1_lattice3])).

thf('25',plain,(
    ! [X0: $i] :
      ( v1_yellow_0 @ ( k3_yellow_1 @ X0 ) ) ),
    inference(clc,[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k9_setfam_1 @ ( k9_setfam_1 @ X0 ) ) )
      | ( v2_struct_0 @ ( k3_yellow_1 @ X0 ) )
      | ~ ( r2_hidden @ k1_xboole_0 @ X1 )
      | ~ ( v1_subset_1 @ X1 @ ( k9_setfam_1 @ X0 ) )
      | ~ ( v13_waybel_0 @ X1 @ ( k3_yellow_1 @ X0 ) )
      | ~ ( v2_waybel_0 @ X1 @ ( k3_yellow_1 @ X0 ) )
      | ( v1_xboole_0 @ X1 ) ) ),
    inference(demod,[status(thm)],['16','25'])).

thf('27',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ~ ( v2_waybel_0 @ sk_B @ ( k3_yellow_1 @ sk_A ) )
    | ~ ( v13_waybel_0 @ sk_B @ ( k3_yellow_1 @ sk_A ) )
    | ~ ( v1_subset_1 @ sk_B @ ( k9_setfam_1 @ sk_A ) )
    | ~ ( r2_hidden @ k1_xboole_0 @ sk_B )
    | ( v2_struct_0 @ ( k3_yellow_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['4','26'])).

thf('28',plain,(
    v2_waybel_0 @ sk_B @ ( k3_yellow_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    v13_waybel_0 @ sk_B @ ( k3_yellow_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    v1_subset_1 @ sk_B @ ( u1_struct_0 @ ( k3_yellow_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    ! [X22: $i] :
      ( ( u1_struct_0 @ ( k3_yellow_1 @ X22 ) )
      = ( k9_setfam_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t4_waybel_7])).

thf('32',plain,(
    v1_subset_1 @ sk_B @ ( k9_setfam_1 @ sk_A ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,(
    r2_hidden @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    v1_xboole_0 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('35',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('36',plain,(
    sk_C = k1_xboole_0 ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    r2_hidden @ k1_xboole_0 @ sk_B ),
    inference(demod,[status(thm)],['33','36'])).

thf('38',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( v2_struct_0 @ ( k3_yellow_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['27','28','29','32','37'])).

thf('39',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    v2_struct_0 @ ( k3_yellow_1 @ sk_A ) ),
    inference(clc,[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X16: $i] :
      ~ ( v2_struct_0 @ ( k3_yellow_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[fc7_yellow_1])).

thf('42',plain,(
    $false ),
    inference('sup-',[status(thm)],['40','41'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.gz2IU1i6wL
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:04:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.20/0.47  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.47  % Solved by: fo/fo7.sh
% 0.20/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.47  % done 44 iterations in 0.020s
% 0.20/0.47  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.47  % SZS output start Refutation
% 0.20/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.47  thf(k3_yellow_1_type, type, k3_yellow_1: $i > $i).
% 0.20/0.47  thf(v1_orders_2_type, type, v1_orders_2: $i > $o).
% 0.20/0.47  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.47  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.47  thf(v10_lattices_type, type, v10_lattices: $i > $o).
% 0.20/0.47  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 0.20/0.47  thf(k3_yellow_0_type, type, k3_yellow_0: $i > $i).
% 0.20/0.47  thf(v1_yellow_0_type, type, v1_yellow_0: $i > $o).
% 0.20/0.47  thf(v13_lattices_type, type, v13_lattices: $i > $o).
% 0.20/0.47  thf(v2_waybel_0_type, type, v2_waybel_0: $i > $i > $o).
% 0.20/0.47  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.47  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 0.20/0.47  thf(k3_lattice3_type, type, k3_lattice3: $i > $i).
% 0.20/0.47  thf(v13_waybel_0_type, type, v13_waybel_0: $i > $i > $o).
% 0.20/0.47  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.20/0.47  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.47  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.20/0.47  thf(k1_lattice3_type, type, k1_lattice3: $i > $i).
% 0.20/0.47  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.47  thf(k5_lattices_type, type, k5_lattices: $i > $i).
% 0.20/0.47  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.20/0.47  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 0.20/0.47  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.47  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.47  thf(v3_lattices_type, type, v3_lattices: $i > $o).
% 0.20/0.47  thf(k9_setfam_1_type, type, k9_setfam_1: $i > $i).
% 0.20/0.47  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.47  thf(l3_lattices_type, type, l3_lattices: $i > $o).
% 0.20/0.47  thf(t2_yellow19, conjecture,
% 0.20/0.47    (![A:$i]:
% 0.20/0.47     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.20/0.47       ( ![B:$i]:
% 0.20/0.47         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.20/0.47             ( v1_subset_1 @ B @ ( u1_struct_0 @ ( k3_yellow_1 @ A ) ) ) & 
% 0.20/0.47             ( v2_waybel_0 @ B @ ( k3_yellow_1 @ A ) ) & 
% 0.20/0.47             ( v13_waybel_0 @ B @ ( k3_yellow_1 @ A ) ) & 
% 0.20/0.47             ( m1_subset_1 @
% 0.20/0.47               B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ A ) ) ) ) ) =>
% 0.20/0.47           ( ![C:$i]: ( ~( ( r2_hidden @ C @ B ) & ( v1_xboole_0 @ C ) ) ) ) ) ) ))).
% 0.20/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.47    (~( ![A:$i]:
% 0.20/0.47        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.20/0.47          ( ![B:$i]:
% 0.20/0.47            ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.20/0.47                ( v1_subset_1 @ B @ ( u1_struct_0 @ ( k3_yellow_1 @ A ) ) ) & 
% 0.20/0.47                ( v2_waybel_0 @ B @ ( k3_yellow_1 @ A ) ) & 
% 0.20/0.47                ( v13_waybel_0 @ B @ ( k3_yellow_1 @ A ) ) & 
% 0.20/0.47                ( m1_subset_1 @
% 0.20/0.47                  B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ A ) ) ) ) ) =>
% 0.20/0.47              ( ![C:$i]: ( ~( ( r2_hidden @ C @ B ) & ( v1_xboole_0 @ C ) ) ) ) ) ) ) )),
% 0.20/0.47    inference('cnf.neg', [status(esa)], [t2_yellow19])).
% 0.20/0.47  thf('0', plain,
% 0.20/0.47      ((m1_subset_1 @ sk_B @ 
% 0.20/0.47        (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ sk_A))))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf(redefinition_k9_setfam_1, axiom,
% 0.20/0.47    (![A:$i]: ( ( k9_setfam_1 @ A ) = ( k1_zfmisc_1 @ A ) ))).
% 0.20/0.47  thf('1', plain, (![X3 : $i]: ((k9_setfam_1 @ X3) = (k1_zfmisc_1 @ X3))),
% 0.20/0.47      inference('cnf', [status(esa)], [redefinition_k9_setfam_1])).
% 0.20/0.47  thf('2', plain,
% 0.20/0.47      ((m1_subset_1 @ sk_B @ 
% 0.20/0.47        (k9_setfam_1 @ (u1_struct_0 @ (k3_yellow_1 @ sk_A))))),
% 0.20/0.47      inference('demod', [status(thm)], ['0', '1'])).
% 0.20/0.47  thf(t4_waybel_7, axiom,
% 0.20/0.47    (![A:$i]: ( ( u1_struct_0 @ ( k3_yellow_1 @ A ) ) = ( k9_setfam_1 @ A ) ))).
% 0.20/0.47  thf('3', plain,
% 0.20/0.47      (![X22 : $i]: ((u1_struct_0 @ (k3_yellow_1 @ X22)) = (k9_setfam_1 @ X22))),
% 0.20/0.47      inference('cnf', [status(esa)], [t4_waybel_7])).
% 0.20/0.47  thf('4', plain,
% 0.20/0.47      ((m1_subset_1 @ sk_B @ (k9_setfam_1 @ (k9_setfam_1 @ sk_A)))),
% 0.20/0.47      inference('demod', [status(thm)], ['2', '3'])).
% 0.20/0.47  thf('5', plain,
% 0.20/0.47      (![X22 : $i]: ((u1_struct_0 @ (k3_yellow_1 @ X22)) = (k9_setfam_1 @ X22))),
% 0.20/0.47      inference('cnf', [status(esa)], [t4_waybel_7])).
% 0.20/0.47  thf(t8_waybel_7, axiom,
% 0.20/0.47    (![A:$i]:
% 0.20/0.47     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.20/0.47         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( v1_yellow_0 @ A ) & 
% 0.20/0.47         ( l1_orders_2 @ A ) ) =>
% 0.20/0.47       ( ![B:$i]:
% 0.20/0.47         ( ( ( ~( v1_xboole_0 @ B ) ) & ( v2_waybel_0 @ B @ A ) & 
% 0.20/0.47             ( v13_waybel_0 @ B @ A ) & 
% 0.20/0.47             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.20/0.47           ( ( v1_subset_1 @ B @ ( u1_struct_0 @ A ) ) <=>
% 0.20/0.47             ( ~( r2_hidden @ ( k3_yellow_0 @ A ) @ B ) ) ) ) ) ))).
% 0.20/0.47  thf('6', plain,
% 0.20/0.47      (![X23 : $i, X24 : $i]:
% 0.20/0.47         ((v1_xboole_0 @ X23)
% 0.20/0.47          | ~ (v2_waybel_0 @ X23 @ X24)
% 0.20/0.47          | ~ (v13_waybel_0 @ X23 @ X24)
% 0.20/0.47          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 0.20/0.47          | ~ (v1_subset_1 @ X23 @ (u1_struct_0 @ X24))
% 0.20/0.47          | ~ (r2_hidden @ (k3_yellow_0 @ X24) @ X23)
% 0.20/0.47          | ~ (l1_orders_2 @ X24)
% 0.20/0.47          | ~ (v1_yellow_0 @ X24)
% 0.20/0.47          | ~ (v5_orders_2 @ X24)
% 0.20/0.47          | ~ (v4_orders_2 @ X24)
% 0.20/0.47          | ~ (v3_orders_2 @ X24)
% 0.20/0.47          | (v2_struct_0 @ X24))),
% 0.20/0.47      inference('cnf', [status(esa)], [t8_waybel_7])).
% 0.20/0.47  thf('7', plain, (![X3 : $i]: ((k9_setfam_1 @ X3) = (k1_zfmisc_1 @ X3))),
% 0.20/0.47      inference('cnf', [status(esa)], [redefinition_k9_setfam_1])).
% 0.20/0.47  thf('8', plain,
% 0.20/0.47      (![X23 : $i, X24 : $i]:
% 0.20/0.47         ((v1_xboole_0 @ X23)
% 0.20/0.47          | ~ (v2_waybel_0 @ X23 @ X24)
% 0.20/0.47          | ~ (v13_waybel_0 @ X23 @ X24)
% 0.20/0.47          | ~ (m1_subset_1 @ X23 @ (k9_setfam_1 @ (u1_struct_0 @ X24)))
% 0.20/0.47          | ~ (v1_subset_1 @ X23 @ (u1_struct_0 @ X24))
% 0.20/0.47          | ~ (r2_hidden @ (k3_yellow_0 @ X24) @ X23)
% 0.20/0.47          | ~ (l1_orders_2 @ X24)
% 0.20/0.47          | ~ (v1_yellow_0 @ X24)
% 0.20/0.47          | ~ (v5_orders_2 @ X24)
% 0.20/0.47          | ~ (v4_orders_2 @ X24)
% 0.20/0.47          | ~ (v3_orders_2 @ X24)
% 0.20/0.47          | (v2_struct_0 @ X24))),
% 0.20/0.47      inference('demod', [status(thm)], ['6', '7'])).
% 0.20/0.47  thf('9', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i]:
% 0.20/0.47         (~ (m1_subset_1 @ X1 @ (k9_setfam_1 @ (k9_setfam_1 @ X0)))
% 0.20/0.47          | (v2_struct_0 @ (k3_yellow_1 @ X0))
% 0.20/0.47          | ~ (v3_orders_2 @ (k3_yellow_1 @ X0))
% 0.20/0.47          | ~ (v4_orders_2 @ (k3_yellow_1 @ X0))
% 0.20/0.47          | ~ (v5_orders_2 @ (k3_yellow_1 @ X0))
% 0.20/0.47          | ~ (v1_yellow_0 @ (k3_yellow_1 @ X0))
% 0.20/0.47          | ~ (l1_orders_2 @ (k3_yellow_1 @ X0))
% 0.20/0.47          | ~ (r2_hidden @ (k3_yellow_0 @ (k3_yellow_1 @ X0)) @ X1)
% 0.20/0.47          | ~ (v1_subset_1 @ X1 @ (u1_struct_0 @ (k3_yellow_1 @ X0)))
% 0.20/0.47          | ~ (v13_waybel_0 @ X1 @ (k3_yellow_1 @ X0))
% 0.20/0.47          | ~ (v2_waybel_0 @ X1 @ (k3_yellow_1 @ X0))
% 0.20/0.47          | (v1_xboole_0 @ X1))),
% 0.20/0.47      inference('sup-', [status(thm)], ['5', '8'])).
% 0.20/0.47  thf(fc7_yellow_1, axiom,
% 0.20/0.47    (![A:$i]:
% 0.20/0.47     ( ( v5_orders_2 @ ( k3_yellow_1 @ A ) ) & 
% 0.20/0.47       ( v4_orders_2 @ ( k3_yellow_1 @ A ) ) & 
% 0.20/0.47       ( v3_orders_2 @ ( k3_yellow_1 @ A ) ) & 
% 0.20/0.47       ( v1_orders_2 @ ( k3_yellow_1 @ A ) ) & 
% 0.20/0.47       ( ~( v2_struct_0 @ ( k3_yellow_1 @ A ) ) ) ))).
% 0.20/0.47  thf('10', plain, (![X18 : $i]: (v3_orders_2 @ (k3_yellow_1 @ X18))),
% 0.20/0.47      inference('cnf', [status(esa)], [fc7_yellow_1])).
% 0.20/0.47  thf('11', plain, (![X19 : $i]: (v4_orders_2 @ (k3_yellow_1 @ X19))),
% 0.20/0.47      inference('cnf', [status(esa)], [fc7_yellow_1])).
% 0.20/0.47  thf('12', plain, (![X20 : $i]: (v5_orders_2 @ (k3_yellow_1 @ X20))),
% 0.20/0.47      inference('cnf', [status(esa)], [fc7_yellow_1])).
% 0.20/0.47  thf(dt_k3_yellow_1, axiom,
% 0.20/0.47    (![A:$i]:
% 0.20/0.47     ( ( l1_orders_2 @ ( k3_yellow_1 @ A ) ) & 
% 0.20/0.47       ( v1_orders_2 @ ( k3_yellow_1 @ A ) ) ))).
% 0.20/0.47  thf('13', plain, (![X14 : $i]: (l1_orders_2 @ (k3_yellow_1 @ X14))),
% 0.20/0.47      inference('cnf', [status(esa)], [dt_k3_yellow_1])).
% 0.20/0.47  thf(t18_yellow_1, axiom,
% 0.20/0.47    (![A:$i]: ( ( k3_yellow_0 @ ( k3_yellow_1 @ A ) ) = ( k1_xboole_0 ) ))).
% 0.20/0.47  thf('14', plain,
% 0.20/0.47      (![X21 : $i]: ((k3_yellow_0 @ (k3_yellow_1 @ X21)) = (k1_xboole_0))),
% 0.20/0.47      inference('cnf', [status(esa)], [t18_yellow_1])).
% 0.20/0.47  thf('15', plain,
% 0.20/0.47      (![X22 : $i]: ((u1_struct_0 @ (k3_yellow_1 @ X22)) = (k9_setfam_1 @ X22))),
% 0.20/0.47      inference('cnf', [status(esa)], [t4_waybel_7])).
% 0.20/0.47  thf('16', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i]:
% 0.20/0.47         (~ (m1_subset_1 @ X1 @ (k9_setfam_1 @ (k9_setfam_1 @ X0)))
% 0.20/0.47          | (v2_struct_0 @ (k3_yellow_1 @ X0))
% 0.20/0.47          | ~ (v1_yellow_0 @ (k3_yellow_1 @ X0))
% 0.20/0.47          | ~ (r2_hidden @ k1_xboole_0 @ X1)
% 0.20/0.47          | ~ (v1_subset_1 @ X1 @ (k9_setfam_1 @ X0))
% 0.20/0.47          | ~ (v13_waybel_0 @ X1 @ (k3_yellow_1 @ X0))
% 0.20/0.47          | ~ (v2_waybel_0 @ X1 @ (k3_yellow_1 @ X0))
% 0.20/0.47          | (v1_xboole_0 @ X1))),
% 0.20/0.47      inference('demod', [status(thm)],
% 0.20/0.47                ['9', '10', '11', '12', '13', '14', '15'])).
% 0.20/0.47  thf(d2_yellow_1, axiom,
% 0.20/0.47    (![A:$i]: ( ( k3_yellow_1 @ A ) = ( k3_lattice3 @ ( k1_lattice3 @ A ) ) ))).
% 0.20/0.47  thf('17', plain,
% 0.20/0.47      (![X12 : $i]: ((k3_yellow_1 @ X12) = (k3_lattice3 @ (k1_lattice3 @ X12)))),
% 0.20/0.47      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.20/0.47  thf(fc3_yellow_1, axiom,
% 0.20/0.47    (![A:$i]:
% 0.20/0.47     ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 0.20/0.47         ( v13_lattices @ A ) & ( l3_lattices @ A ) ) =>
% 0.20/0.47       ( ( v1_orders_2 @ ( k3_lattice3 @ A ) ) & 
% 0.20/0.47         ( v3_orders_2 @ ( k3_lattice3 @ A ) ) & 
% 0.20/0.47         ( v4_orders_2 @ ( k3_lattice3 @ A ) ) & 
% 0.20/0.47         ( v5_orders_2 @ ( k3_lattice3 @ A ) ) & 
% 0.20/0.47         ( v1_yellow_0 @ ( k3_lattice3 @ A ) ) ) ))).
% 0.20/0.47  thf('18', plain,
% 0.20/0.47      (![X15 : $i]:
% 0.20/0.47         ((v1_yellow_0 @ (k3_lattice3 @ X15))
% 0.20/0.47          | ~ (l3_lattices @ X15)
% 0.20/0.47          | ~ (v13_lattices @ X15)
% 0.20/0.47          | ~ (v10_lattices @ X15)
% 0.20/0.47          | (v2_struct_0 @ X15))),
% 0.20/0.47      inference('cnf', [status(esa)], [fc3_yellow_1])).
% 0.20/0.47  thf('19', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         ((v1_yellow_0 @ (k3_yellow_1 @ X0))
% 0.20/0.47          | (v2_struct_0 @ (k1_lattice3 @ X0))
% 0.20/0.47          | ~ (v10_lattices @ (k1_lattice3 @ X0))
% 0.20/0.47          | ~ (v13_lattices @ (k1_lattice3 @ X0))
% 0.20/0.47          | ~ (l3_lattices @ (k1_lattice3 @ X0)))),
% 0.20/0.47      inference('sup+', [status(thm)], ['17', '18'])).
% 0.20/0.47  thf(fc2_lattice3, axiom,
% 0.20/0.47    (![A:$i]:
% 0.20/0.47     ( ( v10_lattices @ ( k1_lattice3 @ A ) ) & 
% 0.20/0.47       ( v3_lattices @ ( k1_lattice3 @ A ) ) ))).
% 0.20/0.47  thf('20', plain, (![X9 : $i]: (v10_lattices @ (k1_lattice3 @ X9))),
% 0.20/0.47      inference('cnf', [status(esa)], [fc2_lattice3])).
% 0.20/0.47  thf(t3_lattice3, axiom,
% 0.20/0.47    (![A:$i]:
% 0.20/0.47     ( ( ( k5_lattices @ ( k1_lattice3 @ A ) ) = ( k1_xboole_0 ) ) & 
% 0.20/0.47       ( v13_lattices @ ( k1_lattice3 @ A ) ) ))).
% 0.20/0.47  thf('21', plain, (![X10 : $i]: (v13_lattices @ (k1_lattice3 @ X10))),
% 0.20/0.47      inference('cnf', [status(esa)], [t3_lattice3])).
% 0.20/0.47  thf(dt_k1_lattice3, axiom,
% 0.20/0.47    (![A:$i]:
% 0.20/0.47     ( ( l3_lattices @ ( k1_lattice3 @ A ) ) & 
% 0.20/0.47       ( v3_lattices @ ( k1_lattice3 @ A ) ) ))).
% 0.20/0.47  thf('22', plain, (![X5 : $i]: (l3_lattices @ (k1_lattice3 @ X5))),
% 0.20/0.47      inference('cnf', [status(esa)], [dt_k1_lattice3])).
% 0.20/0.47  thf('23', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         ((v1_yellow_0 @ (k3_yellow_1 @ X0))
% 0.20/0.47          | (v2_struct_0 @ (k1_lattice3 @ X0)))),
% 0.20/0.47      inference('demod', [status(thm)], ['19', '20', '21', '22'])).
% 0.20/0.47  thf(fc1_lattice3, axiom,
% 0.20/0.47    (![A:$i]:
% 0.20/0.47     ( ( v3_lattices @ ( k1_lattice3 @ A ) ) & 
% 0.20/0.47       ( ~( v2_struct_0 @ ( k1_lattice3 @ A ) ) ) ))).
% 0.20/0.47  thf('24', plain, (![X6 : $i]: ~ (v2_struct_0 @ (k1_lattice3 @ X6))),
% 0.20/0.47      inference('cnf', [status(esa)], [fc1_lattice3])).
% 0.20/0.47  thf('25', plain, (![X0 : $i]: (v1_yellow_0 @ (k3_yellow_1 @ X0))),
% 0.20/0.47      inference('clc', [status(thm)], ['23', '24'])).
% 0.20/0.47  thf('26', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i]:
% 0.20/0.47         (~ (m1_subset_1 @ X1 @ (k9_setfam_1 @ (k9_setfam_1 @ X0)))
% 0.20/0.47          | (v2_struct_0 @ (k3_yellow_1 @ X0))
% 0.20/0.47          | ~ (r2_hidden @ k1_xboole_0 @ X1)
% 0.20/0.47          | ~ (v1_subset_1 @ X1 @ (k9_setfam_1 @ X0))
% 0.20/0.47          | ~ (v13_waybel_0 @ X1 @ (k3_yellow_1 @ X0))
% 0.20/0.47          | ~ (v2_waybel_0 @ X1 @ (k3_yellow_1 @ X0))
% 0.20/0.47          | (v1_xboole_0 @ X1))),
% 0.20/0.47      inference('demod', [status(thm)], ['16', '25'])).
% 0.20/0.47  thf('27', plain,
% 0.20/0.47      (((v1_xboole_0 @ sk_B)
% 0.20/0.47        | ~ (v2_waybel_0 @ sk_B @ (k3_yellow_1 @ sk_A))
% 0.20/0.47        | ~ (v13_waybel_0 @ sk_B @ (k3_yellow_1 @ sk_A))
% 0.20/0.47        | ~ (v1_subset_1 @ sk_B @ (k9_setfam_1 @ sk_A))
% 0.20/0.47        | ~ (r2_hidden @ k1_xboole_0 @ sk_B)
% 0.20/0.47        | (v2_struct_0 @ (k3_yellow_1 @ sk_A)))),
% 0.20/0.47      inference('sup-', [status(thm)], ['4', '26'])).
% 0.20/0.47  thf('28', plain, ((v2_waybel_0 @ sk_B @ (k3_yellow_1 @ sk_A))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('29', plain, ((v13_waybel_0 @ sk_B @ (k3_yellow_1 @ sk_A))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('30', plain,
% 0.20/0.47      ((v1_subset_1 @ sk_B @ (u1_struct_0 @ (k3_yellow_1 @ sk_A)))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('31', plain,
% 0.20/0.47      (![X22 : $i]: ((u1_struct_0 @ (k3_yellow_1 @ X22)) = (k9_setfam_1 @ X22))),
% 0.20/0.47      inference('cnf', [status(esa)], [t4_waybel_7])).
% 0.20/0.47  thf('32', plain, ((v1_subset_1 @ sk_B @ (k9_setfam_1 @ sk_A))),
% 0.20/0.47      inference('demod', [status(thm)], ['30', '31'])).
% 0.20/0.47  thf('33', plain, ((r2_hidden @ sk_C @ sk_B)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('34', plain, ((v1_xboole_0 @ sk_C)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf(l13_xboole_0, axiom,
% 0.20/0.47    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.20/0.47  thf('35', plain,
% 0.20/0.47      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.20/0.47      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.20/0.47  thf('36', plain, (((sk_C) = (k1_xboole_0))),
% 0.20/0.47      inference('sup-', [status(thm)], ['34', '35'])).
% 0.20/0.47  thf('37', plain, ((r2_hidden @ k1_xboole_0 @ sk_B)),
% 0.20/0.47      inference('demod', [status(thm)], ['33', '36'])).
% 0.20/0.47  thf('38', plain,
% 0.20/0.47      (((v1_xboole_0 @ sk_B) | (v2_struct_0 @ (k3_yellow_1 @ sk_A)))),
% 0.20/0.47      inference('demod', [status(thm)], ['27', '28', '29', '32', '37'])).
% 0.20/0.47  thf('39', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('40', plain, ((v2_struct_0 @ (k3_yellow_1 @ sk_A))),
% 0.20/0.47      inference('clc', [status(thm)], ['38', '39'])).
% 0.20/0.47  thf('41', plain, (![X16 : $i]: ~ (v2_struct_0 @ (k3_yellow_1 @ X16))),
% 0.20/0.47      inference('cnf', [status(esa)], [fc7_yellow_1])).
% 0.20/0.47  thf('42', plain, ($false), inference('sup-', [status(thm)], ['40', '41'])).
% 0.20/0.47  
% 0.20/0.47  % SZS output end Refutation
% 0.20/0.47  
% 0.20/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
