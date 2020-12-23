%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.qC6ACk9mMd

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:14:17 EST 2020

% Result     : Theorem 0.88s
% Output     : Refutation 0.88s
% Verified   : 
% Statistics : Number of formulae       :  250 ( 550 expanded)
%              Number of leaves         :   51 ( 179 expanded)
%              Depth                    :   24
%              Number of atoms          : 2313 (7403 expanded)
%              Number of equality atoms :    8 (   9 expanded)
%              Maximal formula depth    :   20 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i > $i )).

thf(v1_waybel_7_type,type,(
    v1_waybel_7: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k5_waybel_0_type,type,(
    k5_waybel_0: $i > $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(zip_tseitin_2_type,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r2_lattice3_type,type,(
    r2_lattice3: $i > $i > $i > $o )).

thf(v12_waybel_0_type,type,(
    v12_waybel_0: $i > $i > $o )).

thf(v1_lattice3_type,type,(
    v1_lattice3: $i > $o )).

thf(v4_waybel_7_type,type,(
    v4_waybel_7: $i > $i > $o )).

thf(v2_lattice3_type,type,(
    v2_lattice3: $i > $o )).

thf(v1_waybel_0_type,type,(
    v1_waybel_0: $i > $i > $o )).

thf(r1_yellow_0_type,type,(
    r1_yellow_0: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(r3_orders_2_type,type,(
    r3_orders_2: $i > $i > $i > $o )).

thf(v5_waybel_6_type,type,(
    v5_waybel_6: $i > $i > $o )).

thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(k1_yellow_0_type,type,(
    k1_yellow_0: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(t38_waybel_7,conjecture,(
    ! [A: $i] :
      ( ( ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( v1_lattice3 @ A )
        & ( v2_lattice3 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ( ( v5_waybel_6 @ B @ A )
           => ( v4_waybel_7 @ B @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v3_orders_2 @ A )
          & ( v4_orders_2 @ A )
          & ( v5_orders_2 @ A )
          & ( v1_lattice3 @ A )
          & ( v2_lattice3 @ A )
          & ( l1_orders_2 @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
           => ( ( v5_waybel_6 @ B @ A )
             => ( v4_waybel_7 @ B @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t38_waybel_7])).

thf('0',plain,(
    ~ ( v4_waybel_7 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k5_waybel_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_orders_2 @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) )
     => ( m1_subset_1 @ ( k5_waybel_0 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('2',plain,(
    ! [X32: $i,X33: $i] :
      ( ~ ( l1_orders_2 @ X32 )
      | ( v2_struct_0 @ X32 )
      | ~ ( m1_subset_1 @ X33 @ ( u1_struct_0 @ X32 ) )
      | ( m1_subset_1 @ ( k5_waybel_0 @ X32 @ X33 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X32 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_waybel_0])).

thf('3',plain,
    ( ( m1_subset_1 @ ( k5_waybel_0 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( m1_subset_1 @ ( k5_waybel_0 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_lattice3,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( ( v1_lattice3 @ A )
       => ~ ( v2_struct_0 @ A ) ) ) )).

thf('7',plain,(
    ! [X9: $i] :
      ( ~ ( v1_lattice3 @ X9 )
      | ~ ( v2_struct_0 @ X9 )
      | ~ ( l1_orders_2 @ X9 ) ) ),
    inference(cnf,[status(esa)],[cc1_lattice3])).

thf('8',plain,
    ( ~ ( v2_struct_0 @ sk_A )
    | ~ ( v1_lattice3 @ sk_A ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    v1_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,(
    m1_subset_1 @ ( k5_waybel_0 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['5','10'])).

thf(d6_waybel_7,axiom,(
    ! [A: $i] :
      ( ( ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( v1_lattice3 @ A )
        & ( v2_lattice3 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ( ( v4_waybel_7 @ B @ A )
          <=> ? [C: $i] :
                ( ( B
                  = ( k1_yellow_0 @ A @ C ) )
                & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                & ( v1_waybel_7 @ C @ A )
                & ( v12_waybel_0 @ C @ A )
                & ( v1_waybel_0 @ C @ A )
                & ~ ( v1_xboole_0 @ C ) ) ) ) ) )).

thf('12',plain,(
    ! [X41: $i,X42: $i,X43: $i] :
      ( ~ ( m1_subset_1 @ X41 @ ( u1_struct_0 @ X42 ) )
      | ( X41
       != ( k1_yellow_0 @ X42 @ X43 ) )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X42 ) ) )
      | ~ ( v1_waybel_7 @ X43 @ X42 )
      | ~ ( v12_waybel_0 @ X43 @ X42 )
      | ~ ( v1_waybel_0 @ X43 @ X42 )
      | ( v1_xboole_0 @ X43 )
      | ( v4_waybel_7 @ X41 @ X42 )
      | ~ ( l1_orders_2 @ X42 )
      | ~ ( v2_lattice3 @ X42 )
      | ~ ( v1_lattice3 @ X42 )
      | ~ ( v5_orders_2 @ X42 )
      | ~ ( v4_orders_2 @ X42 )
      | ~ ( v3_orders_2 @ X42 ) ) ),
    inference(cnf,[status(esa)],[d6_waybel_7])).

thf('13',plain,(
    ! [X42: $i,X43: $i] :
      ( ~ ( v3_orders_2 @ X42 )
      | ~ ( v4_orders_2 @ X42 )
      | ~ ( v5_orders_2 @ X42 )
      | ~ ( v1_lattice3 @ X42 )
      | ~ ( v2_lattice3 @ X42 )
      | ~ ( l1_orders_2 @ X42 )
      | ( v4_waybel_7 @ ( k1_yellow_0 @ X42 @ X43 ) @ X42 )
      | ( v1_xboole_0 @ X43 )
      | ~ ( v1_waybel_0 @ X43 @ X42 )
      | ~ ( v12_waybel_0 @ X43 @ X42 )
      | ~ ( v1_waybel_7 @ X43 @ X42 )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X42 ) ) )
      | ~ ( m1_subset_1 @ ( k1_yellow_0 @ X42 @ X43 ) @ ( u1_struct_0 @ X42 ) ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,
    ( ~ ( m1_subset_1 @ ( k1_yellow_0 @ sk_A @ ( k5_waybel_0 @ sk_A @ sk_B ) ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_waybel_7 @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_A )
    | ~ ( v12_waybel_0 @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_A )
    | ~ ( v1_waybel_0 @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_A )
    | ( v1_xboole_0 @ ( k5_waybel_0 @ sk_A @ sk_B ) )
    | ( v4_waybel_7 @ ( k1_yellow_0 @ sk_A @ ( k5_waybel_0 @ sk_A @ sk_B ) ) @ sk_A )
    | ~ ( l1_orders_2 @ sk_A )
    | ~ ( v2_lattice3 @ sk_A )
    | ~ ( v1_lattice3 @ sk_A )
    | ~ ( v5_orders_2 @ sk_A )
    | ~ ( v4_orders_2 @ sk_A )
    | ~ ( v3_orders_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['11','13'])).

thf(dt_k1_yellow_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( l1_orders_2 @ A )
     => ( m1_subset_1 @ ( k1_yellow_0 @ A @ B ) @ ( u1_struct_0 @ A ) ) ) )).

thf('15',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( l1_orders_2 @ X14 )
      | ( m1_subset_1 @ ( k1_yellow_0 @ X14 @ X15 ) @ ( u1_struct_0 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_yellow_0])).

thf('16',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( l1_orders_2 @ X14 )
      | ( m1_subset_1 @ ( k1_yellow_0 @ X14 @ X15 ) @ ( u1_struct_0 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_yellow_0])).

thf(reflexivity_r3_orders_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( l1_orders_2 @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
        & ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) )
     => ( r3_orders_2 @ A @ B @ B ) ) )).

thf('18',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( r3_orders_2 @ X6 @ X7 @ X7 )
      | ~ ( m1_subset_1 @ X7 @ ( u1_struct_0 @ X6 ) )
      | ~ ( l1_orders_2 @ X6 )
      | ~ ( v3_orders_2 @ X6 )
      | ( v2_struct_0 @ X6 )
      | ~ ( m1_subset_1 @ X8 @ ( u1_struct_0 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[reflexivity_r3_orders_2])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ( r3_orders_2 @ X0 @ ( k1_yellow_0 @ X0 @ X1 ) @ ( k1_yellow_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r3_orders_2 @ X0 @ ( k1_yellow_0 @ X0 @ X1 ) @ ( k1_yellow_0 @ X0 @ X1 ) )
      | ~ ( v3_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ( r3_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ X0 ) @ ( k1_yellow_0 @ sk_A @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['16','20'])).

thf('22',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r3_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ X0 ) @ ( k1_yellow_0 @ sk_A @ X0 ) ) ) ),
    inference(demod,[status(thm)],['21','22','23'])).

thf('25',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('26',plain,(
    ! [X0: $i] :
      ( r3_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ X0 ) @ ( k1_yellow_0 @ sk_A @ X0 ) ) ),
    inference(clc,[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( l1_orders_2 @ X14 )
      | ( m1_subset_1 @ ( k1_yellow_0 @ X14 @ X15 ) @ ( u1_struct_0 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_yellow_0])).

thf('28',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( l1_orders_2 @ X14 )
      | ( m1_subset_1 @ ( k1_yellow_0 @ X14 @ X15 ) @ ( u1_struct_0 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_yellow_0])).

thf(redefinition_r3_orders_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( l1_orders_2 @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
        & ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) )
     => ( ( r3_orders_2 @ A @ B @ C )
      <=> ( r1_orders_2 @ A @ B @ C ) ) ) )).

thf('29',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X4 ) )
      | ~ ( l1_orders_2 @ X4 )
      | ~ ( v3_orders_2 @ X4 )
      | ( v2_struct_0 @ X4 )
      | ~ ( m1_subset_1 @ X5 @ ( u1_struct_0 @ X4 ) )
      | ( r1_orders_2 @ X4 @ X3 @ X5 )
      | ~ ( r3_orders_2 @ X4 @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r3_orders_2])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ~ ( r3_orders_2 @ X0 @ ( k1_yellow_0 @ X0 @ X1 ) @ X2 )
      | ( r1_orders_2 @ X0 @ ( k1_yellow_0 @ X0 @ X1 ) @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v3_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ( r1_orders_2 @ X0 @ ( k1_yellow_0 @ X0 @ X1 ) @ X2 )
      | ~ ( r3_orders_2 @ X0 @ ( k1_yellow_0 @ X0 @ X1 ) @ X2 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( r3_orders_2 @ X0 @ ( k1_yellow_0 @ X0 @ X2 ) @ ( k1_yellow_0 @ X0 @ X1 ) )
      | ( r1_orders_2 @ X0 @ ( k1_yellow_0 @ X0 @ X2 ) @ ( k1_yellow_0 @ X0 @ X1 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['27','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v3_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( r1_orders_2 @ X0 @ ( k1_yellow_0 @ X0 @ X2 ) @ ( k1_yellow_0 @ X0 @ X1 ) )
      | ~ ( r3_orders_2 @ X0 @ ( k1_yellow_0 @ X0 @ X2 ) @ ( k1_yellow_0 @ X0 @ X1 ) )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ( r1_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ X0 ) @ ( k1_yellow_0 @ sk_A @ X0 ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['26','33'])).

thf('35',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( r1_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ X0 ) @ ( k1_yellow_0 @ sk_A @ X0 ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['34','35','36'])).

thf('38',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('39',plain,(
    ! [X0: $i] :
      ( r1_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ X0 ) @ ( k1_yellow_0 @ sk_A @ X0 ) ) ),
    inference(clc,[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( l1_orders_2 @ X14 )
      | ( m1_subset_1 @ ( k1_yellow_0 @ X14 @ X15 ) @ ( u1_struct_0 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_yellow_0])).

thf(t17_waybel_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ( ( r2_hidden @ C @ ( k5_waybel_0 @ A @ B ) )
              <=> ( r1_orders_2 @ A @ C @ B ) ) ) ) ) )).

thf('41',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ~ ( m1_subset_1 @ X38 @ ( u1_struct_0 @ X39 ) )
      | ~ ( r1_orders_2 @ X39 @ X40 @ X38 )
      | ( r2_hidden @ X40 @ ( k5_waybel_0 @ X39 @ X38 ) )
      | ~ ( m1_subset_1 @ X40 @ ( u1_struct_0 @ X39 ) )
      | ~ ( l1_orders_2 @ X39 )
      | ( v2_struct_0 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t17_waybel_0])).

thf('42',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ( r2_hidden @ X2 @ ( k5_waybel_0 @ X0 @ ( k1_yellow_0 @ X0 @ X1 ) ) )
      | ~ ( r1_orders_2 @ X0 @ X2 @ ( k1_yellow_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_orders_2 @ X0 @ X2 @ ( k1_yellow_0 @ X0 @ X1 ) )
      | ( r2_hidden @ X2 @ ( k5_waybel_0 @ X0 @ ( k1_yellow_0 @ X0 @ X1 ) ) )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ ( k1_yellow_0 @ sk_A @ X0 ) @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ ( k1_yellow_0 @ sk_A @ X0 ) @ ( k5_waybel_0 @ sk_A @ ( k1_yellow_0 @ sk_A @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['39','43'])).

thf('45',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ ( k1_yellow_0 @ sk_A @ X0 ) @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ ( k1_yellow_0 @ sk_A @ X0 ) @ ( k5_waybel_0 @ sk_A @ ( k1_yellow_0 @ sk_A @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_yellow_0 @ sk_A @ X0 ) @ ( k5_waybel_0 @ sk_A @ ( k1_yellow_0 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ ( k1_yellow_0 @ sk_A @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ( r2_hidden @ ( k1_yellow_0 @ sk_A @ X0 ) @ ( k5_waybel_0 @ sk_A @ ( k1_yellow_0 @ sk_A @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['15','48'])).

thf('50',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    ! [X0: $i] :
      ( r2_hidden @ ( k1_yellow_0 @ sk_A @ X0 ) @ ( k5_waybel_0 @ sk_A @ ( k1_yellow_0 @ sk_A @ X0 ) ) ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( l1_orders_2 @ X14 )
      | ( m1_subset_1 @ ( k1_yellow_0 @ X14 @ X15 ) @ ( u1_struct_0 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_yellow_0])).

thf('53',plain,(
    ! [X32: $i,X33: $i] :
      ( ~ ( l1_orders_2 @ X32 )
      | ( v2_struct_0 @ X32 )
      | ~ ( m1_subset_1 @ X33 @ ( u1_struct_0 @ X32 ) )
      | ( m1_subset_1 @ ( k5_waybel_0 @ X32 @ X33 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X32 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_waybel_0])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( m1_subset_1 @ ( k5_waybel_0 @ X0 @ ( k1_yellow_0 @ X0 @ X1 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ( m1_subset_1 @ ( k5_waybel_0 @ X0 @ ( k1_yellow_0 @ X0 @ X1 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['54'])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('56',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X2 ) )
      | ( m1_subset_1 @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('57',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ ( k5_waybel_0 @ X0 @ ( k1_yellow_0 @ X0 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k1_yellow_0 @ sk_A @ X0 ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['51','57'])).

thf('59',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k1_yellow_0 @ sk_A @ X0 ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('62',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k1_yellow_0 @ sk_A @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['60','61'])).

thf('63',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc12_waybel_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v4_orders_2 @ A )
        & ( l1_orders_2 @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) )
     => ( v12_waybel_0 @ ( k5_waybel_0 @ A @ B ) @ A ) ) )).

thf('64',plain,(
    ! [X34: $i,X35: $i] :
      ( ~ ( l1_orders_2 @ X34 )
      | ~ ( v4_orders_2 @ X34 )
      | ( v2_struct_0 @ X34 )
      | ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ X34 ) )
      | ( v12_waybel_0 @ ( k5_waybel_0 @ X34 @ X35 ) @ X34 ) ) ),
    inference(cnf,[status(esa)],[fc12_waybel_0])).

thf('65',plain,
    ( ( v12_waybel_0 @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v4_orders_2 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,
    ( ( v12_waybel_0 @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['65','66','67'])).

thf('69',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('70',plain,(
    v12_waybel_0 @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_A ),
    inference(clc,[status(thm)],['68','69'])).

thf('71',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc8_waybel_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( l1_orders_2 @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) )
     => ( ~ ( v1_xboole_0 @ ( k5_waybel_0 @ A @ B ) )
        & ( v1_waybel_0 @ ( k5_waybel_0 @ A @ B ) @ A ) ) ) )).

thf('72',plain,(
    ! [X36: $i,X37: $i] :
      ( ~ ( l1_orders_2 @ X36 )
      | ~ ( v3_orders_2 @ X36 )
      | ( v2_struct_0 @ X36 )
      | ~ ( m1_subset_1 @ X37 @ ( u1_struct_0 @ X36 ) )
      | ( v1_waybel_0 @ ( k5_waybel_0 @ X36 @ X37 ) @ X36 ) ) ),
    inference(cnf,[status(esa)],[fc8_waybel_0])).

thf('73',plain,
    ( ( v1_waybel_0 @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v3_orders_2 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,
    ( ( v1_waybel_0 @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['73','74','75'])).

thf('77',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('78',plain,(
    v1_waybel_0 @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_A ),
    inference(clc,[status(thm)],['76','77'])).

thf('79',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    v2_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    v1_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,
    ( ~ ( v1_waybel_7 @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_A )
    | ( v1_xboole_0 @ ( k5_waybel_0 @ sk_A @ sk_B ) )
    | ( v4_waybel_7 @ ( k1_yellow_0 @ sk_A @ ( k5_waybel_0 @ sk_A @ sk_B ) ) @ sk_A ) ),
    inference(demod,[status(thm)],['14','62','70','78','79','80','81','82','83','84'])).

thf('86',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    ! [X36: $i,X37: $i] :
      ( ~ ( l1_orders_2 @ X36 )
      | ~ ( v3_orders_2 @ X36 )
      | ( v2_struct_0 @ X36 )
      | ~ ( m1_subset_1 @ X37 @ ( u1_struct_0 @ X36 ) )
      | ~ ( v1_xboole_0 @ ( k5_waybel_0 @ X36 @ X37 ) ) ) ),
    inference(cnf,[status(esa)],[fc8_waybel_0])).

thf('88',plain,
    ( ~ ( v1_xboole_0 @ ( k5_waybel_0 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v3_orders_2 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,
    ( ~ ( v1_xboole_0 @ ( k5_waybel_0 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['88','89','90'])).

thf('92',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('93',plain,(
    ~ ( v1_xboole_0 @ ( k5_waybel_0 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['91','92'])).

thf('94',plain,
    ( ( v4_waybel_7 @ ( k1_yellow_0 @ sk_A @ ( k5_waybel_0 @ sk_A @ sk_B ) ) @ sk_A )
    | ~ ( v1_waybel_7 @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_A ) ),
    inference(clc,[status(thm)],['85','93'])).

thf('95',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t37_waybel_7,axiom,(
    ! [A: $i] :
      ( ( ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( v1_lattice3 @ A )
        & ( v2_lattice3 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ( ( v5_waybel_6 @ B @ A )
           => ( v1_waybel_7 @ ( k5_waybel_0 @ A @ B ) @ A ) ) ) ) )).

thf('96',plain,(
    ! [X44: $i,X45: $i] :
      ( ~ ( m1_subset_1 @ X44 @ ( u1_struct_0 @ X45 ) )
      | ( v1_waybel_7 @ ( k5_waybel_0 @ X45 @ X44 ) @ X45 )
      | ~ ( v5_waybel_6 @ X44 @ X45 )
      | ~ ( l1_orders_2 @ X45 )
      | ~ ( v2_lattice3 @ X45 )
      | ~ ( v1_lattice3 @ X45 )
      | ~ ( v5_orders_2 @ X45 )
      | ~ ( v4_orders_2 @ X45 )
      | ~ ( v3_orders_2 @ X45 ) ) ),
    inference(cnf,[status(esa)],[t37_waybel_7])).

thf('97',plain,
    ( ~ ( v3_orders_2 @ sk_A )
    | ~ ( v4_orders_2 @ sk_A )
    | ~ ( v5_orders_2 @ sk_A )
    | ~ ( v1_lattice3 @ sk_A )
    | ~ ( v2_lattice3 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A )
    | ~ ( v5_waybel_6 @ sk_B @ sk_A )
    | ( v1_waybel_7 @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,(
    v1_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    v2_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,(
    v5_waybel_6 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,(
    v1_waybel_7 @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['97','98','99','100','101','102','103','104'])).

thf('106',plain,(
    v4_waybel_7 @ ( k1_yellow_0 @ sk_A @ ( k5_waybel_0 @ sk_A @ sk_B ) ) @ sk_A ),
    inference(demod,[status(thm)],['94','105'])).

thf('107',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ~ ( m1_subset_1 @ X38 @ ( u1_struct_0 @ X39 ) )
      | ~ ( r1_orders_2 @ X39 @ X40 @ X38 )
      | ( r2_hidden @ X40 @ ( k5_waybel_0 @ X39 @ X38 ) )
      | ~ ( m1_subset_1 @ X40 @ ( u1_struct_0 @ X39 ) )
      | ~ ( l1_orders_2 @ X39 )
      | ( v2_struct_0 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t17_waybel_0])).

thf('110',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X0 @ ( k5_waybel_0 @ sk_A @ sk_B ) )
      | ~ ( r1_orders_2 @ sk_A @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['108','109'])).

thf('111',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X0 @ ( k5_waybel_0 @ sk_A @ sk_B ) )
      | ~ ( r1_orders_2 @ sk_A @ X0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['110','111'])).

thf('113',plain,
    ( ~ ( r1_orders_2 @ sk_A @ sk_B @ sk_B )
    | ( r2_hidden @ sk_B @ ( k5_waybel_0 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['107','112'])).

thf('114',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( r3_orders_2 @ X6 @ X7 @ X7 )
      | ~ ( m1_subset_1 @ X7 @ ( u1_struct_0 @ X6 ) )
      | ~ ( l1_orders_2 @ X6 )
      | ~ ( v3_orders_2 @ X6 )
      | ( v2_struct_0 @ X6 )
      | ~ ( m1_subset_1 @ X8 @ ( u1_struct_0 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[reflexivity_r3_orders_2])).

thf('117',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ( r3_orders_2 @ sk_A @ sk_B @ sk_B ) ) ),
    inference('sup-',[status(thm)],['115','116'])).

thf('118',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( r3_orders_2 @ sk_A @ sk_B @ sk_B ) ) ),
    inference(demod,[status(thm)],['117','118','119'])).

thf('121',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('122',plain,(
    ! [X0: $i] :
      ( ( r3_orders_2 @ sk_A @ sk_B @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['120','121'])).

thf('123',plain,(
    r3_orders_2 @ sk_A @ sk_B @ sk_B ),
    inference('sup-',[status(thm)],['114','122'])).

thf('124',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('125',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X4 ) )
      | ~ ( l1_orders_2 @ X4 )
      | ~ ( v3_orders_2 @ X4 )
      | ( v2_struct_0 @ X4 )
      | ~ ( m1_subset_1 @ X5 @ ( u1_struct_0 @ X4 ) )
      | ( r1_orders_2 @ X4 @ X3 @ X5 )
      | ~ ( r3_orders_2 @ X4 @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r3_orders_2])).

thf('126',plain,(
    ! [X0: $i] :
      ( ~ ( r3_orders_2 @ sk_A @ sk_B @ X0 )
      | ( r1_orders_2 @ sk_A @ sk_B @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['124','125'])).

thf('127',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('128',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('129',plain,(
    ! [X0: $i] :
      ( ~ ( r3_orders_2 @ sk_A @ sk_B @ X0 )
      | ( r1_orders_2 @ sk_A @ sk_B @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['126','127','128'])).

thf('130',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( r1_orders_2 @ sk_A @ sk_B @ sk_B ) ),
    inference('sup-',[status(thm)],['123','129'])).

thf('131',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('132',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r1_orders_2 @ sk_A @ sk_B @ sk_B ) ),
    inference(demod,[status(thm)],['130','131'])).

thf('133',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('134',plain,(
    r1_orders_2 @ sk_A @ sk_B @ sk_B ),
    inference(clc,[status(thm)],['132','133'])).

thf('135',plain,
    ( ( r2_hidden @ sk_B @ ( k5_waybel_0 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['113','134'])).

thf('136',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('137',plain,(
    r2_hidden @ sk_B @ ( k5_waybel_0 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['135','136'])).

thf(t30_yellow_0,axiom,(
    ! [A: $i] :
      ( ( ( l1_orders_2 @ A )
        & ( v5_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( ( ( r1_yellow_0 @ A @ C )
                  & ( B
                    = ( k1_yellow_0 @ A @ C ) ) )
               => ( ! [D: $i] :
                      ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                     => ( ( r2_lattice3 @ A @ C @ D )
                       => ( r1_orders_2 @ A @ B @ D ) ) )
                  & ( r2_lattice3 @ A @ C @ B ) ) )
              & ( ( ! [D: $i] :
                      ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                     => ( ( r2_lattice3 @ A @ C @ D )
                       => ( r1_orders_2 @ A @ B @ D ) ) )
                  & ( r2_lattice3 @ A @ C @ B ) )
               => ( ( r1_yellow_0 @ A @ C )
                  & ( B
                    = ( k1_yellow_0 @ A @ C ) ) ) ) ) ) ) )).

thf(zf_stmt_1,axiom,(
    ! [D: $i,C: $i,B: $i,A: $i] :
      ( ( ( r2_lattice3 @ A @ C @ D )
       => ( r1_orders_2 @ A @ B @ D ) )
     => ( zip_tseitin_0 @ D @ C @ B @ A ) ) )).

thf('138',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ( zip_tseitin_0 @ X16 @ X17 @ X18 @ X19 )
      | ( r2_lattice3 @ X19 @ X17 @ X16 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('139',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(zf_stmt_2,axiom,(
    ! [D: $i,C: $i,B: $i,A: $i] :
      ( ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
       => ( zip_tseitin_0 @ D @ C @ B @ A ) )
     => ( zip_tseitin_1 @ D @ C @ B @ A ) ) )).

thf('140',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ( zip_tseitin_1 @ X20 @ X21 @ X22 @ X23 )
      | ( m1_subset_1 @ X20 @ ( u1_struct_0 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf(d9_lattice3,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ! [B: $i,C: $i] :
          ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
         => ( ( r2_lattice3 @ A @ B @ C )
          <=> ! [D: $i] :
                ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
               => ( ( r2_hidden @ D @ B )
                 => ( r1_orders_2 @ A @ D @ C ) ) ) ) ) ) )).

thf('141',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( u1_struct_0 @ X11 ) )
      | ~ ( r2_lattice3 @ X11 @ X12 @ X10 )
      | ~ ( r2_hidden @ X13 @ X12 )
      | ( r1_orders_2 @ X11 @ X13 @ X10 )
      | ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ X11 ) )
      | ~ ( l1_orders_2 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d9_lattice3])).

thf('142',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( zip_tseitin_1 @ X1 @ X5 @ X4 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ( r1_orders_2 @ X0 @ X2 @ X1 )
      | ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( r2_lattice3 @ X0 @ X3 @ X1 ) ) ),
    inference('sup-',[status(thm)],['140','141'])).

thf('143',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_lattice3 @ sk_A @ X1 @ X0 )
      | ~ ( r2_hidden @ sk_B @ X1 )
      | ( r1_orders_2 @ sk_A @ sk_B @ X0 )
      | ~ ( l1_orders_2 @ sk_A )
      | ( zip_tseitin_1 @ X0 @ X3 @ X2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['139','142'])).

thf('144',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('145',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_lattice3 @ sk_A @ X1 @ X0 )
      | ~ ( r2_hidden @ sk_B @ X1 )
      | ( r1_orders_2 @ sk_A @ sk_B @ X0 )
      | ( zip_tseitin_1 @ X0 @ X3 @ X2 @ sk_A ) ) ),
    inference(demod,[status(thm)],['143','144'])).

thf('146',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( zip_tseitin_0 @ X0 @ X1 @ X4 @ sk_A )
      | ( zip_tseitin_1 @ X0 @ X3 @ X2 @ sk_A )
      | ( r1_orders_2 @ sk_A @ sk_B @ X0 )
      | ~ ( r2_hidden @ sk_B @ X1 ) ) ),
    inference('sup-',[status(thm)],['138','145'])).

thf('147',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_orders_2 @ sk_A @ sk_B @ X0 )
      | ( zip_tseitin_1 @ X0 @ X2 @ X1 @ sk_A )
      | ( zip_tseitin_0 @ X0 @ ( k5_waybel_0 @ sk_A @ sk_B ) @ X3 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['137','146'])).

thf('148',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ( zip_tseitin_1 @ X20 @ X21 @ X22 @ X23 )
      | ~ ( zip_tseitin_0 @ X20 @ X21 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('149',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( zip_tseitin_1 @ X1 @ X3 @ X2 @ sk_A )
      | ( r1_orders_2 @ sk_A @ sk_B @ X1 )
      | ( zip_tseitin_1 @ X1 @ ( k5_waybel_0 @ sk_A @ sk_B ) @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['147','148'])).

thf('150',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_1 @ X1 @ ( k5_waybel_0 @ sk_A @ sk_B ) @ X0 @ sk_A )
      | ( r1_orders_2 @ sk_A @ sk_B @ X1 ) ) ),
    inference(condensation,[status(thm)],['149'])).

thf('151',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(zf_stmt_3,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(zf_stmt_4,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_2 @ C @ B @ A )
     => ( ( B
          = ( k1_yellow_0 @ A @ C ) )
        & ( r1_yellow_0 @ A @ C ) ) ) )).

thf(zf_stmt_5,type,(
    zip_tseitin_1: $i > $i > $i > $i > $o )).

thf(zf_stmt_6,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(zf_stmt_7,axiom,(
    ! [A: $i] :
      ( ( ( v5_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( ( ( r2_lattice3 @ A @ C @ B )
                  & ! [D: $i] :
                      ( zip_tseitin_1 @ D @ C @ B @ A ) )
               => ( zip_tseitin_2 @ C @ B @ A ) )
              & ( ( ( B
                    = ( k1_yellow_0 @ A @ C ) )
                  & ( r1_yellow_0 @ A @ C ) )
               => ( ( r2_lattice3 @ A @ C @ B )
                  & ! [D: $i] :
                      ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                     => ( ( r2_lattice3 @ A @ C @ D )
                       => ( r1_orders_2 @ A @ B @ D ) ) ) ) ) ) ) ) )).

thf('152',plain,(
    ! [X27: $i,X28: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( u1_struct_0 @ X28 ) )
      | ~ ( r2_lattice3 @ X28 @ X31 @ X27 )
      | ~ ( zip_tseitin_1 @ ( sk_D_1 @ X31 @ X27 @ X28 ) @ X31 @ X27 @ X28 )
      | ( zip_tseitin_2 @ X31 @ X27 @ X28 )
      | ~ ( l1_orders_2 @ X28 )
      | ~ ( v5_orders_2 @ X28 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_7])).

thf('153',plain,(
    ! [X0: $i] :
      ( ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ( zip_tseitin_2 @ X0 @ sk_B @ sk_A )
      | ~ ( zip_tseitin_1 @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A )
      | ~ ( r2_lattice3 @ sk_A @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['151','152'])).

thf('154',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('155',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('156',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_2 @ X0 @ sk_B @ sk_A )
      | ~ ( zip_tseitin_1 @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A )
      | ~ ( r2_lattice3 @ sk_A @ X0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['153','154','155'])).

thf('157',plain,
    ( ( r1_orders_2 @ sk_A @ sk_B @ ( sk_D_1 @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_B @ sk_A ) )
    | ~ ( r2_lattice3 @ sk_A @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_B )
    | ( zip_tseitin_2 @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['150','156'])).

thf('158',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('159',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( u1_struct_0 @ X11 ) )
      | ( m1_subset_1 @ ( sk_D @ X10 @ X12 @ X11 ) @ ( u1_struct_0 @ X11 ) )
      | ( r2_lattice3 @ X11 @ X12 @ X10 )
      | ~ ( l1_orders_2 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d9_lattice3])).

thf('160',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ( r2_lattice3 @ sk_A @ X0 @ sk_B )
      | ( m1_subset_1 @ ( sk_D @ sk_B @ X0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['158','159'])).

thf('161',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('162',plain,(
    ! [X0: $i] :
      ( ( r2_lattice3 @ sk_A @ X0 @ sk_B )
      | ( m1_subset_1 @ ( sk_D @ sk_B @ X0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['160','161'])).

thf('163',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('164',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( u1_struct_0 @ X11 ) )
      | ( r2_hidden @ ( sk_D @ X10 @ X12 @ X11 ) @ X12 )
      | ( r2_lattice3 @ X11 @ X12 @ X10 )
      | ~ ( l1_orders_2 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d9_lattice3])).

thf('165',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ( r2_lattice3 @ sk_A @ X0 @ sk_B )
      | ( r2_hidden @ ( sk_D @ sk_B @ X0 @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['163','164'])).

thf('166',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('167',plain,(
    ! [X0: $i] :
      ( ( r2_lattice3 @ sk_A @ X0 @ sk_B )
      | ( r2_hidden @ ( sk_D @ sk_B @ X0 @ sk_A ) @ X0 ) ) ),
    inference(demod,[status(thm)],['165','166'])).

thf('168',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('169',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ~ ( m1_subset_1 @ X38 @ ( u1_struct_0 @ X39 ) )
      | ~ ( r2_hidden @ X40 @ ( k5_waybel_0 @ X39 @ X38 ) )
      | ( r1_orders_2 @ X39 @ X40 @ X38 )
      | ~ ( m1_subset_1 @ X40 @ ( u1_struct_0 @ X39 ) )
      | ~ ( l1_orders_2 @ X39 )
      | ( v2_struct_0 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t17_waybel_0])).

thf('170',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ X0 @ sk_B )
      | ~ ( r2_hidden @ X0 @ ( k5_waybel_0 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['168','169'])).

thf('171',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('172',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ X0 @ sk_B )
      | ~ ( r2_hidden @ X0 @ ( k5_waybel_0 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['170','171'])).

thf('173',plain,
    ( ( r2_lattice3 @ sk_A @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_B )
    | ( r1_orders_2 @ sk_A @ ( sk_D @ sk_B @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_A ) @ sk_B )
    | ~ ( m1_subset_1 @ ( sk_D @ sk_B @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['167','172'])).

thf('174',plain,
    ( ( r2_lattice3 @ sk_A @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( r1_orders_2 @ sk_A @ ( sk_D @ sk_B @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_A ) @ sk_B )
    | ( r2_lattice3 @ sk_A @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['162','173'])).

thf('175',plain,
    ( ( r1_orders_2 @ sk_A @ ( sk_D @ sk_B @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_A ) @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( r2_lattice3 @ sk_A @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(simplify,[status(thm)],['174'])).

thf('176',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('177',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( u1_struct_0 @ X11 ) )
      | ~ ( r1_orders_2 @ X11 @ ( sk_D @ X10 @ X12 @ X11 ) @ X10 )
      | ( r2_lattice3 @ X11 @ X12 @ X10 )
      | ~ ( l1_orders_2 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d9_lattice3])).

thf('178',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ( r2_lattice3 @ sk_A @ X0 @ sk_B )
      | ~ ( r1_orders_2 @ sk_A @ ( sk_D @ sk_B @ X0 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['176','177'])).

thf('179',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('180',plain,(
    ! [X0: $i] :
      ( ( r2_lattice3 @ sk_A @ X0 @ sk_B )
      | ~ ( r1_orders_2 @ sk_A @ ( sk_D @ sk_B @ X0 @ sk_A ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['178','179'])).

thf('181',plain,
    ( ( r2_lattice3 @ sk_A @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['175','180'])).

thf('182',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('183',plain,(
    r2_lattice3 @ sk_A @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_B ),
    inference(clc,[status(thm)],['181','182'])).

thf('184',plain,
    ( ( r1_orders_2 @ sk_A @ sk_B @ ( sk_D_1 @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_B @ sk_A ) )
    | ( zip_tseitin_2 @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['157','183'])).

thf('185',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ( zip_tseitin_0 @ X16 @ X17 @ X18 @ X19 )
      | ~ ( r1_orders_2 @ X19 @ X18 @ X16 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('186',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_2 @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_B @ sk_A )
      | ( zip_tseitin_0 @ ( sk_D_1 @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['184','185'])).

thf('187',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ( zip_tseitin_1 @ X20 @ X21 @ X22 @ X23 )
      | ~ ( zip_tseitin_0 @ X20 @ X21 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('188',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_2 @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_B @ sk_A )
      | ( zip_tseitin_1 @ ( sk_D_1 @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['186','187'])).

thf('189',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_2 @ X0 @ sk_B @ sk_A )
      | ~ ( zip_tseitin_1 @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A )
      | ~ ( r2_lattice3 @ sk_A @ X0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['153','154','155'])).

thf('190',plain,
    ( ( zip_tseitin_2 @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_B @ sk_A )
    | ~ ( r2_lattice3 @ sk_A @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_B )
    | ( zip_tseitin_2 @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['188','189'])).

thf('191',plain,(
    r2_lattice3 @ sk_A @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_B ),
    inference(clc,[status(thm)],['181','182'])).

thf('192',plain,
    ( ( zip_tseitin_2 @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_B @ sk_A )
    | ( zip_tseitin_2 @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['190','191'])).

thf('193',plain,(
    zip_tseitin_2 @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_B @ sk_A ),
    inference(simplify,[status(thm)],['192'])).

thf('194',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( X26
        = ( k1_yellow_0 @ X24 @ X25 ) )
      | ~ ( zip_tseitin_2 @ X25 @ X26 @ X24 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('195',plain,
    ( sk_B
    = ( k1_yellow_0 @ sk_A @ ( k5_waybel_0 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['193','194'])).

thf('196',plain,(
    v4_waybel_7 @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['106','195'])).

thf('197',plain,(
    $false ),
    inference(demod,[status(thm)],['0','196'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.qC6ACk9mMd
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 13:20:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.88/1.06  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.88/1.06  % Solved by: fo/fo7.sh
% 0.88/1.06  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.88/1.06  % done 578 iterations in 0.602s
% 0.88/1.06  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.88/1.06  % SZS output start Refutation
% 0.88/1.06  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.88/1.06  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.88/1.06  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.88/1.06  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i > $i).
% 0.88/1.06  thf(v1_waybel_7_type, type, v1_waybel_7: $i > $i > $o).
% 0.88/1.06  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.88/1.06  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.88/1.06  thf(sk_B_type, type, sk_B: $i).
% 0.88/1.06  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 0.88/1.06  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.88/1.06  thf(k5_waybel_0_type, type, k5_waybel_0: $i > $i > $i).
% 0.88/1.06  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $i > $o).
% 0.88/1.06  thf(sk_A_type, type, sk_A: $i).
% 0.88/1.06  thf(zip_tseitin_2_type, type, zip_tseitin_2: $i > $i > $i > $o).
% 0.88/1.06  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.88/1.06  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.88/1.06  thf(r2_lattice3_type, type, r2_lattice3: $i > $i > $i > $o).
% 0.88/1.06  thf(v12_waybel_0_type, type, v12_waybel_0: $i > $i > $o).
% 0.88/1.06  thf(v1_lattice3_type, type, v1_lattice3: $i > $o).
% 0.88/1.06  thf(v4_waybel_7_type, type, v4_waybel_7: $i > $i > $o).
% 0.88/1.06  thf(v2_lattice3_type, type, v2_lattice3: $i > $o).
% 0.88/1.06  thf(v1_waybel_0_type, type, v1_waybel_0: $i > $i > $o).
% 0.88/1.06  thf(r1_yellow_0_type, type, r1_yellow_0: $i > $i > $o).
% 0.88/1.06  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.88/1.06  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 0.88/1.06  thf(r3_orders_2_type, type, r3_orders_2: $i > $i > $i > $o).
% 0.88/1.06  thf(v5_waybel_6_type, type, v5_waybel_6: $i > $i > $o).
% 0.88/1.06  thf(r1_orders_2_type, type, r1_orders_2: $i > $i > $i > $o).
% 0.88/1.06  thf(k1_yellow_0_type, type, k1_yellow_0: $i > $i > $i).
% 0.88/1.06  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.88/1.06  thf(t38_waybel_7, conjecture,
% 0.88/1.06    (![A:$i]:
% 0.88/1.06     ( ( ( v3_orders_2 @ A ) & ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & 
% 0.88/1.06         ( v1_lattice3 @ A ) & ( v2_lattice3 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.88/1.06       ( ![B:$i]:
% 0.88/1.06         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.88/1.06           ( ( v5_waybel_6 @ B @ A ) => ( v4_waybel_7 @ B @ A ) ) ) ) ))).
% 0.88/1.06  thf(zf_stmt_0, negated_conjecture,
% 0.88/1.06    (~( ![A:$i]:
% 0.88/1.06        ( ( ( v3_orders_2 @ A ) & ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & 
% 0.88/1.06            ( v1_lattice3 @ A ) & ( v2_lattice3 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.88/1.06          ( ![B:$i]:
% 0.88/1.06            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.88/1.06              ( ( v5_waybel_6 @ B @ A ) => ( v4_waybel_7 @ B @ A ) ) ) ) ) )),
% 0.88/1.06    inference('cnf.neg', [status(esa)], [t38_waybel_7])).
% 0.88/1.06  thf('0', plain, (~ (v4_waybel_7 @ sk_B @ sk_A)),
% 0.88/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.88/1.06  thf('1', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.88/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.88/1.06  thf(dt_k5_waybel_0, axiom,
% 0.88/1.06    (![A:$i,B:$i]:
% 0.88/1.06     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_orders_2 @ A ) & 
% 0.88/1.06         ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) =>
% 0.88/1.06       ( m1_subset_1 @
% 0.88/1.06         ( k5_waybel_0 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.88/1.06  thf('2', plain,
% 0.88/1.06      (![X32 : $i, X33 : $i]:
% 0.88/1.06         (~ (l1_orders_2 @ X32)
% 0.88/1.06          | (v2_struct_0 @ X32)
% 0.88/1.06          | ~ (m1_subset_1 @ X33 @ (u1_struct_0 @ X32))
% 0.88/1.06          | (m1_subset_1 @ (k5_waybel_0 @ X32 @ X33) @ 
% 0.88/1.06             (k1_zfmisc_1 @ (u1_struct_0 @ X32))))),
% 0.88/1.06      inference('cnf', [status(esa)], [dt_k5_waybel_0])).
% 0.88/1.06  thf('3', plain,
% 0.88/1.06      (((m1_subset_1 @ (k5_waybel_0 @ sk_A @ sk_B) @ 
% 0.88/1.06         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.88/1.06        | (v2_struct_0 @ sk_A)
% 0.88/1.06        | ~ (l1_orders_2 @ sk_A))),
% 0.88/1.06      inference('sup-', [status(thm)], ['1', '2'])).
% 0.88/1.06  thf('4', plain, ((l1_orders_2 @ sk_A)),
% 0.88/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.88/1.06  thf('5', plain,
% 0.88/1.06      (((m1_subset_1 @ (k5_waybel_0 @ sk_A @ sk_B) @ 
% 0.88/1.06         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.88/1.06        | (v2_struct_0 @ sk_A))),
% 0.88/1.06      inference('demod', [status(thm)], ['3', '4'])).
% 0.88/1.06  thf('6', plain, ((l1_orders_2 @ sk_A)),
% 0.88/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.88/1.06  thf(cc1_lattice3, axiom,
% 0.88/1.06    (![A:$i]:
% 0.88/1.06     ( ( l1_orders_2 @ A ) =>
% 0.88/1.06       ( ( v1_lattice3 @ A ) => ( ~( v2_struct_0 @ A ) ) ) ))).
% 0.88/1.06  thf('7', plain,
% 0.88/1.06      (![X9 : $i]:
% 0.88/1.06         (~ (v1_lattice3 @ X9) | ~ (v2_struct_0 @ X9) | ~ (l1_orders_2 @ X9))),
% 0.88/1.06      inference('cnf', [status(esa)], [cc1_lattice3])).
% 0.88/1.06  thf('8', plain, ((~ (v2_struct_0 @ sk_A) | ~ (v1_lattice3 @ sk_A))),
% 0.88/1.06      inference('sup-', [status(thm)], ['6', '7'])).
% 0.88/1.06  thf('9', plain, ((v1_lattice3 @ sk_A)),
% 0.88/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.88/1.06  thf('10', plain, (~ (v2_struct_0 @ sk_A)),
% 0.88/1.06      inference('demod', [status(thm)], ['8', '9'])).
% 0.88/1.06  thf('11', plain,
% 0.88/1.06      ((m1_subset_1 @ (k5_waybel_0 @ sk_A @ sk_B) @ 
% 0.88/1.06        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.88/1.06      inference('clc', [status(thm)], ['5', '10'])).
% 0.88/1.06  thf(d6_waybel_7, axiom,
% 0.88/1.06    (![A:$i]:
% 0.88/1.06     ( ( ( v3_orders_2 @ A ) & ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & 
% 0.88/1.06         ( v1_lattice3 @ A ) & ( v2_lattice3 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.88/1.06       ( ![B:$i]:
% 0.88/1.06         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.88/1.06           ( ( v4_waybel_7 @ B @ A ) <=>
% 0.88/1.06             ( ?[C:$i]:
% 0.88/1.06               ( ( ( B ) = ( k1_yellow_0 @ A @ C ) ) & 
% 0.88/1.06                 ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) & 
% 0.88/1.06                 ( v1_waybel_7 @ C @ A ) & ( v12_waybel_0 @ C @ A ) & 
% 0.88/1.06                 ( v1_waybel_0 @ C @ A ) & ( ~( v1_xboole_0 @ C ) ) ) ) ) ) ) ))).
% 0.88/1.06  thf('12', plain,
% 0.88/1.06      (![X41 : $i, X42 : $i, X43 : $i]:
% 0.88/1.06         (~ (m1_subset_1 @ X41 @ (u1_struct_0 @ X42))
% 0.88/1.06          | ((X41) != (k1_yellow_0 @ X42 @ X43))
% 0.88/1.06          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (u1_struct_0 @ X42)))
% 0.88/1.06          | ~ (v1_waybel_7 @ X43 @ X42)
% 0.88/1.06          | ~ (v12_waybel_0 @ X43 @ X42)
% 0.88/1.06          | ~ (v1_waybel_0 @ X43 @ X42)
% 0.88/1.06          | (v1_xboole_0 @ X43)
% 0.88/1.06          | (v4_waybel_7 @ X41 @ X42)
% 0.88/1.06          | ~ (l1_orders_2 @ X42)
% 0.88/1.06          | ~ (v2_lattice3 @ X42)
% 0.88/1.06          | ~ (v1_lattice3 @ X42)
% 0.88/1.06          | ~ (v5_orders_2 @ X42)
% 0.88/1.06          | ~ (v4_orders_2 @ X42)
% 0.88/1.06          | ~ (v3_orders_2 @ X42))),
% 0.88/1.06      inference('cnf', [status(esa)], [d6_waybel_7])).
% 0.88/1.06  thf('13', plain,
% 0.88/1.06      (![X42 : $i, X43 : $i]:
% 0.88/1.06         (~ (v3_orders_2 @ X42)
% 0.88/1.06          | ~ (v4_orders_2 @ X42)
% 0.88/1.06          | ~ (v5_orders_2 @ X42)
% 0.88/1.06          | ~ (v1_lattice3 @ X42)
% 0.88/1.06          | ~ (v2_lattice3 @ X42)
% 0.88/1.06          | ~ (l1_orders_2 @ X42)
% 0.88/1.06          | (v4_waybel_7 @ (k1_yellow_0 @ X42 @ X43) @ X42)
% 0.88/1.06          | (v1_xboole_0 @ X43)
% 0.88/1.06          | ~ (v1_waybel_0 @ X43 @ X42)
% 0.88/1.06          | ~ (v12_waybel_0 @ X43 @ X42)
% 0.88/1.06          | ~ (v1_waybel_7 @ X43 @ X42)
% 0.88/1.06          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (u1_struct_0 @ X42)))
% 0.88/1.06          | ~ (m1_subset_1 @ (k1_yellow_0 @ X42 @ X43) @ (u1_struct_0 @ X42)))),
% 0.88/1.06      inference('simplify', [status(thm)], ['12'])).
% 0.88/1.06  thf('14', plain,
% 0.88/1.06      ((~ (m1_subset_1 @ (k1_yellow_0 @ sk_A @ (k5_waybel_0 @ sk_A @ sk_B)) @ 
% 0.88/1.06           (u1_struct_0 @ sk_A))
% 0.88/1.06        | ~ (v1_waybel_7 @ (k5_waybel_0 @ sk_A @ sk_B) @ sk_A)
% 0.88/1.06        | ~ (v12_waybel_0 @ (k5_waybel_0 @ sk_A @ sk_B) @ sk_A)
% 0.88/1.06        | ~ (v1_waybel_0 @ (k5_waybel_0 @ sk_A @ sk_B) @ sk_A)
% 0.88/1.06        | (v1_xboole_0 @ (k5_waybel_0 @ sk_A @ sk_B))
% 0.88/1.06        | (v4_waybel_7 @ (k1_yellow_0 @ sk_A @ (k5_waybel_0 @ sk_A @ sk_B)) @ 
% 0.88/1.06           sk_A)
% 0.88/1.06        | ~ (l1_orders_2 @ sk_A)
% 0.88/1.06        | ~ (v2_lattice3 @ sk_A)
% 0.88/1.06        | ~ (v1_lattice3 @ sk_A)
% 0.88/1.06        | ~ (v5_orders_2 @ sk_A)
% 0.88/1.06        | ~ (v4_orders_2 @ sk_A)
% 0.88/1.06        | ~ (v3_orders_2 @ sk_A))),
% 0.88/1.06      inference('sup-', [status(thm)], ['11', '13'])).
% 0.88/1.06  thf(dt_k1_yellow_0, axiom,
% 0.88/1.06    (![A:$i,B:$i]:
% 0.88/1.06     ( ( l1_orders_2 @ A ) =>
% 0.88/1.06       ( m1_subset_1 @ ( k1_yellow_0 @ A @ B ) @ ( u1_struct_0 @ A ) ) ))).
% 0.88/1.06  thf('15', plain,
% 0.88/1.06      (![X14 : $i, X15 : $i]:
% 0.88/1.06         (~ (l1_orders_2 @ X14)
% 0.88/1.06          | (m1_subset_1 @ (k1_yellow_0 @ X14 @ X15) @ (u1_struct_0 @ X14)))),
% 0.88/1.06      inference('cnf', [status(esa)], [dt_k1_yellow_0])).
% 0.88/1.06  thf('16', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.88/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.88/1.06  thf('17', plain,
% 0.88/1.06      (![X14 : $i, X15 : $i]:
% 0.88/1.06         (~ (l1_orders_2 @ X14)
% 0.88/1.06          | (m1_subset_1 @ (k1_yellow_0 @ X14 @ X15) @ (u1_struct_0 @ X14)))),
% 0.88/1.06      inference('cnf', [status(esa)], [dt_k1_yellow_0])).
% 0.88/1.06  thf(reflexivity_r3_orders_2, axiom,
% 0.88/1.06    (![A:$i,B:$i,C:$i]:
% 0.88/1.06     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.88/1.06         ( l1_orders_2 @ A ) & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 0.88/1.06         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 0.88/1.06       ( r3_orders_2 @ A @ B @ B ) ))).
% 0.88/1.06  thf('18', plain,
% 0.88/1.06      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.88/1.06         ((r3_orders_2 @ X6 @ X7 @ X7)
% 0.88/1.06          | ~ (m1_subset_1 @ X7 @ (u1_struct_0 @ X6))
% 0.88/1.06          | ~ (l1_orders_2 @ X6)
% 0.88/1.06          | ~ (v3_orders_2 @ X6)
% 0.88/1.06          | (v2_struct_0 @ X6)
% 0.88/1.06          | ~ (m1_subset_1 @ X8 @ (u1_struct_0 @ X6)))),
% 0.88/1.06      inference('cnf', [status(esa)], [reflexivity_r3_orders_2])).
% 0.88/1.06  thf('19', plain,
% 0.88/1.06      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.88/1.06         (~ (l1_orders_2 @ X0)
% 0.88/1.06          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.88/1.06          | (v2_struct_0 @ X0)
% 0.88/1.06          | ~ (v3_orders_2 @ X0)
% 0.88/1.06          | ~ (l1_orders_2 @ X0)
% 0.88/1.06          | (r3_orders_2 @ X0 @ (k1_yellow_0 @ X0 @ X1) @ 
% 0.88/1.06             (k1_yellow_0 @ X0 @ X1)))),
% 0.88/1.06      inference('sup-', [status(thm)], ['17', '18'])).
% 0.88/1.06  thf('20', plain,
% 0.88/1.06      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.88/1.06         ((r3_orders_2 @ X0 @ (k1_yellow_0 @ X0 @ X1) @ (k1_yellow_0 @ X0 @ X1))
% 0.88/1.06          | ~ (v3_orders_2 @ X0)
% 0.88/1.06          | (v2_struct_0 @ X0)
% 0.88/1.06          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.88/1.06          | ~ (l1_orders_2 @ X0))),
% 0.88/1.06      inference('simplify', [status(thm)], ['19'])).
% 0.88/1.06  thf('21', plain,
% 0.88/1.06      (![X0 : $i]:
% 0.88/1.06         (~ (l1_orders_2 @ sk_A)
% 0.88/1.06          | (v2_struct_0 @ sk_A)
% 0.88/1.06          | ~ (v3_orders_2 @ sk_A)
% 0.88/1.06          | (r3_orders_2 @ sk_A @ (k1_yellow_0 @ sk_A @ X0) @ 
% 0.88/1.06             (k1_yellow_0 @ sk_A @ X0)))),
% 0.88/1.06      inference('sup-', [status(thm)], ['16', '20'])).
% 0.88/1.06  thf('22', plain, ((l1_orders_2 @ sk_A)),
% 0.88/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.88/1.06  thf('23', plain, ((v3_orders_2 @ sk_A)),
% 0.88/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.88/1.06  thf('24', plain,
% 0.88/1.06      (![X0 : $i]:
% 0.88/1.06         ((v2_struct_0 @ sk_A)
% 0.88/1.06          | (r3_orders_2 @ sk_A @ (k1_yellow_0 @ sk_A @ X0) @ 
% 0.88/1.06             (k1_yellow_0 @ sk_A @ X0)))),
% 0.88/1.06      inference('demod', [status(thm)], ['21', '22', '23'])).
% 0.88/1.06  thf('25', plain, (~ (v2_struct_0 @ sk_A)),
% 0.88/1.06      inference('demod', [status(thm)], ['8', '9'])).
% 0.88/1.06  thf('26', plain,
% 0.88/1.06      (![X0 : $i]:
% 0.88/1.06         (r3_orders_2 @ sk_A @ (k1_yellow_0 @ sk_A @ X0) @ 
% 0.88/1.06          (k1_yellow_0 @ sk_A @ X0))),
% 0.88/1.06      inference('clc', [status(thm)], ['24', '25'])).
% 0.88/1.06  thf('27', plain,
% 0.88/1.06      (![X14 : $i, X15 : $i]:
% 0.88/1.06         (~ (l1_orders_2 @ X14)
% 0.88/1.06          | (m1_subset_1 @ (k1_yellow_0 @ X14 @ X15) @ (u1_struct_0 @ X14)))),
% 0.88/1.06      inference('cnf', [status(esa)], [dt_k1_yellow_0])).
% 0.88/1.06  thf('28', plain,
% 0.88/1.06      (![X14 : $i, X15 : $i]:
% 0.88/1.06         (~ (l1_orders_2 @ X14)
% 0.88/1.06          | (m1_subset_1 @ (k1_yellow_0 @ X14 @ X15) @ (u1_struct_0 @ X14)))),
% 0.88/1.06      inference('cnf', [status(esa)], [dt_k1_yellow_0])).
% 0.88/1.06  thf(redefinition_r3_orders_2, axiom,
% 0.88/1.06    (![A:$i,B:$i,C:$i]:
% 0.88/1.06     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.88/1.06         ( l1_orders_2 @ A ) & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 0.88/1.06         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 0.88/1.06       ( ( r3_orders_2 @ A @ B @ C ) <=> ( r1_orders_2 @ A @ B @ C ) ) ))).
% 0.88/1.06  thf('29', plain,
% 0.88/1.06      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.88/1.06         (~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X4))
% 0.88/1.06          | ~ (l1_orders_2 @ X4)
% 0.88/1.06          | ~ (v3_orders_2 @ X4)
% 0.88/1.06          | (v2_struct_0 @ X4)
% 0.88/1.06          | ~ (m1_subset_1 @ X5 @ (u1_struct_0 @ X4))
% 0.88/1.06          | (r1_orders_2 @ X4 @ X3 @ X5)
% 0.88/1.06          | ~ (r3_orders_2 @ X4 @ X3 @ X5))),
% 0.88/1.06      inference('cnf', [status(esa)], [redefinition_r3_orders_2])).
% 0.88/1.06  thf('30', plain,
% 0.88/1.06      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.88/1.06         (~ (l1_orders_2 @ X0)
% 0.88/1.06          | ~ (r3_orders_2 @ X0 @ (k1_yellow_0 @ X0 @ X1) @ X2)
% 0.88/1.06          | (r1_orders_2 @ X0 @ (k1_yellow_0 @ X0 @ X1) @ X2)
% 0.88/1.06          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.88/1.06          | (v2_struct_0 @ X0)
% 0.88/1.06          | ~ (v3_orders_2 @ X0)
% 0.88/1.06          | ~ (l1_orders_2 @ X0))),
% 0.88/1.06      inference('sup-', [status(thm)], ['28', '29'])).
% 0.88/1.06  thf('31', plain,
% 0.88/1.06      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.88/1.06         (~ (v3_orders_2 @ X0)
% 0.88/1.06          | (v2_struct_0 @ X0)
% 0.88/1.06          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.88/1.06          | (r1_orders_2 @ X0 @ (k1_yellow_0 @ X0 @ X1) @ X2)
% 0.88/1.06          | ~ (r3_orders_2 @ X0 @ (k1_yellow_0 @ X0 @ X1) @ X2)
% 0.88/1.06          | ~ (l1_orders_2 @ X0))),
% 0.88/1.06      inference('simplify', [status(thm)], ['30'])).
% 0.88/1.06  thf('32', plain,
% 0.88/1.06      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.88/1.06         (~ (l1_orders_2 @ X0)
% 0.88/1.06          | ~ (l1_orders_2 @ X0)
% 0.88/1.06          | ~ (r3_orders_2 @ X0 @ (k1_yellow_0 @ X0 @ X2) @ 
% 0.88/1.06               (k1_yellow_0 @ X0 @ X1))
% 0.88/1.06          | (r1_orders_2 @ X0 @ (k1_yellow_0 @ X0 @ X2) @ 
% 0.88/1.06             (k1_yellow_0 @ X0 @ X1))
% 0.88/1.06          | (v2_struct_0 @ X0)
% 0.88/1.06          | ~ (v3_orders_2 @ X0))),
% 0.88/1.06      inference('sup-', [status(thm)], ['27', '31'])).
% 0.88/1.06  thf('33', plain,
% 0.88/1.06      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.88/1.06         (~ (v3_orders_2 @ X0)
% 0.88/1.06          | (v2_struct_0 @ X0)
% 0.88/1.06          | (r1_orders_2 @ X0 @ (k1_yellow_0 @ X0 @ X2) @ 
% 0.88/1.06             (k1_yellow_0 @ X0 @ X1))
% 0.88/1.06          | ~ (r3_orders_2 @ X0 @ (k1_yellow_0 @ X0 @ X2) @ 
% 0.88/1.06               (k1_yellow_0 @ X0 @ X1))
% 0.88/1.06          | ~ (l1_orders_2 @ X0))),
% 0.88/1.06      inference('simplify', [status(thm)], ['32'])).
% 0.88/1.06  thf('34', plain,
% 0.88/1.06      (![X0 : $i]:
% 0.88/1.06         (~ (l1_orders_2 @ sk_A)
% 0.88/1.06          | (r1_orders_2 @ sk_A @ (k1_yellow_0 @ sk_A @ X0) @ 
% 0.88/1.06             (k1_yellow_0 @ sk_A @ X0))
% 0.88/1.06          | (v2_struct_0 @ sk_A)
% 0.88/1.06          | ~ (v3_orders_2 @ sk_A))),
% 0.88/1.06      inference('sup-', [status(thm)], ['26', '33'])).
% 0.88/1.06  thf('35', plain, ((l1_orders_2 @ sk_A)),
% 0.88/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.88/1.06  thf('36', plain, ((v3_orders_2 @ sk_A)),
% 0.88/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.88/1.06  thf('37', plain,
% 0.88/1.06      (![X0 : $i]:
% 0.88/1.06         ((r1_orders_2 @ sk_A @ (k1_yellow_0 @ sk_A @ X0) @ 
% 0.88/1.06           (k1_yellow_0 @ sk_A @ X0))
% 0.88/1.06          | (v2_struct_0 @ sk_A))),
% 0.88/1.06      inference('demod', [status(thm)], ['34', '35', '36'])).
% 0.88/1.06  thf('38', plain, (~ (v2_struct_0 @ sk_A)),
% 0.88/1.06      inference('demod', [status(thm)], ['8', '9'])).
% 0.88/1.06  thf('39', plain,
% 0.88/1.06      (![X0 : $i]:
% 0.88/1.06         (r1_orders_2 @ sk_A @ (k1_yellow_0 @ sk_A @ X0) @ 
% 0.88/1.06          (k1_yellow_0 @ sk_A @ X0))),
% 0.88/1.06      inference('clc', [status(thm)], ['37', '38'])).
% 0.88/1.06  thf('40', plain,
% 0.88/1.06      (![X14 : $i, X15 : $i]:
% 0.88/1.06         (~ (l1_orders_2 @ X14)
% 0.88/1.06          | (m1_subset_1 @ (k1_yellow_0 @ X14 @ X15) @ (u1_struct_0 @ X14)))),
% 0.88/1.06      inference('cnf', [status(esa)], [dt_k1_yellow_0])).
% 0.88/1.06  thf(t17_waybel_0, axiom,
% 0.88/1.06    (![A:$i]:
% 0.88/1.06     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_orders_2 @ A ) ) =>
% 0.88/1.06       ( ![B:$i]:
% 0.88/1.06         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.88/1.06           ( ![C:$i]:
% 0.88/1.06             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.88/1.06               ( ( r2_hidden @ C @ ( k5_waybel_0 @ A @ B ) ) <=>
% 0.88/1.06                 ( r1_orders_2 @ A @ C @ B ) ) ) ) ) ) ))).
% 0.88/1.06  thf('41', plain,
% 0.88/1.06      (![X38 : $i, X39 : $i, X40 : $i]:
% 0.88/1.06         (~ (m1_subset_1 @ X38 @ (u1_struct_0 @ X39))
% 0.88/1.06          | ~ (r1_orders_2 @ X39 @ X40 @ X38)
% 0.88/1.06          | (r2_hidden @ X40 @ (k5_waybel_0 @ X39 @ X38))
% 0.88/1.06          | ~ (m1_subset_1 @ X40 @ (u1_struct_0 @ X39))
% 0.88/1.06          | ~ (l1_orders_2 @ X39)
% 0.88/1.06          | (v2_struct_0 @ X39))),
% 0.88/1.06      inference('cnf', [status(esa)], [t17_waybel_0])).
% 0.88/1.06  thf('42', plain,
% 0.88/1.06      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.88/1.06         (~ (l1_orders_2 @ X0)
% 0.88/1.06          | (v2_struct_0 @ X0)
% 0.88/1.06          | ~ (l1_orders_2 @ X0)
% 0.88/1.06          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.88/1.06          | (r2_hidden @ X2 @ (k5_waybel_0 @ X0 @ (k1_yellow_0 @ X0 @ X1)))
% 0.88/1.06          | ~ (r1_orders_2 @ X0 @ X2 @ (k1_yellow_0 @ X0 @ X1)))),
% 0.88/1.06      inference('sup-', [status(thm)], ['40', '41'])).
% 0.88/1.06  thf('43', plain,
% 0.88/1.06      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.88/1.06         (~ (r1_orders_2 @ X0 @ X2 @ (k1_yellow_0 @ X0 @ X1))
% 0.88/1.06          | (r2_hidden @ X2 @ (k5_waybel_0 @ X0 @ (k1_yellow_0 @ X0 @ X1)))
% 0.88/1.06          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.88/1.06          | (v2_struct_0 @ X0)
% 0.88/1.06          | ~ (l1_orders_2 @ X0))),
% 0.88/1.06      inference('simplify', [status(thm)], ['42'])).
% 0.88/1.06  thf('44', plain,
% 0.88/1.06      (![X0 : $i]:
% 0.88/1.06         (~ (l1_orders_2 @ sk_A)
% 0.88/1.06          | (v2_struct_0 @ sk_A)
% 0.88/1.06          | ~ (m1_subset_1 @ (k1_yellow_0 @ sk_A @ X0) @ (u1_struct_0 @ sk_A))
% 0.88/1.06          | (r2_hidden @ (k1_yellow_0 @ sk_A @ X0) @ 
% 0.88/1.06             (k5_waybel_0 @ sk_A @ (k1_yellow_0 @ sk_A @ X0))))),
% 0.88/1.06      inference('sup-', [status(thm)], ['39', '43'])).
% 0.88/1.06  thf('45', plain, ((l1_orders_2 @ sk_A)),
% 0.88/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.88/1.06  thf('46', plain,
% 0.88/1.06      (![X0 : $i]:
% 0.88/1.06         ((v2_struct_0 @ sk_A)
% 0.88/1.06          | ~ (m1_subset_1 @ (k1_yellow_0 @ sk_A @ X0) @ (u1_struct_0 @ sk_A))
% 0.88/1.06          | (r2_hidden @ (k1_yellow_0 @ sk_A @ X0) @ 
% 0.88/1.06             (k5_waybel_0 @ sk_A @ (k1_yellow_0 @ sk_A @ X0))))),
% 0.88/1.06      inference('demod', [status(thm)], ['44', '45'])).
% 0.88/1.06  thf('47', plain, (~ (v2_struct_0 @ sk_A)),
% 0.88/1.06      inference('demod', [status(thm)], ['8', '9'])).
% 0.88/1.06  thf('48', plain,
% 0.88/1.06      (![X0 : $i]:
% 0.88/1.06         ((r2_hidden @ (k1_yellow_0 @ sk_A @ X0) @ 
% 0.88/1.06           (k5_waybel_0 @ sk_A @ (k1_yellow_0 @ sk_A @ X0)))
% 0.88/1.06          | ~ (m1_subset_1 @ (k1_yellow_0 @ sk_A @ X0) @ (u1_struct_0 @ sk_A)))),
% 0.88/1.06      inference('clc', [status(thm)], ['46', '47'])).
% 0.88/1.06  thf('49', plain,
% 0.88/1.06      (![X0 : $i]:
% 0.88/1.06         (~ (l1_orders_2 @ sk_A)
% 0.88/1.06          | (r2_hidden @ (k1_yellow_0 @ sk_A @ X0) @ 
% 0.88/1.06             (k5_waybel_0 @ sk_A @ (k1_yellow_0 @ sk_A @ X0))))),
% 0.88/1.06      inference('sup-', [status(thm)], ['15', '48'])).
% 0.88/1.06  thf('50', plain, ((l1_orders_2 @ sk_A)),
% 0.88/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.88/1.06  thf('51', plain,
% 0.88/1.06      (![X0 : $i]:
% 0.88/1.06         (r2_hidden @ (k1_yellow_0 @ sk_A @ X0) @ 
% 0.88/1.06          (k5_waybel_0 @ sk_A @ (k1_yellow_0 @ sk_A @ X0)))),
% 0.88/1.06      inference('demod', [status(thm)], ['49', '50'])).
% 0.88/1.06  thf('52', plain,
% 0.88/1.07      (![X14 : $i, X15 : $i]:
% 0.88/1.07         (~ (l1_orders_2 @ X14)
% 0.88/1.07          | (m1_subset_1 @ (k1_yellow_0 @ X14 @ X15) @ (u1_struct_0 @ X14)))),
% 0.88/1.07      inference('cnf', [status(esa)], [dt_k1_yellow_0])).
% 0.88/1.07  thf('53', plain,
% 0.88/1.07      (![X32 : $i, X33 : $i]:
% 0.88/1.07         (~ (l1_orders_2 @ X32)
% 0.88/1.07          | (v2_struct_0 @ X32)
% 0.88/1.07          | ~ (m1_subset_1 @ X33 @ (u1_struct_0 @ X32))
% 0.88/1.07          | (m1_subset_1 @ (k5_waybel_0 @ X32 @ X33) @ 
% 0.88/1.07             (k1_zfmisc_1 @ (u1_struct_0 @ X32))))),
% 0.88/1.07      inference('cnf', [status(esa)], [dt_k5_waybel_0])).
% 0.88/1.07  thf('54', plain,
% 0.88/1.07      (![X0 : $i, X1 : $i]:
% 0.88/1.07         (~ (l1_orders_2 @ X0)
% 0.88/1.07          | (m1_subset_1 @ (k5_waybel_0 @ X0 @ (k1_yellow_0 @ X0 @ X1)) @ 
% 0.88/1.07             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.88/1.07          | (v2_struct_0 @ X0)
% 0.88/1.07          | ~ (l1_orders_2 @ X0))),
% 0.88/1.07      inference('sup-', [status(thm)], ['52', '53'])).
% 0.88/1.07  thf('55', plain,
% 0.88/1.07      (![X0 : $i, X1 : $i]:
% 0.88/1.07         ((v2_struct_0 @ X0)
% 0.88/1.07          | (m1_subset_1 @ (k5_waybel_0 @ X0 @ (k1_yellow_0 @ X0 @ X1)) @ 
% 0.88/1.07             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.88/1.07          | ~ (l1_orders_2 @ X0))),
% 0.88/1.07      inference('simplify', [status(thm)], ['54'])).
% 0.88/1.07  thf(t4_subset, axiom,
% 0.88/1.07    (![A:$i,B:$i,C:$i]:
% 0.88/1.07     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 0.88/1.07       ( m1_subset_1 @ A @ C ) ))).
% 0.88/1.07  thf('56', plain,
% 0.88/1.07      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.88/1.07         (~ (r2_hidden @ X0 @ X1)
% 0.88/1.07          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X2))
% 0.88/1.07          | (m1_subset_1 @ X0 @ X2))),
% 0.88/1.07      inference('cnf', [status(esa)], [t4_subset])).
% 0.88/1.07  thf('57', plain,
% 0.88/1.07      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.88/1.07         (~ (l1_orders_2 @ X0)
% 0.88/1.07          | (v2_struct_0 @ X0)
% 0.88/1.07          | (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.88/1.07          | ~ (r2_hidden @ X2 @ (k5_waybel_0 @ X0 @ (k1_yellow_0 @ X0 @ X1))))),
% 0.88/1.07      inference('sup-', [status(thm)], ['55', '56'])).
% 0.88/1.07  thf('58', plain,
% 0.88/1.07      (![X0 : $i]:
% 0.88/1.07         ((m1_subset_1 @ (k1_yellow_0 @ sk_A @ X0) @ (u1_struct_0 @ sk_A))
% 0.88/1.07          | (v2_struct_0 @ sk_A)
% 0.88/1.07          | ~ (l1_orders_2 @ sk_A))),
% 0.88/1.07      inference('sup-', [status(thm)], ['51', '57'])).
% 0.88/1.07  thf('59', plain, ((l1_orders_2 @ sk_A)),
% 0.88/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.88/1.07  thf('60', plain,
% 0.88/1.07      (![X0 : $i]:
% 0.88/1.07         ((m1_subset_1 @ (k1_yellow_0 @ sk_A @ X0) @ (u1_struct_0 @ sk_A))
% 0.88/1.07          | (v2_struct_0 @ sk_A))),
% 0.88/1.07      inference('demod', [status(thm)], ['58', '59'])).
% 0.88/1.07  thf('61', plain, (~ (v2_struct_0 @ sk_A)),
% 0.88/1.07      inference('demod', [status(thm)], ['8', '9'])).
% 0.88/1.07  thf('62', plain,
% 0.88/1.07      (![X0 : $i]:
% 0.88/1.07         (m1_subset_1 @ (k1_yellow_0 @ sk_A @ X0) @ (u1_struct_0 @ sk_A))),
% 0.88/1.07      inference('clc', [status(thm)], ['60', '61'])).
% 0.88/1.07  thf('63', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.88/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.88/1.07  thf(fc12_waybel_0, axiom,
% 0.88/1.07    (![A:$i,B:$i]:
% 0.88/1.07     ( ( ( ~( v2_struct_0 @ A ) ) & ( v4_orders_2 @ A ) & 
% 0.88/1.07         ( l1_orders_2 @ A ) & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) =>
% 0.88/1.07       ( v12_waybel_0 @ ( k5_waybel_0 @ A @ B ) @ A ) ))).
% 0.88/1.07  thf('64', plain,
% 0.88/1.07      (![X34 : $i, X35 : $i]:
% 0.88/1.07         (~ (l1_orders_2 @ X34)
% 0.88/1.07          | ~ (v4_orders_2 @ X34)
% 0.88/1.07          | (v2_struct_0 @ X34)
% 0.88/1.07          | ~ (m1_subset_1 @ X35 @ (u1_struct_0 @ X34))
% 0.88/1.07          | (v12_waybel_0 @ (k5_waybel_0 @ X34 @ X35) @ X34))),
% 0.88/1.07      inference('cnf', [status(esa)], [fc12_waybel_0])).
% 0.88/1.07  thf('65', plain,
% 0.88/1.07      (((v12_waybel_0 @ (k5_waybel_0 @ sk_A @ sk_B) @ sk_A)
% 0.88/1.07        | (v2_struct_0 @ sk_A)
% 0.88/1.07        | ~ (v4_orders_2 @ sk_A)
% 0.88/1.07        | ~ (l1_orders_2 @ sk_A))),
% 0.88/1.07      inference('sup-', [status(thm)], ['63', '64'])).
% 0.88/1.07  thf('66', plain, ((v4_orders_2 @ sk_A)),
% 0.88/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.88/1.07  thf('67', plain, ((l1_orders_2 @ sk_A)),
% 0.88/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.88/1.07  thf('68', plain,
% 0.88/1.07      (((v12_waybel_0 @ (k5_waybel_0 @ sk_A @ sk_B) @ sk_A)
% 0.88/1.07        | (v2_struct_0 @ sk_A))),
% 0.88/1.07      inference('demod', [status(thm)], ['65', '66', '67'])).
% 0.88/1.07  thf('69', plain, (~ (v2_struct_0 @ sk_A)),
% 0.88/1.07      inference('demod', [status(thm)], ['8', '9'])).
% 0.88/1.07  thf('70', plain, ((v12_waybel_0 @ (k5_waybel_0 @ sk_A @ sk_B) @ sk_A)),
% 0.88/1.07      inference('clc', [status(thm)], ['68', '69'])).
% 0.88/1.07  thf('71', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.88/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.88/1.07  thf(fc8_waybel_0, axiom,
% 0.88/1.07    (![A:$i,B:$i]:
% 0.88/1.07     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.88/1.07         ( l1_orders_2 @ A ) & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) =>
% 0.88/1.07       ( ( ~( v1_xboole_0 @ ( k5_waybel_0 @ A @ B ) ) ) & 
% 0.88/1.07         ( v1_waybel_0 @ ( k5_waybel_0 @ A @ B ) @ A ) ) ))).
% 0.88/1.07  thf('72', plain,
% 0.88/1.07      (![X36 : $i, X37 : $i]:
% 0.88/1.07         (~ (l1_orders_2 @ X36)
% 0.88/1.07          | ~ (v3_orders_2 @ X36)
% 0.88/1.07          | (v2_struct_0 @ X36)
% 0.88/1.07          | ~ (m1_subset_1 @ X37 @ (u1_struct_0 @ X36))
% 0.88/1.07          | (v1_waybel_0 @ (k5_waybel_0 @ X36 @ X37) @ X36))),
% 0.88/1.07      inference('cnf', [status(esa)], [fc8_waybel_0])).
% 0.88/1.07  thf('73', plain,
% 0.88/1.07      (((v1_waybel_0 @ (k5_waybel_0 @ sk_A @ sk_B) @ sk_A)
% 0.88/1.07        | (v2_struct_0 @ sk_A)
% 0.88/1.07        | ~ (v3_orders_2 @ sk_A)
% 0.88/1.07        | ~ (l1_orders_2 @ sk_A))),
% 0.88/1.07      inference('sup-', [status(thm)], ['71', '72'])).
% 0.88/1.07  thf('74', plain, ((v3_orders_2 @ sk_A)),
% 0.88/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.88/1.07  thf('75', plain, ((l1_orders_2 @ sk_A)),
% 0.88/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.88/1.07  thf('76', plain,
% 0.88/1.07      (((v1_waybel_0 @ (k5_waybel_0 @ sk_A @ sk_B) @ sk_A)
% 0.88/1.07        | (v2_struct_0 @ sk_A))),
% 0.88/1.07      inference('demod', [status(thm)], ['73', '74', '75'])).
% 0.88/1.07  thf('77', plain, (~ (v2_struct_0 @ sk_A)),
% 0.88/1.07      inference('demod', [status(thm)], ['8', '9'])).
% 0.88/1.07  thf('78', plain, ((v1_waybel_0 @ (k5_waybel_0 @ sk_A @ sk_B) @ sk_A)),
% 0.88/1.07      inference('clc', [status(thm)], ['76', '77'])).
% 0.88/1.07  thf('79', plain, ((l1_orders_2 @ sk_A)),
% 0.88/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.88/1.07  thf('80', plain, ((v2_lattice3 @ sk_A)),
% 0.88/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.88/1.07  thf('81', plain, ((v1_lattice3 @ sk_A)),
% 0.88/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.88/1.07  thf('82', plain, ((v5_orders_2 @ sk_A)),
% 0.88/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.88/1.07  thf('83', plain, ((v4_orders_2 @ sk_A)),
% 0.88/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.88/1.07  thf('84', plain, ((v3_orders_2 @ sk_A)),
% 0.88/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.88/1.07  thf('85', plain,
% 0.88/1.07      ((~ (v1_waybel_7 @ (k5_waybel_0 @ sk_A @ sk_B) @ sk_A)
% 0.88/1.07        | (v1_xboole_0 @ (k5_waybel_0 @ sk_A @ sk_B))
% 0.88/1.07        | (v4_waybel_7 @ (k1_yellow_0 @ sk_A @ (k5_waybel_0 @ sk_A @ sk_B)) @ 
% 0.88/1.07           sk_A))),
% 0.88/1.07      inference('demod', [status(thm)],
% 0.88/1.07                ['14', '62', '70', '78', '79', '80', '81', '82', '83', '84'])).
% 0.88/1.07  thf('86', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.88/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.88/1.07  thf('87', plain,
% 0.88/1.07      (![X36 : $i, X37 : $i]:
% 0.88/1.07         (~ (l1_orders_2 @ X36)
% 0.88/1.07          | ~ (v3_orders_2 @ X36)
% 0.88/1.07          | (v2_struct_0 @ X36)
% 0.88/1.07          | ~ (m1_subset_1 @ X37 @ (u1_struct_0 @ X36))
% 0.88/1.07          | ~ (v1_xboole_0 @ (k5_waybel_0 @ X36 @ X37)))),
% 0.88/1.07      inference('cnf', [status(esa)], [fc8_waybel_0])).
% 0.88/1.07  thf('88', plain,
% 0.88/1.07      ((~ (v1_xboole_0 @ (k5_waybel_0 @ sk_A @ sk_B))
% 0.88/1.07        | (v2_struct_0 @ sk_A)
% 0.88/1.07        | ~ (v3_orders_2 @ sk_A)
% 0.88/1.07        | ~ (l1_orders_2 @ sk_A))),
% 0.88/1.07      inference('sup-', [status(thm)], ['86', '87'])).
% 0.88/1.07  thf('89', plain, ((v3_orders_2 @ sk_A)),
% 0.88/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.88/1.07  thf('90', plain, ((l1_orders_2 @ sk_A)),
% 0.88/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.88/1.07  thf('91', plain,
% 0.88/1.07      ((~ (v1_xboole_0 @ (k5_waybel_0 @ sk_A @ sk_B)) | (v2_struct_0 @ sk_A))),
% 0.88/1.07      inference('demod', [status(thm)], ['88', '89', '90'])).
% 0.88/1.07  thf('92', plain, (~ (v2_struct_0 @ sk_A)),
% 0.88/1.07      inference('demod', [status(thm)], ['8', '9'])).
% 0.88/1.07  thf('93', plain, (~ (v1_xboole_0 @ (k5_waybel_0 @ sk_A @ sk_B))),
% 0.88/1.07      inference('clc', [status(thm)], ['91', '92'])).
% 0.88/1.07  thf('94', plain,
% 0.88/1.07      (((v4_waybel_7 @ (k1_yellow_0 @ sk_A @ (k5_waybel_0 @ sk_A @ sk_B)) @ 
% 0.88/1.07         sk_A)
% 0.88/1.07        | ~ (v1_waybel_7 @ (k5_waybel_0 @ sk_A @ sk_B) @ sk_A))),
% 0.88/1.07      inference('clc', [status(thm)], ['85', '93'])).
% 0.88/1.07  thf('95', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.88/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.88/1.07  thf(t37_waybel_7, axiom,
% 0.88/1.07    (![A:$i]:
% 0.88/1.07     ( ( ( v3_orders_2 @ A ) & ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & 
% 0.88/1.07         ( v1_lattice3 @ A ) & ( v2_lattice3 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.88/1.07       ( ![B:$i]:
% 0.88/1.07         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.88/1.07           ( ( v5_waybel_6 @ B @ A ) =>
% 0.88/1.07             ( v1_waybel_7 @ ( k5_waybel_0 @ A @ B ) @ A ) ) ) ) ))).
% 0.88/1.07  thf('96', plain,
% 0.88/1.07      (![X44 : $i, X45 : $i]:
% 0.88/1.07         (~ (m1_subset_1 @ X44 @ (u1_struct_0 @ X45))
% 0.88/1.07          | (v1_waybel_7 @ (k5_waybel_0 @ X45 @ X44) @ X45)
% 0.88/1.07          | ~ (v5_waybel_6 @ X44 @ X45)
% 0.88/1.07          | ~ (l1_orders_2 @ X45)
% 0.88/1.07          | ~ (v2_lattice3 @ X45)
% 0.88/1.07          | ~ (v1_lattice3 @ X45)
% 0.88/1.07          | ~ (v5_orders_2 @ X45)
% 0.88/1.07          | ~ (v4_orders_2 @ X45)
% 0.88/1.07          | ~ (v3_orders_2 @ X45))),
% 0.88/1.07      inference('cnf', [status(esa)], [t37_waybel_7])).
% 0.88/1.07  thf('97', plain,
% 0.88/1.07      ((~ (v3_orders_2 @ sk_A)
% 0.88/1.07        | ~ (v4_orders_2 @ sk_A)
% 0.88/1.07        | ~ (v5_orders_2 @ sk_A)
% 0.88/1.07        | ~ (v1_lattice3 @ sk_A)
% 0.88/1.07        | ~ (v2_lattice3 @ sk_A)
% 0.88/1.07        | ~ (l1_orders_2 @ sk_A)
% 0.88/1.07        | ~ (v5_waybel_6 @ sk_B @ sk_A)
% 0.88/1.07        | (v1_waybel_7 @ (k5_waybel_0 @ sk_A @ sk_B) @ sk_A))),
% 0.88/1.07      inference('sup-', [status(thm)], ['95', '96'])).
% 0.88/1.07  thf('98', plain, ((v3_orders_2 @ sk_A)),
% 0.88/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.88/1.07  thf('99', plain, ((v4_orders_2 @ sk_A)),
% 0.88/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.88/1.07  thf('100', plain, ((v5_orders_2 @ sk_A)),
% 0.88/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.88/1.07  thf('101', plain, ((v1_lattice3 @ sk_A)),
% 0.88/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.88/1.07  thf('102', plain, ((v2_lattice3 @ sk_A)),
% 0.88/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.88/1.07  thf('103', plain, ((l1_orders_2 @ sk_A)),
% 0.88/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.88/1.07  thf('104', plain, ((v5_waybel_6 @ sk_B @ sk_A)),
% 0.88/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.88/1.07  thf('105', plain, ((v1_waybel_7 @ (k5_waybel_0 @ sk_A @ sk_B) @ sk_A)),
% 0.88/1.07      inference('demod', [status(thm)],
% 0.88/1.07                ['97', '98', '99', '100', '101', '102', '103', '104'])).
% 0.88/1.07  thf('106', plain,
% 0.88/1.07      ((v4_waybel_7 @ (k1_yellow_0 @ sk_A @ (k5_waybel_0 @ sk_A @ sk_B)) @ sk_A)),
% 0.88/1.07      inference('demod', [status(thm)], ['94', '105'])).
% 0.88/1.07  thf('107', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.88/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.88/1.07  thf('108', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.88/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.88/1.07  thf('109', plain,
% 0.88/1.07      (![X38 : $i, X39 : $i, X40 : $i]:
% 0.88/1.07         (~ (m1_subset_1 @ X38 @ (u1_struct_0 @ X39))
% 0.88/1.07          | ~ (r1_orders_2 @ X39 @ X40 @ X38)
% 0.88/1.07          | (r2_hidden @ X40 @ (k5_waybel_0 @ X39 @ X38))
% 0.88/1.07          | ~ (m1_subset_1 @ X40 @ (u1_struct_0 @ X39))
% 0.88/1.07          | ~ (l1_orders_2 @ X39)
% 0.88/1.07          | (v2_struct_0 @ X39))),
% 0.88/1.07      inference('cnf', [status(esa)], [t17_waybel_0])).
% 0.88/1.07  thf('110', plain,
% 0.88/1.07      (![X0 : $i]:
% 0.88/1.07         ((v2_struct_0 @ sk_A)
% 0.88/1.07          | ~ (l1_orders_2 @ sk_A)
% 0.88/1.07          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.88/1.07          | (r2_hidden @ X0 @ (k5_waybel_0 @ sk_A @ sk_B))
% 0.88/1.07          | ~ (r1_orders_2 @ sk_A @ X0 @ sk_B))),
% 0.88/1.07      inference('sup-', [status(thm)], ['108', '109'])).
% 0.88/1.07  thf('111', plain, ((l1_orders_2 @ sk_A)),
% 0.88/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.88/1.07  thf('112', plain,
% 0.88/1.07      (![X0 : $i]:
% 0.88/1.07         ((v2_struct_0 @ sk_A)
% 0.88/1.07          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.88/1.07          | (r2_hidden @ X0 @ (k5_waybel_0 @ sk_A @ sk_B))
% 0.88/1.07          | ~ (r1_orders_2 @ sk_A @ X0 @ sk_B))),
% 0.88/1.07      inference('demod', [status(thm)], ['110', '111'])).
% 0.88/1.07  thf('113', plain,
% 0.88/1.07      ((~ (r1_orders_2 @ sk_A @ sk_B @ sk_B)
% 0.88/1.07        | (r2_hidden @ sk_B @ (k5_waybel_0 @ sk_A @ sk_B))
% 0.88/1.07        | (v2_struct_0 @ sk_A))),
% 0.88/1.07      inference('sup-', [status(thm)], ['107', '112'])).
% 0.88/1.07  thf('114', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.88/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.88/1.07  thf('115', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.88/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.88/1.07  thf('116', plain,
% 0.88/1.07      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.88/1.07         ((r3_orders_2 @ X6 @ X7 @ X7)
% 0.88/1.07          | ~ (m1_subset_1 @ X7 @ (u1_struct_0 @ X6))
% 0.88/1.07          | ~ (l1_orders_2 @ X6)
% 0.88/1.07          | ~ (v3_orders_2 @ X6)
% 0.88/1.07          | (v2_struct_0 @ X6)
% 0.88/1.07          | ~ (m1_subset_1 @ X8 @ (u1_struct_0 @ X6)))),
% 0.88/1.07      inference('cnf', [status(esa)], [reflexivity_r3_orders_2])).
% 0.88/1.07  thf('117', plain,
% 0.88/1.07      (![X0 : $i]:
% 0.88/1.07         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.88/1.07          | (v2_struct_0 @ sk_A)
% 0.88/1.07          | ~ (v3_orders_2 @ sk_A)
% 0.88/1.07          | ~ (l1_orders_2 @ sk_A)
% 0.88/1.07          | (r3_orders_2 @ sk_A @ sk_B @ sk_B))),
% 0.88/1.07      inference('sup-', [status(thm)], ['115', '116'])).
% 0.88/1.07  thf('118', plain, ((v3_orders_2 @ sk_A)),
% 0.88/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.88/1.07  thf('119', plain, ((l1_orders_2 @ sk_A)),
% 0.88/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.88/1.07  thf('120', plain,
% 0.88/1.07      (![X0 : $i]:
% 0.88/1.07         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.88/1.07          | (v2_struct_0 @ sk_A)
% 0.88/1.07          | (r3_orders_2 @ sk_A @ sk_B @ sk_B))),
% 0.88/1.07      inference('demod', [status(thm)], ['117', '118', '119'])).
% 0.88/1.07  thf('121', plain, (~ (v2_struct_0 @ sk_A)),
% 0.88/1.07      inference('demod', [status(thm)], ['8', '9'])).
% 0.88/1.07  thf('122', plain,
% 0.88/1.07      (![X0 : $i]:
% 0.88/1.07         ((r3_orders_2 @ sk_A @ sk_B @ sk_B)
% 0.88/1.07          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.88/1.07      inference('clc', [status(thm)], ['120', '121'])).
% 0.88/1.07  thf('123', plain, ((r3_orders_2 @ sk_A @ sk_B @ sk_B)),
% 0.88/1.07      inference('sup-', [status(thm)], ['114', '122'])).
% 0.88/1.07  thf('124', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.88/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.88/1.07  thf('125', plain,
% 0.88/1.07      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.88/1.07         (~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X4))
% 0.88/1.07          | ~ (l1_orders_2 @ X4)
% 0.88/1.07          | ~ (v3_orders_2 @ X4)
% 0.88/1.07          | (v2_struct_0 @ X4)
% 0.88/1.07          | ~ (m1_subset_1 @ X5 @ (u1_struct_0 @ X4))
% 0.88/1.07          | (r1_orders_2 @ X4 @ X3 @ X5)
% 0.88/1.07          | ~ (r3_orders_2 @ X4 @ X3 @ X5))),
% 0.88/1.07      inference('cnf', [status(esa)], [redefinition_r3_orders_2])).
% 0.88/1.07  thf('126', plain,
% 0.88/1.07      (![X0 : $i]:
% 0.88/1.07         (~ (r3_orders_2 @ sk_A @ sk_B @ X0)
% 0.88/1.07          | (r1_orders_2 @ sk_A @ sk_B @ X0)
% 0.88/1.07          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.88/1.07          | (v2_struct_0 @ sk_A)
% 0.88/1.07          | ~ (v3_orders_2 @ sk_A)
% 0.88/1.07          | ~ (l1_orders_2 @ sk_A))),
% 0.88/1.07      inference('sup-', [status(thm)], ['124', '125'])).
% 0.88/1.07  thf('127', plain, ((v3_orders_2 @ sk_A)),
% 0.88/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.88/1.07  thf('128', plain, ((l1_orders_2 @ sk_A)),
% 0.88/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.88/1.07  thf('129', plain,
% 0.88/1.07      (![X0 : $i]:
% 0.88/1.07         (~ (r3_orders_2 @ sk_A @ sk_B @ X0)
% 0.88/1.07          | (r1_orders_2 @ sk_A @ sk_B @ X0)
% 0.88/1.07          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.88/1.07          | (v2_struct_0 @ sk_A))),
% 0.88/1.07      inference('demod', [status(thm)], ['126', '127', '128'])).
% 0.88/1.07  thf('130', plain,
% 0.88/1.07      (((v2_struct_0 @ sk_A)
% 0.88/1.07        | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 0.88/1.07        | (r1_orders_2 @ sk_A @ sk_B @ sk_B))),
% 0.88/1.07      inference('sup-', [status(thm)], ['123', '129'])).
% 0.88/1.07  thf('131', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.88/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.88/1.07  thf('132', plain,
% 0.88/1.07      (((v2_struct_0 @ sk_A) | (r1_orders_2 @ sk_A @ sk_B @ sk_B))),
% 0.88/1.07      inference('demod', [status(thm)], ['130', '131'])).
% 0.88/1.07  thf('133', plain, (~ (v2_struct_0 @ sk_A)),
% 0.88/1.07      inference('demod', [status(thm)], ['8', '9'])).
% 0.88/1.07  thf('134', plain, ((r1_orders_2 @ sk_A @ sk_B @ sk_B)),
% 0.88/1.07      inference('clc', [status(thm)], ['132', '133'])).
% 0.88/1.07  thf('135', plain,
% 0.88/1.07      (((r2_hidden @ sk_B @ (k5_waybel_0 @ sk_A @ sk_B)) | (v2_struct_0 @ sk_A))),
% 0.88/1.07      inference('demod', [status(thm)], ['113', '134'])).
% 0.88/1.07  thf('136', plain, (~ (v2_struct_0 @ sk_A)),
% 0.88/1.07      inference('demod', [status(thm)], ['8', '9'])).
% 0.88/1.07  thf('137', plain, ((r2_hidden @ sk_B @ (k5_waybel_0 @ sk_A @ sk_B))),
% 0.88/1.07      inference('clc', [status(thm)], ['135', '136'])).
% 0.88/1.07  thf(t30_yellow_0, axiom,
% 0.88/1.07    (![A:$i]:
% 0.88/1.07     ( ( ( l1_orders_2 @ A ) & ( v5_orders_2 @ A ) ) =>
% 0.88/1.07       ( ![B:$i]:
% 0.88/1.07         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.88/1.07           ( ![C:$i]:
% 0.88/1.07             ( ( ( ( r1_yellow_0 @ A @ C ) & 
% 0.88/1.07                   ( ( B ) = ( k1_yellow_0 @ A @ C ) ) ) =>
% 0.88/1.07                 ( ( ![D:$i]:
% 0.88/1.07                     ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.88/1.07                       ( ( r2_lattice3 @ A @ C @ D ) =>
% 0.88/1.07                         ( r1_orders_2 @ A @ B @ D ) ) ) ) & 
% 0.88/1.07                   ( r2_lattice3 @ A @ C @ B ) ) ) & 
% 0.88/1.07               ( ( ( ![D:$i]:
% 0.88/1.07                     ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.88/1.07                       ( ( r2_lattice3 @ A @ C @ D ) =>
% 0.88/1.07                         ( r1_orders_2 @ A @ B @ D ) ) ) ) & 
% 0.88/1.07                   ( r2_lattice3 @ A @ C @ B ) ) =>
% 0.88/1.07                 ( ( r1_yellow_0 @ A @ C ) & 
% 0.88/1.07                   ( ( B ) = ( k1_yellow_0 @ A @ C ) ) ) ) ) ) ) ) ))).
% 0.88/1.07  thf(zf_stmt_1, axiom,
% 0.88/1.07    (![D:$i,C:$i,B:$i,A:$i]:
% 0.88/1.07     ( ( ( r2_lattice3 @ A @ C @ D ) => ( r1_orders_2 @ A @ B @ D ) ) =>
% 0.88/1.07       ( zip_tseitin_0 @ D @ C @ B @ A ) ))).
% 0.88/1.07  thf('138', plain,
% 0.88/1.07      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.88/1.07         ((zip_tseitin_0 @ X16 @ X17 @ X18 @ X19)
% 0.88/1.07          | (r2_lattice3 @ X19 @ X17 @ X16))),
% 0.88/1.07      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.88/1.07  thf('139', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.88/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.88/1.07  thf(zf_stmt_2, axiom,
% 0.88/1.07    (![D:$i,C:$i,B:$i,A:$i]:
% 0.88/1.07     ( ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.88/1.07         ( zip_tseitin_0 @ D @ C @ B @ A ) ) =>
% 0.88/1.07       ( zip_tseitin_1 @ D @ C @ B @ A ) ))).
% 0.88/1.07  thf('140', plain,
% 0.88/1.07      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 0.88/1.07         ((zip_tseitin_1 @ X20 @ X21 @ X22 @ X23)
% 0.88/1.07          | (m1_subset_1 @ X20 @ (u1_struct_0 @ X23)))),
% 0.88/1.07      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.88/1.07  thf(d9_lattice3, axiom,
% 0.88/1.07    (![A:$i]:
% 0.88/1.07     ( ( l1_orders_2 @ A ) =>
% 0.88/1.07       ( ![B:$i,C:$i]:
% 0.88/1.07         ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.88/1.07           ( ( r2_lattice3 @ A @ B @ C ) <=>
% 0.88/1.07             ( ![D:$i]:
% 0.88/1.07               ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.88/1.07                 ( ( r2_hidden @ D @ B ) => ( r1_orders_2 @ A @ D @ C ) ) ) ) ) ) ) ))).
% 0.88/1.07  thf('141', plain,
% 0.88/1.07      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.88/1.07         (~ (m1_subset_1 @ X10 @ (u1_struct_0 @ X11))
% 0.88/1.07          | ~ (r2_lattice3 @ X11 @ X12 @ X10)
% 0.88/1.07          | ~ (r2_hidden @ X13 @ X12)
% 0.88/1.07          | (r1_orders_2 @ X11 @ X13 @ X10)
% 0.88/1.07          | ~ (m1_subset_1 @ X13 @ (u1_struct_0 @ X11))
% 0.88/1.07          | ~ (l1_orders_2 @ X11))),
% 0.88/1.07      inference('cnf', [status(esa)], [d9_lattice3])).
% 0.88/1.07  thf('142', plain,
% 0.88/1.07      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.88/1.07         ((zip_tseitin_1 @ X1 @ X5 @ X4 @ X0)
% 0.88/1.07          | ~ (l1_orders_2 @ X0)
% 0.88/1.07          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.88/1.07          | (r1_orders_2 @ X0 @ X2 @ X1)
% 0.88/1.07          | ~ (r2_hidden @ X2 @ X3)
% 0.88/1.07          | ~ (r2_lattice3 @ X0 @ X3 @ X1))),
% 0.88/1.07      inference('sup-', [status(thm)], ['140', '141'])).
% 0.88/1.07  thf('143', plain,
% 0.88/1.07      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.88/1.07         (~ (r2_lattice3 @ sk_A @ X1 @ X0)
% 0.88/1.07          | ~ (r2_hidden @ sk_B @ X1)
% 0.88/1.07          | (r1_orders_2 @ sk_A @ sk_B @ X0)
% 0.88/1.07          | ~ (l1_orders_2 @ sk_A)
% 0.88/1.07          | (zip_tseitin_1 @ X0 @ X3 @ X2 @ sk_A))),
% 0.88/1.07      inference('sup-', [status(thm)], ['139', '142'])).
% 0.88/1.07  thf('144', plain, ((l1_orders_2 @ sk_A)),
% 0.88/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.88/1.07  thf('145', plain,
% 0.88/1.07      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.88/1.07         (~ (r2_lattice3 @ sk_A @ X1 @ X0)
% 0.88/1.07          | ~ (r2_hidden @ sk_B @ X1)
% 0.88/1.07          | (r1_orders_2 @ sk_A @ sk_B @ X0)
% 0.88/1.07          | (zip_tseitin_1 @ X0 @ X3 @ X2 @ sk_A))),
% 0.88/1.07      inference('demod', [status(thm)], ['143', '144'])).
% 0.88/1.07  thf('146', plain,
% 0.88/1.07      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.88/1.07         ((zip_tseitin_0 @ X0 @ X1 @ X4 @ sk_A)
% 0.88/1.07          | (zip_tseitin_1 @ X0 @ X3 @ X2 @ sk_A)
% 0.88/1.07          | (r1_orders_2 @ sk_A @ sk_B @ X0)
% 0.88/1.07          | ~ (r2_hidden @ sk_B @ X1))),
% 0.88/1.07      inference('sup-', [status(thm)], ['138', '145'])).
% 0.88/1.07  thf('147', plain,
% 0.88/1.07      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.88/1.07         ((r1_orders_2 @ sk_A @ sk_B @ X0)
% 0.88/1.07          | (zip_tseitin_1 @ X0 @ X2 @ X1 @ sk_A)
% 0.88/1.07          | (zip_tseitin_0 @ X0 @ (k5_waybel_0 @ sk_A @ sk_B) @ X3 @ sk_A))),
% 0.88/1.07      inference('sup-', [status(thm)], ['137', '146'])).
% 0.88/1.07  thf('148', plain,
% 0.88/1.07      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 0.88/1.07         ((zip_tseitin_1 @ X20 @ X21 @ X22 @ X23)
% 0.88/1.07          | ~ (zip_tseitin_0 @ X20 @ X21 @ X22 @ X23))),
% 0.88/1.07      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.88/1.07  thf('149', plain,
% 0.88/1.07      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.88/1.07         ((zip_tseitin_1 @ X1 @ X3 @ X2 @ sk_A)
% 0.88/1.07          | (r1_orders_2 @ sk_A @ sk_B @ X1)
% 0.88/1.07          | (zip_tseitin_1 @ X1 @ (k5_waybel_0 @ sk_A @ sk_B) @ X0 @ sk_A))),
% 0.88/1.07      inference('sup-', [status(thm)], ['147', '148'])).
% 0.88/1.07  thf('150', plain,
% 0.88/1.07      (![X0 : $i, X1 : $i]:
% 0.88/1.07         ((zip_tseitin_1 @ X1 @ (k5_waybel_0 @ sk_A @ sk_B) @ X0 @ sk_A)
% 0.88/1.07          | (r1_orders_2 @ sk_A @ sk_B @ X1))),
% 0.88/1.07      inference('condensation', [status(thm)], ['149'])).
% 0.88/1.07  thf('151', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.88/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.88/1.07  thf(zf_stmt_3, type, zip_tseitin_2 : $i > $i > $i > $o).
% 0.88/1.07  thf(zf_stmt_4, axiom,
% 0.88/1.07    (![C:$i,B:$i,A:$i]:
% 0.88/1.07     ( ( zip_tseitin_2 @ C @ B @ A ) =>
% 0.88/1.07       ( ( ( B ) = ( k1_yellow_0 @ A @ C ) ) & ( r1_yellow_0 @ A @ C ) ) ))).
% 0.88/1.07  thf(zf_stmt_5, type, zip_tseitin_1 : $i > $i > $i > $i > $o).
% 0.88/1.07  thf(zf_stmt_6, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.88/1.07  thf(zf_stmt_7, axiom,
% 0.88/1.07    (![A:$i]:
% 0.88/1.07     ( ( ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.88/1.07       ( ![B:$i]:
% 0.88/1.07         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.88/1.07           ( ![C:$i]:
% 0.88/1.07             ( ( ( ( r2_lattice3 @ A @ C @ B ) & 
% 0.88/1.07                   ( ![D:$i]: ( zip_tseitin_1 @ D @ C @ B @ A ) ) ) =>
% 0.88/1.07                 ( zip_tseitin_2 @ C @ B @ A ) ) & 
% 0.88/1.07               ( ( ( ( B ) = ( k1_yellow_0 @ A @ C ) ) & 
% 0.88/1.07                   ( r1_yellow_0 @ A @ C ) ) =>
% 0.88/1.07                 ( ( r2_lattice3 @ A @ C @ B ) & 
% 0.88/1.07                   ( ![D:$i]:
% 0.88/1.07                     ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.88/1.07                       ( ( r2_lattice3 @ A @ C @ D ) =>
% 0.88/1.07                         ( r1_orders_2 @ A @ B @ D ) ) ) ) ) ) ) ) ) ) ))).
% 0.88/1.07  thf('152', plain,
% 0.88/1.07      (![X27 : $i, X28 : $i, X31 : $i]:
% 0.88/1.07         (~ (m1_subset_1 @ X27 @ (u1_struct_0 @ X28))
% 0.88/1.07          | ~ (r2_lattice3 @ X28 @ X31 @ X27)
% 0.88/1.07          | ~ (zip_tseitin_1 @ (sk_D_1 @ X31 @ X27 @ X28) @ X31 @ X27 @ X28)
% 0.88/1.07          | (zip_tseitin_2 @ X31 @ X27 @ X28)
% 0.88/1.07          | ~ (l1_orders_2 @ X28)
% 0.88/1.07          | ~ (v5_orders_2 @ X28))),
% 0.88/1.07      inference('cnf', [status(esa)], [zf_stmt_7])).
% 0.88/1.07  thf('153', plain,
% 0.88/1.07      (![X0 : $i]:
% 0.88/1.07         (~ (v5_orders_2 @ sk_A)
% 0.88/1.07          | ~ (l1_orders_2 @ sk_A)
% 0.88/1.07          | (zip_tseitin_2 @ X0 @ sk_B @ sk_A)
% 0.88/1.07          | ~ (zip_tseitin_1 @ (sk_D_1 @ X0 @ sk_B @ sk_A) @ X0 @ sk_B @ sk_A)
% 0.88/1.07          | ~ (r2_lattice3 @ sk_A @ X0 @ sk_B))),
% 0.88/1.07      inference('sup-', [status(thm)], ['151', '152'])).
% 0.88/1.07  thf('154', plain, ((v5_orders_2 @ sk_A)),
% 0.88/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.88/1.07  thf('155', plain, ((l1_orders_2 @ sk_A)),
% 0.88/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.88/1.07  thf('156', plain,
% 0.88/1.07      (![X0 : $i]:
% 0.88/1.07         ((zip_tseitin_2 @ X0 @ sk_B @ sk_A)
% 0.88/1.07          | ~ (zip_tseitin_1 @ (sk_D_1 @ X0 @ sk_B @ sk_A) @ X0 @ sk_B @ sk_A)
% 0.88/1.07          | ~ (r2_lattice3 @ sk_A @ X0 @ sk_B))),
% 0.88/1.07      inference('demod', [status(thm)], ['153', '154', '155'])).
% 0.88/1.07  thf('157', plain,
% 0.88/1.07      (((r1_orders_2 @ sk_A @ sk_B @ 
% 0.88/1.07         (sk_D_1 @ (k5_waybel_0 @ sk_A @ sk_B) @ sk_B @ sk_A))
% 0.88/1.07        | ~ (r2_lattice3 @ sk_A @ (k5_waybel_0 @ sk_A @ sk_B) @ sk_B)
% 0.88/1.07        | (zip_tseitin_2 @ (k5_waybel_0 @ sk_A @ sk_B) @ sk_B @ sk_A))),
% 0.88/1.07      inference('sup-', [status(thm)], ['150', '156'])).
% 0.88/1.07  thf('158', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.88/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.88/1.07  thf('159', plain,
% 0.88/1.07      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.88/1.07         (~ (m1_subset_1 @ X10 @ (u1_struct_0 @ X11))
% 0.88/1.07          | (m1_subset_1 @ (sk_D @ X10 @ X12 @ X11) @ (u1_struct_0 @ X11))
% 0.88/1.07          | (r2_lattice3 @ X11 @ X12 @ X10)
% 0.88/1.07          | ~ (l1_orders_2 @ X11))),
% 0.88/1.07      inference('cnf', [status(esa)], [d9_lattice3])).
% 0.88/1.07  thf('160', plain,
% 0.88/1.07      (![X0 : $i]:
% 0.88/1.07         (~ (l1_orders_2 @ sk_A)
% 0.88/1.07          | (r2_lattice3 @ sk_A @ X0 @ sk_B)
% 0.88/1.07          | (m1_subset_1 @ (sk_D @ sk_B @ X0 @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 0.88/1.07      inference('sup-', [status(thm)], ['158', '159'])).
% 0.88/1.07  thf('161', plain, ((l1_orders_2 @ sk_A)),
% 0.88/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.88/1.07  thf('162', plain,
% 0.88/1.07      (![X0 : $i]:
% 0.88/1.07         ((r2_lattice3 @ sk_A @ X0 @ sk_B)
% 0.88/1.07          | (m1_subset_1 @ (sk_D @ sk_B @ X0 @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 0.88/1.07      inference('demod', [status(thm)], ['160', '161'])).
% 0.88/1.07  thf('163', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.88/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.88/1.07  thf('164', plain,
% 0.88/1.07      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.88/1.07         (~ (m1_subset_1 @ X10 @ (u1_struct_0 @ X11))
% 0.88/1.07          | (r2_hidden @ (sk_D @ X10 @ X12 @ X11) @ X12)
% 0.88/1.07          | (r2_lattice3 @ X11 @ X12 @ X10)
% 0.88/1.07          | ~ (l1_orders_2 @ X11))),
% 0.88/1.07      inference('cnf', [status(esa)], [d9_lattice3])).
% 0.88/1.07  thf('165', plain,
% 0.88/1.07      (![X0 : $i]:
% 0.88/1.07         (~ (l1_orders_2 @ sk_A)
% 0.88/1.07          | (r2_lattice3 @ sk_A @ X0 @ sk_B)
% 0.88/1.07          | (r2_hidden @ (sk_D @ sk_B @ X0 @ sk_A) @ X0))),
% 0.88/1.07      inference('sup-', [status(thm)], ['163', '164'])).
% 0.88/1.07  thf('166', plain, ((l1_orders_2 @ sk_A)),
% 0.88/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.88/1.07  thf('167', plain,
% 0.88/1.07      (![X0 : $i]:
% 0.88/1.07         ((r2_lattice3 @ sk_A @ X0 @ sk_B)
% 0.88/1.07          | (r2_hidden @ (sk_D @ sk_B @ X0 @ sk_A) @ X0))),
% 0.88/1.07      inference('demod', [status(thm)], ['165', '166'])).
% 0.88/1.07  thf('168', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.88/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.88/1.07  thf('169', plain,
% 0.88/1.07      (![X38 : $i, X39 : $i, X40 : $i]:
% 0.88/1.07         (~ (m1_subset_1 @ X38 @ (u1_struct_0 @ X39))
% 0.88/1.07          | ~ (r2_hidden @ X40 @ (k5_waybel_0 @ X39 @ X38))
% 0.88/1.07          | (r1_orders_2 @ X39 @ X40 @ X38)
% 0.88/1.07          | ~ (m1_subset_1 @ X40 @ (u1_struct_0 @ X39))
% 0.88/1.07          | ~ (l1_orders_2 @ X39)
% 0.88/1.07          | (v2_struct_0 @ X39))),
% 0.88/1.07      inference('cnf', [status(esa)], [t17_waybel_0])).
% 0.88/1.07  thf('170', plain,
% 0.88/1.07      (![X0 : $i]:
% 0.88/1.07         ((v2_struct_0 @ sk_A)
% 0.88/1.07          | ~ (l1_orders_2 @ sk_A)
% 0.88/1.07          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.88/1.07          | (r1_orders_2 @ sk_A @ X0 @ sk_B)
% 0.88/1.07          | ~ (r2_hidden @ X0 @ (k5_waybel_0 @ sk_A @ sk_B)))),
% 0.88/1.07      inference('sup-', [status(thm)], ['168', '169'])).
% 0.88/1.07  thf('171', plain, ((l1_orders_2 @ sk_A)),
% 0.88/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.88/1.07  thf('172', plain,
% 0.88/1.07      (![X0 : $i]:
% 0.88/1.07         ((v2_struct_0 @ sk_A)
% 0.88/1.07          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.88/1.07          | (r1_orders_2 @ sk_A @ X0 @ sk_B)
% 0.88/1.07          | ~ (r2_hidden @ X0 @ (k5_waybel_0 @ sk_A @ sk_B)))),
% 0.88/1.07      inference('demod', [status(thm)], ['170', '171'])).
% 0.88/1.07  thf('173', plain,
% 0.88/1.07      (((r2_lattice3 @ sk_A @ (k5_waybel_0 @ sk_A @ sk_B) @ sk_B)
% 0.88/1.07        | (r1_orders_2 @ sk_A @ 
% 0.88/1.07           (sk_D @ sk_B @ (k5_waybel_0 @ sk_A @ sk_B) @ sk_A) @ sk_B)
% 0.88/1.07        | ~ (m1_subset_1 @ 
% 0.88/1.07             (sk_D @ sk_B @ (k5_waybel_0 @ sk_A @ sk_B) @ sk_A) @ 
% 0.88/1.07             (u1_struct_0 @ sk_A))
% 0.88/1.07        | (v2_struct_0 @ sk_A))),
% 0.88/1.07      inference('sup-', [status(thm)], ['167', '172'])).
% 0.88/1.07  thf('174', plain,
% 0.88/1.07      (((r2_lattice3 @ sk_A @ (k5_waybel_0 @ sk_A @ sk_B) @ sk_B)
% 0.88/1.07        | (v2_struct_0 @ sk_A)
% 0.88/1.07        | (r1_orders_2 @ sk_A @ 
% 0.88/1.07           (sk_D @ sk_B @ (k5_waybel_0 @ sk_A @ sk_B) @ sk_A) @ sk_B)
% 0.88/1.07        | (r2_lattice3 @ sk_A @ (k5_waybel_0 @ sk_A @ sk_B) @ sk_B))),
% 0.88/1.07      inference('sup-', [status(thm)], ['162', '173'])).
% 0.88/1.07  thf('175', plain,
% 0.88/1.07      (((r1_orders_2 @ sk_A @ 
% 0.88/1.07         (sk_D @ sk_B @ (k5_waybel_0 @ sk_A @ sk_B) @ sk_A) @ sk_B)
% 0.88/1.07        | (v2_struct_0 @ sk_A)
% 0.88/1.07        | (r2_lattice3 @ sk_A @ (k5_waybel_0 @ sk_A @ sk_B) @ sk_B))),
% 0.88/1.07      inference('simplify', [status(thm)], ['174'])).
% 0.88/1.07  thf('176', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.88/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.88/1.07  thf('177', plain,
% 0.88/1.07      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.88/1.07         (~ (m1_subset_1 @ X10 @ (u1_struct_0 @ X11))
% 0.88/1.07          | ~ (r1_orders_2 @ X11 @ (sk_D @ X10 @ X12 @ X11) @ X10)
% 0.88/1.07          | (r2_lattice3 @ X11 @ X12 @ X10)
% 0.88/1.07          | ~ (l1_orders_2 @ X11))),
% 0.88/1.07      inference('cnf', [status(esa)], [d9_lattice3])).
% 0.88/1.07  thf('178', plain,
% 0.88/1.07      (![X0 : $i]:
% 0.88/1.07         (~ (l1_orders_2 @ sk_A)
% 0.88/1.07          | (r2_lattice3 @ sk_A @ X0 @ sk_B)
% 0.88/1.07          | ~ (r1_orders_2 @ sk_A @ (sk_D @ sk_B @ X0 @ sk_A) @ sk_B))),
% 0.88/1.07      inference('sup-', [status(thm)], ['176', '177'])).
% 0.88/1.07  thf('179', plain, ((l1_orders_2 @ sk_A)),
% 0.88/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.88/1.07  thf('180', plain,
% 0.88/1.07      (![X0 : $i]:
% 0.88/1.07         ((r2_lattice3 @ sk_A @ X0 @ sk_B)
% 0.88/1.07          | ~ (r1_orders_2 @ sk_A @ (sk_D @ sk_B @ X0 @ sk_A) @ sk_B))),
% 0.88/1.07      inference('demod', [status(thm)], ['178', '179'])).
% 0.88/1.07  thf('181', plain,
% 0.88/1.07      (((r2_lattice3 @ sk_A @ (k5_waybel_0 @ sk_A @ sk_B) @ sk_B)
% 0.88/1.07        | (v2_struct_0 @ sk_A))),
% 0.88/1.07      inference('clc', [status(thm)], ['175', '180'])).
% 0.88/1.07  thf('182', plain, (~ (v2_struct_0 @ sk_A)),
% 0.88/1.07      inference('demod', [status(thm)], ['8', '9'])).
% 0.88/1.07  thf('183', plain,
% 0.88/1.07      ((r2_lattice3 @ sk_A @ (k5_waybel_0 @ sk_A @ sk_B) @ sk_B)),
% 0.88/1.07      inference('clc', [status(thm)], ['181', '182'])).
% 0.88/1.07  thf('184', plain,
% 0.88/1.07      (((r1_orders_2 @ sk_A @ sk_B @ 
% 0.88/1.07         (sk_D_1 @ (k5_waybel_0 @ sk_A @ sk_B) @ sk_B @ sk_A))
% 0.88/1.07        | (zip_tseitin_2 @ (k5_waybel_0 @ sk_A @ sk_B) @ sk_B @ sk_A))),
% 0.88/1.07      inference('demod', [status(thm)], ['157', '183'])).
% 0.88/1.07  thf('185', plain,
% 0.88/1.07      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.88/1.07         ((zip_tseitin_0 @ X16 @ X17 @ X18 @ X19)
% 0.88/1.07          | ~ (r1_orders_2 @ X19 @ X18 @ X16))),
% 0.88/1.07      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.88/1.07  thf('186', plain,
% 0.88/1.07      (![X0 : $i]:
% 0.88/1.07         ((zip_tseitin_2 @ (k5_waybel_0 @ sk_A @ sk_B) @ sk_B @ sk_A)
% 0.88/1.07          | (zip_tseitin_0 @ 
% 0.88/1.07             (sk_D_1 @ (k5_waybel_0 @ sk_A @ sk_B) @ sk_B @ sk_A) @ X0 @ 
% 0.88/1.07             sk_B @ sk_A))),
% 0.88/1.07      inference('sup-', [status(thm)], ['184', '185'])).
% 0.88/1.07  thf('187', plain,
% 0.88/1.07      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 0.88/1.07         ((zip_tseitin_1 @ X20 @ X21 @ X22 @ X23)
% 0.88/1.07          | ~ (zip_tseitin_0 @ X20 @ X21 @ X22 @ X23))),
% 0.88/1.07      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.88/1.07  thf('188', plain,
% 0.88/1.07      (![X0 : $i]:
% 0.88/1.07         ((zip_tseitin_2 @ (k5_waybel_0 @ sk_A @ sk_B) @ sk_B @ sk_A)
% 0.88/1.07          | (zip_tseitin_1 @ 
% 0.88/1.07             (sk_D_1 @ (k5_waybel_0 @ sk_A @ sk_B) @ sk_B @ sk_A) @ X0 @ 
% 0.88/1.07             sk_B @ sk_A))),
% 0.88/1.07      inference('sup-', [status(thm)], ['186', '187'])).
% 0.88/1.07  thf('189', plain,
% 0.88/1.07      (![X0 : $i]:
% 0.88/1.07         ((zip_tseitin_2 @ X0 @ sk_B @ sk_A)
% 0.88/1.07          | ~ (zip_tseitin_1 @ (sk_D_1 @ X0 @ sk_B @ sk_A) @ X0 @ sk_B @ sk_A)
% 0.88/1.07          | ~ (r2_lattice3 @ sk_A @ X0 @ sk_B))),
% 0.88/1.07      inference('demod', [status(thm)], ['153', '154', '155'])).
% 0.88/1.07  thf('190', plain,
% 0.88/1.07      (((zip_tseitin_2 @ (k5_waybel_0 @ sk_A @ sk_B) @ sk_B @ sk_A)
% 0.88/1.07        | ~ (r2_lattice3 @ sk_A @ (k5_waybel_0 @ sk_A @ sk_B) @ sk_B)
% 0.88/1.07        | (zip_tseitin_2 @ (k5_waybel_0 @ sk_A @ sk_B) @ sk_B @ sk_A))),
% 0.88/1.07      inference('sup-', [status(thm)], ['188', '189'])).
% 0.88/1.07  thf('191', plain,
% 0.88/1.07      ((r2_lattice3 @ sk_A @ (k5_waybel_0 @ sk_A @ sk_B) @ sk_B)),
% 0.88/1.07      inference('clc', [status(thm)], ['181', '182'])).
% 0.88/1.07  thf('192', plain,
% 0.88/1.07      (((zip_tseitin_2 @ (k5_waybel_0 @ sk_A @ sk_B) @ sk_B @ sk_A)
% 0.88/1.07        | (zip_tseitin_2 @ (k5_waybel_0 @ sk_A @ sk_B) @ sk_B @ sk_A))),
% 0.88/1.07      inference('demod', [status(thm)], ['190', '191'])).
% 0.88/1.07  thf('193', plain,
% 0.88/1.07      ((zip_tseitin_2 @ (k5_waybel_0 @ sk_A @ sk_B) @ sk_B @ sk_A)),
% 0.88/1.07      inference('simplify', [status(thm)], ['192'])).
% 0.88/1.07  thf('194', plain,
% 0.88/1.07      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.88/1.07         (((X26) = (k1_yellow_0 @ X24 @ X25))
% 0.88/1.07          | ~ (zip_tseitin_2 @ X25 @ X26 @ X24))),
% 0.88/1.07      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.88/1.07  thf('195', plain,
% 0.88/1.07      (((sk_B) = (k1_yellow_0 @ sk_A @ (k5_waybel_0 @ sk_A @ sk_B)))),
% 0.88/1.07      inference('sup-', [status(thm)], ['193', '194'])).
% 0.88/1.07  thf('196', plain, ((v4_waybel_7 @ sk_B @ sk_A)),
% 0.88/1.07      inference('demod', [status(thm)], ['106', '195'])).
% 0.88/1.07  thf('197', plain, ($false), inference('demod', [status(thm)], ['0', '196'])).
% 0.88/1.07  
% 0.88/1.07  % SZS output end Refutation
% 0.88/1.07  
% 0.88/1.07  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
