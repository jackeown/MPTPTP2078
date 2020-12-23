%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT1980+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.vozcfDRgt8

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:54:38 EST 2020

% Result     : Theorem 0.99s
% Output     : Refutation 0.99s
% Verified   : 
% Statistics : Number of formulae       :  502 (2904 expanded)
%              Number of leaves         :   40 ( 881 expanded)
%              Depth                    :   31
%              Number of atoms          : 7390 (103088 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   22 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v13_waybel_0_type,type,(
    v13_waybel_0: $i > $i > $o )).

thf(k7_lattice3_type,type,(
    k7_lattice3: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(v1_waybel_0_type,type,(
    v1_waybel_0: $i > $i > $o )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(v2_waybel_0_type,type,(
    v2_waybel_0: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v12_waybel_0_type,type,(
    v12_waybel_0: $i > $i > $o )).

thf(v2_waybel_7_type,type,(
    v2_waybel_7: $i > $i > $o )).

thf(v2_lattice3_type,type,(
    v2_lattice3: $i > $o )).

thf(v1_waybel_7_type,type,(
    v1_waybel_7: $i > $i > $o )).

thf(v1_orders_2_type,type,(
    v1_orders_2: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(r1_subset_1_type,type,(
    r1_subset_1: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v2_waybel_1_type,type,(
    v2_waybel_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v1_lattice3_type,type,(
    v1_lattice3: $i > $o )).

thf(t29_waybel_7,conjecture,(
    ! [A: $i] :
      ( ( ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( v2_waybel_1 @ A )
        & ( v1_lattice3 @ A )
        & ( v2_lattice3 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v1_xboole_0 @ B )
            & ( v1_waybel_0 @ B @ A )
            & ( v12_waybel_0 @ B @ A )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
         => ! [C: $i] :
              ( ( ~ ( v1_xboole_0 @ C )
                & ( v2_waybel_0 @ C @ A )
                & ( v13_waybel_0 @ C @ A )
                & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
             => ~ ( ( r1_subset_1 @ B @ C )
                  & ! [D: $i] :
                      ( ( ~ ( v1_xboole_0 @ D )
                        & ( v2_waybel_0 @ D @ A )
                        & ( v13_waybel_0 @ D @ A )
                        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
                     => ~ ( ( v2_waybel_7 @ D @ A )
                          & ( r1_tarski @ C @ D )
                          & ( r1_subset_1 @ B @ D ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v3_orders_2 @ A )
          & ( v4_orders_2 @ A )
          & ( v5_orders_2 @ A )
          & ( v2_waybel_1 @ A )
          & ( v1_lattice3 @ A )
          & ( v2_lattice3 @ A )
          & ( l1_orders_2 @ A ) )
       => ! [B: $i] :
            ( ( ~ ( v1_xboole_0 @ B )
              & ( v1_waybel_0 @ B @ A )
              & ( v12_waybel_0 @ B @ A )
              & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
           => ! [C: $i] :
                ( ( ~ ( v1_xboole_0 @ C )
                  & ( v2_waybel_0 @ C @ A )
                  & ( v13_waybel_0 @ C @ A )
                  & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
               => ~ ( ( r1_subset_1 @ B @ C )
                    & ! [D: $i] :
                        ( ( ~ ( v1_xboole_0 @ D )
                          & ( v2_waybel_0 @ D @ A )
                          & ( v13_waybel_0 @ D @ A )
                          & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
                       => ~ ( ( v2_waybel_7 @ D @ A )
                            & ( r1_tarski @ C @ D )
                            & ( r1_subset_1 @ B @ D ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t29_waybel_7])).

thf('0',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t26_yellow_7,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ! [B: $i] :
          ( ( ( v1_waybel_0 @ B @ A )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
        <=> ( ( v2_waybel_0 @ B @ ( k7_lattice3 @ A ) )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k7_lattice3 @ A ) ) ) ) ) ) ) )).

thf('1',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( v1_waybel_0 @ X14 @ X13 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k7_lattice3 @ X13 ) ) ) )
      | ~ ( l1_orders_2 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t26_yellow_7])).

thf('2',plain,
    ( ~ ( l1_orders_2 @ sk_A )
    | ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k7_lattice3 @ sk_A ) ) ) )
    | ~ ( v1_waybel_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    v1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k7_lattice3 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['2','3','4'])).

thf(fc8_yellow_7,axiom,(
    ! [A: $i] :
      ( ( ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( v1_lattice3 @ A )
        & ( v2_lattice3 @ A )
        & ( v2_waybel_1 @ A )
        & ( l1_orders_2 @ A ) )
     => ( ( v1_orders_2 @ ( k7_lattice3 @ A ) )
        & ( v2_waybel_1 @ ( k7_lattice3 @ A ) ) ) ) )).

thf('6',plain,(
    ! [X6: $i] :
      ( ( v2_waybel_1 @ ( k7_lattice3 @ X6 ) )
      | ~ ( l1_orders_2 @ X6 )
      | ~ ( v2_waybel_1 @ X6 )
      | ~ ( v2_lattice3 @ X6 )
      | ~ ( v1_lattice3 @ X6 )
      | ~ ( v5_orders_2 @ X6 )
      | ~ ( v4_orders_2 @ X6 )
      | ~ ( v3_orders_2 @ X6 ) ) ),
    inference(cnf,[status(esa)],[fc8_yellow_7])).

thf(fc5_yellow_7,axiom,(
    ! [A: $i] :
      ( ( ( v2_lattice3 @ A )
        & ( l1_orders_2 @ A ) )
     => ( ( v1_orders_2 @ ( k7_lattice3 @ A ) )
        & ( v1_lattice3 @ ( k7_lattice3 @ A ) ) ) ) )).

thf('7',plain,(
    ! [X4: $i] :
      ( ( v1_lattice3 @ ( k7_lattice3 @ X4 ) )
      | ~ ( l1_orders_2 @ X4 )
      | ~ ( v2_lattice3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc5_yellow_7])).

thf(fc3_yellow_7,axiom,(
    ! [A: $i] :
      ( ( ( v5_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ( ( v1_orders_2 @ ( k7_lattice3 @ A ) )
        & ( v5_orders_2 @ ( k7_lattice3 @ A ) ) ) ) )).

thf('8',plain,(
    ! [X3: $i] :
      ( ( v5_orders_2 @ ( k7_lattice3 @ X3 ) )
      | ~ ( l1_orders_2 @ X3 )
      | ~ ( v5_orders_2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc3_yellow_7])).

thf(fc6_yellow_7,axiom,(
    ! [A: $i] :
      ( ( ( v1_lattice3 @ A )
        & ( l1_orders_2 @ A ) )
     => ( ( v1_orders_2 @ ( k7_lattice3 @ A ) )
        & ( v2_lattice3 @ ( k7_lattice3 @ A ) ) ) ) )).

thf('9',plain,(
    ! [X5: $i] :
      ( ( v2_lattice3 @ ( k7_lattice3 @ X5 ) )
      | ~ ( l1_orders_2 @ X5 )
      | ~ ( v1_lattice3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[fc6_yellow_7])).

thf(fc2_yellow_7,axiom,(
    ! [A: $i] :
      ( ( ( v4_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ( ( v1_orders_2 @ ( k7_lattice3 @ A ) )
        & ( v4_orders_2 @ ( k7_lattice3 @ A ) ) ) ) )).

thf('10',plain,(
    ! [X2: $i] :
      ( ( v4_orders_2 @ ( k7_lattice3 @ X2 ) )
      | ~ ( l1_orders_2 @ X2 )
      | ~ ( v4_orders_2 @ X2 ) ) ),
    inference(cnf,[status(esa)],[fc2_yellow_7])).

thf(dt_k7_lattice3,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( ( v1_orders_2 @ ( k7_lattice3 @ A ) )
        & ( l1_orders_2 @ ( k7_lattice3 @ A ) ) ) ) )).

thf('11',plain,(
    ! [X0: $i] :
      ( ( l1_orders_2 @ ( k7_lattice3 @ X0 ) )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_k7_lattice3])).

thf(fc1_yellow_7,axiom,(
    ! [A: $i] :
      ( ( ( v3_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ( ( v1_orders_2 @ ( k7_lattice3 @ A ) )
        & ( v3_orders_2 @ ( k7_lattice3 @ A ) ) ) ) )).

thf('12',plain,(
    ! [X1: $i] :
      ( ( v3_orders_2 @ ( k7_lattice3 @ X1 ) )
      | ~ ( l1_orders_2 @ X1 )
      | ~ ( v3_orders_2 @ X1 ) ) ),
    inference(cnf,[status(esa)],[fc1_yellow_7])).

thf('13',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t27_yellow_7,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ! [B: $i] :
          ( ( ( v1_waybel_0 @ B @ ( k7_lattice3 @ A ) )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k7_lattice3 @ A ) ) ) ) )
        <=> ( ( v2_waybel_0 @ B @ A )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) )).

thf('14',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( v2_waybel_0 @ X18 @ X19 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k7_lattice3 @ X19 ) ) ) )
      | ~ ( l1_orders_2 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t27_yellow_7])).

thf('15',plain,
    ( ~ ( l1_orders_2 @ sk_A )
    | ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k7_lattice3 @ sk_A ) ) ) )
    | ~ ( v2_waybel_0 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    v2_waybel_0 @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k7_lattice3 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['15','16','17'])).

thf(t27_waybel_7,axiom,(
    ! [A: $i] :
      ( ( ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( v2_waybel_1 @ A )
        & ( v1_lattice3 @ A )
        & ( v2_lattice3 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v1_xboole_0 @ B )
            & ( v1_waybel_0 @ B @ A )
            & ( v12_waybel_0 @ B @ A )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
         => ! [C: $i] :
              ( ( ~ ( v1_xboole_0 @ C )
                & ( v2_waybel_0 @ C @ A )
                & ( v13_waybel_0 @ C @ A )
                & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
             => ~ ( ( r1_subset_1 @ B @ C )
                  & ! [D: $i] :
                      ( ( ~ ( v1_xboole_0 @ D )
                        & ( v1_waybel_0 @ D @ A )
                        & ( v12_waybel_0 @ D @ A )
                        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
                     => ~ ( ( v1_waybel_7 @ D @ A )
                          & ( r1_tarski @ B @ D )
                          & ( r1_subset_1 @ D @ C ) ) ) ) ) ) ) )).

thf('19',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( v1_xboole_0 @ X15 )
      | ~ ( v1_waybel_0 @ X15 @ X16 )
      | ~ ( v12_waybel_0 @ X15 @ X16 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( v1_xboole_0 @ ( sk_D @ X17 @ X15 @ X16 ) )
      | ~ ( r1_subset_1 @ X15 @ X17 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( v13_waybel_0 @ X17 @ X16 )
      | ~ ( v2_waybel_0 @ X17 @ X16 )
      | ( v1_xboole_0 @ X17 )
      | ~ ( l1_orders_2 @ X16 )
      | ~ ( v2_lattice3 @ X16 )
      | ~ ( v1_lattice3 @ X16 )
      | ~ ( v2_waybel_1 @ X16 )
      | ~ ( v5_orders_2 @ X16 )
      | ~ ( v4_orders_2 @ X16 )
      | ~ ( v3_orders_2 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t27_waybel_7])).

thf('20',plain,(
    ! [X0: $i] :
      ( ~ ( v3_orders_2 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v4_orders_2 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v5_orders_2 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v2_waybel_1 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v1_lattice3 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v2_lattice3 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( l1_orders_2 @ ( k7_lattice3 @ sk_A ) )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v2_waybel_0 @ X0 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v13_waybel_0 @ X0 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k7_lattice3 @ sk_A ) ) ) )
      | ~ ( r1_subset_1 @ sk_C @ X0 )
      | ~ ( v1_xboole_0 @ ( sk_D @ X0 @ sk_C @ ( k7_lattice3 @ sk_A ) ) )
      | ~ ( v12_waybel_0 @ sk_C @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v1_waybel_0 @ sk_C @ ( k7_lattice3 @ sk_A ) )
      | ( v1_xboole_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t29_yellow_7,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ! [B: $i] :
          ( ( ( v12_waybel_0 @ B @ ( k7_lattice3 @ A ) )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k7_lattice3 @ A ) ) ) ) )
        <=> ( ( v13_waybel_0 @ B @ A )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) )).

thf('22',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( v13_waybel_0 @ X24 @ X25 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) )
      | ( v12_waybel_0 @ X24 @ ( k7_lattice3 @ X25 ) )
      | ~ ( l1_orders_2 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t29_yellow_7])).

thf('23',plain,
    ( ~ ( l1_orders_2 @ sk_A )
    | ( v12_waybel_0 @ sk_C @ ( k7_lattice3 @ sk_A ) )
    | ~ ( v13_waybel_0 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    v13_waybel_0 @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    v12_waybel_0 @ sk_C @ ( k7_lattice3 @ sk_A ) ),
    inference(demod,[status(thm)],['23','24','25'])).

thf('27',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( v2_waybel_0 @ X18 @ X19 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ( v1_waybel_0 @ X18 @ ( k7_lattice3 @ X19 ) )
      | ~ ( l1_orders_2 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t27_yellow_7])).

thf('29',plain,
    ( ~ ( l1_orders_2 @ sk_A )
    | ( v1_waybel_0 @ sk_C @ ( k7_lattice3 @ sk_A ) )
    | ~ ( v2_waybel_0 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    v2_waybel_0 @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    v1_waybel_0 @ sk_C @ ( k7_lattice3 @ sk_A ) ),
    inference(demod,[status(thm)],['29','30','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( v3_orders_2 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v4_orders_2 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v5_orders_2 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v2_waybel_1 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v1_lattice3 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v2_lattice3 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( l1_orders_2 @ ( k7_lattice3 @ sk_A ) )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v2_waybel_0 @ X0 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v13_waybel_0 @ X0 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k7_lattice3 @ sk_A ) ) ) )
      | ~ ( r1_subset_1 @ sk_C @ X0 )
      | ~ ( v1_xboole_0 @ ( sk_D @ X0 @ sk_C @ ( k7_lattice3 @ sk_A ) ) )
      | ( v1_xboole_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['20','26','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ~ ( v3_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ( v1_xboole_0 @ sk_C )
      | ~ ( v1_xboole_0 @ ( sk_D @ X0 @ sk_C @ ( k7_lattice3 @ sk_A ) ) )
      | ~ ( r1_subset_1 @ sk_C @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k7_lattice3 @ sk_A ) ) ) )
      | ~ ( v13_waybel_0 @ X0 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v2_waybel_0 @ X0 @ ( k7_lattice3 @ sk_A ) )
      | ( v1_xboole_0 @ X0 )
      | ~ ( l1_orders_2 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v2_lattice3 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v1_lattice3 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v2_waybel_1 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v5_orders_2 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v4_orders_2 @ ( k7_lattice3 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['12','33'])).

thf('35',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_C )
      | ~ ( v1_xboole_0 @ ( sk_D @ X0 @ sk_C @ ( k7_lattice3 @ sk_A ) ) )
      | ~ ( r1_subset_1 @ sk_C @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k7_lattice3 @ sk_A ) ) ) )
      | ~ ( v13_waybel_0 @ X0 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v2_waybel_0 @ X0 @ ( k7_lattice3 @ sk_A ) )
      | ( v1_xboole_0 @ X0 )
      | ~ ( l1_orders_2 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v2_lattice3 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v1_lattice3 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v2_waybel_1 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v5_orders_2 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v4_orders_2 @ ( k7_lattice3 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['34','35','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v5_orders_2 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v2_waybel_1 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v1_lattice3 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v2_lattice3 @ ( k7_lattice3 @ sk_A ) )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v2_waybel_0 @ X0 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v13_waybel_0 @ X0 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k7_lattice3 @ sk_A ) ) ) )
      | ~ ( r1_subset_1 @ sk_C @ X0 )
      | ~ ( v1_xboole_0 @ ( sk_D @ X0 @ sk_C @ ( k7_lattice3 @ sk_A ) ) )
      | ( v1_xboole_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['11','37'])).

thf('39',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    ! [X0: $i] :
      ( ~ ( v4_orders_2 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v5_orders_2 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v2_waybel_1 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v1_lattice3 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v2_lattice3 @ ( k7_lattice3 @ sk_A ) )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v2_waybel_0 @ X0 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v13_waybel_0 @ X0 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k7_lattice3 @ sk_A ) ) ) )
      | ~ ( r1_subset_1 @ sk_C @ X0 )
      | ~ ( v1_xboole_0 @ ( sk_D @ X0 @ sk_C @ ( k7_lattice3 @ sk_A ) ) )
      | ( v1_xboole_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ~ ( v4_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ( v1_xboole_0 @ sk_C )
      | ~ ( v1_xboole_0 @ ( sk_D @ X0 @ sk_C @ ( k7_lattice3 @ sk_A ) ) )
      | ~ ( r1_subset_1 @ sk_C @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k7_lattice3 @ sk_A ) ) ) )
      | ~ ( v13_waybel_0 @ X0 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v2_waybel_0 @ X0 @ ( k7_lattice3 @ sk_A ) )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v2_lattice3 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v1_lattice3 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v2_waybel_1 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v5_orders_2 @ ( k7_lattice3 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['10','40'])).

thf('42',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_C )
      | ~ ( v1_xboole_0 @ ( sk_D @ X0 @ sk_C @ ( k7_lattice3 @ sk_A ) ) )
      | ~ ( r1_subset_1 @ sk_C @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k7_lattice3 @ sk_A ) ) ) )
      | ~ ( v13_waybel_0 @ X0 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v2_waybel_0 @ X0 @ ( k7_lattice3 @ sk_A ) )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v2_lattice3 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v1_lattice3 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v2_waybel_1 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v5_orders_2 @ ( k7_lattice3 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['41','42','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ~ ( v1_lattice3 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v2_waybel_1 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v1_lattice3 @ ( k7_lattice3 @ sk_A ) )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v2_waybel_0 @ X0 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v13_waybel_0 @ X0 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k7_lattice3 @ sk_A ) ) ) )
      | ~ ( r1_subset_1 @ sk_C @ X0 )
      | ~ ( v1_xboole_0 @ ( sk_D @ X0 @ sk_C @ ( k7_lattice3 @ sk_A ) ) )
      | ( v1_xboole_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['9','44'])).

thf('46',plain,(
    v1_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    ! [X0: $i] :
      ( ~ ( v5_orders_2 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v2_waybel_1 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v1_lattice3 @ ( k7_lattice3 @ sk_A ) )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v2_waybel_0 @ X0 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v13_waybel_0 @ X0 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k7_lattice3 @ sk_A ) ) ) )
      | ~ ( r1_subset_1 @ sk_C @ X0 )
      | ~ ( v1_xboole_0 @ ( sk_D @ X0 @ sk_C @ ( k7_lattice3 @ sk_A ) ) )
      | ( v1_xboole_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['45','46','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ( v1_xboole_0 @ sk_C )
      | ~ ( v1_xboole_0 @ ( sk_D @ X0 @ sk_C @ ( k7_lattice3 @ sk_A ) ) )
      | ~ ( r1_subset_1 @ sk_C @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k7_lattice3 @ sk_A ) ) ) )
      | ~ ( v13_waybel_0 @ X0 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v2_waybel_0 @ X0 @ ( k7_lattice3 @ sk_A ) )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_lattice3 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v2_waybel_1 @ ( k7_lattice3 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['8','48'])).

thf('50',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_C )
      | ~ ( v1_xboole_0 @ ( sk_D @ X0 @ sk_C @ ( k7_lattice3 @ sk_A ) ) )
      | ~ ( r1_subset_1 @ sk_C @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k7_lattice3 @ sk_A ) ) ) )
      | ~ ( v13_waybel_0 @ X0 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v2_waybel_0 @ X0 @ ( k7_lattice3 @ sk_A ) )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_lattice3 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v2_waybel_1 @ ( k7_lattice3 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['49','50','51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ~ ( v2_lattice3 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( v2_waybel_1 @ ( k7_lattice3 @ sk_A ) )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v2_waybel_0 @ X0 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v13_waybel_0 @ X0 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k7_lattice3 @ sk_A ) ) ) )
      | ~ ( r1_subset_1 @ sk_C @ X0 )
      | ~ ( v1_xboole_0 @ ( sk_D @ X0 @ sk_C @ ( k7_lattice3 @ sk_A ) ) )
      | ( v1_xboole_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['7','52'])).

thf('54',plain,(
    v2_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    ! [X0: $i] :
      ( ~ ( v2_waybel_1 @ ( k7_lattice3 @ sk_A ) )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v2_waybel_0 @ X0 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v13_waybel_0 @ X0 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k7_lattice3 @ sk_A ) ) ) )
      | ~ ( r1_subset_1 @ sk_C @ X0 )
      | ~ ( v1_xboole_0 @ ( sk_D @ X0 @ sk_C @ ( k7_lattice3 @ sk_A ) ) )
      | ( v1_xboole_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['53','54','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( v1_lattice3 @ sk_A )
      | ~ ( v2_lattice3 @ sk_A )
      | ~ ( v2_waybel_1 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ( v1_xboole_0 @ sk_C )
      | ~ ( v1_xboole_0 @ ( sk_D @ X0 @ sk_C @ ( k7_lattice3 @ sk_A ) ) )
      | ~ ( r1_subset_1 @ sk_C @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k7_lattice3 @ sk_A ) ) ) )
      | ~ ( v13_waybel_0 @ X0 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v2_waybel_0 @ X0 @ ( k7_lattice3 @ sk_A ) )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','56'])).

thf('58',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    v1_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    v2_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    v2_waybel_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_C )
      | ~ ( v1_xboole_0 @ ( sk_D @ X0 @ sk_C @ ( k7_lattice3 @ sk_A ) ) )
      | ~ ( r1_subset_1 @ sk_C @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k7_lattice3 @ sk_A ) ) ) )
      | ~ ( v13_waybel_0 @ X0 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v2_waybel_0 @ X0 @ ( k7_lattice3 @ sk_A ) )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['57','58','59','60','61','62','63','64'])).

thf('66',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ~ ( v2_waybel_0 @ sk_B @ ( k7_lattice3 @ sk_A ) )
    | ~ ( v13_waybel_0 @ sk_B @ ( k7_lattice3 @ sk_A ) )
    | ~ ( r1_subset_1 @ sk_C @ sk_B )
    | ~ ( v1_xboole_0 @ ( sk_D @ sk_B @ sk_C @ ( k7_lattice3 @ sk_A ) ) )
    | ( v1_xboole_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['5','65'])).

thf('67',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( v1_waybel_0 @ X14 @ X13 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ( v2_waybel_0 @ X14 @ ( k7_lattice3 @ X13 ) )
      | ~ ( l1_orders_2 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t26_yellow_7])).

thf('69',plain,
    ( ~ ( l1_orders_2 @ sk_A )
    | ( v2_waybel_0 @ sk_B @ ( k7_lattice3 @ sk_A ) )
    | ~ ( v1_waybel_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    v1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    v2_waybel_0 @ sk_B @ ( k7_lattice3 @ sk_A ) ),
    inference(demod,[status(thm)],['69','70','71'])).

thf('73',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t28_yellow_7,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ! [B: $i] :
          ( ( ( v12_waybel_0 @ B @ A )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
        <=> ( ( v13_waybel_0 @ B @ ( k7_lattice3 @ A ) )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k7_lattice3 @ A ) ) ) ) ) ) ) )).

thf('74',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( v12_waybel_0 @ X23 @ X22 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ( v13_waybel_0 @ X23 @ ( k7_lattice3 @ X22 ) )
      | ~ ( l1_orders_2 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t28_yellow_7])).

thf('75',plain,
    ( ~ ( l1_orders_2 @ sk_A )
    | ( v13_waybel_0 @ sk_B @ ( k7_lattice3 @ sk_A ) )
    | ~ ( v12_waybel_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    v12_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    v13_waybel_0 @ sk_B @ ( k7_lattice3 @ sk_A ) ),
    inference(demod,[status(thm)],['75','76','77'])).

thf('79',plain,(
    r1_subset_1 @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(symmetry_r1_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ~ ( v1_xboole_0 @ B ) )
     => ( ( r1_subset_1 @ A @ B )
       => ( r1_subset_1 @ B @ A ) ) ) )).

thf('80',plain,(
    ! [X7: $i,X8: $i] :
      ( ( v1_xboole_0 @ X7 )
      | ( v1_xboole_0 @ X8 )
      | ( r1_subset_1 @ X8 @ X7 )
      | ~ ( r1_subset_1 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_subset_1])).

thf('81',plain,
    ( ( r1_subset_1 @ sk_C @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    ~ ( v1_xboole_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( r1_subset_1 @ sk_C @ sk_B ) ),
    inference(clc,[status(thm)],['81','82'])).

thf('84',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    r1_subset_1 @ sk_C @ sk_B ),
    inference(clc,[status(thm)],['83','84'])).

thf('86',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ~ ( v1_xboole_0 @ ( sk_D @ sk_B @ sk_C @ ( k7_lattice3 @ sk_A ) ) )
    | ( v1_xboole_0 @ sk_C ) ),
    inference(demod,[status(thm)],['66','72','78','85'])).

thf('87',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,
    ( ( v1_xboole_0 @ sk_C )
    | ~ ( v1_xboole_0 @ ( sk_D @ sk_B @ sk_C @ ( k7_lattice3 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['86','87'])).

thf('89',plain,(
    ~ ( v1_xboole_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    ~ ( v1_xboole_0 @ ( sk_D @ sk_B @ sk_C @ ( k7_lattice3 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['88','89'])).

thf('91',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k7_lattice3 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['2','3','4'])).

thf('92',plain,(
    ! [X6: $i] :
      ( ( v2_waybel_1 @ ( k7_lattice3 @ X6 ) )
      | ~ ( l1_orders_2 @ X6 )
      | ~ ( v2_waybel_1 @ X6 )
      | ~ ( v2_lattice3 @ X6 )
      | ~ ( v1_lattice3 @ X6 )
      | ~ ( v5_orders_2 @ X6 )
      | ~ ( v4_orders_2 @ X6 )
      | ~ ( v3_orders_2 @ X6 ) ) ),
    inference(cnf,[status(esa)],[fc8_yellow_7])).

thf('93',plain,(
    ! [X4: $i] :
      ( ( v1_lattice3 @ ( k7_lattice3 @ X4 ) )
      | ~ ( l1_orders_2 @ X4 )
      | ~ ( v2_lattice3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc5_yellow_7])).

thf('94',plain,(
    ! [X3: $i] :
      ( ( v5_orders_2 @ ( k7_lattice3 @ X3 ) )
      | ~ ( l1_orders_2 @ X3 )
      | ~ ( v5_orders_2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc3_yellow_7])).

thf('95',plain,(
    ! [X5: $i] :
      ( ( v2_lattice3 @ ( k7_lattice3 @ X5 ) )
      | ~ ( l1_orders_2 @ X5 )
      | ~ ( v1_lattice3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[fc6_yellow_7])).

thf('96',plain,(
    ! [X2: $i] :
      ( ( v4_orders_2 @ ( k7_lattice3 @ X2 ) )
      | ~ ( l1_orders_2 @ X2 )
      | ~ ( v4_orders_2 @ X2 ) ) ),
    inference(cnf,[status(esa)],[fc2_yellow_7])).

thf('97',plain,(
    ! [X0: $i] :
      ( ( l1_orders_2 @ ( k7_lattice3 @ X0 ) )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_k7_lattice3])).

thf('98',plain,(
    ! [X1: $i] :
      ( ( v3_orders_2 @ ( k7_lattice3 @ X1 ) )
      | ~ ( l1_orders_2 @ X1 )
      | ~ ( v3_orders_2 @ X1 ) ) ),
    inference(cnf,[status(esa)],[fc1_yellow_7])).

thf('99',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k7_lattice3 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['15','16','17'])).

thf('100',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( v1_xboole_0 @ X15 )
      | ~ ( v1_waybel_0 @ X15 @ X16 )
      | ~ ( v12_waybel_0 @ X15 @ X16 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ( m1_subset_1 @ ( sk_D @ X17 @ X15 @ X16 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( r1_subset_1 @ X15 @ X17 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( v13_waybel_0 @ X17 @ X16 )
      | ~ ( v2_waybel_0 @ X17 @ X16 )
      | ( v1_xboole_0 @ X17 )
      | ~ ( l1_orders_2 @ X16 )
      | ~ ( v2_lattice3 @ X16 )
      | ~ ( v1_lattice3 @ X16 )
      | ~ ( v2_waybel_1 @ X16 )
      | ~ ( v5_orders_2 @ X16 )
      | ~ ( v4_orders_2 @ X16 )
      | ~ ( v3_orders_2 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t27_waybel_7])).

thf('101',plain,(
    ! [X0: $i] :
      ( ~ ( v3_orders_2 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v4_orders_2 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v5_orders_2 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v2_waybel_1 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v1_lattice3 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v2_lattice3 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( l1_orders_2 @ ( k7_lattice3 @ sk_A ) )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v2_waybel_0 @ X0 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v13_waybel_0 @ X0 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k7_lattice3 @ sk_A ) ) ) )
      | ~ ( r1_subset_1 @ sk_C @ X0 )
      | ( m1_subset_1 @ ( sk_D @ X0 @ sk_C @ ( k7_lattice3 @ sk_A ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k7_lattice3 @ sk_A ) ) ) )
      | ~ ( v12_waybel_0 @ sk_C @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v1_waybel_0 @ sk_C @ ( k7_lattice3 @ sk_A ) )
      | ( v1_xboole_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,(
    v12_waybel_0 @ sk_C @ ( k7_lattice3 @ sk_A ) ),
    inference(demod,[status(thm)],['23','24','25'])).

thf('103',plain,(
    v1_waybel_0 @ sk_C @ ( k7_lattice3 @ sk_A ) ),
    inference(demod,[status(thm)],['29','30','31'])).

thf('104',plain,(
    ! [X0: $i] :
      ( ~ ( v3_orders_2 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v4_orders_2 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v5_orders_2 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v2_waybel_1 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v1_lattice3 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v2_lattice3 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( l1_orders_2 @ ( k7_lattice3 @ sk_A ) )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v2_waybel_0 @ X0 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v13_waybel_0 @ X0 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k7_lattice3 @ sk_A ) ) ) )
      | ~ ( r1_subset_1 @ sk_C @ X0 )
      | ( m1_subset_1 @ ( sk_D @ X0 @ sk_C @ ( k7_lattice3 @ sk_A ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k7_lattice3 @ sk_A ) ) ) )
      | ( v1_xboole_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['101','102','103'])).

thf('105',plain,(
    ! [X0: $i] :
      ( ~ ( v3_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ( v1_xboole_0 @ sk_C )
      | ( m1_subset_1 @ ( sk_D @ X0 @ sk_C @ ( k7_lattice3 @ sk_A ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k7_lattice3 @ sk_A ) ) ) )
      | ~ ( r1_subset_1 @ sk_C @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k7_lattice3 @ sk_A ) ) ) )
      | ~ ( v13_waybel_0 @ X0 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v2_waybel_0 @ X0 @ ( k7_lattice3 @ sk_A ) )
      | ( v1_xboole_0 @ X0 )
      | ~ ( l1_orders_2 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v2_lattice3 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v1_lattice3 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v2_waybel_1 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v5_orders_2 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v4_orders_2 @ ( k7_lattice3 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['98','104'])).

thf('106',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_C )
      | ( m1_subset_1 @ ( sk_D @ X0 @ sk_C @ ( k7_lattice3 @ sk_A ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k7_lattice3 @ sk_A ) ) ) )
      | ~ ( r1_subset_1 @ sk_C @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k7_lattice3 @ sk_A ) ) ) )
      | ~ ( v13_waybel_0 @ X0 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v2_waybel_0 @ X0 @ ( k7_lattice3 @ sk_A ) )
      | ( v1_xboole_0 @ X0 )
      | ~ ( l1_orders_2 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v2_lattice3 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v1_lattice3 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v2_waybel_1 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v5_orders_2 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v4_orders_2 @ ( k7_lattice3 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['105','106','107'])).

thf('109',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v5_orders_2 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v2_waybel_1 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v1_lattice3 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v2_lattice3 @ ( k7_lattice3 @ sk_A ) )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v2_waybel_0 @ X0 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v13_waybel_0 @ X0 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k7_lattice3 @ sk_A ) ) ) )
      | ~ ( r1_subset_1 @ sk_C @ X0 )
      | ( m1_subset_1 @ ( sk_D @ X0 @ sk_C @ ( k7_lattice3 @ sk_A ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k7_lattice3 @ sk_A ) ) ) )
      | ( v1_xboole_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['97','108'])).

thf('110',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,(
    ! [X0: $i] :
      ( ~ ( v4_orders_2 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v5_orders_2 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v2_waybel_1 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v1_lattice3 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v2_lattice3 @ ( k7_lattice3 @ sk_A ) )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v2_waybel_0 @ X0 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v13_waybel_0 @ X0 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k7_lattice3 @ sk_A ) ) ) )
      | ~ ( r1_subset_1 @ sk_C @ X0 )
      | ( m1_subset_1 @ ( sk_D @ X0 @ sk_C @ ( k7_lattice3 @ sk_A ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k7_lattice3 @ sk_A ) ) ) )
      | ( v1_xboole_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['109','110'])).

thf('112',plain,(
    ! [X0: $i] :
      ( ~ ( v4_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ( v1_xboole_0 @ sk_C )
      | ( m1_subset_1 @ ( sk_D @ X0 @ sk_C @ ( k7_lattice3 @ sk_A ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k7_lattice3 @ sk_A ) ) ) )
      | ~ ( r1_subset_1 @ sk_C @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k7_lattice3 @ sk_A ) ) ) )
      | ~ ( v13_waybel_0 @ X0 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v2_waybel_0 @ X0 @ ( k7_lattice3 @ sk_A ) )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v2_lattice3 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v1_lattice3 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v2_waybel_1 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v5_orders_2 @ ( k7_lattice3 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['96','111'])).

thf('113',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_C )
      | ( m1_subset_1 @ ( sk_D @ X0 @ sk_C @ ( k7_lattice3 @ sk_A ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k7_lattice3 @ sk_A ) ) ) )
      | ~ ( r1_subset_1 @ sk_C @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k7_lattice3 @ sk_A ) ) ) )
      | ~ ( v13_waybel_0 @ X0 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v2_waybel_0 @ X0 @ ( k7_lattice3 @ sk_A ) )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v2_lattice3 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v1_lattice3 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v2_waybel_1 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v5_orders_2 @ ( k7_lattice3 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['112','113','114'])).

thf('116',plain,(
    ! [X0: $i] :
      ( ~ ( v1_lattice3 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v2_waybel_1 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v1_lattice3 @ ( k7_lattice3 @ sk_A ) )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v2_waybel_0 @ X0 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v13_waybel_0 @ X0 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k7_lattice3 @ sk_A ) ) ) )
      | ~ ( r1_subset_1 @ sk_C @ X0 )
      | ( m1_subset_1 @ ( sk_D @ X0 @ sk_C @ ( k7_lattice3 @ sk_A ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k7_lattice3 @ sk_A ) ) ) )
      | ( v1_xboole_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['95','115'])).

thf('117',plain,(
    v1_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,(
    ! [X0: $i] :
      ( ~ ( v5_orders_2 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v2_waybel_1 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v1_lattice3 @ ( k7_lattice3 @ sk_A ) )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v2_waybel_0 @ X0 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v13_waybel_0 @ X0 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k7_lattice3 @ sk_A ) ) ) )
      | ~ ( r1_subset_1 @ sk_C @ X0 )
      | ( m1_subset_1 @ ( sk_D @ X0 @ sk_C @ ( k7_lattice3 @ sk_A ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k7_lattice3 @ sk_A ) ) ) )
      | ( v1_xboole_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['116','117','118'])).

thf('120',plain,(
    ! [X0: $i] :
      ( ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ( v1_xboole_0 @ sk_C )
      | ( m1_subset_1 @ ( sk_D @ X0 @ sk_C @ ( k7_lattice3 @ sk_A ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k7_lattice3 @ sk_A ) ) ) )
      | ~ ( r1_subset_1 @ sk_C @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k7_lattice3 @ sk_A ) ) ) )
      | ~ ( v13_waybel_0 @ X0 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v2_waybel_0 @ X0 @ ( k7_lattice3 @ sk_A ) )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_lattice3 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v2_waybel_1 @ ( k7_lattice3 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['94','119'])).

thf('121',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_C )
      | ( m1_subset_1 @ ( sk_D @ X0 @ sk_C @ ( k7_lattice3 @ sk_A ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k7_lattice3 @ sk_A ) ) ) )
      | ~ ( r1_subset_1 @ sk_C @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k7_lattice3 @ sk_A ) ) ) )
      | ~ ( v13_waybel_0 @ X0 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v2_waybel_0 @ X0 @ ( k7_lattice3 @ sk_A ) )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_lattice3 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v2_waybel_1 @ ( k7_lattice3 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['120','121','122'])).

thf('124',plain,(
    ! [X0: $i] :
      ( ~ ( v2_lattice3 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( v2_waybel_1 @ ( k7_lattice3 @ sk_A ) )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v2_waybel_0 @ X0 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v13_waybel_0 @ X0 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k7_lattice3 @ sk_A ) ) ) )
      | ~ ( r1_subset_1 @ sk_C @ X0 )
      | ( m1_subset_1 @ ( sk_D @ X0 @ sk_C @ ( k7_lattice3 @ sk_A ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k7_lattice3 @ sk_A ) ) ) )
      | ( v1_xboole_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['93','123'])).

thf('125',plain,(
    v2_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,(
    ! [X0: $i] :
      ( ~ ( v2_waybel_1 @ ( k7_lattice3 @ sk_A ) )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v2_waybel_0 @ X0 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v13_waybel_0 @ X0 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k7_lattice3 @ sk_A ) ) ) )
      | ~ ( r1_subset_1 @ sk_C @ X0 )
      | ( m1_subset_1 @ ( sk_D @ X0 @ sk_C @ ( k7_lattice3 @ sk_A ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k7_lattice3 @ sk_A ) ) ) )
      | ( v1_xboole_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['124','125','126'])).

thf('128',plain,(
    ! [X0: $i] :
      ( ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( v1_lattice3 @ sk_A )
      | ~ ( v2_lattice3 @ sk_A )
      | ~ ( v2_waybel_1 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ( v1_xboole_0 @ sk_C )
      | ( m1_subset_1 @ ( sk_D @ X0 @ sk_C @ ( k7_lattice3 @ sk_A ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k7_lattice3 @ sk_A ) ) ) )
      | ~ ( r1_subset_1 @ sk_C @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k7_lattice3 @ sk_A ) ) ) )
      | ~ ( v13_waybel_0 @ X0 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v2_waybel_0 @ X0 @ ( k7_lattice3 @ sk_A ) )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['92','127'])).

thf('129',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('130',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('131',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('132',plain,(
    v1_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('133',plain,(
    v2_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('134',plain,(
    v2_waybel_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('135',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('136',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_C )
      | ( m1_subset_1 @ ( sk_D @ X0 @ sk_C @ ( k7_lattice3 @ sk_A ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k7_lattice3 @ sk_A ) ) ) )
      | ~ ( r1_subset_1 @ sk_C @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k7_lattice3 @ sk_A ) ) ) )
      | ~ ( v13_waybel_0 @ X0 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v2_waybel_0 @ X0 @ ( k7_lattice3 @ sk_A ) )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['128','129','130','131','132','133','134','135'])).

thf('137',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ~ ( v2_waybel_0 @ sk_B @ ( k7_lattice3 @ sk_A ) )
    | ~ ( v13_waybel_0 @ sk_B @ ( k7_lattice3 @ sk_A ) )
    | ~ ( r1_subset_1 @ sk_C @ sk_B )
    | ( m1_subset_1 @ ( sk_D @ sk_B @ sk_C @ ( k7_lattice3 @ sk_A ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k7_lattice3 @ sk_A ) ) ) )
    | ( v1_xboole_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['91','136'])).

thf('138',plain,(
    v2_waybel_0 @ sk_B @ ( k7_lattice3 @ sk_A ) ),
    inference(demod,[status(thm)],['69','70','71'])).

thf('139',plain,(
    v13_waybel_0 @ sk_B @ ( k7_lattice3 @ sk_A ) ),
    inference(demod,[status(thm)],['75','76','77'])).

thf('140',plain,(
    r1_subset_1 @ sk_C @ sk_B ),
    inference(clc,[status(thm)],['83','84'])).

thf('141',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( m1_subset_1 @ ( sk_D @ sk_B @ sk_C @ ( k7_lattice3 @ sk_A ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k7_lattice3 @ sk_A ) ) ) )
    | ( v1_xboole_0 @ sk_C ) ),
    inference(demod,[status(thm)],['137','138','139','140'])).

thf('142',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('143',plain,
    ( ( v1_xboole_0 @ sk_C )
    | ( m1_subset_1 @ ( sk_D @ sk_B @ sk_C @ ( k7_lattice3 @ sk_A ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k7_lattice3 @ sk_A ) ) ) ) ),
    inference(clc,[status(thm)],['141','142'])).

thf('144',plain,(
    ~ ( v1_xboole_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('145',plain,(
    m1_subset_1 @ ( sk_D @ sk_B @ sk_C @ ( k7_lattice3 @ sk_A ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k7_lattice3 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['143','144'])).

thf(t21_waybel_7,axiom,(
    ! [A: $i] :
      ( ( ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( v1_lattice3 @ A )
        & ( v2_lattice3 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v1_xboole_0 @ B )
            & ( v2_waybel_0 @ B @ A )
            & ( v13_waybel_0 @ B @ A )
            & ( v2_waybel_7 @ B @ A )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
        <=> ( ~ ( v1_xboole_0 @ B )
            & ( v1_waybel_0 @ B @ ( k7_lattice3 @ A ) )
            & ( v12_waybel_0 @ B @ ( k7_lattice3 @ A ) )
            & ( v1_waybel_7 @ B @ ( k7_lattice3 @ A ) )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k7_lattice3 @ A ) ) ) ) ) ) ) )).

thf('146',plain,(
    ! [X9: $i,X10: $i] :
      ( ( v1_xboole_0 @ X9 )
      | ~ ( v1_waybel_0 @ X9 @ ( k7_lattice3 @ X10 ) )
      | ~ ( v12_waybel_0 @ X9 @ ( k7_lattice3 @ X10 ) )
      | ~ ( v1_waybel_7 @ X9 @ ( k7_lattice3 @ X10 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k7_lattice3 @ X10 ) ) ) )
      | ( v2_waybel_7 @ X9 @ X10 )
      | ~ ( l1_orders_2 @ X10 )
      | ~ ( v2_lattice3 @ X10 )
      | ~ ( v1_lattice3 @ X10 )
      | ~ ( v5_orders_2 @ X10 )
      | ~ ( v4_orders_2 @ X10 )
      | ~ ( v3_orders_2 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t21_waybel_7])).

thf('147',plain,
    ( ~ ( v3_orders_2 @ sk_A )
    | ~ ( v4_orders_2 @ sk_A )
    | ~ ( v5_orders_2 @ sk_A )
    | ~ ( v1_lattice3 @ sk_A )
    | ~ ( v2_lattice3 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A )
    | ( v2_waybel_7 @ ( sk_D @ sk_B @ sk_C @ ( k7_lattice3 @ sk_A ) ) @ sk_A )
    | ~ ( v1_waybel_7 @ ( sk_D @ sk_B @ sk_C @ ( k7_lattice3 @ sk_A ) ) @ ( k7_lattice3 @ sk_A ) )
    | ~ ( v12_waybel_0 @ ( sk_D @ sk_B @ sk_C @ ( k7_lattice3 @ sk_A ) ) @ ( k7_lattice3 @ sk_A ) )
    | ~ ( v1_waybel_0 @ ( sk_D @ sk_B @ sk_C @ ( k7_lattice3 @ sk_A ) ) @ ( k7_lattice3 @ sk_A ) )
    | ( v1_xboole_0 @ ( sk_D @ sk_B @ sk_C @ ( k7_lattice3 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['145','146'])).

thf('148',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('149',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('150',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('151',plain,(
    v1_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('152',plain,(
    v2_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('153',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('154',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k7_lattice3 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['2','3','4'])).

thf('155',plain,(
    ! [X6: $i] :
      ( ( v2_waybel_1 @ ( k7_lattice3 @ X6 ) )
      | ~ ( l1_orders_2 @ X6 )
      | ~ ( v2_waybel_1 @ X6 )
      | ~ ( v2_lattice3 @ X6 )
      | ~ ( v1_lattice3 @ X6 )
      | ~ ( v5_orders_2 @ X6 )
      | ~ ( v4_orders_2 @ X6 )
      | ~ ( v3_orders_2 @ X6 ) ) ),
    inference(cnf,[status(esa)],[fc8_yellow_7])).

thf('156',plain,(
    ! [X4: $i] :
      ( ( v1_lattice3 @ ( k7_lattice3 @ X4 ) )
      | ~ ( l1_orders_2 @ X4 )
      | ~ ( v2_lattice3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc5_yellow_7])).

thf('157',plain,(
    ! [X3: $i] :
      ( ( v5_orders_2 @ ( k7_lattice3 @ X3 ) )
      | ~ ( l1_orders_2 @ X3 )
      | ~ ( v5_orders_2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc3_yellow_7])).

thf('158',plain,(
    ! [X5: $i] :
      ( ( v2_lattice3 @ ( k7_lattice3 @ X5 ) )
      | ~ ( l1_orders_2 @ X5 )
      | ~ ( v1_lattice3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[fc6_yellow_7])).

thf('159',plain,(
    ! [X2: $i] :
      ( ( v4_orders_2 @ ( k7_lattice3 @ X2 ) )
      | ~ ( l1_orders_2 @ X2 )
      | ~ ( v4_orders_2 @ X2 ) ) ),
    inference(cnf,[status(esa)],[fc2_yellow_7])).

thf('160',plain,(
    ! [X0: $i] :
      ( ( l1_orders_2 @ ( k7_lattice3 @ X0 ) )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_k7_lattice3])).

thf('161',plain,(
    ! [X1: $i] :
      ( ( v3_orders_2 @ ( k7_lattice3 @ X1 ) )
      | ~ ( l1_orders_2 @ X1 )
      | ~ ( v3_orders_2 @ X1 ) ) ),
    inference(cnf,[status(esa)],[fc1_yellow_7])).

thf('162',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k7_lattice3 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['15','16','17'])).

thf('163',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( v1_xboole_0 @ X15 )
      | ~ ( v1_waybel_0 @ X15 @ X16 )
      | ~ ( v12_waybel_0 @ X15 @ X16 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ( v1_waybel_7 @ ( sk_D @ X17 @ X15 @ X16 ) @ X16 )
      | ~ ( r1_subset_1 @ X15 @ X17 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( v13_waybel_0 @ X17 @ X16 )
      | ~ ( v2_waybel_0 @ X17 @ X16 )
      | ( v1_xboole_0 @ X17 )
      | ~ ( l1_orders_2 @ X16 )
      | ~ ( v2_lattice3 @ X16 )
      | ~ ( v1_lattice3 @ X16 )
      | ~ ( v2_waybel_1 @ X16 )
      | ~ ( v5_orders_2 @ X16 )
      | ~ ( v4_orders_2 @ X16 )
      | ~ ( v3_orders_2 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t27_waybel_7])).

thf('164',plain,(
    ! [X0: $i] :
      ( ~ ( v3_orders_2 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v4_orders_2 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v5_orders_2 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v2_waybel_1 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v1_lattice3 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v2_lattice3 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( l1_orders_2 @ ( k7_lattice3 @ sk_A ) )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v2_waybel_0 @ X0 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v13_waybel_0 @ X0 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k7_lattice3 @ sk_A ) ) ) )
      | ~ ( r1_subset_1 @ sk_C @ X0 )
      | ( v1_waybel_7 @ ( sk_D @ X0 @ sk_C @ ( k7_lattice3 @ sk_A ) ) @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v12_waybel_0 @ sk_C @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v1_waybel_0 @ sk_C @ ( k7_lattice3 @ sk_A ) )
      | ( v1_xboole_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['162','163'])).

thf('165',plain,(
    v12_waybel_0 @ sk_C @ ( k7_lattice3 @ sk_A ) ),
    inference(demod,[status(thm)],['23','24','25'])).

thf('166',plain,(
    v1_waybel_0 @ sk_C @ ( k7_lattice3 @ sk_A ) ),
    inference(demod,[status(thm)],['29','30','31'])).

thf('167',plain,(
    ! [X0: $i] :
      ( ~ ( v3_orders_2 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v4_orders_2 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v5_orders_2 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v2_waybel_1 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v1_lattice3 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v2_lattice3 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( l1_orders_2 @ ( k7_lattice3 @ sk_A ) )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v2_waybel_0 @ X0 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v13_waybel_0 @ X0 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k7_lattice3 @ sk_A ) ) ) )
      | ~ ( r1_subset_1 @ sk_C @ X0 )
      | ( v1_waybel_7 @ ( sk_D @ X0 @ sk_C @ ( k7_lattice3 @ sk_A ) ) @ ( k7_lattice3 @ sk_A ) )
      | ( v1_xboole_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['164','165','166'])).

thf('168',plain,(
    ! [X0: $i] :
      ( ~ ( v3_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ( v1_xboole_0 @ sk_C )
      | ( v1_waybel_7 @ ( sk_D @ X0 @ sk_C @ ( k7_lattice3 @ sk_A ) ) @ ( k7_lattice3 @ sk_A ) )
      | ~ ( r1_subset_1 @ sk_C @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k7_lattice3 @ sk_A ) ) ) )
      | ~ ( v13_waybel_0 @ X0 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v2_waybel_0 @ X0 @ ( k7_lattice3 @ sk_A ) )
      | ( v1_xboole_0 @ X0 )
      | ~ ( l1_orders_2 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v2_lattice3 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v1_lattice3 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v2_waybel_1 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v5_orders_2 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v4_orders_2 @ ( k7_lattice3 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['161','167'])).

thf('169',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('170',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('171',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_C )
      | ( v1_waybel_7 @ ( sk_D @ X0 @ sk_C @ ( k7_lattice3 @ sk_A ) ) @ ( k7_lattice3 @ sk_A ) )
      | ~ ( r1_subset_1 @ sk_C @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k7_lattice3 @ sk_A ) ) ) )
      | ~ ( v13_waybel_0 @ X0 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v2_waybel_0 @ X0 @ ( k7_lattice3 @ sk_A ) )
      | ( v1_xboole_0 @ X0 )
      | ~ ( l1_orders_2 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v2_lattice3 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v1_lattice3 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v2_waybel_1 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v5_orders_2 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v4_orders_2 @ ( k7_lattice3 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['168','169','170'])).

thf('172',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v5_orders_2 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v2_waybel_1 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v1_lattice3 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v2_lattice3 @ ( k7_lattice3 @ sk_A ) )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v2_waybel_0 @ X0 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v13_waybel_0 @ X0 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k7_lattice3 @ sk_A ) ) ) )
      | ~ ( r1_subset_1 @ sk_C @ X0 )
      | ( v1_waybel_7 @ ( sk_D @ X0 @ sk_C @ ( k7_lattice3 @ sk_A ) ) @ ( k7_lattice3 @ sk_A ) )
      | ( v1_xboole_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['160','171'])).

thf('173',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('174',plain,(
    ! [X0: $i] :
      ( ~ ( v4_orders_2 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v5_orders_2 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v2_waybel_1 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v1_lattice3 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v2_lattice3 @ ( k7_lattice3 @ sk_A ) )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v2_waybel_0 @ X0 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v13_waybel_0 @ X0 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k7_lattice3 @ sk_A ) ) ) )
      | ~ ( r1_subset_1 @ sk_C @ X0 )
      | ( v1_waybel_7 @ ( sk_D @ X0 @ sk_C @ ( k7_lattice3 @ sk_A ) ) @ ( k7_lattice3 @ sk_A ) )
      | ( v1_xboole_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['172','173'])).

thf('175',plain,(
    ! [X0: $i] :
      ( ~ ( v4_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ( v1_xboole_0 @ sk_C )
      | ( v1_waybel_7 @ ( sk_D @ X0 @ sk_C @ ( k7_lattice3 @ sk_A ) ) @ ( k7_lattice3 @ sk_A ) )
      | ~ ( r1_subset_1 @ sk_C @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k7_lattice3 @ sk_A ) ) ) )
      | ~ ( v13_waybel_0 @ X0 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v2_waybel_0 @ X0 @ ( k7_lattice3 @ sk_A ) )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v2_lattice3 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v1_lattice3 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v2_waybel_1 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v5_orders_2 @ ( k7_lattice3 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['159','174'])).

thf('176',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('177',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('178',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_C )
      | ( v1_waybel_7 @ ( sk_D @ X0 @ sk_C @ ( k7_lattice3 @ sk_A ) ) @ ( k7_lattice3 @ sk_A ) )
      | ~ ( r1_subset_1 @ sk_C @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k7_lattice3 @ sk_A ) ) ) )
      | ~ ( v13_waybel_0 @ X0 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v2_waybel_0 @ X0 @ ( k7_lattice3 @ sk_A ) )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v2_lattice3 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v1_lattice3 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v2_waybel_1 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v5_orders_2 @ ( k7_lattice3 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['175','176','177'])).

thf('179',plain,(
    ! [X0: $i] :
      ( ~ ( v1_lattice3 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v2_waybel_1 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v1_lattice3 @ ( k7_lattice3 @ sk_A ) )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v2_waybel_0 @ X0 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v13_waybel_0 @ X0 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k7_lattice3 @ sk_A ) ) ) )
      | ~ ( r1_subset_1 @ sk_C @ X0 )
      | ( v1_waybel_7 @ ( sk_D @ X0 @ sk_C @ ( k7_lattice3 @ sk_A ) ) @ ( k7_lattice3 @ sk_A ) )
      | ( v1_xboole_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['158','178'])).

thf('180',plain,(
    v1_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('181',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('182',plain,(
    ! [X0: $i] :
      ( ~ ( v5_orders_2 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v2_waybel_1 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v1_lattice3 @ ( k7_lattice3 @ sk_A ) )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v2_waybel_0 @ X0 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v13_waybel_0 @ X0 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k7_lattice3 @ sk_A ) ) ) )
      | ~ ( r1_subset_1 @ sk_C @ X0 )
      | ( v1_waybel_7 @ ( sk_D @ X0 @ sk_C @ ( k7_lattice3 @ sk_A ) ) @ ( k7_lattice3 @ sk_A ) )
      | ( v1_xboole_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['179','180','181'])).

thf('183',plain,(
    ! [X0: $i] :
      ( ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ( v1_xboole_0 @ sk_C )
      | ( v1_waybel_7 @ ( sk_D @ X0 @ sk_C @ ( k7_lattice3 @ sk_A ) ) @ ( k7_lattice3 @ sk_A ) )
      | ~ ( r1_subset_1 @ sk_C @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k7_lattice3 @ sk_A ) ) ) )
      | ~ ( v13_waybel_0 @ X0 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v2_waybel_0 @ X0 @ ( k7_lattice3 @ sk_A ) )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_lattice3 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v2_waybel_1 @ ( k7_lattice3 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['157','182'])).

thf('184',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('185',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('186',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_C )
      | ( v1_waybel_7 @ ( sk_D @ X0 @ sk_C @ ( k7_lattice3 @ sk_A ) ) @ ( k7_lattice3 @ sk_A ) )
      | ~ ( r1_subset_1 @ sk_C @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k7_lattice3 @ sk_A ) ) ) )
      | ~ ( v13_waybel_0 @ X0 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v2_waybel_0 @ X0 @ ( k7_lattice3 @ sk_A ) )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_lattice3 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v2_waybel_1 @ ( k7_lattice3 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['183','184','185'])).

thf('187',plain,(
    ! [X0: $i] :
      ( ~ ( v2_lattice3 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( v2_waybel_1 @ ( k7_lattice3 @ sk_A ) )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v2_waybel_0 @ X0 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v13_waybel_0 @ X0 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k7_lattice3 @ sk_A ) ) ) )
      | ~ ( r1_subset_1 @ sk_C @ X0 )
      | ( v1_waybel_7 @ ( sk_D @ X0 @ sk_C @ ( k7_lattice3 @ sk_A ) ) @ ( k7_lattice3 @ sk_A ) )
      | ( v1_xboole_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['156','186'])).

thf('188',plain,(
    v2_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('189',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('190',plain,(
    ! [X0: $i] :
      ( ~ ( v2_waybel_1 @ ( k7_lattice3 @ sk_A ) )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v2_waybel_0 @ X0 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v13_waybel_0 @ X0 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k7_lattice3 @ sk_A ) ) ) )
      | ~ ( r1_subset_1 @ sk_C @ X0 )
      | ( v1_waybel_7 @ ( sk_D @ X0 @ sk_C @ ( k7_lattice3 @ sk_A ) ) @ ( k7_lattice3 @ sk_A ) )
      | ( v1_xboole_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['187','188','189'])).

thf('191',plain,(
    ! [X0: $i] :
      ( ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( v1_lattice3 @ sk_A )
      | ~ ( v2_lattice3 @ sk_A )
      | ~ ( v2_waybel_1 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ( v1_xboole_0 @ sk_C )
      | ( v1_waybel_7 @ ( sk_D @ X0 @ sk_C @ ( k7_lattice3 @ sk_A ) ) @ ( k7_lattice3 @ sk_A ) )
      | ~ ( r1_subset_1 @ sk_C @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k7_lattice3 @ sk_A ) ) ) )
      | ~ ( v13_waybel_0 @ X0 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v2_waybel_0 @ X0 @ ( k7_lattice3 @ sk_A ) )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['155','190'])).

thf('192',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('193',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('194',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('195',plain,(
    v1_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('196',plain,(
    v2_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('197',plain,(
    v2_waybel_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('198',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('199',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_C )
      | ( v1_waybel_7 @ ( sk_D @ X0 @ sk_C @ ( k7_lattice3 @ sk_A ) ) @ ( k7_lattice3 @ sk_A ) )
      | ~ ( r1_subset_1 @ sk_C @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k7_lattice3 @ sk_A ) ) ) )
      | ~ ( v13_waybel_0 @ X0 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v2_waybel_0 @ X0 @ ( k7_lattice3 @ sk_A ) )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['191','192','193','194','195','196','197','198'])).

thf('200',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ~ ( v2_waybel_0 @ sk_B @ ( k7_lattice3 @ sk_A ) )
    | ~ ( v13_waybel_0 @ sk_B @ ( k7_lattice3 @ sk_A ) )
    | ~ ( r1_subset_1 @ sk_C @ sk_B )
    | ( v1_waybel_7 @ ( sk_D @ sk_B @ sk_C @ ( k7_lattice3 @ sk_A ) ) @ ( k7_lattice3 @ sk_A ) )
    | ( v1_xboole_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['154','199'])).

thf('201',plain,(
    v2_waybel_0 @ sk_B @ ( k7_lattice3 @ sk_A ) ),
    inference(demod,[status(thm)],['69','70','71'])).

thf('202',plain,(
    v13_waybel_0 @ sk_B @ ( k7_lattice3 @ sk_A ) ),
    inference(demod,[status(thm)],['75','76','77'])).

thf('203',plain,(
    r1_subset_1 @ sk_C @ sk_B ),
    inference(clc,[status(thm)],['83','84'])).

thf('204',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( v1_waybel_7 @ ( sk_D @ sk_B @ sk_C @ ( k7_lattice3 @ sk_A ) ) @ ( k7_lattice3 @ sk_A ) )
    | ( v1_xboole_0 @ sk_C ) ),
    inference(demod,[status(thm)],['200','201','202','203'])).

thf('205',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('206',plain,
    ( ( v1_xboole_0 @ sk_C )
    | ( v1_waybel_7 @ ( sk_D @ sk_B @ sk_C @ ( k7_lattice3 @ sk_A ) ) @ ( k7_lattice3 @ sk_A ) ) ),
    inference(clc,[status(thm)],['204','205'])).

thf('207',plain,(
    ~ ( v1_xboole_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('208',plain,(
    v1_waybel_7 @ ( sk_D @ sk_B @ sk_C @ ( k7_lattice3 @ sk_A ) ) @ ( k7_lattice3 @ sk_A ) ),
    inference(clc,[status(thm)],['206','207'])).

thf('209',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k7_lattice3 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['2','3','4'])).

thf('210',plain,(
    ! [X6: $i] :
      ( ( v2_waybel_1 @ ( k7_lattice3 @ X6 ) )
      | ~ ( l1_orders_2 @ X6 )
      | ~ ( v2_waybel_1 @ X6 )
      | ~ ( v2_lattice3 @ X6 )
      | ~ ( v1_lattice3 @ X6 )
      | ~ ( v5_orders_2 @ X6 )
      | ~ ( v4_orders_2 @ X6 )
      | ~ ( v3_orders_2 @ X6 ) ) ),
    inference(cnf,[status(esa)],[fc8_yellow_7])).

thf('211',plain,(
    ! [X4: $i] :
      ( ( v1_lattice3 @ ( k7_lattice3 @ X4 ) )
      | ~ ( l1_orders_2 @ X4 )
      | ~ ( v2_lattice3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc5_yellow_7])).

thf('212',plain,(
    ! [X3: $i] :
      ( ( v5_orders_2 @ ( k7_lattice3 @ X3 ) )
      | ~ ( l1_orders_2 @ X3 )
      | ~ ( v5_orders_2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc3_yellow_7])).

thf('213',plain,(
    ! [X5: $i] :
      ( ( v2_lattice3 @ ( k7_lattice3 @ X5 ) )
      | ~ ( l1_orders_2 @ X5 )
      | ~ ( v1_lattice3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[fc6_yellow_7])).

thf('214',plain,(
    ! [X2: $i] :
      ( ( v4_orders_2 @ ( k7_lattice3 @ X2 ) )
      | ~ ( l1_orders_2 @ X2 )
      | ~ ( v4_orders_2 @ X2 ) ) ),
    inference(cnf,[status(esa)],[fc2_yellow_7])).

thf('215',plain,(
    ! [X0: $i] :
      ( ( l1_orders_2 @ ( k7_lattice3 @ X0 ) )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_k7_lattice3])).

thf('216',plain,(
    ! [X1: $i] :
      ( ( v3_orders_2 @ ( k7_lattice3 @ X1 ) )
      | ~ ( l1_orders_2 @ X1 )
      | ~ ( v3_orders_2 @ X1 ) ) ),
    inference(cnf,[status(esa)],[fc1_yellow_7])).

thf('217',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k7_lattice3 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['15','16','17'])).

thf('218',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( v1_xboole_0 @ X15 )
      | ~ ( v1_waybel_0 @ X15 @ X16 )
      | ~ ( v12_waybel_0 @ X15 @ X16 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ( v12_waybel_0 @ ( sk_D @ X17 @ X15 @ X16 ) @ X16 )
      | ~ ( r1_subset_1 @ X15 @ X17 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( v13_waybel_0 @ X17 @ X16 )
      | ~ ( v2_waybel_0 @ X17 @ X16 )
      | ( v1_xboole_0 @ X17 )
      | ~ ( l1_orders_2 @ X16 )
      | ~ ( v2_lattice3 @ X16 )
      | ~ ( v1_lattice3 @ X16 )
      | ~ ( v2_waybel_1 @ X16 )
      | ~ ( v5_orders_2 @ X16 )
      | ~ ( v4_orders_2 @ X16 )
      | ~ ( v3_orders_2 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t27_waybel_7])).

thf('219',plain,(
    ! [X0: $i] :
      ( ~ ( v3_orders_2 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v4_orders_2 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v5_orders_2 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v2_waybel_1 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v1_lattice3 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v2_lattice3 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( l1_orders_2 @ ( k7_lattice3 @ sk_A ) )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v2_waybel_0 @ X0 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v13_waybel_0 @ X0 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k7_lattice3 @ sk_A ) ) ) )
      | ~ ( r1_subset_1 @ sk_C @ X0 )
      | ( v12_waybel_0 @ ( sk_D @ X0 @ sk_C @ ( k7_lattice3 @ sk_A ) ) @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v12_waybel_0 @ sk_C @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v1_waybel_0 @ sk_C @ ( k7_lattice3 @ sk_A ) )
      | ( v1_xboole_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['217','218'])).

thf('220',plain,(
    v12_waybel_0 @ sk_C @ ( k7_lattice3 @ sk_A ) ),
    inference(demod,[status(thm)],['23','24','25'])).

thf('221',plain,(
    v1_waybel_0 @ sk_C @ ( k7_lattice3 @ sk_A ) ),
    inference(demod,[status(thm)],['29','30','31'])).

thf('222',plain,(
    ! [X0: $i] :
      ( ~ ( v3_orders_2 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v4_orders_2 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v5_orders_2 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v2_waybel_1 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v1_lattice3 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v2_lattice3 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( l1_orders_2 @ ( k7_lattice3 @ sk_A ) )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v2_waybel_0 @ X0 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v13_waybel_0 @ X0 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k7_lattice3 @ sk_A ) ) ) )
      | ~ ( r1_subset_1 @ sk_C @ X0 )
      | ( v12_waybel_0 @ ( sk_D @ X0 @ sk_C @ ( k7_lattice3 @ sk_A ) ) @ ( k7_lattice3 @ sk_A ) )
      | ( v1_xboole_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['219','220','221'])).

thf('223',plain,(
    ! [X0: $i] :
      ( ~ ( v3_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ( v1_xboole_0 @ sk_C )
      | ( v12_waybel_0 @ ( sk_D @ X0 @ sk_C @ ( k7_lattice3 @ sk_A ) ) @ ( k7_lattice3 @ sk_A ) )
      | ~ ( r1_subset_1 @ sk_C @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k7_lattice3 @ sk_A ) ) ) )
      | ~ ( v13_waybel_0 @ X0 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v2_waybel_0 @ X0 @ ( k7_lattice3 @ sk_A ) )
      | ( v1_xboole_0 @ X0 )
      | ~ ( l1_orders_2 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v2_lattice3 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v1_lattice3 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v2_waybel_1 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v5_orders_2 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v4_orders_2 @ ( k7_lattice3 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['216','222'])).

thf('224',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('225',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('226',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_C )
      | ( v12_waybel_0 @ ( sk_D @ X0 @ sk_C @ ( k7_lattice3 @ sk_A ) ) @ ( k7_lattice3 @ sk_A ) )
      | ~ ( r1_subset_1 @ sk_C @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k7_lattice3 @ sk_A ) ) ) )
      | ~ ( v13_waybel_0 @ X0 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v2_waybel_0 @ X0 @ ( k7_lattice3 @ sk_A ) )
      | ( v1_xboole_0 @ X0 )
      | ~ ( l1_orders_2 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v2_lattice3 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v1_lattice3 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v2_waybel_1 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v5_orders_2 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v4_orders_2 @ ( k7_lattice3 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['223','224','225'])).

thf('227',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v5_orders_2 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v2_waybel_1 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v1_lattice3 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v2_lattice3 @ ( k7_lattice3 @ sk_A ) )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v2_waybel_0 @ X0 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v13_waybel_0 @ X0 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k7_lattice3 @ sk_A ) ) ) )
      | ~ ( r1_subset_1 @ sk_C @ X0 )
      | ( v12_waybel_0 @ ( sk_D @ X0 @ sk_C @ ( k7_lattice3 @ sk_A ) ) @ ( k7_lattice3 @ sk_A ) )
      | ( v1_xboole_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['215','226'])).

thf('228',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('229',plain,(
    ! [X0: $i] :
      ( ~ ( v4_orders_2 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v5_orders_2 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v2_waybel_1 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v1_lattice3 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v2_lattice3 @ ( k7_lattice3 @ sk_A ) )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v2_waybel_0 @ X0 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v13_waybel_0 @ X0 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k7_lattice3 @ sk_A ) ) ) )
      | ~ ( r1_subset_1 @ sk_C @ X0 )
      | ( v12_waybel_0 @ ( sk_D @ X0 @ sk_C @ ( k7_lattice3 @ sk_A ) ) @ ( k7_lattice3 @ sk_A ) )
      | ( v1_xboole_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['227','228'])).

thf('230',plain,(
    ! [X0: $i] :
      ( ~ ( v4_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ( v1_xboole_0 @ sk_C )
      | ( v12_waybel_0 @ ( sk_D @ X0 @ sk_C @ ( k7_lattice3 @ sk_A ) ) @ ( k7_lattice3 @ sk_A ) )
      | ~ ( r1_subset_1 @ sk_C @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k7_lattice3 @ sk_A ) ) ) )
      | ~ ( v13_waybel_0 @ X0 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v2_waybel_0 @ X0 @ ( k7_lattice3 @ sk_A ) )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v2_lattice3 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v1_lattice3 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v2_waybel_1 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v5_orders_2 @ ( k7_lattice3 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['214','229'])).

thf('231',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('232',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('233',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_C )
      | ( v12_waybel_0 @ ( sk_D @ X0 @ sk_C @ ( k7_lattice3 @ sk_A ) ) @ ( k7_lattice3 @ sk_A ) )
      | ~ ( r1_subset_1 @ sk_C @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k7_lattice3 @ sk_A ) ) ) )
      | ~ ( v13_waybel_0 @ X0 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v2_waybel_0 @ X0 @ ( k7_lattice3 @ sk_A ) )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v2_lattice3 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v1_lattice3 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v2_waybel_1 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v5_orders_2 @ ( k7_lattice3 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['230','231','232'])).

thf('234',plain,(
    ! [X0: $i] :
      ( ~ ( v1_lattice3 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v2_waybel_1 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v1_lattice3 @ ( k7_lattice3 @ sk_A ) )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v2_waybel_0 @ X0 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v13_waybel_0 @ X0 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k7_lattice3 @ sk_A ) ) ) )
      | ~ ( r1_subset_1 @ sk_C @ X0 )
      | ( v12_waybel_0 @ ( sk_D @ X0 @ sk_C @ ( k7_lattice3 @ sk_A ) ) @ ( k7_lattice3 @ sk_A ) )
      | ( v1_xboole_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['213','233'])).

thf('235',plain,(
    v1_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('236',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('237',plain,(
    ! [X0: $i] :
      ( ~ ( v5_orders_2 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v2_waybel_1 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v1_lattice3 @ ( k7_lattice3 @ sk_A ) )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v2_waybel_0 @ X0 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v13_waybel_0 @ X0 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k7_lattice3 @ sk_A ) ) ) )
      | ~ ( r1_subset_1 @ sk_C @ X0 )
      | ( v12_waybel_0 @ ( sk_D @ X0 @ sk_C @ ( k7_lattice3 @ sk_A ) ) @ ( k7_lattice3 @ sk_A ) )
      | ( v1_xboole_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['234','235','236'])).

thf('238',plain,(
    ! [X0: $i] :
      ( ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ( v1_xboole_0 @ sk_C )
      | ( v12_waybel_0 @ ( sk_D @ X0 @ sk_C @ ( k7_lattice3 @ sk_A ) ) @ ( k7_lattice3 @ sk_A ) )
      | ~ ( r1_subset_1 @ sk_C @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k7_lattice3 @ sk_A ) ) ) )
      | ~ ( v13_waybel_0 @ X0 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v2_waybel_0 @ X0 @ ( k7_lattice3 @ sk_A ) )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_lattice3 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v2_waybel_1 @ ( k7_lattice3 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['212','237'])).

thf('239',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('240',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('241',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_C )
      | ( v12_waybel_0 @ ( sk_D @ X0 @ sk_C @ ( k7_lattice3 @ sk_A ) ) @ ( k7_lattice3 @ sk_A ) )
      | ~ ( r1_subset_1 @ sk_C @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k7_lattice3 @ sk_A ) ) ) )
      | ~ ( v13_waybel_0 @ X0 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v2_waybel_0 @ X0 @ ( k7_lattice3 @ sk_A ) )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_lattice3 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v2_waybel_1 @ ( k7_lattice3 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['238','239','240'])).

thf('242',plain,(
    ! [X0: $i] :
      ( ~ ( v2_lattice3 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( v2_waybel_1 @ ( k7_lattice3 @ sk_A ) )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v2_waybel_0 @ X0 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v13_waybel_0 @ X0 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k7_lattice3 @ sk_A ) ) ) )
      | ~ ( r1_subset_1 @ sk_C @ X0 )
      | ( v12_waybel_0 @ ( sk_D @ X0 @ sk_C @ ( k7_lattice3 @ sk_A ) ) @ ( k7_lattice3 @ sk_A ) )
      | ( v1_xboole_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['211','241'])).

thf('243',plain,(
    v2_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('244',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('245',plain,(
    ! [X0: $i] :
      ( ~ ( v2_waybel_1 @ ( k7_lattice3 @ sk_A ) )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v2_waybel_0 @ X0 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v13_waybel_0 @ X0 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k7_lattice3 @ sk_A ) ) ) )
      | ~ ( r1_subset_1 @ sk_C @ X0 )
      | ( v12_waybel_0 @ ( sk_D @ X0 @ sk_C @ ( k7_lattice3 @ sk_A ) ) @ ( k7_lattice3 @ sk_A ) )
      | ( v1_xboole_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['242','243','244'])).

thf('246',plain,(
    ! [X0: $i] :
      ( ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( v1_lattice3 @ sk_A )
      | ~ ( v2_lattice3 @ sk_A )
      | ~ ( v2_waybel_1 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ( v1_xboole_0 @ sk_C )
      | ( v12_waybel_0 @ ( sk_D @ X0 @ sk_C @ ( k7_lattice3 @ sk_A ) ) @ ( k7_lattice3 @ sk_A ) )
      | ~ ( r1_subset_1 @ sk_C @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k7_lattice3 @ sk_A ) ) ) )
      | ~ ( v13_waybel_0 @ X0 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v2_waybel_0 @ X0 @ ( k7_lattice3 @ sk_A ) )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['210','245'])).

thf('247',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('248',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('249',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('250',plain,(
    v1_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('251',plain,(
    v2_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('252',plain,(
    v2_waybel_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('253',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('254',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_C )
      | ( v12_waybel_0 @ ( sk_D @ X0 @ sk_C @ ( k7_lattice3 @ sk_A ) ) @ ( k7_lattice3 @ sk_A ) )
      | ~ ( r1_subset_1 @ sk_C @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k7_lattice3 @ sk_A ) ) ) )
      | ~ ( v13_waybel_0 @ X0 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v2_waybel_0 @ X0 @ ( k7_lattice3 @ sk_A ) )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['246','247','248','249','250','251','252','253'])).

thf('255',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ~ ( v2_waybel_0 @ sk_B @ ( k7_lattice3 @ sk_A ) )
    | ~ ( v13_waybel_0 @ sk_B @ ( k7_lattice3 @ sk_A ) )
    | ~ ( r1_subset_1 @ sk_C @ sk_B )
    | ( v12_waybel_0 @ ( sk_D @ sk_B @ sk_C @ ( k7_lattice3 @ sk_A ) ) @ ( k7_lattice3 @ sk_A ) )
    | ( v1_xboole_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['209','254'])).

thf('256',plain,(
    v2_waybel_0 @ sk_B @ ( k7_lattice3 @ sk_A ) ),
    inference(demod,[status(thm)],['69','70','71'])).

thf('257',plain,(
    v13_waybel_0 @ sk_B @ ( k7_lattice3 @ sk_A ) ),
    inference(demod,[status(thm)],['75','76','77'])).

thf('258',plain,(
    r1_subset_1 @ sk_C @ sk_B ),
    inference(clc,[status(thm)],['83','84'])).

thf('259',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( v12_waybel_0 @ ( sk_D @ sk_B @ sk_C @ ( k7_lattice3 @ sk_A ) ) @ ( k7_lattice3 @ sk_A ) )
    | ( v1_xboole_0 @ sk_C ) ),
    inference(demod,[status(thm)],['255','256','257','258'])).

thf('260',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('261',plain,
    ( ( v1_xboole_0 @ sk_C )
    | ( v12_waybel_0 @ ( sk_D @ sk_B @ sk_C @ ( k7_lattice3 @ sk_A ) ) @ ( k7_lattice3 @ sk_A ) ) ),
    inference(clc,[status(thm)],['259','260'])).

thf('262',plain,(
    ~ ( v1_xboole_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('263',plain,(
    v12_waybel_0 @ ( sk_D @ sk_B @ sk_C @ ( k7_lattice3 @ sk_A ) ) @ ( k7_lattice3 @ sk_A ) ),
    inference(clc,[status(thm)],['261','262'])).

thf('264',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k7_lattice3 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['2','3','4'])).

thf('265',plain,(
    ! [X6: $i] :
      ( ( v2_waybel_1 @ ( k7_lattice3 @ X6 ) )
      | ~ ( l1_orders_2 @ X6 )
      | ~ ( v2_waybel_1 @ X6 )
      | ~ ( v2_lattice3 @ X6 )
      | ~ ( v1_lattice3 @ X6 )
      | ~ ( v5_orders_2 @ X6 )
      | ~ ( v4_orders_2 @ X6 )
      | ~ ( v3_orders_2 @ X6 ) ) ),
    inference(cnf,[status(esa)],[fc8_yellow_7])).

thf('266',plain,(
    ! [X4: $i] :
      ( ( v1_lattice3 @ ( k7_lattice3 @ X4 ) )
      | ~ ( l1_orders_2 @ X4 )
      | ~ ( v2_lattice3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc5_yellow_7])).

thf('267',plain,(
    ! [X3: $i] :
      ( ( v5_orders_2 @ ( k7_lattice3 @ X3 ) )
      | ~ ( l1_orders_2 @ X3 )
      | ~ ( v5_orders_2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc3_yellow_7])).

thf('268',plain,(
    ! [X5: $i] :
      ( ( v2_lattice3 @ ( k7_lattice3 @ X5 ) )
      | ~ ( l1_orders_2 @ X5 )
      | ~ ( v1_lattice3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[fc6_yellow_7])).

thf('269',plain,(
    ! [X2: $i] :
      ( ( v4_orders_2 @ ( k7_lattice3 @ X2 ) )
      | ~ ( l1_orders_2 @ X2 )
      | ~ ( v4_orders_2 @ X2 ) ) ),
    inference(cnf,[status(esa)],[fc2_yellow_7])).

thf('270',plain,(
    ! [X0: $i] :
      ( ( l1_orders_2 @ ( k7_lattice3 @ X0 ) )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_k7_lattice3])).

thf('271',plain,(
    ! [X1: $i] :
      ( ( v3_orders_2 @ ( k7_lattice3 @ X1 ) )
      | ~ ( l1_orders_2 @ X1 )
      | ~ ( v3_orders_2 @ X1 ) ) ),
    inference(cnf,[status(esa)],[fc1_yellow_7])).

thf('272',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k7_lattice3 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['15','16','17'])).

thf('273',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( v1_xboole_0 @ X15 )
      | ~ ( v1_waybel_0 @ X15 @ X16 )
      | ~ ( v12_waybel_0 @ X15 @ X16 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ( v1_waybel_0 @ ( sk_D @ X17 @ X15 @ X16 ) @ X16 )
      | ~ ( r1_subset_1 @ X15 @ X17 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( v13_waybel_0 @ X17 @ X16 )
      | ~ ( v2_waybel_0 @ X17 @ X16 )
      | ( v1_xboole_0 @ X17 )
      | ~ ( l1_orders_2 @ X16 )
      | ~ ( v2_lattice3 @ X16 )
      | ~ ( v1_lattice3 @ X16 )
      | ~ ( v2_waybel_1 @ X16 )
      | ~ ( v5_orders_2 @ X16 )
      | ~ ( v4_orders_2 @ X16 )
      | ~ ( v3_orders_2 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t27_waybel_7])).

thf('274',plain,(
    ! [X0: $i] :
      ( ~ ( v3_orders_2 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v4_orders_2 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v5_orders_2 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v2_waybel_1 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v1_lattice3 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v2_lattice3 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( l1_orders_2 @ ( k7_lattice3 @ sk_A ) )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v2_waybel_0 @ X0 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v13_waybel_0 @ X0 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k7_lattice3 @ sk_A ) ) ) )
      | ~ ( r1_subset_1 @ sk_C @ X0 )
      | ( v1_waybel_0 @ ( sk_D @ X0 @ sk_C @ ( k7_lattice3 @ sk_A ) ) @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v12_waybel_0 @ sk_C @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v1_waybel_0 @ sk_C @ ( k7_lattice3 @ sk_A ) )
      | ( v1_xboole_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['272','273'])).

thf('275',plain,(
    v12_waybel_0 @ sk_C @ ( k7_lattice3 @ sk_A ) ),
    inference(demod,[status(thm)],['23','24','25'])).

thf('276',plain,(
    v1_waybel_0 @ sk_C @ ( k7_lattice3 @ sk_A ) ),
    inference(demod,[status(thm)],['29','30','31'])).

thf('277',plain,(
    ! [X0: $i] :
      ( ~ ( v3_orders_2 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v4_orders_2 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v5_orders_2 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v2_waybel_1 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v1_lattice3 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v2_lattice3 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( l1_orders_2 @ ( k7_lattice3 @ sk_A ) )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v2_waybel_0 @ X0 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v13_waybel_0 @ X0 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k7_lattice3 @ sk_A ) ) ) )
      | ~ ( r1_subset_1 @ sk_C @ X0 )
      | ( v1_waybel_0 @ ( sk_D @ X0 @ sk_C @ ( k7_lattice3 @ sk_A ) ) @ ( k7_lattice3 @ sk_A ) )
      | ( v1_xboole_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['274','275','276'])).

thf('278',plain,(
    ! [X0: $i] :
      ( ~ ( v3_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ( v1_xboole_0 @ sk_C )
      | ( v1_waybel_0 @ ( sk_D @ X0 @ sk_C @ ( k7_lattice3 @ sk_A ) ) @ ( k7_lattice3 @ sk_A ) )
      | ~ ( r1_subset_1 @ sk_C @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k7_lattice3 @ sk_A ) ) ) )
      | ~ ( v13_waybel_0 @ X0 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v2_waybel_0 @ X0 @ ( k7_lattice3 @ sk_A ) )
      | ( v1_xboole_0 @ X0 )
      | ~ ( l1_orders_2 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v2_lattice3 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v1_lattice3 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v2_waybel_1 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v5_orders_2 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v4_orders_2 @ ( k7_lattice3 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['271','277'])).

thf('279',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('280',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('281',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_C )
      | ( v1_waybel_0 @ ( sk_D @ X0 @ sk_C @ ( k7_lattice3 @ sk_A ) ) @ ( k7_lattice3 @ sk_A ) )
      | ~ ( r1_subset_1 @ sk_C @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k7_lattice3 @ sk_A ) ) ) )
      | ~ ( v13_waybel_0 @ X0 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v2_waybel_0 @ X0 @ ( k7_lattice3 @ sk_A ) )
      | ( v1_xboole_0 @ X0 )
      | ~ ( l1_orders_2 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v2_lattice3 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v1_lattice3 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v2_waybel_1 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v5_orders_2 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v4_orders_2 @ ( k7_lattice3 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['278','279','280'])).

thf('282',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v5_orders_2 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v2_waybel_1 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v1_lattice3 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v2_lattice3 @ ( k7_lattice3 @ sk_A ) )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v2_waybel_0 @ X0 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v13_waybel_0 @ X0 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k7_lattice3 @ sk_A ) ) ) )
      | ~ ( r1_subset_1 @ sk_C @ X0 )
      | ( v1_waybel_0 @ ( sk_D @ X0 @ sk_C @ ( k7_lattice3 @ sk_A ) ) @ ( k7_lattice3 @ sk_A ) )
      | ( v1_xboole_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['270','281'])).

thf('283',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('284',plain,(
    ! [X0: $i] :
      ( ~ ( v4_orders_2 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v5_orders_2 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v2_waybel_1 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v1_lattice3 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v2_lattice3 @ ( k7_lattice3 @ sk_A ) )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v2_waybel_0 @ X0 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v13_waybel_0 @ X0 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k7_lattice3 @ sk_A ) ) ) )
      | ~ ( r1_subset_1 @ sk_C @ X0 )
      | ( v1_waybel_0 @ ( sk_D @ X0 @ sk_C @ ( k7_lattice3 @ sk_A ) ) @ ( k7_lattice3 @ sk_A ) )
      | ( v1_xboole_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['282','283'])).

thf('285',plain,(
    ! [X0: $i] :
      ( ~ ( v4_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ( v1_xboole_0 @ sk_C )
      | ( v1_waybel_0 @ ( sk_D @ X0 @ sk_C @ ( k7_lattice3 @ sk_A ) ) @ ( k7_lattice3 @ sk_A ) )
      | ~ ( r1_subset_1 @ sk_C @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k7_lattice3 @ sk_A ) ) ) )
      | ~ ( v13_waybel_0 @ X0 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v2_waybel_0 @ X0 @ ( k7_lattice3 @ sk_A ) )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v2_lattice3 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v1_lattice3 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v2_waybel_1 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v5_orders_2 @ ( k7_lattice3 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['269','284'])).

thf('286',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('287',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('288',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_C )
      | ( v1_waybel_0 @ ( sk_D @ X0 @ sk_C @ ( k7_lattice3 @ sk_A ) ) @ ( k7_lattice3 @ sk_A ) )
      | ~ ( r1_subset_1 @ sk_C @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k7_lattice3 @ sk_A ) ) ) )
      | ~ ( v13_waybel_0 @ X0 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v2_waybel_0 @ X0 @ ( k7_lattice3 @ sk_A ) )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v2_lattice3 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v1_lattice3 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v2_waybel_1 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v5_orders_2 @ ( k7_lattice3 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['285','286','287'])).

thf('289',plain,(
    ! [X0: $i] :
      ( ~ ( v1_lattice3 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v2_waybel_1 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v1_lattice3 @ ( k7_lattice3 @ sk_A ) )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v2_waybel_0 @ X0 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v13_waybel_0 @ X0 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k7_lattice3 @ sk_A ) ) ) )
      | ~ ( r1_subset_1 @ sk_C @ X0 )
      | ( v1_waybel_0 @ ( sk_D @ X0 @ sk_C @ ( k7_lattice3 @ sk_A ) ) @ ( k7_lattice3 @ sk_A ) )
      | ( v1_xboole_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['268','288'])).

thf('290',plain,(
    v1_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('291',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('292',plain,(
    ! [X0: $i] :
      ( ~ ( v5_orders_2 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v2_waybel_1 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v1_lattice3 @ ( k7_lattice3 @ sk_A ) )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v2_waybel_0 @ X0 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v13_waybel_0 @ X0 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k7_lattice3 @ sk_A ) ) ) )
      | ~ ( r1_subset_1 @ sk_C @ X0 )
      | ( v1_waybel_0 @ ( sk_D @ X0 @ sk_C @ ( k7_lattice3 @ sk_A ) ) @ ( k7_lattice3 @ sk_A ) )
      | ( v1_xboole_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['289','290','291'])).

thf('293',plain,(
    ! [X0: $i] :
      ( ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ( v1_xboole_0 @ sk_C )
      | ( v1_waybel_0 @ ( sk_D @ X0 @ sk_C @ ( k7_lattice3 @ sk_A ) ) @ ( k7_lattice3 @ sk_A ) )
      | ~ ( r1_subset_1 @ sk_C @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k7_lattice3 @ sk_A ) ) ) )
      | ~ ( v13_waybel_0 @ X0 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v2_waybel_0 @ X0 @ ( k7_lattice3 @ sk_A ) )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_lattice3 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v2_waybel_1 @ ( k7_lattice3 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['267','292'])).

thf('294',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('295',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('296',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_C )
      | ( v1_waybel_0 @ ( sk_D @ X0 @ sk_C @ ( k7_lattice3 @ sk_A ) ) @ ( k7_lattice3 @ sk_A ) )
      | ~ ( r1_subset_1 @ sk_C @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k7_lattice3 @ sk_A ) ) ) )
      | ~ ( v13_waybel_0 @ X0 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v2_waybel_0 @ X0 @ ( k7_lattice3 @ sk_A ) )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_lattice3 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v2_waybel_1 @ ( k7_lattice3 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['293','294','295'])).

thf('297',plain,(
    ! [X0: $i] :
      ( ~ ( v2_lattice3 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( v2_waybel_1 @ ( k7_lattice3 @ sk_A ) )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v2_waybel_0 @ X0 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v13_waybel_0 @ X0 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k7_lattice3 @ sk_A ) ) ) )
      | ~ ( r1_subset_1 @ sk_C @ X0 )
      | ( v1_waybel_0 @ ( sk_D @ X0 @ sk_C @ ( k7_lattice3 @ sk_A ) ) @ ( k7_lattice3 @ sk_A ) )
      | ( v1_xboole_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['266','296'])).

thf('298',plain,(
    v2_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('299',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('300',plain,(
    ! [X0: $i] :
      ( ~ ( v2_waybel_1 @ ( k7_lattice3 @ sk_A ) )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v2_waybel_0 @ X0 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v13_waybel_0 @ X0 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k7_lattice3 @ sk_A ) ) ) )
      | ~ ( r1_subset_1 @ sk_C @ X0 )
      | ( v1_waybel_0 @ ( sk_D @ X0 @ sk_C @ ( k7_lattice3 @ sk_A ) ) @ ( k7_lattice3 @ sk_A ) )
      | ( v1_xboole_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['297','298','299'])).

thf('301',plain,(
    ! [X0: $i] :
      ( ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( v1_lattice3 @ sk_A )
      | ~ ( v2_lattice3 @ sk_A )
      | ~ ( v2_waybel_1 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ( v1_xboole_0 @ sk_C )
      | ( v1_waybel_0 @ ( sk_D @ X0 @ sk_C @ ( k7_lattice3 @ sk_A ) ) @ ( k7_lattice3 @ sk_A ) )
      | ~ ( r1_subset_1 @ sk_C @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k7_lattice3 @ sk_A ) ) ) )
      | ~ ( v13_waybel_0 @ X0 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v2_waybel_0 @ X0 @ ( k7_lattice3 @ sk_A ) )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['265','300'])).

thf('302',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('303',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('304',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('305',plain,(
    v1_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('306',plain,(
    v2_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('307',plain,(
    v2_waybel_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('308',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('309',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_C )
      | ( v1_waybel_0 @ ( sk_D @ X0 @ sk_C @ ( k7_lattice3 @ sk_A ) ) @ ( k7_lattice3 @ sk_A ) )
      | ~ ( r1_subset_1 @ sk_C @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k7_lattice3 @ sk_A ) ) ) )
      | ~ ( v13_waybel_0 @ X0 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v2_waybel_0 @ X0 @ ( k7_lattice3 @ sk_A ) )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['301','302','303','304','305','306','307','308'])).

thf('310',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ~ ( v2_waybel_0 @ sk_B @ ( k7_lattice3 @ sk_A ) )
    | ~ ( v13_waybel_0 @ sk_B @ ( k7_lattice3 @ sk_A ) )
    | ~ ( r1_subset_1 @ sk_C @ sk_B )
    | ( v1_waybel_0 @ ( sk_D @ sk_B @ sk_C @ ( k7_lattice3 @ sk_A ) ) @ ( k7_lattice3 @ sk_A ) )
    | ( v1_xboole_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['264','309'])).

thf('311',plain,(
    v2_waybel_0 @ sk_B @ ( k7_lattice3 @ sk_A ) ),
    inference(demod,[status(thm)],['69','70','71'])).

thf('312',plain,(
    v13_waybel_0 @ sk_B @ ( k7_lattice3 @ sk_A ) ),
    inference(demod,[status(thm)],['75','76','77'])).

thf('313',plain,(
    r1_subset_1 @ sk_C @ sk_B ),
    inference(clc,[status(thm)],['83','84'])).

thf('314',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( v1_waybel_0 @ ( sk_D @ sk_B @ sk_C @ ( k7_lattice3 @ sk_A ) ) @ ( k7_lattice3 @ sk_A ) )
    | ( v1_xboole_0 @ sk_C ) ),
    inference(demod,[status(thm)],['310','311','312','313'])).

thf('315',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('316',plain,
    ( ( v1_xboole_0 @ sk_C )
    | ( v1_waybel_0 @ ( sk_D @ sk_B @ sk_C @ ( k7_lattice3 @ sk_A ) ) @ ( k7_lattice3 @ sk_A ) ) ),
    inference(clc,[status(thm)],['314','315'])).

thf('317',plain,(
    ~ ( v1_xboole_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('318',plain,(
    v1_waybel_0 @ ( sk_D @ sk_B @ sk_C @ ( k7_lattice3 @ sk_A ) ) @ ( k7_lattice3 @ sk_A ) ),
    inference(clc,[status(thm)],['316','317'])).

thf('319',plain,
    ( ( v2_waybel_7 @ ( sk_D @ sk_B @ sk_C @ ( k7_lattice3 @ sk_A ) ) @ sk_A )
    | ( v1_xboole_0 @ ( sk_D @ sk_B @ sk_C @ ( k7_lattice3 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['147','148','149','150','151','152','153','208','263','318'])).

thf('320',plain,(
    m1_subset_1 @ ( sk_D @ sk_B @ sk_C @ ( k7_lattice3 @ sk_A ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k7_lattice3 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['143','144'])).

thf('321',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( v1_waybel_0 @ X20 @ ( k7_lattice3 @ X19 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k7_lattice3 @ X19 ) ) ) )
      | ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( l1_orders_2 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t27_yellow_7])).

thf('322',plain,
    ( ~ ( l1_orders_2 @ sk_A )
    | ( m1_subset_1 @ ( sk_D @ sk_B @ sk_C @ ( k7_lattice3 @ sk_A ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( v1_waybel_0 @ ( sk_D @ sk_B @ sk_C @ ( k7_lattice3 @ sk_A ) ) @ ( k7_lattice3 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['320','321'])).

thf('323',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('324',plain,(
    v1_waybel_0 @ ( sk_D @ sk_B @ sk_C @ ( k7_lattice3 @ sk_A ) ) @ ( k7_lattice3 @ sk_A ) ),
    inference(clc,[status(thm)],['316','317'])).

thf('325',plain,(
    m1_subset_1 @ ( sk_D @ sk_B @ sk_C @ ( k7_lattice3 @ sk_A ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['322','323','324'])).

thf('326',plain,(
    ! [X27: $i] :
      ( ~ ( r1_subset_1 @ sk_B @ X27 )
      | ~ ( r1_tarski @ sk_C @ X27 )
      | ~ ( v2_waybel_7 @ X27 @ sk_A )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v13_waybel_0 @ X27 @ sk_A )
      | ~ ( v2_waybel_0 @ X27 @ sk_A )
      | ( v1_xboole_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('327',plain,
    ( ( v1_xboole_0 @ ( sk_D @ sk_B @ sk_C @ ( k7_lattice3 @ sk_A ) ) )
    | ~ ( v2_waybel_0 @ ( sk_D @ sk_B @ sk_C @ ( k7_lattice3 @ sk_A ) ) @ sk_A )
    | ~ ( v13_waybel_0 @ ( sk_D @ sk_B @ sk_C @ ( k7_lattice3 @ sk_A ) ) @ sk_A )
    | ~ ( v2_waybel_7 @ ( sk_D @ sk_B @ sk_C @ ( k7_lattice3 @ sk_A ) ) @ sk_A )
    | ~ ( r1_tarski @ sk_C @ ( sk_D @ sk_B @ sk_C @ ( k7_lattice3 @ sk_A ) ) )
    | ~ ( r1_subset_1 @ sk_B @ ( sk_D @ sk_B @ sk_C @ ( k7_lattice3 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['325','326'])).

thf('328',plain,(
    m1_subset_1 @ ( sk_D @ sk_B @ sk_C @ ( k7_lattice3 @ sk_A ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k7_lattice3 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['143','144'])).

thf('329',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( v1_waybel_0 @ X20 @ ( k7_lattice3 @ X19 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k7_lattice3 @ X19 ) ) ) )
      | ( v2_waybel_0 @ X20 @ X19 )
      | ~ ( l1_orders_2 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t27_yellow_7])).

thf('330',plain,
    ( ~ ( l1_orders_2 @ sk_A )
    | ( v2_waybel_0 @ ( sk_D @ sk_B @ sk_C @ ( k7_lattice3 @ sk_A ) ) @ sk_A )
    | ~ ( v1_waybel_0 @ ( sk_D @ sk_B @ sk_C @ ( k7_lattice3 @ sk_A ) ) @ ( k7_lattice3 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['328','329'])).

thf('331',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('332',plain,(
    v1_waybel_0 @ ( sk_D @ sk_B @ sk_C @ ( k7_lattice3 @ sk_A ) ) @ ( k7_lattice3 @ sk_A ) ),
    inference(clc,[status(thm)],['316','317'])).

thf('333',plain,(
    v2_waybel_0 @ ( sk_D @ sk_B @ sk_C @ ( k7_lattice3 @ sk_A ) ) @ sk_A ),
    inference(demod,[status(thm)],['330','331','332'])).

thf('334',plain,(
    m1_subset_1 @ ( sk_D @ sk_B @ sk_C @ ( k7_lattice3 @ sk_A ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k7_lattice3 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['143','144'])).

thf('335',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( v12_waybel_0 @ X26 @ ( k7_lattice3 @ X25 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k7_lattice3 @ X25 ) ) ) )
      | ( v13_waybel_0 @ X26 @ X25 )
      | ~ ( l1_orders_2 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t29_yellow_7])).

thf('336',plain,
    ( ~ ( l1_orders_2 @ sk_A )
    | ( v13_waybel_0 @ ( sk_D @ sk_B @ sk_C @ ( k7_lattice3 @ sk_A ) ) @ sk_A )
    | ~ ( v12_waybel_0 @ ( sk_D @ sk_B @ sk_C @ ( k7_lattice3 @ sk_A ) ) @ ( k7_lattice3 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['334','335'])).

thf('337',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('338',plain,(
    v12_waybel_0 @ ( sk_D @ sk_B @ sk_C @ ( k7_lattice3 @ sk_A ) ) @ ( k7_lattice3 @ sk_A ) ),
    inference(clc,[status(thm)],['261','262'])).

thf('339',plain,(
    v13_waybel_0 @ ( sk_D @ sk_B @ sk_C @ ( k7_lattice3 @ sk_A ) ) @ sk_A ),
    inference(demod,[status(thm)],['336','337','338'])).

thf('340',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k7_lattice3 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['2','3','4'])).

thf('341',plain,(
    ! [X6: $i] :
      ( ( v2_waybel_1 @ ( k7_lattice3 @ X6 ) )
      | ~ ( l1_orders_2 @ X6 )
      | ~ ( v2_waybel_1 @ X6 )
      | ~ ( v2_lattice3 @ X6 )
      | ~ ( v1_lattice3 @ X6 )
      | ~ ( v5_orders_2 @ X6 )
      | ~ ( v4_orders_2 @ X6 )
      | ~ ( v3_orders_2 @ X6 ) ) ),
    inference(cnf,[status(esa)],[fc8_yellow_7])).

thf('342',plain,(
    ! [X4: $i] :
      ( ( v1_lattice3 @ ( k7_lattice3 @ X4 ) )
      | ~ ( l1_orders_2 @ X4 )
      | ~ ( v2_lattice3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc5_yellow_7])).

thf('343',plain,(
    ! [X3: $i] :
      ( ( v5_orders_2 @ ( k7_lattice3 @ X3 ) )
      | ~ ( l1_orders_2 @ X3 )
      | ~ ( v5_orders_2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc3_yellow_7])).

thf('344',plain,(
    ! [X5: $i] :
      ( ( v2_lattice3 @ ( k7_lattice3 @ X5 ) )
      | ~ ( l1_orders_2 @ X5 )
      | ~ ( v1_lattice3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[fc6_yellow_7])).

thf('345',plain,(
    ! [X2: $i] :
      ( ( v4_orders_2 @ ( k7_lattice3 @ X2 ) )
      | ~ ( l1_orders_2 @ X2 )
      | ~ ( v4_orders_2 @ X2 ) ) ),
    inference(cnf,[status(esa)],[fc2_yellow_7])).

thf('346',plain,(
    ! [X0: $i] :
      ( ( l1_orders_2 @ ( k7_lattice3 @ X0 ) )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_k7_lattice3])).

thf('347',plain,(
    ! [X1: $i] :
      ( ( v3_orders_2 @ ( k7_lattice3 @ X1 ) )
      | ~ ( l1_orders_2 @ X1 )
      | ~ ( v3_orders_2 @ X1 ) ) ),
    inference(cnf,[status(esa)],[fc1_yellow_7])).

thf('348',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k7_lattice3 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['15','16','17'])).

thf('349',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( v1_xboole_0 @ X15 )
      | ~ ( v1_waybel_0 @ X15 @ X16 )
      | ~ ( v12_waybel_0 @ X15 @ X16 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ( r1_tarski @ X15 @ ( sk_D @ X17 @ X15 @ X16 ) )
      | ~ ( r1_subset_1 @ X15 @ X17 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( v13_waybel_0 @ X17 @ X16 )
      | ~ ( v2_waybel_0 @ X17 @ X16 )
      | ( v1_xboole_0 @ X17 )
      | ~ ( l1_orders_2 @ X16 )
      | ~ ( v2_lattice3 @ X16 )
      | ~ ( v1_lattice3 @ X16 )
      | ~ ( v2_waybel_1 @ X16 )
      | ~ ( v5_orders_2 @ X16 )
      | ~ ( v4_orders_2 @ X16 )
      | ~ ( v3_orders_2 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t27_waybel_7])).

thf('350',plain,(
    ! [X0: $i] :
      ( ~ ( v3_orders_2 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v4_orders_2 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v5_orders_2 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v2_waybel_1 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v1_lattice3 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v2_lattice3 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( l1_orders_2 @ ( k7_lattice3 @ sk_A ) )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v2_waybel_0 @ X0 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v13_waybel_0 @ X0 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k7_lattice3 @ sk_A ) ) ) )
      | ~ ( r1_subset_1 @ sk_C @ X0 )
      | ( r1_tarski @ sk_C @ ( sk_D @ X0 @ sk_C @ ( k7_lattice3 @ sk_A ) ) )
      | ~ ( v12_waybel_0 @ sk_C @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v1_waybel_0 @ sk_C @ ( k7_lattice3 @ sk_A ) )
      | ( v1_xboole_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['348','349'])).

thf('351',plain,(
    v12_waybel_0 @ sk_C @ ( k7_lattice3 @ sk_A ) ),
    inference(demod,[status(thm)],['23','24','25'])).

thf('352',plain,(
    v1_waybel_0 @ sk_C @ ( k7_lattice3 @ sk_A ) ),
    inference(demod,[status(thm)],['29','30','31'])).

thf('353',plain,(
    ! [X0: $i] :
      ( ~ ( v3_orders_2 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v4_orders_2 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v5_orders_2 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v2_waybel_1 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v1_lattice3 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v2_lattice3 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( l1_orders_2 @ ( k7_lattice3 @ sk_A ) )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v2_waybel_0 @ X0 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v13_waybel_0 @ X0 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k7_lattice3 @ sk_A ) ) ) )
      | ~ ( r1_subset_1 @ sk_C @ X0 )
      | ( r1_tarski @ sk_C @ ( sk_D @ X0 @ sk_C @ ( k7_lattice3 @ sk_A ) ) )
      | ( v1_xboole_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['350','351','352'])).

thf('354',plain,(
    ! [X0: $i] :
      ( ~ ( v3_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ( v1_xboole_0 @ sk_C )
      | ( r1_tarski @ sk_C @ ( sk_D @ X0 @ sk_C @ ( k7_lattice3 @ sk_A ) ) )
      | ~ ( r1_subset_1 @ sk_C @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k7_lattice3 @ sk_A ) ) ) )
      | ~ ( v13_waybel_0 @ X0 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v2_waybel_0 @ X0 @ ( k7_lattice3 @ sk_A ) )
      | ( v1_xboole_0 @ X0 )
      | ~ ( l1_orders_2 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v2_lattice3 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v1_lattice3 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v2_waybel_1 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v5_orders_2 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v4_orders_2 @ ( k7_lattice3 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['347','353'])).

thf('355',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('356',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('357',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_C )
      | ( r1_tarski @ sk_C @ ( sk_D @ X0 @ sk_C @ ( k7_lattice3 @ sk_A ) ) )
      | ~ ( r1_subset_1 @ sk_C @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k7_lattice3 @ sk_A ) ) ) )
      | ~ ( v13_waybel_0 @ X0 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v2_waybel_0 @ X0 @ ( k7_lattice3 @ sk_A ) )
      | ( v1_xboole_0 @ X0 )
      | ~ ( l1_orders_2 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v2_lattice3 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v1_lattice3 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v2_waybel_1 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v5_orders_2 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v4_orders_2 @ ( k7_lattice3 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['354','355','356'])).

thf('358',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v5_orders_2 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v2_waybel_1 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v1_lattice3 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v2_lattice3 @ ( k7_lattice3 @ sk_A ) )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v2_waybel_0 @ X0 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v13_waybel_0 @ X0 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k7_lattice3 @ sk_A ) ) ) )
      | ~ ( r1_subset_1 @ sk_C @ X0 )
      | ( r1_tarski @ sk_C @ ( sk_D @ X0 @ sk_C @ ( k7_lattice3 @ sk_A ) ) )
      | ( v1_xboole_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['346','357'])).

thf('359',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('360',plain,(
    ! [X0: $i] :
      ( ~ ( v4_orders_2 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v5_orders_2 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v2_waybel_1 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v1_lattice3 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v2_lattice3 @ ( k7_lattice3 @ sk_A ) )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v2_waybel_0 @ X0 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v13_waybel_0 @ X0 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k7_lattice3 @ sk_A ) ) ) )
      | ~ ( r1_subset_1 @ sk_C @ X0 )
      | ( r1_tarski @ sk_C @ ( sk_D @ X0 @ sk_C @ ( k7_lattice3 @ sk_A ) ) )
      | ( v1_xboole_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['358','359'])).

thf('361',plain,(
    ! [X0: $i] :
      ( ~ ( v4_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ( v1_xboole_0 @ sk_C )
      | ( r1_tarski @ sk_C @ ( sk_D @ X0 @ sk_C @ ( k7_lattice3 @ sk_A ) ) )
      | ~ ( r1_subset_1 @ sk_C @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k7_lattice3 @ sk_A ) ) ) )
      | ~ ( v13_waybel_0 @ X0 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v2_waybel_0 @ X0 @ ( k7_lattice3 @ sk_A ) )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v2_lattice3 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v1_lattice3 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v2_waybel_1 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v5_orders_2 @ ( k7_lattice3 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['345','360'])).

thf('362',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('363',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('364',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_C )
      | ( r1_tarski @ sk_C @ ( sk_D @ X0 @ sk_C @ ( k7_lattice3 @ sk_A ) ) )
      | ~ ( r1_subset_1 @ sk_C @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k7_lattice3 @ sk_A ) ) ) )
      | ~ ( v13_waybel_0 @ X0 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v2_waybel_0 @ X0 @ ( k7_lattice3 @ sk_A ) )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v2_lattice3 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v1_lattice3 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v2_waybel_1 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v5_orders_2 @ ( k7_lattice3 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['361','362','363'])).

thf('365',plain,(
    ! [X0: $i] :
      ( ~ ( v1_lattice3 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v2_waybel_1 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v1_lattice3 @ ( k7_lattice3 @ sk_A ) )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v2_waybel_0 @ X0 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v13_waybel_0 @ X0 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k7_lattice3 @ sk_A ) ) ) )
      | ~ ( r1_subset_1 @ sk_C @ X0 )
      | ( r1_tarski @ sk_C @ ( sk_D @ X0 @ sk_C @ ( k7_lattice3 @ sk_A ) ) )
      | ( v1_xboole_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['344','364'])).

thf('366',plain,(
    v1_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('367',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('368',plain,(
    ! [X0: $i] :
      ( ~ ( v5_orders_2 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v2_waybel_1 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v1_lattice3 @ ( k7_lattice3 @ sk_A ) )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v2_waybel_0 @ X0 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v13_waybel_0 @ X0 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k7_lattice3 @ sk_A ) ) ) )
      | ~ ( r1_subset_1 @ sk_C @ X0 )
      | ( r1_tarski @ sk_C @ ( sk_D @ X0 @ sk_C @ ( k7_lattice3 @ sk_A ) ) )
      | ( v1_xboole_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['365','366','367'])).

thf('369',plain,(
    ! [X0: $i] :
      ( ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ( v1_xboole_0 @ sk_C )
      | ( r1_tarski @ sk_C @ ( sk_D @ X0 @ sk_C @ ( k7_lattice3 @ sk_A ) ) )
      | ~ ( r1_subset_1 @ sk_C @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k7_lattice3 @ sk_A ) ) ) )
      | ~ ( v13_waybel_0 @ X0 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v2_waybel_0 @ X0 @ ( k7_lattice3 @ sk_A ) )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_lattice3 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v2_waybel_1 @ ( k7_lattice3 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['343','368'])).

thf('370',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('371',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('372',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_C )
      | ( r1_tarski @ sk_C @ ( sk_D @ X0 @ sk_C @ ( k7_lattice3 @ sk_A ) ) )
      | ~ ( r1_subset_1 @ sk_C @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k7_lattice3 @ sk_A ) ) ) )
      | ~ ( v13_waybel_0 @ X0 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v2_waybel_0 @ X0 @ ( k7_lattice3 @ sk_A ) )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_lattice3 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v2_waybel_1 @ ( k7_lattice3 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['369','370','371'])).

thf('373',plain,(
    ! [X0: $i] :
      ( ~ ( v2_lattice3 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( v2_waybel_1 @ ( k7_lattice3 @ sk_A ) )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v2_waybel_0 @ X0 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v13_waybel_0 @ X0 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k7_lattice3 @ sk_A ) ) ) )
      | ~ ( r1_subset_1 @ sk_C @ X0 )
      | ( r1_tarski @ sk_C @ ( sk_D @ X0 @ sk_C @ ( k7_lattice3 @ sk_A ) ) )
      | ( v1_xboole_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['342','372'])).

thf('374',plain,(
    v2_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('375',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('376',plain,(
    ! [X0: $i] :
      ( ~ ( v2_waybel_1 @ ( k7_lattice3 @ sk_A ) )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v2_waybel_0 @ X0 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v13_waybel_0 @ X0 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k7_lattice3 @ sk_A ) ) ) )
      | ~ ( r1_subset_1 @ sk_C @ X0 )
      | ( r1_tarski @ sk_C @ ( sk_D @ X0 @ sk_C @ ( k7_lattice3 @ sk_A ) ) )
      | ( v1_xboole_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['373','374','375'])).

thf('377',plain,(
    ! [X0: $i] :
      ( ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( v1_lattice3 @ sk_A )
      | ~ ( v2_lattice3 @ sk_A )
      | ~ ( v2_waybel_1 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ( v1_xboole_0 @ sk_C )
      | ( r1_tarski @ sk_C @ ( sk_D @ X0 @ sk_C @ ( k7_lattice3 @ sk_A ) ) )
      | ~ ( r1_subset_1 @ sk_C @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k7_lattice3 @ sk_A ) ) ) )
      | ~ ( v13_waybel_0 @ X0 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v2_waybel_0 @ X0 @ ( k7_lattice3 @ sk_A ) )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['341','376'])).

thf('378',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('379',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('380',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('381',plain,(
    v1_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('382',plain,(
    v2_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('383',plain,(
    v2_waybel_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('384',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('385',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_C )
      | ( r1_tarski @ sk_C @ ( sk_D @ X0 @ sk_C @ ( k7_lattice3 @ sk_A ) ) )
      | ~ ( r1_subset_1 @ sk_C @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k7_lattice3 @ sk_A ) ) ) )
      | ~ ( v13_waybel_0 @ X0 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v2_waybel_0 @ X0 @ ( k7_lattice3 @ sk_A ) )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['377','378','379','380','381','382','383','384'])).

thf('386',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ~ ( v2_waybel_0 @ sk_B @ ( k7_lattice3 @ sk_A ) )
    | ~ ( v13_waybel_0 @ sk_B @ ( k7_lattice3 @ sk_A ) )
    | ~ ( r1_subset_1 @ sk_C @ sk_B )
    | ( r1_tarski @ sk_C @ ( sk_D @ sk_B @ sk_C @ ( k7_lattice3 @ sk_A ) ) )
    | ( v1_xboole_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['340','385'])).

thf('387',plain,(
    v2_waybel_0 @ sk_B @ ( k7_lattice3 @ sk_A ) ),
    inference(demod,[status(thm)],['69','70','71'])).

thf('388',plain,(
    v13_waybel_0 @ sk_B @ ( k7_lattice3 @ sk_A ) ),
    inference(demod,[status(thm)],['75','76','77'])).

thf('389',plain,(
    r1_subset_1 @ sk_C @ sk_B ),
    inference(clc,[status(thm)],['83','84'])).

thf('390',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( r1_tarski @ sk_C @ ( sk_D @ sk_B @ sk_C @ ( k7_lattice3 @ sk_A ) ) )
    | ( v1_xboole_0 @ sk_C ) ),
    inference(demod,[status(thm)],['386','387','388','389'])).

thf('391',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('392',plain,
    ( ( v1_xboole_0 @ sk_C )
    | ( r1_tarski @ sk_C @ ( sk_D @ sk_B @ sk_C @ ( k7_lattice3 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['390','391'])).

thf('393',plain,(
    ~ ( v1_xboole_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('394',plain,(
    r1_tarski @ sk_C @ ( sk_D @ sk_B @ sk_C @ ( k7_lattice3 @ sk_A ) ) ),
    inference(clc,[status(thm)],['392','393'])).

thf('395',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k7_lattice3 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['2','3','4'])).

thf('396',plain,(
    ! [X6: $i] :
      ( ( v2_waybel_1 @ ( k7_lattice3 @ X6 ) )
      | ~ ( l1_orders_2 @ X6 )
      | ~ ( v2_waybel_1 @ X6 )
      | ~ ( v2_lattice3 @ X6 )
      | ~ ( v1_lattice3 @ X6 )
      | ~ ( v5_orders_2 @ X6 )
      | ~ ( v4_orders_2 @ X6 )
      | ~ ( v3_orders_2 @ X6 ) ) ),
    inference(cnf,[status(esa)],[fc8_yellow_7])).

thf('397',plain,(
    ! [X4: $i] :
      ( ( v1_lattice3 @ ( k7_lattice3 @ X4 ) )
      | ~ ( l1_orders_2 @ X4 )
      | ~ ( v2_lattice3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc5_yellow_7])).

thf('398',plain,(
    ! [X3: $i] :
      ( ( v5_orders_2 @ ( k7_lattice3 @ X3 ) )
      | ~ ( l1_orders_2 @ X3 )
      | ~ ( v5_orders_2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc3_yellow_7])).

thf('399',plain,(
    ! [X5: $i] :
      ( ( v2_lattice3 @ ( k7_lattice3 @ X5 ) )
      | ~ ( l1_orders_2 @ X5 )
      | ~ ( v1_lattice3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[fc6_yellow_7])).

thf('400',plain,(
    ! [X2: $i] :
      ( ( v4_orders_2 @ ( k7_lattice3 @ X2 ) )
      | ~ ( l1_orders_2 @ X2 )
      | ~ ( v4_orders_2 @ X2 ) ) ),
    inference(cnf,[status(esa)],[fc2_yellow_7])).

thf('401',plain,(
    ! [X0: $i] :
      ( ( l1_orders_2 @ ( k7_lattice3 @ X0 ) )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_k7_lattice3])).

thf('402',plain,(
    ! [X1: $i] :
      ( ( v3_orders_2 @ ( k7_lattice3 @ X1 ) )
      | ~ ( l1_orders_2 @ X1 )
      | ~ ( v3_orders_2 @ X1 ) ) ),
    inference(cnf,[status(esa)],[fc1_yellow_7])).

thf('403',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k7_lattice3 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['15','16','17'])).

thf('404',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( v1_xboole_0 @ X15 )
      | ~ ( v1_waybel_0 @ X15 @ X16 )
      | ~ ( v12_waybel_0 @ X15 @ X16 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ( r1_subset_1 @ ( sk_D @ X17 @ X15 @ X16 ) @ X17 )
      | ~ ( r1_subset_1 @ X15 @ X17 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( v13_waybel_0 @ X17 @ X16 )
      | ~ ( v2_waybel_0 @ X17 @ X16 )
      | ( v1_xboole_0 @ X17 )
      | ~ ( l1_orders_2 @ X16 )
      | ~ ( v2_lattice3 @ X16 )
      | ~ ( v1_lattice3 @ X16 )
      | ~ ( v2_waybel_1 @ X16 )
      | ~ ( v5_orders_2 @ X16 )
      | ~ ( v4_orders_2 @ X16 )
      | ~ ( v3_orders_2 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t27_waybel_7])).

thf('405',plain,(
    ! [X0: $i] :
      ( ~ ( v3_orders_2 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v4_orders_2 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v5_orders_2 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v2_waybel_1 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v1_lattice3 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v2_lattice3 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( l1_orders_2 @ ( k7_lattice3 @ sk_A ) )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v2_waybel_0 @ X0 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v13_waybel_0 @ X0 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k7_lattice3 @ sk_A ) ) ) )
      | ~ ( r1_subset_1 @ sk_C @ X0 )
      | ( r1_subset_1 @ ( sk_D @ X0 @ sk_C @ ( k7_lattice3 @ sk_A ) ) @ X0 )
      | ~ ( v12_waybel_0 @ sk_C @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v1_waybel_0 @ sk_C @ ( k7_lattice3 @ sk_A ) )
      | ( v1_xboole_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['403','404'])).

thf('406',plain,(
    v12_waybel_0 @ sk_C @ ( k7_lattice3 @ sk_A ) ),
    inference(demod,[status(thm)],['23','24','25'])).

thf('407',plain,(
    v1_waybel_0 @ sk_C @ ( k7_lattice3 @ sk_A ) ),
    inference(demod,[status(thm)],['29','30','31'])).

thf('408',plain,(
    ! [X0: $i] :
      ( ~ ( v3_orders_2 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v4_orders_2 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v5_orders_2 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v2_waybel_1 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v1_lattice3 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v2_lattice3 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( l1_orders_2 @ ( k7_lattice3 @ sk_A ) )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v2_waybel_0 @ X0 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v13_waybel_0 @ X0 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k7_lattice3 @ sk_A ) ) ) )
      | ~ ( r1_subset_1 @ sk_C @ X0 )
      | ( r1_subset_1 @ ( sk_D @ X0 @ sk_C @ ( k7_lattice3 @ sk_A ) ) @ X0 )
      | ( v1_xboole_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['405','406','407'])).

thf('409',plain,(
    ! [X0: $i] :
      ( ~ ( v3_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ( v1_xboole_0 @ sk_C )
      | ( r1_subset_1 @ ( sk_D @ X0 @ sk_C @ ( k7_lattice3 @ sk_A ) ) @ X0 )
      | ~ ( r1_subset_1 @ sk_C @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k7_lattice3 @ sk_A ) ) ) )
      | ~ ( v13_waybel_0 @ X0 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v2_waybel_0 @ X0 @ ( k7_lattice3 @ sk_A ) )
      | ( v1_xboole_0 @ X0 )
      | ~ ( l1_orders_2 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v2_lattice3 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v1_lattice3 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v2_waybel_1 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v5_orders_2 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v4_orders_2 @ ( k7_lattice3 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['402','408'])).

thf('410',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('411',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('412',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_C )
      | ( r1_subset_1 @ ( sk_D @ X0 @ sk_C @ ( k7_lattice3 @ sk_A ) ) @ X0 )
      | ~ ( r1_subset_1 @ sk_C @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k7_lattice3 @ sk_A ) ) ) )
      | ~ ( v13_waybel_0 @ X0 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v2_waybel_0 @ X0 @ ( k7_lattice3 @ sk_A ) )
      | ( v1_xboole_0 @ X0 )
      | ~ ( l1_orders_2 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v2_lattice3 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v1_lattice3 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v2_waybel_1 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v5_orders_2 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v4_orders_2 @ ( k7_lattice3 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['409','410','411'])).

thf('413',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v5_orders_2 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v2_waybel_1 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v1_lattice3 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v2_lattice3 @ ( k7_lattice3 @ sk_A ) )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v2_waybel_0 @ X0 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v13_waybel_0 @ X0 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k7_lattice3 @ sk_A ) ) ) )
      | ~ ( r1_subset_1 @ sk_C @ X0 )
      | ( r1_subset_1 @ ( sk_D @ X0 @ sk_C @ ( k7_lattice3 @ sk_A ) ) @ X0 )
      | ( v1_xboole_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['401','412'])).

thf('414',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('415',plain,(
    ! [X0: $i] :
      ( ~ ( v4_orders_2 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v5_orders_2 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v2_waybel_1 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v1_lattice3 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v2_lattice3 @ ( k7_lattice3 @ sk_A ) )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v2_waybel_0 @ X0 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v13_waybel_0 @ X0 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k7_lattice3 @ sk_A ) ) ) )
      | ~ ( r1_subset_1 @ sk_C @ X0 )
      | ( r1_subset_1 @ ( sk_D @ X0 @ sk_C @ ( k7_lattice3 @ sk_A ) ) @ X0 )
      | ( v1_xboole_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['413','414'])).

thf('416',plain,(
    ! [X0: $i] :
      ( ~ ( v4_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ( v1_xboole_0 @ sk_C )
      | ( r1_subset_1 @ ( sk_D @ X0 @ sk_C @ ( k7_lattice3 @ sk_A ) ) @ X0 )
      | ~ ( r1_subset_1 @ sk_C @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k7_lattice3 @ sk_A ) ) ) )
      | ~ ( v13_waybel_0 @ X0 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v2_waybel_0 @ X0 @ ( k7_lattice3 @ sk_A ) )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v2_lattice3 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v1_lattice3 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v2_waybel_1 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v5_orders_2 @ ( k7_lattice3 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['400','415'])).

thf('417',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('418',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('419',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_C )
      | ( r1_subset_1 @ ( sk_D @ X0 @ sk_C @ ( k7_lattice3 @ sk_A ) ) @ X0 )
      | ~ ( r1_subset_1 @ sk_C @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k7_lattice3 @ sk_A ) ) ) )
      | ~ ( v13_waybel_0 @ X0 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v2_waybel_0 @ X0 @ ( k7_lattice3 @ sk_A ) )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v2_lattice3 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v1_lattice3 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v2_waybel_1 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v5_orders_2 @ ( k7_lattice3 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['416','417','418'])).

thf('420',plain,(
    ! [X0: $i] :
      ( ~ ( v1_lattice3 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v2_waybel_1 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v1_lattice3 @ ( k7_lattice3 @ sk_A ) )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v2_waybel_0 @ X0 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v13_waybel_0 @ X0 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k7_lattice3 @ sk_A ) ) ) )
      | ~ ( r1_subset_1 @ sk_C @ X0 )
      | ( r1_subset_1 @ ( sk_D @ X0 @ sk_C @ ( k7_lattice3 @ sk_A ) ) @ X0 )
      | ( v1_xboole_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['399','419'])).

thf('421',plain,(
    v1_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('422',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('423',plain,(
    ! [X0: $i] :
      ( ~ ( v5_orders_2 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v2_waybel_1 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v1_lattice3 @ ( k7_lattice3 @ sk_A ) )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v2_waybel_0 @ X0 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v13_waybel_0 @ X0 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k7_lattice3 @ sk_A ) ) ) )
      | ~ ( r1_subset_1 @ sk_C @ X0 )
      | ( r1_subset_1 @ ( sk_D @ X0 @ sk_C @ ( k7_lattice3 @ sk_A ) ) @ X0 )
      | ( v1_xboole_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['420','421','422'])).

thf('424',plain,(
    ! [X0: $i] :
      ( ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ( v1_xboole_0 @ sk_C )
      | ( r1_subset_1 @ ( sk_D @ X0 @ sk_C @ ( k7_lattice3 @ sk_A ) ) @ X0 )
      | ~ ( r1_subset_1 @ sk_C @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k7_lattice3 @ sk_A ) ) ) )
      | ~ ( v13_waybel_0 @ X0 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v2_waybel_0 @ X0 @ ( k7_lattice3 @ sk_A ) )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_lattice3 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v2_waybel_1 @ ( k7_lattice3 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['398','423'])).

thf('425',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('426',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('427',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_C )
      | ( r1_subset_1 @ ( sk_D @ X0 @ sk_C @ ( k7_lattice3 @ sk_A ) ) @ X0 )
      | ~ ( r1_subset_1 @ sk_C @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k7_lattice3 @ sk_A ) ) ) )
      | ~ ( v13_waybel_0 @ X0 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v2_waybel_0 @ X0 @ ( k7_lattice3 @ sk_A ) )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_lattice3 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v2_waybel_1 @ ( k7_lattice3 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['424','425','426'])).

thf('428',plain,(
    ! [X0: $i] :
      ( ~ ( v2_lattice3 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( v2_waybel_1 @ ( k7_lattice3 @ sk_A ) )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v2_waybel_0 @ X0 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v13_waybel_0 @ X0 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k7_lattice3 @ sk_A ) ) ) )
      | ~ ( r1_subset_1 @ sk_C @ X0 )
      | ( r1_subset_1 @ ( sk_D @ X0 @ sk_C @ ( k7_lattice3 @ sk_A ) ) @ X0 )
      | ( v1_xboole_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['397','427'])).

thf('429',plain,(
    v2_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('430',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('431',plain,(
    ! [X0: $i] :
      ( ~ ( v2_waybel_1 @ ( k7_lattice3 @ sk_A ) )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v2_waybel_0 @ X0 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v13_waybel_0 @ X0 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k7_lattice3 @ sk_A ) ) ) )
      | ~ ( r1_subset_1 @ sk_C @ X0 )
      | ( r1_subset_1 @ ( sk_D @ X0 @ sk_C @ ( k7_lattice3 @ sk_A ) ) @ X0 )
      | ( v1_xboole_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['428','429','430'])).

thf('432',plain,(
    ! [X0: $i] :
      ( ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( v1_lattice3 @ sk_A )
      | ~ ( v2_lattice3 @ sk_A )
      | ~ ( v2_waybel_1 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ( v1_xboole_0 @ sk_C )
      | ( r1_subset_1 @ ( sk_D @ X0 @ sk_C @ ( k7_lattice3 @ sk_A ) ) @ X0 )
      | ~ ( r1_subset_1 @ sk_C @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k7_lattice3 @ sk_A ) ) ) )
      | ~ ( v13_waybel_0 @ X0 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v2_waybel_0 @ X0 @ ( k7_lattice3 @ sk_A ) )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['396','431'])).

thf('433',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('434',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('435',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('436',plain,(
    v1_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('437',plain,(
    v2_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('438',plain,(
    v2_waybel_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('439',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('440',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_C )
      | ( r1_subset_1 @ ( sk_D @ X0 @ sk_C @ ( k7_lattice3 @ sk_A ) ) @ X0 )
      | ~ ( r1_subset_1 @ sk_C @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k7_lattice3 @ sk_A ) ) ) )
      | ~ ( v13_waybel_0 @ X0 @ ( k7_lattice3 @ sk_A ) )
      | ~ ( v2_waybel_0 @ X0 @ ( k7_lattice3 @ sk_A ) )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['432','433','434','435','436','437','438','439'])).

thf('441',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ~ ( v2_waybel_0 @ sk_B @ ( k7_lattice3 @ sk_A ) )
    | ~ ( v13_waybel_0 @ sk_B @ ( k7_lattice3 @ sk_A ) )
    | ~ ( r1_subset_1 @ sk_C @ sk_B )
    | ( r1_subset_1 @ ( sk_D @ sk_B @ sk_C @ ( k7_lattice3 @ sk_A ) ) @ sk_B )
    | ( v1_xboole_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['395','440'])).

thf('442',plain,(
    v2_waybel_0 @ sk_B @ ( k7_lattice3 @ sk_A ) ),
    inference(demod,[status(thm)],['69','70','71'])).

thf('443',plain,(
    v13_waybel_0 @ sk_B @ ( k7_lattice3 @ sk_A ) ),
    inference(demod,[status(thm)],['75','76','77'])).

thf('444',plain,(
    r1_subset_1 @ sk_C @ sk_B ),
    inference(clc,[status(thm)],['83','84'])).

thf('445',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( r1_subset_1 @ ( sk_D @ sk_B @ sk_C @ ( k7_lattice3 @ sk_A ) ) @ sk_B )
    | ( v1_xboole_0 @ sk_C ) ),
    inference(demod,[status(thm)],['441','442','443','444'])).

thf('446',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('447',plain,
    ( ( v1_xboole_0 @ sk_C )
    | ( r1_subset_1 @ ( sk_D @ sk_B @ sk_C @ ( k7_lattice3 @ sk_A ) ) @ sk_B ) ),
    inference(clc,[status(thm)],['445','446'])).

thf('448',plain,(
    ~ ( v1_xboole_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('449',plain,(
    r1_subset_1 @ ( sk_D @ sk_B @ sk_C @ ( k7_lattice3 @ sk_A ) ) @ sk_B ),
    inference(clc,[status(thm)],['447','448'])).

thf('450',plain,(
    ! [X7: $i,X8: $i] :
      ( ( v1_xboole_0 @ X7 )
      | ( v1_xboole_0 @ X8 )
      | ( r1_subset_1 @ X8 @ X7 )
      | ~ ( r1_subset_1 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_subset_1])).

thf('451',plain,
    ( ( r1_subset_1 @ sk_B @ ( sk_D @ sk_B @ sk_C @ ( k7_lattice3 @ sk_A ) ) )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ ( sk_D @ sk_B @ sk_C @ ( k7_lattice3 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['449','450'])).

thf('452',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('453',plain,
    ( ( v1_xboole_0 @ ( sk_D @ sk_B @ sk_C @ ( k7_lattice3 @ sk_A ) ) )
    | ( r1_subset_1 @ sk_B @ ( sk_D @ sk_B @ sk_C @ ( k7_lattice3 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['451','452'])).

thf('454',plain,(
    ~ ( v1_xboole_0 @ ( sk_D @ sk_B @ sk_C @ ( k7_lattice3 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['88','89'])).

thf('455',plain,(
    r1_subset_1 @ sk_B @ ( sk_D @ sk_B @ sk_C @ ( k7_lattice3 @ sk_A ) ) ),
    inference(clc,[status(thm)],['453','454'])).

thf('456',plain,
    ( ( v1_xboole_0 @ ( sk_D @ sk_B @ sk_C @ ( k7_lattice3 @ sk_A ) ) )
    | ~ ( v2_waybel_7 @ ( sk_D @ sk_B @ sk_C @ ( k7_lattice3 @ sk_A ) ) @ sk_A ) ),
    inference(demod,[status(thm)],['327','333','339','394','455'])).

thf('457',plain,(
    ~ ( v1_xboole_0 @ ( sk_D @ sk_B @ sk_C @ ( k7_lattice3 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['88','89'])).

thf('458',plain,(
    ~ ( v2_waybel_7 @ ( sk_D @ sk_B @ sk_C @ ( k7_lattice3 @ sk_A ) ) @ sk_A ) ),
    inference(clc,[status(thm)],['456','457'])).

thf('459',plain,(
    v1_xboole_0 @ ( sk_D @ sk_B @ sk_C @ ( k7_lattice3 @ sk_A ) ) ),
    inference(clc,[status(thm)],['319','458'])).

thf('460',plain,(
    $false ),
    inference(demod,[status(thm)],['90','459'])).


%------------------------------------------------------------------------------
