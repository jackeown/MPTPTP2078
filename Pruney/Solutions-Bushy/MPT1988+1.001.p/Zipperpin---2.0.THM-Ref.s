%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT1988+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.nIgmaWVkr3

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:54:39 EST 2020

% Result     : Theorem 0.39s
% Output     : Refutation 0.39s
% Verified   : 
% Statistics : Number of formulae       :  193 (1333 expanded)
%              Number of leaves         :   34 ( 400 expanded)
%              Depth                    :   18
%              Number of atoms          : 1853 (19299 expanded)
%              Number of equality atoms :    5 (   5 expanded)
%              Maximal formula depth    :   17 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v12_waybel_0_type,type,(
    v12_waybel_0: $i > $i > $o )).

thf(k11_lattice3_type,type,(
    k11_lattice3: $i > $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v1_lattice3_type,type,(
    v1_lattice3: $i > $o )).

thf(v1_waybel_7_type,type,(
    v1_waybel_7: $i > $i > $o )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k5_waybel_0_type,type,(
    k5_waybel_0: $i > $i > $i )).

thf(v1_waybel_0_type,type,(
    v1_waybel_0: $i > $i > $o )).

thf(v2_lattice3_type,type,(
    v2_lattice3: $i > $o )).

thf(v5_waybel_6_type,type,(
    v5_waybel_6: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k12_lattice3_type,type,(
    k12_lattice3: $i > $i > $i > $i )).

thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i )).

thf(t37_waybel_7,conjecture,(
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
             => ( v1_waybel_7 @ ( k5_waybel_0 @ A @ B ) @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t37_waybel_7])).

thf('0',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k5_waybel_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_orders_2 @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) )
     => ( m1_subset_1 @ ( k5_waybel_0 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('1',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( l1_orders_2 @ X9 )
      | ( v2_struct_0 @ X9 )
      | ~ ( m1_subset_1 @ X10 @ ( u1_struct_0 @ X9 ) )
      | ( m1_subset_1 @ ( k5_waybel_0 @ X9 @ X10 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_waybel_0])).

thf('2',plain,
    ( ( m1_subset_1 @ ( k5_waybel_0 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( m1_subset_1 @ ( k5_waybel_0 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('5',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_lattice3,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( ( v2_lattice3 @ A )
       => ~ ( v2_struct_0 @ A ) ) ) )).

thf('6',plain,(
    ! [X0: $i] :
      ( ~ ( v2_lattice3 @ X0 )
      | ~ ( v2_struct_0 @ X0 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(cnf,[status(esa)],[cc2_lattice3])).

thf('7',plain,
    ( ~ ( v2_struct_0 @ sk_A )
    | ~ ( v2_lattice3 @ sk_A ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    v2_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    m1_subset_1 @ ( k5_waybel_0 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['4','9'])).

thf(d1_waybel_7,axiom,(
    ! [A: $i] :
      ( ( ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( v2_lattice3 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v1_xboole_0 @ B )
            & ( v1_waybel_0 @ B @ A )
            & ( v12_waybel_0 @ B @ A )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
         => ( ( v1_waybel_7 @ B @ A )
          <=> ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
               => ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                   => ~ ( ( r2_hidden @ ( k12_lattice3 @ A @ C @ D ) @ B )
                        & ~ ( r2_hidden @ C @ B )
                        & ~ ( r2_hidden @ D @ B ) ) ) ) ) ) ) )).

thf('11',plain,(
    ! [X1: $i,X2: $i] :
      ( ( v1_xboole_0 @ X1 )
      | ~ ( v1_waybel_0 @ X1 @ X2 )
      | ~ ( v12_waybel_0 @ X1 @ X2 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X2 ) ) )
      | ( m1_subset_1 @ ( sk_C @ X1 @ X2 ) @ ( u1_struct_0 @ X2 ) )
      | ( v1_waybel_7 @ X1 @ X2 )
      | ~ ( l1_orders_2 @ X2 )
      | ~ ( v2_lattice3 @ X2 )
      | ~ ( v5_orders_2 @ X2 )
      | ~ ( v4_orders_2 @ X2 )
      | ~ ( v3_orders_2 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_waybel_7])).

thf('12',plain,
    ( ~ ( v3_orders_2 @ sk_A )
    | ~ ( v4_orders_2 @ sk_A )
    | ~ ( v5_orders_2 @ sk_A )
    | ~ ( v2_lattice3 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A )
    | ( v1_waybel_7 @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_A )
    | ( m1_subset_1 @ ( sk_C @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v12_waybel_0 @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_A )
    | ~ ( v1_waybel_0 @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_A )
    | ( v1_xboole_0 @ ( k5_waybel_0 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    v2_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ( v1_waybel_7 @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_A )
    | ( m1_subset_1 @ ( sk_C @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v12_waybel_0 @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_A )
    | ~ ( v1_waybel_0 @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_A )
    | ( v1_xboole_0 @ ( k5_waybel_0 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['12','13','14','15','16','17'])).

thf('19',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc12_waybel_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v4_orders_2 @ A )
        & ( l1_orders_2 @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) )
     => ( v12_waybel_0 @ ( k5_waybel_0 @ A @ B ) @ A ) ) )).

thf('20',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( l1_orders_2 @ X11 )
      | ~ ( v4_orders_2 @ X11 )
      | ( v2_struct_0 @ X11 )
      | ~ ( m1_subset_1 @ X12 @ ( u1_struct_0 @ X11 ) )
      | ( v12_waybel_0 @ ( k5_waybel_0 @ X11 @ X12 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[fc12_waybel_0])).

thf('21',plain,
    ( ( v12_waybel_0 @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v4_orders_2 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ( v12_waybel_0 @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['21','22','23'])).

thf('25',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('26',plain,(
    v12_waybel_0 @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_A ),
    inference(clc,[status(thm)],['24','25'])).

thf('27',plain,(
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

thf('28',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( l1_orders_2 @ X13 )
      | ~ ( v3_orders_2 @ X13 )
      | ( v2_struct_0 @ X13 )
      | ~ ( m1_subset_1 @ X14 @ ( u1_struct_0 @ X13 ) )
      | ( v1_waybel_0 @ ( k5_waybel_0 @ X13 @ X14 ) @ X13 ) ) ),
    inference(cnf,[status(esa)],[fc8_waybel_0])).

thf('29',plain,
    ( ( v1_waybel_0 @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v3_orders_2 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ( v1_waybel_0 @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['29','30','31'])).

thf('33',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('34',plain,(
    v1_waybel_0 @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_A ),
    inference(clc,[status(thm)],['32','33'])).

thf('35',plain,
    ( ( v1_waybel_7 @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_A )
    | ( m1_subset_1 @ ( sk_C @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( k5_waybel_0 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['18','26','34'])).

thf('36',plain,(
    ~ ( v1_waybel_7 @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ( v1_xboole_0 @ ( k5_waybel_0 @ sk_A @ sk_B ) )
    | ( m1_subset_1 @ ( sk_C @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['35','36'])).

thf('38',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( l1_orders_2 @ X13 )
      | ~ ( v3_orders_2 @ X13 )
      | ( v2_struct_0 @ X13 )
      | ~ ( m1_subset_1 @ X14 @ ( u1_struct_0 @ X13 ) )
      | ~ ( v1_xboole_0 @ ( k5_waybel_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[fc8_waybel_0])).

thf('40',plain,
    ( ~ ( v1_xboole_0 @ ( k5_waybel_0 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v3_orders_2 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ~ ( v1_xboole_0 @ ( k5_waybel_0 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['40','41','42'])).

thf('44',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('45',plain,(
    ~ ( v1_xboole_0 @ ( k5_waybel_0 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['43','44'])).

thf('46',plain,(
    m1_subset_1 @ ( sk_C @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['37','45'])).

thf('47',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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

thf('48',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( u1_struct_0 @ X19 ) )
      | ~ ( r1_orders_2 @ X19 @ X20 @ X18 )
      | ( r2_hidden @ X20 @ ( k5_waybel_0 @ X19 @ X18 ) )
      | ~ ( m1_subset_1 @ X20 @ ( u1_struct_0 @ X19 ) )
      | ~ ( l1_orders_2 @ X19 )
      | ( v2_struct_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t17_waybel_0])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X0 @ ( k5_waybel_0 @ sk_A @ sk_B ) )
      | ~ ( r1_orders_2 @ sk_A @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X0 @ ( k5_waybel_0 @ sk_A @ sk_B ) )
      | ~ ( r1_orders_2 @ sk_A @ X0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,
    ( ~ ( r1_orders_2 @ sk_A @ ( sk_C @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_A ) @ sk_B )
    | ( r2_hidden @ ( sk_C @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_A ) @ ( k5_waybel_0 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['46','51'])).

thf('53',plain,(
    m1_subset_1 @ ( k5_waybel_0 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['4','9'])).

thf('54',plain,(
    ! [X1: $i,X2: $i] :
      ( ( v1_xboole_0 @ X1 )
      | ~ ( v1_waybel_0 @ X1 @ X2 )
      | ~ ( v12_waybel_0 @ X1 @ X2 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X2 ) ) )
      | ~ ( r2_hidden @ ( sk_C @ X1 @ X2 ) @ X1 )
      | ( v1_waybel_7 @ X1 @ X2 )
      | ~ ( l1_orders_2 @ X2 )
      | ~ ( v2_lattice3 @ X2 )
      | ~ ( v5_orders_2 @ X2 )
      | ~ ( v4_orders_2 @ X2 )
      | ~ ( v3_orders_2 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_waybel_7])).

thf('55',plain,
    ( ~ ( v3_orders_2 @ sk_A )
    | ~ ( v4_orders_2 @ sk_A )
    | ~ ( v5_orders_2 @ sk_A )
    | ~ ( v2_lattice3 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A )
    | ( v1_waybel_7 @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_A )
    | ~ ( r2_hidden @ ( sk_C @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_A ) @ ( k5_waybel_0 @ sk_A @ sk_B ) )
    | ~ ( v12_waybel_0 @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_A )
    | ~ ( v1_waybel_0 @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_A )
    | ( v1_xboole_0 @ ( k5_waybel_0 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    v2_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    v12_waybel_0 @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_A ),
    inference(clc,[status(thm)],['24','25'])).

thf('62',plain,(
    v1_waybel_0 @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_A ),
    inference(clc,[status(thm)],['32','33'])).

thf('63',plain,
    ( ( v1_waybel_7 @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_A )
    | ~ ( r2_hidden @ ( sk_C @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_A ) @ ( k5_waybel_0 @ sk_A @ sk_B ) )
    | ( v1_xboole_0 @ ( k5_waybel_0 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['55','56','57','58','59','60','61','62'])).

thf('64',plain,(
    ~ ( v1_waybel_7 @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,
    ( ( v1_xboole_0 @ ( k5_waybel_0 @ sk_A @ sk_B ) )
    | ~ ( r2_hidden @ ( sk_C @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_A ) @ ( k5_waybel_0 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['63','64'])).

thf('66',plain,(
    ~ ( v1_xboole_0 @ ( k5_waybel_0 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['43','44'])).

thf('67',plain,(
    ~ ( r2_hidden @ ( sk_C @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_A ) @ ( k5_waybel_0 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['65','66'])).

thf('68',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( r1_orders_2 @ sk_A @ ( sk_C @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_A ) @ sk_B ) ),
    inference(clc,[status(thm)],['52','67'])).

thf('69',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('70',plain,(
    ~ ( r1_orders_2 @ sk_A @ ( sk_C @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_A ) @ sk_B ) ),
    inference(clc,[status(thm)],['68','69'])).

thf('71',plain,(
    m1_subset_1 @ ( k5_waybel_0 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['4','9'])).

thf('72',plain,(
    ! [X1: $i,X2: $i] :
      ( ( v1_xboole_0 @ X1 )
      | ~ ( v1_waybel_0 @ X1 @ X2 )
      | ~ ( v12_waybel_0 @ X1 @ X2 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X2 ) ) )
      | ( m1_subset_1 @ ( sk_D @ X1 @ X2 ) @ ( u1_struct_0 @ X2 ) )
      | ( v1_waybel_7 @ X1 @ X2 )
      | ~ ( l1_orders_2 @ X2 )
      | ~ ( v2_lattice3 @ X2 )
      | ~ ( v5_orders_2 @ X2 )
      | ~ ( v4_orders_2 @ X2 )
      | ~ ( v3_orders_2 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_waybel_7])).

thf('73',plain,
    ( ~ ( v3_orders_2 @ sk_A )
    | ~ ( v4_orders_2 @ sk_A )
    | ~ ( v5_orders_2 @ sk_A )
    | ~ ( v2_lattice3 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A )
    | ( v1_waybel_7 @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_A )
    | ( m1_subset_1 @ ( sk_D @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v12_waybel_0 @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_A )
    | ~ ( v1_waybel_0 @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_A )
    | ( v1_xboole_0 @ ( k5_waybel_0 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    v2_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    v12_waybel_0 @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_A ),
    inference(clc,[status(thm)],['24','25'])).

thf('80',plain,(
    v1_waybel_0 @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_A ),
    inference(clc,[status(thm)],['32','33'])).

thf('81',plain,
    ( ( v1_waybel_7 @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_A )
    | ( m1_subset_1 @ ( sk_D @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( k5_waybel_0 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['73','74','75','76','77','78','79','80'])).

thf('82',plain,(
    ~ ( v1_waybel_7 @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,
    ( ( v1_xboole_0 @ ( k5_waybel_0 @ sk_A @ sk_B ) )
    | ( m1_subset_1 @ ( sk_D @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['81','82'])).

thf('84',plain,(
    ~ ( v1_xboole_0 @ ( k5_waybel_0 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['43','44'])).

thf('85',plain,(
    m1_subset_1 @ ( sk_D @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['83','84'])).

thf('86',plain,(
    m1_subset_1 @ ( sk_C @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['37','45'])).

thf(redefinition_k12_lattice3,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v5_orders_2 @ A )
        & ( v2_lattice3 @ A )
        & ( l1_orders_2 @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
        & ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) )
     => ( ( k12_lattice3 @ A @ B @ C )
        = ( k11_lattice3 @ A @ B @ C ) ) ) )).

thf('87',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( u1_struct_0 @ X16 ) )
      | ~ ( l1_orders_2 @ X16 )
      | ~ ( v2_lattice3 @ X16 )
      | ~ ( v5_orders_2 @ X16 )
      | ~ ( m1_subset_1 @ X17 @ ( u1_struct_0 @ X16 ) )
      | ( ( k12_lattice3 @ X16 @ X15 @ X17 )
        = ( k11_lattice3 @ X16 @ X15 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k12_lattice3])).

thf('88',plain,(
    ! [X0: $i] :
      ( ( ( k12_lattice3 @ sk_A @ ( sk_C @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_A ) @ X0 )
        = ( k11_lattice3 @ sk_A @ ( sk_C @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_A ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( v2_lattice3 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    v2_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    ! [X0: $i] :
      ( ( ( k12_lattice3 @ sk_A @ ( sk_C @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_A ) @ X0 )
        = ( k11_lattice3 @ sk_A @ ( sk_C @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_A ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['88','89','90','91'])).

thf('93',plain,
    ( ( k12_lattice3 @ sk_A @ ( sk_C @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_A ) @ ( sk_D @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_A ) )
    = ( k11_lattice3 @ sk_A @ ( sk_C @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_A ) @ ( sk_D @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['85','92'])).

thf('94',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d6_waybel_6,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ( ( v5_waybel_6 @ B @ A )
          <=> ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
               => ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                   => ~ ( ( r1_orders_2 @ A @ ( k11_lattice3 @ A @ C @ D ) @ B )
                        & ~ ( r1_orders_2 @ A @ C @ B )
                        & ~ ( r1_orders_2 @ A @ D @ B ) ) ) ) ) ) ) )).

thf('95',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X5 @ ( u1_struct_0 @ X6 ) )
      | ~ ( v5_waybel_6 @ X5 @ X6 )
      | ~ ( m1_subset_1 @ X7 @ ( u1_struct_0 @ X6 ) )
      | ~ ( r1_orders_2 @ X6 @ ( k11_lattice3 @ X6 @ X8 @ X7 ) @ X5 )
      | ( r1_orders_2 @ X6 @ X7 @ X5 )
      | ( r1_orders_2 @ X6 @ X8 @ X5 )
      | ~ ( m1_subset_1 @ X8 @ ( u1_struct_0 @ X6 ) )
      | ~ ( l1_orders_2 @ X6 )
      | ( v2_struct_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d6_waybel_6])).

thf('96',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ X0 @ sk_B )
      | ( r1_orders_2 @ sk_A @ X1 @ sk_B )
      | ~ ( r1_orders_2 @ sk_A @ ( k11_lattice3 @ sk_A @ X0 @ X1 ) @ sk_B )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v5_waybel_6 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
    v5_waybel_6 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ X0 @ sk_B )
      | ( r1_orders_2 @ sk_A @ X1 @ sk_B )
      | ~ ( r1_orders_2 @ sk_A @ ( k11_lattice3 @ sk_A @ X0 @ X1 ) @ sk_B )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['96','97','98'])).

thf('100',plain,
    ( ~ ( r1_orders_2 @ sk_A @ ( k12_lattice3 @ sk_A @ ( sk_C @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_A ) @ ( sk_D @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_A ) ) @ sk_B )
    | ~ ( m1_subset_1 @ ( sk_D @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( r1_orders_2 @ sk_A @ ( sk_D @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_A ) @ sk_B )
    | ( r1_orders_2 @ sk_A @ ( sk_C @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_A ) @ sk_B )
    | ~ ( m1_subset_1 @ ( sk_C @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['93','99'])).

thf('101',plain,(
    m1_subset_1 @ ( k5_waybel_0 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['4','9'])).

thf('102',plain,(
    ! [X1: $i,X2: $i] :
      ( ( v1_xboole_0 @ X1 )
      | ~ ( v1_waybel_0 @ X1 @ X2 )
      | ~ ( v12_waybel_0 @ X1 @ X2 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X2 ) ) )
      | ( r2_hidden @ ( k12_lattice3 @ X2 @ ( sk_C @ X1 @ X2 ) @ ( sk_D @ X1 @ X2 ) ) @ X1 )
      | ( v1_waybel_7 @ X1 @ X2 )
      | ~ ( l1_orders_2 @ X2 )
      | ~ ( v2_lattice3 @ X2 )
      | ~ ( v5_orders_2 @ X2 )
      | ~ ( v4_orders_2 @ X2 )
      | ~ ( v3_orders_2 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_waybel_7])).

thf('103',plain,
    ( ~ ( v3_orders_2 @ sk_A )
    | ~ ( v4_orders_2 @ sk_A )
    | ~ ( v5_orders_2 @ sk_A )
    | ~ ( v2_lattice3 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A )
    | ( v1_waybel_7 @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_A )
    | ( r2_hidden @ ( k12_lattice3 @ sk_A @ ( sk_C @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_A ) @ ( sk_D @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_A ) ) @ ( k5_waybel_0 @ sk_A @ sk_B ) )
    | ~ ( v12_waybel_0 @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_A )
    | ~ ( v1_waybel_0 @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_A )
    | ( v1_xboole_0 @ ( k5_waybel_0 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,(
    v2_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,(
    v12_waybel_0 @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_A ),
    inference(clc,[status(thm)],['24','25'])).

thf('110',plain,(
    v1_waybel_0 @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_A ),
    inference(clc,[status(thm)],['32','33'])).

thf('111',plain,
    ( ( v1_waybel_7 @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_A )
    | ( r2_hidden @ ( k12_lattice3 @ sk_A @ ( sk_C @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_A ) @ ( sk_D @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_A ) ) @ ( k5_waybel_0 @ sk_A @ sk_B ) )
    | ( v1_xboole_0 @ ( k5_waybel_0 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['103','104','105','106','107','108','109','110'])).

thf('112',plain,(
    ~ ( v1_waybel_7 @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,
    ( ( v1_xboole_0 @ ( k5_waybel_0 @ sk_A @ sk_B ) )
    | ( r2_hidden @ ( k12_lattice3 @ sk_A @ ( sk_C @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_A ) @ ( sk_D @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_A ) ) @ ( k5_waybel_0 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['111','112'])).

thf('114',plain,(
    ~ ( v1_xboole_0 @ ( k5_waybel_0 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['43','44'])).

thf('115',plain,(
    r2_hidden @ ( k12_lattice3 @ sk_A @ ( sk_C @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_A ) @ ( sk_D @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_A ) ) @ ( k5_waybel_0 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['113','114'])).

thf('116',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( u1_struct_0 @ X19 ) )
      | ~ ( r2_hidden @ X20 @ ( k5_waybel_0 @ X19 @ X18 ) )
      | ( r1_orders_2 @ X19 @ X20 @ X18 )
      | ~ ( m1_subset_1 @ X20 @ ( u1_struct_0 @ X19 ) )
      | ~ ( l1_orders_2 @ X19 )
      | ( v2_struct_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t17_waybel_0])).

thf('118',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ X0 @ sk_B )
      | ~ ( r2_hidden @ X0 @ ( k5_waybel_0 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['116','117'])).

thf('119',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ X0 @ sk_B )
      | ~ ( r2_hidden @ X0 @ ( k5_waybel_0 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['118','119'])).

thf('121',plain,
    ( ( r1_orders_2 @ sk_A @ ( k12_lattice3 @ sk_A @ ( sk_C @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_A ) @ ( sk_D @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_A ) ) @ sk_B )
    | ~ ( m1_subset_1 @ ( k12_lattice3 @ sk_A @ ( sk_C @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_A ) @ ( sk_D @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['115','120'])).

thf('122',plain,(
    r2_hidden @ ( k12_lattice3 @ sk_A @ ( sk_C @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_A ) @ ( sk_D @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_A ) ) @ ( k5_waybel_0 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['113','114'])).

thf('123',plain,(
    m1_subset_1 @ ( k5_waybel_0 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['4','9'])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('124',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( r2_hidden @ X21 @ X22 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ X23 ) )
      | ( m1_subset_1 @ X21 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('125',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( k5_waybel_0 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['123','124'])).

thf('126',plain,(
    m1_subset_1 @ ( k12_lattice3 @ sk_A @ ( sk_C @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_A ) @ ( sk_D @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['122','125'])).

thf('127',plain,
    ( ( r1_orders_2 @ sk_A @ ( k12_lattice3 @ sk_A @ ( sk_C @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_A ) @ ( sk_D @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_A ) ) @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['121','126'])).

thf('128',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('129',plain,(
    r1_orders_2 @ sk_A @ ( k12_lattice3 @ sk_A @ ( sk_C @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_A ) @ ( sk_D @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_A ) ) @ sk_B ),
    inference(clc,[status(thm)],['127','128'])).

thf('130',plain,(
    m1_subset_1 @ ( sk_D @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['83','84'])).

thf('131',plain,(
    m1_subset_1 @ ( sk_C @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['37','45'])).

thf('132',plain,
    ( ( r1_orders_2 @ sk_A @ ( sk_D @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_A ) @ sk_B )
    | ( r1_orders_2 @ sk_A @ ( sk_C @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_A ) @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['100','129','130','131'])).

thf('133',plain,(
    m1_subset_1 @ ( sk_D @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['83','84'])).

thf('134',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X0 @ ( k5_waybel_0 @ sk_A @ sk_B ) )
      | ~ ( r1_orders_2 @ sk_A @ X0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('135',plain,
    ( ~ ( r1_orders_2 @ sk_A @ ( sk_D @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_A ) @ sk_B )
    | ( r2_hidden @ ( sk_D @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_A ) @ ( k5_waybel_0 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['133','134'])).

thf('136',plain,(
    m1_subset_1 @ ( k5_waybel_0 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['4','9'])).

thf('137',plain,(
    ! [X1: $i,X2: $i] :
      ( ( v1_xboole_0 @ X1 )
      | ~ ( v1_waybel_0 @ X1 @ X2 )
      | ~ ( v12_waybel_0 @ X1 @ X2 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X2 ) ) )
      | ~ ( r2_hidden @ ( sk_D @ X1 @ X2 ) @ X1 )
      | ( v1_waybel_7 @ X1 @ X2 )
      | ~ ( l1_orders_2 @ X2 )
      | ~ ( v2_lattice3 @ X2 )
      | ~ ( v5_orders_2 @ X2 )
      | ~ ( v4_orders_2 @ X2 )
      | ~ ( v3_orders_2 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_waybel_7])).

thf('138',plain,
    ( ~ ( v3_orders_2 @ sk_A )
    | ~ ( v4_orders_2 @ sk_A )
    | ~ ( v5_orders_2 @ sk_A )
    | ~ ( v2_lattice3 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A )
    | ( v1_waybel_7 @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_A )
    | ~ ( r2_hidden @ ( sk_D @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_A ) @ ( k5_waybel_0 @ sk_A @ sk_B ) )
    | ~ ( v12_waybel_0 @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_A )
    | ~ ( v1_waybel_0 @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_A )
    | ( v1_xboole_0 @ ( k5_waybel_0 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['136','137'])).

thf('139',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('140',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('141',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('142',plain,(
    v2_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('143',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('144',plain,(
    v12_waybel_0 @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_A ),
    inference(clc,[status(thm)],['24','25'])).

thf('145',plain,(
    v1_waybel_0 @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_A ),
    inference(clc,[status(thm)],['32','33'])).

thf('146',plain,
    ( ( v1_waybel_7 @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_A )
    | ~ ( r2_hidden @ ( sk_D @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_A ) @ ( k5_waybel_0 @ sk_A @ sk_B ) )
    | ( v1_xboole_0 @ ( k5_waybel_0 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['138','139','140','141','142','143','144','145'])).

thf('147',plain,(
    ~ ( v1_waybel_7 @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('148',plain,
    ( ( v1_xboole_0 @ ( k5_waybel_0 @ sk_A @ sk_B ) )
    | ~ ( r2_hidden @ ( sk_D @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_A ) @ ( k5_waybel_0 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['146','147'])).

thf('149',plain,(
    ~ ( v1_xboole_0 @ ( k5_waybel_0 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['43','44'])).

thf('150',plain,(
    ~ ( r2_hidden @ ( sk_D @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_A ) @ ( k5_waybel_0 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['148','149'])).

thf('151',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( r1_orders_2 @ sk_A @ ( sk_D @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_A ) @ sk_B ) ),
    inference(clc,[status(thm)],['135','150'])).

thf('152',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('153',plain,(
    ~ ( r1_orders_2 @ sk_A @ ( sk_D @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_A ) @ sk_B ) ),
    inference(clc,[status(thm)],['151','152'])).

thf('154',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r1_orders_2 @ sk_A @ ( sk_C @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_A ) @ sk_B ) ),
    inference(clc,[status(thm)],['132','153'])).

thf('155',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('156',plain,(
    r1_orders_2 @ sk_A @ ( sk_C @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_A ) @ sk_B ),
    inference(clc,[status(thm)],['154','155'])).

thf('157',plain,(
    $false ),
    inference(demod,[status(thm)],['70','156'])).


%------------------------------------------------------------------------------
