%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.TiwDcJCHAp

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:14:27 EST 2020

% Result     : Theorem 6.03s
% Output     : Refutation 6.03s
% Verified   : 
% Statistics : Number of formulae       :  170 ( 701 expanded)
%              Number of leaves         :   38 ( 215 expanded)
%              Depth                    :   22
%              Number of atoms          : 1351 (12132 expanded)
%              Number of equality atoms :   16 (  17 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_D_type,type,(
    sk_D: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(m1_connsp_2_type,type,(
    m1_connsp_2: $i > $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k9_yellow_6_type,type,(
    k9_yellow_6: $i > $i > $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(t23_waybel_9,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ ( k9_yellow_6 @ A @ B ) ) )
             => ! [D: $i] :
                  ( ( m1_subset_1 @ D @ ( u1_struct_0 @ ( k9_yellow_6 @ A @ B ) ) )
                 => ( m1_subset_1 @ ( k2_xboole_0 @ C @ D ) @ ( u1_struct_0 @ ( k9_yellow_6 @ A @ B ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ ( k9_yellow_6 @ A @ B ) ) )
               => ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( u1_struct_0 @ ( k9_yellow_6 @ A @ B ) ) )
                   => ( m1_subset_1 @ ( k2_xboole_0 @ C @ D ) @ ( u1_struct_0 @ ( k9_yellow_6 @ A @ B ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t23_waybel_9])).

thf('0',plain,(
    ~ ( m1_subset_1 @ ( k2_xboole_0 @ sk_C @ sk_D ) @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t21_waybel_9,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ ( k9_yellow_6 @ A @ B ) ) )
             => ( m1_connsp_2 @ C @ A @ B ) ) ) ) )).

thf('3',plain,(
    ! [X47: $i,X48: $i,X49: $i] :
      ( ~ ( m1_subset_1 @ X47 @ ( u1_struct_0 @ X48 ) )
      | ( m1_connsp_2 @ X49 @ X48 @ X47 )
      | ~ ( m1_subset_1 @ X49 @ ( u1_struct_0 @ ( k9_yellow_6 @ X48 @ X47 ) ) )
      | ~ ( l1_pre_topc @ X48 )
      | ~ ( v2_pre_topc @ X48 )
      | ( v2_struct_0 @ X48 ) ) ),
    inference(cnf,[status(esa)],[t21_waybel_9])).

thf('4',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( m1_connsp_2 @ sk_C @ sk_A @ sk_B_1 )
    | ~ ( m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_connsp_2 @ sk_C @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['4','5','6','7'])).

thf('9',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    m1_connsp_2 @ sk_C @ sk_A @ sk_B_1 ),
    inference(clc,[status(thm)],['8','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_connsp_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) )
     => ! [C: $i] :
          ( ( m1_connsp_2 @ C @ A @ B )
         => ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('12',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ~ ( l1_pre_topc @ X38 )
      | ~ ( v2_pre_topc @ X38 )
      | ( v2_struct_0 @ X38 )
      | ~ ( m1_subset_1 @ X39 @ ( u1_struct_0 @ X38 ) )
      | ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X38 ) ) )
      | ~ ( m1_connsp_2 @ X40 @ X38 @ X39 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_connsp_2])).

thf('13',plain,(
    ! [X0: $i] :
      ( ~ ( m1_connsp_2 @ X0 @ sk_A @ sk_B_1 )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( m1_connsp_2 @ X0 @ sk_A @ sk_B_1 )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['13','14','15'])).

thf('17',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( m1_connsp_2 @ X0 @ sk_A @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['16','17'])).

thf('19',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['10','18'])).

thf(t6_connsp_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ( ( m1_connsp_2 @ B @ A @ C )
               => ( r2_hidden @ C @ B ) ) ) ) ) )).

thf('20',plain,(
    ! [X41: $i,X42: $i,X43: $i] :
      ( ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X42 ) ) )
      | ~ ( m1_connsp_2 @ X41 @ X42 @ X43 )
      | ( r2_hidden @ X43 @ X41 )
      | ~ ( m1_subset_1 @ X43 @ ( u1_struct_0 @ X42 ) )
      | ~ ( l1_pre_topc @ X42 )
      | ~ ( v2_pre_topc @ X42 )
      | ( v2_struct_0 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t6_connsp_2])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X0 @ sk_C )
      | ~ ( m1_connsp_2 @ sk_C @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X0 @ sk_C )
      | ~ ( m1_connsp_2 @ sk_C @ sk_A @ X0 ) ) ),
    inference(demod,[status(thm)],['21','22','23'])).

thf('25',plain,
    ( ~ ( m1_connsp_2 @ sk_C @ sk_A @ sk_B_1 )
    | ( r2_hidden @ sk_B_1 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['1','24'])).

thf('26',plain,(
    m1_connsp_2 @ sk_C @ sk_A @ sk_B_1 ),
    inference(clc,[status(thm)],['8','9'])).

thf('27',plain,
    ( ( r2_hidden @ sk_B_1 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    r2_hidden @ sk_B_1 @ sk_C ),
    inference(clc,[status(thm)],['27','28'])).

thf(l22_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
        = B ) ) )).

thf('30',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k2_xboole_0 @ ( k1_tarski @ X15 ) @ X14 )
        = X14 )
      | ~ ( r2_hidden @ X15 @ X14 ) ) ),
    inference(cnf,[status(esa)],[l22_zfmisc_1])).

thf('31',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_B_1 ) @ sk_C )
    = sk_C ),
    inference('sup-',[status(thm)],['29','30'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('32',plain,(
    ! [X11: $i,X12: $i] :
      ( r1_tarski @ X11 @ ( k2_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf(t11_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ C ) ) )).

thf('33',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( r1_tarski @ X6 @ X7 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X6 @ X8 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t11_xboole_1])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ X2 @ ( k2_xboole_0 @ ( k2_xboole_0 @ X2 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('35',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k2_xboole_0 @ X10 @ X9 )
        = X9 )
      | ~ ( r1_tarski @ X10 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X2 @ ( k2_xboole_0 @ ( k2_xboole_0 @ X2 @ X1 ) @ X0 ) )
      = ( k2_xboole_0 @ ( k2_xboole_0 @ X2 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X11: $i,X12: $i] :
      ( r1_tarski @ X11 @ ( k2_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('38',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k2_xboole_0 @ X10 @ X9 )
        = X9 )
      | ~ ( r1_tarski @ X10 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('40',plain,(
    ! [X13: $i] :
      ( ( k2_tarski @ X13 @ X13 )
      = ( k1_tarski @ X13 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t47_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) @ C )
     => ( r2_hidden @ A @ C ) ) )).

thf('41',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( r2_hidden @ X18 @ X19 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ ( k2_tarski @ X18 @ X20 ) @ X19 ) @ X19 ) ) ),
    inference(cnf,[status(esa)],[t47_zfmisc_1])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) @ X1 )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ X0 ) @ ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ X0 ) )
      | ( r2_hidden @ X1 @ ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['39','42'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('44',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ( X3 != X4 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('45',plain,(
    ! [X4: $i] :
      ( r1_tarski @ X4 @ X4 ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X1 @ ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['43','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r2_hidden @ X2 @ ( k2_xboole_0 @ ( k2_xboole_0 @ ( k1_tarski @ X2 ) @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['36','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( r2_hidden @ sk_B_1 @ ( k2_xboole_0 @ sk_C @ X0 ) ) ),
    inference('sup+',[status(thm)],['31','47'])).

thf('49',plain,(
    m1_subset_1 @ sk_D @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    ! [X47: $i,X48: $i,X49: $i] :
      ( ~ ( m1_subset_1 @ X47 @ ( u1_struct_0 @ X48 ) )
      | ( m1_connsp_2 @ X49 @ X48 @ X47 )
      | ~ ( m1_subset_1 @ X49 @ ( u1_struct_0 @ ( k9_yellow_6 @ X48 @ X47 ) ) )
      | ~ ( l1_pre_topc @ X48 )
      | ~ ( v2_pre_topc @ X48 )
      | ( v2_struct_0 @ X48 ) ) ),
    inference(cnf,[status(esa)],[t21_waybel_9])).

thf('51',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( m1_connsp_2 @ sk_D @ sk_A @ sk_B_1 )
    | ~ ( m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_connsp_2 @ sk_D @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['51','52','53','54'])).

thf('56',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    m1_connsp_2 @ sk_D @ sk_A @ sk_B_1 ),
    inference(clc,[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( m1_connsp_2 @ X0 @ sk_A @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['16','17'])).

thf('59',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['10','18'])).

thf(dt_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( m1_subset_1 @ ( k4_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('61',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ X25 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ X25 ) )
      | ( m1_subset_1 @ ( k4_subset_1 @ X25 @ X24 @ X26 ) @ ( k1_zfmisc_1 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k4_subset_1])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    m1_subset_1 @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['59','62'])).

thf('64',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('65',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['10','18'])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('66',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ X28 ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ X28 ) )
      | ( ( k4_subset_1 @ X28 @ X27 @ X29 )
        = ( k2_xboole_0 @ X27 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ X0 )
        = ( k2_xboole_0 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,
    ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ sk_D )
    = ( k2_xboole_0 @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['64','67'])).

thf('69',plain,(
    m1_subset_1 @ ( k2_xboole_0 @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['63','68'])).

thf(t39_yellow_6,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( r2_hidden @ C @ ( u1_struct_0 @ ( k9_yellow_6 @ A @ B ) ) )
              <=> ( ( r2_hidden @ B @ C )
                  & ( v3_pre_topc @ C @ A ) ) ) ) ) ) )).

thf('70',plain,(
    ! [X44: $i,X45: $i,X46: $i] :
      ( ~ ( m1_subset_1 @ X44 @ ( u1_struct_0 @ X45 ) )
      | ~ ( r2_hidden @ X44 @ X46 )
      | ~ ( v3_pre_topc @ X46 @ X45 )
      | ( r2_hidden @ X46 @ ( u1_struct_0 @ ( k9_yellow_6 @ X45 @ X44 ) ) )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X45 ) ) )
      | ~ ( l1_pre_topc @ X45 )
      | ~ ( v2_pre_topc @ X45 )
      | ( v2_struct_0 @ X45 ) ) ),
    inference(cnf,[status(esa)],[t39_yellow_6])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( r2_hidden @ ( k2_xboole_0 @ sk_C @ sk_D ) @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ X0 ) ) )
      | ~ ( v3_pre_topc @ ( k2_xboole_0 @ sk_C @ sk_D ) @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( k2_xboole_0 @ sk_C @ sk_D ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('75',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['10','18'])).

thf(fc7_tops_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( v3_pre_topc @ B @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
        & ( v3_pre_topc @ C @ A )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v3_pre_topc @ ( k2_xboole_0 @ B @ C ) @ A ) ) )).

thf('76',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X36 ) ) )
      | ~ ( v3_pre_topc @ X35 @ X36 )
      | ~ ( l1_pre_topc @ X36 )
      | ~ ( v2_pre_topc @ X36 )
      | ~ ( v3_pre_topc @ X37 @ X36 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X36 ) ) )
      | ( v3_pre_topc @ ( k2_xboole_0 @ X35 @ X37 ) @ X36 ) ) ),
    inference(cnf,[status(esa)],[fc7_tops_1])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( v3_pre_topc @ ( k2_xboole_0 @ sk_C @ X0 ) @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v3_pre_topc @ X0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v3_pre_topc @ sk_C @ sk_A ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    ! [X0: $i] :
      ( ( v3_pre_topc @ ( k2_xboole_0 @ sk_C @ X0 ) @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v3_pre_topc @ X0 @ sk_A )
      | ~ ( v3_pre_topc @ sk_C @ sk_A ) ) ),
    inference(demod,[status(thm)],['77','78','79'])).

thf('81',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('82',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X21 @ X22 )
      | ( r2_hidden @ X21 @ X22 )
      | ( v1_xboole_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('83',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B_1 ) ) )
    | ( r2_hidden @ sk_C @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X44: $i,X45: $i,X46: $i] :
      ( ~ ( m1_subset_1 @ X44 @ ( u1_struct_0 @ X45 ) )
      | ~ ( r2_hidden @ X46 @ ( u1_struct_0 @ ( k9_yellow_6 @ X45 @ X44 ) ) )
      | ( v3_pre_topc @ X46 @ X45 )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X45 ) ) )
      | ~ ( l1_pre_topc @ X45 )
      | ~ ( v2_pre_topc @ X45 )
      | ( v2_struct_0 @ X45 ) ) ),
    inference(cnf,[status(esa)],[t39_yellow_6])).

thf('85',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B_1 ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v3_pre_topc @ sk_C @ sk_A )
    | ~ ( m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B_1 ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v3_pre_topc @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['85','86','87','88'])).

thf('90',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['10','18'])).

thf('91',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B_1 ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v3_pre_topc @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['89','90'])).

thf('92',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,
    ( ( v3_pre_topc @ sk_C @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B_1 ) ) ) ),
    inference(clc,[status(thm)],['91','92'])).

thf('94',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X23 @ X22 )
      | ( v1_xboole_0 @ X23 )
      | ~ ( v1_xboole_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('96',plain,
    ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B_1 ) ) )
    | ( v1_xboole_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,
    ( ( v3_pre_topc @ sk_C @ sk_A )
    | ( v1_xboole_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['93','96'])).

thf('98',plain,(
    r2_hidden @ sk_B_1 @ sk_C ),
    inference(clc,[status(thm)],['27','28'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('99',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('100',plain,(
    ~ ( v1_xboole_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,(
    v3_pre_topc @ sk_C @ sk_A ),
    inference(clc,[status(thm)],['97','100'])).

thf('102',plain,(
    ! [X0: $i] :
      ( ( v3_pre_topc @ ( k2_xboole_0 @ sk_C @ X0 ) @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v3_pre_topc @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['80','101'])).

thf('103',plain,
    ( ~ ( v3_pre_topc @ sk_D @ sk_A )
    | ( v3_pre_topc @ ( k2_xboole_0 @ sk_C @ sk_D ) @ sk_A ) ),
    inference('sup-',[status(thm)],['74','102'])).

thf('104',plain,(
    m1_subset_1 @ sk_D @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X21 @ X22 )
      | ( r2_hidden @ X21 @ X22 )
      | ( v1_xboole_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('106',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B_1 ) ) )
    | ( r2_hidden @ sk_D @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['104','105'])).

thf('107',plain,(
    ! [X44: $i,X45: $i,X46: $i] :
      ( ~ ( m1_subset_1 @ X44 @ ( u1_struct_0 @ X45 ) )
      | ~ ( r2_hidden @ X46 @ ( u1_struct_0 @ ( k9_yellow_6 @ X45 @ X44 ) ) )
      | ( v3_pre_topc @ X46 @ X45 )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X45 ) ) )
      | ~ ( l1_pre_topc @ X45 )
      | ~ ( v2_pre_topc @ X45 )
      | ( v2_struct_0 @ X45 ) ) ),
    inference(cnf,[status(esa)],[t39_yellow_6])).

thf('108',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B_1 ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v3_pre_topc @ sk_D @ sk_A )
    | ~ ( m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf('109',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B_1 ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v3_pre_topc @ sk_D @ sk_A ) ),
    inference(demod,[status(thm)],['108','109','110','111'])).

thf('113',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('114',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B_1 ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v3_pre_topc @ sk_D @ sk_A ) ),
    inference(demod,[status(thm)],['112','113'])).

thf('115',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,
    ( ( v3_pre_topc @ sk_D @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B_1 ) ) ) ),
    inference(clc,[status(thm)],['114','115'])).

thf('117',plain,
    ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B_1 ) ) )
    | ( v1_xboole_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('118',plain,
    ( ( v3_pre_topc @ sk_D @ sk_A )
    | ( v1_xboole_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['116','117'])).

thf('119',plain,(
    ~ ( v1_xboole_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('120',plain,(
    v3_pre_topc @ sk_D @ sk_A ),
    inference(clc,[status(thm)],['118','119'])).

thf('121',plain,(
    v3_pre_topc @ ( k2_xboole_0 @ sk_C @ sk_D ) @ sk_A ),
    inference(demod,[status(thm)],['103','120'])).

thf('122',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ ( k2_xboole_0 @ sk_C @ sk_D ) @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ X0 ) ) )
      | ~ ( r2_hidden @ X0 @ ( k2_xboole_0 @ sk_C @ sk_D ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['71','72','73','121'])).

thf('123',plain,
    ( ~ ( m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( k2_xboole_0 @ sk_C @ sk_D ) @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B_1 ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['48','122'])).

thf('124',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('125',plain,
    ( ( r2_hidden @ ( k2_xboole_0 @ sk_C @ sk_D ) @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B_1 ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['123','124'])).

thf('126',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,(
    r2_hidden @ ( k2_xboole_0 @ sk_C @ sk_D ) @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['125','126'])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('128',plain,(
    ! [X30: $i,X31: $i] :
      ( ( m1_subset_1 @ X30 @ X31 )
      | ~ ( r2_hidden @ X30 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('129',plain,(
    m1_subset_1 @ ( k2_xboole_0 @ sk_C @ sk_D ) @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['127','128'])).

thf('130',plain,(
    $false ),
    inference(demod,[status(thm)],['0','129'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.TiwDcJCHAp
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:14:27 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 6.03/6.24  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 6.03/6.24  % Solved by: fo/fo7.sh
% 6.03/6.24  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 6.03/6.24  % done 10513 iterations in 5.777s
% 6.03/6.24  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 6.03/6.24  % SZS output start Refutation
% 6.03/6.24  thf(sk_D_type, type, sk_D: $i).
% 6.03/6.24  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 6.03/6.24  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 6.03/6.24  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 6.03/6.24  thf(m1_connsp_2_type, type, m1_connsp_2: $i > $i > $i > $o).
% 6.03/6.24  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 6.03/6.24  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 6.03/6.24  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 6.03/6.24  thf(sk_B_1_type, type, sk_B_1: $i).
% 6.03/6.24  thf(sk_C_type, type, sk_C: $i).
% 6.03/6.24  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 6.03/6.24  thf(sk_A_type, type, sk_A: $i).
% 6.03/6.24  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 6.03/6.24  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 6.03/6.24  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 6.03/6.24  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 6.03/6.24  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 6.03/6.24  thf(k9_yellow_6_type, type, k9_yellow_6: $i > $i > $i).
% 6.03/6.24  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 6.03/6.24  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 6.03/6.24  thf(t23_waybel_9, conjecture,
% 6.03/6.24    (![A:$i]:
% 6.03/6.24     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 6.03/6.24       ( ![B:$i]:
% 6.03/6.24         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 6.03/6.24           ( ![C:$i]:
% 6.03/6.24             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ ( k9_yellow_6 @ A @ B ) ) ) =>
% 6.03/6.24               ( ![D:$i]:
% 6.03/6.24                 ( ( m1_subset_1 @
% 6.03/6.24                     D @ ( u1_struct_0 @ ( k9_yellow_6 @ A @ B ) ) ) =>
% 6.03/6.24                   ( m1_subset_1 @
% 6.03/6.24                     ( k2_xboole_0 @ C @ D ) @ 
% 6.03/6.24                     ( u1_struct_0 @ ( k9_yellow_6 @ A @ B ) ) ) ) ) ) ) ) ) ))).
% 6.03/6.24  thf(zf_stmt_0, negated_conjecture,
% 6.03/6.24    (~( ![A:$i]:
% 6.03/6.24        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 6.03/6.24            ( l1_pre_topc @ A ) ) =>
% 6.03/6.24          ( ![B:$i]:
% 6.03/6.24            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 6.03/6.24              ( ![C:$i]:
% 6.03/6.24                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ ( k9_yellow_6 @ A @ B ) ) ) =>
% 6.03/6.24                  ( ![D:$i]:
% 6.03/6.24                    ( ( m1_subset_1 @
% 6.03/6.24                        D @ ( u1_struct_0 @ ( k9_yellow_6 @ A @ B ) ) ) =>
% 6.03/6.24                      ( m1_subset_1 @
% 6.03/6.24                        ( k2_xboole_0 @ C @ D ) @ 
% 6.03/6.24                        ( u1_struct_0 @ ( k9_yellow_6 @ A @ B ) ) ) ) ) ) ) ) ) ) )),
% 6.03/6.24    inference('cnf.neg', [status(esa)], [t23_waybel_9])).
% 6.03/6.24  thf('0', plain,
% 6.03/6.24      (~ (m1_subset_1 @ (k2_xboole_0 @ sk_C @ sk_D) @ 
% 6.03/6.24          (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B_1)))),
% 6.03/6.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.03/6.24  thf('1', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 6.03/6.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.03/6.24  thf('2', plain,
% 6.03/6.24      ((m1_subset_1 @ sk_C @ (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B_1)))),
% 6.03/6.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.03/6.24  thf(t21_waybel_9, axiom,
% 6.03/6.24    (![A:$i]:
% 6.03/6.24     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 6.03/6.24       ( ![B:$i]:
% 6.03/6.24         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 6.03/6.24           ( ![C:$i]:
% 6.03/6.24             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ ( k9_yellow_6 @ A @ B ) ) ) =>
% 6.03/6.24               ( m1_connsp_2 @ C @ A @ B ) ) ) ) ) ))).
% 6.03/6.24  thf('3', plain,
% 6.03/6.24      (![X47 : $i, X48 : $i, X49 : $i]:
% 6.03/6.24         (~ (m1_subset_1 @ X47 @ (u1_struct_0 @ X48))
% 6.03/6.24          | (m1_connsp_2 @ X49 @ X48 @ X47)
% 6.03/6.24          | ~ (m1_subset_1 @ X49 @ (u1_struct_0 @ (k9_yellow_6 @ X48 @ X47)))
% 6.03/6.24          | ~ (l1_pre_topc @ X48)
% 6.03/6.24          | ~ (v2_pre_topc @ X48)
% 6.03/6.24          | (v2_struct_0 @ X48))),
% 6.03/6.24      inference('cnf', [status(esa)], [t21_waybel_9])).
% 6.03/6.24  thf('4', plain,
% 6.03/6.24      (((v2_struct_0 @ sk_A)
% 6.03/6.24        | ~ (v2_pre_topc @ sk_A)
% 6.03/6.24        | ~ (l1_pre_topc @ sk_A)
% 6.03/6.24        | (m1_connsp_2 @ sk_C @ sk_A @ sk_B_1)
% 6.03/6.24        | ~ (m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)))),
% 6.03/6.24      inference('sup-', [status(thm)], ['2', '3'])).
% 6.03/6.24  thf('5', plain, ((v2_pre_topc @ sk_A)),
% 6.03/6.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.03/6.24  thf('6', plain, ((l1_pre_topc @ sk_A)),
% 6.03/6.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.03/6.24  thf('7', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 6.03/6.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.03/6.24  thf('8', plain,
% 6.03/6.24      (((v2_struct_0 @ sk_A) | (m1_connsp_2 @ sk_C @ sk_A @ sk_B_1))),
% 6.03/6.24      inference('demod', [status(thm)], ['4', '5', '6', '7'])).
% 6.03/6.24  thf('9', plain, (~ (v2_struct_0 @ sk_A)),
% 6.03/6.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.03/6.24  thf('10', plain, ((m1_connsp_2 @ sk_C @ sk_A @ sk_B_1)),
% 6.03/6.24      inference('clc', [status(thm)], ['8', '9'])).
% 6.03/6.24  thf('11', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 6.03/6.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.03/6.24  thf(dt_m1_connsp_2, axiom,
% 6.03/6.24    (![A:$i,B:$i]:
% 6.03/6.24     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 6.03/6.24         ( l1_pre_topc @ A ) & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) =>
% 6.03/6.24       ( ![C:$i]:
% 6.03/6.24         ( ( m1_connsp_2 @ C @ A @ B ) =>
% 6.03/6.24           ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 6.03/6.24  thf('12', plain,
% 6.03/6.24      (![X38 : $i, X39 : $i, X40 : $i]:
% 6.03/6.24         (~ (l1_pre_topc @ X38)
% 6.03/6.24          | ~ (v2_pre_topc @ X38)
% 6.03/6.24          | (v2_struct_0 @ X38)
% 6.03/6.24          | ~ (m1_subset_1 @ X39 @ (u1_struct_0 @ X38))
% 6.03/6.24          | (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (u1_struct_0 @ X38)))
% 6.03/6.24          | ~ (m1_connsp_2 @ X40 @ X38 @ X39))),
% 6.03/6.24      inference('cnf', [status(esa)], [dt_m1_connsp_2])).
% 6.03/6.24  thf('13', plain,
% 6.03/6.24      (![X0 : $i]:
% 6.03/6.24         (~ (m1_connsp_2 @ X0 @ sk_A @ sk_B_1)
% 6.03/6.24          | (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 6.03/6.24          | (v2_struct_0 @ sk_A)
% 6.03/6.24          | ~ (v2_pre_topc @ sk_A)
% 6.03/6.24          | ~ (l1_pre_topc @ sk_A))),
% 6.03/6.24      inference('sup-', [status(thm)], ['11', '12'])).
% 6.03/6.24  thf('14', plain, ((v2_pre_topc @ sk_A)),
% 6.03/6.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.03/6.24  thf('15', plain, ((l1_pre_topc @ sk_A)),
% 6.03/6.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.03/6.24  thf('16', plain,
% 6.03/6.24      (![X0 : $i]:
% 6.03/6.24         (~ (m1_connsp_2 @ X0 @ sk_A @ sk_B_1)
% 6.03/6.24          | (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 6.03/6.24          | (v2_struct_0 @ sk_A))),
% 6.03/6.24      inference('demod', [status(thm)], ['13', '14', '15'])).
% 6.03/6.24  thf('17', plain, (~ (v2_struct_0 @ sk_A)),
% 6.03/6.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.03/6.24  thf('18', plain,
% 6.03/6.24      (![X0 : $i]:
% 6.03/6.24         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 6.03/6.24          | ~ (m1_connsp_2 @ X0 @ sk_A @ sk_B_1))),
% 6.03/6.24      inference('clc', [status(thm)], ['16', '17'])).
% 6.03/6.24  thf('19', plain,
% 6.03/6.24      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 6.03/6.24      inference('sup-', [status(thm)], ['10', '18'])).
% 6.03/6.24  thf(t6_connsp_2, axiom,
% 6.03/6.24    (![A:$i]:
% 6.03/6.24     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 6.03/6.24       ( ![B:$i]:
% 6.03/6.24         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 6.03/6.24           ( ![C:$i]:
% 6.03/6.24             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 6.03/6.24               ( ( m1_connsp_2 @ B @ A @ C ) => ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 6.03/6.24  thf('20', plain,
% 6.03/6.24      (![X41 : $i, X42 : $i, X43 : $i]:
% 6.03/6.24         (~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (u1_struct_0 @ X42)))
% 6.03/6.24          | ~ (m1_connsp_2 @ X41 @ X42 @ X43)
% 6.03/6.24          | (r2_hidden @ X43 @ X41)
% 6.03/6.24          | ~ (m1_subset_1 @ X43 @ (u1_struct_0 @ X42))
% 6.03/6.24          | ~ (l1_pre_topc @ X42)
% 6.03/6.24          | ~ (v2_pre_topc @ X42)
% 6.03/6.24          | (v2_struct_0 @ X42))),
% 6.03/6.24      inference('cnf', [status(esa)], [t6_connsp_2])).
% 6.03/6.24  thf('21', plain,
% 6.03/6.24      (![X0 : $i]:
% 6.03/6.24         ((v2_struct_0 @ sk_A)
% 6.03/6.24          | ~ (v2_pre_topc @ sk_A)
% 6.03/6.24          | ~ (l1_pre_topc @ sk_A)
% 6.03/6.24          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 6.03/6.24          | (r2_hidden @ X0 @ sk_C)
% 6.03/6.24          | ~ (m1_connsp_2 @ sk_C @ sk_A @ X0))),
% 6.03/6.24      inference('sup-', [status(thm)], ['19', '20'])).
% 6.03/6.24  thf('22', plain, ((v2_pre_topc @ sk_A)),
% 6.03/6.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.03/6.24  thf('23', plain, ((l1_pre_topc @ sk_A)),
% 6.03/6.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.03/6.24  thf('24', plain,
% 6.03/6.24      (![X0 : $i]:
% 6.03/6.24         ((v2_struct_0 @ sk_A)
% 6.03/6.24          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 6.03/6.24          | (r2_hidden @ X0 @ sk_C)
% 6.03/6.24          | ~ (m1_connsp_2 @ sk_C @ sk_A @ X0))),
% 6.03/6.24      inference('demod', [status(thm)], ['21', '22', '23'])).
% 6.03/6.24  thf('25', plain,
% 6.03/6.24      ((~ (m1_connsp_2 @ sk_C @ sk_A @ sk_B_1)
% 6.03/6.24        | (r2_hidden @ sk_B_1 @ sk_C)
% 6.03/6.24        | (v2_struct_0 @ sk_A))),
% 6.03/6.24      inference('sup-', [status(thm)], ['1', '24'])).
% 6.03/6.24  thf('26', plain, ((m1_connsp_2 @ sk_C @ sk_A @ sk_B_1)),
% 6.03/6.24      inference('clc', [status(thm)], ['8', '9'])).
% 6.03/6.24  thf('27', plain, (((r2_hidden @ sk_B_1 @ sk_C) | (v2_struct_0 @ sk_A))),
% 6.03/6.24      inference('demod', [status(thm)], ['25', '26'])).
% 6.03/6.24  thf('28', plain, (~ (v2_struct_0 @ sk_A)),
% 6.03/6.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.03/6.24  thf('29', plain, ((r2_hidden @ sk_B_1 @ sk_C)),
% 6.03/6.24      inference('clc', [status(thm)], ['27', '28'])).
% 6.03/6.24  thf(l22_zfmisc_1, axiom,
% 6.03/6.24    (![A:$i,B:$i]:
% 6.03/6.24     ( ( r2_hidden @ A @ B ) =>
% 6.03/6.24       ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( B ) ) ))).
% 6.03/6.24  thf('30', plain,
% 6.03/6.24      (![X14 : $i, X15 : $i]:
% 6.03/6.24         (((k2_xboole_0 @ (k1_tarski @ X15) @ X14) = (X14))
% 6.03/6.24          | ~ (r2_hidden @ X15 @ X14))),
% 6.03/6.24      inference('cnf', [status(esa)], [l22_zfmisc_1])).
% 6.03/6.24  thf('31', plain, (((k2_xboole_0 @ (k1_tarski @ sk_B_1) @ sk_C) = (sk_C))),
% 6.03/6.24      inference('sup-', [status(thm)], ['29', '30'])).
% 6.03/6.24  thf(t7_xboole_1, axiom,
% 6.03/6.24    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 6.03/6.24  thf('32', plain,
% 6.03/6.24      (![X11 : $i, X12 : $i]: (r1_tarski @ X11 @ (k2_xboole_0 @ X11 @ X12))),
% 6.03/6.24      inference('cnf', [status(esa)], [t7_xboole_1])).
% 6.03/6.24  thf(t11_xboole_1, axiom,
% 6.03/6.24    (![A:$i,B:$i,C:$i]:
% 6.03/6.24     ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C ) => ( r1_tarski @ A @ C ) ))).
% 6.03/6.24  thf('33', plain,
% 6.03/6.24      (![X6 : $i, X7 : $i, X8 : $i]:
% 6.03/6.24         ((r1_tarski @ X6 @ X7) | ~ (r1_tarski @ (k2_xboole_0 @ X6 @ X8) @ X7))),
% 6.03/6.24      inference('cnf', [status(esa)], [t11_xboole_1])).
% 6.03/6.24  thf('34', plain,
% 6.03/6.24      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.03/6.24         (r1_tarski @ X2 @ (k2_xboole_0 @ (k2_xboole_0 @ X2 @ X1) @ X0))),
% 6.03/6.24      inference('sup-', [status(thm)], ['32', '33'])).
% 6.03/6.24  thf(t12_xboole_1, axiom,
% 6.03/6.24    (![A:$i,B:$i]:
% 6.03/6.24     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 6.03/6.24  thf('35', plain,
% 6.03/6.24      (![X9 : $i, X10 : $i]:
% 6.03/6.24         (((k2_xboole_0 @ X10 @ X9) = (X9)) | ~ (r1_tarski @ X10 @ X9))),
% 6.03/6.24      inference('cnf', [status(esa)], [t12_xboole_1])).
% 6.03/6.24  thf('36', plain,
% 6.03/6.24      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.03/6.24         ((k2_xboole_0 @ X2 @ (k2_xboole_0 @ (k2_xboole_0 @ X2 @ X1) @ X0))
% 6.03/6.24           = (k2_xboole_0 @ (k2_xboole_0 @ X2 @ X1) @ X0))),
% 6.03/6.24      inference('sup-', [status(thm)], ['34', '35'])).
% 6.03/6.24  thf('37', plain,
% 6.03/6.24      (![X11 : $i, X12 : $i]: (r1_tarski @ X11 @ (k2_xboole_0 @ X11 @ X12))),
% 6.03/6.24      inference('cnf', [status(esa)], [t7_xboole_1])).
% 6.03/6.24  thf('38', plain,
% 6.03/6.24      (![X9 : $i, X10 : $i]:
% 6.03/6.24         (((k2_xboole_0 @ X10 @ X9) = (X9)) | ~ (r1_tarski @ X10 @ X9))),
% 6.03/6.24      inference('cnf', [status(esa)], [t12_xboole_1])).
% 6.03/6.24  thf('39', plain,
% 6.03/6.24      (![X0 : $i, X1 : $i]:
% 6.03/6.24         ((k2_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0))
% 6.03/6.24           = (k2_xboole_0 @ X1 @ X0))),
% 6.03/6.24      inference('sup-', [status(thm)], ['37', '38'])).
% 6.03/6.24  thf(t69_enumset1, axiom,
% 6.03/6.24    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 6.03/6.24  thf('40', plain,
% 6.03/6.24      (![X13 : $i]: ((k2_tarski @ X13 @ X13) = (k1_tarski @ X13))),
% 6.03/6.24      inference('cnf', [status(esa)], [t69_enumset1])).
% 6.03/6.24  thf(t47_zfmisc_1, axiom,
% 6.03/6.24    (![A:$i,B:$i,C:$i]:
% 6.03/6.24     ( ( r1_tarski @ ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) @ C ) =>
% 6.03/6.24       ( r2_hidden @ A @ C ) ))).
% 6.03/6.24  thf('41', plain,
% 6.03/6.24      (![X18 : $i, X19 : $i, X20 : $i]:
% 6.03/6.24         ((r2_hidden @ X18 @ X19)
% 6.03/6.24          | ~ (r1_tarski @ (k2_xboole_0 @ (k2_tarski @ X18 @ X20) @ X19) @ X19))),
% 6.03/6.24      inference('cnf', [status(esa)], [t47_zfmisc_1])).
% 6.03/6.24  thf('42', plain,
% 6.03/6.24      (![X0 : $i, X1 : $i]:
% 6.03/6.24         (~ (r1_tarski @ (k2_xboole_0 @ (k1_tarski @ X0) @ X1) @ X1)
% 6.03/6.24          | (r2_hidden @ X0 @ X1))),
% 6.03/6.24      inference('sup-', [status(thm)], ['40', '41'])).
% 6.03/6.24  thf('43', plain,
% 6.03/6.24      (![X0 : $i, X1 : $i]:
% 6.03/6.24         (~ (r1_tarski @ (k2_xboole_0 @ (k1_tarski @ X1) @ X0) @ 
% 6.03/6.24             (k2_xboole_0 @ (k1_tarski @ X1) @ X0))
% 6.03/6.24          | (r2_hidden @ X1 @ (k2_xboole_0 @ (k1_tarski @ X1) @ X0)))),
% 6.03/6.24      inference('sup-', [status(thm)], ['39', '42'])).
% 6.03/6.24  thf(d10_xboole_0, axiom,
% 6.03/6.24    (![A:$i,B:$i]:
% 6.03/6.24     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 6.03/6.24  thf('44', plain,
% 6.03/6.24      (![X3 : $i, X4 : $i]: ((r1_tarski @ X3 @ X4) | ((X3) != (X4)))),
% 6.03/6.24      inference('cnf', [status(esa)], [d10_xboole_0])).
% 6.03/6.24  thf('45', plain, (![X4 : $i]: (r1_tarski @ X4 @ X4)),
% 6.03/6.24      inference('simplify', [status(thm)], ['44'])).
% 6.03/6.24  thf('46', plain,
% 6.03/6.24      (![X0 : $i, X1 : $i]:
% 6.03/6.24         (r2_hidden @ X1 @ (k2_xboole_0 @ (k1_tarski @ X1) @ X0))),
% 6.03/6.24      inference('demod', [status(thm)], ['43', '45'])).
% 6.03/6.24  thf('47', plain,
% 6.03/6.24      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.03/6.24         (r2_hidden @ X2 @ 
% 6.03/6.24          (k2_xboole_0 @ (k2_xboole_0 @ (k1_tarski @ X2) @ X1) @ X0))),
% 6.03/6.24      inference('sup+', [status(thm)], ['36', '46'])).
% 6.03/6.24  thf('48', plain,
% 6.03/6.24      (![X0 : $i]: (r2_hidden @ sk_B_1 @ (k2_xboole_0 @ sk_C @ X0))),
% 6.03/6.24      inference('sup+', [status(thm)], ['31', '47'])).
% 6.03/6.24  thf('49', plain,
% 6.03/6.24      ((m1_subset_1 @ sk_D @ (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B_1)))),
% 6.03/6.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.03/6.24  thf('50', plain,
% 6.03/6.24      (![X47 : $i, X48 : $i, X49 : $i]:
% 6.03/6.24         (~ (m1_subset_1 @ X47 @ (u1_struct_0 @ X48))
% 6.03/6.24          | (m1_connsp_2 @ X49 @ X48 @ X47)
% 6.03/6.24          | ~ (m1_subset_1 @ X49 @ (u1_struct_0 @ (k9_yellow_6 @ X48 @ X47)))
% 6.03/6.24          | ~ (l1_pre_topc @ X48)
% 6.03/6.24          | ~ (v2_pre_topc @ X48)
% 6.03/6.24          | (v2_struct_0 @ X48))),
% 6.03/6.24      inference('cnf', [status(esa)], [t21_waybel_9])).
% 6.03/6.24  thf('51', plain,
% 6.03/6.24      (((v2_struct_0 @ sk_A)
% 6.03/6.24        | ~ (v2_pre_topc @ sk_A)
% 6.03/6.24        | ~ (l1_pre_topc @ sk_A)
% 6.03/6.24        | (m1_connsp_2 @ sk_D @ sk_A @ sk_B_1)
% 6.03/6.24        | ~ (m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)))),
% 6.03/6.24      inference('sup-', [status(thm)], ['49', '50'])).
% 6.03/6.24  thf('52', plain, ((v2_pre_topc @ sk_A)),
% 6.03/6.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.03/6.24  thf('53', plain, ((l1_pre_topc @ sk_A)),
% 6.03/6.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.03/6.24  thf('54', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 6.03/6.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.03/6.24  thf('55', plain,
% 6.03/6.24      (((v2_struct_0 @ sk_A) | (m1_connsp_2 @ sk_D @ sk_A @ sk_B_1))),
% 6.03/6.24      inference('demod', [status(thm)], ['51', '52', '53', '54'])).
% 6.03/6.24  thf('56', plain, (~ (v2_struct_0 @ sk_A)),
% 6.03/6.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.03/6.24  thf('57', plain, ((m1_connsp_2 @ sk_D @ sk_A @ sk_B_1)),
% 6.03/6.24      inference('clc', [status(thm)], ['55', '56'])).
% 6.03/6.24  thf('58', plain,
% 6.03/6.24      (![X0 : $i]:
% 6.03/6.24         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 6.03/6.24          | ~ (m1_connsp_2 @ X0 @ sk_A @ sk_B_1))),
% 6.03/6.24      inference('clc', [status(thm)], ['16', '17'])).
% 6.03/6.24  thf('59', plain,
% 6.03/6.24      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 6.03/6.24      inference('sup-', [status(thm)], ['57', '58'])).
% 6.03/6.24  thf('60', plain,
% 6.03/6.24      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 6.03/6.24      inference('sup-', [status(thm)], ['10', '18'])).
% 6.03/6.24  thf(dt_k4_subset_1, axiom,
% 6.03/6.24    (![A:$i,B:$i,C:$i]:
% 6.03/6.24     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 6.03/6.24         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 6.03/6.24       ( m1_subset_1 @ ( k4_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 6.03/6.24  thf('61', plain,
% 6.03/6.24      (![X24 : $i, X25 : $i, X26 : $i]:
% 6.03/6.24         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ X25))
% 6.03/6.24          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ X25))
% 6.03/6.24          | (m1_subset_1 @ (k4_subset_1 @ X25 @ X24 @ X26) @ 
% 6.03/6.24             (k1_zfmisc_1 @ X25)))),
% 6.03/6.24      inference('cnf', [status(esa)], [dt_k4_subset_1])).
% 6.03/6.24  thf('62', plain,
% 6.03/6.24      (![X0 : $i]:
% 6.03/6.24         ((m1_subset_1 @ (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ X0) @ 
% 6.03/6.24           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 6.03/6.24          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 6.03/6.24      inference('sup-', [status(thm)], ['60', '61'])).
% 6.03/6.24  thf('63', plain,
% 6.03/6.24      ((m1_subset_1 @ (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ sk_D) @ 
% 6.03/6.24        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 6.03/6.24      inference('sup-', [status(thm)], ['59', '62'])).
% 6.03/6.24  thf('64', plain,
% 6.03/6.24      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 6.03/6.24      inference('sup-', [status(thm)], ['57', '58'])).
% 6.03/6.24  thf('65', plain,
% 6.03/6.24      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 6.03/6.24      inference('sup-', [status(thm)], ['10', '18'])).
% 6.03/6.24  thf(redefinition_k4_subset_1, axiom,
% 6.03/6.24    (![A:$i,B:$i,C:$i]:
% 6.03/6.24     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 6.03/6.24         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 6.03/6.24       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 6.03/6.24  thf('66', plain,
% 6.03/6.24      (![X27 : $i, X28 : $i, X29 : $i]:
% 6.03/6.24         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ X28))
% 6.03/6.24          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ X28))
% 6.03/6.24          | ((k4_subset_1 @ X28 @ X27 @ X29) = (k2_xboole_0 @ X27 @ X29)))),
% 6.03/6.24      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 6.03/6.24  thf('67', plain,
% 6.03/6.24      (![X0 : $i]:
% 6.03/6.24         (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ X0)
% 6.03/6.24            = (k2_xboole_0 @ sk_C @ X0))
% 6.03/6.24          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 6.03/6.24      inference('sup-', [status(thm)], ['65', '66'])).
% 6.03/6.24  thf('68', plain,
% 6.03/6.24      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ sk_D)
% 6.03/6.24         = (k2_xboole_0 @ sk_C @ sk_D))),
% 6.03/6.24      inference('sup-', [status(thm)], ['64', '67'])).
% 6.03/6.24  thf('69', plain,
% 6.03/6.24      ((m1_subset_1 @ (k2_xboole_0 @ sk_C @ sk_D) @ 
% 6.03/6.24        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 6.03/6.24      inference('demod', [status(thm)], ['63', '68'])).
% 6.03/6.24  thf(t39_yellow_6, axiom,
% 6.03/6.24    (![A:$i]:
% 6.03/6.24     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 6.03/6.24       ( ![B:$i]:
% 6.03/6.24         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 6.03/6.24           ( ![C:$i]:
% 6.03/6.24             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 6.03/6.24               ( ( r2_hidden @ C @ ( u1_struct_0 @ ( k9_yellow_6 @ A @ B ) ) ) <=>
% 6.03/6.24                 ( ( r2_hidden @ B @ C ) & ( v3_pre_topc @ C @ A ) ) ) ) ) ) ) ))).
% 6.03/6.24  thf('70', plain,
% 6.03/6.24      (![X44 : $i, X45 : $i, X46 : $i]:
% 6.03/6.24         (~ (m1_subset_1 @ X44 @ (u1_struct_0 @ X45))
% 6.03/6.24          | ~ (r2_hidden @ X44 @ X46)
% 6.03/6.24          | ~ (v3_pre_topc @ X46 @ X45)
% 6.03/6.24          | (r2_hidden @ X46 @ (u1_struct_0 @ (k9_yellow_6 @ X45 @ X44)))
% 6.03/6.24          | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (u1_struct_0 @ X45)))
% 6.03/6.24          | ~ (l1_pre_topc @ X45)
% 6.03/6.24          | ~ (v2_pre_topc @ X45)
% 6.03/6.24          | (v2_struct_0 @ X45))),
% 6.03/6.24      inference('cnf', [status(esa)], [t39_yellow_6])).
% 6.03/6.24  thf('71', plain,
% 6.03/6.24      (![X0 : $i]:
% 6.03/6.24         ((v2_struct_0 @ sk_A)
% 6.03/6.24          | ~ (v2_pre_topc @ sk_A)
% 6.03/6.24          | ~ (l1_pre_topc @ sk_A)
% 6.03/6.24          | (r2_hidden @ (k2_xboole_0 @ sk_C @ sk_D) @ 
% 6.03/6.24             (u1_struct_0 @ (k9_yellow_6 @ sk_A @ X0)))
% 6.03/6.24          | ~ (v3_pre_topc @ (k2_xboole_0 @ sk_C @ sk_D) @ sk_A)
% 6.03/6.24          | ~ (r2_hidden @ X0 @ (k2_xboole_0 @ sk_C @ sk_D))
% 6.03/6.24          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 6.03/6.24      inference('sup-', [status(thm)], ['69', '70'])).
% 6.03/6.24  thf('72', plain, ((v2_pre_topc @ sk_A)),
% 6.03/6.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.03/6.24  thf('73', plain, ((l1_pre_topc @ sk_A)),
% 6.03/6.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.03/6.24  thf('74', plain,
% 6.03/6.24      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 6.03/6.24      inference('sup-', [status(thm)], ['57', '58'])).
% 6.03/6.24  thf('75', plain,
% 6.03/6.24      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 6.03/6.24      inference('sup-', [status(thm)], ['10', '18'])).
% 6.03/6.24  thf(fc7_tops_1, axiom,
% 6.03/6.24    (![A:$i,B:$i,C:$i]:
% 6.03/6.24     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & ( v3_pre_topc @ B @ A ) & 
% 6.03/6.24         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) & 
% 6.03/6.24         ( v3_pre_topc @ C @ A ) & 
% 6.03/6.24         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 6.03/6.24       ( v3_pre_topc @ ( k2_xboole_0 @ B @ C ) @ A ) ))).
% 6.03/6.24  thf('76', plain,
% 6.03/6.24      (![X35 : $i, X36 : $i, X37 : $i]:
% 6.03/6.24         (~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (u1_struct_0 @ X36)))
% 6.03/6.24          | ~ (v3_pre_topc @ X35 @ X36)
% 6.03/6.24          | ~ (l1_pre_topc @ X36)
% 6.03/6.24          | ~ (v2_pre_topc @ X36)
% 6.03/6.24          | ~ (v3_pre_topc @ X37 @ X36)
% 6.03/6.24          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (u1_struct_0 @ X36)))
% 6.03/6.24          | (v3_pre_topc @ (k2_xboole_0 @ X35 @ X37) @ X36))),
% 6.03/6.24      inference('cnf', [status(esa)], [fc7_tops_1])).
% 6.03/6.24  thf('77', plain,
% 6.03/6.24      (![X0 : $i]:
% 6.03/6.24         ((v3_pre_topc @ (k2_xboole_0 @ sk_C @ X0) @ sk_A)
% 6.03/6.24          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 6.03/6.24          | ~ (v3_pre_topc @ X0 @ sk_A)
% 6.03/6.24          | ~ (v2_pre_topc @ sk_A)
% 6.03/6.24          | ~ (l1_pre_topc @ sk_A)
% 6.03/6.24          | ~ (v3_pre_topc @ sk_C @ sk_A))),
% 6.03/6.24      inference('sup-', [status(thm)], ['75', '76'])).
% 6.03/6.24  thf('78', plain, ((v2_pre_topc @ sk_A)),
% 6.03/6.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.03/6.24  thf('79', plain, ((l1_pre_topc @ sk_A)),
% 6.03/6.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.03/6.24  thf('80', plain,
% 6.03/6.24      (![X0 : $i]:
% 6.03/6.24         ((v3_pre_topc @ (k2_xboole_0 @ sk_C @ X0) @ sk_A)
% 6.03/6.24          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 6.03/6.24          | ~ (v3_pre_topc @ X0 @ sk_A)
% 6.03/6.24          | ~ (v3_pre_topc @ sk_C @ sk_A))),
% 6.03/6.24      inference('demod', [status(thm)], ['77', '78', '79'])).
% 6.03/6.24  thf('81', plain,
% 6.03/6.24      ((m1_subset_1 @ sk_C @ (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B_1)))),
% 6.03/6.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.03/6.24  thf(d2_subset_1, axiom,
% 6.03/6.24    (![A:$i,B:$i]:
% 6.03/6.24     ( ( ( v1_xboole_0 @ A ) =>
% 6.03/6.24         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 6.03/6.24       ( ( ~( v1_xboole_0 @ A ) ) =>
% 6.03/6.24         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 6.03/6.24  thf('82', plain,
% 6.03/6.24      (![X21 : $i, X22 : $i]:
% 6.03/6.24         (~ (m1_subset_1 @ X21 @ X22)
% 6.03/6.24          | (r2_hidden @ X21 @ X22)
% 6.03/6.24          | (v1_xboole_0 @ X22))),
% 6.03/6.24      inference('cnf', [status(esa)], [d2_subset_1])).
% 6.03/6.24  thf('83', plain,
% 6.03/6.24      (((v1_xboole_0 @ (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B_1)))
% 6.03/6.24        | (r2_hidden @ sk_C @ (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B_1))))),
% 6.03/6.24      inference('sup-', [status(thm)], ['81', '82'])).
% 6.03/6.24  thf('84', plain,
% 6.03/6.24      (![X44 : $i, X45 : $i, X46 : $i]:
% 6.03/6.24         (~ (m1_subset_1 @ X44 @ (u1_struct_0 @ X45))
% 6.03/6.24          | ~ (r2_hidden @ X46 @ (u1_struct_0 @ (k9_yellow_6 @ X45 @ X44)))
% 6.03/6.24          | (v3_pre_topc @ X46 @ X45)
% 6.03/6.24          | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (u1_struct_0 @ X45)))
% 6.03/6.24          | ~ (l1_pre_topc @ X45)
% 6.03/6.24          | ~ (v2_pre_topc @ X45)
% 6.03/6.24          | (v2_struct_0 @ X45))),
% 6.03/6.24      inference('cnf', [status(esa)], [t39_yellow_6])).
% 6.03/6.24  thf('85', plain,
% 6.03/6.24      (((v1_xboole_0 @ (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B_1)))
% 6.03/6.24        | (v2_struct_0 @ sk_A)
% 6.03/6.24        | ~ (v2_pre_topc @ sk_A)
% 6.03/6.24        | ~ (l1_pre_topc @ sk_A)
% 6.03/6.24        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 6.03/6.24        | (v3_pre_topc @ sk_C @ sk_A)
% 6.03/6.24        | ~ (m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)))),
% 6.03/6.24      inference('sup-', [status(thm)], ['83', '84'])).
% 6.03/6.24  thf('86', plain, ((v2_pre_topc @ sk_A)),
% 6.03/6.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.03/6.24  thf('87', plain, ((l1_pre_topc @ sk_A)),
% 6.03/6.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.03/6.24  thf('88', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 6.03/6.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.03/6.24  thf('89', plain,
% 6.03/6.24      (((v1_xboole_0 @ (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B_1)))
% 6.03/6.24        | (v2_struct_0 @ sk_A)
% 6.03/6.24        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 6.03/6.24        | (v3_pre_topc @ sk_C @ sk_A))),
% 6.03/6.24      inference('demod', [status(thm)], ['85', '86', '87', '88'])).
% 6.03/6.24  thf('90', plain,
% 6.03/6.24      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 6.03/6.24      inference('sup-', [status(thm)], ['10', '18'])).
% 6.03/6.24  thf('91', plain,
% 6.03/6.24      (((v1_xboole_0 @ (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B_1)))
% 6.03/6.24        | (v2_struct_0 @ sk_A)
% 6.03/6.24        | (v3_pre_topc @ sk_C @ sk_A))),
% 6.03/6.24      inference('demod', [status(thm)], ['89', '90'])).
% 6.03/6.24  thf('92', plain, (~ (v2_struct_0 @ sk_A)),
% 6.03/6.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.03/6.24  thf('93', plain,
% 6.03/6.24      (((v3_pre_topc @ sk_C @ sk_A)
% 6.03/6.24        | (v1_xboole_0 @ (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B_1))))),
% 6.03/6.24      inference('clc', [status(thm)], ['91', '92'])).
% 6.03/6.24  thf('94', plain,
% 6.03/6.24      ((m1_subset_1 @ sk_C @ (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B_1)))),
% 6.03/6.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.03/6.24  thf('95', plain,
% 6.03/6.24      (![X22 : $i, X23 : $i]:
% 6.03/6.24         (~ (m1_subset_1 @ X23 @ X22)
% 6.03/6.24          | (v1_xboole_0 @ X23)
% 6.03/6.24          | ~ (v1_xboole_0 @ X22))),
% 6.03/6.24      inference('cnf', [status(esa)], [d2_subset_1])).
% 6.03/6.24  thf('96', plain,
% 6.03/6.24      ((~ (v1_xboole_0 @ (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B_1)))
% 6.03/6.24        | (v1_xboole_0 @ sk_C))),
% 6.03/6.24      inference('sup-', [status(thm)], ['94', '95'])).
% 6.03/6.24  thf('97', plain, (((v3_pre_topc @ sk_C @ sk_A) | (v1_xboole_0 @ sk_C))),
% 6.03/6.24      inference('sup-', [status(thm)], ['93', '96'])).
% 6.03/6.24  thf('98', plain, ((r2_hidden @ sk_B_1 @ sk_C)),
% 6.03/6.24      inference('clc', [status(thm)], ['27', '28'])).
% 6.03/6.24  thf(d1_xboole_0, axiom,
% 6.03/6.24    (![A:$i]:
% 6.03/6.24     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 6.03/6.24  thf('99', plain,
% 6.03/6.24      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 6.03/6.24      inference('cnf', [status(esa)], [d1_xboole_0])).
% 6.03/6.24  thf('100', plain, (~ (v1_xboole_0 @ sk_C)),
% 6.03/6.24      inference('sup-', [status(thm)], ['98', '99'])).
% 6.03/6.24  thf('101', plain, ((v3_pre_topc @ sk_C @ sk_A)),
% 6.03/6.24      inference('clc', [status(thm)], ['97', '100'])).
% 6.03/6.24  thf('102', plain,
% 6.03/6.24      (![X0 : $i]:
% 6.03/6.24         ((v3_pre_topc @ (k2_xboole_0 @ sk_C @ X0) @ sk_A)
% 6.03/6.24          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 6.03/6.24          | ~ (v3_pre_topc @ X0 @ sk_A))),
% 6.03/6.24      inference('demod', [status(thm)], ['80', '101'])).
% 6.03/6.24  thf('103', plain,
% 6.03/6.24      ((~ (v3_pre_topc @ sk_D @ sk_A)
% 6.03/6.24        | (v3_pre_topc @ (k2_xboole_0 @ sk_C @ sk_D) @ sk_A))),
% 6.03/6.24      inference('sup-', [status(thm)], ['74', '102'])).
% 6.03/6.24  thf('104', plain,
% 6.03/6.24      ((m1_subset_1 @ sk_D @ (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B_1)))),
% 6.03/6.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.03/6.24  thf('105', plain,
% 6.03/6.24      (![X21 : $i, X22 : $i]:
% 6.03/6.24         (~ (m1_subset_1 @ X21 @ X22)
% 6.03/6.24          | (r2_hidden @ X21 @ X22)
% 6.03/6.24          | (v1_xboole_0 @ X22))),
% 6.03/6.24      inference('cnf', [status(esa)], [d2_subset_1])).
% 6.03/6.24  thf('106', plain,
% 6.03/6.24      (((v1_xboole_0 @ (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B_1)))
% 6.03/6.24        | (r2_hidden @ sk_D @ (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B_1))))),
% 6.03/6.24      inference('sup-', [status(thm)], ['104', '105'])).
% 6.03/6.24  thf('107', plain,
% 6.03/6.24      (![X44 : $i, X45 : $i, X46 : $i]:
% 6.03/6.24         (~ (m1_subset_1 @ X44 @ (u1_struct_0 @ X45))
% 6.03/6.24          | ~ (r2_hidden @ X46 @ (u1_struct_0 @ (k9_yellow_6 @ X45 @ X44)))
% 6.03/6.24          | (v3_pre_topc @ X46 @ X45)
% 6.03/6.24          | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (u1_struct_0 @ X45)))
% 6.03/6.24          | ~ (l1_pre_topc @ X45)
% 6.03/6.24          | ~ (v2_pre_topc @ X45)
% 6.03/6.24          | (v2_struct_0 @ X45))),
% 6.03/6.24      inference('cnf', [status(esa)], [t39_yellow_6])).
% 6.03/6.24  thf('108', plain,
% 6.03/6.24      (((v1_xboole_0 @ (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B_1)))
% 6.03/6.24        | (v2_struct_0 @ sk_A)
% 6.03/6.24        | ~ (v2_pre_topc @ sk_A)
% 6.03/6.24        | ~ (l1_pre_topc @ sk_A)
% 6.03/6.24        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 6.03/6.24        | (v3_pre_topc @ sk_D @ sk_A)
% 6.03/6.24        | ~ (m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)))),
% 6.03/6.24      inference('sup-', [status(thm)], ['106', '107'])).
% 6.03/6.24  thf('109', plain, ((v2_pre_topc @ sk_A)),
% 6.03/6.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.03/6.24  thf('110', plain, ((l1_pre_topc @ sk_A)),
% 6.03/6.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.03/6.24  thf('111', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 6.03/6.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.03/6.24  thf('112', plain,
% 6.03/6.24      (((v1_xboole_0 @ (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B_1)))
% 6.03/6.24        | (v2_struct_0 @ sk_A)
% 6.03/6.24        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 6.03/6.24        | (v3_pre_topc @ sk_D @ sk_A))),
% 6.03/6.24      inference('demod', [status(thm)], ['108', '109', '110', '111'])).
% 6.03/6.24  thf('113', plain,
% 6.03/6.24      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 6.03/6.24      inference('sup-', [status(thm)], ['57', '58'])).
% 6.03/6.24  thf('114', plain,
% 6.03/6.24      (((v1_xboole_0 @ (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B_1)))
% 6.03/6.24        | (v2_struct_0 @ sk_A)
% 6.03/6.24        | (v3_pre_topc @ sk_D @ sk_A))),
% 6.03/6.24      inference('demod', [status(thm)], ['112', '113'])).
% 6.03/6.24  thf('115', plain, (~ (v2_struct_0 @ sk_A)),
% 6.03/6.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.03/6.24  thf('116', plain,
% 6.03/6.24      (((v3_pre_topc @ sk_D @ sk_A)
% 6.03/6.24        | (v1_xboole_0 @ (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B_1))))),
% 6.03/6.24      inference('clc', [status(thm)], ['114', '115'])).
% 6.03/6.24  thf('117', plain,
% 6.03/6.24      ((~ (v1_xboole_0 @ (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B_1)))
% 6.03/6.24        | (v1_xboole_0 @ sk_C))),
% 6.03/6.24      inference('sup-', [status(thm)], ['94', '95'])).
% 6.03/6.24  thf('118', plain, (((v3_pre_topc @ sk_D @ sk_A) | (v1_xboole_0 @ sk_C))),
% 6.03/6.24      inference('sup-', [status(thm)], ['116', '117'])).
% 6.03/6.24  thf('119', plain, (~ (v1_xboole_0 @ sk_C)),
% 6.03/6.24      inference('sup-', [status(thm)], ['98', '99'])).
% 6.03/6.24  thf('120', plain, ((v3_pre_topc @ sk_D @ sk_A)),
% 6.03/6.24      inference('clc', [status(thm)], ['118', '119'])).
% 6.03/6.24  thf('121', plain, ((v3_pre_topc @ (k2_xboole_0 @ sk_C @ sk_D) @ sk_A)),
% 6.03/6.24      inference('demod', [status(thm)], ['103', '120'])).
% 6.03/6.24  thf('122', plain,
% 6.03/6.24      (![X0 : $i]:
% 6.03/6.24         ((v2_struct_0 @ sk_A)
% 6.03/6.24          | (r2_hidden @ (k2_xboole_0 @ sk_C @ sk_D) @ 
% 6.03/6.24             (u1_struct_0 @ (k9_yellow_6 @ sk_A @ X0)))
% 6.03/6.24          | ~ (r2_hidden @ X0 @ (k2_xboole_0 @ sk_C @ sk_D))
% 6.03/6.24          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 6.03/6.24      inference('demod', [status(thm)], ['71', '72', '73', '121'])).
% 6.03/6.24  thf('123', plain,
% 6.03/6.24      ((~ (m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 6.03/6.24        | (r2_hidden @ (k2_xboole_0 @ sk_C @ sk_D) @ 
% 6.03/6.24           (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B_1)))
% 6.03/6.24        | (v2_struct_0 @ sk_A))),
% 6.03/6.24      inference('sup-', [status(thm)], ['48', '122'])).
% 6.03/6.24  thf('124', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 6.03/6.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.03/6.24  thf('125', plain,
% 6.03/6.24      (((r2_hidden @ (k2_xboole_0 @ sk_C @ sk_D) @ 
% 6.03/6.24         (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B_1)))
% 6.03/6.24        | (v2_struct_0 @ sk_A))),
% 6.03/6.24      inference('demod', [status(thm)], ['123', '124'])).
% 6.03/6.24  thf('126', plain, (~ (v2_struct_0 @ sk_A)),
% 6.03/6.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.03/6.24  thf('127', plain,
% 6.03/6.24      ((r2_hidden @ (k2_xboole_0 @ sk_C @ sk_D) @ 
% 6.03/6.24        (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B_1)))),
% 6.03/6.24      inference('clc', [status(thm)], ['125', '126'])).
% 6.03/6.24  thf(t1_subset, axiom,
% 6.03/6.24    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 6.03/6.24  thf('128', plain,
% 6.03/6.24      (![X30 : $i, X31 : $i]:
% 6.03/6.24         ((m1_subset_1 @ X30 @ X31) | ~ (r2_hidden @ X30 @ X31))),
% 6.03/6.24      inference('cnf', [status(esa)], [t1_subset])).
% 6.03/6.24  thf('129', plain,
% 6.03/6.24      ((m1_subset_1 @ (k2_xboole_0 @ sk_C @ sk_D) @ 
% 6.03/6.24        (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B_1)))),
% 6.03/6.24      inference('sup-', [status(thm)], ['127', '128'])).
% 6.03/6.24  thf('130', plain, ($false), inference('demod', [status(thm)], ['0', '129'])).
% 6.03/6.24  
% 6.03/6.24  % SZS output end Refutation
% 6.03/6.24  
% 6.03/6.25  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
