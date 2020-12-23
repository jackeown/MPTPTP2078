%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.b6rnQgMz6a

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:14:26 EST 2020

% Result     : Theorem 5.50s
% Output     : Refutation 5.50s
% Verified   : 
% Statistics : Number of formulae       :  184 ( 649 expanded)
%              Number of leaves         :   39 ( 202 expanded)
%              Depth                    :   20
%              Number of atoms          : 1556 (10999 expanded)
%              Number of equality atoms :   26 (  39 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(m1_connsp_2_type,type,(
    m1_connsp_2: $i > $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k9_yellow_6_type,type,(
    k9_yellow_6: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

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

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('1',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X18 @ X19 ) )
      = ( k2_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('2',plain,(
    ~ ( m1_subset_1 @ ( k3_tarski @ ( k2_tarski @ sk_C @ sk_D ) ) @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('3',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
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

thf('5',plain,(
    ! [X46: $i,X47: $i,X48: $i] :
      ( ~ ( m1_subset_1 @ X46 @ ( u1_struct_0 @ X47 ) )
      | ( m1_connsp_2 @ X48 @ X47 @ X46 )
      | ~ ( m1_subset_1 @ X48 @ ( u1_struct_0 @ ( k9_yellow_6 @ X47 @ X46 ) ) )
      | ~ ( l1_pre_topc @ X47 )
      | ~ ( v2_pre_topc @ X47 )
      | ( v2_struct_0 @ X47 ) ) ),
    inference(cnf,[status(esa)],[t21_waybel_9])).

thf('6',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( m1_connsp_2 @ sk_C @ sk_A @ sk_B_1 )
    | ~ ( m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_connsp_2 @ sk_C @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['6','7','8','9'])).

thf('11',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    m1_connsp_2 @ sk_C @ sk_A @ sk_B_1 ),
    inference(clc,[status(thm)],['10','11'])).

thf('13',plain,(
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

thf('14',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ~ ( l1_pre_topc @ X37 )
      | ~ ( v2_pre_topc @ X37 )
      | ( v2_struct_0 @ X37 )
      | ~ ( m1_subset_1 @ X38 @ ( u1_struct_0 @ X37 ) )
      | ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X37 ) ) )
      | ~ ( m1_connsp_2 @ X39 @ X37 @ X38 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_connsp_2])).

thf('15',plain,(
    ! [X0: $i] :
      ( ~ ( m1_connsp_2 @ X0 @ sk_A @ sk_B_1 )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ! [X0: $i] :
      ( ~ ( m1_connsp_2 @ X0 @ sk_A @ sk_B_1 )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['15','16','17'])).

thf('19',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( m1_connsp_2 @ X0 @ sk_A @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['18','19'])).

thf('21',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['12','20'])).

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

thf('22',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X41 ) ) )
      | ~ ( m1_connsp_2 @ X40 @ X41 @ X42 )
      | ( r2_hidden @ X42 @ X40 )
      | ~ ( m1_subset_1 @ X42 @ ( u1_struct_0 @ X41 ) )
      | ~ ( l1_pre_topc @ X41 )
      | ~ ( v2_pre_topc @ X41 )
      | ( v2_struct_0 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t6_connsp_2])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X0 @ sk_C )
      | ~ ( m1_connsp_2 @ sk_C @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X0 @ sk_C )
      | ~ ( m1_connsp_2 @ sk_C @ sk_A @ X0 ) ) ),
    inference(demod,[status(thm)],['23','24','25'])).

thf('27',plain,
    ( ~ ( m1_connsp_2 @ sk_C @ sk_A @ sk_B_1 )
    | ( r2_hidden @ sk_B_1 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['3','26'])).

thf('28',plain,(
    m1_connsp_2 @ sk_C @ sk_A @ sk_B_1 ),
    inference(clc,[status(thm)],['10','11'])).

thf('29',plain,
    ( ( r2_hidden @ sk_B_1 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    r2_hidden @ sk_B_1 @ sk_C ),
    inference(clc,[status(thm)],['29','30'])).

thf(l22_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
        = B ) ) )).

thf('32',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k2_xboole_0 @ ( k1_tarski @ X17 ) @ X16 )
        = X16 )
      | ~ ( r2_hidden @ X17 @ X16 ) ) ),
    inference(cnf,[status(esa)],[l22_zfmisc_1])).

thf('33',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X18 @ X19 ) )
      = ( k2_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('34',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k3_tarski @ ( k2_tarski @ ( k1_tarski @ X17 ) @ X16 ) )
        = X16 )
      | ~ ( r2_hidden @ X17 @ X16 ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,
    ( ( k3_tarski @ ( k2_tarski @ ( k1_tarski @ sk_B_1 ) @ sk_C ) )
    = sk_C ),
    inference('sup-',[status(thm)],['31','34'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('36',plain,(
    ! [X11: $i,X12: $i] :
      ( r1_tarski @ X11 @ ( k2_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('37',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X18 @ X19 ) )
      = ( k2_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('38',plain,(
    ! [X11: $i,X12: $i] :
      ( r1_tarski @ X11 @ ( k3_tarski @ ( k2_tarski @ X11 @ X12 ) ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf(t11_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ C ) ) )).

thf('39',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( r1_tarski @ X6 @ X7 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X6 @ X8 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t11_xboole_1])).

thf('40',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X18 @ X19 ) )
      = ( k2_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('41',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( r1_tarski @ X6 @ X7 )
      | ~ ( r1_tarski @ ( k3_tarski @ ( k2_tarski @ X6 @ X8 ) ) @ X7 ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ X2 @ ( k3_tarski @ ( k2_tarski @ ( k3_tarski @ ( k2_tarski @ X2 @ X1 ) ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['38','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_tarski @ sk_B_1 ) @ ( k3_tarski @ ( k2_tarski @ sk_C @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['35','42'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('44',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k2_xboole_0 @ X10 @ X9 )
        = X9 )
      | ~ ( r1_tarski @ X10 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('45',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X18 @ X19 ) )
      = ( k2_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('46',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k3_tarski @ ( k2_tarski @ X10 @ X9 ) )
        = X9 )
      | ~ ( r1_tarski @ X10 @ X9 ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k2_tarski @ ( k1_tarski @ sk_B_1 ) @ ( k3_tarski @ ( k2_tarski @ sk_C @ X0 ) ) ) )
      = ( k3_tarski @ ( k2_tarski @ sk_C @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['43','46'])).

thf('48',plain,(
    ! [X11: $i,X12: $i] :
      ( r1_tarski @ X11 @ ( k3_tarski @ ( k2_tarski @ X11 @ X12 ) ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('49',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k3_tarski @ ( k2_tarski @ X10 @ X9 ) )
        = X9 )
      | ~ ( r1_tarski @ X10 @ X9 ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) ) ) )
      = ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf(l20_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) @ B )
     => ( r2_hidden @ A @ B ) ) )).

thf('51',plain,(
    ! [X14: $i,X15: $i] :
      ( ( r2_hidden @ X14 @ X15 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ ( k1_tarski @ X14 ) @ X15 ) @ X15 ) ) ),
    inference(cnf,[status(esa)],[l20_zfmisc_1])).

thf('52',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X18 @ X19 ) )
      = ( k2_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('53',plain,(
    ! [X14: $i,X15: $i] :
      ( ( r2_hidden @ X14 @ X15 )
      | ~ ( r1_tarski @ ( k3_tarski @ ( k2_tarski @ ( k1_tarski @ X14 ) @ X15 ) ) @ X15 ) ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k3_tarski @ ( k2_tarski @ ( k1_tarski @ X1 ) @ X0 ) ) @ ( k3_tarski @ ( k2_tarski @ ( k1_tarski @ X1 ) @ X0 ) ) )
      | ( r2_hidden @ X1 @ ( k3_tarski @ ( k2_tarski @ ( k1_tarski @ X1 ) @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['50','53'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('55',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ( X3 != X4 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('56',plain,(
    ! [X4: $i] :
      ( r1_tarski @ X4 @ X4 ) ),
    inference(simplify,[status(thm)],['55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X1 @ ( k3_tarski @ ( k2_tarski @ ( k1_tarski @ X1 ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['54','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( r2_hidden @ sk_B_1 @ ( k3_tarski @ ( k2_tarski @ sk_C @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['47','57'])).

thf('59',plain,(
    m1_subset_1 @ sk_D @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    ! [X46: $i,X47: $i,X48: $i] :
      ( ~ ( m1_subset_1 @ X46 @ ( u1_struct_0 @ X47 ) )
      | ( m1_connsp_2 @ X48 @ X47 @ X46 )
      | ~ ( m1_subset_1 @ X48 @ ( u1_struct_0 @ ( k9_yellow_6 @ X47 @ X46 ) ) )
      | ~ ( l1_pre_topc @ X47 )
      | ~ ( v2_pre_topc @ X47 )
      | ( v2_struct_0 @ X47 ) ) ),
    inference(cnf,[status(esa)],[t21_waybel_9])).

thf('61',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( m1_connsp_2 @ sk_D @ sk_A @ sk_B_1 )
    | ~ ( m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_connsp_2 @ sk_D @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['61','62','63','64'])).

thf('66',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    m1_connsp_2 @ sk_D @ sk_A @ sk_B_1 ),
    inference(clc,[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( m1_connsp_2 @ X0 @ sk_A @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['18','19'])).

thf('69',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['12','20'])).

thf(dt_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( m1_subset_1 @ ( k4_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('71',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ X24 ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ X24 ) )
      | ( m1_subset_1 @ ( k4_subset_1 @ X24 @ X23 @ X25 ) @ ( k1_zfmisc_1 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k4_subset_1])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    m1_subset_1 @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['69','72'])).

thf('74',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('75',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['12','20'])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('76',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ X27 ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ X27 ) )
      | ( ( k4_subset_1 @ X27 @ X26 @ X28 )
        = ( k2_xboole_0 @ X26 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('77',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X18 @ X19 ) )
      = ( k2_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('78',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ X27 ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ X27 ) )
      | ( ( k4_subset_1 @ X27 @ X26 @ X28 )
        = ( k3_tarski @ ( k2_tarski @ X26 @ X28 ) ) ) ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ X0 )
        = ( k3_tarski @ ( k2_tarski @ sk_C @ X0 ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['75','78'])).

thf('80',plain,
    ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ sk_D )
    = ( k3_tarski @ ( k2_tarski @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['74','79'])).

thf('81',plain,(
    m1_subset_1 @ ( k3_tarski @ ( k2_tarski @ sk_C @ sk_D ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['73','80'])).

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

thf('82',plain,(
    ! [X43: $i,X44: $i,X45: $i] :
      ( ~ ( m1_subset_1 @ X43 @ ( u1_struct_0 @ X44 ) )
      | ~ ( r2_hidden @ X43 @ X45 )
      | ~ ( v3_pre_topc @ X45 @ X44 )
      | ( r2_hidden @ X45 @ ( u1_struct_0 @ ( k9_yellow_6 @ X44 @ X43 ) ) )
      | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X44 ) ) )
      | ~ ( l1_pre_topc @ X44 )
      | ~ ( v2_pre_topc @ X44 )
      | ( v2_struct_0 @ X44 ) ) ),
    inference(cnf,[status(esa)],[t39_yellow_6])).

thf('83',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( r2_hidden @ ( k3_tarski @ ( k2_tarski @ sk_C @ sk_D ) ) @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ X0 ) ) )
      | ~ ( v3_pre_topc @ ( k3_tarski @ ( k2_tarski @ sk_C @ sk_D ) ) @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( k3_tarski @ ( k2_tarski @ sk_C @ sk_D ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ ( k3_tarski @ ( k2_tarski @ sk_C @ sk_D ) ) @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ X0 ) ) )
      | ~ ( v3_pre_topc @ ( k3_tarski @ ( k2_tarski @ sk_C @ sk_D ) ) @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( k3_tarski @ ( k2_tarski @ sk_C @ sk_D ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['83','84','85'])).

thf('87',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('88',plain,(
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

thf('89',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X20 @ X21 )
      | ( r2_hidden @ X20 @ X21 )
      | ( v1_xboole_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('90',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B_1 ) ) )
    | ( r2_hidden @ sk_C @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,(
    ! [X43: $i,X44: $i,X45: $i] :
      ( ~ ( m1_subset_1 @ X43 @ ( u1_struct_0 @ X44 ) )
      | ~ ( r2_hidden @ X45 @ ( u1_struct_0 @ ( k9_yellow_6 @ X44 @ X43 ) ) )
      | ( v3_pre_topc @ X45 @ X44 )
      | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X44 ) ) )
      | ~ ( l1_pre_topc @ X44 )
      | ~ ( v2_pre_topc @ X44 )
      | ( v2_struct_0 @ X44 ) ) ),
    inference(cnf,[status(esa)],[t39_yellow_6])).

thf('92',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B_1 ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v3_pre_topc @ sk_C @ sk_A )
    | ~ ( m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B_1 ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v3_pre_topc @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['92','93','94','95'])).

thf('97',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['12','20'])).

thf('98',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B_1 ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v3_pre_topc @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['96','97'])).

thf('99',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,
    ( ( v3_pre_topc @ sk_C @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B_1 ) ) ) ),
    inference(clc,[status(thm)],['98','99'])).

thf('101',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X22 @ X21 )
      | ( v1_xboole_0 @ X22 )
      | ~ ( v1_xboole_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('103',plain,
    ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B_1 ) ) )
    | ( v1_xboole_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,
    ( ( v3_pre_topc @ sk_C @ sk_A )
    | ( v1_xboole_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['100','103'])).

thf('105',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['12','20'])).

thf(fc7_tops_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( v3_pre_topc @ B @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
        & ( v3_pre_topc @ C @ A )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v3_pre_topc @ ( k2_xboole_0 @ B @ C ) @ A ) ) )).

thf('106',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X35 ) ) )
      | ~ ( v3_pre_topc @ X34 @ X35 )
      | ~ ( l1_pre_topc @ X35 )
      | ~ ( v2_pre_topc @ X35 )
      | ~ ( v3_pre_topc @ X36 @ X35 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X35 ) ) )
      | ( v3_pre_topc @ ( k2_xboole_0 @ X34 @ X36 ) @ X35 ) ) ),
    inference(cnf,[status(esa)],[fc7_tops_1])).

thf('107',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X18 @ X19 ) )
      = ( k2_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('108',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X35 ) ) )
      | ~ ( v3_pre_topc @ X34 @ X35 )
      | ~ ( l1_pre_topc @ X35 )
      | ~ ( v2_pre_topc @ X35 )
      | ~ ( v3_pre_topc @ X36 @ X35 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X35 ) ) )
      | ( v3_pre_topc @ ( k3_tarski @ ( k2_tarski @ X34 @ X36 ) ) @ X35 ) ) ),
    inference(demod,[status(thm)],['106','107'])).

thf('109',plain,(
    ! [X0: $i] :
      ( ( v3_pre_topc @ ( k3_tarski @ ( k2_tarski @ sk_C @ X0 ) ) @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v3_pre_topc @ X0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v3_pre_topc @ sk_C @ sk_A ) ) ),
    inference('sup-',[status(thm)],['105','108'])).

thf('110',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,(
    ! [X0: $i] :
      ( ( v3_pre_topc @ ( k3_tarski @ ( k2_tarski @ sk_C @ X0 ) ) @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v3_pre_topc @ X0 @ sk_A )
      | ~ ( v3_pre_topc @ sk_C @ sk_A ) ) ),
    inference(demod,[status(thm)],['109','110','111'])).

thf('113',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_C )
      | ~ ( v3_pre_topc @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v3_pre_topc @ ( k3_tarski @ ( k2_tarski @ sk_C @ X0 ) ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['104','112'])).

thf('114',plain,
    ( ( v3_pre_topc @ ( k3_tarski @ ( k2_tarski @ sk_C @ sk_D ) ) @ sk_A )
    | ~ ( v3_pre_topc @ sk_D @ sk_A )
    | ( v1_xboole_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['87','113'])).

thf('115',plain,(
    m1_subset_1 @ sk_D @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X20 @ X21 )
      | ( r2_hidden @ X20 @ X21 )
      | ( v1_xboole_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('117',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B_1 ) ) )
    | ( r2_hidden @ sk_D @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['115','116'])).

thf('118',plain,(
    ! [X43: $i,X44: $i,X45: $i] :
      ( ~ ( m1_subset_1 @ X43 @ ( u1_struct_0 @ X44 ) )
      | ~ ( r2_hidden @ X45 @ ( u1_struct_0 @ ( k9_yellow_6 @ X44 @ X43 ) ) )
      | ( v3_pre_topc @ X45 @ X44 )
      | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X44 ) ) )
      | ~ ( l1_pre_topc @ X44 )
      | ~ ( v2_pre_topc @ X44 )
      | ( v2_struct_0 @ X44 ) ) ),
    inference(cnf,[status(esa)],[t39_yellow_6])).

thf('119',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B_1 ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v3_pre_topc @ sk_D @ sk_A )
    | ~ ( m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['117','118'])).

thf('120',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('121',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B_1 ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v3_pre_topc @ sk_D @ sk_A ) ),
    inference(demod,[status(thm)],['119','120','121','122'])).

thf('124',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('125',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B_1 ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v3_pre_topc @ sk_D @ sk_A ) ),
    inference(demod,[status(thm)],['123','124'])).

thf('126',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,
    ( ( v3_pre_topc @ sk_D @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B_1 ) ) ) ),
    inference(clc,[status(thm)],['125','126'])).

thf('128',plain,
    ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B_1 ) ) )
    | ( v1_xboole_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('129',plain,
    ( ( v3_pre_topc @ sk_D @ sk_A )
    | ( v1_xboole_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['127','128'])).

thf('130',plain,
    ( ( v1_xboole_0 @ sk_C )
    | ( v3_pre_topc @ ( k3_tarski @ ( k2_tarski @ sk_C @ sk_D ) ) @ sk_A ) ),
    inference(clc,[status(thm)],['114','129'])).

thf('131',plain,(
    r2_hidden @ sk_B_1 @ sk_C ),
    inference(clc,[status(thm)],['29','30'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('132',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('133',plain,(
    ~ ( v1_xboole_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['131','132'])).

thf('134',plain,(
    v3_pre_topc @ ( k3_tarski @ ( k2_tarski @ sk_C @ sk_D ) ) @ sk_A ),
    inference(clc,[status(thm)],['130','133'])).

thf('135',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ ( k3_tarski @ ( k2_tarski @ sk_C @ sk_D ) ) @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ X0 ) ) )
      | ~ ( r2_hidden @ X0 @ ( k3_tarski @ ( k2_tarski @ sk_C @ sk_D ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['86','134'])).

thf('136',plain,
    ( ~ ( m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( k3_tarski @ ( k2_tarski @ sk_C @ sk_D ) ) @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B_1 ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['58','135'])).

thf('137',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('138',plain,
    ( ( r2_hidden @ ( k3_tarski @ ( k2_tarski @ sk_C @ sk_D ) ) @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B_1 ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['136','137'])).

thf('139',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('140',plain,(
    r2_hidden @ ( k3_tarski @ ( k2_tarski @ sk_C @ sk_D ) ) @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['138','139'])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('141',plain,(
    ! [X29: $i,X30: $i] :
      ( ( m1_subset_1 @ X29 @ X30 )
      | ~ ( r2_hidden @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('142',plain,(
    m1_subset_1 @ ( k3_tarski @ ( k2_tarski @ sk_C @ sk_D ) ) @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['140','141'])).

thf('143',plain,(
    $false ),
    inference(demod,[status(thm)],['2','142'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.b6rnQgMz6a
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:42:40 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 5.50/5.70  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 5.50/5.70  % Solved by: fo/fo7.sh
% 5.50/5.70  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 5.50/5.70  % done 10755 iterations in 5.245s
% 5.50/5.70  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 5.50/5.70  % SZS output start Refutation
% 5.50/5.70  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 5.50/5.70  thf(m1_connsp_2_type, type, m1_connsp_2: $i > $i > $i > $o).
% 5.50/5.70  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 5.50/5.70  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 5.50/5.70  thf(sk_A_type, type, sk_A: $i).
% 5.50/5.70  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 5.50/5.70  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 5.50/5.70  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 5.50/5.70  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 5.50/5.70  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 5.50/5.70  thf(sk_B_1_type, type, sk_B_1: $i).
% 5.50/5.70  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 5.50/5.70  thf(k9_yellow_6_type, type, k9_yellow_6: $i > $i > $i).
% 5.50/5.70  thf(sk_D_type, type, sk_D: $i).
% 5.50/5.70  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 5.50/5.70  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 5.50/5.70  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 5.50/5.70  thf(sk_C_type, type, sk_C: $i).
% 5.50/5.70  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 5.50/5.70  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 5.50/5.70  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 5.50/5.70  thf(t23_waybel_9, conjecture,
% 5.50/5.70    (![A:$i]:
% 5.50/5.70     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 5.50/5.70       ( ![B:$i]:
% 5.50/5.70         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 5.50/5.70           ( ![C:$i]:
% 5.50/5.70             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ ( k9_yellow_6 @ A @ B ) ) ) =>
% 5.50/5.70               ( ![D:$i]:
% 5.50/5.70                 ( ( m1_subset_1 @
% 5.50/5.70                     D @ ( u1_struct_0 @ ( k9_yellow_6 @ A @ B ) ) ) =>
% 5.50/5.70                   ( m1_subset_1 @
% 5.50/5.70                     ( k2_xboole_0 @ C @ D ) @ 
% 5.50/5.70                     ( u1_struct_0 @ ( k9_yellow_6 @ A @ B ) ) ) ) ) ) ) ) ) ))).
% 5.50/5.70  thf(zf_stmt_0, negated_conjecture,
% 5.50/5.70    (~( ![A:$i]:
% 5.50/5.70        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 5.50/5.70            ( l1_pre_topc @ A ) ) =>
% 5.50/5.70          ( ![B:$i]:
% 5.50/5.70            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 5.50/5.70              ( ![C:$i]:
% 5.50/5.70                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ ( k9_yellow_6 @ A @ B ) ) ) =>
% 5.50/5.70                  ( ![D:$i]:
% 5.50/5.70                    ( ( m1_subset_1 @
% 5.50/5.70                        D @ ( u1_struct_0 @ ( k9_yellow_6 @ A @ B ) ) ) =>
% 5.50/5.70                      ( m1_subset_1 @
% 5.50/5.70                        ( k2_xboole_0 @ C @ D ) @ 
% 5.50/5.70                        ( u1_struct_0 @ ( k9_yellow_6 @ A @ B ) ) ) ) ) ) ) ) ) ) )),
% 5.50/5.70    inference('cnf.neg', [status(esa)], [t23_waybel_9])).
% 5.50/5.70  thf('0', plain,
% 5.50/5.70      (~ (m1_subset_1 @ (k2_xboole_0 @ sk_C @ sk_D) @ 
% 5.50/5.70          (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B_1)))),
% 5.50/5.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.50/5.70  thf(l51_zfmisc_1, axiom,
% 5.50/5.70    (![A:$i,B:$i]:
% 5.50/5.70     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 5.50/5.70  thf('1', plain,
% 5.50/5.70      (![X18 : $i, X19 : $i]:
% 5.50/5.70         ((k3_tarski @ (k2_tarski @ X18 @ X19)) = (k2_xboole_0 @ X18 @ X19))),
% 5.50/5.70      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 5.50/5.70  thf('2', plain,
% 5.50/5.70      (~ (m1_subset_1 @ (k3_tarski @ (k2_tarski @ sk_C @ sk_D)) @ 
% 5.50/5.70          (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B_1)))),
% 5.50/5.70      inference('demod', [status(thm)], ['0', '1'])).
% 5.50/5.70  thf('3', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 5.50/5.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.50/5.70  thf('4', plain,
% 5.50/5.70      ((m1_subset_1 @ sk_C @ (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B_1)))),
% 5.50/5.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.50/5.70  thf(t21_waybel_9, axiom,
% 5.50/5.70    (![A:$i]:
% 5.50/5.70     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 5.50/5.70       ( ![B:$i]:
% 5.50/5.70         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 5.50/5.70           ( ![C:$i]:
% 5.50/5.70             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ ( k9_yellow_6 @ A @ B ) ) ) =>
% 5.50/5.70               ( m1_connsp_2 @ C @ A @ B ) ) ) ) ) ))).
% 5.50/5.70  thf('5', plain,
% 5.50/5.70      (![X46 : $i, X47 : $i, X48 : $i]:
% 5.50/5.70         (~ (m1_subset_1 @ X46 @ (u1_struct_0 @ X47))
% 5.50/5.70          | (m1_connsp_2 @ X48 @ X47 @ X46)
% 5.50/5.70          | ~ (m1_subset_1 @ X48 @ (u1_struct_0 @ (k9_yellow_6 @ X47 @ X46)))
% 5.50/5.70          | ~ (l1_pre_topc @ X47)
% 5.50/5.70          | ~ (v2_pre_topc @ X47)
% 5.50/5.70          | (v2_struct_0 @ X47))),
% 5.50/5.70      inference('cnf', [status(esa)], [t21_waybel_9])).
% 5.50/5.70  thf('6', plain,
% 5.50/5.70      (((v2_struct_0 @ sk_A)
% 5.50/5.70        | ~ (v2_pre_topc @ sk_A)
% 5.50/5.70        | ~ (l1_pre_topc @ sk_A)
% 5.50/5.70        | (m1_connsp_2 @ sk_C @ sk_A @ sk_B_1)
% 5.50/5.70        | ~ (m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)))),
% 5.50/5.70      inference('sup-', [status(thm)], ['4', '5'])).
% 5.50/5.70  thf('7', plain, ((v2_pre_topc @ sk_A)),
% 5.50/5.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.50/5.70  thf('8', plain, ((l1_pre_topc @ sk_A)),
% 5.50/5.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.50/5.70  thf('9', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 5.50/5.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.50/5.70  thf('10', plain,
% 5.50/5.70      (((v2_struct_0 @ sk_A) | (m1_connsp_2 @ sk_C @ sk_A @ sk_B_1))),
% 5.50/5.70      inference('demod', [status(thm)], ['6', '7', '8', '9'])).
% 5.50/5.70  thf('11', plain, (~ (v2_struct_0 @ sk_A)),
% 5.50/5.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.50/5.70  thf('12', plain, ((m1_connsp_2 @ sk_C @ sk_A @ sk_B_1)),
% 5.50/5.70      inference('clc', [status(thm)], ['10', '11'])).
% 5.50/5.70  thf('13', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 5.50/5.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.50/5.70  thf(dt_m1_connsp_2, axiom,
% 5.50/5.70    (![A:$i,B:$i]:
% 5.50/5.70     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 5.50/5.70         ( l1_pre_topc @ A ) & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) =>
% 5.50/5.70       ( ![C:$i]:
% 5.50/5.70         ( ( m1_connsp_2 @ C @ A @ B ) =>
% 5.50/5.70           ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 5.50/5.70  thf('14', plain,
% 5.50/5.70      (![X37 : $i, X38 : $i, X39 : $i]:
% 5.50/5.70         (~ (l1_pre_topc @ X37)
% 5.50/5.70          | ~ (v2_pre_topc @ X37)
% 5.50/5.70          | (v2_struct_0 @ X37)
% 5.50/5.70          | ~ (m1_subset_1 @ X38 @ (u1_struct_0 @ X37))
% 5.50/5.70          | (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (u1_struct_0 @ X37)))
% 5.50/5.70          | ~ (m1_connsp_2 @ X39 @ X37 @ X38))),
% 5.50/5.70      inference('cnf', [status(esa)], [dt_m1_connsp_2])).
% 5.50/5.70  thf('15', plain,
% 5.50/5.70      (![X0 : $i]:
% 5.50/5.70         (~ (m1_connsp_2 @ X0 @ sk_A @ sk_B_1)
% 5.50/5.70          | (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 5.50/5.70          | (v2_struct_0 @ sk_A)
% 5.50/5.70          | ~ (v2_pre_topc @ sk_A)
% 5.50/5.70          | ~ (l1_pre_topc @ sk_A))),
% 5.50/5.70      inference('sup-', [status(thm)], ['13', '14'])).
% 5.50/5.70  thf('16', plain, ((v2_pre_topc @ sk_A)),
% 5.50/5.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.50/5.70  thf('17', plain, ((l1_pre_topc @ sk_A)),
% 5.50/5.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.50/5.70  thf('18', plain,
% 5.50/5.70      (![X0 : $i]:
% 5.50/5.70         (~ (m1_connsp_2 @ X0 @ sk_A @ sk_B_1)
% 5.50/5.70          | (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 5.50/5.70          | (v2_struct_0 @ sk_A))),
% 5.50/5.70      inference('demod', [status(thm)], ['15', '16', '17'])).
% 5.50/5.70  thf('19', plain, (~ (v2_struct_0 @ sk_A)),
% 5.50/5.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.50/5.70  thf('20', plain,
% 5.50/5.70      (![X0 : $i]:
% 5.50/5.70         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 5.50/5.70          | ~ (m1_connsp_2 @ X0 @ sk_A @ sk_B_1))),
% 5.50/5.70      inference('clc', [status(thm)], ['18', '19'])).
% 5.50/5.70  thf('21', plain,
% 5.50/5.70      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 5.50/5.70      inference('sup-', [status(thm)], ['12', '20'])).
% 5.50/5.70  thf(t6_connsp_2, axiom,
% 5.50/5.70    (![A:$i]:
% 5.50/5.70     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 5.50/5.70       ( ![B:$i]:
% 5.50/5.70         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 5.50/5.70           ( ![C:$i]:
% 5.50/5.70             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 5.50/5.70               ( ( m1_connsp_2 @ B @ A @ C ) => ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 5.50/5.70  thf('22', plain,
% 5.50/5.70      (![X40 : $i, X41 : $i, X42 : $i]:
% 5.50/5.70         (~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (u1_struct_0 @ X41)))
% 5.50/5.70          | ~ (m1_connsp_2 @ X40 @ X41 @ X42)
% 5.50/5.70          | (r2_hidden @ X42 @ X40)
% 5.50/5.70          | ~ (m1_subset_1 @ X42 @ (u1_struct_0 @ X41))
% 5.50/5.70          | ~ (l1_pre_topc @ X41)
% 5.50/5.70          | ~ (v2_pre_topc @ X41)
% 5.50/5.70          | (v2_struct_0 @ X41))),
% 5.50/5.70      inference('cnf', [status(esa)], [t6_connsp_2])).
% 5.50/5.70  thf('23', plain,
% 5.50/5.70      (![X0 : $i]:
% 5.50/5.70         ((v2_struct_0 @ sk_A)
% 5.50/5.70          | ~ (v2_pre_topc @ sk_A)
% 5.50/5.70          | ~ (l1_pre_topc @ sk_A)
% 5.50/5.70          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 5.50/5.70          | (r2_hidden @ X0 @ sk_C)
% 5.50/5.70          | ~ (m1_connsp_2 @ sk_C @ sk_A @ X0))),
% 5.50/5.70      inference('sup-', [status(thm)], ['21', '22'])).
% 5.50/5.70  thf('24', plain, ((v2_pre_topc @ sk_A)),
% 5.50/5.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.50/5.70  thf('25', plain, ((l1_pre_topc @ sk_A)),
% 5.50/5.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.50/5.70  thf('26', plain,
% 5.50/5.70      (![X0 : $i]:
% 5.50/5.70         ((v2_struct_0 @ sk_A)
% 5.50/5.70          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 5.50/5.70          | (r2_hidden @ X0 @ sk_C)
% 5.50/5.70          | ~ (m1_connsp_2 @ sk_C @ sk_A @ X0))),
% 5.50/5.70      inference('demod', [status(thm)], ['23', '24', '25'])).
% 5.50/5.70  thf('27', plain,
% 5.50/5.70      ((~ (m1_connsp_2 @ sk_C @ sk_A @ sk_B_1)
% 5.50/5.70        | (r2_hidden @ sk_B_1 @ sk_C)
% 5.50/5.70        | (v2_struct_0 @ sk_A))),
% 5.50/5.70      inference('sup-', [status(thm)], ['3', '26'])).
% 5.50/5.70  thf('28', plain, ((m1_connsp_2 @ sk_C @ sk_A @ sk_B_1)),
% 5.50/5.70      inference('clc', [status(thm)], ['10', '11'])).
% 5.50/5.70  thf('29', plain, (((r2_hidden @ sk_B_1 @ sk_C) | (v2_struct_0 @ sk_A))),
% 5.50/5.70      inference('demod', [status(thm)], ['27', '28'])).
% 5.50/5.70  thf('30', plain, (~ (v2_struct_0 @ sk_A)),
% 5.50/5.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.50/5.70  thf('31', plain, ((r2_hidden @ sk_B_1 @ sk_C)),
% 5.50/5.70      inference('clc', [status(thm)], ['29', '30'])).
% 5.50/5.70  thf(l22_zfmisc_1, axiom,
% 5.50/5.70    (![A:$i,B:$i]:
% 5.50/5.70     ( ( r2_hidden @ A @ B ) =>
% 5.50/5.70       ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( B ) ) ))).
% 5.50/5.70  thf('32', plain,
% 5.50/5.70      (![X16 : $i, X17 : $i]:
% 5.50/5.70         (((k2_xboole_0 @ (k1_tarski @ X17) @ X16) = (X16))
% 5.50/5.70          | ~ (r2_hidden @ X17 @ X16))),
% 5.50/5.70      inference('cnf', [status(esa)], [l22_zfmisc_1])).
% 5.50/5.70  thf('33', plain,
% 5.50/5.70      (![X18 : $i, X19 : $i]:
% 5.50/5.70         ((k3_tarski @ (k2_tarski @ X18 @ X19)) = (k2_xboole_0 @ X18 @ X19))),
% 5.50/5.70      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 5.50/5.70  thf('34', plain,
% 5.50/5.70      (![X16 : $i, X17 : $i]:
% 5.50/5.70         (((k3_tarski @ (k2_tarski @ (k1_tarski @ X17) @ X16)) = (X16))
% 5.50/5.70          | ~ (r2_hidden @ X17 @ X16))),
% 5.50/5.70      inference('demod', [status(thm)], ['32', '33'])).
% 5.50/5.70  thf('35', plain,
% 5.50/5.70      (((k3_tarski @ (k2_tarski @ (k1_tarski @ sk_B_1) @ sk_C)) = (sk_C))),
% 5.50/5.70      inference('sup-', [status(thm)], ['31', '34'])).
% 5.50/5.70  thf(t7_xboole_1, axiom,
% 5.50/5.70    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 5.50/5.70  thf('36', plain,
% 5.50/5.70      (![X11 : $i, X12 : $i]: (r1_tarski @ X11 @ (k2_xboole_0 @ X11 @ X12))),
% 5.50/5.70      inference('cnf', [status(esa)], [t7_xboole_1])).
% 5.50/5.70  thf('37', plain,
% 5.50/5.70      (![X18 : $i, X19 : $i]:
% 5.50/5.70         ((k3_tarski @ (k2_tarski @ X18 @ X19)) = (k2_xboole_0 @ X18 @ X19))),
% 5.50/5.70      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 5.50/5.70  thf('38', plain,
% 5.50/5.70      (![X11 : $i, X12 : $i]:
% 5.50/5.70         (r1_tarski @ X11 @ (k3_tarski @ (k2_tarski @ X11 @ X12)))),
% 5.50/5.70      inference('demod', [status(thm)], ['36', '37'])).
% 5.50/5.70  thf(t11_xboole_1, axiom,
% 5.50/5.70    (![A:$i,B:$i,C:$i]:
% 5.50/5.70     ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C ) => ( r1_tarski @ A @ C ) ))).
% 5.50/5.70  thf('39', plain,
% 5.50/5.70      (![X6 : $i, X7 : $i, X8 : $i]:
% 5.50/5.70         ((r1_tarski @ X6 @ X7) | ~ (r1_tarski @ (k2_xboole_0 @ X6 @ X8) @ X7))),
% 5.50/5.70      inference('cnf', [status(esa)], [t11_xboole_1])).
% 5.50/5.70  thf('40', plain,
% 5.50/5.70      (![X18 : $i, X19 : $i]:
% 5.50/5.70         ((k3_tarski @ (k2_tarski @ X18 @ X19)) = (k2_xboole_0 @ X18 @ X19))),
% 5.50/5.70      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 5.50/5.70  thf('41', plain,
% 5.50/5.70      (![X6 : $i, X7 : $i, X8 : $i]:
% 5.50/5.70         ((r1_tarski @ X6 @ X7)
% 5.50/5.70          | ~ (r1_tarski @ (k3_tarski @ (k2_tarski @ X6 @ X8)) @ X7))),
% 5.50/5.70      inference('demod', [status(thm)], ['39', '40'])).
% 5.50/5.70  thf('42', plain,
% 5.50/5.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.50/5.70         (r1_tarski @ X2 @ 
% 5.50/5.70          (k3_tarski @ (k2_tarski @ (k3_tarski @ (k2_tarski @ X2 @ X1)) @ X0)))),
% 5.50/5.70      inference('sup-', [status(thm)], ['38', '41'])).
% 5.50/5.70  thf('43', plain,
% 5.50/5.70      (![X0 : $i]:
% 5.50/5.70         (r1_tarski @ (k1_tarski @ sk_B_1) @ 
% 5.50/5.70          (k3_tarski @ (k2_tarski @ sk_C @ X0)))),
% 5.50/5.70      inference('sup+', [status(thm)], ['35', '42'])).
% 5.50/5.70  thf(t12_xboole_1, axiom,
% 5.50/5.70    (![A:$i,B:$i]:
% 5.50/5.70     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 5.50/5.70  thf('44', plain,
% 5.50/5.70      (![X9 : $i, X10 : $i]:
% 5.50/5.70         (((k2_xboole_0 @ X10 @ X9) = (X9)) | ~ (r1_tarski @ X10 @ X9))),
% 5.50/5.70      inference('cnf', [status(esa)], [t12_xboole_1])).
% 5.50/5.70  thf('45', plain,
% 5.50/5.70      (![X18 : $i, X19 : $i]:
% 5.50/5.70         ((k3_tarski @ (k2_tarski @ X18 @ X19)) = (k2_xboole_0 @ X18 @ X19))),
% 5.50/5.70      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 5.50/5.70  thf('46', plain,
% 5.50/5.70      (![X9 : $i, X10 : $i]:
% 5.50/5.70         (((k3_tarski @ (k2_tarski @ X10 @ X9)) = (X9))
% 5.50/5.70          | ~ (r1_tarski @ X10 @ X9))),
% 5.50/5.70      inference('demod', [status(thm)], ['44', '45'])).
% 5.50/5.70  thf('47', plain,
% 5.50/5.70      (![X0 : $i]:
% 5.50/5.70         ((k3_tarski @ 
% 5.50/5.70           (k2_tarski @ (k1_tarski @ sk_B_1) @ 
% 5.50/5.70            (k3_tarski @ (k2_tarski @ sk_C @ X0))))
% 5.50/5.70           = (k3_tarski @ (k2_tarski @ sk_C @ X0)))),
% 5.50/5.70      inference('sup-', [status(thm)], ['43', '46'])).
% 5.50/5.70  thf('48', plain,
% 5.50/5.70      (![X11 : $i, X12 : $i]:
% 5.50/5.70         (r1_tarski @ X11 @ (k3_tarski @ (k2_tarski @ X11 @ X12)))),
% 5.50/5.70      inference('demod', [status(thm)], ['36', '37'])).
% 5.50/5.70  thf('49', plain,
% 5.50/5.70      (![X9 : $i, X10 : $i]:
% 5.50/5.70         (((k3_tarski @ (k2_tarski @ X10 @ X9)) = (X9))
% 5.50/5.70          | ~ (r1_tarski @ X10 @ X9))),
% 5.50/5.70      inference('demod', [status(thm)], ['44', '45'])).
% 5.50/5.70  thf('50', plain,
% 5.50/5.70      (![X0 : $i, X1 : $i]:
% 5.50/5.70         ((k3_tarski @ (k2_tarski @ X1 @ (k3_tarski @ (k2_tarski @ X1 @ X0))))
% 5.50/5.70           = (k3_tarski @ (k2_tarski @ X1 @ X0)))),
% 5.50/5.70      inference('sup-', [status(thm)], ['48', '49'])).
% 5.50/5.70  thf(l20_zfmisc_1, axiom,
% 5.50/5.70    (![A:$i,B:$i]:
% 5.50/5.70     ( ( r1_tarski @ ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) @ B ) =>
% 5.50/5.70       ( r2_hidden @ A @ B ) ))).
% 5.50/5.70  thf('51', plain,
% 5.50/5.70      (![X14 : $i, X15 : $i]:
% 5.50/5.70         ((r2_hidden @ X14 @ X15)
% 5.50/5.70          | ~ (r1_tarski @ (k2_xboole_0 @ (k1_tarski @ X14) @ X15) @ X15))),
% 5.50/5.70      inference('cnf', [status(esa)], [l20_zfmisc_1])).
% 5.50/5.70  thf('52', plain,
% 5.50/5.70      (![X18 : $i, X19 : $i]:
% 5.50/5.70         ((k3_tarski @ (k2_tarski @ X18 @ X19)) = (k2_xboole_0 @ X18 @ X19))),
% 5.50/5.70      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 5.50/5.70  thf('53', plain,
% 5.50/5.70      (![X14 : $i, X15 : $i]:
% 5.50/5.70         ((r2_hidden @ X14 @ X15)
% 5.50/5.70          | ~ (r1_tarski @ 
% 5.50/5.70               (k3_tarski @ (k2_tarski @ (k1_tarski @ X14) @ X15)) @ X15))),
% 5.50/5.70      inference('demod', [status(thm)], ['51', '52'])).
% 5.50/5.70  thf('54', plain,
% 5.50/5.70      (![X0 : $i, X1 : $i]:
% 5.50/5.70         (~ (r1_tarski @ (k3_tarski @ (k2_tarski @ (k1_tarski @ X1) @ X0)) @ 
% 5.50/5.70             (k3_tarski @ (k2_tarski @ (k1_tarski @ X1) @ X0)))
% 5.50/5.70          | (r2_hidden @ X1 @ (k3_tarski @ (k2_tarski @ (k1_tarski @ X1) @ X0))))),
% 5.50/5.70      inference('sup-', [status(thm)], ['50', '53'])).
% 5.50/5.70  thf(d10_xboole_0, axiom,
% 5.50/5.70    (![A:$i,B:$i]:
% 5.50/5.70     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 5.50/5.70  thf('55', plain,
% 5.50/5.70      (![X3 : $i, X4 : $i]: ((r1_tarski @ X3 @ X4) | ((X3) != (X4)))),
% 5.50/5.70      inference('cnf', [status(esa)], [d10_xboole_0])).
% 5.50/5.70  thf('56', plain, (![X4 : $i]: (r1_tarski @ X4 @ X4)),
% 5.50/5.70      inference('simplify', [status(thm)], ['55'])).
% 5.50/5.70  thf('57', plain,
% 5.50/5.70      (![X0 : $i, X1 : $i]:
% 5.50/5.70         (r2_hidden @ X1 @ (k3_tarski @ (k2_tarski @ (k1_tarski @ X1) @ X0)))),
% 5.50/5.70      inference('demod', [status(thm)], ['54', '56'])).
% 5.50/5.70  thf('58', plain,
% 5.50/5.70      (![X0 : $i]: (r2_hidden @ sk_B_1 @ (k3_tarski @ (k2_tarski @ sk_C @ X0)))),
% 5.50/5.70      inference('sup+', [status(thm)], ['47', '57'])).
% 5.50/5.70  thf('59', plain,
% 5.50/5.70      ((m1_subset_1 @ sk_D @ (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B_1)))),
% 5.50/5.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.50/5.70  thf('60', plain,
% 5.50/5.70      (![X46 : $i, X47 : $i, X48 : $i]:
% 5.50/5.70         (~ (m1_subset_1 @ X46 @ (u1_struct_0 @ X47))
% 5.50/5.70          | (m1_connsp_2 @ X48 @ X47 @ X46)
% 5.50/5.70          | ~ (m1_subset_1 @ X48 @ (u1_struct_0 @ (k9_yellow_6 @ X47 @ X46)))
% 5.50/5.70          | ~ (l1_pre_topc @ X47)
% 5.50/5.70          | ~ (v2_pre_topc @ X47)
% 5.50/5.70          | (v2_struct_0 @ X47))),
% 5.50/5.70      inference('cnf', [status(esa)], [t21_waybel_9])).
% 5.50/5.70  thf('61', plain,
% 5.50/5.70      (((v2_struct_0 @ sk_A)
% 5.50/5.70        | ~ (v2_pre_topc @ sk_A)
% 5.50/5.70        | ~ (l1_pre_topc @ sk_A)
% 5.50/5.70        | (m1_connsp_2 @ sk_D @ sk_A @ sk_B_1)
% 5.50/5.70        | ~ (m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)))),
% 5.50/5.70      inference('sup-', [status(thm)], ['59', '60'])).
% 5.50/5.70  thf('62', plain, ((v2_pre_topc @ sk_A)),
% 5.50/5.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.50/5.70  thf('63', plain, ((l1_pre_topc @ sk_A)),
% 5.50/5.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.50/5.70  thf('64', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 5.50/5.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.50/5.70  thf('65', plain,
% 5.50/5.70      (((v2_struct_0 @ sk_A) | (m1_connsp_2 @ sk_D @ sk_A @ sk_B_1))),
% 5.50/5.70      inference('demod', [status(thm)], ['61', '62', '63', '64'])).
% 5.50/5.70  thf('66', plain, (~ (v2_struct_0 @ sk_A)),
% 5.50/5.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.50/5.70  thf('67', plain, ((m1_connsp_2 @ sk_D @ sk_A @ sk_B_1)),
% 5.50/5.70      inference('clc', [status(thm)], ['65', '66'])).
% 5.50/5.70  thf('68', plain,
% 5.50/5.70      (![X0 : $i]:
% 5.50/5.70         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 5.50/5.70          | ~ (m1_connsp_2 @ X0 @ sk_A @ sk_B_1))),
% 5.50/5.70      inference('clc', [status(thm)], ['18', '19'])).
% 5.50/5.70  thf('69', plain,
% 5.50/5.70      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 5.50/5.70      inference('sup-', [status(thm)], ['67', '68'])).
% 5.50/5.70  thf('70', plain,
% 5.50/5.70      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 5.50/5.70      inference('sup-', [status(thm)], ['12', '20'])).
% 5.50/5.70  thf(dt_k4_subset_1, axiom,
% 5.50/5.70    (![A:$i,B:$i,C:$i]:
% 5.50/5.70     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 5.50/5.70         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 5.50/5.70       ( m1_subset_1 @ ( k4_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 5.50/5.70  thf('71', plain,
% 5.50/5.70      (![X23 : $i, X24 : $i, X25 : $i]:
% 5.50/5.70         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ X24))
% 5.50/5.70          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ X24))
% 5.50/5.70          | (m1_subset_1 @ (k4_subset_1 @ X24 @ X23 @ X25) @ 
% 5.50/5.70             (k1_zfmisc_1 @ X24)))),
% 5.50/5.70      inference('cnf', [status(esa)], [dt_k4_subset_1])).
% 5.50/5.70  thf('72', plain,
% 5.50/5.70      (![X0 : $i]:
% 5.50/5.70         ((m1_subset_1 @ (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ X0) @ 
% 5.50/5.70           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 5.50/5.70          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 5.50/5.70      inference('sup-', [status(thm)], ['70', '71'])).
% 5.50/5.70  thf('73', plain,
% 5.50/5.70      ((m1_subset_1 @ (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ sk_D) @ 
% 5.50/5.70        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 5.50/5.70      inference('sup-', [status(thm)], ['69', '72'])).
% 5.50/5.70  thf('74', plain,
% 5.50/5.70      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 5.50/5.70      inference('sup-', [status(thm)], ['67', '68'])).
% 5.50/5.70  thf('75', plain,
% 5.50/5.70      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 5.50/5.70      inference('sup-', [status(thm)], ['12', '20'])).
% 5.50/5.70  thf(redefinition_k4_subset_1, axiom,
% 5.50/5.70    (![A:$i,B:$i,C:$i]:
% 5.50/5.70     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 5.50/5.70         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 5.50/5.70       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 5.50/5.70  thf('76', plain,
% 5.50/5.70      (![X26 : $i, X27 : $i, X28 : $i]:
% 5.50/5.70         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ X27))
% 5.50/5.70          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ X27))
% 5.50/5.70          | ((k4_subset_1 @ X27 @ X26 @ X28) = (k2_xboole_0 @ X26 @ X28)))),
% 5.50/5.70      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 5.50/5.70  thf('77', plain,
% 5.50/5.70      (![X18 : $i, X19 : $i]:
% 5.50/5.70         ((k3_tarski @ (k2_tarski @ X18 @ X19)) = (k2_xboole_0 @ X18 @ X19))),
% 5.50/5.70      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 5.50/5.70  thf('78', plain,
% 5.50/5.70      (![X26 : $i, X27 : $i, X28 : $i]:
% 5.50/5.70         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ X27))
% 5.50/5.70          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ X27))
% 5.50/5.70          | ((k4_subset_1 @ X27 @ X26 @ X28)
% 5.50/5.70              = (k3_tarski @ (k2_tarski @ X26 @ X28))))),
% 5.50/5.70      inference('demod', [status(thm)], ['76', '77'])).
% 5.50/5.70  thf('79', plain,
% 5.50/5.70      (![X0 : $i]:
% 5.50/5.70         (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ X0)
% 5.50/5.70            = (k3_tarski @ (k2_tarski @ sk_C @ X0)))
% 5.50/5.70          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 5.50/5.70      inference('sup-', [status(thm)], ['75', '78'])).
% 5.50/5.70  thf('80', plain,
% 5.50/5.70      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ sk_D)
% 5.50/5.70         = (k3_tarski @ (k2_tarski @ sk_C @ sk_D)))),
% 5.50/5.70      inference('sup-', [status(thm)], ['74', '79'])).
% 5.50/5.70  thf('81', plain,
% 5.50/5.70      ((m1_subset_1 @ (k3_tarski @ (k2_tarski @ sk_C @ sk_D)) @ 
% 5.50/5.70        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 5.50/5.70      inference('demod', [status(thm)], ['73', '80'])).
% 5.50/5.70  thf(t39_yellow_6, axiom,
% 5.50/5.70    (![A:$i]:
% 5.50/5.70     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 5.50/5.70       ( ![B:$i]:
% 5.50/5.70         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 5.50/5.70           ( ![C:$i]:
% 5.50/5.70             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 5.50/5.70               ( ( r2_hidden @ C @ ( u1_struct_0 @ ( k9_yellow_6 @ A @ B ) ) ) <=>
% 5.50/5.70                 ( ( r2_hidden @ B @ C ) & ( v3_pre_topc @ C @ A ) ) ) ) ) ) ) ))).
% 5.50/5.70  thf('82', plain,
% 5.50/5.70      (![X43 : $i, X44 : $i, X45 : $i]:
% 5.50/5.70         (~ (m1_subset_1 @ X43 @ (u1_struct_0 @ X44))
% 5.50/5.70          | ~ (r2_hidden @ X43 @ X45)
% 5.50/5.70          | ~ (v3_pre_topc @ X45 @ X44)
% 5.50/5.70          | (r2_hidden @ X45 @ (u1_struct_0 @ (k9_yellow_6 @ X44 @ X43)))
% 5.50/5.70          | ~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (u1_struct_0 @ X44)))
% 5.50/5.70          | ~ (l1_pre_topc @ X44)
% 5.50/5.70          | ~ (v2_pre_topc @ X44)
% 5.50/5.70          | (v2_struct_0 @ X44))),
% 5.50/5.70      inference('cnf', [status(esa)], [t39_yellow_6])).
% 5.50/5.70  thf('83', plain,
% 5.50/5.70      (![X0 : $i]:
% 5.50/5.70         ((v2_struct_0 @ sk_A)
% 5.50/5.70          | ~ (v2_pre_topc @ sk_A)
% 5.50/5.70          | ~ (l1_pre_topc @ sk_A)
% 5.50/5.70          | (r2_hidden @ (k3_tarski @ (k2_tarski @ sk_C @ sk_D)) @ 
% 5.50/5.70             (u1_struct_0 @ (k9_yellow_6 @ sk_A @ X0)))
% 5.50/5.70          | ~ (v3_pre_topc @ (k3_tarski @ (k2_tarski @ sk_C @ sk_D)) @ sk_A)
% 5.50/5.70          | ~ (r2_hidden @ X0 @ (k3_tarski @ (k2_tarski @ sk_C @ sk_D)))
% 5.50/5.70          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 5.50/5.70      inference('sup-', [status(thm)], ['81', '82'])).
% 5.50/5.70  thf('84', plain, ((v2_pre_topc @ sk_A)),
% 5.50/5.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.50/5.70  thf('85', plain, ((l1_pre_topc @ sk_A)),
% 5.50/5.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.50/5.70  thf('86', plain,
% 5.50/5.70      (![X0 : $i]:
% 5.50/5.70         ((v2_struct_0 @ sk_A)
% 5.50/5.70          | (r2_hidden @ (k3_tarski @ (k2_tarski @ sk_C @ sk_D)) @ 
% 5.50/5.70             (u1_struct_0 @ (k9_yellow_6 @ sk_A @ X0)))
% 5.50/5.70          | ~ (v3_pre_topc @ (k3_tarski @ (k2_tarski @ sk_C @ sk_D)) @ sk_A)
% 5.50/5.70          | ~ (r2_hidden @ X0 @ (k3_tarski @ (k2_tarski @ sk_C @ sk_D)))
% 5.50/5.70          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 5.50/5.70      inference('demod', [status(thm)], ['83', '84', '85'])).
% 5.50/5.70  thf('87', plain,
% 5.50/5.70      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 5.50/5.70      inference('sup-', [status(thm)], ['67', '68'])).
% 5.50/5.70  thf('88', plain,
% 5.50/5.70      ((m1_subset_1 @ sk_C @ (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B_1)))),
% 5.50/5.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.50/5.70  thf(d2_subset_1, axiom,
% 5.50/5.70    (![A:$i,B:$i]:
% 5.50/5.70     ( ( ( v1_xboole_0 @ A ) =>
% 5.50/5.70         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 5.50/5.70       ( ( ~( v1_xboole_0 @ A ) ) =>
% 5.50/5.70         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 5.50/5.70  thf('89', plain,
% 5.50/5.70      (![X20 : $i, X21 : $i]:
% 5.50/5.70         (~ (m1_subset_1 @ X20 @ X21)
% 5.50/5.70          | (r2_hidden @ X20 @ X21)
% 5.50/5.70          | (v1_xboole_0 @ X21))),
% 5.50/5.70      inference('cnf', [status(esa)], [d2_subset_1])).
% 5.50/5.70  thf('90', plain,
% 5.50/5.70      (((v1_xboole_0 @ (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B_1)))
% 5.50/5.70        | (r2_hidden @ sk_C @ (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B_1))))),
% 5.50/5.70      inference('sup-', [status(thm)], ['88', '89'])).
% 5.50/5.70  thf('91', plain,
% 5.50/5.70      (![X43 : $i, X44 : $i, X45 : $i]:
% 5.50/5.70         (~ (m1_subset_1 @ X43 @ (u1_struct_0 @ X44))
% 5.50/5.70          | ~ (r2_hidden @ X45 @ (u1_struct_0 @ (k9_yellow_6 @ X44 @ X43)))
% 5.50/5.70          | (v3_pre_topc @ X45 @ X44)
% 5.50/5.70          | ~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (u1_struct_0 @ X44)))
% 5.50/5.70          | ~ (l1_pre_topc @ X44)
% 5.50/5.70          | ~ (v2_pre_topc @ X44)
% 5.50/5.70          | (v2_struct_0 @ X44))),
% 5.50/5.70      inference('cnf', [status(esa)], [t39_yellow_6])).
% 5.50/5.70  thf('92', plain,
% 5.50/5.70      (((v1_xboole_0 @ (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B_1)))
% 5.50/5.70        | (v2_struct_0 @ sk_A)
% 5.50/5.70        | ~ (v2_pre_topc @ sk_A)
% 5.50/5.70        | ~ (l1_pre_topc @ sk_A)
% 5.50/5.70        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 5.50/5.70        | (v3_pre_topc @ sk_C @ sk_A)
% 5.50/5.70        | ~ (m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)))),
% 5.50/5.70      inference('sup-', [status(thm)], ['90', '91'])).
% 5.50/5.70  thf('93', plain, ((v2_pre_topc @ sk_A)),
% 5.50/5.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.50/5.70  thf('94', plain, ((l1_pre_topc @ sk_A)),
% 5.50/5.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.50/5.70  thf('95', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 5.50/5.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.50/5.70  thf('96', plain,
% 5.50/5.70      (((v1_xboole_0 @ (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B_1)))
% 5.50/5.70        | (v2_struct_0 @ sk_A)
% 5.50/5.70        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 5.50/5.70        | (v3_pre_topc @ sk_C @ sk_A))),
% 5.50/5.70      inference('demod', [status(thm)], ['92', '93', '94', '95'])).
% 5.50/5.70  thf('97', plain,
% 5.50/5.70      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 5.50/5.70      inference('sup-', [status(thm)], ['12', '20'])).
% 5.50/5.70  thf('98', plain,
% 5.50/5.70      (((v1_xboole_0 @ (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B_1)))
% 5.50/5.70        | (v2_struct_0 @ sk_A)
% 5.50/5.70        | (v3_pre_topc @ sk_C @ sk_A))),
% 5.50/5.70      inference('demod', [status(thm)], ['96', '97'])).
% 5.50/5.70  thf('99', plain, (~ (v2_struct_0 @ sk_A)),
% 5.50/5.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.50/5.70  thf('100', plain,
% 5.50/5.70      (((v3_pre_topc @ sk_C @ sk_A)
% 5.50/5.70        | (v1_xboole_0 @ (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B_1))))),
% 5.50/5.70      inference('clc', [status(thm)], ['98', '99'])).
% 5.50/5.70  thf('101', plain,
% 5.50/5.70      ((m1_subset_1 @ sk_C @ (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B_1)))),
% 5.50/5.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.50/5.70  thf('102', plain,
% 5.50/5.70      (![X21 : $i, X22 : $i]:
% 5.50/5.70         (~ (m1_subset_1 @ X22 @ X21)
% 5.50/5.70          | (v1_xboole_0 @ X22)
% 5.50/5.70          | ~ (v1_xboole_0 @ X21))),
% 5.50/5.70      inference('cnf', [status(esa)], [d2_subset_1])).
% 5.50/5.70  thf('103', plain,
% 5.50/5.70      ((~ (v1_xboole_0 @ (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B_1)))
% 5.50/5.70        | (v1_xboole_0 @ sk_C))),
% 5.50/5.70      inference('sup-', [status(thm)], ['101', '102'])).
% 5.50/5.70  thf('104', plain, (((v3_pre_topc @ sk_C @ sk_A) | (v1_xboole_0 @ sk_C))),
% 5.50/5.70      inference('sup-', [status(thm)], ['100', '103'])).
% 5.50/5.70  thf('105', plain,
% 5.50/5.70      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 5.50/5.70      inference('sup-', [status(thm)], ['12', '20'])).
% 5.50/5.70  thf(fc7_tops_1, axiom,
% 5.50/5.70    (![A:$i,B:$i,C:$i]:
% 5.50/5.70     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & ( v3_pre_topc @ B @ A ) & 
% 5.50/5.70         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) & 
% 5.50/5.70         ( v3_pre_topc @ C @ A ) & 
% 5.50/5.70         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 5.50/5.70       ( v3_pre_topc @ ( k2_xboole_0 @ B @ C ) @ A ) ))).
% 5.50/5.70  thf('106', plain,
% 5.50/5.70      (![X34 : $i, X35 : $i, X36 : $i]:
% 5.50/5.70         (~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (u1_struct_0 @ X35)))
% 5.50/5.70          | ~ (v3_pre_topc @ X34 @ X35)
% 5.50/5.70          | ~ (l1_pre_topc @ X35)
% 5.50/5.70          | ~ (v2_pre_topc @ X35)
% 5.50/5.70          | ~ (v3_pre_topc @ X36 @ X35)
% 5.50/5.70          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (u1_struct_0 @ X35)))
% 5.50/5.70          | (v3_pre_topc @ (k2_xboole_0 @ X34 @ X36) @ X35))),
% 5.50/5.70      inference('cnf', [status(esa)], [fc7_tops_1])).
% 5.50/5.70  thf('107', plain,
% 5.50/5.70      (![X18 : $i, X19 : $i]:
% 5.50/5.70         ((k3_tarski @ (k2_tarski @ X18 @ X19)) = (k2_xboole_0 @ X18 @ X19))),
% 5.50/5.70      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 5.50/5.70  thf('108', plain,
% 5.50/5.70      (![X34 : $i, X35 : $i, X36 : $i]:
% 5.50/5.70         (~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (u1_struct_0 @ X35)))
% 5.50/5.70          | ~ (v3_pre_topc @ X34 @ X35)
% 5.50/5.70          | ~ (l1_pre_topc @ X35)
% 5.50/5.70          | ~ (v2_pre_topc @ X35)
% 5.50/5.70          | ~ (v3_pre_topc @ X36 @ X35)
% 5.50/5.70          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (u1_struct_0 @ X35)))
% 5.50/5.70          | (v3_pre_topc @ (k3_tarski @ (k2_tarski @ X34 @ X36)) @ X35))),
% 5.50/5.70      inference('demod', [status(thm)], ['106', '107'])).
% 5.50/5.70  thf('109', plain,
% 5.50/5.70      (![X0 : $i]:
% 5.50/5.70         ((v3_pre_topc @ (k3_tarski @ (k2_tarski @ sk_C @ X0)) @ sk_A)
% 5.50/5.70          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 5.50/5.70          | ~ (v3_pre_topc @ X0 @ sk_A)
% 5.50/5.70          | ~ (v2_pre_topc @ sk_A)
% 5.50/5.70          | ~ (l1_pre_topc @ sk_A)
% 5.50/5.70          | ~ (v3_pre_topc @ sk_C @ sk_A))),
% 5.50/5.70      inference('sup-', [status(thm)], ['105', '108'])).
% 5.50/5.70  thf('110', plain, ((v2_pre_topc @ sk_A)),
% 5.50/5.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.50/5.70  thf('111', plain, ((l1_pre_topc @ sk_A)),
% 5.50/5.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.50/5.70  thf('112', plain,
% 5.50/5.70      (![X0 : $i]:
% 5.50/5.70         ((v3_pre_topc @ (k3_tarski @ (k2_tarski @ sk_C @ X0)) @ sk_A)
% 5.50/5.70          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 5.50/5.70          | ~ (v3_pre_topc @ X0 @ sk_A)
% 5.50/5.70          | ~ (v3_pre_topc @ sk_C @ sk_A))),
% 5.50/5.70      inference('demod', [status(thm)], ['109', '110', '111'])).
% 5.50/5.70  thf('113', plain,
% 5.50/5.70      (![X0 : $i]:
% 5.50/5.70         ((v1_xboole_0 @ sk_C)
% 5.50/5.70          | ~ (v3_pre_topc @ X0 @ sk_A)
% 5.50/5.70          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 5.50/5.70          | (v3_pre_topc @ (k3_tarski @ (k2_tarski @ sk_C @ X0)) @ sk_A))),
% 5.50/5.70      inference('sup-', [status(thm)], ['104', '112'])).
% 5.50/5.70  thf('114', plain,
% 5.50/5.70      (((v3_pre_topc @ (k3_tarski @ (k2_tarski @ sk_C @ sk_D)) @ sk_A)
% 5.50/5.70        | ~ (v3_pre_topc @ sk_D @ sk_A)
% 5.50/5.70        | (v1_xboole_0 @ sk_C))),
% 5.50/5.70      inference('sup-', [status(thm)], ['87', '113'])).
% 5.50/5.70  thf('115', plain,
% 5.50/5.70      ((m1_subset_1 @ sk_D @ (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B_1)))),
% 5.50/5.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.50/5.70  thf('116', plain,
% 5.50/5.70      (![X20 : $i, X21 : $i]:
% 5.50/5.70         (~ (m1_subset_1 @ X20 @ X21)
% 5.50/5.70          | (r2_hidden @ X20 @ X21)
% 5.50/5.70          | (v1_xboole_0 @ X21))),
% 5.50/5.70      inference('cnf', [status(esa)], [d2_subset_1])).
% 5.50/5.70  thf('117', plain,
% 5.50/5.70      (((v1_xboole_0 @ (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B_1)))
% 5.50/5.70        | (r2_hidden @ sk_D @ (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B_1))))),
% 5.50/5.70      inference('sup-', [status(thm)], ['115', '116'])).
% 5.50/5.70  thf('118', plain,
% 5.50/5.70      (![X43 : $i, X44 : $i, X45 : $i]:
% 5.50/5.70         (~ (m1_subset_1 @ X43 @ (u1_struct_0 @ X44))
% 5.50/5.70          | ~ (r2_hidden @ X45 @ (u1_struct_0 @ (k9_yellow_6 @ X44 @ X43)))
% 5.50/5.70          | (v3_pre_topc @ X45 @ X44)
% 5.50/5.70          | ~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (u1_struct_0 @ X44)))
% 5.50/5.70          | ~ (l1_pre_topc @ X44)
% 5.50/5.70          | ~ (v2_pre_topc @ X44)
% 5.50/5.70          | (v2_struct_0 @ X44))),
% 5.50/5.70      inference('cnf', [status(esa)], [t39_yellow_6])).
% 5.50/5.70  thf('119', plain,
% 5.50/5.70      (((v1_xboole_0 @ (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B_1)))
% 5.50/5.70        | (v2_struct_0 @ sk_A)
% 5.50/5.70        | ~ (v2_pre_topc @ sk_A)
% 5.50/5.70        | ~ (l1_pre_topc @ sk_A)
% 5.50/5.70        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 5.50/5.70        | (v3_pre_topc @ sk_D @ sk_A)
% 5.50/5.70        | ~ (m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)))),
% 5.50/5.70      inference('sup-', [status(thm)], ['117', '118'])).
% 5.50/5.70  thf('120', plain, ((v2_pre_topc @ sk_A)),
% 5.50/5.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.50/5.70  thf('121', plain, ((l1_pre_topc @ sk_A)),
% 5.50/5.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.50/5.70  thf('122', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 5.50/5.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.50/5.70  thf('123', plain,
% 5.50/5.70      (((v1_xboole_0 @ (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B_1)))
% 5.50/5.70        | (v2_struct_0 @ sk_A)
% 5.50/5.70        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 5.50/5.70        | (v3_pre_topc @ sk_D @ sk_A))),
% 5.50/5.70      inference('demod', [status(thm)], ['119', '120', '121', '122'])).
% 5.50/5.70  thf('124', plain,
% 5.50/5.70      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 5.50/5.70      inference('sup-', [status(thm)], ['67', '68'])).
% 5.50/5.70  thf('125', plain,
% 5.50/5.70      (((v1_xboole_0 @ (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B_1)))
% 5.50/5.70        | (v2_struct_0 @ sk_A)
% 5.50/5.70        | (v3_pre_topc @ sk_D @ sk_A))),
% 5.50/5.70      inference('demod', [status(thm)], ['123', '124'])).
% 5.50/5.70  thf('126', plain, (~ (v2_struct_0 @ sk_A)),
% 5.50/5.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.50/5.70  thf('127', plain,
% 5.50/5.70      (((v3_pre_topc @ sk_D @ sk_A)
% 5.50/5.70        | (v1_xboole_0 @ (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B_1))))),
% 5.50/5.70      inference('clc', [status(thm)], ['125', '126'])).
% 5.50/5.70  thf('128', plain,
% 5.50/5.70      ((~ (v1_xboole_0 @ (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B_1)))
% 5.50/5.70        | (v1_xboole_0 @ sk_C))),
% 5.50/5.70      inference('sup-', [status(thm)], ['101', '102'])).
% 5.50/5.70  thf('129', plain, (((v3_pre_topc @ sk_D @ sk_A) | (v1_xboole_0 @ sk_C))),
% 5.50/5.70      inference('sup-', [status(thm)], ['127', '128'])).
% 5.50/5.70  thf('130', plain,
% 5.50/5.70      (((v1_xboole_0 @ sk_C)
% 5.50/5.70        | (v3_pre_topc @ (k3_tarski @ (k2_tarski @ sk_C @ sk_D)) @ sk_A))),
% 5.50/5.70      inference('clc', [status(thm)], ['114', '129'])).
% 5.50/5.70  thf('131', plain, ((r2_hidden @ sk_B_1 @ sk_C)),
% 5.50/5.70      inference('clc', [status(thm)], ['29', '30'])).
% 5.50/5.70  thf(d1_xboole_0, axiom,
% 5.50/5.70    (![A:$i]:
% 5.50/5.70     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 5.50/5.70  thf('132', plain,
% 5.50/5.70      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 5.50/5.70      inference('cnf', [status(esa)], [d1_xboole_0])).
% 5.50/5.70  thf('133', plain, (~ (v1_xboole_0 @ sk_C)),
% 5.50/5.70      inference('sup-', [status(thm)], ['131', '132'])).
% 5.50/5.70  thf('134', plain,
% 5.50/5.70      ((v3_pre_topc @ (k3_tarski @ (k2_tarski @ sk_C @ sk_D)) @ sk_A)),
% 5.50/5.70      inference('clc', [status(thm)], ['130', '133'])).
% 5.50/5.70  thf('135', plain,
% 5.50/5.70      (![X0 : $i]:
% 5.50/5.70         ((v2_struct_0 @ sk_A)
% 5.50/5.70          | (r2_hidden @ (k3_tarski @ (k2_tarski @ sk_C @ sk_D)) @ 
% 5.50/5.70             (u1_struct_0 @ (k9_yellow_6 @ sk_A @ X0)))
% 5.50/5.70          | ~ (r2_hidden @ X0 @ (k3_tarski @ (k2_tarski @ sk_C @ sk_D)))
% 5.50/5.70          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 5.50/5.70      inference('demod', [status(thm)], ['86', '134'])).
% 5.50/5.70  thf('136', plain,
% 5.50/5.70      ((~ (m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 5.50/5.70        | (r2_hidden @ (k3_tarski @ (k2_tarski @ sk_C @ sk_D)) @ 
% 5.50/5.70           (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B_1)))
% 5.50/5.70        | (v2_struct_0 @ sk_A))),
% 5.50/5.70      inference('sup-', [status(thm)], ['58', '135'])).
% 5.50/5.70  thf('137', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 5.50/5.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.50/5.70  thf('138', plain,
% 5.50/5.70      (((r2_hidden @ (k3_tarski @ (k2_tarski @ sk_C @ sk_D)) @ 
% 5.50/5.70         (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B_1)))
% 5.50/5.70        | (v2_struct_0 @ sk_A))),
% 5.50/5.70      inference('demod', [status(thm)], ['136', '137'])).
% 5.50/5.70  thf('139', plain, (~ (v2_struct_0 @ sk_A)),
% 5.50/5.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.50/5.70  thf('140', plain,
% 5.50/5.70      ((r2_hidden @ (k3_tarski @ (k2_tarski @ sk_C @ sk_D)) @ 
% 5.50/5.70        (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B_1)))),
% 5.50/5.70      inference('clc', [status(thm)], ['138', '139'])).
% 5.50/5.70  thf(t1_subset, axiom,
% 5.50/5.70    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 5.50/5.70  thf('141', plain,
% 5.50/5.70      (![X29 : $i, X30 : $i]:
% 5.50/5.70         ((m1_subset_1 @ X29 @ X30) | ~ (r2_hidden @ X29 @ X30))),
% 5.50/5.70      inference('cnf', [status(esa)], [t1_subset])).
% 5.50/5.70  thf('142', plain,
% 5.50/5.70      ((m1_subset_1 @ (k3_tarski @ (k2_tarski @ sk_C @ sk_D)) @ 
% 5.50/5.70        (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B_1)))),
% 5.50/5.70      inference('sup-', [status(thm)], ['140', '141'])).
% 5.50/5.70  thf('143', plain, ($false), inference('demod', [status(thm)], ['2', '142'])).
% 5.50/5.70  
% 5.50/5.70  % SZS output end Refutation
% 5.50/5.70  
% 5.50/5.71  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
