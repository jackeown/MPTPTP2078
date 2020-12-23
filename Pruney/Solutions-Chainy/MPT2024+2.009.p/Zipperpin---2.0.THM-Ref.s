%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.kGEEH0iYmB

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:14:27 EST 2020

% Result     : Theorem 3.35s
% Output     : Refutation 3.35s
% Verified   : 
% Statistics : Number of formulae       :  165 ( 607 expanded)
%              Number of leaves         :   33 ( 188 expanded)
%              Depth                    :   19
%              Number of atoms          : 1334 (10599 expanded)
%              Number of equality atoms :    4 (   4 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(m1_connsp_2_type,type,(
    m1_connsp_2: $i > $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k9_yellow_6_type,type,(
    k9_yellow_6: $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

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
    m1_subset_1 @ sk_D @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B_1 ) ) ),
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
    ! [X40: $i,X41: $i,X42: $i] :
      ( ~ ( m1_subset_1 @ X40 @ ( u1_struct_0 @ X41 ) )
      | ( m1_connsp_2 @ X42 @ X41 @ X40 )
      | ~ ( m1_subset_1 @ X42 @ ( u1_struct_0 @ ( k9_yellow_6 @ X41 @ X40 ) ) )
      | ~ ( l1_pre_topc @ X41 )
      | ~ ( v2_pre_topc @ X41 )
      | ( v2_struct_0 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t21_waybel_9])).

thf('4',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( m1_connsp_2 @ sk_D @ sk_A @ sk_B_1 )
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
    | ( m1_connsp_2 @ sk_D @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['4','5','6','7'])).

thf('9',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    m1_connsp_2 @ sk_D @ sk_A @ sk_B_1 ),
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
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( l1_pre_topc @ X31 )
      | ~ ( v2_pre_topc @ X31 )
      | ( v2_struct_0 @ X31 )
      | ~ ( m1_subset_1 @ X32 @ ( u1_struct_0 @ X31 ) )
      | ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X31 ) ) )
      | ~ ( m1_connsp_2 @ X33 @ X31 @ X32 ) ) ),
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
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
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
    ! [X34: $i,X35: $i,X36: $i] :
      ( ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X35 ) ) )
      | ~ ( m1_connsp_2 @ X34 @ X35 @ X36 )
      | ( r2_hidden @ X36 @ X34 )
      | ~ ( m1_subset_1 @ X36 @ ( u1_struct_0 @ X35 ) )
      | ~ ( l1_pre_topc @ X35 )
      | ~ ( v2_pre_topc @ X35 )
      | ( v2_struct_0 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t6_connsp_2])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X0 @ sk_D )
      | ~ ( m1_connsp_2 @ sk_D @ sk_A @ X0 ) ) ),
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
      | ( r2_hidden @ X0 @ sk_D )
      | ~ ( m1_connsp_2 @ sk_D @ sk_A @ X0 ) ) ),
    inference(demod,[status(thm)],['21','22','23'])).

thf('25',plain,
    ( ~ ( m1_connsp_2 @ sk_D @ sk_A @ sk_B_1 )
    | ( r2_hidden @ sk_B_1 @ sk_D )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['1','24'])).

thf('26',plain,(
    m1_connsp_2 @ sk_D @ sk_A @ sk_B_1 ),
    inference(clc,[status(thm)],['8','9'])).

thf('27',plain,
    ( ( r2_hidden @ sk_B_1 @ sk_D )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    r2_hidden @ sk_B_1 @ sk_D ),
    inference(clc,[status(thm)],['27','28'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('30',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(t38_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ C ) ) ) )).

thf('31',plain,(
    ! [X8: $i,X10: $i,X11: $i] :
      ( ( r1_tarski @ ( k2_tarski @ X8 @ X10 ) @ X11 )
      | ~ ( r2_hidden @ X10 @ X11 )
      | ~ ( r2_hidden @ X8 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X1 @ X0 )
      | ( r1_tarski @ ( k2_tarski @ X1 @ ( sk_B @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_tarski @ X1 @ ( sk_B @ X0 ) ) @ X0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference(clc,[status(thm)],['32','33'])).

thf('35',plain,(
    r1_tarski @ ( k2_tarski @ sk_B_1 @ ( sk_B @ sk_D ) ) @ sk_D ),
    inference('sup-',[status(thm)],['29','34'])).

thf(t10_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ) )).

thf('36',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ( r1_tarski @ X3 @ ( k2_xboole_0 @ X5 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t10_xboole_1])).

thf('37',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_tarski @ sk_B_1 @ ( sk_B @ sk_D ) ) @ ( k2_xboole_0 @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( r2_hidden @ X8 @ X9 )
      | ~ ( r1_tarski @ ( k2_tarski @ X8 @ X10 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('39',plain,(
    ! [X0: $i] :
      ( r2_hidden @ sk_B_1 @ ( k2_xboole_0 @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['10','18'])).

thf('41',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ~ ( m1_subset_1 @ X40 @ ( u1_struct_0 @ X41 ) )
      | ( m1_connsp_2 @ X42 @ X41 @ X40 )
      | ~ ( m1_subset_1 @ X42 @ ( u1_struct_0 @ ( k9_yellow_6 @ X41 @ X40 ) ) )
      | ~ ( l1_pre_topc @ X41 )
      | ~ ( v2_pre_topc @ X41 )
      | ( v2_struct_0 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t21_waybel_9])).

thf('43',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( m1_connsp_2 @ sk_C @ sk_A @ sk_B_1 )
    | ~ ( m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_connsp_2 @ sk_C @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['43','44','45','46'])).

thf('48',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    m1_connsp_2 @ sk_C @ sk_A @ sk_B_1 ),
    inference(clc,[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( m1_connsp_2 @ X0 @ sk_A @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['16','17'])).

thf('51',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf(dt_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( m1_subset_1 @ ( k4_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('52',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X16 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X16 ) )
      | ( m1_subset_1 @ ( k4_subset_1 @ X16 @ X15 @ X17 ) @ ( k1_zfmisc_1 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k4_subset_1])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    m1_subset_1 @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['40','53'])).

thf('55',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['10','18'])).

thf('56',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('57',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X19 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X19 ) )
      | ( ( k4_subset_1 @ X19 @ X18 @ X20 )
        = ( k2_xboole_0 @ X18 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ X0 )
        = ( k2_xboole_0 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,
    ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ sk_D )
    = ( k2_xboole_0 @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['55','58'])).

thf('60',plain,(
    m1_subset_1 @ ( k2_xboole_0 @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['54','59'])).

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

thf('61',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ~ ( m1_subset_1 @ X37 @ ( u1_struct_0 @ X38 ) )
      | ~ ( r2_hidden @ X37 @ X39 )
      | ~ ( v3_pre_topc @ X39 @ X38 )
      | ( r2_hidden @ X39 @ ( u1_struct_0 @ ( k9_yellow_6 @ X38 @ X37 ) ) )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X38 ) ) )
      | ~ ( l1_pre_topc @ X38 )
      | ~ ( v2_pre_topc @ X38 )
      | ( v2_struct_0 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t39_yellow_6])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( r2_hidden @ ( k2_xboole_0 @ sk_C @ sk_D ) @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ X0 ) ) )
      | ~ ( v3_pre_topc @ ( k2_xboole_0 @ sk_C @ sk_D ) @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( k2_xboole_0 @ sk_C @ sk_D ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['10','18'])).

thf('66',plain,(
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

thf('67',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X12 @ X13 )
      | ( r2_hidden @ X12 @ X13 )
      | ( v1_xboole_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('68',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B_1 ) ) )
    | ( r2_hidden @ sk_C @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ~ ( m1_subset_1 @ X37 @ ( u1_struct_0 @ X38 ) )
      | ~ ( r2_hidden @ X39 @ ( u1_struct_0 @ ( k9_yellow_6 @ X38 @ X37 ) ) )
      | ( v3_pre_topc @ X39 @ X38 )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X38 ) ) )
      | ~ ( l1_pre_topc @ X38 )
      | ~ ( v2_pre_topc @ X38 )
      | ( v2_struct_0 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t39_yellow_6])).

thf('70',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B_1 ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v3_pre_topc @ sk_C @ sk_A )
    | ~ ( m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B_1 ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v3_pre_topc @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['70','71','72','73'])).

thf('75',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('76',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B_1 ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v3_pre_topc @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['74','75'])).

thf('77',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,
    ( ( v3_pre_topc @ sk_C @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B_1 ) ) ) ),
    inference(clc,[status(thm)],['76','77'])).

thf('79',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X14 @ X13 )
      | ( v1_xboole_0 @ X14 )
      | ~ ( v1_xboole_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('81',plain,
    ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B_1 ) ) )
    | ( v1_xboole_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,
    ( ( v3_pre_topc @ sk_C @ sk_A )
    | ( v1_xboole_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['78','81'])).

thf('83',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf(fc7_tops_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( v3_pre_topc @ B @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
        & ( v3_pre_topc @ C @ A )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v3_pre_topc @ ( k2_xboole_0 @ B @ C ) @ A ) ) )).

thf('84',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) )
      | ~ ( v3_pre_topc @ X28 @ X29 )
      | ~ ( l1_pre_topc @ X29 )
      | ~ ( v2_pre_topc @ X29 )
      | ~ ( v3_pre_topc @ X30 @ X29 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) )
      | ( v3_pre_topc @ ( k2_xboole_0 @ X28 @ X30 ) @ X29 ) ) ),
    inference(cnf,[status(esa)],[fc7_tops_1])).

thf('85',plain,(
    ! [X0: $i] :
      ( ( v3_pre_topc @ ( k2_xboole_0 @ sk_C @ X0 ) @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v3_pre_topc @ X0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v3_pre_topc @ sk_C @ sk_A ) ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    ! [X0: $i] :
      ( ( v3_pre_topc @ ( k2_xboole_0 @ sk_C @ X0 ) @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v3_pre_topc @ X0 @ sk_A )
      | ~ ( v3_pre_topc @ sk_C @ sk_A ) ) ),
    inference(demod,[status(thm)],['85','86','87'])).

thf('89',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_C )
      | ~ ( v3_pre_topc @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v3_pre_topc @ ( k2_xboole_0 @ sk_C @ X0 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['82','88'])).

thf('90',plain,
    ( ( v3_pre_topc @ ( k2_xboole_0 @ sk_C @ sk_D ) @ sk_A )
    | ~ ( v3_pre_topc @ sk_D @ sk_A )
    | ( v1_xboole_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['65','89'])).

thf('91',plain,(
    m1_subset_1 @ sk_D @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X12 @ X13 )
      | ( r2_hidden @ X12 @ X13 )
      | ( v1_xboole_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('93',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B_1 ) ) )
    | ( r2_hidden @ sk_D @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ~ ( m1_subset_1 @ X37 @ ( u1_struct_0 @ X38 ) )
      | ~ ( r2_hidden @ X39 @ ( u1_struct_0 @ ( k9_yellow_6 @ X38 @ X37 ) ) )
      | ( v3_pre_topc @ X39 @ X38 )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X38 ) ) )
      | ~ ( l1_pre_topc @ X38 )
      | ~ ( v2_pre_topc @ X38 )
      | ( v2_struct_0 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t39_yellow_6])).

thf('95',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B_1 ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v3_pre_topc @ sk_D @ sk_A )
    | ~ ( m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B_1 ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v3_pre_topc @ sk_D @ sk_A ) ),
    inference(demod,[status(thm)],['95','96','97','98'])).

thf('100',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['10','18'])).

thf('101',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B_1 ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v3_pre_topc @ sk_D @ sk_A ) ),
    inference(demod,[status(thm)],['99','100'])).

thf('102',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,
    ( ( v3_pre_topc @ sk_D @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B_1 ) ) ) ),
    inference(clc,[status(thm)],['101','102'])).

thf('104',plain,
    ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B_1 ) ) )
    | ( v1_xboole_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('105',plain,
    ( ( v3_pre_topc @ sk_D @ sk_A )
    | ( v1_xboole_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,
    ( ( v1_xboole_0 @ sk_C )
    | ( v3_pre_topc @ ( k2_xboole_0 @ sk_C @ sk_D ) @ sk_A ) ),
    inference(clc,[status(thm)],['90','105'])).

thf('107',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('109',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X35 ) ) )
      | ~ ( m1_connsp_2 @ X34 @ X35 @ X36 )
      | ( r2_hidden @ X36 @ X34 )
      | ~ ( m1_subset_1 @ X36 @ ( u1_struct_0 @ X35 ) )
      | ~ ( l1_pre_topc @ X35 )
      | ~ ( v2_pre_topc @ X35 )
      | ( v2_struct_0 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t6_connsp_2])).

thf('110',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X0 @ sk_C )
      | ~ ( m1_connsp_2 @ sk_C @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['108','109'])).

thf('111',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X0 @ sk_C )
      | ~ ( m1_connsp_2 @ sk_C @ sk_A @ X0 ) ) ),
    inference(demod,[status(thm)],['110','111','112'])).

thf('114',plain,
    ( ~ ( m1_connsp_2 @ sk_C @ sk_A @ sk_B_1 )
    | ( r2_hidden @ sk_B_1 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['107','113'])).

thf('115',plain,(
    m1_connsp_2 @ sk_C @ sk_A @ sk_B_1 ),
    inference(clc,[status(thm)],['47','48'])).

thf('116',plain,
    ( ( r2_hidden @ sk_B_1 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['114','115'])).

thf('117',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,(
    r2_hidden @ sk_B_1 @ sk_C ),
    inference(clc,[status(thm)],['116','117'])).

thf('119',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('120',plain,(
    ~ ( v1_xboole_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['118','119'])).

thf('121',plain,(
    v3_pre_topc @ ( k2_xboole_0 @ sk_C @ sk_D ) @ sk_A ),
    inference(clc,[status(thm)],['106','120'])).

thf('122',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ ( k2_xboole_0 @ sk_C @ sk_D ) @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ X0 ) ) )
      | ~ ( r2_hidden @ X0 @ ( k2_xboole_0 @ sk_C @ sk_D ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['62','63','64','121'])).

thf('123',plain,
    ( ~ ( m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( k2_xboole_0 @ sk_C @ sk_D ) @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B_1 ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['39','122'])).

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
    ! [X21: $i,X22: $i] :
      ( ( m1_subset_1 @ X21 @ X22 )
      | ~ ( r2_hidden @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('129',plain,(
    m1_subset_1 @ ( k2_xboole_0 @ sk_C @ sk_D ) @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['127','128'])).

thf('130',plain,(
    $false ),
    inference(demod,[status(thm)],['0','129'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.kGEEH0iYmB
% 0.12/0.36  % Computer   : n003.cluster.edu
% 0.12/0.36  % Model      : x86_64 x86_64
% 0.12/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.36  % Memory     : 8042.1875MB
% 0.12/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.36  % CPULimit   : 60
% 0.12/0.36  % DateTime   : Tue Dec  1 15:58:42 EST 2020
% 0.12/0.36  % CPUTime    : 
% 0.12/0.36  % Running portfolio for 600 s
% 0.12/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.36  % Number of cores: 8
% 0.12/0.36  % Python version: Python 3.6.8
% 0.12/0.36  % Running in FO mode
% 3.35/3.55  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 3.35/3.55  % Solved by: fo/fo7.sh
% 3.35/3.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 3.35/3.55  % done 4146 iterations in 3.081s
% 3.35/3.55  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 3.35/3.55  % SZS output start Refutation
% 3.35/3.55  thf(sk_C_type, type, sk_C: $i).
% 3.35/3.55  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 3.35/3.55  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 3.35/3.55  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 3.35/3.55  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 3.35/3.55  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 3.35/3.55  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 3.35/3.55  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 3.35/3.55  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 3.35/3.55  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 3.35/3.55  thf(sk_D_type, type, sk_D: $i).
% 3.35/3.55  thf(sk_B_type, type, sk_B: $i > $i).
% 3.35/3.55  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 3.35/3.55  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 3.35/3.55  thf(m1_connsp_2_type, type, m1_connsp_2: $i > $i > $i > $o).
% 3.35/3.55  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 3.35/3.55  thf(sk_A_type, type, sk_A: $i).
% 3.35/3.55  thf(sk_B_1_type, type, sk_B_1: $i).
% 3.35/3.55  thf(k9_yellow_6_type, type, k9_yellow_6: $i > $i > $i).
% 3.35/3.55  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 3.35/3.55  thf(t23_waybel_9, conjecture,
% 3.35/3.55    (![A:$i]:
% 3.35/3.55     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 3.35/3.55       ( ![B:$i]:
% 3.35/3.55         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 3.35/3.55           ( ![C:$i]:
% 3.35/3.55             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ ( k9_yellow_6 @ A @ B ) ) ) =>
% 3.35/3.55               ( ![D:$i]:
% 3.35/3.55                 ( ( m1_subset_1 @
% 3.35/3.55                     D @ ( u1_struct_0 @ ( k9_yellow_6 @ A @ B ) ) ) =>
% 3.35/3.55                   ( m1_subset_1 @
% 3.35/3.55                     ( k2_xboole_0 @ C @ D ) @ 
% 3.35/3.55                     ( u1_struct_0 @ ( k9_yellow_6 @ A @ B ) ) ) ) ) ) ) ) ) ))).
% 3.35/3.55  thf(zf_stmt_0, negated_conjecture,
% 3.35/3.55    (~( ![A:$i]:
% 3.35/3.55        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 3.35/3.55            ( l1_pre_topc @ A ) ) =>
% 3.35/3.55          ( ![B:$i]:
% 3.35/3.55            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 3.35/3.55              ( ![C:$i]:
% 3.35/3.55                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ ( k9_yellow_6 @ A @ B ) ) ) =>
% 3.35/3.55                  ( ![D:$i]:
% 3.35/3.55                    ( ( m1_subset_1 @
% 3.35/3.55                        D @ ( u1_struct_0 @ ( k9_yellow_6 @ A @ B ) ) ) =>
% 3.35/3.55                      ( m1_subset_1 @
% 3.35/3.55                        ( k2_xboole_0 @ C @ D ) @ 
% 3.35/3.55                        ( u1_struct_0 @ ( k9_yellow_6 @ A @ B ) ) ) ) ) ) ) ) ) ) )),
% 3.35/3.55    inference('cnf.neg', [status(esa)], [t23_waybel_9])).
% 3.35/3.55  thf('0', plain,
% 3.35/3.55      (~ (m1_subset_1 @ (k2_xboole_0 @ sk_C @ sk_D) @ 
% 3.35/3.55          (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B_1)))),
% 3.35/3.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.35/3.55  thf('1', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 3.35/3.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.35/3.55  thf('2', plain,
% 3.35/3.55      ((m1_subset_1 @ sk_D @ (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B_1)))),
% 3.35/3.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.35/3.55  thf(t21_waybel_9, axiom,
% 3.35/3.55    (![A:$i]:
% 3.35/3.55     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 3.35/3.55       ( ![B:$i]:
% 3.35/3.55         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 3.35/3.55           ( ![C:$i]:
% 3.35/3.55             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ ( k9_yellow_6 @ A @ B ) ) ) =>
% 3.35/3.55               ( m1_connsp_2 @ C @ A @ B ) ) ) ) ) ))).
% 3.35/3.55  thf('3', plain,
% 3.35/3.55      (![X40 : $i, X41 : $i, X42 : $i]:
% 3.35/3.55         (~ (m1_subset_1 @ X40 @ (u1_struct_0 @ X41))
% 3.35/3.55          | (m1_connsp_2 @ X42 @ X41 @ X40)
% 3.35/3.55          | ~ (m1_subset_1 @ X42 @ (u1_struct_0 @ (k9_yellow_6 @ X41 @ X40)))
% 3.35/3.55          | ~ (l1_pre_topc @ X41)
% 3.35/3.55          | ~ (v2_pre_topc @ X41)
% 3.35/3.55          | (v2_struct_0 @ X41))),
% 3.35/3.55      inference('cnf', [status(esa)], [t21_waybel_9])).
% 3.35/3.55  thf('4', plain,
% 3.35/3.55      (((v2_struct_0 @ sk_A)
% 3.35/3.55        | ~ (v2_pre_topc @ sk_A)
% 3.35/3.55        | ~ (l1_pre_topc @ sk_A)
% 3.35/3.55        | (m1_connsp_2 @ sk_D @ sk_A @ sk_B_1)
% 3.35/3.55        | ~ (m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)))),
% 3.35/3.55      inference('sup-', [status(thm)], ['2', '3'])).
% 3.35/3.55  thf('5', plain, ((v2_pre_topc @ sk_A)),
% 3.35/3.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.35/3.55  thf('6', plain, ((l1_pre_topc @ sk_A)),
% 3.35/3.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.35/3.55  thf('7', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 3.35/3.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.35/3.55  thf('8', plain,
% 3.35/3.55      (((v2_struct_0 @ sk_A) | (m1_connsp_2 @ sk_D @ sk_A @ sk_B_1))),
% 3.35/3.55      inference('demod', [status(thm)], ['4', '5', '6', '7'])).
% 3.35/3.55  thf('9', plain, (~ (v2_struct_0 @ sk_A)),
% 3.35/3.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.35/3.55  thf('10', plain, ((m1_connsp_2 @ sk_D @ sk_A @ sk_B_1)),
% 3.35/3.55      inference('clc', [status(thm)], ['8', '9'])).
% 3.35/3.55  thf('11', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 3.35/3.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.35/3.55  thf(dt_m1_connsp_2, axiom,
% 3.35/3.55    (![A:$i,B:$i]:
% 3.35/3.55     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 3.35/3.55         ( l1_pre_topc @ A ) & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) =>
% 3.35/3.55       ( ![C:$i]:
% 3.35/3.55         ( ( m1_connsp_2 @ C @ A @ B ) =>
% 3.35/3.55           ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 3.35/3.55  thf('12', plain,
% 3.35/3.55      (![X31 : $i, X32 : $i, X33 : $i]:
% 3.35/3.55         (~ (l1_pre_topc @ X31)
% 3.35/3.55          | ~ (v2_pre_topc @ X31)
% 3.35/3.55          | (v2_struct_0 @ X31)
% 3.35/3.55          | ~ (m1_subset_1 @ X32 @ (u1_struct_0 @ X31))
% 3.35/3.55          | (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (u1_struct_0 @ X31)))
% 3.35/3.55          | ~ (m1_connsp_2 @ X33 @ X31 @ X32))),
% 3.35/3.55      inference('cnf', [status(esa)], [dt_m1_connsp_2])).
% 3.35/3.55  thf('13', plain,
% 3.35/3.55      (![X0 : $i]:
% 3.35/3.55         (~ (m1_connsp_2 @ X0 @ sk_A @ sk_B_1)
% 3.35/3.55          | (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 3.35/3.55          | (v2_struct_0 @ sk_A)
% 3.35/3.55          | ~ (v2_pre_topc @ sk_A)
% 3.35/3.55          | ~ (l1_pre_topc @ sk_A))),
% 3.35/3.55      inference('sup-', [status(thm)], ['11', '12'])).
% 3.35/3.55  thf('14', plain, ((v2_pre_topc @ sk_A)),
% 3.35/3.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.35/3.55  thf('15', plain, ((l1_pre_topc @ sk_A)),
% 3.35/3.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.35/3.55  thf('16', plain,
% 3.35/3.55      (![X0 : $i]:
% 3.35/3.55         (~ (m1_connsp_2 @ X0 @ sk_A @ sk_B_1)
% 3.35/3.55          | (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 3.35/3.55          | (v2_struct_0 @ sk_A))),
% 3.35/3.55      inference('demod', [status(thm)], ['13', '14', '15'])).
% 3.35/3.55  thf('17', plain, (~ (v2_struct_0 @ sk_A)),
% 3.35/3.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.35/3.55  thf('18', plain,
% 3.35/3.55      (![X0 : $i]:
% 3.35/3.55         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 3.35/3.55          | ~ (m1_connsp_2 @ X0 @ sk_A @ sk_B_1))),
% 3.35/3.55      inference('clc', [status(thm)], ['16', '17'])).
% 3.35/3.55  thf('19', plain,
% 3.35/3.55      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.35/3.55      inference('sup-', [status(thm)], ['10', '18'])).
% 3.35/3.55  thf(t6_connsp_2, axiom,
% 3.35/3.55    (![A:$i]:
% 3.35/3.55     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 3.35/3.55       ( ![B:$i]:
% 3.35/3.55         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 3.35/3.55           ( ![C:$i]:
% 3.35/3.55             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 3.35/3.55               ( ( m1_connsp_2 @ B @ A @ C ) => ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 3.35/3.55  thf('20', plain,
% 3.35/3.55      (![X34 : $i, X35 : $i, X36 : $i]:
% 3.35/3.55         (~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (u1_struct_0 @ X35)))
% 3.35/3.55          | ~ (m1_connsp_2 @ X34 @ X35 @ X36)
% 3.35/3.55          | (r2_hidden @ X36 @ X34)
% 3.35/3.55          | ~ (m1_subset_1 @ X36 @ (u1_struct_0 @ X35))
% 3.35/3.55          | ~ (l1_pre_topc @ X35)
% 3.35/3.55          | ~ (v2_pre_topc @ X35)
% 3.35/3.55          | (v2_struct_0 @ X35))),
% 3.35/3.55      inference('cnf', [status(esa)], [t6_connsp_2])).
% 3.35/3.55  thf('21', plain,
% 3.35/3.55      (![X0 : $i]:
% 3.35/3.55         ((v2_struct_0 @ sk_A)
% 3.35/3.55          | ~ (v2_pre_topc @ sk_A)
% 3.35/3.55          | ~ (l1_pre_topc @ sk_A)
% 3.35/3.55          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 3.35/3.55          | (r2_hidden @ X0 @ sk_D)
% 3.35/3.55          | ~ (m1_connsp_2 @ sk_D @ sk_A @ X0))),
% 3.35/3.55      inference('sup-', [status(thm)], ['19', '20'])).
% 3.35/3.55  thf('22', plain, ((v2_pre_topc @ sk_A)),
% 3.35/3.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.35/3.55  thf('23', plain, ((l1_pre_topc @ sk_A)),
% 3.35/3.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.35/3.55  thf('24', plain,
% 3.35/3.55      (![X0 : $i]:
% 3.35/3.55         ((v2_struct_0 @ sk_A)
% 3.35/3.55          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 3.35/3.55          | (r2_hidden @ X0 @ sk_D)
% 3.35/3.55          | ~ (m1_connsp_2 @ sk_D @ sk_A @ X0))),
% 3.35/3.55      inference('demod', [status(thm)], ['21', '22', '23'])).
% 3.35/3.55  thf('25', plain,
% 3.35/3.55      ((~ (m1_connsp_2 @ sk_D @ sk_A @ sk_B_1)
% 3.35/3.55        | (r2_hidden @ sk_B_1 @ sk_D)
% 3.35/3.55        | (v2_struct_0 @ sk_A))),
% 3.35/3.55      inference('sup-', [status(thm)], ['1', '24'])).
% 3.35/3.55  thf('26', plain, ((m1_connsp_2 @ sk_D @ sk_A @ sk_B_1)),
% 3.35/3.55      inference('clc', [status(thm)], ['8', '9'])).
% 3.35/3.55  thf('27', plain, (((r2_hidden @ sk_B_1 @ sk_D) | (v2_struct_0 @ sk_A))),
% 3.35/3.55      inference('demod', [status(thm)], ['25', '26'])).
% 3.35/3.55  thf('28', plain, (~ (v2_struct_0 @ sk_A)),
% 3.35/3.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.35/3.55  thf('29', plain, ((r2_hidden @ sk_B_1 @ sk_D)),
% 3.35/3.55      inference('clc', [status(thm)], ['27', '28'])).
% 3.35/3.55  thf(d1_xboole_0, axiom,
% 3.35/3.55    (![A:$i]:
% 3.35/3.55     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 3.35/3.55  thf('30', plain,
% 3.35/3.55      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 3.35/3.55      inference('cnf', [status(esa)], [d1_xboole_0])).
% 3.35/3.55  thf(t38_zfmisc_1, axiom,
% 3.35/3.55    (![A:$i,B:$i,C:$i]:
% 3.35/3.55     ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C ) <=>
% 3.35/3.55       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ C ) ) ))).
% 3.35/3.55  thf('31', plain,
% 3.35/3.55      (![X8 : $i, X10 : $i, X11 : $i]:
% 3.35/3.55         ((r1_tarski @ (k2_tarski @ X8 @ X10) @ X11)
% 3.35/3.55          | ~ (r2_hidden @ X10 @ X11)
% 3.35/3.55          | ~ (r2_hidden @ X8 @ X11))),
% 3.35/3.55      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 3.35/3.55  thf('32', plain,
% 3.35/3.55      (![X0 : $i, X1 : $i]:
% 3.35/3.55         ((v1_xboole_0 @ X0)
% 3.35/3.55          | ~ (r2_hidden @ X1 @ X0)
% 3.35/3.55          | (r1_tarski @ (k2_tarski @ X1 @ (sk_B @ X0)) @ X0))),
% 3.35/3.55      inference('sup-', [status(thm)], ['30', '31'])).
% 3.35/3.55  thf('33', plain,
% 3.35/3.55      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 3.35/3.55      inference('cnf', [status(esa)], [d1_xboole_0])).
% 3.35/3.55  thf('34', plain,
% 3.35/3.55      (![X0 : $i, X1 : $i]:
% 3.35/3.55         ((r1_tarski @ (k2_tarski @ X1 @ (sk_B @ X0)) @ X0)
% 3.35/3.55          | ~ (r2_hidden @ X1 @ X0))),
% 3.35/3.55      inference('clc', [status(thm)], ['32', '33'])).
% 3.35/3.55  thf('35', plain, ((r1_tarski @ (k2_tarski @ sk_B_1 @ (sk_B @ sk_D)) @ sk_D)),
% 3.35/3.55      inference('sup-', [status(thm)], ['29', '34'])).
% 3.35/3.55  thf(t10_xboole_1, axiom,
% 3.35/3.55    (![A:$i,B:$i,C:$i]:
% 3.35/3.55     ( ( r1_tarski @ A @ B ) => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ))).
% 3.35/3.55  thf('36', plain,
% 3.35/3.55      (![X3 : $i, X4 : $i, X5 : $i]:
% 3.35/3.55         (~ (r1_tarski @ X3 @ X4) | (r1_tarski @ X3 @ (k2_xboole_0 @ X5 @ X4)))),
% 3.35/3.55      inference('cnf', [status(esa)], [t10_xboole_1])).
% 3.35/3.55  thf('37', plain,
% 3.35/3.55      (![X0 : $i]:
% 3.35/3.55         (r1_tarski @ (k2_tarski @ sk_B_1 @ (sk_B @ sk_D)) @ 
% 3.35/3.55          (k2_xboole_0 @ X0 @ sk_D))),
% 3.35/3.55      inference('sup-', [status(thm)], ['35', '36'])).
% 3.35/3.55  thf('38', plain,
% 3.35/3.55      (![X8 : $i, X9 : $i, X10 : $i]:
% 3.35/3.55         ((r2_hidden @ X8 @ X9) | ~ (r1_tarski @ (k2_tarski @ X8 @ X10) @ X9))),
% 3.35/3.55      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 3.35/3.55  thf('39', plain,
% 3.35/3.55      (![X0 : $i]: (r2_hidden @ sk_B_1 @ (k2_xboole_0 @ X0 @ sk_D))),
% 3.35/3.55      inference('sup-', [status(thm)], ['37', '38'])).
% 3.35/3.55  thf('40', plain,
% 3.35/3.55      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.35/3.55      inference('sup-', [status(thm)], ['10', '18'])).
% 3.35/3.55  thf('41', plain,
% 3.35/3.55      ((m1_subset_1 @ sk_C @ (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B_1)))),
% 3.35/3.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.35/3.55  thf('42', plain,
% 3.35/3.55      (![X40 : $i, X41 : $i, X42 : $i]:
% 3.35/3.55         (~ (m1_subset_1 @ X40 @ (u1_struct_0 @ X41))
% 3.35/3.55          | (m1_connsp_2 @ X42 @ X41 @ X40)
% 3.35/3.55          | ~ (m1_subset_1 @ X42 @ (u1_struct_0 @ (k9_yellow_6 @ X41 @ X40)))
% 3.35/3.55          | ~ (l1_pre_topc @ X41)
% 3.35/3.55          | ~ (v2_pre_topc @ X41)
% 3.35/3.55          | (v2_struct_0 @ X41))),
% 3.35/3.55      inference('cnf', [status(esa)], [t21_waybel_9])).
% 3.35/3.55  thf('43', plain,
% 3.35/3.55      (((v2_struct_0 @ sk_A)
% 3.35/3.55        | ~ (v2_pre_topc @ sk_A)
% 3.35/3.55        | ~ (l1_pre_topc @ sk_A)
% 3.35/3.55        | (m1_connsp_2 @ sk_C @ sk_A @ sk_B_1)
% 3.35/3.55        | ~ (m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)))),
% 3.35/3.55      inference('sup-', [status(thm)], ['41', '42'])).
% 3.35/3.55  thf('44', plain, ((v2_pre_topc @ sk_A)),
% 3.35/3.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.35/3.55  thf('45', plain, ((l1_pre_topc @ sk_A)),
% 3.35/3.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.35/3.55  thf('46', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 3.35/3.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.35/3.55  thf('47', plain,
% 3.35/3.55      (((v2_struct_0 @ sk_A) | (m1_connsp_2 @ sk_C @ sk_A @ sk_B_1))),
% 3.35/3.55      inference('demod', [status(thm)], ['43', '44', '45', '46'])).
% 3.35/3.55  thf('48', plain, (~ (v2_struct_0 @ sk_A)),
% 3.35/3.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.35/3.55  thf('49', plain, ((m1_connsp_2 @ sk_C @ sk_A @ sk_B_1)),
% 3.35/3.55      inference('clc', [status(thm)], ['47', '48'])).
% 3.35/3.55  thf('50', plain,
% 3.35/3.55      (![X0 : $i]:
% 3.35/3.55         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 3.35/3.55          | ~ (m1_connsp_2 @ X0 @ sk_A @ sk_B_1))),
% 3.35/3.55      inference('clc', [status(thm)], ['16', '17'])).
% 3.35/3.55  thf('51', plain,
% 3.35/3.55      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.35/3.55      inference('sup-', [status(thm)], ['49', '50'])).
% 3.35/3.55  thf(dt_k4_subset_1, axiom,
% 3.35/3.55    (![A:$i,B:$i,C:$i]:
% 3.35/3.55     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 3.35/3.55         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 3.35/3.55       ( m1_subset_1 @ ( k4_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 3.35/3.55  thf('52', plain,
% 3.35/3.55      (![X15 : $i, X16 : $i, X17 : $i]:
% 3.35/3.55         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X16))
% 3.35/3.55          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X16))
% 3.35/3.55          | (m1_subset_1 @ (k4_subset_1 @ X16 @ X15 @ X17) @ 
% 3.35/3.55             (k1_zfmisc_1 @ X16)))),
% 3.35/3.55      inference('cnf', [status(esa)], [dt_k4_subset_1])).
% 3.35/3.55  thf('53', plain,
% 3.35/3.55      (![X0 : $i]:
% 3.35/3.55         ((m1_subset_1 @ (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ X0) @ 
% 3.35/3.55           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 3.35/3.55          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 3.35/3.55      inference('sup-', [status(thm)], ['51', '52'])).
% 3.35/3.55  thf('54', plain,
% 3.35/3.55      ((m1_subset_1 @ (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ sk_D) @ 
% 3.35/3.55        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.35/3.55      inference('sup-', [status(thm)], ['40', '53'])).
% 3.35/3.55  thf('55', plain,
% 3.35/3.55      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.35/3.55      inference('sup-', [status(thm)], ['10', '18'])).
% 3.35/3.55  thf('56', plain,
% 3.35/3.55      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.35/3.55      inference('sup-', [status(thm)], ['49', '50'])).
% 3.35/3.55  thf(redefinition_k4_subset_1, axiom,
% 3.35/3.55    (![A:$i,B:$i,C:$i]:
% 3.35/3.55     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 3.35/3.55         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 3.35/3.55       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 3.35/3.55  thf('57', plain,
% 3.35/3.55      (![X18 : $i, X19 : $i, X20 : $i]:
% 3.35/3.55         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X19))
% 3.35/3.55          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X19))
% 3.35/3.55          | ((k4_subset_1 @ X19 @ X18 @ X20) = (k2_xboole_0 @ X18 @ X20)))),
% 3.35/3.55      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 3.35/3.55  thf('58', plain,
% 3.35/3.55      (![X0 : $i]:
% 3.35/3.55         (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ X0)
% 3.35/3.55            = (k2_xboole_0 @ sk_C @ X0))
% 3.35/3.55          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 3.35/3.55      inference('sup-', [status(thm)], ['56', '57'])).
% 3.35/3.55  thf('59', plain,
% 3.35/3.55      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ sk_D)
% 3.35/3.55         = (k2_xboole_0 @ sk_C @ sk_D))),
% 3.35/3.55      inference('sup-', [status(thm)], ['55', '58'])).
% 3.35/3.55  thf('60', plain,
% 3.35/3.55      ((m1_subset_1 @ (k2_xboole_0 @ sk_C @ sk_D) @ 
% 3.35/3.55        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.35/3.55      inference('demod', [status(thm)], ['54', '59'])).
% 3.35/3.55  thf(t39_yellow_6, axiom,
% 3.35/3.55    (![A:$i]:
% 3.35/3.55     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 3.35/3.55       ( ![B:$i]:
% 3.35/3.55         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 3.35/3.55           ( ![C:$i]:
% 3.35/3.55             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 3.35/3.55               ( ( r2_hidden @ C @ ( u1_struct_0 @ ( k9_yellow_6 @ A @ B ) ) ) <=>
% 3.35/3.55                 ( ( r2_hidden @ B @ C ) & ( v3_pre_topc @ C @ A ) ) ) ) ) ) ) ))).
% 3.35/3.55  thf('61', plain,
% 3.35/3.55      (![X37 : $i, X38 : $i, X39 : $i]:
% 3.35/3.55         (~ (m1_subset_1 @ X37 @ (u1_struct_0 @ X38))
% 3.35/3.55          | ~ (r2_hidden @ X37 @ X39)
% 3.35/3.55          | ~ (v3_pre_topc @ X39 @ X38)
% 3.35/3.55          | (r2_hidden @ X39 @ (u1_struct_0 @ (k9_yellow_6 @ X38 @ X37)))
% 3.35/3.55          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (u1_struct_0 @ X38)))
% 3.35/3.55          | ~ (l1_pre_topc @ X38)
% 3.35/3.55          | ~ (v2_pre_topc @ X38)
% 3.35/3.55          | (v2_struct_0 @ X38))),
% 3.35/3.55      inference('cnf', [status(esa)], [t39_yellow_6])).
% 3.35/3.55  thf('62', plain,
% 3.35/3.55      (![X0 : $i]:
% 3.35/3.55         ((v2_struct_0 @ sk_A)
% 3.35/3.55          | ~ (v2_pre_topc @ sk_A)
% 3.35/3.55          | ~ (l1_pre_topc @ sk_A)
% 3.35/3.55          | (r2_hidden @ (k2_xboole_0 @ sk_C @ sk_D) @ 
% 3.35/3.55             (u1_struct_0 @ (k9_yellow_6 @ sk_A @ X0)))
% 3.35/3.55          | ~ (v3_pre_topc @ (k2_xboole_0 @ sk_C @ sk_D) @ sk_A)
% 3.35/3.55          | ~ (r2_hidden @ X0 @ (k2_xboole_0 @ sk_C @ sk_D))
% 3.35/3.55          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 3.35/3.55      inference('sup-', [status(thm)], ['60', '61'])).
% 3.35/3.55  thf('63', plain, ((v2_pre_topc @ sk_A)),
% 3.35/3.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.35/3.55  thf('64', plain, ((l1_pre_topc @ sk_A)),
% 3.35/3.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.35/3.55  thf('65', plain,
% 3.35/3.55      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.35/3.55      inference('sup-', [status(thm)], ['10', '18'])).
% 3.35/3.55  thf('66', plain,
% 3.35/3.55      ((m1_subset_1 @ sk_C @ (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B_1)))),
% 3.35/3.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.35/3.55  thf(d2_subset_1, axiom,
% 3.35/3.55    (![A:$i,B:$i]:
% 3.35/3.55     ( ( ( v1_xboole_0 @ A ) =>
% 3.35/3.55         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 3.35/3.55       ( ( ~( v1_xboole_0 @ A ) ) =>
% 3.35/3.55         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 3.35/3.55  thf('67', plain,
% 3.35/3.55      (![X12 : $i, X13 : $i]:
% 3.35/3.55         (~ (m1_subset_1 @ X12 @ X13)
% 3.35/3.55          | (r2_hidden @ X12 @ X13)
% 3.35/3.55          | (v1_xboole_0 @ X13))),
% 3.35/3.55      inference('cnf', [status(esa)], [d2_subset_1])).
% 3.35/3.55  thf('68', plain,
% 3.35/3.55      (((v1_xboole_0 @ (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B_1)))
% 3.35/3.55        | (r2_hidden @ sk_C @ (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B_1))))),
% 3.35/3.55      inference('sup-', [status(thm)], ['66', '67'])).
% 3.35/3.55  thf('69', plain,
% 3.35/3.55      (![X37 : $i, X38 : $i, X39 : $i]:
% 3.35/3.55         (~ (m1_subset_1 @ X37 @ (u1_struct_0 @ X38))
% 3.35/3.55          | ~ (r2_hidden @ X39 @ (u1_struct_0 @ (k9_yellow_6 @ X38 @ X37)))
% 3.35/3.55          | (v3_pre_topc @ X39 @ X38)
% 3.35/3.55          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (u1_struct_0 @ X38)))
% 3.35/3.55          | ~ (l1_pre_topc @ X38)
% 3.35/3.55          | ~ (v2_pre_topc @ X38)
% 3.35/3.55          | (v2_struct_0 @ X38))),
% 3.35/3.55      inference('cnf', [status(esa)], [t39_yellow_6])).
% 3.35/3.55  thf('70', plain,
% 3.35/3.55      (((v1_xboole_0 @ (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B_1)))
% 3.35/3.55        | (v2_struct_0 @ sk_A)
% 3.35/3.55        | ~ (v2_pre_topc @ sk_A)
% 3.35/3.55        | ~ (l1_pre_topc @ sk_A)
% 3.35/3.55        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 3.35/3.55        | (v3_pre_topc @ sk_C @ sk_A)
% 3.35/3.55        | ~ (m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)))),
% 3.35/3.55      inference('sup-', [status(thm)], ['68', '69'])).
% 3.35/3.55  thf('71', plain, ((v2_pre_topc @ sk_A)),
% 3.35/3.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.35/3.55  thf('72', plain, ((l1_pre_topc @ sk_A)),
% 3.35/3.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.35/3.55  thf('73', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 3.35/3.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.35/3.55  thf('74', plain,
% 3.35/3.55      (((v1_xboole_0 @ (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B_1)))
% 3.35/3.55        | (v2_struct_0 @ sk_A)
% 3.35/3.55        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 3.35/3.55        | (v3_pre_topc @ sk_C @ sk_A))),
% 3.35/3.55      inference('demod', [status(thm)], ['70', '71', '72', '73'])).
% 3.35/3.55  thf('75', plain,
% 3.35/3.55      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.35/3.55      inference('sup-', [status(thm)], ['49', '50'])).
% 3.35/3.55  thf('76', plain,
% 3.35/3.55      (((v1_xboole_0 @ (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B_1)))
% 3.35/3.55        | (v2_struct_0 @ sk_A)
% 3.35/3.55        | (v3_pre_topc @ sk_C @ sk_A))),
% 3.35/3.55      inference('demod', [status(thm)], ['74', '75'])).
% 3.35/3.55  thf('77', plain, (~ (v2_struct_0 @ sk_A)),
% 3.35/3.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.35/3.55  thf('78', plain,
% 3.35/3.55      (((v3_pre_topc @ sk_C @ sk_A)
% 3.35/3.55        | (v1_xboole_0 @ (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B_1))))),
% 3.35/3.55      inference('clc', [status(thm)], ['76', '77'])).
% 3.35/3.55  thf('79', plain,
% 3.35/3.55      ((m1_subset_1 @ sk_C @ (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B_1)))),
% 3.35/3.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.35/3.55  thf('80', plain,
% 3.35/3.55      (![X13 : $i, X14 : $i]:
% 3.35/3.55         (~ (m1_subset_1 @ X14 @ X13)
% 3.35/3.55          | (v1_xboole_0 @ X14)
% 3.35/3.55          | ~ (v1_xboole_0 @ X13))),
% 3.35/3.55      inference('cnf', [status(esa)], [d2_subset_1])).
% 3.35/3.55  thf('81', plain,
% 3.35/3.55      ((~ (v1_xboole_0 @ (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B_1)))
% 3.35/3.55        | (v1_xboole_0 @ sk_C))),
% 3.35/3.55      inference('sup-', [status(thm)], ['79', '80'])).
% 3.35/3.55  thf('82', plain, (((v3_pre_topc @ sk_C @ sk_A) | (v1_xboole_0 @ sk_C))),
% 3.35/3.55      inference('sup-', [status(thm)], ['78', '81'])).
% 3.35/3.55  thf('83', plain,
% 3.35/3.55      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.35/3.55      inference('sup-', [status(thm)], ['49', '50'])).
% 3.35/3.55  thf(fc7_tops_1, axiom,
% 3.35/3.55    (![A:$i,B:$i,C:$i]:
% 3.35/3.55     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & ( v3_pre_topc @ B @ A ) & 
% 3.35/3.55         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) & 
% 3.35/3.55         ( v3_pre_topc @ C @ A ) & 
% 3.35/3.55         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 3.35/3.55       ( v3_pre_topc @ ( k2_xboole_0 @ B @ C ) @ A ) ))).
% 3.35/3.55  thf('84', plain,
% 3.35/3.55      (![X28 : $i, X29 : $i, X30 : $i]:
% 3.35/3.55         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (u1_struct_0 @ X29)))
% 3.35/3.55          | ~ (v3_pre_topc @ X28 @ X29)
% 3.35/3.55          | ~ (l1_pre_topc @ X29)
% 3.35/3.55          | ~ (v2_pre_topc @ X29)
% 3.35/3.55          | ~ (v3_pre_topc @ X30 @ X29)
% 3.35/3.55          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ X29)))
% 3.35/3.55          | (v3_pre_topc @ (k2_xboole_0 @ X28 @ X30) @ X29))),
% 3.35/3.55      inference('cnf', [status(esa)], [fc7_tops_1])).
% 3.35/3.55  thf('85', plain,
% 3.35/3.55      (![X0 : $i]:
% 3.35/3.55         ((v3_pre_topc @ (k2_xboole_0 @ sk_C @ X0) @ sk_A)
% 3.35/3.55          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 3.35/3.55          | ~ (v3_pre_topc @ X0 @ sk_A)
% 3.35/3.55          | ~ (v2_pre_topc @ sk_A)
% 3.35/3.55          | ~ (l1_pre_topc @ sk_A)
% 3.35/3.55          | ~ (v3_pre_topc @ sk_C @ sk_A))),
% 3.35/3.55      inference('sup-', [status(thm)], ['83', '84'])).
% 3.35/3.55  thf('86', plain, ((v2_pre_topc @ sk_A)),
% 3.35/3.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.35/3.55  thf('87', plain, ((l1_pre_topc @ sk_A)),
% 3.35/3.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.35/3.55  thf('88', plain,
% 3.35/3.55      (![X0 : $i]:
% 3.35/3.55         ((v3_pre_topc @ (k2_xboole_0 @ sk_C @ X0) @ sk_A)
% 3.35/3.55          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 3.35/3.55          | ~ (v3_pre_topc @ X0 @ sk_A)
% 3.35/3.55          | ~ (v3_pre_topc @ sk_C @ sk_A))),
% 3.35/3.55      inference('demod', [status(thm)], ['85', '86', '87'])).
% 3.35/3.55  thf('89', plain,
% 3.35/3.55      (![X0 : $i]:
% 3.35/3.55         ((v1_xboole_0 @ sk_C)
% 3.35/3.55          | ~ (v3_pre_topc @ X0 @ sk_A)
% 3.35/3.55          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 3.35/3.55          | (v3_pre_topc @ (k2_xboole_0 @ sk_C @ X0) @ sk_A))),
% 3.35/3.55      inference('sup-', [status(thm)], ['82', '88'])).
% 3.35/3.55  thf('90', plain,
% 3.35/3.55      (((v3_pre_topc @ (k2_xboole_0 @ sk_C @ sk_D) @ sk_A)
% 3.35/3.55        | ~ (v3_pre_topc @ sk_D @ sk_A)
% 3.35/3.55        | (v1_xboole_0 @ sk_C))),
% 3.35/3.55      inference('sup-', [status(thm)], ['65', '89'])).
% 3.35/3.55  thf('91', plain,
% 3.35/3.55      ((m1_subset_1 @ sk_D @ (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B_1)))),
% 3.35/3.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.35/3.55  thf('92', plain,
% 3.35/3.55      (![X12 : $i, X13 : $i]:
% 3.35/3.55         (~ (m1_subset_1 @ X12 @ X13)
% 3.35/3.55          | (r2_hidden @ X12 @ X13)
% 3.35/3.55          | (v1_xboole_0 @ X13))),
% 3.35/3.55      inference('cnf', [status(esa)], [d2_subset_1])).
% 3.35/3.55  thf('93', plain,
% 3.35/3.55      (((v1_xboole_0 @ (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B_1)))
% 3.35/3.55        | (r2_hidden @ sk_D @ (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B_1))))),
% 3.35/3.55      inference('sup-', [status(thm)], ['91', '92'])).
% 3.35/3.55  thf('94', plain,
% 3.35/3.55      (![X37 : $i, X38 : $i, X39 : $i]:
% 3.35/3.55         (~ (m1_subset_1 @ X37 @ (u1_struct_0 @ X38))
% 3.35/3.55          | ~ (r2_hidden @ X39 @ (u1_struct_0 @ (k9_yellow_6 @ X38 @ X37)))
% 3.35/3.55          | (v3_pre_topc @ X39 @ X38)
% 3.35/3.55          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (u1_struct_0 @ X38)))
% 3.35/3.55          | ~ (l1_pre_topc @ X38)
% 3.35/3.55          | ~ (v2_pre_topc @ X38)
% 3.35/3.55          | (v2_struct_0 @ X38))),
% 3.35/3.55      inference('cnf', [status(esa)], [t39_yellow_6])).
% 3.35/3.55  thf('95', plain,
% 3.35/3.55      (((v1_xboole_0 @ (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B_1)))
% 3.35/3.55        | (v2_struct_0 @ sk_A)
% 3.35/3.55        | ~ (v2_pre_topc @ sk_A)
% 3.35/3.55        | ~ (l1_pre_topc @ sk_A)
% 3.35/3.55        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 3.35/3.55        | (v3_pre_topc @ sk_D @ sk_A)
% 3.35/3.55        | ~ (m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)))),
% 3.35/3.55      inference('sup-', [status(thm)], ['93', '94'])).
% 3.35/3.55  thf('96', plain, ((v2_pre_topc @ sk_A)),
% 3.35/3.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.35/3.55  thf('97', plain, ((l1_pre_topc @ sk_A)),
% 3.35/3.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.35/3.55  thf('98', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 3.35/3.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.35/3.55  thf('99', plain,
% 3.35/3.55      (((v1_xboole_0 @ (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B_1)))
% 3.35/3.55        | (v2_struct_0 @ sk_A)
% 3.35/3.55        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 3.35/3.55        | (v3_pre_topc @ sk_D @ sk_A))),
% 3.35/3.55      inference('demod', [status(thm)], ['95', '96', '97', '98'])).
% 3.35/3.55  thf('100', plain,
% 3.35/3.55      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.35/3.55      inference('sup-', [status(thm)], ['10', '18'])).
% 3.35/3.55  thf('101', plain,
% 3.35/3.55      (((v1_xboole_0 @ (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B_1)))
% 3.35/3.55        | (v2_struct_0 @ sk_A)
% 3.35/3.55        | (v3_pre_topc @ sk_D @ sk_A))),
% 3.35/3.55      inference('demod', [status(thm)], ['99', '100'])).
% 3.35/3.55  thf('102', plain, (~ (v2_struct_0 @ sk_A)),
% 3.35/3.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.35/3.55  thf('103', plain,
% 3.35/3.55      (((v3_pre_topc @ sk_D @ sk_A)
% 3.35/3.55        | (v1_xboole_0 @ (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B_1))))),
% 3.35/3.55      inference('clc', [status(thm)], ['101', '102'])).
% 3.35/3.55  thf('104', plain,
% 3.35/3.55      ((~ (v1_xboole_0 @ (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B_1)))
% 3.35/3.55        | (v1_xboole_0 @ sk_C))),
% 3.35/3.55      inference('sup-', [status(thm)], ['79', '80'])).
% 3.35/3.55  thf('105', plain, (((v3_pre_topc @ sk_D @ sk_A) | (v1_xboole_0 @ sk_C))),
% 3.35/3.55      inference('sup-', [status(thm)], ['103', '104'])).
% 3.35/3.55  thf('106', plain,
% 3.35/3.55      (((v1_xboole_0 @ sk_C)
% 3.35/3.55        | (v3_pre_topc @ (k2_xboole_0 @ sk_C @ sk_D) @ sk_A))),
% 3.35/3.55      inference('clc', [status(thm)], ['90', '105'])).
% 3.35/3.55  thf('107', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 3.35/3.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.35/3.55  thf('108', plain,
% 3.35/3.55      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.35/3.55      inference('sup-', [status(thm)], ['49', '50'])).
% 3.35/3.55  thf('109', plain,
% 3.35/3.55      (![X34 : $i, X35 : $i, X36 : $i]:
% 3.35/3.55         (~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (u1_struct_0 @ X35)))
% 3.35/3.55          | ~ (m1_connsp_2 @ X34 @ X35 @ X36)
% 3.35/3.55          | (r2_hidden @ X36 @ X34)
% 3.35/3.55          | ~ (m1_subset_1 @ X36 @ (u1_struct_0 @ X35))
% 3.35/3.55          | ~ (l1_pre_topc @ X35)
% 3.35/3.55          | ~ (v2_pre_topc @ X35)
% 3.35/3.55          | (v2_struct_0 @ X35))),
% 3.35/3.55      inference('cnf', [status(esa)], [t6_connsp_2])).
% 3.35/3.55  thf('110', plain,
% 3.35/3.55      (![X0 : $i]:
% 3.35/3.55         ((v2_struct_0 @ sk_A)
% 3.35/3.55          | ~ (v2_pre_topc @ sk_A)
% 3.35/3.55          | ~ (l1_pre_topc @ sk_A)
% 3.35/3.55          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 3.35/3.55          | (r2_hidden @ X0 @ sk_C)
% 3.35/3.55          | ~ (m1_connsp_2 @ sk_C @ sk_A @ X0))),
% 3.35/3.55      inference('sup-', [status(thm)], ['108', '109'])).
% 3.35/3.55  thf('111', plain, ((v2_pre_topc @ sk_A)),
% 3.35/3.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.35/3.55  thf('112', plain, ((l1_pre_topc @ sk_A)),
% 3.35/3.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.35/3.55  thf('113', plain,
% 3.35/3.55      (![X0 : $i]:
% 3.35/3.55         ((v2_struct_0 @ sk_A)
% 3.35/3.55          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 3.35/3.55          | (r2_hidden @ X0 @ sk_C)
% 3.35/3.55          | ~ (m1_connsp_2 @ sk_C @ sk_A @ X0))),
% 3.35/3.55      inference('demod', [status(thm)], ['110', '111', '112'])).
% 3.35/3.55  thf('114', plain,
% 3.35/3.55      ((~ (m1_connsp_2 @ sk_C @ sk_A @ sk_B_1)
% 3.35/3.55        | (r2_hidden @ sk_B_1 @ sk_C)
% 3.35/3.55        | (v2_struct_0 @ sk_A))),
% 3.35/3.55      inference('sup-', [status(thm)], ['107', '113'])).
% 3.35/3.55  thf('115', plain, ((m1_connsp_2 @ sk_C @ sk_A @ sk_B_1)),
% 3.35/3.55      inference('clc', [status(thm)], ['47', '48'])).
% 3.35/3.55  thf('116', plain, (((r2_hidden @ sk_B_1 @ sk_C) | (v2_struct_0 @ sk_A))),
% 3.35/3.55      inference('demod', [status(thm)], ['114', '115'])).
% 3.35/3.55  thf('117', plain, (~ (v2_struct_0 @ sk_A)),
% 3.35/3.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.35/3.55  thf('118', plain, ((r2_hidden @ sk_B_1 @ sk_C)),
% 3.35/3.55      inference('clc', [status(thm)], ['116', '117'])).
% 3.35/3.55  thf('119', plain,
% 3.35/3.55      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 3.35/3.55      inference('cnf', [status(esa)], [d1_xboole_0])).
% 3.35/3.55  thf('120', plain, (~ (v1_xboole_0 @ sk_C)),
% 3.35/3.55      inference('sup-', [status(thm)], ['118', '119'])).
% 3.35/3.55  thf('121', plain, ((v3_pre_topc @ (k2_xboole_0 @ sk_C @ sk_D) @ sk_A)),
% 3.35/3.55      inference('clc', [status(thm)], ['106', '120'])).
% 3.35/3.55  thf('122', plain,
% 3.35/3.55      (![X0 : $i]:
% 3.35/3.55         ((v2_struct_0 @ sk_A)
% 3.35/3.55          | (r2_hidden @ (k2_xboole_0 @ sk_C @ sk_D) @ 
% 3.35/3.55             (u1_struct_0 @ (k9_yellow_6 @ sk_A @ X0)))
% 3.35/3.55          | ~ (r2_hidden @ X0 @ (k2_xboole_0 @ sk_C @ sk_D))
% 3.35/3.55          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 3.35/3.55      inference('demod', [status(thm)], ['62', '63', '64', '121'])).
% 3.35/3.55  thf('123', plain,
% 3.35/3.55      ((~ (m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 3.35/3.55        | (r2_hidden @ (k2_xboole_0 @ sk_C @ sk_D) @ 
% 3.35/3.55           (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B_1)))
% 3.35/3.55        | (v2_struct_0 @ sk_A))),
% 3.35/3.55      inference('sup-', [status(thm)], ['39', '122'])).
% 3.35/3.55  thf('124', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 3.35/3.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.35/3.55  thf('125', plain,
% 3.35/3.55      (((r2_hidden @ (k2_xboole_0 @ sk_C @ sk_D) @ 
% 3.35/3.55         (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B_1)))
% 3.35/3.55        | (v2_struct_0 @ sk_A))),
% 3.35/3.55      inference('demod', [status(thm)], ['123', '124'])).
% 3.35/3.55  thf('126', plain, (~ (v2_struct_0 @ sk_A)),
% 3.35/3.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.35/3.55  thf('127', plain,
% 3.35/3.55      ((r2_hidden @ (k2_xboole_0 @ sk_C @ sk_D) @ 
% 3.35/3.55        (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B_1)))),
% 3.35/3.55      inference('clc', [status(thm)], ['125', '126'])).
% 3.35/3.55  thf(t1_subset, axiom,
% 3.35/3.55    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 3.35/3.55  thf('128', plain,
% 3.35/3.55      (![X21 : $i, X22 : $i]:
% 3.35/3.55         ((m1_subset_1 @ X21 @ X22) | ~ (r2_hidden @ X21 @ X22))),
% 3.35/3.55      inference('cnf', [status(esa)], [t1_subset])).
% 3.35/3.55  thf('129', plain,
% 3.35/3.55      ((m1_subset_1 @ (k2_xboole_0 @ sk_C @ sk_D) @ 
% 3.35/3.55        (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B_1)))),
% 3.35/3.55      inference('sup-', [status(thm)], ['127', '128'])).
% 3.35/3.55  thf('130', plain, ($false), inference('demod', [status(thm)], ['0', '129'])).
% 3.35/3.55  
% 3.35/3.55  % SZS output end Refutation
% 3.35/3.55  
% 3.35/3.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
