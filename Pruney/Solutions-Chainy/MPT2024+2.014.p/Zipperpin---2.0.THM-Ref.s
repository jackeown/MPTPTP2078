%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.8goKp3SZI8

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:14:28 EST 2020

% Result     : Theorem 2.30s
% Output     : Refutation 2.30s
% Verified   : 
% Statistics : Number of formulae       :  131 ( 432 expanded)
%              Number of leaves         :   26 ( 139 expanded)
%              Depth                    :   18
%              Number of atoms          : 1058 (8046 expanded)
%              Number of equality atoms :   16 (  58 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k9_yellow_6_type,type,(
    k9_yellow_6: $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

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
    ~ ( m1_subset_1 @ ( k2_xboole_0 @ sk_C_1 @ sk_D_1 ) @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t38_yellow_6,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ ( k9_yellow_6 @ A @ B ) ) )
             => ? [D: $i] :
                  ( ( v3_pre_topc @ D @ A )
                  & ( r2_hidden @ B @ D )
                  & ( D = C )
                  & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) )).

thf('2',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( u1_struct_0 @ X21 ) )
      | ( r2_hidden @ X20 @ ( sk_D @ X22 @ X20 @ X21 ) )
      | ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ ( k9_yellow_6 @ X21 @ X20 ) ) )
      | ~ ( l1_pre_topc @ X21 )
      | ~ ( v2_pre_topc @ X21 )
      | ( v2_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t38_yellow_6])).

thf('3',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( r2_hidden @ sk_B @ ( sk_D @ sk_C_1 @ sk_B @ sk_A ) )
    | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( u1_struct_0 @ X21 ) )
      | ( ( sk_D @ X22 @ X20 @ X21 )
        = X22 )
      | ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ ( k9_yellow_6 @ X21 @ X20 ) ) )
      | ~ ( l1_pre_topc @ X21 )
      | ~ ( v2_pre_topc @ X21 )
      | ( v2_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t38_yellow_6])).

thf('8',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( ( sk_D @ sk_C_1 @ sk_B @ sk_A )
      = sk_C_1 )
    | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( sk_D @ sk_C_1 @ sk_B @ sk_A )
      = sk_C_1 ) ),
    inference(demod,[status(thm)],['8','9','10','11'])).

thf('13',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ( sk_D @ sk_C_1 @ sk_B @ sk_A )
    = sk_C_1 ),
    inference(clc,[status(thm)],['12','13'])).

thf('15',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ sk_B @ sk_C_1 ) ),
    inference(demod,[status(thm)],['3','4','5','14','15'])).

thf('17',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    r2_hidden @ sk_B @ sk_C_1 ),
    inference(clc,[status(thm)],['16','17'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('19',plain,(
    ! [X4: $i,X5: $i] :
      ( r1_tarski @ X4 @ ( k2_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( r2_hidden @ sk_B @ ( k2_xboole_0 @ sk_C_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','21'])).

thf('23',plain,(
    m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( u1_struct_0 @ X21 ) )
      | ( m1_subset_1 @ ( sk_D @ X22 @ X20 @ X21 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ ( k9_yellow_6 @ X21 @ X20 ) ) )
      | ~ ( l1_pre_topc @ X21 )
      | ~ ( v2_pre_topc @ X21 )
      | ( v2_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t38_yellow_6])).

thf('25',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( m1_subset_1 @ ( sk_D @ sk_D_1 @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( u1_struct_0 @ X21 ) )
      | ( ( sk_D @ X22 @ X20 @ X21 )
        = X22 )
      | ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ ( k9_yellow_6 @ X21 @ X20 ) ) )
      | ~ ( l1_pre_topc @ X21 )
      | ~ ( v2_pre_topc @ X21 )
      | ( v2_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t38_yellow_6])).

thf('30',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( ( sk_D @ sk_D_1 @ sk_B @ sk_A )
      = sk_D_1 )
    | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( sk_D @ sk_D_1 @ sk_B @ sk_A )
      = sk_D_1 ) ),
    inference(demod,[status(thm)],['30','31','32','33'])).

thf('35',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ( sk_D @ sk_D_1 @ sk_B @ sk_A )
    = sk_D_1 ),
    inference(clc,[status(thm)],['34','35'])).

thf('37',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['25','26','27','36','37'])).

thf('39',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['38','39'])).

thf('41',plain,(
    m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( u1_struct_0 @ X21 ) )
      | ( m1_subset_1 @ ( sk_D @ X22 @ X20 @ X21 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ ( k9_yellow_6 @ X21 @ X20 ) ) )
      | ~ ( l1_pre_topc @ X21 )
      | ~ ( v2_pre_topc @ X21 )
      | ( v2_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t38_yellow_6])).

thf('43',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( m1_subset_1 @ ( sk_D @ sk_C_1 @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( ( sk_D @ sk_C_1 @ sk_B @ sk_A )
    = sk_C_1 ),
    inference(clc,[status(thm)],['12','13'])).

thf('47',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['43','44','45','46','47'])).

thf('49',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['48','49'])).

thf(dt_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( m1_subset_1 @ ( k4_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('51',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X7 ) )
      | ( m1_subset_1 @ ( k4_subset_1 @ X7 @ X6 @ X8 ) @ ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k4_subset_1])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    m1_subset_1 @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 @ sk_D_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['40','52'])).

thf('54',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['38','39'])).

thf('55',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['48','49'])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('56',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X10 ) )
      | ( ( k4_subset_1 @ X10 @ X9 @ X11 )
        = ( k2_xboole_0 @ X9 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 @ X0 )
        = ( k2_xboole_0 @ sk_C_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,
    ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 @ sk_D_1 )
    = ( k2_xboole_0 @ sk_C_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['54','57'])).

thf('59',plain,(
    m1_subset_1 @ ( k2_xboole_0 @ sk_C_1 @ sk_D_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['53','58'])).

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

thf('60',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( u1_struct_0 @ X24 ) )
      | ~ ( r2_hidden @ X23 @ X25 )
      | ~ ( v3_pre_topc @ X25 @ X24 )
      | ( r2_hidden @ X25 @ ( u1_struct_0 @ ( k9_yellow_6 @ X24 @ X23 ) ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ~ ( l1_pre_topc @ X24 )
      | ~ ( v2_pre_topc @ X24 )
      | ( v2_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t39_yellow_6])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( r2_hidden @ ( k2_xboole_0 @ sk_C_1 @ sk_D_1 ) @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ X0 ) ) )
      | ~ ( v3_pre_topc @ ( k2_xboole_0 @ sk_C_1 @ sk_D_1 ) @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( k2_xboole_0 @ sk_C_1 @ sk_D_1 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ ( k2_xboole_0 @ sk_C_1 @ sk_D_1 ) @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ X0 ) ) )
      | ~ ( v3_pre_topc @ ( k2_xboole_0 @ sk_C_1 @ sk_D_1 ) @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( k2_xboole_0 @ sk_C_1 @ sk_D_1 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['61','62','63'])).

thf('65',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['38','39'])).

thf('66',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['48','49'])).

thf(fc7_tops_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( v3_pre_topc @ B @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
        & ( v3_pre_topc @ C @ A )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v3_pre_topc @ ( k2_xboole_0 @ B @ C ) @ A ) ) )).

thf('67',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( v3_pre_topc @ X17 @ X18 )
      | ~ ( l1_pre_topc @ X18 )
      | ~ ( v2_pre_topc @ X18 )
      | ~ ( v3_pre_topc @ X19 @ X18 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ( v3_pre_topc @ ( k2_xboole_0 @ X17 @ X19 ) @ X18 ) ) ),
    inference(cnf,[status(esa)],[fc7_tops_1])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( v3_pre_topc @ ( k2_xboole_0 @ sk_C_1 @ X0 ) @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v3_pre_topc @ X0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v3_pre_topc @ sk_C_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( v3_pre_topc @ ( k2_xboole_0 @ sk_C_1 @ X0 ) @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v3_pre_topc @ X0 @ sk_A )
      | ~ ( v3_pre_topc @ sk_C_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['68','69','70'])).

thf('72',plain,(
    m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( u1_struct_0 @ X21 ) )
      | ( v3_pre_topc @ ( sk_D @ X22 @ X20 @ X21 ) @ X21 )
      | ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ ( k9_yellow_6 @ X21 @ X20 ) ) )
      | ~ ( l1_pre_topc @ X21 )
      | ~ ( v2_pre_topc @ X21 )
      | ( v2_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t38_yellow_6])).

thf('74',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v3_pre_topc @ ( sk_D @ sk_C_1 @ sk_B @ sk_A ) @ sk_A )
    | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,
    ( ( sk_D @ sk_C_1 @ sk_B @ sk_A )
    = sk_C_1 ),
    inference(clc,[status(thm)],['12','13'])).

thf('78',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v3_pre_topc @ sk_C_1 @ sk_A ) ),
    inference(demod,[status(thm)],['74','75','76','77','78'])).

thf('80',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    v3_pre_topc @ sk_C_1 @ sk_A ),
    inference(clc,[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X0: $i] :
      ( ( v3_pre_topc @ ( k2_xboole_0 @ sk_C_1 @ X0 ) @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v3_pre_topc @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['71','81'])).

thf('83',plain,
    ( ~ ( v3_pre_topc @ sk_D_1 @ sk_A )
    | ( v3_pre_topc @ ( k2_xboole_0 @ sk_C_1 @ sk_D_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['65','82'])).

thf('84',plain,(
    m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( u1_struct_0 @ X21 ) )
      | ( v3_pre_topc @ ( sk_D @ X22 @ X20 @ X21 ) @ X21 )
      | ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ ( k9_yellow_6 @ X21 @ X20 ) ) )
      | ~ ( l1_pre_topc @ X21 )
      | ~ ( v2_pre_topc @ X21 )
      | ( v2_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t38_yellow_6])).

thf('86',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v3_pre_topc @ ( sk_D @ sk_D_1 @ sk_B @ sk_A ) @ sk_A )
    | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,
    ( ( sk_D @ sk_D_1 @ sk_B @ sk_A )
    = sk_D_1 ),
    inference(clc,[status(thm)],['34','35'])).

thf('90',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v3_pre_topc @ sk_D_1 @ sk_A ) ),
    inference(demod,[status(thm)],['86','87','88','89','90'])).

thf('92',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    v3_pre_topc @ sk_D_1 @ sk_A ),
    inference(clc,[status(thm)],['91','92'])).

thf('94',plain,(
    v3_pre_topc @ ( k2_xboole_0 @ sk_C_1 @ sk_D_1 ) @ sk_A ),
    inference(demod,[status(thm)],['83','93'])).

thf('95',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ ( k2_xboole_0 @ sk_C_1 @ sk_D_1 ) @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ X0 ) ) )
      | ~ ( r2_hidden @ X0 @ ( k2_xboole_0 @ sk_C_1 @ sk_D_1 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['64','94'])).

thf('96',plain,
    ( ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( k2_xboole_0 @ sk_C_1 @ sk_D_1 ) @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['22','95'])).

thf('97',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,
    ( ( r2_hidden @ ( k2_xboole_0 @ sk_C_1 @ sk_D_1 ) @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['96','97'])).

thf('99',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    r2_hidden @ ( k2_xboole_0 @ sk_C_1 @ sk_D_1 ) @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['98','99'])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('101',plain,(
    ! [X12: $i,X13: $i] :
      ( ( m1_subset_1 @ X12 @ X13 )
      | ~ ( r2_hidden @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('102',plain,(
    m1_subset_1 @ ( k2_xboole_0 @ sk_C_1 @ sk_D_1 ) @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,(
    $false ),
    inference(demod,[status(thm)],['0','102'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.8goKp3SZI8
% 0.14/0.35  % Computer   : n016.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 16:38:04 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 2.30/2.48  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 2.30/2.48  % Solved by: fo/fo7.sh
% 2.30/2.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.30/2.48  % done 969 iterations in 2.015s
% 2.30/2.48  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 2.30/2.48  % SZS output start Refutation
% 2.30/2.48  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 2.30/2.48  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 2.30/2.48  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 2.30/2.48  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 2.30/2.48  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 2.30/2.48  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 2.30/2.48  thf(sk_B_type, type, sk_B: $i).
% 2.30/2.48  thf(sk_D_1_type, type, sk_D_1: $i).
% 2.30/2.48  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 2.30/2.48  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 2.30/2.48  thf(sk_C_1_type, type, sk_C_1: $i).
% 2.30/2.48  thf(k9_yellow_6_type, type, k9_yellow_6: $i > $i > $i).
% 2.30/2.48  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 2.30/2.48  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 2.30/2.48  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 2.30/2.48  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 2.30/2.48  thf(sk_A_type, type, sk_A: $i).
% 2.30/2.48  thf(t23_waybel_9, conjecture,
% 2.30/2.48    (![A:$i]:
% 2.30/2.48     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 2.30/2.48       ( ![B:$i]:
% 2.30/2.48         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 2.30/2.48           ( ![C:$i]:
% 2.30/2.48             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ ( k9_yellow_6 @ A @ B ) ) ) =>
% 2.30/2.48               ( ![D:$i]:
% 2.30/2.48                 ( ( m1_subset_1 @
% 2.30/2.48                     D @ ( u1_struct_0 @ ( k9_yellow_6 @ A @ B ) ) ) =>
% 2.30/2.48                   ( m1_subset_1 @
% 2.30/2.48                     ( k2_xboole_0 @ C @ D ) @ 
% 2.30/2.48                     ( u1_struct_0 @ ( k9_yellow_6 @ A @ B ) ) ) ) ) ) ) ) ) ))).
% 2.30/2.48  thf(zf_stmt_0, negated_conjecture,
% 2.30/2.48    (~( ![A:$i]:
% 2.30/2.48        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 2.30/2.48            ( l1_pre_topc @ A ) ) =>
% 2.30/2.48          ( ![B:$i]:
% 2.30/2.48            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 2.30/2.48              ( ![C:$i]:
% 2.30/2.48                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ ( k9_yellow_6 @ A @ B ) ) ) =>
% 2.30/2.48                  ( ![D:$i]:
% 2.30/2.48                    ( ( m1_subset_1 @
% 2.30/2.48                        D @ ( u1_struct_0 @ ( k9_yellow_6 @ A @ B ) ) ) =>
% 2.30/2.48                      ( m1_subset_1 @
% 2.30/2.48                        ( k2_xboole_0 @ C @ D ) @ 
% 2.30/2.48                        ( u1_struct_0 @ ( k9_yellow_6 @ A @ B ) ) ) ) ) ) ) ) ) ) )),
% 2.30/2.48    inference('cnf.neg', [status(esa)], [t23_waybel_9])).
% 2.30/2.48  thf('0', plain,
% 2.30/2.48      (~ (m1_subset_1 @ (k2_xboole_0 @ sk_C_1 @ sk_D_1) @ 
% 2.30/2.48          (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B)))),
% 2.30/2.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.30/2.48  thf('1', plain,
% 2.30/2.48      ((m1_subset_1 @ sk_C_1 @ (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B)))),
% 2.30/2.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.30/2.48  thf(t38_yellow_6, axiom,
% 2.30/2.48    (![A:$i]:
% 2.30/2.48     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 2.30/2.48       ( ![B:$i]:
% 2.30/2.48         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 2.30/2.48           ( ![C:$i]:
% 2.30/2.48             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ ( k9_yellow_6 @ A @ B ) ) ) =>
% 2.30/2.48               ( ?[D:$i]:
% 2.30/2.48                 ( ( v3_pre_topc @ D @ A ) & ( r2_hidden @ B @ D ) & 
% 2.30/2.48                   ( ( D ) = ( C ) ) & 
% 2.30/2.48                   ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ) ) ))).
% 2.30/2.48  thf('2', plain,
% 2.30/2.48      (![X20 : $i, X21 : $i, X22 : $i]:
% 2.30/2.48         (~ (m1_subset_1 @ X20 @ (u1_struct_0 @ X21))
% 2.30/2.48          | (r2_hidden @ X20 @ (sk_D @ X22 @ X20 @ X21))
% 2.30/2.48          | ~ (m1_subset_1 @ X22 @ (u1_struct_0 @ (k9_yellow_6 @ X21 @ X20)))
% 2.30/2.48          | ~ (l1_pre_topc @ X21)
% 2.30/2.48          | ~ (v2_pre_topc @ X21)
% 2.30/2.48          | (v2_struct_0 @ X21))),
% 2.30/2.48      inference('cnf', [status(esa)], [t38_yellow_6])).
% 2.30/2.48  thf('3', plain,
% 2.30/2.48      (((v2_struct_0 @ sk_A)
% 2.30/2.48        | ~ (v2_pre_topc @ sk_A)
% 2.30/2.48        | ~ (l1_pre_topc @ sk_A)
% 2.30/2.48        | (r2_hidden @ sk_B @ (sk_D @ sk_C_1 @ sk_B @ sk_A))
% 2.30/2.48        | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 2.30/2.48      inference('sup-', [status(thm)], ['1', '2'])).
% 2.30/2.48  thf('4', plain, ((v2_pre_topc @ sk_A)),
% 2.30/2.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.30/2.48  thf('5', plain, ((l1_pre_topc @ sk_A)),
% 2.30/2.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.30/2.48  thf('6', plain,
% 2.30/2.48      ((m1_subset_1 @ sk_C_1 @ (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B)))),
% 2.30/2.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.30/2.48  thf('7', plain,
% 2.30/2.48      (![X20 : $i, X21 : $i, X22 : $i]:
% 2.30/2.48         (~ (m1_subset_1 @ X20 @ (u1_struct_0 @ X21))
% 2.30/2.48          | ((sk_D @ X22 @ X20 @ X21) = (X22))
% 2.30/2.48          | ~ (m1_subset_1 @ X22 @ (u1_struct_0 @ (k9_yellow_6 @ X21 @ X20)))
% 2.30/2.48          | ~ (l1_pre_topc @ X21)
% 2.30/2.48          | ~ (v2_pre_topc @ X21)
% 2.30/2.48          | (v2_struct_0 @ X21))),
% 2.30/2.48      inference('cnf', [status(esa)], [t38_yellow_6])).
% 2.30/2.48  thf('8', plain,
% 2.30/2.48      (((v2_struct_0 @ sk_A)
% 2.30/2.48        | ~ (v2_pre_topc @ sk_A)
% 2.30/2.48        | ~ (l1_pre_topc @ sk_A)
% 2.30/2.48        | ((sk_D @ sk_C_1 @ sk_B @ sk_A) = (sk_C_1))
% 2.30/2.48        | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 2.30/2.48      inference('sup-', [status(thm)], ['6', '7'])).
% 2.30/2.48  thf('9', plain, ((v2_pre_topc @ sk_A)),
% 2.30/2.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.30/2.48  thf('10', plain, ((l1_pre_topc @ sk_A)),
% 2.30/2.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.30/2.48  thf('11', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 2.30/2.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.30/2.48  thf('12', plain,
% 2.30/2.48      (((v2_struct_0 @ sk_A) | ((sk_D @ sk_C_1 @ sk_B @ sk_A) = (sk_C_1)))),
% 2.30/2.48      inference('demod', [status(thm)], ['8', '9', '10', '11'])).
% 2.30/2.48  thf('13', plain, (~ (v2_struct_0 @ sk_A)),
% 2.30/2.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.30/2.48  thf('14', plain, (((sk_D @ sk_C_1 @ sk_B @ sk_A) = (sk_C_1))),
% 2.30/2.48      inference('clc', [status(thm)], ['12', '13'])).
% 2.30/2.48  thf('15', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 2.30/2.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.30/2.48  thf('16', plain, (((v2_struct_0 @ sk_A) | (r2_hidden @ sk_B @ sk_C_1))),
% 2.30/2.48      inference('demod', [status(thm)], ['3', '4', '5', '14', '15'])).
% 2.30/2.48  thf('17', plain, (~ (v2_struct_0 @ sk_A)),
% 2.30/2.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.30/2.48  thf('18', plain, ((r2_hidden @ sk_B @ sk_C_1)),
% 2.30/2.48      inference('clc', [status(thm)], ['16', '17'])).
% 2.30/2.48  thf(t7_xboole_1, axiom,
% 2.30/2.48    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 2.30/2.48  thf('19', plain,
% 2.30/2.48      (![X4 : $i, X5 : $i]: (r1_tarski @ X4 @ (k2_xboole_0 @ X4 @ X5))),
% 2.30/2.48      inference('cnf', [status(esa)], [t7_xboole_1])).
% 2.30/2.48  thf(d3_tarski, axiom,
% 2.30/2.48    (![A:$i,B:$i]:
% 2.30/2.48     ( ( r1_tarski @ A @ B ) <=>
% 2.30/2.48       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 2.30/2.48  thf('20', plain,
% 2.30/2.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.30/2.48         (~ (r2_hidden @ X0 @ X1)
% 2.30/2.48          | (r2_hidden @ X0 @ X2)
% 2.30/2.48          | ~ (r1_tarski @ X1 @ X2))),
% 2.30/2.48      inference('cnf', [status(esa)], [d3_tarski])).
% 2.30/2.48  thf('21', plain,
% 2.30/2.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.30/2.48         ((r2_hidden @ X2 @ (k2_xboole_0 @ X1 @ X0)) | ~ (r2_hidden @ X2 @ X1))),
% 2.30/2.48      inference('sup-', [status(thm)], ['19', '20'])).
% 2.30/2.48  thf('22', plain,
% 2.30/2.48      (![X0 : $i]: (r2_hidden @ sk_B @ (k2_xboole_0 @ sk_C_1 @ X0))),
% 2.30/2.48      inference('sup-', [status(thm)], ['18', '21'])).
% 2.30/2.48  thf('23', plain,
% 2.30/2.48      ((m1_subset_1 @ sk_D_1 @ (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B)))),
% 2.30/2.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.30/2.48  thf('24', plain,
% 2.30/2.48      (![X20 : $i, X21 : $i, X22 : $i]:
% 2.30/2.48         (~ (m1_subset_1 @ X20 @ (u1_struct_0 @ X21))
% 2.30/2.48          | (m1_subset_1 @ (sk_D @ X22 @ X20 @ X21) @ 
% 2.30/2.48             (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 2.30/2.48          | ~ (m1_subset_1 @ X22 @ (u1_struct_0 @ (k9_yellow_6 @ X21 @ X20)))
% 2.30/2.48          | ~ (l1_pre_topc @ X21)
% 2.30/2.48          | ~ (v2_pre_topc @ X21)
% 2.30/2.48          | (v2_struct_0 @ X21))),
% 2.30/2.48      inference('cnf', [status(esa)], [t38_yellow_6])).
% 2.30/2.48  thf('25', plain,
% 2.30/2.48      (((v2_struct_0 @ sk_A)
% 2.30/2.48        | ~ (v2_pre_topc @ sk_A)
% 2.30/2.48        | ~ (l1_pre_topc @ sk_A)
% 2.30/2.48        | (m1_subset_1 @ (sk_D @ sk_D_1 @ sk_B @ sk_A) @ 
% 2.30/2.48           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 2.30/2.48        | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 2.30/2.48      inference('sup-', [status(thm)], ['23', '24'])).
% 2.30/2.48  thf('26', plain, ((v2_pre_topc @ sk_A)),
% 2.30/2.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.30/2.48  thf('27', plain, ((l1_pre_topc @ sk_A)),
% 2.30/2.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.30/2.48  thf('28', plain,
% 2.30/2.48      ((m1_subset_1 @ sk_D_1 @ (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B)))),
% 2.30/2.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.30/2.48  thf('29', plain,
% 2.30/2.48      (![X20 : $i, X21 : $i, X22 : $i]:
% 2.30/2.48         (~ (m1_subset_1 @ X20 @ (u1_struct_0 @ X21))
% 2.30/2.48          | ((sk_D @ X22 @ X20 @ X21) = (X22))
% 2.30/2.48          | ~ (m1_subset_1 @ X22 @ (u1_struct_0 @ (k9_yellow_6 @ X21 @ X20)))
% 2.30/2.48          | ~ (l1_pre_topc @ X21)
% 2.30/2.48          | ~ (v2_pre_topc @ X21)
% 2.30/2.48          | (v2_struct_0 @ X21))),
% 2.30/2.48      inference('cnf', [status(esa)], [t38_yellow_6])).
% 2.30/2.48  thf('30', plain,
% 2.30/2.48      (((v2_struct_0 @ sk_A)
% 2.30/2.48        | ~ (v2_pre_topc @ sk_A)
% 2.30/2.48        | ~ (l1_pre_topc @ sk_A)
% 2.30/2.48        | ((sk_D @ sk_D_1 @ sk_B @ sk_A) = (sk_D_1))
% 2.30/2.48        | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 2.30/2.48      inference('sup-', [status(thm)], ['28', '29'])).
% 2.30/2.48  thf('31', plain, ((v2_pre_topc @ sk_A)),
% 2.30/2.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.30/2.48  thf('32', plain, ((l1_pre_topc @ sk_A)),
% 2.30/2.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.30/2.48  thf('33', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 2.30/2.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.30/2.48  thf('34', plain,
% 2.30/2.48      (((v2_struct_0 @ sk_A) | ((sk_D @ sk_D_1 @ sk_B @ sk_A) = (sk_D_1)))),
% 2.30/2.48      inference('demod', [status(thm)], ['30', '31', '32', '33'])).
% 2.30/2.48  thf('35', plain, (~ (v2_struct_0 @ sk_A)),
% 2.30/2.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.30/2.48  thf('36', plain, (((sk_D @ sk_D_1 @ sk_B @ sk_A) = (sk_D_1))),
% 2.30/2.48      inference('clc', [status(thm)], ['34', '35'])).
% 2.30/2.48  thf('37', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 2.30/2.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.30/2.48  thf('38', plain,
% 2.30/2.48      (((v2_struct_0 @ sk_A)
% 2.30/2.48        | (m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 2.30/2.48      inference('demod', [status(thm)], ['25', '26', '27', '36', '37'])).
% 2.30/2.48  thf('39', plain, (~ (v2_struct_0 @ sk_A)),
% 2.30/2.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.30/2.48  thf('40', plain,
% 2.30/2.48      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.30/2.48      inference('clc', [status(thm)], ['38', '39'])).
% 2.30/2.48  thf('41', plain,
% 2.30/2.48      ((m1_subset_1 @ sk_C_1 @ (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B)))),
% 2.30/2.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.30/2.48  thf('42', plain,
% 2.30/2.48      (![X20 : $i, X21 : $i, X22 : $i]:
% 2.30/2.48         (~ (m1_subset_1 @ X20 @ (u1_struct_0 @ X21))
% 2.30/2.48          | (m1_subset_1 @ (sk_D @ X22 @ X20 @ X21) @ 
% 2.30/2.48             (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 2.30/2.48          | ~ (m1_subset_1 @ X22 @ (u1_struct_0 @ (k9_yellow_6 @ X21 @ X20)))
% 2.30/2.48          | ~ (l1_pre_topc @ X21)
% 2.30/2.48          | ~ (v2_pre_topc @ X21)
% 2.30/2.48          | (v2_struct_0 @ X21))),
% 2.30/2.48      inference('cnf', [status(esa)], [t38_yellow_6])).
% 2.30/2.48  thf('43', plain,
% 2.30/2.48      (((v2_struct_0 @ sk_A)
% 2.30/2.48        | ~ (v2_pre_topc @ sk_A)
% 2.30/2.48        | ~ (l1_pre_topc @ sk_A)
% 2.30/2.48        | (m1_subset_1 @ (sk_D @ sk_C_1 @ sk_B @ sk_A) @ 
% 2.30/2.48           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 2.30/2.48        | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 2.30/2.48      inference('sup-', [status(thm)], ['41', '42'])).
% 2.30/2.48  thf('44', plain, ((v2_pre_topc @ sk_A)),
% 2.30/2.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.30/2.48  thf('45', plain, ((l1_pre_topc @ sk_A)),
% 2.30/2.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.30/2.48  thf('46', plain, (((sk_D @ sk_C_1 @ sk_B @ sk_A) = (sk_C_1))),
% 2.30/2.48      inference('clc', [status(thm)], ['12', '13'])).
% 2.30/2.48  thf('47', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 2.30/2.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.30/2.48  thf('48', plain,
% 2.30/2.48      (((v2_struct_0 @ sk_A)
% 2.30/2.48        | (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 2.30/2.48      inference('demod', [status(thm)], ['43', '44', '45', '46', '47'])).
% 2.30/2.48  thf('49', plain, (~ (v2_struct_0 @ sk_A)),
% 2.30/2.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.30/2.48  thf('50', plain,
% 2.30/2.48      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.30/2.48      inference('clc', [status(thm)], ['48', '49'])).
% 2.30/2.48  thf(dt_k4_subset_1, axiom,
% 2.30/2.48    (![A:$i,B:$i,C:$i]:
% 2.30/2.48     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 2.30/2.48         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 2.30/2.48       ( m1_subset_1 @ ( k4_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 2.30/2.48  thf('51', plain,
% 2.30/2.48      (![X6 : $i, X7 : $i, X8 : $i]:
% 2.30/2.48         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7))
% 2.30/2.48          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X7))
% 2.30/2.48          | (m1_subset_1 @ (k4_subset_1 @ X7 @ X6 @ X8) @ (k1_zfmisc_1 @ X7)))),
% 2.30/2.48      inference('cnf', [status(esa)], [dt_k4_subset_1])).
% 2.30/2.48  thf('52', plain,
% 2.30/2.48      (![X0 : $i]:
% 2.30/2.48         ((m1_subset_1 @ (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C_1 @ X0) @ 
% 2.30/2.48           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 2.30/2.48          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 2.30/2.48      inference('sup-', [status(thm)], ['50', '51'])).
% 2.30/2.48  thf('53', plain,
% 2.30/2.48      ((m1_subset_1 @ (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C_1 @ sk_D_1) @ 
% 2.30/2.48        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.30/2.48      inference('sup-', [status(thm)], ['40', '52'])).
% 2.30/2.48  thf('54', plain,
% 2.30/2.48      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.30/2.48      inference('clc', [status(thm)], ['38', '39'])).
% 2.30/2.48  thf('55', plain,
% 2.30/2.48      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.30/2.48      inference('clc', [status(thm)], ['48', '49'])).
% 2.30/2.48  thf(redefinition_k4_subset_1, axiom,
% 2.30/2.48    (![A:$i,B:$i,C:$i]:
% 2.30/2.48     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 2.30/2.48         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 2.30/2.48       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 2.30/2.48  thf('56', plain,
% 2.30/2.48      (![X9 : $i, X10 : $i, X11 : $i]:
% 2.30/2.48         (~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10))
% 2.30/2.48          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X10))
% 2.30/2.48          | ((k4_subset_1 @ X10 @ X9 @ X11) = (k2_xboole_0 @ X9 @ X11)))),
% 2.30/2.48      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 2.30/2.48  thf('57', plain,
% 2.30/2.48      (![X0 : $i]:
% 2.30/2.48         (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C_1 @ X0)
% 2.30/2.48            = (k2_xboole_0 @ sk_C_1 @ X0))
% 2.30/2.48          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 2.30/2.48      inference('sup-', [status(thm)], ['55', '56'])).
% 2.30/2.48  thf('58', plain,
% 2.30/2.48      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C_1 @ sk_D_1)
% 2.30/2.48         = (k2_xboole_0 @ sk_C_1 @ sk_D_1))),
% 2.30/2.48      inference('sup-', [status(thm)], ['54', '57'])).
% 2.30/2.48  thf('59', plain,
% 2.30/2.48      ((m1_subset_1 @ (k2_xboole_0 @ sk_C_1 @ sk_D_1) @ 
% 2.30/2.48        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.30/2.48      inference('demod', [status(thm)], ['53', '58'])).
% 2.30/2.48  thf(t39_yellow_6, axiom,
% 2.30/2.48    (![A:$i]:
% 2.30/2.48     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 2.30/2.48       ( ![B:$i]:
% 2.30/2.48         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 2.30/2.48           ( ![C:$i]:
% 2.30/2.48             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.30/2.48               ( ( r2_hidden @ C @ ( u1_struct_0 @ ( k9_yellow_6 @ A @ B ) ) ) <=>
% 2.30/2.48                 ( ( r2_hidden @ B @ C ) & ( v3_pre_topc @ C @ A ) ) ) ) ) ) ) ))).
% 2.30/2.48  thf('60', plain,
% 2.30/2.48      (![X23 : $i, X24 : $i, X25 : $i]:
% 2.30/2.48         (~ (m1_subset_1 @ X23 @ (u1_struct_0 @ X24))
% 2.30/2.48          | ~ (r2_hidden @ X23 @ X25)
% 2.30/2.48          | ~ (v3_pre_topc @ X25 @ X24)
% 2.30/2.48          | (r2_hidden @ X25 @ (u1_struct_0 @ (k9_yellow_6 @ X24 @ X23)))
% 2.30/2.48          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 2.30/2.48          | ~ (l1_pre_topc @ X24)
% 2.30/2.48          | ~ (v2_pre_topc @ X24)
% 2.30/2.48          | (v2_struct_0 @ X24))),
% 2.30/2.48      inference('cnf', [status(esa)], [t39_yellow_6])).
% 2.30/2.48  thf('61', plain,
% 2.30/2.48      (![X0 : $i]:
% 2.30/2.48         ((v2_struct_0 @ sk_A)
% 2.30/2.48          | ~ (v2_pre_topc @ sk_A)
% 2.30/2.48          | ~ (l1_pre_topc @ sk_A)
% 2.30/2.48          | (r2_hidden @ (k2_xboole_0 @ sk_C_1 @ sk_D_1) @ 
% 2.30/2.48             (u1_struct_0 @ (k9_yellow_6 @ sk_A @ X0)))
% 2.30/2.48          | ~ (v3_pre_topc @ (k2_xboole_0 @ sk_C_1 @ sk_D_1) @ sk_A)
% 2.30/2.48          | ~ (r2_hidden @ X0 @ (k2_xboole_0 @ sk_C_1 @ sk_D_1))
% 2.30/2.48          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 2.30/2.48      inference('sup-', [status(thm)], ['59', '60'])).
% 2.30/2.48  thf('62', plain, ((v2_pre_topc @ sk_A)),
% 2.30/2.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.30/2.48  thf('63', plain, ((l1_pre_topc @ sk_A)),
% 2.30/2.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.30/2.48  thf('64', plain,
% 2.30/2.48      (![X0 : $i]:
% 2.30/2.48         ((v2_struct_0 @ sk_A)
% 2.30/2.48          | (r2_hidden @ (k2_xboole_0 @ sk_C_1 @ sk_D_1) @ 
% 2.30/2.48             (u1_struct_0 @ (k9_yellow_6 @ sk_A @ X0)))
% 2.30/2.48          | ~ (v3_pre_topc @ (k2_xboole_0 @ sk_C_1 @ sk_D_1) @ sk_A)
% 2.30/2.48          | ~ (r2_hidden @ X0 @ (k2_xboole_0 @ sk_C_1 @ sk_D_1))
% 2.30/2.48          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 2.30/2.48      inference('demod', [status(thm)], ['61', '62', '63'])).
% 2.30/2.48  thf('65', plain,
% 2.30/2.48      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.30/2.48      inference('clc', [status(thm)], ['38', '39'])).
% 2.30/2.48  thf('66', plain,
% 2.30/2.48      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.30/2.48      inference('clc', [status(thm)], ['48', '49'])).
% 2.30/2.48  thf(fc7_tops_1, axiom,
% 2.30/2.48    (![A:$i,B:$i,C:$i]:
% 2.30/2.48     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & ( v3_pre_topc @ B @ A ) & 
% 2.30/2.48         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) & 
% 2.30/2.48         ( v3_pre_topc @ C @ A ) & 
% 2.30/2.48         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 2.30/2.48       ( v3_pre_topc @ ( k2_xboole_0 @ B @ C ) @ A ) ))).
% 2.30/2.48  thf('67', plain,
% 2.30/2.48      (![X17 : $i, X18 : $i, X19 : $i]:
% 2.30/2.48         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 2.30/2.48          | ~ (v3_pre_topc @ X17 @ X18)
% 2.30/2.48          | ~ (l1_pre_topc @ X18)
% 2.30/2.48          | ~ (v2_pre_topc @ X18)
% 2.30/2.48          | ~ (v3_pre_topc @ X19 @ X18)
% 2.30/2.48          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 2.30/2.48          | (v3_pre_topc @ (k2_xboole_0 @ X17 @ X19) @ X18))),
% 2.30/2.48      inference('cnf', [status(esa)], [fc7_tops_1])).
% 2.30/2.48  thf('68', plain,
% 2.30/2.48      (![X0 : $i]:
% 2.30/2.48         ((v3_pre_topc @ (k2_xboole_0 @ sk_C_1 @ X0) @ sk_A)
% 2.30/2.48          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 2.30/2.48          | ~ (v3_pre_topc @ X0 @ sk_A)
% 2.30/2.48          | ~ (v2_pre_topc @ sk_A)
% 2.30/2.48          | ~ (l1_pre_topc @ sk_A)
% 2.30/2.48          | ~ (v3_pre_topc @ sk_C_1 @ sk_A))),
% 2.30/2.48      inference('sup-', [status(thm)], ['66', '67'])).
% 2.30/2.48  thf('69', plain, ((v2_pre_topc @ sk_A)),
% 2.30/2.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.30/2.48  thf('70', plain, ((l1_pre_topc @ sk_A)),
% 2.30/2.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.30/2.48  thf('71', plain,
% 2.30/2.48      (![X0 : $i]:
% 2.30/2.48         ((v3_pre_topc @ (k2_xboole_0 @ sk_C_1 @ X0) @ sk_A)
% 2.30/2.48          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 2.30/2.48          | ~ (v3_pre_topc @ X0 @ sk_A)
% 2.30/2.48          | ~ (v3_pre_topc @ sk_C_1 @ sk_A))),
% 2.30/2.48      inference('demod', [status(thm)], ['68', '69', '70'])).
% 2.30/2.48  thf('72', plain,
% 2.30/2.48      ((m1_subset_1 @ sk_C_1 @ (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B)))),
% 2.30/2.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.30/2.48  thf('73', plain,
% 2.30/2.48      (![X20 : $i, X21 : $i, X22 : $i]:
% 2.30/2.48         (~ (m1_subset_1 @ X20 @ (u1_struct_0 @ X21))
% 2.30/2.48          | (v3_pre_topc @ (sk_D @ X22 @ X20 @ X21) @ X21)
% 2.30/2.48          | ~ (m1_subset_1 @ X22 @ (u1_struct_0 @ (k9_yellow_6 @ X21 @ X20)))
% 2.30/2.48          | ~ (l1_pre_topc @ X21)
% 2.30/2.48          | ~ (v2_pre_topc @ X21)
% 2.30/2.48          | (v2_struct_0 @ X21))),
% 2.30/2.48      inference('cnf', [status(esa)], [t38_yellow_6])).
% 2.30/2.48  thf('74', plain,
% 2.30/2.48      (((v2_struct_0 @ sk_A)
% 2.30/2.48        | ~ (v2_pre_topc @ sk_A)
% 2.30/2.48        | ~ (l1_pre_topc @ sk_A)
% 2.30/2.48        | (v3_pre_topc @ (sk_D @ sk_C_1 @ sk_B @ sk_A) @ sk_A)
% 2.30/2.48        | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 2.30/2.48      inference('sup-', [status(thm)], ['72', '73'])).
% 2.30/2.48  thf('75', plain, ((v2_pre_topc @ sk_A)),
% 2.30/2.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.30/2.48  thf('76', plain, ((l1_pre_topc @ sk_A)),
% 2.30/2.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.30/2.48  thf('77', plain, (((sk_D @ sk_C_1 @ sk_B @ sk_A) = (sk_C_1))),
% 2.30/2.48      inference('clc', [status(thm)], ['12', '13'])).
% 2.30/2.48  thf('78', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 2.30/2.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.30/2.48  thf('79', plain, (((v2_struct_0 @ sk_A) | (v3_pre_topc @ sk_C_1 @ sk_A))),
% 2.30/2.48      inference('demod', [status(thm)], ['74', '75', '76', '77', '78'])).
% 2.30/2.48  thf('80', plain, (~ (v2_struct_0 @ sk_A)),
% 2.30/2.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.30/2.48  thf('81', plain, ((v3_pre_topc @ sk_C_1 @ sk_A)),
% 2.30/2.48      inference('clc', [status(thm)], ['79', '80'])).
% 2.30/2.48  thf('82', plain,
% 2.30/2.48      (![X0 : $i]:
% 2.30/2.48         ((v3_pre_topc @ (k2_xboole_0 @ sk_C_1 @ X0) @ sk_A)
% 2.30/2.48          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 2.30/2.48          | ~ (v3_pre_topc @ X0 @ sk_A))),
% 2.30/2.48      inference('demod', [status(thm)], ['71', '81'])).
% 2.30/2.48  thf('83', plain,
% 2.30/2.48      ((~ (v3_pre_topc @ sk_D_1 @ sk_A)
% 2.30/2.48        | (v3_pre_topc @ (k2_xboole_0 @ sk_C_1 @ sk_D_1) @ sk_A))),
% 2.30/2.48      inference('sup-', [status(thm)], ['65', '82'])).
% 2.30/2.48  thf('84', plain,
% 2.30/2.48      ((m1_subset_1 @ sk_D_1 @ (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B)))),
% 2.30/2.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.30/2.48  thf('85', plain,
% 2.30/2.48      (![X20 : $i, X21 : $i, X22 : $i]:
% 2.30/2.48         (~ (m1_subset_1 @ X20 @ (u1_struct_0 @ X21))
% 2.30/2.48          | (v3_pre_topc @ (sk_D @ X22 @ X20 @ X21) @ X21)
% 2.30/2.48          | ~ (m1_subset_1 @ X22 @ (u1_struct_0 @ (k9_yellow_6 @ X21 @ X20)))
% 2.30/2.48          | ~ (l1_pre_topc @ X21)
% 2.30/2.48          | ~ (v2_pre_topc @ X21)
% 2.30/2.48          | (v2_struct_0 @ X21))),
% 2.30/2.48      inference('cnf', [status(esa)], [t38_yellow_6])).
% 2.30/2.48  thf('86', plain,
% 2.30/2.48      (((v2_struct_0 @ sk_A)
% 2.30/2.48        | ~ (v2_pre_topc @ sk_A)
% 2.30/2.48        | ~ (l1_pre_topc @ sk_A)
% 2.30/2.48        | (v3_pre_topc @ (sk_D @ sk_D_1 @ sk_B @ sk_A) @ sk_A)
% 2.30/2.48        | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 2.30/2.48      inference('sup-', [status(thm)], ['84', '85'])).
% 2.30/2.48  thf('87', plain, ((v2_pre_topc @ sk_A)),
% 2.30/2.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.30/2.48  thf('88', plain, ((l1_pre_topc @ sk_A)),
% 2.30/2.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.30/2.48  thf('89', plain, (((sk_D @ sk_D_1 @ sk_B @ sk_A) = (sk_D_1))),
% 2.30/2.48      inference('clc', [status(thm)], ['34', '35'])).
% 2.30/2.48  thf('90', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 2.30/2.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.30/2.48  thf('91', plain, (((v2_struct_0 @ sk_A) | (v3_pre_topc @ sk_D_1 @ sk_A))),
% 2.30/2.48      inference('demod', [status(thm)], ['86', '87', '88', '89', '90'])).
% 2.30/2.48  thf('92', plain, (~ (v2_struct_0 @ sk_A)),
% 2.30/2.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.30/2.48  thf('93', plain, ((v3_pre_topc @ sk_D_1 @ sk_A)),
% 2.30/2.48      inference('clc', [status(thm)], ['91', '92'])).
% 2.30/2.48  thf('94', plain, ((v3_pre_topc @ (k2_xboole_0 @ sk_C_1 @ sk_D_1) @ sk_A)),
% 2.30/2.48      inference('demod', [status(thm)], ['83', '93'])).
% 2.30/2.48  thf('95', plain,
% 2.30/2.48      (![X0 : $i]:
% 2.30/2.48         ((v2_struct_0 @ sk_A)
% 2.30/2.48          | (r2_hidden @ (k2_xboole_0 @ sk_C_1 @ sk_D_1) @ 
% 2.30/2.48             (u1_struct_0 @ (k9_yellow_6 @ sk_A @ X0)))
% 2.30/2.48          | ~ (r2_hidden @ X0 @ (k2_xboole_0 @ sk_C_1 @ sk_D_1))
% 2.30/2.48          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 2.30/2.48      inference('demod', [status(thm)], ['64', '94'])).
% 2.30/2.48  thf('96', plain,
% 2.30/2.48      ((~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 2.30/2.48        | (r2_hidden @ (k2_xboole_0 @ sk_C_1 @ sk_D_1) @ 
% 2.30/2.48           (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B)))
% 2.30/2.48        | (v2_struct_0 @ sk_A))),
% 2.30/2.48      inference('sup-', [status(thm)], ['22', '95'])).
% 2.30/2.48  thf('97', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 2.30/2.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.30/2.48  thf('98', plain,
% 2.30/2.48      (((r2_hidden @ (k2_xboole_0 @ sk_C_1 @ sk_D_1) @ 
% 2.30/2.48         (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B)))
% 2.30/2.48        | (v2_struct_0 @ sk_A))),
% 2.30/2.48      inference('demod', [status(thm)], ['96', '97'])).
% 2.30/2.48  thf('99', plain, (~ (v2_struct_0 @ sk_A)),
% 2.30/2.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.30/2.48  thf('100', plain,
% 2.30/2.48      ((r2_hidden @ (k2_xboole_0 @ sk_C_1 @ sk_D_1) @ 
% 2.30/2.48        (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B)))),
% 2.30/2.48      inference('clc', [status(thm)], ['98', '99'])).
% 2.30/2.48  thf(t1_subset, axiom,
% 2.30/2.48    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 2.30/2.48  thf('101', plain,
% 2.30/2.48      (![X12 : $i, X13 : $i]:
% 2.30/2.48         ((m1_subset_1 @ X12 @ X13) | ~ (r2_hidden @ X12 @ X13))),
% 2.30/2.48      inference('cnf', [status(esa)], [t1_subset])).
% 2.30/2.48  thf('102', plain,
% 2.30/2.48      ((m1_subset_1 @ (k2_xboole_0 @ sk_C_1 @ sk_D_1) @ 
% 2.30/2.48        (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B)))),
% 2.30/2.48      inference('sup-', [status(thm)], ['100', '101'])).
% 2.30/2.48  thf('103', plain, ($false), inference('demod', [status(thm)], ['0', '102'])).
% 2.30/2.48  
% 2.30/2.48  % SZS output end Refutation
% 2.30/2.48  
% 2.30/2.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
