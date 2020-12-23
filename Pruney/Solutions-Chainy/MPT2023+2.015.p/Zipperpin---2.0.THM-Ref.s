%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.tGGQNG1JXQ

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:14:26 EST 2020

% Result     : Theorem 3.61s
% Output     : Refutation 3.61s
% Verified   : 
% Statistics : Number of formulae       :  138 ( 353 expanded)
%              Number of leaves         :   25 ( 115 expanded)
%              Depth                    :   18
%              Number of atoms          : 1081 (6419 expanded)
%              Number of equality atoms :   15 (  44 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_D_2_type,type,(
    sk_D_2: $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k9_yellow_6_type,type,(
    k9_yellow_6: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(t22_waybel_9,conjecture,(
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
                 => ( m1_subset_1 @ ( k3_xboole_0 @ C @ D ) @ ( u1_struct_0 @ ( k9_yellow_6 @ A @ B ) ) ) ) ) ) ) )).

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
                   => ( m1_subset_1 @ ( k3_xboole_0 @ C @ D ) @ ( u1_struct_0 @ ( k9_yellow_6 @ A @ B ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t22_waybel_9])).

thf('0',plain,(
    ~ ( m1_subset_1 @ ( k3_xboole_0 @ sk_C @ sk_D_2 ) @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B ) ) ),
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
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( u1_struct_0 @ X20 ) )
      | ( r2_hidden @ X19 @ ( sk_D_1 @ X21 @ X19 @ X20 ) )
      | ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ ( k9_yellow_6 @ X20 @ X19 ) ) )
      | ~ ( l1_pre_topc @ X20 )
      | ~ ( v2_pre_topc @ X20 )
      | ( v2_struct_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t38_yellow_6])).

thf('3',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( r2_hidden @ sk_B @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) )
    | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( u1_struct_0 @ X20 ) )
      | ( ( sk_D_1 @ X21 @ X19 @ X20 )
        = X21 )
      | ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ ( k9_yellow_6 @ X20 @ X19 ) ) )
      | ~ ( l1_pre_topc @ X20 )
      | ~ ( v2_pre_topc @ X20 )
      | ( v2_struct_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t38_yellow_6])).

thf('8',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( ( sk_D_1 @ sk_C @ sk_B @ sk_A )
      = sk_C )
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
    | ( ( sk_D_1 @ sk_C @ sk_B @ sk_A )
      = sk_C ) ),
    inference(demod,[status(thm)],['8','9','10','11'])).

thf('13',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ( sk_D_1 @ sk_C @ sk_B @ sk_A )
    = sk_C ),
    inference(clc,[status(thm)],['12','13'])).

thf('15',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['3','4','5','14','15'])).

thf('17',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    r2_hidden @ sk_B @ sk_C ),
    inference(clc,[status(thm)],['16','17'])).

thf('19',plain,(
    m1_subset_1 @ sk_D_2 @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( u1_struct_0 @ X20 ) )
      | ( r2_hidden @ X19 @ ( sk_D_1 @ X21 @ X19 @ X20 ) )
      | ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ ( k9_yellow_6 @ X20 @ X19 ) ) )
      | ~ ( l1_pre_topc @ X20 )
      | ~ ( v2_pre_topc @ X20 )
      | ( v2_struct_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t38_yellow_6])).

thf('21',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( r2_hidden @ sk_B @ ( sk_D_1 @ sk_D_2 @ sk_B @ sk_A ) )
    | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    m1_subset_1 @ sk_D_2 @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( u1_struct_0 @ X20 ) )
      | ( ( sk_D_1 @ X21 @ X19 @ X20 )
        = X21 )
      | ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ ( k9_yellow_6 @ X20 @ X19 ) ) )
      | ~ ( l1_pre_topc @ X20 )
      | ~ ( v2_pre_topc @ X20 )
      | ( v2_struct_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t38_yellow_6])).

thf('26',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( ( sk_D_1 @ sk_D_2 @ sk_B @ sk_A )
      = sk_D_2 )
    | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( sk_D_1 @ sk_D_2 @ sk_B @ sk_A )
      = sk_D_2 ) ),
    inference(demod,[status(thm)],['26','27','28','29'])).

thf('31',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ( sk_D_1 @ sk_D_2 @ sk_B @ sk_A )
    = sk_D_2 ),
    inference(clc,[status(thm)],['30','31'])).

thf('33',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ sk_B @ sk_D_2 ) ),
    inference(demod,[status(thm)],['21','22','23','32','33'])).

thf('35',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    r2_hidden @ sk_B @ sk_D_2 ),
    inference(clc,[status(thm)],['34','35'])).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_hidden @ X0 @ X2 )
      | ( r2_hidden @ X0 @ X3 )
      | ( X3
       != ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X0 @ ( k3_xboole_0 @ X1 @ X2 ) )
      | ~ ( r2_hidden @ X0 @ X2 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ sk_B @ X0 )
      | ( r2_hidden @ sk_B @ ( k3_xboole_0 @ X0 @ sk_D_2 ) ) ) ),
    inference('sup-',[status(thm)],['36','38'])).

thf('40',plain,(
    r2_hidden @ sk_B @ ( k3_xboole_0 @ sk_C @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['18','39'])).

thf('41',plain,(
    m1_subset_1 @ sk_D_2 @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( u1_struct_0 @ X20 ) )
      | ( m1_subset_1 @ ( sk_D_1 @ X21 @ X19 @ X20 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ ( k9_yellow_6 @ X20 @ X19 ) ) )
      | ~ ( l1_pre_topc @ X20 )
      | ~ ( v2_pre_topc @ X20 )
      | ( v2_struct_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t38_yellow_6])).

thf('43',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( m1_subset_1 @ ( sk_D_1 @ sk_D_2 @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( ( sk_D_1 @ sk_D_2 @ sk_B @ sk_A )
    = sk_D_2 ),
    inference(clc,[status(thm)],['30','31'])).

thf('47',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['43','44','45','46','47'])).

thf('49',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['48','49'])).

thf('51',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( u1_struct_0 @ X20 ) )
      | ( m1_subset_1 @ ( sk_D_1 @ X21 @ X19 @ X20 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ ( k9_yellow_6 @ X20 @ X19 ) ) )
      | ~ ( l1_pre_topc @ X20 )
      | ~ ( v2_pre_topc @ X20 )
      | ( v2_struct_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t38_yellow_6])).

thf('53',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( m1_subset_1 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,
    ( ( sk_D_1 @ sk_C @ sk_B @ sk_A )
    = sk_C ),
    inference(clc,[status(thm)],['12','13'])).

thf('57',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['53','54','55','56','57'])).

thf('59',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['58','59'])).

thf(fc6_tops_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( v3_pre_topc @ B @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
        & ( v3_pre_topc @ C @ A )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v3_pre_topc @ ( k3_xboole_0 @ B @ C ) @ A ) ) )).

thf('61',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ~ ( v3_pre_topc @ X16 @ X17 )
      | ~ ( l1_pre_topc @ X17 )
      | ~ ( v2_pre_topc @ X17 )
      | ~ ( v3_pre_topc @ X18 @ X17 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ( v3_pre_topc @ ( k3_xboole_0 @ X16 @ X18 ) @ X17 ) ) ),
    inference(cnf,[status(esa)],[fc6_tops_1])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( v3_pre_topc @ ( k3_xboole_0 @ sk_C @ X0 ) @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v3_pre_topc @ X0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v3_pre_topc @ sk_C @ sk_A ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( v3_pre_topc @ ( k3_xboole_0 @ sk_C @ X0 ) @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v3_pre_topc @ X0 @ sk_A )
      | ~ ( v3_pre_topc @ sk_C @ sk_A ) ) ),
    inference(demod,[status(thm)],['62','63','64'])).

thf('66',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( u1_struct_0 @ X20 ) )
      | ( v3_pre_topc @ ( sk_D_1 @ X21 @ X19 @ X20 ) @ X20 )
      | ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ ( k9_yellow_6 @ X20 @ X19 ) ) )
      | ~ ( l1_pre_topc @ X20 )
      | ~ ( v2_pre_topc @ X20 )
      | ( v2_struct_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t38_yellow_6])).

thf('68',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v3_pre_topc @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_A )
    | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,
    ( ( sk_D_1 @ sk_C @ sk_B @ sk_A )
    = sk_C ),
    inference(clc,[status(thm)],['12','13'])).

thf('72',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v3_pre_topc @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['68','69','70','71','72'])).

thf('74',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    v3_pre_topc @ sk_C @ sk_A ),
    inference(clc,[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( v3_pre_topc @ ( k3_xboole_0 @ sk_C @ X0 ) @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v3_pre_topc @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['65','75'])).

thf('77',plain,
    ( ~ ( v3_pre_topc @ sk_D_2 @ sk_A )
    | ( v3_pre_topc @ ( k3_xboole_0 @ sk_C @ sk_D_2 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['50','76'])).

thf('78',plain,(
    m1_subset_1 @ sk_D_2 @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( u1_struct_0 @ X20 ) )
      | ( v3_pre_topc @ ( sk_D_1 @ X21 @ X19 @ X20 ) @ X20 )
      | ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ ( k9_yellow_6 @ X20 @ X19 ) ) )
      | ~ ( l1_pre_topc @ X20 )
      | ~ ( v2_pre_topc @ X20 )
      | ( v2_struct_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t38_yellow_6])).

thf('80',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v3_pre_topc @ ( sk_D_1 @ sk_D_2 @ sk_B @ sk_A ) @ sk_A )
    | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,
    ( ( sk_D_1 @ sk_D_2 @ sk_B @ sk_A )
    = sk_D_2 ),
    inference(clc,[status(thm)],['30','31'])).

thf('84',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v3_pre_topc @ sk_D_2 @ sk_A ) ),
    inference(demod,[status(thm)],['80','81','82','83','84'])).

thf('86',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    v3_pre_topc @ sk_D_2 @ sk_A ),
    inference(clc,[status(thm)],['85','86'])).

thf('88',plain,(
    v3_pre_topc @ ( k3_xboole_0 @ sk_C @ sk_D_2 ) @ sk_A ),
    inference(demod,[status(thm)],['77','87'])).

thf('89',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['58','59'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('90',plain,(
    ! [X13: $i,X14: $i] :
      ( ( r1_tarski @ X13 @ X14 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('91',plain,(
    r1_tarski @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('92',plain,(
    ! [X6: $i,X7: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X6 @ X7 ) @ X6 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('93',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r1_tarski @ X8 @ X9 )
      | ~ ( r1_tarski @ X9 @ X10 )
      | ( r1_tarski @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('94',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ X2 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ sk_C @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['91','94'])).

thf('96',plain,(
    ! [X13: $i,X15: $i] :
      ( ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X15 ) )
      | ~ ( r1_tarski @ X13 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('97',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ sk_C @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['95','96'])).

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

thf('98',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ X23 ) )
      | ~ ( r2_hidden @ X22 @ X24 )
      | ~ ( v3_pre_topc @ X24 @ X23 )
      | ( r2_hidden @ X24 @ ( u1_struct_0 @ ( k9_yellow_6 @ X23 @ X22 ) ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ~ ( l1_pre_topc @ X23 )
      | ~ ( v2_pre_topc @ X23 )
      | ( v2_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t39_yellow_6])).

thf('99',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( r2_hidden @ ( k3_xboole_0 @ sk_C @ X0 ) @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ X1 ) ) )
      | ~ ( v3_pre_topc @ ( k3_xboole_0 @ sk_C @ X0 ) @ sk_A )
      | ~ ( r2_hidden @ X1 @ ( k3_xboole_0 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ ( k3_xboole_0 @ sk_C @ X0 ) @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ X1 ) ) )
      | ~ ( v3_pre_topc @ ( k3_xboole_0 @ sk_C @ X0 ) @ sk_A )
      | ~ ( r2_hidden @ X1 @ ( k3_xboole_0 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['99','100','101'])).

thf('103',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( k3_xboole_0 @ sk_C @ sk_D_2 ) )
      | ( r2_hidden @ ( k3_xboole_0 @ sk_C @ sk_D_2 ) @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ X0 ) ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['88','102'])).

thf('104',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ ( k3_xboole_0 @ sk_C @ sk_D_2 ) @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B ) ) )
    | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['40','103'])).

thf('105',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ ( k3_xboole_0 @ sk_C @ sk_D_2 ) @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['104','105'])).

thf('107',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,(
    r2_hidden @ ( k3_xboole_0 @ sk_C @ sk_D_2 ) @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['106','107'])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('109',plain,(
    ! [X11: $i,X12: $i] :
      ( ( m1_subset_1 @ X11 @ X12 )
      | ~ ( r2_hidden @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('110',plain,(
    m1_subset_1 @ ( k3_xboole_0 @ sk_C @ sk_D_2 ) @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['108','109'])).

thf('111',plain,(
    $false ),
    inference(demod,[status(thm)],['0','110'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.tGGQNG1JXQ
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 18:26:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 3.61/3.85  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 3.61/3.85  % Solved by: fo/fo7.sh
% 3.61/3.85  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 3.61/3.85  % done 4471 iterations in 3.405s
% 3.61/3.85  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 3.61/3.85  % SZS output start Refutation
% 3.61/3.85  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 3.61/3.85  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 3.61/3.85  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 3.61/3.85  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 3.61/3.85  thf(sk_C_type, type, sk_C: $i).
% 3.61/3.85  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 3.61/3.85  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 3.61/3.85  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 3.61/3.85  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 3.61/3.85  thf(sk_D_2_type, type, sk_D_2: $i).
% 3.61/3.85  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i > $i).
% 3.61/3.85  thf(sk_A_type, type, sk_A: $i).
% 3.61/3.85  thf(sk_B_type, type, sk_B: $i).
% 3.61/3.85  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 3.61/3.85  thf(k9_yellow_6_type, type, k9_yellow_6: $i > $i > $i).
% 3.61/3.85  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 3.61/3.85  thf(t22_waybel_9, conjecture,
% 3.61/3.85    (![A:$i]:
% 3.61/3.85     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 3.61/3.85       ( ![B:$i]:
% 3.61/3.85         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 3.61/3.85           ( ![C:$i]:
% 3.61/3.85             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ ( k9_yellow_6 @ A @ B ) ) ) =>
% 3.61/3.85               ( ![D:$i]:
% 3.61/3.85                 ( ( m1_subset_1 @
% 3.61/3.85                     D @ ( u1_struct_0 @ ( k9_yellow_6 @ A @ B ) ) ) =>
% 3.61/3.85                   ( m1_subset_1 @
% 3.61/3.85                     ( k3_xboole_0 @ C @ D ) @ 
% 3.61/3.85                     ( u1_struct_0 @ ( k9_yellow_6 @ A @ B ) ) ) ) ) ) ) ) ) ))).
% 3.61/3.85  thf(zf_stmt_0, negated_conjecture,
% 3.61/3.85    (~( ![A:$i]:
% 3.61/3.85        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 3.61/3.85            ( l1_pre_topc @ A ) ) =>
% 3.61/3.85          ( ![B:$i]:
% 3.61/3.85            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 3.61/3.85              ( ![C:$i]:
% 3.61/3.85                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ ( k9_yellow_6 @ A @ B ) ) ) =>
% 3.61/3.85                  ( ![D:$i]:
% 3.61/3.85                    ( ( m1_subset_1 @
% 3.61/3.85                        D @ ( u1_struct_0 @ ( k9_yellow_6 @ A @ B ) ) ) =>
% 3.61/3.85                      ( m1_subset_1 @
% 3.61/3.85                        ( k3_xboole_0 @ C @ D ) @ 
% 3.61/3.85                        ( u1_struct_0 @ ( k9_yellow_6 @ A @ B ) ) ) ) ) ) ) ) ) ) )),
% 3.61/3.85    inference('cnf.neg', [status(esa)], [t22_waybel_9])).
% 3.61/3.85  thf('0', plain,
% 3.61/3.85      (~ (m1_subset_1 @ (k3_xboole_0 @ sk_C @ sk_D_2) @ 
% 3.61/3.85          (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B)))),
% 3.61/3.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.61/3.85  thf('1', plain,
% 3.61/3.85      ((m1_subset_1 @ sk_C @ (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B)))),
% 3.61/3.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.61/3.85  thf(t38_yellow_6, axiom,
% 3.61/3.85    (![A:$i]:
% 3.61/3.85     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 3.61/3.85       ( ![B:$i]:
% 3.61/3.85         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 3.61/3.85           ( ![C:$i]:
% 3.61/3.85             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ ( k9_yellow_6 @ A @ B ) ) ) =>
% 3.61/3.85               ( ?[D:$i]:
% 3.61/3.85                 ( ( v3_pre_topc @ D @ A ) & ( r2_hidden @ B @ D ) & 
% 3.61/3.85                   ( ( D ) = ( C ) ) & 
% 3.61/3.85                   ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ) ) ))).
% 3.61/3.85  thf('2', plain,
% 3.61/3.85      (![X19 : $i, X20 : $i, X21 : $i]:
% 3.61/3.85         (~ (m1_subset_1 @ X19 @ (u1_struct_0 @ X20))
% 3.61/3.85          | (r2_hidden @ X19 @ (sk_D_1 @ X21 @ X19 @ X20))
% 3.61/3.85          | ~ (m1_subset_1 @ X21 @ (u1_struct_0 @ (k9_yellow_6 @ X20 @ X19)))
% 3.61/3.85          | ~ (l1_pre_topc @ X20)
% 3.61/3.85          | ~ (v2_pre_topc @ X20)
% 3.61/3.85          | (v2_struct_0 @ X20))),
% 3.61/3.85      inference('cnf', [status(esa)], [t38_yellow_6])).
% 3.61/3.85  thf('3', plain,
% 3.61/3.85      (((v2_struct_0 @ sk_A)
% 3.61/3.85        | ~ (v2_pre_topc @ sk_A)
% 3.61/3.85        | ~ (l1_pre_topc @ sk_A)
% 3.61/3.85        | (r2_hidden @ sk_B @ (sk_D_1 @ sk_C @ sk_B @ sk_A))
% 3.61/3.85        | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 3.61/3.85      inference('sup-', [status(thm)], ['1', '2'])).
% 3.61/3.85  thf('4', plain, ((v2_pre_topc @ sk_A)),
% 3.61/3.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.61/3.85  thf('5', plain, ((l1_pre_topc @ sk_A)),
% 3.61/3.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.61/3.85  thf('6', plain,
% 3.61/3.85      ((m1_subset_1 @ sk_C @ (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B)))),
% 3.61/3.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.61/3.85  thf('7', plain,
% 3.61/3.85      (![X19 : $i, X20 : $i, X21 : $i]:
% 3.61/3.85         (~ (m1_subset_1 @ X19 @ (u1_struct_0 @ X20))
% 3.61/3.85          | ((sk_D_1 @ X21 @ X19 @ X20) = (X21))
% 3.61/3.85          | ~ (m1_subset_1 @ X21 @ (u1_struct_0 @ (k9_yellow_6 @ X20 @ X19)))
% 3.61/3.85          | ~ (l1_pre_topc @ X20)
% 3.61/3.85          | ~ (v2_pre_topc @ X20)
% 3.61/3.85          | (v2_struct_0 @ X20))),
% 3.61/3.85      inference('cnf', [status(esa)], [t38_yellow_6])).
% 3.61/3.85  thf('8', plain,
% 3.61/3.85      (((v2_struct_0 @ sk_A)
% 3.61/3.85        | ~ (v2_pre_topc @ sk_A)
% 3.61/3.85        | ~ (l1_pre_topc @ sk_A)
% 3.61/3.85        | ((sk_D_1 @ sk_C @ sk_B @ sk_A) = (sk_C))
% 3.61/3.85        | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 3.61/3.85      inference('sup-', [status(thm)], ['6', '7'])).
% 3.61/3.85  thf('9', plain, ((v2_pre_topc @ sk_A)),
% 3.61/3.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.61/3.85  thf('10', plain, ((l1_pre_topc @ sk_A)),
% 3.61/3.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.61/3.85  thf('11', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 3.61/3.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.61/3.85  thf('12', plain,
% 3.61/3.85      (((v2_struct_0 @ sk_A) | ((sk_D_1 @ sk_C @ sk_B @ sk_A) = (sk_C)))),
% 3.61/3.85      inference('demod', [status(thm)], ['8', '9', '10', '11'])).
% 3.61/3.85  thf('13', plain, (~ (v2_struct_0 @ sk_A)),
% 3.61/3.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.61/3.85  thf('14', plain, (((sk_D_1 @ sk_C @ sk_B @ sk_A) = (sk_C))),
% 3.61/3.85      inference('clc', [status(thm)], ['12', '13'])).
% 3.61/3.85  thf('15', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 3.61/3.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.61/3.85  thf('16', plain, (((v2_struct_0 @ sk_A) | (r2_hidden @ sk_B @ sk_C))),
% 3.61/3.85      inference('demod', [status(thm)], ['3', '4', '5', '14', '15'])).
% 3.61/3.85  thf('17', plain, (~ (v2_struct_0 @ sk_A)),
% 3.61/3.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.61/3.85  thf('18', plain, ((r2_hidden @ sk_B @ sk_C)),
% 3.61/3.85      inference('clc', [status(thm)], ['16', '17'])).
% 3.61/3.85  thf('19', plain,
% 3.61/3.85      ((m1_subset_1 @ sk_D_2 @ (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B)))),
% 3.61/3.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.61/3.85  thf('20', plain,
% 3.61/3.85      (![X19 : $i, X20 : $i, X21 : $i]:
% 3.61/3.85         (~ (m1_subset_1 @ X19 @ (u1_struct_0 @ X20))
% 3.61/3.85          | (r2_hidden @ X19 @ (sk_D_1 @ X21 @ X19 @ X20))
% 3.61/3.85          | ~ (m1_subset_1 @ X21 @ (u1_struct_0 @ (k9_yellow_6 @ X20 @ X19)))
% 3.61/3.85          | ~ (l1_pre_topc @ X20)
% 3.61/3.85          | ~ (v2_pre_topc @ X20)
% 3.61/3.85          | (v2_struct_0 @ X20))),
% 3.61/3.85      inference('cnf', [status(esa)], [t38_yellow_6])).
% 3.61/3.85  thf('21', plain,
% 3.61/3.85      (((v2_struct_0 @ sk_A)
% 3.61/3.85        | ~ (v2_pre_topc @ sk_A)
% 3.61/3.85        | ~ (l1_pre_topc @ sk_A)
% 3.61/3.85        | (r2_hidden @ sk_B @ (sk_D_1 @ sk_D_2 @ sk_B @ sk_A))
% 3.61/3.85        | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 3.61/3.85      inference('sup-', [status(thm)], ['19', '20'])).
% 3.61/3.85  thf('22', plain, ((v2_pre_topc @ sk_A)),
% 3.61/3.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.61/3.85  thf('23', plain, ((l1_pre_topc @ sk_A)),
% 3.61/3.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.61/3.85  thf('24', plain,
% 3.61/3.85      ((m1_subset_1 @ sk_D_2 @ (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B)))),
% 3.61/3.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.61/3.85  thf('25', plain,
% 3.61/3.85      (![X19 : $i, X20 : $i, X21 : $i]:
% 3.61/3.85         (~ (m1_subset_1 @ X19 @ (u1_struct_0 @ X20))
% 3.61/3.85          | ((sk_D_1 @ X21 @ X19 @ X20) = (X21))
% 3.61/3.85          | ~ (m1_subset_1 @ X21 @ (u1_struct_0 @ (k9_yellow_6 @ X20 @ X19)))
% 3.61/3.85          | ~ (l1_pre_topc @ X20)
% 3.61/3.85          | ~ (v2_pre_topc @ X20)
% 3.61/3.85          | (v2_struct_0 @ X20))),
% 3.61/3.85      inference('cnf', [status(esa)], [t38_yellow_6])).
% 3.61/3.85  thf('26', plain,
% 3.61/3.85      (((v2_struct_0 @ sk_A)
% 3.61/3.85        | ~ (v2_pre_topc @ sk_A)
% 3.61/3.85        | ~ (l1_pre_topc @ sk_A)
% 3.61/3.85        | ((sk_D_1 @ sk_D_2 @ sk_B @ sk_A) = (sk_D_2))
% 3.61/3.85        | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 3.61/3.85      inference('sup-', [status(thm)], ['24', '25'])).
% 3.61/3.85  thf('27', plain, ((v2_pre_topc @ sk_A)),
% 3.61/3.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.61/3.85  thf('28', plain, ((l1_pre_topc @ sk_A)),
% 3.61/3.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.61/3.85  thf('29', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 3.61/3.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.61/3.85  thf('30', plain,
% 3.61/3.85      (((v2_struct_0 @ sk_A) | ((sk_D_1 @ sk_D_2 @ sk_B @ sk_A) = (sk_D_2)))),
% 3.61/3.85      inference('demod', [status(thm)], ['26', '27', '28', '29'])).
% 3.61/3.85  thf('31', plain, (~ (v2_struct_0 @ sk_A)),
% 3.61/3.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.61/3.85  thf('32', plain, (((sk_D_1 @ sk_D_2 @ sk_B @ sk_A) = (sk_D_2))),
% 3.61/3.85      inference('clc', [status(thm)], ['30', '31'])).
% 3.61/3.85  thf('33', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 3.61/3.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.61/3.85  thf('34', plain, (((v2_struct_0 @ sk_A) | (r2_hidden @ sk_B @ sk_D_2))),
% 3.61/3.85      inference('demod', [status(thm)], ['21', '22', '23', '32', '33'])).
% 3.61/3.85  thf('35', plain, (~ (v2_struct_0 @ sk_A)),
% 3.61/3.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.61/3.85  thf('36', plain, ((r2_hidden @ sk_B @ sk_D_2)),
% 3.61/3.85      inference('clc', [status(thm)], ['34', '35'])).
% 3.61/3.85  thf(d4_xboole_0, axiom,
% 3.61/3.85    (![A:$i,B:$i,C:$i]:
% 3.61/3.85     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 3.61/3.85       ( ![D:$i]:
% 3.61/3.85         ( ( r2_hidden @ D @ C ) <=>
% 3.61/3.85           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 3.61/3.85  thf('37', plain,
% 3.61/3.85      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 3.61/3.85         (~ (r2_hidden @ X0 @ X1)
% 3.61/3.85          | ~ (r2_hidden @ X0 @ X2)
% 3.61/3.85          | (r2_hidden @ X0 @ X3)
% 3.61/3.85          | ((X3) != (k3_xboole_0 @ X1 @ X2)))),
% 3.61/3.85      inference('cnf', [status(esa)], [d4_xboole_0])).
% 3.61/3.85  thf('38', plain,
% 3.61/3.85      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.61/3.85         ((r2_hidden @ X0 @ (k3_xboole_0 @ X1 @ X2))
% 3.61/3.85          | ~ (r2_hidden @ X0 @ X2)
% 3.61/3.85          | ~ (r2_hidden @ X0 @ X1))),
% 3.61/3.85      inference('simplify', [status(thm)], ['37'])).
% 3.61/3.85  thf('39', plain,
% 3.61/3.85      (![X0 : $i]:
% 3.61/3.85         (~ (r2_hidden @ sk_B @ X0)
% 3.61/3.85          | (r2_hidden @ sk_B @ (k3_xboole_0 @ X0 @ sk_D_2)))),
% 3.61/3.85      inference('sup-', [status(thm)], ['36', '38'])).
% 3.61/3.85  thf('40', plain, ((r2_hidden @ sk_B @ (k3_xboole_0 @ sk_C @ sk_D_2))),
% 3.61/3.85      inference('sup-', [status(thm)], ['18', '39'])).
% 3.61/3.85  thf('41', plain,
% 3.61/3.85      ((m1_subset_1 @ sk_D_2 @ (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B)))),
% 3.61/3.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.61/3.85  thf('42', plain,
% 3.61/3.85      (![X19 : $i, X20 : $i, X21 : $i]:
% 3.61/3.85         (~ (m1_subset_1 @ X19 @ (u1_struct_0 @ X20))
% 3.61/3.85          | (m1_subset_1 @ (sk_D_1 @ X21 @ X19 @ X20) @ 
% 3.61/3.85             (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 3.61/3.85          | ~ (m1_subset_1 @ X21 @ (u1_struct_0 @ (k9_yellow_6 @ X20 @ X19)))
% 3.61/3.85          | ~ (l1_pre_topc @ X20)
% 3.61/3.85          | ~ (v2_pre_topc @ X20)
% 3.61/3.85          | (v2_struct_0 @ X20))),
% 3.61/3.85      inference('cnf', [status(esa)], [t38_yellow_6])).
% 3.61/3.85  thf('43', plain,
% 3.61/3.85      (((v2_struct_0 @ sk_A)
% 3.61/3.85        | ~ (v2_pre_topc @ sk_A)
% 3.61/3.85        | ~ (l1_pre_topc @ sk_A)
% 3.61/3.85        | (m1_subset_1 @ (sk_D_1 @ sk_D_2 @ sk_B @ sk_A) @ 
% 3.61/3.85           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 3.61/3.85        | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 3.61/3.85      inference('sup-', [status(thm)], ['41', '42'])).
% 3.61/3.85  thf('44', plain, ((v2_pre_topc @ sk_A)),
% 3.61/3.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.61/3.85  thf('45', plain, ((l1_pre_topc @ sk_A)),
% 3.61/3.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.61/3.85  thf('46', plain, (((sk_D_1 @ sk_D_2 @ sk_B @ sk_A) = (sk_D_2))),
% 3.61/3.85      inference('clc', [status(thm)], ['30', '31'])).
% 3.61/3.85  thf('47', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 3.61/3.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.61/3.85  thf('48', plain,
% 3.61/3.85      (((v2_struct_0 @ sk_A)
% 3.61/3.85        | (m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 3.61/3.85      inference('demod', [status(thm)], ['43', '44', '45', '46', '47'])).
% 3.61/3.85  thf('49', plain, (~ (v2_struct_0 @ sk_A)),
% 3.61/3.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.61/3.85  thf('50', plain,
% 3.61/3.85      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.61/3.85      inference('clc', [status(thm)], ['48', '49'])).
% 3.61/3.85  thf('51', plain,
% 3.61/3.85      ((m1_subset_1 @ sk_C @ (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B)))),
% 3.61/3.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.61/3.85  thf('52', plain,
% 3.61/3.85      (![X19 : $i, X20 : $i, X21 : $i]:
% 3.61/3.85         (~ (m1_subset_1 @ X19 @ (u1_struct_0 @ X20))
% 3.61/3.85          | (m1_subset_1 @ (sk_D_1 @ X21 @ X19 @ X20) @ 
% 3.61/3.85             (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 3.61/3.85          | ~ (m1_subset_1 @ X21 @ (u1_struct_0 @ (k9_yellow_6 @ X20 @ X19)))
% 3.61/3.85          | ~ (l1_pre_topc @ X20)
% 3.61/3.85          | ~ (v2_pre_topc @ X20)
% 3.61/3.85          | (v2_struct_0 @ X20))),
% 3.61/3.85      inference('cnf', [status(esa)], [t38_yellow_6])).
% 3.61/3.85  thf('53', plain,
% 3.61/3.85      (((v2_struct_0 @ sk_A)
% 3.61/3.85        | ~ (v2_pre_topc @ sk_A)
% 3.61/3.85        | ~ (l1_pre_topc @ sk_A)
% 3.61/3.85        | (m1_subset_1 @ (sk_D_1 @ sk_C @ sk_B @ sk_A) @ 
% 3.61/3.85           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 3.61/3.85        | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 3.61/3.85      inference('sup-', [status(thm)], ['51', '52'])).
% 3.61/3.85  thf('54', plain, ((v2_pre_topc @ sk_A)),
% 3.61/3.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.61/3.85  thf('55', plain, ((l1_pre_topc @ sk_A)),
% 3.61/3.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.61/3.85  thf('56', plain, (((sk_D_1 @ sk_C @ sk_B @ sk_A) = (sk_C))),
% 3.61/3.85      inference('clc', [status(thm)], ['12', '13'])).
% 3.61/3.85  thf('57', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 3.61/3.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.61/3.85  thf('58', plain,
% 3.61/3.85      (((v2_struct_0 @ sk_A)
% 3.61/3.85        | (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 3.61/3.85      inference('demod', [status(thm)], ['53', '54', '55', '56', '57'])).
% 3.61/3.85  thf('59', plain, (~ (v2_struct_0 @ sk_A)),
% 3.61/3.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.61/3.85  thf('60', plain,
% 3.61/3.85      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.61/3.85      inference('clc', [status(thm)], ['58', '59'])).
% 3.61/3.85  thf(fc6_tops_1, axiom,
% 3.61/3.85    (![A:$i,B:$i,C:$i]:
% 3.61/3.85     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & ( v3_pre_topc @ B @ A ) & 
% 3.61/3.85         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) & 
% 3.61/3.85         ( v3_pre_topc @ C @ A ) & 
% 3.61/3.85         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 3.61/3.85       ( v3_pre_topc @ ( k3_xboole_0 @ B @ C ) @ A ) ))).
% 3.61/3.85  thf('61', plain,
% 3.61/3.85      (![X16 : $i, X17 : $i, X18 : $i]:
% 3.61/3.85         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 3.61/3.85          | ~ (v3_pre_topc @ X16 @ X17)
% 3.61/3.85          | ~ (l1_pre_topc @ X17)
% 3.61/3.85          | ~ (v2_pre_topc @ X17)
% 3.61/3.85          | ~ (v3_pre_topc @ X18 @ X17)
% 3.61/3.85          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 3.61/3.85          | (v3_pre_topc @ (k3_xboole_0 @ X16 @ X18) @ X17))),
% 3.61/3.85      inference('cnf', [status(esa)], [fc6_tops_1])).
% 3.61/3.85  thf('62', plain,
% 3.61/3.85      (![X0 : $i]:
% 3.61/3.85         ((v3_pre_topc @ (k3_xboole_0 @ sk_C @ X0) @ sk_A)
% 3.61/3.85          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 3.61/3.85          | ~ (v3_pre_topc @ X0 @ sk_A)
% 3.61/3.85          | ~ (v2_pre_topc @ sk_A)
% 3.61/3.85          | ~ (l1_pre_topc @ sk_A)
% 3.61/3.85          | ~ (v3_pre_topc @ sk_C @ sk_A))),
% 3.61/3.85      inference('sup-', [status(thm)], ['60', '61'])).
% 3.61/3.85  thf('63', plain, ((v2_pre_topc @ sk_A)),
% 3.61/3.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.61/3.85  thf('64', plain, ((l1_pre_topc @ sk_A)),
% 3.61/3.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.61/3.85  thf('65', plain,
% 3.61/3.85      (![X0 : $i]:
% 3.61/3.85         ((v3_pre_topc @ (k3_xboole_0 @ sk_C @ X0) @ sk_A)
% 3.61/3.85          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 3.61/3.85          | ~ (v3_pre_topc @ X0 @ sk_A)
% 3.61/3.85          | ~ (v3_pre_topc @ sk_C @ sk_A))),
% 3.61/3.85      inference('demod', [status(thm)], ['62', '63', '64'])).
% 3.61/3.85  thf('66', plain,
% 3.61/3.85      ((m1_subset_1 @ sk_C @ (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B)))),
% 3.61/3.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.61/3.85  thf('67', plain,
% 3.61/3.85      (![X19 : $i, X20 : $i, X21 : $i]:
% 3.61/3.85         (~ (m1_subset_1 @ X19 @ (u1_struct_0 @ X20))
% 3.61/3.85          | (v3_pre_topc @ (sk_D_1 @ X21 @ X19 @ X20) @ X20)
% 3.61/3.85          | ~ (m1_subset_1 @ X21 @ (u1_struct_0 @ (k9_yellow_6 @ X20 @ X19)))
% 3.61/3.85          | ~ (l1_pre_topc @ X20)
% 3.61/3.85          | ~ (v2_pre_topc @ X20)
% 3.61/3.85          | (v2_struct_0 @ X20))),
% 3.61/3.85      inference('cnf', [status(esa)], [t38_yellow_6])).
% 3.61/3.85  thf('68', plain,
% 3.61/3.85      (((v2_struct_0 @ sk_A)
% 3.61/3.85        | ~ (v2_pre_topc @ sk_A)
% 3.61/3.85        | ~ (l1_pre_topc @ sk_A)
% 3.61/3.85        | (v3_pre_topc @ (sk_D_1 @ sk_C @ sk_B @ sk_A) @ sk_A)
% 3.61/3.85        | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 3.61/3.85      inference('sup-', [status(thm)], ['66', '67'])).
% 3.61/3.85  thf('69', plain, ((v2_pre_topc @ sk_A)),
% 3.61/3.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.61/3.85  thf('70', plain, ((l1_pre_topc @ sk_A)),
% 3.61/3.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.61/3.85  thf('71', plain, (((sk_D_1 @ sk_C @ sk_B @ sk_A) = (sk_C))),
% 3.61/3.85      inference('clc', [status(thm)], ['12', '13'])).
% 3.61/3.85  thf('72', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 3.61/3.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.61/3.85  thf('73', plain, (((v2_struct_0 @ sk_A) | (v3_pre_topc @ sk_C @ sk_A))),
% 3.61/3.85      inference('demod', [status(thm)], ['68', '69', '70', '71', '72'])).
% 3.61/3.85  thf('74', plain, (~ (v2_struct_0 @ sk_A)),
% 3.61/3.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.61/3.85  thf('75', plain, ((v3_pre_topc @ sk_C @ sk_A)),
% 3.61/3.85      inference('clc', [status(thm)], ['73', '74'])).
% 3.61/3.85  thf('76', plain,
% 3.61/3.85      (![X0 : $i]:
% 3.61/3.85         ((v3_pre_topc @ (k3_xboole_0 @ sk_C @ X0) @ sk_A)
% 3.61/3.85          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 3.61/3.85          | ~ (v3_pre_topc @ X0 @ sk_A))),
% 3.61/3.85      inference('demod', [status(thm)], ['65', '75'])).
% 3.61/3.85  thf('77', plain,
% 3.61/3.85      ((~ (v3_pre_topc @ sk_D_2 @ sk_A)
% 3.61/3.85        | (v3_pre_topc @ (k3_xboole_0 @ sk_C @ sk_D_2) @ sk_A))),
% 3.61/3.85      inference('sup-', [status(thm)], ['50', '76'])).
% 3.61/3.85  thf('78', plain,
% 3.61/3.85      ((m1_subset_1 @ sk_D_2 @ (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B)))),
% 3.61/3.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.61/3.85  thf('79', plain,
% 3.61/3.85      (![X19 : $i, X20 : $i, X21 : $i]:
% 3.61/3.85         (~ (m1_subset_1 @ X19 @ (u1_struct_0 @ X20))
% 3.61/3.85          | (v3_pre_topc @ (sk_D_1 @ X21 @ X19 @ X20) @ X20)
% 3.61/3.85          | ~ (m1_subset_1 @ X21 @ (u1_struct_0 @ (k9_yellow_6 @ X20 @ X19)))
% 3.61/3.85          | ~ (l1_pre_topc @ X20)
% 3.61/3.85          | ~ (v2_pre_topc @ X20)
% 3.61/3.85          | (v2_struct_0 @ X20))),
% 3.61/3.85      inference('cnf', [status(esa)], [t38_yellow_6])).
% 3.61/3.85  thf('80', plain,
% 3.61/3.85      (((v2_struct_0 @ sk_A)
% 3.61/3.85        | ~ (v2_pre_topc @ sk_A)
% 3.61/3.85        | ~ (l1_pre_topc @ sk_A)
% 3.61/3.85        | (v3_pre_topc @ (sk_D_1 @ sk_D_2 @ sk_B @ sk_A) @ sk_A)
% 3.61/3.85        | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 3.61/3.85      inference('sup-', [status(thm)], ['78', '79'])).
% 3.61/3.85  thf('81', plain, ((v2_pre_topc @ sk_A)),
% 3.61/3.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.61/3.85  thf('82', plain, ((l1_pre_topc @ sk_A)),
% 3.61/3.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.61/3.85  thf('83', plain, (((sk_D_1 @ sk_D_2 @ sk_B @ sk_A) = (sk_D_2))),
% 3.61/3.85      inference('clc', [status(thm)], ['30', '31'])).
% 3.61/3.85  thf('84', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 3.61/3.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.61/3.85  thf('85', plain, (((v2_struct_0 @ sk_A) | (v3_pre_topc @ sk_D_2 @ sk_A))),
% 3.61/3.85      inference('demod', [status(thm)], ['80', '81', '82', '83', '84'])).
% 3.61/3.85  thf('86', plain, (~ (v2_struct_0 @ sk_A)),
% 3.61/3.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.61/3.85  thf('87', plain, ((v3_pre_topc @ sk_D_2 @ sk_A)),
% 3.61/3.85      inference('clc', [status(thm)], ['85', '86'])).
% 3.61/3.85  thf('88', plain, ((v3_pre_topc @ (k3_xboole_0 @ sk_C @ sk_D_2) @ sk_A)),
% 3.61/3.85      inference('demod', [status(thm)], ['77', '87'])).
% 3.61/3.85  thf('89', plain,
% 3.61/3.85      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.61/3.85      inference('clc', [status(thm)], ['58', '59'])).
% 3.61/3.85  thf(t3_subset, axiom,
% 3.61/3.85    (![A:$i,B:$i]:
% 3.61/3.85     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 3.61/3.85  thf('90', plain,
% 3.61/3.85      (![X13 : $i, X14 : $i]:
% 3.61/3.85         ((r1_tarski @ X13 @ X14) | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14)))),
% 3.61/3.85      inference('cnf', [status(esa)], [t3_subset])).
% 3.61/3.85  thf('91', plain, ((r1_tarski @ sk_C @ (u1_struct_0 @ sk_A))),
% 3.61/3.85      inference('sup-', [status(thm)], ['89', '90'])).
% 3.61/3.85  thf(t17_xboole_1, axiom,
% 3.61/3.85    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 3.61/3.85  thf('92', plain,
% 3.61/3.85      (![X6 : $i, X7 : $i]: (r1_tarski @ (k3_xboole_0 @ X6 @ X7) @ X6)),
% 3.61/3.85      inference('cnf', [status(esa)], [t17_xboole_1])).
% 3.61/3.85  thf(t1_xboole_1, axiom,
% 3.61/3.85    (![A:$i,B:$i,C:$i]:
% 3.61/3.85     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 3.61/3.85       ( r1_tarski @ A @ C ) ))).
% 3.61/3.85  thf('93', plain,
% 3.61/3.85      (![X8 : $i, X9 : $i, X10 : $i]:
% 3.61/3.85         (~ (r1_tarski @ X8 @ X9)
% 3.61/3.85          | ~ (r1_tarski @ X9 @ X10)
% 3.61/3.85          | (r1_tarski @ X8 @ X10))),
% 3.61/3.85      inference('cnf', [status(esa)], [t1_xboole_1])).
% 3.61/3.85  thf('94', plain,
% 3.61/3.85      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.61/3.85         ((r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ X2) | ~ (r1_tarski @ X0 @ X2))),
% 3.61/3.85      inference('sup-', [status(thm)], ['92', '93'])).
% 3.61/3.85  thf('95', plain,
% 3.61/3.85      (![X0 : $i]:
% 3.61/3.85         (r1_tarski @ (k3_xboole_0 @ sk_C @ X0) @ (u1_struct_0 @ sk_A))),
% 3.61/3.85      inference('sup-', [status(thm)], ['91', '94'])).
% 3.61/3.85  thf('96', plain,
% 3.61/3.85      (![X13 : $i, X15 : $i]:
% 3.61/3.85         ((m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X15)) | ~ (r1_tarski @ X13 @ X15))),
% 3.61/3.85      inference('cnf', [status(esa)], [t3_subset])).
% 3.61/3.85  thf('97', plain,
% 3.61/3.85      (![X0 : $i]:
% 3.61/3.85         (m1_subset_1 @ (k3_xboole_0 @ sk_C @ X0) @ 
% 3.61/3.85          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.61/3.85      inference('sup-', [status(thm)], ['95', '96'])).
% 3.61/3.85  thf(t39_yellow_6, axiom,
% 3.61/3.85    (![A:$i]:
% 3.61/3.85     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 3.61/3.85       ( ![B:$i]:
% 3.61/3.85         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 3.61/3.85           ( ![C:$i]:
% 3.61/3.85             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 3.61/3.85               ( ( r2_hidden @ C @ ( u1_struct_0 @ ( k9_yellow_6 @ A @ B ) ) ) <=>
% 3.61/3.85                 ( ( r2_hidden @ B @ C ) & ( v3_pre_topc @ C @ A ) ) ) ) ) ) ) ))).
% 3.61/3.85  thf('98', plain,
% 3.61/3.85      (![X22 : $i, X23 : $i, X24 : $i]:
% 3.61/3.85         (~ (m1_subset_1 @ X22 @ (u1_struct_0 @ X23))
% 3.61/3.85          | ~ (r2_hidden @ X22 @ X24)
% 3.61/3.85          | ~ (v3_pre_topc @ X24 @ X23)
% 3.61/3.85          | (r2_hidden @ X24 @ (u1_struct_0 @ (k9_yellow_6 @ X23 @ X22)))
% 3.61/3.85          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 3.61/3.85          | ~ (l1_pre_topc @ X23)
% 3.61/3.85          | ~ (v2_pre_topc @ X23)
% 3.61/3.85          | (v2_struct_0 @ X23))),
% 3.61/3.85      inference('cnf', [status(esa)], [t39_yellow_6])).
% 3.61/3.85  thf('99', plain,
% 3.61/3.85      (![X0 : $i, X1 : $i]:
% 3.61/3.85         ((v2_struct_0 @ sk_A)
% 3.61/3.85          | ~ (v2_pre_topc @ sk_A)
% 3.61/3.85          | ~ (l1_pre_topc @ sk_A)
% 3.61/3.85          | (r2_hidden @ (k3_xboole_0 @ sk_C @ X0) @ 
% 3.61/3.85             (u1_struct_0 @ (k9_yellow_6 @ sk_A @ X1)))
% 3.61/3.85          | ~ (v3_pre_topc @ (k3_xboole_0 @ sk_C @ X0) @ sk_A)
% 3.61/3.85          | ~ (r2_hidden @ X1 @ (k3_xboole_0 @ sk_C @ X0))
% 3.61/3.85          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 3.61/3.85      inference('sup-', [status(thm)], ['97', '98'])).
% 3.61/3.85  thf('100', plain, ((v2_pre_topc @ sk_A)),
% 3.61/3.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.61/3.85  thf('101', plain, ((l1_pre_topc @ sk_A)),
% 3.61/3.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.61/3.85  thf('102', plain,
% 3.61/3.85      (![X0 : $i, X1 : $i]:
% 3.61/3.85         ((v2_struct_0 @ sk_A)
% 3.61/3.85          | (r2_hidden @ (k3_xboole_0 @ sk_C @ X0) @ 
% 3.61/3.85             (u1_struct_0 @ (k9_yellow_6 @ sk_A @ X1)))
% 3.61/3.85          | ~ (v3_pre_topc @ (k3_xboole_0 @ sk_C @ X0) @ sk_A)
% 3.61/3.85          | ~ (r2_hidden @ X1 @ (k3_xboole_0 @ sk_C @ X0))
% 3.61/3.85          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 3.61/3.85      inference('demod', [status(thm)], ['99', '100', '101'])).
% 3.61/3.85  thf('103', plain,
% 3.61/3.85      (![X0 : $i]:
% 3.61/3.85         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 3.61/3.85          | ~ (r2_hidden @ X0 @ (k3_xboole_0 @ sk_C @ sk_D_2))
% 3.61/3.85          | (r2_hidden @ (k3_xboole_0 @ sk_C @ sk_D_2) @ 
% 3.61/3.85             (u1_struct_0 @ (k9_yellow_6 @ sk_A @ X0)))
% 3.61/3.85          | (v2_struct_0 @ sk_A))),
% 3.61/3.85      inference('sup-', [status(thm)], ['88', '102'])).
% 3.61/3.85  thf('104', plain,
% 3.61/3.85      (((v2_struct_0 @ sk_A)
% 3.61/3.85        | (r2_hidden @ (k3_xboole_0 @ sk_C @ sk_D_2) @ 
% 3.61/3.85           (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B)))
% 3.61/3.85        | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 3.61/3.85      inference('sup-', [status(thm)], ['40', '103'])).
% 3.61/3.85  thf('105', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 3.61/3.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.61/3.85  thf('106', plain,
% 3.61/3.85      (((v2_struct_0 @ sk_A)
% 3.61/3.85        | (r2_hidden @ (k3_xboole_0 @ sk_C @ sk_D_2) @ 
% 3.61/3.85           (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B))))),
% 3.61/3.85      inference('demod', [status(thm)], ['104', '105'])).
% 3.61/3.85  thf('107', plain, (~ (v2_struct_0 @ sk_A)),
% 3.61/3.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.61/3.85  thf('108', plain,
% 3.61/3.85      ((r2_hidden @ (k3_xboole_0 @ sk_C @ sk_D_2) @ 
% 3.61/3.85        (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B)))),
% 3.61/3.85      inference('clc', [status(thm)], ['106', '107'])).
% 3.61/3.85  thf(t1_subset, axiom,
% 3.61/3.85    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 3.61/3.85  thf('109', plain,
% 3.61/3.85      (![X11 : $i, X12 : $i]:
% 3.61/3.85         ((m1_subset_1 @ X11 @ X12) | ~ (r2_hidden @ X11 @ X12))),
% 3.61/3.85      inference('cnf', [status(esa)], [t1_subset])).
% 3.61/3.85  thf('110', plain,
% 3.61/3.85      ((m1_subset_1 @ (k3_xboole_0 @ sk_C @ sk_D_2) @ 
% 3.61/3.85        (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B)))),
% 3.61/3.85      inference('sup-', [status(thm)], ['108', '109'])).
% 3.61/3.85  thf('111', plain, ($false), inference('demod', [status(thm)], ['0', '110'])).
% 3.61/3.85  
% 3.61/3.85  % SZS output end Refutation
% 3.61/3.85  
% 3.61/3.86  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
