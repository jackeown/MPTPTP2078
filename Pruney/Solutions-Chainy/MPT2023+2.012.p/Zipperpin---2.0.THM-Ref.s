%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.5MiLLELmsP

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:14:26 EST 2020

% Result     : Theorem 20.41s
% Output     : Refutation 20.41s
% Verified   : 
% Statistics : Number of formulae       :  135 ( 388 expanded)
%              Number of leaves         :   24 ( 125 expanded)
%              Depth                    :   18
%              Number of atoms          : 1083 (7207 expanded)
%              Number of equality atoms :   18 (  53 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_D_2_type,type,(
    sk_D_2: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k9_yellow_6_type,type,(
    k9_yellow_6: $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

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
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ X23 ) )
      | ( r2_hidden @ X22 @ ( sk_D_1 @ X24 @ X22 @ X23 ) )
      | ~ ( m1_subset_1 @ X24 @ ( u1_struct_0 @ ( k9_yellow_6 @ X23 @ X22 ) ) )
      | ~ ( l1_pre_topc @ X23 )
      | ~ ( v2_pre_topc @ X23 )
      | ( v2_struct_0 @ X23 ) ) ),
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
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ X23 ) )
      | ( ( sk_D_1 @ X24 @ X22 @ X23 )
        = X24 )
      | ~ ( m1_subset_1 @ X24 @ ( u1_struct_0 @ ( k9_yellow_6 @ X23 @ X22 ) ) )
      | ~ ( l1_pre_topc @ X23 )
      | ~ ( v2_pre_topc @ X23 )
      | ( v2_struct_0 @ X23 ) ) ),
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
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ X23 ) )
      | ( r2_hidden @ X22 @ ( sk_D_1 @ X24 @ X22 @ X23 ) )
      | ~ ( m1_subset_1 @ X24 @ ( u1_struct_0 @ ( k9_yellow_6 @ X23 @ X22 ) ) )
      | ~ ( l1_pre_topc @ X23 )
      | ~ ( v2_pre_topc @ X23 )
      | ( v2_struct_0 @ X23 ) ) ),
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
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ X23 ) )
      | ( ( sk_D_1 @ X24 @ X22 @ X23 )
        = X24 )
      | ~ ( m1_subset_1 @ X24 @ ( u1_struct_0 @ ( k9_yellow_6 @ X23 @ X22 ) ) )
      | ~ ( l1_pre_topc @ X23 )
      | ~ ( v2_pre_topc @ X23 )
      | ( v2_struct_0 @ X23 ) ) ),
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
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ X23 ) )
      | ( m1_subset_1 @ ( sk_D_1 @ X24 @ X22 @ X23 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ~ ( m1_subset_1 @ X24 @ ( u1_struct_0 @ ( k9_yellow_6 @ X23 @ X22 ) ) )
      | ~ ( l1_pre_topc @ X23 )
      | ~ ( v2_pre_topc @ X23 )
      | ( v2_struct_0 @ X23 ) ) ),
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
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ X23 ) )
      | ( m1_subset_1 @ ( sk_D_1 @ X24 @ X22 @ X23 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ~ ( m1_subset_1 @ X24 @ ( u1_struct_0 @ ( k9_yellow_6 @ X23 @ X22 ) ) )
      | ~ ( l1_pre_topc @ X23 )
      | ~ ( v2_pre_topc @ X23 )
      | ( v2_struct_0 @ X23 ) ) ),
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
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ~ ( v3_pre_topc @ X19 @ X20 )
      | ~ ( l1_pre_topc @ X20 )
      | ~ ( v2_pre_topc @ X20 )
      | ~ ( v3_pre_topc @ X21 @ X20 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ( v3_pre_topc @ ( k3_xboole_0 @ X19 @ X21 ) @ X20 ) ) ),
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
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ X23 ) )
      | ( v3_pre_topc @ ( sk_D_1 @ X24 @ X22 @ X23 ) @ X23 )
      | ~ ( m1_subset_1 @ X24 @ ( u1_struct_0 @ ( k9_yellow_6 @ X23 @ X22 ) ) )
      | ~ ( l1_pre_topc @ X23 )
      | ~ ( v2_pre_topc @ X23 )
      | ( v2_struct_0 @ X23 ) ) ),
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
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ X23 ) )
      | ( v3_pre_topc @ ( sk_D_1 @ X24 @ X22 @ X23 ) @ X23 )
      | ~ ( m1_subset_1 @ X24 @ ( u1_struct_0 @ ( k9_yellow_6 @ X23 @ X22 ) ) )
      | ~ ( l1_pre_topc @ X23 )
      | ~ ( v2_pre_topc @ X23 )
      | ( v2_struct_0 @ X23 ) ) ),
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
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['48','49'])).

thf(dt_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k9_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('90',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( m1_subset_1 @ ( k9_subset_1 @ X6 @ X7 @ X8 ) @ ( k1_zfmisc_1 @ X6 ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k9_subset_1])).

thf('91',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_D_2 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['48','49'])).

thf(redefinition_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k3_xboole_0 @ B @ C ) ) ) )).

thf('93',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( ( k9_subset_1 @ X11 @ X9 @ X10 )
        = ( k3_xboole_0 @ X9 @ X10 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('94',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_D_2 )
      = ( k3_xboole_0 @ X0 @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X0 @ sk_D_2 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['91','94'])).

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

thf('96',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( u1_struct_0 @ X26 ) )
      | ~ ( r2_hidden @ X25 @ X27 )
      | ~ ( v3_pre_topc @ X27 @ X26 )
      | ( r2_hidden @ X27 @ ( u1_struct_0 @ ( k9_yellow_6 @ X26 @ X25 ) ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) )
      | ~ ( l1_pre_topc @ X26 )
      | ~ ( v2_pre_topc @ X26 )
      | ( v2_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t39_yellow_6])).

thf('97',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( r2_hidden @ ( k3_xboole_0 @ X0 @ sk_D_2 ) @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ X1 ) ) )
      | ~ ( v3_pre_topc @ ( k3_xboole_0 @ X0 @ sk_D_2 ) @ sk_A )
      | ~ ( r2_hidden @ X1 @ ( k3_xboole_0 @ X0 @ sk_D_2 ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ ( k3_xboole_0 @ X0 @ sk_D_2 ) @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ X1 ) ) )
      | ~ ( v3_pre_topc @ ( k3_xboole_0 @ X0 @ sk_D_2 ) @ sk_A )
      | ~ ( r2_hidden @ X1 @ ( k3_xboole_0 @ X0 @ sk_D_2 ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['97','98','99'])).

thf('101',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( k3_xboole_0 @ sk_C @ sk_D_2 ) )
      | ( r2_hidden @ ( k3_xboole_0 @ sk_C @ sk_D_2 ) @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ X0 ) ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['88','100'])).

thf('102',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ ( k3_xboole_0 @ sk_C @ sk_D_2 ) @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B ) ) )
    | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['40','101'])).

thf('103',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ ( k3_xboole_0 @ sk_C @ sk_D_2 ) @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['102','103'])).

thf('105',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,(
    r2_hidden @ ( k3_xboole_0 @ sk_C @ sk_D_2 ) @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['104','105'])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('107',plain,(
    ! [X14: $i,X15: $i] :
      ( ( m1_subset_1 @ X14 @ X15 )
      | ~ ( r2_hidden @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('108',plain,(
    m1_subset_1 @ ( k3_xboole_0 @ sk_C @ sk_D_2 ) @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf('109',plain,(
    $false ),
    inference(demod,[status(thm)],['0','108'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.5MiLLELmsP
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:43:12 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 20.41/20.61  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 20.41/20.61  % Solved by: fo/fo7.sh
% 20.41/20.61  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 20.41/20.61  % done 7965 iterations in 20.150s
% 20.41/20.61  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 20.41/20.61  % SZS output start Refutation
% 20.41/20.61  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 20.41/20.61  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 20.41/20.61  thf(sk_A_type, type, sk_A: $i).
% 20.41/20.61  thf(sk_C_type, type, sk_C: $i).
% 20.41/20.61  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 20.41/20.61  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i > $i).
% 20.41/20.61  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 20.41/20.61  thf(sk_D_2_type, type, sk_D_2: $i).
% 20.41/20.61  thf(sk_B_type, type, sk_B: $i).
% 20.41/20.61  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 20.41/20.61  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 20.41/20.61  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 20.41/20.61  thf(k9_yellow_6_type, type, k9_yellow_6: $i > $i > $i).
% 20.41/20.61  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 20.41/20.61  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 20.41/20.61  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 20.41/20.61  thf(t22_waybel_9, conjecture,
% 20.41/20.61    (![A:$i]:
% 20.41/20.61     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 20.41/20.61       ( ![B:$i]:
% 20.41/20.61         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 20.41/20.61           ( ![C:$i]:
% 20.41/20.61             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ ( k9_yellow_6 @ A @ B ) ) ) =>
% 20.41/20.61               ( ![D:$i]:
% 20.41/20.61                 ( ( m1_subset_1 @
% 20.41/20.61                     D @ ( u1_struct_0 @ ( k9_yellow_6 @ A @ B ) ) ) =>
% 20.41/20.61                   ( m1_subset_1 @
% 20.41/20.61                     ( k3_xboole_0 @ C @ D ) @ 
% 20.41/20.61                     ( u1_struct_0 @ ( k9_yellow_6 @ A @ B ) ) ) ) ) ) ) ) ) ))).
% 20.41/20.61  thf(zf_stmt_0, negated_conjecture,
% 20.41/20.61    (~( ![A:$i]:
% 20.41/20.61        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 20.41/20.61            ( l1_pre_topc @ A ) ) =>
% 20.41/20.61          ( ![B:$i]:
% 20.41/20.61            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 20.41/20.61              ( ![C:$i]:
% 20.41/20.61                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ ( k9_yellow_6 @ A @ B ) ) ) =>
% 20.41/20.61                  ( ![D:$i]:
% 20.41/20.61                    ( ( m1_subset_1 @
% 20.41/20.61                        D @ ( u1_struct_0 @ ( k9_yellow_6 @ A @ B ) ) ) =>
% 20.41/20.61                      ( m1_subset_1 @
% 20.41/20.61                        ( k3_xboole_0 @ C @ D ) @ 
% 20.41/20.61                        ( u1_struct_0 @ ( k9_yellow_6 @ A @ B ) ) ) ) ) ) ) ) ) ) )),
% 20.41/20.61    inference('cnf.neg', [status(esa)], [t22_waybel_9])).
% 20.41/20.61  thf('0', plain,
% 20.41/20.61      (~ (m1_subset_1 @ (k3_xboole_0 @ sk_C @ sk_D_2) @ 
% 20.41/20.61          (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B)))),
% 20.41/20.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.61  thf('1', plain,
% 20.41/20.61      ((m1_subset_1 @ sk_C @ (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B)))),
% 20.41/20.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.61  thf(t38_yellow_6, axiom,
% 20.41/20.61    (![A:$i]:
% 20.41/20.61     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 20.41/20.61       ( ![B:$i]:
% 20.41/20.61         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 20.41/20.61           ( ![C:$i]:
% 20.41/20.61             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ ( k9_yellow_6 @ A @ B ) ) ) =>
% 20.41/20.61               ( ?[D:$i]:
% 20.41/20.61                 ( ( v3_pre_topc @ D @ A ) & ( r2_hidden @ B @ D ) & 
% 20.41/20.61                   ( ( D ) = ( C ) ) & 
% 20.41/20.61                   ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ) ) ))).
% 20.41/20.61  thf('2', plain,
% 20.41/20.61      (![X22 : $i, X23 : $i, X24 : $i]:
% 20.41/20.61         (~ (m1_subset_1 @ X22 @ (u1_struct_0 @ X23))
% 20.41/20.61          | (r2_hidden @ X22 @ (sk_D_1 @ X24 @ X22 @ X23))
% 20.41/20.61          | ~ (m1_subset_1 @ X24 @ (u1_struct_0 @ (k9_yellow_6 @ X23 @ X22)))
% 20.41/20.61          | ~ (l1_pre_topc @ X23)
% 20.41/20.61          | ~ (v2_pre_topc @ X23)
% 20.41/20.61          | (v2_struct_0 @ X23))),
% 20.41/20.61      inference('cnf', [status(esa)], [t38_yellow_6])).
% 20.41/20.61  thf('3', plain,
% 20.41/20.61      (((v2_struct_0 @ sk_A)
% 20.41/20.61        | ~ (v2_pre_topc @ sk_A)
% 20.41/20.61        | ~ (l1_pre_topc @ sk_A)
% 20.41/20.61        | (r2_hidden @ sk_B @ (sk_D_1 @ sk_C @ sk_B @ sk_A))
% 20.41/20.61        | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 20.41/20.61      inference('sup-', [status(thm)], ['1', '2'])).
% 20.41/20.61  thf('4', plain, ((v2_pre_topc @ sk_A)),
% 20.41/20.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.61  thf('5', plain, ((l1_pre_topc @ sk_A)),
% 20.41/20.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.61  thf('6', plain,
% 20.41/20.61      ((m1_subset_1 @ sk_C @ (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B)))),
% 20.41/20.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.61  thf('7', plain,
% 20.41/20.61      (![X22 : $i, X23 : $i, X24 : $i]:
% 20.41/20.61         (~ (m1_subset_1 @ X22 @ (u1_struct_0 @ X23))
% 20.41/20.61          | ((sk_D_1 @ X24 @ X22 @ X23) = (X24))
% 20.41/20.61          | ~ (m1_subset_1 @ X24 @ (u1_struct_0 @ (k9_yellow_6 @ X23 @ X22)))
% 20.41/20.61          | ~ (l1_pre_topc @ X23)
% 20.41/20.61          | ~ (v2_pre_topc @ X23)
% 20.41/20.61          | (v2_struct_0 @ X23))),
% 20.41/20.61      inference('cnf', [status(esa)], [t38_yellow_6])).
% 20.41/20.61  thf('8', plain,
% 20.41/20.61      (((v2_struct_0 @ sk_A)
% 20.41/20.61        | ~ (v2_pre_topc @ sk_A)
% 20.41/20.61        | ~ (l1_pre_topc @ sk_A)
% 20.41/20.61        | ((sk_D_1 @ sk_C @ sk_B @ sk_A) = (sk_C))
% 20.41/20.61        | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 20.41/20.61      inference('sup-', [status(thm)], ['6', '7'])).
% 20.41/20.61  thf('9', plain, ((v2_pre_topc @ sk_A)),
% 20.41/20.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.61  thf('10', plain, ((l1_pre_topc @ sk_A)),
% 20.41/20.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.61  thf('11', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 20.41/20.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.61  thf('12', plain,
% 20.41/20.61      (((v2_struct_0 @ sk_A) | ((sk_D_1 @ sk_C @ sk_B @ sk_A) = (sk_C)))),
% 20.41/20.61      inference('demod', [status(thm)], ['8', '9', '10', '11'])).
% 20.41/20.61  thf('13', plain, (~ (v2_struct_0 @ sk_A)),
% 20.41/20.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.61  thf('14', plain, (((sk_D_1 @ sk_C @ sk_B @ sk_A) = (sk_C))),
% 20.41/20.61      inference('clc', [status(thm)], ['12', '13'])).
% 20.41/20.61  thf('15', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 20.41/20.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.61  thf('16', plain, (((v2_struct_0 @ sk_A) | (r2_hidden @ sk_B @ sk_C))),
% 20.41/20.61      inference('demod', [status(thm)], ['3', '4', '5', '14', '15'])).
% 20.41/20.61  thf('17', plain, (~ (v2_struct_0 @ sk_A)),
% 20.41/20.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.61  thf('18', plain, ((r2_hidden @ sk_B @ sk_C)),
% 20.41/20.61      inference('clc', [status(thm)], ['16', '17'])).
% 20.41/20.61  thf('19', plain,
% 20.41/20.61      ((m1_subset_1 @ sk_D_2 @ (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B)))),
% 20.41/20.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.61  thf('20', plain,
% 20.41/20.61      (![X22 : $i, X23 : $i, X24 : $i]:
% 20.41/20.61         (~ (m1_subset_1 @ X22 @ (u1_struct_0 @ X23))
% 20.41/20.61          | (r2_hidden @ X22 @ (sk_D_1 @ X24 @ X22 @ X23))
% 20.41/20.61          | ~ (m1_subset_1 @ X24 @ (u1_struct_0 @ (k9_yellow_6 @ X23 @ X22)))
% 20.41/20.61          | ~ (l1_pre_topc @ X23)
% 20.41/20.61          | ~ (v2_pre_topc @ X23)
% 20.41/20.61          | (v2_struct_0 @ X23))),
% 20.41/20.61      inference('cnf', [status(esa)], [t38_yellow_6])).
% 20.41/20.61  thf('21', plain,
% 20.41/20.61      (((v2_struct_0 @ sk_A)
% 20.41/20.61        | ~ (v2_pre_topc @ sk_A)
% 20.41/20.61        | ~ (l1_pre_topc @ sk_A)
% 20.41/20.61        | (r2_hidden @ sk_B @ (sk_D_1 @ sk_D_2 @ sk_B @ sk_A))
% 20.41/20.61        | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 20.41/20.61      inference('sup-', [status(thm)], ['19', '20'])).
% 20.41/20.61  thf('22', plain, ((v2_pre_topc @ sk_A)),
% 20.41/20.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.61  thf('23', plain, ((l1_pre_topc @ sk_A)),
% 20.41/20.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.61  thf('24', plain,
% 20.41/20.61      ((m1_subset_1 @ sk_D_2 @ (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B)))),
% 20.41/20.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.61  thf('25', plain,
% 20.41/20.61      (![X22 : $i, X23 : $i, X24 : $i]:
% 20.41/20.61         (~ (m1_subset_1 @ X22 @ (u1_struct_0 @ X23))
% 20.41/20.61          | ((sk_D_1 @ X24 @ X22 @ X23) = (X24))
% 20.41/20.61          | ~ (m1_subset_1 @ X24 @ (u1_struct_0 @ (k9_yellow_6 @ X23 @ X22)))
% 20.41/20.61          | ~ (l1_pre_topc @ X23)
% 20.41/20.61          | ~ (v2_pre_topc @ X23)
% 20.41/20.61          | (v2_struct_0 @ X23))),
% 20.41/20.61      inference('cnf', [status(esa)], [t38_yellow_6])).
% 20.41/20.61  thf('26', plain,
% 20.41/20.61      (((v2_struct_0 @ sk_A)
% 20.41/20.61        | ~ (v2_pre_topc @ sk_A)
% 20.41/20.61        | ~ (l1_pre_topc @ sk_A)
% 20.41/20.61        | ((sk_D_1 @ sk_D_2 @ sk_B @ sk_A) = (sk_D_2))
% 20.41/20.61        | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 20.41/20.61      inference('sup-', [status(thm)], ['24', '25'])).
% 20.41/20.61  thf('27', plain, ((v2_pre_topc @ sk_A)),
% 20.41/20.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.61  thf('28', plain, ((l1_pre_topc @ sk_A)),
% 20.41/20.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.61  thf('29', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 20.41/20.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.61  thf('30', plain,
% 20.41/20.61      (((v2_struct_0 @ sk_A) | ((sk_D_1 @ sk_D_2 @ sk_B @ sk_A) = (sk_D_2)))),
% 20.41/20.61      inference('demod', [status(thm)], ['26', '27', '28', '29'])).
% 20.41/20.61  thf('31', plain, (~ (v2_struct_0 @ sk_A)),
% 20.41/20.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.61  thf('32', plain, (((sk_D_1 @ sk_D_2 @ sk_B @ sk_A) = (sk_D_2))),
% 20.41/20.61      inference('clc', [status(thm)], ['30', '31'])).
% 20.41/20.61  thf('33', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 20.41/20.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.61  thf('34', plain, (((v2_struct_0 @ sk_A) | (r2_hidden @ sk_B @ sk_D_2))),
% 20.41/20.61      inference('demod', [status(thm)], ['21', '22', '23', '32', '33'])).
% 20.41/20.61  thf('35', plain, (~ (v2_struct_0 @ sk_A)),
% 20.41/20.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.61  thf('36', plain, ((r2_hidden @ sk_B @ sk_D_2)),
% 20.41/20.61      inference('clc', [status(thm)], ['34', '35'])).
% 20.41/20.61  thf(d4_xboole_0, axiom,
% 20.41/20.61    (![A:$i,B:$i,C:$i]:
% 20.41/20.61     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 20.41/20.61       ( ![D:$i]:
% 20.41/20.61         ( ( r2_hidden @ D @ C ) <=>
% 20.41/20.61           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 20.41/20.61  thf('37', plain,
% 20.41/20.61      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 20.41/20.61         (~ (r2_hidden @ X0 @ X1)
% 20.41/20.61          | ~ (r2_hidden @ X0 @ X2)
% 20.41/20.61          | (r2_hidden @ X0 @ X3)
% 20.41/20.61          | ((X3) != (k3_xboole_0 @ X1 @ X2)))),
% 20.41/20.61      inference('cnf', [status(esa)], [d4_xboole_0])).
% 20.41/20.61  thf('38', plain,
% 20.41/20.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 20.41/20.61         ((r2_hidden @ X0 @ (k3_xboole_0 @ X1 @ X2))
% 20.41/20.61          | ~ (r2_hidden @ X0 @ X2)
% 20.41/20.61          | ~ (r2_hidden @ X0 @ X1))),
% 20.41/20.61      inference('simplify', [status(thm)], ['37'])).
% 20.41/20.61  thf('39', plain,
% 20.41/20.61      (![X0 : $i]:
% 20.41/20.61         (~ (r2_hidden @ sk_B @ X0)
% 20.41/20.61          | (r2_hidden @ sk_B @ (k3_xboole_0 @ X0 @ sk_D_2)))),
% 20.41/20.61      inference('sup-', [status(thm)], ['36', '38'])).
% 20.41/20.61  thf('40', plain, ((r2_hidden @ sk_B @ (k3_xboole_0 @ sk_C @ sk_D_2))),
% 20.41/20.61      inference('sup-', [status(thm)], ['18', '39'])).
% 20.41/20.61  thf('41', plain,
% 20.41/20.61      ((m1_subset_1 @ sk_D_2 @ (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B)))),
% 20.41/20.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.61  thf('42', plain,
% 20.41/20.61      (![X22 : $i, X23 : $i, X24 : $i]:
% 20.41/20.61         (~ (m1_subset_1 @ X22 @ (u1_struct_0 @ X23))
% 20.41/20.61          | (m1_subset_1 @ (sk_D_1 @ X24 @ X22 @ X23) @ 
% 20.41/20.61             (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 20.41/20.61          | ~ (m1_subset_1 @ X24 @ (u1_struct_0 @ (k9_yellow_6 @ X23 @ X22)))
% 20.41/20.61          | ~ (l1_pre_topc @ X23)
% 20.41/20.61          | ~ (v2_pre_topc @ X23)
% 20.41/20.61          | (v2_struct_0 @ X23))),
% 20.41/20.61      inference('cnf', [status(esa)], [t38_yellow_6])).
% 20.41/20.61  thf('43', plain,
% 20.41/20.61      (((v2_struct_0 @ sk_A)
% 20.41/20.61        | ~ (v2_pre_topc @ sk_A)
% 20.41/20.61        | ~ (l1_pre_topc @ sk_A)
% 20.41/20.61        | (m1_subset_1 @ (sk_D_1 @ sk_D_2 @ sk_B @ sk_A) @ 
% 20.41/20.61           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 20.41/20.61        | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 20.41/20.61      inference('sup-', [status(thm)], ['41', '42'])).
% 20.41/20.61  thf('44', plain, ((v2_pre_topc @ sk_A)),
% 20.41/20.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.61  thf('45', plain, ((l1_pre_topc @ sk_A)),
% 20.41/20.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.61  thf('46', plain, (((sk_D_1 @ sk_D_2 @ sk_B @ sk_A) = (sk_D_2))),
% 20.41/20.61      inference('clc', [status(thm)], ['30', '31'])).
% 20.41/20.61  thf('47', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 20.41/20.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.61  thf('48', plain,
% 20.41/20.61      (((v2_struct_0 @ sk_A)
% 20.41/20.61        | (m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 20.41/20.61      inference('demod', [status(thm)], ['43', '44', '45', '46', '47'])).
% 20.41/20.61  thf('49', plain, (~ (v2_struct_0 @ sk_A)),
% 20.41/20.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.61  thf('50', plain,
% 20.41/20.61      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 20.41/20.61      inference('clc', [status(thm)], ['48', '49'])).
% 20.41/20.61  thf('51', plain,
% 20.41/20.61      ((m1_subset_1 @ sk_C @ (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B)))),
% 20.41/20.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.61  thf('52', plain,
% 20.41/20.61      (![X22 : $i, X23 : $i, X24 : $i]:
% 20.41/20.61         (~ (m1_subset_1 @ X22 @ (u1_struct_0 @ X23))
% 20.41/20.61          | (m1_subset_1 @ (sk_D_1 @ X24 @ X22 @ X23) @ 
% 20.41/20.61             (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 20.41/20.61          | ~ (m1_subset_1 @ X24 @ (u1_struct_0 @ (k9_yellow_6 @ X23 @ X22)))
% 20.41/20.61          | ~ (l1_pre_topc @ X23)
% 20.41/20.61          | ~ (v2_pre_topc @ X23)
% 20.41/20.61          | (v2_struct_0 @ X23))),
% 20.41/20.61      inference('cnf', [status(esa)], [t38_yellow_6])).
% 20.41/20.61  thf('53', plain,
% 20.41/20.61      (((v2_struct_0 @ sk_A)
% 20.41/20.61        | ~ (v2_pre_topc @ sk_A)
% 20.41/20.61        | ~ (l1_pre_topc @ sk_A)
% 20.41/20.61        | (m1_subset_1 @ (sk_D_1 @ sk_C @ sk_B @ sk_A) @ 
% 20.41/20.61           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 20.41/20.61        | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 20.41/20.61      inference('sup-', [status(thm)], ['51', '52'])).
% 20.41/20.61  thf('54', plain, ((v2_pre_topc @ sk_A)),
% 20.41/20.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.61  thf('55', plain, ((l1_pre_topc @ sk_A)),
% 20.41/20.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.61  thf('56', plain, (((sk_D_1 @ sk_C @ sk_B @ sk_A) = (sk_C))),
% 20.41/20.61      inference('clc', [status(thm)], ['12', '13'])).
% 20.41/20.61  thf('57', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 20.41/20.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.61  thf('58', plain,
% 20.41/20.61      (((v2_struct_0 @ sk_A)
% 20.41/20.61        | (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 20.41/20.61      inference('demod', [status(thm)], ['53', '54', '55', '56', '57'])).
% 20.41/20.61  thf('59', plain, (~ (v2_struct_0 @ sk_A)),
% 20.41/20.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.61  thf('60', plain,
% 20.41/20.61      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 20.41/20.61      inference('clc', [status(thm)], ['58', '59'])).
% 20.41/20.61  thf(fc6_tops_1, axiom,
% 20.41/20.61    (![A:$i,B:$i,C:$i]:
% 20.41/20.61     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & ( v3_pre_topc @ B @ A ) & 
% 20.41/20.61         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) & 
% 20.41/20.61         ( v3_pre_topc @ C @ A ) & 
% 20.41/20.61         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 20.41/20.61       ( v3_pre_topc @ ( k3_xboole_0 @ B @ C ) @ A ) ))).
% 20.41/20.61  thf('61', plain,
% 20.41/20.61      (![X19 : $i, X20 : $i, X21 : $i]:
% 20.41/20.61         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 20.41/20.61          | ~ (v3_pre_topc @ X19 @ X20)
% 20.41/20.61          | ~ (l1_pre_topc @ X20)
% 20.41/20.61          | ~ (v2_pre_topc @ X20)
% 20.41/20.61          | ~ (v3_pre_topc @ X21 @ X20)
% 20.41/20.61          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 20.41/20.61          | (v3_pre_topc @ (k3_xboole_0 @ X19 @ X21) @ X20))),
% 20.41/20.61      inference('cnf', [status(esa)], [fc6_tops_1])).
% 20.41/20.61  thf('62', plain,
% 20.41/20.61      (![X0 : $i]:
% 20.41/20.61         ((v3_pre_topc @ (k3_xboole_0 @ sk_C @ X0) @ sk_A)
% 20.41/20.61          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 20.41/20.61          | ~ (v3_pre_topc @ X0 @ sk_A)
% 20.41/20.61          | ~ (v2_pre_topc @ sk_A)
% 20.41/20.61          | ~ (l1_pre_topc @ sk_A)
% 20.41/20.61          | ~ (v3_pre_topc @ sk_C @ sk_A))),
% 20.41/20.61      inference('sup-', [status(thm)], ['60', '61'])).
% 20.41/20.61  thf('63', plain, ((v2_pre_topc @ sk_A)),
% 20.41/20.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.61  thf('64', plain, ((l1_pre_topc @ sk_A)),
% 20.41/20.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.61  thf('65', plain,
% 20.41/20.61      (![X0 : $i]:
% 20.41/20.61         ((v3_pre_topc @ (k3_xboole_0 @ sk_C @ X0) @ sk_A)
% 20.41/20.61          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 20.41/20.61          | ~ (v3_pre_topc @ X0 @ sk_A)
% 20.41/20.61          | ~ (v3_pre_topc @ sk_C @ sk_A))),
% 20.41/20.61      inference('demod', [status(thm)], ['62', '63', '64'])).
% 20.41/20.61  thf('66', plain,
% 20.41/20.61      ((m1_subset_1 @ sk_C @ (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B)))),
% 20.41/20.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.61  thf('67', plain,
% 20.41/20.61      (![X22 : $i, X23 : $i, X24 : $i]:
% 20.41/20.61         (~ (m1_subset_1 @ X22 @ (u1_struct_0 @ X23))
% 20.41/20.61          | (v3_pre_topc @ (sk_D_1 @ X24 @ X22 @ X23) @ X23)
% 20.41/20.61          | ~ (m1_subset_1 @ X24 @ (u1_struct_0 @ (k9_yellow_6 @ X23 @ X22)))
% 20.41/20.61          | ~ (l1_pre_topc @ X23)
% 20.41/20.61          | ~ (v2_pre_topc @ X23)
% 20.41/20.61          | (v2_struct_0 @ X23))),
% 20.41/20.61      inference('cnf', [status(esa)], [t38_yellow_6])).
% 20.41/20.61  thf('68', plain,
% 20.41/20.61      (((v2_struct_0 @ sk_A)
% 20.41/20.61        | ~ (v2_pre_topc @ sk_A)
% 20.41/20.61        | ~ (l1_pre_topc @ sk_A)
% 20.41/20.61        | (v3_pre_topc @ (sk_D_1 @ sk_C @ sk_B @ sk_A) @ sk_A)
% 20.41/20.61        | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 20.41/20.61      inference('sup-', [status(thm)], ['66', '67'])).
% 20.41/20.61  thf('69', plain, ((v2_pre_topc @ sk_A)),
% 20.41/20.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.61  thf('70', plain, ((l1_pre_topc @ sk_A)),
% 20.41/20.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.61  thf('71', plain, (((sk_D_1 @ sk_C @ sk_B @ sk_A) = (sk_C))),
% 20.41/20.61      inference('clc', [status(thm)], ['12', '13'])).
% 20.41/20.61  thf('72', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 20.41/20.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.61  thf('73', plain, (((v2_struct_0 @ sk_A) | (v3_pre_topc @ sk_C @ sk_A))),
% 20.41/20.61      inference('demod', [status(thm)], ['68', '69', '70', '71', '72'])).
% 20.41/20.61  thf('74', plain, (~ (v2_struct_0 @ sk_A)),
% 20.41/20.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.61  thf('75', plain, ((v3_pre_topc @ sk_C @ sk_A)),
% 20.41/20.61      inference('clc', [status(thm)], ['73', '74'])).
% 20.41/20.61  thf('76', plain,
% 20.41/20.61      (![X0 : $i]:
% 20.41/20.61         ((v3_pre_topc @ (k3_xboole_0 @ sk_C @ X0) @ sk_A)
% 20.41/20.61          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 20.41/20.61          | ~ (v3_pre_topc @ X0 @ sk_A))),
% 20.41/20.61      inference('demod', [status(thm)], ['65', '75'])).
% 20.41/20.61  thf('77', plain,
% 20.41/20.61      ((~ (v3_pre_topc @ sk_D_2 @ sk_A)
% 20.41/20.61        | (v3_pre_topc @ (k3_xboole_0 @ sk_C @ sk_D_2) @ sk_A))),
% 20.41/20.61      inference('sup-', [status(thm)], ['50', '76'])).
% 20.41/20.61  thf('78', plain,
% 20.41/20.61      ((m1_subset_1 @ sk_D_2 @ (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B)))),
% 20.41/20.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.61  thf('79', plain,
% 20.41/20.61      (![X22 : $i, X23 : $i, X24 : $i]:
% 20.41/20.61         (~ (m1_subset_1 @ X22 @ (u1_struct_0 @ X23))
% 20.41/20.61          | (v3_pre_topc @ (sk_D_1 @ X24 @ X22 @ X23) @ X23)
% 20.41/20.61          | ~ (m1_subset_1 @ X24 @ (u1_struct_0 @ (k9_yellow_6 @ X23 @ X22)))
% 20.41/20.61          | ~ (l1_pre_topc @ X23)
% 20.41/20.61          | ~ (v2_pre_topc @ X23)
% 20.41/20.61          | (v2_struct_0 @ X23))),
% 20.41/20.61      inference('cnf', [status(esa)], [t38_yellow_6])).
% 20.41/20.61  thf('80', plain,
% 20.41/20.61      (((v2_struct_0 @ sk_A)
% 20.41/20.61        | ~ (v2_pre_topc @ sk_A)
% 20.41/20.61        | ~ (l1_pre_topc @ sk_A)
% 20.41/20.61        | (v3_pre_topc @ (sk_D_1 @ sk_D_2 @ sk_B @ sk_A) @ sk_A)
% 20.41/20.61        | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 20.41/20.61      inference('sup-', [status(thm)], ['78', '79'])).
% 20.41/20.61  thf('81', plain, ((v2_pre_topc @ sk_A)),
% 20.41/20.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.61  thf('82', plain, ((l1_pre_topc @ sk_A)),
% 20.41/20.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.61  thf('83', plain, (((sk_D_1 @ sk_D_2 @ sk_B @ sk_A) = (sk_D_2))),
% 20.41/20.61      inference('clc', [status(thm)], ['30', '31'])).
% 20.41/20.61  thf('84', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 20.41/20.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.61  thf('85', plain, (((v2_struct_0 @ sk_A) | (v3_pre_topc @ sk_D_2 @ sk_A))),
% 20.41/20.61      inference('demod', [status(thm)], ['80', '81', '82', '83', '84'])).
% 20.41/20.61  thf('86', plain, (~ (v2_struct_0 @ sk_A)),
% 20.41/20.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.61  thf('87', plain, ((v3_pre_topc @ sk_D_2 @ sk_A)),
% 20.41/20.61      inference('clc', [status(thm)], ['85', '86'])).
% 20.41/20.61  thf('88', plain, ((v3_pre_topc @ (k3_xboole_0 @ sk_C @ sk_D_2) @ sk_A)),
% 20.41/20.61      inference('demod', [status(thm)], ['77', '87'])).
% 20.41/20.61  thf('89', plain,
% 20.41/20.61      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 20.41/20.61      inference('clc', [status(thm)], ['48', '49'])).
% 20.41/20.61  thf(dt_k9_subset_1, axiom,
% 20.41/20.61    (![A:$i,B:$i,C:$i]:
% 20.41/20.61     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 20.41/20.61       ( m1_subset_1 @ ( k9_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 20.41/20.61  thf('90', plain,
% 20.41/20.61      (![X6 : $i, X7 : $i, X8 : $i]:
% 20.41/20.61         ((m1_subset_1 @ (k9_subset_1 @ X6 @ X7 @ X8) @ (k1_zfmisc_1 @ X6))
% 20.41/20.61          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X6)))),
% 20.41/20.61      inference('cnf', [status(esa)], [dt_k9_subset_1])).
% 20.41/20.61  thf('91', plain,
% 20.41/20.61      (![X0 : $i]:
% 20.41/20.61         (m1_subset_1 @ (k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_D_2) @ 
% 20.41/20.61          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 20.41/20.61      inference('sup-', [status(thm)], ['89', '90'])).
% 20.41/20.61  thf('92', plain,
% 20.41/20.61      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 20.41/20.61      inference('clc', [status(thm)], ['48', '49'])).
% 20.41/20.61  thf(redefinition_k9_subset_1, axiom,
% 20.41/20.61    (![A:$i,B:$i,C:$i]:
% 20.41/20.61     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 20.41/20.61       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 20.41/20.61  thf('93', plain,
% 20.41/20.61      (![X9 : $i, X10 : $i, X11 : $i]:
% 20.41/20.61         (((k9_subset_1 @ X11 @ X9 @ X10) = (k3_xboole_0 @ X9 @ X10))
% 20.41/20.61          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11)))),
% 20.41/20.61      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 20.41/20.61  thf('94', plain,
% 20.41/20.61      (![X0 : $i]:
% 20.41/20.61         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_D_2)
% 20.41/20.61           = (k3_xboole_0 @ X0 @ sk_D_2))),
% 20.41/20.61      inference('sup-', [status(thm)], ['92', '93'])).
% 20.41/20.61  thf('95', plain,
% 20.41/20.61      (![X0 : $i]:
% 20.41/20.61         (m1_subset_1 @ (k3_xboole_0 @ X0 @ sk_D_2) @ 
% 20.41/20.61          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 20.41/20.61      inference('demod', [status(thm)], ['91', '94'])).
% 20.41/20.61  thf(t39_yellow_6, axiom,
% 20.41/20.61    (![A:$i]:
% 20.41/20.61     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 20.41/20.61       ( ![B:$i]:
% 20.41/20.61         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 20.41/20.61           ( ![C:$i]:
% 20.41/20.61             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 20.41/20.61               ( ( r2_hidden @ C @ ( u1_struct_0 @ ( k9_yellow_6 @ A @ B ) ) ) <=>
% 20.41/20.61                 ( ( r2_hidden @ B @ C ) & ( v3_pre_topc @ C @ A ) ) ) ) ) ) ) ))).
% 20.41/20.61  thf('96', plain,
% 20.41/20.61      (![X25 : $i, X26 : $i, X27 : $i]:
% 20.41/20.61         (~ (m1_subset_1 @ X25 @ (u1_struct_0 @ X26))
% 20.41/20.61          | ~ (r2_hidden @ X25 @ X27)
% 20.41/20.61          | ~ (v3_pre_topc @ X27 @ X26)
% 20.41/20.61          | (r2_hidden @ X27 @ (u1_struct_0 @ (k9_yellow_6 @ X26 @ X25)))
% 20.41/20.61          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ X26)))
% 20.41/20.61          | ~ (l1_pre_topc @ X26)
% 20.41/20.61          | ~ (v2_pre_topc @ X26)
% 20.41/20.61          | (v2_struct_0 @ X26))),
% 20.41/20.61      inference('cnf', [status(esa)], [t39_yellow_6])).
% 20.41/20.61  thf('97', plain,
% 20.41/20.61      (![X0 : $i, X1 : $i]:
% 20.41/20.61         ((v2_struct_0 @ sk_A)
% 20.41/20.61          | ~ (v2_pre_topc @ sk_A)
% 20.41/20.61          | ~ (l1_pre_topc @ sk_A)
% 20.41/20.61          | (r2_hidden @ (k3_xboole_0 @ X0 @ sk_D_2) @ 
% 20.41/20.61             (u1_struct_0 @ (k9_yellow_6 @ sk_A @ X1)))
% 20.41/20.61          | ~ (v3_pre_topc @ (k3_xboole_0 @ X0 @ sk_D_2) @ sk_A)
% 20.41/20.61          | ~ (r2_hidden @ X1 @ (k3_xboole_0 @ X0 @ sk_D_2))
% 20.41/20.61          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 20.41/20.61      inference('sup-', [status(thm)], ['95', '96'])).
% 20.41/20.61  thf('98', plain, ((v2_pre_topc @ sk_A)),
% 20.41/20.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.61  thf('99', plain, ((l1_pre_topc @ sk_A)),
% 20.41/20.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.61  thf('100', plain,
% 20.41/20.61      (![X0 : $i, X1 : $i]:
% 20.41/20.61         ((v2_struct_0 @ sk_A)
% 20.41/20.61          | (r2_hidden @ (k3_xboole_0 @ X0 @ sk_D_2) @ 
% 20.41/20.61             (u1_struct_0 @ (k9_yellow_6 @ sk_A @ X1)))
% 20.41/20.61          | ~ (v3_pre_topc @ (k3_xboole_0 @ X0 @ sk_D_2) @ sk_A)
% 20.41/20.61          | ~ (r2_hidden @ X1 @ (k3_xboole_0 @ X0 @ sk_D_2))
% 20.41/20.61          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 20.41/20.61      inference('demod', [status(thm)], ['97', '98', '99'])).
% 20.41/20.61  thf('101', plain,
% 20.41/20.61      (![X0 : $i]:
% 20.41/20.61         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 20.41/20.61          | ~ (r2_hidden @ X0 @ (k3_xboole_0 @ sk_C @ sk_D_2))
% 20.41/20.61          | (r2_hidden @ (k3_xboole_0 @ sk_C @ sk_D_2) @ 
% 20.41/20.61             (u1_struct_0 @ (k9_yellow_6 @ sk_A @ X0)))
% 20.41/20.61          | (v2_struct_0 @ sk_A))),
% 20.41/20.61      inference('sup-', [status(thm)], ['88', '100'])).
% 20.41/20.61  thf('102', plain,
% 20.41/20.61      (((v2_struct_0 @ sk_A)
% 20.41/20.61        | (r2_hidden @ (k3_xboole_0 @ sk_C @ sk_D_2) @ 
% 20.41/20.61           (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B)))
% 20.41/20.61        | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 20.41/20.61      inference('sup-', [status(thm)], ['40', '101'])).
% 20.41/20.61  thf('103', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 20.41/20.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.61  thf('104', plain,
% 20.41/20.61      (((v2_struct_0 @ sk_A)
% 20.41/20.61        | (r2_hidden @ (k3_xboole_0 @ sk_C @ sk_D_2) @ 
% 20.41/20.61           (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B))))),
% 20.41/20.61      inference('demod', [status(thm)], ['102', '103'])).
% 20.41/20.61  thf('105', plain, (~ (v2_struct_0 @ sk_A)),
% 20.41/20.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.61  thf('106', plain,
% 20.41/20.61      ((r2_hidden @ (k3_xboole_0 @ sk_C @ sk_D_2) @ 
% 20.41/20.61        (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B)))),
% 20.41/20.61      inference('clc', [status(thm)], ['104', '105'])).
% 20.41/20.61  thf(t1_subset, axiom,
% 20.41/20.61    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 20.41/20.61  thf('107', plain,
% 20.41/20.61      (![X14 : $i, X15 : $i]:
% 20.41/20.61         ((m1_subset_1 @ X14 @ X15) | ~ (r2_hidden @ X14 @ X15))),
% 20.41/20.61      inference('cnf', [status(esa)], [t1_subset])).
% 20.41/20.61  thf('108', plain,
% 20.41/20.61      ((m1_subset_1 @ (k3_xboole_0 @ sk_C @ sk_D_2) @ 
% 20.41/20.61        (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B)))),
% 20.41/20.61      inference('sup-', [status(thm)], ['106', '107'])).
% 20.41/20.61  thf('109', plain, ($false), inference('demod', [status(thm)], ['0', '108'])).
% 20.41/20.61  
% 20.41/20.61  % SZS output end Refutation
% 20.41/20.61  
% 20.41/20.62  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
