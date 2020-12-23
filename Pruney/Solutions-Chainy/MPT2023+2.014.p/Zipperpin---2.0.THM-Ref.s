%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.8Z3yrjso8G

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:14:26 EST 2020

% Result     : Theorem 17.41s
% Output     : Refutation 17.41s
% Verified   : 
% Statistics : Number of formulae       :  150 ( 372 expanded)
%              Number of leaves         :   25 ( 120 expanded)
%              Depth                    :   19
%              Number of atoms          : 1256 (6698 expanded)
%              Number of equality atoms :   29 (  65 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_D_2_type,type,(
    sk_D_2: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k9_yellow_6_type,type,(
    k9_yellow_6: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

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
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k3_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X2 )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('90',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['89'])).

thf('91',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ( r2_hidden @ X4 @ X2 )
      | ( X3
       != ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('92',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['91'])).

thf('93',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      | ( r2_hidden @ ( sk_D @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['90','92'])).

thf('94',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['89'])).

thf('95',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k3_xboole_0 @ X1 @ X2 ) )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X2 )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('96',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['96'])).

thf('98',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['89'])).

thf('99',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 ) ) ),
    inference(clc,[status(thm)],['97','98'])).

thf('100',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      | ( ( k3_xboole_0 @ X1 @ X0 )
        = ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['93','99'])).

thf('101',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['100'])).

thf('102',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['48','49'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('103',plain,(
    ! [X13: $i,X14: $i] :
      ( ( r1_tarski @ X13 @ X14 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('104',plain,(
    r1_tarski @ sk_D_2 @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['102','103'])).

thf(t108_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ ( k3_xboole_0 @ A @ C ) @ B ) ) )).

thf('105',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r1_tarski @ X6 @ X7 )
      | ( r1_tarski @ ( k3_xboole_0 @ X6 @ X8 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t108_xboole_1])).

thf('106',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ sk_D_2 @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['104','105'])).

thf('107',plain,(
    ! [X13: $i,X15: $i] :
      ( ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X15 ) )
      | ~ ( r1_tarski @ X13 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('108',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ sk_D_2 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf('109',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X0 @ sk_D_2 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['101','108'])).

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

thf('110',plain,(
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

thf('111',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( r2_hidden @ ( k3_xboole_0 @ X0 @ sk_D_2 ) @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ X1 ) ) )
      | ~ ( v3_pre_topc @ ( k3_xboole_0 @ X0 @ sk_D_2 ) @ sk_A )
      | ~ ( r2_hidden @ X1 @ ( k3_xboole_0 @ X0 @ sk_D_2 ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['109','110'])).

thf('112',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ ( k3_xboole_0 @ X0 @ sk_D_2 ) @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ X1 ) ) )
      | ~ ( v3_pre_topc @ ( k3_xboole_0 @ X0 @ sk_D_2 ) @ sk_A )
      | ~ ( r2_hidden @ X1 @ ( k3_xboole_0 @ X0 @ sk_D_2 ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['111','112','113'])).

thf('115',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( k3_xboole_0 @ sk_C @ sk_D_2 ) )
      | ( r2_hidden @ ( k3_xboole_0 @ sk_C @ sk_D_2 ) @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ X0 ) ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['88','114'])).

thf('116',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ ( k3_xboole_0 @ sk_C @ sk_D_2 ) @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B ) ) )
    | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['40','115'])).

thf('117',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ ( k3_xboole_0 @ sk_C @ sk_D_2 ) @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['116','117'])).

thf('119',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,(
    r2_hidden @ ( k3_xboole_0 @ sk_C @ sk_D_2 ) @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['118','119'])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('121',plain,(
    ! [X11: $i,X12: $i] :
      ( ( m1_subset_1 @ X11 @ X12 )
      | ~ ( r2_hidden @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('122',plain,(
    m1_subset_1 @ ( k3_xboole_0 @ sk_C @ sk_D_2 ) @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['120','121'])).

thf('123',plain,(
    $false ),
    inference(demod,[status(thm)],['0','122'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.8Z3yrjso8G
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:27:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 17.41/17.60  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 17.41/17.60  % Solved by: fo/fo7.sh
% 17.41/17.60  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 17.41/17.60  % done 7774 iterations in 17.136s
% 17.41/17.60  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 17.41/17.60  % SZS output start Refutation
% 17.41/17.60  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 17.41/17.60  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 17.41/17.60  thf(sk_D_2_type, type, sk_D_2: $i).
% 17.41/17.60  thf(sk_C_type, type, sk_C: $i).
% 17.41/17.60  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 17.41/17.60  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 17.41/17.60  thf(sk_B_type, type, sk_B: $i).
% 17.41/17.60  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 17.41/17.60  thf(k9_yellow_6_type, type, k9_yellow_6: $i > $i > $i).
% 17.41/17.60  thf(sk_A_type, type, sk_A: $i).
% 17.41/17.60  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 17.41/17.60  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 17.41/17.60  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 17.41/17.60  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i > $i).
% 17.41/17.60  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 17.41/17.60  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 17.41/17.60  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 17.41/17.60  thf(t22_waybel_9, conjecture,
% 17.41/17.60    (![A:$i]:
% 17.41/17.60     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 17.41/17.60       ( ![B:$i]:
% 17.41/17.60         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 17.41/17.60           ( ![C:$i]:
% 17.41/17.60             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ ( k9_yellow_6 @ A @ B ) ) ) =>
% 17.41/17.60               ( ![D:$i]:
% 17.41/17.60                 ( ( m1_subset_1 @
% 17.41/17.60                     D @ ( u1_struct_0 @ ( k9_yellow_6 @ A @ B ) ) ) =>
% 17.41/17.60                   ( m1_subset_1 @
% 17.41/17.60                     ( k3_xboole_0 @ C @ D ) @ 
% 17.41/17.60                     ( u1_struct_0 @ ( k9_yellow_6 @ A @ B ) ) ) ) ) ) ) ) ) ))).
% 17.41/17.60  thf(zf_stmt_0, negated_conjecture,
% 17.41/17.60    (~( ![A:$i]:
% 17.41/17.60        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 17.41/17.60            ( l1_pre_topc @ A ) ) =>
% 17.41/17.60          ( ![B:$i]:
% 17.41/17.60            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 17.41/17.60              ( ![C:$i]:
% 17.41/17.60                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ ( k9_yellow_6 @ A @ B ) ) ) =>
% 17.41/17.60                  ( ![D:$i]:
% 17.41/17.60                    ( ( m1_subset_1 @
% 17.41/17.60                        D @ ( u1_struct_0 @ ( k9_yellow_6 @ A @ B ) ) ) =>
% 17.41/17.60                      ( m1_subset_1 @
% 17.41/17.60                        ( k3_xboole_0 @ C @ D ) @ 
% 17.41/17.60                        ( u1_struct_0 @ ( k9_yellow_6 @ A @ B ) ) ) ) ) ) ) ) ) ) )),
% 17.41/17.60    inference('cnf.neg', [status(esa)], [t22_waybel_9])).
% 17.41/17.60  thf('0', plain,
% 17.41/17.60      (~ (m1_subset_1 @ (k3_xboole_0 @ sk_C @ sk_D_2) @ 
% 17.41/17.60          (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B)))),
% 17.41/17.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.41/17.60  thf('1', plain,
% 17.41/17.60      ((m1_subset_1 @ sk_C @ (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B)))),
% 17.41/17.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.41/17.60  thf(t38_yellow_6, axiom,
% 17.41/17.60    (![A:$i]:
% 17.41/17.60     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 17.41/17.60       ( ![B:$i]:
% 17.41/17.60         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 17.41/17.60           ( ![C:$i]:
% 17.41/17.60             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ ( k9_yellow_6 @ A @ B ) ) ) =>
% 17.41/17.60               ( ?[D:$i]:
% 17.41/17.60                 ( ( v3_pre_topc @ D @ A ) & ( r2_hidden @ B @ D ) & 
% 17.41/17.60                   ( ( D ) = ( C ) ) & 
% 17.41/17.60                   ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ) ) ))).
% 17.41/17.60  thf('2', plain,
% 17.41/17.60      (![X22 : $i, X23 : $i, X24 : $i]:
% 17.41/17.60         (~ (m1_subset_1 @ X22 @ (u1_struct_0 @ X23))
% 17.41/17.60          | (r2_hidden @ X22 @ (sk_D_1 @ X24 @ X22 @ X23))
% 17.41/17.60          | ~ (m1_subset_1 @ X24 @ (u1_struct_0 @ (k9_yellow_6 @ X23 @ X22)))
% 17.41/17.60          | ~ (l1_pre_topc @ X23)
% 17.41/17.60          | ~ (v2_pre_topc @ X23)
% 17.41/17.60          | (v2_struct_0 @ X23))),
% 17.41/17.60      inference('cnf', [status(esa)], [t38_yellow_6])).
% 17.41/17.60  thf('3', plain,
% 17.41/17.60      (((v2_struct_0 @ sk_A)
% 17.41/17.60        | ~ (v2_pre_topc @ sk_A)
% 17.41/17.60        | ~ (l1_pre_topc @ sk_A)
% 17.41/17.60        | (r2_hidden @ sk_B @ (sk_D_1 @ sk_C @ sk_B @ sk_A))
% 17.41/17.60        | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 17.41/17.60      inference('sup-', [status(thm)], ['1', '2'])).
% 17.41/17.60  thf('4', plain, ((v2_pre_topc @ sk_A)),
% 17.41/17.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.41/17.60  thf('5', plain, ((l1_pre_topc @ sk_A)),
% 17.41/17.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.41/17.60  thf('6', plain,
% 17.41/17.60      ((m1_subset_1 @ sk_C @ (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B)))),
% 17.41/17.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.41/17.60  thf('7', plain,
% 17.41/17.60      (![X22 : $i, X23 : $i, X24 : $i]:
% 17.41/17.60         (~ (m1_subset_1 @ X22 @ (u1_struct_0 @ X23))
% 17.41/17.60          | ((sk_D_1 @ X24 @ X22 @ X23) = (X24))
% 17.41/17.60          | ~ (m1_subset_1 @ X24 @ (u1_struct_0 @ (k9_yellow_6 @ X23 @ X22)))
% 17.41/17.60          | ~ (l1_pre_topc @ X23)
% 17.41/17.60          | ~ (v2_pre_topc @ X23)
% 17.41/17.60          | (v2_struct_0 @ X23))),
% 17.41/17.60      inference('cnf', [status(esa)], [t38_yellow_6])).
% 17.41/17.60  thf('8', plain,
% 17.41/17.60      (((v2_struct_0 @ sk_A)
% 17.41/17.60        | ~ (v2_pre_topc @ sk_A)
% 17.41/17.60        | ~ (l1_pre_topc @ sk_A)
% 17.41/17.60        | ((sk_D_1 @ sk_C @ sk_B @ sk_A) = (sk_C))
% 17.41/17.60        | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 17.41/17.60      inference('sup-', [status(thm)], ['6', '7'])).
% 17.41/17.60  thf('9', plain, ((v2_pre_topc @ sk_A)),
% 17.41/17.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.41/17.60  thf('10', plain, ((l1_pre_topc @ sk_A)),
% 17.41/17.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.41/17.60  thf('11', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 17.41/17.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.41/17.60  thf('12', plain,
% 17.41/17.60      (((v2_struct_0 @ sk_A) | ((sk_D_1 @ sk_C @ sk_B @ sk_A) = (sk_C)))),
% 17.41/17.60      inference('demod', [status(thm)], ['8', '9', '10', '11'])).
% 17.41/17.60  thf('13', plain, (~ (v2_struct_0 @ sk_A)),
% 17.41/17.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.41/17.60  thf('14', plain, (((sk_D_1 @ sk_C @ sk_B @ sk_A) = (sk_C))),
% 17.41/17.60      inference('clc', [status(thm)], ['12', '13'])).
% 17.41/17.60  thf('15', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 17.41/17.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.41/17.60  thf('16', plain, (((v2_struct_0 @ sk_A) | (r2_hidden @ sk_B @ sk_C))),
% 17.41/17.60      inference('demod', [status(thm)], ['3', '4', '5', '14', '15'])).
% 17.41/17.60  thf('17', plain, (~ (v2_struct_0 @ sk_A)),
% 17.41/17.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.41/17.60  thf('18', plain, ((r2_hidden @ sk_B @ sk_C)),
% 17.41/17.60      inference('clc', [status(thm)], ['16', '17'])).
% 17.41/17.60  thf('19', plain,
% 17.41/17.60      ((m1_subset_1 @ sk_D_2 @ (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B)))),
% 17.41/17.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.41/17.60  thf('20', plain,
% 17.41/17.60      (![X22 : $i, X23 : $i, X24 : $i]:
% 17.41/17.60         (~ (m1_subset_1 @ X22 @ (u1_struct_0 @ X23))
% 17.41/17.60          | (r2_hidden @ X22 @ (sk_D_1 @ X24 @ X22 @ X23))
% 17.41/17.60          | ~ (m1_subset_1 @ X24 @ (u1_struct_0 @ (k9_yellow_6 @ X23 @ X22)))
% 17.41/17.60          | ~ (l1_pre_topc @ X23)
% 17.41/17.60          | ~ (v2_pre_topc @ X23)
% 17.41/17.60          | (v2_struct_0 @ X23))),
% 17.41/17.60      inference('cnf', [status(esa)], [t38_yellow_6])).
% 17.41/17.60  thf('21', plain,
% 17.41/17.60      (((v2_struct_0 @ sk_A)
% 17.41/17.60        | ~ (v2_pre_topc @ sk_A)
% 17.41/17.60        | ~ (l1_pre_topc @ sk_A)
% 17.41/17.60        | (r2_hidden @ sk_B @ (sk_D_1 @ sk_D_2 @ sk_B @ sk_A))
% 17.41/17.60        | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 17.41/17.60      inference('sup-', [status(thm)], ['19', '20'])).
% 17.41/17.60  thf('22', plain, ((v2_pre_topc @ sk_A)),
% 17.41/17.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.41/17.60  thf('23', plain, ((l1_pre_topc @ sk_A)),
% 17.41/17.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.41/17.60  thf('24', plain,
% 17.41/17.60      ((m1_subset_1 @ sk_D_2 @ (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B)))),
% 17.41/17.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.41/17.60  thf('25', plain,
% 17.41/17.60      (![X22 : $i, X23 : $i, X24 : $i]:
% 17.41/17.60         (~ (m1_subset_1 @ X22 @ (u1_struct_0 @ X23))
% 17.41/17.60          | ((sk_D_1 @ X24 @ X22 @ X23) = (X24))
% 17.41/17.60          | ~ (m1_subset_1 @ X24 @ (u1_struct_0 @ (k9_yellow_6 @ X23 @ X22)))
% 17.41/17.60          | ~ (l1_pre_topc @ X23)
% 17.41/17.60          | ~ (v2_pre_topc @ X23)
% 17.41/17.60          | (v2_struct_0 @ X23))),
% 17.41/17.60      inference('cnf', [status(esa)], [t38_yellow_6])).
% 17.41/17.60  thf('26', plain,
% 17.41/17.60      (((v2_struct_0 @ sk_A)
% 17.41/17.60        | ~ (v2_pre_topc @ sk_A)
% 17.41/17.60        | ~ (l1_pre_topc @ sk_A)
% 17.41/17.60        | ((sk_D_1 @ sk_D_2 @ sk_B @ sk_A) = (sk_D_2))
% 17.41/17.60        | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 17.41/17.60      inference('sup-', [status(thm)], ['24', '25'])).
% 17.41/17.60  thf('27', plain, ((v2_pre_topc @ sk_A)),
% 17.41/17.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.41/17.60  thf('28', plain, ((l1_pre_topc @ sk_A)),
% 17.41/17.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.41/17.60  thf('29', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 17.41/17.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.41/17.60  thf('30', plain,
% 17.41/17.60      (((v2_struct_0 @ sk_A) | ((sk_D_1 @ sk_D_2 @ sk_B @ sk_A) = (sk_D_2)))),
% 17.41/17.60      inference('demod', [status(thm)], ['26', '27', '28', '29'])).
% 17.41/17.60  thf('31', plain, (~ (v2_struct_0 @ sk_A)),
% 17.41/17.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.41/17.60  thf('32', plain, (((sk_D_1 @ sk_D_2 @ sk_B @ sk_A) = (sk_D_2))),
% 17.41/17.60      inference('clc', [status(thm)], ['30', '31'])).
% 17.41/17.60  thf('33', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 17.41/17.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.41/17.60  thf('34', plain, (((v2_struct_0 @ sk_A) | (r2_hidden @ sk_B @ sk_D_2))),
% 17.41/17.60      inference('demod', [status(thm)], ['21', '22', '23', '32', '33'])).
% 17.41/17.60  thf('35', plain, (~ (v2_struct_0 @ sk_A)),
% 17.41/17.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.41/17.60  thf('36', plain, ((r2_hidden @ sk_B @ sk_D_2)),
% 17.41/17.60      inference('clc', [status(thm)], ['34', '35'])).
% 17.41/17.60  thf(d4_xboole_0, axiom,
% 17.41/17.60    (![A:$i,B:$i,C:$i]:
% 17.41/17.60     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 17.41/17.60       ( ![D:$i]:
% 17.41/17.60         ( ( r2_hidden @ D @ C ) <=>
% 17.41/17.60           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 17.41/17.60  thf('37', plain,
% 17.41/17.60      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 17.41/17.60         (~ (r2_hidden @ X0 @ X1)
% 17.41/17.60          | ~ (r2_hidden @ X0 @ X2)
% 17.41/17.60          | (r2_hidden @ X0 @ X3)
% 17.41/17.60          | ((X3) != (k3_xboole_0 @ X1 @ X2)))),
% 17.41/17.60      inference('cnf', [status(esa)], [d4_xboole_0])).
% 17.41/17.60  thf('38', plain,
% 17.41/17.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 17.41/17.60         ((r2_hidden @ X0 @ (k3_xboole_0 @ X1 @ X2))
% 17.41/17.60          | ~ (r2_hidden @ X0 @ X2)
% 17.41/17.60          | ~ (r2_hidden @ X0 @ X1))),
% 17.41/17.60      inference('simplify', [status(thm)], ['37'])).
% 17.41/17.60  thf('39', plain,
% 17.41/17.60      (![X0 : $i]:
% 17.41/17.60         (~ (r2_hidden @ sk_B @ X0)
% 17.41/17.60          | (r2_hidden @ sk_B @ (k3_xboole_0 @ X0 @ sk_D_2)))),
% 17.41/17.60      inference('sup-', [status(thm)], ['36', '38'])).
% 17.41/17.60  thf('40', plain, ((r2_hidden @ sk_B @ (k3_xboole_0 @ sk_C @ sk_D_2))),
% 17.41/17.60      inference('sup-', [status(thm)], ['18', '39'])).
% 17.41/17.60  thf('41', plain,
% 17.41/17.60      ((m1_subset_1 @ sk_D_2 @ (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B)))),
% 17.41/17.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.41/17.60  thf('42', plain,
% 17.41/17.60      (![X22 : $i, X23 : $i, X24 : $i]:
% 17.41/17.60         (~ (m1_subset_1 @ X22 @ (u1_struct_0 @ X23))
% 17.41/17.60          | (m1_subset_1 @ (sk_D_1 @ X24 @ X22 @ X23) @ 
% 17.41/17.60             (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 17.41/17.60          | ~ (m1_subset_1 @ X24 @ (u1_struct_0 @ (k9_yellow_6 @ X23 @ X22)))
% 17.41/17.60          | ~ (l1_pre_topc @ X23)
% 17.41/17.60          | ~ (v2_pre_topc @ X23)
% 17.41/17.60          | (v2_struct_0 @ X23))),
% 17.41/17.60      inference('cnf', [status(esa)], [t38_yellow_6])).
% 17.41/17.60  thf('43', plain,
% 17.41/17.60      (((v2_struct_0 @ sk_A)
% 17.41/17.60        | ~ (v2_pre_topc @ sk_A)
% 17.41/17.60        | ~ (l1_pre_topc @ sk_A)
% 17.41/17.60        | (m1_subset_1 @ (sk_D_1 @ sk_D_2 @ sk_B @ sk_A) @ 
% 17.41/17.60           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 17.41/17.60        | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 17.41/17.60      inference('sup-', [status(thm)], ['41', '42'])).
% 17.41/17.60  thf('44', plain, ((v2_pre_topc @ sk_A)),
% 17.41/17.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.41/17.60  thf('45', plain, ((l1_pre_topc @ sk_A)),
% 17.41/17.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.41/17.60  thf('46', plain, (((sk_D_1 @ sk_D_2 @ sk_B @ sk_A) = (sk_D_2))),
% 17.41/17.60      inference('clc', [status(thm)], ['30', '31'])).
% 17.41/17.60  thf('47', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 17.41/17.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.41/17.60  thf('48', plain,
% 17.41/17.60      (((v2_struct_0 @ sk_A)
% 17.41/17.60        | (m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 17.41/17.60      inference('demod', [status(thm)], ['43', '44', '45', '46', '47'])).
% 17.41/17.60  thf('49', plain, (~ (v2_struct_0 @ sk_A)),
% 17.41/17.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.41/17.60  thf('50', plain,
% 17.41/17.60      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 17.41/17.60      inference('clc', [status(thm)], ['48', '49'])).
% 17.41/17.60  thf('51', plain,
% 17.41/17.60      ((m1_subset_1 @ sk_C @ (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B)))),
% 17.41/17.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.41/17.60  thf('52', plain,
% 17.41/17.60      (![X22 : $i, X23 : $i, X24 : $i]:
% 17.41/17.60         (~ (m1_subset_1 @ X22 @ (u1_struct_0 @ X23))
% 17.41/17.60          | (m1_subset_1 @ (sk_D_1 @ X24 @ X22 @ X23) @ 
% 17.41/17.60             (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 17.41/17.60          | ~ (m1_subset_1 @ X24 @ (u1_struct_0 @ (k9_yellow_6 @ X23 @ X22)))
% 17.41/17.60          | ~ (l1_pre_topc @ X23)
% 17.41/17.60          | ~ (v2_pre_topc @ X23)
% 17.41/17.60          | (v2_struct_0 @ X23))),
% 17.41/17.60      inference('cnf', [status(esa)], [t38_yellow_6])).
% 17.41/17.60  thf('53', plain,
% 17.41/17.60      (((v2_struct_0 @ sk_A)
% 17.41/17.60        | ~ (v2_pre_topc @ sk_A)
% 17.41/17.60        | ~ (l1_pre_topc @ sk_A)
% 17.41/17.60        | (m1_subset_1 @ (sk_D_1 @ sk_C @ sk_B @ sk_A) @ 
% 17.41/17.60           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 17.41/17.60        | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 17.41/17.60      inference('sup-', [status(thm)], ['51', '52'])).
% 17.41/17.60  thf('54', plain, ((v2_pre_topc @ sk_A)),
% 17.41/17.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.41/17.60  thf('55', plain, ((l1_pre_topc @ sk_A)),
% 17.41/17.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.41/17.60  thf('56', plain, (((sk_D_1 @ sk_C @ sk_B @ sk_A) = (sk_C))),
% 17.41/17.60      inference('clc', [status(thm)], ['12', '13'])).
% 17.41/17.60  thf('57', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 17.41/17.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.41/17.60  thf('58', plain,
% 17.41/17.60      (((v2_struct_0 @ sk_A)
% 17.41/17.60        | (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 17.41/17.60      inference('demod', [status(thm)], ['53', '54', '55', '56', '57'])).
% 17.41/17.60  thf('59', plain, (~ (v2_struct_0 @ sk_A)),
% 17.41/17.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.41/17.60  thf('60', plain,
% 17.41/17.60      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 17.41/17.60      inference('clc', [status(thm)], ['58', '59'])).
% 17.41/17.60  thf(fc6_tops_1, axiom,
% 17.41/17.60    (![A:$i,B:$i,C:$i]:
% 17.41/17.60     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & ( v3_pre_topc @ B @ A ) & 
% 17.41/17.60         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) & 
% 17.41/17.60         ( v3_pre_topc @ C @ A ) & 
% 17.41/17.60         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 17.41/17.60       ( v3_pre_topc @ ( k3_xboole_0 @ B @ C ) @ A ) ))).
% 17.41/17.60  thf('61', plain,
% 17.41/17.60      (![X19 : $i, X20 : $i, X21 : $i]:
% 17.41/17.60         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 17.41/17.60          | ~ (v3_pre_topc @ X19 @ X20)
% 17.41/17.60          | ~ (l1_pre_topc @ X20)
% 17.41/17.60          | ~ (v2_pre_topc @ X20)
% 17.41/17.60          | ~ (v3_pre_topc @ X21 @ X20)
% 17.41/17.60          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 17.41/17.60          | (v3_pre_topc @ (k3_xboole_0 @ X19 @ X21) @ X20))),
% 17.41/17.60      inference('cnf', [status(esa)], [fc6_tops_1])).
% 17.41/17.60  thf('62', plain,
% 17.41/17.60      (![X0 : $i]:
% 17.41/17.60         ((v3_pre_topc @ (k3_xboole_0 @ sk_C @ X0) @ sk_A)
% 17.41/17.60          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 17.41/17.60          | ~ (v3_pre_topc @ X0 @ sk_A)
% 17.41/17.60          | ~ (v2_pre_topc @ sk_A)
% 17.41/17.60          | ~ (l1_pre_topc @ sk_A)
% 17.41/17.60          | ~ (v3_pre_topc @ sk_C @ sk_A))),
% 17.41/17.60      inference('sup-', [status(thm)], ['60', '61'])).
% 17.41/17.60  thf('63', plain, ((v2_pre_topc @ sk_A)),
% 17.41/17.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.41/17.60  thf('64', plain, ((l1_pre_topc @ sk_A)),
% 17.41/17.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.41/17.60  thf('65', plain,
% 17.41/17.60      (![X0 : $i]:
% 17.41/17.60         ((v3_pre_topc @ (k3_xboole_0 @ sk_C @ X0) @ sk_A)
% 17.41/17.60          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 17.41/17.60          | ~ (v3_pre_topc @ X0 @ sk_A)
% 17.41/17.60          | ~ (v3_pre_topc @ sk_C @ sk_A))),
% 17.41/17.60      inference('demod', [status(thm)], ['62', '63', '64'])).
% 17.41/17.60  thf('66', plain,
% 17.41/17.60      ((m1_subset_1 @ sk_C @ (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B)))),
% 17.41/17.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.41/17.60  thf('67', plain,
% 17.41/17.60      (![X22 : $i, X23 : $i, X24 : $i]:
% 17.41/17.60         (~ (m1_subset_1 @ X22 @ (u1_struct_0 @ X23))
% 17.41/17.60          | (v3_pre_topc @ (sk_D_1 @ X24 @ X22 @ X23) @ X23)
% 17.41/17.60          | ~ (m1_subset_1 @ X24 @ (u1_struct_0 @ (k9_yellow_6 @ X23 @ X22)))
% 17.41/17.60          | ~ (l1_pre_topc @ X23)
% 17.41/17.60          | ~ (v2_pre_topc @ X23)
% 17.41/17.60          | (v2_struct_0 @ X23))),
% 17.41/17.60      inference('cnf', [status(esa)], [t38_yellow_6])).
% 17.41/17.60  thf('68', plain,
% 17.41/17.60      (((v2_struct_0 @ sk_A)
% 17.41/17.60        | ~ (v2_pre_topc @ sk_A)
% 17.41/17.60        | ~ (l1_pre_topc @ sk_A)
% 17.41/17.60        | (v3_pre_topc @ (sk_D_1 @ sk_C @ sk_B @ sk_A) @ sk_A)
% 17.41/17.60        | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 17.41/17.60      inference('sup-', [status(thm)], ['66', '67'])).
% 17.41/17.60  thf('69', plain, ((v2_pre_topc @ sk_A)),
% 17.41/17.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.41/17.60  thf('70', plain, ((l1_pre_topc @ sk_A)),
% 17.41/17.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.41/17.60  thf('71', plain, (((sk_D_1 @ sk_C @ sk_B @ sk_A) = (sk_C))),
% 17.41/17.60      inference('clc', [status(thm)], ['12', '13'])).
% 17.41/17.60  thf('72', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 17.41/17.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.41/17.60  thf('73', plain, (((v2_struct_0 @ sk_A) | (v3_pre_topc @ sk_C @ sk_A))),
% 17.41/17.60      inference('demod', [status(thm)], ['68', '69', '70', '71', '72'])).
% 17.41/17.60  thf('74', plain, (~ (v2_struct_0 @ sk_A)),
% 17.41/17.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.41/17.60  thf('75', plain, ((v3_pre_topc @ sk_C @ sk_A)),
% 17.41/17.60      inference('clc', [status(thm)], ['73', '74'])).
% 17.41/17.60  thf('76', plain,
% 17.41/17.60      (![X0 : $i]:
% 17.41/17.60         ((v3_pre_topc @ (k3_xboole_0 @ sk_C @ X0) @ sk_A)
% 17.41/17.60          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 17.41/17.60          | ~ (v3_pre_topc @ X0 @ sk_A))),
% 17.41/17.60      inference('demod', [status(thm)], ['65', '75'])).
% 17.41/17.60  thf('77', plain,
% 17.41/17.60      ((~ (v3_pre_topc @ sk_D_2 @ sk_A)
% 17.41/17.60        | (v3_pre_topc @ (k3_xboole_0 @ sk_C @ sk_D_2) @ sk_A))),
% 17.41/17.60      inference('sup-', [status(thm)], ['50', '76'])).
% 17.41/17.60  thf('78', plain,
% 17.41/17.60      ((m1_subset_1 @ sk_D_2 @ (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B)))),
% 17.41/17.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.41/17.60  thf('79', plain,
% 17.41/17.60      (![X22 : $i, X23 : $i, X24 : $i]:
% 17.41/17.60         (~ (m1_subset_1 @ X22 @ (u1_struct_0 @ X23))
% 17.41/17.60          | (v3_pre_topc @ (sk_D_1 @ X24 @ X22 @ X23) @ X23)
% 17.41/17.60          | ~ (m1_subset_1 @ X24 @ (u1_struct_0 @ (k9_yellow_6 @ X23 @ X22)))
% 17.41/17.60          | ~ (l1_pre_topc @ X23)
% 17.41/17.60          | ~ (v2_pre_topc @ X23)
% 17.41/17.60          | (v2_struct_0 @ X23))),
% 17.41/17.60      inference('cnf', [status(esa)], [t38_yellow_6])).
% 17.41/17.60  thf('80', plain,
% 17.41/17.60      (((v2_struct_0 @ sk_A)
% 17.41/17.60        | ~ (v2_pre_topc @ sk_A)
% 17.41/17.60        | ~ (l1_pre_topc @ sk_A)
% 17.41/17.60        | (v3_pre_topc @ (sk_D_1 @ sk_D_2 @ sk_B @ sk_A) @ sk_A)
% 17.41/17.60        | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 17.41/17.60      inference('sup-', [status(thm)], ['78', '79'])).
% 17.41/17.60  thf('81', plain, ((v2_pre_topc @ sk_A)),
% 17.41/17.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.41/17.60  thf('82', plain, ((l1_pre_topc @ sk_A)),
% 17.41/17.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.41/17.60  thf('83', plain, (((sk_D_1 @ sk_D_2 @ sk_B @ sk_A) = (sk_D_2))),
% 17.41/17.60      inference('clc', [status(thm)], ['30', '31'])).
% 17.41/17.60  thf('84', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 17.41/17.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.41/17.60  thf('85', plain, (((v2_struct_0 @ sk_A) | (v3_pre_topc @ sk_D_2 @ sk_A))),
% 17.41/17.60      inference('demod', [status(thm)], ['80', '81', '82', '83', '84'])).
% 17.41/17.60  thf('86', plain, (~ (v2_struct_0 @ sk_A)),
% 17.41/17.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.41/17.60  thf('87', plain, ((v3_pre_topc @ sk_D_2 @ sk_A)),
% 17.41/17.60      inference('clc', [status(thm)], ['85', '86'])).
% 17.41/17.60  thf('88', plain, ((v3_pre_topc @ (k3_xboole_0 @ sk_C @ sk_D_2) @ sk_A)),
% 17.41/17.60      inference('demod', [status(thm)], ['77', '87'])).
% 17.41/17.60  thf('89', plain,
% 17.41/17.60      (![X1 : $i, X2 : $i, X5 : $i]:
% 17.41/17.60         (((X5) = (k3_xboole_0 @ X1 @ X2))
% 17.41/17.60          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X2)
% 17.41/17.60          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 17.41/17.60      inference('cnf', [status(esa)], [d4_xboole_0])).
% 17.41/17.60  thf('90', plain,
% 17.41/17.60      (![X0 : $i, X1 : $i]:
% 17.41/17.60         ((r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 17.41/17.60          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 17.41/17.60      inference('eq_fact', [status(thm)], ['89'])).
% 17.41/17.60  thf('91', plain,
% 17.41/17.60      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 17.41/17.60         (~ (r2_hidden @ X4 @ X3)
% 17.41/17.60          | (r2_hidden @ X4 @ X2)
% 17.41/17.60          | ((X3) != (k3_xboole_0 @ X1 @ X2)))),
% 17.41/17.60      inference('cnf', [status(esa)], [d4_xboole_0])).
% 17.41/17.60  thf('92', plain,
% 17.41/17.60      (![X1 : $i, X2 : $i, X4 : $i]:
% 17.41/17.60         ((r2_hidden @ X4 @ X2) | ~ (r2_hidden @ X4 @ (k3_xboole_0 @ X1 @ X2)))),
% 17.41/17.60      inference('simplify', [status(thm)], ['91'])).
% 17.41/17.60  thf('93', plain,
% 17.41/17.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 17.41/17.60         (((k3_xboole_0 @ X1 @ X0)
% 17.41/17.60            = (k3_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0)))
% 17.41/17.60          | (r2_hidden @ 
% 17.41/17.60             (sk_D @ (k3_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0) @ X2) @ 
% 17.41/17.60             X0))),
% 17.41/17.60      inference('sup-', [status(thm)], ['90', '92'])).
% 17.41/17.60  thf('94', plain,
% 17.41/17.60      (![X0 : $i, X1 : $i]:
% 17.41/17.60         ((r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 17.41/17.60          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 17.41/17.60      inference('eq_fact', [status(thm)], ['89'])).
% 17.41/17.60  thf('95', plain,
% 17.41/17.60      (![X1 : $i, X2 : $i, X5 : $i]:
% 17.41/17.60         (((X5) = (k3_xboole_0 @ X1 @ X2))
% 17.41/17.60          | ~ (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X2)
% 17.41/17.60          | ~ (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X1)
% 17.41/17.60          | ~ (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 17.41/17.60      inference('cnf', [status(esa)], [d4_xboole_0])).
% 17.41/17.60  thf('96', plain,
% 17.41/17.60      (![X0 : $i, X1 : $i]:
% 17.41/17.60         (((X0) = (k3_xboole_0 @ X1 @ X0))
% 17.41/17.60          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 17.41/17.60          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1)
% 17.41/17.60          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 17.41/17.60      inference('sup-', [status(thm)], ['94', '95'])).
% 17.41/17.60  thf('97', plain,
% 17.41/17.60      (![X0 : $i, X1 : $i]:
% 17.41/17.60         (~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1)
% 17.41/17.60          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 17.41/17.60          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 17.41/17.60      inference('simplify', [status(thm)], ['96'])).
% 17.41/17.60  thf('98', plain,
% 17.41/17.60      (![X0 : $i, X1 : $i]:
% 17.41/17.60         ((r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 17.41/17.60          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 17.41/17.60      inference('eq_fact', [status(thm)], ['89'])).
% 17.41/17.60  thf('99', plain,
% 17.41/17.60      (![X0 : $i, X1 : $i]:
% 17.41/17.60         (((X0) = (k3_xboole_0 @ X1 @ X0))
% 17.41/17.60          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1))),
% 17.41/17.60      inference('clc', [status(thm)], ['97', '98'])).
% 17.41/17.60  thf('100', plain,
% 17.41/17.60      (![X0 : $i, X1 : $i]:
% 17.41/17.60         (((k3_xboole_0 @ X1 @ X0)
% 17.41/17.60            = (k3_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))
% 17.41/17.60          | ((k3_xboole_0 @ X1 @ X0)
% 17.41/17.60              = (k3_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))))),
% 17.41/17.60      inference('sup-', [status(thm)], ['93', '99'])).
% 17.41/17.60  thf('101', plain,
% 17.41/17.60      (![X0 : $i, X1 : $i]:
% 17.41/17.60         ((k3_xboole_0 @ X1 @ X0)
% 17.41/17.60           = (k3_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 17.41/17.60      inference('simplify', [status(thm)], ['100'])).
% 17.41/17.60  thf('102', plain,
% 17.41/17.60      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 17.41/17.60      inference('clc', [status(thm)], ['48', '49'])).
% 17.41/17.60  thf(t3_subset, axiom,
% 17.41/17.60    (![A:$i,B:$i]:
% 17.41/17.60     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 17.41/17.60  thf('103', plain,
% 17.41/17.60      (![X13 : $i, X14 : $i]:
% 17.41/17.60         ((r1_tarski @ X13 @ X14) | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14)))),
% 17.41/17.60      inference('cnf', [status(esa)], [t3_subset])).
% 17.41/17.60  thf('104', plain, ((r1_tarski @ sk_D_2 @ (u1_struct_0 @ sk_A))),
% 17.41/17.60      inference('sup-', [status(thm)], ['102', '103'])).
% 17.41/17.60  thf(t108_xboole_1, axiom,
% 17.41/17.60    (![A:$i,B:$i,C:$i]:
% 17.41/17.60     ( ( r1_tarski @ A @ B ) => ( r1_tarski @ ( k3_xboole_0 @ A @ C ) @ B ) ))).
% 17.41/17.60  thf('105', plain,
% 17.41/17.60      (![X6 : $i, X7 : $i, X8 : $i]:
% 17.41/17.60         (~ (r1_tarski @ X6 @ X7) | (r1_tarski @ (k3_xboole_0 @ X6 @ X8) @ X7))),
% 17.41/17.60      inference('cnf', [status(esa)], [t108_xboole_1])).
% 17.41/17.60  thf('106', plain,
% 17.41/17.60      (![X0 : $i]:
% 17.41/17.60         (r1_tarski @ (k3_xboole_0 @ sk_D_2 @ X0) @ (u1_struct_0 @ sk_A))),
% 17.41/17.60      inference('sup-', [status(thm)], ['104', '105'])).
% 17.41/17.60  thf('107', plain,
% 17.41/17.60      (![X13 : $i, X15 : $i]:
% 17.41/17.60         ((m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X15)) | ~ (r1_tarski @ X13 @ X15))),
% 17.41/17.60      inference('cnf', [status(esa)], [t3_subset])).
% 17.41/17.60  thf('108', plain,
% 17.41/17.60      (![X0 : $i]:
% 17.41/17.60         (m1_subset_1 @ (k3_xboole_0 @ sk_D_2 @ X0) @ 
% 17.41/17.60          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 17.41/17.60      inference('sup-', [status(thm)], ['106', '107'])).
% 17.41/17.60  thf('109', plain,
% 17.41/17.60      (![X0 : $i]:
% 17.41/17.60         (m1_subset_1 @ (k3_xboole_0 @ X0 @ sk_D_2) @ 
% 17.41/17.60          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 17.41/17.60      inference('sup+', [status(thm)], ['101', '108'])).
% 17.41/17.60  thf(t39_yellow_6, axiom,
% 17.41/17.60    (![A:$i]:
% 17.41/17.60     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 17.41/17.60       ( ![B:$i]:
% 17.41/17.60         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 17.41/17.60           ( ![C:$i]:
% 17.41/17.60             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 17.41/17.60               ( ( r2_hidden @ C @ ( u1_struct_0 @ ( k9_yellow_6 @ A @ B ) ) ) <=>
% 17.41/17.60                 ( ( r2_hidden @ B @ C ) & ( v3_pre_topc @ C @ A ) ) ) ) ) ) ) ))).
% 17.41/17.60  thf('110', plain,
% 17.41/17.60      (![X25 : $i, X26 : $i, X27 : $i]:
% 17.41/17.60         (~ (m1_subset_1 @ X25 @ (u1_struct_0 @ X26))
% 17.41/17.60          | ~ (r2_hidden @ X25 @ X27)
% 17.41/17.60          | ~ (v3_pre_topc @ X27 @ X26)
% 17.41/17.60          | (r2_hidden @ X27 @ (u1_struct_0 @ (k9_yellow_6 @ X26 @ X25)))
% 17.41/17.60          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ X26)))
% 17.41/17.60          | ~ (l1_pre_topc @ X26)
% 17.41/17.60          | ~ (v2_pre_topc @ X26)
% 17.41/17.60          | (v2_struct_0 @ X26))),
% 17.41/17.60      inference('cnf', [status(esa)], [t39_yellow_6])).
% 17.41/17.60  thf('111', plain,
% 17.41/17.60      (![X0 : $i, X1 : $i]:
% 17.41/17.60         ((v2_struct_0 @ sk_A)
% 17.41/17.60          | ~ (v2_pre_topc @ sk_A)
% 17.41/17.60          | ~ (l1_pre_topc @ sk_A)
% 17.41/17.60          | (r2_hidden @ (k3_xboole_0 @ X0 @ sk_D_2) @ 
% 17.41/17.60             (u1_struct_0 @ (k9_yellow_6 @ sk_A @ X1)))
% 17.41/17.60          | ~ (v3_pre_topc @ (k3_xboole_0 @ X0 @ sk_D_2) @ sk_A)
% 17.41/17.60          | ~ (r2_hidden @ X1 @ (k3_xboole_0 @ X0 @ sk_D_2))
% 17.41/17.60          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 17.41/17.60      inference('sup-', [status(thm)], ['109', '110'])).
% 17.41/17.60  thf('112', plain, ((v2_pre_topc @ sk_A)),
% 17.41/17.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.41/17.60  thf('113', plain, ((l1_pre_topc @ sk_A)),
% 17.41/17.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.41/17.60  thf('114', plain,
% 17.41/17.60      (![X0 : $i, X1 : $i]:
% 17.41/17.60         ((v2_struct_0 @ sk_A)
% 17.41/17.60          | (r2_hidden @ (k3_xboole_0 @ X0 @ sk_D_2) @ 
% 17.41/17.60             (u1_struct_0 @ (k9_yellow_6 @ sk_A @ X1)))
% 17.41/17.60          | ~ (v3_pre_topc @ (k3_xboole_0 @ X0 @ sk_D_2) @ sk_A)
% 17.41/17.60          | ~ (r2_hidden @ X1 @ (k3_xboole_0 @ X0 @ sk_D_2))
% 17.41/17.60          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 17.41/17.60      inference('demod', [status(thm)], ['111', '112', '113'])).
% 17.41/17.60  thf('115', plain,
% 17.41/17.60      (![X0 : $i]:
% 17.41/17.60         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 17.41/17.60          | ~ (r2_hidden @ X0 @ (k3_xboole_0 @ sk_C @ sk_D_2))
% 17.41/17.60          | (r2_hidden @ (k3_xboole_0 @ sk_C @ sk_D_2) @ 
% 17.41/17.60             (u1_struct_0 @ (k9_yellow_6 @ sk_A @ X0)))
% 17.41/17.60          | (v2_struct_0 @ sk_A))),
% 17.41/17.60      inference('sup-', [status(thm)], ['88', '114'])).
% 17.41/17.60  thf('116', plain,
% 17.41/17.60      (((v2_struct_0 @ sk_A)
% 17.41/17.60        | (r2_hidden @ (k3_xboole_0 @ sk_C @ sk_D_2) @ 
% 17.41/17.60           (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B)))
% 17.41/17.60        | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 17.41/17.60      inference('sup-', [status(thm)], ['40', '115'])).
% 17.41/17.60  thf('117', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 17.41/17.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.41/17.60  thf('118', plain,
% 17.41/17.60      (((v2_struct_0 @ sk_A)
% 17.41/17.60        | (r2_hidden @ (k3_xboole_0 @ sk_C @ sk_D_2) @ 
% 17.41/17.60           (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B))))),
% 17.41/17.60      inference('demod', [status(thm)], ['116', '117'])).
% 17.41/17.60  thf('119', plain, (~ (v2_struct_0 @ sk_A)),
% 17.41/17.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.41/17.60  thf('120', plain,
% 17.41/17.60      ((r2_hidden @ (k3_xboole_0 @ sk_C @ sk_D_2) @ 
% 17.41/17.60        (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B)))),
% 17.41/17.60      inference('clc', [status(thm)], ['118', '119'])).
% 17.41/17.60  thf(t1_subset, axiom,
% 17.41/17.60    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 17.41/17.60  thf('121', plain,
% 17.41/17.60      (![X11 : $i, X12 : $i]:
% 17.41/17.60         ((m1_subset_1 @ X11 @ X12) | ~ (r2_hidden @ X11 @ X12))),
% 17.41/17.60      inference('cnf', [status(esa)], [t1_subset])).
% 17.41/17.60  thf('122', plain,
% 17.41/17.60      ((m1_subset_1 @ (k3_xboole_0 @ sk_C @ sk_D_2) @ 
% 17.41/17.60        (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B)))),
% 17.41/17.60      inference('sup-', [status(thm)], ['120', '121'])).
% 17.41/17.60  thf('123', plain, ($false), inference('demod', [status(thm)], ['0', '122'])).
% 17.41/17.60  
% 17.41/17.60  % SZS output end Refutation
% 17.41/17.60  
% 17.41/17.61  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
