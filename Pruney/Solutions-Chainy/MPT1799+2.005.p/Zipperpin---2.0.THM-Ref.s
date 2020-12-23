%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.4NvETP7DuL

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:10:54 EST 2020

% Result     : Theorem 0.35s
% Output     : Refutation 0.35s
% Verified   : 
% Statistics : Number of formulae       :  114 ( 244 expanded)
%              Number of leaves         :   26 (  81 expanded)
%              Depth                    :   12
%              Number of atoms          :  932 (4045 expanded)
%              Number of equality atoms :   24 ( 119 expanded)
%              Maximal formula depth    :   13 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k8_tmap_1_type,type,(
    k8_tmap_1: $i > $i > $i )).

thf(k5_tmap_1_type,type,(
    k5_tmap_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_tsep_1_type,type,(
    v1_tsep_1: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(t115_tmap_1,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( m1_pre_topc @ B @ A ) )
         => ! [C: $i] :
              ( ( m1_pre_topc @ C @ ( k8_tmap_1 @ A @ B ) )
             => ( ( ( u1_struct_0 @ C )
                  = ( u1_struct_0 @ B ) )
               => ( ( v1_tsep_1 @ C @ ( k8_tmap_1 @ A @ B ) )
                  & ( m1_pre_topc @ C @ ( k8_tmap_1 @ A @ B ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( ~ ( v2_struct_0 @ B )
              & ( m1_pre_topc @ B @ A ) )
           => ! [C: $i] :
                ( ( m1_pre_topc @ C @ ( k8_tmap_1 @ A @ B ) )
               => ( ( ( u1_struct_0 @ C )
                    = ( u1_struct_0 @ B ) )
                 => ( ( v1_tsep_1 @ C @ ( k8_tmap_1 @ A @ B ) )
                    & ( m1_pre_topc @ C @ ( k8_tmap_1 @ A @ B ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t115_tmap_1])).

thf('0',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t35_borsuk_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( r1_tarski @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) )).

thf('1',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( m1_pre_topc @ X15 @ X16 )
      | ( r1_tarski @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ X16 ) )
      | ~ ( l1_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[t35_borsuk_1])).

thf('2',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( u1_struct_0 @ sk_C )
    = ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['2','3','4'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('6',plain,(
    ! [X0: $i,X2: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X2 ) )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('7',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t114_tmap_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( m1_pre_topc @ B @ A ) )
         => ( ( ( u1_struct_0 @ ( k8_tmap_1 @ A @ B ) )
              = ( u1_struct_0 @ A ) )
            & ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
               => ( ( C
                    = ( u1_struct_0 @ B ) )
                 => ( ( u1_pre_topc @ ( k8_tmap_1 @ A @ B ) )
                    = ( k5_tmap_1 @ A @ C ) ) ) ) ) ) ) )).

thf('9',plain,(
    ! [X9: $i,X10: $i] :
      ( ( v2_struct_0 @ X9 )
      | ~ ( m1_pre_topc @ X9 @ X10 )
      | ( ( u1_struct_0 @ ( k8_tmap_1 @ X10 @ X9 ) )
        = ( u1_struct_0 @ X10 ) )
      | ~ ( l1_pre_topc @ X10 )
      | ~ ( v2_pre_topc @ X10 )
      | ( v2_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t114_tmap_1])).

thf('10',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
      = ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
      = ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['10','11','12'])).

thf('14',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['13','14'])).

thf('16',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['15','16'])).

thf(t16_tsep_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( C
                  = ( u1_struct_0 @ B ) )
               => ( ( ( v1_tsep_1 @ B @ A )
                    & ( m1_pre_topc @ B @ A ) )
                <=> ( v3_pre_topc @ C @ A ) ) ) ) ) ) )).

thf('18',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_pre_topc @ X12 @ X13 )
      | ( X14
       != ( u1_struct_0 @ X12 ) )
      | ~ ( v3_pre_topc @ X14 @ X13 )
      | ( v1_tsep_1 @ X12 @ X13 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ~ ( l1_pre_topc @ X13 )
      | ~ ( v2_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[t16_tsep_1])).

thf('19',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v2_pre_topc @ X13 )
      | ~ ( l1_pre_topc @ X13 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X12 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ( v1_tsep_1 @ X12 @ X13 )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ X12 ) @ X13 )
      | ~ ( m1_pre_topc @ X12 @ X13 ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( m1_pre_topc @ X0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ ( k8_tmap_1 @ sk_A @ sk_B ) )
      | ( v1_tsep_1 @ X0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
      | ~ ( l1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
      | ~ ( v2_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['17','19'])).

thf('21',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k8_tmap_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_pre_topc @ B @ A ) )
     => ( ( v1_pre_topc @ ( k8_tmap_1 @ A @ B ) )
        & ( v2_pre_topc @ ( k8_tmap_1 @ A @ B ) )
        & ( l1_pre_topc @ ( k8_tmap_1 @ A @ B ) ) ) ) )).

thf('22',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( l1_pre_topc @ X5 )
      | ~ ( v2_pre_topc @ X5 )
      | ( v2_struct_0 @ X5 )
      | ~ ( m1_pre_topc @ X6 @ X5 )
      | ( l1_pre_topc @ ( k8_tmap_1 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k8_tmap_1])).

thf('23',plain,
    ( ( l1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ( l1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['23','24','25'])).

thf('27',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    l1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['26','27'])).

thf('29',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( l1_pre_topc @ X5 )
      | ~ ( v2_pre_topc @ X5 )
      | ( v2_struct_0 @ X5 )
      | ~ ( m1_pre_topc @ X6 @ X5 )
      | ( v2_pre_topc @ ( k8_tmap_1 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k8_tmap_1])).

thf('31',plain,
    ( ( v2_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ( v2_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['31','32','33'])).

thf('35',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    v2_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( m1_pre_topc @ X0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ ( k8_tmap_1 @ sk_A @ sk_B ) )
      | ( v1_tsep_1 @ X0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['20','28','36'])).

thf('38',plain,
    ( ( v1_tsep_1 @ sk_C @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( m1_pre_topc @ sk_C @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['7','37'])).

thf('39',plain,(
    m1_pre_topc @ sk_C @ ( k8_tmap_1 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,
    ( ( v1_tsep_1 @ sk_C @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,
    ( ~ ( v1_tsep_1 @ sk_C @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( m1_pre_topc @ sk_C @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( ~ ( v1_tsep_1 @ sk_C @ ( k8_tmap_1 @ sk_A @ sk_B ) )
   <= ~ ( v1_tsep_1 @ sk_C @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['41'])).

thf('43',plain,(
    m1_pre_topc @ sk_C @ ( k8_tmap_1 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,
    ( ~ ( m1_pre_topc @ sk_C @ ( k8_tmap_1 @ sk_A @ sk_B ) )
   <= ~ ( m1_pre_topc @ sk_C @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['41'])).

thf('45',plain,(
    m1_pre_topc @ sk_C @ ( k8_tmap_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,
    ( ~ ( v1_tsep_1 @ sk_C @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( m1_pre_topc @ sk_C @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['41'])).

thf('47',plain,(
    ~ ( v1_tsep_1 @ sk_C @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sat_resolution*',[status(thm)],['45','46'])).

thf('48',plain,(
    ~ ( v1_tsep_1 @ sk_C @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(simpl_trail,[status(thm)],['42','47'])).

thf('49',plain,(
    ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['40','48'])).

thf('50',plain,(
    m1_pre_topc @ sk_C @ ( k8_tmap_1 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( m1_pre_topc @ X15 @ X16 )
      | ( r1_tarski @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ X16 ) )
      | ~ ( l1_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[t35_borsuk_1])).

thf('52',plain,
    ( ~ ( l1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( r1_tarski @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    l1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['26','27'])).

thf('54',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i,X2: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X2 ) )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('56',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf(d5_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v3_pre_topc @ B @ A )
          <=> ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) ) ) ) )).

thf('57',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X4 ) ) )
      | ~ ( r2_hidden @ X3 @ ( u1_pre_topc @ X4 ) )
      | ( v3_pre_topc @ X3 @ X4 )
      | ~ ( l1_pre_topc @ X4 ) ) ),
    inference(cnf,[status(esa)],[d5_pre_topc])).

thf('58',plain,
    ( ~ ( l1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v3_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( r2_hidden @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    l1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['26','27'])).

thf('60',plain,
    ( ( v3_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( r2_hidden @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('62',plain,
    ( ( u1_struct_0 @ sk_C )
    = ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( v2_struct_0 @ X9 )
      | ~ ( m1_pre_topc @ X9 @ X10 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ( ( u1_pre_topc @ ( k8_tmap_1 @ X10 @ X9 ) )
        = ( k5_tmap_1 @ X10 @ X11 ) )
      | ( X11
       != ( u1_struct_0 @ X9 ) )
      | ~ ( l1_pre_topc @ X10 )
      | ~ ( v2_pre_topc @ X10 )
      | ( v2_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t114_tmap_1])).

thf('64',plain,(
    ! [X9: $i,X10: $i] :
      ( ( v2_struct_0 @ X10 )
      | ~ ( v2_pre_topc @ X10 )
      | ~ ( l1_pre_topc @ X10 )
      | ( ( u1_pre_topc @ ( k8_tmap_1 @ X10 @ X9 ) )
        = ( k5_tmap_1 @ X10 @ ( u1_struct_0 @ X9 ) ) )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X9 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ~ ( m1_pre_topc @ X9 @ X10 )
      | ( v2_struct_0 @ X9 ) ) ),
    inference(simplify,[status(thm)],['63'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ sk_B @ X0 )
      | ( ( u1_pre_topc @ ( k8_tmap_1 @ X0 @ sk_B ) )
        = ( k5_tmap_1 @ X0 @ ( u1_struct_0 @ sk_B ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['62','64'])).

thf('66',plain,
    ( ( u1_struct_0 @ sk_C )
    = ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ sk_B @ X0 )
      | ( ( u1_pre_topc @ ( k8_tmap_1 @ X0 @ sk_B ) )
        = ( k5_tmap_1 @ X0 @ ( u1_struct_0 @ sk_C ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['65','66'])).

thf('68',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( ( u1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
      = ( k5_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_C ) ) )
    | ~ ( m1_pre_topc @ sk_B @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['61','67'])).

thf('69',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( u1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
      = ( k5_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_C ) ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['68','69','70','71'])).

thf('73',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( u1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
      = ( k5_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference(clc,[status(thm)],['72','73'])).

thf('75',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,
    ( ( u1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    = ( k5_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_C ) ) ),
    inference(clc,[status(thm)],['74','75'])).

thf('77',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(t102_tmap_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r2_hidden @ B @ ( k5_tmap_1 @ A @ B ) ) ) ) )).

thf('78',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ( r2_hidden @ X7 @ ( k5_tmap_1 @ X8 @ X7 ) )
      | ~ ( l1_pre_topc @ X8 )
      | ~ ( v2_pre_topc @ X8 )
      | ( v2_struct_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t102_tmap_1])).

thf('79',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( r2_hidden @ ( u1_struct_0 @ sk_C ) @ ( k5_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ ( u1_struct_0 @ sk_C ) @ ( k5_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['79','80','81'])).

thf('83',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    r2_hidden @ ( u1_struct_0 @ sk_C ) @ ( k5_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_C ) ) ),
    inference(clc,[status(thm)],['82','83'])).

thf('85',plain,(
    v3_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( k8_tmap_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['60','76','84'])).

thf('86',plain,(
    $false ),
    inference(demod,[status(thm)],['49','85'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.4NvETP7DuL
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:17:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.35/0.53  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.35/0.53  % Solved by: fo/fo7.sh
% 0.35/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.35/0.53  % done 94 iterations in 0.059s
% 0.35/0.53  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.35/0.53  % SZS output start Refutation
% 0.35/0.53  thf(k8_tmap_1_type, type, k8_tmap_1: $i > $i > $i).
% 0.35/0.53  thf(k5_tmap_1_type, type, k5_tmap_1: $i > $i > $i).
% 0.35/0.53  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.35/0.53  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.35/0.53  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 0.35/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.35/0.53  thf(sk_C_type, type, sk_C: $i).
% 0.35/0.53  thf(v1_tsep_1_type, type, v1_tsep_1: $i > $i > $o).
% 0.35/0.53  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.35/0.53  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 0.35/0.53  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.35/0.53  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.35/0.53  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.35/0.53  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.35/0.53  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.35/0.53  thf(sk_B_type, type, sk_B: $i).
% 0.35/0.53  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.35/0.53  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.35/0.53  thf(t115_tmap_1, conjecture,
% 0.35/0.53    (![A:$i]:
% 0.35/0.53     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.35/0.53       ( ![B:$i]:
% 0.35/0.53         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.35/0.53           ( ![C:$i]:
% 0.35/0.53             ( ( m1_pre_topc @ C @ ( k8_tmap_1 @ A @ B ) ) =>
% 0.35/0.53               ( ( ( u1_struct_0 @ C ) = ( u1_struct_0 @ B ) ) =>
% 0.35/0.53                 ( ( v1_tsep_1 @ C @ ( k8_tmap_1 @ A @ B ) ) & 
% 0.35/0.53                   ( m1_pre_topc @ C @ ( k8_tmap_1 @ A @ B ) ) ) ) ) ) ) ) ))).
% 0.35/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.35/0.53    (~( ![A:$i]:
% 0.35/0.53        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.35/0.53            ( l1_pre_topc @ A ) ) =>
% 0.35/0.53          ( ![B:$i]:
% 0.35/0.53            ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.35/0.53              ( ![C:$i]:
% 0.35/0.53                ( ( m1_pre_topc @ C @ ( k8_tmap_1 @ A @ B ) ) =>
% 0.35/0.53                  ( ( ( u1_struct_0 @ C ) = ( u1_struct_0 @ B ) ) =>
% 0.35/0.53                    ( ( v1_tsep_1 @ C @ ( k8_tmap_1 @ A @ B ) ) & 
% 0.35/0.53                      ( m1_pre_topc @ C @ ( k8_tmap_1 @ A @ B ) ) ) ) ) ) ) ) ) )),
% 0.35/0.53    inference('cnf.neg', [status(esa)], [t115_tmap_1])).
% 0.35/0.53  thf('0', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf(t35_borsuk_1, axiom,
% 0.35/0.53    (![A:$i]:
% 0.35/0.53     ( ( l1_pre_topc @ A ) =>
% 0.35/0.53       ( ![B:$i]:
% 0.35/0.53         ( ( m1_pre_topc @ B @ A ) =>
% 0.35/0.53           ( r1_tarski @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ))).
% 0.35/0.53  thf('1', plain,
% 0.35/0.53      (![X15 : $i, X16 : $i]:
% 0.35/0.53         (~ (m1_pre_topc @ X15 @ X16)
% 0.35/0.53          | (r1_tarski @ (u1_struct_0 @ X15) @ (u1_struct_0 @ X16))
% 0.35/0.53          | ~ (l1_pre_topc @ X16))),
% 0.35/0.53      inference('cnf', [status(esa)], [t35_borsuk_1])).
% 0.35/0.53  thf('2', plain,
% 0.35/0.53      ((~ (l1_pre_topc @ sk_A)
% 0.35/0.53        | (r1_tarski @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 0.35/0.53      inference('sup-', [status(thm)], ['0', '1'])).
% 0.35/0.53  thf('3', plain, ((l1_pre_topc @ sk_A)),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf('4', plain, (((u1_struct_0 @ sk_C) = (u1_struct_0 @ sk_B))),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf('5', plain, ((r1_tarski @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A))),
% 0.35/0.53      inference('demod', [status(thm)], ['2', '3', '4'])).
% 0.35/0.53  thf(t3_subset, axiom,
% 0.35/0.53    (![A:$i,B:$i]:
% 0.35/0.53     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.35/0.53  thf('6', plain,
% 0.35/0.53      (![X0 : $i, X2 : $i]:
% 0.35/0.53         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X2)) | ~ (r1_tarski @ X0 @ X2))),
% 0.35/0.53      inference('cnf', [status(esa)], [t3_subset])).
% 0.35/0.53  thf('7', plain,
% 0.35/0.53      ((m1_subset_1 @ (u1_struct_0 @ sk_C) @ 
% 0.35/0.53        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.35/0.53      inference('sup-', [status(thm)], ['5', '6'])).
% 0.35/0.53  thf('8', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf(t114_tmap_1, axiom,
% 0.35/0.53    (![A:$i]:
% 0.35/0.53     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.35/0.53       ( ![B:$i]:
% 0.35/0.53         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.35/0.53           ( ( ( u1_struct_0 @ ( k8_tmap_1 @ A @ B ) ) = ( u1_struct_0 @ A ) ) & 
% 0.35/0.53             ( ![C:$i]:
% 0.35/0.53               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.35/0.53                 ( ( ( C ) = ( u1_struct_0 @ B ) ) =>
% 0.35/0.53                   ( ( u1_pre_topc @ ( k8_tmap_1 @ A @ B ) ) =
% 0.35/0.53                     ( k5_tmap_1 @ A @ C ) ) ) ) ) ) ) ) ))).
% 0.35/0.53  thf('9', plain,
% 0.35/0.53      (![X9 : $i, X10 : $i]:
% 0.35/0.53         ((v2_struct_0 @ X9)
% 0.35/0.53          | ~ (m1_pre_topc @ X9 @ X10)
% 0.35/0.53          | ((u1_struct_0 @ (k8_tmap_1 @ X10 @ X9)) = (u1_struct_0 @ X10))
% 0.35/0.53          | ~ (l1_pre_topc @ X10)
% 0.35/0.53          | ~ (v2_pre_topc @ X10)
% 0.35/0.53          | (v2_struct_0 @ X10))),
% 0.35/0.53      inference('cnf', [status(esa)], [t114_tmap_1])).
% 0.35/0.53  thf('10', plain,
% 0.35/0.53      (((v2_struct_0 @ sk_A)
% 0.35/0.53        | ~ (v2_pre_topc @ sk_A)
% 0.35/0.53        | ~ (l1_pre_topc @ sk_A)
% 0.35/0.53        | ((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))
% 0.35/0.53        | (v2_struct_0 @ sk_B))),
% 0.35/0.53      inference('sup-', [status(thm)], ['8', '9'])).
% 0.35/0.53  thf('11', plain, ((v2_pre_topc @ sk_A)),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf('12', plain, ((l1_pre_topc @ sk_A)),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf('13', plain,
% 0.35/0.53      (((v2_struct_0 @ sk_A)
% 0.35/0.53        | ((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))
% 0.35/0.53        | (v2_struct_0 @ sk_B))),
% 0.35/0.53      inference('demod', [status(thm)], ['10', '11', '12'])).
% 0.35/0.53  thf('14', plain, (~ (v2_struct_0 @ sk_A)),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf('15', plain,
% 0.35/0.53      (((v2_struct_0 @ sk_B)
% 0.35/0.53        | ((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A)))),
% 0.35/0.53      inference('clc', [status(thm)], ['13', '14'])).
% 0.35/0.53  thf('16', plain, (~ (v2_struct_0 @ sk_B)),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf('17', plain,
% 0.35/0.53      (((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 0.35/0.53      inference('clc', [status(thm)], ['15', '16'])).
% 0.35/0.53  thf(t16_tsep_1, axiom,
% 0.35/0.53    (![A:$i]:
% 0.35/0.53     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.35/0.53       ( ![B:$i]:
% 0.35/0.53         ( ( m1_pre_topc @ B @ A ) =>
% 0.35/0.53           ( ![C:$i]:
% 0.35/0.53             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.35/0.53               ( ( ( C ) = ( u1_struct_0 @ B ) ) =>
% 0.35/0.53                 ( ( ( v1_tsep_1 @ B @ A ) & ( m1_pre_topc @ B @ A ) ) <=>
% 0.35/0.53                   ( v3_pre_topc @ C @ A ) ) ) ) ) ) ) ))).
% 0.35/0.53  thf('18', plain,
% 0.35/0.53      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.35/0.53         (~ (m1_pre_topc @ X12 @ X13)
% 0.35/0.53          | ((X14) != (u1_struct_0 @ X12))
% 0.35/0.53          | ~ (v3_pre_topc @ X14 @ X13)
% 0.35/0.53          | (v1_tsep_1 @ X12 @ X13)
% 0.35/0.53          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.35/0.53          | ~ (l1_pre_topc @ X13)
% 0.35/0.53          | ~ (v2_pre_topc @ X13))),
% 0.35/0.53      inference('cnf', [status(esa)], [t16_tsep_1])).
% 0.35/0.53  thf('19', plain,
% 0.35/0.53      (![X12 : $i, X13 : $i]:
% 0.35/0.53         (~ (v2_pre_topc @ X13)
% 0.35/0.53          | ~ (l1_pre_topc @ X13)
% 0.35/0.53          | ~ (m1_subset_1 @ (u1_struct_0 @ X12) @ 
% 0.35/0.53               (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.35/0.53          | (v1_tsep_1 @ X12 @ X13)
% 0.35/0.53          | ~ (v3_pre_topc @ (u1_struct_0 @ X12) @ X13)
% 0.35/0.53          | ~ (m1_pre_topc @ X12 @ X13))),
% 0.35/0.53      inference('simplify', [status(thm)], ['18'])).
% 0.35/0.53  thf('20', plain,
% 0.35/0.53      (![X0 : $i]:
% 0.35/0.53         (~ (m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 0.35/0.53             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.35/0.53          | ~ (m1_pre_topc @ X0 @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.35/0.53          | ~ (v3_pre_topc @ (u1_struct_0 @ X0) @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.35/0.53          | (v1_tsep_1 @ X0 @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.35/0.53          | ~ (l1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.35/0.53          | ~ (v2_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B)))),
% 0.35/0.53      inference('sup-', [status(thm)], ['17', '19'])).
% 0.35/0.53  thf('21', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf(dt_k8_tmap_1, axiom,
% 0.35/0.53    (![A:$i,B:$i]:
% 0.35/0.53     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.35/0.53         ( l1_pre_topc @ A ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.35/0.53       ( ( v1_pre_topc @ ( k8_tmap_1 @ A @ B ) ) & 
% 0.35/0.53         ( v2_pre_topc @ ( k8_tmap_1 @ A @ B ) ) & 
% 0.35/0.53         ( l1_pre_topc @ ( k8_tmap_1 @ A @ B ) ) ) ))).
% 0.35/0.53  thf('22', plain,
% 0.35/0.53      (![X5 : $i, X6 : $i]:
% 0.35/0.53         (~ (l1_pre_topc @ X5)
% 0.35/0.53          | ~ (v2_pre_topc @ X5)
% 0.35/0.53          | (v2_struct_0 @ X5)
% 0.35/0.53          | ~ (m1_pre_topc @ X6 @ X5)
% 0.35/0.53          | (l1_pre_topc @ (k8_tmap_1 @ X5 @ X6)))),
% 0.35/0.53      inference('cnf', [status(esa)], [dt_k8_tmap_1])).
% 0.35/0.53  thf('23', plain,
% 0.35/0.53      (((l1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.35/0.53        | (v2_struct_0 @ sk_A)
% 0.35/0.53        | ~ (v2_pre_topc @ sk_A)
% 0.35/0.53        | ~ (l1_pre_topc @ sk_A))),
% 0.35/0.53      inference('sup-', [status(thm)], ['21', '22'])).
% 0.35/0.53  thf('24', plain, ((v2_pre_topc @ sk_A)),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf('25', plain, ((l1_pre_topc @ sk_A)),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf('26', plain,
% 0.35/0.53      (((l1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B)) | (v2_struct_0 @ sk_A))),
% 0.35/0.53      inference('demod', [status(thm)], ['23', '24', '25'])).
% 0.35/0.53  thf('27', plain, (~ (v2_struct_0 @ sk_A)),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf('28', plain, ((l1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))),
% 0.35/0.53      inference('clc', [status(thm)], ['26', '27'])).
% 0.35/0.53  thf('29', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf('30', plain,
% 0.35/0.53      (![X5 : $i, X6 : $i]:
% 0.35/0.53         (~ (l1_pre_topc @ X5)
% 0.35/0.53          | ~ (v2_pre_topc @ X5)
% 0.35/0.53          | (v2_struct_0 @ X5)
% 0.35/0.53          | ~ (m1_pre_topc @ X6 @ X5)
% 0.35/0.53          | (v2_pre_topc @ (k8_tmap_1 @ X5 @ X6)))),
% 0.35/0.53      inference('cnf', [status(esa)], [dt_k8_tmap_1])).
% 0.35/0.53  thf('31', plain,
% 0.35/0.53      (((v2_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.35/0.53        | (v2_struct_0 @ sk_A)
% 0.35/0.53        | ~ (v2_pre_topc @ sk_A)
% 0.35/0.53        | ~ (l1_pre_topc @ sk_A))),
% 0.35/0.53      inference('sup-', [status(thm)], ['29', '30'])).
% 0.35/0.53  thf('32', plain, ((v2_pre_topc @ sk_A)),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf('33', plain, ((l1_pre_topc @ sk_A)),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf('34', plain,
% 0.35/0.53      (((v2_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B)) | (v2_struct_0 @ sk_A))),
% 0.35/0.53      inference('demod', [status(thm)], ['31', '32', '33'])).
% 0.35/0.53  thf('35', plain, (~ (v2_struct_0 @ sk_A)),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf('36', plain, ((v2_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))),
% 0.35/0.53      inference('clc', [status(thm)], ['34', '35'])).
% 0.35/0.53  thf('37', plain,
% 0.35/0.53      (![X0 : $i]:
% 0.35/0.53         (~ (m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 0.35/0.53             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.35/0.53          | ~ (m1_pre_topc @ X0 @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.35/0.53          | ~ (v3_pre_topc @ (u1_struct_0 @ X0) @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.35/0.53          | (v1_tsep_1 @ X0 @ (k8_tmap_1 @ sk_A @ sk_B)))),
% 0.35/0.53      inference('demod', [status(thm)], ['20', '28', '36'])).
% 0.35/0.53  thf('38', plain,
% 0.35/0.53      (((v1_tsep_1 @ sk_C @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.35/0.53        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_C) @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.35/0.53        | ~ (m1_pre_topc @ sk_C @ (k8_tmap_1 @ sk_A @ sk_B)))),
% 0.35/0.53      inference('sup-', [status(thm)], ['7', '37'])).
% 0.35/0.53  thf('39', plain, ((m1_pre_topc @ sk_C @ (k8_tmap_1 @ sk_A @ sk_B))),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf('40', plain,
% 0.35/0.53      (((v1_tsep_1 @ sk_C @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.35/0.53        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_C) @ (k8_tmap_1 @ sk_A @ sk_B)))),
% 0.35/0.53      inference('demod', [status(thm)], ['38', '39'])).
% 0.35/0.53  thf('41', plain,
% 0.35/0.53      ((~ (v1_tsep_1 @ sk_C @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.35/0.53        | ~ (m1_pre_topc @ sk_C @ (k8_tmap_1 @ sk_A @ sk_B)))),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf('42', plain,
% 0.35/0.53      ((~ (v1_tsep_1 @ sk_C @ (k8_tmap_1 @ sk_A @ sk_B)))
% 0.35/0.53         <= (~ ((v1_tsep_1 @ sk_C @ (k8_tmap_1 @ sk_A @ sk_B))))),
% 0.35/0.53      inference('split', [status(esa)], ['41'])).
% 0.35/0.53  thf('43', plain, ((m1_pre_topc @ sk_C @ (k8_tmap_1 @ sk_A @ sk_B))),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf('44', plain,
% 0.35/0.53      ((~ (m1_pre_topc @ sk_C @ (k8_tmap_1 @ sk_A @ sk_B)))
% 0.35/0.53         <= (~ ((m1_pre_topc @ sk_C @ (k8_tmap_1 @ sk_A @ sk_B))))),
% 0.35/0.53      inference('split', [status(esa)], ['41'])).
% 0.35/0.53  thf('45', plain, (((m1_pre_topc @ sk_C @ (k8_tmap_1 @ sk_A @ sk_B)))),
% 0.35/0.53      inference('sup-', [status(thm)], ['43', '44'])).
% 0.35/0.53  thf('46', plain,
% 0.35/0.53      (~ ((v1_tsep_1 @ sk_C @ (k8_tmap_1 @ sk_A @ sk_B))) | 
% 0.35/0.53       ~ ((m1_pre_topc @ sk_C @ (k8_tmap_1 @ sk_A @ sk_B)))),
% 0.35/0.53      inference('split', [status(esa)], ['41'])).
% 0.35/0.53  thf('47', plain, (~ ((v1_tsep_1 @ sk_C @ (k8_tmap_1 @ sk_A @ sk_B)))),
% 0.35/0.53      inference('sat_resolution*', [status(thm)], ['45', '46'])).
% 0.35/0.53  thf('48', plain, (~ (v1_tsep_1 @ sk_C @ (k8_tmap_1 @ sk_A @ sk_B))),
% 0.35/0.53      inference('simpl_trail', [status(thm)], ['42', '47'])).
% 0.35/0.53  thf('49', plain,
% 0.35/0.53      (~ (v3_pre_topc @ (u1_struct_0 @ sk_C) @ (k8_tmap_1 @ sk_A @ sk_B))),
% 0.35/0.53      inference('clc', [status(thm)], ['40', '48'])).
% 0.35/0.53  thf('50', plain, ((m1_pre_topc @ sk_C @ (k8_tmap_1 @ sk_A @ sk_B))),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf('51', plain,
% 0.35/0.53      (![X15 : $i, X16 : $i]:
% 0.35/0.53         (~ (m1_pre_topc @ X15 @ X16)
% 0.35/0.53          | (r1_tarski @ (u1_struct_0 @ X15) @ (u1_struct_0 @ X16))
% 0.35/0.53          | ~ (l1_pre_topc @ X16))),
% 0.35/0.53      inference('cnf', [status(esa)], [t35_borsuk_1])).
% 0.35/0.53  thf('52', plain,
% 0.35/0.53      ((~ (l1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.35/0.53        | (r1_tarski @ (u1_struct_0 @ sk_C) @ 
% 0.35/0.53           (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B))))),
% 0.35/0.53      inference('sup-', [status(thm)], ['50', '51'])).
% 0.35/0.53  thf('53', plain, ((l1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))),
% 0.35/0.53      inference('clc', [status(thm)], ['26', '27'])).
% 0.35/0.53  thf('54', plain,
% 0.35/0.53      ((r1_tarski @ (u1_struct_0 @ sk_C) @ 
% 0.35/0.53        (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))),
% 0.35/0.53      inference('demod', [status(thm)], ['52', '53'])).
% 0.35/0.53  thf('55', plain,
% 0.35/0.53      (![X0 : $i, X2 : $i]:
% 0.35/0.53         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X2)) | ~ (r1_tarski @ X0 @ X2))),
% 0.35/0.53      inference('cnf', [status(esa)], [t3_subset])).
% 0.35/0.53  thf('56', plain,
% 0.35/0.53      ((m1_subset_1 @ (u1_struct_0 @ sk_C) @ 
% 0.35/0.53        (k1_zfmisc_1 @ (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B))))),
% 0.35/0.53      inference('sup-', [status(thm)], ['54', '55'])).
% 0.35/0.53  thf(d5_pre_topc, axiom,
% 0.35/0.53    (![A:$i]:
% 0.35/0.53     ( ( l1_pre_topc @ A ) =>
% 0.35/0.53       ( ![B:$i]:
% 0.35/0.53         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.35/0.53           ( ( v3_pre_topc @ B @ A ) <=>
% 0.35/0.53             ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) ) ) ) ))).
% 0.35/0.53  thf('57', plain,
% 0.35/0.53      (![X3 : $i, X4 : $i]:
% 0.35/0.53         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (u1_struct_0 @ X4)))
% 0.35/0.53          | ~ (r2_hidden @ X3 @ (u1_pre_topc @ X4))
% 0.35/0.53          | (v3_pre_topc @ X3 @ X4)
% 0.35/0.53          | ~ (l1_pre_topc @ X4))),
% 0.35/0.53      inference('cnf', [status(esa)], [d5_pre_topc])).
% 0.35/0.53  thf('58', plain,
% 0.35/0.53      ((~ (l1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.35/0.53        | (v3_pre_topc @ (u1_struct_0 @ sk_C) @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.35/0.53        | ~ (r2_hidden @ (u1_struct_0 @ sk_C) @ 
% 0.35/0.53             (u1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))))),
% 0.35/0.53      inference('sup-', [status(thm)], ['56', '57'])).
% 0.35/0.53  thf('59', plain, ((l1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))),
% 0.35/0.53      inference('clc', [status(thm)], ['26', '27'])).
% 0.35/0.53  thf('60', plain,
% 0.35/0.53      (((v3_pre_topc @ (u1_struct_0 @ sk_C) @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.35/0.53        | ~ (r2_hidden @ (u1_struct_0 @ sk_C) @ 
% 0.35/0.53             (u1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))))),
% 0.35/0.53      inference('demod', [status(thm)], ['58', '59'])).
% 0.35/0.53  thf('61', plain,
% 0.35/0.53      ((m1_subset_1 @ (u1_struct_0 @ sk_C) @ 
% 0.35/0.53        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.35/0.53      inference('sup-', [status(thm)], ['5', '6'])).
% 0.35/0.53  thf('62', plain, (((u1_struct_0 @ sk_C) = (u1_struct_0 @ sk_B))),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf('63', plain,
% 0.35/0.53      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.35/0.53         ((v2_struct_0 @ X9)
% 0.35/0.53          | ~ (m1_pre_topc @ X9 @ X10)
% 0.35/0.53          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 0.35/0.53          | ((u1_pre_topc @ (k8_tmap_1 @ X10 @ X9)) = (k5_tmap_1 @ X10 @ X11))
% 0.35/0.53          | ((X11) != (u1_struct_0 @ X9))
% 0.35/0.53          | ~ (l1_pre_topc @ X10)
% 0.35/0.53          | ~ (v2_pre_topc @ X10)
% 0.35/0.53          | (v2_struct_0 @ X10))),
% 0.35/0.53      inference('cnf', [status(esa)], [t114_tmap_1])).
% 0.35/0.53  thf('64', plain,
% 0.35/0.53      (![X9 : $i, X10 : $i]:
% 0.35/0.53         ((v2_struct_0 @ X10)
% 0.35/0.53          | ~ (v2_pre_topc @ X10)
% 0.35/0.53          | ~ (l1_pre_topc @ X10)
% 0.35/0.53          | ((u1_pre_topc @ (k8_tmap_1 @ X10 @ X9))
% 0.35/0.53              = (k5_tmap_1 @ X10 @ (u1_struct_0 @ X9)))
% 0.35/0.53          | ~ (m1_subset_1 @ (u1_struct_0 @ X9) @ 
% 0.35/0.53               (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 0.35/0.53          | ~ (m1_pre_topc @ X9 @ X10)
% 0.35/0.53          | (v2_struct_0 @ X9))),
% 0.35/0.53      inference('simplify', [status(thm)], ['63'])).
% 0.35/0.53  thf('65', plain,
% 0.35/0.53      (![X0 : $i]:
% 0.35/0.53         (~ (m1_subset_1 @ (u1_struct_0 @ sk_C) @ 
% 0.35/0.53             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.35/0.53          | (v2_struct_0 @ sk_B)
% 0.35/0.53          | ~ (m1_pre_topc @ sk_B @ X0)
% 0.35/0.53          | ((u1_pre_topc @ (k8_tmap_1 @ X0 @ sk_B))
% 0.35/0.53              = (k5_tmap_1 @ X0 @ (u1_struct_0 @ sk_B)))
% 0.35/0.53          | ~ (l1_pre_topc @ X0)
% 0.35/0.53          | ~ (v2_pre_topc @ X0)
% 0.35/0.53          | (v2_struct_0 @ X0))),
% 0.35/0.53      inference('sup-', [status(thm)], ['62', '64'])).
% 0.35/0.53  thf('66', plain, (((u1_struct_0 @ sk_C) = (u1_struct_0 @ sk_B))),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf('67', plain,
% 0.35/0.53      (![X0 : $i]:
% 0.35/0.53         (~ (m1_subset_1 @ (u1_struct_0 @ sk_C) @ 
% 0.35/0.53             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.35/0.53          | (v2_struct_0 @ sk_B)
% 0.35/0.53          | ~ (m1_pre_topc @ sk_B @ X0)
% 0.35/0.53          | ((u1_pre_topc @ (k8_tmap_1 @ X0 @ sk_B))
% 0.35/0.53              = (k5_tmap_1 @ X0 @ (u1_struct_0 @ sk_C)))
% 0.35/0.53          | ~ (l1_pre_topc @ X0)
% 0.35/0.53          | ~ (v2_pre_topc @ X0)
% 0.35/0.53          | (v2_struct_0 @ X0))),
% 0.35/0.53      inference('demod', [status(thm)], ['65', '66'])).
% 0.35/0.53  thf('68', plain,
% 0.35/0.53      (((v2_struct_0 @ sk_A)
% 0.35/0.53        | ~ (v2_pre_topc @ sk_A)
% 0.35/0.53        | ~ (l1_pre_topc @ sk_A)
% 0.35/0.53        | ((u1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.35/0.53            = (k5_tmap_1 @ sk_A @ (u1_struct_0 @ sk_C)))
% 0.35/0.53        | ~ (m1_pre_topc @ sk_B @ sk_A)
% 0.35/0.53        | (v2_struct_0 @ sk_B))),
% 0.35/0.53      inference('sup-', [status(thm)], ['61', '67'])).
% 0.35/0.53  thf('69', plain, ((v2_pre_topc @ sk_A)),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf('70', plain, ((l1_pre_topc @ sk_A)),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf('71', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf('72', plain,
% 0.35/0.53      (((v2_struct_0 @ sk_A)
% 0.35/0.53        | ((u1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.35/0.53            = (k5_tmap_1 @ sk_A @ (u1_struct_0 @ sk_C)))
% 0.35/0.53        | (v2_struct_0 @ sk_B))),
% 0.35/0.53      inference('demod', [status(thm)], ['68', '69', '70', '71'])).
% 0.35/0.53  thf('73', plain, (~ (v2_struct_0 @ sk_A)),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf('74', plain,
% 0.35/0.53      (((v2_struct_0 @ sk_B)
% 0.35/0.53        | ((u1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.35/0.53            = (k5_tmap_1 @ sk_A @ (u1_struct_0 @ sk_C))))),
% 0.35/0.53      inference('clc', [status(thm)], ['72', '73'])).
% 0.35/0.53  thf('75', plain, (~ (v2_struct_0 @ sk_B)),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf('76', plain,
% 0.35/0.53      (((u1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.35/0.53         = (k5_tmap_1 @ sk_A @ (u1_struct_0 @ sk_C)))),
% 0.35/0.53      inference('clc', [status(thm)], ['74', '75'])).
% 0.35/0.53  thf('77', plain,
% 0.35/0.53      ((m1_subset_1 @ (u1_struct_0 @ sk_C) @ 
% 0.35/0.53        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.35/0.53      inference('sup-', [status(thm)], ['5', '6'])).
% 0.35/0.53  thf(t102_tmap_1, axiom,
% 0.35/0.53    (![A:$i]:
% 0.35/0.53     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.35/0.53       ( ![B:$i]:
% 0.35/0.53         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.35/0.53           ( r2_hidden @ B @ ( k5_tmap_1 @ A @ B ) ) ) ) ))).
% 0.35/0.53  thf('78', plain,
% 0.35/0.53      (![X7 : $i, X8 : $i]:
% 0.35/0.53         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 0.35/0.53          | (r2_hidden @ X7 @ (k5_tmap_1 @ X8 @ X7))
% 0.35/0.53          | ~ (l1_pre_topc @ X8)
% 0.35/0.53          | ~ (v2_pre_topc @ X8)
% 0.35/0.53          | (v2_struct_0 @ X8))),
% 0.35/0.53      inference('cnf', [status(esa)], [t102_tmap_1])).
% 0.35/0.53  thf('79', plain,
% 0.35/0.53      (((v2_struct_0 @ sk_A)
% 0.35/0.53        | ~ (v2_pre_topc @ sk_A)
% 0.35/0.53        | ~ (l1_pre_topc @ sk_A)
% 0.35/0.53        | (r2_hidden @ (u1_struct_0 @ sk_C) @ 
% 0.35/0.53           (k5_tmap_1 @ sk_A @ (u1_struct_0 @ sk_C))))),
% 0.35/0.53      inference('sup-', [status(thm)], ['77', '78'])).
% 0.35/0.53  thf('80', plain, ((v2_pre_topc @ sk_A)),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf('81', plain, ((l1_pre_topc @ sk_A)),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf('82', plain,
% 0.35/0.53      (((v2_struct_0 @ sk_A)
% 0.35/0.53        | (r2_hidden @ (u1_struct_0 @ sk_C) @ 
% 0.35/0.53           (k5_tmap_1 @ sk_A @ (u1_struct_0 @ sk_C))))),
% 0.35/0.53      inference('demod', [status(thm)], ['79', '80', '81'])).
% 0.35/0.53  thf('83', plain, (~ (v2_struct_0 @ sk_A)),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf('84', plain,
% 0.35/0.53      ((r2_hidden @ (u1_struct_0 @ sk_C) @ 
% 0.35/0.53        (k5_tmap_1 @ sk_A @ (u1_struct_0 @ sk_C)))),
% 0.35/0.53      inference('clc', [status(thm)], ['82', '83'])).
% 0.35/0.53  thf('85', plain,
% 0.35/0.53      ((v3_pre_topc @ (u1_struct_0 @ sk_C) @ (k8_tmap_1 @ sk_A @ sk_B))),
% 0.35/0.53      inference('demod', [status(thm)], ['60', '76', '84'])).
% 0.35/0.53  thf('86', plain, ($false), inference('demod', [status(thm)], ['49', '85'])).
% 0.35/0.53  
% 0.35/0.53  % SZS output end Refutation
% 0.35/0.53  
% 0.37/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
