%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Ygg6Gkq2Pm

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:10:55 EST 2020

% Result     : Theorem 0.90s
% Output     : Refutation 0.90s
% Verified   : 
% Statistics : Number of formulae       :  164 ( 652 expanded)
%              Number of leaves         :   31 ( 195 expanded)
%              Depth                    :   20
%              Number of atoms          : 1431 (9834 expanded)
%              Number of equality atoms :   74 ( 372 expanded)
%              Maximal formula depth    :   17 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k8_tmap_1_type,type,(
    k8_tmap_1: $i > $i > $i )).

thf(k5_tmap_1_type,type,(
    k5_tmap_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k6_tmap_1_type,type,(
    k6_tmap_1: $i > $i > $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(g1_pre_topc_type,type,(
    g1_pre_topc: $i > $i > $i )).

thf(v1_tsep_1_type,type,(
    v1_tsep_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(t116_tmap_1,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( m1_pre_topc @ B @ A ) )
         => ( ( ( v1_tsep_1 @ B @ A )
              & ( m1_pre_topc @ B @ A ) )
          <=> ( ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) )
              = ( k8_tmap_1 @ A @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( ~ ( v2_struct_0 @ B )
              & ( m1_pre_topc @ B @ A ) )
           => ( ( ( v1_tsep_1 @ B @ A )
                & ( m1_pre_topc @ B @ A ) )
            <=> ( ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) )
                = ( k8_tmap_1 @ A @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t116_tmap_1])).

thf('0',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d1_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( ( v1_tsep_1 @ B @ A )
          <=> ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
               => ( ( C
                    = ( u1_struct_0 @ B ) )
                 => ( v3_pre_topc @ C @ A ) ) ) ) ) ) )).

thf('1',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( m1_pre_topc @ X27 @ X28 )
      | ( ( sk_C @ X27 @ X28 )
        = ( u1_struct_0 @ X27 ) )
      | ( v1_tsep_1 @ X27 @ X28 )
      | ~ ( l1_pre_topc @ X28 ) ) ),
    inference(cnf,[status(esa)],[d1_tsep_1])).

thf('2',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v1_tsep_1 @ sk_B @ sk_A )
    | ( ( sk_C @ sk_B @ sk_A )
      = ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( v1_tsep_1 @ sk_B @ sk_A )
    | ( ( sk_C @ sk_B @ sk_A )
      = ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('5',plain,
    ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
     != ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( m1_pre_topc @ sk_B @ sk_A )
    | ~ ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ~ ( v1_tsep_1 @ sk_B @ sk_A )
   <= ~ ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['5'])).

thf('7',plain,
    ( ( ( sk_C @ sk_B @ sk_A )
      = ( u1_struct_0 @ sk_B ) )
   <= ~ ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['4','6'])).

thf('8',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( m1_pre_topc @ X27 @ X28 )
      | ~ ( v3_pre_topc @ ( sk_C @ X27 @ X28 ) @ X28 )
      | ( v1_tsep_1 @ X27 @ X28 )
      | ~ ( l1_pre_topc @ X28 ) ) ),
    inference(cnf,[status(esa)],[d1_tsep_1])).

thf('9',plain,
    ( ( ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_B ) @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v1_tsep_1 @ sk_B @ sk_A )
      | ~ ( m1_pre_topc @ sk_B @ sk_A ) )
   <= ~ ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ( ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_B ) @ sk_A )
      | ( v1_tsep_1 @ sk_B @ sk_A ) )
   <= ~ ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['9','10','11'])).

thf('13',plain,
    ( ~ ( v1_tsep_1 @ sk_B @ sk_A )
   <= ~ ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['5'])).

thf('14',plain,
    ( ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_B ) @ sk_A )
   <= ~ ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['12','13'])).

thf('15',plain,
    ( ~ ( v1_tsep_1 @ sk_B @ sk_A )
    | ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
     != ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['5'])).

thf('16',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ~ ( m1_pre_topc @ sk_B @ sk_A )
   <= ~ ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['5'])).

thf('18',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t35_borsuk_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( r1_tarski @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) )).

thf('20',plain,(
    ! [X43: $i,X44: $i] :
      ( ~ ( m1_pre_topc @ X43 @ X44 )
      | ( r1_tarski @ ( u1_struct_0 @ X43 ) @ ( u1_struct_0 @ X44 ) )
      | ~ ( l1_pre_topc @ X44 ) ) ),
    inference(cnf,[status(esa)],[t35_borsuk_1])).

thf('21',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['21','22'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('24',plain,(
    ! [X7: $i,X9: $i] :
      ( ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X9 ) )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('25',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf(d11_tmap_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ! [C: $i] :
              ( ( ( v1_pre_topc @ C )
                & ( v2_pre_topc @ C )
                & ( l1_pre_topc @ C ) )
             => ( ( C
                  = ( k8_tmap_1 @ A @ B ) )
              <=> ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                   => ( ( D
                        = ( u1_struct_0 @ B ) )
                     => ( C
                        = ( k6_tmap_1 @ A @ D ) ) ) ) ) ) ) ) )).

thf('26',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ~ ( m1_pre_topc @ X23 @ X24 )
      | ( X25
       != ( k8_tmap_1 @ X24 @ X23 ) )
      | ( X26
       != ( u1_struct_0 @ X23 ) )
      | ( X25
        = ( k6_tmap_1 @ X24 @ X26 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ~ ( l1_pre_topc @ X25 )
      | ~ ( v2_pre_topc @ X25 )
      | ~ ( v1_pre_topc @ X25 )
      | ~ ( l1_pre_topc @ X24 )
      | ~ ( v2_pre_topc @ X24 )
      | ( v2_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d11_tmap_1])).

thf('27',plain,(
    ! [X23: $i,X24: $i] :
      ( ( v2_struct_0 @ X24 )
      | ~ ( v2_pre_topc @ X24 )
      | ~ ( l1_pre_topc @ X24 )
      | ~ ( v1_pre_topc @ ( k8_tmap_1 @ X24 @ X23 ) )
      | ~ ( v2_pre_topc @ ( k8_tmap_1 @ X24 @ X23 ) )
      | ~ ( l1_pre_topc @ ( k8_tmap_1 @ X24 @ X23 ) )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X23 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ( ( k8_tmap_1 @ X24 @ X23 )
        = ( k6_tmap_1 @ X24 @ ( u1_struct_0 @ X23 ) ) )
      | ~ ( m1_pre_topc @ X23 @ X24 ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,
    ( ~ ( m1_pre_topc @ sk_B @ sk_A )
    | ( ( k8_tmap_1 @ sk_A @ sk_B )
      = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
    | ~ ( l1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( v2_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( v1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['25','27'])).

thf('29',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
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

thf('31',plain,(
    ! [X32: $i,X33: $i] :
      ( ~ ( l1_pre_topc @ X32 )
      | ~ ( v2_pre_topc @ X32 )
      | ( v2_struct_0 @ X32 )
      | ~ ( m1_pre_topc @ X33 @ X32 )
      | ( l1_pre_topc @ ( k8_tmap_1 @ X32 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k8_tmap_1])).

thf('32',plain,
    ( ( l1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( l1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['32','33','34'])).

thf('36',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    l1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['35','36'])).

thf('38',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    ! [X32: $i,X33: $i] :
      ( ~ ( l1_pre_topc @ X32 )
      | ~ ( v2_pre_topc @ X32 )
      | ( v2_struct_0 @ X32 )
      | ~ ( m1_pre_topc @ X33 @ X32 )
      | ( v2_pre_topc @ ( k8_tmap_1 @ X32 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k8_tmap_1])).

thf('40',plain,
    ( ( v2_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ( v2_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['40','41','42'])).

thf('44',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    v2_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['43','44'])).

thf('46',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,
    ( ( ( k8_tmap_1 @ sk_A @ sk_B )
      = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
    | ~ ( v1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['28','29','37','45','46','47'])).

thf('49',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    ! [X32: $i,X33: $i] :
      ( ~ ( l1_pre_topc @ X32 )
      | ~ ( v2_pre_topc @ X32 )
      | ( v2_struct_0 @ X32 )
      | ~ ( m1_pre_topc @ X33 @ X32 )
      | ( v1_pre_topc @ ( k8_tmap_1 @ X32 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k8_tmap_1])).

thf('51',plain,
    ( ( v1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,
    ( ( v1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['51','52','53'])).

thf('55',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    v1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['54','55'])).

thf('57',plain,
    ( ( ( k8_tmap_1 @ sk_A @ sk_B )
      = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['48','56'])).

thf('58',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,
    ( ( k8_tmap_1 @ sk_A @ sk_B )
    = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['57','58'])).

thf('60',plain,
    ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,
    ( ( v1_tsep_1 @ sk_B @ sk_A )
   <= ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['60'])).

thf('62',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('63',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( m1_pre_topc @ X27 @ X28 )
      | ~ ( v1_tsep_1 @ X27 @ X28 )
      | ( X29
       != ( u1_struct_0 @ X27 ) )
      | ( v3_pre_topc @ X29 @ X28 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ~ ( l1_pre_topc @ X28 ) ) ),
    inference(cnf,[status(esa)],[d1_tsep_1])).

thf('64',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( l1_pre_topc @ X28 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X27 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ( v3_pre_topc @ ( u1_struct_0 @ X27 ) @ X28 )
      | ~ ( v1_tsep_1 @ X27 @ X28 )
      | ~ ( m1_pre_topc @ X27 @ X28 ) ) ),
    inference(simplify,[status(thm)],['63'])).

thf('65',plain,
    ( ~ ( m1_pre_topc @ sk_B @ sk_A )
    | ~ ( v1_tsep_1 @ sk_B @ sk_A )
    | ( v3_pre_topc @ ( u1_struct_0 @ sk_B ) @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['62','64'])).

thf('66',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,
    ( ~ ( v1_tsep_1 @ sk_B @ sk_A )
    | ( v3_pre_topc @ ( u1_struct_0 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['65','66','67'])).

thf('69',plain,
    ( ( v3_pre_topc @ ( u1_struct_0 @ sk_B ) @ sk_A )
   <= ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['61','68'])).

thf('70',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf(d5_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v3_pre_topc @ B @ A )
          <=> ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) ) ) ) )).

thf('71',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ~ ( v3_pre_topc @ X11 @ X12 )
      | ( r2_hidden @ X11 @ ( u1_pre_topc @ X12 ) )
      | ~ ( l1_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[d5_pre_topc])).

thf('72',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r2_hidden @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_A ) )
    | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,
    ( ( r2_hidden @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_A ) )
    | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('75',plain,
    ( ( r2_hidden @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_A ) )
   <= ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['69','74'])).

thf('76',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf(t103_tmap_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( r2_hidden @ B @ ( u1_pre_topc @ A ) )
          <=> ( ( u1_pre_topc @ A )
              = ( k5_tmap_1 @ A @ B ) ) ) ) ) )).

thf('77',plain,(
    ! [X34: $i,X35: $i] :
      ( ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X35 ) ) )
      | ~ ( r2_hidden @ X34 @ ( u1_pre_topc @ X35 ) )
      | ( ( u1_pre_topc @ X35 )
        = ( k5_tmap_1 @ X35 @ X34 ) )
      | ~ ( l1_pre_topc @ X35 )
      | ~ ( v2_pre_topc @ X35 )
      | ( v2_struct_0 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t103_tmap_1])).

thf('78',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( ( u1_pre_topc @ sk_A )
      = ( k5_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
    | ~ ( r2_hidden @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( u1_pre_topc @ sk_A )
      = ( k5_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
    | ~ ( r2_hidden @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_A ) ) ),
    inference(demod,[status(thm)],['78','79','80'])).

thf('82',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,
    ( ~ ( r2_hidden @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_A ) )
    | ( ( u1_pre_topc @ sk_A )
      = ( k5_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['81','82'])).

thf('84',plain,
    ( ( ( u1_pre_topc @ sk_A )
      = ( k5_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
   <= ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['75','83'])).

thf('85',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf(d9_tmap_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k6_tmap_1 @ A @ B )
            = ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( k5_tmap_1 @ A @ B ) ) ) ) ) )).

thf('86',plain,(
    ! [X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X31 ) ) )
      | ( ( k6_tmap_1 @ X31 @ X30 )
        = ( g1_pre_topc @ ( u1_struct_0 @ X31 ) @ ( k5_tmap_1 @ X31 @ X30 ) ) )
      | ~ ( l1_pre_topc @ X31 )
      | ~ ( v2_pre_topc @ X31 )
      | ( v2_struct_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[d9_tmap_1])).

thf('87',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) )
      = ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( k5_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) )
      = ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( k5_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['87','88','89'])).

thf('91',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,
    ( ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( k5_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['90','91'])).

thf('93',plain,
    ( ( ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) )
      = ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
   <= ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['84','92'])).

thf('94',plain,
    ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
     != ( k8_tmap_1 @ sk_A @ sk_B ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
     != ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['5'])).

thf('95',plain,
    ( ( ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) )
     != ( k8_tmap_1 @ sk_A @ sk_B ) )
   <= ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
       != ( k8_tmap_1 @ sk_A @ sk_B ) )
      & ( v1_tsep_1 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,
    ( ( ( k8_tmap_1 @ sk_A @ sk_B )
     != ( k8_tmap_1 @ sk_A @ sk_B ) )
   <= ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
       != ( k8_tmap_1 @ sk_A @ sk_B ) )
      & ( v1_tsep_1 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['59','95'])).

thf('97',plain,
    ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['96'])).

thf('98',plain,(
    ~ ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['15','18','97'])).

thf('99',plain,(
    ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_B ) @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['14','98'])).

thf('100',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('101',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ~ ( r2_hidden @ X11 @ ( u1_pre_topc @ X12 ) )
      | ( v3_pre_topc @ X11 @ X12 )
      | ~ ( l1_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[d5_pre_topc])).

thf('102',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v3_pre_topc @ ( u1_struct_0 @ sk_B ) @ sk_A )
    | ~ ( r2_hidden @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,
    ( ( v3_pre_topc @ ( u1_struct_0 @ sk_B ) @ sk_A )
    | ~ ( r2_hidden @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_A ) ) ),
    inference(demod,[status(thm)],['102','103'])).

thf('105',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('106',plain,(
    ! [X34: $i,X35: $i] :
      ( ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X35 ) ) )
      | ( ( u1_pre_topc @ X35 )
       != ( k5_tmap_1 @ X35 @ X34 ) )
      | ( r2_hidden @ X34 @ ( u1_pre_topc @ X35 ) )
      | ~ ( l1_pre_topc @ X35 )
      | ~ ( v2_pre_topc @ X35 )
      | ( v2_struct_0 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t103_tmap_1])).

thf('107',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( r2_hidden @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_A ) )
    | ( ( u1_pre_topc @ sk_A )
     != ( k5_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['105','106'])).

thf('108',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_A ) )
    | ( ( u1_pre_topc @ sk_A )
     != ( k5_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['107','108','109'])).

thf('111',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,
    ( ( ( u1_pre_topc @ sk_A )
     != ( k5_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
    | ( r2_hidden @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_A ) ) ),
    inference(clc,[status(thm)],['110','111'])).

thf('113',plain,
    ( ( k8_tmap_1 @ sk_A @ sk_B )
    = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['57','58'])).

thf('114',plain,
    ( ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( k5_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['90','91'])).

thf('115',plain,
    ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k8_tmap_1 @ sk_A @ sk_B ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['60'])).

thf(dt_u1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( m1_subset_1 @ ( u1_pre_topc @ A ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('116',plain,(
    ! [X16: $i] :
      ( ( m1_subset_1 @ ( u1_pre_topc @ X16 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) ) )
      | ~ ( l1_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_pre_topc])).

thf(free_g1_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ! [C: $i,D: $i] :
          ( ( ( g1_pre_topc @ A @ B )
            = ( g1_pre_topc @ C @ D ) )
         => ( ( A = C )
            & ( B = D ) ) ) ) )).

thf('117',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ( ( g1_pre_topc @ X21 @ X22 )
       != ( g1_pre_topc @ X19 @ X20 ) )
      | ( X22 = X20 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[free_g1_pre_topc])).

thf('118',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( u1_pre_topc @ X0 )
        = X1 )
      | ( ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) )
       != ( g1_pre_topc @ X2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['116','117'])).

thf('119',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( ( k8_tmap_1 @ sk_A @ sk_B )
         != ( g1_pre_topc @ X1 @ X0 ) )
        | ( ( u1_pre_topc @ sk_A )
          = X0 )
        | ~ ( l1_pre_topc @ sk_A ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['115','118'])).

thf('120',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('121',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( ( k8_tmap_1 @ sk_A @ sk_B )
         != ( g1_pre_topc @ X1 @ X0 ) )
        | ( ( u1_pre_topc @ sk_A )
          = X0 ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['119','120'])).

thf('122',plain,
    ( ( ( ( k8_tmap_1 @ sk_A @ sk_B )
       != ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
      | ( ( u1_pre_topc @ sk_A )
        = ( k5_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['114','121'])).

thf('123',plain,
    ( ( ( ( k8_tmap_1 @ sk_A @ sk_B )
       != ( k8_tmap_1 @ sk_A @ sk_B ) )
      | ( ( u1_pre_topc @ sk_A )
        = ( k5_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['113','122'])).

thf('124',plain,
    ( ( ( u1_pre_topc @ sk_A )
      = ( k5_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['123'])).

thf('125',plain,
    ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['60'])).

thf('126',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
    = ( k8_tmap_1 @ sk_A @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['15','18','97','125'])).

thf('127',plain,
    ( ( u1_pre_topc @ sk_A )
    = ( k5_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ),
    inference(simpl_trail,[status(thm)],['124','126'])).

thf('128',plain,
    ( ( ( u1_pre_topc @ sk_A )
     != ( u1_pre_topc @ sk_A ) )
    | ( r2_hidden @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_A ) ) ),
    inference(demod,[status(thm)],['112','127'])).

thf('129',plain,(
    r2_hidden @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_A ) ),
    inference(simplify,[status(thm)],['128'])).

thf('130',plain,(
    v3_pre_topc @ ( u1_struct_0 @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['104','129'])).

thf('131',plain,(
    $false ),
    inference(demod,[status(thm)],['99','130'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Ygg6Gkq2Pm
% 0.13/0.36  % Computer   : n024.cluster.edu
% 0.13/0.36  % Model      : x86_64 x86_64
% 0.13/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.36  % Memory     : 8042.1875MB
% 0.13/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.36  % CPULimit   : 60
% 0.13/0.36  % DateTime   : Tue Dec  1 20:25:06 EST 2020
% 0.13/0.36  % CPUTime    : 
% 0.13/0.36  % Running portfolio for 600 s
% 0.13/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.36  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.90/1.10  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.90/1.10  % Solved by: fo/fo7.sh
% 0.90/1.10  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.90/1.10  % done 950 iterations in 0.626s
% 0.90/1.10  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.90/1.10  % SZS output start Refutation
% 0.90/1.10  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.90/1.10  thf(k8_tmap_1_type, type, k8_tmap_1: $i > $i > $i).
% 0.90/1.10  thf(k5_tmap_1_type, type, k5_tmap_1: $i > $i > $i).
% 0.90/1.10  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.90/1.10  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.90/1.10  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.90/1.10  thf(k6_tmap_1_type, type, k6_tmap_1: $i > $i > $i).
% 0.90/1.10  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.90/1.10  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.90/1.10  thf(sk_A_type, type, sk_A: $i).
% 0.90/1.10  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.90/1.10  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 0.90/1.10  thf(g1_pre_topc_type, type, g1_pre_topc: $i > $i > $i).
% 0.90/1.10  thf(v1_tsep_1_type, type, v1_tsep_1: $i > $i > $o).
% 0.90/1.10  thf(sk_B_type, type, sk_B: $i).
% 0.90/1.10  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.90/1.10  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.90/1.10  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.90/1.10  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 0.90/1.10  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.90/1.10  thf(t116_tmap_1, conjecture,
% 0.90/1.10    (![A:$i]:
% 0.90/1.10     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.90/1.10       ( ![B:$i]:
% 0.90/1.10         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.90/1.10           ( ( ( v1_tsep_1 @ B @ A ) & ( m1_pre_topc @ B @ A ) ) <=>
% 0.90/1.10             ( ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) =
% 0.90/1.10               ( k8_tmap_1 @ A @ B ) ) ) ) ) ))).
% 0.90/1.10  thf(zf_stmt_0, negated_conjecture,
% 0.90/1.10    (~( ![A:$i]:
% 0.90/1.10        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.90/1.10            ( l1_pre_topc @ A ) ) =>
% 0.90/1.10          ( ![B:$i]:
% 0.90/1.10            ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.90/1.10              ( ( ( v1_tsep_1 @ B @ A ) & ( m1_pre_topc @ B @ A ) ) <=>
% 0.90/1.10                ( ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) =
% 0.90/1.10                  ( k8_tmap_1 @ A @ B ) ) ) ) ) ) )),
% 0.90/1.10    inference('cnf.neg', [status(esa)], [t116_tmap_1])).
% 0.90/1.10  thf('0', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.90/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.10  thf(d1_tsep_1, axiom,
% 0.90/1.10    (![A:$i]:
% 0.90/1.10     ( ( l1_pre_topc @ A ) =>
% 0.90/1.10       ( ![B:$i]:
% 0.90/1.10         ( ( m1_pre_topc @ B @ A ) =>
% 0.90/1.10           ( ( v1_tsep_1 @ B @ A ) <=>
% 0.90/1.10             ( ![C:$i]:
% 0.90/1.10               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.90/1.10                 ( ( ( C ) = ( u1_struct_0 @ B ) ) => ( v3_pre_topc @ C @ A ) ) ) ) ) ) ) ))).
% 0.90/1.10  thf('1', plain,
% 0.90/1.10      (![X27 : $i, X28 : $i]:
% 0.90/1.10         (~ (m1_pre_topc @ X27 @ X28)
% 0.90/1.10          | ((sk_C @ X27 @ X28) = (u1_struct_0 @ X27))
% 0.90/1.10          | (v1_tsep_1 @ X27 @ X28)
% 0.90/1.10          | ~ (l1_pre_topc @ X28))),
% 0.90/1.10      inference('cnf', [status(esa)], [d1_tsep_1])).
% 0.90/1.10  thf('2', plain,
% 0.90/1.10      ((~ (l1_pre_topc @ sk_A)
% 0.90/1.10        | (v1_tsep_1 @ sk_B @ sk_A)
% 0.90/1.10        | ((sk_C @ sk_B @ sk_A) = (u1_struct_0 @ sk_B)))),
% 0.90/1.10      inference('sup-', [status(thm)], ['0', '1'])).
% 0.90/1.10  thf('3', plain, ((l1_pre_topc @ sk_A)),
% 0.90/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.10  thf('4', plain,
% 0.90/1.10      (((v1_tsep_1 @ sk_B @ sk_A)
% 0.90/1.10        | ((sk_C @ sk_B @ sk_A) = (u1_struct_0 @ sk_B)))),
% 0.90/1.10      inference('demod', [status(thm)], ['2', '3'])).
% 0.90/1.10  thf('5', plain,
% 0.90/1.10      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.90/1.10          != (k8_tmap_1 @ sk_A @ sk_B))
% 0.90/1.10        | ~ (m1_pre_topc @ sk_B @ sk_A)
% 0.90/1.10        | ~ (v1_tsep_1 @ sk_B @ sk_A))),
% 0.90/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.10  thf('6', plain,
% 0.90/1.10      ((~ (v1_tsep_1 @ sk_B @ sk_A)) <= (~ ((v1_tsep_1 @ sk_B @ sk_A)))),
% 0.90/1.10      inference('split', [status(esa)], ['5'])).
% 0.90/1.10  thf('7', plain,
% 0.90/1.10      ((((sk_C @ sk_B @ sk_A) = (u1_struct_0 @ sk_B)))
% 0.90/1.10         <= (~ ((v1_tsep_1 @ sk_B @ sk_A)))),
% 0.90/1.10      inference('sup-', [status(thm)], ['4', '6'])).
% 0.90/1.10  thf('8', plain,
% 0.90/1.10      (![X27 : $i, X28 : $i]:
% 0.90/1.10         (~ (m1_pre_topc @ X27 @ X28)
% 0.90/1.10          | ~ (v3_pre_topc @ (sk_C @ X27 @ X28) @ X28)
% 0.90/1.10          | (v1_tsep_1 @ X27 @ X28)
% 0.90/1.10          | ~ (l1_pre_topc @ X28))),
% 0.90/1.10      inference('cnf', [status(esa)], [d1_tsep_1])).
% 0.90/1.10  thf('9', plain,
% 0.90/1.10      (((~ (v3_pre_topc @ (u1_struct_0 @ sk_B) @ sk_A)
% 0.90/1.10         | ~ (l1_pre_topc @ sk_A)
% 0.90/1.10         | (v1_tsep_1 @ sk_B @ sk_A)
% 0.90/1.10         | ~ (m1_pre_topc @ sk_B @ sk_A))) <= (~ ((v1_tsep_1 @ sk_B @ sk_A)))),
% 0.90/1.10      inference('sup-', [status(thm)], ['7', '8'])).
% 0.90/1.10  thf('10', plain, ((l1_pre_topc @ sk_A)),
% 0.90/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.10  thf('11', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.90/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.10  thf('12', plain,
% 0.90/1.10      (((~ (v3_pre_topc @ (u1_struct_0 @ sk_B) @ sk_A)
% 0.90/1.10         | (v1_tsep_1 @ sk_B @ sk_A))) <= (~ ((v1_tsep_1 @ sk_B @ sk_A)))),
% 0.90/1.10      inference('demod', [status(thm)], ['9', '10', '11'])).
% 0.90/1.10  thf('13', plain,
% 0.90/1.10      ((~ (v1_tsep_1 @ sk_B @ sk_A)) <= (~ ((v1_tsep_1 @ sk_B @ sk_A)))),
% 0.90/1.10      inference('split', [status(esa)], ['5'])).
% 0.90/1.10  thf('14', plain,
% 0.90/1.10      ((~ (v3_pre_topc @ (u1_struct_0 @ sk_B) @ sk_A))
% 0.90/1.10         <= (~ ((v1_tsep_1 @ sk_B @ sk_A)))),
% 0.90/1.10      inference('clc', [status(thm)], ['12', '13'])).
% 0.90/1.10  thf('15', plain,
% 0.90/1.10      (~ ((v1_tsep_1 @ sk_B @ sk_A)) | 
% 0.90/1.10       ~
% 0.90/1.10       (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.90/1.10          = (k8_tmap_1 @ sk_A @ sk_B))) | 
% 0.90/1.10       ~ ((m1_pre_topc @ sk_B @ sk_A))),
% 0.90/1.10      inference('split', [status(esa)], ['5'])).
% 0.90/1.10  thf('16', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.90/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.10  thf('17', plain,
% 0.90/1.10      ((~ (m1_pre_topc @ sk_B @ sk_A)) <= (~ ((m1_pre_topc @ sk_B @ sk_A)))),
% 0.90/1.10      inference('split', [status(esa)], ['5'])).
% 0.90/1.10  thf('18', plain, (((m1_pre_topc @ sk_B @ sk_A))),
% 0.90/1.10      inference('sup-', [status(thm)], ['16', '17'])).
% 0.90/1.10  thf('19', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.90/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.10  thf(t35_borsuk_1, axiom,
% 0.90/1.10    (![A:$i]:
% 0.90/1.10     ( ( l1_pre_topc @ A ) =>
% 0.90/1.10       ( ![B:$i]:
% 0.90/1.10         ( ( m1_pre_topc @ B @ A ) =>
% 0.90/1.10           ( r1_tarski @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ))).
% 0.90/1.10  thf('20', plain,
% 0.90/1.10      (![X43 : $i, X44 : $i]:
% 0.90/1.10         (~ (m1_pre_topc @ X43 @ X44)
% 0.90/1.10          | (r1_tarski @ (u1_struct_0 @ X43) @ (u1_struct_0 @ X44))
% 0.90/1.10          | ~ (l1_pre_topc @ X44))),
% 0.90/1.10      inference('cnf', [status(esa)], [t35_borsuk_1])).
% 0.90/1.10  thf('21', plain,
% 0.90/1.10      ((~ (l1_pre_topc @ sk_A)
% 0.90/1.10        | (r1_tarski @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 0.90/1.10      inference('sup-', [status(thm)], ['19', '20'])).
% 0.90/1.10  thf('22', plain, ((l1_pre_topc @ sk_A)),
% 0.90/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.10  thf('23', plain, ((r1_tarski @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.90/1.10      inference('demod', [status(thm)], ['21', '22'])).
% 0.90/1.10  thf(t3_subset, axiom,
% 0.90/1.10    (![A:$i,B:$i]:
% 0.90/1.10     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.90/1.10  thf('24', plain,
% 0.90/1.10      (![X7 : $i, X9 : $i]:
% 0.90/1.10         ((m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X9)) | ~ (r1_tarski @ X7 @ X9))),
% 0.90/1.10      inference('cnf', [status(esa)], [t3_subset])).
% 0.90/1.10  thf('25', plain,
% 0.90/1.10      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.90/1.10        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.90/1.10      inference('sup-', [status(thm)], ['23', '24'])).
% 0.90/1.10  thf(d11_tmap_1, axiom,
% 0.90/1.10    (![A:$i]:
% 0.90/1.10     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.90/1.10       ( ![B:$i]:
% 0.90/1.10         ( ( m1_pre_topc @ B @ A ) =>
% 0.90/1.10           ( ![C:$i]:
% 0.90/1.10             ( ( ( v1_pre_topc @ C ) & ( v2_pre_topc @ C ) & 
% 0.90/1.10                 ( l1_pre_topc @ C ) ) =>
% 0.90/1.10               ( ( ( C ) = ( k8_tmap_1 @ A @ B ) ) <=>
% 0.90/1.10                 ( ![D:$i]:
% 0.90/1.10                   ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.90/1.10                     ( ( ( D ) = ( u1_struct_0 @ B ) ) =>
% 0.90/1.10                       ( ( C ) = ( k6_tmap_1 @ A @ D ) ) ) ) ) ) ) ) ) ) ))).
% 0.90/1.10  thf('26', plain,
% 0.90/1.10      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 0.90/1.10         (~ (m1_pre_topc @ X23 @ X24)
% 0.90/1.10          | ((X25) != (k8_tmap_1 @ X24 @ X23))
% 0.90/1.10          | ((X26) != (u1_struct_0 @ X23))
% 0.90/1.10          | ((X25) = (k6_tmap_1 @ X24 @ X26))
% 0.90/1.10          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 0.90/1.10          | ~ (l1_pre_topc @ X25)
% 0.90/1.10          | ~ (v2_pre_topc @ X25)
% 0.90/1.10          | ~ (v1_pre_topc @ X25)
% 0.90/1.10          | ~ (l1_pre_topc @ X24)
% 0.90/1.10          | ~ (v2_pre_topc @ X24)
% 0.90/1.10          | (v2_struct_0 @ X24))),
% 0.90/1.10      inference('cnf', [status(esa)], [d11_tmap_1])).
% 0.90/1.10  thf('27', plain,
% 0.90/1.10      (![X23 : $i, X24 : $i]:
% 0.90/1.10         ((v2_struct_0 @ X24)
% 0.90/1.10          | ~ (v2_pre_topc @ X24)
% 0.90/1.10          | ~ (l1_pre_topc @ X24)
% 0.90/1.10          | ~ (v1_pre_topc @ (k8_tmap_1 @ X24 @ X23))
% 0.90/1.10          | ~ (v2_pre_topc @ (k8_tmap_1 @ X24 @ X23))
% 0.90/1.10          | ~ (l1_pre_topc @ (k8_tmap_1 @ X24 @ X23))
% 0.90/1.10          | ~ (m1_subset_1 @ (u1_struct_0 @ X23) @ 
% 0.90/1.10               (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 0.90/1.10          | ((k8_tmap_1 @ X24 @ X23) = (k6_tmap_1 @ X24 @ (u1_struct_0 @ X23)))
% 0.90/1.10          | ~ (m1_pre_topc @ X23 @ X24))),
% 0.90/1.10      inference('simplify', [status(thm)], ['26'])).
% 0.90/1.10  thf('28', plain,
% 0.90/1.10      ((~ (m1_pre_topc @ sk_B @ sk_A)
% 0.90/1.10        | ((k8_tmap_1 @ sk_A @ sk_B)
% 0.90/1.10            = (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 0.90/1.10        | ~ (l1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.90/1.10        | ~ (v2_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.90/1.10        | ~ (v1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.90/1.10        | ~ (l1_pre_topc @ sk_A)
% 0.90/1.10        | ~ (v2_pre_topc @ sk_A)
% 0.90/1.10        | (v2_struct_0 @ sk_A))),
% 0.90/1.10      inference('sup-', [status(thm)], ['25', '27'])).
% 0.90/1.10  thf('29', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.90/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.10  thf('30', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.90/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.10  thf(dt_k8_tmap_1, axiom,
% 0.90/1.10    (![A:$i,B:$i]:
% 0.90/1.10     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.90/1.10         ( l1_pre_topc @ A ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.90/1.10       ( ( v1_pre_topc @ ( k8_tmap_1 @ A @ B ) ) & 
% 0.90/1.10         ( v2_pre_topc @ ( k8_tmap_1 @ A @ B ) ) & 
% 0.90/1.10         ( l1_pre_topc @ ( k8_tmap_1 @ A @ B ) ) ) ))).
% 0.90/1.10  thf('31', plain,
% 0.90/1.10      (![X32 : $i, X33 : $i]:
% 0.90/1.10         (~ (l1_pre_topc @ X32)
% 0.90/1.10          | ~ (v2_pre_topc @ X32)
% 0.90/1.10          | (v2_struct_0 @ X32)
% 0.90/1.10          | ~ (m1_pre_topc @ X33 @ X32)
% 0.90/1.10          | (l1_pre_topc @ (k8_tmap_1 @ X32 @ X33)))),
% 0.90/1.10      inference('cnf', [status(esa)], [dt_k8_tmap_1])).
% 0.90/1.10  thf('32', plain,
% 0.90/1.10      (((l1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.90/1.10        | (v2_struct_0 @ sk_A)
% 0.90/1.10        | ~ (v2_pre_topc @ sk_A)
% 0.90/1.10        | ~ (l1_pre_topc @ sk_A))),
% 0.90/1.10      inference('sup-', [status(thm)], ['30', '31'])).
% 0.90/1.10  thf('33', plain, ((v2_pre_topc @ sk_A)),
% 0.90/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.10  thf('34', plain, ((l1_pre_topc @ sk_A)),
% 0.90/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.10  thf('35', plain,
% 0.90/1.10      (((l1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B)) | (v2_struct_0 @ sk_A))),
% 0.90/1.10      inference('demod', [status(thm)], ['32', '33', '34'])).
% 0.90/1.10  thf('36', plain, (~ (v2_struct_0 @ sk_A)),
% 0.90/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.10  thf('37', plain, ((l1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))),
% 0.90/1.10      inference('clc', [status(thm)], ['35', '36'])).
% 0.90/1.10  thf('38', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.90/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.10  thf('39', plain,
% 0.90/1.10      (![X32 : $i, X33 : $i]:
% 0.90/1.10         (~ (l1_pre_topc @ X32)
% 0.90/1.10          | ~ (v2_pre_topc @ X32)
% 0.90/1.10          | (v2_struct_0 @ X32)
% 0.90/1.10          | ~ (m1_pre_topc @ X33 @ X32)
% 0.90/1.10          | (v2_pre_topc @ (k8_tmap_1 @ X32 @ X33)))),
% 0.90/1.10      inference('cnf', [status(esa)], [dt_k8_tmap_1])).
% 0.90/1.10  thf('40', plain,
% 0.90/1.10      (((v2_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.90/1.10        | (v2_struct_0 @ sk_A)
% 0.90/1.10        | ~ (v2_pre_topc @ sk_A)
% 0.90/1.10        | ~ (l1_pre_topc @ sk_A))),
% 0.90/1.10      inference('sup-', [status(thm)], ['38', '39'])).
% 0.90/1.10  thf('41', plain, ((v2_pre_topc @ sk_A)),
% 0.90/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.10  thf('42', plain, ((l1_pre_topc @ sk_A)),
% 0.90/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.10  thf('43', plain,
% 0.90/1.10      (((v2_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B)) | (v2_struct_0 @ sk_A))),
% 0.90/1.10      inference('demod', [status(thm)], ['40', '41', '42'])).
% 0.90/1.10  thf('44', plain, (~ (v2_struct_0 @ sk_A)),
% 0.90/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.10  thf('45', plain, ((v2_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))),
% 0.90/1.10      inference('clc', [status(thm)], ['43', '44'])).
% 0.90/1.10  thf('46', plain, ((l1_pre_topc @ sk_A)),
% 0.90/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.10  thf('47', plain, ((v2_pre_topc @ sk_A)),
% 0.90/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.10  thf('48', plain,
% 0.90/1.10      ((((k8_tmap_1 @ sk_A @ sk_B) = (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 0.90/1.10        | ~ (v1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.90/1.10        | (v2_struct_0 @ sk_A))),
% 0.90/1.10      inference('demod', [status(thm)], ['28', '29', '37', '45', '46', '47'])).
% 0.90/1.10  thf('49', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.90/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.10  thf('50', plain,
% 0.90/1.10      (![X32 : $i, X33 : $i]:
% 0.90/1.10         (~ (l1_pre_topc @ X32)
% 0.90/1.10          | ~ (v2_pre_topc @ X32)
% 0.90/1.10          | (v2_struct_0 @ X32)
% 0.90/1.10          | ~ (m1_pre_topc @ X33 @ X32)
% 0.90/1.10          | (v1_pre_topc @ (k8_tmap_1 @ X32 @ X33)))),
% 0.90/1.10      inference('cnf', [status(esa)], [dt_k8_tmap_1])).
% 0.90/1.10  thf('51', plain,
% 0.90/1.10      (((v1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.90/1.10        | (v2_struct_0 @ sk_A)
% 0.90/1.10        | ~ (v2_pre_topc @ sk_A)
% 0.90/1.10        | ~ (l1_pre_topc @ sk_A))),
% 0.90/1.10      inference('sup-', [status(thm)], ['49', '50'])).
% 0.90/1.10  thf('52', plain, ((v2_pre_topc @ sk_A)),
% 0.90/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.10  thf('53', plain, ((l1_pre_topc @ sk_A)),
% 0.90/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.10  thf('54', plain,
% 0.90/1.10      (((v1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B)) | (v2_struct_0 @ sk_A))),
% 0.90/1.10      inference('demod', [status(thm)], ['51', '52', '53'])).
% 0.90/1.10  thf('55', plain, (~ (v2_struct_0 @ sk_A)),
% 0.90/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.10  thf('56', plain, ((v1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))),
% 0.90/1.10      inference('clc', [status(thm)], ['54', '55'])).
% 0.90/1.10  thf('57', plain,
% 0.90/1.10      ((((k8_tmap_1 @ sk_A @ sk_B) = (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 0.90/1.10        | (v2_struct_0 @ sk_A))),
% 0.90/1.10      inference('demod', [status(thm)], ['48', '56'])).
% 0.90/1.10  thf('58', plain, (~ (v2_struct_0 @ sk_A)),
% 0.90/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.10  thf('59', plain,
% 0.90/1.10      (((k8_tmap_1 @ sk_A @ sk_B) = (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))),
% 0.90/1.10      inference('clc', [status(thm)], ['57', '58'])).
% 0.90/1.10  thf('60', plain,
% 0.90/1.10      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.90/1.10          = (k8_tmap_1 @ sk_A @ sk_B))
% 0.90/1.10        | (v1_tsep_1 @ sk_B @ sk_A))),
% 0.90/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.10  thf('61', plain,
% 0.90/1.10      (((v1_tsep_1 @ sk_B @ sk_A)) <= (((v1_tsep_1 @ sk_B @ sk_A)))),
% 0.90/1.10      inference('split', [status(esa)], ['60'])).
% 0.90/1.10  thf('62', plain,
% 0.90/1.10      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.90/1.10        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.90/1.10      inference('sup-', [status(thm)], ['23', '24'])).
% 0.90/1.10  thf('63', plain,
% 0.90/1.10      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.90/1.10         (~ (m1_pre_topc @ X27 @ X28)
% 0.90/1.10          | ~ (v1_tsep_1 @ X27 @ X28)
% 0.90/1.10          | ((X29) != (u1_struct_0 @ X27))
% 0.90/1.10          | (v3_pre_topc @ X29 @ X28)
% 0.90/1.10          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 0.90/1.10          | ~ (l1_pre_topc @ X28))),
% 0.90/1.10      inference('cnf', [status(esa)], [d1_tsep_1])).
% 0.90/1.10  thf('64', plain,
% 0.90/1.10      (![X27 : $i, X28 : $i]:
% 0.90/1.10         (~ (l1_pre_topc @ X28)
% 0.90/1.10          | ~ (m1_subset_1 @ (u1_struct_0 @ X27) @ 
% 0.90/1.10               (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 0.90/1.10          | (v3_pre_topc @ (u1_struct_0 @ X27) @ X28)
% 0.90/1.10          | ~ (v1_tsep_1 @ X27 @ X28)
% 0.90/1.10          | ~ (m1_pre_topc @ X27 @ X28))),
% 0.90/1.10      inference('simplify', [status(thm)], ['63'])).
% 0.90/1.10  thf('65', plain,
% 0.90/1.10      ((~ (m1_pre_topc @ sk_B @ sk_A)
% 0.90/1.10        | ~ (v1_tsep_1 @ sk_B @ sk_A)
% 0.90/1.10        | (v3_pre_topc @ (u1_struct_0 @ sk_B) @ sk_A)
% 0.90/1.10        | ~ (l1_pre_topc @ sk_A))),
% 0.90/1.10      inference('sup-', [status(thm)], ['62', '64'])).
% 0.90/1.10  thf('66', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.90/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.10  thf('67', plain, ((l1_pre_topc @ sk_A)),
% 0.90/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.10  thf('68', plain,
% 0.90/1.10      ((~ (v1_tsep_1 @ sk_B @ sk_A)
% 0.90/1.10        | (v3_pre_topc @ (u1_struct_0 @ sk_B) @ sk_A))),
% 0.90/1.10      inference('demod', [status(thm)], ['65', '66', '67'])).
% 0.90/1.10  thf('69', plain,
% 0.90/1.10      (((v3_pre_topc @ (u1_struct_0 @ sk_B) @ sk_A))
% 0.90/1.10         <= (((v1_tsep_1 @ sk_B @ sk_A)))),
% 0.90/1.10      inference('sup-', [status(thm)], ['61', '68'])).
% 0.90/1.10  thf('70', plain,
% 0.90/1.10      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.90/1.10        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.90/1.10      inference('sup-', [status(thm)], ['23', '24'])).
% 0.90/1.10  thf(d5_pre_topc, axiom,
% 0.90/1.10    (![A:$i]:
% 0.90/1.10     ( ( l1_pre_topc @ A ) =>
% 0.90/1.10       ( ![B:$i]:
% 0.90/1.10         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.90/1.10           ( ( v3_pre_topc @ B @ A ) <=>
% 0.90/1.10             ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) ) ) ) ))).
% 0.90/1.10  thf('71', plain,
% 0.90/1.10      (![X11 : $i, X12 : $i]:
% 0.90/1.10         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.90/1.10          | ~ (v3_pre_topc @ X11 @ X12)
% 0.90/1.10          | (r2_hidden @ X11 @ (u1_pre_topc @ X12))
% 0.90/1.10          | ~ (l1_pre_topc @ X12))),
% 0.90/1.10      inference('cnf', [status(esa)], [d5_pre_topc])).
% 0.90/1.10  thf('72', plain,
% 0.90/1.10      ((~ (l1_pre_topc @ sk_A)
% 0.90/1.10        | (r2_hidden @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_A))
% 0.90/1.10        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_B) @ sk_A))),
% 0.90/1.10      inference('sup-', [status(thm)], ['70', '71'])).
% 0.90/1.10  thf('73', plain, ((l1_pre_topc @ sk_A)),
% 0.90/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.10  thf('74', plain,
% 0.90/1.10      (((r2_hidden @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_A))
% 0.90/1.10        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_B) @ sk_A))),
% 0.90/1.10      inference('demod', [status(thm)], ['72', '73'])).
% 0.90/1.10  thf('75', plain,
% 0.90/1.10      (((r2_hidden @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_A)))
% 0.90/1.10         <= (((v1_tsep_1 @ sk_B @ sk_A)))),
% 0.90/1.10      inference('sup-', [status(thm)], ['69', '74'])).
% 0.90/1.10  thf('76', plain,
% 0.90/1.10      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.90/1.10        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.90/1.10      inference('sup-', [status(thm)], ['23', '24'])).
% 0.90/1.10  thf(t103_tmap_1, axiom,
% 0.90/1.10    (![A:$i]:
% 0.90/1.10     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.90/1.10       ( ![B:$i]:
% 0.90/1.10         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.90/1.10           ( ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) <=>
% 0.90/1.10             ( ( u1_pre_topc @ A ) = ( k5_tmap_1 @ A @ B ) ) ) ) ) ))).
% 0.90/1.10  thf('77', plain,
% 0.90/1.10      (![X34 : $i, X35 : $i]:
% 0.90/1.10         (~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (u1_struct_0 @ X35)))
% 0.90/1.10          | ~ (r2_hidden @ X34 @ (u1_pre_topc @ X35))
% 0.90/1.10          | ((u1_pre_topc @ X35) = (k5_tmap_1 @ X35 @ X34))
% 0.90/1.10          | ~ (l1_pre_topc @ X35)
% 0.90/1.10          | ~ (v2_pre_topc @ X35)
% 0.90/1.10          | (v2_struct_0 @ X35))),
% 0.90/1.10      inference('cnf', [status(esa)], [t103_tmap_1])).
% 0.90/1.10  thf('78', plain,
% 0.90/1.10      (((v2_struct_0 @ sk_A)
% 0.90/1.10        | ~ (v2_pre_topc @ sk_A)
% 0.90/1.10        | ~ (l1_pre_topc @ sk_A)
% 0.90/1.10        | ((u1_pre_topc @ sk_A) = (k5_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 0.90/1.10        | ~ (r2_hidden @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_A)))),
% 0.90/1.10      inference('sup-', [status(thm)], ['76', '77'])).
% 0.90/1.10  thf('79', plain, ((v2_pre_topc @ sk_A)),
% 0.90/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.10  thf('80', plain, ((l1_pre_topc @ sk_A)),
% 0.90/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.10  thf('81', plain,
% 0.90/1.10      (((v2_struct_0 @ sk_A)
% 0.90/1.10        | ((u1_pre_topc @ sk_A) = (k5_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 0.90/1.10        | ~ (r2_hidden @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_A)))),
% 0.90/1.10      inference('demod', [status(thm)], ['78', '79', '80'])).
% 0.90/1.10  thf('82', plain, (~ (v2_struct_0 @ sk_A)),
% 0.90/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.10  thf('83', plain,
% 0.90/1.10      ((~ (r2_hidden @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_A))
% 0.90/1.10        | ((u1_pre_topc @ sk_A) = (k5_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B))))),
% 0.90/1.10      inference('clc', [status(thm)], ['81', '82'])).
% 0.90/1.10  thf('84', plain,
% 0.90/1.10      ((((u1_pre_topc @ sk_A) = (k5_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B))))
% 0.90/1.10         <= (((v1_tsep_1 @ sk_B @ sk_A)))),
% 0.90/1.10      inference('sup-', [status(thm)], ['75', '83'])).
% 0.90/1.10  thf('85', plain,
% 0.90/1.10      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.90/1.10        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.90/1.10      inference('sup-', [status(thm)], ['23', '24'])).
% 0.90/1.10  thf(d9_tmap_1, axiom,
% 0.90/1.10    (![A:$i]:
% 0.90/1.10     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.90/1.10       ( ![B:$i]:
% 0.90/1.10         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.90/1.10           ( ( k6_tmap_1 @ A @ B ) =
% 0.90/1.10             ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( k5_tmap_1 @ A @ B ) ) ) ) ) ))).
% 0.90/1.10  thf('86', plain,
% 0.90/1.10      (![X30 : $i, X31 : $i]:
% 0.90/1.10         (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ X31)))
% 0.90/1.10          | ((k6_tmap_1 @ X31 @ X30)
% 0.90/1.10              = (g1_pre_topc @ (u1_struct_0 @ X31) @ (k5_tmap_1 @ X31 @ X30)))
% 0.90/1.10          | ~ (l1_pre_topc @ X31)
% 0.90/1.10          | ~ (v2_pre_topc @ X31)
% 0.90/1.10          | (v2_struct_0 @ X31))),
% 0.90/1.10      inference('cnf', [status(esa)], [d9_tmap_1])).
% 0.90/1.10  thf('87', plain,
% 0.90/1.10      (((v2_struct_0 @ sk_A)
% 0.90/1.10        | ~ (v2_pre_topc @ sk_A)
% 0.90/1.10        | ~ (l1_pre_topc @ sk_A)
% 0.90/1.10        | ((k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B))
% 0.90/1.10            = (g1_pre_topc @ (u1_struct_0 @ sk_A) @ 
% 0.90/1.10               (k5_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))))),
% 0.90/1.10      inference('sup-', [status(thm)], ['85', '86'])).
% 0.90/1.10  thf('88', plain, ((v2_pre_topc @ sk_A)),
% 0.90/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.10  thf('89', plain, ((l1_pre_topc @ sk_A)),
% 0.90/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.10  thf('90', plain,
% 0.90/1.10      (((v2_struct_0 @ sk_A)
% 0.90/1.10        | ((k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B))
% 0.90/1.10            = (g1_pre_topc @ (u1_struct_0 @ sk_A) @ 
% 0.90/1.10               (k5_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))))),
% 0.90/1.10      inference('demod', [status(thm)], ['87', '88', '89'])).
% 0.90/1.10  thf('91', plain, (~ (v2_struct_0 @ sk_A)),
% 0.90/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.10  thf('92', plain,
% 0.90/1.10      (((k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B))
% 0.90/1.10         = (g1_pre_topc @ (u1_struct_0 @ sk_A) @ 
% 0.90/1.10            (k5_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B))))),
% 0.90/1.10      inference('clc', [status(thm)], ['90', '91'])).
% 0.90/1.10  thf('93', plain,
% 0.90/1.10      ((((k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B))
% 0.90/1.10          = (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))
% 0.90/1.10         <= (((v1_tsep_1 @ sk_B @ sk_A)))),
% 0.90/1.10      inference('sup+', [status(thm)], ['84', '92'])).
% 0.90/1.10  thf('94', plain,
% 0.90/1.10      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.90/1.10          != (k8_tmap_1 @ sk_A @ sk_B)))
% 0.90/1.10         <= (~
% 0.90/1.10             (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.90/1.10                = (k8_tmap_1 @ sk_A @ sk_B))))),
% 0.90/1.10      inference('split', [status(esa)], ['5'])).
% 0.90/1.10  thf('95', plain,
% 0.90/1.10      ((((k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)) != (k8_tmap_1 @ sk_A @ sk_B)))
% 0.90/1.10         <= (~
% 0.90/1.10             (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.90/1.10                = (k8_tmap_1 @ sk_A @ sk_B))) & 
% 0.90/1.10             ((v1_tsep_1 @ sk_B @ sk_A)))),
% 0.90/1.10      inference('sup-', [status(thm)], ['93', '94'])).
% 0.90/1.10  thf('96', plain,
% 0.90/1.10      ((((k8_tmap_1 @ sk_A @ sk_B) != (k8_tmap_1 @ sk_A @ sk_B)))
% 0.90/1.10         <= (~
% 0.90/1.10             (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.90/1.10                = (k8_tmap_1 @ sk_A @ sk_B))) & 
% 0.90/1.10             ((v1_tsep_1 @ sk_B @ sk_A)))),
% 0.90/1.10      inference('sup-', [status(thm)], ['59', '95'])).
% 0.90/1.10  thf('97', plain,
% 0.90/1.10      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.90/1.10          = (k8_tmap_1 @ sk_A @ sk_B))) | 
% 0.90/1.10       ~ ((v1_tsep_1 @ sk_B @ sk_A))),
% 0.90/1.10      inference('simplify', [status(thm)], ['96'])).
% 0.90/1.10  thf('98', plain, (~ ((v1_tsep_1 @ sk_B @ sk_A))),
% 0.90/1.10      inference('sat_resolution*', [status(thm)], ['15', '18', '97'])).
% 0.90/1.10  thf('99', plain, (~ (v3_pre_topc @ (u1_struct_0 @ sk_B) @ sk_A)),
% 0.90/1.10      inference('simpl_trail', [status(thm)], ['14', '98'])).
% 0.90/1.10  thf('100', plain,
% 0.90/1.10      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.90/1.10        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.90/1.10      inference('sup-', [status(thm)], ['23', '24'])).
% 0.90/1.10  thf('101', plain,
% 0.90/1.10      (![X11 : $i, X12 : $i]:
% 0.90/1.10         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.90/1.10          | ~ (r2_hidden @ X11 @ (u1_pre_topc @ X12))
% 0.90/1.10          | (v3_pre_topc @ X11 @ X12)
% 0.90/1.10          | ~ (l1_pre_topc @ X12))),
% 0.90/1.10      inference('cnf', [status(esa)], [d5_pre_topc])).
% 0.90/1.10  thf('102', plain,
% 0.90/1.10      ((~ (l1_pre_topc @ sk_A)
% 0.90/1.10        | (v3_pre_topc @ (u1_struct_0 @ sk_B) @ sk_A)
% 0.90/1.10        | ~ (r2_hidden @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_A)))),
% 0.90/1.10      inference('sup-', [status(thm)], ['100', '101'])).
% 0.90/1.10  thf('103', plain, ((l1_pre_topc @ sk_A)),
% 0.90/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.10  thf('104', plain,
% 0.90/1.10      (((v3_pre_topc @ (u1_struct_0 @ sk_B) @ sk_A)
% 0.90/1.10        | ~ (r2_hidden @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_A)))),
% 0.90/1.10      inference('demod', [status(thm)], ['102', '103'])).
% 0.90/1.10  thf('105', plain,
% 0.90/1.10      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.90/1.10        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.90/1.10      inference('sup-', [status(thm)], ['23', '24'])).
% 0.90/1.10  thf('106', plain,
% 0.90/1.10      (![X34 : $i, X35 : $i]:
% 0.90/1.10         (~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (u1_struct_0 @ X35)))
% 0.90/1.10          | ((u1_pre_topc @ X35) != (k5_tmap_1 @ X35 @ X34))
% 0.90/1.10          | (r2_hidden @ X34 @ (u1_pre_topc @ X35))
% 0.90/1.10          | ~ (l1_pre_topc @ X35)
% 0.90/1.10          | ~ (v2_pre_topc @ X35)
% 0.90/1.10          | (v2_struct_0 @ X35))),
% 0.90/1.10      inference('cnf', [status(esa)], [t103_tmap_1])).
% 0.90/1.10  thf('107', plain,
% 0.90/1.10      (((v2_struct_0 @ sk_A)
% 0.90/1.10        | ~ (v2_pre_topc @ sk_A)
% 0.90/1.10        | ~ (l1_pre_topc @ sk_A)
% 0.90/1.10        | (r2_hidden @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_A))
% 0.90/1.10        | ((u1_pre_topc @ sk_A) != (k5_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B))))),
% 0.90/1.10      inference('sup-', [status(thm)], ['105', '106'])).
% 0.90/1.10  thf('108', plain, ((v2_pre_topc @ sk_A)),
% 0.90/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.10  thf('109', plain, ((l1_pre_topc @ sk_A)),
% 0.90/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.10  thf('110', plain,
% 0.90/1.10      (((v2_struct_0 @ sk_A)
% 0.90/1.10        | (r2_hidden @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_A))
% 0.90/1.10        | ((u1_pre_topc @ sk_A) != (k5_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B))))),
% 0.90/1.10      inference('demod', [status(thm)], ['107', '108', '109'])).
% 0.90/1.10  thf('111', plain, (~ (v2_struct_0 @ sk_A)),
% 0.90/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.10  thf('112', plain,
% 0.90/1.10      ((((u1_pre_topc @ sk_A) != (k5_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 0.90/1.10        | (r2_hidden @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_A)))),
% 0.90/1.10      inference('clc', [status(thm)], ['110', '111'])).
% 0.90/1.10  thf('113', plain,
% 0.90/1.10      (((k8_tmap_1 @ sk_A @ sk_B) = (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))),
% 0.90/1.10      inference('clc', [status(thm)], ['57', '58'])).
% 0.90/1.10  thf('114', plain,
% 0.90/1.10      (((k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B))
% 0.90/1.10         = (g1_pre_topc @ (u1_struct_0 @ sk_A) @ 
% 0.90/1.10            (k5_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B))))),
% 0.90/1.10      inference('clc', [status(thm)], ['90', '91'])).
% 0.90/1.10  thf('115', plain,
% 0.90/1.10      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.90/1.10          = (k8_tmap_1 @ sk_A @ sk_B)))
% 0.90/1.10         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.90/1.10                = (k8_tmap_1 @ sk_A @ sk_B))))),
% 0.90/1.10      inference('split', [status(esa)], ['60'])).
% 0.90/1.10  thf(dt_u1_pre_topc, axiom,
% 0.90/1.10    (![A:$i]:
% 0.90/1.10     ( ( l1_pre_topc @ A ) =>
% 0.90/1.10       ( m1_subset_1 @
% 0.90/1.10         ( u1_pre_topc @ A ) @ 
% 0.90/1.10         ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ))).
% 0.90/1.10  thf('116', plain,
% 0.90/1.10      (![X16 : $i]:
% 0.90/1.10         ((m1_subset_1 @ (u1_pre_topc @ X16) @ 
% 0.90/1.10           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16))))
% 0.90/1.10          | ~ (l1_pre_topc @ X16))),
% 0.90/1.10      inference('cnf', [status(esa)], [dt_u1_pre_topc])).
% 0.90/1.10  thf(free_g1_pre_topc, axiom,
% 0.90/1.10    (![A:$i,B:$i]:
% 0.90/1.10     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.90/1.10       ( ![C:$i,D:$i]:
% 0.90/1.10         ( ( ( g1_pre_topc @ A @ B ) = ( g1_pre_topc @ C @ D ) ) =>
% 0.90/1.10           ( ( ( A ) = ( C ) ) & ( ( B ) = ( D ) ) ) ) ) ))).
% 0.90/1.10  thf('117', plain,
% 0.90/1.10      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 0.90/1.10         (((g1_pre_topc @ X21 @ X22) != (g1_pre_topc @ X19 @ X20))
% 0.90/1.10          | ((X22) = (X20))
% 0.90/1.10          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X21))))),
% 0.90/1.10      inference('cnf', [status(esa)], [free_g1_pre_topc])).
% 0.90/1.10  thf('118', plain,
% 0.90/1.10      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.90/1.10         (~ (l1_pre_topc @ X0)
% 0.90/1.10          | ((u1_pre_topc @ X0) = (X1))
% 0.90/1.10          | ((g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))
% 0.90/1.10              != (g1_pre_topc @ X2 @ X1)))),
% 0.90/1.10      inference('sup-', [status(thm)], ['116', '117'])).
% 0.90/1.10  thf('119', plain,
% 0.90/1.10      ((![X0 : $i, X1 : $i]:
% 0.90/1.10          (((k8_tmap_1 @ sk_A @ sk_B) != (g1_pre_topc @ X1 @ X0))
% 0.90/1.10           | ((u1_pre_topc @ sk_A) = (X0))
% 0.90/1.10           | ~ (l1_pre_topc @ sk_A)))
% 0.90/1.10         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.90/1.10                = (k8_tmap_1 @ sk_A @ sk_B))))),
% 0.90/1.10      inference('sup-', [status(thm)], ['115', '118'])).
% 0.90/1.10  thf('120', plain, ((l1_pre_topc @ sk_A)),
% 0.90/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.10  thf('121', plain,
% 0.90/1.10      ((![X0 : $i, X1 : $i]:
% 0.90/1.10          (((k8_tmap_1 @ sk_A @ sk_B) != (g1_pre_topc @ X1 @ X0))
% 0.90/1.10           | ((u1_pre_topc @ sk_A) = (X0))))
% 0.90/1.10         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.90/1.10                = (k8_tmap_1 @ sk_A @ sk_B))))),
% 0.90/1.10      inference('demod', [status(thm)], ['119', '120'])).
% 0.90/1.10  thf('122', plain,
% 0.90/1.10      (((((k8_tmap_1 @ sk_A @ sk_B)
% 0.90/1.10           != (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 0.90/1.10         | ((u1_pre_topc @ sk_A) = (k5_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))))
% 0.90/1.10         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.90/1.10                = (k8_tmap_1 @ sk_A @ sk_B))))),
% 0.90/1.10      inference('sup-', [status(thm)], ['114', '121'])).
% 0.90/1.10  thf('123', plain,
% 0.90/1.10      (((((k8_tmap_1 @ sk_A @ sk_B) != (k8_tmap_1 @ sk_A @ sk_B))
% 0.90/1.10         | ((u1_pre_topc @ sk_A) = (k5_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))))
% 0.90/1.10         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.90/1.10                = (k8_tmap_1 @ sk_A @ sk_B))))),
% 0.90/1.10      inference('sup-', [status(thm)], ['113', '122'])).
% 0.90/1.10  thf('124', plain,
% 0.90/1.10      ((((u1_pre_topc @ sk_A) = (k5_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B))))
% 0.90/1.10         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.90/1.10                = (k8_tmap_1 @ sk_A @ sk_B))))),
% 0.90/1.10      inference('simplify', [status(thm)], ['123'])).
% 0.90/1.10  thf('125', plain,
% 0.90/1.10      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.90/1.10          = (k8_tmap_1 @ sk_A @ sk_B))) | 
% 0.90/1.10       ((v1_tsep_1 @ sk_B @ sk_A))),
% 0.90/1.10      inference('split', [status(esa)], ['60'])).
% 0.90/1.10  thf('126', plain,
% 0.90/1.10      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.90/1.10          = (k8_tmap_1 @ sk_A @ sk_B)))),
% 0.90/1.10      inference('sat_resolution*', [status(thm)], ['15', '18', '97', '125'])).
% 0.90/1.10  thf('127', plain,
% 0.90/1.10      (((u1_pre_topc @ sk_A) = (k5_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))),
% 0.90/1.10      inference('simpl_trail', [status(thm)], ['124', '126'])).
% 0.90/1.10  thf('128', plain,
% 0.90/1.10      ((((u1_pre_topc @ sk_A) != (u1_pre_topc @ sk_A))
% 0.90/1.10        | (r2_hidden @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_A)))),
% 0.90/1.10      inference('demod', [status(thm)], ['112', '127'])).
% 0.90/1.10  thf('129', plain,
% 0.90/1.10      ((r2_hidden @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_A))),
% 0.90/1.10      inference('simplify', [status(thm)], ['128'])).
% 0.90/1.10  thf('130', plain, ((v3_pre_topc @ (u1_struct_0 @ sk_B) @ sk_A)),
% 0.90/1.10      inference('demod', [status(thm)], ['104', '129'])).
% 0.90/1.10  thf('131', plain, ($false), inference('demod', [status(thm)], ['99', '130'])).
% 0.90/1.10  
% 0.90/1.10  % SZS output end Refutation
% 0.90/1.10  
% 0.90/1.11  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
