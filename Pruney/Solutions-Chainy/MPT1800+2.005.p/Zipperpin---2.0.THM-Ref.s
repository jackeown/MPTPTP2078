%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.43al58nCtD

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:10:55 EST 2020

% Result     : Theorem 0.84s
% Output     : Refutation 0.84s
% Verified   : 
% Statistics : Number of formulae       :  174 ( 685 expanded)
%              Number of leaves         :   32 ( 203 expanded)
%              Depth                    :   18
%              Number of atoms          : 1538 (10436 expanded)
%              Number of equality atoms :   71 ( 394 expanded)
%              Maximal formula depth    :   17 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k6_tmap_1_type,type,(
    k6_tmap_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(g1_pre_topc_type,type,(
    g1_pre_topc: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k5_tmap_1_type,type,(
    k5_tmap_1: $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_tsep_1_type,type,(
    v1_tsep_1: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(k8_tmap_1_type,type,(
    k8_tmap_1: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

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
    ! [X20: $i,X21: $i] :
      ( ~ ( m1_pre_topc @ X20 @ X21 )
      | ( ( sk_C @ X20 @ X21 )
        = ( u1_struct_0 @ X20 ) )
      | ( v1_tsep_1 @ X20 @ X21 )
      | ~ ( l1_pre_topc @ X21 ) ) ),
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
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( m1_pre_topc @ X20 @ X21 )
      | ( m1_subset_1 @ ( sk_C @ X20 @ X21 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ( v1_tsep_1 @ X20 @ X21 )
      | ~ ( l1_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[d1_tsep_1])).

thf('10',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v1_tsep_1 @ sk_B @ sk_A )
    | ( m1_subset_1 @ ( sk_C @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ( v1_tsep_1 @ sk_B @ sk_A )
    | ( m1_subset_1 @ ( sk_C @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf(d5_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v3_pre_topc @ B @ A )
          <=> ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) ) ) ) )).

thf('13',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) )
      | ~ ( r2_hidden @ X4 @ ( u1_pre_topc @ X5 ) )
      | ( v3_pre_topc @ X4 @ X5 )
      | ~ ( l1_pre_topc @ X5 ) ) ),
    inference(cnf,[status(esa)],[d5_pre_topc])).

thf('14',plain,
    ( ( v1_tsep_1 @ sk_B @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v3_pre_topc @ ( sk_C @ sk_B @ sk_A ) @ sk_A )
    | ~ ( r2_hidden @ ( sk_C @ sk_B @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( v1_tsep_1 @ sk_B @ sk_A )
    | ( v3_pre_topc @ ( sk_C @ sk_B @ sk_A ) @ sk_A )
    | ~ ( r2_hidden @ ( sk_C @ sk_B @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,
    ( ( ~ ( r2_hidden @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_A ) )
      | ( v3_pre_topc @ ( sk_C @ sk_B @ sk_A ) @ sk_A )
      | ( v1_tsep_1 @ sk_B @ sk_A ) )
   <= ~ ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['7','16'])).

thf('18',plain,
    ( ( ( sk_C @ sk_B @ sk_A )
      = ( u1_struct_0 @ sk_B ) )
   <= ~ ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['4','6'])).

thf('19',plain,
    ( ( ~ ( r2_hidden @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_A ) )
      | ( v3_pre_topc @ ( u1_struct_0 @ sk_B ) @ sk_A )
      | ( v1_tsep_1 @ sk_B @ sk_A ) )
   <= ~ ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,
    ( ( ( sk_C @ sk_B @ sk_A )
      = ( u1_struct_0 @ sk_B ) )
   <= ~ ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['4','6'])).

thf('21',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( m1_pre_topc @ X20 @ X21 )
      | ~ ( v3_pre_topc @ ( sk_C @ X20 @ X21 ) @ X21 )
      | ( v1_tsep_1 @ X20 @ X21 )
      | ~ ( l1_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[d1_tsep_1])).

thf('22',plain,
    ( ( ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_B ) @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v1_tsep_1 @ sk_B @ sk_A )
      | ~ ( m1_pre_topc @ sk_B @ sk_A ) )
   <= ~ ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ( ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_B ) @ sk_A )
      | ( v1_tsep_1 @ sk_B @ sk_A ) )
   <= ~ ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['22','23','24'])).

thf('26',plain,
    ( ~ ( v1_tsep_1 @ sk_B @ sk_A )
   <= ~ ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['5'])).

thf('27',plain,
    ( ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_B ) @ sk_A )
   <= ~ ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['25','26'])).

thf('28',plain,
    ( ( ( v1_tsep_1 @ sk_B @ sk_A )
      | ~ ( r2_hidden @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_A ) ) )
   <= ~ ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['19','27'])).

thf('29',plain,
    ( ~ ( v1_tsep_1 @ sk_B @ sk_A )
   <= ~ ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['5'])).

thf('30',plain,
    ( ~ ( r2_hidden @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_A ) )
   <= ~ ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['28','29'])).

thf('31',plain,
    ( ~ ( v1_tsep_1 @ sk_B @ sk_A )
    | ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
     != ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['5'])).

thf('32',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ~ ( m1_pre_topc @ sk_B @ sk_A )
   <= ~ ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['5'])).

thf('34',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t35_borsuk_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( r1_tarski @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) )).

thf('36',plain,(
    ! [X38: $i,X39: $i] :
      ( ~ ( m1_pre_topc @ X38 @ X39 )
      | ( r1_tarski @ ( u1_struct_0 @ X38 ) @ ( u1_struct_0 @ X39 ) )
      | ~ ( l1_pre_topc @ X39 ) ) ),
    inference(cnf,[status(esa)],[t35_borsuk_1])).

thf('37',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['37','38'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('40',plain,(
    ! [X0: $i,X2: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X2 ) )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('41',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

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

thf('42',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_pre_topc @ X16 @ X17 )
      | ( X18
       != ( k8_tmap_1 @ X17 @ X16 ) )
      | ( X19
       != ( u1_struct_0 @ X16 ) )
      | ( X18
        = ( k6_tmap_1 @ X17 @ X19 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ~ ( l1_pre_topc @ X18 )
      | ~ ( v2_pre_topc @ X18 )
      | ~ ( v1_pre_topc @ X18 )
      | ~ ( l1_pre_topc @ X17 )
      | ~ ( v2_pre_topc @ X17 )
      | ( v2_struct_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d11_tmap_1])).

thf('43',plain,(
    ! [X16: $i,X17: $i] :
      ( ( v2_struct_0 @ X17 )
      | ~ ( v2_pre_topc @ X17 )
      | ~ ( l1_pre_topc @ X17 )
      | ~ ( v1_pre_topc @ ( k8_tmap_1 @ X17 @ X16 ) )
      | ~ ( v2_pre_topc @ ( k8_tmap_1 @ X17 @ X16 ) )
      | ~ ( l1_pre_topc @ ( k8_tmap_1 @ X17 @ X16 ) )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X16 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ( ( k8_tmap_1 @ X17 @ X16 )
        = ( k6_tmap_1 @ X17 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( m1_pre_topc @ X16 @ X17 ) ) ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,
    ( ~ ( m1_pre_topc @ sk_B @ sk_A )
    | ( ( k8_tmap_1 @ sk_A @ sk_B )
      = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
    | ~ ( l1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( v2_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( v1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['41','43'])).

thf('45',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
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

thf('47',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( l1_pre_topc @ X25 )
      | ~ ( v2_pre_topc @ X25 )
      | ( v2_struct_0 @ X25 )
      | ~ ( m1_pre_topc @ X26 @ X25 )
      | ( l1_pre_topc @ ( k8_tmap_1 @ X25 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k8_tmap_1])).

thf('48',plain,
    ( ( l1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,
    ( ( l1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['48','49','50'])).

thf('52',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    l1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['51','52'])).

thf('54',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,
    ( ( ( k8_tmap_1 @ sk_A @ sk_B )
      = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
    | ~ ( v2_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( v1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['44','45','53','54','55'])).

thf('57',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( l1_pre_topc @ X25 )
      | ~ ( v2_pre_topc @ X25 )
      | ( v2_struct_0 @ X25 )
      | ~ ( m1_pre_topc @ X26 @ X25 )
      | ( v2_pre_topc @ ( k8_tmap_1 @ X25 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k8_tmap_1])).

thf('59',plain,
    ( ( v2_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,
    ( ( v2_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['59','60','61'])).

thf('63',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    v2_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['62','63'])).

thf('65',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( l1_pre_topc @ X25 )
      | ~ ( v2_pre_topc @ X25 )
      | ( v2_struct_0 @ X25 )
      | ~ ( m1_pre_topc @ X26 @ X25 )
      | ( v1_pre_topc @ ( k8_tmap_1 @ X25 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k8_tmap_1])).

thf('67',plain,
    ( ( v1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,
    ( ( v1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['67','68','69'])).

thf('71',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    v1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['70','71'])).

thf('73',plain,
    ( ( ( k8_tmap_1 @ sk_A @ sk_B )
      = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['56','64','72'])).

thf('74',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,
    ( ( k8_tmap_1 @ sk_A @ sk_B )
    = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['73','74'])).

thf('76',plain,
    ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,
    ( ( v1_tsep_1 @ sk_B @ sk_A )
   <= ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['76'])).

thf('78',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('79',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_pre_topc @ X20 @ X21 )
      | ~ ( v1_tsep_1 @ X20 @ X21 )
      | ( X22
       != ( u1_struct_0 @ X20 ) )
      | ( v3_pre_topc @ X22 @ X21 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( l1_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[d1_tsep_1])).

thf('80',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( l1_pre_topc @ X21 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X20 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ( v3_pre_topc @ ( u1_struct_0 @ X20 ) @ X21 )
      | ~ ( v1_tsep_1 @ X20 @ X21 )
      | ~ ( m1_pre_topc @ X20 @ X21 ) ) ),
    inference(simplify,[status(thm)],['79'])).

thf('81',plain,
    ( ~ ( m1_pre_topc @ sk_B @ sk_A )
    | ~ ( v1_tsep_1 @ sk_B @ sk_A )
    | ( v3_pre_topc @ ( u1_struct_0 @ sk_B ) @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['78','80'])).

thf('82',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,
    ( ~ ( v1_tsep_1 @ sk_B @ sk_A )
    | ( v3_pre_topc @ ( u1_struct_0 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['81','82','83'])).

thf('85',plain,
    ( ( v3_pre_topc @ ( u1_struct_0 @ sk_B ) @ sk_A )
   <= ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['77','84'])).

thf('86',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('87',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) )
      | ~ ( v3_pre_topc @ X4 @ X5 )
      | ( r2_hidden @ X4 @ ( u1_pre_topc @ X5 ) )
      | ~ ( l1_pre_topc @ X5 ) ) ),
    inference(cnf,[status(esa)],[d5_pre_topc])).

thf('88',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r2_hidden @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_A ) )
    | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,
    ( ( r2_hidden @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_A ) )
    | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['88','89'])).

thf('91',plain,
    ( ( r2_hidden @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_A ) )
   <= ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['85','90'])).

thf('92',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

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

thf('93',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X30 ) ) )
      | ~ ( r2_hidden @ X29 @ ( u1_pre_topc @ X30 ) )
      | ( ( u1_pre_topc @ X30 )
        = ( k5_tmap_1 @ X30 @ X29 ) )
      | ~ ( l1_pre_topc @ X30 )
      | ~ ( v2_pre_topc @ X30 )
      | ( v2_struct_0 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t103_tmap_1])).

thf('94',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( ( u1_pre_topc @ sk_A )
      = ( k5_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
    | ~ ( r2_hidden @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( u1_pre_topc @ sk_A )
      = ( k5_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
    | ~ ( r2_hidden @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_A ) ) ),
    inference(demod,[status(thm)],['94','95','96'])).

thf('98',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,
    ( ~ ( r2_hidden @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_A ) )
    | ( ( u1_pre_topc @ sk_A )
      = ( k5_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['97','98'])).

thf('100',plain,
    ( ( ( u1_pre_topc @ sk_A )
      = ( k5_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
   <= ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['91','99'])).

thf('101',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf(d9_tmap_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k6_tmap_1 @ A @ B )
            = ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( k5_tmap_1 @ A @ B ) ) ) ) ) )).

thf('102',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ( ( k6_tmap_1 @ X24 @ X23 )
        = ( g1_pre_topc @ ( u1_struct_0 @ X24 ) @ ( k5_tmap_1 @ X24 @ X23 ) ) )
      | ~ ( l1_pre_topc @ X24 )
      | ~ ( v2_pre_topc @ X24 )
      | ( v2_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d9_tmap_1])).

thf('103',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) )
      = ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( k5_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) )
      = ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( k5_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['103','104','105'])).

thf('107',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,
    ( ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( k5_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['106','107'])).

thf('109',plain,
    ( ( ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) )
      = ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
   <= ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['100','108'])).

thf('110',plain,
    ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
     != ( k8_tmap_1 @ sk_A @ sk_B ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
     != ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['5'])).

thf('111',plain,
    ( ( ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) )
     != ( k8_tmap_1 @ sk_A @ sk_B ) )
   <= ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
       != ( k8_tmap_1 @ sk_A @ sk_B ) )
      & ( v1_tsep_1 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['109','110'])).

thf('112',plain,
    ( ( ( k8_tmap_1 @ sk_A @ sk_B )
     != ( k8_tmap_1 @ sk_A @ sk_B ) )
   <= ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
       != ( k8_tmap_1 @ sk_A @ sk_B ) )
      & ( v1_tsep_1 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['75','111'])).

thf('113',plain,
    ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['112'])).

thf('114',plain,(
    ~ ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['31','34','113'])).

thf('115',plain,(
    ~ ( r2_hidden @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_A ) ) ),
    inference(simpl_trail,[status(thm)],['30','114'])).

thf('116',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf(t102_tmap_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r2_hidden @ B @ ( k5_tmap_1 @ A @ B ) ) ) ) )).

thf('117',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ( r2_hidden @ X27 @ ( k5_tmap_1 @ X28 @ X27 ) )
      | ~ ( l1_pre_topc @ X28 )
      | ~ ( v2_pre_topc @ X28 )
      | ( v2_struct_0 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t102_tmap_1])).

thf('118',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( r2_hidden @ ( u1_struct_0 @ sk_B ) @ ( k5_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['116','117'])).

thf('119',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('121',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ ( u1_struct_0 @ sk_B ) @ ( k5_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['118','119','120'])).

thf('122',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,(
    r2_hidden @ ( u1_struct_0 @ sk_B ) @ ( k5_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['121','122'])).

thf('124',plain,
    ( ( k8_tmap_1 @ sk_A @ sk_B )
    = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['73','74'])).

thf('125',plain,
    ( ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( k5_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['106','107'])).

thf('126',plain,
    ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k8_tmap_1 @ sk_A @ sk_B ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['76'])).

thf(dt_u1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( m1_subset_1 @ ( u1_pre_topc @ A ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('127',plain,(
    ! [X8: $i] :
      ( ( m1_subset_1 @ ( u1_pre_topc @ X8 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) ) )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_pre_topc])).

thf(free_g1_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ! [C: $i,D: $i] :
          ( ( ( g1_pre_topc @ A @ B )
            = ( g1_pre_topc @ C @ D ) )
         => ( ( A = C )
            & ( B = D ) ) ) ) )).

thf('128',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( ( g1_pre_topc @ X12 @ X13 )
       != ( g1_pre_topc @ X10 @ X11 ) )
      | ( X13 = X11 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[free_g1_pre_topc])).

thf('129',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( u1_pre_topc @ X0 )
        = X1 )
      | ( ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) )
       != ( g1_pre_topc @ X2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['127','128'])).

thf('130',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( ( k8_tmap_1 @ sk_A @ sk_B )
         != ( g1_pre_topc @ X1 @ X0 ) )
        | ( ( u1_pre_topc @ sk_A )
          = X0 )
        | ~ ( l1_pre_topc @ sk_A ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['126','129'])).

thf('131',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('132',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( ( k8_tmap_1 @ sk_A @ sk_B )
         != ( g1_pre_topc @ X1 @ X0 ) )
        | ( ( u1_pre_topc @ sk_A )
          = X0 ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['130','131'])).

thf('133',plain,
    ( ( ( ( k8_tmap_1 @ sk_A @ sk_B )
       != ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
      | ( ( u1_pre_topc @ sk_A )
        = ( k5_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['125','132'])).

thf('134',plain,
    ( ( ( ( k8_tmap_1 @ sk_A @ sk_B )
       != ( k8_tmap_1 @ sk_A @ sk_B ) )
      | ( ( u1_pre_topc @ sk_A )
        = ( k5_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['124','133'])).

thf('135',plain,
    ( ( ( u1_pre_topc @ sk_A )
      = ( k5_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['134'])).

thf('136',plain,
    ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['76'])).

thf('137',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
    = ( k8_tmap_1 @ sk_A @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['31','34','113','136'])).

thf('138',plain,
    ( ( u1_pre_topc @ sk_A )
    = ( k5_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ),
    inference(simpl_trail,[status(thm)],['135','137'])).

thf('139',plain,(
    r2_hidden @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_A ) ),
    inference(demod,[status(thm)],['123','138'])).

thf('140',plain,(
    $false ),
    inference(demod,[status(thm)],['115','139'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.43al58nCtD
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:44:57 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.84/1.06  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.84/1.06  % Solved by: fo/fo7.sh
% 0.84/1.06  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.84/1.06  % done 779 iterations in 0.606s
% 0.84/1.06  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.84/1.06  % SZS output start Refutation
% 0.84/1.06  thf(k6_tmap_1_type, type, k6_tmap_1: $i > $i > $i).
% 0.84/1.06  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.84/1.06  thf(g1_pre_topc_type, type, g1_pre_topc: $i > $i > $i).
% 0.84/1.06  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.84/1.06  thf(k5_tmap_1_type, type, k5_tmap_1: $i > $i > $i).
% 0.84/1.06  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.84/1.06  thf(sk_A_type, type, sk_A: $i).
% 0.84/1.06  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 0.84/1.06  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.84/1.06  thf(sk_B_type, type, sk_B: $i).
% 0.84/1.06  thf(v1_tsep_1_type, type, v1_tsep_1: $i > $i > $o).
% 0.84/1.06  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.84/1.06  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.84/1.06  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 0.84/1.06  thf(k8_tmap_1_type, type, k8_tmap_1: $i > $i > $i).
% 0.84/1.06  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.84/1.06  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.84/1.06  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.84/1.06  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.84/1.06  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.84/1.06  thf(t116_tmap_1, conjecture,
% 0.84/1.06    (![A:$i]:
% 0.84/1.06     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.84/1.06       ( ![B:$i]:
% 0.84/1.06         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.84/1.06           ( ( ( v1_tsep_1 @ B @ A ) & ( m1_pre_topc @ B @ A ) ) <=>
% 0.84/1.06             ( ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) =
% 0.84/1.06               ( k8_tmap_1 @ A @ B ) ) ) ) ) ))).
% 0.84/1.06  thf(zf_stmt_0, negated_conjecture,
% 0.84/1.06    (~( ![A:$i]:
% 0.84/1.06        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.84/1.06            ( l1_pre_topc @ A ) ) =>
% 0.84/1.06          ( ![B:$i]:
% 0.84/1.06            ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.84/1.06              ( ( ( v1_tsep_1 @ B @ A ) & ( m1_pre_topc @ B @ A ) ) <=>
% 0.84/1.06                ( ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) =
% 0.84/1.06                  ( k8_tmap_1 @ A @ B ) ) ) ) ) ) )),
% 0.84/1.06    inference('cnf.neg', [status(esa)], [t116_tmap_1])).
% 0.84/1.06  thf('0', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.84/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.06  thf(d1_tsep_1, axiom,
% 0.84/1.06    (![A:$i]:
% 0.84/1.06     ( ( l1_pre_topc @ A ) =>
% 0.84/1.06       ( ![B:$i]:
% 0.84/1.06         ( ( m1_pre_topc @ B @ A ) =>
% 0.84/1.06           ( ( v1_tsep_1 @ B @ A ) <=>
% 0.84/1.06             ( ![C:$i]:
% 0.84/1.06               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.84/1.06                 ( ( ( C ) = ( u1_struct_0 @ B ) ) => ( v3_pre_topc @ C @ A ) ) ) ) ) ) ) ))).
% 0.84/1.06  thf('1', plain,
% 0.84/1.06      (![X20 : $i, X21 : $i]:
% 0.84/1.06         (~ (m1_pre_topc @ X20 @ X21)
% 0.84/1.06          | ((sk_C @ X20 @ X21) = (u1_struct_0 @ X20))
% 0.84/1.06          | (v1_tsep_1 @ X20 @ X21)
% 0.84/1.06          | ~ (l1_pre_topc @ X21))),
% 0.84/1.06      inference('cnf', [status(esa)], [d1_tsep_1])).
% 0.84/1.06  thf('2', plain,
% 0.84/1.06      ((~ (l1_pre_topc @ sk_A)
% 0.84/1.06        | (v1_tsep_1 @ sk_B @ sk_A)
% 0.84/1.06        | ((sk_C @ sk_B @ sk_A) = (u1_struct_0 @ sk_B)))),
% 0.84/1.06      inference('sup-', [status(thm)], ['0', '1'])).
% 0.84/1.06  thf('3', plain, ((l1_pre_topc @ sk_A)),
% 0.84/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.06  thf('4', plain,
% 0.84/1.06      (((v1_tsep_1 @ sk_B @ sk_A)
% 0.84/1.06        | ((sk_C @ sk_B @ sk_A) = (u1_struct_0 @ sk_B)))),
% 0.84/1.06      inference('demod', [status(thm)], ['2', '3'])).
% 0.84/1.06  thf('5', plain,
% 0.84/1.06      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.84/1.06          != (k8_tmap_1 @ sk_A @ sk_B))
% 0.84/1.06        | ~ (m1_pre_topc @ sk_B @ sk_A)
% 0.84/1.06        | ~ (v1_tsep_1 @ sk_B @ sk_A))),
% 0.84/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.06  thf('6', plain,
% 0.84/1.06      ((~ (v1_tsep_1 @ sk_B @ sk_A)) <= (~ ((v1_tsep_1 @ sk_B @ sk_A)))),
% 0.84/1.06      inference('split', [status(esa)], ['5'])).
% 0.84/1.06  thf('7', plain,
% 0.84/1.06      ((((sk_C @ sk_B @ sk_A) = (u1_struct_0 @ sk_B)))
% 0.84/1.06         <= (~ ((v1_tsep_1 @ sk_B @ sk_A)))),
% 0.84/1.06      inference('sup-', [status(thm)], ['4', '6'])).
% 0.84/1.06  thf('8', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.84/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.06  thf('9', plain,
% 0.84/1.06      (![X20 : $i, X21 : $i]:
% 0.84/1.06         (~ (m1_pre_topc @ X20 @ X21)
% 0.84/1.06          | (m1_subset_1 @ (sk_C @ X20 @ X21) @ 
% 0.84/1.06             (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.84/1.06          | (v1_tsep_1 @ X20 @ X21)
% 0.84/1.06          | ~ (l1_pre_topc @ X21))),
% 0.84/1.06      inference('cnf', [status(esa)], [d1_tsep_1])).
% 0.84/1.06  thf('10', plain,
% 0.84/1.06      ((~ (l1_pre_topc @ sk_A)
% 0.84/1.06        | (v1_tsep_1 @ sk_B @ sk_A)
% 0.84/1.06        | (m1_subset_1 @ (sk_C @ sk_B @ sk_A) @ 
% 0.84/1.06           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.84/1.06      inference('sup-', [status(thm)], ['8', '9'])).
% 0.84/1.06  thf('11', plain, ((l1_pre_topc @ sk_A)),
% 0.84/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.06  thf('12', plain,
% 0.84/1.06      (((v1_tsep_1 @ sk_B @ sk_A)
% 0.84/1.06        | (m1_subset_1 @ (sk_C @ sk_B @ sk_A) @ 
% 0.84/1.06           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.84/1.06      inference('demod', [status(thm)], ['10', '11'])).
% 0.84/1.06  thf(d5_pre_topc, axiom,
% 0.84/1.06    (![A:$i]:
% 0.84/1.06     ( ( l1_pre_topc @ A ) =>
% 0.84/1.06       ( ![B:$i]:
% 0.84/1.06         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.84/1.06           ( ( v3_pre_topc @ B @ A ) <=>
% 0.84/1.06             ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) ) ) ) ))).
% 0.84/1.06  thf('13', plain,
% 0.84/1.06      (![X4 : $i, X5 : $i]:
% 0.84/1.06         (~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (u1_struct_0 @ X5)))
% 0.84/1.06          | ~ (r2_hidden @ X4 @ (u1_pre_topc @ X5))
% 0.84/1.06          | (v3_pre_topc @ X4 @ X5)
% 0.84/1.06          | ~ (l1_pre_topc @ X5))),
% 0.84/1.06      inference('cnf', [status(esa)], [d5_pre_topc])).
% 0.84/1.06  thf('14', plain,
% 0.84/1.06      (((v1_tsep_1 @ sk_B @ sk_A)
% 0.84/1.06        | ~ (l1_pre_topc @ sk_A)
% 0.84/1.06        | (v3_pre_topc @ (sk_C @ sk_B @ sk_A) @ sk_A)
% 0.84/1.06        | ~ (r2_hidden @ (sk_C @ sk_B @ sk_A) @ (u1_pre_topc @ sk_A)))),
% 0.84/1.06      inference('sup-', [status(thm)], ['12', '13'])).
% 0.84/1.06  thf('15', plain, ((l1_pre_topc @ sk_A)),
% 0.84/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.06  thf('16', plain,
% 0.84/1.06      (((v1_tsep_1 @ sk_B @ sk_A)
% 0.84/1.06        | (v3_pre_topc @ (sk_C @ sk_B @ sk_A) @ sk_A)
% 0.84/1.06        | ~ (r2_hidden @ (sk_C @ sk_B @ sk_A) @ (u1_pre_topc @ sk_A)))),
% 0.84/1.06      inference('demod', [status(thm)], ['14', '15'])).
% 0.84/1.06  thf('17', plain,
% 0.84/1.06      (((~ (r2_hidden @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_A))
% 0.84/1.06         | (v3_pre_topc @ (sk_C @ sk_B @ sk_A) @ sk_A)
% 0.84/1.06         | (v1_tsep_1 @ sk_B @ sk_A))) <= (~ ((v1_tsep_1 @ sk_B @ sk_A)))),
% 0.84/1.06      inference('sup-', [status(thm)], ['7', '16'])).
% 0.84/1.06  thf('18', plain,
% 0.84/1.06      ((((sk_C @ sk_B @ sk_A) = (u1_struct_0 @ sk_B)))
% 0.84/1.06         <= (~ ((v1_tsep_1 @ sk_B @ sk_A)))),
% 0.84/1.06      inference('sup-', [status(thm)], ['4', '6'])).
% 0.84/1.06  thf('19', plain,
% 0.84/1.06      (((~ (r2_hidden @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_A))
% 0.84/1.06         | (v3_pre_topc @ (u1_struct_0 @ sk_B) @ sk_A)
% 0.84/1.06         | (v1_tsep_1 @ sk_B @ sk_A))) <= (~ ((v1_tsep_1 @ sk_B @ sk_A)))),
% 0.84/1.06      inference('demod', [status(thm)], ['17', '18'])).
% 0.84/1.06  thf('20', plain,
% 0.84/1.06      ((((sk_C @ sk_B @ sk_A) = (u1_struct_0 @ sk_B)))
% 0.84/1.06         <= (~ ((v1_tsep_1 @ sk_B @ sk_A)))),
% 0.84/1.06      inference('sup-', [status(thm)], ['4', '6'])).
% 0.84/1.06  thf('21', plain,
% 0.84/1.06      (![X20 : $i, X21 : $i]:
% 0.84/1.06         (~ (m1_pre_topc @ X20 @ X21)
% 0.84/1.06          | ~ (v3_pre_topc @ (sk_C @ X20 @ X21) @ X21)
% 0.84/1.06          | (v1_tsep_1 @ X20 @ X21)
% 0.84/1.06          | ~ (l1_pre_topc @ X21))),
% 0.84/1.06      inference('cnf', [status(esa)], [d1_tsep_1])).
% 0.84/1.06  thf('22', plain,
% 0.84/1.06      (((~ (v3_pre_topc @ (u1_struct_0 @ sk_B) @ sk_A)
% 0.84/1.06         | ~ (l1_pre_topc @ sk_A)
% 0.84/1.06         | (v1_tsep_1 @ sk_B @ sk_A)
% 0.84/1.06         | ~ (m1_pre_topc @ sk_B @ sk_A))) <= (~ ((v1_tsep_1 @ sk_B @ sk_A)))),
% 0.84/1.06      inference('sup-', [status(thm)], ['20', '21'])).
% 0.84/1.06  thf('23', plain, ((l1_pre_topc @ sk_A)),
% 0.84/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.06  thf('24', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.84/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.06  thf('25', plain,
% 0.84/1.06      (((~ (v3_pre_topc @ (u1_struct_0 @ sk_B) @ sk_A)
% 0.84/1.06         | (v1_tsep_1 @ sk_B @ sk_A))) <= (~ ((v1_tsep_1 @ sk_B @ sk_A)))),
% 0.84/1.06      inference('demod', [status(thm)], ['22', '23', '24'])).
% 0.84/1.06  thf('26', plain,
% 0.84/1.06      ((~ (v1_tsep_1 @ sk_B @ sk_A)) <= (~ ((v1_tsep_1 @ sk_B @ sk_A)))),
% 0.84/1.06      inference('split', [status(esa)], ['5'])).
% 0.84/1.06  thf('27', plain,
% 0.84/1.06      ((~ (v3_pre_topc @ (u1_struct_0 @ sk_B) @ sk_A))
% 0.84/1.06         <= (~ ((v1_tsep_1 @ sk_B @ sk_A)))),
% 0.84/1.06      inference('clc', [status(thm)], ['25', '26'])).
% 0.84/1.06  thf('28', plain,
% 0.84/1.06      ((((v1_tsep_1 @ sk_B @ sk_A)
% 0.84/1.06         | ~ (r2_hidden @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_A))))
% 0.84/1.06         <= (~ ((v1_tsep_1 @ sk_B @ sk_A)))),
% 0.84/1.06      inference('clc', [status(thm)], ['19', '27'])).
% 0.84/1.06  thf('29', plain,
% 0.84/1.06      ((~ (v1_tsep_1 @ sk_B @ sk_A)) <= (~ ((v1_tsep_1 @ sk_B @ sk_A)))),
% 0.84/1.06      inference('split', [status(esa)], ['5'])).
% 0.84/1.06  thf('30', plain,
% 0.84/1.06      ((~ (r2_hidden @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_A)))
% 0.84/1.06         <= (~ ((v1_tsep_1 @ sk_B @ sk_A)))),
% 0.84/1.06      inference('clc', [status(thm)], ['28', '29'])).
% 0.84/1.06  thf('31', plain,
% 0.84/1.06      (~ ((v1_tsep_1 @ sk_B @ sk_A)) | 
% 0.84/1.06       ~
% 0.84/1.06       (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.84/1.06          = (k8_tmap_1 @ sk_A @ sk_B))) | 
% 0.84/1.06       ~ ((m1_pre_topc @ sk_B @ sk_A))),
% 0.84/1.06      inference('split', [status(esa)], ['5'])).
% 0.84/1.06  thf('32', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.84/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.06  thf('33', plain,
% 0.84/1.06      ((~ (m1_pre_topc @ sk_B @ sk_A)) <= (~ ((m1_pre_topc @ sk_B @ sk_A)))),
% 0.84/1.06      inference('split', [status(esa)], ['5'])).
% 0.84/1.06  thf('34', plain, (((m1_pre_topc @ sk_B @ sk_A))),
% 0.84/1.06      inference('sup-', [status(thm)], ['32', '33'])).
% 0.84/1.06  thf('35', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.84/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.06  thf(t35_borsuk_1, axiom,
% 0.84/1.06    (![A:$i]:
% 0.84/1.06     ( ( l1_pre_topc @ A ) =>
% 0.84/1.06       ( ![B:$i]:
% 0.84/1.06         ( ( m1_pre_topc @ B @ A ) =>
% 0.84/1.06           ( r1_tarski @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ))).
% 0.84/1.06  thf('36', plain,
% 0.84/1.06      (![X38 : $i, X39 : $i]:
% 0.84/1.06         (~ (m1_pre_topc @ X38 @ X39)
% 0.84/1.06          | (r1_tarski @ (u1_struct_0 @ X38) @ (u1_struct_0 @ X39))
% 0.84/1.06          | ~ (l1_pre_topc @ X39))),
% 0.84/1.06      inference('cnf', [status(esa)], [t35_borsuk_1])).
% 0.84/1.06  thf('37', plain,
% 0.84/1.06      ((~ (l1_pre_topc @ sk_A)
% 0.84/1.06        | (r1_tarski @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 0.84/1.06      inference('sup-', [status(thm)], ['35', '36'])).
% 0.84/1.06  thf('38', plain, ((l1_pre_topc @ sk_A)),
% 0.84/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.06  thf('39', plain, ((r1_tarski @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.84/1.06      inference('demod', [status(thm)], ['37', '38'])).
% 0.84/1.06  thf(t3_subset, axiom,
% 0.84/1.06    (![A:$i,B:$i]:
% 0.84/1.06     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.84/1.06  thf('40', plain,
% 0.84/1.06      (![X0 : $i, X2 : $i]:
% 0.84/1.06         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X2)) | ~ (r1_tarski @ X0 @ X2))),
% 0.84/1.06      inference('cnf', [status(esa)], [t3_subset])).
% 0.84/1.06  thf('41', plain,
% 0.84/1.06      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.84/1.06        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.84/1.06      inference('sup-', [status(thm)], ['39', '40'])).
% 0.84/1.06  thf(d11_tmap_1, axiom,
% 0.84/1.06    (![A:$i]:
% 0.84/1.06     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.84/1.06       ( ![B:$i]:
% 0.84/1.06         ( ( m1_pre_topc @ B @ A ) =>
% 0.84/1.06           ( ![C:$i]:
% 0.84/1.06             ( ( ( v1_pre_topc @ C ) & ( v2_pre_topc @ C ) & 
% 0.84/1.06                 ( l1_pre_topc @ C ) ) =>
% 0.84/1.06               ( ( ( C ) = ( k8_tmap_1 @ A @ B ) ) <=>
% 0.84/1.06                 ( ![D:$i]:
% 0.84/1.06                   ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.84/1.06                     ( ( ( D ) = ( u1_struct_0 @ B ) ) =>
% 0.84/1.06                       ( ( C ) = ( k6_tmap_1 @ A @ D ) ) ) ) ) ) ) ) ) ) ))).
% 0.84/1.06  thf('42', plain,
% 0.84/1.06      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.84/1.06         (~ (m1_pre_topc @ X16 @ X17)
% 0.84/1.06          | ((X18) != (k8_tmap_1 @ X17 @ X16))
% 0.84/1.06          | ((X19) != (u1_struct_0 @ X16))
% 0.84/1.06          | ((X18) = (k6_tmap_1 @ X17 @ X19))
% 0.84/1.06          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.84/1.06          | ~ (l1_pre_topc @ X18)
% 0.84/1.06          | ~ (v2_pre_topc @ X18)
% 0.84/1.06          | ~ (v1_pre_topc @ X18)
% 0.84/1.06          | ~ (l1_pre_topc @ X17)
% 0.84/1.06          | ~ (v2_pre_topc @ X17)
% 0.84/1.06          | (v2_struct_0 @ X17))),
% 0.84/1.06      inference('cnf', [status(esa)], [d11_tmap_1])).
% 0.84/1.06  thf('43', plain,
% 0.84/1.06      (![X16 : $i, X17 : $i]:
% 0.84/1.06         ((v2_struct_0 @ X17)
% 0.84/1.06          | ~ (v2_pre_topc @ X17)
% 0.84/1.06          | ~ (l1_pre_topc @ X17)
% 0.84/1.06          | ~ (v1_pre_topc @ (k8_tmap_1 @ X17 @ X16))
% 0.84/1.06          | ~ (v2_pre_topc @ (k8_tmap_1 @ X17 @ X16))
% 0.84/1.06          | ~ (l1_pre_topc @ (k8_tmap_1 @ X17 @ X16))
% 0.84/1.06          | ~ (m1_subset_1 @ (u1_struct_0 @ X16) @ 
% 0.84/1.06               (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.84/1.06          | ((k8_tmap_1 @ X17 @ X16) = (k6_tmap_1 @ X17 @ (u1_struct_0 @ X16)))
% 0.84/1.06          | ~ (m1_pre_topc @ X16 @ X17))),
% 0.84/1.06      inference('simplify', [status(thm)], ['42'])).
% 0.84/1.06  thf('44', plain,
% 0.84/1.06      ((~ (m1_pre_topc @ sk_B @ sk_A)
% 0.84/1.06        | ((k8_tmap_1 @ sk_A @ sk_B)
% 0.84/1.06            = (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 0.84/1.06        | ~ (l1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.84/1.06        | ~ (v2_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.84/1.06        | ~ (v1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.84/1.06        | ~ (l1_pre_topc @ sk_A)
% 0.84/1.06        | ~ (v2_pre_topc @ sk_A)
% 0.84/1.06        | (v2_struct_0 @ sk_A))),
% 0.84/1.06      inference('sup-', [status(thm)], ['41', '43'])).
% 0.84/1.06  thf('45', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.84/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.06  thf('46', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.84/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.06  thf(dt_k8_tmap_1, axiom,
% 0.84/1.06    (![A:$i,B:$i]:
% 0.84/1.06     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.84/1.06         ( l1_pre_topc @ A ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.84/1.06       ( ( v1_pre_topc @ ( k8_tmap_1 @ A @ B ) ) & 
% 0.84/1.06         ( v2_pre_topc @ ( k8_tmap_1 @ A @ B ) ) & 
% 0.84/1.06         ( l1_pre_topc @ ( k8_tmap_1 @ A @ B ) ) ) ))).
% 0.84/1.06  thf('47', plain,
% 0.84/1.06      (![X25 : $i, X26 : $i]:
% 0.84/1.06         (~ (l1_pre_topc @ X25)
% 0.84/1.06          | ~ (v2_pre_topc @ X25)
% 0.84/1.06          | (v2_struct_0 @ X25)
% 0.84/1.06          | ~ (m1_pre_topc @ X26 @ X25)
% 0.84/1.06          | (l1_pre_topc @ (k8_tmap_1 @ X25 @ X26)))),
% 0.84/1.06      inference('cnf', [status(esa)], [dt_k8_tmap_1])).
% 0.84/1.06  thf('48', plain,
% 0.84/1.06      (((l1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.84/1.06        | (v2_struct_0 @ sk_A)
% 0.84/1.06        | ~ (v2_pre_topc @ sk_A)
% 0.84/1.06        | ~ (l1_pre_topc @ sk_A))),
% 0.84/1.06      inference('sup-', [status(thm)], ['46', '47'])).
% 0.84/1.06  thf('49', plain, ((v2_pre_topc @ sk_A)),
% 0.84/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.06  thf('50', plain, ((l1_pre_topc @ sk_A)),
% 0.84/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.06  thf('51', plain,
% 0.84/1.06      (((l1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B)) | (v2_struct_0 @ sk_A))),
% 0.84/1.06      inference('demod', [status(thm)], ['48', '49', '50'])).
% 0.84/1.06  thf('52', plain, (~ (v2_struct_0 @ sk_A)),
% 0.84/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.06  thf('53', plain, ((l1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))),
% 0.84/1.06      inference('clc', [status(thm)], ['51', '52'])).
% 0.84/1.06  thf('54', plain, ((l1_pre_topc @ sk_A)),
% 0.84/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.06  thf('55', plain, ((v2_pre_topc @ sk_A)),
% 0.84/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.06  thf('56', plain,
% 0.84/1.06      ((((k8_tmap_1 @ sk_A @ sk_B) = (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 0.84/1.06        | ~ (v2_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.84/1.06        | ~ (v1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.84/1.06        | (v2_struct_0 @ sk_A))),
% 0.84/1.06      inference('demod', [status(thm)], ['44', '45', '53', '54', '55'])).
% 0.84/1.06  thf('57', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.84/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.06  thf('58', plain,
% 0.84/1.06      (![X25 : $i, X26 : $i]:
% 0.84/1.06         (~ (l1_pre_topc @ X25)
% 0.84/1.06          | ~ (v2_pre_topc @ X25)
% 0.84/1.06          | (v2_struct_0 @ X25)
% 0.84/1.06          | ~ (m1_pre_topc @ X26 @ X25)
% 0.84/1.06          | (v2_pre_topc @ (k8_tmap_1 @ X25 @ X26)))),
% 0.84/1.06      inference('cnf', [status(esa)], [dt_k8_tmap_1])).
% 0.84/1.06  thf('59', plain,
% 0.84/1.06      (((v2_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.84/1.06        | (v2_struct_0 @ sk_A)
% 0.84/1.06        | ~ (v2_pre_topc @ sk_A)
% 0.84/1.06        | ~ (l1_pre_topc @ sk_A))),
% 0.84/1.06      inference('sup-', [status(thm)], ['57', '58'])).
% 0.84/1.06  thf('60', plain, ((v2_pre_topc @ sk_A)),
% 0.84/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.06  thf('61', plain, ((l1_pre_topc @ sk_A)),
% 0.84/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.06  thf('62', plain,
% 0.84/1.06      (((v2_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B)) | (v2_struct_0 @ sk_A))),
% 0.84/1.06      inference('demod', [status(thm)], ['59', '60', '61'])).
% 0.84/1.06  thf('63', plain, (~ (v2_struct_0 @ sk_A)),
% 0.84/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.06  thf('64', plain, ((v2_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))),
% 0.84/1.06      inference('clc', [status(thm)], ['62', '63'])).
% 0.84/1.06  thf('65', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.84/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.06  thf('66', plain,
% 0.84/1.06      (![X25 : $i, X26 : $i]:
% 0.84/1.06         (~ (l1_pre_topc @ X25)
% 0.84/1.06          | ~ (v2_pre_topc @ X25)
% 0.84/1.06          | (v2_struct_0 @ X25)
% 0.84/1.06          | ~ (m1_pre_topc @ X26 @ X25)
% 0.84/1.06          | (v1_pre_topc @ (k8_tmap_1 @ X25 @ X26)))),
% 0.84/1.06      inference('cnf', [status(esa)], [dt_k8_tmap_1])).
% 0.84/1.06  thf('67', plain,
% 0.84/1.06      (((v1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.84/1.06        | (v2_struct_0 @ sk_A)
% 0.84/1.06        | ~ (v2_pre_topc @ sk_A)
% 0.84/1.06        | ~ (l1_pre_topc @ sk_A))),
% 0.84/1.06      inference('sup-', [status(thm)], ['65', '66'])).
% 0.84/1.06  thf('68', plain, ((v2_pre_topc @ sk_A)),
% 0.84/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.06  thf('69', plain, ((l1_pre_topc @ sk_A)),
% 0.84/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.06  thf('70', plain,
% 0.84/1.06      (((v1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B)) | (v2_struct_0 @ sk_A))),
% 0.84/1.06      inference('demod', [status(thm)], ['67', '68', '69'])).
% 0.84/1.06  thf('71', plain, (~ (v2_struct_0 @ sk_A)),
% 0.84/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.06  thf('72', plain, ((v1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))),
% 0.84/1.06      inference('clc', [status(thm)], ['70', '71'])).
% 0.84/1.06  thf('73', plain,
% 0.84/1.06      ((((k8_tmap_1 @ sk_A @ sk_B) = (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 0.84/1.06        | (v2_struct_0 @ sk_A))),
% 0.84/1.06      inference('demod', [status(thm)], ['56', '64', '72'])).
% 0.84/1.06  thf('74', plain, (~ (v2_struct_0 @ sk_A)),
% 0.84/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.06  thf('75', plain,
% 0.84/1.06      (((k8_tmap_1 @ sk_A @ sk_B) = (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))),
% 0.84/1.06      inference('clc', [status(thm)], ['73', '74'])).
% 0.84/1.06  thf('76', plain,
% 0.84/1.06      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.84/1.06          = (k8_tmap_1 @ sk_A @ sk_B))
% 0.84/1.06        | (v1_tsep_1 @ sk_B @ sk_A))),
% 0.84/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.06  thf('77', plain,
% 0.84/1.06      (((v1_tsep_1 @ sk_B @ sk_A)) <= (((v1_tsep_1 @ sk_B @ sk_A)))),
% 0.84/1.06      inference('split', [status(esa)], ['76'])).
% 0.84/1.06  thf('78', plain,
% 0.84/1.06      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.84/1.06        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.84/1.06      inference('sup-', [status(thm)], ['39', '40'])).
% 0.84/1.06  thf('79', plain,
% 0.84/1.06      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.84/1.06         (~ (m1_pre_topc @ X20 @ X21)
% 0.84/1.06          | ~ (v1_tsep_1 @ X20 @ X21)
% 0.84/1.06          | ((X22) != (u1_struct_0 @ X20))
% 0.84/1.06          | (v3_pre_topc @ X22 @ X21)
% 0.84/1.06          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.84/1.06          | ~ (l1_pre_topc @ X21))),
% 0.84/1.06      inference('cnf', [status(esa)], [d1_tsep_1])).
% 0.84/1.06  thf('80', plain,
% 0.84/1.06      (![X20 : $i, X21 : $i]:
% 0.84/1.06         (~ (l1_pre_topc @ X21)
% 0.84/1.06          | ~ (m1_subset_1 @ (u1_struct_0 @ X20) @ 
% 0.84/1.06               (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.84/1.06          | (v3_pre_topc @ (u1_struct_0 @ X20) @ X21)
% 0.84/1.06          | ~ (v1_tsep_1 @ X20 @ X21)
% 0.84/1.06          | ~ (m1_pre_topc @ X20 @ X21))),
% 0.84/1.06      inference('simplify', [status(thm)], ['79'])).
% 0.84/1.06  thf('81', plain,
% 0.84/1.06      ((~ (m1_pre_topc @ sk_B @ sk_A)
% 0.84/1.06        | ~ (v1_tsep_1 @ sk_B @ sk_A)
% 0.84/1.06        | (v3_pre_topc @ (u1_struct_0 @ sk_B) @ sk_A)
% 0.84/1.06        | ~ (l1_pre_topc @ sk_A))),
% 0.84/1.06      inference('sup-', [status(thm)], ['78', '80'])).
% 0.84/1.06  thf('82', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.84/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.06  thf('83', plain, ((l1_pre_topc @ sk_A)),
% 0.84/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.06  thf('84', plain,
% 0.84/1.06      ((~ (v1_tsep_1 @ sk_B @ sk_A)
% 0.84/1.06        | (v3_pre_topc @ (u1_struct_0 @ sk_B) @ sk_A))),
% 0.84/1.06      inference('demod', [status(thm)], ['81', '82', '83'])).
% 0.84/1.06  thf('85', plain,
% 0.84/1.06      (((v3_pre_topc @ (u1_struct_0 @ sk_B) @ sk_A))
% 0.84/1.06         <= (((v1_tsep_1 @ sk_B @ sk_A)))),
% 0.84/1.06      inference('sup-', [status(thm)], ['77', '84'])).
% 0.84/1.06  thf('86', plain,
% 0.84/1.06      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.84/1.06        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.84/1.06      inference('sup-', [status(thm)], ['39', '40'])).
% 0.84/1.06  thf('87', plain,
% 0.84/1.06      (![X4 : $i, X5 : $i]:
% 0.84/1.06         (~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (u1_struct_0 @ X5)))
% 0.84/1.06          | ~ (v3_pre_topc @ X4 @ X5)
% 0.84/1.06          | (r2_hidden @ X4 @ (u1_pre_topc @ X5))
% 0.84/1.06          | ~ (l1_pre_topc @ X5))),
% 0.84/1.06      inference('cnf', [status(esa)], [d5_pre_topc])).
% 0.84/1.06  thf('88', plain,
% 0.84/1.06      ((~ (l1_pre_topc @ sk_A)
% 0.84/1.06        | (r2_hidden @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_A))
% 0.84/1.06        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_B) @ sk_A))),
% 0.84/1.06      inference('sup-', [status(thm)], ['86', '87'])).
% 0.84/1.06  thf('89', plain, ((l1_pre_topc @ sk_A)),
% 0.84/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.06  thf('90', plain,
% 0.84/1.06      (((r2_hidden @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_A))
% 0.84/1.06        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_B) @ sk_A))),
% 0.84/1.06      inference('demod', [status(thm)], ['88', '89'])).
% 0.84/1.06  thf('91', plain,
% 0.84/1.06      (((r2_hidden @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_A)))
% 0.84/1.06         <= (((v1_tsep_1 @ sk_B @ sk_A)))),
% 0.84/1.06      inference('sup-', [status(thm)], ['85', '90'])).
% 0.84/1.06  thf('92', plain,
% 0.84/1.06      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.84/1.06        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.84/1.06      inference('sup-', [status(thm)], ['39', '40'])).
% 0.84/1.06  thf(t103_tmap_1, axiom,
% 0.84/1.06    (![A:$i]:
% 0.84/1.06     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.84/1.06       ( ![B:$i]:
% 0.84/1.06         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.84/1.06           ( ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) <=>
% 0.84/1.06             ( ( u1_pre_topc @ A ) = ( k5_tmap_1 @ A @ B ) ) ) ) ) ))).
% 0.84/1.06  thf('93', plain,
% 0.84/1.06      (![X29 : $i, X30 : $i]:
% 0.84/1.06         (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X30)))
% 0.84/1.06          | ~ (r2_hidden @ X29 @ (u1_pre_topc @ X30))
% 0.84/1.06          | ((u1_pre_topc @ X30) = (k5_tmap_1 @ X30 @ X29))
% 0.84/1.06          | ~ (l1_pre_topc @ X30)
% 0.84/1.06          | ~ (v2_pre_topc @ X30)
% 0.84/1.06          | (v2_struct_0 @ X30))),
% 0.84/1.06      inference('cnf', [status(esa)], [t103_tmap_1])).
% 0.84/1.06  thf('94', plain,
% 0.84/1.06      (((v2_struct_0 @ sk_A)
% 0.84/1.06        | ~ (v2_pre_topc @ sk_A)
% 0.84/1.06        | ~ (l1_pre_topc @ sk_A)
% 0.84/1.06        | ((u1_pre_topc @ sk_A) = (k5_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 0.84/1.06        | ~ (r2_hidden @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_A)))),
% 0.84/1.06      inference('sup-', [status(thm)], ['92', '93'])).
% 0.84/1.06  thf('95', plain, ((v2_pre_topc @ sk_A)),
% 0.84/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.06  thf('96', plain, ((l1_pre_topc @ sk_A)),
% 0.84/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.06  thf('97', plain,
% 0.84/1.06      (((v2_struct_0 @ sk_A)
% 0.84/1.06        | ((u1_pre_topc @ sk_A) = (k5_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 0.84/1.06        | ~ (r2_hidden @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_A)))),
% 0.84/1.06      inference('demod', [status(thm)], ['94', '95', '96'])).
% 0.84/1.06  thf('98', plain, (~ (v2_struct_0 @ sk_A)),
% 0.84/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.06  thf('99', plain,
% 0.84/1.06      ((~ (r2_hidden @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_A))
% 0.84/1.06        | ((u1_pre_topc @ sk_A) = (k5_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B))))),
% 0.84/1.06      inference('clc', [status(thm)], ['97', '98'])).
% 0.84/1.06  thf('100', plain,
% 0.84/1.06      ((((u1_pre_topc @ sk_A) = (k5_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B))))
% 0.84/1.06         <= (((v1_tsep_1 @ sk_B @ sk_A)))),
% 0.84/1.06      inference('sup-', [status(thm)], ['91', '99'])).
% 0.84/1.06  thf('101', plain,
% 0.84/1.06      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.84/1.06        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.84/1.06      inference('sup-', [status(thm)], ['39', '40'])).
% 0.84/1.06  thf(d9_tmap_1, axiom,
% 0.84/1.06    (![A:$i]:
% 0.84/1.06     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.84/1.06       ( ![B:$i]:
% 0.84/1.06         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.84/1.06           ( ( k6_tmap_1 @ A @ B ) =
% 0.84/1.06             ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( k5_tmap_1 @ A @ B ) ) ) ) ) ))).
% 0.84/1.06  thf('102', plain,
% 0.84/1.06      (![X23 : $i, X24 : $i]:
% 0.84/1.06         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 0.84/1.06          | ((k6_tmap_1 @ X24 @ X23)
% 0.84/1.06              = (g1_pre_topc @ (u1_struct_0 @ X24) @ (k5_tmap_1 @ X24 @ X23)))
% 0.84/1.06          | ~ (l1_pre_topc @ X24)
% 0.84/1.06          | ~ (v2_pre_topc @ X24)
% 0.84/1.06          | (v2_struct_0 @ X24))),
% 0.84/1.06      inference('cnf', [status(esa)], [d9_tmap_1])).
% 0.84/1.06  thf('103', plain,
% 0.84/1.06      (((v2_struct_0 @ sk_A)
% 0.84/1.06        | ~ (v2_pre_topc @ sk_A)
% 0.84/1.06        | ~ (l1_pre_topc @ sk_A)
% 0.84/1.06        | ((k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B))
% 0.84/1.06            = (g1_pre_topc @ (u1_struct_0 @ sk_A) @ 
% 0.84/1.06               (k5_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))))),
% 0.84/1.06      inference('sup-', [status(thm)], ['101', '102'])).
% 0.84/1.06  thf('104', plain, ((v2_pre_topc @ sk_A)),
% 0.84/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.06  thf('105', plain, ((l1_pre_topc @ sk_A)),
% 0.84/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.06  thf('106', plain,
% 0.84/1.06      (((v2_struct_0 @ sk_A)
% 0.84/1.06        | ((k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B))
% 0.84/1.06            = (g1_pre_topc @ (u1_struct_0 @ sk_A) @ 
% 0.84/1.06               (k5_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))))),
% 0.84/1.06      inference('demod', [status(thm)], ['103', '104', '105'])).
% 0.84/1.06  thf('107', plain, (~ (v2_struct_0 @ sk_A)),
% 0.84/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.06  thf('108', plain,
% 0.84/1.06      (((k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B))
% 0.84/1.06         = (g1_pre_topc @ (u1_struct_0 @ sk_A) @ 
% 0.84/1.06            (k5_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B))))),
% 0.84/1.06      inference('clc', [status(thm)], ['106', '107'])).
% 0.84/1.06  thf('109', plain,
% 0.84/1.06      ((((k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B))
% 0.84/1.06          = (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))
% 0.84/1.06         <= (((v1_tsep_1 @ sk_B @ sk_A)))),
% 0.84/1.06      inference('sup+', [status(thm)], ['100', '108'])).
% 0.84/1.06  thf('110', plain,
% 0.84/1.06      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.84/1.06          != (k8_tmap_1 @ sk_A @ sk_B)))
% 0.84/1.06         <= (~
% 0.84/1.06             (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.84/1.06                = (k8_tmap_1 @ sk_A @ sk_B))))),
% 0.84/1.06      inference('split', [status(esa)], ['5'])).
% 0.84/1.06  thf('111', plain,
% 0.84/1.06      ((((k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)) != (k8_tmap_1 @ sk_A @ sk_B)))
% 0.84/1.06         <= (~
% 0.84/1.06             (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.84/1.06                = (k8_tmap_1 @ sk_A @ sk_B))) & 
% 0.84/1.06             ((v1_tsep_1 @ sk_B @ sk_A)))),
% 0.84/1.06      inference('sup-', [status(thm)], ['109', '110'])).
% 0.84/1.06  thf('112', plain,
% 0.84/1.06      ((((k8_tmap_1 @ sk_A @ sk_B) != (k8_tmap_1 @ sk_A @ sk_B)))
% 0.84/1.06         <= (~
% 0.84/1.06             (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.84/1.06                = (k8_tmap_1 @ sk_A @ sk_B))) & 
% 0.84/1.06             ((v1_tsep_1 @ sk_B @ sk_A)))),
% 0.84/1.06      inference('sup-', [status(thm)], ['75', '111'])).
% 0.84/1.06  thf('113', plain,
% 0.84/1.06      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.84/1.06          = (k8_tmap_1 @ sk_A @ sk_B))) | 
% 0.84/1.06       ~ ((v1_tsep_1 @ sk_B @ sk_A))),
% 0.84/1.06      inference('simplify', [status(thm)], ['112'])).
% 0.84/1.06  thf('114', plain, (~ ((v1_tsep_1 @ sk_B @ sk_A))),
% 0.84/1.06      inference('sat_resolution*', [status(thm)], ['31', '34', '113'])).
% 0.84/1.06  thf('115', plain,
% 0.84/1.06      (~ (r2_hidden @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_A))),
% 0.84/1.06      inference('simpl_trail', [status(thm)], ['30', '114'])).
% 0.84/1.06  thf('116', plain,
% 0.84/1.06      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.84/1.06        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.84/1.06      inference('sup-', [status(thm)], ['39', '40'])).
% 0.84/1.06  thf(t102_tmap_1, axiom,
% 0.84/1.06    (![A:$i]:
% 0.84/1.06     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.84/1.06       ( ![B:$i]:
% 0.84/1.06         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.84/1.06           ( r2_hidden @ B @ ( k5_tmap_1 @ A @ B ) ) ) ) ))).
% 0.84/1.06  thf('117', plain,
% 0.84/1.06      (![X27 : $i, X28 : $i]:
% 0.84/1.06         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 0.84/1.06          | (r2_hidden @ X27 @ (k5_tmap_1 @ X28 @ X27))
% 0.84/1.06          | ~ (l1_pre_topc @ X28)
% 0.84/1.06          | ~ (v2_pre_topc @ X28)
% 0.84/1.06          | (v2_struct_0 @ X28))),
% 0.84/1.06      inference('cnf', [status(esa)], [t102_tmap_1])).
% 0.84/1.06  thf('118', plain,
% 0.84/1.06      (((v2_struct_0 @ sk_A)
% 0.84/1.06        | ~ (v2_pre_topc @ sk_A)
% 0.84/1.06        | ~ (l1_pre_topc @ sk_A)
% 0.84/1.06        | (r2_hidden @ (u1_struct_0 @ sk_B) @ 
% 0.84/1.06           (k5_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B))))),
% 0.84/1.06      inference('sup-', [status(thm)], ['116', '117'])).
% 0.84/1.06  thf('119', plain, ((v2_pre_topc @ sk_A)),
% 0.84/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.06  thf('120', plain, ((l1_pre_topc @ sk_A)),
% 0.84/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.06  thf('121', plain,
% 0.84/1.06      (((v2_struct_0 @ sk_A)
% 0.84/1.06        | (r2_hidden @ (u1_struct_0 @ sk_B) @ 
% 0.84/1.06           (k5_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B))))),
% 0.84/1.06      inference('demod', [status(thm)], ['118', '119', '120'])).
% 0.84/1.06  thf('122', plain, (~ (v2_struct_0 @ sk_A)),
% 0.84/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.06  thf('123', plain,
% 0.84/1.06      ((r2_hidden @ (u1_struct_0 @ sk_B) @ 
% 0.84/1.06        (k5_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))),
% 0.84/1.06      inference('clc', [status(thm)], ['121', '122'])).
% 0.84/1.06  thf('124', plain,
% 0.84/1.06      (((k8_tmap_1 @ sk_A @ sk_B) = (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))),
% 0.84/1.06      inference('clc', [status(thm)], ['73', '74'])).
% 0.84/1.06  thf('125', plain,
% 0.84/1.06      (((k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B))
% 0.84/1.06         = (g1_pre_topc @ (u1_struct_0 @ sk_A) @ 
% 0.84/1.06            (k5_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B))))),
% 0.84/1.06      inference('clc', [status(thm)], ['106', '107'])).
% 0.84/1.06  thf('126', plain,
% 0.84/1.06      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.84/1.06          = (k8_tmap_1 @ sk_A @ sk_B)))
% 0.84/1.06         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.84/1.06                = (k8_tmap_1 @ sk_A @ sk_B))))),
% 0.84/1.06      inference('split', [status(esa)], ['76'])).
% 0.84/1.06  thf(dt_u1_pre_topc, axiom,
% 0.84/1.06    (![A:$i]:
% 0.84/1.06     ( ( l1_pre_topc @ A ) =>
% 0.84/1.06       ( m1_subset_1 @
% 0.84/1.06         ( u1_pre_topc @ A ) @ 
% 0.84/1.06         ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ))).
% 0.84/1.06  thf('127', plain,
% 0.84/1.06      (![X8 : $i]:
% 0.84/1.06         ((m1_subset_1 @ (u1_pre_topc @ X8) @ 
% 0.84/1.06           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X8))))
% 0.84/1.06          | ~ (l1_pre_topc @ X8))),
% 0.84/1.06      inference('cnf', [status(esa)], [dt_u1_pre_topc])).
% 0.84/1.06  thf(free_g1_pre_topc, axiom,
% 0.84/1.06    (![A:$i,B:$i]:
% 0.84/1.06     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.84/1.06       ( ![C:$i,D:$i]:
% 0.84/1.06         ( ( ( g1_pre_topc @ A @ B ) = ( g1_pre_topc @ C @ D ) ) =>
% 0.84/1.06           ( ( ( A ) = ( C ) ) & ( ( B ) = ( D ) ) ) ) ) ))).
% 0.84/1.06  thf('128', plain,
% 0.84/1.06      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.84/1.06         (((g1_pre_topc @ X12 @ X13) != (g1_pre_topc @ X10 @ X11))
% 0.84/1.06          | ((X13) = (X11))
% 0.84/1.06          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X12))))),
% 0.84/1.06      inference('cnf', [status(esa)], [free_g1_pre_topc])).
% 0.84/1.06  thf('129', plain,
% 0.84/1.06      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.84/1.06         (~ (l1_pre_topc @ X0)
% 0.84/1.06          | ((u1_pre_topc @ X0) = (X1))
% 0.84/1.06          | ((g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))
% 0.84/1.06              != (g1_pre_topc @ X2 @ X1)))),
% 0.84/1.06      inference('sup-', [status(thm)], ['127', '128'])).
% 0.84/1.06  thf('130', plain,
% 0.84/1.06      ((![X0 : $i, X1 : $i]:
% 0.84/1.06          (((k8_tmap_1 @ sk_A @ sk_B) != (g1_pre_topc @ X1 @ X0))
% 0.84/1.06           | ((u1_pre_topc @ sk_A) = (X0))
% 0.84/1.06           | ~ (l1_pre_topc @ sk_A)))
% 0.84/1.06         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.84/1.06                = (k8_tmap_1 @ sk_A @ sk_B))))),
% 0.84/1.06      inference('sup-', [status(thm)], ['126', '129'])).
% 0.84/1.06  thf('131', plain, ((l1_pre_topc @ sk_A)),
% 0.84/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.06  thf('132', plain,
% 0.84/1.06      ((![X0 : $i, X1 : $i]:
% 0.84/1.06          (((k8_tmap_1 @ sk_A @ sk_B) != (g1_pre_topc @ X1 @ X0))
% 0.84/1.06           | ((u1_pre_topc @ sk_A) = (X0))))
% 0.84/1.06         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.84/1.06                = (k8_tmap_1 @ sk_A @ sk_B))))),
% 0.84/1.06      inference('demod', [status(thm)], ['130', '131'])).
% 0.84/1.06  thf('133', plain,
% 0.84/1.06      (((((k8_tmap_1 @ sk_A @ sk_B)
% 0.84/1.06           != (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 0.84/1.06         | ((u1_pre_topc @ sk_A) = (k5_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))))
% 0.84/1.06         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.84/1.06                = (k8_tmap_1 @ sk_A @ sk_B))))),
% 0.84/1.06      inference('sup-', [status(thm)], ['125', '132'])).
% 0.84/1.06  thf('134', plain,
% 0.84/1.06      (((((k8_tmap_1 @ sk_A @ sk_B) != (k8_tmap_1 @ sk_A @ sk_B))
% 0.84/1.06         | ((u1_pre_topc @ sk_A) = (k5_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))))
% 0.84/1.06         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.84/1.06                = (k8_tmap_1 @ sk_A @ sk_B))))),
% 0.84/1.06      inference('sup-', [status(thm)], ['124', '133'])).
% 0.84/1.06  thf('135', plain,
% 0.84/1.06      ((((u1_pre_topc @ sk_A) = (k5_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B))))
% 0.84/1.06         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.84/1.06                = (k8_tmap_1 @ sk_A @ sk_B))))),
% 0.84/1.06      inference('simplify', [status(thm)], ['134'])).
% 0.84/1.06  thf('136', plain,
% 0.84/1.06      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.84/1.06          = (k8_tmap_1 @ sk_A @ sk_B))) | 
% 0.84/1.06       ((v1_tsep_1 @ sk_B @ sk_A))),
% 0.84/1.06      inference('split', [status(esa)], ['76'])).
% 0.84/1.06  thf('137', plain,
% 0.84/1.06      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.84/1.06          = (k8_tmap_1 @ sk_A @ sk_B)))),
% 0.84/1.06      inference('sat_resolution*', [status(thm)], ['31', '34', '113', '136'])).
% 0.84/1.06  thf('138', plain,
% 0.84/1.06      (((u1_pre_topc @ sk_A) = (k5_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))),
% 0.84/1.06      inference('simpl_trail', [status(thm)], ['135', '137'])).
% 0.84/1.06  thf('139', plain,
% 0.84/1.06      ((r2_hidden @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_A))),
% 0.84/1.06      inference('demod', [status(thm)], ['123', '138'])).
% 0.84/1.06  thf('140', plain, ($false), inference('demod', [status(thm)], ['115', '139'])).
% 0.84/1.06  
% 0.84/1.06  % SZS output end Refutation
% 0.84/1.06  
% 0.84/1.07  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
