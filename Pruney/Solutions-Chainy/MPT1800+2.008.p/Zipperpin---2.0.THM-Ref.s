%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.NHo6HU1iDS

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:10:56 EST 2020

% Result     : Theorem 0.59s
% Output     : Refutation 0.59s
% Verified   : 
% Statistics : Number of formulae       :  234 (1245 expanded)
%              Number of leaves         :   35 ( 353 expanded)
%              Depth                    :   22
%              Number of atoms          : 2067 (19243 expanded)
%              Number of equality atoms :   92 ( 782 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(g1_pre_topc_type,type,(
    g1_pre_topc: $i > $i > $i )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k8_tmap_1_type,type,(
    k8_tmap_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(v1_tsep_1_type,type,(
    v1_tsep_1: $i > $i > $o )).

thf(k5_tmap_1_type,type,(
    k5_tmap_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

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
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,
    ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k8_tmap_1 @ sk_A @ sk_B ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['1'])).

thf('3',plain,
    ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
     != ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( m1_pre_topc @ sk_B @ sk_A )
    | ~ ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ~ ( v1_tsep_1 @ sk_B @ sk_A )
    | ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
     != ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['3'])).

thf('5',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ~ ( m1_pre_topc @ sk_B @ sk_A )
   <= ~ ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['3'])).

thf('7',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t1_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( m1_subset_1 @ ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('9',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( m1_pre_topc @ X18 @ X19 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X18 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( l1_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('10',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['10','11'])).

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

thf('13',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( v2_struct_0 @ X15 )
      | ~ ( m1_pre_topc @ X15 @ X16 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ( ( u1_pre_topc @ ( k8_tmap_1 @ X16 @ X15 ) )
        = ( k5_tmap_1 @ X16 @ X17 ) )
      | ( X17
       != ( u1_struct_0 @ X15 ) )
      | ~ ( l1_pre_topc @ X16 )
      | ~ ( v2_pre_topc @ X16 )
      | ( v2_struct_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t114_tmap_1])).

thf('14',plain,(
    ! [X15: $i,X16: $i] :
      ( ( v2_struct_0 @ X16 )
      | ~ ( v2_pre_topc @ X16 )
      | ~ ( l1_pre_topc @ X16 )
      | ( ( u1_pre_topc @ ( k8_tmap_1 @ X16 @ X15 ) )
        = ( k5_tmap_1 @ X16 @ ( u1_struct_0 @ X15 ) ) )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X15 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( m1_pre_topc @ X15 @ X16 )
      | ( v2_struct_0 @ X15 ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,
    ( ( v2_struct_0 @ sk_B )
    | ~ ( m1_pre_topc @ sk_B @ sk_A )
    | ( ( u1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
      = ( k5_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['12','14'])).

thf('16',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( u1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
      = ( k5_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['15','16','17','18'])).

thf('20',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( u1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
      = ( k5_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['19','20'])).

thf('22',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ( u1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    = ( k5_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['21','22'])).

thf('24',plain,
    ( ( v1_tsep_1 @ sk_B @ sk_A )
   <= ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['1'])).

thf('25',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['10','11'])).

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

thf('26',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( m1_pre_topc @ X8 @ X9 )
      | ~ ( v1_tsep_1 @ X8 @ X9 )
      | ( X10
       != ( u1_struct_0 @ X8 ) )
      | ( v3_pre_topc @ X10 @ X9 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[d1_tsep_1])).

thf('27',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( l1_pre_topc @ X9 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X8 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ( v3_pre_topc @ ( u1_struct_0 @ X8 ) @ X9 )
      | ~ ( v1_tsep_1 @ X8 @ X9 )
      | ~ ( m1_pre_topc @ X8 @ X9 ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,
    ( ~ ( m1_pre_topc @ sk_B @ sk_A )
    | ~ ( v1_tsep_1 @ sk_B @ sk_A )
    | ( v3_pre_topc @ ( u1_struct_0 @ sk_B ) @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['25','27'])).

thf('29',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ~ ( v1_tsep_1 @ sk_B @ sk_A )
    | ( v3_pre_topc @ ( u1_struct_0 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['28','29','30'])).

thf('32',plain,
    ( ( v3_pre_topc @ ( u1_struct_0 @ sk_B ) @ sk_A )
   <= ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['24','31'])).

thf('33',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf(d5_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v3_pre_topc @ B @ A )
          <=> ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) ) ) ) )).

thf('34',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) )
      | ~ ( v3_pre_topc @ X4 @ X5 )
      | ( r2_hidden @ X4 @ ( u1_pre_topc @ X5 ) )
      | ~ ( l1_pre_topc @ X5 ) ) ),
    inference(cnf,[status(esa)],[d5_pre_topc])).

thf('35',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r2_hidden @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_A ) )
    | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ( r2_hidden @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_A ) )
    | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,
    ( ( r2_hidden @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_A ) )
   <= ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['32','37'])).

thf('39',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['10','11'])).

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

thf('40',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( r2_hidden @ X13 @ ( u1_pre_topc @ X14 ) )
      | ( ( u1_pre_topc @ X14 )
        = ( k5_tmap_1 @ X14 @ X13 ) )
      | ~ ( l1_pre_topc @ X14 )
      | ~ ( v2_pre_topc @ X14 )
      | ( v2_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t103_tmap_1])).

thf('41',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( ( u1_pre_topc @ sk_A )
      = ( k5_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
    | ~ ( r2_hidden @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( u1_pre_topc @ sk_A )
      = ( k5_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
    | ~ ( r2_hidden @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_A ) ) ),
    inference(demod,[status(thm)],['41','42','43'])).

thf('45',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( ~ ( r2_hidden @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_A ) )
    | ( ( u1_pre_topc @ sk_A )
      = ( k5_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['44','45'])).

thf('47',plain,
    ( ( ( u1_pre_topc @ sk_A )
      = ( k5_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
   <= ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['38','46'])).

thf('48',plain,
    ( ( ( u1_pre_topc @ sk_A )
      = ( u1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) ) )
   <= ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['23','47'])).

thf('49',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    ! [X15: $i,X16: $i] :
      ( ( v2_struct_0 @ X15 )
      | ~ ( m1_pre_topc @ X15 @ X16 )
      | ( ( u1_struct_0 @ ( k8_tmap_1 @ X16 @ X15 ) )
        = ( u1_struct_0 @ X16 ) )
      | ~ ( l1_pre_topc @ X16 )
      | ~ ( v2_pre_topc @ X16 )
      | ( v2_struct_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t114_tmap_1])).

thf('51',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
      = ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
      = ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['51','52','53'])).

thf('55',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['54','55'])).

thf('57',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,
    ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['56','57'])).

thf(abstractness_v1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( ( v1_pre_topc @ A )
       => ( A
          = ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ) )).

thf('59',plain,(
    ! [X2: $i] :
      ( ~ ( v1_pre_topc @ X2 )
      | ( X2
        = ( g1_pre_topc @ ( u1_struct_0 @ X2 ) @ ( u1_pre_topc @ X2 ) ) )
      | ~ ( l1_pre_topc @ X2 ) ) ),
    inference(cnf,[status(esa)],[abstractness_v1_pre_topc])).

thf('60',plain,
    ( ( ( k8_tmap_1 @ sk_A @ sk_B )
      = ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) )
    | ~ ( l1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( v1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['58','59'])).

thf('61',plain,(
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

thf('62',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( l1_pre_topc @ X11 )
      | ~ ( v2_pre_topc @ X11 )
      | ( v2_struct_0 @ X11 )
      | ~ ( m1_pre_topc @ X12 @ X11 )
      | ( l1_pre_topc @ ( k8_tmap_1 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k8_tmap_1])).

thf('63',plain,
    ( ( l1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,
    ( ( l1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['63','64','65'])).

thf('67',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    l1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['66','67'])).

thf('69',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( l1_pre_topc @ X11 )
      | ~ ( v2_pre_topc @ X11 )
      | ( v2_struct_0 @ X11 )
      | ~ ( m1_pre_topc @ X12 @ X11 )
      | ( v1_pre_topc @ ( k8_tmap_1 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k8_tmap_1])).

thf('71',plain,
    ( ( v1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,
    ( ( v1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['71','72','73'])).

thf('75',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    v1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['74','75'])).

thf('77',plain,
    ( ( k8_tmap_1 @ sk_A @ sk_B )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['60','68','76'])).

thf('78',plain,
    ( ( ( k8_tmap_1 @ sk_A @ sk_B )
      = ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
   <= ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['48','77'])).

thf('79',plain,
    ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
     != ( k8_tmap_1 @ sk_A @ sk_B ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
     != ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['3'])).

thf('80',plain,
    ( ( ( k8_tmap_1 @ sk_A @ sk_B )
     != ( k8_tmap_1 @ sk_A @ sk_B ) )
   <= ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
       != ( k8_tmap_1 @ sk_A @ sk_B ) )
      & ( v1_tsep_1 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,
    ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['80'])).

thf('82',plain,
    ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['1'])).

thf('83',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
    = ( k8_tmap_1 @ sk_A @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['4','7','81','82'])).

thf('84',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
    = ( k8_tmap_1 @ sk_A @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['2','83'])).

thf(fc10_tops_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( v3_pre_topc @ ( k2_struct_0 @ A ) @ A ) ) )).

thf('85',plain,(
    ! [X7: $i] :
      ( ( v3_pre_topc @ ( k2_struct_0 @ X7 ) @ X7 )
      | ~ ( l1_pre_topc @ X7 )
      | ~ ( v2_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[fc10_tops_1])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('86',plain,(
    ! [X3: $i] :
      ( ( ( k2_struct_0 @ X3 )
        = ( u1_struct_0 @ X3 ) )
      | ~ ( l1_struct_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('87',plain,(
    ! [X1: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X1 ) @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('88',plain,(
    ! [X0: $i] :
      ( ( k2_subset_1 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('89',plain,(
    ! [X1: $i] :
      ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) )
      | ~ ( v3_pre_topc @ X4 @ X5 )
      | ( r2_hidden @ X4 @ ( u1_pre_topc @ X5 ) )
      | ~ ( l1_pre_topc @ X5 ) ) ),
    inference(cnf,[status(esa)],[d5_pre_topc])).

thf('91',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( r2_hidden @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X0: $i] :
      ( ~ ( v3_pre_topc @ ( k2_struct_0 @ X0 ) @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( r2_hidden @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['86','91'])).

thf('93',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( r2_hidden @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['85','92'])).

thf('94',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( r2_hidden @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['93'])).

thf('95',plain,(
    ! [X1: $i] :
      ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['87','88'])).

thf('96',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( r2_hidden @ X13 @ ( u1_pre_topc @ X14 ) )
      | ( ( u1_pre_topc @ X14 )
        = ( k5_tmap_1 @ X14 @ X13 ) )
      | ~ ( l1_pre_topc @ X14 )
      | ~ ( v2_pre_topc @ X14 )
      | ( v2_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t103_tmap_1])).

thf('97',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( u1_pre_topc @ X0 )
        = ( k5_tmap_1 @ X0 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( r2_hidden @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( ( u1_pre_topc @ X0 )
        = ( k5_tmap_1 @ X0 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['94','97'])).

thf('99',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ( ( u1_pre_topc @ X0 )
        = ( k5_tmap_1 @ X0 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['98'])).

thf(t2_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( m1_pre_topc @ A @ A ) ) )).

thf('100',plain,(
    ! [X20: $i] :
      ( ( m1_pre_topc @ X20 @ X20 )
      | ~ ( l1_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('101',plain,(
    ! [X1: $i] :
      ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['87','88'])).

thf('102',plain,(
    ! [X15: $i,X16: $i] :
      ( ( v2_struct_0 @ X16 )
      | ~ ( v2_pre_topc @ X16 )
      | ~ ( l1_pre_topc @ X16 )
      | ( ( u1_pre_topc @ ( k8_tmap_1 @ X16 @ X15 ) )
        = ( k5_tmap_1 @ X16 @ ( u1_struct_0 @ X15 ) ) )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X15 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( m1_pre_topc @ X15 @ X16 )
      | ( v2_struct_0 @ X15 ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('103',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X0 )
      | ( ( u1_pre_topc @ ( k8_tmap_1 @ X0 @ X0 ) )
        = ( k5_tmap_1 @ X0 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( u1_pre_topc @ ( k8_tmap_1 @ X0 @ X0 ) )
        = ( k5_tmap_1 @ X0 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['103'])).

thf('105',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( ( u1_pre_topc @ ( k8_tmap_1 @ X0 @ X0 ) )
        = ( k5_tmap_1 @ X0 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['100','104'])).

thf('106',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ( ( u1_pre_topc @ ( k8_tmap_1 @ X0 @ X0 ) )
        = ( k5_tmap_1 @ X0 @ ( u1_struct_0 @ X0 ) ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['105'])).

thf('107',plain,(
    ! [X0: $i] :
      ( ( ( u1_pre_topc @ ( k8_tmap_1 @ X0 @ X0 ) )
        = ( u1_pre_topc @ X0 ) )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference('sup+',[status(thm)],['99','106'])).

thf('108',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( ( u1_pre_topc @ ( k8_tmap_1 @ X0 @ X0 ) )
        = ( u1_pre_topc @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['107'])).

thf('109',plain,(
    ! [X20: $i] :
      ( ( m1_pre_topc @ X20 @ X20 )
      | ~ ( l1_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('110',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( l1_pre_topc @ X11 )
      | ~ ( v2_pre_topc @ X11 )
      | ( v2_struct_0 @ X11 )
      | ~ ( m1_pre_topc @ X12 @ X11 )
      | ( v1_pre_topc @ ( k8_tmap_1 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k8_tmap_1])).

thf('111',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v1_pre_topc @ ( k8_tmap_1 @ X0 @ X0 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['109','110'])).

thf('112',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( v1_pre_topc @ ( k8_tmap_1 @ X0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['111'])).

thf('113',plain,(
    ! [X20: $i] :
      ( ( m1_pre_topc @ X20 @ X20 )
      | ~ ( l1_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('114',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( l1_pre_topc @ X11 )
      | ~ ( v2_pre_topc @ X11 )
      | ( v2_struct_0 @ X11 )
      | ~ ( m1_pre_topc @ X12 @ X11 )
      | ( l1_pre_topc @ ( k8_tmap_1 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k8_tmap_1])).

thf('115',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( l1_pre_topc @ ( k8_tmap_1 @ X0 @ X0 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['113','114'])).

thf('116',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( l1_pre_topc @ ( k8_tmap_1 @ X0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['115'])).

thf('117',plain,(
    ! [X20: $i] :
      ( ( m1_pre_topc @ X20 @ X20 )
      | ~ ( l1_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('118',plain,(
    ! [X15: $i,X16: $i] :
      ( ( v2_struct_0 @ X15 )
      | ~ ( m1_pre_topc @ X15 @ X16 )
      | ( ( u1_struct_0 @ ( k8_tmap_1 @ X16 @ X15 ) )
        = ( u1_struct_0 @ X16 ) )
      | ~ ( l1_pre_topc @ X16 )
      | ~ ( v2_pre_topc @ X16 )
      | ( v2_struct_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t114_tmap_1])).

thf('119',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( u1_struct_0 @ ( k8_tmap_1 @ X0 @ X0 ) )
        = ( u1_struct_0 @ X0 ) )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['117','118'])).

thf('120',plain,(
    ! [X0: $i] :
      ( ( ( u1_struct_0 @ ( k8_tmap_1 @ X0 @ X0 ) )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['119'])).

thf('121',plain,(
    ! [X2: $i] :
      ( ~ ( v1_pre_topc @ X2 )
      | ( X2
        = ( g1_pre_topc @ ( u1_struct_0 @ X2 ) @ ( u1_pre_topc @ X2 ) ) )
      | ~ ( l1_pre_topc @ X2 ) ) ),
    inference(cnf,[status(esa)],[abstractness_v1_pre_topc])).

thf('122',plain,(
    ! [X0: $i] :
      ( ( ( k8_tmap_1 @ X0 @ X0 )
        = ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ ( k8_tmap_1 @ X0 @ X0 ) ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ ( k8_tmap_1 @ X0 @ X0 ) )
      | ~ ( v1_pre_topc @ ( k8_tmap_1 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['120','121'])).

thf('123',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( v1_pre_topc @ ( k8_tmap_1 @ X0 @ X0 ) )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( k8_tmap_1 @ X0 @ X0 )
        = ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ ( k8_tmap_1 @ X0 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['116','122'])).

thf('124',plain,(
    ! [X0: $i] :
      ( ( ( k8_tmap_1 @ X0 @ X0 )
        = ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ ( k8_tmap_1 @ X0 @ X0 ) ) ) )
      | ~ ( v1_pre_topc @ ( k8_tmap_1 @ X0 @ X0 ) )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['123'])).

thf('125',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( ( k8_tmap_1 @ X0 @ X0 )
        = ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ ( k8_tmap_1 @ X0 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['112','124'])).

thf('126',plain,(
    ! [X0: $i] :
      ( ( ( k8_tmap_1 @ X0 @ X0 )
        = ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ ( k8_tmap_1 @ X0 @ X0 ) ) ) )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['125'])).

thf('127',plain,(
    ! [X0: $i] :
      ( ( ( k8_tmap_1 @ X0 @ X0 )
        = ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference('sup+',[status(thm)],['108','126'])).

thf('128',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( ( k8_tmap_1 @ X0 @ X0 )
        = ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['127'])).

thf('129',plain,
    ( ( ( k8_tmap_1 @ sk_A @ sk_A )
      = ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( l1_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['84','128'])).

thf('130',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('131',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('132',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('133',plain,(
    ! [X6: $i] :
      ( ( l1_struct_0 @ X6 )
      | ~ ( l1_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('134',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['132','133'])).

thf('135',plain,
    ( ( ( k8_tmap_1 @ sk_A @ sk_A )
      = ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['129','130','131','134'])).

thf('136',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('137',plain,
    ( ( k8_tmap_1 @ sk_A @ sk_A )
    = ( k8_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['135','136'])).

thf('138',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( ( u1_pre_topc @ ( k8_tmap_1 @ X0 @ X0 ) )
        = ( u1_pre_topc @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['107'])).

thf('139',plain,
    ( ( ( u1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
      = ( u1_pre_topc @ sk_A ) )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( l1_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['137','138'])).

thf('140',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('141',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('142',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['132','133'])).

thf('143',plain,
    ( ( ( u1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
      = ( u1_pre_topc @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['139','140','141','142'])).

thf('144',plain,(
    ! [X3: $i] :
      ( ( ( k2_struct_0 @ X3 )
        = ( u1_struct_0 @ X3 ) )
      | ~ ( l1_struct_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('145',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('146',plain,
    ( ( m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['144','145'])).

thf('147',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['132','133'])).

thf('148',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['146','147'])).

thf('149',plain,(
    ! [X3: $i] :
      ( ( ( k2_struct_0 @ X3 )
        = ( u1_struct_0 @ X3 ) )
      | ~ ( l1_struct_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('150',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ( ( u1_pre_topc @ X14 )
       != ( k5_tmap_1 @ X14 @ X13 ) )
      | ( r2_hidden @ X13 @ ( u1_pre_topc @ X14 ) )
      | ~ ( l1_pre_topc @ X14 )
      | ~ ( v2_pre_topc @ X14 )
      | ( v2_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t103_tmap_1])).

thf('151',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ X0 ) ) )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( r2_hidden @ X1 @ ( u1_pre_topc @ X0 ) )
      | ( ( u1_pre_topc @ X0 )
       != ( k5_tmap_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['149','150'])).

thf('152',plain,
    ( ( ( u1_pre_topc @ sk_A )
     != ( k5_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
    | ( r2_hidden @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_A ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['148','151'])).

thf('153',plain,
    ( ( u1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    = ( k5_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['21','22'])).

thf('154',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('155',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('156',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['132','133'])).

thf('157',plain,
    ( ( ( u1_pre_topc @ sk_A )
     != ( u1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) ) )
    | ( r2_hidden @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['152','153','154','155','156'])).

thf('158',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('159',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( m1_pre_topc @ X8 @ X9 )
      | ( m1_subset_1 @ ( sk_C @ X8 @ X9 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ( v1_tsep_1 @ X8 @ X9 )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[d1_tsep_1])).

thf('160',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v1_tsep_1 @ sk_B @ sk_A )
    | ( m1_subset_1 @ ( sk_C @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['158','159'])).

thf('161',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('162',plain,
    ( ( v1_tsep_1 @ sk_B @ sk_A )
    | ( m1_subset_1 @ ( sk_C @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['160','161'])).

thf('163',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) )
      | ~ ( r2_hidden @ X4 @ ( u1_pre_topc @ X5 ) )
      | ( v3_pre_topc @ X4 @ X5 )
      | ~ ( l1_pre_topc @ X5 ) ) ),
    inference(cnf,[status(esa)],[d5_pre_topc])).

thf('164',plain,
    ( ( v1_tsep_1 @ sk_B @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v3_pre_topc @ ( sk_C @ sk_B @ sk_A ) @ sk_A )
    | ~ ( r2_hidden @ ( sk_C @ sk_B @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['162','163'])).

thf('165',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('166',plain,
    ( ( v1_tsep_1 @ sk_B @ sk_A )
    | ( v3_pre_topc @ ( sk_C @ sk_B @ sk_A ) @ sk_A )
    | ~ ( r2_hidden @ ( sk_C @ sk_B @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ),
    inference(demod,[status(thm)],['164','165'])).

thf('167',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('168',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( m1_pre_topc @ X8 @ X9 )
      | ( ( sk_C @ X8 @ X9 )
        = ( u1_struct_0 @ X8 ) )
      | ( v1_tsep_1 @ X8 @ X9 )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[d1_tsep_1])).

thf('169',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v1_tsep_1 @ sk_B @ sk_A )
    | ( ( sk_C @ sk_B @ sk_A )
      = ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['167','168'])).

thf('170',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('171',plain,
    ( ( v1_tsep_1 @ sk_B @ sk_A )
    | ( ( sk_C @ sk_B @ sk_A )
      = ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['169','170'])).

thf('172',plain,
    ( ~ ( v1_tsep_1 @ sk_B @ sk_A )
   <= ~ ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['3'])).

thf('173',plain,
    ( ( ( sk_C @ sk_B @ sk_A )
      = ( u1_struct_0 @ sk_B ) )
   <= ~ ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['171','172'])).

thf('174',plain,(
    ~ ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['4','7','81'])).

thf('175',plain,
    ( ( sk_C @ sk_B @ sk_A )
    = ( u1_struct_0 @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['173','174'])).

thf('176',plain,
    ( ( sk_C @ sk_B @ sk_A )
    = ( u1_struct_0 @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['173','174'])).

thf('177',plain,
    ( ( v1_tsep_1 @ sk_B @ sk_A )
    | ( v3_pre_topc @ ( u1_struct_0 @ sk_B ) @ sk_A )
    | ~ ( r2_hidden @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_A ) ) ),
    inference(demod,[status(thm)],['166','175','176'])).

thf('178',plain,
    ( ~ ( v1_tsep_1 @ sk_B @ sk_A )
   <= ~ ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['3'])).

thf('179',plain,(
    ~ ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['4','7','81'])).

thf('180',plain,(
    ~ ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['178','179'])).

thf('181',plain,
    ( ~ ( r2_hidden @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_A ) )
    | ( v3_pre_topc @ ( u1_struct_0 @ sk_B ) @ sk_A ) ),
    inference(clc,[status(thm)],['177','180'])).

thf('182',plain,
    ( ( ( sk_C @ sk_B @ sk_A )
      = ( u1_struct_0 @ sk_B ) )
   <= ~ ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['171','172'])).

thf('183',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( m1_pre_topc @ X8 @ X9 )
      | ~ ( v3_pre_topc @ ( sk_C @ X8 @ X9 ) @ X9 )
      | ( v1_tsep_1 @ X8 @ X9 )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[d1_tsep_1])).

thf('184',plain,
    ( ( ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_B ) @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v1_tsep_1 @ sk_B @ sk_A )
      | ~ ( m1_pre_topc @ sk_B @ sk_A ) )
   <= ~ ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['182','183'])).

thf('185',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('186',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('187',plain,
    ( ( ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_B ) @ sk_A )
      | ( v1_tsep_1 @ sk_B @ sk_A ) )
   <= ~ ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['184','185','186'])).

thf('188',plain,
    ( ~ ( v1_tsep_1 @ sk_B @ sk_A )
   <= ~ ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['3'])).

thf('189',plain,
    ( ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_B ) @ sk_A )
   <= ~ ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['187','188'])).

thf('190',plain,(
    ~ ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['4','7','81'])).

thf('191',plain,(
    ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_B ) @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['189','190'])).

thf('192',plain,(
    ~ ( r2_hidden @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_A ) ) ),
    inference(clc,[status(thm)],['181','191'])).

thf('193',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( u1_pre_topc @ sk_A )
     != ( u1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['157','192'])).

thf('194',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('195',plain,(
    ( u1_pre_topc @ sk_A )
 != ( u1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['193','194'])).

thf('196',plain,(
    v2_struct_0 @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['143','195'])).

thf('197',plain,(
    $false ),
    inference(demod,[status(thm)],['0','196'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.NHo6HU1iDS
% 0.15/0.35  % Computer   : n022.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 15:15:26 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  % Running portfolio for 600 s
% 0.15/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.35  % Number of cores: 8
% 0.15/0.36  % Python version: Python 3.6.8
% 0.15/0.36  % Running in FO mode
% 0.59/0.79  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.59/0.79  % Solved by: fo/fo7.sh
% 0.59/0.79  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.59/0.79  % done 628 iterations in 0.326s
% 0.59/0.79  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.59/0.79  % SZS output start Refutation
% 0.59/0.79  thf(g1_pre_topc_type, type, g1_pre_topc: $i > $i > $i).
% 0.59/0.79  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 0.59/0.79  thf(sk_B_type, type, sk_B: $i).
% 0.59/0.79  thf(k8_tmap_1_type, type, k8_tmap_1: $i > $i > $i).
% 0.59/0.79  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.59/0.79  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.59/0.79  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.59/0.79  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.59/0.79  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.59/0.79  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.59/0.79  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 0.59/0.79  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.59/0.79  thf(v1_tsep_1_type, type, v1_tsep_1: $i > $i > $o).
% 0.59/0.79  thf(k5_tmap_1_type, type, k5_tmap_1: $i > $i > $i).
% 0.59/0.79  thf(sk_A_type, type, sk_A: $i).
% 0.59/0.79  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.59/0.79  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.59/0.79  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.59/0.79  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.59/0.79  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.59/0.79  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.59/0.79  thf(t116_tmap_1, conjecture,
% 0.59/0.79    (![A:$i]:
% 0.59/0.79     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.59/0.79       ( ![B:$i]:
% 0.59/0.79         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.59/0.79           ( ( ( v1_tsep_1 @ B @ A ) & ( m1_pre_topc @ B @ A ) ) <=>
% 0.59/0.79             ( ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) =
% 0.59/0.79               ( k8_tmap_1 @ A @ B ) ) ) ) ) ))).
% 0.59/0.79  thf(zf_stmt_0, negated_conjecture,
% 0.59/0.79    (~( ![A:$i]:
% 0.59/0.79        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.59/0.79            ( l1_pre_topc @ A ) ) =>
% 0.59/0.79          ( ![B:$i]:
% 0.59/0.79            ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.59/0.79              ( ( ( v1_tsep_1 @ B @ A ) & ( m1_pre_topc @ B @ A ) ) <=>
% 0.59/0.79                ( ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) =
% 0.59/0.79                  ( k8_tmap_1 @ A @ B ) ) ) ) ) ) )),
% 0.59/0.79    inference('cnf.neg', [status(esa)], [t116_tmap_1])).
% 0.59/0.79  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.59/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.79  thf('1', plain,
% 0.59/0.79      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.59/0.79          = (k8_tmap_1 @ sk_A @ sk_B))
% 0.59/0.79        | (v1_tsep_1 @ sk_B @ sk_A))),
% 0.59/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.79  thf('2', plain,
% 0.59/0.79      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.59/0.79          = (k8_tmap_1 @ sk_A @ sk_B)))
% 0.59/0.79         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.59/0.79                = (k8_tmap_1 @ sk_A @ sk_B))))),
% 0.59/0.79      inference('split', [status(esa)], ['1'])).
% 0.59/0.79  thf('3', plain,
% 0.59/0.79      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.59/0.79          != (k8_tmap_1 @ sk_A @ sk_B))
% 0.59/0.79        | ~ (m1_pre_topc @ sk_B @ sk_A)
% 0.59/0.79        | ~ (v1_tsep_1 @ sk_B @ sk_A))),
% 0.59/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.79  thf('4', plain,
% 0.59/0.79      (~ ((v1_tsep_1 @ sk_B @ sk_A)) | 
% 0.59/0.79       ~
% 0.59/0.79       (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.59/0.79          = (k8_tmap_1 @ sk_A @ sk_B))) | 
% 0.59/0.79       ~ ((m1_pre_topc @ sk_B @ sk_A))),
% 0.59/0.79      inference('split', [status(esa)], ['3'])).
% 0.59/0.79  thf('5', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.59/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.79  thf('6', plain,
% 0.59/0.79      ((~ (m1_pre_topc @ sk_B @ sk_A)) <= (~ ((m1_pre_topc @ sk_B @ sk_A)))),
% 0.59/0.79      inference('split', [status(esa)], ['3'])).
% 0.59/0.79  thf('7', plain, (((m1_pre_topc @ sk_B @ sk_A))),
% 0.59/0.79      inference('sup-', [status(thm)], ['5', '6'])).
% 0.59/0.79  thf('8', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.59/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.79  thf(t1_tsep_1, axiom,
% 0.59/0.79    (![A:$i]:
% 0.59/0.79     ( ( l1_pre_topc @ A ) =>
% 0.59/0.79       ( ![B:$i]:
% 0.59/0.79         ( ( m1_pre_topc @ B @ A ) =>
% 0.59/0.79           ( m1_subset_1 @
% 0.59/0.79             ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.59/0.79  thf('9', plain,
% 0.59/0.79      (![X18 : $i, X19 : $i]:
% 0.59/0.79         (~ (m1_pre_topc @ X18 @ X19)
% 0.59/0.79          | (m1_subset_1 @ (u1_struct_0 @ X18) @ 
% 0.59/0.79             (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.59/0.79          | ~ (l1_pre_topc @ X19))),
% 0.59/0.79      inference('cnf', [status(esa)], [t1_tsep_1])).
% 0.59/0.79  thf('10', plain,
% 0.59/0.79      ((~ (l1_pre_topc @ sk_A)
% 0.59/0.79        | (m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.59/0.79           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.59/0.79      inference('sup-', [status(thm)], ['8', '9'])).
% 0.59/0.79  thf('11', plain, ((l1_pre_topc @ sk_A)),
% 0.59/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.79  thf('12', plain,
% 0.59/0.79      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.59/0.79        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.59/0.79      inference('demod', [status(thm)], ['10', '11'])).
% 0.59/0.79  thf(t114_tmap_1, axiom,
% 0.59/0.79    (![A:$i]:
% 0.59/0.79     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.59/0.79       ( ![B:$i]:
% 0.59/0.79         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.59/0.79           ( ( ( u1_struct_0 @ ( k8_tmap_1 @ A @ B ) ) = ( u1_struct_0 @ A ) ) & 
% 0.59/0.79             ( ![C:$i]:
% 0.59/0.79               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.59/0.79                 ( ( ( C ) = ( u1_struct_0 @ B ) ) =>
% 0.59/0.79                   ( ( u1_pre_topc @ ( k8_tmap_1 @ A @ B ) ) =
% 0.59/0.79                     ( k5_tmap_1 @ A @ C ) ) ) ) ) ) ) ) ))).
% 0.59/0.79  thf('13', plain,
% 0.59/0.79      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.59/0.79         ((v2_struct_0 @ X15)
% 0.59/0.79          | ~ (m1_pre_topc @ X15 @ X16)
% 0.59/0.79          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.59/0.79          | ((u1_pre_topc @ (k8_tmap_1 @ X16 @ X15)) = (k5_tmap_1 @ X16 @ X17))
% 0.59/0.79          | ((X17) != (u1_struct_0 @ X15))
% 0.59/0.79          | ~ (l1_pre_topc @ X16)
% 0.59/0.79          | ~ (v2_pre_topc @ X16)
% 0.59/0.79          | (v2_struct_0 @ X16))),
% 0.59/0.79      inference('cnf', [status(esa)], [t114_tmap_1])).
% 0.59/0.79  thf('14', plain,
% 0.59/0.79      (![X15 : $i, X16 : $i]:
% 0.59/0.79         ((v2_struct_0 @ X16)
% 0.59/0.79          | ~ (v2_pre_topc @ X16)
% 0.59/0.79          | ~ (l1_pre_topc @ X16)
% 0.59/0.79          | ((u1_pre_topc @ (k8_tmap_1 @ X16 @ X15))
% 0.59/0.79              = (k5_tmap_1 @ X16 @ (u1_struct_0 @ X15)))
% 0.59/0.79          | ~ (m1_subset_1 @ (u1_struct_0 @ X15) @ 
% 0.59/0.79               (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.59/0.79          | ~ (m1_pre_topc @ X15 @ X16)
% 0.59/0.79          | (v2_struct_0 @ X15))),
% 0.59/0.79      inference('simplify', [status(thm)], ['13'])).
% 0.59/0.79  thf('15', plain,
% 0.59/0.79      (((v2_struct_0 @ sk_B)
% 0.59/0.79        | ~ (m1_pre_topc @ sk_B @ sk_A)
% 0.59/0.79        | ((u1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.59/0.79            = (k5_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 0.59/0.79        | ~ (l1_pre_topc @ sk_A)
% 0.59/0.79        | ~ (v2_pre_topc @ sk_A)
% 0.59/0.79        | (v2_struct_0 @ sk_A))),
% 0.59/0.79      inference('sup-', [status(thm)], ['12', '14'])).
% 0.59/0.79  thf('16', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.59/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.79  thf('17', plain, ((l1_pre_topc @ sk_A)),
% 0.59/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.79  thf('18', plain, ((v2_pre_topc @ sk_A)),
% 0.59/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.79  thf('19', plain,
% 0.59/0.79      (((v2_struct_0 @ sk_B)
% 0.59/0.79        | ((u1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.59/0.79            = (k5_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 0.59/0.79        | (v2_struct_0 @ sk_A))),
% 0.59/0.79      inference('demod', [status(thm)], ['15', '16', '17', '18'])).
% 0.59/0.79  thf('20', plain, (~ (v2_struct_0 @ sk_B)),
% 0.59/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.79  thf('21', plain,
% 0.59/0.79      (((v2_struct_0 @ sk_A)
% 0.59/0.80        | ((u1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.59/0.80            = (k5_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B))))),
% 0.59/0.80      inference('clc', [status(thm)], ['19', '20'])).
% 0.59/0.80  thf('22', plain, (~ (v2_struct_0 @ sk_A)),
% 0.59/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.80  thf('23', plain,
% 0.59/0.80      (((u1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.59/0.80         = (k5_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))),
% 0.59/0.80      inference('clc', [status(thm)], ['21', '22'])).
% 0.59/0.80  thf('24', plain,
% 0.59/0.80      (((v1_tsep_1 @ sk_B @ sk_A)) <= (((v1_tsep_1 @ sk_B @ sk_A)))),
% 0.59/0.80      inference('split', [status(esa)], ['1'])).
% 0.59/0.80  thf('25', plain,
% 0.59/0.80      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.59/0.80        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.59/0.80      inference('demod', [status(thm)], ['10', '11'])).
% 0.59/0.80  thf(d1_tsep_1, axiom,
% 0.59/0.80    (![A:$i]:
% 0.59/0.80     ( ( l1_pre_topc @ A ) =>
% 0.59/0.80       ( ![B:$i]:
% 0.59/0.80         ( ( m1_pre_topc @ B @ A ) =>
% 0.59/0.80           ( ( v1_tsep_1 @ B @ A ) <=>
% 0.59/0.80             ( ![C:$i]:
% 0.59/0.80               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.59/0.80                 ( ( ( C ) = ( u1_struct_0 @ B ) ) => ( v3_pre_topc @ C @ A ) ) ) ) ) ) ) ))).
% 0.59/0.80  thf('26', plain,
% 0.59/0.80      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.59/0.80         (~ (m1_pre_topc @ X8 @ X9)
% 0.59/0.80          | ~ (v1_tsep_1 @ X8 @ X9)
% 0.59/0.80          | ((X10) != (u1_struct_0 @ X8))
% 0.59/0.80          | (v3_pre_topc @ X10 @ X9)
% 0.59/0.80          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.59/0.80          | ~ (l1_pre_topc @ X9))),
% 0.59/0.80      inference('cnf', [status(esa)], [d1_tsep_1])).
% 0.59/0.80  thf('27', plain,
% 0.59/0.80      (![X8 : $i, X9 : $i]:
% 0.59/0.80         (~ (l1_pre_topc @ X9)
% 0.59/0.80          | ~ (m1_subset_1 @ (u1_struct_0 @ X8) @ 
% 0.59/0.80               (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.59/0.80          | (v3_pre_topc @ (u1_struct_0 @ X8) @ X9)
% 0.59/0.80          | ~ (v1_tsep_1 @ X8 @ X9)
% 0.59/0.80          | ~ (m1_pre_topc @ X8 @ X9))),
% 0.59/0.80      inference('simplify', [status(thm)], ['26'])).
% 0.59/0.80  thf('28', plain,
% 0.59/0.80      ((~ (m1_pre_topc @ sk_B @ sk_A)
% 0.59/0.80        | ~ (v1_tsep_1 @ sk_B @ sk_A)
% 0.59/0.80        | (v3_pre_topc @ (u1_struct_0 @ sk_B) @ sk_A)
% 0.59/0.80        | ~ (l1_pre_topc @ sk_A))),
% 0.59/0.80      inference('sup-', [status(thm)], ['25', '27'])).
% 0.59/0.80  thf('29', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.59/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.80  thf('30', plain, ((l1_pre_topc @ sk_A)),
% 0.59/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.80  thf('31', plain,
% 0.59/0.80      ((~ (v1_tsep_1 @ sk_B @ sk_A)
% 0.59/0.80        | (v3_pre_topc @ (u1_struct_0 @ sk_B) @ sk_A))),
% 0.59/0.80      inference('demod', [status(thm)], ['28', '29', '30'])).
% 0.59/0.80  thf('32', plain,
% 0.59/0.80      (((v3_pre_topc @ (u1_struct_0 @ sk_B) @ sk_A))
% 0.59/0.80         <= (((v1_tsep_1 @ sk_B @ sk_A)))),
% 0.59/0.80      inference('sup-', [status(thm)], ['24', '31'])).
% 0.59/0.80  thf('33', plain,
% 0.59/0.80      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.59/0.80        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.59/0.80      inference('demod', [status(thm)], ['10', '11'])).
% 0.59/0.80  thf(d5_pre_topc, axiom,
% 0.59/0.80    (![A:$i]:
% 0.59/0.80     ( ( l1_pre_topc @ A ) =>
% 0.59/0.80       ( ![B:$i]:
% 0.59/0.80         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.59/0.80           ( ( v3_pre_topc @ B @ A ) <=>
% 0.59/0.80             ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) ) ) ) ))).
% 0.59/0.80  thf('34', plain,
% 0.59/0.80      (![X4 : $i, X5 : $i]:
% 0.59/0.80         (~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (u1_struct_0 @ X5)))
% 0.59/0.80          | ~ (v3_pre_topc @ X4 @ X5)
% 0.59/0.80          | (r2_hidden @ X4 @ (u1_pre_topc @ X5))
% 0.59/0.80          | ~ (l1_pre_topc @ X5))),
% 0.59/0.80      inference('cnf', [status(esa)], [d5_pre_topc])).
% 0.59/0.80  thf('35', plain,
% 0.59/0.80      ((~ (l1_pre_topc @ sk_A)
% 0.59/0.80        | (r2_hidden @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_A))
% 0.59/0.80        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_B) @ sk_A))),
% 0.59/0.80      inference('sup-', [status(thm)], ['33', '34'])).
% 0.59/0.80  thf('36', plain, ((l1_pre_topc @ sk_A)),
% 0.59/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.80  thf('37', plain,
% 0.59/0.80      (((r2_hidden @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_A))
% 0.59/0.80        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_B) @ sk_A))),
% 0.59/0.80      inference('demod', [status(thm)], ['35', '36'])).
% 0.59/0.80  thf('38', plain,
% 0.59/0.80      (((r2_hidden @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_A)))
% 0.59/0.80         <= (((v1_tsep_1 @ sk_B @ sk_A)))),
% 0.59/0.80      inference('sup-', [status(thm)], ['32', '37'])).
% 0.59/0.80  thf('39', plain,
% 0.59/0.80      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.59/0.80        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.59/0.80      inference('demod', [status(thm)], ['10', '11'])).
% 0.59/0.80  thf(t103_tmap_1, axiom,
% 0.59/0.80    (![A:$i]:
% 0.59/0.80     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.59/0.80       ( ![B:$i]:
% 0.59/0.80         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.59/0.80           ( ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) <=>
% 0.59/0.80             ( ( u1_pre_topc @ A ) = ( k5_tmap_1 @ A @ B ) ) ) ) ) ))).
% 0.59/0.80  thf('40', plain,
% 0.59/0.80      (![X13 : $i, X14 : $i]:
% 0.59/0.80         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.59/0.80          | ~ (r2_hidden @ X13 @ (u1_pre_topc @ X14))
% 0.59/0.80          | ((u1_pre_topc @ X14) = (k5_tmap_1 @ X14 @ X13))
% 0.59/0.80          | ~ (l1_pre_topc @ X14)
% 0.59/0.80          | ~ (v2_pre_topc @ X14)
% 0.59/0.80          | (v2_struct_0 @ X14))),
% 0.59/0.80      inference('cnf', [status(esa)], [t103_tmap_1])).
% 0.59/0.80  thf('41', plain,
% 0.59/0.80      (((v2_struct_0 @ sk_A)
% 0.59/0.80        | ~ (v2_pre_topc @ sk_A)
% 0.59/0.80        | ~ (l1_pre_topc @ sk_A)
% 0.59/0.80        | ((u1_pre_topc @ sk_A) = (k5_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 0.59/0.80        | ~ (r2_hidden @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_A)))),
% 0.59/0.80      inference('sup-', [status(thm)], ['39', '40'])).
% 0.59/0.80  thf('42', plain, ((v2_pre_topc @ sk_A)),
% 0.59/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.80  thf('43', plain, ((l1_pre_topc @ sk_A)),
% 0.59/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.80  thf('44', plain,
% 0.59/0.80      (((v2_struct_0 @ sk_A)
% 0.59/0.80        | ((u1_pre_topc @ sk_A) = (k5_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 0.59/0.80        | ~ (r2_hidden @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_A)))),
% 0.59/0.80      inference('demod', [status(thm)], ['41', '42', '43'])).
% 0.59/0.80  thf('45', plain, (~ (v2_struct_0 @ sk_A)),
% 0.59/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.80  thf('46', plain,
% 0.59/0.80      ((~ (r2_hidden @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_A))
% 0.59/0.80        | ((u1_pre_topc @ sk_A) = (k5_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B))))),
% 0.59/0.80      inference('clc', [status(thm)], ['44', '45'])).
% 0.59/0.80  thf('47', plain,
% 0.59/0.80      ((((u1_pre_topc @ sk_A) = (k5_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B))))
% 0.59/0.80         <= (((v1_tsep_1 @ sk_B @ sk_A)))),
% 0.59/0.80      inference('sup-', [status(thm)], ['38', '46'])).
% 0.59/0.80  thf('48', plain,
% 0.59/0.80      ((((u1_pre_topc @ sk_A) = (u1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))))
% 0.59/0.80         <= (((v1_tsep_1 @ sk_B @ sk_A)))),
% 0.59/0.80      inference('sup+', [status(thm)], ['23', '47'])).
% 0.59/0.80  thf('49', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.59/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.80  thf('50', plain,
% 0.59/0.80      (![X15 : $i, X16 : $i]:
% 0.59/0.80         ((v2_struct_0 @ X15)
% 0.59/0.80          | ~ (m1_pre_topc @ X15 @ X16)
% 0.59/0.80          | ((u1_struct_0 @ (k8_tmap_1 @ X16 @ X15)) = (u1_struct_0 @ X16))
% 0.59/0.80          | ~ (l1_pre_topc @ X16)
% 0.59/0.80          | ~ (v2_pre_topc @ X16)
% 0.59/0.80          | (v2_struct_0 @ X16))),
% 0.59/0.80      inference('cnf', [status(esa)], [t114_tmap_1])).
% 0.59/0.80  thf('51', plain,
% 0.59/0.80      (((v2_struct_0 @ sk_A)
% 0.59/0.80        | ~ (v2_pre_topc @ sk_A)
% 0.59/0.80        | ~ (l1_pre_topc @ sk_A)
% 0.59/0.80        | ((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))
% 0.59/0.80        | (v2_struct_0 @ sk_B))),
% 0.59/0.80      inference('sup-', [status(thm)], ['49', '50'])).
% 0.59/0.80  thf('52', plain, ((v2_pre_topc @ sk_A)),
% 0.59/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.80  thf('53', plain, ((l1_pre_topc @ sk_A)),
% 0.59/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.80  thf('54', plain,
% 0.59/0.80      (((v2_struct_0 @ sk_A)
% 0.59/0.80        | ((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))
% 0.59/0.80        | (v2_struct_0 @ sk_B))),
% 0.59/0.80      inference('demod', [status(thm)], ['51', '52', '53'])).
% 0.59/0.80  thf('55', plain, (~ (v2_struct_0 @ sk_A)),
% 0.59/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.80  thf('56', plain,
% 0.59/0.80      (((v2_struct_0 @ sk_B)
% 0.59/0.80        | ((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A)))),
% 0.59/0.80      inference('clc', [status(thm)], ['54', '55'])).
% 0.59/0.80  thf('57', plain, (~ (v2_struct_0 @ sk_B)),
% 0.59/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.80  thf('58', plain,
% 0.59/0.80      (((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 0.59/0.80      inference('clc', [status(thm)], ['56', '57'])).
% 0.59/0.80  thf(abstractness_v1_pre_topc, axiom,
% 0.59/0.80    (![A:$i]:
% 0.59/0.80     ( ( l1_pre_topc @ A ) =>
% 0.59/0.80       ( ( v1_pre_topc @ A ) =>
% 0.59/0.80         ( ( A ) = ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ))).
% 0.59/0.80  thf('59', plain,
% 0.59/0.80      (![X2 : $i]:
% 0.59/0.80         (~ (v1_pre_topc @ X2)
% 0.59/0.80          | ((X2) = (g1_pre_topc @ (u1_struct_0 @ X2) @ (u1_pre_topc @ X2)))
% 0.59/0.80          | ~ (l1_pre_topc @ X2))),
% 0.59/0.80      inference('cnf', [status(esa)], [abstractness_v1_pre_topc])).
% 0.59/0.80  thf('60', plain,
% 0.59/0.80      ((((k8_tmap_1 @ sk_A @ sk_B)
% 0.59/0.80          = (g1_pre_topc @ (u1_struct_0 @ sk_A) @ 
% 0.59/0.80             (u1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))))
% 0.59/0.80        | ~ (l1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.59/0.80        | ~ (v1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B)))),
% 0.59/0.80      inference('sup+', [status(thm)], ['58', '59'])).
% 0.59/0.80  thf('61', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.59/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.80  thf(dt_k8_tmap_1, axiom,
% 0.59/0.80    (![A:$i,B:$i]:
% 0.59/0.80     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.59/0.80         ( l1_pre_topc @ A ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.59/0.80       ( ( v1_pre_topc @ ( k8_tmap_1 @ A @ B ) ) & 
% 0.59/0.80         ( v2_pre_topc @ ( k8_tmap_1 @ A @ B ) ) & 
% 0.59/0.80         ( l1_pre_topc @ ( k8_tmap_1 @ A @ B ) ) ) ))).
% 0.59/0.80  thf('62', plain,
% 0.59/0.80      (![X11 : $i, X12 : $i]:
% 0.59/0.80         (~ (l1_pre_topc @ X11)
% 0.59/0.80          | ~ (v2_pre_topc @ X11)
% 0.59/0.80          | (v2_struct_0 @ X11)
% 0.59/0.80          | ~ (m1_pre_topc @ X12 @ X11)
% 0.59/0.80          | (l1_pre_topc @ (k8_tmap_1 @ X11 @ X12)))),
% 0.59/0.80      inference('cnf', [status(esa)], [dt_k8_tmap_1])).
% 0.59/0.80  thf('63', plain,
% 0.59/0.80      (((l1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.59/0.80        | (v2_struct_0 @ sk_A)
% 0.59/0.80        | ~ (v2_pre_topc @ sk_A)
% 0.59/0.80        | ~ (l1_pre_topc @ sk_A))),
% 0.59/0.80      inference('sup-', [status(thm)], ['61', '62'])).
% 0.59/0.80  thf('64', plain, ((v2_pre_topc @ sk_A)),
% 0.59/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.80  thf('65', plain, ((l1_pre_topc @ sk_A)),
% 0.59/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.80  thf('66', plain,
% 0.59/0.80      (((l1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B)) | (v2_struct_0 @ sk_A))),
% 0.59/0.80      inference('demod', [status(thm)], ['63', '64', '65'])).
% 0.59/0.80  thf('67', plain, (~ (v2_struct_0 @ sk_A)),
% 0.59/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.80  thf('68', plain, ((l1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))),
% 0.59/0.80      inference('clc', [status(thm)], ['66', '67'])).
% 0.59/0.80  thf('69', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.59/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.80  thf('70', plain,
% 0.59/0.80      (![X11 : $i, X12 : $i]:
% 0.59/0.80         (~ (l1_pre_topc @ X11)
% 0.59/0.80          | ~ (v2_pre_topc @ X11)
% 0.59/0.80          | (v2_struct_0 @ X11)
% 0.59/0.80          | ~ (m1_pre_topc @ X12 @ X11)
% 0.59/0.80          | (v1_pre_topc @ (k8_tmap_1 @ X11 @ X12)))),
% 0.59/0.80      inference('cnf', [status(esa)], [dt_k8_tmap_1])).
% 0.59/0.80  thf('71', plain,
% 0.59/0.80      (((v1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.59/0.80        | (v2_struct_0 @ sk_A)
% 0.59/0.80        | ~ (v2_pre_topc @ sk_A)
% 0.59/0.80        | ~ (l1_pre_topc @ sk_A))),
% 0.59/0.80      inference('sup-', [status(thm)], ['69', '70'])).
% 0.59/0.80  thf('72', plain, ((v2_pre_topc @ sk_A)),
% 0.59/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.80  thf('73', plain, ((l1_pre_topc @ sk_A)),
% 0.59/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.80  thf('74', plain,
% 0.59/0.80      (((v1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B)) | (v2_struct_0 @ sk_A))),
% 0.59/0.80      inference('demod', [status(thm)], ['71', '72', '73'])).
% 0.59/0.80  thf('75', plain, (~ (v2_struct_0 @ sk_A)),
% 0.59/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.80  thf('76', plain, ((v1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))),
% 0.59/0.80      inference('clc', [status(thm)], ['74', '75'])).
% 0.59/0.80  thf('77', plain,
% 0.59/0.80      (((k8_tmap_1 @ sk_A @ sk_B)
% 0.59/0.80         = (g1_pre_topc @ (u1_struct_0 @ sk_A) @ 
% 0.59/0.80            (u1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))))),
% 0.59/0.80      inference('demod', [status(thm)], ['60', '68', '76'])).
% 0.59/0.80  thf('78', plain,
% 0.59/0.80      ((((k8_tmap_1 @ sk_A @ sk_B)
% 0.59/0.80          = (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))
% 0.59/0.80         <= (((v1_tsep_1 @ sk_B @ sk_A)))),
% 0.59/0.80      inference('sup+', [status(thm)], ['48', '77'])).
% 0.59/0.80  thf('79', plain,
% 0.59/0.80      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.59/0.80          != (k8_tmap_1 @ sk_A @ sk_B)))
% 0.59/0.80         <= (~
% 0.59/0.80             (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.59/0.80                = (k8_tmap_1 @ sk_A @ sk_B))))),
% 0.59/0.80      inference('split', [status(esa)], ['3'])).
% 0.59/0.80  thf('80', plain,
% 0.59/0.80      ((((k8_tmap_1 @ sk_A @ sk_B) != (k8_tmap_1 @ sk_A @ sk_B)))
% 0.59/0.80         <= (~
% 0.59/0.80             (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.59/0.80                = (k8_tmap_1 @ sk_A @ sk_B))) & 
% 0.59/0.80             ((v1_tsep_1 @ sk_B @ sk_A)))),
% 0.59/0.80      inference('sup-', [status(thm)], ['78', '79'])).
% 0.59/0.80  thf('81', plain,
% 0.59/0.80      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.59/0.80          = (k8_tmap_1 @ sk_A @ sk_B))) | 
% 0.59/0.80       ~ ((v1_tsep_1 @ sk_B @ sk_A))),
% 0.59/0.80      inference('simplify', [status(thm)], ['80'])).
% 0.59/0.80  thf('82', plain,
% 0.59/0.80      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.59/0.80          = (k8_tmap_1 @ sk_A @ sk_B))) | 
% 0.59/0.80       ((v1_tsep_1 @ sk_B @ sk_A))),
% 0.59/0.80      inference('split', [status(esa)], ['1'])).
% 0.59/0.80  thf('83', plain,
% 0.59/0.80      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.59/0.80          = (k8_tmap_1 @ sk_A @ sk_B)))),
% 0.59/0.80      inference('sat_resolution*', [status(thm)], ['4', '7', '81', '82'])).
% 0.59/0.80  thf('84', plain,
% 0.59/0.80      (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.59/0.80         = (k8_tmap_1 @ sk_A @ sk_B))),
% 0.59/0.80      inference('simpl_trail', [status(thm)], ['2', '83'])).
% 0.59/0.80  thf(fc10_tops_1, axiom,
% 0.59/0.80    (![A:$i]:
% 0.59/0.80     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.59/0.80       ( v3_pre_topc @ ( k2_struct_0 @ A ) @ A ) ))).
% 0.59/0.80  thf('85', plain,
% 0.59/0.80      (![X7 : $i]:
% 0.59/0.80         ((v3_pre_topc @ (k2_struct_0 @ X7) @ X7)
% 0.59/0.80          | ~ (l1_pre_topc @ X7)
% 0.59/0.80          | ~ (v2_pre_topc @ X7))),
% 0.59/0.80      inference('cnf', [status(esa)], [fc10_tops_1])).
% 0.59/0.80  thf(d3_struct_0, axiom,
% 0.59/0.80    (![A:$i]:
% 0.59/0.80     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.59/0.80  thf('86', plain,
% 0.59/0.80      (![X3 : $i]:
% 0.59/0.80         (((k2_struct_0 @ X3) = (u1_struct_0 @ X3)) | ~ (l1_struct_0 @ X3))),
% 0.59/0.80      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.59/0.80  thf(dt_k2_subset_1, axiom,
% 0.59/0.80    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.59/0.80  thf('87', plain,
% 0.59/0.80      (![X1 : $i]: (m1_subset_1 @ (k2_subset_1 @ X1) @ (k1_zfmisc_1 @ X1))),
% 0.59/0.80      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 0.59/0.80  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.59/0.80  thf('88', plain, (![X0 : $i]: ((k2_subset_1 @ X0) = (X0))),
% 0.59/0.80      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.59/0.80  thf('89', plain, (![X1 : $i]: (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X1))),
% 0.59/0.80      inference('demod', [status(thm)], ['87', '88'])).
% 0.59/0.80  thf('90', plain,
% 0.59/0.80      (![X4 : $i, X5 : $i]:
% 0.59/0.80         (~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (u1_struct_0 @ X5)))
% 0.59/0.80          | ~ (v3_pre_topc @ X4 @ X5)
% 0.59/0.80          | (r2_hidden @ X4 @ (u1_pre_topc @ X5))
% 0.59/0.80          | ~ (l1_pre_topc @ X5))),
% 0.59/0.80      inference('cnf', [status(esa)], [d5_pre_topc])).
% 0.59/0.80  thf('91', plain,
% 0.59/0.80      (![X0 : $i]:
% 0.59/0.80         (~ (l1_pre_topc @ X0)
% 0.59/0.80          | (r2_hidden @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))
% 0.59/0.80          | ~ (v3_pre_topc @ (u1_struct_0 @ X0) @ X0))),
% 0.59/0.80      inference('sup-', [status(thm)], ['89', '90'])).
% 0.59/0.80  thf('92', plain,
% 0.59/0.80      (![X0 : $i]:
% 0.59/0.80         (~ (v3_pre_topc @ (k2_struct_0 @ X0) @ X0)
% 0.59/0.80          | ~ (l1_struct_0 @ X0)
% 0.59/0.80          | (r2_hidden @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))
% 0.59/0.80          | ~ (l1_pre_topc @ X0))),
% 0.59/0.80      inference('sup-', [status(thm)], ['86', '91'])).
% 0.59/0.80  thf('93', plain,
% 0.59/0.80      (![X0 : $i]:
% 0.59/0.80         (~ (v2_pre_topc @ X0)
% 0.59/0.80          | ~ (l1_pre_topc @ X0)
% 0.59/0.80          | ~ (l1_pre_topc @ X0)
% 0.59/0.80          | (r2_hidden @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))
% 0.59/0.80          | ~ (l1_struct_0 @ X0))),
% 0.59/0.80      inference('sup-', [status(thm)], ['85', '92'])).
% 0.59/0.80  thf('94', plain,
% 0.59/0.80      (![X0 : $i]:
% 0.59/0.80         (~ (l1_struct_0 @ X0)
% 0.59/0.80          | (r2_hidden @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))
% 0.59/0.80          | ~ (l1_pre_topc @ X0)
% 0.59/0.80          | ~ (v2_pre_topc @ X0))),
% 0.59/0.80      inference('simplify', [status(thm)], ['93'])).
% 0.59/0.80  thf('95', plain, (![X1 : $i]: (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X1))),
% 0.59/0.80      inference('demod', [status(thm)], ['87', '88'])).
% 0.59/0.80  thf('96', plain,
% 0.59/0.80      (![X13 : $i, X14 : $i]:
% 0.59/0.80         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.59/0.80          | ~ (r2_hidden @ X13 @ (u1_pre_topc @ X14))
% 0.59/0.80          | ((u1_pre_topc @ X14) = (k5_tmap_1 @ X14 @ X13))
% 0.59/0.80          | ~ (l1_pre_topc @ X14)
% 0.59/0.80          | ~ (v2_pre_topc @ X14)
% 0.59/0.80          | (v2_struct_0 @ X14))),
% 0.59/0.80      inference('cnf', [status(esa)], [t103_tmap_1])).
% 0.59/0.80  thf('97', plain,
% 0.59/0.80      (![X0 : $i]:
% 0.59/0.80         ((v2_struct_0 @ X0)
% 0.59/0.80          | ~ (v2_pre_topc @ X0)
% 0.59/0.80          | ~ (l1_pre_topc @ X0)
% 0.59/0.80          | ((u1_pre_topc @ X0) = (k5_tmap_1 @ X0 @ (u1_struct_0 @ X0)))
% 0.59/0.80          | ~ (r2_hidden @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))),
% 0.59/0.80      inference('sup-', [status(thm)], ['95', '96'])).
% 0.59/0.80  thf('98', plain,
% 0.59/0.80      (![X0 : $i]:
% 0.59/0.80         (~ (v2_pre_topc @ X0)
% 0.59/0.80          | ~ (l1_pre_topc @ X0)
% 0.59/0.80          | ~ (l1_struct_0 @ X0)
% 0.59/0.80          | ((u1_pre_topc @ X0) = (k5_tmap_1 @ X0 @ (u1_struct_0 @ X0)))
% 0.59/0.80          | ~ (l1_pre_topc @ X0)
% 0.59/0.80          | ~ (v2_pre_topc @ X0)
% 0.59/0.80          | (v2_struct_0 @ X0))),
% 0.59/0.80      inference('sup-', [status(thm)], ['94', '97'])).
% 0.59/0.80  thf('99', plain,
% 0.59/0.80      (![X0 : $i]:
% 0.59/0.80         ((v2_struct_0 @ X0)
% 0.59/0.80          | ((u1_pre_topc @ X0) = (k5_tmap_1 @ X0 @ (u1_struct_0 @ X0)))
% 0.59/0.80          | ~ (l1_struct_0 @ X0)
% 0.59/0.80          | ~ (l1_pre_topc @ X0)
% 0.59/0.80          | ~ (v2_pre_topc @ X0))),
% 0.59/0.80      inference('simplify', [status(thm)], ['98'])).
% 0.59/0.80  thf(t2_tsep_1, axiom,
% 0.59/0.80    (![A:$i]: ( ( l1_pre_topc @ A ) => ( m1_pre_topc @ A @ A ) ))).
% 0.59/0.80  thf('100', plain,
% 0.59/0.80      (![X20 : $i]: ((m1_pre_topc @ X20 @ X20) | ~ (l1_pre_topc @ X20))),
% 0.59/0.80      inference('cnf', [status(esa)], [t2_tsep_1])).
% 0.59/0.80  thf('101', plain, (![X1 : $i]: (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X1))),
% 0.59/0.80      inference('demod', [status(thm)], ['87', '88'])).
% 0.59/0.80  thf('102', plain,
% 0.59/0.80      (![X15 : $i, X16 : $i]:
% 0.59/0.80         ((v2_struct_0 @ X16)
% 0.59/0.80          | ~ (v2_pre_topc @ X16)
% 0.59/0.80          | ~ (l1_pre_topc @ X16)
% 0.59/0.80          | ((u1_pre_topc @ (k8_tmap_1 @ X16 @ X15))
% 0.59/0.80              = (k5_tmap_1 @ X16 @ (u1_struct_0 @ X15)))
% 0.59/0.80          | ~ (m1_subset_1 @ (u1_struct_0 @ X15) @ 
% 0.59/0.80               (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.59/0.80          | ~ (m1_pre_topc @ X15 @ X16)
% 0.59/0.80          | (v2_struct_0 @ X15))),
% 0.59/0.80      inference('simplify', [status(thm)], ['13'])).
% 0.59/0.80  thf('103', plain,
% 0.59/0.80      (![X0 : $i]:
% 0.59/0.80         ((v2_struct_0 @ X0)
% 0.59/0.80          | ~ (m1_pre_topc @ X0 @ X0)
% 0.59/0.80          | ((u1_pre_topc @ (k8_tmap_1 @ X0 @ X0))
% 0.59/0.80              = (k5_tmap_1 @ X0 @ (u1_struct_0 @ X0)))
% 0.59/0.80          | ~ (l1_pre_topc @ X0)
% 0.59/0.80          | ~ (v2_pre_topc @ X0)
% 0.59/0.80          | (v2_struct_0 @ X0))),
% 0.59/0.80      inference('sup-', [status(thm)], ['101', '102'])).
% 0.59/0.80  thf('104', plain,
% 0.59/0.80      (![X0 : $i]:
% 0.59/0.80         (~ (v2_pre_topc @ X0)
% 0.59/0.80          | ~ (l1_pre_topc @ X0)
% 0.59/0.80          | ((u1_pre_topc @ (k8_tmap_1 @ X0 @ X0))
% 0.59/0.80              = (k5_tmap_1 @ X0 @ (u1_struct_0 @ X0)))
% 0.59/0.80          | ~ (m1_pre_topc @ X0 @ X0)
% 0.59/0.80          | (v2_struct_0 @ X0))),
% 0.59/0.80      inference('simplify', [status(thm)], ['103'])).
% 0.59/0.80  thf('105', plain,
% 0.59/0.80      (![X0 : $i]:
% 0.59/0.80         (~ (l1_pre_topc @ X0)
% 0.59/0.80          | (v2_struct_0 @ X0)
% 0.59/0.80          | ((u1_pre_topc @ (k8_tmap_1 @ X0 @ X0))
% 0.59/0.80              = (k5_tmap_1 @ X0 @ (u1_struct_0 @ X0)))
% 0.59/0.80          | ~ (l1_pre_topc @ X0)
% 0.59/0.80          | ~ (v2_pre_topc @ X0))),
% 0.59/0.80      inference('sup-', [status(thm)], ['100', '104'])).
% 0.59/0.80  thf('106', plain,
% 0.59/0.80      (![X0 : $i]:
% 0.59/0.80         (~ (v2_pre_topc @ X0)
% 0.59/0.80          | ((u1_pre_topc @ (k8_tmap_1 @ X0 @ X0))
% 0.59/0.80              = (k5_tmap_1 @ X0 @ (u1_struct_0 @ X0)))
% 0.59/0.80          | (v2_struct_0 @ X0)
% 0.59/0.80          | ~ (l1_pre_topc @ X0))),
% 0.59/0.80      inference('simplify', [status(thm)], ['105'])).
% 0.59/0.80  thf('107', plain,
% 0.59/0.80      (![X0 : $i]:
% 0.59/0.80         (((u1_pre_topc @ (k8_tmap_1 @ X0 @ X0)) = (u1_pre_topc @ X0))
% 0.59/0.80          | ~ (v2_pre_topc @ X0)
% 0.59/0.80          | ~ (l1_pre_topc @ X0)
% 0.59/0.80          | ~ (l1_struct_0 @ X0)
% 0.59/0.80          | (v2_struct_0 @ X0)
% 0.59/0.80          | ~ (l1_pre_topc @ X0)
% 0.59/0.80          | (v2_struct_0 @ X0)
% 0.59/0.80          | ~ (v2_pre_topc @ X0))),
% 0.59/0.80      inference('sup+', [status(thm)], ['99', '106'])).
% 0.59/0.80  thf('108', plain,
% 0.59/0.80      (![X0 : $i]:
% 0.59/0.80         ((v2_struct_0 @ X0)
% 0.59/0.80          | ~ (l1_struct_0 @ X0)
% 0.59/0.80          | ~ (l1_pre_topc @ X0)
% 0.59/0.80          | ~ (v2_pre_topc @ X0)
% 0.59/0.80          | ((u1_pre_topc @ (k8_tmap_1 @ X0 @ X0)) = (u1_pre_topc @ X0)))),
% 0.59/0.80      inference('simplify', [status(thm)], ['107'])).
% 0.59/0.80  thf('109', plain,
% 0.59/0.80      (![X20 : $i]: ((m1_pre_topc @ X20 @ X20) | ~ (l1_pre_topc @ X20))),
% 0.59/0.80      inference('cnf', [status(esa)], [t2_tsep_1])).
% 0.59/0.80  thf('110', plain,
% 0.59/0.80      (![X11 : $i, X12 : $i]:
% 0.59/0.80         (~ (l1_pre_topc @ X11)
% 0.59/0.80          | ~ (v2_pre_topc @ X11)
% 0.59/0.80          | (v2_struct_0 @ X11)
% 0.59/0.80          | ~ (m1_pre_topc @ X12 @ X11)
% 0.59/0.80          | (v1_pre_topc @ (k8_tmap_1 @ X11 @ X12)))),
% 0.59/0.80      inference('cnf', [status(esa)], [dt_k8_tmap_1])).
% 0.59/0.80  thf('111', plain,
% 0.59/0.80      (![X0 : $i]:
% 0.59/0.80         (~ (l1_pre_topc @ X0)
% 0.59/0.80          | (v1_pre_topc @ (k8_tmap_1 @ X0 @ X0))
% 0.59/0.80          | (v2_struct_0 @ X0)
% 0.59/0.80          | ~ (v2_pre_topc @ X0)
% 0.59/0.80          | ~ (l1_pre_topc @ X0))),
% 0.59/0.80      inference('sup-', [status(thm)], ['109', '110'])).
% 0.59/0.80  thf('112', plain,
% 0.59/0.80      (![X0 : $i]:
% 0.59/0.80         (~ (v2_pre_topc @ X0)
% 0.59/0.80          | (v2_struct_0 @ X0)
% 0.59/0.80          | (v1_pre_topc @ (k8_tmap_1 @ X0 @ X0))
% 0.59/0.80          | ~ (l1_pre_topc @ X0))),
% 0.59/0.80      inference('simplify', [status(thm)], ['111'])).
% 0.59/0.80  thf('113', plain,
% 0.59/0.80      (![X20 : $i]: ((m1_pre_topc @ X20 @ X20) | ~ (l1_pre_topc @ X20))),
% 0.59/0.80      inference('cnf', [status(esa)], [t2_tsep_1])).
% 0.59/0.80  thf('114', plain,
% 0.59/0.80      (![X11 : $i, X12 : $i]:
% 0.59/0.80         (~ (l1_pre_topc @ X11)
% 0.59/0.80          | ~ (v2_pre_topc @ X11)
% 0.59/0.80          | (v2_struct_0 @ X11)
% 0.59/0.80          | ~ (m1_pre_topc @ X12 @ X11)
% 0.59/0.80          | (l1_pre_topc @ (k8_tmap_1 @ X11 @ X12)))),
% 0.59/0.80      inference('cnf', [status(esa)], [dt_k8_tmap_1])).
% 0.59/0.80  thf('115', plain,
% 0.59/0.80      (![X0 : $i]:
% 0.59/0.80         (~ (l1_pre_topc @ X0)
% 0.59/0.80          | (l1_pre_topc @ (k8_tmap_1 @ X0 @ X0))
% 0.59/0.80          | (v2_struct_0 @ X0)
% 0.59/0.80          | ~ (v2_pre_topc @ X0)
% 0.59/0.80          | ~ (l1_pre_topc @ X0))),
% 0.59/0.80      inference('sup-', [status(thm)], ['113', '114'])).
% 0.59/0.80  thf('116', plain,
% 0.59/0.80      (![X0 : $i]:
% 0.59/0.80         (~ (v2_pre_topc @ X0)
% 0.59/0.80          | (v2_struct_0 @ X0)
% 0.59/0.80          | (l1_pre_topc @ (k8_tmap_1 @ X0 @ X0))
% 0.59/0.80          | ~ (l1_pre_topc @ X0))),
% 0.59/0.80      inference('simplify', [status(thm)], ['115'])).
% 0.59/0.80  thf('117', plain,
% 0.59/0.80      (![X20 : $i]: ((m1_pre_topc @ X20 @ X20) | ~ (l1_pre_topc @ X20))),
% 0.59/0.80      inference('cnf', [status(esa)], [t2_tsep_1])).
% 0.59/0.80  thf('118', plain,
% 0.59/0.80      (![X15 : $i, X16 : $i]:
% 0.59/0.80         ((v2_struct_0 @ X15)
% 0.59/0.80          | ~ (m1_pre_topc @ X15 @ X16)
% 0.59/0.80          | ((u1_struct_0 @ (k8_tmap_1 @ X16 @ X15)) = (u1_struct_0 @ X16))
% 0.59/0.80          | ~ (l1_pre_topc @ X16)
% 0.59/0.80          | ~ (v2_pre_topc @ X16)
% 0.59/0.80          | (v2_struct_0 @ X16))),
% 0.59/0.80      inference('cnf', [status(esa)], [t114_tmap_1])).
% 0.59/0.80  thf('119', plain,
% 0.59/0.80      (![X0 : $i]:
% 0.59/0.80         (~ (l1_pre_topc @ X0)
% 0.59/0.80          | (v2_struct_0 @ X0)
% 0.59/0.80          | ~ (v2_pre_topc @ X0)
% 0.59/0.80          | ~ (l1_pre_topc @ X0)
% 0.59/0.80          | ((u1_struct_0 @ (k8_tmap_1 @ X0 @ X0)) = (u1_struct_0 @ X0))
% 0.59/0.80          | (v2_struct_0 @ X0))),
% 0.59/0.80      inference('sup-', [status(thm)], ['117', '118'])).
% 0.59/0.80  thf('120', plain,
% 0.59/0.80      (![X0 : $i]:
% 0.59/0.80         (((u1_struct_0 @ (k8_tmap_1 @ X0 @ X0)) = (u1_struct_0 @ X0))
% 0.59/0.80          | ~ (v2_pre_topc @ X0)
% 0.59/0.80          | (v2_struct_0 @ X0)
% 0.59/0.80          | ~ (l1_pre_topc @ X0))),
% 0.59/0.80      inference('simplify', [status(thm)], ['119'])).
% 0.59/0.80  thf('121', plain,
% 0.59/0.80      (![X2 : $i]:
% 0.59/0.80         (~ (v1_pre_topc @ X2)
% 0.59/0.80          | ((X2) = (g1_pre_topc @ (u1_struct_0 @ X2) @ (u1_pre_topc @ X2)))
% 0.59/0.80          | ~ (l1_pre_topc @ X2))),
% 0.59/0.80      inference('cnf', [status(esa)], [abstractness_v1_pre_topc])).
% 0.59/0.80  thf('122', plain,
% 0.59/0.80      (![X0 : $i]:
% 0.59/0.80         (((k8_tmap_1 @ X0 @ X0)
% 0.59/0.80            = (g1_pre_topc @ (u1_struct_0 @ X0) @ 
% 0.59/0.80               (u1_pre_topc @ (k8_tmap_1 @ X0 @ X0))))
% 0.59/0.80          | ~ (l1_pre_topc @ X0)
% 0.59/0.80          | (v2_struct_0 @ X0)
% 0.59/0.80          | ~ (v2_pre_topc @ X0)
% 0.59/0.80          | ~ (l1_pre_topc @ (k8_tmap_1 @ X0 @ X0))
% 0.59/0.80          | ~ (v1_pre_topc @ (k8_tmap_1 @ X0 @ X0)))),
% 0.59/0.80      inference('sup+', [status(thm)], ['120', '121'])).
% 0.59/0.80  thf('123', plain,
% 0.59/0.80      (![X0 : $i]:
% 0.59/0.80         (~ (l1_pre_topc @ X0)
% 0.59/0.80          | (v2_struct_0 @ X0)
% 0.59/0.80          | ~ (v2_pre_topc @ X0)
% 0.59/0.80          | ~ (v1_pre_topc @ (k8_tmap_1 @ X0 @ X0))
% 0.59/0.80          | ~ (v2_pre_topc @ X0)
% 0.59/0.80          | (v2_struct_0 @ X0)
% 0.59/0.80          | ~ (l1_pre_topc @ X0)
% 0.59/0.80          | ((k8_tmap_1 @ X0 @ X0)
% 0.59/0.80              = (g1_pre_topc @ (u1_struct_0 @ X0) @ 
% 0.59/0.80                 (u1_pre_topc @ (k8_tmap_1 @ X0 @ X0)))))),
% 0.59/0.80      inference('sup-', [status(thm)], ['116', '122'])).
% 0.59/0.80  thf('124', plain,
% 0.59/0.80      (![X0 : $i]:
% 0.59/0.80         (((k8_tmap_1 @ X0 @ X0)
% 0.59/0.80            = (g1_pre_topc @ (u1_struct_0 @ X0) @ 
% 0.59/0.80               (u1_pre_topc @ (k8_tmap_1 @ X0 @ X0))))
% 0.59/0.80          | ~ (v1_pre_topc @ (k8_tmap_1 @ X0 @ X0))
% 0.59/0.80          | ~ (v2_pre_topc @ X0)
% 0.59/0.80          | (v2_struct_0 @ X0)
% 0.59/0.80          | ~ (l1_pre_topc @ X0))),
% 0.59/0.80      inference('simplify', [status(thm)], ['123'])).
% 0.59/0.80  thf('125', plain,
% 0.59/0.80      (![X0 : $i]:
% 0.59/0.80         (~ (l1_pre_topc @ X0)
% 0.59/0.80          | (v2_struct_0 @ X0)
% 0.59/0.80          | ~ (v2_pre_topc @ X0)
% 0.59/0.80          | ~ (l1_pre_topc @ X0)
% 0.59/0.80          | (v2_struct_0 @ X0)
% 0.59/0.80          | ~ (v2_pre_topc @ X0)
% 0.59/0.80          | ((k8_tmap_1 @ X0 @ X0)
% 0.59/0.80              = (g1_pre_topc @ (u1_struct_0 @ X0) @ 
% 0.59/0.80                 (u1_pre_topc @ (k8_tmap_1 @ X0 @ X0)))))),
% 0.59/0.80      inference('sup-', [status(thm)], ['112', '124'])).
% 0.59/0.80  thf('126', plain,
% 0.59/0.80      (![X0 : $i]:
% 0.59/0.80         (((k8_tmap_1 @ X0 @ X0)
% 0.59/0.80            = (g1_pre_topc @ (u1_struct_0 @ X0) @ 
% 0.59/0.80               (u1_pre_topc @ (k8_tmap_1 @ X0 @ X0))))
% 0.59/0.80          | ~ (v2_pre_topc @ X0)
% 0.59/0.80          | (v2_struct_0 @ X0)
% 0.59/0.80          | ~ (l1_pre_topc @ X0))),
% 0.59/0.80      inference('simplify', [status(thm)], ['125'])).
% 0.59/0.80  thf('127', plain,
% 0.59/0.80      (![X0 : $i]:
% 0.59/0.80         (((k8_tmap_1 @ X0 @ X0)
% 0.59/0.80            = (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.59/0.80          | ~ (v2_pre_topc @ X0)
% 0.59/0.80          | ~ (l1_pre_topc @ X0)
% 0.59/0.80          | ~ (l1_struct_0 @ X0)
% 0.59/0.80          | (v2_struct_0 @ X0)
% 0.59/0.80          | ~ (l1_pre_topc @ X0)
% 0.59/0.80          | (v2_struct_0 @ X0)
% 0.59/0.80          | ~ (v2_pre_topc @ X0))),
% 0.59/0.80      inference('sup+', [status(thm)], ['108', '126'])).
% 0.59/0.80  thf('128', plain,
% 0.59/0.80      (![X0 : $i]:
% 0.59/0.80         ((v2_struct_0 @ X0)
% 0.59/0.80          | ~ (l1_struct_0 @ X0)
% 0.59/0.80          | ~ (l1_pre_topc @ X0)
% 0.59/0.80          | ~ (v2_pre_topc @ X0)
% 0.59/0.80          | ((k8_tmap_1 @ X0 @ X0)
% 0.59/0.80              = (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 0.59/0.80      inference('simplify', [status(thm)], ['127'])).
% 0.59/0.80  thf('129', plain,
% 0.59/0.80      ((((k8_tmap_1 @ sk_A @ sk_A) = (k8_tmap_1 @ sk_A @ sk_B))
% 0.59/0.80        | ~ (v2_pre_topc @ sk_A)
% 0.59/0.80        | ~ (l1_pre_topc @ sk_A)
% 0.59/0.80        | ~ (l1_struct_0 @ sk_A)
% 0.59/0.80        | (v2_struct_0 @ sk_A))),
% 0.59/0.80      inference('sup+', [status(thm)], ['84', '128'])).
% 0.59/0.80  thf('130', plain, ((v2_pre_topc @ sk_A)),
% 0.59/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.80  thf('131', plain, ((l1_pre_topc @ sk_A)),
% 0.59/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.80  thf('132', plain, ((l1_pre_topc @ sk_A)),
% 0.59/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.80  thf(dt_l1_pre_topc, axiom,
% 0.59/0.80    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.59/0.80  thf('133', plain, (![X6 : $i]: ((l1_struct_0 @ X6) | ~ (l1_pre_topc @ X6))),
% 0.59/0.80      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.59/0.80  thf('134', plain, ((l1_struct_0 @ sk_A)),
% 0.59/0.80      inference('sup-', [status(thm)], ['132', '133'])).
% 0.59/0.80  thf('135', plain,
% 0.59/0.80      ((((k8_tmap_1 @ sk_A @ sk_A) = (k8_tmap_1 @ sk_A @ sk_B))
% 0.59/0.80        | (v2_struct_0 @ sk_A))),
% 0.59/0.80      inference('demod', [status(thm)], ['129', '130', '131', '134'])).
% 0.59/0.80  thf('136', plain, (~ (v2_struct_0 @ sk_A)),
% 0.59/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.80  thf('137', plain, (((k8_tmap_1 @ sk_A @ sk_A) = (k8_tmap_1 @ sk_A @ sk_B))),
% 0.59/0.80      inference('clc', [status(thm)], ['135', '136'])).
% 0.59/0.80  thf('138', plain,
% 0.59/0.80      (![X0 : $i]:
% 0.59/0.80         ((v2_struct_0 @ X0)
% 0.59/0.80          | ~ (l1_struct_0 @ X0)
% 0.59/0.80          | ~ (l1_pre_topc @ X0)
% 0.59/0.80          | ~ (v2_pre_topc @ X0)
% 0.59/0.80          | ((u1_pre_topc @ (k8_tmap_1 @ X0 @ X0)) = (u1_pre_topc @ X0)))),
% 0.59/0.80      inference('simplify', [status(thm)], ['107'])).
% 0.59/0.80  thf('139', plain,
% 0.59/0.80      ((((u1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B)) = (u1_pre_topc @ sk_A))
% 0.59/0.80        | ~ (v2_pre_topc @ sk_A)
% 0.59/0.80        | ~ (l1_pre_topc @ sk_A)
% 0.59/0.80        | ~ (l1_struct_0 @ sk_A)
% 0.59/0.80        | (v2_struct_0 @ sk_A))),
% 0.59/0.80      inference('sup+', [status(thm)], ['137', '138'])).
% 0.59/0.80  thf('140', plain, ((v2_pre_topc @ sk_A)),
% 0.59/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.80  thf('141', plain, ((l1_pre_topc @ sk_A)),
% 0.59/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.80  thf('142', plain, ((l1_struct_0 @ sk_A)),
% 0.59/0.80      inference('sup-', [status(thm)], ['132', '133'])).
% 0.59/0.80  thf('143', plain,
% 0.59/0.80      ((((u1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B)) = (u1_pre_topc @ sk_A))
% 0.59/0.80        | (v2_struct_0 @ sk_A))),
% 0.59/0.80      inference('demod', [status(thm)], ['139', '140', '141', '142'])).
% 0.59/0.80  thf('144', plain,
% 0.59/0.80      (![X3 : $i]:
% 0.59/0.80         (((k2_struct_0 @ X3) = (u1_struct_0 @ X3)) | ~ (l1_struct_0 @ X3))),
% 0.59/0.80      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.59/0.80  thf('145', plain,
% 0.59/0.80      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.59/0.80        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.59/0.80      inference('demod', [status(thm)], ['10', '11'])).
% 0.59/0.80  thf('146', plain,
% 0.59/0.80      (((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.59/0.80         (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))
% 0.59/0.80        | ~ (l1_struct_0 @ sk_A))),
% 0.59/0.80      inference('sup+', [status(thm)], ['144', '145'])).
% 0.59/0.80  thf('147', plain, ((l1_struct_0 @ sk_A)),
% 0.59/0.80      inference('sup-', [status(thm)], ['132', '133'])).
% 0.59/0.80  thf('148', plain,
% 0.59/0.80      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.59/0.80        (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))),
% 0.59/0.80      inference('demod', [status(thm)], ['146', '147'])).
% 0.59/0.80  thf('149', plain,
% 0.59/0.80      (![X3 : $i]:
% 0.59/0.80         (((k2_struct_0 @ X3) = (u1_struct_0 @ X3)) | ~ (l1_struct_0 @ X3))),
% 0.59/0.80      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.59/0.80  thf('150', plain,
% 0.59/0.80      (![X13 : $i, X14 : $i]:
% 0.59/0.80         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.59/0.80          | ((u1_pre_topc @ X14) != (k5_tmap_1 @ X14 @ X13))
% 0.59/0.80          | (r2_hidden @ X13 @ (u1_pre_topc @ X14))
% 0.59/0.80          | ~ (l1_pre_topc @ X14)
% 0.59/0.80          | ~ (v2_pre_topc @ X14)
% 0.59/0.80          | (v2_struct_0 @ X14))),
% 0.59/0.80      inference('cnf', [status(esa)], [t103_tmap_1])).
% 0.59/0.80  thf('151', plain,
% 0.59/0.80      (![X0 : $i, X1 : $i]:
% 0.59/0.80         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_struct_0 @ X0)))
% 0.59/0.80          | ~ (l1_struct_0 @ X0)
% 0.59/0.80          | (v2_struct_0 @ X0)
% 0.59/0.80          | ~ (v2_pre_topc @ X0)
% 0.59/0.80          | ~ (l1_pre_topc @ X0)
% 0.59/0.80          | (r2_hidden @ X1 @ (u1_pre_topc @ X0))
% 0.59/0.80          | ((u1_pre_topc @ X0) != (k5_tmap_1 @ X0 @ X1)))),
% 0.59/0.80      inference('sup-', [status(thm)], ['149', '150'])).
% 0.59/0.80  thf('152', plain,
% 0.59/0.80      ((((u1_pre_topc @ sk_A) != (k5_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 0.59/0.80        | (r2_hidden @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_A))
% 0.59/0.80        | ~ (l1_pre_topc @ sk_A)
% 0.59/0.80        | ~ (v2_pre_topc @ sk_A)
% 0.59/0.80        | (v2_struct_0 @ sk_A)
% 0.59/0.80        | ~ (l1_struct_0 @ sk_A))),
% 0.59/0.80      inference('sup-', [status(thm)], ['148', '151'])).
% 0.59/0.80  thf('153', plain,
% 0.59/0.80      (((u1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.59/0.80         = (k5_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))),
% 0.59/0.80      inference('clc', [status(thm)], ['21', '22'])).
% 0.59/0.80  thf('154', plain, ((l1_pre_topc @ sk_A)),
% 0.59/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.80  thf('155', plain, ((v2_pre_topc @ sk_A)),
% 0.59/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.80  thf('156', plain, ((l1_struct_0 @ sk_A)),
% 0.59/0.80      inference('sup-', [status(thm)], ['132', '133'])).
% 0.59/0.80  thf('157', plain,
% 0.59/0.80      ((((u1_pre_topc @ sk_A) != (u1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B)))
% 0.59/0.80        | (r2_hidden @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_A))
% 0.59/0.80        | (v2_struct_0 @ sk_A))),
% 0.59/0.80      inference('demod', [status(thm)], ['152', '153', '154', '155', '156'])).
% 0.59/0.80  thf('158', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.59/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.80  thf('159', plain,
% 0.59/0.80      (![X8 : $i, X9 : $i]:
% 0.59/0.80         (~ (m1_pre_topc @ X8 @ X9)
% 0.59/0.80          | (m1_subset_1 @ (sk_C @ X8 @ X9) @ 
% 0.59/0.80             (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.59/0.80          | (v1_tsep_1 @ X8 @ X9)
% 0.59/0.80          | ~ (l1_pre_topc @ X9))),
% 0.59/0.80      inference('cnf', [status(esa)], [d1_tsep_1])).
% 0.59/0.80  thf('160', plain,
% 0.59/0.80      ((~ (l1_pre_topc @ sk_A)
% 0.59/0.80        | (v1_tsep_1 @ sk_B @ sk_A)
% 0.59/0.80        | (m1_subset_1 @ (sk_C @ sk_B @ sk_A) @ 
% 0.59/0.80           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.59/0.80      inference('sup-', [status(thm)], ['158', '159'])).
% 0.59/0.80  thf('161', plain, ((l1_pre_topc @ sk_A)),
% 0.59/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.80  thf('162', plain,
% 0.59/0.80      (((v1_tsep_1 @ sk_B @ sk_A)
% 0.59/0.80        | (m1_subset_1 @ (sk_C @ sk_B @ sk_A) @ 
% 0.59/0.80           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.59/0.80      inference('demod', [status(thm)], ['160', '161'])).
% 0.59/0.80  thf('163', plain,
% 0.59/0.80      (![X4 : $i, X5 : $i]:
% 0.59/0.80         (~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (u1_struct_0 @ X5)))
% 0.59/0.80          | ~ (r2_hidden @ X4 @ (u1_pre_topc @ X5))
% 0.59/0.80          | (v3_pre_topc @ X4 @ X5)
% 0.59/0.80          | ~ (l1_pre_topc @ X5))),
% 0.59/0.80      inference('cnf', [status(esa)], [d5_pre_topc])).
% 0.59/0.80  thf('164', plain,
% 0.59/0.80      (((v1_tsep_1 @ sk_B @ sk_A)
% 0.59/0.80        | ~ (l1_pre_topc @ sk_A)
% 0.59/0.80        | (v3_pre_topc @ (sk_C @ sk_B @ sk_A) @ sk_A)
% 0.59/0.80        | ~ (r2_hidden @ (sk_C @ sk_B @ sk_A) @ (u1_pre_topc @ sk_A)))),
% 0.59/0.80      inference('sup-', [status(thm)], ['162', '163'])).
% 0.59/0.80  thf('165', plain, ((l1_pre_topc @ sk_A)),
% 0.59/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.80  thf('166', plain,
% 0.59/0.80      (((v1_tsep_1 @ sk_B @ sk_A)
% 0.59/0.80        | (v3_pre_topc @ (sk_C @ sk_B @ sk_A) @ sk_A)
% 0.59/0.80        | ~ (r2_hidden @ (sk_C @ sk_B @ sk_A) @ (u1_pre_topc @ sk_A)))),
% 0.59/0.80      inference('demod', [status(thm)], ['164', '165'])).
% 0.59/0.80  thf('167', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.59/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.80  thf('168', plain,
% 0.59/0.80      (![X8 : $i, X9 : $i]:
% 0.59/0.80         (~ (m1_pre_topc @ X8 @ X9)
% 0.59/0.80          | ((sk_C @ X8 @ X9) = (u1_struct_0 @ X8))
% 0.59/0.80          | (v1_tsep_1 @ X8 @ X9)
% 0.59/0.80          | ~ (l1_pre_topc @ X9))),
% 0.59/0.80      inference('cnf', [status(esa)], [d1_tsep_1])).
% 0.59/0.80  thf('169', plain,
% 0.59/0.80      ((~ (l1_pre_topc @ sk_A)
% 0.59/0.80        | (v1_tsep_1 @ sk_B @ sk_A)
% 0.59/0.80        | ((sk_C @ sk_B @ sk_A) = (u1_struct_0 @ sk_B)))),
% 0.59/0.80      inference('sup-', [status(thm)], ['167', '168'])).
% 0.59/0.80  thf('170', plain, ((l1_pre_topc @ sk_A)),
% 0.59/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.80  thf('171', plain,
% 0.59/0.80      (((v1_tsep_1 @ sk_B @ sk_A)
% 0.59/0.80        | ((sk_C @ sk_B @ sk_A) = (u1_struct_0 @ sk_B)))),
% 0.59/0.80      inference('demod', [status(thm)], ['169', '170'])).
% 0.59/0.80  thf('172', plain,
% 0.59/0.80      ((~ (v1_tsep_1 @ sk_B @ sk_A)) <= (~ ((v1_tsep_1 @ sk_B @ sk_A)))),
% 0.59/0.80      inference('split', [status(esa)], ['3'])).
% 0.59/0.80  thf('173', plain,
% 0.59/0.80      ((((sk_C @ sk_B @ sk_A) = (u1_struct_0 @ sk_B)))
% 0.59/0.80         <= (~ ((v1_tsep_1 @ sk_B @ sk_A)))),
% 0.59/0.80      inference('sup-', [status(thm)], ['171', '172'])).
% 0.59/0.80  thf('174', plain, (~ ((v1_tsep_1 @ sk_B @ sk_A))),
% 0.59/0.80      inference('sat_resolution*', [status(thm)], ['4', '7', '81'])).
% 0.59/0.80  thf('175', plain, (((sk_C @ sk_B @ sk_A) = (u1_struct_0 @ sk_B))),
% 0.59/0.80      inference('simpl_trail', [status(thm)], ['173', '174'])).
% 0.59/0.80  thf('176', plain, (((sk_C @ sk_B @ sk_A) = (u1_struct_0 @ sk_B))),
% 0.59/0.80      inference('simpl_trail', [status(thm)], ['173', '174'])).
% 0.59/0.80  thf('177', plain,
% 0.59/0.80      (((v1_tsep_1 @ sk_B @ sk_A)
% 0.59/0.80        | (v3_pre_topc @ (u1_struct_0 @ sk_B) @ sk_A)
% 0.59/0.80        | ~ (r2_hidden @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_A)))),
% 0.59/0.80      inference('demod', [status(thm)], ['166', '175', '176'])).
% 0.59/0.80  thf('178', plain,
% 0.59/0.80      ((~ (v1_tsep_1 @ sk_B @ sk_A)) <= (~ ((v1_tsep_1 @ sk_B @ sk_A)))),
% 0.59/0.80      inference('split', [status(esa)], ['3'])).
% 0.59/0.80  thf('179', plain, (~ ((v1_tsep_1 @ sk_B @ sk_A))),
% 0.59/0.80      inference('sat_resolution*', [status(thm)], ['4', '7', '81'])).
% 0.59/0.80  thf('180', plain, (~ (v1_tsep_1 @ sk_B @ sk_A)),
% 0.59/0.80      inference('simpl_trail', [status(thm)], ['178', '179'])).
% 0.59/0.80  thf('181', plain,
% 0.59/0.80      ((~ (r2_hidden @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_A))
% 0.59/0.80        | (v3_pre_topc @ (u1_struct_0 @ sk_B) @ sk_A))),
% 0.59/0.80      inference('clc', [status(thm)], ['177', '180'])).
% 0.59/0.80  thf('182', plain,
% 0.59/0.80      ((((sk_C @ sk_B @ sk_A) = (u1_struct_0 @ sk_B)))
% 0.59/0.80         <= (~ ((v1_tsep_1 @ sk_B @ sk_A)))),
% 0.59/0.80      inference('sup-', [status(thm)], ['171', '172'])).
% 0.59/0.80  thf('183', plain,
% 0.59/0.80      (![X8 : $i, X9 : $i]:
% 0.59/0.80         (~ (m1_pre_topc @ X8 @ X9)
% 0.59/0.80          | ~ (v3_pre_topc @ (sk_C @ X8 @ X9) @ X9)
% 0.59/0.80          | (v1_tsep_1 @ X8 @ X9)
% 0.59/0.80          | ~ (l1_pre_topc @ X9))),
% 0.59/0.80      inference('cnf', [status(esa)], [d1_tsep_1])).
% 0.59/0.80  thf('184', plain,
% 0.59/0.80      (((~ (v3_pre_topc @ (u1_struct_0 @ sk_B) @ sk_A)
% 0.59/0.80         | ~ (l1_pre_topc @ sk_A)
% 0.59/0.80         | (v1_tsep_1 @ sk_B @ sk_A)
% 0.59/0.80         | ~ (m1_pre_topc @ sk_B @ sk_A))) <= (~ ((v1_tsep_1 @ sk_B @ sk_A)))),
% 0.59/0.80      inference('sup-', [status(thm)], ['182', '183'])).
% 0.59/0.80  thf('185', plain, ((l1_pre_topc @ sk_A)),
% 0.59/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.80  thf('186', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.59/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.80  thf('187', plain,
% 0.59/0.80      (((~ (v3_pre_topc @ (u1_struct_0 @ sk_B) @ sk_A)
% 0.59/0.80         | (v1_tsep_1 @ sk_B @ sk_A))) <= (~ ((v1_tsep_1 @ sk_B @ sk_A)))),
% 0.59/0.80      inference('demod', [status(thm)], ['184', '185', '186'])).
% 0.59/0.80  thf('188', plain,
% 0.59/0.80      ((~ (v1_tsep_1 @ sk_B @ sk_A)) <= (~ ((v1_tsep_1 @ sk_B @ sk_A)))),
% 0.59/0.80      inference('split', [status(esa)], ['3'])).
% 0.59/0.80  thf('189', plain,
% 0.59/0.80      ((~ (v3_pre_topc @ (u1_struct_0 @ sk_B) @ sk_A))
% 0.59/0.80         <= (~ ((v1_tsep_1 @ sk_B @ sk_A)))),
% 0.59/0.80      inference('clc', [status(thm)], ['187', '188'])).
% 0.59/0.80  thf('190', plain, (~ ((v1_tsep_1 @ sk_B @ sk_A))),
% 0.59/0.80      inference('sat_resolution*', [status(thm)], ['4', '7', '81'])).
% 0.59/0.80  thf('191', plain, (~ (v3_pre_topc @ (u1_struct_0 @ sk_B) @ sk_A)),
% 0.59/0.80      inference('simpl_trail', [status(thm)], ['189', '190'])).
% 0.59/0.80  thf('192', plain,
% 0.59/0.80      (~ (r2_hidden @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_A))),
% 0.59/0.80      inference('clc', [status(thm)], ['181', '191'])).
% 0.59/0.80  thf('193', plain,
% 0.59/0.80      (((v2_struct_0 @ sk_A)
% 0.59/0.80        | ((u1_pre_topc @ sk_A) != (u1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))))),
% 0.59/0.80      inference('clc', [status(thm)], ['157', '192'])).
% 0.59/0.80  thf('194', plain, (~ (v2_struct_0 @ sk_A)),
% 0.59/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.80  thf('195', plain,
% 0.59/0.80      (((u1_pre_topc @ sk_A) != (u1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B)))),
% 0.59/0.80      inference('clc', [status(thm)], ['193', '194'])).
% 0.59/0.80  thf('196', plain, ((v2_struct_0 @ sk_A)),
% 0.59/0.80      inference('simplify_reflect-', [status(thm)], ['143', '195'])).
% 0.59/0.80  thf('197', plain, ($false), inference('demod', [status(thm)], ['0', '196'])).
% 0.59/0.80  
% 0.59/0.80  % SZS output end Refutation
% 0.59/0.80  
% 0.59/0.80  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
