%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Tt5uNbm6EY

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:10:57 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  167 ( 615 expanded)
%              Number of leaves         :   28 ( 179 expanded)
%              Depth                    :   15
%              Number of atoms          : 1527 (9849 expanded)
%              Number of equality atoms :   61 ( 392 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(g1_pre_topc_type,type,(
    g1_pre_topc: $i > $i > $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(k8_tmap_1_type,type,(
    k8_tmap_1: $i > $i > $i )).

thf(v1_tsep_1_type,type,(
    v1_tsep_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k5_tmap_1_type,type,(
    k5_tmap_1: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

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
    ! [X6: $i,X7: $i] :
      ( ~ ( m1_pre_topc @ X6 @ X7 )
      | ( ( sk_C @ X6 @ X7 )
        = ( u1_struct_0 @ X6 ) )
      | ( v1_tsep_1 @ X6 @ X7 )
      | ~ ( l1_pre_topc @ X7 ) ) ),
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
    ! [X6: $i,X7: $i] :
      ( ~ ( m1_pre_topc @ X6 @ X7 )
      | ( m1_subset_1 @ ( sk_C @ X6 @ X7 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) )
      | ( v1_tsep_1 @ X6 @ X7 )
      | ~ ( l1_pre_topc @ X7 ) ) ),
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

thf('13',plain,
    ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k8_tmap_1 @ sk_A @ sk_B ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['13'])).

thf(t60_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ( v3_pre_topc @ B @ A )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
        <=> ( ( v3_pre_topc @ B @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ) ) ) ) )).

thf('15',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v3_pre_topc @ X3 @ ( g1_pre_topc @ ( u1_struct_0 @ X4 ) @ ( u1_pre_topc @ X4 ) ) )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X4 ) @ ( u1_pre_topc @ X4 ) ) ) ) )
      | ( v3_pre_topc @ X3 @ X4 )
      | ~ ( l1_pre_topc @ X4 )
      | ~ ( v2_pre_topc @ X4 ) ) ),
    inference(cnf,[status(esa)],[t60_pre_topc])).

thf('16',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) )
        | ~ ( v2_pre_topc @ sk_A )
        | ~ ( l1_pre_topc @ sk_A )
        | ( v3_pre_topc @ X0 @ sk_A )
        | ~ ( v3_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
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

thf('18',plain,(
    ! [X15: $i,X16: $i] :
      ( ( v2_struct_0 @ X15 )
      | ~ ( m1_pre_topc @ X15 @ X16 )
      | ( ( u1_struct_0 @ ( k8_tmap_1 @ X16 @ X15 ) )
        = ( u1_struct_0 @ X16 ) )
      | ~ ( l1_pre_topc @ X16 )
      | ~ ( v2_pre_topc @ X16 )
      | ( v2_struct_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t114_tmap_1])).

thf('19',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
      = ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
      = ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['19','20','21'])).

thf('23',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['22','23'])).

thf('25',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['24','25'])).

thf('27',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k8_tmap_1 @ sk_A @ sk_B ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['13'])).

thf('30',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( v3_pre_topc @ X0 @ sk_A )
        | ~ ( v3_pre_topc @ X0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['16','26','27','28','29'])).

thf('31',plain,
    ( ( ( v1_tsep_1 @ sk_B @ sk_A )
      | ~ ( v3_pre_topc @ ( sk_C @ sk_B @ sk_A ) @ ( k8_tmap_1 @ sk_A @ sk_B ) )
      | ( v3_pre_topc @ ( sk_C @ sk_B @ sk_A ) @ sk_A ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['12','30'])).

thf('32',plain,
    ( ( ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( k8_tmap_1 @ sk_A @ sk_B ) )
      | ( v3_pre_topc @ ( sk_C @ sk_B @ sk_A ) @ sk_A )
      | ( v1_tsep_1 @ sk_B @ sk_A ) )
   <= ( ~ ( v1_tsep_1 @ sk_B @ sk_A )
      & ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
        = ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['7','31'])).

thf('33',plain,
    ( ( ( sk_C @ sk_B @ sk_A )
      = ( u1_struct_0 @ sk_B ) )
   <= ~ ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['4','6'])).

thf('34',plain,
    ( ( ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( k8_tmap_1 @ sk_A @ sk_B ) )
      | ( v3_pre_topc @ ( u1_struct_0 @ sk_B ) @ sk_A )
      | ( v1_tsep_1 @ sk_B @ sk_A ) )
   <= ( ~ ( v1_tsep_1 @ sk_B @ sk_A )
      & ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
        = ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,
    ( ( ( sk_C @ sk_B @ sk_A )
      = ( u1_struct_0 @ sk_B ) )
   <= ~ ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['4','6'])).

thf('36',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( m1_pre_topc @ X6 @ X7 )
      | ~ ( v3_pre_topc @ ( sk_C @ X6 @ X7 ) @ X7 )
      | ( v1_tsep_1 @ X6 @ X7 )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[d1_tsep_1])).

thf('37',plain,
    ( ( ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_B ) @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v1_tsep_1 @ sk_B @ sk_A )
      | ~ ( m1_pre_topc @ sk_B @ sk_A ) )
   <= ~ ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,
    ( ( ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_B ) @ sk_A )
      | ( v1_tsep_1 @ sk_B @ sk_A ) )
   <= ~ ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['37','38','39'])).

thf('41',plain,
    ( ~ ( v1_tsep_1 @ sk_B @ sk_A )
   <= ~ ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['5'])).

thf('42',plain,
    ( ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_B ) @ sk_A )
   <= ~ ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['40','41'])).

thf('43',plain,
    ( ( ( v1_tsep_1 @ sk_B @ sk_A )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( k8_tmap_1 @ sk_A @ sk_B ) ) )
   <= ( ~ ( v1_tsep_1 @ sk_B @ sk_A )
      & ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
        = ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['34','42'])).

thf('44',plain,
    ( ~ ( v1_tsep_1 @ sk_B @ sk_A )
   <= ~ ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['5'])).

thf('45',plain,
    ( ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( k8_tmap_1 @ sk_A @ sk_B ) )
   <= ( ~ ( v1_tsep_1 @ sk_B @ sk_A )
      & ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
        = ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['43','44'])).

thf('46',plain,
    ( ~ ( v1_tsep_1 @ sk_B @ sk_A )
    | ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
     != ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['5'])).

thf('47',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,
    ( ~ ( m1_pre_topc @ sk_B @ sk_A )
   <= ~ ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['5'])).

thf('49',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,
    ( ( v1_tsep_1 @ sk_B @ sk_A )
   <= ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['13'])).

thf('51',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t1_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( m1_subset_1 @ ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('52',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( m1_pre_topc @ X18 @ X19 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X18 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( l1_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('53',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( m1_pre_topc @ X6 @ X7 )
      | ~ ( v1_tsep_1 @ X6 @ X7 )
      | ( X8
       != ( u1_struct_0 @ X6 ) )
      | ( v3_pre_topc @ X8 @ X7 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[d1_tsep_1])).

thf('57',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( l1_pre_topc @ X7 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X6 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) )
      | ( v3_pre_topc @ ( u1_struct_0 @ X6 ) @ X7 )
      | ~ ( v1_tsep_1 @ X6 @ X7 )
      | ~ ( m1_pre_topc @ X6 @ X7 ) ) ),
    inference(simplify,[status(thm)],['56'])).

thf('58',plain,
    ( ~ ( m1_pre_topc @ sk_B @ sk_A )
    | ~ ( v1_tsep_1 @ sk_B @ sk_A )
    | ( v3_pre_topc @ ( u1_struct_0 @ sk_B ) @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['55','57'])).

thf('59',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,
    ( ~ ( v1_tsep_1 @ sk_B @ sk_A )
    | ( v3_pre_topc @ ( u1_struct_0 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['58','59','60'])).

thf('62',plain,
    ( ( v3_pre_topc @ ( u1_struct_0 @ sk_B ) @ sk_A )
   <= ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['50','61'])).

thf('63',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['53','54'])).

thf(d5_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v3_pre_topc @ B @ A )
          <=> ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) ) ) ) )).

thf('64',plain,(
    ! [X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X2 ) ) )
      | ~ ( v3_pre_topc @ X1 @ X2 )
      | ( r2_hidden @ X1 @ ( u1_pre_topc @ X2 ) )
      | ~ ( l1_pre_topc @ X2 ) ) ),
    inference(cnf,[status(esa)],[d5_pre_topc])).

thf('65',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r2_hidden @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_A ) )
    | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,
    ( ( r2_hidden @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_A ) )
    | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['65','66'])).

thf('68',plain,
    ( ( r2_hidden @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_A ) )
   <= ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['62','67'])).

thf('69',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['53','54'])).

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

thf('70',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( r2_hidden @ X13 @ ( u1_pre_topc @ X14 ) )
      | ( ( u1_pre_topc @ X14 )
        = ( k5_tmap_1 @ X14 @ X13 ) )
      | ~ ( l1_pre_topc @ X14 )
      | ~ ( v2_pre_topc @ X14 )
      | ( v2_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t103_tmap_1])).

thf('71',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( ( u1_pre_topc @ sk_A )
      = ( k5_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
    | ~ ( r2_hidden @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( u1_pre_topc @ sk_A )
      = ( k5_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
    | ~ ( r2_hidden @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_A ) ) ),
    inference(demod,[status(thm)],['71','72','73'])).

thf('75',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,
    ( ~ ( r2_hidden @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_A ) )
    | ( ( u1_pre_topc @ sk_A )
      = ( k5_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['74','75'])).

thf('77',plain,
    ( ( ( u1_pre_topc @ sk_A )
      = ( k5_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
   <= ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['68','76'])).

thf('78',plain,
    ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['24','25'])).

thf(abstractness_v1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( ( v1_pre_topc @ A )
       => ( A
          = ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ) )).

thf('79',plain,(
    ! [X0: $i] :
      ( ~ ( v1_pre_topc @ X0 )
      | ( X0
        = ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(cnf,[status(esa)],[abstractness_v1_pre_topc])).

thf('80',plain,
    ( ( ( k8_tmap_1 @ sk_A @ sk_B )
      = ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) )
    | ~ ( l1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( v1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['78','79'])).

thf('81',plain,(
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

thf('82',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( l1_pre_topc @ X9 )
      | ~ ( v2_pre_topc @ X9 )
      | ( v2_struct_0 @ X9 )
      | ~ ( m1_pre_topc @ X10 @ X9 )
      | ( l1_pre_topc @ ( k8_tmap_1 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k8_tmap_1])).

thf('83',plain,
    ( ( l1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,
    ( ( l1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['83','84','85'])).

thf('87',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    l1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['86','87'])).

thf('89',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( l1_pre_topc @ X9 )
      | ~ ( v2_pre_topc @ X9 )
      | ( v2_struct_0 @ X9 )
      | ~ ( m1_pre_topc @ X10 @ X9 )
      | ( v1_pre_topc @ ( k8_tmap_1 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k8_tmap_1])).

thf('91',plain,
    ( ( v1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,
    ( ( v1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['91','92','93'])).

thf('95',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    v1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['94','95'])).

thf('97',plain,
    ( ( k8_tmap_1 @ sk_A @ sk_B )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['80','88','96'])).

thf('98',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('99',plain,(
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

thf('100',plain,(
    ! [X15: $i,X16: $i] :
      ( ( v2_struct_0 @ X16 )
      | ~ ( v2_pre_topc @ X16 )
      | ~ ( l1_pre_topc @ X16 )
      | ( ( u1_pre_topc @ ( k8_tmap_1 @ X16 @ X15 ) )
        = ( k5_tmap_1 @ X16 @ ( u1_struct_0 @ X15 ) ) )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X15 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( m1_pre_topc @ X15 @ X16 )
      | ( v2_struct_0 @ X15 ) ) ),
    inference(simplify,[status(thm)],['99'])).

thf('101',plain,
    ( ( v2_struct_0 @ sk_B )
    | ~ ( m1_pre_topc @ sk_B @ sk_A )
    | ( ( u1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
      = ( k5_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['98','100'])).

thf('102',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( u1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
      = ( k5_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['101','102','103','104'])).

thf('106',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( u1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
      = ( k5_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['105','106'])).

thf('108',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,
    ( ( u1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    = ( k5_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['107','108'])).

thf('110',plain,
    ( ( k8_tmap_1 @ sk_A @ sk_B )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( k5_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['97','109'])).

thf('111',plain,
    ( ( ( k8_tmap_1 @ sk_A @ sk_B )
      = ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
   <= ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['77','110'])).

thf('112',plain,
    ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
     != ( k8_tmap_1 @ sk_A @ sk_B ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
     != ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['5'])).

thf('113',plain,
    ( ( ( k8_tmap_1 @ sk_A @ sk_B )
     != ( k8_tmap_1 @ sk_A @ sk_B ) )
   <= ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
       != ( k8_tmap_1 @ sk_A @ sk_B ) )
      & ( v1_tsep_1 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['111','112'])).

thf('114',plain,
    ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['113'])).

thf('115',plain,(
    ~ ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['46','49','114'])).

thf('116',plain,
    ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['13'])).

thf('117',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
    = ( k8_tmap_1 @ sk_A @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['46','49','114','116'])).

thf('118',plain,(
    ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(simpl_trail,[status(thm)],['45','115','117'])).

thf('119',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['53','54'])).

thf(t102_tmap_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r2_hidden @ B @ ( k5_tmap_1 @ A @ B ) ) ) ) )).

thf('120',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ( r2_hidden @ X11 @ ( k5_tmap_1 @ X12 @ X11 ) )
      | ~ ( l1_pre_topc @ X12 )
      | ~ ( v2_pre_topc @ X12 )
      | ( v2_struct_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t102_tmap_1])).

thf('121',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( r2_hidden @ ( u1_struct_0 @ sk_B ) @ ( k5_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['119','120'])).

thf('122',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ ( u1_struct_0 @ sk_B ) @ ( k5_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['121','122','123'])).

thf('125',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,(
    r2_hidden @ ( u1_struct_0 @ sk_B ) @ ( k5_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['124','125'])).

thf('127',plain,
    ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['24','25'])).

thf('128',plain,(
    ! [X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X2 ) ) )
      | ~ ( r2_hidden @ X1 @ ( u1_pre_topc @ X2 ) )
      | ( v3_pre_topc @ X1 @ X2 )
      | ~ ( l1_pre_topc @ X2 ) ) ),
    inference(cnf,[status(esa)],[d5_pre_topc])).

thf('129',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( l1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
      | ( v3_pre_topc @ X0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ ( u1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['127','128'])).

thf('130',plain,(
    l1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['86','87'])).

thf('131',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v3_pre_topc @ X0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ ( u1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['129','130'])).

thf('132',plain,
    ( ( u1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    = ( k5_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['107','108'])).

thf('133',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v3_pre_topc @ X0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ ( k5_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['131','132'])).

thf('134',plain,
    ( ( v3_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['126','133'])).

thf('135',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('136',plain,(
    v3_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( k8_tmap_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['134','135'])).

thf('137',plain,(
    $false ),
    inference(demod,[status(thm)],['118','136'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Tt5uNbm6EY
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:50:42 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.54  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.54  % Solved by: fo/fo7.sh
% 0.20/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.54  % done 158 iterations in 0.075s
% 0.20/0.54  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.54  % SZS output start Refutation
% 0.20/0.54  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.54  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.20/0.54  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.54  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 0.20/0.54  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.20/0.54  thf(g1_pre_topc_type, type, g1_pre_topc: $i > $i > $i).
% 0.20/0.54  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.20/0.54  thf(k8_tmap_1_type, type, k8_tmap_1: $i > $i > $i).
% 0.20/0.54  thf(v1_tsep_1_type, type, v1_tsep_1: $i > $i > $o).
% 0.20/0.54  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.20/0.54  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 0.20/0.54  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.20/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.54  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.54  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.54  thf(k5_tmap_1_type, type, k5_tmap_1: $i > $i > $i).
% 0.20/0.54  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.54  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.20/0.54  thf(t116_tmap_1, conjecture,
% 0.20/0.54    (![A:$i]:
% 0.20/0.54     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.54       ( ![B:$i]:
% 0.20/0.54         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.20/0.54           ( ( ( v1_tsep_1 @ B @ A ) & ( m1_pre_topc @ B @ A ) ) <=>
% 0.20/0.54             ( ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) =
% 0.20/0.54               ( k8_tmap_1 @ A @ B ) ) ) ) ) ))).
% 0.20/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.54    (~( ![A:$i]:
% 0.20/0.54        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.20/0.54            ( l1_pre_topc @ A ) ) =>
% 0.20/0.54          ( ![B:$i]:
% 0.20/0.54            ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.20/0.54              ( ( ( v1_tsep_1 @ B @ A ) & ( m1_pre_topc @ B @ A ) ) <=>
% 0.20/0.54                ( ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) =
% 0.20/0.54                  ( k8_tmap_1 @ A @ B ) ) ) ) ) ) )),
% 0.20/0.54    inference('cnf.neg', [status(esa)], [t116_tmap_1])).
% 0.20/0.54  thf('0', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf(d1_tsep_1, axiom,
% 0.20/0.54    (![A:$i]:
% 0.20/0.54     ( ( l1_pre_topc @ A ) =>
% 0.20/0.54       ( ![B:$i]:
% 0.20/0.54         ( ( m1_pre_topc @ B @ A ) =>
% 0.20/0.54           ( ( v1_tsep_1 @ B @ A ) <=>
% 0.20/0.54             ( ![C:$i]:
% 0.20/0.54               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.54                 ( ( ( C ) = ( u1_struct_0 @ B ) ) => ( v3_pre_topc @ C @ A ) ) ) ) ) ) ) ))).
% 0.20/0.54  thf('1', plain,
% 0.20/0.54      (![X6 : $i, X7 : $i]:
% 0.20/0.54         (~ (m1_pre_topc @ X6 @ X7)
% 0.20/0.54          | ((sk_C @ X6 @ X7) = (u1_struct_0 @ X6))
% 0.20/0.54          | (v1_tsep_1 @ X6 @ X7)
% 0.20/0.54          | ~ (l1_pre_topc @ X7))),
% 0.20/0.54      inference('cnf', [status(esa)], [d1_tsep_1])).
% 0.20/0.54  thf('2', plain,
% 0.20/0.54      ((~ (l1_pre_topc @ sk_A)
% 0.20/0.54        | (v1_tsep_1 @ sk_B @ sk_A)
% 0.20/0.54        | ((sk_C @ sk_B @ sk_A) = (u1_struct_0 @ sk_B)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['0', '1'])).
% 0.20/0.54  thf('3', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('4', plain,
% 0.20/0.54      (((v1_tsep_1 @ sk_B @ sk_A)
% 0.20/0.54        | ((sk_C @ sk_B @ sk_A) = (u1_struct_0 @ sk_B)))),
% 0.20/0.54      inference('demod', [status(thm)], ['2', '3'])).
% 0.20/0.54  thf('5', plain,
% 0.20/0.54      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.20/0.54          != (k8_tmap_1 @ sk_A @ sk_B))
% 0.20/0.54        | ~ (m1_pre_topc @ sk_B @ sk_A)
% 0.20/0.54        | ~ (v1_tsep_1 @ sk_B @ sk_A))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('6', plain,
% 0.20/0.54      ((~ (v1_tsep_1 @ sk_B @ sk_A)) <= (~ ((v1_tsep_1 @ sk_B @ sk_A)))),
% 0.20/0.54      inference('split', [status(esa)], ['5'])).
% 0.20/0.54  thf('7', plain,
% 0.20/0.54      ((((sk_C @ sk_B @ sk_A) = (u1_struct_0 @ sk_B)))
% 0.20/0.54         <= (~ ((v1_tsep_1 @ sk_B @ sk_A)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['4', '6'])).
% 0.20/0.54  thf('8', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('9', plain,
% 0.20/0.54      (![X6 : $i, X7 : $i]:
% 0.20/0.54         (~ (m1_pre_topc @ X6 @ X7)
% 0.20/0.54          | (m1_subset_1 @ (sk_C @ X6 @ X7) @ 
% 0.20/0.54             (k1_zfmisc_1 @ (u1_struct_0 @ X7)))
% 0.20/0.54          | (v1_tsep_1 @ X6 @ X7)
% 0.20/0.54          | ~ (l1_pre_topc @ X7))),
% 0.20/0.54      inference('cnf', [status(esa)], [d1_tsep_1])).
% 0.20/0.54  thf('10', plain,
% 0.20/0.54      ((~ (l1_pre_topc @ sk_A)
% 0.20/0.54        | (v1_tsep_1 @ sk_B @ sk_A)
% 0.20/0.54        | (m1_subset_1 @ (sk_C @ sk_B @ sk_A) @ 
% 0.20/0.54           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.54      inference('sup-', [status(thm)], ['8', '9'])).
% 0.20/0.54  thf('11', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('12', plain,
% 0.20/0.54      (((v1_tsep_1 @ sk_B @ sk_A)
% 0.20/0.54        | (m1_subset_1 @ (sk_C @ sk_B @ sk_A) @ 
% 0.20/0.54           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.54      inference('demod', [status(thm)], ['10', '11'])).
% 0.20/0.54  thf('13', plain,
% 0.20/0.54      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.20/0.54          = (k8_tmap_1 @ sk_A @ sk_B))
% 0.20/0.54        | (v1_tsep_1 @ sk_B @ sk_A))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('14', plain,
% 0.20/0.54      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.20/0.54          = (k8_tmap_1 @ sk_A @ sk_B)))
% 0.20/0.54         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.20/0.54                = (k8_tmap_1 @ sk_A @ sk_B))))),
% 0.20/0.54      inference('split', [status(esa)], ['13'])).
% 0.20/0.54  thf(t60_pre_topc, axiom,
% 0.20/0.54    (![A:$i]:
% 0.20/0.54     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.54       ( ![B:$i]:
% 0.20/0.54         ( ( ( v3_pre_topc @ B @ A ) & 
% 0.20/0.54             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) <=>
% 0.20/0.54           ( ( v3_pre_topc @
% 0.20/0.54               B @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) & 
% 0.20/0.54             ( m1_subset_1 @
% 0.20/0.54               B @ 
% 0.20/0.54               ( k1_zfmisc_1 @
% 0.20/0.54                 ( u1_struct_0 @
% 0.20/0.54                   ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ) ) ) ) ))).
% 0.20/0.54  thf('15', plain,
% 0.20/0.54      (![X3 : $i, X4 : $i]:
% 0.20/0.54         (~ (v3_pre_topc @ X3 @ 
% 0.20/0.54             (g1_pre_topc @ (u1_struct_0 @ X4) @ (u1_pre_topc @ X4)))
% 0.20/0.54          | ~ (m1_subset_1 @ X3 @ 
% 0.20/0.54               (k1_zfmisc_1 @ 
% 0.20/0.54                (u1_struct_0 @ 
% 0.20/0.54                 (g1_pre_topc @ (u1_struct_0 @ X4) @ (u1_pre_topc @ X4)))))
% 0.20/0.54          | (v3_pre_topc @ X3 @ X4)
% 0.20/0.54          | ~ (l1_pre_topc @ X4)
% 0.20/0.54          | ~ (v2_pre_topc @ X4))),
% 0.20/0.54      inference('cnf', [status(esa)], [t60_pre_topc])).
% 0.20/0.54  thf('16', plain,
% 0.20/0.54      ((![X0 : $i]:
% 0.20/0.54          (~ (m1_subset_1 @ X0 @ 
% 0.20/0.54              (k1_zfmisc_1 @ (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B))))
% 0.20/0.54           | ~ (v2_pre_topc @ sk_A)
% 0.20/0.54           | ~ (l1_pre_topc @ sk_A)
% 0.20/0.54           | (v3_pre_topc @ X0 @ sk_A)
% 0.20/0.54           | ~ (v3_pre_topc @ X0 @ 
% 0.20/0.54                (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))
% 0.20/0.54         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.20/0.54                = (k8_tmap_1 @ sk_A @ sk_B))))),
% 0.20/0.54      inference('sup-', [status(thm)], ['14', '15'])).
% 0.20/0.54  thf('17', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf(t114_tmap_1, axiom,
% 0.20/0.54    (![A:$i]:
% 0.20/0.54     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.54       ( ![B:$i]:
% 0.20/0.54         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.20/0.54           ( ( ( u1_struct_0 @ ( k8_tmap_1 @ A @ B ) ) = ( u1_struct_0 @ A ) ) & 
% 0.20/0.54             ( ![C:$i]:
% 0.20/0.54               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.54                 ( ( ( C ) = ( u1_struct_0 @ B ) ) =>
% 0.20/0.54                   ( ( u1_pre_topc @ ( k8_tmap_1 @ A @ B ) ) =
% 0.20/0.54                     ( k5_tmap_1 @ A @ C ) ) ) ) ) ) ) ) ))).
% 0.20/0.54  thf('18', plain,
% 0.20/0.54      (![X15 : $i, X16 : $i]:
% 0.20/0.54         ((v2_struct_0 @ X15)
% 0.20/0.54          | ~ (m1_pre_topc @ X15 @ X16)
% 0.20/0.54          | ((u1_struct_0 @ (k8_tmap_1 @ X16 @ X15)) = (u1_struct_0 @ X16))
% 0.20/0.54          | ~ (l1_pre_topc @ X16)
% 0.20/0.54          | ~ (v2_pre_topc @ X16)
% 0.20/0.54          | (v2_struct_0 @ X16))),
% 0.20/0.54      inference('cnf', [status(esa)], [t114_tmap_1])).
% 0.20/0.54  thf('19', plain,
% 0.20/0.54      (((v2_struct_0 @ sk_A)
% 0.20/0.54        | ~ (v2_pre_topc @ sk_A)
% 0.20/0.54        | ~ (l1_pre_topc @ sk_A)
% 0.20/0.54        | ((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))
% 0.20/0.54        | (v2_struct_0 @ sk_B))),
% 0.20/0.54      inference('sup-', [status(thm)], ['17', '18'])).
% 0.20/0.54  thf('20', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('21', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('22', plain,
% 0.20/0.54      (((v2_struct_0 @ sk_A)
% 0.20/0.54        | ((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))
% 0.20/0.54        | (v2_struct_0 @ sk_B))),
% 0.20/0.54      inference('demod', [status(thm)], ['19', '20', '21'])).
% 0.20/0.54  thf('23', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('24', plain,
% 0.20/0.54      (((v2_struct_0 @ sk_B)
% 0.20/0.54        | ((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A)))),
% 0.20/0.54      inference('clc', [status(thm)], ['22', '23'])).
% 0.20/0.54  thf('25', plain, (~ (v2_struct_0 @ sk_B)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('26', plain,
% 0.20/0.54      (((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 0.20/0.54      inference('clc', [status(thm)], ['24', '25'])).
% 0.20/0.54  thf('27', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('28', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('29', plain,
% 0.20/0.54      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.20/0.54          = (k8_tmap_1 @ sk_A @ sk_B)))
% 0.20/0.54         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.20/0.54                = (k8_tmap_1 @ sk_A @ sk_B))))),
% 0.20/0.54      inference('split', [status(esa)], ['13'])).
% 0.20/0.54  thf('30', plain,
% 0.20/0.54      ((![X0 : $i]:
% 0.20/0.54          (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.54           | (v3_pre_topc @ X0 @ sk_A)
% 0.20/0.54           | ~ (v3_pre_topc @ X0 @ (k8_tmap_1 @ sk_A @ sk_B))))
% 0.20/0.54         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.20/0.54                = (k8_tmap_1 @ sk_A @ sk_B))))),
% 0.20/0.54      inference('demod', [status(thm)], ['16', '26', '27', '28', '29'])).
% 0.20/0.54  thf('31', plain,
% 0.20/0.54      ((((v1_tsep_1 @ sk_B @ sk_A)
% 0.20/0.54         | ~ (v3_pre_topc @ (sk_C @ sk_B @ sk_A) @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.20/0.54         | (v3_pre_topc @ (sk_C @ sk_B @ sk_A) @ sk_A)))
% 0.20/0.54         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.20/0.54                = (k8_tmap_1 @ sk_A @ sk_B))))),
% 0.20/0.54      inference('sup-', [status(thm)], ['12', '30'])).
% 0.20/0.54  thf('32', plain,
% 0.20/0.54      (((~ (v3_pre_topc @ (u1_struct_0 @ sk_B) @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.20/0.54         | (v3_pre_topc @ (sk_C @ sk_B @ sk_A) @ sk_A)
% 0.20/0.54         | (v1_tsep_1 @ sk_B @ sk_A)))
% 0.20/0.54         <= (~ ((v1_tsep_1 @ sk_B @ sk_A)) & 
% 0.20/0.54             (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.20/0.54                = (k8_tmap_1 @ sk_A @ sk_B))))),
% 0.20/0.54      inference('sup-', [status(thm)], ['7', '31'])).
% 0.20/0.54  thf('33', plain,
% 0.20/0.54      ((((sk_C @ sk_B @ sk_A) = (u1_struct_0 @ sk_B)))
% 0.20/0.54         <= (~ ((v1_tsep_1 @ sk_B @ sk_A)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['4', '6'])).
% 0.20/0.54  thf('34', plain,
% 0.20/0.54      (((~ (v3_pre_topc @ (u1_struct_0 @ sk_B) @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.20/0.54         | (v3_pre_topc @ (u1_struct_0 @ sk_B) @ sk_A)
% 0.20/0.54         | (v1_tsep_1 @ sk_B @ sk_A)))
% 0.20/0.54         <= (~ ((v1_tsep_1 @ sk_B @ sk_A)) & 
% 0.20/0.54             (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.20/0.54                = (k8_tmap_1 @ sk_A @ sk_B))))),
% 0.20/0.54      inference('demod', [status(thm)], ['32', '33'])).
% 0.20/0.54  thf('35', plain,
% 0.20/0.54      ((((sk_C @ sk_B @ sk_A) = (u1_struct_0 @ sk_B)))
% 0.20/0.54         <= (~ ((v1_tsep_1 @ sk_B @ sk_A)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['4', '6'])).
% 0.20/0.54  thf('36', plain,
% 0.20/0.54      (![X6 : $i, X7 : $i]:
% 0.20/0.54         (~ (m1_pre_topc @ X6 @ X7)
% 0.20/0.54          | ~ (v3_pre_topc @ (sk_C @ X6 @ X7) @ X7)
% 0.20/0.54          | (v1_tsep_1 @ X6 @ X7)
% 0.20/0.54          | ~ (l1_pre_topc @ X7))),
% 0.20/0.54      inference('cnf', [status(esa)], [d1_tsep_1])).
% 0.20/0.54  thf('37', plain,
% 0.20/0.54      (((~ (v3_pre_topc @ (u1_struct_0 @ sk_B) @ sk_A)
% 0.20/0.54         | ~ (l1_pre_topc @ sk_A)
% 0.20/0.54         | (v1_tsep_1 @ sk_B @ sk_A)
% 0.20/0.54         | ~ (m1_pre_topc @ sk_B @ sk_A))) <= (~ ((v1_tsep_1 @ sk_B @ sk_A)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['35', '36'])).
% 0.20/0.54  thf('38', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('39', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('40', plain,
% 0.20/0.54      (((~ (v3_pre_topc @ (u1_struct_0 @ sk_B) @ sk_A)
% 0.20/0.54         | (v1_tsep_1 @ sk_B @ sk_A))) <= (~ ((v1_tsep_1 @ sk_B @ sk_A)))),
% 0.20/0.54      inference('demod', [status(thm)], ['37', '38', '39'])).
% 0.20/0.54  thf('41', plain,
% 0.20/0.54      ((~ (v1_tsep_1 @ sk_B @ sk_A)) <= (~ ((v1_tsep_1 @ sk_B @ sk_A)))),
% 0.20/0.54      inference('split', [status(esa)], ['5'])).
% 0.20/0.54  thf('42', plain,
% 0.20/0.54      ((~ (v3_pre_topc @ (u1_struct_0 @ sk_B) @ sk_A))
% 0.20/0.54         <= (~ ((v1_tsep_1 @ sk_B @ sk_A)))),
% 0.20/0.54      inference('clc', [status(thm)], ['40', '41'])).
% 0.20/0.54  thf('43', plain,
% 0.20/0.54      ((((v1_tsep_1 @ sk_B @ sk_A)
% 0.20/0.54         | ~ (v3_pre_topc @ (u1_struct_0 @ sk_B) @ (k8_tmap_1 @ sk_A @ sk_B))))
% 0.20/0.54         <= (~ ((v1_tsep_1 @ sk_B @ sk_A)) & 
% 0.20/0.54             (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.20/0.54                = (k8_tmap_1 @ sk_A @ sk_B))))),
% 0.20/0.54      inference('clc', [status(thm)], ['34', '42'])).
% 0.20/0.54  thf('44', plain,
% 0.20/0.54      ((~ (v1_tsep_1 @ sk_B @ sk_A)) <= (~ ((v1_tsep_1 @ sk_B @ sk_A)))),
% 0.20/0.54      inference('split', [status(esa)], ['5'])).
% 0.20/0.54  thf('45', plain,
% 0.20/0.54      ((~ (v3_pre_topc @ (u1_struct_0 @ sk_B) @ (k8_tmap_1 @ sk_A @ sk_B)))
% 0.20/0.54         <= (~ ((v1_tsep_1 @ sk_B @ sk_A)) & 
% 0.20/0.54             (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.20/0.54                = (k8_tmap_1 @ sk_A @ sk_B))))),
% 0.20/0.54      inference('clc', [status(thm)], ['43', '44'])).
% 0.20/0.54  thf('46', plain,
% 0.20/0.54      (~ ((v1_tsep_1 @ sk_B @ sk_A)) | 
% 0.20/0.54       ~
% 0.20/0.54       (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.20/0.54          = (k8_tmap_1 @ sk_A @ sk_B))) | 
% 0.20/0.54       ~ ((m1_pre_topc @ sk_B @ sk_A))),
% 0.20/0.54      inference('split', [status(esa)], ['5'])).
% 0.20/0.54  thf('47', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('48', plain,
% 0.20/0.54      ((~ (m1_pre_topc @ sk_B @ sk_A)) <= (~ ((m1_pre_topc @ sk_B @ sk_A)))),
% 0.20/0.54      inference('split', [status(esa)], ['5'])).
% 0.20/0.54  thf('49', plain, (((m1_pre_topc @ sk_B @ sk_A))),
% 0.20/0.54      inference('sup-', [status(thm)], ['47', '48'])).
% 0.20/0.54  thf('50', plain,
% 0.20/0.54      (((v1_tsep_1 @ sk_B @ sk_A)) <= (((v1_tsep_1 @ sk_B @ sk_A)))),
% 0.20/0.54      inference('split', [status(esa)], ['13'])).
% 0.20/0.54  thf('51', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf(t1_tsep_1, axiom,
% 0.20/0.54    (![A:$i]:
% 0.20/0.54     ( ( l1_pre_topc @ A ) =>
% 0.20/0.54       ( ![B:$i]:
% 0.20/0.54         ( ( m1_pre_topc @ B @ A ) =>
% 0.20/0.54           ( m1_subset_1 @
% 0.20/0.54             ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.20/0.54  thf('52', plain,
% 0.20/0.54      (![X18 : $i, X19 : $i]:
% 0.20/0.54         (~ (m1_pre_topc @ X18 @ X19)
% 0.20/0.54          | (m1_subset_1 @ (u1_struct_0 @ X18) @ 
% 0.20/0.54             (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.20/0.54          | ~ (l1_pre_topc @ X19))),
% 0.20/0.54      inference('cnf', [status(esa)], [t1_tsep_1])).
% 0.20/0.54  thf('53', plain,
% 0.20/0.54      ((~ (l1_pre_topc @ sk_A)
% 0.20/0.54        | (m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.54           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.54      inference('sup-', [status(thm)], ['51', '52'])).
% 0.20/0.54  thf('54', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('55', plain,
% 0.20/0.54      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.54        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.54      inference('demod', [status(thm)], ['53', '54'])).
% 0.20/0.54  thf('56', plain,
% 0.20/0.54      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.20/0.54         (~ (m1_pre_topc @ X6 @ X7)
% 0.20/0.54          | ~ (v1_tsep_1 @ X6 @ X7)
% 0.20/0.54          | ((X8) != (u1_struct_0 @ X6))
% 0.20/0.54          | (v3_pre_topc @ X8 @ X7)
% 0.20/0.54          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (u1_struct_0 @ X7)))
% 0.20/0.54          | ~ (l1_pre_topc @ X7))),
% 0.20/0.54      inference('cnf', [status(esa)], [d1_tsep_1])).
% 0.20/0.54  thf('57', plain,
% 0.20/0.54      (![X6 : $i, X7 : $i]:
% 0.20/0.54         (~ (l1_pre_topc @ X7)
% 0.20/0.54          | ~ (m1_subset_1 @ (u1_struct_0 @ X6) @ 
% 0.20/0.54               (k1_zfmisc_1 @ (u1_struct_0 @ X7)))
% 0.20/0.54          | (v3_pre_topc @ (u1_struct_0 @ X6) @ X7)
% 0.20/0.54          | ~ (v1_tsep_1 @ X6 @ X7)
% 0.20/0.54          | ~ (m1_pre_topc @ X6 @ X7))),
% 0.20/0.54      inference('simplify', [status(thm)], ['56'])).
% 0.20/0.54  thf('58', plain,
% 0.20/0.54      ((~ (m1_pre_topc @ sk_B @ sk_A)
% 0.20/0.54        | ~ (v1_tsep_1 @ sk_B @ sk_A)
% 0.20/0.54        | (v3_pre_topc @ (u1_struct_0 @ sk_B) @ sk_A)
% 0.20/0.54        | ~ (l1_pre_topc @ sk_A))),
% 0.20/0.54      inference('sup-', [status(thm)], ['55', '57'])).
% 0.20/0.54  thf('59', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('60', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('61', plain,
% 0.20/0.54      ((~ (v1_tsep_1 @ sk_B @ sk_A)
% 0.20/0.54        | (v3_pre_topc @ (u1_struct_0 @ sk_B) @ sk_A))),
% 0.20/0.54      inference('demod', [status(thm)], ['58', '59', '60'])).
% 0.20/0.54  thf('62', plain,
% 0.20/0.54      (((v3_pre_topc @ (u1_struct_0 @ sk_B) @ sk_A))
% 0.20/0.54         <= (((v1_tsep_1 @ sk_B @ sk_A)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['50', '61'])).
% 0.20/0.54  thf('63', plain,
% 0.20/0.54      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.54        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.54      inference('demod', [status(thm)], ['53', '54'])).
% 0.20/0.54  thf(d5_pre_topc, axiom,
% 0.20/0.54    (![A:$i]:
% 0.20/0.54     ( ( l1_pre_topc @ A ) =>
% 0.20/0.54       ( ![B:$i]:
% 0.20/0.54         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.54           ( ( v3_pre_topc @ B @ A ) <=>
% 0.20/0.54             ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) ) ) ) ))).
% 0.20/0.54  thf('64', plain,
% 0.20/0.54      (![X1 : $i, X2 : $i]:
% 0.20/0.54         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X2)))
% 0.20/0.54          | ~ (v3_pre_topc @ X1 @ X2)
% 0.20/0.54          | (r2_hidden @ X1 @ (u1_pre_topc @ X2))
% 0.20/0.54          | ~ (l1_pre_topc @ X2))),
% 0.20/0.54      inference('cnf', [status(esa)], [d5_pre_topc])).
% 0.20/0.54  thf('65', plain,
% 0.20/0.54      ((~ (l1_pre_topc @ sk_A)
% 0.20/0.54        | (r2_hidden @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_A))
% 0.20/0.54        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_B) @ sk_A))),
% 0.20/0.54      inference('sup-', [status(thm)], ['63', '64'])).
% 0.20/0.54  thf('66', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('67', plain,
% 0.20/0.54      (((r2_hidden @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_A))
% 0.20/0.54        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_B) @ sk_A))),
% 0.20/0.54      inference('demod', [status(thm)], ['65', '66'])).
% 0.20/0.54  thf('68', plain,
% 0.20/0.54      (((r2_hidden @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_A)))
% 0.20/0.54         <= (((v1_tsep_1 @ sk_B @ sk_A)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['62', '67'])).
% 0.20/0.54  thf('69', plain,
% 0.20/0.54      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.54        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.54      inference('demod', [status(thm)], ['53', '54'])).
% 0.20/0.54  thf(t103_tmap_1, axiom,
% 0.20/0.54    (![A:$i]:
% 0.20/0.54     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.54       ( ![B:$i]:
% 0.20/0.54         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.54           ( ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) <=>
% 0.20/0.54             ( ( u1_pre_topc @ A ) = ( k5_tmap_1 @ A @ B ) ) ) ) ) ))).
% 0.20/0.54  thf('70', plain,
% 0.20/0.54      (![X13 : $i, X14 : $i]:
% 0.20/0.54         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.20/0.54          | ~ (r2_hidden @ X13 @ (u1_pre_topc @ X14))
% 0.20/0.54          | ((u1_pre_topc @ X14) = (k5_tmap_1 @ X14 @ X13))
% 0.20/0.54          | ~ (l1_pre_topc @ X14)
% 0.20/0.54          | ~ (v2_pre_topc @ X14)
% 0.20/0.54          | (v2_struct_0 @ X14))),
% 0.20/0.54      inference('cnf', [status(esa)], [t103_tmap_1])).
% 0.20/0.54  thf('71', plain,
% 0.20/0.54      (((v2_struct_0 @ sk_A)
% 0.20/0.54        | ~ (v2_pre_topc @ sk_A)
% 0.20/0.54        | ~ (l1_pre_topc @ sk_A)
% 0.20/0.54        | ((u1_pre_topc @ sk_A) = (k5_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 0.20/0.54        | ~ (r2_hidden @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_A)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['69', '70'])).
% 0.20/0.54  thf('72', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('73', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('74', plain,
% 0.20/0.54      (((v2_struct_0 @ sk_A)
% 0.20/0.54        | ((u1_pre_topc @ sk_A) = (k5_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 0.20/0.54        | ~ (r2_hidden @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_A)))),
% 0.20/0.54      inference('demod', [status(thm)], ['71', '72', '73'])).
% 0.20/0.54  thf('75', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('76', plain,
% 0.20/0.54      ((~ (r2_hidden @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_A))
% 0.20/0.54        | ((u1_pre_topc @ sk_A) = (k5_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B))))),
% 0.20/0.54      inference('clc', [status(thm)], ['74', '75'])).
% 0.20/0.54  thf('77', plain,
% 0.20/0.54      ((((u1_pre_topc @ sk_A) = (k5_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B))))
% 0.20/0.54         <= (((v1_tsep_1 @ sk_B @ sk_A)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['68', '76'])).
% 0.20/0.54  thf('78', plain,
% 0.20/0.54      (((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 0.20/0.54      inference('clc', [status(thm)], ['24', '25'])).
% 0.20/0.54  thf(abstractness_v1_pre_topc, axiom,
% 0.20/0.54    (![A:$i]:
% 0.20/0.54     ( ( l1_pre_topc @ A ) =>
% 0.20/0.54       ( ( v1_pre_topc @ A ) =>
% 0.20/0.54         ( ( A ) = ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ))).
% 0.20/0.54  thf('79', plain,
% 0.20/0.54      (![X0 : $i]:
% 0.20/0.54         (~ (v1_pre_topc @ X0)
% 0.20/0.54          | ((X0) = (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.20/0.54          | ~ (l1_pre_topc @ X0))),
% 0.20/0.54      inference('cnf', [status(esa)], [abstractness_v1_pre_topc])).
% 0.20/0.54  thf('80', plain,
% 0.20/0.54      ((((k8_tmap_1 @ sk_A @ sk_B)
% 0.20/0.54          = (g1_pre_topc @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.54             (u1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))))
% 0.20/0.54        | ~ (l1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.20/0.54        | ~ (v1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B)))),
% 0.20/0.54      inference('sup+', [status(thm)], ['78', '79'])).
% 0.20/0.54  thf('81', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf(dt_k8_tmap_1, axiom,
% 0.20/0.54    (![A:$i,B:$i]:
% 0.20/0.54     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.20/0.54         ( l1_pre_topc @ A ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.20/0.54       ( ( v1_pre_topc @ ( k8_tmap_1 @ A @ B ) ) & 
% 0.20/0.54         ( v2_pre_topc @ ( k8_tmap_1 @ A @ B ) ) & 
% 0.20/0.54         ( l1_pre_topc @ ( k8_tmap_1 @ A @ B ) ) ) ))).
% 0.20/0.54  thf('82', plain,
% 0.20/0.54      (![X9 : $i, X10 : $i]:
% 0.20/0.54         (~ (l1_pre_topc @ X9)
% 0.20/0.54          | ~ (v2_pre_topc @ X9)
% 0.20/0.54          | (v2_struct_0 @ X9)
% 0.20/0.54          | ~ (m1_pre_topc @ X10 @ X9)
% 0.20/0.54          | (l1_pre_topc @ (k8_tmap_1 @ X9 @ X10)))),
% 0.20/0.54      inference('cnf', [status(esa)], [dt_k8_tmap_1])).
% 0.20/0.54  thf('83', plain,
% 0.20/0.54      (((l1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.20/0.54        | (v2_struct_0 @ sk_A)
% 0.20/0.54        | ~ (v2_pre_topc @ sk_A)
% 0.20/0.54        | ~ (l1_pre_topc @ sk_A))),
% 0.20/0.54      inference('sup-', [status(thm)], ['81', '82'])).
% 0.20/0.54  thf('84', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('85', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('86', plain,
% 0.20/0.54      (((l1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B)) | (v2_struct_0 @ sk_A))),
% 0.20/0.54      inference('demod', [status(thm)], ['83', '84', '85'])).
% 0.20/0.54  thf('87', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('88', plain, ((l1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))),
% 0.20/0.54      inference('clc', [status(thm)], ['86', '87'])).
% 0.20/0.54  thf('89', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('90', plain,
% 0.20/0.54      (![X9 : $i, X10 : $i]:
% 0.20/0.54         (~ (l1_pre_topc @ X9)
% 0.20/0.54          | ~ (v2_pre_topc @ X9)
% 0.20/0.54          | (v2_struct_0 @ X9)
% 0.20/0.54          | ~ (m1_pre_topc @ X10 @ X9)
% 0.20/0.54          | (v1_pre_topc @ (k8_tmap_1 @ X9 @ X10)))),
% 0.20/0.54      inference('cnf', [status(esa)], [dt_k8_tmap_1])).
% 0.20/0.54  thf('91', plain,
% 0.20/0.54      (((v1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.20/0.54        | (v2_struct_0 @ sk_A)
% 0.20/0.54        | ~ (v2_pre_topc @ sk_A)
% 0.20/0.54        | ~ (l1_pre_topc @ sk_A))),
% 0.20/0.54      inference('sup-', [status(thm)], ['89', '90'])).
% 0.20/0.54  thf('92', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('93', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('94', plain,
% 0.20/0.54      (((v1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B)) | (v2_struct_0 @ sk_A))),
% 0.20/0.54      inference('demod', [status(thm)], ['91', '92', '93'])).
% 0.20/0.54  thf('95', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('96', plain, ((v1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))),
% 0.20/0.54      inference('clc', [status(thm)], ['94', '95'])).
% 0.20/0.54  thf('97', plain,
% 0.20/0.54      (((k8_tmap_1 @ sk_A @ sk_B)
% 0.20/0.54         = (g1_pre_topc @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.54            (u1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))))),
% 0.20/0.54      inference('demod', [status(thm)], ['80', '88', '96'])).
% 0.20/0.54  thf('98', plain,
% 0.20/0.54      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.54        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.54      inference('demod', [status(thm)], ['53', '54'])).
% 0.20/0.54  thf('99', plain,
% 0.20/0.54      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.20/0.54         ((v2_struct_0 @ X15)
% 0.20/0.54          | ~ (m1_pre_topc @ X15 @ X16)
% 0.20/0.54          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.20/0.54          | ((u1_pre_topc @ (k8_tmap_1 @ X16 @ X15)) = (k5_tmap_1 @ X16 @ X17))
% 0.20/0.54          | ((X17) != (u1_struct_0 @ X15))
% 0.20/0.54          | ~ (l1_pre_topc @ X16)
% 0.20/0.54          | ~ (v2_pre_topc @ X16)
% 0.20/0.54          | (v2_struct_0 @ X16))),
% 0.20/0.54      inference('cnf', [status(esa)], [t114_tmap_1])).
% 0.20/0.54  thf('100', plain,
% 0.20/0.54      (![X15 : $i, X16 : $i]:
% 0.20/0.54         ((v2_struct_0 @ X16)
% 0.20/0.54          | ~ (v2_pre_topc @ X16)
% 0.20/0.54          | ~ (l1_pre_topc @ X16)
% 0.20/0.54          | ((u1_pre_topc @ (k8_tmap_1 @ X16 @ X15))
% 0.20/0.54              = (k5_tmap_1 @ X16 @ (u1_struct_0 @ X15)))
% 0.20/0.54          | ~ (m1_subset_1 @ (u1_struct_0 @ X15) @ 
% 0.20/0.54               (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.20/0.54          | ~ (m1_pre_topc @ X15 @ X16)
% 0.20/0.54          | (v2_struct_0 @ X15))),
% 0.20/0.54      inference('simplify', [status(thm)], ['99'])).
% 0.20/0.54  thf('101', plain,
% 0.20/0.54      (((v2_struct_0 @ sk_B)
% 0.20/0.54        | ~ (m1_pre_topc @ sk_B @ sk_A)
% 0.20/0.54        | ((u1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.20/0.54            = (k5_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 0.20/0.54        | ~ (l1_pre_topc @ sk_A)
% 0.20/0.54        | ~ (v2_pre_topc @ sk_A)
% 0.20/0.54        | (v2_struct_0 @ sk_A))),
% 0.20/0.54      inference('sup-', [status(thm)], ['98', '100'])).
% 0.20/0.54  thf('102', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('103', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('104', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('105', plain,
% 0.20/0.54      (((v2_struct_0 @ sk_B)
% 0.20/0.54        | ((u1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.20/0.54            = (k5_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 0.20/0.54        | (v2_struct_0 @ sk_A))),
% 0.20/0.54      inference('demod', [status(thm)], ['101', '102', '103', '104'])).
% 0.20/0.54  thf('106', plain, (~ (v2_struct_0 @ sk_B)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('107', plain,
% 0.20/0.54      (((v2_struct_0 @ sk_A)
% 0.20/0.54        | ((u1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.20/0.54            = (k5_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B))))),
% 0.20/0.54      inference('clc', [status(thm)], ['105', '106'])).
% 0.20/0.54  thf('108', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('109', plain,
% 0.20/0.54      (((u1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.20/0.54         = (k5_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))),
% 0.20/0.54      inference('clc', [status(thm)], ['107', '108'])).
% 0.20/0.54  thf('110', plain,
% 0.20/0.54      (((k8_tmap_1 @ sk_A @ sk_B)
% 0.20/0.54         = (g1_pre_topc @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.54            (k5_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B))))),
% 0.20/0.54      inference('demod', [status(thm)], ['97', '109'])).
% 0.20/0.54  thf('111', plain,
% 0.20/0.54      ((((k8_tmap_1 @ sk_A @ sk_B)
% 0.20/0.54          = (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))
% 0.20/0.54         <= (((v1_tsep_1 @ sk_B @ sk_A)))),
% 0.20/0.54      inference('sup+', [status(thm)], ['77', '110'])).
% 0.20/0.54  thf('112', plain,
% 0.20/0.54      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.20/0.54          != (k8_tmap_1 @ sk_A @ sk_B)))
% 0.20/0.54         <= (~
% 0.20/0.54             (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.20/0.54                = (k8_tmap_1 @ sk_A @ sk_B))))),
% 0.20/0.54      inference('split', [status(esa)], ['5'])).
% 0.20/0.54  thf('113', plain,
% 0.20/0.54      ((((k8_tmap_1 @ sk_A @ sk_B) != (k8_tmap_1 @ sk_A @ sk_B)))
% 0.20/0.54         <= (~
% 0.20/0.54             (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.20/0.54                = (k8_tmap_1 @ sk_A @ sk_B))) & 
% 0.20/0.54             ((v1_tsep_1 @ sk_B @ sk_A)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['111', '112'])).
% 0.20/0.54  thf('114', plain,
% 0.20/0.54      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.20/0.54          = (k8_tmap_1 @ sk_A @ sk_B))) | 
% 0.20/0.54       ~ ((v1_tsep_1 @ sk_B @ sk_A))),
% 0.20/0.54      inference('simplify', [status(thm)], ['113'])).
% 0.20/0.54  thf('115', plain, (~ ((v1_tsep_1 @ sk_B @ sk_A))),
% 0.20/0.54      inference('sat_resolution*', [status(thm)], ['46', '49', '114'])).
% 0.20/0.54  thf('116', plain,
% 0.20/0.54      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.20/0.54          = (k8_tmap_1 @ sk_A @ sk_B))) | 
% 0.20/0.54       ((v1_tsep_1 @ sk_B @ sk_A))),
% 0.20/0.54      inference('split', [status(esa)], ['13'])).
% 0.20/0.54  thf('117', plain,
% 0.20/0.54      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.20/0.54          = (k8_tmap_1 @ sk_A @ sk_B)))),
% 0.20/0.54      inference('sat_resolution*', [status(thm)], ['46', '49', '114', '116'])).
% 0.20/0.54  thf('118', plain,
% 0.20/0.54      (~ (v3_pre_topc @ (u1_struct_0 @ sk_B) @ (k8_tmap_1 @ sk_A @ sk_B))),
% 0.20/0.54      inference('simpl_trail', [status(thm)], ['45', '115', '117'])).
% 0.20/0.54  thf('119', plain,
% 0.20/0.54      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.54        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.54      inference('demod', [status(thm)], ['53', '54'])).
% 0.20/0.54  thf(t102_tmap_1, axiom,
% 0.20/0.54    (![A:$i]:
% 0.20/0.54     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.54       ( ![B:$i]:
% 0.20/0.54         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.54           ( r2_hidden @ B @ ( k5_tmap_1 @ A @ B ) ) ) ) ))).
% 0.20/0.54  thf('120', plain,
% 0.20/0.54      (![X11 : $i, X12 : $i]:
% 0.20/0.54         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.20/0.54          | (r2_hidden @ X11 @ (k5_tmap_1 @ X12 @ X11))
% 0.20/0.54          | ~ (l1_pre_topc @ X12)
% 0.20/0.54          | ~ (v2_pre_topc @ X12)
% 0.20/0.54          | (v2_struct_0 @ X12))),
% 0.20/0.54      inference('cnf', [status(esa)], [t102_tmap_1])).
% 0.20/0.54  thf('121', plain,
% 0.20/0.54      (((v2_struct_0 @ sk_A)
% 0.20/0.54        | ~ (v2_pre_topc @ sk_A)
% 0.20/0.54        | ~ (l1_pre_topc @ sk_A)
% 0.20/0.54        | (r2_hidden @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.54           (k5_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B))))),
% 0.20/0.54      inference('sup-', [status(thm)], ['119', '120'])).
% 0.20/0.54  thf('122', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('123', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('124', plain,
% 0.20/0.54      (((v2_struct_0 @ sk_A)
% 0.20/0.54        | (r2_hidden @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.54           (k5_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B))))),
% 0.20/0.54      inference('demod', [status(thm)], ['121', '122', '123'])).
% 0.20/0.54  thf('125', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('126', plain,
% 0.20/0.54      ((r2_hidden @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.54        (k5_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))),
% 0.20/0.54      inference('clc', [status(thm)], ['124', '125'])).
% 0.20/0.54  thf('127', plain,
% 0.20/0.54      (((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 0.20/0.54      inference('clc', [status(thm)], ['24', '25'])).
% 0.20/0.54  thf('128', plain,
% 0.20/0.54      (![X1 : $i, X2 : $i]:
% 0.20/0.54         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X2)))
% 0.20/0.54          | ~ (r2_hidden @ X1 @ (u1_pre_topc @ X2))
% 0.20/0.54          | (v3_pre_topc @ X1 @ X2)
% 0.20/0.54          | ~ (l1_pre_topc @ X2))),
% 0.20/0.54      inference('cnf', [status(esa)], [d5_pre_topc])).
% 0.20/0.54  thf('129', plain,
% 0.20/0.54      (![X0 : $i]:
% 0.20/0.54         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.54          | ~ (l1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.20/0.54          | (v3_pre_topc @ X0 @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.20/0.54          | ~ (r2_hidden @ X0 @ (u1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))))),
% 0.20/0.54      inference('sup-', [status(thm)], ['127', '128'])).
% 0.20/0.54  thf('130', plain, ((l1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))),
% 0.20/0.54      inference('clc', [status(thm)], ['86', '87'])).
% 0.20/0.54  thf('131', plain,
% 0.20/0.54      (![X0 : $i]:
% 0.20/0.54         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.54          | (v3_pre_topc @ X0 @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.20/0.54          | ~ (r2_hidden @ X0 @ (u1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))))),
% 0.20/0.54      inference('demod', [status(thm)], ['129', '130'])).
% 0.20/0.54  thf('132', plain,
% 0.20/0.54      (((u1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.20/0.54         = (k5_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))),
% 0.20/0.54      inference('clc', [status(thm)], ['107', '108'])).
% 0.20/0.54  thf('133', plain,
% 0.20/0.54      (![X0 : $i]:
% 0.20/0.54         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.54          | (v3_pre_topc @ X0 @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.20/0.54          | ~ (r2_hidden @ X0 @ (k5_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B))))),
% 0.20/0.54      inference('demod', [status(thm)], ['131', '132'])).
% 0.20/0.54  thf('134', plain,
% 0.20/0.54      (((v3_pre_topc @ (u1_struct_0 @ sk_B) @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.20/0.54        | ~ (m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.54             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.54      inference('sup-', [status(thm)], ['126', '133'])).
% 0.20/0.54  thf('135', plain,
% 0.20/0.54      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.54        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.54      inference('demod', [status(thm)], ['53', '54'])).
% 0.20/0.54  thf('136', plain,
% 0.20/0.54      ((v3_pre_topc @ (u1_struct_0 @ sk_B) @ (k8_tmap_1 @ sk_A @ sk_B))),
% 0.20/0.54      inference('demod', [status(thm)], ['134', '135'])).
% 0.20/0.54  thf('137', plain, ($false), inference('demod', [status(thm)], ['118', '136'])).
% 0.20/0.54  
% 0.20/0.54  % SZS output end Refutation
% 0.20/0.54  
% 0.36/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
