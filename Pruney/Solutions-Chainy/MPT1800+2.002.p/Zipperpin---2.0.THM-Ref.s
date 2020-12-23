%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.YpbFmZvjac

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:10:55 EST 2020

% Result     : Theorem 0.42s
% Output     : Refutation 0.47s
% Verified   : 
% Statistics : Number of formulae       :  236 (1200 expanded)
%              Number of leaves         :   33 ( 338 expanded)
%              Depth                    :   24
%              Number of atoms          : 2252 (18500 expanded)
%              Number of equality atoms :  110 ( 691 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(g1_pre_topc_type,type,(
    g1_pre_topc: $i > $i > $i )).

thf(v1_tsep_1_type,type,(
    v1_tsep_1: $i > $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k8_tmap_1_type,type,(
    k8_tmap_1: $i > $i > $i )).

thf(k5_tmap_1_type,type,(
    k5_tmap_1: $i > $i > $i )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k6_tmap_1_type,type,(
    k6_tmap_1: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

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
    m1_pre_topc @ sk_B_1 @ sk_A ),
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
    | ( v1_tsep_1 @ sk_B_1 @ sk_A )
    | ( ( sk_C @ sk_B_1 @ sk_A )
      = ( u1_struct_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( v1_tsep_1 @ sk_B_1 @ sk_A )
    | ( ( sk_C @ sk_B_1 @ sk_A )
      = ( u1_struct_0 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('5',plain,
    ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
     != ( k8_tmap_1 @ sk_A @ sk_B_1 ) )
    | ~ ( m1_pre_topc @ sk_B_1 @ sk_A )
    | ~ ( v1_tsep_1 @ sk_B_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ~ ( v1_tsep_1 @ sk_B_1 @ sk_A )
   <= ~ ( v1_tsep_1 @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['5'])).

thf('7',plain,
    ( ( ( sk_C @ sk_B_1 @ sk_A )
      = ( u1_struct_0 @ sk_B_1 ) )
   <= ~ ( v1_tsep_1 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['4','6'])).

thf('8',plain,(
    m1_pre_topc @ sk_B_1 @ sk_A ),
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
    | ( v1_tsep_1 @ sk_B_1 @ sk_A )
    | ( m1_subset_1 @ ( sk_C @ sk_B_1 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ( v1_tsep_1 @ sk_B_1 @ sk_A )
    | ( m1_subset_1 @ ( sk_C @ sk_B_1 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf(d5_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v3_pre_topc @ B @ A )
          <=> ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) ) ) ) )).

thf('13',plain,(
    ! [X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X2 ) ) )
      | ~ ( r2_hidden @ X1 @ ( u1_pre_topc @ X2 ) )
      | ( v3_pre_topc @ X1 @ X2 )
      | ~ ( l1_pre_topc @ X2 ) ) ),
    inference(cnf,[status(esa)],[d5_pre_topc])).

thf('14',plain,
    ( ( v1_tsep_1 @ sk_B_1 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v3_pre_topc @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_A )
    | ~ ( r2_hidden @ ( sk_C @ sk_B_1 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( v1_tsep_1 @ sk_B_1 @ sk_A )
    | ( v3_pre_topc @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_A )
    | ~ ( r2_hidden @ ( sk_C @ sk_B_1 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,
    ( ( ~ ( r2_hidden @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_A ) )
      | ( v3_pre_topc @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_A )
      | ( v1_tsep_1 @ sk_B_1 @ sk_A ) )
   <= ~ ( v1_tsep_1 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['7','16'])).

thf('18',plain,
    ( ( ( sk_C @ sk_B_1 @ sk_A )
      = ( u1_struct_0 @ sk_B_1 ) )
   <= ~ ( v1_tsep_1 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['4','6'])).

thf('19',plain,
    ( ( ~ ( r2_hidden @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_A ) )
      | ( v3_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ sk_A )
      | ( v1_tsep_1 @ sk_B_1 @ sk_A ) )
   <= ~ ( v1_tsep_1 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,
    ( ( ( sk_C @ sk_B_1 @ sk_A )
      = ( u1_struct_0 @ sk_B_1 ) )
   <= ~ ( v1_tsep_1 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['4','6'])).

thf('21',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( m1_pre_topc @ X6 @ X7 )
      | ~ ( v3_pre_topc @ ( sk_C @ X6 @ X7 ) @ X7 )
      | ( v1_tsep_1 @ X6 @ X7 )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[d1_tsep_1])).

thf('22',plain,
    ( ( ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v1_tsep_1 @ sk_B_1 @ sk_A )
      | ~ ( m1_pre_topc @ sk_B_1 @ sk_A ) )
   <= ~ ( v1_tsep_1 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    m1_pre_topc @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ( ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ sk_A )
      | ( v1_tsep_1 @ sk_B_1 @ sk_A ) )
   <= ~ ( v1_tsep_1 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['22','23','24'])).

thf('26',plain,
    ( ~ ( v1_tsep_1 @ sk_B_1 @ sk_A )
   <= ~ ( v1_tsep_1 @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['5'])).

thf('27',plain,
    ( ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ sk_A )
   <= ~ ( v1_tsep_1 @ sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['25','26'])).

thf('28',plain,
    ( ( ( v1_tsep_1 @ sk_B_1 @ sk_A )
      | ~ ( r2_hidden @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_A ) ) )
   <= ~ ( v1_tsep_1 @ sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['19','27'])).

thf('29',plain,
    ( ~ ( v1_tsep_1 @ sk_B_1 @ sk_A )
   <= ~ ( v1_tsep_1 @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['5'])).

thf('30',plain,
    ( ~ ( r2_hidden @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_A ) )
   <= ~ ( v1_tsep_1 @ sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['28','29'])).

thf('31',plain,
    ( ~ ( v1_tsep_1 @ sk_B_1 @ sk_A )
    | ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
     != ( k8_tmap_1 @ sk_A @ sk_B_1 ) )
    | ~ ( m1_pre_topc @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['5'])).

thf('32',plain,(
    m1_pre_topc @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ~ ( m1_pre_topc @ sk_B_1 @ sk_A )
   <= ~ ( m1_pre_topc @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['5'])).

thf('34',plain,(
    m1_pre_topc @ sk_B_1 @ sk_A ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    m1_pre_topc @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t1_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( m1_subset_1 @ ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('36',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( m1_pre_topc @ X20 @ X21 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X20 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( l1_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('37',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( m1_subset_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['37','38'])).

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

thf('40',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( v2_struct_0 @ X17 )
      | ~ ( m1_pre_topc @ X17 @ X18 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ( ( u1_pre_topc @ ( k8_tmap_1 @ X18 @ X17 ) )
        = ( k5_tmap_1 @ X18 @ X19 ) )
      | ( X19
       != ( u1_struct_0 @ X17 ) )
      | ~ ( l1_pre_topc @ X18 )
      | ~ ( v2_pre_topc @ X18 )
      | ( v2_struct_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t114_tmap_1])).

thf('41',plain,(
    ! [X17: $i,X18: $i] :
      ( ( v2_struct_0 @ X18 )
      | ~ ( v2_pre_topc @ X18 )
      | ~ ( l1_pre_topc @ X18 )
      | ( ( u1_pre_topc @ ( k8_tmap_1 @ X18 @ X17 ) )
        = ( k5_tmap_1 @ X18 @ ( u1_struct_0 @ X17 ) ) )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X17 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( m1_pre_topc @ X17 @ X18 )
      | ( v2_struct_0 @ X17 ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,
    ( ( v2_struct_0 @ sk_B_1 )
    | ~ ( m1_pre_topc @ sk_B_1 @ sk_A )
    | ( ( u1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) )
      = ( k5_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B_1 ) ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['39','41'])).

thf('43',plain,(
    m1_pre_topc @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( ( v2_struct_0 @ sk_B_1 )
    | ( ( u1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) )
      = ( k5_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B_1 ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['42','43','44','45'])).

thf('47',plain,(
    ~ ( v2_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( u1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) )
      = ( k5_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference(clc,[status(thm)],['46','47'])).

thf('49',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,
    ( ( u1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) )
    = ( k5_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['48','49'])).

thf('51',plain,
    ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k8_tmap_1 @ sk_A @ sk_B_1 ) )
    | ( v1_tsep_1 @ sk_B_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,
    ( ( v1_tsep_1 @ sk_B_1 @ sk_A )
   <= ( v1_tsep_1 @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['51'])).

thf('53',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('54',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( m1_pre_topc @ X6 @ X7 )
      | ~ ( v1_tsep_1 @ X6 @ X7 )
      | ( X8
       != ( u1_struct_0 @ X6 ) )
      | ( v3_pre_topc @ X8 @ X7 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[d1_tsep_1])).

thf('55',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( l1_pre_topc @ X7 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X6 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) )
      | ( v3_pre_topc @ ( u1_struct_0 @ X6 ) @ X7 )
      | ~ ( v1_tsep_1 @ X6 @ X7 )
      | ~ ( m1_pre_topc @ X6 @ X7 ) ) ),
    inference(simplify,[status(thm)],['54'])).

thf('56',plain,
    ( ~ ( m1_pre_topc @ sk_B_1 @ sk_A )
    | ~ ( v1_tsep_1 @ sk_B_1 @ sk_A )
    | ( v3_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['53','55'])).

thf('57',plain,(
    m1_pre_topc @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,
    ( ~ ( v1_tsep_1 @ sk_B_1 @ sk_A )
    | ( v3_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ sk_A ) ),
    inference(demod,[status(thm)],['56','57','58'])).

thf('60',plain,
    ( ( v3_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ sk_A )
   <= ( v1_tsep_1 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['52','59'])).

thf('61',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('62',plain,(
    ! [X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X2 ) ) )
      | ~ ( v3_pre_topc @ X1 @ X2 )
      | ( r2_hidden @ X1 @ ( u1_pre_topc @ X2 ) )
      | ~ ( l1_pre_topc @ X2 ) ) ),
    inference(cnf,[status(esa)],[d5_pre_topc])).

thf('63',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r2_hidden @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_A ) )
    | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,
    ( ( r2_hidden @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_A ) )
    | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ sk_A ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('66',plain,
    ( ( r2_hidden @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_A ) )
   <= ( v1_tsep_1 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['60','65'])).

thf('67',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['37','38'])).

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

thf('68',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( r2_hidden @ X13 @ ( u1_pre_topc @ X14 ) )
      | ( ( u1_pre_topc @ X14 )
        = ( k5_tmap_1 @ X14 @ X13 ) )
      | ~ ( l1_pre_topc @ X14 )
      | ~ ( v2_pre_topc @ X14 )
      | ( v2_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t103_tmap_1])).

thf('69',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( ( u1_pre_topc @ sk_A )
      = ( k5_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B_1 ) ) )
    | ~ ( r2_hidden @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( u1_pre_topc @ sk_A )
      = ( k5_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B_1 ) ) )
    | ~ ( r2_hidden @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_A ) ) ),
    inference(demod,[status(thm)],['69','70','71'])).

thf('73',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,
    ( ~ ( r2_hidden @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_A ) )
    | ( ( u1_pre_topc @ sk_A )
      = ( k5_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference(clc,[status(thm)],['72','73'])).

thf('75',plain,
    ( ( ( u1_pre_topc @ sk_A )
      = ( k5_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B_1 ) ) )
   <= ( v1_tsep_1 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['66','74'])).

thf('76',plain,
    ( ( ( u1_pre_topc @ sk_A )
      = ( u1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) ) )
   <= ( v1_tsep_1 @ sk_B_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['50','75'])).

thf(abstractness_v1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( ( v1_pre_topc @ A )
       => ( A
          = ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ) )).

thf('77',plain,(
    ! [X0: $i] :
      ( ~ ( v1_pre_topc @ X0 )
      | ( X0
        = ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(cnf,[status(esa)],[abstractness_v1_pre_topc])).

thf('78',plain,
    ( ( ( ( k8_tmap_1 @ sk_A @ sk_B_1 )
        = ( g1_pre_topc @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) ) @ ( u1_pre_topc @ sk_A ) ) )
      | ~ ( l1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) )
      | ~ ( v1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) ) )
   <= ( v1_tsep_1 @ sk_B_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['76','77'])).

thf('79',plain,(
    m1_pre_topc @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    ! [X17: $i,X18: $i] :
      ( ( v2_struct_0 @ X17 )
      | ~ ( m1_pre_topc @ X17 @ X18 )
      | ( ( u1_struct_0 @ ( k8_tmap_1 @ X18 @ X17 ) )
        = ( u1_struct_0 @ X18 ) )
      | ~ ( l1_pre_topc @ X18 )
      | ~ ( v2_pre_topc @ X18 )
      | ( v2_struct_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t114_tmap_1])).

thf('81',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) )
      = ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) )
      = ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['81','82','83'])).

thf('85',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,
    ( ( v2_struct_0 @ sk_B_1 )
    | ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['84','85'])).

thf('87',plain,(
    ~ ( v2_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,
    ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['86','87'])).

thf('89',plain,
    ( ( ( u1_pre_topc @ sk_A )
      = ( k5_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B_1 ) ) )
   <= ( v1_tsep_1 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['66','74'])).

thf('90',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf(d9_tmap_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k6_tmap_1 @ A @ B )
            = ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( k5_tmap_1 @ A @ B ) ) ) ) ) )).

thf('91',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ( ( k6_tmap_1 @ X10 @ X9 )
        = ( g1_pre_topc @ ( u1_struct_0 @ X10 ) @ ( k5_tmap_1 @ X10 @ X9 ) ) )
      | ~ ( l1_pre_topc @ X10 )
      | ~ ( v2_pre_topc @ X10 )
      | ( v2_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d9_tmap_1])).

thf('92',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B_1 ) )
      = ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( k5_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B_1 ) )
      = ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( k5_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B_1 ) ) ) ) ),
    inference(demod,[status(thm)],['92','93','94'])).

thf('96',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,
    ( ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B_1 ) )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( k5_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference(clc,[status(thm)],['95','96'])).

thf('98',plain,
    ( ( ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B_1 ) )
      = ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
   <= ( v1_tsep_1 @ sk_B_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['89','97'])).

thf(rc1_connsp_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ? [B: $i] :
          ( ( v1_xboole_0 @ B )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('99',plain,(
    ! [X5: $i] :
      ( ( v1_xboole_0 @ ( sk_B @ X5 ) )
      | ~ ( l1_pre_topc @ X5 ) ) ),
    inference(cnf,[status(esa)],[rc1_connsp_1])).

thf('100',plain,(
    ! [X5: $i] :
      ( ( m1_subset_1 @ ( sk_B @ X5 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) )
      | ~ ( l1_pre_topc @ X5 ) ) ),
    inference(cnf,[status(esa)],[rc1_connsp_1])).

thf(cc1_tops_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v1_xboole_0 @ B )
           => ( v3_pre_topc @ B @ A ) ) ) ) )).

thf('101',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X4 ) ) )
      | ( v3_pre_topc @ X3 @ X4 )
      | ~ ( v1_xboole_0 @ X3 )
      | ~ ( l1_pre_topc @ X4 )
      | ~ ( v2_pre_topc @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc1_tops_1])).

thf('102',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_xboole_0 @ ( sk_B @ X0 ) )
      | ( v3_pre_topc @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,(
    ! [X0: $i] :
      ( ( v3_pre_topc @ ( sk_B @ X0 ) @ X0 )
      | ~ ( v1_xboole_0 @ ( sk_B @ X0 ) )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['102'])).

thf('104',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v3_pre_topc @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['99','103'])).

thf('105',plain,(
    ! [X0: $i] :
      ( ( v3_pre_topc @ ( sk_B @ X0 ) @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['104'])).

thf('106',plain,(
    ! [X5: $i] :
      ( ( m1_subset_1 @ ( sk_B @ X5 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) )
      | ~ ( l1_pre_topc @ X5 ) ) ),
    inference(cnf,[status(esa)],[rc1_connsp_1])).

thf('107',plain,(
    ! [X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X2 ) ) )
      | ~ ( v3_pre_topc @ X1 @ X2 )
      | ( r2_hidden @ X1 @ ( u1_pre_topc @ X2 ) )
      | ~ ( l1_pre_topc @ X2 ) ) ),
    inference(cnf,[status(esa)],[d5_pre_topc])).

thf('108',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ ( u1_pre_topc @ X0 ) )
      | ~ ( v3_pre_topc @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf('109',plain,(
    ! [X0: $i] :
      ( ~ ( v3_pre_topc @ ( sk_B @ X0 ) @ X0 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ ( u1_pre_topc @ X0 ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['108'])).

thf('110',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['105','109'])).

thf('111',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_B @ X0 ) @ ( u1_pre_topc @ X0 ) )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['110'])).

thf('112',plain,(
    ! [X5: $i] :
      ( ( m1_subset_1 @ ( sk_B @ X5 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) )
      | ~ ( l1_pre_topc @ X5 ) ) ),
    inference(cnf,[status(esa)],[rc1_connsp_1])).

thf('113',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( r2_hidden @ X13 @ ( u1_pre_topc @ X14 ) )
      | ( ( u1_pre_topc @ X14 )
        = ( k5_tmap_1 @ X14 @ X13 ) )
      | ~ ( l1_pre_topc @ X14 )
      | ~ ( v2_pre_topc @ X14 )
      | ( v2_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t103_tmap_1])).

thf('114',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( u1_pre_topc @ X0 )
        = ( k5_tmap_1 @ X0 @ ( sk_B @ X0 ) ) )
      | ~ ( r2_hidden @ ( sk_B @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['112','113'])).

thf('115',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( sk_B @ X0 ) @ ( u1_pre_topc @ X0 ) )
      | ( ( u1_pre_topc @ X0 )
        = ( k5_tmap_1 @ X0 @ ( sk_B @ X0 ) ) )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['114'])).

thf('116',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( ( u1_pre_topc @ X0 )
        = ( k5_tmap_1 @ X0 @ ( sk_B @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['111','115'])).

thf('117',plain,(
    ! [X0: $i] :
      ( ( ( u1_pre_topc @ X0 )
        = ( k5_tmap_1 @ X0 @ ( sk_B @ X0 ) ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['116'])).

thf('118',plain,(
    ! [X5: $i] :
      ( ( m1_subset_1 @ ( sk_B @ X5 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) )
      | ~ ( l1_pre_topc @ X5 ) ) ),
    inference(cnf,[status(esa)],[rc1_connsp_1])).

thf('119',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ( ( k6_tmap_1 @ X10 @ X9 )
        = ( g1_pre_topc @ ( u1_struct_0 @ X10 ) @ ( k5_tmap_1 @ X10 @ X9 ) ) )
      | ~ ( l1_pre_topc @ X10 )
      | ~ ( v2_pre_topc @ X10 )
      | ( v2_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d9_tmap_1])).

thf('120',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( k6_tmap_1 @ X0 @ ( sk_B @ X0 ) )
        = ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( k5_tmap_1 @ X0 @ ( sk_B @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['118','119'])).

thf('121',plain,(
    ! [X0: $i] :
      ( ( ( k6_tmap_1 @ X0 @ ( sk_B @ X0 ) )
        = ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( k5_tmap_1 @ X0 @ ( sk_B @ X0 ) ) ) )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['120'])).

thf('122',plain,(
    ! [X0: $i] :
      ( ( ( k6_tmap_1 @ X0 @ ( sk_B @ X0 ) )
        = ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference('sup+',[status(thm)],['117','121'])).

thf('123',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( k6_tmap_1 @ X0 @ ( sk_B @ X0 ) )
        = ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['122'])).

thf('124',plain,
    ( ( ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B_1 ) )
      = ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
   <= ( v1_tsep_1 @ sk_B_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['89','97'])).

thf('125',plain,
    ( ( ( ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B_1 ) )
        = ( k6_tmap_1 @ sk_A @ ( sk_B @ sk_A ) ) )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ( v1_tsep_1 @ sk_B_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['123','124'])).

thf('126',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('128',plain,
    ( ( ( ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B_1 ) )
        = ( k6_tmap_1 @ sk_A @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( v1_tsep_1 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['125','126','127'])).

thf('129',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('130',plain,
    ( ( ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B_1 ) )
      = ( k6_tmap_1 @ sk_A @ ( sk_B @ sk_A ) ) )
   <= ( v1_tsep_1 @ sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['128','129'])).

thf('131',plain,
    ( ( ( k6_tmap_1 @ sk_A @ ( sk_B @ sk_A ) )
      = ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
   <= ( v1_tsep_1 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['98','130'])).

thf('132',plain,(
    m1_pre_topc @ sk_B_1 @ sk_A ),
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

thf('133',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( l1_pre_topc @ X11 )
      | ~ ( v2_pre_topc @ X11 )
      | ( v2_struct_0 @ X11 )
      | ~ ( m1_pre_topc @ X12 @ X11 )
      | ( l1_pre_topc @ ( k8_tmap_1 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k8_tmap_1])).

thf('134',plain,
    ( ( l1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['132','133'])).

thf('135',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('136',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('137',plain,
    ( ( l1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['134','135','136'])).

thf('138',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('139',plain,(
    l1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) ),
    inference(clc,[status(thm)],['137','138'])).

thf('140',plain,(
    m1_pre_topc @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('141',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( l1_pre_topc @ X11 )
      | ~ ( v2_pre_topc @ X11 )
      | ( v2_struct_0 @ X11 )
      | ~ ( m1_pre_topc @ X12 @ X11 )
      | ( v1_pre_topc @ ( k8_tmap_1 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k8_tmap_1])).

thf('142',plain,
    ( ( v1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['140','141'])).

thf('143',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('144',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('145',plain,
    ( ( v1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['142','143','144'])).

thf('146',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('147',plain,(
    v1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) ),
    inference(clc,[status(thm)],['145','146'])).

thf('148',plain,
    ( ( ( k8_tmap_1 @ sk_A @ sk_B_1 )
      = ( k6_tmap_1 @ sk_A @ ( sk_B @ sk_A ) ) )
   <= ( v1_tsep_1 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['78','88','131','139','147'])).

thf('149',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( k6_tmap_1 @ X0 @ ( sk_B @ X0 ) )
        = ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['122'])).

thf('150',plain,
    ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
     != ( k8_tmap_1 @ sk_A @ sk_B_1 ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
     != ( k8_tmap_1 @ sk_A @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['5'])).

thf('151',plain,
    ( ( ( ( k6_tmap_1 @ sk_A @ ( sk_B @ sk_A ) )
       != ( k8_tmap_1 @ sk_A @ sk_B_1 ) )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
     != ( k8_tmap_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['149','150'])).

thf('152',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('153',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('154',plain,
    ( ( ( ( k6_tmap_1 @ sk_A @ ( sk_B @ sk_A ) )
       != ( k8_tmap_1 @ sk_A @ sk_B_1 ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
     != ( k8_tmap_1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['151','152','153'])).

thf('155',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('156',plain,
    ( ( ( k6_tmap_1 @ sk_A @ ( sk_B @ sk_A ) )
     != ( k8_tmap_1 @ sk_A @ sk_B_1 ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
     != ( k8_tmap_1 @ sk_A @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['154','155'])).

thf('157',plain,
    ( ( ( k8_tmap_1 @ sk_A @ sk_B_1 )
     != ( k8_tmap_1 @ sk_A @ sk_B_1 ) )
   <= ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
       != ( k8_tmap_1 @ sk_A @ sk_B_1 ) )
      & ( v1_tsep_1 @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['148','156'])).

thf('158',plain,
    ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k8_tmap_1 @ sk_A @ sk_B_1 ) )
    | ~ ( v1_tsep_1 @ sk_B_1 @ sk_A ) ),
    inference(simplify,[status(thm)],['157'])).

thf('159',plain,(
    ~ ( v1_tsep_1 @ sk_B_1 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['31','34','158'])).

thf('160',plain,(
    ~ ( r2_hidden @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_A ) ) ),
    inference(simpl_trail,[status(thm)],['30','159'])).

thf('161',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('162',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ( ( u1_pre_topc @ X14 )
       != ( k5_tmap_1 @ X14 @ X13 ) )
      | ( r2_hidden @ X13 @ ( u1_pre_topc @ X14 ) )
      | ~ ( l1_pre_topc @ X14 )
      | ~ ( v2_pre_topc @ X14 )
      | ( v2_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t103_tmap_1])).

thf('163',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( r2_hidden @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_A ) )
    | ( ( u1_pre_topc @ sk_A )
     != ( k5_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['161','162'])).

thf('164',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('165',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('166',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_A ) )
    | ( ( u1_pre_topc @ sk_A )
     != ( k5_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['163','164','165'])).

thf('167',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('168',plain,
    ( ( ( u1_pre_topc @ sk_A )
     != ( k5_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B_1 ) ) )
    | ( r2_hidden @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_A ) ) ),
    inference(clc,[status(thm)],['166','167'])).

thf('169',plain,
    ( ( u1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) )
    = ( k5_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['48','49'])).

thf('170',plain,
    ( ( ( u1_pre_topc @ sk_A )
     != ( u1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) ) )
    | ( r2_hidden @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_A ) ) ),
    inference(demod,[status(thm)],['168','169'])).

thf('171',plain,(
    ! [X0: $i] :
      ( ( ( u1_pre_topc @ X0 )
        = ( k5_tmap_1 @ X0 @ ( sk_B @ X0 ) ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['116'])).

thf('172',plain,
    ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k8_tmap_1 @ sk_A @ sk_B_1 ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k8_tmap_1 @ sk_A @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['51'])).

thf('173',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( k6_tmap_1 @ X0 @ ( sk_B @ X0 ) )
        = ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['122'])).

thf('174',plain,
    ( ( ( ( k6_tmap_1 @ sk_A @ ( sk_B @ sk_A ) )
        = ( k8_tmap_1 @ sk_A @ sk_B_1 ) )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k8_tmap_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['172','173'])).

thf('175',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('176',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('177',plain,
    ( ( ( ( k6_tmap_1 @ sk_A @ ( sk_B @ sk_A ) )
        = ( k8_tmap_1 @ sk_A @ sk_B_1 ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k8_tmap_1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['174','175','176'])).

thf('178',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('179',plain,
    ( ( ( k6_tmap_1 @ sk_A @ ( sk_B @ sk_A ) )
      = ( k8_tmap_1 @ sk_A @ sk_B_1 ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k8_tmap_1 @ sk_A @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['177','178'])).

thf('180',plain,(
    ! [X5: $i] :
      ( ( m1_subset_1 @ ( sk_B @ X5 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) )
      | ~ ( l1_pre_topc @ X5 ) ) ),
    inference(cnf,[status(esa)],[rc1_connsp_1])).

thf(t104_tmap_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( ( u1_struct_0 @ ( k6_tmap_1 @ A @ B ) )
              = ( u1_struct_0 @ A ) )
            & ( ( u1_pre_topc @ ( k6_tmap_1 @ A @ B ) )
              = ( k5_tmap_1 @ A @ B ) ) ) ) ) )).

thf('181',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ( ( u1_pre_topc @ ( k6_tmap_1 @ X16 @ X15 ) )
        = ( k5_tmap_1 @ X16 @ X15 ) )
      | ~ ( l1_pre_topc @ X16 )
      | ~ ( v2_pre_topc @ X16 )
      | ( v2_struct_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t104_tmap_1])).

thf('182',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( u1_pre_topc @ ( k6_tmap_1 @ X0 @ ( sk_B @ X0 ) ) )
        = ( k5_tmap_1 @ X0 @ ( sk_B @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['180','181'])).

thf('183',plain,(
    ! [X0: $i] :
      ( ( ( u1_pre_topc @ ( k6_tmap_1 @ X0 @ ( sk_B @ X0 ) ) )
        = ( k5_tmap_1 @ X0 @ ( sk_B @ X0 ) ) )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['182'])).

thf('184',plain,
    ( ( ( ( u1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) )
        = ( k5_tmap_1 @ sk_A @ ( sk_B @ sk_A ) ) )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k8_tmap_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['179','183'])).

thf('185',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('186',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('187',plain,
    ( ( ( ( u1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) )
        = ( k5_tmap_1 @ sk_A @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k8_tmap_1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['184','185','186'])).

thf('188',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('189',plain,
    ( ( ( u1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) )
      = ( k5_tmap_1 @ sk_A @ ( sk_B @ sk_A ) ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k8_tmap_1 @ sk_A @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['187','188'])).

thf('190',plain,
    ( ( ( ( u1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) )
        = ( u1_pre_topc @ sk_A ) )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k8_tmap_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['171','189'])).

thf('191',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('192',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('193',plain,
    ( ( ( ( u1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) )
        = ( u1_pre_topc @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k8_tmap_1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['190','191','192'])).

thf('194',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('195',plain,
    ( ( ( u1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) )
      = ( u1_pre_topc @ sk_A ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k8_tmap_1 @ sk_A @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['193','194'])).

thf('196',plain,
    ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k8_tmap_1 @ sk_A @ sk_B_1 ) )
    | ( v1_tsep_1 @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['51'])).

thf('197',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
    = ( k8_tmap_1 @ sk_A @ sk_B_1 ) ),
    inference('sat_resolution*',[status(thm)],['31','34','158','196'])).

thf('198',plain,
    ( ( u1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) )
    = ( u1_pre_topc @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['195','197'])).

thf('199',plain,
    ( ( ( u1_pre_topc @ sk_A )
     != ( u1_pre_topc @ sk_A ) )
    | ( r2_hidden @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_A ) ) ),
    inference(demod,[status(thm)],['170','198'])).

thf('200',plain,(
    r2_hidden @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_A ) ),
    inference(simplify,[status(thm)],['199'])).

thf('201',plain,(
    $false ),
    inference(demod,[status(thm)],['160','200'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.YpbFmZvjac
% 0.14/0.34  % Computer   : n007.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 17:56:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.42/0.63  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.42/0.63  % Solved by: fo/fo7.sh
% 0.42/0.63  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.42/0.63  % done 252 iterations in 0.166s
% 0.42/0.63  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.42/0.63  % SZS output start Refutation
% 0.42/0.63  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.42/0.63  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.42/0.63  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 0.42/0.63  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.42/0.63  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.42/0.63  thf(g1_pre_topc_type, type, g1_pre_topc: $i > $i > $i).
% 0.42/0.63  thf(v1_tsep_1_type, type, v1_tsep_1: $i > $i > $o).
% 0.42/0.63  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.42/0.63  thf(sk_A_type, type, sk_A: $i).
% 0.42/0.63  thf(k8_tmap_1_type, type, k8_tmap_1: $i > $i > $i).
% 0.42/0.63  thf(k5_tmap_1_type, type, k5_tmap_1: $i > $i > $i).
% 0.42/0.63  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 0.42/0.63  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.42/0.63  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.42/0.63  thf(sk_B_type, type, sk_B: $i > $i).
% 0.42/0.63  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.42/0.63  thf(k6_tmap_1_type, type, k6_tmap_1: $i > $i > $i).
% 0.42/0.63  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.42/0.63  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.42/0.63  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.42/0.63  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.42/0.63  thf(t116_tmap_1, conjecture,
% 0.42/0.63    (![A:$i]:
% 0.42/0.63     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.42/0.63       ( ![B:$i]:
% 0.42/0.63         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.42/0.63           ( ( ( v1_tsep_1 @ B @ A ) & ( m1_pre_topc @ B @ A ) ) <=>
% 0.42/0.63             ( ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) =
% 0.42/0.63               ( k8_tmap_1 @ A @ B ) ) ) ) ) ))).
% 0.42/0.63  thf(zf_stmt_0, negated_conjecture,
% 0.42/0.63    (~( ![A:$i]:
% 0.42/0.63        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.42/0.63            ( l1_pre_topc @ A ) ) =>
% 0.42/0.63          ( ![B:$i]:
% 0.42/0.63            ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.42/0.63              ( ( ( v1_tsep_1 @ B @ A ) & ( m1_pre_topc @ B @ A ) ) <=>
% 0.42/0.63                ( ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) =
% 0.42/0.63                  ( k8_tmap_1 @ A @ B ) ) ) ) ) ) )),
% 0.42/0.63    inference('cnf.neg', [status(esa)], [t116_tmap_1])).
% 0.42/0.63  thf('0', plain, ((m1_pre_topc @ sk_B_1 @ sk_A)),
% 0.42/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.63  thf(d1_tsep_1, axiom,
% 0.42/0.63    (![A:$i]:
% 0.42/0.63     ( ( l1_pre_topc @ A ) =>
% 0.42/0.63       ( ![B:$i]:
% 0.42/0.63         ( ( m1_pre_topc @ B @ A ) =>
% 0.42/0.63           ( ( v1_tsep_1 @ B @ A ) <=>
% 0.42/0.63             ( ![C:$i]:
% 0.42/0.63               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.42/0.63                 ( ( ( C ) = ( u1_struct_0 @ B ) ) => ( v3_pre_topc @ C @ A ) ) ) ) ) ) ) ))).
% 0.42/0.63  thf('1', plain,
% 0.42/0.63      (![X6 : $i, X7 : $i]:
% 0.42/0.63         (~ (m1_pre_topc @ X6 @ X7)
% 0.42/0.63          | ((sk_C @ X6 @ X7) = (u1_struct_0 @ X6))
% 0.42/0.63          | (v1_tsep_1 @ X6 @ X7)
% 0.42/0.63          | ~ (l1_pre_topc @ X7))),
% 0.42/0.63      inference('cnf', [status(esa)], [d1_tsep_1])).
% 0.42/0.63  thf('2', plain,
% 0.42/0.63      ((~ (l1_pre_topc @ sk_A)
% 0.42/0.63        | (v1_tsep_1 @ sk_B_1 @ sk_A)
% 0.42/0.63        | ((sk_C @ sk_B_1 @ sk_A) = (u1_struct_0 @ sk_B_1)))),
% 0.42/0.63      inference('sup-', [status(thm)], ['0', '1'])).
% 0.42/0.63  thf('3', plain, ((l1_pre_topc @ sk_A)),
% 0.42/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.63  thf('4', plain,
% 0.42/0.63      (((v1_tsep_1 @ sk_B_1 @ sk_A)
% 0.42/0.63        | ((sk_C @ sk_B_1 @ sk_A) = (u1_struct_0 @ sk_B_1)))),
% 0.42/0.63      inference('demod', [status(thm)], ['2', '3'])).
% 0.42/0.63  thf('5', plain,
% 0.42/0.63      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.42/0.63          != (k8_tmap_1 @ sk_A @ sk_B_1))
% 0.42/0.63        | ~ (m1_pre_topc @ sk_B_1 @ sk_A)
% 0.42/0.63        | ~ (v1_tsep_1 @ sk_B_1 @ sk_A))),
% 0.42/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.63  thf('6', plain,
% 0.42/0.63      ((~ (v1_tsep_1 @ sk_B_1 @ sk_A)) <= (~ ((v1_tsep_1 @ sk_B_1 @ sk_A)))),
% 0.42/0.63      inference('split', [status(esa)], ['5'])).
% 0.42/0.63  thf('7', plain,
% 0.42/0.63      ((((sk_C @ sk_B_1 @ sk_A) = (u1_struct_0 @ sk_B_1)))
% 0.42/0.63         <= (~ ((v1_tsep_1 @ sk_B_1 @ sk_A)))),
% 0.42/0.63      inference('sup-', [status(thm)], ['4', '6'])).
% 0.42/0.63  thf('8', plain, ((m1_pre_topc @ sk_B_1 @ sk_A)),
% 0.42/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.63  thf('9', plain,
% 0.42/0.63      (![X6 : $i, X7 : $i]:
% 0.42/0.63         (~ (m1_pre_topc @ X6 @ X7)
% 0.42/0.63          | (m1_subset_1 @ (sk_C @ X6 @ X7) @ 
% 0.42/0.63             (k1_zfmisc_1 @ (u1_struct_0 @ X7)))
% 0.42/0.63          | (v1_tsep_1 @ X6 @ X7)
% 0.42/0.63          | ~ (l1_pre_topc @ X7))),
% 0.42/0.63      inference('cnf', [status(esa)], [d1_tsep_1])).
% 0.42/0.63  thf('10', plain,
% 0.42/0.63      ((~ (l1_pre_topc @ sk_A)
% 0.42/0.63        | (v1_tsep_1 @ sk_B_1 @ sk_A)
% 0.42/0.63        | (m1_subset_1 @ (sk_C @ sk_B_1 @ sk_A) @ 
% 0.42/0.63           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.42/0.63      inference('sup-', [status(thm)], ['8', '9'])).
% 0.42/0.63  thf('11', plain, ((l1_pre_topc @ sk_A)),
% 0.42/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.63  thf('12', plain,
% 0.42/0.63      (((v1_tsep_1 @ sk_B_1 @ sk_A)
% 0.42/0.63        | (m1_subset_1 @ (sk_C @ sk_B_1 @ sk_A) @ 
% 0.42/0.63           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.42/0.63      inference('demod', [status(thm)], ['10', '11'])).
% 0.42/0.63  thf(d5_pre_topc, axiom,
% 0.42/0.63    (![A:$i]:
% 0.42/0.63     ( ( l1_pre_topc @ A ) =>
% 0.42/0.63       ( ![B:$i]:
% 0.42/0.63         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.42/0.63           ( ( v3_pre_topc @ B @ A ) <=>
% 0.42/0.63             ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) ) ) ) ))).
% 0.42/0.63  thf('13', plain,
% 0.42/0.63      (![X1 : $i, X2 : $i]:
% 0.42/0.63         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X2)))
% 0.42/0.63          | ~ (r2_hidden @ X1 @ (u1_pre_topc @ X2))
% 0.42/0.63          | (v3_pre_topc @ X1 @ X2)
% 0.42/0.63          | ~ (l1_pre_topc @ X2))),
% 0.42/0.63      inference('cnf', [status(esa)], [d5_pre_topc])).
% 0.42/0.63  thf('14', plain,
% 0.42/0.63      (((v1_tsep_1 @ sk_B_1 @ sk_A)
% 0.42/0.63        | ~ (l1_pre_topc @ sk_A)
% 0.42/0.63        | (v3_pre_topc @ (sk_C @ sk_B_1 @ sk_A) @ sk_A)
% 0.42/0.63        | ~ (r2_hidden @ (sk_C @ sk_B_1 @ sk_A) @ (u1_pre_topc @ sk_A)))),
% 0.42/0.63      inference('sup-', [status(thm)], ['12', '13'])).
% 0.42/0.63  thf('15', plain, ((l1_pre_topc @ sk_A)),
% 0.42/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.63  thf('16', plain,
% 0.42/0.63      (((v1_tsep_1 @ sk_B_1 @ sk_A)
% 0.42/0.63        | (v3_pre_topc @ (sk_C @ sk_B_1 @ sk_A) @ sk_A)
% 0.42/0.63        | ~ (r2_hidden @ (sk_C @ sk_B_1 @ sk_A) @ (u1_pre_topc @ sk_A)))),
% 0.42/0.63      inference('demod', [status(thm)], ['14', '15'])).
% 0.42/0.63  thf('17', plain,
% 0.42/0.63      (((~ (r2_hidden @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_A))
% 0.42/0.63         | (v3_pre_topc @ (sk_C @ sk_B_1 @ sk_A) @ sk_A)
% 0.42/0.63         | (v1_tsep_1 @ sk_B_1 @ sk_A))) <= (~ ((v1_tsep_1 @ sk_B_1 @ sk_A)))),
% 0.42/0.63      inference('sup-', [status(thm)], ['7', '16'])).
% 0.42/0.63  thf('18', plain,
% 0.42/0.63      ((((sk_C @ sk_B_1 @ sk_A) = (u1_struct_0 @ sk_B_1)))
% 0.42/0.63         <= (~ ((v1_tsep_1 @ sk_B_1 @ sk_A)))),
% 0.42/0.63      inference('sup-', [status(thm)], ['4', '6'])).
% 0.42/0.63  thf('19', plain,
% 0.42/0.63      (((~ (r2_hidden @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_A))
% 0.42/0.63         | (v3_pre_topc @ (u1_struct_0 @ sk_B_1) @ sk_A)
% 0.42/0.63         | (v1_tsep_1 @ sk_B_1 @ sk_A))) <= (~ ((v1_tsep_1 @ sk_B_1 @ sk_A)))),
% 0.42/0.63      inference('demod', [status(thm)], ['17', '18'])).
% 0.42/0.63  thf('20', plain,
% 0.42/0.63      ((((sk_C @ sk_B_1 @ sk_A) = (u1_struct_0 @ sk_B_1)))
% 0.42/0.63         <= (~ ((v1_tsep_1 @ sk_B_1 @ sk_A)))),
% 0.42/0.63      inference('sup-', [status(thm)], ['4', '6'])).
% 0.42/0.63  thf('21', plain,
% 0.42/0.63      (![X6 : $i, X7 : $i]:
% 0.42/0.63         (~ (m1_pre_topc @ X6 @ X7)
% 0.42/0.63          | ~ (v3_pre_topc @ (sk_C @ X6 @ X7) @ X7)
% 0.42/0.63          | (v1_tsep_1 @ X6 @ X7)
% 0.42/0.63          | ~ (l1_pre_topc @ X7))),
% 0.42/0.63      inference('cnf', [status(esa)], [d1_tsep_1])).
% 0.42/0.63  thf('22', plain,
% 0.42/0.63      (((~ (v3_pre_topc @ (u1_struct_0 @ sk_B_1) @ sk_A)
% 0.42/0.63         | ~ (l1_pre_topc @ sk_A)
% 0.42/0.63         | (v1_tsep_1 @ sk_B_1 @ sk_A)
% 0.42/0.63         | ~ (m1_pre_topc @ sk_B_1 @ sk_A)))
% 0.42/0.63         <= (~ ((v1_tsep_1 @ sk_B_1 @ sk_A)))),
% 0.42/0.63      inference('sup-', [status(thm)], ['20', '21'])).
% 0.42/0.63  thf('23', plain, ((l1_pre_topc @ sk_A)),
% 0.42/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.63  thf('24', plain, ((m1_pre_topc @ sk_B_1 @ sk_A)),
% 0.42/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.63  thf('25', plain,
% 0.42/0.63      (((~ (v3_pre_topc @ (u1_struct_0 @ sk_B_1) @ sk_A)
% 0.42/0.63         | (v1_tsep_1 @ sk_B_1 @ sk_A))) <= (~ ((v1_tsep_1 @ sk_B_1 @ sk_A)))),
% 0.42/0.63      inference('demod', [status(thm)], ['22', '23', '24'])).
% 0.42/0.63  thf('26', plain,
% 0.42/0.63      ((~ (v1_tsep_1 @ sk_B_1 @ sk_A)) <= (~ ((v1_tsep_1 @ sk_B_1 @ sk_A)))),
% 0.42/0.63      inference('split', [status(esa)], ['5'])).
% 0.42/0.63  thf('27', plain,
% 0.42/0.63      ((~ (v3_pre_topc @ (u1_struct_0 @ sk_B_1) @ sk_A))
% 0.42/0.63         <= (~ ((v1_tsep_1 @ sk_B_1 @ sk_A)))),
% 0.42/0.63      inference('clc', [status(thm)], ['25', '26'])).
% 0.42/0.63  thf('28', plain,
% 0.42/0.63      ((((v1_tsep_1 @ sk_B_1 @ sk_A)
% 0.42/0.63         | ~ (r2_hidden @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_A))))
% 0.42/0.63         <= (~ ((v1_tsep_1 @ sk_B_1 @ sk_A)))),
% 0.42/0.63      inference('clc', [status(thm)], ['19', '27'])).
% 0.42/0.63  thf('29', plain,
% 0.42/0.63      ((~ (v1_tsep_1 @ sk_B_1 @ sk_A)) <= (~ ((v1_tsep_1 @ sk_B_1 @ sk_A)))),
% 0.42/0.63      inference('split', [status(esa)], ['5'])).
% 0.42/0.63  thf('30', plain,
% 0.42/0.63      ((~ (r2_hidden @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_A)))
% 0.42/0.63         <= (~ ((v1_tsep_1 @ sk_B_1 @ sk_A)))),
% 0.42/0.63      inference('clc', [status(thm)], ['28', '29'])).
% 0.42/0.63  thf('31', plain,
% 0.42/0.63      (~ ((v1_tsep_1 @ sk_B_1 @ sk_A)) | 
% 0.42/0.63       ~
% 0.42/0.63       (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.42/0.63          = (k8_tmap_1 @ sk_A @ sk_B_1))) | 
% 0.42/0.63       ~ ((m1_pre_topc @ sk_B_1 @ sk_A))),
% 0.42/0.63      inference('split', [status(esa)], ['5'])).
% 0.42/0.63  thf('32', plain, ((m1_pre_topc @ sk_B_1 @ sk_A)),
% 0.42/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.63  thf('33', plain,
% 0.42/0.63      ((~ (m1_pre_topc @ sk_B_1 @ sk_A)) <= (~ ((m1_pre_topc @ sk_B_1 @ sk_A)))),
% 0.42/0.63      inference('split', [status(esa)], ['5'])).
% 0.42/0.63  thf('34', plain, (((m1_pre_topc @ sk_B_1 @ sk_A))),
% 0.42/0.63      inference('sup-', [status(thm)], ['32', '33'])).
% 0.42/0.63  thf('35', plain, ((m1_pre_topc @ sk_B_1 @ sk_A)),
% 0.42/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.63  thf(t1_tsep_1, axiom,
% 0.42/0.63    (![A:$i]:
% 0.42/0.63     ( ( l1_pre_topc @ A ) =>
% 0.42/0.63       ( ![B:$i]:
% 0.42/0.63         ( ( m1_pre_topc @ B @ A ) =>
% 0.42/0.63           ( m1_subset_1 @
% 0.42/0.63             ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.42/0.63  thf('36', plain,
% 0.42/0.63      (![X20 : $i, X21 : $i]:
% 0.42/0.63         (~ (m1_pre_topc @ X20 @ X21)
% 0.42/0.63          | (m1_subset_1 @ (u1_struct_0 @ X20) @ 
% 0.42/0.63             (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.42/0.63          | ~ (l1_pre_topc @ X21))),
% 0.42/0.63      inference('cnf', [status(esa)], [t1_tsep_1])).
% 0.42/0.63  thf('37', plain,
% 0.42/0.63      ((~ (l1_pre_topc @ sk_A)
% 0.42/0.63        | (m1_subset_1 @ (u1_struct_0 @ sk_B_1) @ 
% 0.42/0.63           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.42/0.63      inference('sup-', [status(thm)], ['35', '36'])).
% 0.42/0.63  thf('38', plain, ((l1_pre_topc @ sk_A)),
% 0.42/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.63  thf('39', plain,
% 0.42/0.63      ((m1_subset_1 @ (u1_struct_0 @ sk_B_1) @ 
% 0.42/0.63        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.42/0.63      inference('demod', [status(thm)], ['37', '38'])).
% 0.42/0.63  thf(t114_tmap_1, axiom,
% 0.42/0.63    (![A:$i]:
% 0.42/0.63     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.42/0.63       ( ![B:$i]:
% 0.42/0.63         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.42/0.63           ( ( ( u1_struct_0 @ ( k8_tmap_1 @ A @ B ) ) = ( u1_struct_0 @ A ) ) & 
% 0.42/0.63             ( ![C:$i]:
% 0.42/0.63               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.42/0.63                 ( ( ( C ) = ( u1_struct_0 @ B ) ) =>
% 0.42/0.63                   ( ( u1_pre_topc @ ( k8_tmap_1 @ A @ B ) ) =
% 0.42/0.63                     ( k5_tmap_1 @ A @ C ) ) ) ) ) ) ) ) ))).
% 0.42/0.63  thf('40', plain,
% 0.42/0.63      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.42/0.63         ((v2_struct_0 @ X17)
% 0.42/0.63          | ~ (m1_pre_topc @ X17 @ X18)
% 0.42/0.63          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.42/0.63          | ((u1_pre_topc @ (k8_tmap_1 @ X18 @ X17)) = (k5_tmap_1 @ X18 @ X19))
% 0.42/0.63          | ((X19) != (u1_struct_0 @ X17))
% 0.42/0.63          | ~ (l1_pre_topc @ X18)
% 0.42/0.63          | ~ (v2_pre_topc @ X18)
% 0.42/0.63          | (v2_struct_0 @ X18))),
% 0.42/0.63      inference('cnf', [status(esa)], [t114_tmap_1])).
% 0.42/0.63  thf('41', plain,
% 0.42/0.63      (![X17 : $i, X18 : $i]:
% 0.42/0.63         ((v2_struct_0 @ X18)
% 0.42/0.63          | ~ (v2_pre_topc @ X18)
% 0.42/0.63          | ~ (l1_pre_topc @ X18)
% 0.42/0.63          | ((u1_pre_topc @ (k8_tmap_1 @ X18 @ X17))
% 0.42/0.63              = (k5_tmap_1 @ X18 @ (u1_struct_0 @ X17)))
% 0.42/0.63          | ~ (m1_subset_1 @ (u1_struct_0 @ X17) @ 
% 0.42/0.63               (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.42/0.63          | ~ (m1_pre_topc @ X17 @ X18)
% 0.42/0.63          | (v2_struct_0 @ X17))),
% 0.42/0.63      inference('simplify', [status(thm)], ['40'])).
% 0.42/0.63  thf('42', plain,
% 0.42/0.63      (((v2_struct_0 @ sk_B_1)
% 0.42/0.63        | ~ (m1_pre_topc @ sk_B_1 @ sk_A)
% 0.42/0.63        | ((u1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B_1))
% 0.42/0.63            = (k5_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B_1)))
% 0.42/0.63        | ~ (l1_pre_topc @ sk_A)
% 0.42/0.63        | ~ (v2_pre_topc @ sk_A)
% 0.42/0.63        | (v2_struct_0 @ sk_A))),
% 0.42/0.63      inference('sup-', [status(thm)], ['39', '41'])).
% 0.42/0.63  thf('43', plain, ((m1_pre_topc @ sk_B_1 @ sk_A)),
% 0.42/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.63  thf('44', plain, ((l1_pre_topc @ sk_A)),
% 0.42/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.63  thf('45', plain, ((v2_pre_topc @ sk_A)),
% 0.42/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.63  thf('46', plain,
% 0.42/0.63      (((v2_struct_0 @ sk_B_1)
% 0.42/0.63        | ((u1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B_1))
% 0.42/0.63            = (k5_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B_1)))
% 0.42/0.63        | (v2_struct_0 @ sk_A))),
% 0.42/0.63      inference('demod', [status(thm)], ['42', '43', '44', '45'])).
% 0.42/0.63  thf('47', plain, (~ (v2_struct_0 @ sk_B_1)),
% 0.42/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.63  thf('48', plain,
% 0.42/0.63      (((v2_struct_0 @ sk_A)
% 0.42/0.63        | ((u1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B_1))
% 0.42/0.63            = (k5_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B_1))))),
% 0.42/0.63      inference('clc', [status(thm)], ['46', '47'])).
% 0.42/0.63  thf('49', plain, (~ (v2_struct_0 @ sk_A)),
% 0.42/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.63  thf('50', plain,
% 0.42/0.63      (((u1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B_1))
% 0.42/0.63         = (k5_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B_1)))),
% 0.42/0.63      inference('clc', [status(thm)], ['48', '49'])).
% 0.42/0.63  thf('51', plain,
% 0.42/0.63      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.42/0.63          = (k8_tmap_1 @ sk_A @ sk_B_1))
% 0.42/0.63        | (v1_tsep_1 @ sk_B_1 @ sk_A))),
% 0.42/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.63  thf('52', plain,
% 0.42/0.63      (((v1_tsep_1 @ sk_B_1 @ sk_A)) <= (((v1_tsep_1 @ sk_B_1 @ sk_A)))),
% 0.42/0.63      inference('split', [status(esa)], ['51'])).
% 0.42/0.63  thf('53', plain,
% 0.42/0.63      ((m1_subset_1 @ (u1_struct_0 @ sk_B_1) @ 
% 0.42/0.63        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.42/0.63      inference('demod', [status(thm)], ['37', '38'])).
% 0.42/0.63  thf('54', plain,
% 0.42/0.63      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.42/0.63         (~ (m1_pre_topc @ X6 @ X7)
% 0.42/0.63          | ~ (v1_tsep_1 @ X6 @ X7)
% 0.42/0.63          | ((X8) != (u1_struct_0 @ X6))
% 0.42/0.63          | (v3_pre_topc @ X8 @ X7)
% 0.42/0.63          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (u1_struct_0 @ X7)))
% 0.42/0.63          | ~ (l1_pre_topc @ X7))),
% 0.42/0.63      inference('cnf', [status(esa)], [d1_tsep_1])).
% 0.42/0.63  thf('55', plain,
% 0.42/0.63      (![X6 : $i, X7 : $i]:
% 0.42/0.63         (~ (l1_pre_topc @ X7)
% 0.42/0.63          | ~ (m1_subset_1 @ (u1_struct_0 @ X6) @ 
% 0.42/0.63               (k1_zfmisc_1 @ (u1_struct_0 @ X7)))
% 0.42/0.63          | (v3_pre_topc @ (u1_struct_0 @ X6) @ X7)
% 0.42/0.63          | ~ (v1_tsep_1 @ X6 @ X7)
% 0.42/0.63          | ~ (m1_pre_topc @ X6 @ X7))),
% 0.42/0.63      inference('simplify', [status(thm)], ['54'])).
% 0.42/0.63  thf('56', plain,
% 0.42/0.63      ((~ (m1_pre_topc @ sk_B_1 @ sk_A)
% 0.42/0.63        | ~ (v1_tsep_1 @ sk_B_1 @ sk_A)
% 0.42/0.63        | (v3_pre_topc @ (u1_struct_0 @ sk_B_1) @ sk_A)
% 0.42/0.63        | ~ (l1_pre_topc @ sk_A))),
% 0.42/0.63      inference('sup-', [status(thm)], ['53', '55'])).
% 0.42/0.63  thf('57', plain, ((m1_pre_topc @ sk_B_1 @ sk_A)),
% 0.42/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.63  thf('58', plain, ((l1_pre_topc @ sk_A)),
% 0.42/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.63  thf('59', plain,
% 0.42/0.63      ((~ (v1_tsep_1 @ sk_B_1 @ sk_A)
% 0.42/0.63        | (v3_pre_topc @ (u1_struct_0 @ sk_B_1) @ sk_A))),
% 0.42/0.63      inference('demod', [status(thm)], ['56', '57', '58'])).
% 0.42/0.63  thf('60', plain,
% 0.42/0.63      (((v3_pre_topc @ (u1_struct_0 @ sk_B_1) @ sk_A))
% 0.42/0.63         <= (((v1_tsep_1 @ sk_B_1 @ sk_A)))),
% 0.42/0.63      inference('sup-', [status(thm)], ['52', '59'])).
% 0.42/0.63  thf('61', plain,
% 0.42/0.63      ((m1_subset_1 @ (u1_struct_0 @ sk_B_1) @ 
% 0.42/0.63        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.42/0.63      inference('demod', [status(thm)], ['37', '38'])).
% 0.42/0.63  thf('62', plain,
% 0.42/0.63      (![X1 : $i, X2 : $i]:
% 0.42/0.63         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X2)))
% 0.42/0.63          | ~ (v3_pre_topc @ X1 @ X2)
% 0.42/0.63          | (r2_hidden @ X1 @ (u1_pre_topc @ X2))
% 0.42/0.63          | ~ (l1_pre_topc @ X2))),
% 0.42/0.63      inference('cnf', [status(esa)], [d5_pre_topc])).
% 0.42/0.63  thf('63', plain,
% 0.42/0.63      ((~ (l1_pre_topc @ sk_A)
% 0.42/0.63        | (r2_hidden @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_A))
% 0.42/0.63        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_B_1) @ sk_A))),
% 0.42/0.63      inference('sup-', [status(thm)], ['61', '62'])).
% 0.42/0.63  thf('64', plain, ((l1_pre_topc @ sk_A)),
% 0.42/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.63  thf('65', plain,
% 0.42/0.63      (((r2_hidden @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_A))
% 0.42/0.63        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_B_1) @ sk_A))),
% 0.42/0.63      inference('demod', [status(thm)], ['63', '64'])).
% 0.42/0.63  thf('66', plain,
% 0.42/0.63      (((r2_hidden @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_A)))
% 0.42/0.63         <= (((v1_tsep_1 @ sk_B_1 @ sk_A)))),
% 0.42/0.63      inference('sup-', [status(thm)], ['60', '65'])).
% 0.42/0.63  thf('67', plain,
% 0.42/0.63      ((m1_subset_1 @ (u1_struct_0 @ sk_B_1) @ 
% 0.42/0.63        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.42/0.63      inference('demod', [status(thm)], ['37', '38'])).
% 0.42/0.63  thf(t103_tmap_1, axiom,
% 0.42/0.63    (![A:$i]:
% 0.42/0.63     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.42/0.63       ( ![B:$i]:
% 0.42/0.63         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.42/0.63           ( ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) <=>
% 0.42/0.63             ( ( u1_pre_topc @ A ) = ( k5_tmap_1 @ A @ B ) ) ) ) ) ))).
% 0.42/0.63  thf('68', plain,
% 0.42/0.63      (![X13 : $i, X14 : $i]:
% 0.42/0.63         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.42/0.63          | ~ (r2_hidden @ X13 @ (u1_pre_topc @ X14))
% 0.42/0.63          | ((u1_pre_topc @ X14) = (k5_tmap_1 @ X14 @ X13))
% 0.42/0.63          | ~ (l1_pre_topc @ X14)
% 0.42/0.63          | ~ (v2_pre_topc @ X14)
% 0.42/0.63          | (v2_struct_0 @ X14))),
% 0.42/0.63      inference('cnf', [status(esa)], [t103_tmap_1])).
% 0.42/0.63  thf('69', plain,
% 0.42/0.63      (((v2_struct_0 @ sk_A)
% 0.42/0.63        | ~ (v2_pre_topc @ sk_A)
% 0.42/0.63        | ~ (l1_pre_topc @ sk_A)
% 0.42/0.63        | ((u1_pre_topc @ sk_A) = (k5_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B_1)))
% 0.42/0.63        | ~ (r2_hidden @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_A)))),
% 0.42/0.63      inference('sup-', [status(thm)], ['67', '68'])).
% 0.42/0.63  thf('70', plain, ((v2_pre_topc @ sk_A)),
% 0.42/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.63  thf('71', plain, ((l1_pre_topc @ sk_A)),
% 0.42/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.63  thf('72', plain,
% 0.42/0.63      (((v2_struct_0 @ sk_A)
% 0.42/0.63        | ((u1_pre_topc @ sk_A) = (k5_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B_1)))
% 0.42/0.63        | ~ (r2_hidden @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_A)))),
% 0.42/0.63      inference('demod', [status(thm)], ['69', '70', '71'])).
% 0.42/0.63  thf('73', plain, (~ (v2_struct_0 @ sk_A)),
% 0.42/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.63  thf('74', plain,
% 0.42/0.63      ((~ (r2_hidden @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_A))
% 0.42/0.63        | ((u1_pre_topc @ sk_A) = (k5_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B_1))))),
% 0.42/0.63      inference('clc', [status(thm)], ['72', '73'])).
% 0.42/0.63  thf('75', plain,
% 0.42/0.63      ((((u1_pre_topc @ sk_A) = (k5_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B_1))))
% 0.42/0.63         <= (((v1_tsep_1 @ sk_B_1 @ sk_A)))),
% 0.42/0.63      inference('sup-', [status(thm)], ['66', '74'])).
% 0.42/0.63  thf('76', plain,
% 0.42/0.63      ((((u1_pre_topc @ sk_A) = (u1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B_1))))
% 0.42/0.63         <= (((v1_tsep_1 @ sk_B_1 @ sk_A)))),
% 0.42/0.63      inference('sup+', [status(thm)], ['50', '75'])).
% 0.42/0.63  thf(abstractness_v1_pre_topc, axiom,
% 0.42/0.63    (![A:$i]:
% 0.42/0.63     ( ( l1_pre_topc @ A ) =>
% 0.42/0.63       ( ( v1_pre_topc @ A ) =>
% 0.42/0.63         ( ( A ) = ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ))).
% 0.42/0.63  thf('77', plain,
% 0.42/0.63      (![X0 : $i]:
% 0.42/0.63         (~ (v1_pre_topc @ X0)
% 0.42/0.63          | ((X0) = (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.42/0.63          | ~ (l1_pre_topc @ X0))),
% 0.42/0.63      inference('cnf', [status(esa)], [abstractness_v1_pre_topc])).
% 0.42/0.63  thf('78', plain,
% 0.42/0.63      (((((k8_tmap_1 @ sk_A @ sk_B_1)
% 0.42/0.63           = (g1_pre_topc @ (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B_1)) @ 
% 0.42/0.63              (u1_pre_topc @ sk_A)))
% 0.42/0.63         | ~ (l1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B_1))
% 0.42/0.63         | ~ (v1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B_1))))
% 0.42/0.63         <= (((v1_tsep_1 @ sk_B_1 @ sk_A)))),
% 0.42/0.63      inference('sup+', [status(thm)], ['76', '77'])).
% 0.42/0.63  thf('79', plain, ((m1_pre_topc @ sk_B_1 @ sk_A)),
% 0.42/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.63  thf('80', plain,
% 0.42/0.63      (![X17 : $i, X18 : $i]:
% 0.42/0.63         ((v2_struct_0 @ X17)
% 0.42/0.63          | ~ (m1_pre_topc @ X17 @ X18)
% 0.42/0.63          | ((u1_struct_0 @ (k8_tmap_1 @ X18 @ X17)) = (u1_struct_0 @ X18))
% 0.42/0.63          | ~ (l1_pre_topc @ X18)
% 0.42/0.63          | ~ (v2_pre_topc @ X18)
% 0.42/0.63          | (v2_struct_0 @ X18))),
% 0.42/0.63      inference('cnf', [status(esa)], [t114_tmap_1])).
% 0.42/0.63  thf('81', plain,
% 0.42/0.63      (((v2_struct_0 @ sk_A)
% 0.42/0.63        | ~ (v2_pre_topc @ sk_A)
% 0.42/0.63        | ~ (l1_pre_topc @ sk_A)
% 0.42/0.63        | ((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B_1)) = (u1_struct_0 @ sk_A))
% 0.42/0.63        | (v2_struct_0 @ sk_B_1))),
% 0.42/0.63      inference('sup-', [status(thm)], ['79', '80'])).
% 0.42/0.63  thf('82', plain, ((v2_pre_topc @ sk_A)),
% 0.42/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.63  thf('83', plain, ((l1_pre_topc @ sk_A)),
% 0.42/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.63  thf('84', plain,
% 0.42/0.63      (((v2_struct_0 @ sk_A)
% 0.42/0.63        | ((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B_1)) = (u1_struct_0 @ sk_A))
% 0.42/0.63        | (v2_struct_0 @ sk_B_1))),
% 0.42/0.63      inference('demod', [status(thm)], ['81', '82', '83'])).
% 0.42/0.63  thf('85', plain, (~ (v2_struct_0 @ sk_A)),
% 0.42/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.63  thf('86', plain,
% 0.42/0.63      (((v2_struct_0 @ sk_B_1)
% 0.42/0.63        | ((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B_1)) = (u1_struct_0 @ sk_A)))),
% 0.42/0.63      inference('clc', [status(thm)], ['84', '85'])).
% 0.42/0.63  thf('87', plain, (~ (v2_struct_0 @ sk_B_1)),
% 0.42/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.63  thf('88', plain,
% 0.42/0.63      (((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B_1)) = (u1_struct_0 @ sk_A))),
% 0.42/0.63      inference('clc', [status(thm)], ['86', '87'])).
% 0.42/0.63  thf('89', plain,
% 0.42/0.63      ((((u1_pre_topc @ sk_A) = (k5_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B_1))))
% 0.42/0.63         <= (((v1_tsep_1 @ sk_B_1 @ sk_A)))),
% 0.42/0.63      inference('sup-', [status(thm)], ['66', '74'])).
% 0.42/0.63  thf('90', plain,
% 0.42/0.63      ((m1_subset_1 @ (u1_struct_0 @ sk_B_1) @ 
% 0.42/0.63        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.42/0.63      inference('demod', [status(thm)], ['37', '38'])).
% 0.42/0.63  thf(d9_tmap_1, axiom,
% 0.42/0.63    (![A:$i]:
% 0.42/0.63     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.42/0.63       ( ![B:$i]:
% 0.42/0.63         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.42/0.63           ( ( k6_tmap_1 @ A @ B ) =
% 0.42/0.63             ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( k5_tmap_1 @ A @ B ) ) ) ) ) ))).
% 0.42/0.63  thf('91', plain,
% 0.42/0.63      (![X9 : $i, X10 : $i]:
% 0.42/0.63         (~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 0.42/0.63          | ((k6_tmap_1 @ X10 @ X9)
% 0.42/0.63              = (g1_pre_topc @ (u1_struct_0 @ X10) @ (k5_tmap_1 @ X10 @ X9)))
% 0.42/0.63          | ~ (l1_pre_topc @ X10)
% 0.42/0.63          | ~ (v2_pre_topc @ X10)
% 0.42/0.63          | (v2_struct_0 @ X10))),
% 0.42/0.63      inference('cnf', [status(esa)], [d9_tmap_1])).
% 0.42/0.63  thf('92', plain,
% 0.42/0.63      (((v2_struct_0 @ sk_A)
% 0.42/0.63        | ~ (v2_pre_topc @ sk_A)
% 0.42/0.63        | ~ (l1_pre_topc @ sk_A)
% 0.42/0.63        | ((k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B_1))
% 0.42/0.63            = (g1_pre_topc @ (u1_struct_0 @ sk_A) @ 
% 0.42/0.63               (k5_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B_1)))))),
% 0.42/0.63      inference('sup-', [status(thm)], ['90', '91'])).
% 0.42/0.63  thf('93', plain, ((v2_pre_topc @ sk_A)),
% 0.42/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.63  thf('94', plain, ((l1_pre_topc @ sk_A)),
% 0.42/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.63  thf('95', plain,
% 0.42/0.63      (((v2_struct_0 @ sk_A)
% 0.42/0.63        | ((k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B_1))
% 0.42/0.63            = (g1_pre_topc @ (u1_struct_0 @ sk_A) @ 
% 0.42/0.63               (k5_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B_1)))))),
% 0.42/0.63      inference('demod', [status(thm)], ['92', '93', '94'])).
% 0.42/0.63  thf('96', plain, (~ (v2_struct_0 @ sk_A)),
% 0.42/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.63  thf('97', plain,
% 0.42/0.63      (((k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B_1))
% 0.42/0.63         = (g1_pre_topc @ (u1_struct_0 @ sk_A) @ 
% 0.42/0.63            (k5_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B_1))))),
% 0.42/0.63      inference('clc', [status(thm)], ['95', '96'])).
% 0.42/0.63  thf('98', plain,
% 0.42/0.63      ((((k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B_1))
% 0.42/0.63          = (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))
% 0.42/0.63         <= (((v1_tsep_1 @ sk_B_1 @ sk_A)))),
% 0.42/0.63      inference('sup+', [status(thm)], ['89', '97'])).
% 0.42/0.63  thf(rc1_connsp_1, axiom,
% 0.42/0.63    (![A:$i]:
% 0.42/0.63     ( ( l1_pre_topc @ A ) =>
% 0.42/0.63       ( ?[B:$i]:
% 0.42/0.63         ( ( v1_xboole_0 @ B ) & 
% 0.42/0.63           ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.42/0.63  thf('99', plain,
% 0.42/0.63      (![X5 : $i]: ((v1_xboole_0 @ (sk_B @ X5)) | ~ (l1_pre_topc @ X5))),
% 0.42/0.63      inference('cnf', [status(esa)], [rc1_connsp_1])).
% 0.42/0.63  thf('100', plain,
% 0.42/0.63      (![X5 : $i]:
% 0.42/0.63         ((m1_subset_1 @ (sk_B @ X5) @ (k1_zfmisc_1 @ (u1_struct_0 @ X5)))
% 0.42/0.63          | ~ (l1_pre_topc @ X5))),
% 0.42/0.63      inference('cnf', [status(esa)], [rc1_connsp_1])).
% 0.42/0.63  thf(cc1_tops_1, axiom,
% 0.42/0.63    (![A:$i]:
% 0.42/0.63     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.42/0.63       ( ![B:$i]:
% 0.42/0.63         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.42/0.63           ( ( v1_xboole_0 @ B ) => ( v3_pre_topc @ B @ A ) ) ) ) ))).
% 0.42/0.63  thf('101', plain,
% 0.42/0.63      (![X3 : $i, X4 : $i]:
% 0.42/0.63         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (u1_struct_0 @ X4)))
% 0.42/0.63          | (v3_pre_topc @ X3 @ X4)
% 0.42/0.63          | ~ (v1_xboole_0 @ X3)
% 0.42/0.63          | ~ (l1_pre_topc @ X4)
% 0.42/0.63          | ~ (v2_pre_topc @ X4))),
% 0.42/0.63      inference('cnf', [status(esa)], [cc1_tops_1])).
% 0.42/0.63  thf('102', plain,
% 0.42/0.63      (![X0 : $i]:
% 0.42/0.63         (~ (l1_pre_topc @ X0)
% 0.42/0.63          | ~ (v2_pre_topc @ X0)
% 0.42/0.63          | ~ (l1_pre_topc @ X0)
% 0.42/0.63          | ~ (v1_xboole_0 @ (sk_B @ X0))
% 0.42/0.63          | (v3_pre_topc @ (sk_B @ X0) @ X0))),
% 0.42/0.63      inference('sup-', [status(thm)], ['100', '101'])).
% 0.42/0.63  thf('103', plain,
% 0.42/0.63      (![X0 : $i]:
% 0.42/0.63         ((v3_pre_topc @ (sk_B @ X0) @ X0)
% 0.42/0.63          | ~ (v1_xboole_0 @ (sk_B @ X0))
% 0.42/0.63          | ~ (v2_pre_topc @ X0)
% 0.42/0.63          | ~ (l1_pre_topc @ X0))),
% 0.42/0.63      inference('simplify', [status(thm)], ['102'])).
% 0.42/0.63  thf('104', plain,
% 0.42/0.63      (![X0 : $i]:
% 0.42/0.63         (~ (l1_pre_topc @ X0)
% 0.42/0.63          | ~ (l1_pre_topc @ X0)
% 0.42/0.63          | ~ (v2_pre_topc @ X0)
% 0.42/0.63          | (v3_pre_topc @ (sk_B @ X0) @ X0))),
% 0.42/0.63      inference('sup-', [status(thm)], ['99', '103'])).
% 0.42/0.63  thf('105', plain,
% 0.42/0.63      (![X0 : $i]:
% 0.42/0.63         ((v3_pre_topc @ (sk_B @ X0) @ X0)
% 0.42/0.63          | ~ (v2_pre_topc @ X0)
% 0.42/0.63          | ~ (l1_pre_topc @ X0))),
% 0.42/0.63      inference('simplify', [status(thm)], ['104'])).
% 0.42/0.63  thf('106', plain,
% 0.42/0.63      (![X5 : $i]:
% 0.42/0.63         ((m1_subset_1 @ (sk_B @ X5) @ (k1_zfmisc_1 @ (u1_struct_0 @ X5)))
% 0.42/0.63          | ~ (l1_pre_topc @ X5))),
% 0.42/0.63      inference('cnf', [status(esa)], [rc1_connsp_1])).
% 0.42/0.63  thf('107', plain,
% 0.42/0.63      (![X1 : $i, X2 : $i]:
% 0.42/0.63         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X2)))
% 0.42/0.63          | ~ (v3_pre_topc @ X1 @ X2)
% 0.42/0.63          | (r2_hidden @ X1 @ (u1_pre_topc @ X2))
% 0.42/0.63          | ~ (l1_pre_topc @ X2))),
% 0.42/0.63      inference('cnf', [status(esa)], [d5_pre_topc])).
% 0.42/0.63  thf('108', plain,
% 0.42/0.63      (![X0 : $i]:
% 0.42/0.63         (~ (l1_pre_topc @ X0)
% 0.42/0.63          | ~ (l1_pre_topc @ X0)
% 0.42/0.63          | (r2_hidden @ (sk_B @ X0) @ (u1_pre_topc @ X0))
% 0.42/0.63          | ~ (v3_pre_topc @ (sk_B @ X0) @ X0))),
% 0.42/0.63      inference('sup-', [status(thm)], ['106', '107'])).
% 0.42/0.63  thf('109', plain,
% 0.42/0.63      (![X0 : $i]:
% 0.42/0.63         (~ (v3_pre_topc @ (sk_B @ X0) @ X0)
% 0.42/0.63          | (r2_hidden @ (sk_B @ X0) @ (u1_pre_topc @ X0))
% 0.42/0.63          | ~ (l1_pre_topc @ X0))),
% 0.42/0.63      inference('simplify', [status(thm)], ['108'])).
% 0.42/0.63  thf('110', plain,
% 0.42/0.63      (![X0 : $i]:
% 0.42/0.63         (~ (l1_pre_topc @ X0)
% 0.42/0.63          | ~ (v2_pre_topc @ X0)
% 0.42/0.63          | ~ (l1_pre_topc @ X0)
% 0.42/0.63          | (r2_hidden @ (sk_B @ X0) @ (u1_pre_topc @ X0)))),
% 0.42/0.63      inference('sup-', [status(thm)], ['105', '109'])).
% 0.42/0.63  thf('111', plain,
% 0.42/0.63      (![X0 : $i]:
% 0.42/0.63         ((r2_hidden @ (sk_B @ X0) @ (u1_pre_topc @ X0))
% 0.42/0.63          | ~ (v2_pre_topc @ X0)
% 0.42/0.63          | ~ (l1_pre_topc @ X0))),
% 0.42/0.63      inference('simplify', [status(thm)], ['110'])).
% 0.42/0.63  thf('112', plain,
% 0.42/0.63      (![X5 : $i]:
% 0.42/0.63         ((m1_subset_1 @ (sk_B @ X5) @ (k1_zfmisc_1 @ (u1_struct_0 @ X5)))
% 0.42/0.63          | ~ (l1_pre_topc @ X5))),
% 0.42/0.63      inference('cnf', [status(esa)], [rc1_connsp_1])).
% 0.42/0.63  thf('113', plain,
% 0.42/0.63      (![X13 : $i, X14 : $i]:
% 0.42/0.63         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.42/0.63          | ~ (r2_hidden @ X13 @ (u1_pre_topc @ X14))
% 0.42/0.63          | ((u1_pre_topc @ X14) = (k5_tmap_1 @ X14 @ X13))
% 0.42/0.63          | ~ (l1_pre_topc @ X14)
% 0.42/0.63          | ~ (v2_pre_topc @ X14)
% 0.42/0.63          | (v2_struct_0 @ X14))),
% 0.42/0.63      inference('cnf', [status(esa)], [t103_tmap_1])).
% 0.42/0.63  thf('114', plain,
% 0.42/0.63      (![X0 : $i]:
% 0.42/0.63         (~ (l1_pre_topc @ X0)
% 0.42/0.63          | (v2_struct_0 @ X0)
% 0.42/0.63          | ~ (v2_pre_topc @ X0)
% 0.42/0.63          | ~ (l1_pre_topc @ X0)
% 0.42/0.63          | ((u1_pre_topc @ X0) = (k5_tmap_1 @ X0 @ (sk_B @ X0)))
% 0.42/0.63          | ~ (r2_hidden @ (sk_B @ X0) @ (u1_pre_topc @ X0)))),
% 0.42/0.63      inference('sup-', [status(thm)], ['112', '113'])).
% 0.42/0.63  thf('115', plain,
% 0.42/0.63      (![X0 : $i]:
% 0.42/0.63         (~ (r2_hidden @ (sk_B @ X0) @ (u1_pre_topc @ X0))
% 0.42/0.63          | ((u1_pre_topc @ X0) = (k5_tmap_1 @ X0 @ (sk_B @ X0)))
% 0.42/0.63          | ~ (v2_pre_topc @ X0)
% 0.42/0.63          | (v2_struct_0 @ X0)
% 0.42/0.63          | ~ (l1_pre_topc @ X0))),
% 0.42/0.63      inference('simplify', [status(thm)], ['114'])).
% 0.42/0.63  thf('116', plain,
% 0.42/0.63      (![X0 : $i]:
% 0.42/0.63         (~ (l1_pre_topc @ X0)
% 0.42/0.63          | ~ (v2_pre_topc @ X0)
% 0.42/0.63          | ~ (l1_pre_topc @ X0)
% 0.42/0.63          | (v2_struct_0 @ X0)
% 0.42/0.63          | ~ (v2_pre_topc @ X0)
% 0.42/0.63          | ((u1_pre_topc @ X0) = (k5_tmap_1 @ X0 @ (sk_B @ X0))))),
% 0.42/0.63      inference('sup-', [status(thm)], ['111', '115'])).
% 0.42/0.63  thf('117', plain,
% 0.42/0.63      (![X0 : $i]:
% 0.42/0.63         (((u1_pre_topc @ X0) = (k5_tmap_1 @ X0 @ (sk_B @ X0)))
% 0.42/0.63          | (v2_struct_0 @ X0)
% 0.42/0.63          | ~ (v2_pre_topc @ X0)
% 0.42/0.63          | ~ (l1_pre_topc @ X0))),
% 0.42/0.63      inference('simplify', [status(thm)], ['116'])).
% 0.42/0.63  thf('118', plain,
% 0.42/0.63      (![X5 : $i]:
% 0.42/0.63         ((m1_subset_1 @ (sk_B @ X5) @ (k1_zfmisc_1 @ (u1_struct_0 @ X5)))
% 0.47/0.63          | ~ (l1_pre_topc @ X5))),
% 0.47/0.63      inference('cnf', [status(esa)], [rc1_connsp_1])).
% 0.47/0.63  thf('119', plain,
% 0.47/0.63      (![X9 : $i, X10 : $i]:
% 0.47/0.63         (~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 0.47/0.63          | ((k6_tmap_1 @ X10 @ X9)
% 0.47/0.63              = (g1_pre_topc @ (u1_struct_0 @ X10) @ (k5_tmap_1 @ X10 @ X9)))
% 0.47/0.63          | ~ (l1_pre_topc @ X10)
% 0.47/0.63          | ~ (v2_pre_topc @ X10)
% 0.47/0.63          | (v2_struct_0 @ X10))),
% 0.47/0.63      inference('cnf', [status(esa)], [d9_tmap_1])).
% 0.47/0.63  thf('120', plain,
% 0.47/0.63      (![X0 : $i]:
% 0.47/0.63         (~ (l1_pre_topc @ X0)
% 0.47/0.63          | (v2_struct_0 @ X0)
% 0.47/0.63          | ~ (v2_pre_topc @ X0)
% 0.47/0.63          | ~ (l1_pre_topc @ X0)
% 0.47/0.63          | ((k6_tmap_1 @ X0 @ (sk_B @ X0))
% 0.47/0.63              = (g1_pre_topc @ (u1_struct_0 @ X0) @ 
% 0.47/0.63                 (k5_tmap_1 @ X0 @ (sk_B @ X0)))))),
% 0.47/0.63      inference('sup-', [status(thm)], ['118', '119'])).
% 0.47/0.63  thf('121', plain,
% 0.47/0.63      (![X0 : $i]:
% 0.47/0.63         (((k6_tmap_1 @ X0 @ (sk_B @ X0))
% 0.47/0.63            = (g1_pre_topc @ (u1_struct_0 @ X0) @ 
% 0.47/0.63               (k5_tmap_1 @ X0 @ (sk_B @ X0))))
% 0.47/0.63          | ~ (v2_pre_topc @ X0)
% 0.47/0.63          | (v2_struct_0 @ X0)
% 0.47/0.63          | ~ (l1_pre_topc @ X0))),
% 0.47/0.63      inference('simplify', [status(thm)], ['120'])).
% 0.47/0.63  thf('122', plain,
% 0.47/0.63      (![X0 : $i]:
% 0.47/0.63         (((k6_tmap_1 @ X0 @ (sk_B @ X0))
% 0.47/0.63            = (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.47/0.63          | ~ (l1_pre_topc @ X0)
% 0.47/0.63          | ~ (v2_pre_topc @ X0)
% 0.47/0.63          | (v2_struct_0 @ X0)
% 0.47/0.63          | ~ (l1_pre_topc @ X0)
% 0.47/0.63          | (v2_struct_0 @ X0)
% 0.47/0.63          | ~ (v2_pre_topc @ X0))),
% 0.47/0.63      inference('sup+', [status(thm)], ['117', '121'])).
% 0.47/0.63  thf('123', plain,
% 0.47/0.63      (![X0 : $i]:
% 0.47/0.63         ((v2_struct_0 @ X0)
% 0.47/0.63          | ~ (v2_pre_topc @ X0)
% 0.47/0.63          | ~ (l1_pre_topc @ X0)
% 0.47/0.63          | ((k6_tmap_1 @ X0 @ (sk_B @ X0))
% 0.47/0.63              = (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 0.47/0.63      inference('simplify', [status(thm)], ['122'])).
% 0.47/0.63  thf('124', plain,
% 0.47/0.63      ((((k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B_1))
% 0.47/0.63          = (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))
% 0.47/0.63         <= (((v1_tsep_1 @ sk_B_1 @ sk_A)))),
% 0.47/0.63      inference('sup+', [status(thm)], ['89', '97'])).
% 0.47/0.63  thf('125', plain,
% 0.47/0.63      (((((k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B_1))
% 0.47/0.63           = (k6_tmap_1 @ sk_A @ (sk_B @ sk_A)))
% 0.47/0.63         | ~ (l1_pre_topc @ sk_A)
% 0.47/0.63         | ~ (v2_pre_topc @ sk_A)
% 0.47/0.63         | (v2_struct_0 @ sk_A))) <= (((v1_tsep_1 @ sk_B_1 @ sk_A)))),
% 0.47/0.63      inference('sup+', [status(thm)], ['123', '124'])).
% 0.47/0.63  thf('126', plain, ((l1_pre_topc @ sk_A)),
% 0.47/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.63  thf('127', plain, ((v2_pre_topc @ sk_A)),
% 0.47/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.63  thf('128', plain,
% 0.47/0.63      (((((k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B_1))
% 0.47/0.63           = (k6_tmap_1 @ sk_A @ (sk_B @ sk_A)))
% 0.47/0.63         | (v2_struct_0 @ sk_A))) <= (((v1_tsep_1 @ sk_B_1 @ sk_A)))),
% 0.47/0.63      inference('demod', [status(thm)], ['125', '126', '127'])).
% 0.47/0.63  thf('129', plain, (~ (v2_struct_0 @ sk_A)),
% 0.47/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.63  thf('130', plain,
% 0.47/0.63      ((((k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B_1))
% 0.47/0.63          = (k6_tmap_1 @ sk_A @ (sk_B @ sk_A))))
% 0.47/0.63         <= (((v1_tsep_1 @ sk_B_1 @ sk_A)))),
% 0.47/0.63      inference('clc', [status(thm)], ['128', '129'])).
% 0.47/0.63  thf('131', plain,
% 0.47/0.63      ((((k6_tmap_1 @ sk_A @ (sk_B @ sk_A))
% 0.47/0.63          = (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))
% 0.47/0.63         <= (((v1_tsep_1 @ sk_B_1 @ sk_A)))),
% 0.47/0.63      inference('demod', [status(thm)], ['98', '130'])).
% 0.47/0.63  thf('132', plain, ((m1_pre_topc @ sk_B_1 @ sk_A)),
% 0.47/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.63  thf(dt_k8_tmap_1, axiom,
% 0.47/0.63    (![A:$i,B:$i]:
% 0.47/0.63     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.47/0.63         ( l1_pre_topc @ A ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.47/0.63       ( ( v1_pre_topc @ ( k8_tmap_1 @ A @ B ) ) & 
% 0.47/0.63         ( v2_pre_topc @ ( k8_tmap_1 @ A @ B ) ) & 
% 0.47/0.63         ( l1_pre_topc @ ( k8_tmap_1 @ A @ B ) ) ) ))).
% 0.47/0.63  thf('133', plain,
% 0.47/0.63      (![X11 : $i, X12 : $i]:
% 0.47/0.63         (~ (l1_pre_topc @ X11)
% 0.47/0.63          | ~ (v2_pre_topc @ X11)
% 0.47/0.63          | (v2_struct_0 @ X11)
% 0.47/0.63          | ~ (m1_pre_topc @ X12 @ X11)
% 0.47/0.63          | (l1_pre_topc @ (k8_tmap_1 @ X11 @ X12)))),
% 0.47/0.63      inference('cnf', [status(esa)], [dt_k8_tmap_1])).
% 0.47/0.63  thf('134', plain,
% 0.47/0.63      (((l1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B_1))
% 0.47/0.63        | (v2_struct_0 @ sk_A)
% 0.47/0.63        | ~ (v2_pre_topc @ sk_A)
% 0.47/0.63        | ~ (l1_pre_topc @ sk_A))),
% 0.47/0.63      inference('sup-', [status(thm)], ['132', '133'])).
% 0.47/0.63  thf('135', plain, ((v2_pre_topc @ sk_A)),
% 0.47/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.63  thf('136', plain, ((l1_pre_topc @ sk_A)),
% 0.47/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.63  thf('137', plain,
% 0.47/0.63      (((l1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B_1)) | (v2_struct_0 @ sk_A))),
% 0.47/0.63      inference('demod', [status(thm)], ['134', '135', '136'])).
% 0.47/0.63  thf('138', plain, (~ (v2_struct_0 @ sk_A)),
% 0.47/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.63  thf('139', plain, ((l1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B_1))),
% 0.47/0.63      inference('clc', [status(thm)], ['137', '138'])).
% 0.47/0.63  thf('140', plain, ((m1_pre_topc @ sk_B_1 @ sk_A)),
% 0.47/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.63  thf('141', plain,
% 0.47/0.63      (![X11 : $i, X12 : $i]:
% 0.47/0.63         (~ (l1_pre_topc @ X11)
% 0.47/0.63          | ~ (v2_pre_topc @ X11)
% 0.47/0.63          | (v2_struct_0 @ X11)
% 0.47/0.63          | ~ (m1_pre_topc @ X12 @ X11)
% 0.47/0.63          | (v1_pre_topc @ (k8_tmap_1 @ X11 @ X12)))),
% 0.47/0.63      inference('cnf', [status(esa)], [dt_k8_tmap_1])).
% 0.47/0.63  thf('142', plain,
% 0.47/0.63      (((v1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B_1))
% 0.47/0.63        | (v2_struct_0 @ sk_A)
% 0.47/0.63        | ~ (v2_pre_topc @ sk_A)
% 0.47/0.63        | ~ (l1_pre_topc @ sk_A))),
% 0.47/0.63      inference('sup-', [status(thm)], ['140', '141'])).
% 0.47/0.63  thf('143', plain, ((v2_pre_topc @ sk_A)),
% 0.47/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.63  thf('144', plain, ((l1_pre_topc @ sk_A)),
% 0.47/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.63  thf('145', plain,
% 0.47/0.63      (((v1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B_1)) | (v2_struct_0 @ sk_A))),
% 0.47/0.63      inference('demod', [status(thm)], ['142', '143', '144'])).
% 0.47/0.63  thf('146', plain, (~ (v2_struct_0 @ sk_A)),
% 0.47/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.63  thf('147', plain, ((v1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B_1))),
% 0.47/0.63      inference('clc', [status(thm)], ['145', '146'])).
% 0.47/0.63  thf('148', plain,
% 0.47/0.63      ((((k8_tmap_1 @ sk_A @ sk_B_1) = (k6_tmap_1 @ sk_A @ (sk_B @ sk_A))))
% 0.47/0.63         <= (((v1_tsep_1 @ sk_B_1 @ sk_A)))),
% 0.47/0.63      inference('demod', [status(thm)], ['78', '88', '131', '139', '147'])).
% 0.47/0.63  thf('149', plain,
% 0.47/0.63      (![X0 : $i]:
% 0.47/0.63         ((v2_struct_0 @ X0)
% 0.47/0.63          | ~ (v2_pre_topc @ X0)
% 0.47/0.63          | ~ (l1_pre_topc @ X0)
% 0.47/0.63          | ((k6_tmap_1 @ X0 @ (sk_B @ X0))
% 0.47/0.63              = (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 0.47/0.63      inference('simplify', [status(thm)], ['122'])).
% 0.47/0.63  thf('150', plain,
% 0.47/0.63      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.47/0.63          != (k8_tmap_1 @ sk_A @ sk_B_1)))
% 0.47/0.63         <= (~
% 0.47/0.63             (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.47/0.63                = (k8_tmap_1 @ sk_A @ sk_B_1))))),
% 0.47/0.63      inference('split', [status(esa)], ['5'])).
% 0.47/0.63  thf('151', plain,
% 0.47/0.63      (((((k6_tmap_1 @ sk_A @ (sk_B @ sk_A)) != (k8_tmap_1 @ sk_A @ sk_B_1))
% 0.47/0.63         | ~ (l1_pre_topc @ sk_A)
% 0.47/0.63         | ~ (v2_pre_topc @ sk_A)
% 0.47/0.63         | (v2_struct_0 @ sk_A)))
% 0.47/0.63         <= (~
% 0.47/0.63             (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.47/0.63                = (k8_tmap_1 @ sk_A @ sk_B_1))))),
% 0.47/0.63      inference('sup-', [status(thm)], ['149', '150'])).
% 0.47/0.63  thf('152', plain, ((l1_pre_topc @ sk_A)),
% 0.47/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.63  thf('153', plain, ((v2_pre_topc @ sk_A)),
% 0.47/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.63  thf('154', plain,
% 0.47/0.63      (((((k6_tmap_1 @ sk_A @ (sk_B @ sk_A)) != (k8_tmap_1 @ sk_A @ sk_B_1))
% 0.47/0.63         | (v2_struct_0 @ sk_A)))
% 0.47/0.63         <= (~
% 0.47/0.63             (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.47/0.63                = (k8_tmap_1 @ sk_A @ sk_B_1))))),
% 0.47/0.63      inference('demod', [status(thm)], ['151', '152', '153'])).
% 0.47/0.63  thf('155', plain, (~ (v2_struct_0 @ sk_A)),
% 0.47/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.63  thf('156', plain,
% 0.47/0.63      ((((k6_tmap_1 @ sk_A @ (sk_B @ sk_A)) != (k8_tmap_1 @ sk_A @ sk_B_1)))
% 0.47/0.63         <= (~
% 0.47/0.63             (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.47/0.63                = (k8_tmap_1 @ sk_A @ sk_B_1))))),
% 0.47/0.63      inference('clc', [status(thm)], ['154', '155'])).
% 0.47/0.63  thf('157', plain,
% 0.47/0.63      ((((k8_tmap_1 @ sk_A @ sk_B_1) != (k8_tmap_1 @ sk_A @ sk_B_1)))
% 0.47/0.63         <= (~
% 0.47/0.63             (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.47/0.63                = (k8_tmap_1 @ sk_A @ sk_B_1))) & 
% 0.47/0.63             ((v1_tsep_1 @ sk_B_1 @ sk_A)))),
% 0.47/0.63      inference('sup-', [status(thm)], ['148', '156'])).
% 0.47/0.63  thf('158', plain,
% 0.47/0.63      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.47/0.63          = (k8_tmap_1 @ sk_A @ sk_B_1))) | 
% 0.47/0.63       ~ ((v1_tsep_1 @ sk_B_1 @ sk_A))),
% 0.47/0.63      inference('simplify', [status(thm)], ['157'])).
% 0.47/0.63  thf('159', plain, (~ ((v1_tsep_1 @ sk_B_1 @ sk_A))),
% 0.47/0.63      inference('sat_resolution*', [status(thm)], ['31', '34', '158'])).
% 0.47/0.63  thf('160', plain,
% 0.47/0.63      (~ (r2_hidden @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_A))),
% 0.47/0.63      inference('simpl_trail', [status(thm)], ['30', '159'])).
% 0.47/0.63  thf('161', plain,
% 0.47/0.63      ((m1_subset_1 @ (u1_struct_0 @ sk_B_1) @ 
% 0.47/0.63        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.47/0.63      inference('demod', [status(thm)], ['37', '38'])).
% 0.47/0.63  thf('162', plain,
% 0.47/0.63      (![X13 : $i, X14 : $i]:
% 0.47/0.63         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.47/0.63          | ((u1_pre_topc @ X14) != (k5_tmap_1 @ X14 @ X13))
% 0.47/0.63          | (r2_hidden @ X13 @ (u1_pre_topc @ X14))
% 0.47/0.63          | ~ (l1_pre_topc @ X14)
% 0.47/0.63          | ~ (v2_pre_topc @ X14)
% 0.47/0.63          | (v2_struct_0 @ X14))),
% 0.47/0.63      inference('cnf', [status(esa)], [t103_tmap_1])).
% 0.47/0.63  thf('163', plain,
% 0.47/0.63      (((v2_struct_0 @ sk_A)
% 0.47/0.63        | ~ (v2_pre_topc @ sk_A)
% 0.47/0.63        | ~ (l1_pre_topc @ sk_A)
% 0.47/0.63        | (r2_hidden @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_A))
% 0.47/0.63        | ((u1_pre_topc @ sk_A) != (k5_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B_1))))),
% 0.47/0.63      inference('sup-', [status(thm)], ['161', '162'])).
% 0.47/0.63  thf('164', plain, ((v2_pre_topc @ sk_A)),
% 0.47/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.63  thf('165', plain, ((l1_pre_topc @ sk_A)),
% 0.47/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.63  thf('166', plain,
% 0.47/0.63      (((v2_struct_0 @ sk_A)
% 0.47/0.63        | (r2_hidden @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_A))
% 0.47/0.63        | ((u1_pre_topc @ sk_A) != (k5_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B_1))))),
% 0.47/0.63      inference('demod', [status(thm)], ['163', '164', '165'])).
% 0.47/0.63  thf('167', plain, (~ (v2_struct_0 @ sk_A)),
% 0.47/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.63  thf('168', plain,
% 0.47/0.63      ((((u1_pre_topc @ sk_A) != (k5_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B_1)))
% 0.47/0.63        | (r2_hidden @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_A)))),
% 0.47/0.63      inference('clc', [status(thm)], ['166', '167'])).
% 0.47/0.63  thf('169', plain,
% 0.47/0.63      (((u1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B_1))
% 0.47/0.63         = (k5_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B_1)))),
% 0.47/0.63      inference('clc', [status(thm)], ['48', '49'])).
% 0.47/0.63  thf('170', plain,
% 0.47/0.63      ((((u1_pre_topc @ sk_A) != (u1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B_1)))
% 0.47/0.63        | (r2_hidden @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_A)))),
% 0.47/0.63      inference('demod', [status(thm)], ['168', '169'])).
% 0.47/0.63  thf('171', plain,
% 0.47/0.63      (![X0 : $i]:
% 0.47/0.63         (((u1_pre_topc @ X0) = (k5_tmap_1 @ X0 @ (sk_B @ X0)))
% 0.47/0.63          | (v2_struct_0 @ X0)
% 0.47/0.63          | ~ (v2_pre_topc @ X0)
% 0.47/0.63          | ~ (l1_pre_topc @ X0))),
% 0.47/0.63      inference('simplify', [status(thm)], ['116'])).
% 0.47/0.63  thf('172', plain,
% 0.47/0.63      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.47/0.63          = (k8_tmap_1 @ sk_A @ sk_B_1)))
% 0.47/0.63         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.47/0.63                = (k8_tmap_1 @ sk_A @ sk_B_1))))),
% 0.47/0.63      inference('split', [status(esa)], ['51'])).
% 0.47/0.63  thf('173', plain,
% 0.47/0.63      (![X0 : $i]:
% 0.47/0.63         ((v2_struct_0 @ X0)
% 0.47/0.63          | ~ (v2_pre_topc @ X0)
% 0.47/0.63          | ~ (l1_pre_topc @ X0)
% 0.47/0.63          | ((k6_tmap_1 @ X0 @ (sk_B @ X0))
% 0.47/0.63              = (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 0.47/0.63      inference('simplify', [status(thm)], ['122'])).
% 0.47/0.63  thf('174', plain,
% 0.47/0.63      (((((k6_tmap_1 @ sk_A @ (sk_B @ sk_A)) = (k8_tmap_1 @ sk_A @ sk_B_1))
% 0.47/0.63         | ~ (l1_pre_topc @ sk_A)
% 0.47/0.63         | ~ (v2_pre_topc @ sk_A)
% 0.47/0.63         | (v2_struct_0 @ sk_A)))
% 0.47/0.63         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.47/0.63                = (k8_tmap_1 @ sk_A @ sk_B_1))))),
% 0.47/0.63      inference('sup+', [status(thm)], ['172', '173'])).
% 0.47/0.63  thf('175', plain, ((l1_pre_topc @ sk_A)),
% 0.47/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.63  thf('176', plain, ((v2_pre_topc @ sk_A)),
% 0.47/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.63  thf('177', plain,
% 0.47/0.63      (((((k6_tmap_1 @ sk_A @ (sk_B @ sk_A)) = (k8_tmap_1 @ sk_A @ sk_B_1))
% 0.47/0.63         | (v2_struct_0 @ sk_A)))
% 0.47/0.63         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.47/0.63                = (k8_tmap_1 @ sk_A @ sk_B_1))))),
% 0.47/0.63      inference('demod', [status(thm)], ['174', '175', '176'])).
% 0.47/0.63  thf('178', plain, (~ (v2_struct_0 @ sk_A)),
% 0.47/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.63  thf('179', plain,
% 0.47/0.63      ((((k6_tmap_1 @ sk_A @ (sk_B @ sk_A)) = (k8_tmap_1 @ sk_A @ sk_B_1)))
% 0.47/0.63         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.47/0.63                = (k8_tmap_1 @ sk_A @ sk_B_1))))),
% 0.47/0.63      inference('clc', [status(thm)], ['177', '178'])).
% 0.47/0.63  thf('180', plain,
% 0.47/0.63      (![X5 : $i]:
% 0.47/0.63         ((m1_subset_1 @ (sk_B @ X5) @ (k1_zfmisc_1 @ (u1_struct_0 @ X5)))
% 0.47/0.63          | ~ (l1_pre_topc @ X5))),
% 0.47/0.63      inference('cnf', [status(esa)], [rc1_connsp_1])).
% 0.47/0.63  thf(t104_tmap_1, axiom,
% 0.47/0.63    (![A:$i]:
% 0.47/0.63     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.47/0.63       ( ![B:$i]:
% 0.47/0.63         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.47/0.63           ( ( ( u1_struct_0 @ ( k6_tmap_1 @ A @ B ) ) = ( u1_struct_0 @ A ) ) & 
% 0.47/0.63             ( ( u1_pre_topc @ ( k6_tmap_1 @ A @ B ) ) = ( k5_tmap_1 @ A @ B ) ) ) ) ) ))).
% 0.47/0.63  thf('181', plain,
% 0.47/0.63      (![X15 : $i, X16 : $i]:
% 0.47/0.63         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.47/0.63          | ((u1_pre_topc @ (k6_tmap_1 @ X16 @ X15)) = (k5_tmap_1 @ X16 @ X15))
% 0.47/0.63          | ~ (l1_pre_topc @ X16)
% 0.47/0.63          | ~ (v2_pre_topc @ X16)
% 0.47/0.63          | (v2_struct_0 @ X16))),
% 0.47/0.63      inference('cnf', [status(esa)], [t104_tmap_1])).
% 0.47/0.63  thf('182', plain,
% 0.47/0.63      (![X0 : $i]:
% 0.47/0.63         (~ (l1_pre_topc @ X0)
% 0.47/0.63          | (v2_struct_0 @ X0)
% 0.47/0.63          | ~ (v2_pre_topc @ X0)
% 0.47/0.63          | ~ (l1_pre_topc @ X0)
% 0.47/0.63          | ((u1_pre_topc @ (k6_tmap_1 @ X0 @ (sk_B @ X0)))
% 0.47/0.63              = (k5_tmap_1 @ X0 @ (sk_B @ X0))))),
% 0.47/0.63      inference('sup-', [status(thm)], ['180', '181'])).
% 0.47/0.63  thf('183', plain,
% 0.47/0.63      (![X0 : $i]:
% 0.47/0.63         (((u1_pre_topc @ (k6_tmap_1 @ X0 @ (sk_B @ X0)))
% 0.47/0.63            = (k5_tmap_1 @ X0 @ (sk_B @ X0)))
% 0.47/0.63          | ~ (v2_pre_topc @ X0)
% 0.47/0.63          | (v2_struct_0 @ X0)
% 0.47/0.63          | ~ (l1_pre_topc @ X0))),
% 0.47/0.63      inference('simplify', [status(thm)], ['182'])).
% 0.47/0.63  thf('184', plain,
% 0.47/0.63      (((((u1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B_1))
% 0.47/0.63           = (k5_tmap_1 @ sk_A @ (sk_B @ sk_A)))
% 0.47/0.63         | ~ (l1_pre_topc @ sk_A)
% 0.47/0.63         | (v2_struct_0 @ sk_A)
% 0.47/0.63         | ~ (v2_pre_topc @ sk_A)))
% 0.47/0.63         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.47/0.63                = (k8_tmap_1 @ sk_A @ sk_B_1))))),
% 0.47/0.63      inference('sup+', [status(thm)], ['179', '183'])).
% 0.47/0.63  thf('185', plain, ((l1_pre_topc @ sk_A)),
% 0.47/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.63  thf('186', plain, ((v2_pre_topc @ sk_A)),
% 0.47/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.63  thf('187', plain,
% 0.47/0.63      (((((u1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B_1))
% 0.47/0.63           = (k5_tmap_1 @ sk_A @ (sk_B @ sk_A)))
% 0.47/0.63         | (v2_struct_0 @ sk_A)))
% 0.47/0.63         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.47/0.63                = (k8_tmap_1 @ sk_A @ sk_B_1))))),
% 0.47/0.63      inference('demod', [status(thm)], ['184', '185', '186'])).
% 0.47/0.63  thf('188', plain, (~ (v2_struct_0 @ sk_A)),
% 0.47/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.63  thf('189', plain,
% 0.47/0.63      ((((u1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B_1))
% 0.47/0.63          = (k5_tmap_1 @ sk_A @ (sk_B @ sk_A))))
% 0.47/0.63         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.47/0.63                = (k8_tmap_1 @ sk_A @ sk_B_1))))),
% 0.47/0.63      inference('clc', [status(thm)], ['187', '188'])).
% 0.47/0.63  thf('190', plain,
% 0.47/0.63      (((((u1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B_1)) = (u1_pre_topc @ sk_A))
% 0.47/0.63         | ~ (l1_pre_topc @ sk_A)
% 0.47/0.63         | ~ (v2_pre_topc @ sk_A)
% 0.47/0.63         | (v2_struct_0 @ sk_A)))
% 0.47/0.63         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.47/0.63                = (k8_tmap_1 @ sk_A @ sk_B_1))))),
% 0.47/0.63      inference('sup+', [status(thm)], ['171', '189'])).
% 0.47/0.63  thf('191', plain, ((l1_pre_topc @ sk_A)),
% 0.47/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.63  thf('192', plain, ((v2_pre_topc @ sk_A)),
% 0.47/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.63  thf('193', plain,
% 0.47/0.63      (((((u1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B_1)) = (u1_pre_topc @ sk_A))
% 0.47/0.63         | (v2_struct_0 @ sk_A)))
% 0.47/0.63         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.47/0.63                = (k8_tmap_1 @ sk_A @ sk_B_1))))),
% 0.47/0.63      inference('demod', [status(thm)], ['190', '191', '192'])).
% 0.47/0.63  thf('194', plain, (~ (v2_struct_0 @ sk_A)),
% 0.47/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.63  thf('195', plain,
% 0.47/0.63      ((((u1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B_1)) = (u1_pre_topc @ sk_A)))
% 0.47/0.63         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.47/0.63                = (k8_tmap_1 @ sk_A @ sk_B_1))))),
% 0.47/0.63      inference('clc', [status(thm)], ['193', '194'])).
% 0.47/0.63  thf('196', plain,
% 0.47/0.63      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.47/0.63          = (k8_tmap_1 @ sk_A @ sk_B_1))) | 
% 0.47/0.63       ((v1_tsep_1 @ sk_B_1 @ sk_A))),
% 0.47/0.63      inference('split', [status(esa)], ['51'])).
% 0.47/0.63  thf('197', plain,
% 0.47/0.63      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.47/0.63          = (k8_tmap_1 @ sk_A @ sk_B_1)))),
% 0.47/0.63      inference('sat_resolution*', [status(thm)], ['31', '34', '158', '196'])).
% 0.47/0.63  thf('198', plain,
% 0.47/0.63      (((u1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B_1)) = (u1_pre_topc @ sk_A))),
% 0.47/0.63      inference('simpl_trail', [status(thm)], ['195', '197'])).
% 0.47/0.63  thf('199', plain,
% 0.47/0.63      ((((u1_pre_topc @ sk_A) != (u1_pre_topc @ sk_A))
% 0.47/0.63        | (r2_hidden @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_A)))),
% 0.47/0.63      inference('demod', [status(thm)], ['170', '198'])).
% 0.47/0.63  thf('200', plain,
% 0.47/0.63      ((r2_hidden @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_A))),
% 0.47/0.63      inference('simplify', [status(thm)], ['199'])).
% 0.47/0.63  thf('201', plain, ($false), inference('demod', [status(thm)], ['160', '200'])).
% 0.47/0.63  
% 0.47/0.63  % SZS output end Refutation
% 0.47/0.63  
% 0.47/0.64  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
