%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.evsnmEwCfZ

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:10:47 EST 2020

% Result     : Theorem 0.47s
% Output     : Refutation 0.47s
% Verified   : 
% Statistics : Number of formulae       :  182 (1032 expanded)
%              Number of leaves         :   27 ( 299 expanded)
%              Depth                    :   25
%              Number of atoms          : 1795 (15697 expanded)
%              Number of equality atoms :   76 ( 665 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k5_tmap_1_type,type,(
    k5_tmap_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k6_tmap_1_type,type,(
    k6_tmap_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_tops_2_type,type,(
    v1_tops_2: $i > $i > $o )).

thf(g1_pre_topc_type,type,(
    g1_pre_topc: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(t106_tmap_1,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v3_pre_topc @ B @ A )
          <=> ( ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) )
              = ( k6_tmap_1 @ A @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( ( v3_pre_topc @ B @ A )
            <=> ( ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) )
                = ( k6_tmap_1 @ A @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t106_tmap_1])).

thf('0',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d9_tmap_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k6_tmap_1 @ A @ B )
            = ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( k5_tmap_1 @ A @ B ) ) ) ) ) )).

thf('1',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ( ( k6_tmap_1 @ X18 @ X17 )
        = ( g1_pre_topc @ ( u1_struct_0 @ X18 ) @ ( k5_tmap_1 @ X18 @ X17 ) ) )
      | ~ ( l1_pre_topc @ X18 )
      | ~ ( v2_pre_topc @ X18 )
      | ( v2_struct_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d9_tmap_1])).

thf('2',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( ( k6_tmap_1 @ sk_A @ sk_B )
      = ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( k5_tmap_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k6_tmap_1 @ sk_A @ sk_B )
      = ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( k5_tmap_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['2','3','4'])).

thf('6',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( k6_tmap_1 @ sk_A @ sk_B )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( k5_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['5','6'])).

thf('8',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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

thf('9',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ~ ( r2_hidden @ X23 @ ( u1_pre_topc @ X24 ) )
      | ( ( u1_pre_topc @ X24 )
        = ( k5_tmap_1 @ X24 @ X23 ) )
      | ~ ( l1_pre_topc @ X24 )
      | ~ ( v2_pre_topc @ X24 )
      | ( v2_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t103_tmap_1])).

thf('10',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( ( u1_pre_topc @ sk_A )
      = ( k5_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( r2_hidden @ sk_B @ ( u1_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,
    ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) )
    | ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ( v3_pre_topc @ sk_B @ sk_A )
   <= ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['13'])).

thf('15',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v3_pre_topc @ B @ A )
          <=> ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) ) ) ) )).

thf('16',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) )
      | ~ ( v3_pre_topc @ X6 @ X7 )
      | ( r2_hidden @ X6 @ ( u1_pre_topc @ X7 ) )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[d5_pre_topc])).

thf('17',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r2_hidden @ sk_B @ ( u1_pre_topc @ sk_A ) )
    | ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( r2_hidden @ sk_B @ ( u1_pre_topc @ sk_A ) )
    | ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,
    ( ( r2_hidden @ sk_B @ ( u1_pre_topc @ sk_A ) )
   <= ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['14','19'])).

thf('21',plain,
    ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
     != ( k6_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,
    ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
     != ( k6_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['21'])).

thf('23',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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

thf('24',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) )
      | ( ( u1_pre_topc @ ( k6_tmap_1 @ X26 @ X25 ) )
        = ( k5_tmap_1 @ X26 @ X25 ) )
      | ~ ( l1_pre_topc @ X26 )
      | ~ ( v2_pre_topc @ X26 )
      | ( v2_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t104_tmap_1])).

thf('25',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( ( u1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) )
      = ( k5_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( u1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) )
      = ( k5_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['25','26','27'])).

thf('29',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ( u1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) )
    = ( k5_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['28','29'])).

thf(dt_u1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( m1_subset_1 @ ( u1_pre_topc @ A ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('31',plain,(
    ! [X8: $i] :
      ( ( m1_subset_1 @ ( u1_pre_topc @ X8 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) ) )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_pre_topc])).

thf('32',plain,
    ( ( m1_subset_1 @ ( k5_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ) ) )
    | ~ ( l1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k6_tmap_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( ( v1_pre_topc @ ( k6_tmap_1 @ A @ B ) )
        & ( v2_pre_topc @ ( k6_tmap_1 @ A @ B ) )
        & ( l1_pre_topc @ ( k6_tmap_1 @ A @ B ) ) ) ) )).

thf('34',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( l1_pre_topc @ X19 )
      | ~ ( v2_pre_topc @ X19 )
      | ( v2_struct_0 @ X19 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ( l1_pre_topc @ ( k6_tmap_1 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_tmap_1])).

thf('35',plain,
    ( ( l1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ( l1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['35','36','37'])).

thf('39',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    l1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['38','39'])).

thf('41',plain,(
    m1_subset_1 @ ( k5_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['32','40'])).

thf('42',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) )
      | ( ( u1_struct_0 @ ( k6_tmap_1 @ X26 @ X25 ) )
        = ( u1_struct_0 @ X26 ) )
      | ~ ( l1_pre_topc @ X26 )
      | ~ ( v2_pre_topc @ X26 )
      | ( v2_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t104_tmap_1])).

thf('44',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['44','45','46'])).

thf('48',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['47','48'])).

thf('50',plain,(
    m1_subset_1 @ ( k5_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['41','49'])).

thf('51',plain,
    ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['13'])).

thf(t32_compts_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ( v1_tops_2 @ B @ A )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )
        <=> ( ( v1_tops_2 @ B @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ) ) ) ) ) )).

thf('52',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( v1_tops_2 @ X14 @ ( g1_pre_topc @ ( u1_struct_0 @ X15 ) @ ( u1_pre_topc @ X15 ) ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X15 ) @ ( u1_pre_topc @ X15 ) ) ) ) ) )
      | ( v1_tops_2 @ X14 @ X15 )
      | ~ ( l1_pre_topc @ X15 )
      | ~ ( v2_pre_topc @ X15 )
      | ( v2_struct_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t32_compts_1])).

thf('53',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ) ) )
        | ( v2_struct_0 @ sk_A )
        | ~ ( v2_pre_topc @ sk_A )
        | ~ ( l1_pre_topc @ sk_A )
        | ( v1_tops_2 @ X0 @ sk_A )
        | ~ ( v1_tops_2 @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,
    ( ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['47','48'])).

thf('55',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,
    ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['13'])).

thf('58',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
        | ( v2_struct_0 @ sk_A )
        | ( v1_tops_2 @ X0 @ sk_A )
        | ~ ( v1_tops_2 @ X0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['53','54','55','56','57'])).

thf('59',plain,
    ( ( ~ ( v1_tops_2 @ ( k5_tmap_1 @ sk_A @ sk_B ) @ ( k6_tmap_1 @ sk_A @ sk_B ) )
      | ( v1_tops_2 @ ( k5_tmap_1 @ sk_A @ sk_B ) @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['50','58'])).

thf('60',plain,(
    m1_subset_1 @ ( k5_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['32','40'])).

thf(t78_tops_2,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
         => ( ( v1_tops_2 @ B @ A )
          <=> ( r1_tarski @ B @ ( u1_pre_topc @ A ) ) ) ) ) )).

thf('61',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) ) )
      | ~ ( r1_tarski @ X12 @ ( u1_pre_topc @ X13 ) )
      | ( v1_tops_2 @ X12 @ X13 )
      | ~ ( l1_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[t78_tops_2])).

thf('62',plain,
    ( ~ ( l1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) )
    | ( v1_tops_2 @ ( k5_tmap_1 @ sk_A @ sk_B ) @ ( k6_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( r1_tarski @ ( k5_tmap_1 @ sk_A @ sk_B ) @ ( u1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    l1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['38','39'])).

thf('64',plain,
    ( ( u1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) )
    = ( k5_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['28','29'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('66',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['65'])).

thf('67',plain,(
    v1_tops_2 @ ( k5_tmap_1 @ sk_A @ sk_B ) @ ( k6_tmap_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['62','63','64','66'])).

thf('68',plain,
    ( ( ( v1_tops_2 @ ( k5_tmap_1 @ sk_A @ sk_B ) @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['59','67'])).

thf('69',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,
    ( ( v1_tops_2 @ ( k5_tmap_1 @ sk_A @ sk_B ) @ sk_A )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['68','69'])).

thf('71',plain,(
    m1_subset_1 @ ( k5_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['41','49'])).

thf('72',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) ) )
      | ~ ( v1_tops_2 @ X12 @ X13 )
      | ( r1_tarski @ X12 @ ( u1_pre_topc @ X13 ) )
      | ~ ( l1_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[t78_tops_2])).

thf('73',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ ( k5_tmap_1 @ sk_A @ sk_B ) @ ( u1_pre_topc @ sk_A ) )
    | ~ ( v1_tops_2 @ ( k5_tmap_1 @ sk_A @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,
    ( ( r1_tarski @ ( k5_tmap_1 @ sk_A @ sk_B ) @ ( u1_pre_topc @ sk_A ) )
    | ~ ( v1_tops_2 @ ( k5_tmap_1 @ sk_A @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('76',plain,
    ( ( r1_tarski @ ( k5_tmap_1 @ sk_A @ sk_B ) @ ( u1_pre_topc @ sk_A ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['70','75'])).

thf('77',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('78',plain,
    ( ( ~ ( r1_tarski @ ( u1_pre_topc @ sk_A ) @ ( k5_tmap_1 @ sk_A @ sk_B ) )
      | ( ( u1_pre_topc @ sk_A )
        = ( k5_tmap_1 @ sk_A @ sk_B ) ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,
    ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['13'])).

thf('80',plain,(
    ! [X8: $i] :
      ( ( m1_subset_1 @ ( u1_pre_topc @ X8 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) ) )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_pre_topc])).

thf('81',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) ) )
      | ~ ( r1_tarski @ X12 @ ( u1_pre_topc @ X13 ) )
      | ( v1_tops_2 @ X12 @ X13 )
      | ~ ( l1_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[t78_tops_2])).

thf('82',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v1_tops_2 @ ( u1_pre_topc @ X0 ) @ X0 )
      | ~ ( r1_tarski @ ( u1_pre_topc @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['65'])).

thf('84',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v1_tops_2 @ ( u1_pre_topc @ X0 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['82','83'])).

thf('85',plain,(
    ! [X0: $i] :
      ( ( v1_tops_2 @ ( u1_pre_topc @ X0 ) @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['84'])).

thf('86',plain,(
    ! [X8: $i] :
      ( ( m1_subset_1 @ ( u1_pre_topc @ X8 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) ) )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_pre_topc])).

thf('87',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( v1_tops_2 @ X16 @ X15 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) ) )
      | ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X15 ) @ ( u1_pre_topc @ X15 ) ) ) ) ) )
      | ~ ( l1_pre_topc @ X15 )
      | ~ ( v2_pre_topc @ X15 )
      | ( v2_struct_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t32_compts_1])).

thf('88',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_subset_1 @ ( u1_pre_topc @ X0 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ) )
      | ~ ( v1_tops_2 @ ( u1_pre_topc @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X0: $i] :
      ( ~ ( v1_tops_2 @ ( u1_pre_topc @ X0 ) @ X0 )
      | ( m1_subset_1 @ ( u1_pre_topc @ X0 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ) )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['88'])).

thf('90',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( m1_subset_1 @ ( u1_pre_topc @ X0 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['85','89'])).

thf('91',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( u1_pre_topc @ X0 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ) )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['90'])).

thf('92',plain,
    ( ( ( m1_subset_1 @ ( u1_pre_topc @ sk_A ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ) ) )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['79','91'])).

thf('93',plain,
    ( ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['47','48'])).

thf('94',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,
    ( ( ( m1_subset_1 @ ( u1_pre_topc @ sk_A ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['92','93','94','95'])).

thf('97',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,
    ( ( m1_subset_1 @ ( u1_pre_topc @ sk_A ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['96','97'])).

thf('99',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( v1_tops_2 @ X16 @ X15 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) ) )
      | ( v1_tops_2 @ X16 @ ( g1_pre_topc @ ( u1_struct_0 @ X15 ) @ ( u1_pre_topc @ X15 ) ) )
      | ~ ( l1_pre_topc @ X15 )
      | ~ ( v2_pre_topc @ X15 )
      | ( v2_struct_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t32_compts_1])).

thf('100',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v1_tops_2 @ ( u1_pre_topc @ sk_A ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      | ~ ( v1_tops_2 @ ( u1_pre_topc @ sk_A ) @ sk_A ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,
    ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['13'])).

thf('104',plain,
    ( ( m1_subset_1 @ ( u1_pre_topc @ sk_A ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['96','97'])).

thf('105',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) ) )
      | ~ ( r1_tarski @ X12 @ ( u1_pre_topc @ X13 ) )
      | ( v1_tops_2 @ X12 @ X13 )
      | ~ ( l1_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[t78_tops_2])).

thf('106',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ( v1_tops_2 @ ( u1_pre_topc @ sk_A ) @ sk_A )
      | ~ ( r1_tarski @ ( u1_pre_topc @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['104','105'])).

thf('107',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['65'])).

thf('109',plain,
    ( ( v1_tops_2 @ ( u1_pre_topc @ sk_A ) @ sk_A )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['106','107','108'])).

thf('110',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_tops_2 @ ( u1_pre_topc @ sk_A ) @ ( k6_tmap_1 @ sk_A @ sk_B ) ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['100','101','102','103','109'])).

thf('111',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,
    ( ( v1_tops_2 @ ( u1_pre_topc @ sk_A ) @ ( k6_tmap_1 @ sk_A @ sk_B ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['110','111'])).

thf('113',plain,(
    ! [X8: $i] :
      ( ( m1_subset_1 @ ( u1_pre_topc @ X8 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) ) )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_pre_topc])).

thf('114',plain,
    ( ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['47','48'])).

thf('115',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) ) )
      | ~ ( v1_tops_2 @ X12 @ X13 )
      | ( r1_tarski @ X12 @ ( u1_pre_topc @ X13 ) )
      | ~ ( l1_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[t78_tops_2])).

thf('116',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
      | ~ ( l1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) )
      | ( r1_tarski @ X0 @ ( u1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) ) )
      | ~ ( v1_tops_2 @ X0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['114','115'])).

thf('117',plain,(
    l1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['38','39'])).

thf('118',plain,
    ( ( u1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) )
    = ( k5_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['28','29'])).

thf('119',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
      | ( r1_tarski @ X0 @ ( k5_tmap_1 @ sk_A @ sk_B ) )
      | ~ ( v1_tops_2 @ X0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['116','117','118'])).

thf('120',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v1_tops_2 @ ( u1_pre_topc @ sk_A ) @ ( k6_tmap_1 @ sk_A @ sk_B ) )
    | ( r1_tarski @ ( u1_pre_topc @ sk_A ) @ ( k5_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['113','119'])).

thf('121',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,
    ( ~ ( v1_tops_2 @ ( u1_pre_topc @ sk_A ) @ ( k6_tmap_1 @ sk_A @ sk_B ) )
    | ( r1_tarski @ ( u1_pre_topc @ sk_A ) @ ( k5_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['120','121'])).

thf('123',plain,
    ( ( r1_tarski @ ( u1_pre_topc @ sk_A ) @ ( k5_tmap_1 @ sk_A @ sk_B ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['112','122'])).

thf('124',plain,
    ( ( ( u1_pre_topc @ sk_A )
      = ( k5_tmap_1 @ sk_A @ sk_B ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['78','123'])).

thf('125',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ( ( u1_pre_topc @ X24 )
       != ( k5_tmap_1 @ X24 @ X23 ) )
      | ( r2_hidden @ X23 @ ( u1_pre_topc @ X24 ) )
      | ~ ( l1_pre_topc @ X24 )
      | ~ ( v2_pre_topc @ X24 )
      | ( v2_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t103_tmap_1])).

thf('127',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( r2_hidden @ sk_B @ ( u1_pre_topc @ sk_A ) )
    | ( ( u1_pre_topc @ sk_A )
     != ( k5_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['125','126'])).

thf('128',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('129',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('130',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ sk_B @ ( u1_pre_topc @ sk_A ) )
    | ( ( u1_pre_topc @ sk_A )
     != ( k5_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['127','128','129'])).

thf('131',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('132',plain,
    ( ( ( u1_pre_topc @ sk_A )
     != ( k5_tmap_1 @ sk_A @ sk_B ) )
    | ( r2_hidden @ sk_B @ ( u1_pre_topc @ sk_A ) ) ),
    inference(clc,[status(thm)],['130','131'])).

thf('133',plain,
    ( ( ( ( u1_pre_topc @ sk_A )
       != ( u1_pre_topc @ sk_A ) )
      | ( r2_hidden @ sk_B @ ( u1_pre_topc @ sk_A ) ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['124','132'])).

thf('134',plain,
    ( ( r2_hidden @ sk_B @ ( u1_pre_topc @ sk_A ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['133'])).

thf('135',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('136',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) )
      | ~ ( r2_hidden @ X6 @ ( u1_pre_topc @ X7 ) )
      | ( v3_pre_topc @ X6 @ X7 )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[d5_pre_topc])).

thf('137',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v3_pre_topc @ sk_B @ sk_A )
    | ~ ( r2_hidden @ sk_B @ ( u1_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['135','136'])).

thf('138',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('139',plain,
    ( ( v3_pre_topc @ sk_B @ sk_A )
    | ~ ( r2_hidden @ sk_B @ ( u1_pre_topc @ sk_A ) ) ),
    inference(demod,[status(thm)],['137','138'])).

thf('140',plain,
    ( ( v3_pre_topc @ sk_B @ sk_A )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['134','139'])).

thf('141',plain,
    ( ~ ( v3_pre_topc @ sk_B @ sk_A )
   <= ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['21'])).

thf('142',plain,
    ( ( v3_pre_topc @ sk_B @ sk_A )
    | ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
     != ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['140','141'])).

thf('143',plain,
    ( ( v3_pre_topc @ sk_B @ sk_A )
    | ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['13'])).

thf('144',plain,(
    v3_pre_topc @ sk_B @ sk_A ),
    inference('sat_resolution*',[status(thm)],['22','142','143'])).

thf('145',plain,(
    r2_hidden @ sk_B @ ( u1_pre_topc @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['20','144'])).

thf('146',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( u1_pre_topc @ sk_A )
      = ( k5_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['10','11','12','145'])).

thf('147',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('148',plain,
    ( ( u1_pre_topc @ sk_A )
    = ( k5_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['146','147'])).

thf('149',plain,
    ( ( k6_tmap_1 @ sk_A @ sk_B )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ),
    inference(demod,[status(thm)],['7','148'])).

thf('150',plain,
    ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
     != ( k6_tmap_1 @ sk_A @ sk_B ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
     != ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['21'])).

thf('151',plain,(
    ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
 != ( k6_tmap_1 @ sk_A @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['22','142'])).

thf('152',plain,(
    ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
 != ( k6_tmap_1 @ sk_A @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['150','151'])).

thf('153',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['149','152'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.evsnmEwCfZ
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 14:49:41 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.47/0.65  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.47/0.65  % Solved by: fo/fo7.sh
% 0.47/0.65  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.47/0.65  % done 221 iterations in 0.188s
% 0.47/0.65  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.47/0.65  % SZS output start Refutation
% 0.47/0.65  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 0.47/0.65  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.47/0.65  thf(k5_tmap_1_type, type, k5_tmap_1: $i > $i > $i).
% 0.47/0.65  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.47/0.65  thf(sk_A_type, type, sk_A: $i).
% 0.47/0.65  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.47/0.65  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.47/0.65  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.47/0.65  thf(k6_tmap_1_type, type, k6_tmap_1: $i > $i > $i).
% 0.47/0.65  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.47/0.65  thf(sk_B_type, type, sk_B: $i).
% 0.47/0.65  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.47/0.65  thf(v1_tops_2_type, type, v1_tops_2: $i > $i > $o).
% 0.47/0.65  thf(g1_pre_topc_type, type, g1_pre_topc: $i > $i > $i).
% 0.47/0.65  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.47/0.65  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.47/0.65  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 0.47/0.65  thf(t106_tmap_1, conjecture,
% 0.47/0.65    (![A:$i]:
% 0.47/0.65     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.47/0.65       ( ![B:$i]:
% 0.47/0.65         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.47/0.65           ( ( v3_pre_topc @ B @ A ) <=>
% 0.47/0.65             ( ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) =
% 0.47/0.65               ( k6_tmap_1 @ A @ B ) ) ) ) ) ))).
% 0.47/0.65  thf(zf_stmt_0, negated_conjecture,
% 0.47/0.65    (~( ![A:$i]:
% 0.47/0.65        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.47/0.65            ( l1_pre_topc @ A ) ) =>
% 0.47/0.65          ( ![B:$i]:
% 0.47/0.65            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.47/0.65              ( ( v3_pre_topc @ B @ A ) <=>
% 0.47/0.65                ( ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) =
% 0.47/0.65                  ( k6_tmap_1 @ A @ B ) ) ) ) ) ) )),
% 0.47/0.65    inference('cnf.neg', [status(esa)], [t106_tmap_1])).
% 0.47/0.65  thf('0', plain,
% 0.47/0.65      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf(d9_tmap_1, axiom,
% 0.47/0.65    (![A:$i]:
% 0.47/0.65     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.47/0.65       ( ![B:$i]:
% 0.47/0.65         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.47/0.65           ( ( k6_tmap_1 @ A @ B ) =
% 0.47/0.65             ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( k5_tmap_1 @ A @ B ) ) ) ) ) ))).
% 0.47/0.65  thf('1', plain,
% 0.47/0.65      (![X17 : $i, X18 : $i]:
% 0.47/0.65         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.47/0.65          | ((k6_tmap_1 @ X18 @ X17)
% 0.47/0.65              = (g1_pre_topc @ (u1_struct_0 @ X18) @ (k5_tmap_1 @ X18 @ X17)))
% 0.47/0.65          | ~ (l1_pre_topc @ X18)
% 0.47/0.65          | ~ (v2_pre_topc @ X18)
% 0.47/0.65          | (v2_struct_0 @ X18))),
% 0.47/0.65      inference('cnf', [status(esa)], [d9_tmap_1])).
% 0.47/0.65  thf('2', plain,
% 0.47/0.65      (((v2_struct_0 @ sk_A)
% 0.47/0.65        | ~ (v2_pre_topc @ sk_A)
% 0.47/0.65        | ~ (l1_pre_topc @ sk_A)
% 0.47/0.65        | ((k6_tmap_1 @ sk_A @ sk_B)
% 0.47/0.65            = (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (k5_tmap_1 @ sk_A @ sk_B))))),
% 0.47/0.65      inference('sup-', [status(thm)], ['0', '1'])).
% 0.47/0.65  thf('3', plain, ((v2_pre_topc @ sk_A)),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('4', plain, ((l1_pre_topc @ sk_A)),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('5', plain,
% 0.47/0.65      (((v2_struct_0 @ sk_A)
% 0.47/0.65        | ((k6_tmap_1 @ sk_A @ sk_B)
% 0.47/0.65            = (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (k5_tmap_1 @ sk_A @ sk_B))))),
% 0.47/0.65      inference('demod', [status(thm)], ['2', '3', '4'])).
% 0.47/0.65  thf('6', plain, (~ (v2_struct_0 @ sk_A)),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('7', plain,
% 0.47/0.65      (((k6_tmap_1 @ sk_A @ sk_B)
% 0.47/0.65         = (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (k5_tmap_1 @ sk_A @ sk_B)))),
% 0.47/0.65      inference('clc', [status(thm)], ['5', '6'])).
% 0.47/0.65  thf('8', plain,
% 0.47/0.65      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf(t103_tmap_1, axiom,
% 0.47/0.65    (![A:$i]:
% 0.47/0.65     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.47/0.65       ( ![B:$i]:
% 0.47/0.65         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.47/0.65           ( ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) <=>
% 0.47/0.65             ( ( u1_pre_topc @ A ) = ( k5_tmap_1 @ A @ B ) ) ) ) ) ))).
% 0.47/0.65  thf('9', plain,
% 0.47/0.65      (![X23 : $i, X24 : $i]:
% 0.47/0.65         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 0.47/0.65          | ~ (r2_hidden @ X23 @ (u1_pre_topc @ X24))
% 0.47/0.65          | ((u1_pre_topc @ X24) = (k5_tmap_1 @ X24 @ X23))
% 0.47/0.65          | ~ (l1_pre_topc @ X24)
% 0.47/0.65          | ~ (v2_pre_topc @ X24)
% 0.47/0.65          | (v2_struct_0 @ X24))),
% 0.47/0.65      inference('cnf', [status(esa)], [t103_tmap_1])).
% 0.47/0.65  thf('10', plain,
% 0.47/0.65      (((v2_struct_0 @ sk_A)
% 0.47/0.65        | ~ (v2_pre_topc @ sk_A)
% 0.47/0.65        | ~ (l1_pre_topc @ sk_A)
% 0.47/0.65        | ((u1_pre_topc @ sk_A) = (k5_tmap_1 @ sk_A @ sk_B))
% 0.47/0.65        | ~ (r2_hidden @ sk_B @ (u1_pre_topc @ sk_A)))),
% 0.47/0.65      inference('sup-', [status(thm)], ['8', '9'])).
% 0.47/0.65  thf('11', plain, ((v2_pre_topc @ sk_A)),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('12', plain, ((l1_pre_topc @ sk_A)),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('13', plain,
% 0.47/0.65      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.47/0.65          = (k6_tmap_1 @ sk_A @ sk_B))
% 0.47/0.65        | (v3_pre_topc @ sk_B @ sk_A))),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('14', plain,
% 0.47/0.65      (((v3_pre_topc @ sk_B @ sk_A)) <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 0.47/0.65      inference('split', [status(esa)], ['13'])).
% 0.47/0.65  thf('15', plain,
% 0.47/0.65      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf(d5_pre_topc, axiom,
% 0.47/0.65    (![A:$i]:
% 0.47/0.65     ( ( l1_pre_topc @ A ) =>
% 0.47/0.65       ( ![B:$i]:
% 0.47/0.65         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.47/0.65           ( ( v3_pre_topc @ B @ A ) <=>
% 0.47/0.65             ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) ) ) ) ))).
% 0.47/0.65  thf('16', plain,
% 0.47/0.65      (![X6 : $i, X7 : $i]:
% 0.47/0.65         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (u1_struct_0 @ X7)))
% 0.47/0.65          | ~ (v3_pre_topc @ X6 @ X7)
% 0.47/0.65          | (r2_hidden @ X6 @ (u1_pre_topc @ X7))
% 0.47/0.65          | ~ (l1_pre_topc @ X7))),
% 0.47/0.65      inference('cnf', [status(esa)], [d5_pre_topc])).
% 0.47/0.65  thf('17', plain,
% 0.47/0.65      ((~ (l1_pre_topc @ sk_A)
% 0.47/0.65        | (r2_hidden @ sk_B @ (u1_pre_topc @ sk_A))
% 0.47/0.65        | ~ (v3_pre_topc @ sk_B @ sk_A))),
% 0.47/0.65      inference('sup-', [status(thm)], ['15', '16'])).
% 0.47/0.65  thf('18', plain, ((l1_pre_topc @ sk_A)),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('19', plain,
% 0.47/0.65      (((r2_hidden @ sk_B @ (u1_pre_topc @ sk_A))
% 0.47/0.65        | ~ (v3_pre_topc @ sk_B @ sk_A))),
% 0.47/0.65      inference('demod', [status(thm)], ['17', '18'])).
% 0.47/0.65  thf('20', plain,
% 0.47/0.65      (((r2_hidden @ sk_B @ (u1_pre_topc @ sk_A)))
% 0.47/0.65         <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 0.47/0.65      inference('sup-', [status(thm)], ['14', '19'])).
% 0.47/0.65  thf('21', plain,
% 0.47/0.65      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.47/0.65          != (k6_tmap_1 @ sk_A @ sk_B))
% 0.47/0.65        | ~ (v3_pre_topc @ sk_B @ sk_A))),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('22', plain,
% 0.47/0.65      (~
% 0.47/0.65       (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.47/0.65          = (k6_tmap_1 @ sk_A @ sk_B))) | 
% 0.47/0.65       ~ ((v3_pre_topc @ sk_B @ sk_A))),
% 0.47/0.65      inference('split', [status(esa)], ['21'])).
% 0.47/0.65  thf('23', plain,
% 0.47/0.65      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf(t104_tmap_1, axiom,
% 0.47/0.65    (![A:$i]:
% 0.47/0.65     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.47/0.65       ( ![B:$i]:
% 0.47/0.65         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.47/0.65           ( ( ( u1_struct_0 @ ( k6_tmap_1 @ A @ B ) ) = ( u1_struct_0 @ A ) ) & 
% 0.47/0.65             ( ( u1_pre_topc @ ( k6_tmap_1 @ A @ B ) ) = ( k5_tmap_1 @ A @ B ) ) ) ) ) ))).
% 0.47/0.65  thf('24', plain,
% 0.47/0.65      (![X25 : $i, X26 : $i]:
% 0.47/0.65         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X26)))
% 0.47/0.65          | ((u1_pre_topc @ (k6_tmap_1 @ X26 @ X25)) = (k5_tmap_1 @ X26 @ X25))
% 0.47/0.65          | ~ (l1_pre_topc @ X26)
% 0.47/0.65          | ~ (v2_pre_topc @ X26)
% 0.47/0.65          | (v2_struct_0 @ X26))),
% 0.47/0.65      inference('cnf', [status(esa)], [t104_tmap_1])).
% 0.47/0.65  thf('25', plain,
% 0.47/0.65      (((v2_struct_0 @ sk_A)
% 0.47/0.65        | ~ (v2_pre_topc @ sk_A)
% 0.47/0.65        | ~ (l1_pre_topc @ sk_A)
% 0.47/0.65        | ((u1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B))
% 0.47/0.65            = (k5_tmap_1 @ sk_A @ sk_B)))),
% 0.47/0.65      inference('sup-', [status(thm)], ['23', '24'])).
% 0.47/0.65  thf('26', plain, ((v2_pre_topc @ sk_A)),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('27', plain, ((l1_pre_topc @ sk_A)),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('28', plain,
% 0.47/0.65      (((v2_struct_0 @ sk_A)
% 0.47/0.65        | ((u1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B))
% 0.47/0.65            = (k5_tmap_1 @ sk_A @ sk_B)))),
% 0.47/0.65      inference('demod', [status(thm)], ['25', '26', '27'])).
% 0.47/0.65  thf('29', plain, (~ (v2_struct_0 @ sk_A)),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('30', plain,
% 0.47/0.65      (((u1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B)) = (k5_tmap_1 @ sk_A @ sk_B))),
% 0.47/0.65      inference('clc', [status(thm)], ['28', '29'])).
% 0.47/0.65  thf(dt_u1_pre_topc, axiom,
% 0.47/0.65    (![A:$i]:
% 0.47/0.65     ( ( l1_pre_topc @ A ) =>
% 0.47/0.65       ( m1_subset_1 @
% 0.47/0.65         ( u1_pre_topc @ A ) @ 
% 0.47/0.65         ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ))).
% 0.47/0.65  thf('31', plain,
% 0.47/0.65      (![X8 : $i]:
% 0.47/0.65         ((m1_subset_1 @ (u1_pre_topc @ X8) @ 
% 0.47/0.65           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X8))))
% 0.47/0.65          | ~ (l1_pre_topc @ X8))),
% 0.47/0.65      inference('cnf', [status(esa)], [dt_u1_pre_topc])).
% 0.47/0.65  thf('32', plain,
% 0.47/0.65      (((m1_subset_1 @ (k5_tmap_1 @ sk_A @ sk_B) @ 
% 0.47/0.65         (k1_zfmisc_1 @ 
% 0.47/0.65          (k1_zfmisc_1 @ (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)))))
% 0.47/0.65        | ~ (l1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B)))),
% 0.47/0.65      inference('sup+', [status(thm)], ['30', '31'])).
% 0.47/0.65  thf('33', plain,
% 0.47/0.65      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf(dt_k6_tmap_1, axiom,
% 0.47/0.65    (![A:$i,B:$i]:
% 0.47/0.65     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.47/0.65         ( l1_pre_topc @ A ) & 
% 0.47/0.65         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.47/0.65       ( ( v1_pre_topc @ ( k6_tmap_1 @ A @ B ) ) & 
% 0.47/0.65         ( v2_pre_topc @ ( k6_tmap_1 @ A @ B ) ) & 
% 0.47/0.65         ( l1_pre_topc @ ( k6_tmap_1 @ A @ B ) ) ) ))).
% 0.47/0.65  thf('34', plain,
% 0.47/0.65      (![X19 : $i, X20 : $i]:
% 0.47/0.65         (~ (l1_pre_topc @ X19)
% 0.47/0.65          | ~ (v2_pre_topc @ X19)
% 0.47/0.65          | (v2_struct_0 @ X19)
% 0.47/0.65          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.47/0.65          | (l1_pre_topc @ (k6_tmap_1 @ X19 @ X20)))),
% 0.47/0.65      inference('cnf', [status(esa)], [dt_k6_tmap_1])).
% 0.47/0.65  thf('35', plain,
% 0.47/0.65      (((l1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B))
% 0.47/0.65        | (v2_struct_0 @ sk_A)
% 0.47/0.65        | ~ (v2_pre_topc @ sk_A)
% 0.47/0.65        | ~ (l1_pre_topc @ sk_A))),
% 0.47/0.65      inference('sup-', [status(thm)], ['33', '34'])).
% 0.47/0.65  thf('36', plain, ((v2_pre_topc @ sk_A)),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('37', plain, ((l1_pre_topc @ sk_A)),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('38', plain,
% 0.47/0.65      (((l1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B)) | (v2_struct_0 @ sk_A))),
% 0.47/0.65      inference('demod', [status(thm)], ['35', '36', '37'])).
% 0.47/0.65  thf('39', plain, (~ (v2_struct_0 @ sk_A)),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('40', plain, ((l1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B))),
% 0.47/0.65      inference('clc', [status(thm)], ['38', '39'])).
% 0.47/0.65  thf('41', plain,
% 0.47/0.65      ((m1_subset_1 @ (k5_tmap_1 @ sk_A @ sk_B) @ 
% 0.47/0.65        (k1_zfmisc_1 @ 
% 0.47/0.65         (k1_zfmisc_1 @ (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)))))),
% 0.47/0.65      inference('demod', [status(thm)], ['32', '40'])).
% 0.47/0.65  thf('42', plain,
% 0.47/0.65      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('43', plain,
% 0.47/0.65      (![X25 : $i, X26 : $i]:
% 0.47/0.65         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X26)))
% 0.47/0.65          | ((u1_struct_0 @ (k6_tmap_1 @ X26 @ X25)) = (u1_struct_0 @ X26))
% 0.47/0.65          | ~ (l1_pre_topc @ X26)
% 0.47/0.65          | ~ (v2_pre_topc @ X26)
% 0.47/0.65          | (v2_struct_0 @ X26))),
% 0.47/0.65      inference('cnf', [status(esa)], [t104_tmap_1])).
% 0.47/0.65  thf('44', plain,
% 0.47/0.65      (((v2_struct_0 @ sk_A)
% 0.47/0.65        | ~ (v2_pre_topc @ sk_A)
% 0.47/0.65        | ~ (l1_pre_topc @ sk_A)
% 0.47/0.65        | ((u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A)))),
% 0.47/0.65      inference('sup-', [status(thm)], ['42', '43'])).
% 0.47/0.65  thf('45', plain, ((v2_pre_topc @ sk_A)),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('46', plain, ((l1_pre_topc @ sk_A)),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('47', plain,
% 0.47/0.65      (((v2_struct_0 @ sk_A)
% 0.47/0.65        | ((u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A)))),
% 0.47/0.65      inference('demod', [status(thm)], ['44', '45', '46'])).
% 0.47/0.65  thf('48', plain, (~ (v2_struct_0 @ sk_A)),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('49', plain,
% 0.47/0.65      (((u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 0.47/0.65      inference('clc', [status(thm)], ['47', '48'])).
% 0.47/0.65  thf('50', plain,
% 0.47/0.65      ((m1_subset_1 @ (k5_tmap_1 @ sk_A @ sk_B) @ 
% 0.47/0.65        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.47/0.65      inference('demod', [status(thm)], ['41', '49'])).
% 0.47/0.65  thf('51', plain,
% 0.47/0.65      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.47/0.65          = (k6_tmap_1 @ sk_A @ sk_B)))
% 0.47/0.65         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.47/0.65                = (k6_tmap_1 @ sk_A @ sk_B))))),
% 0.47/0.65      inference('split', [status(esa)], ['13'])).
% 0.47/0.65  thf(t32_compts_1, axiom,
% 0.47/0.65    (![A:$i]:
% 0.47/0.65     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.47/0.65       ( ![B:$i]:
% 0.47/0.65         ( ( ( v1_tops_2 @ B @ A ) & 
% 0.47/0.65             ( m1_subset_1 @
% 0.47/0.65               B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) <=>
% 0.47/0.65           ( ( v1_tops_2 @
% 0.47/0.65               B @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) & 
% 0.47/0.65             ( m1_subset_1 @
% 0.47/0.65               B @ 
% 0.47/0.65               ( k1_zfmisc_1 @
% 0.47/0.65                 ( k1_zfmisc_1 @
% 0.47/0.65                   ( u1_struct_0 @
% 0.47/0.65                     ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ) ) ) ) ) ))).
% 0.47/0.65  thf('52', plain,
% 0.47/0.65      (![X14 : $i, X15 : $i]:
% 0.47/0.65         (~ (v1_tops_2 @ X14 @ 
% 0.47/0.65             (g1_pre_topc @ (u1_struct_0 @ X15) @ (u1_pre_topc @ X15)))
% 0.47/0.65          | ~ (m1_subset_1 @ X14 @ 
% 0.47/0.65               (k1_zfmisc_1 @ 
% 0.47/0.65                (k1_zfmisc_1 @ 
% 0.47/0.65                 (u1_struct_0 @ 
% 0.47/0.65                  (g1_pre_topc @ (u1_struct_0 @ X15) @ (u1_pre_topc @ X15))))))
% 0.47/0.65          | (v1_tops_2 @ X14 @ X15)
% 0.47/0.65          | ~ (l1_pre_topc @ X15)
% 0.47/0.65          | ~ (v2_pre_topc @ X15)
% 0.47/0.65          | (v2_struct_0 @ X15))),
% 0.47/0.65      inference('cnf', [status(esa)], [t32_compts_1])).
% 0.47/0.65  thf('53', plain,
% 0.47/0.65      ((![X0 : $i]:
% 0.47/0.65          (~ (m1_subset_1 @ X0 @ 
% 0.47/0.65              (k1_zfmisc_1 @ 
% 0.47/0.65               (k1_zfmisc_1 @ (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)))))
% 0.47/0.65           | (v2_struct_0 @ sk_A)
% 0.47/0.65           | ~ (v2_pre_topc @ sk_A)
% 0.47/0.65           | ~ (l1_pre_topc @ sk_A)
% 0.47/0.65           | (v1_tops_2 @ X0 @ sk_A)
% 0.47/0.65           | ~ (v1_tops_2 @ X0 @ 
% 0.47/0.65                (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))
% 0.47/0.65         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.47/0.65                = (k6_tmap_1 @ sk_A @ sk_B))))),
% 0.47/0.65      inference('sup-', [status(thm)], ['51', '52'])).
% 0.47/0.65  thf('54', plain,
% 0.47/0.65      (((u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 0.47/0.65      inference('clc', [status(thm)], ['47', '48'])).
% 0.47/0.65  thf('55', plain, ((v2_pre_topc @ sk_A)),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('56', plain, ((l1_pre_topc @ sk_A)),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('57', plain,
% 0.47/0.65      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.47/0.65          = (k6_tmap_1 @ sk_A @ sk_B)))
% 0.47/0.65         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.47/0.65                = (k6_tmap_1 @ sk_A @ sk_B))))),
% 0.47/0.65      inference('split', [status(esa)], ['13'])).
% 0.47/0.65  thf('58', plain,
% 0.47/0.65      ((![X0 : $i]:
% 0.47/0.65          (~ (m1_subset_1 @ X0 @ 
% 0.47/0.65              (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.47/0.65           | (v2_struct_0 @ sk_A)
% 0.47/0.65           | (v1_tops_2 @ X0 @ sk_A)
% 0.47/0.65           | ~ (v1_tops_2 @ X0 @ (k6_tmap_1 @ sk_A @ sk_B))))
% 0.47/0.65         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.47/0.65                = (k6_tmap_1 @ sk_A @ sk_B))))),
% 0.47/0.65      inference('demod', [status(thm)], ['53', '54', '55', '56', '57'])).
% 0.47/0.65  thf('59', plain,
% 0.47/0.65      (((~ (v1_tops_2 @ (k5_tmap_1 @ sk_A @ sk_B) @ (k6_tmap_1 @ sk_A @ sk_B))
% 0.47/0.65         | (v1_tops_2 @ (k5_tmap_1 @ sk_A @ sk_B) @ sk_A)
% 0.47/0.65         | (v2_struct_0 @ sk_A)))
% 0.47/0.65         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.47/0.65                = (k6_tmap_1 @ sk_A @ sk_B))))),
% 0.47/0.65      inference('sup-', [status(thm)], ['50', '58'])).
% 0.47/0.65  thf('60', plain,
% 0.47/0.65      ((m1_subset_1 @ (k5_tmap_1 @ sk_A @ sk_B) @ 
% 0.47/0.65        (k1_zfmisc_1 @ 
% 0.47/0.65         (k1_zfmisc_1 @ (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)))))),
% 0.47/0.65      inference('demod', [status(thm)], ['32', '40'])).
% 0.47/0.65  thf(t78_tops_2, axiom,
% 0.47/0.65    (![A:$i]:
% 0.47/0.65     ( ( l1_pre_topc @ A ) =>
% 0.47/0.65       ( ![B:$i]:
% 0.47/0.65         ( ( m1_subset_1 @
% 0.47/0.65             B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.47/0.65           ( ( v1_tops_2 @ B @ A ) <=> ( r1_tarski @ B @ ( u1_pre_topc @ A ) ) ) ) ) ))).
% 0.47/0.65  thf('61', plain,
% 0.47/0.65      (![X12 : $i, X13 : $i]:
% 0.47/0.65         (~ (m1_subset_1 @ X12 @ 
% 0.47/0.65             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13))))
% 0.47/0.65          | ~ (r1_tarski @ X12 @ (u1_pre_topc @ X13))
% 0.47/0.65          | (v1_tops_2 @ X12 @ X13)
% 0.47/0.65          | ~ (l1_pre_topc @ X13))),
% 0.47/0.65      inference('cnf', [status(esa)], [t78_tops_2])).
% 0.47/0.65  thf('62', plain,
% 0.47/0.65      ((~ (l1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B))
% 0.47/0.65        | (v1_tops_2 @ (k5_tmap_1 @ sk_A @ sk_B) @ (k6_tmap_1 @ sk_A @ sk_B))
% 0.47/0.65        | ~ (r1_tarski @ (k5_tmap_1 @ sk_A @ sk_B) @ 
% 0.47/0.65             (u1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B))))),
% 0.47/0.65      inference('sup-', [status(thm)], ['60', '61'])).
% 0.47/0.65  thf('63', plain, ((l1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B))),
% 0.47/0.65      inference('clc', [status(thm)], ['38', '39'])).
% 0.47/0.65  thf('64', plain,
% 0.47/0.65      (((u1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B)) = (k5_tmap_1 @ sk_A @ sk_B))),
% 0.47/0.65      inference('clc', [status(thm)], ['28', '29'])).
% 0.47/0.65  thf(d10_xboole_0, axiom,
% 0.47/0.65    (![A:$i,B:$i]:
% 0.47/0.65     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.47/0.65  thf('65', plain,
% 0.47/0.65      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.47/0.65      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.47/0.65  thf('66', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.47/0.65      inference('simplify', [status(thm)], ['65'])).
% 0.47/0.65  thf('67', plain,
% 0.47/0.65      ((v1_tops_2 @ (k5_tmap_1 @ sk_A @ sk_B) @ (k6_tmap_1 @ sk_A @ sk_B))),
% 0.47/0.65      inference('demod', [status(thm)], ['62', '63', '64', '66'])).
% 0.47/0.65  thf('68', plain,
% 0.47/0.65      ((((v1_tops_2 @ (k5_tmap_1 @ sk_A @ sk_B) @ sk_A) | (v2_struct_0 @ sk_A)))
% 0.47/0.65         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.47/0.65                = (k6_tmap_1 @ sk_A @ sk_B))))),
% 0.47/0.65      inference('demod', [status(thm)], ['59', '67'])).
% 0.47/0.65  thf('69', plain, (~ (v2_struct_0 @ sk_A)),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('70', plain,
% 0.47/0.65      (((v1_tops_2 @ (k5_tmap_1 @ sk_A @ sk_B) @ sk_A))
% 0.47/0.65         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.47/0.65                = (k6_tmap_1 @ sk_A @ sk_B))))),
% 0.47/0.65      inference('clc', [status(thm)], ['68', '69'])).
% 0.47/0.65  thf('71', plain,
% 0.47/0.65      ((m1_subset_1 @ (k5_tmap_1 @ sk_A @ sk_B) @ 
% 0.47/0.65        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.47/0.65      inference('demod', [status(thm)], ['41', '49'])).
% 0.47/0.65  thf('72', plain,
% 0.47/0.65      (![X12 : $i, X13 : $i]:
% 0.47/0.65         (~ (m1_subset_1 @ X12 @ 
% 0.47/0.65             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13))))
% 0.47/0.65          | ~ (v1_tops_2 @ X12 @ X13)
% 0.47/0.65          | (r1_tarski @ X12 @ (u1_pre_topc @ X13))
% 0.47/0.65          | ~ (l1_pre_topc @ X13))),
% 0.47/0.65      inference('cnf', [status(esa)], [t78_tops_2])).
% 0.47/0.65  thf('73', plain,
% 0.47/0.65      ((~ (l1_pre_topc @ sk_A)
% 0.47/0.65        | (r1_tarski @ (k5_tmap_1 @ sk_A @ sk_B) @ (u1_pre_topc @ sk_A))
% 0.47/0.65        | ~ (v1_tops_2 @ (k5_tmap_1 @ sk_A @ sk_B) @ sk_A))),
% 0.47/0.65      inference('sup-', [status(thm)], ['71', '72'])).
% 0.47/0.65  thf('74', plain, ((l1_pre_topc @ sk_A)),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('75', plain,
% 0.47/0.65      (((r1_tarski @ (k5_tmap_1 @ sk_A @ sk_B) @ (u1_pre_topc @ sk_A))
% 0.47/0.65        | ~ (v1_tops_2 @ (k5_tmap_1 @ sk_A @ sk_B) @ sk_A))),
% 0.47/0.65      inference('demod', [status(thm)], ['73', '74'])).
% 0.47/0.65  thf('76', plain,
% 0.47/0.65      (((r1_tarski @ (k5_tmap_1 @ sk_A @ sk_B) @ (u1_pre_topc @ sk_A)))
% 0.47/0.65         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.47/0.65                = (k6_tmap_1 @ sk_A @ sk_B))))),
% 0.47/0.65      inference('sup-', [status(thm)], ['70', '75'])).
% 0.47/0.65  thf('77', plain,
% 0.47/0.65      (![X0 : $i, X2 : $i]:
% 0.47/0.65         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.47/0.65      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.47/0.65  thf('78', plain,
% 0.47/0.65      (((~ (r1_tarski @ (u1_pre_topc @ sk_A) @ (k5_tmap_1 @ sk_A @ sk_B))
% 0.47/0.65         | ((u1_pre_topc @ sk_A) = (k5_tmap_1 @ sk_A @ sk_B))))
% 0.47/0.65         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.47/0.65                = (k6_tmap_1 @ sk_A @ sk_B))))),
% 0.47/0.65      inference('sup-', [status(thm)], ['76', '77'])).
% 0.47/0.65  thf('79', plain,
% 0.47/0.65      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.47/0.65          = (k6_tmap_1 @ sk_A @ sk_B)))
% 0.47/0.65         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.47/0.65                = (k6_tmap_1 @ sk_A @ sk_B))))),
% 0.47/0.65      inference('split', [status(esa)], ['13'])).
% 0.47/0.65  thf('80', plain,
% 0.47/0.65      (![X8 : $i]:
% 0.47/0.65         ((m1_subset_1 @ (u1_pre_topc @ X8) @ 
% 0.47/0.65           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X8))))
% 0.47/0.65          | ~ (l1_pre_topc @ X8))),
% 0.47/0.65      inference('cnf', [status(esa)], [dt_u1_pre_topc])).
% 0.47/0.65  thf('81', plain,
% 0.47/0.65      (![X12 : $i, X13 : $i]:
% 0.47/0.65         (~ (m1_subset_1 @ X12 @ 
% 0.47/0.65             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13))))
% 0.47/0.65          | ~ (r1_tarski @ X12 @ (u1_pre_topc @ X13))
% 0.47/0.65          | (v1_tops_2 @ X12 @ X13)
% 0.47/0.65          | ~ (l1_pre_topc @ X13))),
% 0.47/0.65      inference('cnf', [status(esa)], [t78_tops_2])).
% 0.47/0.65  thf('82', plain,
% 0.47/0.65      (![X0 : $i]:
% 0.47/0.65         (~ (l1_pre_topc @ X0)
% 0.47/0.65          | ~ (l1_pre_topc @ X0)
% 0.47/0.65          | (v1_tops_2 @ (u1_pre_topc @ X0) @ X0)
% 0.47/0.65          | ~ (r1_tarski @ (u1_pre_topc @ X0) @ (u1_pre_topc @ X0)))),
% 0.47/0.65      inference('sup-', [status(thm)], ['80', '81'])).
% 0.47/0.65  thf('83', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.47/0.65      inference('simplify', [status(thm)], ['65'])).
% 0.47/0.65  thf('84', plain,
% 0.47/0.65      (![X0 : $i]:
% 0.47/0.65         (~ (l1_pre_topc @ X0)
% 0.47/0.65          | ~ (l1_pre_topc @ X0)
% 0.47/0.65          | (v1_tops_2 @ (u1_pre_topc @ X0) @ X0))),
% 0.47/0.65      inference('demod', [status(thm)], ['82', '83'])).
% 0.47/0.65  thf('85', plain,
% 0.47/0.65      (![X0 : $i]:
% 0.47/0.65         ((v1_tops_2 @ (u1_pre_topc @ X0) @ X0) | ~ (l1_pre_topc @ X0))),
% 0.47/0.65      inference('simplify', [status(thm)], ['84'])).
% 0.47/0.65  thf('86', plain,
% 0.47/0.65      (![X8 : $i]:
% 0.47/0.65         ((m1_subset_1 @ (u1_pre_topc @ X8) @ 
% 0.47/0.65           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X8))))
% 0.47/0.65          | ~ (l1_pre_topc @ X8))),
% 0.47/0.65      inference('cnf', [status(esa)], [dt_u1_pre_topc])).
% 0.47/0.65  thf('87', plain,
% 0.47/0.65      (![X15 : $i, X16 : $i]:
% 0.47/0.65         (~ (v1_tops_2 @ X16 @ X15)
% 0.47/0.65          | ~ (m1_subset_1 @ X16 @ 
% 0.47/0.65               (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15))))
% 0.47/0.65          | (m1_subset_1 @ X16 @ 
% 0.47/0.65             (k1_zfmisc_1 @ 
% 0.47/0.65              (k1_zfmisc_1 @ 
% 0.47/0.65               (u1_struct_0 @ 
% 0.47/0.65                (g1_pre_topc @ (u1_struct_0 @ X15) @ (u1_pre_topc @ X15))))))
% 0.47/0.65          | ~ (l1_pre_topc @ X15)
% 0.47/0.65          | ~ (v2_pre_topc @ X15)
% 0.47/0.65          | (v2_struct_0 @ X15))),
% 0.47/0.65      inference('cnf', [status(esa)], [t32_compts_1])).
% 0.47/0.65  thf('88', plain,
% 0.47/0.65      (![X0 : $i]:
% 0.47/0.65         (~ (l1_pre_topc @ X0)
% 0.47/0.65          | (v2_struct_0 @ X0)
% 0.47/0.65          | ~ (v2_pre_topc @ X0)
% 0.47/0.65          | ~ (l1_pre_topc @ X0)
% 0.47/0.65          | (m1_subset_1 @ (u1_pre_topc @ X0) @ 
% 0.47/0.65             (k1_zfmisc_1 @ 
% 0.47/0.65              (k1_zfmisc_1 @ 
% 0.47/0.65               (u1_struct_0 @ 
% 0.47/0.65                (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))))
% 0.47/0.65          | ~ (v1_tops_2 @ (u1_pre_topc @ X0) @ X0))),
% 0.47/0.65      inference('sup-', [status(thm)], ['86', '87'])).
% 0.47/0.65  thf('89', plain,
% 0.47/0.65      (![X0 : $i]:
% 0.47/0.65         (~ (v1_tops_2 @ (u1_pre_topc @ X0) @ X0)
% 0.47/0.65          | (m1_subset_1 @ (u1_pre_topc @ X0) @ 
% 0.47/0.65             (k1_zfmisc_1 @ 
% 0.47/0.65              (k1_zfmisc_1 @ 
% 0.47/0.65               (u1_struct_0 @ 
% 0.47/0.65                (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))))
% 0.47/0.65          | ~ (v2_pre_topc @ X0)
% 0.47/0.65          | (v2_struct_0 @ X0)
% 0.47/0.65          | ~ (l1_pre_topc @ X0))),
% 0.47/0.65      inference('simplify', [status(thm)], ['88'])).
% 0.47/0.65  thf('90', plain,
% 0.47/0.65      (![X0 : $i]:
% 0.47/0.65         (~ (l1_pre_topc @ X0)
% 0.47/0.65          | ~ (l1_pre_topc @ X0)
% 0.47/0.65          | (v2_struct_0 @ X0)
% 0.47/0.65          | ~ (v2_pre_topc @ X0)
% 0.47/0.65          | (m1_subset_1 @ (u1_pre_topc @ X0) @ 
% 0.47/0.65             (k1_zfmisc_1 @ 
% 0.47/0.65              (k1_zfmisc_1 @ 
% 0.47/0.65               (u1_struct_0 @ 
% 0.47/0.65                (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))))))),
% 0.47/0.65      inference('sup-', [status(thm)], ['85', '89'])).
% 0.47/0.65  thf('91', plain,
% 0.47/0.65      (![X0 : $i]:
% 0.47/0.65         ((m1_subset_1 @ (u1_pre_topc @ X0) @ 
% 0.47/0.65           (k1_zfmisc_1 @ 
% 0.47/0.65            (k1_zfmisc_1 @ 
% 0.47/0.65             (u1_struct_0 @ 
% 0.47/0.65              (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))))
% 0.47/0.65          | ~ (v2_pre_topc @ X0)
% 0.47/0.65          | (v2_struct_0 @ X0)
% 0.47/0.65          | ~ (l1_pre_topc @ X0))),
% 0.47/0.65      inference('simplify', [status(thm)], ['90'])).
% 0.47/0.65  thf('92', plain,
% 0.47/0.65      ((((m1_subset_1 @ (u1_pre_topc @ sk_A) @ 
% 0.47/0.65          (k1_zfmisc_1 @ 
% 0.47/0.66           (k1_zfmisc_1 @ (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)))))
% 0.47/0.66         | ~ (l1_pre_topc @ sk_A)
% 0.47/0.66         | (v2_struct_0 @ sk_A)
% 0.47/0.66         | ~ (v2_pre_topc @ sk_A)))
% 0.47/0.66         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.47/0.66                = (k6_tmap_1 @ sk_A @ sk_B))))),
% 0.47/0.66      inference('sup+', [status(thm)], ['79', '91'])).
% 0.47/0.66  thf('93', plain,
% 0.47/0.66      (((u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 0.47/0.66      inference('clc', [status(thm)], ['47', '48'])).
% 0.47/0.66  thf('94', plain, ((l1_pre_topc @ sk_A)),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('95', plain, ((v2_pre_topc @ sk_A)),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('96', plain,
% 0.47/0.66      ((((m1_subset_1 @ (u1_pre_topc @ sk_A) @ 
% 0.47/0.66          (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.47/0.66         | (v2_struct_0 @ sk_A)))
% 0.47/0.66         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.47/0.66                = (k6_tmap_1 @ sk_A @ sk_B))))),
% 0.47/0.66      inference('demod', [status(thm)], ['92', '93', '94', '95'])).
% 0.47/0.66  thf('97', plain, (~ (v2_struct_0 @ sk_A)),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('98', plain,
% 0.47/0.66      (((m1_subset_1 @ (u1_pre_topc @ sk_A) @ 
% 0.47/0.66         (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))
% 0.47/0.66         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.47/0.66                = (k6_tmap_1 @ sk_A @ sk_B))))),
% 0.47/0.66      inference('clc', [status(thm)], ['96', '97'])).
% 0.47/0.66  thf('99', plain,
% 0.47/0.66      (![X15 : $i, X16 : $i]:
% 0.47/0.66         (~ (v1_tops_2 @ X16 @ X15)
% 0.47/0.66          | ~ (m1_subset_1 @ X16 @ 
% 0.47/0.66               (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15))))
% 0.47/0.66          | (v1_tops_2 @ X16 @ 
% 0.47/0.66             (g1_pre_topc @ (u1_struct_0 @ X15) @ (u1_pre_topc @ X15)))
% 0.47/0.66          | ~ (l1_pre_topc @ X15)
% 0.47/0.66          | ~ (v2_pre_topc @ X15)
% 0.47/0.66          | (v2_struct_0 @ X15))),
% 0.47/0.66      inference('cnf', [status(esa)], [t32_compts_1])).
% 0.47/0.66  thf('100', plain,
% 0.47/0.66      ((((v2_struct_0 @ sk_A)
% 0.47/0.66         | ~ (v2_pre_topc @ sk_A)
% 0.47/0.66         | ~ (l1_pre_topc @ sk_A)
% 0.47/0.66         | (v1_tops_2 @ (u1_pre_topc @ sk_A) @ 
% 0.47/0.66            (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.47/0.66         | ~ (v1_tops_2 @ (u1_pre_topc @ sk_A) @ sk_A)))
% 0.47/0.66         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.47/0.66                = (k6_tmap_1 @ sk_A @ sk_B))))),
% 0.47/0.66      inference('sup-', [status(thm)], ['98', '99'])).
% 0.47/0.66  thf('101', plain, ((v2_pre_topc @ sk_A)),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('102', plain, ((l1_pre_topc @ sk_A)),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('103', plain,
% 0.47/0.66      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.47/0.66          = (k6_tmap_1 @ sk_A @ sk_B)))
% 0.47/0.66         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.47/0.66                = (k6_tmap_1 @ sk_A @ sk_B))))),
% 0.47/0.66      inference('split', [status(esa)], ['13'])).
% 0.47/0.66  thf('104', plain,
% 0.47/0.66      (((m1_subset_1 @ (u1_pre_topc @ sk_A) @ 
% 0.47/0.66         (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))
% 0.47/0.66         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.47/0.66                = (k6_tmap_1 @ sk_A @ sk_B))))),
% 0.47/0.66      inference('clc', [status(thm)], ['96', '97'])).
% 0.47/0.66  thf('105', plain,
% 0.47/0.66      (![X12 : $i, X13 : $i]:
% 0.47/0.66         (~ (m1_subset_1 @ X12 @ 
% 0.47/0.66             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13))))
% 0.47/0.66          | ~ (r1_tarski @ X12 @ (u1_pre_topc @ X13))
% 0.47/0.66          | (v1_tops_2 @ X12 @ X13)
% 0.47/0.66          | ~ (l1_pre_topc @ X13))),
% 0.47/0.66      inference('cnf', [status(esa)], [t78_tops_2])).
% 0.47/0.66  thf('106', plain,
% 0.47/0.66      (((~ (l1_pre_topc @ sk_A)
% 0.47/0.66         | (v1_tops_2 @ (u1_pre_topc @ sk_A) @ sk_A)
% 0.47/0.66         | ~ (r1_tarski @ (u1_pre_topc @ sk_A) @ (u1_pre_topc @ sk_A))))
% 0.47/0.66         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.47/0.66                = (k6_tmap_1 @ sk_A @ sk_B))))),
% 0.47/0.66      inference('sup-', [status(thm)], ['104', '105'])).
% 0.47/0.66  thf('107', plain, ((l1_pre_topc @ sk_A)),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('108', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.47/0.66      inference('simplify', [status(thm)], ['65'])).
% 0.47/0.66  thf('109', plain,
% 0.47/0.66      (((v1_tops_2 @ (u1_pre_topc @ sk_A) @ sk_A))
% 0.47/0.66         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.47/0.66                = (k6_tmap_1 @ sk_A @ sk_B))))),
% 0.47/0.66      inference('demod', [status(thm)], ['106', '107', '108'])).
% 0.47/0.66  thf('110', plain,
% 0.47/0.66      ((((v2_struct_0 @ sk_A)
% 0.47/0.66         | (v1_tops_2 @ (u1_pre_topc @ sk_A) @ (k6_tmap_1 @ sk_A @ sk_B))))
% 0.47/0.66         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.47/0.66                = (k6_tmap_1 @ sk_A @ sk_B))))),
% 0.47/0.66      inference('demod', [status(thm)], ['100', '101', '102', '103', '109'])).
% 0.47/0.66  thf('111', plain, (~ (v2_struct_0 @ sk_A)),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('112', plain,
% 0.47/0.66      (((v1_tops_2 @ (u1_pre_topc @ sk_A) @ (k6_tmap_1 @ sk_A @ sk_B)))
% 0.47/0.66         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.47/0.66                = (k6_tmap_1 @ sk_A @ sk_B))))),
% 0.47/0.66      inference('clc', [status(thm)], ['110', '111'])).
% 0.47/0.66  thf('113', plain,
% 0.47/0.66      (![X8 : $i]:
% 0.47/0.66         ((m1_subset_1 @ (u1_pre_topc @ X8) @ 
% 0.47/0.66           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X8))))
% 0.47/0.66          | ~ (l1_pre_topc @ X8))),
% 0.47/0.66      inference('cnf', [status(esa)], [dt_u1_pre_topc])).
% 0.47/0.66  thf('114', plain,
% 0.47/0.66      (((u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 0.47/0.66      inference('clc', [status(thm)], ['47', '48'])).
% 0.47/0.66  thf('115', plain,
% 0.47/0.66      (![X12 : $i, X13 : $i]:
% 0.47/0.66         (~ (m1_subset_1 @ X12 @ 
% 0.47/0.66             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13))))
% 0.47/0.66          | ~ (v1_tops_2 @ X12 @ X13)
% 0.47/0.66          | (r1_tarski @ X12 @ (u1_pre_topc @ X13))
% 0.47/0.66          | ~ (l1_pre_topc @ X13))),
% 0.47/0.66      inference('cnf', [status(esa)], [t78_tops_2])).
% 0.47/0.66  thf('116', plain,
% 0.47/0.66      (![X0 : $i]:
% 0.47/0.66         (~ (m1_subset_1 @ X0 @ 
% 0.47/0.66             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.47/0.66          | ~ (l1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B))
% 0.47/0.66          | (r1_tarski @ X0 @ (u1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B)))
% 0.47/0.66          | ~ (v1_tops_2 @ X0 @ (k6_tmap_1 @ sk_A @ sk_B)))),
% 0.47/0.66      inference('sup-', [status(thm)], ['114', '115'])).
% 0.47/0.66  thf('117', plain, ((l1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B))),
% 0.47/0.66      inference('clc', [status(thm)], ['38', '39'])).
% 0.47/0.66  thf('118', plain,
% 0.47/0.66      (((u1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B)) = (k5_tmap_1 @ sk_A @ sk_B))),
% 0.47/0.66      inference('clc', [status(thm)], ['28', '29'])).
% 0.47/0.66  thf('119', plain,
% 0.47/0.66      (![X0 : $i]:
% 0.47/0.66         (~ (m1_subset_1 @ X0 @ 
% 0.47/0.66             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.47/0.66          | (r1_tarski @ X0 @ (k5_tmap_1 @ sk_A @ sk_B))
% 0.47/0.66          | ~ (v1_tops_2 @ X0 @ (k6_tmap_1 @ sk_A @ sk_B)))),
% 0.47/0.66      inference('demod', [status(thm)], ['116', '117', '118'])).
% 0.47/0.66  thf('120', plain,
% 0.47/0.66      ((~ (l1_pre_topc @ sk_A)
% 0.47/0.66        | ~ (v1_tops_2 @ (u1_pre_topc @ sk_A) @ (k6_tmap_1 @ sk_A @ sk_B))
% 0.47/0.66        | (r1_tarski @ (u1_pre_topc @ sk_A) @ (k5_tmap_1 @ sk_A @ sk_B)))),
% 0.47/0.66      inference('sup-', [status(thm)], ['113', '119'])).
% 0.47/0.66  thf('121', plain, ((l1_pre_topc @ sk_A)),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('122', plain,
% 0.47/0.66      ((~ (v1_tops_2 @ (u1_pre_topc @ sk_A) @ (k6_tmap_1 @ sk_A @ sk_B))
% 0.47/0.66        | (r1_tarski @ (u1_pre_topc @ sk_A) @ (k5_tmap_1 @ sk_A @ sk_B)))),
% 0.47/0.66      inference('demod', [status(thm)], ['120', '121'])).
% 0.47/0.66  thf('123', plain,
% 0.47/0.66      (((r1_tarski @ (u1_pre_topc @ sk_A) @ (k5_tmap_1 @ sk_A @ sk_B)))
% 0.47/0.66         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.47/0.66                = (k6_tmap_1 @ sk_A @ sk_B))))),
% 0.47/0.66      inference('sup-', [status(thm)], ['112', '122'])).
% 0.47/0.66  thf('124', plain,
% 0.47/0.66      ((((u1_pre_topc @ sk_A) = (k5_tmap_1 @ sk_A @ sk_B)))
% 0.47/0.66         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.47/0.66                = (k6_tmap_1 @ sk_A @ sk_B))))),
% 0.47/0.66      inference('demod', [status(thm)], ['78', '123'])).
% 0.47/0.66  thf('125', plain,
% 0.47/0.66      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('126', plain,
% 0.47/0.66      (![X23 : $i, X24 : $i]:
% 0.47/0.66         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 0.47/0.66          | ((u1_pre_topc @ X24) != (k5_tmap_1 @ X24 @ X23))
% 0.47/0.66          | (r2_hidden @ X23 @ (u1_pre_topc @ X24))
% 0.47/0.66          | ~ (l1_pre_topc @ X24)
% 0.47/0.66          | ~ (v2_pre_topc @ X24)
% 0.47/0.66          | (v2_struct_0 @ X24))),
% 0.47/0.66      inference('cnf', [status(esa)], [t103_tmap_1])).
% 0.47/0.66  thf('127', plain,
% 0.47/0.66      (((v2_struct_0 @ sk_A)
% 0.47/0.66        | ~ (v2_pre_topc @ sk_A)
% 0.47/0.66        | ~ (l1_pre_topc @ sk_A)
% 0.47/0.66        | (r2_hidden @ sk_B @ (u1_pre_topc @ sk_A))
% 0.47/0.66        | ((u1_pre_topc @ sk_A) != (k5_tmap_1 @ sk_A @ sk_B)))),
% 0.47/0.66      inference('sup-', [status(thm)], ['125', '126'])).
% 0.47/0.66  thf('128', plain, ((v2_pre_topc @ sk_A)),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('129', plain, ((l1_pre_topc @ sk_A)),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('130', plain,
% 0.47/0.66      (((v2_struct_0 @ sk_A)
% 0.47/0.66        | (r2_hidden @ sk_B @ (u1_pre_topc @ sk_A))
% 0.47/0.66        | ((u1_pre_topc @ sk_A) != (k5_tmap_1 @ sk_A @ sk_B)))),
% 0.47/0.66      inference('demod', [status(thm)], ['127', '128', '129'])).
% 0.47/0.66  thf('131', plain, (~ (v2_struct_0 @ sk_A)),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('132', plain,
% 0.47/0.66      ((((u1_pre_topc @ sk_A) != (k5_tmap_1 @ sk_A @ sk_B))
% 0.47/0.66        | (r2_hidden @ sk_B @ (u1_pre_topc @ sk_A)))),
% 0.47/0.66      inference('clc', [status(thm)], ['130', '131'])).
% 0.47/0.66  thf('133', plain,
% 0.47/0.66      (((((u1_pre_topc @ sk_A) != (u1_pre_topc @ sk_A))
% 0.47/0.66         | (r2_hidden @ sk_B @ (u1_pre_topc @ sk_A))))
% 0.47/0.66         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.47/0.66                = (k6_tmap_1 @ sk_A @ sk_B))))),
% 0.47/0.66      inference('sup-', [status(thm)], ['124', '132'])).
% 0.47/0.66  thf('134', plain,
% 0.47/0.66      (((r2_hidden @ sk_B @ (u1_pre_topc @ sk_A)))
% 0.47/0.66         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.47/0.66                = (k6_tmap_1 @ sk_A @ sk_B))))),
% 0.47/0.66      inference('simplify', [status(thm)], ['133'])).
% 0.47/0.66  thf('135', plain,
% 0.47/0.66      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('136', plain,
% 0.47/0.66      (![X6 : $i, X7 : $i]:
% 0.47/0.66         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (u1_struct_0 @ X7)))
% 0.47/0.66          | ~ (r2_hidden @ X6 @ (u1_pre_topc @ X7))
% 0.47/0.66          | (v3_pre_topc @ X6 @ X7)
% 0.47/0.66          | ~ (l1_pre_topc @ X7))),
% 0.47/0.66      inference('cnf', [status(esa)], [d5_pre_topc])).
% 0.47/0.66  thf('137', plain,
% 0.47/0.66      ((~ (l1_pre_topc @ sk_A)
% 0.47/0.66        | (v3_pre_topc @ sk_B @ sk_A)
% 0.47/0.66        | ~ (r2_hidden @ sk_B @ (u1_pre_topc @ sk_A)))),
% 0.47/0.66      inference('sup-', [status(thm)], ['135', '136'])).
% 0.47/0.66  thf('138', plain, ((l1_pre_topc @ sk_A)),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('139', plain,
% 0.47/0.66      (((v3_pre_topc @ sk_B @ sk_A)
% 0.47/0.66        | ~ (r2_hidden @ sk_B @ (u1_pre_topc @ sk_A)))),
% 0.47/0.66      inference('demod', [status(thm)], ['137', '138'])).
% 0.47/0.66  thf('140', plain,
% 0.47/0.66      (((v3_pre_topc @ sk_B @ sk_A))
% 0.47/0.66         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.47/0.66                = (k6_tmap_1 @ sk_A @ sk_B))))),
% 0.47/0.66      inference('sup-', [status(thm)], ['134', '139'])).
% 0.47/0.66  thf('141', plain,
% 0.47/0.66      ((~ (v3_pre_topc @ sk_B @ sk_A)) <= (~ ((v3_pre_topc @ sk_B @ sk_A)))),
% 0.47/0.66      inference('split', [status(esa)], ['21'])).
% 0.47/0.66  thf('142', plain,
% 0.47/0.66      (((v3_pre_topc @ sk_B @ sk_A)) | 
% 0.47/0.66       ~
% 0.47/0.66       (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.47/0.66          = (k6_tmap_1 @ sk_A @ sk_B)))),
% 0.47/0.66      inference('sup-', [status(thm)], ['140', '141'])).
% 0.47/0.66  thf('143', plain,
% 0.47/0.66      (((v3_pre_topc @ sk_B @ sk_A)) | 
% 0.47/0.66       (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.47/0.66          = (k6_tmap_1 @ sk_A @ sk_B)))),
% 0.47/0.66      inference('split', [status(esa)], ['13'])).
% 0.47/0.66  thf('144', plain, (((v3_pre_topc @ sk_B @ sk_A))),
% 0.47/0.66      inference('sat_resolution*', [status(thm)], ['22', '142', '143'])).
% 0.47/0.66  thf('145', plain, ((r2_hidden @ sk_B @ (u1_pre_topc @ sk_A))),
% 0.47/0.66      inference('simpl_trail', [status(thm)], ['20', '144'])).
% 0.47/0.66  thf('146', plain,
% 0.47/0.66      (((v2_struct_0 @ sk_A)
% 0.47/0.66        | ((u1_pre_topc @ sk_A) = (k5_tmap_1 @ sk_A @ sk_B)))),
% 0.47/0.66      inference('demod', [status(thm)], ['10', '11', '12', '145'])).
% 0.47/0.66  thf('147', plain, (~ (v2_struct_0 @ sk_A)),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('148', plain, (((u1_pre_topc @ sk_A) = (k5_tmap_1 @ sk_A @ sk_B))),
% 0.47/0.66      inference('clc', [status(thm)], ['146', '147'])).
% 0.47/0.66  thf('149', plain,
% 0.47/0.66      (((k6_tmap_1 @ sk_A @ sk_B)
% 0.47/0.66         = (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))),
% 0.47/0.66      inference('demod', [status(thm)], ['7', '148'])).
% 0.47/0.66  thf('150', plain,
% 0.47/0.66      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.47/0.66          != (k6_tmap_1 @ sk_A @ sk_B)))
% 0.47/0.66         <= (~
% 0.47/0.66             (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.47/0.66                = (k6_tmap_1 @ sk_A @ sk_B))))),
% 0.47/0.66      inference('split', [status(esa)], ['21'])).
% 0.47/0.66  thf('151', plain,
% 0.47/0.66      (~
% 0.47/0.66       (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.47/0.66          = (k6_tmap_1 @ sk_A @ sk_B)))),
% 0.47/0.66      inference('sat_resolution*', [status(thm)], ['22', '142'])).
% 0.47/0.66  thf('152', plain,
% 0.47/0.66      (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.47/0.66         != (k6_tmap_1 @ sk_A @ sk_B))),
% 0.47/0.66      inference('simpl_trail', [status(thm)], ['150', '151'])).
% 0.47/0.66  thf('153', plain, ($false),
% 0.47/0.66      inference('simplify_reflect-', [status(thm)], ['149', '152'])).
% 0.47/0.66  
% 0.47/0.66  % SZS output end Refutation
% 0.47/0.66  
% 0.47/0.66  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
