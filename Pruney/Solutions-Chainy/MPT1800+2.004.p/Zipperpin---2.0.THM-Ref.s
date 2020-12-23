%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.pOpStS61ip

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:10:55 EST 2020

% Result     : Theorem 1.07s
% Output     : Refutation 1.07s
% Verified   : 
% Statistics : Number of formulae       :  198 ( 665 expanded)
%              Number of leaves         :   33 ( 199 expanded)
%              Depth                    :   17
%              Number of atoms          : 1806 (10242 expanded)
%              Number of equality atoms :   92 ( 396 expanded)
%              Maximal formula depth    :   17 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k6_tmap_1_type,type,(
    k6_tmap_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k5_tmap_1_type,type,(
    k5_tmap_1: $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(g1_pre_topc_type,type,(
    g1_pre_topc: $i > $i > $i )).

thf(v1_tsep_1_type,type,(
    v1_tsep_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k8_tmap_1_type,type,(
    k8_tmap_1: $i > $i > $i )).

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

thf('0',plain,
    ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
     != ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( m1_pre_topc @ sk_B @ sk_A )
    | ~ ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( v1_tsep_1 @ sk_B @ sk_A )
    | ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
     != ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ~ ( m1_pre_topc @ sk_B @ sk_A )
   <= ~ ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('4',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t35_borsuk_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( r1_tarski @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) )).

thf('6',plain,(
    ! [X43: $i,X44: $i] :
      ( ~ ( m1_pre_topc @ X43 @ X44 )
      | ( r1_tarski @ ( u1_struct_0 @ X43 ) @ ( u1_struct_0 @ X44 ) )
      | ~ ( l1_pre_topc @ X44 ) ) ),
    inference(cnf,[status(esa)],[t35_borsuk_1])).

thf('7',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['7','8'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('10',plain,(
    ! [X7: $i,X9: $i] :
      ( ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X9 ) )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('11',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

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

thf('12',plain,(
    ! [X36: $i,X37: $i] :
      ( ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X37 ) ) )
      | ( ( u1_pre_topc @ ( k6_tmap_1 @ X37 @ X36 ) )
        = ( k5_tmap_1 @ X37 @ X36 ) )
      | ~ ( l1_pre_topc @ X37 )
      | ~ ( v2_pre_topc @ X37 )
      | ( v2_struct_0 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t104_tmap_1])).

thf('13',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( ( u1_pre_topc @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
      = ( k5_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( u1_pre_topc @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
      = ( k5_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['13','14','15'])).

thf('17',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ( u1_pre_topc @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
    = ( k5_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['16','17'])).

thf('19',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

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

thf('20',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ~ ( m1_pre_topc @ X25 @ X26 )
      | ( X27
       != ( k8_tmap_1 @ X26 @ X25 ) )
      | ( X28
       != ( u1_struct_0 @ X25 ) )
      | ( X27
        = ( k6_tmap_1 @ X26 @ X28 ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) )
      | ~ ( l1_pre_topc @ X27 )
      | ~ ( v2_pre_topc @ X27 )
      | ~ ( v1_pre_topc @ X27 )
      | ~ ( l1_pre_topc @ X26 )
      | ~ ( v2_pre_topc @ X26 )
      | ( v2_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d11_tmap_1])).

thf('21',plain,(
    ! [X25: $i,X26: $i] :
      ( ( v2_struct_0 @ X26 )
      | ~ ( v2_pre_topc @ X26 )
      | ~ ( l1_pre_topc @ X26 )
      | ~ ( v1_pre_topc @ ( k8_tmap_1 @ X26 @ X25 ) )
      | ~ ( v2_pre_topc @ ( k8_tmap_1 @ X26 @ X25 ) )
      | ~ ( l1_pre_topc @ ( k8_tmap_1 @ X26 @ X25 ) )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X25 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) )
      | ( ( k8_tmap_1 @ X26 @ X25 )
        = ( k6_tmap_1 @ X26 @ ( u1_struct_0 @ X25 ) ) )
      | ~ ( m1_pre_topc @ X25 @ X26 ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,
    ( ~ ( m1_pre_topc @ sk_B @ sk_A )
    | ( ( k8_tmap_1 @ sk_A @ sk_B )
      = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
    | ~ ( l1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( v2_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( v1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['19','21'])).

thf('23',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
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

thf('25',plain,(
    ! [X32: $i,X33: $i] :
      ( ~ ( l1_pre_topc @ X32 )
      | ~ ( v2_pre_topc @ X32 )
      | ( v2_struct_0 @ X32 )
      | ~ ( m1_pre_topc @ X33 @ X32 )
      | ( l1_pre_topc @ ( k8_tmap_1 @ X32 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k8_tmap_1])).

thf('26',plain,
    ( ( l1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ( l1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['26','27','28'])).

thf('30',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    l1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['29','30'])).

thf('32',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ( ( k8_tmap_1 @ sk_A @ sk_B )
      = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
    | ~ ( v2_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( v1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['22','23','31','32','33'])).

thf('35',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    ! [X32: $i,X33: $i] :
      ( ~ ( l1_pre_topc @ X32 )
      | ~ ( v2_pre_topc @ X32 )
      | ( v2_struct_0 @ X32 )
      | ~ ( m1_pre_topc @ X33 @ X32 )
      | ( v2_pre_topc @ ( k8_tmap_1 @ X32 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k8_tmap_1])).

thf('37',plain,
    ( ( v2_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,
    ( ( v2_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['37','38','39'])).

thf('41',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    v2_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['40','41'])).

thf('43',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    ! [X32: $i,X33: $i] :
      ( ~ ( l1_pre_topc @ X32 )
      | ~ ( v2_pre_topc @ X32 )
      | ( v2_struct_0 @ X32 )
      | ~ ( m1_pre_topc @ X33 @ X32 )
      | ( v1_pre_topc @ ( k8_tmap_1 @ X32 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k8_tmap_1])).

thf('45',plain,
    ( ( v1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,
    ( ( v1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['45','46','47'])).

thf('49',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    v1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['48','49'])).

thf('51',plain,
    ( ( ( k8_tmap_1 @ sk_A @ sk_B )
      = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['34','42','50'])).

thf('52',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,
    ( ( k8_tmap_1 @ sk_A @ sk_B )
    = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['51','52'])).

thf('54',plain,
    ( ( u1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    = ( k5_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['18','53'])).

thf('55',plain,
    ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,
    ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k8_tmap_1 @ sk_A @ sk_B ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['55'])).

thf(abstractness_v1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( ( v1_pre_topc @ A )
       => ( A
          = ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ) )).

thf('57',plain,(
    ! [X10: $i] :
      ( ~ ( v1_pre_topc @ X10 )
      | ( X10
        = ( g1_pre_topc @ ( u1_struct_0 @ X10 ) @ ( u1_pre_topc @ X10 ) ) )
      | ~ ( l1_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[abstractness_v1_pre_topc])).

thf(dt_u1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( m1_subset_1 @ ( u1_pre_topc @ A ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('58',plain,(
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

thf('59',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ( ( g1_pre_topc @ X21 @ X22 )
       != ( g1_pre_topc @ X19 @ X20 ) )
      | ( X22 = X20 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[free_g1_pre_topc])).

thf('60',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( u1_pre_topc @ X0 )
        = X1 )
      | ( ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) )
       != ( g1_pre_topc @ X2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0
       != ( g1_pre_topc @ X2 @ X1 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_pre_topc @ X0 )
      | ( ( u1_pre_topc @ X0 )
        = X1 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['57','60'])).

thf('62',plain,(
    ! [X1: $i,X2: $i] :
      ( ( ( u1_pre_topc @ ( g1_pre_topc @ X2 @ X1 ) )
        = X1 )
      | ~ ( v1_pre_topc @ ( g1_pre_topc @ X2 @ X1 ) )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ X2 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['61'])).

thf('63',plain,
    ( ( ~ ( v1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      | ( ( u1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
        = ( u1_pre_topc @ sk_A ) ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['56','62'])).

thf('64',plain,
    ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k8_tmap_1 @ sk_A @ sk_B ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['55'])).

thf(fc7_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_pre_topc @ A ) )
     => ( ~ ( v2_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) )
        & ( v1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ) )).

thf('65',plain,(
    ! [X18: $i] :
      ( ( v1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X18 ) @ ( u1_pre_topc @ X18 ) ) )
      | ~ ( l1_pre_topc @ X18 )
      | ( v2_struct_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[fc7_pre_topc])).

thf('66',plain,
    ( ( ( v1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_pre_topc @ sk_A ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['64','65'])).

thf('67',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,
    ( ( ( v1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('69',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,
    ( ( v1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['68','69'])).

thf('71',plain,
    ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k8_tmap_1 @ sk_A @ sk_B ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['55'])).

thf('72',plain,(
    l1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['29','30'])).

thf('73',plain,
    ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k8_tmap_1 @ sk_A @ sk_B ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['55'])).

thf('74',plain,
    ( ( ( u1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
      = ( u1_pre_topc @ sk_A ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['63','70','71','72','73'])).

thf('75',plain,
    ( ( ( k5_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) )
      = ( u1_pre_topc @ sk_A ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['54','74'])).

thf('76',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

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
      | ( ( u1_pre_topc @ X35 )
       != ( k5_tmap_1 @ X35 @ X34 ) )
      | ( r2_hidden @ X34 @ ( u1_pre_topc @ X35 ) )
      | ~ ( l1_pre_topc @ X35 )
      | ~ ( v2_pre_topc @ X35 )
      | ( v2_struct_0 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t103_tmap_1])).

thf('78',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( r2_hidden @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_A ) )
    | ( ( u1_pre_topc @ sk_A )
     != ( k5_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_A ) )
    | ( ( u1_pre_topc @ sk_A )
     != ( k5_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['78','79','80'])).

thf('82',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,
    ( ( ( u1_pre_topc @ sk_A )
     != ( k5_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
    | ( r2_hidden @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_A ) ) ),
    inference(clc,[status(thm)],['81','82'])).

thf('84',plain,
    ( ( ( ( u1_pre_topc @ sk_A )
       != ( u1_pre_topc @ sk_A ) )
      | ( r2_hidden @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_A ) ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['75','83'])).

thf('85',plain,
    ( ( r2_hidden @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_A ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['84'])).

thf('86',plain,(
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

thf('87',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( m1_pre_topc @ X29 @ X30 )
      | ( ( sk_C @ X29 @ X30 )
        = ( u1_struct_0 @ X29 ) )
      | ( v1_tsep_1 @ X29 @ X30 )
      | ~ ( l1_pre_topc @ X30 ) ) ),
    inference(cnf,[status(esa)],[d1_tsep_1])).

thf('88',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v1_tsep_1 @ sk_B @ sk_A )
    | ( ( sk_C @ sk_B @ sk_A )
      = ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,
    ( ( v1_tsep_1 @ sk_B @ sk_A )
    | ( ( sk_C @ sk_B @ sk_A )
      = ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['88','89'])).

thf('91',plain,
    ( ~ ( v1_tsep_1 @ sk_B @ sk_A )
   <= ~ ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('92',plain,
    ( ( ( sk_C @ sk_B @ sk_A )
      = ( u1_struct_0 @ sk_B ) )
   <= ~ ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( m1_pre_topc @ X29 @ X30 )
      | ( m1_subset_1 @ ( sk_C @ X29 @ X30 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X30 ) ) )
      | ( v1_tsep_1 @ X29 @ X30 )
      | ~ ( l1_pre_topc @ X30 ) ) ),
    inference(cnf,[status(esa)],[d1_tsep_1])).

thf('95',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v1_tsep_1 @ sk_B @ sk_A )
    | ( m1_subset_1 @ ( sk_C @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,
    ( ( v1_tsep_1 @ sk_B @ sk_A )
    | ( m1_subset_1 @ ( sk_C @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['95','96'])).

thf(d5_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v3_pre_topc @ B @ A )
          <=> ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) ) ) ) )).

thf('98',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ~ ( r2_hidden @ X11 @ ( u1_pre_topc @ X12 ) )
      | ( v3_pre_topc @ X11 @ X12 )
      | ~ ( l1_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[d5_pre_topc])).

thf('99',plain,
    ( ( v1_tsep_1 @ sk_B @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v3_pre_topc @ ( sk_C @ sk_B @ sk_A ) @ sk_A )
    | ~ ( r2_hidden @ ( sk_C @ sk_B @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,
    ( ( v1_tsep_1 @ sk_B @ sk_A )
    | ( v3_pre_topc @ ( sk_C @ sk_B @ sk_A ) @ sk_A )
    | ~ ( r2_hidden @ ( sk_C @ sk_B @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ),
    inference(demod,[status(thm)],['99','100'])).

thf('102',plain,
    ( ( ~ ( r2_hidden @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_A ) )
      | ( v3_pre_topc @ ( sk_C @ sk_B @ sk_A ) @ sk_A )
      | ( v1_tsep_1 @ sk_B @ sk_A ) )
   <= ~ ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['92','101'])).

thf('103',plain,
    ( ( ( sk_C @ sk_B @ sk_A )
      = ( u1_struct_0 @ sk_B ) )
   <= ~ ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('104',plain,
    ( ( ~ ( r2_hidden @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_A ) )
      | ( v3_pre_topc @ ( u1_struct_0 @ sk_B ) @ sk_A )
      | ( v1_tsep_1 @ sk_B @ sk_A ) )
   <= ~ ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['102','103'])).

thf('105',plain,
    ( ( ( sk_C @ sk_B @ sk_A )
      = ( u1_struct_0 @ sk_B ) )
   <= ~ ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('106',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( m1_pre_topc @ X29 @ X30 )
      | ~ ( v3_pre_topc @ ( sk_C @ X29 @ X30 ) @ X30 )
      | ( v1_tsep_1 @ X29 @ X30 )
      | ~ ( l1_pre_topc @ X30 ) ) ),
    inference(cnf,[status(esa)],[d1_tsep_1])).

thf('107',plain,
    ( ( ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_B ) @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v1_tsep_1 @ sk_B @ sk_A )
      | ~ ( m1_pre_topc @ sk_B @ sk_A ) )
   <= ~ ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['105','106'])).

thf('108',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,
    ( ( ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_B ) @ sk_A )
      | ( v1_tsep_1 @ sk_B @ sk_A ) )
   <= ~ ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['107','108','109'])).

thf('111',plain,
    ( ~ ( v1_tsep_1 @ sk_B @ sk_A )
   <= ~ ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('112',plain,
    ( ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_B ) @ sk_A )
   <= ~ ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['110','111'])).

thf('113',plain,
    ( ( ( v1_tsep_1 @ sk_B @ sk_A )
      | ~ ( r2_hidden @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_A ) ) )
   <= ~ ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['104','112'])).

thf('114',plain,
    ( ~ ( v1_tsep_1 @ sk_B @ sk_A )
   <= ~ ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('115',plain,
    ( ~ ( r2_hidden @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_A ) )
   <= ~ ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['113','114'])).

thf('116',plain,
    ( ( v1_tsep_1 @ sk_B @ sk_A )
    | ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
     != ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['85','115'])).

thf('117',plain,
    ( ( v1_tsep_1 @ sk_B @ sk_A )
    | ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['55'])).

thf('118',plain,
    ( ( v1_tsep_1 @ sk_B @ sk_A )
   <= ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['55'])).

thf('119',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('120',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( m1_pre_topc @ X29 @ X30 )
      | ~ ( v1_tsep_1 @ X29 @ X30 )
      | ( X31
       != ( u1_struct_0 @ X29 ) )
      | ( v3_pre_topc @ X31 @ X30 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X30 ) ) )
      | ~ ( l1_pre_topc @ X30 ) ) ),
    inference(cnf,[status(esa)],[d1_tsep_1])).

thf('121',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( l1_pre_topc @ X30 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X29 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X30 ) ) )
      | ( v3_pre_topc @ ( u1_struct_0 @ X29 ) @ X30 )
      | ~ ( v1_tsep_1 @ X29 @ X30 )
      | ~ ( m1_pre_topc @ X29 @ X30 ) ) ),
    inference(simplify,[status(thm)],['120'])).

thf('122',plain,
    ( ~ ( m1_pre_topc @ sk_B @ sk_A )
    | ~ ( v1_tsep_1 @ sk_B @ sk_A )
    | ( v3_pre_topc @ ( u1_struct_0 @ sk_B ) @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['119','121'])).

thf('123',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('125',plain,
    ( ~ ( v1_tsep_1 @ sk_B @ sk_A )
    | ( v3_pre_topc @ ( u1_struct_0 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['122','123','124'])).

thf('126',plain,
    ( ( v3_pre_topc @ ( u1_struct_0 @ sk_B ) @ sk_A )
   <= ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['118','125'])).

thf('127',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('128',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ~ ( v3_pre_topc @ X11 @ X12 )
      | ( r2_hidden @ X11 @ ( u1_pre_topc @ X12 ) )
      | ~ ( l1_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[d5_pre_topc])).

thf('129',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r2_hidden @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_A ) )
    | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['127','128'])).

thf('130',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('131',plain,
    ( ( r2_hidden @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_A ) )
    | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['129','130'])).

thf('132',plain,
    ( ( r2_hidden @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_A ) )
   <= ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['126','131'])).

thf('133',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('134',plain,(
    ! [X34: $i,X35: $i] :
      ( ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X35 ) ) )
      | ~ ( r2_hidden @ X34 @ ( u1_pre_topc @ X35 ) )
      | ( ( u1_pre_topc @ X35 )
        = ( k5_tmap_1 @ X35 @ X34 ) )
      | ~ ( l1_pre_topc @ X35 )
      | ~ ( v2_pre_topc @ X35 )
      | ( v2_struct_0 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t103_tmap_1])).

thf('135',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( ( u1_pre_topc @ sk_A )
      = ( k5_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
    | ~ ( r2_hidden @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['133','134'])).

thf('136',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('137',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('138',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( u1_pre_topc @ sk_A )
      = ( k5_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
    | ~ ( r2_hidden @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_A ) ) ),
    inference(demod,[status(thm)],['135','136','137'])).

thf('139',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('140',plain,
    ( ~ ( r2_hidden @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_A ) )
    | ( ( u1_pre_topc @ sk_A )
      = ( k5_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['138','139'])).

thf('141',plain,
    ( ( ( u1_pre_topc @ sk_A )
      = ( k5_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
   <= ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['132','140'])).

thf('142',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('143',plain,(
    ! [X36: $i,X37: $i] :
      ( ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X37 ) ) )
      | ( ( u1_struct_0 @ ( k6_tmap_1 @ X37 @ X36 ) )
        = ( u1_struct_0 @ X37 ) )
      | ~ ( l1_pre_topc @ X37 )
      | ~ ( v2_pre_topc @ X37 )
      | ( v2_struct_0 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t104_tmap_1])).

thf('144',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['142','143'])).

thf('145',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('146',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('147',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['144','145','146'])).

thf('148',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('149',plain,
    ( ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['147','148'])).

thf('150',plain,
    ( ( k8_tmap_1 @ sk_A @ sk_B )
    = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['51','52'])).

thf('151',plain,
    ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['149','150'])).

thf('152',plain,(
    ! [X10: $i] :
      ( ~ ( v1_pre_topc @ X10 )
      | ( X10
        = ( g1_pre_topc @ ( u1_struct_0 @ X10 ) @ ( u1_pre_topc @ X10 ) ) )
      | ~ ( l1_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[abstractness_v1_pre_topc])).

thf('153',plain,
    ( ( ( k8_tmap_1 @ sk_A @ sk_B )
      = ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) )
    | ~ ( l1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( v1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['151','152'])).

thf('154',plain,(
    l1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['29','30'])).

thf('155',plain,(
    v1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['48','49'])).

thf('156',plain,
    ( ( k8_tmap_1 @ sk_A @ sk_B )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['153','154','155'])).

thf('157',plain,
    ( ( u1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    = ( k5_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['18','53'])).

thf('158',plain,
    ( ( k8_tmap_1 @ sk_A @ sk_B )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( k5_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['156','157'])).

thf('159',plain,
    ( ( ( k8_tmap_1 @ sk_A @ sk_B )
      = ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
   <= ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['141','158'])).

thf('160',plain,
    ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
     != ( k8_tmap_1 @ sk_A @ sk_B ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
     != ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('161',plain,
    ( ( ( k8_tmap_1 @ sk_A @ sk_B )
     != ( k8_tmap_1 @ sk_A @ sk_B ) )
   <= ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
       != ( k8_tmap_1 @ sk_A @ sk_B ) )
      & ( v1_tsep_1 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['159','160'])).

thf('162',plain,
    ( ~ ( v1_tsep_1 @ sk_B @ sk_A )
    | ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['161'])).

thf('163',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','4','116','117','162'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.pOpStS61ip
% 0.13/0.33  % Computer   : n005.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 12:16:18 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  % Running portfolio for 600 s
% 0.13/0.33  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 1.07/1.28  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.07/1.28  % Solved by: fo/fo7.sh
% 1.07/1.28  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.07/1.28  % done 912 iterations in 0.834s
% 1.07/1.28  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.07/1.28  % SZS output start Refutation
% 1.07/1.28  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.07/1.28  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 1.07/1.28  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 1.07/1.28  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 1.07/1.28  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 1.07/1.28  thf(sk_A_type, type, sk_A: $i).
% 1.07/1.28  thf(k6_tmap_1_type, type, k6_tmap_1: $i > $i > $i).
% 1.07/1.28  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 1.07/1.28  thf(k5_tmap_1_type, type, k5_tmap_1: $i > $i > $i).
% 1.07/1.28  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 1.07/1.28  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 1.07/1.28  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 1.07/1.28  thf(g1_pre_topc_type, type, g1_pre_topc: $i > $i > $i).
% 1.07/1.28  thf(v1_tsep_1_type, type, v1_tsep_1: $i > $i > $o).
% 1.07/1.28  thf(sk_B_type, type, sk_B: $i).
% 1.07/1.28  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.07/1.28  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.07/1.28  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 1.07/1.28  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.07/1.28  thf(k8_tmap_1_type, type, k8_tmap_1: $i > $i > $i).
% 1.07/1.28  thf(t116_tmap_1, conjecture,
% 1.07/1.28    (![A:$i]:
% 1.07/1.28     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.07/1.28       ( ![B:$i]:
% 1.07/1.28         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 1.07/1.28           ( ( ( v1_tsep_1 @ B @ A ) & ( m1_pre_topc @ B @ A ) ) <=>
% 1.07/1.28             ( ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) =
% 1.07/1.28               ( k8_tmap_1 @ A @ B ) ) ) ) ) ))).
% 1.07/1.28  thf(zf_stmt_0, negated_conjecture,
% 1.07/1.28    (~( ![A:$i]:
% 1.07/1.28        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 1.07/1.28            ( l1_pre_topc @ A ) ) =>
% 1.07/1.28          ( ![B:$i]:
% 1.07/1.28            ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 1.07/1.28              ( ( ( v1_tsep_1 @ B @ A ) & ( m1_pre_topc @ B @ A ) ) <=>
% 1.07/1.28                ( ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) =
% 1.07/1.28                  ( k8_tmap_1 @ A @ B ) ) ) ) ) ) )),
% 1.07/1.28    inference('cnf.neg', [status(esa)], [t116_tmap_1])).
% 1.07/1.28  thf('0', plain,
% 1.07/1.28      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 1.07/1.28          != (k8_tmap_1 @ sk_A @ sk_B))
% 1.07/1.28        | ~ (m1_pre_topc @ sk_B @ sk_A)
% 1.07/1.28        | ~ (v1_tsep_1 @ sk_B @ sk_A))),
% 1.07/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.28  thf('1', plain,
% 1.07/1.28      (~ ((v1_tsep_1 @ sk_B @ sk_A)) | 
% 1.07/1.28       ~
% 1.07/1.28       (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 1.07/1.28          = (k8_tmap_1 @ sk_A @ sk_B))) | 
% 1.07/1.28       ~ ((m1_pre_topc @ sk_B @ sk_A))),
% 1.07/1.28      inference('split', [status(esa)], ['0'])).
% 1.07/1.28  thf('2', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 1.07/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.28  thf('3', plain,
% 1.07/1.28      ((~ (m1_pre_topc @ sk_B @ sk_A)) <= (~ ((m1_pre_topc @ sk_B @ sk_A)))),
% 1.07/1.28      inference('split', [status(esa)], ['0'])).
% 1.07/1.28  thf('4', plain, (((m1_pre_topc @ sk_B @ sk_A))),
% 1.07/1.28      inference('sup-', [status(thm)], ['2', '3'])).
% 1.07/1.28  thf('5', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 1.07/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.28  thf(t35_borsuk_1, axiom,
% 1.07/1.28    (![A:$i]:
% 1.07/1.28     ( ( l1_pre_topc @ A ) =>
% 1.07/1.28       ( ![B:$i]:
% 1.07/1.28         ( ( m1_pre_topc @ B @ A ) =>
% 1.07/1.28           ( r1_tarski @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ))).
% 1.07/1.28  thf('6', plain,
% 1.07/1.28      (![X43 : $i, X44 : $i]:
% 1.07/1.28         (~ (m1_pre_topc @ X43 @ X44)
% 1.07/1.28          | (r1_tarski @ (u1_struct_0 @ X43) @ (u1_struct_0 @ X44))
% 1.07/1.28          | ~ (l1_pre_topc @ X44))),
% 1.07/1.28      inference('cnf', [status(esa)], [t35_borsuk_1])).
% 1.07/1.28  thf('7', plain,
% 1.07/1.28      ((~ (l1_pre_topc @ sk_A)
% 1.07/1.28        | (r1_tarski @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 1.07/1.28      inference('sup-', [status(thm)], ['5', '6'])).
% 1.07/1.28  thf('8', plain, ((l1_pre_topc @ sk_A)),
% 1.07/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.28  thf('9', plain, ((r1_tarski @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 1.07/1.28      inference('demod', [status(thm)], ['7', '8'])).
% 1.07/1.28  thf(t3_subset, axiom,
% 1.07/1.28    (![A:$i,B:$i]:
% 1.07/1.28     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 1.07/1.28  thf('10', plain,
% 1.07/1.28      (![X7 : $i, X9 : $i]:
% 1.07/1.28         ((m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X9)) | ~ (r1_tarski @ X7 @ X9))),
% 1.07/1.28      inference('cnf', [status(esa)], [t3_subset])).
% 1.07/1.28  thf('11', plain,
% 1.07/1.28      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 1.07/1.28        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.07/1.28      inference('sup-', [status(thm)], ['9', '10'])).
% 1.07/1.28  thf(t104_tmap_1, axiom,
% 1.07/1.28    (![A:$i]:
% 1.07/1.28     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.07/1.28       ( ![B:$i]:
% 1.07/1.28         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.07/1.28           ( ( ( u1_struct_0 @ ( k6_tmap_1 @ A @ B ) ) = ( u1_struct_0 @ A ) ) & 
% 1.07/1.28             ( ( u1_pre_topc @ ( k6_tmap_1 @ A @ B ) ) = ( k5_tmap_1 @ A @ B ) ) ) ) ) ))).
% 1.07/1.28  thf('12', plain,
% 1.07/1.28      (![X36 : $i, X37 : $i]:
% 1.07/1.28         (~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (u1_struct_0 @ X37)))
% 1.07/1.28          | ((u1_pre_topc @ (k6_tmap_1 @ X37 @ X36)) = (k5_tmap_1 @ X37 @ X36))
% 1.07/1.28          | ~ (l1_pre_topc @ X37)
% 1.07/1.28          | ~ (v2_pre_topc @ X37)
% 1.07/1.28          | (v2_struct_0 @ X37))),
% 1.07/1.28      inference('cnf', [status(esa)], [t104_tmap_1])).
% 1.07/1.28  thf('13', plain,
% 1.07/1.28      (((v2_struct_0 @ sk_A)
% 1.07/1.28        | ~ (v2_pre_topc @ sk_A)
% 1.07/1.28        | ~ (l1_pre_topc @ sk_A)
% 1.07/1.28        | ((u1_pre_topc @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 1.07/1.28            = (k5_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B))))),
% 1.07/1.28      inference('sup-', [status(thm)], ['11', '12'])).
% 1.07/1.28  thf('14', plain, ((v2_pre_topc @ sk_A)),
% 1.07/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.28  thf('15', plain, ((l1_pre_topc @ sk_A)),
% 1.07/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.28  thf('16', plain,
% 1.07/1.28      (((v2_struct_0 @ sk_A)
% 1.07/1.28        | ((u1_pre_topc @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 1.07/1.28            = (k5_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B))))),
% 1.07/1.28      inference('demod', [status(thm)], ['13', '14', '15'])).
% 1.07/1.28  thf('17', plain, (~ (v2_struct_0 @ sk_A)),
% 1.07/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.28  thf('18', plain,
% 1.07/1.28      (((u1_pre_topc @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 1.07/1.28         = (k5_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))),
% 1.07/1.28      inference('clc', [status(thm)], ['16', '17'])).
% 1.07/1.28  thf('19', plain,
% 1.07/1.28      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 1.07/1.28        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.07/1.28      inference('sup-', [status(thm)], ['9', '10'])).
% 1.07/1.28  thf(d11_tmap_1, axiom,
% 1.07/1.28    (![A:$i]:
% 1.07/1.28     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.07/1.28       ( ![B:$i]:
% 1.07/1.28         ( ( m1_pre_topc @ B @ A ) =>
% 1.07/1.28           ( ![C:$i]:
% 1.07/1.28             ( ( ( v1_pre_topc @ C ) & ( v2_pre_topc @ C ) & 
% 1.07/1.28                 ( l1_pre_topc @ C ) ) =>
% 1.07/1.28               ( ( ( C ) = ( k8_tmap_1 @ A @ B ) ) <=>
% 1.07/1.28                 ( ![D:$i]:
% 1.07/1.28                   ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.07/1.28                     ( ( ( D ) = ( u1_struct_0 @ B ) ) =>
% 1.07/1.28                       ( ( C ) = ( k6_tmap_1 @ A @ D ) ) ) ) ) ) ) ) ) ) ))).
% 1.07/1.28  thf('20', plain,
% 1.07/1.28      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 1.07/1.28         (~ (m1_pre_topc @ X25 @ X26)
% 1.07/1.28          | ((X27) != (k8_tmap_1 @ X26 @ X25))
% 1.07/1.28          | ((X28) != (u1_struct_0 @ X25))
% 1.07/1.28          | ((X27) = (k6_tmap_1 @ X26 @ X28))
% 1.07/1.28          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (u1_struct_0 @ X26)))
% 1.07/1.28          | ~ (l1_pre_topc @ X27)
% 1.07/1.28          | ~ (v2_pre_topc @ X27)
% 1.07/1.28          | ~ (v1_pre_topc @ X27)
% 1.07/1.28          | ~ (l1_pre_topc @ X26)
% 1.07/1.28          | ~ (v2_pre_topc @ X26)
% 1.07/1.28          | (v2_struct_0 @ X26))),
% 1.07/1.28      inference('cnf', [status(esa)], [d11_tmap_1])).
% 1.07/1.28  thf('21', plain,
% 1.07/1.28      (![X25 : $i, X26 : $i]:
% 1.07/1.28         ((v2_struct_0 @ X26)
% 1.07/1.28          | ~ (v2_pre_topc @ X26)
% 1.07/1.28          | ~ (l1_pre_topc @ X26)
% 1.07/1.28          | ~ (v1_pre_topc @ (k8_tmap_1 @ X26 @ X25))
% 1.07/1.28          | ~ (v2_pre_topc @ (k8_tmap_1 @ X26 @ X25))
% 1.07/1.28          | ~ (l1_pre_topc @ (k8_tmap_1 @ X26 @ X25))
% 1.07/1.28          | ~ (m1_subset_1 @ (u1_struct_0 @ X25) @ 
% 1.07/1.28               (k1_zfmisc_1 @ (u1_struct_0 @ X26)))
% 1.07/1.28          | ((k8_tmap_1 @ X26 @ X25) = (k6_tmap_1 @ X26 @ (u1_struct_0 @ X25)))
% 1.07/1.28          | ~ (m1_pre_topc @ X25 @ X26))),
% 1.07/1.28      inference('simplify', [status(thm)], ['20'])).
% 1.07/1.28  thf('22', plain,
% 1.07/1.28      ((~ (m1_pre_topc @ sk_B @ sk_A)
% 1.07/1.28        | ((k8_tmap_1 @ sk_A @ sk_B)
% 1.07/1.28            = (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 1.07/1.28        | ~ (l1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 1.07/1.28        | ~ (v2_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 1.07/1.28        | ~ (v1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 1.07/1.28        | ~ (l1_pre_topc @ sk_A)
% 1.07/1.28        | ~ (v2_pre_topc @ sk_A)
% 1.07/1.28        | (v2_struct_0 @ sk_A))),
% 1.07/1.28      inference('sup-', [status(thm)], ['19', '21'])).
% 1.07/1.28  thf('23', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 1.07/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.28  thf('24', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 1.07/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.28  thf(dt_k8_tmap_1, axiom,
% 1.07/1.28    (![A:$i,B:$i]:
% 1.07/1.28     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 1.07/1.28         ( l1_pre_topc @ A ) & ( m1_pre_topc @ B @ A ) ) =>
% 1.07/1.28       ( ( v1_pre_topc @ ( k8_tmap_1 @ A @ B ) ) & 
% 1.07/1.28         ( v2_pre_topc @ ( k8_tmap_1 @ A @ B ) ) & 
% 1.07/1.28         ( l1_pre_topc @ ( k8_tmap_1 @ A @ B ) ) ) ))).
% 1.07/1.28  thf('25', plain,
% 1.07/1.28      (![X32 : $i, X33 : $i]:
% 1.07/1.28         (~ (l1_pre_topc @ X32)
% 1.07/1.28          | ~ (v2_pre_topc @ X32)
% 1.07/1.28          | (v2_struct_0 @ X32)
% 1.07/1.28          | ~ (m1_pre_topc @ X33 @ X32)
% 1.07/1.28          | (l1_pre_topc @ (k8_tmap_1 @ X32 @ X33)))),
% 1.07/1.28      inference('cnf', [status(esa)], [dt_k8_tmap_1])).
% 1.07/1.28  thf('26', plain,
% 1.07/1.28      (((l1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 1.07/1.28        | (v2_struct_0 @ sk_A)
% 1.07/1.28        | ~ (v2_pre_topc @ sk_A)
% 1.07/1.28        | ~ (l1_pre_topc @ sk_A))),
% 1.07/1.28      inference('sup-', [status(thm)], ['24', '25'])).
% 1.07/1.28  thf('27', plain, ((v2_pre_topc @ sk_A)),
% 1.07/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.28  thf('28', plain, ((l1_pre_topc @ sk_A)),
% 1.07/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.28  thf('29', plain,
% 1.07/1.28      (((l1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B)) | (v2_struct_0 @ sk_A))),
% 1.07/1.28      inference('demod', [status(thm)], ['26', '27', '28'])).
% 1.07/1.28  thf('30', plain, (~ (v2_struct_0 @ sk_A)),
% 1.07/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.28  thf('31', plain, ((l1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))),
% 1.07/1.28      inference('clc', [status(thm)], ['29', '30'])).
% 1.07/1.28  thf('32', plain, ((l1_pre_topc @ sk_A)),
% 1.07/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.28  thf('33', plain, ((v2_pre_topc @ sk_A)),
% 1.07/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.28  thf('34', plain,
% 1.07/1.28      ((((k8_tmap_1 @ sk_A @ sk_B) = (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 1.07/1.28        | ~ (v2_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 1.07/1.28        | ~ (v1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 1.07/1.28        | (v2_struct_0 @ sk_A))),
% 1.07/1.28      inference('demod', [status(thm)], ['22', '23', '31', '32', '33'])).
% 1.07/1.28  thf('35', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 1.07/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.28  thf('36', plain,
% 1.07/1.28      (![X32 : $i, X33 : $i]:
% 1.07/1.28         (~ (l1_pre_topc @ X32)
% 1.07/1.28          | ~ (v2_pre_topc @ X32)
% 1.07/1.28          | (v2_struct_0 @ X32)
% 1.07/1.28          | ~ (m1_pre_topc @ X33 @ X32)
% 1.07/1.28          | (v2_pre_topc @ (k8_tmap_1 @ X32 @ X33)))),
% 1.07/1.28      inference('cnf', [status(esa)], [dt_k8_tmap_1])).
% 1.07/1.28  thf('37', plain,
% 1.07/1.28      (((v2_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 1.07/1.28        | (v2_struct_0 @ sk_A)
% 1.07/1.28        | ~ (v2_pre_topc @ sk_A)
% 1.07/1.28        | ~ (l1_pre_topc @ sk_A))),
% 1.07/1.28      inference('sup-', [status(thm)], ['35', '36'])).
% 1.07/1.28  thf('38', plain, ((v2_pre_topc @ sk_A)),
% 1.07/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.28  thf('39', plain, ((l1_pre_topc @ sk_A)),
% 1.07/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.28  thf('40', plain,
% 1.07/1.28      (((v2_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B)) | (v2_struct_0 @ sk_A))),
% 1.07/1.28      inference('demod', [status(thm)], ['37', '38', '39'])).
% 1.07/1.28  thf('41', plain, (~ (v2_struct_0 @ sk_A)),
% 1.07/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.28  thf('42', plain, ((v2_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))),
% 1.07/1.28      inference('clc', [status(thm)], ['40', '41'])).
% 1.07/1.28  thf('43', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 1.07/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.28  thf('44', plain,
% 1.07/1.28      (![X32 : $i, X33 : $i]:
% 1.07/1.28         (~ (l1_pre_topc @ X32)
% 1.07/1.28          | ~ (v2_pre_topc @ X32)
% 1.07/1.28          | (v2_struct_0 @ X32)
% 1.07/1.28          | ~ (m1_pre_topc @ X33 @ X32)
% 1.07/1.28          | (v1_pre_topc @ (k8_tmap_1 @ X32 @ X33)))),
% 1.07/1.28      inference('cnf', [status(esa)], [dt_k8_tmap_1])).
% 1.07/1.28  thf('45', plain,
% 1.07/1.28      (((v1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 1.07/1.28        | (v2_struct_0 @ sk_A)
% 1.07/1.28        | ~ (v2_pre_topc @ sk_A)
% 1.07/1.28        | ~ (l1_pre_topc @ sk_A))),
% 1.07/1.28      inference('sup-', [status(thm)], ['43', '44'])).
% 1.07/1.28  thf('46', plain, ((v2_pre_topc @ sk_A)),
% 1.07/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.28  thf('47', plain, ((l1_pre_topc @ sk_A)),
% 1.07/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.28  thf('48', plain,
% 1.07/1.28      (((v1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B)) | (v2_struct_0 @ sk_A))),
% 1.07/1.28      inference('demod', [status(thm)], ['45', '46', '47'])).
% 1.07/1.28  thf('49', plain, (~ (v2_struct_0 @ sk_A)),
% 1.07/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.28  thf('50', plain, ((v1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))),
% 1.07/1.28      inference('clc', [status(thm)], ['48', '49'])).
% 1.07/1.28  thf('51', plain,
% 1.07/1.28      ((((k8_tmap_1 @ sk_A @ sk_B) = (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 1.07/1.28        | (v2_struct_0 @ sk_A))),
% 1.07/1.28      inference('demod', [status(thm)], ['34', '42', '50'])).
% 1.07/1.28  thf('52', plain, (~ (v2_struct_0 @ sk_A)),
% 1.07/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.28  thf('53', plain,
% 1.07/1.28      (((k8_tmap_1 @ sk_A @ sk_B) = (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))),
% 1.07/1.28      inference('clc', [status(thm)], ['51', '52'])).
% 1.07/1.28  thf('54', plain,
% 1.07/1.28      (((u1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 1.07/1.28         = (k5_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))),
% 1.07/1.28      inference('demod', [status(thm)], ['18', '53'])).
% 1.07/1.28  thf('55', plain,
% 1.07/1.28      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 1.07/1.28          = (k8_tmap_1 @ sk_A @ sk_B))
% 1.07/1.28        | (v1_tsep_1 @ sk_B @ sk_A))),
% 1.07/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.28  thf('56', plain,
% 1.07/1.28      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 1.07/1.28          = (k8_tmap_1 @ sk_A @ sk_B)))
% 1.07/1.28         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 1.07/1.28                = (k8_tmap_1 @ sk_A @ sk_B))))),
% 1.07/1.28      inference('split', [status(esa)], ['55'])).
% 1.07/1.28  thf(abstractness_v1_pre_topc, axiom,
% 1.07/1.28    (![A:$i]:
% 1.07/1.28     ( ( l1_pre_topc @ A ) =>
% 1.07/1.28       ( ( v1_pre_topc @ A ) =>
% 1.07/1.28         ( ( A ) = ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ))).
% 1.07/1.28  thf('57', plain,
% 1.07/1.28      (![X10 : $i]:
% 1.07/1.28         (~ (v1_pre_topc @ X10)
% 1.07/1.28          | ((X10) = (g1_pre_topc @ (u1_struct_0 @ X10) @ (u1_pre_topc @ X10)))
% 1.07/1.28          | ~ (l1_pre_topc @ X10))),
% 1.07/1.28      inference('cnf', [status(esa)], [abstractness_v1_pre_topc])).
% 1.07/1.28  thf(dt_u1_pre_topc, axiom,
% 1.07/1.28    (![A:$i]:
% 1.07/1.28     ( ( l1_pre_topc @ A ) =>
% 1.07/1.28       ( m1_subset_1 @
% 1.07/1.28         ( u1_pre_topc @ A ) @ 
% 1.07/1.28         ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ))).
% 1.07/1.28  thf('58', plain,
% 1.07/1.28      (![X16 : $i]:
% 1.07/1.28         ((m1_subset_1 @ (u1_pre_topc @ X16) @ 
% 1.07/1.28           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16))))
% 1.07/1.28          | ~ (l1_pre_topc @ X16))),
% 1.07/1.28      inference('cnf', [status(esa)], [dt_u1_pre_topc])).
% 1.07/1.28  thf(free_g1_pre_topc, axiom,
% 1.07/1.28    (![A:$i,B:$i]:
% 1.07/1.28     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 1.07/1.28       ( ![C:$i,D:$i]:
% 1.07/1.28         ( ( ( g1_pre_topc @ A @ B ) = ( g1_pre_topc @ C @ D ) ) =>
% 1.07/1.28           ( ( ( A ) = ( C ) ) & ( ( B ) = ( D ) ) ) ) ) ))).
% 1.07/1.28  thf('59', plain,
% 1.07/1.28      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 1.07/1.28         (((g1_pre_topc @ X21 @ X22) != (g1_pre_topc @ X19 @ X20))
% 1.07/1.28          | ((X22) = (X20))
% 1.07/1.28          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X21))))),
% 1.07/1.28      inference('cnf', [status(esa)], [free_g1_pre_topc])).
% 1.07/1.28  thf('60', plain,
% 1.07/1.28      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.07/1.28         (~ (l1_pre_topc @ X0)
% 1.07/1.28          | ((u1_pre_topc @ X0) = (X1))
% 1.07/1.28          | ((g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))
% 1.07/1.28              != (g1_pre_topc @ X2 @ X1)))),
% 1.07/1.28      inference('sup-', [status(thm)], ['58', '59'])).
% 1.07/1.28  thf('61', plain,
% 1.07/1.28      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.07/1.28         (((X0) != (g1_pre_topc @ X2 @ X1))
% 1.07/1.28          | ~ (l1_pre_topc @ X0)
% 1.07/1.28          | ~ (v1_pre_topc @ X0)
% 1.07/1.28          | ((u1_pre_topc @ X0) = (X1))
% 1.07/1.28          | ~ (l1_pre_topc @ X0))),
% 1.07/1.28      inference('sup-', [status(thm)], ['57', '60'])).
% 1.07/1.28  thf('62', plain,
% 1.07/1.28      (![X1 : $i, X2 : $i]:
% 1.07/1.28         (((u1_pre_topc @ (g1_pre_topc @ X2 @ X1)) = (X1))
% 1.07/1.28          | ~ (v1_pre_topc @ (g1_pre_topc @ X2 @ X1))
% 1.07/1.28          | ~ (l1_pre_topc @ (g1_pre_topc @ X2 @ X1)))),
% 1.07/1.28      inference('simplify', [status(thm)], ['61'])).
% 1.07/1.28  thf('63', plain,
% 1.07/1.28      (((~ (v1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 1.07/1.28         | ~ (l1_pre_topc @ 
% 1.07/1.28              (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 1.07/1.28         | ((u1_pre_topc @ 
% 1.07/1.28             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 1.07/1.28             = (u1_pre_topc @ sk_A))))
% 1.07/1.28         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 1.07/1.28                = (k8_tmap_1 @ sk_A @ sk_B))))),
% 1.07/1.28      inference('sup-', [status(thm)], ['56', '62'])).
% 1.07/1.28  thf('64', plain,
% 1.07/1.28      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 1.07/1.28          = (k8_tmap_1 @ sk_A @ sk_B)))
% 1.07/1.28         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 1.07/1.28                = (k8_tmap_1 @ sk_A @ sk_B))))),
% 1.07/1.28      inference('split', [status(esa)], ['55'])).
% 1.07/1.28  thf(fc7_pre_topc, axiom,
% 1.07/1.28    (![A:$i]:
% 1.07/1.28     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 1.07/1.28       ( ( ~( v2_struct_0 @
% 1.07/1.28              ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) & 
% 1.07/1.28         ( v1_pre_topc @
% 1.07/1.28           ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ))).
% 1.07/1.28  thf('65', plain,
% 1.07/1.28      (![X18 : $i]:
% 1.07/1.28         ((v1_pre_topc @ 
% 1.07/1.28           (g1_pre_topc @ (u1_struct_0 @ X18) @ (u1_pre_topc @ X18)))
% 1.07/1.28          | ~ (l1_pre_topc @ X18)
% 1.07/1.28          | (v2_struct_0 @ X18))),
% 1.07/1.28      inference('cnf', [status(esa)], [fc7_pre_topc])).
% 1.07/1.28  thf('66', plain,
% 1.07/1.28      ((((v1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 1.07/1.28         | (v2_struct_0 @ sk_A)
% 1.07/1.28         | ~ (l1_pre_topc @ sk_A)))
% 1.07/1.28         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 1.07/1.28                = (k8_tmap_1 @ sk_A @ sk_B))))),
% 1.07/1.28      inference('sup+', [status(thm)], ['64', '65'])).
% 1.07/1.28  thf('67', plain, ((l1_pre_topc @ sk_A)),
% 1.07/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.28  thf('68', plain,
% 1.07/1.28      ((((v1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B)) | (v2_struct_0 @ sk_A)))
% 1.07/1.28         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 1.07/1.28                = (k8_tmap_1 @ sk_A @ sk_B))))),
% 1.07/1.28      inference('demod', [status(thm)], ['66', '67'])).
% 1.07/1.28  thf('69', plain, (~ (v2_struct_0 @ sk_A)),
% 1.07/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.28  thf('70', plain,
% 1.07/1.28      (((v1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B)))
% 1.07/1.28         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 1.07/1.28                = (k8_tmap_1 @ sk_A @ sk_B))))),
% 1.07/1.28      inference('clc', [status(thm)], ['68', '69'])).
% 1.07/1.28  thf('71', plain,
% 1.07/1.28      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 1.07/1.28          = (k8_tmap_1 @ sk_A @ sk_B)))
% 1.07/1.28         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 1.07/1.28                = (k8_tmap_1 @ sk_A @ sk_B))))),
% 1.07/1.28      inference('split', [status(esa)], ['55'])).
% 1.07/1.28  thf('72', plain, ((l1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))),
% 1.07/1.28      inference('clc', [status(thm)], ['29', '30'])).
% 1.07/1.28  thf('73', plain,
% 1.07/1.28      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 1.07/1.28          = (k8_tmap_1 @ sk_A @ sk_B)))
% 1.07/1.28         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 1.07/1.28                = (k8_tmap_1 @ sk_A @ sk_B))))),
% 1.07/1.28      inference('split', [status(esa)], ['55'])).
% 1.07/1.28  thf('74', plain,
% 1.07/1.28      ((((u1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B)) = (u1_pre_topc @ sk_A)))
% 1.07/1.28         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 1.07/1.28                = (k8_tmap_1 @ sk_A @ sk_B))))),
% 1.07/1.28      inference('demod', [status(thm)], ['63', '70', '71', '72', '73'])).
% 1.07/1.28  thf('75', plain,
% 1.07/1.28      ((((k5_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)) = (u1_pre_topc @ sk_A)))
% 1.07/1.28         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 1.07/1.28                = (k8_tmap_1 @ sk_A @ sk_B))))),
% 1.07/1.28      inference('sup+', [status(thm)], ['54', '74'])).
% 1.07/1.28  thf('76', plain,
% 1.07/1.28      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 1.07/1.28        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.07/1.28      inference('sup-', [status(thm)], ['9', '10'])).
% 1.07/1.28  thf(t103_tmap_1, axiom,
% 1.07/1.28    (![A:$i]:
% 1.07/1.28     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.07/1.28       ( ![B:$i]:
% 1.07/1.28         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.07/1.28           ( ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) <=>
% 1.07/1.28             ( ( u1_pre_topc @ A ) = ( k5_tmap_1 @ A @ B ) ) ) ) ) ))).
% 1.07/1.28  thf('77', plain,
% 1.07/1.28      (![X34 : $i, X35 : $i]:
% 1.07/1.28         (~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (u1_struct_0 @ X35)))
% 1.07/1.28          | ((u1_pre_topc @ X35) != (k5_tmap_1 @ X35 @ X34))
% 1.07/1.28          | (r2_hidden @ X34 @ (u1_pre_topc @ X35))
% 1.07/1.28          | ~ (l1_pre_topc @ X35)
% 1.07/1.28          | ~ (v2_pre_topc @ X35)
% 1.07/1.28          | (v2_struct_0 @ X35))),
% 1.07/1.28      inference('cnf', [status(esa)], [t103_tmap_1])).
% 1.07/1.28  thf('78', plain,
% 1.07/1.28      (((v2_struct_0 @ sk_A)
% 1.07/1.28        | ~ (v2_pre_topc @ sk_A)
% 1.07/1.28        | ~ (l1_pre_topc @ sk_A)
% 1.07/1.28        | (r2_hidden @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_A))
% 1.07/1.28        | ((u1_pre_topc @ sk_A) != (k5_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B))))),
% 1.07/1.28      inference('sup-', [status(thm)], ['76', '77'])).
% 1.07/1.28  thf('79', plain, ((v2_pre_topc @ sk_A)),
% 1.07/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.28  thf('80', plain, ((l1_pre_topc @ sk_A)),
% 1.07/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.28  thf('81', plain,
% 1.07/1.28      (((v2_struct_0 @ sk_A)
% 1.07/1.28        | (r2_hidden @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_A))
% 1.07/1.28        | ((u1_pre_topc @ sk_A) != (k5_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B))))),
% 1.07/1.28      inference('demod', [status(thm)], ['78', '79', '80'])).
% 1.07/1.28  thf('82', plain, (~ (v2_struct_0 @ sk_A)),
% 1.07/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.28  thf('83', plain,
% 1.07/1.28      ((((u1_pre_topc @ sk_A) != (k5_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 1.07/1.28        | (r2_hidden @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_A)))),
% 1.07/1.28      inference('clc', [status(thm)], ['81', '82'])).
% 1.07/1.28  thf('84', plain,
% 1.07/1.28      (((((u1_pre_topc @ sk_A) != (u1_pre_topc @ sk_A))
% 1.07/1.28         | (r2_hidden @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_A))))
% 1.07/1.28         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 1.07/1.28                = (k8_tmap_1 @ sk_A @ sk_B))))),
% 1.07/1.28      inference('sup-', [status(thm)], ['75', '83'])).
% 1.07/1.28  thf('85', plain,
% 1.07/1.28      (((r2_hidden @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_A)))
% 1.07/1.28         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 1.07/1.28                = (k8_tmap_1 @ sk_A @ sk_B))))),
% 1.07/1.28      inference('simplify', [status(thm)], ['84'])).
% 1.07/1.28  thf('86', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 1.07/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.28  thf(d1_tsep_1, axiom,
% 1.07/1.28    (![A:$i]:
% 1.07/1.28     ( ( l1_pre_topc @ A ) =>
% 1.07/1.28       ( ![B:$i]:
% 1.07/1.28         ( ( m1_pre_topc @ B @ A ) =>
% 1.07/1.28           ( ( v1_tsep_1 @ B @ A ) <=>
% 1.07/1.28             ( ![C:$i]:
% 1.07/1.28               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.07/1.28                 ( ( ( C ) = ( u1_struct_0 @ B ) ) => ( v3_pre_topc @ C @ A ) ) ) ) ) ) ) ))).
% 1.07/1.28  thf('87', plain,
% 1.07/1.28      (![X29 : $i, X30 : $i]:
% 1.07/1.28         (~ (m1_pre_topc @ X29 @ X30)
% 1.07/1.28          | ((sk_C @ X29 @ X30) = (u1_struct_0 @ X29))
% 1.07/1.28          | (v1_tsep_1 @ X29 @ X30)
% 1.07/1.28          | ~ (l1_pre_topc @ X30))),
% 1.07/1.28      inference('cnf', [status(esa)], [d1_tsep_1])).
% 1.07/1.28  thf('88', plain,
% 1.07/1.28      ((~ (l1_pre_topc @ sk_A)
% 1.07/1.28        | (v1_tsep_1 @ sk_B @ sk_A)
% 1.07/1.28        | ((sk_C @ sk_B @ sk_A) = (u1_struct_0 @ sk_B)))),
% 1.07/1.28      inference('sup-', [status(thm)], ['86', '87'])).
% 1.07/1.28  thf('89', plain, ((l1_pre_topc @ sk_A)),
% 1.07/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.28  thf('90', plain,
% 1.07/1.28      (((v1_tsep_1 @ sk_B @ sk_A)
% 1.07/1.28        | ((sk_C @ sk_B @ sk_A) = (u1_struct_0 @ sk_B)))),
% 1.07/1.28      inference('demod', [status(thm)], ['88', '89'])).
% 1.07/1.28  thf('91', plain,
% 1.07/1.28      ((~ (v1_tsep_1 @ sk_B @ sk_A)) <= (~ ((v1_tsep_1 @ sk_B @ sk_A)))),
% 1.07/1.28      inference('split', [status(esa)], ['0'])).
% 1.07/1.28  thf('92', plain,
% 1.07/1.28      ((((sk_C @ sk_B @ sk_A) = (u1_struct_0 @ sk_B)))
% 1.07/1.28         <= (~ ((v1_tsep_1 @ sk_B @ sk_A)))),
% 1.07/1.28      inference('sup-', [status(thm)], ['90', '91'])).
% 1.07/1.28  thf('93', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 1.07/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.28  thf('94', plain,
% 1.07/1.28      (![X29 : $i, X30 : $i]:
% 1.07/1.28         (~ (m1_pre_topc @ X29 @ X30)
% 1.07/1.28          | (m1_subset_1 @ (sk_C @ X29 @ X30) @ 
% 1.07/1.28             (k1_zfmisc_1 @ (u1_struct_0 @ X30)))
% 1.07/1.28          | (v1_tsep_1 @ X29 @ X30)
% 1.07/1.28          | ~ (l1_pre_topc @ X30))),
% 1.07/1.28      inference('cnf', [status(esa)], [d1_tsep_1])).
% 1.07/1.28  thf('95', plain,
% 1.07/1.28      ((~ (l1_pre_topc @ sk_A)
% 1.07/1.28        | (v1_tsep_1 @ sk_B @ sk_A)
% 1.07/1.28        | (m1_subset_1 @ (sk_C @ sk_B @ sk_A) @ 
% 1.07/1.28           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 1.07/1.28      inference('sup-', [status(thm)], ['93', '94'])).
% 1.07/1.28  thf('96', plain, ((l1_pre_topc @ sk_A)),
% 1.07/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.28  thf('97', plain,
% 1.07/1.28      (((v1_tsep_1 @ sk_B @ sk_A)
% 1.07/1.28        | (m1_subset_1 @ (sk_C @ sk_B @ sk_A) @ 
% 1.07/1.28           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 1.07/1.28      inference('demod', [status(thm)], ['95', '96'])).
% 1.07/1.28  thf(d5_pre_topc, axiom,
% 1.07/1.28    (![A:$i]:
% 1.07/1.28     ( ( l1_pre_topc @ A ) =>
% 1.07/1.28       ( ![B:$i]:
% 1.07/1.28         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.07/1.28           ( ( v3_pre_topc @ B @ A ) <=>
% 1.07/1.28             ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) ) ) ) ))).
% 1.07/1.28  thf('98', plain,
% 1.07/1.28      (![X11 : $i, X12 : $i]:
% 1.07/1.28         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 1.07/1.28          | ~ (r2_hidden @ X11 @ (u1_pre_topc @ X12))
% 1.07/1.28          | (v3_pre_topc @ X11 @ X12)
% 1.07/1.28          | ~ (l1_pre_topc @ X12))),
% 1.07/1.28      inference('cnf', [status(esa)], [d5_pre_topc])).
% 1.07/1.28  thf('99', plain,
% 1.07/1.28      (((v1_tsep_1 @ sk_B @ sk_A)
% 1.07/1.28        | ~ (l1_pre_topc @ sk_A)
% 1.07/1.28        | (v3_pre_topc @ (sk_C @ sk_B @ sk_A) @ sk_A)
% 1.07/1.28        | ~ (r2_hidden @ (sk_C @ sk_B @ sk_A) @ (u1_pre_topc @ sk_A)))),
% 1.07/1.28      inference('sup-', [status(thm)], ['97', '98'])).
% 1.07/1.28  thf('100', plain, ((l1_pre_topc @ sk_A)),
% 1.07/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.28  thf('101', plain,
% 1.07/1.28      (((v1_tsep_1 @ sk_B @ sk_A)
% 1.07/1.28        | (v3_pre_topc @ (sk_C @ sk_B @ sk_A) @ sk_A)
% 1.07/1.28        | ~ (r2_hidden @ (sk_C @ sk_B @ sk_A) @ (u1_pre_topc @ sk_A)))),
% 1.07/1.28      inference('demod', [status(thm)], ['99', '100'])).
% 1.07/1.28  thf('102', plain,
% 1.07/1.28      (((~ (r2_hidden @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_A))
% 1.07/1.28         | (v3_pre_topc @ (sk_C @ sk_B @ sk_A) @ sk_A)
% 1.07/1.28         | (v1_tsep_1 @ sk_B @ sk_A))) <= (~ ((v1_tsep_1 @ sk_B @ sk_A)))),
% 1.07/1.28      inference('sup-', [status(thm)], ['92', '101'])).
% 1.07/1.28  thf('103', plain,
% 1.07/1.28      ((((sk_C @ sk_B @ sk_A) = (u1_struct_0 @ sk_B)))
% 1.07/1.28         <= (~ ((v1_tsep_1 @ sk_B @ sk_A)))),
% 1.07/1.28      inference('sup-', [status(thm)], ['90', '91'])).
% 1.07/1.28  thf('104', plain,
% 1.07/1.28      (((~ (r2_hidden @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_A))
% 1.07/1.28         | (v3_pre_topc @ (u1_struct_0 @ sk_B) @ sk_A)
% 1.07/1.28         | (v1_tsep_1 @ sk_B @ sk_A))) <= (~ ((v1_tsep_1 @ sk_B @ sk_A)))),
% 1.07/1.28      inference('demod', [status(thm)], ['102', '103'])).
% 1.07/1.28  thf('105', plain,
% 1.07/1.28      ((((sk_C @ sk_B @ sk_A) = (u1_struct_0 @ sk_B)))
% 1.07/1.28         <= (~ ((v1_tsep_1 @ sk_B @ sk_A)))),
% 1.07/1.28      inference('sup-', [status(thm)], ['90', '91'])).
% 1.07/1.28  thf('106', plain,
% 1.07/1.28      (![X29 : $i, X30 : $i]:
% 1.07/1.28         (~ (m1_pre_topc @ X29 @ X30)
% 1.07/1.28          | ~ (v3_pre_topc @ (sk_C @ X29 @ X30) @ X30)
% 1.07/1.28          | (v1_tsep_1 @ X29 @ X30)
% 1.07/1.28          | ~ (l1_pre_topc @ X30))),
% 1.07/1.28      inference('cnf', [status(esa)], [d1_tsep_1])).
% 1.07/1.28  thf('107', plain,
% 1.07/1.28      (((~ (v3_pre_topc @ (u1_struct_0 @ sk_B) @ sk_A)
% 1.07/1.28         | ~ (l1_pre_topc @ sk_A)
% 1.07/1.28         | (v1_tsep_1 @ sk_B @ sk_A)
% 1.07/1.28         | ~ (m1_pre_topc @ sk_B @ sk_A))) <= (~ ((v1_tsep_1 @ sk_B @ sk_A)))),
% 1.07/1.28      inference('sup-', [status(thm)], ['105', '106'])).
% 1.07/1.28  thf('108', plain, ((l1_pre_topc @ sk_A)),
% 1.07/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.28  thf('109', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 1.07/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.28  thf('110', plain,
% 1.07/1.28      (((~ (v3_pre_topc @ (u1_struct_0 @ sk_B) @ sk_A)
% 1.07/1.28         | (v1_tsep_1 @ sk_B @ sk_A))) <= (~ ((v1_tsep_1 @ sk_B @ sk_A)))),
% 1.07/1.28      inference('demod', [status(thm)], ['107', '108', '109'])).
% 1.07/1.28  thf('111', plain,
% 1.07/1.28      ((~ (v1_tsep_1 @ sk_B @ sk_A)) <= (~ ((v1_tsep_1 @ sk_B @ sk_A)))),
% 1.07/1.28      inference('split', [status(esa)], ['0'])).
% 1.07/1.28  thf('112', plain,
% 1.07/1.28      ((~ (v3_pre_topc @ (u1_struct_0 @ sk_B) @ sk_A))
% 1.07/1.28         <= (~ ((v1_tsep_1 @ sk_B @ sk_A)))),
% 1.07/1.28      inference('clc', [status(thm)], ['110', '111'])).
% 1.07/1.28  thf('113', plain,
% 1.07/1.28      ((((v1_tsep_1 @ sk_B @ sk_A)
% 1.07/1.28         | ~ (r2_hidden @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_A))))
% 1.07/1.28         <= (~ ((v1_tsep_1 @ sk_B @ sk_A)))),
% 1.07/1.28      inference('clc', [status(thm)], ['104', '112'])).
% 1.07/1.28  thf('114', plain,
% 1.07/1.28      ((~ (v1_tsep_1 @ sk_B @ sk_A)) <= (~ ((v1_tsep_1 @ sk_B @ sk_A)))),
% 1.07/1.28      inference('split', [status(esa)], ['0'])).
% 1.07/1.28  thf('115', plain,
% 1.07/1.28      ((~ (r2_hidden @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_A)))
% 1.07/1.28         <= (~ ((v1_tsep_1 @ sk_B @ sk_A)))),
% 1.07/1.28      inference('clc', [status(thm)], ['113', '114'])).
% 1.07/1.28  thf('116', plain,
% 1.07/1.28      (((v1_tsep_1 @ sk_B @ sk_A)) | 
% 1.07/1.28       ~
% 1.07/1.28       (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 1.07/1.28          = (k8_tmap_1 @ sk_A @ sk_B)))),
% 1.07/1.28      inference('sup-', [status(thm)], ['85', '115'])).
% 1.07/1.28  thf('117', plain,
% 1.07/1.28      (((v1_tsep_1 @ sk_B @ sk_A)) | 
% 1.07/1.28       (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 1.07/1.28          = (k8_tmap_1 @ sk_A @ sk_B)))),
% 1.07/1.28      inference('split', [status(esa)], ['55'])).
% 1.07/1.28  thf('118', plain,
% 1.07/1.28      (((v1_tsep_1 @ sk_B @ sk_A)) <= (((v1_tsep_1 @ sk_B @ sk_A)))),
% 1.07/1.28      inference('split', [status(esa)], ['55'])).
% 1.07/1.28  thf('119', plain,
% 1.07/1.28      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 1.07/1.28        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.07/1.28      inference('sup-', [status(thm)], ['9', '10'])).
% 1.07/1.28  thf('120', plain,
% 1.07/1.28      (![X29 : $i, X30 : $i, X31 : $i]:
% 1.07/1.28         (~ (m1_pre_topc @ X29 @ X30)
% 1.07/1.28          | ~ (v1_tsep_1 @ X29 @ X30)
% 1.07/1.28          | ((X31) != (u1_struct_0 @ X29))
% 1.07/1.28          | (v3_pre_topc @ X31 @ X30)
% 1.07/1.28          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (u1_struct_0 @ X30)))
% 1.07/1.28          | ~ (l1_pre_topc @ X30))),
% 1.07/1.28      inference('cnf', [status(esa)], [d1_tsep_1])).
% 1.07/1.28  thf('121', plain,
% 1.07/1.28      (![X29 : $i, X30 : $i]:
% 1.07/1.28         (~ (l1_pre_topc @ X30)
% 1.07/1.28          | ~ (m1_subset_1 @ (u1_struct_0 @ X29) @ 
% 1.07/1.28               (k1_zfmisc_1 @ (u1_struct_0 @ X30)))
% 1.07/1.28          | (v3_pre_topc @ (u1_struct_0 @ X29) @ X30)
% 1.07/1.28          | ~ (v1_tsep_1 @ X29 @ X30)
% 1.07/1.28          | ~ (m1_pre_topc @ X29 @ X30))),
% 1.07/1.28      inference('simplify', [status(thm)], ['120'])).
% 1.07/1.28  thf('122', plain,
% 1.07/1.28      ((~ (m1_pre_topc @ sk_B @ sk_A)
% 1.07/1.28        | ~ (v1_tsep_1 @ sk_B @ sk_A)
% 1.07/1.28        | (v3_pre_topc @ (u1_struct_0 @ sk_B) @ sk_A)
% 1.07/1.28        | ~ (l1_pre_topc @ sk_A))),
% 1.07/1.28      inference('sup-', [status(thm)], ['119', '121'])).
% 1.07/1.28  thf('123', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 1.07/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.28  thf('124', plain, ((l1_pre_topc @ sk_A)),
% 1.07/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.28  thf('125', plain,
% 1.07/1.28      ((~ (v1_tsep_1 @ sk_B @ sk_A)
% 1.07/1.28        | (v3_pre_topc @ (u1_struct_0 @ sk_B) @ sk_A))),
% 1.07/1.28      inference('demod', [status(thm)], ['122', '123', '124'])).
% 1.07/1.28  thf('126', plain,
% 1.07/1.28      (((v3_pre_topc @ (u1_struct_0 @ sk_B) @ sk_A))
% 1.07/1.28         <= (((v1_tsep_1 @ sk_B @ sk_A)))),
% 1.07/1.28      inference('sup-', [status(thm)], ['118', '125'])).
% 1.07/1.28  thf('127', plain,
% 1.07/1.28      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 1.07/1.28        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.07/1.28      inference('sup-', [status(thm)], ['9', '10'])).
% 1.07/1.28  thf('128', plain,
% 1.07/1.28      (![X11 : $i, X12 : $i]:
% 1.07/1.28         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 1.07/1.28          | ~ (v3_pre_topc @ X11 @ X12)
% 1.07/1.28          | (r2_hidden @ X11 @ (u1_pre_topc @ X12))
% 1.07/1.28          | ~ (l1_pre_topc @ X12))),
% 1.07/1.28      inference('cnf', [status(esa)], [d5_pre_topc])).
% 1.07/1.28  thf('129', plain,
% 1.07/1.28      ((~ (l1_pre_topc @ sk_A)
% 1.07/1.28        | (r2_hidden @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_A))
% 1.07/1.28        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_B) @ sk_A))),
% 1.07/1.28      inference('sup-', [status(thm)], ['127', '128'])).
% 1.07/1.28  thf('130', plain, ((l1_pre_topc @ sk_A)),
% 1.07/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.28  thf('131', plain,
% 1.07/1.28      (((r2_hidden @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_A))
% 1.07/1.28        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_B) @ sk_A))),
% 1.07/1.28      inference('demod', [status(thm)], ['129', '130'])).
% 1.07/1.28  thf('132', plain,
% 1.07/1.28      (((r2_hidden @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_A)))
% 1.07/1.28         <= (((v1_tsep_1 @ sk_B @ sk_A)))),
% 1.07/1.28      inference('sup-', [status(thm)], ['126', '131'])).
% 1.07/1.28  thf('133', plain,
% 1.07/1.28      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 1.07/1.28        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.07/1.28      inference('sup-', [status(thm)], ['9', '10'])).
% 1.07/1.28  thf('134', plain,
% 1.07/1.28      (![X34 : $i, X35 : $i]:
% 1.07/1.28         (~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (u1_struct_0 @ X35)))
% 1.07/1.28          | ~ (r2_hidden @ X34 @ (u1_pre_topc @ X35))
% 1.07/1.28          | ((u1_pre_topc @ X35) = (k5_tmap_1 @ X35 @ X34))
% 1.07/1.28          | ~ (l1_pre_topc @ X35)
% 1.07/1.28          | ~ (v2_pre_topc @ X35)
% 1.07/1.28          | (v2_struct_0 @ X35))),
% 1.07/1.28      inference('cnf', [status(esa)], [t103_tmap_1])).
% 1.07/1.28  thf('135', plain,
% 1.07/1.28      (((v2_struct_0 @ sk_A)
% 1.07/1.28        | ~ (v2_pre_topc @ sk_A)
% 1.07/1.28        | ~ (l1_pre_topc @ sk_A)
% 1.07/1.28        | ((u1_pre_topc @ sk_A) = (k5_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 1.07/1.28        | ~ (r2_hidden @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_A)))),
% 1.07/1.28      inference('sup-', [status(thm)], ['133', '134'])).
% 1.07/1.28  thf('136', plain, ((v2_pre_topc @ sk_A)),
% 1.07/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.28  thf('137', plain, ((l1_pre_topc @ sk_A)),
% 1.07/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.28  thf('138', plain,
% 1.07/1.28      (((v2_struct_0 @ sk_A)
% 1.07/1.28        | ((u1_pre_topc @ sk_A) = (k5_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 1.07/1.28        | ~ (r2_hidden @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_A)))),
% 1.07/1.28      inference('demod', [status(thm)], ['135', '136', '137'])).
% 1.07/1.28  thf('139', plain, (~ (v2_struct_0 @ sk_A)),
% 1.07/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.28  thf('140', plain,
% 1.07/1.28      ((~ (r2_hidden @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_A))
% 1.07/1.28        | ((u1_pre_topc @ sk_A) = (k5_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B))))),
% 1.07/1.28      inference('clc', [status(thm)], ['138', '139'])).
% 1.07/1.28  thf('141', plain,
% 1.07/1.28      ((((u1_pre_topc @ sk_A) = (k5_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B))))
% 1.07/1.28         <= (((v1_tsep_1 @ sk_B @ sk_A)))),
% 1.07/1.28      inference('sup-', [status(thm)], ['132', '140'])).
% 1.07/1.28  thf('142', plain,
% 1.07/1.28      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 1.07/1.28        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.07/1.28      inference('sup-', [status(thm)], ['9', '10'])).
% 1.07/1.28  thf('143', plain,
% 1.07/1.28      (![X36 : $i, X37 : $i]:
% 1.07/1.28         (~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (u1_struct_0 @ X37)))
% 1.07/1.28          | ((u1_struct_0 @ (k6_tmap_1 @ X37 @ X36)) = (u1_struct_0 @ X37))
% 1.07/1.28          | ~ (l1_pre_topc @ X37)
% 1.07/1.28          | ~ (v2_pre_topc @ X37)
% 1.07/1.28          | (v2_struct_0 @ X37))),
% 1.07/1.28      inference('cnf', [status(esa)], [t104_tmap_1])).
% 1.07/1.28  thf('144', plain,
% 1.07/1.28      (((v2_struct_0 @ sk_A)
% 1.07/1.28        | ~ (v2_pre_topc @ sk_A)
% 1.07/1.28        | ~ (l1_pre_topc @ sk_A)
% 1.07/1.28        | ((u1_struct_0 @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 1.07/1.28            = (u1_struct_0 @ sk_A)))),
% 1.07/1.28      inference('sup-', [status(thm)], ['142', '143'])).
% 1.07/1.28  thf('145', plain, ((v2_pre_topc @ sk_A)),
% 1.07/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.28  thf('146', plain, ((l1_pre_topc @ sk_A)),
% 1.07/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.28  thf('147', plain,
% 1.07/1.28      (((v2_struct_0 @ sk_A)
% 1.07/1.28        | ((u1_struct_0 @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 1.07/1.28            = (u1_struct_0 @ sk_A)))),
% 1.07/1.28      inference('demod', [status(thm)], ['144', '145', '146'])).
% 1.07/1.28  thf('148', plain, (~ (v2_struct_0 @ sk_A)),
% 1.07/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.28  thf('149', plain,
% 1.07/1.28      (((u1_struct_0 @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 1.07/1.28         = (u1_struct_0 @ sk_A))),
% 1.07/1.28      inference('clc', [status(thm)], ['147', '148'])).
% 1.07/1.28  thf('150', plain,
% 1.07/1.28      (((k8_tmap_1 @ sk_A @ sk_B) = (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))),
% 1.07/1.28      inference('clc', [status(thm)], ['51', '52'])).
% 1.07/1.28  thf('151', plain,
% 1.07/1.28      (((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 1.07/1.28      inference('demod', [status(thm)], ['149', '150'])).
% 1.07/1.28  thf('152', plain,
% 1.07/1.28      (![X10 : $i]:
% 1.07/1.28         (~ (v1_pre_topc @ X10)
% 1.07/1.28          | ((X10) = (g1_pre_topc @ (u1_struct_0 @ X10) @ (u1_pre_topc @ X10)))
% 1.07/1.28          | ~ (l1_pre_topc @ X10))),
% 1.07/1.28      inference('cnf', [status(esa)], [abstractness_v1_pre_topc])).
% 1.07/1.28  thf('153', plain,
% 1.07/1.28      ((((k8_tmap_1 @ sk_A @ sk_B)
% 1.07/1.28          = (g1_pre_topc @ (u1_struct_0 @ sk_A) @ 
% 1.07/1.28             (u1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))))
% 1.07/1.28        | ~ (l1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 1.07/1.28        | ~ (v1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B)))),
% 1.07/1.28      inference('sup+', [status(thm)], ['151', '152'])).
% 1.07/1.28  thf('154', plain, ((l1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))),
% 1.07/1.28      inference('clc', [status(thm)], ['29', '30'])).
% 1.07/1.28  thf('155', plain, ((v1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))),
% 1.07/1.28      inference('clc', [status(thm)], ['48', '49'])).
% 1.07/1.28  thf('156', plain,
% 1.07/1.28      (((k8_tmap_1 @ sk_A @ sk_B)
% 1.07/1.28         = (g1_pre_topc @ (u1_struct_0 @ sk_A) @ 
% 1.07/1.28            (u1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))))),
% 1.07/1.28      inference('demod', [status(thm)], ['153', '154', '155'])).
% 1.07/1.28  thf('157', plain,
% 1.07/1.28      (((u1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 1.07/1.28         = (k5_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))),
% 1.07/1.28      inference('demod', [status(thm)], ['18', '53'])).
% 1.07/1.28  thf('158', plain,
% 1.07/1.28      (((k8_tmap_1 @ sk_A @ sk_B)
% 1.07/1.28         = (g1_pre_topc @ (u1_struct_0 @ sk_A) @ 
% 1.07/1.28            (k5_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B))))),
% 1.07/1.28      inference('demod', [status(thm)], ['156', '157'])).
% 1.07/1.28  thf('159', plain,
% 1.07/1.28      ((((k8_tmap_1 @ sk_A @ sk_B)
% 1.07/1.28          = (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))
% 1.07/1.28         <= (((v1_tsep_1 @ sk_B @ sk_A)))),
% 1.07/1.28      inference('sup+', [status(thm)], ['141', '158'])).
% 1.07/1.28  thf('160', plain,
% 1.07/1.28      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 1.07/1.28          != (k8_tmap_1 @ sk_A @ sk_B)))
% 1.07/1.28         <= (~
% 1.07/1.28             (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 1.07/1.28                = (k8_tmap_1 @ sk_A @ sk_B))))),
% 1.07/1.28      inference('split', [status(esa)], ['0'])).
% 1.07/1.28  thf('161', plain,
% 1.07/1.28      ((((k8_tmap_1 @ sk_A @ sk_B) != (k8_tmap_1 @ sk_A @ sk_B)))
% 1.07/1.28         <= (~
% 1.07/1.28             (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 1.07/1.28                = (k8_tmap_1 @ sk_A @ sk_B))) & 
% 1.07/1.28             ((v1_tsep_1 @ sk_B @ sk_A)))),
% 1.07/1.28      inference('sup-', [status(thm)], ['159', '160'])).
% 1.07/1.28  thf('162', plain,
% 1.07/1.28      (~ ((v1_tsep_1 @ sk_B @ sk_A)) | 
% 1.07/1.28       (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 1.07/1.28          = (k8_tmap_1 @ sk_A @ sk_B)))),
% 1.07/1.28      inference('simplify', [status(thm)], ['161'])).
% 1.07/1.28  thf('163', plain, ($false),
% 1.07/1.28      inference('sat_resolution*', [status(thm)],
% 1.07/1.28                ['1', '4', '116', '117', '162'])).
% 1.07/1.28  
% 1.07/1.28  % SZS output end Refutation
% 1.07/1.28  
% 1.07/1.29  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
