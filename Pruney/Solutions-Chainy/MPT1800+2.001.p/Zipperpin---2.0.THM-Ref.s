%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.pv9Rh4XsqV

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:10:55 EST 2020

% Result     : Theorem 7.42s
% Output     : Refutation 7.42s
% Verified   : 
% Statistics : Number of formulae       :  224 (5891 expanded)
%              Number of leaves         :   40 (1661 expanded)
%              Depth                    :   29
%              Number of atoms          : 1942 (95470 expanded)
%              Number of equality atoms :   74 (3508 expanded)
%              Maximal formula depth    :   17 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_tsep_1_type,type,(
    v1_tsep_1: $i > $i > $o )).

thf(k6_tmap_1_type,type,(
    k6_tmap_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k5_tmap_1_type,type,(
    k5_tmap_1: $i > $i > $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k8_tmap_1_type,type,(
    k8_tmap_1: $i > $i > $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(g1_pre_topc_type,type,(
    g1_pre_topc: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

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

thf('1',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t1_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( m1_subset_1 @ ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('2',plain,(
    ! [X60: $i,X61: $i] :
      ( ~ ( m1_pre_topc @ X60 @ X61 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X60 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X61 ) ) )
      | ~ ( l1_pre_topc @ X61 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('3',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['3','4'])).

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

thf('6',plain,(
    ! [X44: $i,X45: $i] :
      ( ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X45 ) ) )
      | ( ( u1_struct_0 @ ( k6_tmap_1 @ X45 @ X44 ) )
        = ( u1_struct_0 @ X45 ) )
      | ~ ( l1_pre_topc @ X45 )
      | ~ ( v2_pre_topc @ X45 )
      | ( v2_struct_0 @ X45 ) ) ),
    inference(cnf,[status(esa)],[t104_tmap_1])).

thf('7',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['3','4'])).

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

thf('11',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( m1_pre_topc @ X31 @ X32 )
      | ( X33
       != ( k8_tmap_1 @ X32 @ X31 ) )
      | ( X34
       != ( u1_struct_0 @ X31 ) )
      | ( X33
        = ( k6_tmap_1 @ X32 @ X34 ) )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X32 ) ) )
      | ~ ( l1_pre_topc @ X33 )
      | ~ ( v2_pre_topc @ X33 )
      | ~ ( v1_pre_topc @ X33 )
      | ~ ( l1_pre_topc @ X32 )
      | ~ ( v2_pre_topc @ X32 )
      | ( v2_struct_0 @ X32 ) ) ),
    inference(cnf,[status(esa)],[d11_tmap_1])).

thf('12',plain,(
    ! [X31: $i,X32: $i] :
      ( ( v2_struct_0 @ X32 )
      | ~ ( v2_pre_topc @ X32 )
      | ~ ( l1_pre_topc @ X32 )
      | ~ ( v1_pre_topc @ ( k8_tmap_1 @ X32 @ X31 ) )
      | ~ ( v2_pre_topc @ ( k8_tmap_1 @ X32 @ X31 ) )
      | ~ ( l1_pre_topc @ ( k8_tmap_1 @ X32 @ X31 ) )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X31 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X32 ) ) )
      | ( ( k8_tmap_1 @ X32 @ X31 )
        = ( k6_tmap_1 @ X32 @ ( u1_struct_0 @ X31 ) ) )
      | ~ ( m1_pre_topc @ X31 @ X32 ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,
    ( ~ ( m1_pre_topc @ sk_B @ sk_A )
    | ( ( k8_tmap_1 @ sk_A @ sk_B )
      = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
    | ~ ( l1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( v2_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( v1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['10','12'])).

thf('14',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
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

thf('16',plain,(
    ! [X40: $i,X41: $i] :
      ( ~ ( l1_pre_topc @ X40 )
      | ~ ( v2_pre_topc @ X40 )
      | ( v2_struct_0 @ X40 )
      | ~ ( m1_pre_topc @ X41 @ X40 )
      | ( l1_pre_topc @ ( k8_tmap_1 @ X40 @ X41 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k8_tmap_1])).

thf('17',plain,
    ( ( l1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ( l1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['17','18','19'])).

thf('21',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    l1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['20','21'])).

thf('23',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ! [X40: $i,X41: $i] :
      ( ~ ( l1_pre_topc @ X40 )
      | ~ ( v2_pre_topc @ X40 )
      | ( v2_struct_0 @ X40 )
      | ~ ( m1_pre_topc @ X41 @ X40 )
      | ( v2_pre_topc @ ( k8_tmap_1 @ X40 @ X41 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k8_tmap_1])).

thf('25',plain,
    ( ( v2_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( ( v2_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['25','26','27'])).

thf('29',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    v2_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['28','29'])).

thf('31',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ( ( k8_tmap_1 @ sk_A @ sk_B )
      = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
    | ~ ( v1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['13','14','22','30','31','32'])).

thf('34',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    ! [X40: $i,X41: $i] :
      ( ~ ( l1_pre_topc @ X40 )
      | ~ ( v2_pre_topc @ X40 )
      | ( v2_struct_0 @ X40 )
      | ~ ( m1_pre_topc @ X41 @ X40 )
      | ( v1_pre_topc @ ( k8_tmap_1 @ X40 @ X41 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k8_tmap_1])).

thf('36',plain,
    ( ( v1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ( v1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['36','37','38'])).

thf('40',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    v1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['39','40'])).

thf('42',plain,
    ( ( ( k8_tmap_1 @ sk_A @ sk_B )
      = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['33','41'])).

thf('43',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,
    ( ( k8_tmap_1 @ sk_A @ sk_B )
    = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['42','43'])).

thf('45',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['7','8','9','44'])).

thf('46',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['45','46'])).

thf(fc1_struct_0,axiom,(
    ! [A: $i] :
      ( ( ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('48',plain,(
    ! [X22: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ X22 ) )
      | ~ ( l1_struct_0 @ X22 )
      | ~ ( v2_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[fc1_struct_0])).

thf('49',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v2_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( l1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['47','48'])).

thf('50',plain,(
    l1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['20','21'])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('51',plain,(
    ! [X19: $i] :
      ( ( l1_struct_0 @ X19 )
      | ~ ( l1_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('52',plain,(
    l1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v2_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['49','52'])).

thf('54',plain,
    ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k8_tmap_1 @ sk_A @ sk_B ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['54'])).

thf('56',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t65_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( l1_pre_topc @ B )
         => ( ( m1_pre_topc @ A @ B )
          <=> ( m1_pre_topc @ A @ ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ) )).

thf('57',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( l1_pre_topc @ X29 )
      | ~ ( m1_pre_topc @ X30 @ X29 )
      | ( m1_pre_topc @ X30 @ ( g1_pre_topc @ ( u1_struct_0 @ X29 ) @ ( u1_pre_topc @ X29 ) ) )
      | ~ ( l1_pre_topc @ X30 ) ) ),
    inference(cnf,[status(esa)],[t65_pre_topc])).

thf('58',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( m1_pre_topc @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('60',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( m1_pre_topc @ X20 @ X21 )
      | ( l1_pre_topc @ X20 )
      | ~ ( l1_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('61',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    m1_pre_topc @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ),
    inference(demod,[status(thm)],['58','63','64'])).

thf('66',plain,
    ( ( m1_pre_topc @ sk_B @ ( k8_tmap_1 @ sk_A @ sk_B ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['55','65'])).

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

thf('67',plain,(
    ! [X35: $i,X36: $i] :
      ( ~ ( m1_pre_topc @ X35 @ X36 )
      | ( ( sk_C @ X35 @ X36 )
        = ( u1_struct_0 @ X35 ) )
      | ( v1_tsep_1 @ X35 @ X36 )
      | ~ ( l1_pre_topc @ X36 ) ) ),
    inference(cnf,[status(esa)],[d1_tsep_1])).

thf('68',plain,
    ( ( ~ ( l1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
      | ( v1_tsep_1 @ sk_B @ ( k8_tmap_1 @ sk_A @ sk_B ) )
      | ( ( sk_C @ sk_B @ ( k8_tmap_1 @ sk_A @ sk_B ) )
        = ( u1_struct_0 @ sk_B ) ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    l1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['20','21'])).

thf('70',plain,
    ( ( ( v1_tsep_1 @ sk_B @ ( k8_tmap_1 @ sk_A @ sk_B ) )
      | ( ( sk_C @ sk_B @ ( k8_tmap_1 @ sk_A @ sk_B ) )
        = ( u1_struct_0 @ sk_B ) ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('71',plain,
    ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
     != ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( m1_pre_topc @ sk_B @ sk_A )
    | ~ ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,
    ( ~ ( v1_tsep_1 @ sk_B @ sk_A )
    | ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
     != ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['71'])).

thf('73',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,
    ( ~ ( m1_pre_topc @ sk_B @ sk_A )
   <= ~ ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['71'])).

thf('75',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,
    ( ( v1_tsep_1 @ sk_B @ sk_A )
   <= ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['54'])).

thf('77',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('78',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ~ ( m1_pre_topc @ X35 @ X36 )
      | ~ ( v1_tsep_1 @ X35 @ X36 )
      | ( X37
       != ( u1_struct_0 @ X35 ) )
      | ( v3_pre_topc @ X37 @ X36 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X36 ) ) )
      | ~ ( l1_pre_topc @ X36 ) ) ),
    inference(cnf,[status(esa)],[d1_tsep_1])).

thf('79',plain,(
    ! [X35: $i,X36: $i] :
      ( ~ ( l1_pre_topc @ X36 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X35 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X36 ) ) )
      | ( v3_pre_topc @ ( u1_struct_0 @ X35 ) @ X36 )
      | ~ ( v1_tsep_1 @ X35 @ X36 )
      | ~ ( m1_pre_topc @ X35 @ X36 ) ) ),
    inference(simplify,[status(thm)],['78'])).

thf('80',plain,
    ( ~ ( m1_pre_topc @ sk_B @ sk_A )
    | ~ ( v1_tsep_1 @ sk_B @ sk_A )
    | ( v3_pre_topc @ ( u1_struct_0 @ sk_B ) @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['77','79'])).

thf('81',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,
    ( ~ ( v1_tsep_1 @ sk_B @ sk_A )
    | ( v3_pre_topc @ ( u1_struct_0 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['80','81','82'])).

thf('84',plain,
    ( ( v3_pre_topc @ ( u1_struct_0 @ sk_B ) @ sk_A )
   <= ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['76','83'])).

thf('85',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf(d5_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v3_pre_topc @ B @ A )
          <=> ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) ) ) ) )).

thf('86',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( v3_pre_topc @ X17 @ X18 )
      | ( r2_hidden @ X17 @ ( u1_pre_topc @ X18 ) )
      | ~ ( l1_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[d5_pre_topc])).

thf('87',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r2_hidden @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_A ) )
    | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,
    ( ( r2_hidden @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_A ) )
    | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['87','88'])).

thf('90',plain,
    ( ( r2_hidden @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_A ) )
   <= ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['84','89'])).

thf('91',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['3','4'])).

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

thf('92',plain,(
    ! [X42: $i,X43: $i] :
      ( ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X43 ) ) )
      | ~ ( r2_hidden @ X42 @ ( u1_pre_topc @ X43 ) )
      | ( ( u1_pre_topc @ X43 )
        = ( k5_tmap_1 @ X43 @ X42 ) )
      | ~ ( l1_pre_topc @ X43 )
      | ~ ( v2_pre_topc @ X43 )
      | ( v2_struct_0 @ X43 ) ) ),
    inference(cnf,[status(esa)],[t103_tmap_1])).

thf('93',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( ( u1_pre_topc @ sk_A )
      = ( k5_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
    | ~ ( r2_hidden @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( u1_pre_topc @ sk_A )
      = ( k5_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
    | ~ ( r2_hidden @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_A ) ) ),
    inference(demod,[status(thm)],['93','94','95'])).

thf('97',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,
    ( ~ ( r2_hidden @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_A ) )
    | ( ( u1_pre_topc @ sk_A )
      = ( k5_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['96','97'])).

thf('99',plain,
    ( ( ( u1_pre_topc @ sk_A )
      = ( k5_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
   <= ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['90','98'])).

thf('100',plain,
    ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['45','46'])).

thf(abstractness_v1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( ( v1_pre_topc @ A )
       => ( A
          = ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ) )).

thf('101',plain,(
    ! [X14: $i] :
      ( ~ ( v1_pre_topc @ X14 )
      | ( X14
        = ( g1_pre_topc @ ( u1_struct_0 @ X14 ) @ ( u1_pre_topc @ X14 ) ) )
      | ~ ( l1_pre_topc @ X14 ) ) ),
    inference(cnf,[status(esa)],[abstractness_v1_pre_topc])).

thf('102',plain,
    ( ( ( k8_tmap_1 @ sk_A @ sk_B )
      = ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) )
    | ~ ( l1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( v1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['100','101'])).

thf('103',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('104',plain,(
    ! [X44: $i,X45: $i] :
      ( ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X45 ) ) )
      | ( ( u1_pre_topc @ ( k6_tmap_1 @ X45 @ X44 ) )
        = ( k5_tmap_1 @ X45 @ X44 ) )
      | ~ ( l1_pre_topc @ X45 )
      | ~ ( v2_pre_topc @ X45 )
      | ( v2_struct_0 @ X45 ) ) ),
    inference(cnf,[status(esa)],[t104_tmap_1])).

thf('105',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( ( u1_pre_topc @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
      = ( k5_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( u1_pre_topc @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
      = ( k5_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['105','106','107'])).

thf('109',plain,
    ( ( k8_tmap_1 @ sk_A @ sk_B )
    = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['42','43'])).

thf('110',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( u1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
      = ( k5_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['108','109'])).

thf('111',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,
    ( ( u1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    = ( k5_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['110','111'])).

thf('113',plain,(
    l1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['20','21'])).

thf('114',plain,(
    v1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['39','40'])).

thf('115',plain,
    ( ( k8_tmap_1 @ sk_A @ sk_B )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( k5_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['102','112','113','114'])).

thf('116',plain,
    ( ( ( k8_tmap_1 @ sk_A @ sk_B )
      = ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
   <= ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['99','115'])).

thf('117',plain,
    ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
     != ( k8_tmap_1 @ sk_A @ sk_B ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
     != ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['71'])).

thf('118',plain,
    ( ( ( k8_tmap_1 @ sk_A @ sk_B )
     != ( k8_tmap_1 @ sk_A @ sk_B ) )
   <= ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
       != ( k8_tmap_1 @ sk_A @ sk_B ) )
      & ( v1_tsep_1 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['116','117'])).

thf('119',plain,
    ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['118'])).

thf('120',plain,
    ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['54'])).

thf('121',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
    = ( k8_tmap_1 @ sk_A @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['72','75','119','120'])).

thf('122',plain,
    ( ( v1_tsep_1 @ sk_B @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( ( sk_C @ sk_B @ ( k8_tmap_1 @ sk_A @ sk_B ) )
      = ( u1_struct_0 @ sk_B ) ) ),
    inference(simpl_trail,[status(thm)],['70','121'])).

thf(t2_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( m1_pre_topc @ A @ A ) ) )).

thf('123',plain,(
    ! [X62: $i] :
      ( ( m1_pre_topc @ X62 @ X62 )
      | ~ ( l1_pre_topc @ X62 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('124',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( l1_pre_topc @ X29 )
      | ~ ( m1_pre_topc @ X30 @ X29 )
      | ( m1_pre_topc @ X30 @ ( g1_pre_topc @ ( u1_struct_0 @ X29 ) @ ( u1_pre_topc @ X29 ) ) )
      | ~ ( l1_pre_topc @ X30 ) ) ),
    inference(cnf,[status(esa)],[t65_pre_topc])).

thf('125',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['123','124'])).

thf('126',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['125'])).

thf('127',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('128',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_tarski @ X8 @ X9 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('129',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['127','128'])).

thf(t19_tsep_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ( v1_tsep_1 @ B @ A )
            & ( m1_pre_topc @ B @ A ) )
         => ! [C: $i] :
              ( ( ~ ( v2_struct_0 @ C )
                & ( m1_pre_topc @ C @ A ) )
             => ( ( r1_tarski @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ C ) )
               => ( ( v1_tsep_1 @ B @ C )
                  & ( m1_pre_topc @ B @ C ) ) ) ) ) ) )).

thf('130',plain,(
    ! [X57: $i,X58: $i,X59: $i] :
      ( ~ ( v1_tsep_1 @ X57 @ X58 )
      | ~ ( m1_pre_topc @ X57 @ X58 )
      | ~ ( r1_tarski @ ( u1_struct_0 @ X57 ) @ ( u1_struct_0 @ X59 ) )
      | ( v1_tsep_1 @ X57 @ X59 )
      | ~ ( m1_pre_topc @ X59 @ X58 )
      | ( v2_struct_0 @ X59 )
      | ~ ( l1_pre_topc @ X58 )
      | ~ ( v2_pre_topc @ X58 )
      | ( v2_struct_0 @ X58 ) ) ),
    inference(cnf,[status(esa)],[t19_tsep_1])).

thf('131',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( m1_pre_topc @ sk_A @ X0 )
      | ( v1_tsep_1 @ sk_B @ sk_A )
      | ~ ( m1_pre_topc @ sk_B @ X0 )
      | ~ ( v1_tsep_1 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['129','130'])).

thf('132',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v1_tsep_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
    | ~ ( m1_pre_topc @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
    | ( v1_tsep_1 @ sk_B @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
    | ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
    | ( v2_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['126','131'])).

thf('133',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('134',plain,
    ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k8_tmap_1 @ sk_A @ sk_B ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['54'])).

thf('135',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
    = ( k8_tmap_1 @ sk_A @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['72','75','119','120'])).

thf('136',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
    = ( k8_tmap_1 @ sk_A @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['134','135'])).

thf('137',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
    = ( k8_tmap_1 @ sk_A @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['134','135'])).

thf('138',plain,
    ( ( m1_pre_topc @ sk_B @ ( k8_tmap_1 @ sk_A @ sk_B ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['55','65'])).

thf('139',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
    = ( k8_tmap_1 @ sk_A @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['72','75','119','120'])).

thf('140',plain,(
    m1_pre_topc @ sk_B @ ( k8_tmap_1 @ sk_A @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['138','139'])).

thf('141',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
    = ( k8_tmap_1 @ sk_A @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['134','135'])).

thf('142',plain,(
    l1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['20','21'])).

thf('143',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
    = ( k8_tmap_1 @ sk_A @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['134','135'])).

thf('144',plain,(
    v2_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['28','29'])).

thf('145',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
    = ( k8_tmap_1 @ sk_A @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['134','135'])).

thf('146',plain,
    ( ~ ( v1_tsep_1 @ sk_B @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v1_tsep_1 @ sk_B @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['132','133','136','137','140','141','142','143','144','145'])).

thf('147',plain,
    ( ( ( sk_C @ sk_B @ ( k8_tmap_1 @ sk_A @ sk_B ) )
      = ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['122','146'])).

thf('148',plain,(
    ! [X35: $i,X36: $i] :
      ( ~ ( m1_pre_topc @ X35 @ X36 )
      | ~ ( v3_pre_topc @ ( sk_C @ X35 @ X36 ) @ X36 )
      | ( v1_tsep_1 @ X35 @ X36 )
      | ~ ( l1_pre_topc @ X36 ) ) ),
    inference(cnf,[status(esa)],[d1_tsep_1])).

thf('149',plain,
    ( ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v1_tsep_1 @ sk_B @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( l1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v1_tsep_1 @ sk_B @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( m1_pre_topc @ sk_B @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['147','148'])).

thf('150',plain,
    ( ( k8_tmap_1 @ sk_A @ sk_B )
    = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['42','43'])).

thf(t105_tmap_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k6_tmap_1 @ A @ B ) ) ) )
             => ( ( C = B )
               => ( v3_pre_topc @ C @ ( k6_tmap_1 @ A @ B ) ) ) ) ) ) )).

thf('151',plain,(
    ! [X46: $i,X47: $i,X48: $i] :
      ( ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X47 ) ) )
      | ( X48 != X46 )
      | ( v3_pre_topc @ X48 @ ( k6_tmap_1 @ X47 @ X46 ) )
      | ~ ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k6_tmap_1 @ X47 @ X46 ) ) ) )
      | ~ ( l1_pre_topc @ X47 )
      | ~ ( v2_pre_topc @ X47 )
      | ( v2_struct_0 @ X47 ) ) ),
    inference(cnf,[status(esa)],[t105_tmap_1])).

thf('152',plain,(
    ! [X46: $i,X47: $i] :
      ( ( v2_struct_0 @ X47 )
      | ~ ( v2_pre_topc @ X47 )
      | ~ ( l1_pre_topc @ X47 )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k6_tmap_1 @ X47 @ X46 ) ) ) )
      | ( v3_pre_topc @ X46 @ ( k6_tmap_1 @ X47 @ X46 ) )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X47 ) ) ) ) ),
    inference(simplify,[status(thm)],['151'])).

thf('153',plain,
    ( ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) )
    | ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v3_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['150','152'])).

thf('154',plain,
    ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['45','46'])).

thf('155',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('156',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('157',plain,
    ( ( k8_tmap_1 @ sk_A @ sk_B )
    = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['42','43'])).

thf('158',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('159',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('160',plain,
    ( ( v3_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['153','154','155','156','157','158','159'])).

thf('161',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('162',plain,(
    v3_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( k8_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['160','161'])).

thf('163',plain,(
    l1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['20','21'])).

thf('164',plain,(
    m1_pre_topc @ sk_B @ ( k8_tmap_1 @ sk_A @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['138','139'])).

thf('165',plain,
    ( ( v1_tsep_1 @ sk_B @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v1_tsep_1 @ sk_B @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['149','162','163','164'])).

thf('166',plain,
    ( ~ ( v1_tsep_1 @ sk_B @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v1_tsep_1 @ sk_B @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['132','133','136','137','140','141','142','143','144','145'])).

thf('167',plain,
    ( ( v2_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_tsep_1 @ sk_B @ sk_A )
    | ( v2_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['165','166'])).

thf('168',plain,
    ( ( v1_tsep_1 @ sk_B @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['167'])).

thf('169',plain,
    ( ~ ( v1_tsep_1 @ sk_B @ sk_A )
   <= ~ ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['71'])).

thf('170',plain,(
    ~ ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['72','75','119'])).

thf('171',plain,(
    ~ ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['169','170'])).

thf('172',plain,
    ( ( v2_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['168','171'])).

thf('173',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('174',plain,(
    v2_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['172','173'])).

thf('175',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['53','174'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('176',plain,(
    ! [X23: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X23 ) )
      | ~ ( l1_struct_0 @ X23 )
      | ( v2_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('177',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['175','176'])).

thf('178',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('179',plain,(
    ! [X19: $i] :
      ( ( l1_struct_0 @ X19 )
      | ~ ( l1_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('180',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['178','179'])).

thf('181',plain,(
    v2_struct_0 @ sk_A ),
    inference(demod,[status(thm)],['177','180'])).

thf('182',plain,(
    $false ),
    inference(demod,[status(thm)],['0','181'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.pv9Rh4XsqV
% 0.14/0.34  % Computer   : n006.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:21:38 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 7.42/7.63  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 7.42/7.63  % Solved by: fo/fo7.sh
% 7.42/7.63  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 7.42/7.63  % done 4667 iterations in 7.183s
% 7.42/7.63  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 7.42/7.63  % SZS output start Refutation
% 7.42/7.63  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 7.42/7.63  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 7.42/7.63  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 7.42/7.63  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 7.42/7.63  thf(v1_tsep_1_type, type, v1_tsep_1: $i > $i > $o).
% 7.42/7.63  thf(k6_tmap_1_type, type, k6_tmap_1: $i > $i > $i).
% 7.42/7.63  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 7.42/7.63  thf(k5_tmap_1_type, type, k5_tmap_1: $i > $i > $i).
% 7.42/7.63  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 7.42/7.63  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 7.42/7.63  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 7.42/7.63  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 7.42/7.63  thf(k8_tmap_1_type, type, k8_tmap_1: $i > $i > $i).
% 7.42/7.63  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 7.42/7.63  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 7.42/7.63  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 7.42/7.63  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 7.42/7.63  thf(g1_pre_topc_type, type, g1_pre_topc: $i > $i > $i).
% 7.42/7.63  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 7.42/7.63  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 7.42/7.63  thf(sk_A_type, type, sk_A: $i).
% 7.42/7.63  thf(sk_B_type, type, sk_B: $i).
% 7.42/7.63  thf(t116_tmap_1, conjecture,
% 7.42/7.63    (![A:$i]:
% 7.42/7.63     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 7.42/7.63       ( ![B:$i]:
% 7.42/7.63         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 7.42/7.63           ( ( ( v1_tsep_1 @ B @ A ) & ( m1_pre_topc @ B @ A ) ) <=>
% 7.42/7.63             ( ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) =
% 7.42/7.63               ( k8_tmap_1 @ A @ B ) ) ) ) ) ))).
% 7.42/7.63  thf(zf_stmt_0, negated_conjecture,
% 7.42/7.63    (~( ![A:$i]:
% 7.42/7.63        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 7.42/7.63            ( l1_pre_topc @ A ) ) =>
% 7.42/7.63          ( ![B:$i]:
% 7.42/7.63            ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 7.42/7.63              ( ( ( v1_tsep_1 @ B @ A ) & ( m1_pre_topc @ B @ A ) ) <=>
% 7.42/7.63                ( ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) =
% 7.42/7.63                  ( k8_tmap_1 @ A @ B ) ) ) ) ) ) )),
% 7.42/7.63    inference('cnf.neg', [status(esa)], [t116_tmap_1])).
% 7.42/7.63  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 7.42/7.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.42/7.63  thf('1', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 7.42/7.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.42/7.63  thf(t1_tsep_1, axiom,
% 7.42/7.63    (![A:$i]:
% 7.42/7.63     ( ( l1_pre_topc @ A ) =>
% 7.42/7.63       ( ![B:$i]:
% 7.42/7.63         ( ( m1_pre_topc @ B @ A ) =>
% 7.42/7.63           ( m1_subset_1 @
% 7.42/7.63             ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 7.42/7.63  thf('2', plain,
% 7.42/7.63      (![X60 : $i, X61 : $i]:
% 7.42/7.63         (~ (m1_pre_topc @ X60 @ X61)
% 7.42/7.63          | (m1_subset_1 @ (u1_struct_0 @ X60) @ 
% 7.42/7.63             (k1_zfmisc_1 @ (u1_struct_0 @ X61)))
% 7.42/7.63          | ~ (l1_pre_topc @ X61))),
% 7.42/7.63      inference('cnf', [status(esa)], [t1_tsep_1])).
% 7.42/7.63  thf('3', plain,
% 7.42/7.63      ((~ (l1_pre_topc @ sk_A)
% 7.42/7.63        | (m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 7.42/7.63           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 7.42/7.63      inference('sup-', [status(thm)], ['1', '2'])).
% 7.42/7.63  thf('4', plain, ((l1_pre_topc @ sk_A)),
% 7.42/7.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.42/7.63  thf('5', plain,
% 7.42/7.63      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 7.42/7.63        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 7.42/7.63      inference('demod', [status(thm)], ['3', '4'])).
% 7.42/7.63  thf(t104_tmap_1, axiom,
% 7.42/7.63    (![A:$i]:
% 7.42/7.63     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 7.42/7.63       ( ![B:$i]:
% 7.42/7.63         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 7.42/7.63           ( ( ( u1_struct_0 @ ( k6_tmap_1 @ A @ B ) ) = ( u1_struct_0 @ A ) ) & 
% 7.42/7.63             ( ( u1_pre_topc @ ( k6_tmap_1 @ A @ B ) ) = ( k5_tmap_1 @ A @ B ) ) ) ) ) ))).
% 7.42/7.63  thf('6', plain,
% 7.42/7.63      (![X44 : $i, X45 : $i]:
% 7.42/7.63         (~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (u1_struct_0 @ X45)))
% 7.42/7.63          | ((u1_struct_0 @ (k6_tmap_1 @ X45 @ X44)) = (u1_struct_0 @ X45))
% 7.42/7.63          | ~ (l1_pre_topc @ X45)
% 7.42/7.63          | ~ (v2_pre_topc @ X45)
% 7.42/7.63          | (v2_struct_0 @ X45))),
% 7.42/7.63      inference('cnf', [status(esa)], [t104_tmap_1])).
% 7.42/7.63  thf('7', plain,
% 7.42/7.63      (((v2_struct_0 @ sk_A)
% 7.42/7.63        | ~ (v2_pre_topc @ sk_A)
% 7.42/7.63        | ~ (l1_pre_topc @ sk_A)
% 7.42/7.63        | ((u1_struct_0 @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 7.42/7.63            = (u1_struct_0 @ sk_A)))),
% 7.42/7.63      inference('sup-', [status(thm)], ['5', '6'])).
% 7.42/7.63  thf('8', plain, ((v2_pre_topc @ sk_A)),
% 7.42/7.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.42/7.63  thf('9', plain, ((l1_pre_topc @ sk_A)),
% 7.42/7.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.42/7.63  thf('10', plain,
% 7.42/7.63      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 7.42/7.63        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 7.42/7.63      inference('demod', [status(thm)], ['3', '4'])).
% 7.42/7.63  thf(d11_tmap_1, axiom,
% 7.42/7.63    (![A:$i]:
% 7.42/7.63     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 7.42/7.63       ( ![B:$i]:
% 7.42/7.63         ( ( m1_pre_topc @ B @ A ) =>
% 7.42/7.63           ( ![C:$i]:
% 7.42/7.63             ( ( ( v1_pre_topc @ C ) & ( v2_pre_topc @ C ) & 
% 7.42/7.63                 ( l1_pre_topc @ C ) ) =>
% 7.42/7.63               ( ( ( C ) = ( k8_tmap_1 @ A @ B ) ) <=>
% 7.42/7.63                 ( ![D:$i]:
% 7.42/7.63                   ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 7.42/7.63                     ( ( ( D ) = ( u1_struct_0 @ B ) ) =>
% 7.42/7.63                       ( ( C ) = ( k6_tmap_1 @ A @ D ) ) ) ) ) ) ) ) ) ) ))).
% 7.42/7.63  thf('11', plain,
% 7.42/7.63      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 7.42/7.63         (~ (m1_pre_topc @ X31 @ X32)
% 7.42/7.63          | ((X33) != (k8_tmap_1 @ X32 @ X31))
% 7.42/7.63          | ((X34) != (u1_struct_0 @ X31))
% 7.42/7.63          | ((X33) = (k6_tmap_1 @ X32 @ X34))
% 7.42/7.63          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (u1_struct_0 @ X32)))
% 7.42/7.63          | ~ (l1_pre_topc @ X33)
% 7.42/7.63          | ~ (v2_pre_topc @ X33)
% 7.42/7.63          | ~ (v1_pre_topc @ X33)
% 7.42/7.63          | ~ (l1_pre_topc @ X32)
% 7.42/7.63          | ~ (v2_pre_topc @ X32)
% 7.42/7.63          | (v2_struct_0 @ X32))),
% 7.42/7.63      inference('cnf', [status(esa)], [d11_tmap_1])).
% 7.42/7.63  thf('12', plain,
% 7.42/7.63      (![X31 : $i, X32 : $i]:
% 7.42/7.63         ((v2_struct_0 @ X32)
% 7.42/7.63          | ~ (v2_pre_topc @ X32)
% 7.42/7.63          | ~ (l1_pre_topc @ X32)
% 7.42/7.63          | ~ (v1_pre_topc @ (k8_tmap_1 @ X32 @ X31))
% 7.42/7.63          | ~ (v2_pre_topc @ (k8_tmap_1 @ X32 @ X31))
% 7.42/7.63          | ~ (l1_pre_topc @ (k8_tmap_1 @ X32 @ X31))
% 7.42/7.63          | ~ (m1_subset_1 @ (u1_struct_0 @ X31) @ 
% 7.42/7.63               (k1_zfmisc_1 @ (u1_struct_0 @ X32)))
% 7.42/7.63          | ((k8_tmap_1 @ X32 @ X31) = (k6_tmap_1 @ X32 @ (u1_struct_0 @ X31)))
% 7.42/7.63          | ~ (m1_pre_topc @ X31 @ X32))),
% 7.42/7.63      inference('simplify', [status(thm)], ['11'])).
% 7.42/7.63  thf('13', plain,
% 7.42/7.63      ((~ (m1_pre_topc @ sk_B @ sk_A)
% 7.42/7.63        | ((k8_tmap_1 @ sk_A @ sk_B)
% 7.42/7.63            = (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 7.42/7.63        | ~ (l1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 7.42/7.63        | ~ (v2_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 7.42/7.63        | ~ (v1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 7.42/7.63        | ~ (l1_pre_topc @ sk_A)
% 7.42/7.63        | ~ (v2_pre_topc @ sk_A)
% 7.42/7.63        | (v2_struct_0 @ sk_A))),
% 7.42/7.63      inference('sup-', [status(thm)], ['10', '12'])).
% 7.42/7.63  thf('14', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 7.42/7.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.42/7.63  thf('15', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 7.42/7.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.42/7.63  thf(dt_k8_tmap_1, axiom,
% 7.42/7.63    (![A:$i,B:$i]:
% 7.42/7.63     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 7.42/7.63         ( l1_pre_topc @ A ) & ( m1_pre_topc @ B @ A ) ) =>
% 7.42/7.63       ( ( v1_pre_topc @ ( k8_tmap_1 @ A @ B ) ) & 
% 7.42/7.63         ( v2_pre_topc @ ( k8_tmap_1 @ A @ B ) ) & 
% 7.42/7.63         ( l1_pre_topc @ ( k8_tmap_1 @ A @ B ) ) ) ))).
% 7.42/7.63  thf('16', plain,
% 7.42/7.63      (![X40 : $i, X41 : $i]:
% 7.42/7.63         (~ (l1_pre_topc @ X40)
% 7.42/7.63          | ~ (v2_pre_topc @ X40)
% 7.42/7.63          | (v2_struct_0 @ X40)
% 7.42/7.63          | ~ (m1_pre_topc @ X41 @ X40)
% 7.42/7.63          | (l1_pre_topc @ (k8_tmap_1 @ X40 @ X41)))),
% 7.42/7.63      inference('cnf', [status(esa)], [dt_k8_tmap_1])).
% 7.42/7.63  thf('17', plain,
% 7.42/7.63      (((l1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 7.42/7.63        | (v2_struct_0 @ sk_A)
% 7.42/7.63        | ~ (v2_pre_topc @ sk_A)
% 7.42/7.63        | ~ (l1_pre_topc @ sk_A))),
% 7.42/7.63      inference('sup-', [status(thm)], ['15', '16'])).
% 7.42/7.63  thf('18', plain, ((v2_pre_topc @ sk_A)),
% 7.42/7.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.42/7.63  thf('19', plain, ((l1_pre_topc @ sk_A)),
% 7.42/7.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.42/7.63  thf('20', plain,
% 7.42/7.63      (((l1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B)) | (v2_struct_0 @ sk_A))),
% 7.42/7.63      inference('demod', [status(thm)], ['17', '18', '19'])).
% 7.42/7.63  thf('21', plain, (~ (v2_struct_0 @ sk_A)),
% 7.42/7.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.42/7.63  thf('22', plain, ((l1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))),
% 7.42/7.63      inference('clc', [status(thm)], ['20', '21'])).
% 7.42/7.63  thf('23', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 7.42/7.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.42/7.63  thf('24', plain,
% 7.42/7.63      (![X40 : $i, X41 : $i]:
% 7.42/7.63         (~ (l1_pre_topc @ X40)
% 7.42/7.63          | ~ (v2_pre_topc @ X40)
% 7.42/7.63          | (v2_struct_0 @ X40)
% 7.42/7.63          | ~ (m1_pre_topc @ X41 @ X40)
% 7.42/7.63          | (v2_pre_topc @ (k8_tmap_1 @ X40 @ X41)))),
% 7.42/7.63      inference('cnf', [status(esa)], [dt_k8_tmap_1])).
% 7.42/7.63  thf('25', plain,
% 7.42/7.63      (((v2_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 7.42/7.63        | (v2_struct_0 @ sk_A)
% 7.42/7.63        | ~ (v2_pre_topc @ sk_A)
% 7.42/7.63        | ~ (l1_pre_topc @ sk_A))),
% 7.42/7.63      inference('sup-', [status(thm)], ['23', '24'])).
% 7.42/7.63  thf('26', plain, ((v2_pre_topc @ sk_A)),
% 7.42/7.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.42/7.63  thf('27', plain, ((l1_pre_topc @ sk_A)),
% 7.42/7.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.42/7.63  thf('28', plain,
% 7.42/7.63      (((v2_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B)) | (v2_struct_0 @ sk_A))),
% 7.42/7.63      inference('demod', [status(thm)], ['25', '26', '27'])).
% 7.42/7.63  thf('29', plain, (~ (v2_struct_0 @ sk_A)),
% 7.42/7.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.42/7.63  thf('30', plain, ((v2_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))),
% 7.42/7.63      inference('clc', [status(thm)], ['28', '29'])).
% 7.42/7.63  thf('31', plain, ((l1_pre_topc @ sk_A)),
% 7.42/7.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.42/7.63  thf('32', plain, ((v2_pre_topc @ sk_A)),
% 7.42/7.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.42/7.63  thf('33', plain,
% 7.42/7.63      ((((k8_tmap_1 @ sk_A @ sk_B) = (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 7.42/7.63        | ~ (v1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 7.42/7.63        | (v2_struct_0 @ sk_A))),
% 7.42/7.63      inference('demod', [status(thm)], ['13', '14', '22', '30', '31', '32'])).
% 7.42/7.63  thf('34', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 7.42/7.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.42/7.63  thf('35', plain,
% 7.42/7.63      (![X40 : $i, X41 : $i]:
% 7.42/7.63         (~ (l1_pre_topc @ X40)
% 7.42/7.63          | ~ (v2_pre_topc @ X40)
% 7.42/7.63          | (v2_struct_0 @ X40)
% 7.42/7.63          | ~ (m1_pre_topc @ X41 @ X40)
% 7.42/7.63          | (v1_pre_topc @ (k8_tmap_1 @ X40 @ X41)))),
% 7.42/7.63      inference('cnf', [status(esa)], [dt_k8_tmap_1])).
% 7.42/7.63  thf('36', plain,
% 7.42/7.63      (((v1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 7.42/7.63        | (v2_struct_0 @ sk_A)
% 7.42/7.63        | ~ (v2_pre_topc @ sk_A)
% 7.42/7.63        | ~ (l1_pre_topc @ sk_A))),
% 7.42/7.63      inference('sup-', [status(thm)], ['34', '35'])).
% 7.42/7.63  thf('37', plain, ((v2_pre_topc @ sk_A)),
% 7.42/7.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.42/7.63  thf('38', plain, ((l1_pre_topc @ sk_A)),
% 7.42/7.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.42/7.63  thf('39', plain,
% 7.42/7.63      (((v1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B)) | (v2_struct_0 @ sk_A))),
% 7.42/7.63      inference('demod', [status(thm)], ['36', '37', '38'])).
% 7.42/7.63  thf('40', plain, (~ (v2_struct_0 @ sk_A)),
% 7.42/7.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.42/7.63  thf('41', plain, ((v1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))),
% 7.42/7.63      inference('clc', [status(thm)], ['39', '40'])).
% 7.42/7.63  thf('42', plain,
% 7.42/7.63      ((((k8_tmap_1 @ sk_A @ sk_B) = (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 7.42/7.63        | (v2_struct_0 @ sk_A))),
% 7.42/7.63      inference('demod', [status(thm)], ['33', '41'])).
% 7.42/7.63  thf('43', plain, (~ (v2_struct_0 @ sk_A)),
% 7.42/7.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.42/7.63  thf('44', plain,
% 7.42/7.63      (((k8_tmap_1 @ sk_A @ sk_B) = (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))),
% 7.42/7.63      inference('clc', [status(thm)], ['42', '43'])).
% 7.42/7.63  thf('45', plain,
% 7.42/7.63      (((v2_struct_0 @ sk_A)
% 7.42/7.63        | ((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A)))),
% 7.42/7.63      inference('demod', [status(thm)], ['7', '8', '9', '44'])).
% 7.42/7.63  thf('46', plain, (~ (v2_struct_0 @ sk_A)),
% 7.42/7.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.42/7.63  thf('47', plain,
% 7.42/7.63      (((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 7.42/7.63      inference('clc', [status(thm)], ['45', '46'])).
% 7.42/7.63  thf(fc1_struct_0, axiom,
% 7.42/7.63    (![A:$i]:
% 7.42/7.63     ( ( ( v2_struct_0 @ A ) & ( l1_struct_0 @ A ) ) =>
% 7.42/7.63       ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ))).
% 7.42/7.63  thf('48', plain,
% 7.42/7.63      (![X22 : $i]:
% 7.42/7.63         ((v1_xboole_0 @ (u1_struct_0 @ X22))
% 7.42/7.63          | ~ (l1_struct_0 @ X22)
% 7.42/7.63          | ~ (v2_struct_0 @ X22))),
% 7.42/7.63      inference('cnf', [status(esa)], [fc1_struct_0])).
% 7.42/7.63  thf('49', plain,
% 7.42/7.63      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 7.42/7.63        | ~ (v2_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B))
% 7.42/7.63        | ~ (l1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))),
% 7.42/7.63      inference('sup+', [status(thm)], ['47', '48'])).
% 7.42/7.63  thf('50', plain, ((l1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))),
% 7.42/7.63      inference('clc', [status(thm)], ['20', '21'])).
% 7.42/7.63  thf(dt_l1_pre_topc, axiom,
% 7.42/7.63    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 7.42/7.63  thf('51', plain,
% 7.42/7.63      (![X19 : $i]: ((l1_struct_0 @ X19) | ~ (l1_pre_topc @ X19))),
% 7.42/7.63      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 7.42/7.63  thf('52', plain, ((l1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B))),
% 7.42/7.63      inference('sup-', [status(thm)], ['50', '51'])).
% 7.42/7.63  thf('53', plain,
% 7.42/7.63      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 7.42/7.63        | ~ (v2_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))),
% 7.42/7.63      inference('demod', [status(thm)], ['49', '52'])).
% 7.42/7.63  thf('54', plain,
% 7.42/7.63      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 7.42/7.63          = (k8_tmap_1 @ sk_A @ sk_B))
% 7.42/7.63        | (v1_tsep_1 @ sk_B @ sk_A))),
% 7.42/7.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.42/7.63  thf('55', plain,
% 7.42/7.63      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 7.42/7.63          = (k8_tmap_1 @ sk_A @ sk_B)))
% 7.42/7.63         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 7.42/7.63                = (k8_tmap_1 @ sk_A @ sk_B))))),
% 7.42/7.63      inference('split', [status(esa)], ['54'])).
% 7.42/7.63  thf('56', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 7.42/7.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.42/7.63  thf(t65_pre_topc, axiom,
% 7.42/7.63    (![A:$i]:
% 7.42/7.63     ( ( l1_pre_topc @ A ) =>
% 7.42/7.63       ( ![B:$i]:
% 7.42/7.63         ( ( l1_pre_topc @ B ) =>
% 7.42/7.63           ( ( m1_pre_topc @ A @ B ) <=>
% 7.42/7.63             ( m1_pre_topc @
% 7.42/7.63               A @ ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ) ))).
% 7.42/7.63  thf('57', plain,
% 7.42/7.63      (![X29 : $i, X30 : $i]:
% 7.42/7.63         (~ (l1_pre_topc @ X29)
% 7.42/7.63          | ~ (m1_pre_topc @ X30 @ X29)
% 7.42/7.63          | (m1_pre_topc @ X30 @ 
% 7.42/7.63             (g1_pre_topc @ (u1_struct_0 @ X29) @ (u1_pre_topc @ X29)))
% 7.42/7.63          | ~ (l1_pre_topc @ X30))),
% 7.42/7.63      inference('cnf', [status(esa)], [t65_pre_topc])).
% 7.42/7.63  thf('58', plain,
% 7.42/7.63      ((~ (l1_pre_topc @ sk_B)
% 7.42/7.63        | (m1_pre_topc @ sk_B @ 
% 7.42/7.63           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 7.42/7.63        | ~ (l1_pre_topc @ sk_A))),
% 7.42/7.63      inference('sup-', [status(thm)], ['56', '57'])).
% 7.42/7.63  thf('59', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 7.42/7.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.42/7.63  thf(dt_m1_pre_topc, axiom,
% 7.42/7.63    (![A:$i]:
% 7.42/7.63     ( ( l1_pre_topc @ A ) =>
% 7.42/7.63       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 7.42/7.63  thf('60', plain,
% 7.42/7.63      (![X20 : $i, X21 : $i]:
% 7.42/7.63         (~ (m1_pre_topc @ X20 @ X21)
% 7.42/7.63          | (l1_pre_topc @ X20)
% 7.42/7.63          | ~ (l1_pre_topc @ X21))),
% 7.42/7.63      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 7.42/7.63  thf('61', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_B))),
% 7.42/7.63      inference('sup-', [status(thm)], ['59', '60'])).
% 7.42/7.63  thf('62', plain, ((l1_pre_topc @ sk_A)),
% 7.42/7.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.42/7.63  thf('63', plain, ((l1_pre_topc @ sk_B)),
% 7.42/7.63      inference('demod', [status(thm)], ['61', '62'])).
% 7.42/7.63  thf('64', plain, ((l1_pre_topc @ sk_A)),
% 7.42/7.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.42/7.64  thf('65', plain,
% 7.42/7.64      ((m1_pre_topc @ sk_B @ 
% 7.42/7.64        (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))),
% 7.42/7.64      inference('demod', [status(thm)], ['58', '63', '64'])).
% 7.42/7.64  thf('66', plain,
% 7.42/7.64      (((m1_pre_topc @ sk_B @ (k8_tmap_1 @ sk_A @ sk_B)))
% 7.42/7.64         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 7.42/7.64                = (k8_tmap_1 @ sk_A @ sk_B))))),
% 7.42/7.64      inference('sup+', [status(thm)], ['55', '65'])).
% 7.42/7.64  thf(d1_tsep_1, axiom,
% 7.42/7.64    (![A:$i]:
% 7.42/7.64     ( ( l1_pre_topc @ A ) =>
% 7.42/7.64       ( ![B:$i]:
% 7.42/7.64         ( ( m1_pre_topc @ B @ A ) =>
% 7.42/7.64           ( ( v1_tsep_1 @ B @ A ) <=>
% 7.42/7.64             ( ![C:$i]:
% 7.42/7.64               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 7.42/7.64                 ( ( ( C ) = ( u1_struct_0 @ B ) ) => ( v3_pre_topc @ C @ A ) ) ) ) ) ) ) ))).
% 7.42/7.64  thf('67', plain,
% 7.42/7.64      (![X35 : $i, X36 : $i]:
% 7.42/7.64         (~ (m1_pre_topc @ X35 @ X36)
% 7.42/7.64          | ((sk_C @ X35 @ X36) = (u1_struct_0 @ X35))
% 7.42/7.64          | (v1_tsep_1 @ X35 @ X36)
% 7.42/7.64          | ~ (l1_pre_topc @ X36))),
% 7.42/7.64      inference('cnf', [status(esa)], [d1_tsep_1])).
% 7.42/7.64  thf('68', plain,
% 7.42/7.64      (((~ (l1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 7.42/7.64         | (v1_tsep_1 @ sk_B @ (k8_tmap_1 @ sk_A @ sk_B))
% 7.42/7.64         | ((sk_C @ sk_B @ (k8_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_B))))
% 7.42/7.64         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 7.42/7.64                = (k8_tmap_1 @ sk_A @ sk_B))))),
% 7.42/7.64      inference('sup-', [status(thm)], ['66', '67'])).
% 7.42/7.64  thf('69', plain, ((l1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))),
% 7.42/7.64      inference('clc', [status(thm)], ['20', '21'])).
% 7.42/7.64  thf('70', plain,
% 7.42/7.64      ((((v1_tsep_1 @ sk_B @ (k8_tmap_1 @ sk_A @ sk_B))
% 7.42/7.64         | ((sk_C @ sk_B @ (k8_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_B))))
% 7.42/7.64         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 7.42/7.64                = (k8_tmap_1 @ sk_A @ sk_B))))),
% 7.42/7.64      inference('demod', [status(thm)], ['68', '69'])).
% 7.42/7.64  thf('71', plain,
% 7.42/7.64      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 7.42/7.64          != (k8_tmap_1 @ sk_A @ sk_B))
% 7.42/7.64        | ~ (m1_pre_topc @ sk_B @ sk_A)
% 7.42/7.64        | ~ (v1_tsep_1 @ sk_B @ sk_A))),
% 7.42/7.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.42/7.64  thf('72', plain,
% 7.42/7.64      (~ ((v1_tsep_1 @ sk_B @ sk_A)) | 
% 7.42/7.64       ~
% 7.42/7.64       (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 7.42/7.64          = (k8_tmap_1 @ sk_A @ sk_B))) | 
% 7.42/7.64       ~ ((m1_pre_topc @ sk_B @ sk_A))),
% 7.42/7.64      inference('split', [status(esa)], ['71'])).
% 7.42/7.64  thf('73', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 7.42/7.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.42/7.64  thf('74', plain,
% 7.42/7.64      ((~ (m1_pre_topc @ sk_B @ sk_A)) <= (~ ((m1_pre_topc @ sk_B @ sk_A)))),
% 7.42/7.64      inference('split', [status(esa)], ['71'])).
% 7.42/7.64  thf('75', plain, (((m1_pre_topc @ sk_B @ sk_A))),
% 7.42/7.64      inference('sup-', [status(thm)], ['73', '74'])).
% 7.42/7.64  thf('76', plain,
% 7.42/7.64      (((v1_tsep_1 @ sk_B @ sk_A)) <= (((v1_tsep_1 @ sk_B @ sk_A)))),
% 7.42/7.64      inference('split', [status(esa)], ['54'])).
% 7.42/7.64  thf('77', plain,
% 7.42/7.64      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 7.42/7.64        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 7.42/7.64      inference('demod', [status(thm)], ['3', '4'])).
% 7.42/7.64  thf('78', plain,
% 7.42/7.64      (![X35 : $i, X36 : $i, X37 : $i]:
% 7.42/7.64         (~ (m1_pre_topc @ X35 @ X36)
% 7.42/7.64          | ~ (v1_tsep_1 @ X35 @ X36)
% 7.42/7.64          | ((X37) != (u1_struct_0 @ X35))
% 7.42/7.64          | (v3_pre_topc @ X37 @ X36)
% 7.42/7.64          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (u1_struct_0 @ X36)))
% 7.42/7.64          | ~ (l1_pre_topc @ X36))),
% 7.42/7.64      inference('cnf', [status(esa)], [d1_tsep_1])).
% 7.42/7.64  thf('79', plain,
% 7.42/7.64      (![X35 : $i, X36 : $i]:
% 7.42/7.64         (~ (l1_pre_topc @ X36)
% 7.42/7.64          | ~ (m1_subset_1 @ (u1_struct_0 @ X35) @ 
% 7.42/7.64               (k1_zfmisc_1 @ (u1_struct_0 @ X36)))
% 7.42/7.64          | (v3_pre_topc @ (u1_struct_0 @ X35) @ X36)
% 7.42/7.64          | ~ (v1_tsep_1 @ X35 @ X36)
% 7.42/7.64          | ~ (m1_pre_topc @ X35 @ X36))),
% 7.42/7.64      inference('simplify', [status(thm)], ['78'])).
% 7.42/7.64  thf('80', plain,
% 7.42/7.64      ((~ (m1_pre_topc @ sk_B @ sk_A)
% 7.42/7.64        | ~ (v1_tsep_1 @ sk_B @ sk_A)
% 7.42/7.64        | (v3_pre_topc @ (u1_struct_0 @ sk_B) @ sk_A)
% 7.42/7.64        | ~ (l1_pre_topc @ sk_A))),
% 7.42/7.64      inference('sup-', [status(thm)], ['77', '79'])).
% 7.42/7.64  thf('81', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 7.42/7.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.42/7.64  thf('82', plain, ((l1_pre_topc @ sk_A)),
% 7.42/7.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.42/7.64  thf('83', plain,
% 7.42/7.64      ((~ (v1_tsep_1 @ sk_B @ sk_A)
% 7.42/7.64        | (v3_pre_topc @ (u1_struct_0 @ sk_B) @ sk_A))),
% 7.42/7.64      inference('demod', [status(thm)], ['80', '81', '82'])).
% 7.42/7.64  thf('84', plain,
% 7.42/7.64      (((v3_pre_topc @ (u1_struct_0 @ sk_B) @ sk_A))
% 7.42/7.64         <= (((v1_tsep_1 @ sk_B @ sk_A)))),
% 7.42/7.64      inference('sup-', [status(thm)], ['76', '83'])).
% 7.42/7.64  thf('85', plain,
% 7.42/7.64      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 7.42/7.64        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 7.42/7.64      inference('demod', [status(thm)], ['3', '4'])).
% 7.42/7.64  thf(d5_pre_topc, axiom,
% 7.42/7.64    (![A:$i]:
% 7.42/7.64     ( ( l1_pre_topc @ A ) =>
% 7.42/7.64       ( ![B:$i]:
% 7.42/7.64         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 7.42/7.64           ( ( v3_pre_topc @ B @ A ) <=>
% 7.42/7.64             ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) ) ) ) ))).
% 7.42/7.64  thf('86', plain,
% 7.42/7.64      (![X17 : $i, X18 : $i]:
% 7.42/7.64         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 7.42/7.64          | ~ (v3_pre_topc @ X17 @ X18)
% 7.42/7.64          | (r2_hidden @ X17 @ (u1_pre_topc @ X18))
% 7.42/7.64          | ~ (l1_pre_topc @ X18))),
% 7.42/7.64      inference('cnf', [status(esa)], [d5_pre_topc])).
% 7.42/7.64  thf('87', plain,
% 7.42/7.64      ((~ (l1_pre_topc @ sk_A)
% 7.42/7.64        | (r2_hidden @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_A))
% 7.42/7.64        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_B) @ sk_A))),
% 7.42/7.64      inference('sup-', [status(thm)], ['85', '86'])).
% 7.42/7.64  thf('88', plain, ((l1_pre_topc @ sk_A)),
% 7.42/7.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.42/7.64  thf('89', plain,
% 7.42/7.64      (((r2_hidden @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_A))
% 7.42/7.64        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_B) @ sk_A))),
% 7.42/7.64      inference('demod', [status(thm)], ['87', '88'])).
% 7.42/7.64  thf('90', plain,
% 7.42/7.64      (((r2_hidden @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_A)))
% 7.42/7.64         <= (((v1_tsep_1 @ sk_B @ sk_A)))),
% 7.42/7.64      inference('sup-', [status(thm)], ['84', '89'])).
% 7.42/7.64  thf('91', plain,
% 7.42/7.64      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 7.42/7.64        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 7.42/7.64      inference('demod', [status(thm)], ['3', '4'])).
% 7.42/7.64  thf(t103_tmap_1, axiom,
% 7.42/7.64    (![A:$i]:
% 7.42/7.64     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 7.42/7.64       ( ![B:$i]:
% 7.42/7.64         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 7.42/7.64           ( ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) <=>
% 7.42/7.64             ( ( u1_pre_topc @ A ) = ( k5_tmap_1 @ A @ B ) ) ) ) ) ))).
% 7.42/7.64  thf('92', plain,
% 7.42/7.64      (![X42 : $i, X43 : $i]:
% 7.42/7.64         (~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (u1_struct_0 @ X43)))
% 7.42/7.64          | ~ (r2_hidden @ X42 @ (u1_pre_topc @ X43))
% 7.42/7.64          | ((u1_pre_topc @ X43) = (k5_tmap_1 @ X43 @ X42))
% 7.42/7.64          | ~ (l1_pre_topc @ X43)
% 7.42/7.64          | ~ (v2_pre_topc @ X43)
% 7.42/7.64          | (v2_struct_0 @ X43))),
% 7.42/7.64      inference('cnf', [status(esa)], [t103_tmap_1])).
% 7.42/7.64  thf('93', plain,
% 7.42/7.64      (((v2_struct_0 @ sk_A)
% 7.42/7.64        | ~ (v2_pre_topc @ sk_A)
% 7.42/7.64        | ~ (l1_pre_topc @ sk_A)
% 7.42/7.64        | ((u1_pre_topc @ sk_A) = (k5_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 7.42/7.64        | ~ (r2_hidden @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_A)))),
% 7.42/7.64      inference('sup-', [status(thm)], ['91', '92'])).
% 7.42/7.64  thf('94', plain, ((v2_pre_topc @ sk_A)),
% 7.42/7.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.42/7.64  thf('95', plain, ((l1_pre_topc @ sk_A)),
% 7.42/7.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.42/7.64  thf('96', plain,
% 7.42/7.64      (((v2_struct_0 @ sk_A)
% 7.42/7.64        | ((u1_pre_topc @ sk_A) = (k5_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 7.42/7.64        | ~ (r2_hidden @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_A)))),
% 7.42/7.64      inference('demod', [status(thm)], ['93', '94', '95'])).
% 7.42/7.64  thf('97', plain, (~ (v2_struct_0 @ sk_A)),
% 7.42/7.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.42/7.64  thf('98', plain,
% 7.42/7.64      ((~ (r2_hidden @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_A))
% 7.42/7.64        | ((u1_pre_topc @ sk_A) = (k5_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B))))),
% 7.42/7.64      inference('clc', [status(thm)], ['96', '97'])).
% 7.42/7.64  thf('99', plain,
% 7.42/7.64      ((((u1_pre_topc @ sk_A) = (k5_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B))))
% 7.42/7.64         <= (((v1_tsep_1 @ sk_B @ sk_A)))),
% 7.42/7.64      inference('sup-', [status(thm)], ['90', '98'])).
% 7.42/7.64  thf('100', plain,
% 7.42/7.64      (((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 7.42/7.64      inference('clc', [status(thm)], ['45', '46'])).
% 7.42/7.64  thf(abstractness_v1_pre_topc, axiom,
% 7.42/7.64    (![A:$i]:
% 7.42/7.64     ( ( l1_pre_topc @ A ) =>
% 7.42/7.64       ( ( v1_pre_topc @ A ) =>
% 7.42/7.64         ( ( A ) = ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ))).
% 7.42/7.64  thf('101', plain,
% 7.42/7.64      (![X14 : $i]:
% 7.42/7.64         (~ (v1_pre_topc @ X14)
% 7.42/7.64          | ((X14) = (g1_pre_topc @ (u1_struct_0 @ X14) @ (u1_pre_topc @ X14)))
% 7.42/7.64          | ~ (l1_pre_topc @ X14))),
% 7.42/7.64      inference('cnf', [status(esa)], [abstractness_v1_pre_topc])).
% 7.42/7.64  thf('102', plain,
% 7.42/7.64      ((((k8_tmap_1 @ sk_A @ sk_B)
% 7.42/7.64          = (g1_pre_topc @ (u1_struct_0 @ sk_A) @ 
% 7.42/7.64             (u1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))))
% 7.42/7.64        | ~ (l1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 7.42/7.64        | ~ (v1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B)))),
% 7.42/7.64      inference('sup+', [status(thm)], ['100', '101'])).
% 7.42/7.64  thf('103', plain,
% 7.42/7.64      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 7.42/7.64        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 7.42/7.64      inference('demod', [status(thm)], ['3', '4'])).
% 7.42/7.64  thf('104', plain,
% 7.42/7.64      (![X44 : $i, X45 : $i]:
% 7.42/7.64         (~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (u1_struct_0 @ X45)))
% 7.42/7.64          | ((u1_pre_topc @ (k6_tmap_1 @ X45 @ X44)) = (k5_tmap_1 @ X45 @ X44))
% 7.42/7.64          | ~ (l1_pre_topc @ X45)
% 7.42/7.64          | ~ (v2_pre_topc @ X45)
% 7.42/7.64          | (v2_struct_0 @ X45))),
% 7.42/7.64      inference('cnf', [status(esa)], [t104_tmap_1])).
% 7.42/7.64  thf('105', plain,
% 7.42/7.64      (((v2_struct_0 @ sk_A)
% 7.42/7.64        | ~ (v2_pre_topc @ sk_A)
% 7.42/7.64        | ~ (l1_pre_topc @ sk_A)
% 7.42/7.64        | ((u1_pre_topc @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 7.42/7.64            = (k5_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B))))),
% 7.42/7.64      inference('sup-', [status(thm)], ['103', '104'])).
% 7.42/7.64  thf('106', plain, ((v2_pre_topc @ sk_A)),
% 7.42/7.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.42/7.64  thf('107', plain, ((l1_pre_topc @ sk_A)),
% 7.42/7.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.42/7.64  thf('108', plain,
% 7.42/7.64      (((v2_struct_0 @ sk_A)
% 7.42/7.64        | ((u1_pre_topc @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 7.42/7.64            = (k5_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B))))),
% 7.42/7.64      inference('demod', [status(thm)], ['105', '106', '107'])).
% 7.42/7.64  thf('109', plain,
% 7.42/7.64      (((k8_tmap_1 @ sk_A @ sk_B) = (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))),
% 7.42/7.64      inference('clc', [status(thm)], ['42', '43'])).
% 7.42/7.64  thf('110', plain,
% 7.42/7.64      (((v2_struct_0 @ sk_A)
% 7.42/7.64        | ((u1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 7.42/7.64            = (k5_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B))))),
% 7.42/7.64      inference('demod', [status(thm)], ['108', '109'])).
% 7.42/7.64  thf('111', plain, (~ (v2_struct_0 @ sk_A)),
% 7.42/7.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.42/7.64  thf('112', plain,
% 7.42/7.64      (((u1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 7.42/7.64         = (k5_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))),
% 7.42/7.64      inference('clc', [status(thm)], ['110', '111'])).
% 7.42/7.64  thf('113', plain, ((l1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))),
% 7.42/7.64      inference('clc', [status(thm)], ['20', '21'])).
% 7.42/7.64  thf('114', plain, ((v1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))),
% 7.42/7.64      inference('clc', [status(thm)], ['39', '40'])).
% 7.42/7.64  thf('115', plain,
% 7.42/7.64      (((k8_tmap_1 @ sk_A @ sk_B)
% 7.42/7.64         = (g1_pre_topc @ (u1_struct_0 @ sk_A) @ 
% 7.42/7.64            (k5_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B))))),
% 7.42/7.64      inference('demod', [status(thm)], ['102', '112', '113', '114'])).
% 7.42/7.64  thf('116', plain,
% 7.42/7.64      ((((k8_tmap_1 @ sk_A @ sk_B)
% 7.42/7.64          = (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))
% 7.42/7.64         <= (((v1_tsep_1 @ sk_B @ sk_A)))),
% 7.42/7.64      inference('sup+', [status(thm)], ['99', '115'])).
% 7.42/7.64  thf('117', plain,
% 7.42/7.64      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 7.42/7.64          != (k8_tmap_1 @ sk_A @ sk_B)))
% 7.42/7.64         <= (~
% 7.42/7.64             (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 7.42/7.64                = (k8_tmap_1 @ sk_A @ sk_B))))),
% 7.42/7.64      inference('split', [status(esa)], ['71'])).
% 7.42/7.64  thf('118', plain,
% 7.42/7.64      ((((k8_tmap_1 @ sk_A @ sk_B) != (k8_tmap_1 @ sk_A @ sk_B)))
% 7.42/7.64         <= (~
% 7.42/7.64             (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 7.42/7.64                = (k8_tmap_1 @ sk_A @ sk_B))) & 
% 7.42/7.64             ((v1_tsep_1 @ sk_B @ sk_A)))),
% 7.42/7.64      inference('sup-', [status(thm)], ['116', '117'])).
% 7.42/7.64  thf('119', plain,
% 7.42/7.64      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 7.42/7.64          = (k8_tmap_1 @ sk_A @ sk_B))) | 
% 7.42/7.64       ~ ((v1_tsep_1 @ sk_B @ sk_A))),
% 7.42/7.64      inference('simplify', [status(thm)], ['118'])).
% 7.42/7.64  thf('120', plain,
% 7.42/7.64      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 7.42/7.64          = (k8_tmap_1 @ sk_A @ sk_B))) | 
% 7.42/7.64       ((v1_tsep_1 @ sk_B @ sk_A))),
% 7.42/7.64      inference('split', [status(esa)], ['54'])).
% 7.42/7.64  thf('121', plain,
% 7.42/7.64      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 7.42/7.64          = (k8_tmap_1 @ sk_A @ sk_B)))),
% 7.42/7.64      inference('sat_resolution*', [status(thm)], ['72', '75', '119', '120'])).
% 7.42/7.64  thf('122', plain,
% 7.42/7.64      (((v1_tsep_1 @ sk_B @ (k8_tmap_1 @ sk_A @ sk_B))
% 7.42/7.64        | ((sk_C @ sk_B @ (k8_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_B)))),
% 7.42/7.64      inference('simpl_trail', [status(thm)], ['70', '121'])).
% 7.42/7.64  thf(t2_tsep_1, axiom,
% 7.42/7.64    (![A:$i]: ( ( l1_pre_topc @ A ) => ( m1_pre_topc @ A @ A ) ))).
% 7.42/7.64  thf('123', plain,
% 7.42/7.64      (![X62 : $i]: ((m1_pre_topc @ X62 @ X62) | ~ (l1_pre_topc @ X62))),
% 7.42/7.64      inference('cnf', [status(esa)], [t2_tsep_1])).
% 7.42/7.64  thf('124', plain,
% 7.42/7.64      (![X29 : $i, X30 : $i]:
% 7.42/7.64         (~ (l1_pre_topc @ X29)
% 7.42/7.64          | ~ (m1_pre_topc @ X30 @ X29)
% 7.42/7.64          | (m1_pre_topc @ X30 @ 
% 7.42/7.64             (g1_pre_topc @ (u1_struct_0 @ X29) @ (u1_pre_topc @ X29)))
% 7.42/7.64          | ~ (l1_pre_topc @ X30))),
% 7.42/7.64      inference('cnf', [status(esa)], [t65_pre_topc])).
% 7.42/7.64  thf('125', plain,
% 7.42/7.64      (![X0 : $i]:
% 7.42/7.64         (~ (l1_pre_topc @ X0)
% 7.42/7.64          | ~ (l1_pre_topc @ X0)
% 7.42/7.64          | (m1_pre_topc @ X0 @ 
% 7.42/7.64             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 7.42/7.64          | ~ (l1_pre_topc @ X0))),
% 7.42/7.64      inference('sup-', [status(thm)], ['123', '124'])).
% 7.42/7.64  thf('126', plain,
% 7.42/7.64      (![X0 : $i]:
% 7.42/7.64         ((m1_pre_topc @ X0 @ 
% 7.42/7.64           (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 7.42/7.64          | ~ (l1_pre_topc @ X0))),
% 7.42/7.64      inference('simplify', [status(thm)], ['125'])).
% 7.42/7.64  thf('127', plain,
% 7.42/7.64      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 7.42/7.64        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 7.42/7.64      inference('demod', [status(thm)], ['3', '4'])).
% 7.42/7.64  thf(t3_subset, axiom,
% 7.42/7.64    (![A:$i,B:$i]:
% 7.42/7.64     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 7.42/7.64  thf('128', plain,
% 7.42/7.64      (![X8 : $i, X9 : $i]:
% 7.42/7.64         ((r1_tarski @ X8 @ X9) | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9)))),
% 7.42/7.64      inference('cnf', [status(esa)], [t3_subset])).
% 7.42/7.64  thf('129', plain,
% 7.42/7.64      ((r1_tarski @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 7.42/7.64      inference('sup-', [status(thm)], ['127', '128'])).
% 7.42/7.64  thf(t19_tsep_1, axiom,
% 7.42/7.64    (![A:$i]:
% 7.42/7.64     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 7.42/7.64       ( ![B:$i]:
% 7.42/7.64         ( ( ( v1_tsep_1 @ B @ A ) & ( m1_pre_topc @ B @ A ) ) =>
% 7.42/7.64           ( ![C:$i]:
% 7.42/7.64             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 7.42/7.64               ( ( r1_tarski @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ C ) ) =>
% 7.42/7.64                 ( ( v1_tsep_1 @ B @ C ) & ( m1_pre_topc @ B @ C ) ) ) ) ) ) ) ))).
% 7.42/7.64  thf('130', plain,
% 7.42/7.64      (![X57 : $i, X58 : $i, X59 : $i]:
% 7.42/7.64         (~ (v1_tsep_1 @ X57 @ X58)
% 7.42/7.64          | ~ (m1_pre_topc @ X57 @ X58)
% 7.42/7.64          | ~ (r1_tarski @ (u1_struct_0 @ X57) @ (u1_struct_0 @ X59))
% 7.42/7.64          | (v1_tsep_1 @ X57 @ X59)
% 7.42/7.64          | ~ (m1_pre_topc @ X59 @ X58)
% 7.42/7.64          | (v2_struct_0 @ X59)
% 7.42/7.64          | ~ (l1_pre_topc @ X58)
% 7.42/7.64          | ~ (v2_pre_topc @ X58)
% 7.42/7.64          | (v2_struct_0 @ X58))),
% 7.42/7.64      inference('cnf', [status(esa)], [t19_tsep_1])).
% 7.42/7.64  thf('131', plain,
% 7.42/7.64      (![X0 : $i]:
% 7.42/7.64         ((v2_struct_0 @ X0)
% 7.42/7.64          | ~ (v2_pre_topc @ X0)
% 7.42/7.64          | ~ (l1_pre_topc @ X0)
% 7.42/7.64          | (v2_struct_0 @ sk_A)
% 7.42/7.64          | ~ (m1_pre_topc @ sk_A @ X0)
% 7.42/7.64          | (v1_tsep_1 @ sk_B @ sk_A)
% 7.42/7.64          | ~ (m1_pre_topc @ sk_B @ X0)
% 7.42/7.64          | ~ (v1_tsep_1 @ sk_B @ X0))),
% 7.42/7.64      inference('sup-', [status(thm)], ['129', '130'])).
% 7.42/7.64  thf('132', plain,
% 7.42/7.64      ((~ (l1_pre_topc @ sk_A)
% 7.42/7.64        | ~ (v1_tsep_1 @ sk_B @ 
% 7.42/7.64             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 7.42/7.64        | ~ (m1_pre_topc @ sk_B @ 
% 7.42/7.64             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 7.42/7.64        | (v1_tsep_1 @ sk_B @ sk_A)
% 7.42/7.64        | (v2_struct_0 @ sk_A)
% 7.42/7.64        | ~ (l1_pre_topc @ 
% 7.42/7.64             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 7.42/7.64        | ~ (v2_pre_topc @ 
% 7.42/7.64             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 7.42/7.64        | (v2_struct_0 @ 
% 7.42/7.64           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))),
% 7.42/7.64      inference('sup-', [status(thm)], ['126', '131'])).
% 7.42/7.64  thf('133', plain, ((l1_pre_topc @ sk_A)),
% 7.42/7.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.42/7.64  thf('134', plain,
% 7.42/7.64      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 7.42/7.64          = (k8_tmap_1 @ sk_A @ sk_B)))
% 7.42/7.64         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 7.42/7.64                = (k8_tmap_1 @ sk_A @ sk_B))))),
% 7.42/7.64      inference('split', [status(esa)], ['54'])).
% 7.42/7.64  thf('135', plain,
% 7.42/7.64      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 7.42/7.64          = (k8_tmap_1 @ sk_A @ sk_B)))),
% 7.42/7.64      inference('sat_resolution*', [status(thm)], ['72', '75', '119', '120'])).
% 7.42/7.64  thf('136', plain,
% 7.42/7.64      (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 7.42/7.64         = (k8_tmap_1 @ sk_A @ sk_B))),
% 7.42/7.64      inference('simpl_trail', [status(thm)], ['134', '135'])).
% 7.42/7.64  thf('137', plain,
% 7.42/7.64      (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 7.42/7.64         = (k8_tmap_1 @ sk_A @ sk_B))),
% 7.42/7.64      inference('simpl_trail', [status(thm)], ['134', '135'])).
% 7.42/7.64  thf('138', plain,
% 7.42/7.64      (((m1_pre_topc @ sk_B @ (k8_tmap_1 @ sk_A @ sk_B)))
% 7.42/7.64         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 7.42/7.64                = (k8_tmap_1 @ sk_A @ sk_B))))),
% 7.42/7.64      inference('sup+', [status(thm)], ['55', '65'])).
% 7.42/7.64  thf('139', plain,
% 7.42/7.64      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 7.42/7.64          = (k8_tmap_1 @ sk_A @ sk_B)))),
% 7.42/7.64      inference('sat_resolution*', [status(thm)], ['72', '75', '119', '120'])).
% 7.42/7.64  thf('140', plain, ((m1_pre_topc @ sk_B @ (k8_tmap_1 @ sk_A @ sk_B))),
% 7.42/7.64      inference('simpl_trail', [status(thm)], ['138', '139'])).
% 7.42/7.64  thf('141', plain,
% 7.42/7.64      (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 7.42/7.64         = (k8_tmap_1 @ sk_A @ sk_B))),
% 7.42/7.64      inference('simpl_trail', [status(thm)], ['134', '135'])).
% 7.42/7.64  thf('142', plain, ((l1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))),
% 7.42/7.64      inference('clc', [status(thm)], ['20', '21'])).
% 7.42/7.64  thf('143', plain,
% 7.42/7.64      (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 7.42/7.64         = (k8_tmap_1 @ sk_A @ sk_B))),
% 7.42/7.64      inference('simpl_trail', [status(thm)], ['134', '135'])).
% 7.42/7.64  thf('144', plain, ((v2_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))),
% 7.42/7.64      inference('clc', [status(thm)], ['28', '29'])).
% 7.42/7.64  thf('145', plain,
% 7.42/7.64      (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 7.42/7.64         = (k8_tmap_1 @ sk_A @ sk_B))),
% 7.42/7.64      inference('simpl_trail', [status(thm)], ['134', '135'])).
% 7.42/7.64  thf('146', plain,
% 7.42/7.64      ((~ (v1_tsep_1 @ sk_B @ (k8_tmap_1 @ sk_A @ sk_B))
% 7.42/7.64        | (v1_tsep_1 @ sk_B @ sk_A)
% 7.42/7.64        | (v2_struct_0 @ sk_A)
% 7.42/7.64        | (v2_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))),
% 7.42/7.64      inference('demod', [status(thm)],
% 7.42/7.64                ['132', '133', '136', '137', '140', '141', '142', '143', 
% 7.42/7.64                 '144', '145'])).
% 7.42/7.64  thf('147', plain,
% 7.42/7.64      ((((sk_C @ sk_B @ (k8_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_B))
% 7.42/7.64        | (v2_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B))
% 7.42/7.64        | (v2_struct_0 @ sk_A)
% 7.42/7.64        | (v1_tsep_1 @ sk_B @ sk_A))),
% 7.42/7.64      inference('sup-', [status(thm)], ['122', '146'])).
% 7.42/7.64  thf('148', plain,
% 7.42/7.64      (![X35 : $i, X36 : $i]:
% 7.42/7.64         (~ (m1_pre_topc @ X35 @ X36)
% 7.42/7.64          | ~ (v3_pre_topc @ (sk_C @ X35 @ X36) @ X36)
% 7.42/7.64          | (v1_tsep_1 @ X35 @ X36)
% 7.42/7.64          | ~ (l1_pre_topc @ X36))),
% 7.42/7.64      inference('cnf', [status(esa)], [d1_tsep_1])).
% 7.42/7.64  thf('149', plain,
% 7.42/7.64      ((~ (v3_pre_topc @ (u1_struct_0 @ sk_B) @ (k8_tmap_1 @ sk_A @ sk_B))
% 7.42/7.64        | (v1_tsep_1 @ sk_B @ sk_A)
% 7.42/7.64        | (v2_struct_0 @ sk_A)
% 7.42/7.64        | (v2_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B))
% 7.42/7.64        | ~ (l1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 7.42/7.64        | (v1_tsep_1 @ sk_B @ (k8_tmap_1 @ sk_A @ sk_B))
% 7.42/7.64        | ~ (m1_pre_topc @ sk_B @ (k8_tmap_1 @ sk_A @ sk_B)))),
% 7.42/7.64      inference('sup-', [status(thm)], ['147', '148'])).
% 7.42/7.64  thf('150', plain,
% 7.42/7.64      (((k8_tmap_1 @ sk_A @ sk_B) = (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))),
% 7.42/7.64      inference('clc', [status(thm)], ['42', '43'])).
% 7.42/7.64  thf(t105_tmap_1, axiom,
% 7.42/7.64    (![A:$i]:
% 7.42/7.64     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 7.42/7.64       ( ![B:$i]:
% 7.42/7.64         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 7.42/7.64           ( ![C:$i]:
% 7.42/7.64             ( ( m1_subset_1 @
% 7.42/7.64                 C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k6_tmap_1 @ A @ B ) ) ) ) =>
% 7.42/7.64               ( ( ( C ) = ( B ) ) =>
% 7.42/7.64                 ( v3_pre_topc @ C @ ( k6_tmap_1 @ A @ B ) ) ) ) ) ) ) ))).
% 7.42/7.64  thf('151', plain,
% 7.42/7.64      (![X46 : $i, X47 : $i, X48 : $i]:
% 7.42/7.64         (~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (u1_struct_0 @ X47)))
% 7.42/7.64          | ((X48) != (X46))
% 7.42/7.64          | (v3_pre_topc @ X48 @ (k6_tmap_1 @ X47 @ X46))
% 7.42/7.64          | ~ (m1_subset_1 @ X48 @ 
% 7.42/7.64               (k1_zfmisc_1 @ (u1_struct_0 @ (k6_tmap_1 @ X47 @ X46))))
% 7.42/7.64          | ~ (l1_pre_topc @ X47)
% 7.42/7.64          | ~ (v2_pre_topc @ X47)
% 7.42/7.64          | (v2_struct_0 @ X47))),
% 7.42/7.64      inference('cnf', [status(esa)], [t105_tmap_1])).
% 7.42/7.64  thf('152', plain,
% 7.42/7.64      (![X46 : $i, X47 : $i]:
% 7.42/7.64         ((v2_struct_0 @ X47)
% 7.42/7.64          | ~ (v2_pre_topc @ X47)
% 7.42/7.64          | ~ (l1_pre_topc @ X47)
% 7.42/7.64          | ~ (m1_subset_1 @ X46 @ 
% 7.42/7.64               (k1_zfmisc_1 @ (u1_struct_0 @ (k6_tmap_1 @ X47 @ X46))))
% 7.42/7.64          | (v3_pre_topc @ X46 @ (k6_tmap_1 @ X47 @ X46))
% 7.42/7.64          | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (u1_struct_0 @ X47))))),
% 7.42/7.64      inference('simplify', [status(thm)], ['151'])).
% 7.42/7.64  thf('153', plain,
% 7.42/7.64      ((~ (m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 7.42/7.64           (k1_zfmisc_1 @ (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B))))
% 7.42/7.64        | ~ (m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 7.42/7.64             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 7.42/7.64        | (v3_pre_topc @ (u1_struct_0 @ sk_B) @ 
% 7.42/7.64           (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 7.42/7.64        | ~ (l1_pre_topc @ sk_A)
% 7.42/7.64        | ~ (v2_pre_topc @ sk_A)
% 7.42/7.64        | (v2_struct_0 @ sk_A))),
% 7.42/7.64      inference('sup-', [status(thm)], ['150', '152'])).
% 7.42/7.64  thf('154', plain,
% 7.42/7.64      (((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 7.42/7.64      inference('clc', [status(thm)], ['45', '46'])).
% 7.42/7.64  thf('155', plain,
% 7.42/7.64      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 7.42/7.64        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 7.42/7.64      inference('demod', [status(thm)], ['3', '4'])).
% 7.42/7.64  thf('156', plain,
% 7.42/7.64      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 7.42/7.64        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 7.42/7.64      inference('demod', [status(thm)], ['3', '4'])).
% 7.42/7.64  thf('157', plain,
% 7.42/7.64      (((k8_tmap_1 @ sk_A @ sk_B) = (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))),
% 7.42/7.64      inference('clc', [status(thm)], ['42', '43'])).
% 7.42/7.64  thf('158', plain, ((l1_pre_topc @ sk_A)),
% 7.42/7.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.42/7.64  thf('159', plain, ((v2_pre_topc @ sk_A)),
% 7.42/7.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.42/7.64  thf('160', plain,
% 7.42/7.64      (((v3_pre_topc @ (u1_struct_0 @ sk_B) @ (k8_tmap_1 @ sk_A @ sk_B))
% 7.42/7.64        | (v2_struct_0 @ sk_A))),
% 7.42/7.64      inference('demod', [status(thm)],
% 7.42/7.64                ['153', '154', '155', '156', '157', '158', '159'])).
% 7.42/7.64  thf('161', plain, (~ (v2_struct_0 @ sk_A)),
% 7.42/7.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.42/7.64  thf('162', plain,
% 7.42/7.64      ((v3_pre_topc @ (u1_struct_0 @ sk_B) @ (k8_tmap_1 @ sk_A @ sk_B))),
% 7.42/7.64      inference('clc', [status(thm)], ['160', '161'])).
% 7.42/7.64  thf('163', plain, ((l1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))),
% 7.42/7.64      inference('clc', [status(thm)], ['20', '21'])).
% 7.42/7.64  thf('164', plain, ((m1_pre_topc @ sk_B @ (k8_tmap_1 @ sk_A @ sk_B))),
% 7.42/7.64      inference('simpl_trail', [status(thm)], ['138', '139'])).
% 7.42/7.64  thf('165', plain,
% 7.42/7.64      (((v1_tsep_1 @ sk_B @ sk_A)
% 7.42/7.64        | (v2_struct_0 @ sk_A)
% 7.42/7.64        | (v2_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B))
% 7.42/7.64        | (v1_tsep_1 @ sk_B @ (k8_tmap_1 @ sk_A @ sk_B)))),
% 7.42/7.64      inference('demod', [status(thm)], ['149', '162', '163', '164'])).
% 7.42/7.64  thf('166', plain,
% 7.42/7.64      ((~ (v1_tsep_1 @ sk_B @ (k8_tmap_1 @ sk_A @ sk_B))
% 7.42/7.64        | (v1_tsep_1 @ sk_B @ sk_A)
% 7.42/7.64        | (v2_struct_0 @ sk_A)
% 7.42/7.64        | (v2_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))),
% 7.42/7.64      inference('demod', [status(thm)],
% 7.42/7.64                ['132', '133', '136', '137', '140', '141', '142', '143', 
% 7.42/7.64                 '144', '145'])).
% 7.42/7.64  thf('167', plain,
% 7.42/7.64      (((v2_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B))
% 7.42/7.64        | (v2_struct_0 @ sk_A)
% 7.42/7.64        | (v1_tsep_1 @ sk_B @ sk_A)
% 7.42/7.64        | (v2_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B))
% 7.42/7.64        | (v2_struct_0 @ sk_A)
% 7.42/7.64        | (v1_tsep_1 @ sk_B @ sk_A))),
% 7.42/7.64      inference('sup-', [status(thm)], ['165', '166'])).
% 7.42/7.64  thf('168', plain,
% 7.42/7.64      (((v1_tsep_1 @ sk_B @ sk_A)
% 7.42/7.64        | (v2_struct_0 @ sk_A)
% 7.42/7.64        | (v2_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))),
% 7.42/7.64      inference('simplify', [status(thm)], ['167'])).
% 7.42/7.64  thf('169', plain,
% 7.42/7.64      ((~ (v1_tsep_1 @ sk_B @ sk_A)) <= (~ ((v1_tsep_1 @ sk_B @ sk_A)))),
% 7.42/7.64      inference('split', [status(esa)], ['71'])).
% 7.42/7.64  thf('170', plain, (~ ((v1_tsep_1 @ sk_B @ sk_A))),
% 7.42/7.64      inference('sat_resolution*', [status(thm)], ['72', '75', '119'])).
% 7.42/7.64  thf('171', plain, (~ (v1_tsep_1 @ sk_B @ sk_A)),
% 7.42/7.64      inference('simpl_trail', [status(thm)], ['169', '170'])).
% 7.42/7.64  thf('172', plain,
% 7.42/7.64      (((v2_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)) | (v2_struct_0 @ sk_A))),
% 7.42/7.64      inference('clc', [status(thm)], ['168', '171'])).
% 7.42/7.64  thf('173', plain, (~ (v2_struct_0 @ sk_A)),
% 7.42/7.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.42/7.64  thf('174', plain, ((v2_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B))),
% 7.42/7.64      inference('clc', [status(thm)], ['172', '173'])).
% 7.42/7.64  thf('175', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 7.42/7.64      inference('demod', [status(thm)], ['53', '174'])).
% 7.42/7.64  thf(fc2_struct_0, axiom,
% 7.42/7.64    (![A:$i]:
% 7.42/7.64     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 7.42/7.64       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 7.42/7.64  thf('176', plain,
% 7.42/7.64      (![X23 : $i]:
% 7.42/7.64         (~ (v1_xboole_0 @ (u1_struct_0 @ X23))
% 7.42/7.64          | ~ (l1_struct_0 @ X23)
% 7.42/7.64          | (v2_struct_0 @ X23))),
% 7.42/7.64      inference('cnf', [status(esa)], [fc2_struct_0])).
% 7.42/7.64  thf('177', plain, (((v2_struct_0 @ sk_A) | ~ (l1_struct_0 @ sk_A))),
% 7.42/7.64      inference('sup-', [status(thm)], ['175', '176'])).
% 7.42/7.64  thf('178', plain, ((l1_pre_topc @ sk_A)),
% 7.42/7.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.42/7.64  thf('179', plain,
% 7.42/7.64      (![X19 : $i]: ((l1_struct_0 @ X19) | ~ (l1_pre_topc @ X19))),
% 7.42/7.64      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 7.42/7.64  thf('180', plain, ((l1_struct_0 @ sk_A)),
% 7.42/7.64      inference('sup-', [status(thm)], ['178', '179'])).
% 7.42/7.64  thf('181', plain, ((v2_struct_0 @ sk_A)),
% 7.42/7.64      inference('demod', [status(thm)], ['177', '180'])).
% 7.42/7.64  thf('182', plain, ($false), inference('demod', [status(thm)], ['0', '181'])).
% 7.42/7.64  
% 7.42/7.64  % SZS output end Refutation
% 7.42/7.64  
% 7.42/7.64  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
