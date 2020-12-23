%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.vPim1DOa4I

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:10:56 EST 2020

% Result     : Theorem 0.60s
% Output     : Refutation 0.60s
% Verified   : 
% Statistics : Number of formulae       :  227 ( 687 expanded)
%              Number of leaves         :   37 ( 205 expanded)
%              Depth                    :   25
%              Number of atoms          : 2061 (10226 expanded)
%              Number of equality atoms :   91 ( 423 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(g1_pre_topc_type,type,(
    g1_pre_topc: $i > $i > $i )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k6_tmap_1_type,type,(
    k6_tmap_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

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

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_tsep_1_type,type,(
    v1_tsep_1: $i > $i > $o )).

thf(k8_tmap_1_type,type,(
    k8_tmap_1: $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k5_tmap_1_type,type,(
    k5_tmap_1: $i > $i > $i )).

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

thf(fc10_tops_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( v3_pre_topc @ ( k2_struct_0 @ A ) @ A ) ) )).

thf('1',plain,(
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

thf('2',plain,(
    ! [X3: $i] :
      ( ( ( k2_struct_0 @ X3 )
        = ( u1_struct_0 @ X3 ) )
      | ~ ( l1_struct_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('3',plain,(
    ! [X1: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X1 ) @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('4',plain,(
    ! [X0: $i] :
      ( ( k2_subset_1 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('5',plain,(
    ! [X1: $i] :
      ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf(d5_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v3_pre_topc @ B @ A )
          <=> ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) ) ) ) )).

thf('6',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) )
      | ~ ( v3_pre_topc @ X4 @ X5 )
      | ( r2_hidden @ X4 @ ( u1_pre_topc @ X5 ) )
      | ~ ( l1_pre_topc @ X5 ) ) ),
    inference(cnf,[status(esa)],[d5_pre_topc])).

thf('7',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( r2_hidden @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ~ ( v3_pre_topc @ ( k2_struct_0 @ X0 ) @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( r2_hidden @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( r2_hidden @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( r2_hidden @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    ! [X1: $i] :
      ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X1 ) ) ),
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

thf('12',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( r2_hidden @ X15 @ ( u1_pre_topc @ X16 ) )
      | ( ( u1_pre_topc @ X16 )
        = ( k5_tmap_1 @ X16 @ X15 ) )
      | ~ ( l1_pre_topc @ X16 )
      | ~ ( v2_pre_topc @ X16 )
      | ( v2_struct_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t103_tmap_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( u1_pre_topc @ X0 )
        = ( k5_tmap_1 @ X0 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( r2_hidden @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( ( u1_pre_topc @ X0 )
        = ( k5_tmap_1 @ X0 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ( ( u1_pre_topc @ X0 )
        = ( k5_tmap_1 @ X0 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,
    ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k8_tmap_1 @ sk_A @ sk_B ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['16'])).

thf('18',plain,
    ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
     != ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( m1_pre_topc @ sk_B @ sk_A )
    | ~ ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ~ ( v1_tsep_1 @ sk_B @ sk_A )
    | ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
     != ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['18'])).

thf('20',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ~ ( m1_pre_topc @ sk_B @ sk_A )
   <= ~ ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['18'])).

thf('22',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t1_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( m1_subset_1 @ ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('24',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( m1_pre_topc @ X22 @ X23 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X22 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ~ ( l1_pre_topc @ X23 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('25',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['25','26'])).

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

thf('28',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( v2_struct_0 @ X19 )
      | ~ ( m1_pre_topc @ X19 @ X20 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ( ( u1_pre_topc @ ( k8_tmap_1 @ X20 @ X19 ) )
        = ( k5_tmap_1 @ X20 @ X21 ) )
      | ( X21
       != ( u1_struct_0 @ X19 ) )
      | ~ ( l1_pre_topc @ X20 )
      | ~ ( v2_pre_topc @ X20 )
      | ( v2_struct_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t114_tmap_1])).

thf('29',plain,(
    ! [X19: $i,X20: $i] :
      ( ( v2_struct_0 @ X20 )
      | ~ ( v2_pre_topc @ X20 )
      | ~ ( l1_pre_topc @ X20 )
      | ( ( u1_pre_topc @ ( k8_tmap_1 @ X20 @ X19 ) )
        = ( k5_tmap_1 @ X20 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X19 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ~ ( m1_pre_topc @ X19 @ X20 )
      | ( v2_struct_0 @ X19 ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,
    ( ( v2_struct_0 @ sk_B )
    | ~ ( m1_pre_topc @ sk_B @ sk_A )
    | ( ( u1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
      = ( k5_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['27','29'])).

thf('31',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( u1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
      = ( k5_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['30','31','32','33'])).

thf('35',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( u1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
      = ( k5_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['34','35'])).

thf('37',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ( u1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    = ( k5_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['36','37'])).

thf('39',plain,
    ( ( v1_tsep_1 @ sk_B @ sk_A )
   <= ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['16'])).

thf('40',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['25','26'])).

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

thf('41',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( m1_pre_topc @ X8 @ X9 )
      | ~ ( v1_tsep_1 @ X8 @ X9 )
      | ( X10
       != ( u1_struct_0 @ X8 ) )
      | ( v3_pre_topc @ X10 @ X9 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[d1_tsep_1])).

thf('42',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( l1_pre_topc @ X9 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X8 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ( v3_pre_topc @ ( u1_struct_0 @ X8 ) @ X9 )
      | ~ ( v1_tsep_1 @ X8 @ X9 )
      | ~ ( m1_pre_topc @ X8 @ X9 ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,
    ( ~ ( m1_pre_topc @ sk_B @ sk_A )
    | ~ ( v1_tsep_1 @ sk_B @ sk_A )
    | ( v3_pre_topc @ ( u1_struct_0 @ sk_B ) @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['40','42'])).

thf('44',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( ~ ( v1_tsep_1 @ sk_B @ sk_A )
    | ( v3_pre_topc @ ( u1_struct_0 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['43','44','45'])).

thf('47',plain,
    ( ( v3_pre_topc @ ( u1_struct_0 @ sk_B ) @ sk_A )
   <= ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['39','46'])).

thf('48',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('49',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) )
      | ~ ( v3_pre_topc @ X4 @ X5 )
      | ( r2_hidden @ X4 @ ( u1_pre_topc @ X5 ) )
      | ~ ( l1_pre_topc @ X5 ) ) ),
    inference(cnf,[status(esa)],[d5_pre_topc])).

thf('50',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r2_hidden @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_A ) )
    | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,
    ( ( r2_hidden @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_A ) )
    | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,
    ( ( r2_hidden @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_A ) )
   <= ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['47','52'])).

thf('54',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('55',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( r2_hidden @ X15 @ ( u1_pre_topc @ X16 ) )
      | ( ( u1_pre_topc @ X16 )
        = ( k5_tmap_1 @ X16 @ X15 ) )
      | ~ ( l1_pre_topc @ X16 )
      | ~ ( v2_pre_topc @ X16 )
      | ( v2_struct_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t103_tmap_1])).

thf('56',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( ( u1_pre_topc @ sk_A )
      = ( k5_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
    | ~ ( r2_hidden @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( u1_pre_topc @ sk_A )
      = ( k5_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
    | ~ ( r2_hidden @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_A ) ) ),
    inference(demod,[status(thm)],['56','57','58'])).

thf('60',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,
    ( ~ ( r2_hidden @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_A ) )
    | ( ( u1_pre_topc @ sk_A )
      = ( k5_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['59','60'])).

thf('62',plain,
    ( ( ( u1_pre_topc @ sk_A )
      = ( k5_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
   <= ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['53','61'])).

thf('63',plain,
    ( ( ( u1_pre_topc @ sk_A )
      = ( u1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) ) )
   <= ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['38','62'])).

thf('64',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    ! [X19: $i,X20: $i] :
      ( ( v2_struct_0 @ X19 )
      | ~ ( m1_pre_topc @ X19 @ X20 )
      | ( ( u1_struct_0 @ ( k8_tmap_1 @ X20 @ X19 ) )
        = ( u1_struct_0 @ X20 ) )
      | ~ ( l1_pre_topc @ X20 )
      | ~ ( v2_pre_topc @ X20 )
      | ( v2_struct_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t114_tmap_1])).

thf('66',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
      = ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
      = ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['66','67','68'])).

thf('70',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['69','70'])).

thf('72',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,
    ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['71','72'])).

thf(abstractness_v1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( ( v1_pre_topc @ A )
       => ( A
          = ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ) )).

thf('74',plain,(
    ! [X2: $i] :
      ( ~ ( v1_pre_topc @ X2 )
      | ( X2
        = ( g1_pre_topc @ ( u1_struct_0 @ X2 ) @ ( u1_pre_topc @ X2 ) ) )
      | ~ ( l1_pre_topc @ X2 ) ) ),
    inference(cnf,[status(esa)],[abstractness_v1_pre_topc])).

thf('75',plain,
    ( ( ( k8_tmap_1 @ sk_A @ sk_B )
      = ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) )
    | ~ ( l1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( v1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['73','74'])).

thf('76',plain,(
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

thf('77',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( l1_pre_topc @ X13 )
      | ~ ( v2_pre_topc @ X13 )
      | ( v2_struct_0 @ X13 )
      | ~ ( m1_pre_topc @ X14 @ X13 )
      | ( l1_pre_topc @ ( k8_tmap_1 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k8_tmap_1])).

thf('78',plain,
    ( ( l1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,
    ( ( l1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['78','79','80'])).

thf('82',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    l1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['81','82'])).

thf('84',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( l1_pre_topc @ X13 )
      | ~ ( v2_pre_topc @ X13 )
      | ( v2_struct_0 @ X13 )
      | ~ ( m1_pre_topc @ X14 @ X13 )
      | ( v1_pre_topc @ ( k8_tmap_1 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k8_tmap_1])).

thf('86',plain,
    ( ( v1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,
    ( ( v1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['86','87','88'])).

thf('90',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    v1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['89','90'])).

thf('92',plain,
    ( ( k8_tmap_1 @ sk_A @ sk_B )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['75','83','91'])).

thf('93',plain,
    ( ( ( k8_tmap_1 @ sk_A @ sk_B )
      = ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
   <= ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['63','92'])).

thf('94',plain,
    ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
     != ( k8_tmap_1 @ sk_A @ sk_B ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
     != ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['18'])).

thf('95',plain,
    ( ( ( k8_tmap_1 @ sk_A @ sk_B )
     != ( k8_tmap_1 @ sk_A @ sk_B ) )
   <= ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
       != ( k8_tmap_1 @ sk_A @ sk_B ) )
      & ( v1_tsep_1 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,
    ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['95'])).

thf('97',plain,
    ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['16'])).

thf('98',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
    = ( k8_tmap_1 @ sk_A @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['19','22','96','97'])).

thf('99',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
    = ( k8_tmap_1 @ sk_A @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['17','98'])).

thf('100',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ( ( u1_pre_topc @ X0 )
        = ( k5_tmap_1 @ X0 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('101',plain,(
    ! [X1: $i] :
      ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X1 ) ) ),
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

thf('102',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ( ( u1_pre_topc @ ( k6_tmap_1 @ X18 @ X17 ) )
        = ( k5_tmap_1 @ X18 @ X17 ) )
      | ~ ( l1_pre_topc @ X18 )
      | ~ ( v2_pre_topc @ X18 )
      | ( v2_struct_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t104_tmap_1])).

thf('103',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( u1_pre_topc @ ( k6_tmap_1 @ X0 @ ( u1_struct_0 @ X0 ) ) )
        = ( k5_tmap_1 @ X0 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,(
    ! [X1: $i] :
      ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf(dt_k6_tmap_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( ( v1_pre_topc @ ( k6_tmap_1 @ A @ B ) )
        & ( v2_pre_topc @ ( k6_tmap_1 @ A @ B ) )
        & ( l1_pre_topc @ ( k6_tmap_1 @ A @ B ) ) ) ) )).

thf('105',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( l1_pre_topc @ X11 )
      | ~ ( v2_pre_topc @ X11 )
      | ( v2_struct_0 @ X11 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ( v1_pre_topc @ ( k6_tmap_1 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_tmap_1])).

thf('106',plain,(
    ! [X0: $i] :
      ( ( v1_pre_topc @ ( k6_tmap_1 @ X0 @ ( u1_struct_0 @ X0 ) ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['104','105'])).

thf('107',plain,(
    ! [X1: $i] :
      ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('108',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( l1_pre_topc @ X11 )
      | ~ ( v2_pre_topc @ X11 )
      | ( v2_struct_0 @ X11 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ( l1_pre_topc @ ( k6_tmap_1 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_tmap_1])).

thf('109',plain,(
    ! [X0: $i] :
      ( ( l1_pre_topc @ ( k6_tmap_1 @ X0 @ ( u1_struct_0 @ X0 ) ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['107','108'])).

thf('110',plain,(
    ! [X1: $i] :
      ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('111',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ( ( u1_struct_0 @ ( k6_tmap_1 @ X18 @ X17 ) )
        = ( u1_struct_0 @ X18 ) )
      | ~ ( l1_pre_topc @ X18 )
      | ~ ( v2_pre_topc @ X18 )
      | ( v2_struct_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t104_tmap_1])).

thf('112',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( u1_struct_0 @ ( k6_tmap_1 @ X0 @ ( u1_struct_0 @ X0 ) ) )
        = ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['110','111'])).

thf('113',plain,(
    ! [X2: $i] :
      ( ~ ( v1_pre_topc @ X2 )
      | ( X2
        = ( g1_pre_topc @ ( u1_struct_0 @ X2 ) @ ( u1_pre_topc @ X2 ) ) )
      | ~ ( l1_pre_topc @ X2 ) ) ),
    inference(cnf,[status(esa)],[abstractness_v1_pre_topc])).

thf('114',plain,(
    ! [X0: $i] :
      ( ( ( k6_tmap_1 @ X0 @ ( u1_struct_0 @ X0 ) )
        = ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ ( k6_tmap_1 @ X0 @ ( u1_struct_0 @ X0 ) ) ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ ( k6_tmap_1 @ X0 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( v1_pre_topc @ ( k6_tmap_1 @ X0 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['112','113'])).

thf('115',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v1_pre_topc @ ( k6_tmap_1 @ X0 @ ( u1_struct_0 @ X0 ) ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( k6_tmap_1 @ X0 @ ( u1_struct_0 @ X0 ) )
        = ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ ( k6_tmap_1 @ X0 @ ( u1_struct_0 @ X0 ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['109','114'])).

thf('116',plain,(
    ! [X0: $i] :
      ( ( ( k6_tmap_1 @ X0 @ ( u1_struct_0 @ X0 ) )
        = ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ ( k6_tmap_1 @ X0 @ ( u1_struct_0 @ X0 ) ) ) ) )
      | ~ ( v1_pre_topc @ ( k6_tmap_1 @ X0 @ ( u1_struct_0 @ X0 ) ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['115'])).

thf('117',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( ( k6_tmap_1 @ X0 @ ( u1_struct_0 @ X0 ) )
        = ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ ( k6_tmap_1 @ X0 @ ( u1_struct_0 @ X0 ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['106','116'])).

thf('118',plain,(
    ! [X0: $i] :
      ( ( ( k6_tmap_1 @ X0 @ ( u1_struct_0 @ X0 ) )
        = ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ ( k6_tmap_1 @ X0 @ ( u1_struct_0 @ X0 ) ) ) ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['117'])).

thf('119',plain,(
    ! [X0: $i] :
      ( ( ( k6_tmap_1 @ X0 @ ( u1_struct_0 @ X0 ) )
        = ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( k5_tmap_1 @ X0 @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['103','118'])).

thf('120',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( k6_tmap_1 @ X0 @ ( u1_struct_0 @ X0 ) )
        = ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( k5_tmap_1 @ X0 @ ( u1_struct_0 @ X0 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['119'])).

thf('121',plain,(
    ! [X0: $i] :
      ( ( ( k6_tmap_1 @ X0 @ ( u1_struct_0 @ X0 ) )
        = ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['100','120'])).

thf('122',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( ( k6_tmap_1 @ X0 @ ( u1_struct_0 @ X0 ) )
        = ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['121'])).

thf('123',plain,
    ( ( ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_A ) )
      = ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( l1_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['99','122'])).

thf('124',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('125',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('127',plain,(
    ! [X6: $i] :
      ( ( l1_struct_0 @ X6 )
      | ~ ( l1_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('128',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['126','127'])).

thf('129',plain,
    ( ( ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_A ) )
      = ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['123','124','125','128'])).

thf('130',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('131',plain,
    ( ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_A ) )
    = ( k8_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['129','130'])).

thf('132',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( u1_pre_topc @ ( k6_tmap_1 @ X0 @ ( u1_struct_0 @ X0 ) ) )
        = ( k5_tmap_1 @ X0 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('133',plain,
    ( ( ( u1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
      = ( k5_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['131','132'])).

thf('134',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('135',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('136',plain,
    ( ( ( u1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
      = ( k5_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_A ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['133','134','135'])).

thf('137',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('138',plain,
    ( ( u1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    = ( k5_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['136','137'])).

thf('139',plain,
    ( ( ( u1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
      = ( u1_pre_topc @ sk_A ) )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( l1_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['15','138'])).

thf('140',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('141',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('142',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['126','127'])).

thf('143',plain,
    ( ( ( u1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
      = ( u1_pre_topc @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['139','140','141','142'])).

thf('144',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('145',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ( ( u1_pre_topc @ X16 )
       != ( k5_tmap_1 @ X16 @ X15 ) )
      | ( r2_hidden @ X15 @ ( u1_pre_topc @ X16 ) )
      | ~ ( l1_pre_topc @ X16 )
      | ~ ( v2_pre_topc @ X16 )
      | ( v2_struct_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t103_tmap_1])).

thf('146',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( r2_hidden @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_A ) )
    | ( ( u1_pre_topc @ sk_A )
     != ( k5_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['144','145'])).

thf('147',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('148',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('149',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_A ) )
    | ( ( u1_pre_topc @ sk_A )
     != ( k5_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['146','147','148'])).

thf('150',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('151',plain,
    ( ( ( u1_pre_topc @ sk_A )
     != ( k5_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
    | ( r2_hidden @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_A ) ) ),
    inference(clc,[status(thm)],['149','150'])).

thf('152',plain,
    ( ( u1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    = ( k5_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['36','37'])).

thf('153',plain,
    ( ( ( u1_pre_topc @ sk_A )
     != ( u1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) ) )
    | ( r2_hidden @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_A ) ) ),
    inference(demod,[status(thm)],['151','152'])).

thf('154',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('155',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( m1_pre_topc @ X8 @ X9 )
      | ( ( sk_C @ X8 @ X9 )
        = ( u1_struct_0 @ X8 ) )
      | ( v1_tsep_1 @ X8 @ X9 )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[d1_tsep_1])).

thf('156',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v1_tsep_1 @ sk_B @ sk_A )
    | ( ( sk_C @ sk_B @ sk_A )
      = ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['154','155'])).

thf('157',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('158',plain,
    ( ( v1_tsep_1 @ sk_B @ sk_A )
    | ( ( sk_C @ sk_B @ sk_A )
      = ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['156','157'])).

thf('159',plain,
    ( ~ ( v1_tsep_1 @ sk_B @ sk_A )
   <= ~ ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['18'])).

thf('160',plain,
    ( ( ( sk_C @ sk_B @ sk_A )
      = ( u1_struct_0 @ sk_B ) )
   <= ~ ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['158','159'])).

thf('161',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('162',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( m1_pre_topc @ X8 @ X9 )
      | ( m1_subset_1 @ ( sk_C @ X8 @ X9 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ( v1_tsep_1 @ X8 @ X9 )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[d1_tsep_1])).

thf('163',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v1_tsep_1 @ sk_B @ sk_A )
    | ( m1_subset_1 @ ( sk_C @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['161','162'])).

thf('164',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('165',plain,
    ( ( v1_tsep_1 @ sk_B @ sk_A )
    | ( m1_subset_1 @ ( sk_C @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['163','164'])).

thf('166',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) )
      | ~ ( r2_hidden @ X4 @ ( u1_pre_topc @ X5 ) )
      | ( v3_pre_topc @ X4 @ X5 )
      | ~ ( l1_pre_topc @ X5 ) ) ),
    inference(cnf,[status(esa)],[d5_pre_topc])).

thf('167',plain,
    ( ( v1_tsep_1 @ sk_B @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v3_pre_topc @ ( sk_C @ sk_B @ sk_A ) @ sk_A )
    | ~ ( r2_hidden @ ( sk_C @ sk_B @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['165','166'])).

thf('168',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('169',plain,
    ( ( v1_tsep_1 @ sk_B @ sk_A )
    | ( v3_pre_topc @ ( sk_C @ sk_B @ sk_A ) @ sk_A )
    | ~ ( r2_hidden @ ( sk_C @ sk_B @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ),
    inference(demod,[status(thm)],['167','168'])).

thf('170',plain,
    ( ( ~ ( r2_hidden @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_A ) )
      | ( v3_pre_topc @ ( sk_C @ sk_B @ sk_A ) @ sk_A )
      | ( v1_tsep_1 @ sk_B @ sk_A ) )
   <= ~ ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['160','169'])).

thf('171',plain,
    ( ( ( sk_C @ sk_B @ sk_A )
      = ( u1_struct_0 @ sk_B ) )
   <= ~ ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['158','159'])).

thf('172',plain,
    ( ( ~ ( r2_hidden @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_A ) )
      | ( v3_pre_topc @ ( u1_struct_0 @ sk_B ) @ sk_A )
      | ( v1_tsep_1 @ sk_B @ sk_A ) )
   <= ~ ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['170','171'])).

thf('173',plain,
    ( ( ( sk_C @ sk_B @ sk_A )
      = ( u1_struct_0 @ sk_B ) )
   <= ~ ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['158','159'])).

thf('174',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( m1_pre_topc @ X8 @ X9 )
      | ~ ( v3_pre_topc @ ( sk_C @ X8 @ X9 ) @ X9 )
      | ( v1_tsep_1 @ X8 @ X9 )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[d1_tsep_1])).

thf('175',plain,
    ( ( ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_B ) @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v1_tsep_1 @ sk_B @ sk_A )
      | ~ ( m1_pre_topc @ sk_B @ sk_A ) )
   <= ~ ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['173','174'])).

thf('176',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('177',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('178',plain,
    ( ( ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_B ) @ sk_A )
      | ( v1_tsep_1 @ sk_B @ sk_A ) )
   <= ~ ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['175','176','177'])).

thf('179',plain,
    ( ~ ( v1_tsep_1 @ sk_B @ sk_A )
   <= ~ ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['18'])).

thf('180',plain,
    ( ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_B ) @ sk_A )
   <= ~ ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['178','179'])).

thf('181',plain,
    ( ( ( v1_tsep_1 @ sk_B @ sk_A )
      | ~ ( r2_hidden @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_A ) ) )
   <= ~ ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['172','180'])).

thf('182',plain,
    ( ~ ( v1_tsep_1 @ sk_B @ sk_A )
   <= ~ ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['18'])).

thf('183',plain,
    ( ~ ( r2_hidden @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_A ) )
   <= ~ ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['181','182'])).

thf('184',plain,(
    ~ ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['19','22','96'])).

thf('185',plain,(
    ~ ( r2_hidden @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_A ) ) ),
    inference(simpl_trail,[status(thm)],['183','184'])).

thf('186',plain,(
    ( u1_pre_topc @ sk_A )
 != ( u1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['153','185'])).

thf('187',plain,(
    v2_struct_0 @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['143','186'])).

thf('188',plain,(
    $false ),
    inference(demod,[status(thm)],['0','187'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.vPim1DOa4I
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:02:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.60/0.79  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.60/0.79  % Solved by: fo/fo7.sh
% 0.60/0.79  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.60/0.79  % done 481 iterations in 0.330s
% 0.60/0.79  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.60/0.79  % SZS output start Refutation
% 0.60/0.79  thf(g1_pre_topc_type, type, g1_pre_topc: $i > $i > $i).
% 0.60/0.79  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 0.60/0.79  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.60/0.79  thf(k6_tmap_1_type, type, k6_tmap_1: $i > $i > $i).
% 0.60/0.79  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.60/0.79  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.60/0.79  thf(sk_B_type, type, sk_B: $i).
% 0.60/0.79  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.60/0.79  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.60/0.79  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.60/0.79  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 0.60/0.79  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.60/0.79  thf(sk_A_type, type, sk_A: $i).
% 0.60/0.79  thf(v1_tsep_1_type, type, v1_tsep_1: $i > $i > $o).
% 0.60/0.79  thf(k8_tmap_1_type, type, k8_tmap_1: $i > $i > $i).
% 0.60/0.79  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.60/0.79  thf(k5_tmap_1_type, type, k5_tmap_1: $i > $i > $i).
% 0.60/0.79  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.60/0.79  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.60/0.79  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.60/0.79  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.60/0.79  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.60/0.79  thf(t116_tmap_1, conjecture,
% 0.60/0.79    (![A:$i]:
% 0.60/0.79     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.60/0.79       ( ![B:$i]:
% 0.60/0.79         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.60/0.79           ( ( ( v1_tsep_1 @ B @ A ) & ( m1_pre_topc @ B @ A ) ) <=>
% 0.60/0.79             ( ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) =
% 0.60/0.79               ( k8_tmap_1 @ A @ B ) ) ) ) ) ))).
% 0.60/0.79  thf(zf_stmt_0, negated_conjecture,
% 0.60/0.79    (~( ![A:$i]:
% 0.60/0.79        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.60/0.79            ( l1_pre_topc @ A ) ) =>
% 0.60/0.79          ( ![B:$i]:
% 0.60/0.79            ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.60/0.79              ( ( ( v1_tsep_1 @ B @ A ) & ( m1_pre_topc @ B @ A ) ) <=>
% 0.60/0.79                ( ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) =
% 0.60/0.79                  ( k8_tmap_1 @ A @ B ) ) ) ) ) ) )),
% 0.60/0.79    inference('cnf.neg', [status(esa)], [t116_tmap_1])).
% 0.60/0.79  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.60/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.79  thf(fc10_tops_1, axiom,
% 0.60/0.79    (![A:$i]:
% 0.60/0.79     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.60/0.79       ( v3_pre_topc @ ( k2_struct_0 @ A ) @ A ) ))).
% 0.60/0.79  thf('1', plain,
% 0.60/0.79      (![X7 : $i]:
% 0.60/0.79         ((v3_pre_topc @ (k2_struct_0 @ X7) @ X7)
% 0.60/0.79          | ~ (l1_pre_topc @ X7)
% 0.60/0.79          | ~ (v2_pre_topc @ X7))),
% 0.60/0.79      inference('cnf', [status(esa)], [fc10_tops_1])).
% 0.60/0.79  thf(d3_struct_0, axiom,
% 0.60/0.79    (![A:$i]:
% 0.60/0.79     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.60/0.79  thf('2', plain,
% 0.60/0.79      (![X3 : $i]:
% 0.60/0.79         (((k2_struct_0 @ X3) = (u1_struct_0 @ X3)) | ~ (l1_struct_0 @ X3))),
% 0.60/0.79      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.60/0.79  thf(dt_k2_subset_1, axiom,
% 0.60/0.79    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.60/0.79  thf('3', plain,
% 0.60/0.79      (![X1 : $i]: (m1_subset_1 @ (k2_subset_1 @ X1) @ (k1_zfmisc_1 @ X1))),
% 0.60/0.79      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 0.60/0.79  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.60/0.79  thf('4', plain, (![X0 : $i]: ((k2_subset_1 @ X0) = (X0))),
% 0.60/0.79      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.60/0.79  thf('5', plain, (![X1 : $i]: (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X1))),
% 0.60/0.79      inference('demod', [status(thm)], ['3', '4'])).
% 0.60/0.79  thf(d5_pre_topc, axiom,
% 0.60/0.79    (![A:$i]:
% 0.60/0.79     ( ( l1_pre_topc @ A ) =>
% 0.60/0.79       ( ![B:$i]:
% 0.60/0.79         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.60/0.79           ( ( v3_pre_topc @ B @ A ) <=>
% 0.60/0.79             ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) ) ) ) ))).
% 0.60/0.79  thf('6', plain,
% 0.60/0.79      (![X4 : $i, X5 : $i]:
% 0.60/0.79         (~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (u1_struct_0 @ X5)))
% 0.60/0.79          | ~ (v3_pre_topc @ X4 @ X5)
% 0.60/0.79          | (r2_hidden @ X4 @ (u1_pre_topc @ X5))
% 0.60/0.79          | ~ (l1_pre_topc @ X5))),
% 0.60/0.79      inference('cnf', [status(esa)], [d5_pre_topc])).
% 0.60/0.79  thf('7', plain,
% 0.60/0.79      (![X0 : $i]:
% 0.60/0.79         (~ (l1_pre_topc @ X0)
% 0.60/0.79          | (r2_hidden @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))
% 0.60/0.79          | ~ (v3_pre_topc @ (u1_struct_0 @ X0) @ X0))),
% 0.60/0.79      inference('sup-', [status(thm)], ['5', '6'])).
% 0.60/0.79  thf('8', plain,
% 0.60/0.79      (![X0 : $i]:
% 0.60/0.79         (~ (v3_pre_topc @ (k2_struct_0 @ X0) @ X0)
% 0.60/0.79          | ~ (l1_struct_0 @ X0)
% 0.60/0.79          | (r2_hidden @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))
% 0.60/0.79          | ~ (l1_pre_topc @ X0))),
% 0.60/0.79      inference('sup-', [status(thm)], ['2', '7'])).
% 0.60/0.79  thf('9', plain,
% 0.60/0.79      (![X0 : $i]:
% 0.60/0.79         (~ (v2_pre_topc @ X0)
% 0.60/0.79          | ~ (l1_pre_topc @ X0)
% 0.60/0.79          | ~ (l1_pre_topc @ X0)
% 0.60/0.79          | (r2_hidden @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))
% 0.60/0.79          | ~ (l1_struct_0 @ X0))),
% 0.60/0.79      inference('sup-', [status(thm)], ['1', '8'])).
% 0.60/0.79  thf('10', plain,
% 0.60/0.79      (![X0 : $i]:
% 0.60/0.79         (~ (l1_struct_0 @ X0)
% 0.60/0.79          | (r2_hidden @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))
% 0.60/0.79          | ~ (l1_pre_topc @ X0)
% 0.60/0.79          | ~ (v2_pre_topc @ X0))),
% 0.60/0.79      inference('simplify', [status(thm)], ['9'])).
% 0.60/0.79  thf('11', plain, (![X1 : $i]: (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X1))),
% 0.60/0.79      inference('demod', [status(thm)], ['3', '4'])).
% 0.60/0.79  thf(t103_tmap_1, axiom,
% 0.60/0.79    (![A:$i]:
% 0.60/0.79     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.60/0.79       ( ![B:$i]:
% 0.60/0.79         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.60/0.79           ( ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) <=>
% 0.60/0.79             ( ( u1_pre_topc @ A ) = ( k5_tmap_1 @ A @ B ) ) ) ) ) ))).
% 0.60/0.79  thf('12', plain,
% 0.60/0.79      (![X15 : $i, X16 : $i]:
% 0.60/0.79         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.60/0.79          | ~ (r2_hidden @ X15 @ (u1_pre_topc @ X16))
% 0.60/0.79          | ((u1_pre_topc @ X16) = (k5_tmap_1 @ X16 @ X15))
% 0.60/0.79          | ~ (l1_pre_topc @ X16)
% 0.60/0.79          | ~ (v2_pre_topc @ X16)
% 0.60/0.79          | (v2_struct_0 @ X16))),
% 0.60/0.79      inference('cnf', [status(esa)], [t103_tmap_1])).
% 0.60/0.79  thf('13', plain,
% 0.60/0.79      (![X0 : $i]:
% 0.60/0.79         ((v2_struct_0 @ X0)
% 0.60/0.79          | ~ (v2_pre_topc @ X0)
% 0.60/0.79          | ~ (l1_pre_topc @ X0)
% 0.60/0.79          | ((u1_pre_topc @ X0) = (k5_tmap_1 @ X0 @ (u1_struct_0 @ X0)))
% 0.60/0.79          | ~ (r2_hidden @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))),
% 0.60/0.79      inference('sup-', [status(thm)], ['11', '12'])).
% 0.60/0.79  thf('14', plain,
% 0.60/0.79      (![X0 : $i]:
% 0.60/0.79         (~ (v2_pre_topc @ X0)
% 0.60/0.79          | ~ (l1_pre_topc @ X0)
% 0.60/0.79          | ~ (l1_struct_0 @ X0)
% 0.60/0.79          | ((u1_pre_topc @ X0) = (k5_tmap_1 @ X0 @ (u1_struct_0 @ X0)))
% 0.60/0.79          | ~ (l1_pre_topc @ X0)
% 0.60/0.79          | ~ (v2_pre_topc @ X0)
% 0.60/0.79          | (v2_struct_0 @ X0))),
% 0.60/0.79      inference('sup-', [status(thm)], ['10', '13'])).
% 0.60/0.79  thf('15', plain,
% 0.60/0.79      (![X0 : $i]:
% 0.60/0.79         ((v2_struct_0 @ X0)
% 0.60/0.79          | ((u1_pre_topc @ X0) = (k5_tmap_1 @ X0 @ (u1_struct_0 @ X0)))
% 0.60/0.79          | ~ (l1_struct_0 @ X0)
% 0.60/0.79          | ~ (l1_pre_topc @ X0)
% 0.60/0.79          | ~ (v2_pre_topc @ X0))),
% 0.60/0.79      inference('simplify', [status(thm)], ['14'])).
% 0.60/0.79  thf('16', plain,
% 0.60/0.79      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.60/0.79          = (k8_tmap_1 @ sk_A @ sk_B))
% 0.60/0.79        | (v1_tsep_1 @ sk_B @ sk_A))),
% 0.60/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.79  thf('17', plain,
% 0.60/0.79      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.60/0.79          = (k8_tmap_1 @ sk_A @ sk_B)))
% 0.60/0.79         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.60/0.79                = (k8_tmap_1 @ sk_A @ sk_B))))),
% 0.60/0.79      inference('split', [status(esa)], ['16'])).
% 0.60/0.79  thf('18', plain,
% 0.60/0.79      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.60/0.79          != (k8_tmap_1 @ sk_A @ sk_B))
% 0.60/0.79        | ~ (m1_pre_topc @ sk_B @ sk_A)
% 0.60/0.79        | ~ (v1_tsep_1 @ sk_B @ sk_A))),
% 0.60/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.79  thf('19', plain,
% 0.60/0.79      (~ ((v1_tsep_1 @ sk_B @ sk_A)) | 
% 0.60/0.79       ~
% 0.60/0.79       (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.60/0.79          = (k8_tmap_1 @ sk_A @ sk_B))) | 
% 0.60/0.79       ~ ((m1_pre_topc @ sk_B @ sk_A))),
% 0.60/0.79      inference('split', [status(esa)], ['18'])).
% 0.60/0.79  thf('20', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.60/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.79  thf('21', plain,
% 0.60/0.79      ((~ (m1_pre_topc @ sk_B @ sk_A)) <= (~ ((m1_pre_topc @ sk_B @ sk_A)))),
% 0.60/0.79      inference('split', [status(esa)], ['18'])).
% 0.60/0.79  thf('22', plain, (((m1_pre_topc @ sk_B @ sk_A))),
% 0.60/0.79      inference('sup-', [status(thm)], ['20', '21'])).
% 0.60/0.79  thf('23', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.60/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.79  thf(t1_tsep_1, axiom,
% 0.60/0.79    (![A:$i]:
% 0.60/0.79     ( ( l1_pre_topc @ A ) =>
% 0.60/0.79       ( ![B:$i]:
% 0.60/0.79         ( ( m1_pre_topc @ B @ A ) =>
% 0.60/0.79           ( m1_subset_1 @
% 0.60/0.79             ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.60/0.79  thf('24', plain,
% 0.60/0.79      (![X22 : $i, X23 : $i]:
% 0.60/0.79         (~ (m1_pre_topc @ X22 @ X23)
% 0.60/0.79          | (m1_subset_1 @ (u1_struct_0 @ X22) @ 
% 0.60/0.79             (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 0.60/0.79          | ~ (l1_pre_topc @ X23))),
% 0.60/0.79      inference('cnf', [status(esa)], [t1_tsep_1])).
% 0.60/0.79  thf('25', plain,
% 0.60/0.79      ((~ (l1_pre_topc @ sk_A)
% 0.60/0.79        | (m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.60/0.79           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.60/0.79      inference('sup-', [status(thm)], ['23', '24'])).
% 0.60/0.79  thf('26', plain, ((l1_pre_topc @ sk_A)),
% 0.60/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.79  thf('27', plain,
% 0.60/0.79      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.60/0.79        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.60/0.79      inference('demod', [status(thm)], ['25', '26'])).
% 0.60/0.79  thf(t114_tmap_1, axiom,
% 0.60/0.79    (![A:$i]:
% 0.60/0.79     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.60/0.79       ( ![B:$i]:
% 0.60/0.79         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.60/0.79           ( ( ( u1_struct_0 @ ( k8_tmap_1 @ A @ B ) ) = ( u1_struct_0 @ A ) ) & 
% 0.60/0.79             ( ![C:$i]:
% 0.60/0.79               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.60/0.79                 ( ( ( C ) = ( u1_struct_0 @ B ) ) =>
% 0.60/0.79                   ( ( u1_pre_topc @ ( k8_tmap_1 @ A @ B ) ) =
% 0.60/0.79                     ( k5_tmap_1 @ A @ C ) ) ) ) ) ) ) ) ))).
% 0.60/0.79  thf('28', plain,
% 0.60/0.79      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.60/0.79         ((v2_struct_0 @ X19)
% 0.60/0.79          | ~ (m1_pre_topc @ X19 @ X20)
% 0.60/0.79          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.60/0.79          | ((u1_pre_topc @ (k8_tmap_1 @ X20 @ X19)) = (k5_tmap_1 @ X20 @ X21))
% 0.60/0.79          | ((X21) != (u1_struct_0 @ X19))
% 0.60/0.79          | ~ (l1_pre_topc @ X20)
% 0.60/0.79          | ~ (v2_pre_topc @ X20)
% 0.60/0.79          | (v2_struct_0 @ X20))),
% 0.60/0.79      inference('cnf', [status(esa)], [t114_tmap_1])).
% 0.60/0.79  thf('29', plain,
% 0.60/0.79      (![X19 : $i, X20 : $i]:
% 0.60/0.79         ((v2_struct_0 @ X20)
% 0.60/0.79          | ~ (v2_pre_topc @ X20)
% 0.60/0.79          | ~ (l1_pre_topc @ X20)
% 0.60/0.79          | ((u1_pre_topc @ (k8_tmap_1 @ X20 @ X19))
% 0.60/0.79              = (k5_tmap_1 @ X20 @ (u1_struct_0 @ X19)))
% 0.60/0.79          | ~ (m1_subset_1 @ (u1_struct_0 @ X19) @ 
% 0.60/0.79               (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.60/0.79          | ~ (m1_pre_topc @ X19 @ X20)
% 0.60/0.79          | (v2_struct_0 @ X19))),
% 0.60/0.79      inference('simplify', [status(thm)], ['28'])).
% 0.60/0.79  thf('30', plain,
% 0.60/0.79      (((v2_struct_0 @ sk_B)
% 0.60/0.79        | ~ (m1_pre_topc @ sk_B @ sk_A)
% 0.60/0.79        | ((u1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.60/0.79            = (k5_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 0.60/0.79        | ~ (l1_pre_topc @ sk_A)
% 0.60/0.79        | ~ (v2_pre_topc @ sk_A)
% 0.60/0.79        | (v2_struct_0 @ sk_A))),
% 0.60/0.79      inference('sup-', [status(thm)], ['27', '29'])).
% 0.60/0.79  thf('31', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.60/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.79  thf('32', plain, ((l1_pre_topc @ sk_A)),
% 0.60/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.79  thf('33', plain, ((v2_pre_topc @ sk_A)),
% 0.60/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.79  thf('34', plain,
% 0.60/0.79      (((v2_struct_0 @ sk_B)
% 0.60/0.79        | ((u1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.60/0.79            = (k5_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 0.60/0.79        | (v2_struct_0 @ sk_A))),
% 0.60/0.79      inference('demod', [status(thm)], ['30', '31', '32', '33'])).
% 0.60/0.79  thf('35', plain, (~ (v2_struct_0 @ sk_B)),
% 0.60/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.79  thf('36', plain,
% 0.60/0.79      (((v2_struct_0 @ sk_A)
% 0.60/0.79        | ((u1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.60/0.79            = (k5_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B))))),
% 0.60/0.79      inference('clc', [status(thm)], ['34', '35'])).
% 0.60/0.79  thf('37', plain, (~ (v2_struct_0 @ sk_A)),
% 0.60/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.79  thf('38', plain,
% 0.60/0.79      (((u1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.60/0.79         = (k5_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))),
% 0.60/0.79      inference('clc', [status(thm)], ['36', '37'])).
% 0.60/0.79  thf('39', plain,
% 0.60/0.79      (((v1_tsep_1 @ sk_B @ sk_A)) <= (((v1_tsep_1 @ sk_B @ sk_A)))),
% 0.60/0.79      inference('split', [status(esa)], ['16'])).
% 0.60/0.79  thf('40', plain,
% 0.60/0.79      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.60/0.79        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.60/0.79      inference('demod', [status(thm)], ['25', '26'])).
% 0.60/0.79  thf(d1_tsep_1, axiom,
% 0.60/0.79    (![A:$i]:
% 0.60/0.79     ( ( l1_pre_topc @ A ) =>
% 0.60/0.79       ( ![B:$i]:
% 0.60/0.79         ( ( m1_pre_topc @ B @ A ) =>
% 0.60/0.79           ( ( v1_tsep_1 @ B @ A ) <=>
% 0.60/0.79             ( ![C:$i]:
% 0.60/0.79               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.60/0.79                 ( ( ( C ) = ( u1_struct_0 @ B ) ) => ( v3_pre_topc @ C @ A ) ) ) ) ) ) ) ))).
% 0.60/0.79  thf('41', plain,
% 0.60/0.79      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.60/0.79         (~ (m1_pre_topc @ X8 @ X9)
% 0.60/0.79          | ~ (v1_tsep_1 @ X8 @ X9)
% 0.60/0.79          | ((X10) != (u1_struct_0 @ X8))
% 0.60/0.79          | (v3_pre_topc @ X10 @ X9)
% 0.60/0.79          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.60/0.79          | ~ (l1_pre_topc @ X9))),
% 0.60/0.79      inference('cnf', [status(esa)], [d1_tsep_1])).
% 0.60/0.79  thf('42', plain,
% 0.60/0.79      (![X8 : $i, X9 : $i]:
% 0.60/0.79         (~ (l1_pre_topc @ X9)
% 0.60/0.79          | ~ (m1_subset_1 @ (u1_struct_0 @ X8) @ 
% 0.60/0.79               (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.60/0.79          | (v3_pre_topc @ (u1_struct_0 @ X8) @ X9)
% 0.60/0.79          | ~ (v1_tsep_1 @ X8 @ X9)
% 0.60/0.79          | ~ (m1_pre_topc @ X8 @ X9))),
% 0.60/0.79      inference('simplify', [status(thm)], ['41'])).
% 0.60/0.79  thf('43', plain,
% 0.60/0.79      ((~ (m1_pre_topc @ sk_B @ sk_A)
% 0.60/0.79        | ~ (v1_tsep_1 @ sk_B @ sk_A)
% 0.60/0.79        | (v3_pre_topc @ (u1_struct_0 @ sk_B) @ sk_A)
% 0.60/0.79        | ~ (l1_pre_topc @ sk_A))),
% 0.60/0.79      inference('sup-', [status(thm)], ['40', '42'])).
% 0.60/0.79  thf('44', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.60/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.79  thf('45', plain, ((l1_pre_topc @ sk_A)),
% 0.60/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.79  thf('46', plain,
% 0.60/0.79      ((~ (v1_tsep_1 @ sk_B @ sk_A)
% 0.60/0.79        | (v3_pre_topc @ (u1_struct_0 @ sk_B) @ sk_A))),
% 0.60/0.79      inference('demod', [status(thm)], ['43', '44', '45'])).
% 0.60/0.79  thf('47', plain,
% 0.60/0.79      (((v3_pre_topc @ (u1_struct_0 @ sk_B) @ sk_A))
% 0.60/0.79         <= (((v1_tsep_1 @ sk_B @ sk_A)))),
% 0.60/0.79      inference('sup-', [status(thm)], ['39', '46'])).
% 0.60/0.79  thf('48', plain,
% 0.60/0.79      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.60/0.79        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.60/0.79      inference('demod', [status(thm)], ['25', '26'])).
% 0.60/0.79  thf('49', plain,
% 0.60/0.79      (![X4 : $i, X5 : $i]:
% 0.60/0.79         (~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (u1_struct_0 @ X5)))
% 0.60/0.79          | ~ (v3_pre_topc @ X4 @ X5)
% 0.60/0.79          | (r2_hidden @ X4 @ (u1_pre_topc @ X5))
% 0.60/0.79          | ~ (l1_pre_topc @ X5))),
% 0.60/0.79      inference('cnf', [status(esa)], [d5_pre_topc])).
% 0.60/0.79  thf('50', plain,
% 0.60/0.79      ((~ (l1_pre_topc @ sk_A)
% 0.60/0.79        | (r2_hidden @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_A))
% 0.60/0.79        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_B) @ sk_A))),
% 0.60/0.79      inference('sup-', [status(thm)], ['48', '49'])).
% 0.60/0.79  thf('51', plain, ((l1_pre_topc @ sk_A)),
% 0.60/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.79  thf('52', plain,
% 0.60/0.79      (((r2_hidden @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_A))
% 0.60/0.79        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_B) @ sk_A))),
% 0.60/0.79      inference('demod', [status(thm)], ['50', '51'])).
% 0.60/0.79  thf('53', plain,
% 0.60/0.79      (((r2_hidden @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_A)))
% 0.60/0.79         <= (((v1_tsep_1 @ sk_B @ sk_A)))),
% 0.60/0.79      inference('sup-', [status(thm)], ['47', '52'])).
% 0.60/0.79  thf('54', plain,
% 0.60/0.79      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.60/0.79        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.60/0.79      inference('demod', [status(thm)], ['25', '26'])).
% 0.60/0.79  thf('55', plain,
% 0.60/0.79      (![X15 : $i, X16 : $i]:
% 0.60/0.79         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.60/0.79          | ~ (r2_hidden @ X15 @ (u1_pre_topc @ X16))
% 0.60/0.79          | ((u1_pre_topc @ X16) = (k5_tmap_1 @ X16 @ X15))
% 0.60/0.79          | ~ (l1_pre_topc @ X16)
% 0.60/0.79          | ~ (v2_pre_topc @ X16)
% 0.60/0.79          | (v2_struct_0 @ X16))),
% 0.60/0.79      inference('cnf', [status(esa)], [t103_tmap_1])).
% 0.60/0.79  thf('56', plain,
% 0.60/0.79      (((v2_struct_0 @ sk_A)
% 0.60/0.79        | ~ (v2_pre_topc @ sk_A)
% 0.60/0.79        | ~ (l1_pre_topc @ sk_A)
% 0.60/0.79        | ((u1_pre_topc @ sk_A) = (k5_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 0.60/0.79        | ~ (r2_hidden @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_A)))),
% 0.60/0.79      inference('sup-', [status(thm)], ['54', '55'])).
% 0.60/0.79  thf('57', plain, ((v2_pre_topc @ sk_A)),
% 0.60/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.79  thf('58', plain, ((l1_pre_topc @ sk_A)),
% 0.60/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.79  thf('59', plain,
% 0.60/0.79      (((v2_struct_0 @ sk_A)
% 0.60/0.79        | ((u1_pre_topc @ sk_A) = (k5_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 0.60/0.79        | ~ (r2_hidden @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_A)))),
% 0.60/0.79      inference('demod', [status(thm)], ['56', '57', '58'])).
% 0.60/0.79  thf('60', plain, (~ (v2_struct_0 @ sk_A)),
% 0.60/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.79  thf('61', plain,
% 0.60/0.79      ((~ (r2_hidden @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_A))
% 0.60/0.79        | ((u1_pre_topc @ sk_A) = (k5_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B))))),
% 0.60/0.79      inference('clc', [status(thm)], ['59', '60'])).
% 0.60/0.79  thf('62', plain,
% 0.60/0.79      ((((u1_pre_topc @ sk_A) = (k5_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B))))
% 0.60/0.79         <= (((v1_tsep_1 @ sk_B @ sk_A)))),
% 0.60/0.79      inference('sup-', [status(thm)], ['53', '61'])).
% 0.60/0.79  thf('63', plain,
% 0.60/0.79      ((((u1_pre_topc @ sk_A) = (u1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))))
% 0.60/0.79         <= (((v1_tsep_1 @ sk_B @ sk_A)))),
% 0.60/0.79      inference('sup+', [status(thm)], ['38', '62'])).
% 0.60/0.79  thf('64', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.60/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.79  thf('65', plain,
% 0.60/0.79      (![X19 : $i, X20 : $i]:
% 0.60/0.79         ((v2_struct_0 @ X19)
% 0.60/0.79          | ~ (m1_pre_topc @ X19 @ X20)
% 0.60/0.79          | ((u1_struct_0 @ (k8_tmap_1 @ X20 @ X19)) = (u1_struct_0 @ X20))
% 0.60/0.79          | ~ (l1_pre_topc @ X20)
% 0.60/0.79          | ~ (v2_pre_topc @ X20)
% 0.60/0.79          | (v2_struct_0 @ X20))),
% 0.60/0.79      inference('cnf', [status(esa)], [t114_tmap_1])).
% 0.60/0.79  thf('66', plain,
% 0.60/0.79      (((v2_struct_0 @ sk_A)
% 0.60/0.79        | ~ (v2_pre_topc @ sk_A)
% 0.60/0.79        | ~ (l1_pre_topc @ sk_A)
% 0.60/0.79        | ((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))
% 0.60/0.79        | (v2_struct_0 @ sk_B))),
% 0.60/0.79      inference('sup-', [status(thm)], ['64', '65'])).
% 0.60/0.79  thf('67', plain, ((v2_pre_topc @ sk_A)),
% 0.60/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.79  thf('68', plain, ((l1_pre_topc @ sk_A)),
% 0.60/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.79  thf('69', plain,
% 0.60/0.79      (((v2_struct_0 @ sk_A)
% 0.60/0.79        | ((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))
% 0.60/0.79        | (v2_struct_0 @ sk_B))),
% 0.60/0.79      inference('demod', [status(thm)], ['66', '67', '68'])).
% 0.60/0.79  thf('70', plain, (~ (v2_struct_0 @ sk_A)),
% 0.60/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.79  thf('71', plain,
% 0.60/0.79      (((v2_struct_0 @ sk_B)
% 0.60/0.79        | ((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A)))),
% 0.60/0.79      inference('clc', [status(thm)], ['69', '70'])).
% 0.60/0.79  thf('72', plain, (~ (v2_struct_0 @ sk_B)),
% 0.60/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.79  thf('73', plain,
% 0.60/0.79      (((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 0.60/0.79      inference('clc', [status(thm)], ['71', '72'])).
% 0.60/0.79  thf(abstractness_v1_pre_topc, axiom,
% 0.60/0.79    (![A:$i]:
% 0.60/0.79     ( ( l1_pre_topc @ A ) =>
% 0.60/0.79       ( ( v1_pre_topc @ A ) =>
% 0.60/0.79         ( ( A ) = ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ))).
% 0.60/0.79  thf('74', plain,
% 0.60/0.79      (![X2 : $i]:
% 0.60/0.79         (~ (v1_pre_topc @ X2)
% 0.60/0.79          | ((X2) = (g1_pre_topc @ (u1_struct_0 @ X2) @ (u1_pre_topc @ X2)))
% 0.60/0.79          | ~ (l1_pre_topc @ X2))),
% 0.60/0.79      inference('cnf', [status(esa)], [abstractness_v1_pre_topc])).
% 0.60/0.79  thf('75', plain,
% 0.60/0.79      ((((k8_tmap_1 @ sk_A @ sk_B)
% 0.60/0.79          = (g1_pre_topc @ (u1_struct_0 @ sk_A) @ 
% 0.60/0.79             (u1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))))
% 0.60/0.79        | ~ (l1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.60/0.79        | ~ (v1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B)))),
% 0.60/0.79      inference('sup+', [status(thm)], ['73', '74'])).
% 0.60/0.79  thf('76', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.60/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.79  thf(dt_k8_tmap_1, axiom,
% 0.60/0.79    (![A:$i,B:$i]:
% 0.60/0.79     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.60/0.79         ( l1_pre_topc @ A ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.60/0.79       ( ( v1_pre_topc @ ( k8_tmap_1 @ A @ B ) ) & 
% 0.60/0.79         ( v2_pre_topc @ ( k8_tmap_1 @ A @ B ) ) & 
% 0.60/0.79         ( l1_pre_topc @ ( k8_tmap_1 @ A @ B ) ) ) ))).
% 0.60/0.79  thf('77', plain,
% 0.60/0.79      (![X13 : $i, X14 : $i]:
% 0.60/0.79         (~ (l1_pre_topc @ X13)
% 0.60/0.79          | ~ (v2_pre_topc @ X13)
% 0.60/0.79          | (v2_struct_0 @ X13)
% 0.60/0.79          | ~ (m1_pre_topc @ X14 @ X13)
% 0.60/0.79          | (l1_pre_topc @ (k8_tmap_1 @ X13 @ X14)))),
% 0.60/0.79      inference('cnf', [status(esa)], [dt_k8_tmap_1])).
% 0.60/0.79  thf('78', plain,
% 0.60/0.79      (((l1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.60/0.79        | (v2_struct_0 @ sk_A)
% 0.60/0.79        | ~ (v2_pre_topc @ sk_A)
% 0.60/0.79        | ~ (l1_pre_topc @ sk_A))),
% 0.60/0.79      inference('sup-', [status(thm)], ['76', '77'])).
% 0.60/0.79  thf('79', plain, ((v2_pre_topc @ sk_A)),
% 0.60/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.79  thf('80', plain, ((l1_pre_topc @ sk_A)),
% 0.60/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.79  thf('81', plain,
% 0.60/0.79      (((l1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B)) | (v2_struct_0 @ sk_A))),
% 0.60/0.79      inference('demod', [status(thm)], ['78', '79', '80'])).
% 0.60/0.79  thf('82', plain, (~ (v2_struct_0 @ sk_A)),
% 0.60/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.79  thf('83', plain, ((l1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))),
% 0.60/0.79      inference('clc', [status(thm)], ['81', '82'])).
% 0.60/0.79  thf('84', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.60/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.79  thf('85', plain,
% 0.60/0.79      (![X13 : $i, X14 : $i]:
% 0.60/0.79         (~ (l1_pre_topc @ X13)
% 0.60/0.79          | ~ (v2_pre_topc @ X13)
% 0.60/0.79          | (v2_struct_0 @ X13)
% 0.60/0.79          | ~ (m1_pre_topc @ X14 @ X13)
% 0.60/0.79          | (v1_pre_topc @ (k8_tmap_1 @ X13 @ X14)))),
% 0.60/0.79      inference('cnf', [status(esa)], [dt_k8_tmap_1])).
% 0.60/0.79  thf('86', plain,
% 0.60/0.79      (((v1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.60/0.79        | (v2_struct_0 @ sk_A)
% 0.60/0.79        | ~ (v2_pre_topc @ sk_A)
% 0.60/0.79        | ~ (l1_pre_topc @ sk_A))),
% 0.60/0.79      inference('sup-', [status(thm)], ['84', '85'])).
% 0.60/0.79  thf('87', plain, ((v2_pre_topc @ sk_A)),
% 0.60/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.79  thf('88', plain, ((l1_pre_topc @ sk_A)),
% 0.60/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.79  thf('89', plain,
% 0.60/0.79      (((v1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B)) | (v2_struct_0 @ sk_A))),
% 0.60/0.79      inference('demod', [status(thm)], ['86', '87', '88'])).
% 0.60/0.79  thf('90', plain, (~ (v2_struct_0 @ sk_A)),
% 0.60/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.79  thf('91', plain, ((v1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))),
% 0.60/0.79      inference('clc', [status(thm)], ['89', '90'])).
% 0.60/0.79  thf('92', plain,
% 0.60/0.79      (((k8_tmap_1 @ sk_A @ sk_B)
% 0.60/0.79         = (g1_pre_topc @ (u1_struct_0 @ sk_A) @ 
% 0.60/0.79            (u1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))))),
% 0.60/0.79      inference('demod', [status(thm)], ['75', '83', '91'])).
% 0.60/0.79  thf('93', plain,
% 0.60/0.79      ((((k8_tmap_1 @ sk_A @ sk_B)
% 0.60/0.79          = (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))
% 0.60/0.79         <= (((v1_tsep_1 @ sk_B @ sk_A)))),
% 0.60/0.79      inference('sup+', [status(thm)], ['63', '92'])).
% 0.60/0.79  thf('94', plain,
% 0.60/0.79      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.60/0.79          != (k8_tmap_1 @ sk_A @ sk_B)))
% 0.60/0.79         <= (~
% 0.60/0.79             (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.60/0.79                = (k8_tmap_1 @ sk_A @ sk_B))))),
% 0.60/0.79      inference('split', [status(esa)], ['18'])).
% 0.60/0.79  thf('95', plain,
% 0.60/0.79      ((((k8_tmap_1 @ sk_A @ sk_B) != (k8_tmap_1 @ sk_A @ sk_B)))
% 0.60/0.79         <= (~
% 0.60/0.79             (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.60/0.79                = (k8_tmap_1 @ sk_A @ sk_B))) & 
% 0.60/0.79             ((v1_tsep_1 @ sk_B @ sk_A)))),
% 0.60/0.79      inference('sup-', [status(thm)], ['93', '94'])).
% 0.60/0.79  thf('96', plain,
% 0.60/0.79      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.60/0.79          = (k8_tmap_1 @ sk_A @ sk_B))) | 
% 0.60/0.79       ~ ((v1_tsep_1 @ sk_B @ sk_A))),
% 0.60/0.79      inference('simplify', [status(thm)], ['95'])).
% 0.60/0.79  thf('97', plain,
% 0.60/0.79      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.60/0.79          = (k8_tmap_1 @ sk_A @ sk_B))) | 
% 0.60/0.79       ((v1_tsep_1 @ sk_B @ sk_A))),
% 0.60/0.79      inference('split', [status(esa)], ['16'])).
% 0.60/0.79  thf('98', plain,
% 0.60/0.79      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.60/0.79          = (k8_tmap_1 @ sk_A @ sk_B)))),
% 0.60/0.79      inference('sat_resolution*', [status(thm)], ['19', '22', '96', '97'])).
% 0.60/0.79  thf('99', plain,
% 0.60/0.79      (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.60/0.79         = (k8_tmap_1 @ sk_A @ sk_B))),
% 0.60/0.79      inference('simpl_trail', [status(thm)], ['17', '98'])).
% 0.60/0.79  thf('100', plain,
% 0.60/0.79      (![X0 : $i]:
% 0.60/0.79         ((v2_struct_0 @ X0)
% 0.60/0.79          | ((u1_pre_topc @ X0) = (k5_tmap_1 @ X0 @ (u1_struct_0 @ X0)))
% 0.60/0.79          | ~ (l1_struct_0 @ X0)
% 0.60/0.79          | ~ (l1_pre_topc @ X0)
% 0.60/0.79          | ~ (v2_pre_topc @ X0))),
% 0.60/0.79      inference('simplify', [status(thm)], ['14'])).
% 0.60/0.79  thf('101', plain, (![X1 : $i]: (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X1))),
% 0.60/0.79      inference('demod', [status(thm)], ['3', '4'])).
% 0.60/0.79  thf(t104_tmap_1, axiom,
% 0.60/0.79    (![A:$i]:
% 0.60/0.79     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.60/0.79       ( ![B:$i]:
% 0.60/0.79         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.60/0.79           ( ( ( u1_struct_0 @ ( k6_tmap_1 @ A @ B ) ) = ( u1_struct_0 @ A ) ) & 
% 0.60/0.79             ( ( u1_pre_topc @ ( k6_tmap_1 @ A @ B ) ) = ( k5_tmap_1 @ A @ B ) ) ) ) ) ))).
% 0.60/0.79  thf('102', plain,
% 0.60/0.79      (![X17 : $i, X18 : $i]:
% 0.60/0.79         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.60/0.79          | ((u1_pre_topc @ (k6_tmap_1 @ X18 @ X17)) = (k5_tmap_1 @ X18 @ X17))
% 0.60/0.79          | ~ (l1_pre_topc @ X18)
% 0.60/0.79          | ~ (v2_pre_topc @ X18)
% 0.60/0.79          | (v2_struct_0 @ X18))),
% 0.60/0.79      inference('cnf', [status(esa)], [t104_tmap_1])).
% 0.60/0.79  thf('103', plain,
% 0.60/0.79      (![X0 : $i]:
% 0.60/0.79         ((v2_struct_0 @ X0)
% 0.60/0.79          | ~ (v2_pre_topc @ X0)
% 0.60/0.79          | ~ (l1_pre_topc @ X0)
% 0.60/0.79          | ((u1_pre_topc @ (k6_tmap_1 @ X0 @ (u1_struct_0 @ X0)))
% 0.60/0.79              = (k5_tmap_1 @ X0 @ (u1_struct_0 @ X0))))),
% 0.60/0.79      inference('sup-', [status(thm)], ['101', '102'])).
% 0.60/0.79  thf('104', plain, (![X1 : $i]: (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X1))),
% 0.60/0.79      inference('demod', [status(thm)], ['3', '4'])).
% 0.60/0.79  thf(dt_k6_tmap_1, axiom,
% 0.60/0.79    (![A:$i,B:$i]:
% 0.60/0.79     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.60/0.79         ( l1_pre_topc @ A ) & 
% 0.60/0.79         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.60/0.79       ( ( v1_pre_topc @ ( k6_tmap_1 @ A @ B ) ) & 
% 0.60/0.79         ( v2_pre_topc @ ( k6_tmap_1 @ A @ B ) ) & 
% 0.60/0.79         ( l1_pre_topc @ ( k6_tmap_1 @ A @ B ) ) ) ))).
% 0.60/0.79  thf('105', plain,
% 0.60/0.79      (![X11 : $i, X12 : $i]:
% 0.60/0.79         (~ (l1_pre_topc @ X11)
% 0.60/0.79          | ~ (v2_pre_topc @ X11)
% 0.60/0.79          | (v2_struct_0 @ X11)
% 0.60/0.79          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.60/0.79          | (v1_pre_topc @ (k6_tmap_1 @ X11 @ X12)))),
% 0.60/0.79      inference('cnf', [status(esa)], [dt_k6_tmap_1])).
% 0.60/0.79  thf('106', plain,
% 0.60/0.79      (![X0 : $i]:
% 0.60/0.79         ((v1_pre_topc @ (k6_tmap_1 @ X0 @ (u1_struct_0 @ X0)))
% 0.60/0.79          | (v2_struct_0 @ X0)
% 0.60/0.79          | ~ (v2_pre_topc @ X0)
% 0.60/0.79          | ~ (l1_pre_topc @ X0))),
% 0.60/0.79      inference('sup-', [status(thm)], ['104', '105'])).
% 0.60/0.79  thf('107', plain, (![X1 : $i]: (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X1))),
% 0.60/0.79      inference('demod', [status(thm)], ['3', '4'])).
% 0.60/0.79  thf('108', plain,
% 0.60/0.79      (![X11 : $i, X12 : $i]:
% 0.60/0.79         (~ (l1_pre_topc @ X11)
% 0.60/0.79          | ~ (v2_pre_topc @ X11)
% 0.60/0.79          | (v2_struct_0 @ X11)
% 0.60/0.79          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.60/0.79          | (l1_pre_topc @ (k6_tmap_1 @ X11 @ X12)))),
% 0.60/0.79      inference('cnf', [status(esa)], [dt_k6_tmap_1])).
% 0.60/0.79  thf('109', plain,
% 0.60/0.79      (![X0 : $i]:
% 0.60/0.79         ((l1_pre_topc @ (k6_tmap_1 @ X0 @ (u1_struct_0 @ X0)))
% 0.60/0.79          | (v2_struct_0 @ X0)
% 0.60/0.79          | ~ (v2_pre_topc @ X0)
% 0.60/0.79          | ~ (l1_pre_topc @ X0))),
% 0.60/0.79      inference('sup-', [status(thm)], ['107', '108'])).
% 0.60/0.79  thf('110', plain, (![X1 : $i]: (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X1))),
% 0.60/0.79      inference('demod', [status(thm)], ['3', '4'])).
% 0.60/0.79  thf('111', plain,
% 0.60/0.79      (![X17 : $i, X18 : $i]:
% 0.60/0.79         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.60/0.79          | ((u1_struct_0 @ (k6_tmap_1 @ X18 @ X17)) = (u1_struct_0 @ X18))
% 0.60/0.79          | ~ (l1_pre_topc @ X18)
% 0.60/0.79          | ~ (v2_pre_topc @ X18)
% 0.60/0.79          | (v2_struct_0 @ X18))),
% 0.60/0.79      inference('cnf', [status(esa)], [t104_tmap_1])).
% 0.60/0.79  thf('112', plain,
% 0.60/0.79      (![X0 : $i]:
% 0.60/0.79         ((v2_struct_0 @ X0)
% 0.60/0.79          | ~ (v2_pre_topc @ X0)
% 0.60/0.79          | ~ (l1_pre_topc @ X0)
% 0.60/0.79          | ((u1_struct_0 @ (k6_tmap_1 @ X0 @ (u1_struct_0 @ X0)))
% 0.60/0.79              = (u1_struct_0 @ X0)))),
% 0.60/0.79      inference('sup-', [status(thm)], ['110', '111'])).
% 0.60/0.79  thf('113', plain,
% 0.60/0.79      (![X2 : $i]:
% 0.60/0.79         (~ (v1_pre_topc @ X2)
% 0.60/0.79          | ((X2) = (g1_pre_topc @ (u1_struct_0 @ X2) @ (u1_pre_topc @ X2)))
% 0.60/0.79          | ~ (l1_pre_topc @ X2))),
% 0.60/0.79      inference('cnf', [status(esa)], [abstractness_v1_pre_topc])).
% 0.60/0.79  thf('114', plain,
% 0.60/0.79      (![X0 : $i]:
% 0.60/0.79         (((k6_tmap_1 @ X0 @ (u1_struct_0 @ X0))
% 0.60/0.79            = (g1_pre_topc @ (u1_struct_0 @ X0) @ 
% 0.60/0.79               (u1_pre_topc @ (k6_tmap_1 @ X0 @ (u1_struct_0 @ X0)))))
% 0.60/0.79          | ~ (l1_pre_topc @ X0)
% 0.60/0.79          | ~ (v2_pre_topc @ X0)
% 0.60/0.79          | (v2_struct_0 @ X0)
% 0.60/0.79          | ~ (l1_pre_topc @ (k6_tmap_1 @ X0 @ (u1_struct_0 @ X0)))
% 0.60/0.79          | ~ (v1_pre_topc @ (k6_tmap_1 @ X0 @ (u1_struct_0 @ X0))))),
% 0.60/0.79      inference('sup+', [status(thm)], ['112', '113'])).
% 0.60/0.79  thf('115', plain,
% 0.60/0.79      (![X0 : $i]:
% 0.60/0.79         (~ (l1_pre_topc @ X0)
% 0.60/0.79          | ~ (v2_pre_topc @ X0)
% 0.60/0.79          | (v2_struct_0 @ X0)
% 0.60/0.79          | ~ (v1_pre_topc @ (k6_tmap_1 @ X0 @ (u1_struct_0 @ X0)))
% 0.60/0.79          | (v2_struct_0 @ X0)
% 0.60/0.79          | ~ (v2_pre_topc @ X0)
% 0.60/0.79          | ~ (l1_pre_topc @ X0)
% 0.60/0.79          | ((k6_tmap_1 @ X0 @ (u1_struct_0 @ X0))
% 0.60/0.79              = (g1_pre_topc @ (u1_struct_0 @ X0) @ 
% 0.60/0.79                 (u1_pre_topc @ (k6_tmap_1 @ X0 @ (u1_struct_0 @ X0))))))),
% 0.60/0.79      inference('sup-', [status(thm)], ['109', '114'])).
% 0.60/0.79  thf('116', plain,
% 0.60/0.79      (![X0 : $i]:
% 0.60/0.79         (((k6_tmap_1 @ X0 @ (u1_struct_0 @ X0))
% 0.60/0.79            = (g1_pre_topc @ (u1_struct_0 @ X0) @ 
% 0.60/0.79               (u1_pre_topc @ (k6_tmap_1 @ X0 @ (u1_struct_0 @ X0)))))
% 0.60/0.79          | ~ (v1_pre_topc @ (k6_tmap_1 @ X0 @ (u1_struct_0 @ X0)))
% 0.60/0.79          | (v2_struct_0 @ X0)
% 0.60/0.79          | ~ (v2_pre_topc @ X0)
% 0.60/0.79          | ~ (l1_pre_topc @ X0))),
% 0.60/0.79      inference('simplify', [status(thm)], ['115'])).
% 0.60/0.79  thf('117', plain,
% 0.60/0.79      (![X0 : $i]:
% 0.60/0.79         (~ (l1_pre_topc @ X0)
% 0.60/0.79          | ~ (v2_pre_topc @ X0)
% 0.60/0.79          | (v2_struct_0 @ X0)
% 0.60/0.79          | ~ (l1_pre_topc @ X0)
% 0.60/0.79          | ~ (v2_pre_topc @ X0)
% 0.60/0.79          | (v2_struct_0 @ X0)
% 0.60/0.79          | ((k6_tmap_1 @ X0 @ (u1_struct_0 @ X0))
% 0.60/0.79              = (g1_pre_topc @ (u1_struct_0 @ X0) @ 
% 0.60/0.79                 (u1_pre_topc @ (k6_tmap_1 @ X0 @ (u1_struct_0 @ X0))))))),
% 0.60/0.79      inference('sup-', [status(thm)], ['106', '116'])).
% 0.60/0.79  thf('118', plain,
% 0.60/0.79      (![X0 : $i]:
% 0.60/0.79         (((k6_tmap_1 @ X0 @ (u1_struct_0 @ X0))
% 0.60/0.79            = (g1_pre_topc @ (u1_struct_0 @ X0) @ 
% 0.60/0.79               (u1_pre_topc @ (k6_tmap_1 @ X0 @ (u1_struct_0 @ X0)))))
% 0.60/0.79          | (v2_struct_0 @ X0)
% 0.60/0.79          | ~ (v2_pre_topc @ X0)
% 0.60/0.79          | ~ (l1_pre_topc @ X0))),
% 0.60/0.79      inference('simplify', [status(thm)], ['117'])).
% 0.60/0.79  thf('119', plain,
% 0.60/0.79      (![X0 : $i]:
% 0.60/0.79         (((k6_tmap_1 @ X0 @ (u1_struct_0 @ X0))
% 0.60/0.79            = (g1_pre_topc @ (u1_struct_0 @ X0) @ 
% 0.60/0.79               (k5_tmap_1 @ X0 @ (u1_struct_0 @ X0))))
% 0.60/0.79          | ~ (l1_pre_topc @ X0)
% 0.60/0.79          | ~ (v2_pre_topc @ X0)
% 0.60/0.79          | (v2_struct_0 @ X0)
% 0.60/0.79          | ~ (l1_pre_topc @ X0)
% 0.60/0.79          | ~ (v2_pre_topc @ X0)
% 0.60/0.79          | (v2_struct_0 @ X0))),
% 0.60/0.79      inference('sup+', [status(thm)], ['103', '118'])).
% 0.60/0.79  thf('120', plain,
% 0.60/0.79      (![X0 : $i]:
% 0.60/0.79         ((v2_struct_0 @ X0)
% 0.60/0.79          | ~ (v2_pre_topc @ X0)
% 0.60/0.79          | ~ (l1_pre_topc @ X0)
% 0.60/0.79          | ((k6_tmap_1 @ X0 @ (u1_struct_0 @ X0))
% 0.60/0.79              = (g1_pre_topc @ (u1_struct_0 @ X0) @ 
% 0.60/0.79                 (k5_tmap_1 @ X0 @ (u1_struct_0 @ X0)))))),
% 0.60/0.79      inference('simplify', [status(thm)], ['119'])).
% 0.60/0.79  thf('121', plain,
% 0.60/0.79      (![X0 : $i]:
% 0.60/0.79         (((k6_tmap_1 @ X0 @ (u1_struct_0 @ X0))
% 0.60/0.79            = (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.60/0.79          | ~ (v2_pre_topc @ X0)
% 0.60/0.79          | ~ (l1_pre_topc @ X0)
% 0.60/0.79          | ~ (l1_struct_0 @ X0)
% 0.60/0.79          | (v2_struct_0 @ X0)
% 0.60/0.79          | ~ (l1_pre_topc @ X0)
% 0.60/0.79          | ~ (v2_pre_topc @ X0)
% 0.60/0.79          | (v2_struct_0 @ X0))),
% 0.60/0.79      inference('sup+', [status(thm)], ['100', '120'])).
% 0.60/0.79  thf('122', plain,
% 0.60/0.79      (![X0 : $i]:
% 0.60/0.79         ((v2_struct_0 @ X0)
% 0.60/0.79          | ~ (l1_struct_0 @ X0)
% 0.60/0.79          | ~ (l1_pre_topc @ X0)
% 0.60/0.79          | ~ (v2_pre_topc @ X0)
% 0.60/0.79          | ((k6_tmap_1 @ X0 @ (u1_struct_0 @ X0))
% 0.60/0.79              = (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 0.60/0.79      inference('simplify', [status(thm)], ['121'])).
% 0.60/0.79  thf('123', plain,
% 0.60/0.79      ((((k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_A)) = (k8_tmap_1 @ sk_A @ sk_B))
% 0.60/0.79        | ~ (v2_pre_topc @ sk_A)
% 0.60/0.79        | ~ (l1_pre_topc @ sk_A)
% 0.60/0.79        | ~ (l1_struct_0 @ sk_A)
% 0.60/0.79        | (v2_struct_0 @ sk_A))),
% 0.60/0.79      inference('sup+', [status(thm)], ['99', '122'])).
% 0.60/0.79  thf('124', plain, ((v2_pre_topc @ sk_A)),
% 0.60/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.79  thf('125', plain, ((l1_pre_topc @ sk_A)),
% 0.60/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.79  thf('126', plain, ((l1_pre_topc @ sk_A)),
% 0.60/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.79  thf(dt_l1_pre_topc, axiom,
% 0.60/0.79    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.60/0.79  thf('127', plain, (![X6 : $i]: ((l1_struct_0 @ X6) | ~ (l1_pre_topc @ X6))),
% 0.60/0.79      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.60/0.79  thf('128', plain, ((l1_struct_0 @ sk_A)),
% 0.60/0.79      inference('sup-', [status(thm)], ['126', '127'])).
% 0.60/0.79  thf('129', plain,
% 0.60/0.79      ((((k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_A)) = (k8_tmap_1 @ sk_A @ sk_B))
% 0.60/0.79        | (v2_struct_0 @ sk_A))),
% 0.60/0.79      inference('demod', [status(thm)], ['123', '124', '125', '128'])).
% 0.60/0.79  thf('130', plain, (~ (v2_struct_0 @ sk_A)),
% 0.60/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.79  thf('131', plain,
% 0.60/0.79      (((k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_A)) = (k8_tmap_1 @ sk_A @ sk_B))),
% 0.60/0.79      inference('clc', [status(thm)], ['129', '130'])).
% 0.60/0.79  thf('132', plain,
% 0.60/0.79      (![X0 : $i]:
% 0.60/0.79         ((v2_struct_0 @ X0)
% 0.60/0.79          | ~ (v2_pre_topc @ X0)
% 0.60/0.79          | ~ (l1_pre_topc @ X0)
% 0.60/0.79          | ((u1_pre_topc @ (k6_tmap_1 @ X0 @ (u1_struct_0 @ X0)))
% 0.60/0.79              = (k5_tmap_1 @ X0 @ (u1_struct_0 @ X0))))),
% 0.60/0.79      inference('sup-', [status(thm)], ['101', '102'])).
% 0.60/0.79  thf('133', plain,
% 0.60/0.79      ((((u1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.60/0.79          = (k5_tmap_1 @ sk_A @ (u1_struct_0 @ sk_A)))
% 0.60/0.79        | ~ (l1_pre_topc @ sk_A)
% 0.60/0.79        | ~ (v2_pre_topc @ sk_A)
% 0.60/0.79        | (v2_struct_0 @ sk_A))),
% 0.60/0.79      inference('sup+', [status(thm)], ['131', '132'])).
% 0.60/0.79  thf('134', plain, ((l1_pre_topc @ sk_A)),
% 0.60/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.79  thf('135', plain, ((v2_pre_topc @ sk_A)),
% 0.60/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.79  thf('136', plain,
% 0.60/0.79      ((((u1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.60/0.79          = (k5_tmap_1 @ sk_A @ (u1_struct_0 @ sk_A)))
% 0.60/0.79        | (v2_struct_0 @ sk_A))),
% 0.60/0.79      inference('demod', [status(thm)], ['133', '134', '135'])).
% 0.60/0.79  thf('137', plain, (~ (v2_struct_0 @ sk_A)),
% 0.60/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.79  thf('138', plain,
% 0.60/0.79      (((u1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.60/0.79         = (k5_tmap_1 @ sk_A @ (u1_struct_0 @ sk_A)))),
% 0.60/0.79      inference('clc', [status(thm)], ['136', '137'])).
% 0.60/0.79  thf('139', plain,
% 0.60/0.79      ((((u1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B)) = (u1_pre_topc @ sk_A))
% 0.60/0.79        | ~ (v2_pre_topc @ sk_A)
% 0.60/0.79        | ~ (l1_pre_topc @ sk_A)
% 0.60/0.79        | ~ (l1_struct_0 @ sk_A)
% 0.60/0.79        | (v2_struct_0 @ sk_A))),
% 0.60/0.79      inference('sup+', [status(thm)], ['15', '138'])).
% 0.60/0.79  thf('140', plain, ((v2_pre_topc @ sk_A)),
% 0.60/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.79  thf('141', plain, ((l1_pre_topc @ sk_A)),
% 0.60/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.79  thf('142', plain, ((l1_struct_0 @ sk_A)),
% 0.60/0.79      inference('sup-', [status(thm)], ['126', '127'])).
% 0.60/0.79  thf('143', plain,
% 0.60/0.79      ((((u1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B)) = (u1_pre_topc @ sk_A))
% 0.60/0.79        | (v2_struct_0 @ sk_A))),
% 0.60/0.79      inference('demod', [status(thm)], ['139', '140', '141', '142'])).
% 0.60/0.79  thf('144', plain,
% 0.60/0.79      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.60/0.79        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.60/0.79      inference('demod', [status(thm)], ['25', '26'])).
% 0.60/0.79  thf('145', plain,
% 0.60/0.79      (![X15 : $i, X16 : $i]:
% 0.60/0.79         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.60/0.79          | ((u1_pre_topc @ X16) != (k5_tmap_1 @ X16 @ X15))
% 0.60/0.79          | (r2_hidden @ X15 @ (u1_pre_topc @ X16))
% 0.60/0.79          | ~ (l1_pre_topc @ X16)
% 0.60/0.79          | ~ (v2_pre_topc @ X16)
% 0.60/0.79          | (v2_struct_0 @ X16))),
% 0.60/0.79      inference('cnf', [status(esa)], [t103_tmap_1])).
% 0.60/0.79  thf('146', plain,
% 0.60/0.79      (((v2_struct_0 @ sk_A)
% 0.60/0.79        | ~ (v2_pre_topc @ sk_A)
% 0.60/0.79        | ~ (l1_pre_topc @ sk_A)
% 0.60/0.79        | (r2_hidden @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_A))
% 0.60/0.79        | ((u1_pre_topc @ sk_A) != (k5_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B))))),
% 0.60/0.79      inference('sup-', [status(thm)], ['144', '145'])).
% 0.60/0.79  thf('147', plain, ((v2_pre_topc @ sk_A)),
% 0.60/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.79  thf('148', plain, ((l1_pre_topc @ sk_A)),
% 0.60/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.79  thf('149', plain,
% 0.60/0.79      (((v2_struct_0 @ sk_A)
% 0.60/0.79        | (r2_hidden @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_A))
% 0.60/0.79        | ((u1_pre_topc @ sk_A) != (k5_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B))))),
% 0.60/0.79      inference('demod', [status(thm)], ['146', '147', '148'])).
% 0.60/0.79  thf('150', plain, (~ (v2_struct_0 @ sk_A)),
% 0.60/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.79  thf('151', plain,
% 0.60/0.79      ((((u1_pre_topc @ sk_A) != (k5_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 0.60/0.79        | (r2_hidden @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_A)))),
% 0.60/0.79      inference('clc', [status(thm)], ['149', '150'])).
% 0.60/0.79  thf('152', plain,
% 0.60/0.79      (((u1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.60/0.79         = (k5_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))),
% 0.60/0.79      inference('clc', [status(thm)], ['36', '37'])).
% 0.60/0.79  thf('153', plain,
% 0.60/0.79      ((((u1_pre_topc @ sk_A) != (u1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B)))
% 0.60/0.79        | (r2_hidden @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_A)))),
% 0.60/0.79      inference('demod', [status(thm)], ['151', '152'])).
% 0.60/0.79  thf('154', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.60/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.79  thf('155', plain,
% 0.60/0.79      (![X8 : $i, X9 : $i]:
% 0.60/0.79         (~ (m1_pre_topc @ X8 @ X9)
% 0.60/0.79          | ((sk_C @ X8 @ X9) = (u1_struct_0 @ X8))
% 0.60/0.79          | (v1_tsep_1 @ X8 @ X9)
% 0.60/0.79          | ~ (l1_pre_topc @ X9))),
% 0.60/0.79      inference('cnf', [status(esa)], [d1_tsep_1])).
% 0.60/0.79  thf('156', plain,
% 0.60/0.79      ((~ (l1_pre_topc @ sk_A)
% 0.60/0.79        | (v1_tsep_1 @ sk_B @ sk_A)
% 0.60/0.79        | ((sk_C @ sk_B @ sk_A) = (u1_struct_0 @ sk_B)))),
% 0.60/0.79      inference('sup-', [status(thm)], ['154', '155'])).
% 0.60/0.79  thf('157', plain, ((l1_pre_topc @ sk_A)),
% 0.60/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.79  thf('158', plain,
% 0.60/0.79      (((v1_tsep_1 @ sk_B @ sk_A)
% 0.60/0.79        | ((sk_C @ sk_B @ sk_A) = (u1_struct_0 @ sk_B)))),
% 0.60/0.79      inference('demod', [status(thm)], ['156', '157'])).
% 0.60/0.79  thf('159', plain,
% 0.60/0.79      ((~ (v1_tsep_1 @ sk_B @ sk_A)) <= (~ ((v1_tsep_1 @ sk_B @ sk_A)))),
% 0.60/0.79      inference('split', [status(esa)], ['18'])).
% 0.60/0.79  thf('160', plain,
% 0.60/0.79      ((((sk_C @ sk_B @ sk_A) = (u1_struct_0 @ sk_B)))
% 0.60/0.79         <= (~ ((v1_tsep_1 @ sk_B @ sk_A)))),
% 0.60/0.79      inference('sup-', [status(thm)], ['158', '159'])).
% 0.60/0.79  thf('161', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.60/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.79  thf('162', plain,
% 0.60/0.79      (![X8 : $i, X9 : $i]:
% 0.60/0.79         (~ (m1_pre_topc @ X8 @ X9)
% 0.60/0.79          | (m1_subset_1 @ (sk_C @ X8 @ X9) @ 
% 0.60/0.79             (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.60/0.79          | (v1_tsep_1 @ X8 @ X9)
% 0.60/0.79          | ~ (l1_pre_topc @ X9))),
% 0.60/0.79      inference('cnf', [status(esa)], [d1_tsep_1])).
% 0.60/0.79  thf('163', plain,
% 0.60/0.79      ((~ (l1_pre_topc @ sk_A)
% 0.60/0.79        | (v1_tsep_1 @ sk_B @ sk_A)
% 0.60/0.79        | (m1_subset_1 @ (sk_C @ sk_B @ sk_A) @ 
% 0.60/0.79           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.60/0.79      inference('sup-', [status(thm)], ['161', '162'])).
% 0.60/0.79  thf('164', plain, ((l1_pre_topc @ sk_A)),
% 0.60/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.79  thf('165', plain,
% 0.60/0.79      (((v1_tsep_1 @ sk_B @ sk_A)
% 0.60/0.79        | (m1_subset_1 @ (sk_C @ sk_B @ sk_A) @ 
% 0.60/0.79           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.60/0.79      inference('demod', [status(thm)], ['163', '164'])).
% 0.60/0.79  thf('166', plain,
% 0.60/0.79      (![X4 : $i, X5 : $i]:
% 0.60/0.79         (~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (u1_struct_0 @ X5)))
% 0.60/0.79          | ~ (r2_hidden @ X4 @ (u1_pre_topc @ X5))
% 0.60/0.79          | (v3_pre_topc @ X4 @ X5)
% 0.60/0.79          | ~ (l1_pre_topc @ X5))),
% 0.60/0.79      inference('cnf', [status(esa)], [d5_pre_topc])).
% 0.60/0.79  thf('167', plain,
% 0.60/0.79      (((v1_tsep_1 @ sk_B @ sk_A)
% 0.60/0.79        | ~ (l1_pre_topc @ sk_A)
% 0.60/0.79        | (v3_pre_topc @ (sk_C @ sk_B @ sk_A) @ sk_A)
% 0.60/0.79        | ~ (r2_hidden @ (sk_C @ sk_B @ sk_A) @ (u1_pre_topc @ sk_A)))),
% 0.60/0.79      inference('sup-', [status(thm)], ['165', '166'])).
% 0.60/0.79  thf('168', plain, ((l1_pre_topc @ sk_A)),
% 0.60/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.79  thf('169', plain,
% 0.60/0.79      (((v1_tsep_1 @ sk_B @ sk_A)
% 0.60/0.79        | (v3_pre_topc @ (sk_C @ sk_B @ sk_A) @ sk_A)
% 0.60/0.79        | ~ (r2_hidden @ (sk_C @ sk_B @ sk_A) @ (u1_pre_topc @ sk_A)))),
% 0.60/0.79      inference('demod', [status(thm)], ['167', '168'])).
% 0.60/0.79  thf('170', plain,
% 0.60/0.79      (((~ (r2_hidden @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_A))
% 0.60/0.79         | (v3_pre_topc @ (sk_C @ sk_B @ sk_A) @ sk_A)
% 0.60/0.79         | (v1_tsep_1 @ sk_B @ sk_A))) <= (~ ((v1_tsep_1 @ sk_B @ sk_A)))),
% 0.60/0.79      inference('sup-', [status(thm)], ['160', '169'])).
% 0.60/0.79  thf('171', plain,
% 0.60/0.79      ((((sk_C @ sk_B @ sk_A) = (u1_struct_0 @ sk_B)))
% 0.60/0.79         <= (~ ((v1_tsep_1 @ sk_B @ sk_A)))),
% 0.60/0.79      inference('sup-', [status(thm)], ['158', '159'])).
% 0.60/0.79  thf('172', plain,
% 0.60/0.79      (((~ (r2_hidden @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_A))
% 0.60/0.79         | (v3_pre_topc @ (u1_struct_0 @ sk_B) @ sk_A)
% 0.60/0.79         | (v1_tsep_1 @ sk_B @ sk_A))) <= (~ ((v1_tsep_1 @ sk_B @ sk_A)))),
% 0.60/0.79      inference('demod', [status(thm)], ['170', '171'])).
% 0.60/0.79  thf('173', plain,
% 0.60/0.79      ((((sk_C @ sk_B @ sk_A) = (u1_struct_0 @ sk_B)))
% 0.60/0.79         <= (~ ((v1_tsep_1 @ sk_B @ sk_A)))),
% 0.60/0.79      inference('sup-', [status(thm)], ['158', '159'])).
% 0.60/0.79  thf('174', plain,
% 0.60/0.79      (![X8 : $i, X9 : $i]:
% 0.60/0.79         (~ (m1_pre_topc @ X8 @ X9)
% 0.60/0.79          | ~ (v3_pre_topc @ (sk_C @ X8 @ X9) @ X9)
% 0.60/0.79          | (v1_tsep_1 @ X8 @ X9)
% 0.60/0.79          | ~ (l1_pre_topc @ X9))),
% 0.60/0.79      inference('cnf', [status(esa)], [d1_tsep_1])).
% 0.60/0.79  thf('175', plain,
% 0.60/0.79      (((~ (v3_pre_topc @ (u1_struct_0 @ sk_B) @ sk_A)
% 0.60/0.79         | ~ (l1_pre_topc @ sk_A)
% 0.60/0.79         | (v1_tsep_1 @ sk_B @ sk_A)
% 0.60/0.79         | ~ (m1_pre_topc @ sk_B @ sk_A))) <= (~ ((v1_tsep_1 @ sk_B @ sk_A)))),
% 0.60/0.79      inference('sup-', [status(thm)], ['173', '174'])).
% 0.60/0.79  thf('176', plain, ((l1_pre_topc @ sk_A)),
% 0.60/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.79  thf('177', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.60/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.79  thf('178', plain,
% 0.60/0.79      (((~ (v3_pre_topc @ (u1_struct_0 @ sk_B) @ sk_A)
% 0.60/0.79         | (v1_tsep_1 @ sk_B @ sk_A))) <= (~ ((v1_tsep_1 @ sk_B @ sk_A)))),
% 0.60/0.79      inference('demod', [status(thm)], ['175', '176', '177'])).
% 0.60/0.79  thf('179', plain,
% 0.60/0.79      ((~ (v1_tsep_1 @ sk_B @ sk_A)) <= (~ ((v1_tsep_1 @ sk_B @ sk_A)))),
% 0.60/0.79      inference('split', [status(esa)], ['18'])).
% 0.60/0.79  thf('180', plain,
% 0.60/0.79      ((~ (v3_pre_topc @ (u1_struct_0 @ sk_B) @ sk_A))
% 0.60/0.79         <= (~ ((v1_tsep_1 @ sk_B @ sk_A)))),
% 0.60/0.79      inference('clc', [status(thm)], ['178', '179'])).
% 0.60/0.79  thf('181', plain,
% 0.60/0.79      ((((v1_tsep_1 @ sk_B @ sk_A)
% 0.60/0.79         | ~ (r2_hidden @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_A))))
% 0.60/0.79         <= (~ ((v1_tsep_1 @ sk_B @ sk_A)))),
% 0.60/0.79      inference('clc', [status(thm)], ['172', '180'])).
% 0.60/0.79  thf('182', plain,
% 0.60/0.79      ((~ (v1_tsep_1 @ sk_B @ sk_A)) <= (~ ((v1_tsep_1 @ sk_B @ sk_A)))),
% 0.60/0.79      inference('split', [status(esa)], ['18'])).
% 0.60/0.79  thf('183', plain,
% 0.60/0.79      ((~ (r2_hidden @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_A)))
% 0.60/0.79         <= (~ ((v1_tsep_1 @ sk_B @ sk_A)))),
% 0.60/0.79      inference('clc', [status(thm)], ['181', '182'])).
% 0.60/0.79  thf('184', plain, (~ ((v1_tsep_1 @ sk_B @ sk_A))),
% 0.60/0.79      inference('sat_resolution*', [status(thm)], ['19', '22', '96'])).
% 0.60/0.79  thf('185', plain,
% 0.60/0.79      (~ (r2_hidden @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_A))),
% 0.60/0.79      inference('simpl_trail', [status(thm)], ['183', '184'])).
% 0.60/0.79  thf('186', plain,
% 0.60/0.79      (((u1_pre_topc @ sk_A) != (u1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B)))),
% 0.60/0.79      inference('clc', [status(thm)], ['153', '185'])).
% 0.60/0.79  thf('187', plain, ((v2_struct_0 @ sk_A)),
% 0.60/0.79      inference('simplify_reflect-', [status(thm)], ['143', '186'])).
% 0.60/0.79  thf('188', plain, ($false), inference('demod', [status(thm)], ['0', '187'])).
% 0.60/0.79  
% 0.60/0.79  % SZS output end Refutation
% 0.60/0.79  
% 0.60/0.80  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
