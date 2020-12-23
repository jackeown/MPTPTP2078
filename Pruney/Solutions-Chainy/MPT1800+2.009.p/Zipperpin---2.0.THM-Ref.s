%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.uphSH13g1D

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:10:56 EST 2020

% Result     : Theorem 0.43s
% Output     : Refutation 0.44s
% Verified   : 
% Statistics : Number of formulae       :  264 (1097 expanded)
%              Number of leaves         :   34 ( 315 expanded)
%              Depth                    :   34
%              Number of atoms          : 2253 (16606 expanded)
%              Number of equality atoms :   94 ( 651 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(g1_pre_topc_type,type,(
    g1_pre_topc: $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v1_tsep_1_type,type,(
    v1_tsep_1: $i > $i > $o )).

thf(k5_tmap_1_type,type,(
    k5_tmap_1: $i > $i > $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k8_tmap_1_type,type,(
    k8_tmap_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(t2_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( m1_pre_topc @ A @ A ) ) )).

thf('0',plain,(
    ! [X20: $i] :
      ( ( m1_pre_topc @ X20 @ X20 )
      | ~ ( l1_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

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

thf('1',plain,(
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

thf('2',plain,(
    ! [X15: $i,X16: $i] :
      ( ( v2_struct_0 @ X15 )
      | ~ ( m1_pre_topc @ X15 @ X16 )
      | ( ( u1_struct_0 @ ( k8_tmap_1 @ X16 @ X15 ) )
        = ( u1_struct_0 @ X16 ) )
      | ~ ( l1_pre_topc @ X16 )
      | ~ ( v2_pre_topc @ X16 )
      | ( v2_struct_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t114_tmap_1])).

thf('3',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
      = ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
      = ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['3','4','5'])).

thf('7',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['6','7'])).

thf('9',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X20: $i] :
      ( ( m1_pre_topc @ X20 @ X20 )
      | ~ ( l1_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf(t1_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( m1_subset_1 @ ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('12',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( m1_pre_topc @ X18 @ X19 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X18 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( l1_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,
    ( ( m1_subset_1 @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['10','14'])).

thf('16',plain,
    ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['8','9'])).

thf('17',plain,(
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

thf('18',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( l1_pre_topc @ X11 )
      | ~ ( v2_pre_topc @ X11 )
      | ( v2_struct_0 @ X11 )
      | ~ ( m1_pre_topc @ X12 @ X11 )
      | ( l1_pre_topc @ ( k8_tmap_1 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k8_tmap_1])).

thf('19',plain,
    ( ( l1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,
    ( ( l1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['19','20','21'])).

thf('23',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    l1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['22','23'])).

thf('25',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['15','16','24'])).

thf('26',plain,(
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

thf('27',plain,(
    ! [X15: $i,X16: $i] :
      ( ( v2_struct_0 @ X16 )
      | ~ ( v2_pre_topc @ X16 )
      | ~ ( l1_pre_topc @ X16 )
      | ( ( u1_pre_topc @ ( k8_tmap_1 @ X16 @ X15 ) )
        = ( k5_tmap_1 @ X16 @ ( u1_struct_0 @ X15 ) ) )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X15 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( m1_pre_topc @ X15 @ X16 )
      | ( v2_struct_0 @ X15 ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( m1_pre_topc @ sk_A @ sk_A )
    | ( ( u1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_A ) )
      = ( k5_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['25','27'])).

thf('29',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( m1_pre_topc @ sk_A @ sk_A )
    | ( ( u1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_A ) )
      = ( k5_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_A ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['28','29','30'])).

thf('32',plain,
    ( ( ( u1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_A ) )
      = ( k5_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( m1_pre_topc @ sk_A @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['31'])).

thf(t43_tops_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( ( k1_tops_1 @ A @ ( k2_struct_0 @ A ) )
        = ( k2_struct_0 @ A ) ) ) )).

thf('33',plain,(
    ! [X7: $i] :
      ( ( ( k1_tops_1 @ X7 @ ( k2_struct_0 @ X7 ) )
        = ( k2_struct_0 @ X7 ) )
      | ~ ( l1_pre_topc @ X7 )
      | ~ ( v2_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[t43_tops_1])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('34',plain,(
    ! [X1: $i] :
      ( ( ( k2_struct_0 @ X1 )
        = ( u1_struct_0 @ X1 ) )
      | ~ ( l1_struct_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('37',plain,(
    ! [X4: $i] :
      ( ( l1_struct_0 @ X4 )
      | ~ ( l1_pre_topc @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('38',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( m1_subset_1 @ ( k2_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference(clc,[status(thm)],['36','37'])).

thf(fc9_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ) )).

thf('39',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( l1_pre_topc @ X5 )
      | ~ ( v2_pre_topc @ X5 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) )
      | ( v3_pre_topc @ ( k1_tops_1 @ X5 @ X6 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[fc9_tops_1])).

thf('40',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v3_pre_topc @ ( k1_tops_1 @ X0 @ ( k2_struct_0 @ X0 ) ) @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ( v3_pre_topc @ ( k1_tops_1 @ X0 @ ( k2_struct_0 @ X0 ) ) @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( v3_pre_topc @ ( k2_struct_0 @ X0 ) @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference('sup+',[status(thm)],['33','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v3_pre_topc @ ( k2_struct_0 @ X0 ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,(
    ! [X1: $i] :
      ( ( ( k2_struct_0 @ X1 )
        = ( u1_struct_0 @ X1 ) )
      | ~ ( l1_struct_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf(d5_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v3_pre_topc @ B @ A )
          <=> ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) ) ) ) )).

thf('46',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X3 ) ) )
      | ~ ( v3_pre_topc @ X2 @ X3 )
      | ( r2_hidden @ X2 @ ( u1_pre_topc @ X3 ) )
      | ~ ( l1_pre_topc @ X3 ) ) ),
    inference(cnf,[status(esa)],[d5_pre_topc])).

thf('47',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( r2_hidden @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ~ ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 )
      | ( r2_hidden @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ~ ( v3_pre_topc @ ( k2_struct_0 @ X0 ) @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( r2_hidden @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['44','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( r2_hidden @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['43','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( r2_hidden @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['50'])).

thf('52',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['15','16','24'])).

thf('53',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X3 ) ) )
      | ~ ( r2_hidden @ X2 @ ( u1_pre_topc @ X3 ) )
      | ( v3_pre_topc @ X2 @ X3 )
      | ~ ( l1_pre_topc @ X3 ) ) ),
    inference(cnf,[status(esa)],[d5_pre_topc])).

thf('54',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v3_pre_topc @ ( u1_struct_0 @ sk_A ) @ sk_A )
    | ~ ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,
    ( ( v3_pre_topc @ ( u1_struct_0 @ sk_A ) @ sk_A )
    | ~ ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( l1_struct_0 @ sk_A )
    | ( v3_pre_topc @ ( u1_struct_0 @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['51','56'])).

thf('58',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    ! [X4: $i] :
      ( ( l1_struct_0 @ X4 )
      | ~ ( l1_pre_topc @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('62',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    v3_pre_topc @ ( u1_struct_0 @ sk_A ) @ sk_A ),
    inference(demod,[status(thm)],['57','58','59','62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ~ ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 )
      | ( r2_hidden @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['47'])).

thf('65',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    r2_hidden @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ),
    inference(demod,[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['13'])).

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

thf('69',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( r2_hidden @ X13 @ ( u1_pre_topc @ X14 ) )
      | ( ( u1_pre_topc @ X14 )
        = ( k5_tmap_1 @ X14 @ X13 ) )
      | ~ ( l1_pre_topc @ X14 )
      | ~ ( v2_pre_topc @ X14 )
      | ( v2_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t103_tmap_1])).

thf('70',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( u1_pre_topc @ X0 )
        = ( k5_tmap_1 @ X0 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( r2_hidden @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) )
      | ( ( u1_pre_topc @ X0 )
        = ( k5_tmap_1 @ X0 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['70'])).

thf('72',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ( ( u1_pre_topc @ sk_A )
      = ( k5_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['67','71'])).

thf('73',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( u1_pre_topc @ sk_A )
      = ( k5_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['72','73','74'])).

thf('76',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,
    ( ( u1_pre_topc @ sk_A )
    = ( k5_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['75','76'])).

thf('78',plain,
    ( ( ( u1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_A ) )
      = ( u1_pre_topc @ sk_A ) )
    | ~ ( m1_pre_topc @ sk_A @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['32','77'])).

thf('79',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,
    ( ~ ( m1_pre_topc @ sk_A @ sk_A )
    | ( ( u1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_A ) )
      = ( u1_pre_topc @ sk_A ) ) ),
    inference(clc,[status(thm)],['78','79'])).

thf('81',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( u1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_A ) )
      = ( u1_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['0','80'])).

thf('82',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,
    ( ( u1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_A ) )
    = ( u1_pre_topc @ sk_A ) ),
    inference(demod,[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X20: $i] :
      ( ( m1_pre_topc @ X20 @ X20 )
      | ~ ( l1_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('85',plain,(
    ! [X15: $i,X16: $i] :
      ( ( v2_struct_0 @ X15 )
      | ~ ( m1_pre_topc @ X15 @ X16 )
      | ( ( u1_struct_0 @ ( k8_tmap_1 @ X16 @ X15 ) )
        = ( u1_struct_0 @ X16 ) )
      | ~ ( l1_pre_topc @ X16 )
      | ~ ( v2_pre_topc @ X16 )
      | ( v2_struct_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t114_tmap_1])).

thf('86',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( u1_struct_0 @ ( k8_tmap_1 @ X0 @ X0 ) )
        = ( u1_struct_0 @ X0 ) )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X0: $i] :
      ( ( ( u1_struct_0 @ ( k8_tmap_1 @ X0 @ X0 ) )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['86'])).

thf('88',plain,(
    ! [X20: $i] :
      ( ( m1_pre_topc @ X20 @ X20 )
      | ~ ( l1_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('89',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( l1_pre_topc @ X11 )
      | ~ ( v2_pre_topc @ X11 )
      | ( v2_struct_0 @ X11 )
      | ~ ( m1_pre_topc @ X12 @ X11 )
      | ( v1_pre_topc @ ( k8_tmap_1 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k8_tmap_1])).

thf('90',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v1_pre_topc @ ( k8_tmap_1 @ X0 @ X0 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( v1_pre_topc @ ( k8_tmap_1 @ X0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['90'])).

thf('92',plain,(
    ! [X20: $i] :
      ( ( m1_pre_topc @ X20 @ X20 )
      | ~ ( l1_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('93',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( l1_pre_topc @ X11 )
      | ~ ( v2_pre_topc @ X11 )
      | ( v2_struct_0 @ X11 )
      | ~ ( m1_pre_topc @ X12 @ X11 )
      | ( l1_pre_topc @ ( k8_tmap_1 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k8_tmap_1])).

thf('94',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( l1_pre_topc @ ( k8_tmap_1 @ X0 @ X0 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( l1_pre_topc @ ( k8_tmap_1 @ X0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['94'])).

thf('96',plain,
    ( ( u1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_A ) )
    = ( u1_pre_topc @ sk_A ) ),
    inference(demod,[status(thm)],['81','82'])).

thf(abstractness_v1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( ( v1_pre_topc @ A )
       => ( A
          = ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ) )).

thf('97',plain,(
    ! [X0: $i] :
      ( ~ ( v1_pre_topc @ X0 )
      | ( X0
        = ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(cnf,[status(esa)],[abstractness_v1_pre_topc])).

thf('98',plain,
    ( ( ( k8_tmap_1 @ sk_A @ sk_A )
      = ( g1_pre_topc @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_A ) ) @ ( u1_pre_topc @ sk_A ) ) )
    | ~ ( l1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_A ) )
    | ~ ( v1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_A ) ) ),
    inference('sup+',[status(thm)],['96','97'])).

thf('99',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( v1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_A ) )
    | ( ( k8_tmap_1 @ sk_A @ sk_A )
      = ( g1_pre_topc @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_A ) ) @ ( u1_pre_topc @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['95','98'])).

thf('100',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_A ) )
    | ( ( k8_tmap_1 @ sk_A @ sk_A )
      = ( g1_pre_topc @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_A ) ) @ ( u1_pre_topc @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['99','100','101'])).

thf('103',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,
    ( ( ( k8_tmap_1 @ sk_A @ sk_A )
      = ( g1_pre_topc @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_A ) ) @ ( u1_pre_topc @ sk_A ) ) )
    | ~ ( v1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_A ) ) ),
    inference(clc,[status(thm)],['102','103'])).

thf('105',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ( ( k8_tmap_1 @ sk_A @ sk_A )
      = ( g1_pre_topc @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_A ) ) @ ( u1_pre_topc @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['91','104'])).

thf('106',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k8_tmap_1 @ sk_A @ sk_A )
      = ( g1_pre_topc @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_A ) ) @ ( u1_pre_topc @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['105','106','107'])).

thf('109',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,
    ( ( k8_tmap_1 @ sk_A @ sk_A )
    = ( g1_pre_topc @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_A ) ) @ ( u1_pre_topc @ sk_A ) ) ),
    inference(clc,[status(thm)],['108','109'])).

thf('111',plain,
    ( ( ( k8_tmap_1 @ sk_A @ sk_A )
      = ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A ) ),
    inference('sup+',[status(thm)],['87','110'])).

thf('112',plain,
    ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,
    ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k8_tmap_1 @ sk_A @ sk_B ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['112'])).

thf('114',plain,
    ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
     != ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( m1_pre_topc @ sk_B @ sk_A )
    | ~ ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,
    ( ~ ( v1_tsep_1 @ sk_B @ sk_A )
    | ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
     != ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['114'])).

thf('116',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,
    ( ~ ( m1_pre_topc @ sk_B @ sk_A )
   <= ~ ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['114'])).

thf('118',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['116','117'])).

thf('119',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( m1_pre_topc @ X18 @ X19 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X18 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( l1_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('121',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['119','120'])).

thf('122',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['121','122'])).

thf('124',plain,(
    ! [X15: $i,X16: $i] :
      ( ( v2_struct_0 @ X16 )
      | ~ ( v2_pre_topc @ X16 )
      | ~ ( l1_pre_topc @ X16 )
      | ( ( u1_pre_topc @ ( k8_tmap_1 @ X16 @ X15 ) )
        = ( k5_tmap_1 @ X16 @ ( u1_struct_0 @ X15 ) ) )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X15 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( m1_pre_topc @ X15 @ X16 )
      | ( v2_struct_0 @ X15 ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('125',plain,
    ( ( v2_struct_0 @ sk_B )
    | ~ ( m1_pre_topc @ sk_B @ sk_A )
    | ( ( u1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
      = ( k5_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['123','124'])).

thf('126',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('128',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('129',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( u1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
      = ( k5_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['125','126','127','128'])).

thf('130',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('131',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( u1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
      = ( k5_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['129','130'])).

thf('132',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('133',plain,
    ( ( u1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    = ( k5_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['131','132'])).

thf('134',plain,
    ( ( v1_tsep_1 @ sk_B @ sk_A )
   <= ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['112'])).

thf('135',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['121','122'])).

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

thf('136',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( m1_pre_topc @ X8 @ X9 )
      | ~ ( v1_tsep_1 @ X8 @ X9 )
      | ( X10
       != ( u1_struct_0 @ X8 ) )
      | ( v3_pre_topc @ X10 @ X9 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[d1_tsep_1])).

thf('137',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( l1_pre_topc @ X9 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X8 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ( v3_pre_topc @ ( u1_struct_0 @ X8 ) @ X9 )
      | ~ ( v1_tsep_1 @ X8 @ X9 )
      | ~ ( m1_pre_topc @ X8 @ X9 ) ) ),
    inference(simplify,[status(thm)],['136'])).

thf('138',plain,
    ( ~ ( m1_pre_topc @ sk_B @ sk_A )
    | ~ ( v1_tsep_1 @ sk_B @ sk_A )
    | ( v3_pre_topc @ ( u1_struct_0 @ sk_B ) @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['135','137'])).

thf('139',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('140',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('141',plain,
    ( ~ ( v1_tsep_1 @ sk_B @ sk_A )
    | ( v3_pre_topc @ ( u1_struct_0 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['138','139','140'])).

thf('142',plain,
    ( ( v3_pre_topc @ ( u1_struct_0 @ sk_B ) @ sk_A )
   <= ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['134','141'])).

thf('143',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['121','122'])).

thf('144',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X3 ) ) )
      | ~ ( v3_pre_topc @ X2 @ X3 )
      | ( r2_hidden @ X2 @ ( u1_pre_topc @ X3 ) )
      | ~ ( l1_pre_topc @ X3 ) ) ),
    inference(cnf,[status(esa)],[d5_pre_topc])).

thf('145',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r2_hidden @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_A ) )
    | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['143','144'])).

thf('146',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('147',plain,
    ( ( r2_hidden @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_A ) )
    | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['145','146'])).

thf('148',plain,
    ( ( r2_hidden @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_A ) )
   <= ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['142','147'])).

thf('149',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['121','122'])).

thf('150',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( r2_hidden @ X13 @ ( u1_pre_topc @ X14 ) )
      | ( ( u1_pre_topc @ X14 )
        = ( k5_tmap_1 @ X14 @ X13 ) )
      | ~ ( l1_pre_topc @ X14 )
      | ~ ( v2_pre_topc @ X14 )
      | ( v2_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t103_tmap_1])).

thf('151',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( ( u1_pre_topc @ sk_A )
      = ( k5_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
    | ~ ( r2_hidden @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['149','150'])).

thf('152',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('153',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('154',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( u1_pre_topc @ sk_A )
      = ( k5_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
    | ~ ( r2_hidden @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_A ) ) ),
    inference(demod,[status(thm)],['151','152','153'])).

thf('155',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('156',plain,
    ( ~ ( r2_hidden @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_A ) )
    | ( ( u1_pre_topc @ sk_A )
      = ( k5_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['154','155'])).

thf('157',plain,
    ( ( ( u1_pre_topc @ sk_A )
      = ( k5_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
   <= ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['148','156'])).

thf('158',plain,
    ( ( ( u1_pre_topc @ sk_A )
      = ( u1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) ) )
   <= ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['133','157'])).

thf('159',plain,
    ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['8','9'])).

thf('160',plain,(
    ! [X0: $i] :
      ( ~ ( v1_pre_topc @ X0 )
      | ( X0
        = ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(cnf,[status(esa)],[abstractness_v1_pre_topc])).

thf('161',plain,
    ( ( ( k8_tmap_1 @ sk_A @ sk_B )
      = ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) )
    | ~ ( l1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( v1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['159','160'])).

thf('162',plain,(
    l1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['22','23'])).

thf('163',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('164',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( l1_pre_topc @ X11 )
      | ~ ( v2_pre_topc @ X11 )
      | ( v2_struct_0 @ X11 )
      | ~ ( m1_pre_topc @ X12 @ X11 )
      | ( v1_pre_topc @ ( k8_tmap_1 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k8_tmap_1])).

thf('165',plain,
    ( ( v1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['163','164'])).

thf('166',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('167',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('168',plain,
    ( ( v1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['165','166','167'])).

thf('169',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('170',plain,(
    v1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['168','169'])).

thf('171',plain,
    ( ( k8_tmap_1 @ sk_A @ sk_B )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['161','162','170'])).

thf('172',plain,
    ( ( ( k8_tmap_1 @ sk_A @ sk_B )
      = ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
   <= ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['158','171'])).

thf('173',plain,
    ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
     != ( k8_tmap_1 @ sk_A @ sk_B ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
     != ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['114'])).

thf('174',plain,
    ( ( ( k8_tmap_1 @ sk_A @ sk_B )
     != ( k8_tmap_1 @ sk_A @ sk_B ) )
   <= ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
       != ( k8_tmap_1 @ sk_A @ sk_B ) )
      & ( v1_tsep_1 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['172','173'])).

thf('175',plain,
    ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['174'])).

thf('176',plain,
    ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['112'])).

thf('177',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
    = ( k8_tmap_1 @ sk_A @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['115','118','175','176'])).

thf('178',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
    = ( k8_tmap_1 @ sk_A @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['113','177'])).

thf('179',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('180',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('181',plain,
    ( ( ( k8_tmap_1 @ sk_A @ sk_A )
      = ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['111','178','179','180'])).

thf('182',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('183',plain,
    ( ( k8_tmap_1 @ sk_A @ sk_A )
    = ( k8_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['181','182'])).

thf('184',plain,
    ( ( u1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_pre_topc @ sk_A ) ),
    inference(demod,[status(thm)],['83','183'])).

thf('185',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['121','122'])).

thf('186',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ( ( u1_pre_topc @ X14 )
       != ( k5_tmap_1 @ X14 @ X13 ) )
      | ( r2_hidden @ X13 @ ( u1_pre_topc @ X14 ) )
      | ~ ( l1_pre_topc @ X14 )
      | ~ ( v2_pre_topc @ X14 )
      | ( v2_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t103_tmap_1])).

thf('187',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( r2_hidden @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_A ) )
    | ( ( u1_pre_topc @ sk_A )
     != ( k5_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['185','186'])).

thf('188',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('189',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('190',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_A ) )
    | ( ( u1_pre_topc @ sk_A )
     != ( k5_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['187','188','189'])).

thf('191',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('192',plain,
    ( ( ( u1_pre_topc @ sk_A )
     != ( k5_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
    | ( r2_hidden @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_A ) ) ),
    inference(clc,[status(thm)],['190','191'])).

thf('193',plain,
    ( ( u1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    = ( k5_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['131','132'])).

thf('194',plain,
    ( ( ( u1_pre_topc @ sk_A )
     != ( u1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) ) )
    | ( r2_hidden @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_A ) ) ),
    inference(demod,[status(thm)],['192','193'])).

thf('195',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('196',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( m1_pre_topc @ X8 @ X9 )
      | ( ( sk_C @ X8 @ X9 )
        = ( u1_struct_0 @ X8 ) )
      | ( v1_tsep_1 @ X8 @ X9 )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[d1_tsep_1])).

thf('197',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v1_tsep_1 @ sk_B @ sk_A )
    | ( ( sk_C @ sk_B @ sk_A )
      = ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['195','196'])).

thf('198',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('199',plain,
    ( ( v1_tsep_1 @ sk_B @ sk_A )
    | ( ( sk_C @ sk_B @ sk_A )
      = ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['197','198'])).

thf('200',plain,
    ( ~ ( v1_tsep_1 @ sk_B @ sk_A )
   <= ~ ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['114'])).

thf('201',plain,
    ( ( ( sk_C @ sk_B @ sk_A )
      = ( u1_struct_0 @ sk_B ) )
   <= ~ ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['199','200'])).

thf('202',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('203',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( m1_pre_topc @ X8 @ X9 )
      | ( m1_subset_1 @ ( sk_C @ X8 @ X9 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ( v1_tsep_1 @ X8 @ X9 )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[d1_tsep_1])).

thf('204',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v1_tsep_1 @ sk_B @ sk_A )
    | ( m1_subset_1 @ ( sk_C @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['202','203'])).

thf('205',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('206',plain,
    ( ( v1_tsep_1 @ sk_B @ sk_A )
    | ( m1_subset_1 @ ( sk_C @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['204','205'])).

thf('207',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X3 ) ) )
      | ~ ( r2_hidden @ X2 @ ( u1_pre_topc @ X3 ) )
      | ( v3_pre_topc @ X2 @ X3 )
      | ~ ( l1_pre_topc @ X3 ) ) ),
    inference(cnf,[status(esa)],[d5_pre_topc])).

thf('208',plain,
    ( ( v1_tsep_1 @ sk_B @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v3_pre_topc @ ( sk_C @ sk_B @ sk_A ) @ sk_A )
    | ~ ( r2_hidden @ ( sk_C @ sk_B @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['206','207'])).

thf('209',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('210',plain,
    ( ( v1_tsep_1 @ sk_B @ sk_A )
    | ( v3_pre_topc @ ( sk_C @ sk_B @ sk_A ) @ sk_A )
    | ~ ( r2_hidden @ ( sk_C @ sk_B @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ),
    inference(demod,[status(thm)],['208','209'])).

thf('211',plain,
    ( ( ~ ( r2_hidden @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_A ) )
      | ( v3_pre_topc @ ( sk_C @ sk_B @ sk_A ) @ sk_A )
      | ( v1_tsep_1 @ sk_B @ sk_A ) )
   <= ~ ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['201','210'])).

thf('212',plain,
    ( ( ( sk_C @ sk_B @ sk_A )
      = ( u1_struct_0 @ sk_B ) )
   <= ~ ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['199','200'])).

thf('213',plain,
    ( ( ~ ( r2_hidden @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_A ) )
      | ( v3_pre_topc @ ( u1_struct_0 @ sk_B ) @ sk_A )
      | ( v1_tsep_1 @ sk_B @ sk_A ) )
   <= ~ ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['211','212'])).

thf('214',plain,
    ( ( ( sk_C @ sk_B @ sk_A )
      = ( u1_struct_0 @ sk_B ) )
   <= ~ ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['199','200'])).

thf('215',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( m1_pre_topc @ X8 @ X9 )
      | ~ ( v3_pre_topc @ ( sk_C @ X8 @ X9 ) @ X9 )
      | ( v1_tsep_1 @ X8 @ X9 )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[d1_tsep_1])).

thf('216',plain,
    ( ( ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_B ) @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v1_tsep_1 @ sk_B @ sk_A )
      | ~ ( m1_pre_topc @ sk_B @ sk_A ) )
   <= ~ ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['214','215'])).

thf('217',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('218',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('219',plain,
    ( ( ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_B ) @ sk_A )
      | ( v1_tsep_1 @ sk_B @ sk_A ) )
   <= ~ ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['216','217','218'])).

thf('220',plain,
    ( ~ ( v1_tsep_1 @ sk_B @ sk_A )
   <= ~ ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['114'])).

thf('221',plain,
    ( ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_B ) @ sk_A )
   <= ~ ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['219','220'])).

thf('222',plain,
    ( ( ( v1_tsep_1 @ sk_B @ sk_A )
      | ~ ( r2_hidden @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_A ) ) )
   <= ~ ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['213','221'])).

thf('223',plain,
    ( ~ ( v1_tsep_1 @ sk_B @ sk_A )
   <= ~ ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['114'])).

thf('224',plain,
    ( ~ ( r2_hidden @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_A ) )
   <= ~ ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['222','223'])).

thf('225',plain,(
    ~ ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['115','118','175'])).

thf('226',plain,(
    ~ ( r2_hidden @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_A ) ) ),
    inference(simpl_trail,[status(thm)],['224','225'])).

thf('227',plain,(
    ( u1_pre_topc @ sk_A )
 != ( u1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['194','226'])).

thf('228',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['184','227'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.uphSH13g1D
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:13:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.43/0.62  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.43/0.62  % Solved by: fo/fo7.sh
% 0.43/0.62  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.43/0.62  % done 369 iterations in 0.154s
% 0.43/0.62  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.43/0.62  % SZS output start Refutation
% 0.43/0.62  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.43/0.62  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.43/0.62  thf(sk_A_type, type, sk_A: $i).
% 0.43/0.62  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 0.43/0.62  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.43/0.62  thf(g1_pre_topc_type, type, g1_pre_topc: $i > $i > $i).
% 0.43/0.62  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.43/0.62  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.43/0.62  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.43/0.62  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 0.43/0.62  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.43/0.62  thf(v1_tsep_1_type, type, v1_tsep_1: $i > $i > $o).
% 0.43/0.62  thf(k5_tmap_1_type, type, k5_tmap_1: $i > $i > $i).
% 0.43/0.62  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.43/0.62  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.44/0.62  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.44/0.62  thf(k8_tmap_1_type, type, k8_tmap_1: $i > $i > $i).
% 0.44/0.62  thf(sk_B_type, type, sk_B: $i).
% 0.44/0.62  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.44/0.62  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.44/0.62  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.44/0.62  thf(t2_tsep_1, axiom,
% 0.44/0.62    (![A:$i]: ( ( l1_pre_topc @ A ) => ( m1_pre_topc @ A @ A ) ))).
% 0.44/0.62  thf('0', plain,
% 0.44/0.62      (![X20 : $i]: ((m1_pre_topc @ X20 @ X20) | ~ (l1_pre_topc @ X20))),
% 0.44/0.62      inference('cnf', [status(esa)], [t2_tsep_1])).
% 0.44/0.62  thf(t116_tmap_1, conjecture,
% 0.44/0.62    (![A:$i]:
% 0.44/0.62     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.44/0.62       ( ![B:$i]:
% 0.44/0.62         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.44/0.62           ( ( ( v1_tsep_1 @ B @ A ) & ( m1_pre_topc @ B @ A ) ) <=>
% 0.44/0.62             ( ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) =
% 0.44/0.62               ( k8_tmap_1 @ A @ B ) ) ) ) ) ))).
% 0.44/0.62  thf(zf_stmt_0, negated_conjecture,
% 0.44/0.62    (~( ![A:$i]:
% 0.44/0.62        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.44/0.62            ( l1_pre_topc @ A ) ) =>
% 0.44/0.62          ( ![B:$i]:
% 0.44/0.62            ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.44/0.62              ( ( ( v1_tsep_1 @ B @ A ) & ( m1_pre_topc @ B @ A ) ) <=>
% 0.44/0.62                ( ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) =
% 0.44/0.62                  ( k8_tmap_1 @ A @ B ) ) ) ) ) ) )),
% 0.44/0.62    inference('cnf.neg', [status(esa)], [t116_tmap_1])).
% 0.44/0.62  thf('1', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf(t114_tmap_1, axiom,
% 0.44/0.62    (![A:$i]:
% 0.44/0.62     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.44/0.62       ( ![B:$i]:
% 0.44/0.62         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.44/0.62           ( ( ( u1_struct_0 @ ( k8_tmap_1 @ A @ B ) ) = ( u1_struct_0 @ A ) ) & 
% 0.44/0.62             ( ![C:$i]:
% 0.44/0.62               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.44/0.62                 ( ( ( C ) = ( u1_struct_0 @ B ) ) =>
% 0.44/0.62                   ( ( u1_pre_topc @ ( k8_tmap_1 @ A @ B ) ) =
% 0.44/0.62                     ( k5_tmap_1 @ A @ C ) ) ) ) ) ) ) ) ))).
% 0.44/0.62  thf('2', plain,
% 0.44/0.62      (![X15 : $i, X16 : $i]:
% 0.44/0.62         ((v2_struct_0 @ X15)
% 0.44/0.62          | ~ (m1_pre_topc @ X15 @ X16)
% 0.44/0.62          | ((u1_struct_0 @ (k8_tmap_1 @ X16 @ X15)) = (u1_struct_0 @ X16))
% 0.44/0.62          | ~ (l1_pre_topc @ X16)
% 0.44/0.62          | ~ (v2_pre_topc @ X16)
% 0.44/0.62          | (v2_struct_0 @ X16))),
% 0.44/0.62      inference('cnf', [status(esa)], [t114_tmap_1])).
% 0.44/0.62  thf('3', plain,
% 0.44/0.62      (((v2_struct_0 @ sk_A)
% 0.44/0.62        | ~ (v2_pre_topc @ sk_A)
% 0.44/0.62        | ~ (l1_pre_topc @ sk_A)
% 0.44/0.62        | ((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))
% 0.44/0.62        | (v2_struct_0 @ sk_B))),
% 0.44/0.62      inference('sup-', [status(thm)], ['1', '2'])).
% 0.44/0.62  thf('4', plain, ((v2_pre_topc @ sk_A)),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('5', plain, ((l1_pre_topc @ sk_A)),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('6', plain,
% 0.44/0.62      (((v2_struct_0 @ sk_A)
% 0.44/0.62        | ((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))
% 0.44/0.62        | (v2_struct_0 @ sk_B))),
% 0.44/0.62      inference('demod', [status(thm)], ['3', '4', '5'])).
% 0.44/0.62  thf('7', plain, (~ (v2_struct_0 @ sk_A)),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('8', plain,
% 0.44/0.62      (((v2_struct_0 @ sk_B)
% 0.44/0.62        | ((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A)))),
% 0.44/0.62      inference('clc', [status(thm)], ['6', '7'])).
% 0.44/0.62  thf('9', plain, (~ (v2_struct_0 @ sk_B)),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('10', plain,
% 0.44/0.62      (((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 0.44/0.62      inference('clc', [status(thm)], ['8', '9'])).
% 0.44/0.62  thf('11', plain,
% 0.44/0.62      (![X20 : $i]: ((m1_pre_topc @ X20 @ X20) | ~ (l1_pre_topc @ X20))),
% 0.44/0.62      inference('cnf', [status(esa)], [t2_tsep_1])).
% 0.44/0.62  thf(t1_tsep_1, axiom,
% 0.44/0.62    (![A:$i]:
% 0.44/0.62     ( ( l1_pre_topc @ A ) =>
% 0.44/0.62       ( ![B:$i]:
% 0.44/0.62         ( ( m1_pre_topc @ B @ A ) =>
% 0.44/0.62           ( m1_subset_1 @
% 0.44/0.62             ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.44/0.62  thf('12', plain,
% 0.44/0.62      (![X18 : $i, X19 : $i]:
% 0.44/0.62         (~ (m1_pre_topc @ X18 @ X19)
% 0.44/0.62          | (m1_subset_1 @ (u1_struct_0 @ X18) @ 
% 0.44/0.62             (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.44/0.62          | ~ (l1_pre_topc @ X19))),
% 0.44/0.62      inference('cnf', [status(esa)], [t1_tsep_1])).
% 0.44/0.62  thf('13', plain,
% 0.44/0.62      (![X0 : $i]:
% 0.44/0.62         (~ (l1_pre_topc @ X0)
% 0.44/0.62          | ~ (l1_pre_topc @ X0)
% 0.44/0.62          | (m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 0.44/0.62             (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.44/0.62      inference('sup-', [status(thm)], ['11', '12'])).
% 0.44/0.62  thf('14', plain,
% 0.44/0.62      (![X0 : $i]:
% 0.44/0.62         ((m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 0.44/0.62           (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.44/0.62          | ~ (l1_pre_topc @ X0))),
% 0.44/0.62      inference('simplify', [status(thm)], ['13'])).
% 0.44/0.62  thf('15', plain,
% 0.44/0.62      (((m1_subset_1 @ (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)) @ 
% 0.44/0.62         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.44/0.62        | ~ (l1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B)))),
% 0.44/0.62      inference('sup+', [status(thm)], ['10', '14'])).
% 0.44/0.62  thf('16', plain,
% 0.44/0.62      (((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 0.44/0.62      inference('clc', [status(thm)], ['8', '9'])).
% 0.44/0.62  thf('17', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf(dt_k8_tmap_1, axiom,
% 0.44/0.62    (![A:$i,B:$i]:
% 0.44/0.62     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.44/0.62         ( l1_pre_topc @ A ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.44/0.62       ( ( v1_pre_topc @ ( k8_tmap_1 @ A @ B ) ) & 
% 0.44/0.62         ( v2_pre_topc @ ( k8_tmap_1 @ A @ B ) ) & 
% 0.44/0.62         ( l1_pre_topc @ ( k8_tmap_1 @ A @ B ) ) ) ))).
% 0.44/0.62  thf('18', plain,
% 0.44/0.62      (![X11 : $i, X12 : $i]:
% 0.44/0.62         (~ (l1_pre_topc @ X11)
% 0.44/0.62          | ~ (v2_pre_topc @ X11)
% 0.44/0.62          | (v2_struct_0 @ X11)
% 0.44/0.62          | ~ (m1_pre_topc @ X12 @ X11)
% 0.44/0.62          | (l1_pre_topc @ (k8_tmap_1 @ X11 @ X12)))),
% 0.44/0.62      inference('cnf', [status(esa)], [dt_k8_tmap_1])).
% 0.44/0.62  thf('19', plain,
% 0.44/0.62      (((l1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.44/0.62        | (v2_struct_0 @ sk_A)
% 0.44/0.62        | ~ (v2_pre_topc @ sk_A)
% 0.44/0.62        | ~ (l1_pre_topc @ sk_A))),
% 0.44/0.62      inference('sup-', [status(thm)], ['17', '18'])).
% 0.44/0.62  thf('20', plain, ((v2_pre_topc @ sk_A)),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('21', plain, ((l1_pre_topc @ sk_A)),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('22', plain,
% 0.44/0.62      (((l1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B)) | (v2_struct_0 @ sk_A))),
% 0.44/0.62      inference('demod', [status(thm)], ['19', '20', '21'])).
% 0.44/0.62  thf('23', plain, (~ (v2_struct_0 @ sk_A)),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('24', plain, ((l1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))),
% 0.44/0.62      inference('clc', [status(thm)], ['22', '23'])).
% 0.44/0.62  thf('25', plain,
% 0.44/0.62      ((m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.44/0.62        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.44/0.62      inference('demod', [status(thm)], ['15', '16', '24'])).
% 0.44/0.62  thf('26', plain,
% 0.44/0.62      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.44/0.62         ((v2_struct_0 @ X15)
% 0.44/0.62          | ~ (m1_pre_topc @ X15 @ X16)
% 0.44/0.62          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.44/0.62          | ((u1_pre_topc @ (k8_tmap_1 @ X16 @ X15)) = (k5_tmap_1 @ X16 @ X17))
% 0.44/0.62          | ((X17) != (u1_struct_0 @ X15))
% 0.44/0.62          | ~ (l1_pre_topc @ X16)
% 0.44/0.62          | ~ (v2_pre_topc @ X16)
% 0.44/0.62          | (v2_struct_0 @ X16))),
% 0.44/0.62      inference('cnf', [status(esa)], [t114_tmap_1])).
% 0.44/0.62  thf('27', plain,
% 0.44/0.62      (![X15 : $i, X16 : $i]:
% 0.44/0.62         ((v2_struct_0 @ X16)
% 0.44/0.62          | ~ (v2_pre_topc @ X16)
% 0.44/0.62          | ~ (l1_pre_topc @ X16)
% 0.44/0.62          | ((u1_pre_topc @ (k8_tmap_1 @ X16 @ X15))
% 0.44/0.62              = (k5_tmap_1 @ X16 @ (u1_struct_0 @ X15)))
% 0.44/0.62          | ~ (m1_subset_1 @ (u1_struct_0 @ X15) @ 
% 0.44/0.62               (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.44/0.62          | ~ (m1_pre_topc @ X15 @ X16)
% 0.44/0.62          | (v2_struct_0 @ X15))),
% 0.44/0.62      inference('simplify', [status(thm)], ['26'])).
% 0.44/0.62  thf('28', plain,
% 0.44/0.62      (((v2_struct_0 @ sk_A)
% 0.44/0.62        | ~ (m1_pre_topc @ sk_A @ sk_A)
% 0.44/0.62        | ((u1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_A))
% 0.44/0.62            = (k5_tmap_1 @ sk_A @ (u1_struct_0 @ sk_A)))
% 0.44/0.62        | ~ (l1_pre_topc @ sk_A)
% 0.44/0.62        | ~ (v2_pre_topc @ sk_A)
% 0.44/0.62        | (v2_struct_0 @ sk_A))),
% 0.44/0.62      inference('sup-', [status(thm)], ['25', '27'])).
% 0.44/0.62  thf('29', plain, ((l1_pre_topc @ sk_A)),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('30', plain, ((v2_pre_topc @ sk_A)),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('31', plain,
% 0.44/0.62      (((v2_struct_0 @ sk_A)
% 0.44/0.62        | ~ (m1_pre_topc @ sk_A @ sk_A)
% 0.44/0.62        | ((u1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_A))
% 0.44/0.62            = (k5_tmap_1 @ sk_A @ (u1_struct_0 @ sk_A)))
% 0.44/0.62        | (v2_struct_0 @ sk_A))),
% 0.44/0.62      inference('demod', [status(thm)], ['28', '29', '30'])).
% 0.44/0.62  thf('32', plain,
% 0.44/0.62      ((((u1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_A))
% 0.44/0.62          = (k5_tmap_1 @ sk_A @ (u1_struct_0 @ sk_A)))
% 0.44/0.62        | ~ (m1_pre_topc @ sk_A @ sk_A)
% 0.44/0.62        | (v2_struct_0 @ sk_A))),
% 0.44/0.62      inference('simplify', [status(thm)], ['31'])).
% 0.44/0.62  thf(t43_tops_1, axiom,
% 0.44/0.62    (![A:$i]:
% 0.44/0.62     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.44/0.62       ( ( k1_tops_1 @ A @ ( k2_struct_0 @ A ) ) = ( k2_struct_0 @ A ) ) ))).
% 0.44/0.62  thf('33', plain,
% 0.44/0.62      (![X7 : $i]:
% 0.44/0.62         (((k1_tops_1 @ X7 @ (k2_struct_0 @ X7)) = (k2_struct_0 @ X7))
% 0.44/0.62          | ~ (l1_pre_topc @ X7)
% 0.44/0.62          | ~ (v2_pre_topc @ X7))),
% 0.44/0.62      inference('cnf', [status(esa)], [t43_tops_1])).
% 0.44/0.62  thf(d3_struct_0, axiom,
% 0.44/0.62    (![A:$i]:
% 0.44/0.62     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.44/0.62  thf('34', plain,
% 0.44/0.62      (![X1 : $i]:
% 0.44/0.62         (((k2_struct_0 @ X1) = (u1_struct_0 @ X1)) | ~ (l1_struct_0 @ X1))),
% 0.44/0.62      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.44/0.62  thf('35', plain,
% 0.44/0.62      (![X0 : $i]:
% 0.44/0.62         ((m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 0.44/0.62           (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.44/0.62          | ~ (l1_pre_topc @ X0))),
% 0.44/0.62      inference('simplify', [status(thm)], ['13'])).
% 0.44/0.62  thf('36', plain,
% 0.44/0.62      (![X0 : $i]:
% 0.44/0.62         ((m1_subset_1 @ (k2_struct_0 @ X0) @ 
% 0.44/0.62           (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.44/0.62          | ~ (l1_struct_0 @ X0)
% 0.44/0.62          | ~ (l1_pre_topc @ X0))),
% 0.44/0.62      inference('sup+', [status(thm)], ['34', '35'])).
% 0.44/0.62  thf(dt_l1_pre_topc, axiom,
% 0.44/0.62    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.44/0.62  thf('37', plain, (![X4 : $i]: ((l1_struct_0 @ X4) | ~ (l1_pre_topc @ X4))),
% 0.44/0.62      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.44/0.62  thf('38', plain,
% 0.44/0.62      (![X0 : $i]:
% 0.44/0.62         (~ (l1_pre_topc @ X0)
% 0.44/0.62          | (m1_subset_1 @ (k2_struct_0 @ X0) @ 
% 0.44/0.62             (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.44/0.62      inference('clc', [status(thm)], ['36', '37'])).
% 0.44/0.62  thf(fc9_tops_1, axiom,
% 0.44/0.62    (![A:$i,B:$i]:
% 0.44/0.62     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 0.44/0.62         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.44/0.62       ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ))).
% 0.44/0.62  thf('39', plain,
% 0.44/0.62      (![X5 : $i, X6 : $i]:
% 0.44/0.62         (~ (l1_pre_topc @ X5)
% 0.44/0.62          | ~ (v2_pre_topc @ X5)
% 0.44/0.62          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (u1_struct_0 @ X5)))
% 0.44/0.62          | (v3_pre_topc @ (k1_tops_1 @ X5 @ X6) @ X5))),
% 0.44/0.62      inference('cnf', [status(esa)], [fc9_tops_1])).
% 0.44/0.62  thf('40', plain,
% 0.44/0.62      (![X0 : $i]:
% 0.44/0.62         (~ (l1_pre_topc @ X0)
% 0.44/0.62          | (v3_pre_topc @ (k1_tops_1 @ X0 @ (k2_struct_0 @ X0)) @ X0)
% 0.44/0.62          | ~ (v2_pre_topc @ X0)
% 0.44/0.62          | ~ (l1_pre_topc @ X0))),
% 0.44/0.62      inference('sup-', [status(thm)], ['38', '39'])).
% 0.44/0.62  thf('41', plain,
% 0.44/0.62      (![X0 : $i]:
% 0.44/0.62         (~ (v2_pre_topc @ X0)
% 0.44/0.62          | (v3_pre_topc @ (k1_tops_1 @ X0 @ (k2_struct_0 @ X0)) @ X0)
% 0.44/0.62          | ~ (l1_pre_topc @ X0))),
% 0.44/0.62      inference('simplify', [status(thm)], ['40'])).
% 0.44/0.62  thf('42', plain,
% 0.44/0.62      (![X0 : $i]:
% 0.44/0.62         ((v3_pre_topc @ (k2_struct_0 @ X0) @ X0)
% 0.44/0.62          | ~ (v2_pre_topc @ X0)
% 0.44/0.62          | ~ (l1_pre_topc @ X0)
% 0.44/0.62          | ~ (l1_pre_topc @ X0)
% 0.44/0.62          | ~ (v2_pre_topc @ X0))),
% 0.44/0.62      inference('sup+', [status(thm)], ['33', '41'])).
% 0.44/0.62  thf('43', plain,
% 0.44/0.62      (![X0 : $i]:
% 0.44/0.62         (~ (l1_pre_topc @ X0)
% 0.44/0.62          | ~ (v2_pre_topc @ X0)
% 0.44/0.62          | (v3_pre_topc @ (k2_struct_0 @ X0) @ X0))),
% 0.44/0.62      inference('simplify', [status(thm)], ['42'])).
% 0.44/0.62  thf('44', plain,
% 0.44/0.62      (![X1 : $i]:
% 0.44/0.62         (((k2_struct_0 @ X1) = (u1_struct_0 @ X1)) | ~ (l1_struct_0 @ X1))),
% 0.44/0.62      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.44/0.62  thf('45', plain,
% 0.44/0.62      (![X0 : $i]:
% 0.44/0.62         ((m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 0.44/0.62           (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.44/0.62          | ~ (l1_pre_topc @ X0))),
% 0.44/0.62      inference('simplify', [status(thm)], ['13'])).
% 0.44/0.62  thf(d5_pre_topc, axiom,
% 0.44/0.62    (![A:$i]:
% 0.44/0.62     ( ( l1_pre_topc @ A ) =>
% 0.44/0.62       ( ![B:$i]:
% 0.44/0.62         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.44/0.62           ( ( v3_pre_topc @ B @ A ) <=>
% 0.44/0.62             ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) ) ) ) ))).
% 0.44/0.62  thf('46', plain,
% 0.44/0.62      (![X2 : $i, X3 : $i]:
% 0.44/0.62         (~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ X3)))
% 0.44/0.62          | ~ (v3_pre_topc @ X2 @ X3)
% 0.44/0.62          | (r2_hidden @ X2 @ (u1_pre_topc @ X3))
% 0.44/0.62          | ~ (l1_pre_topc @ X3))),
% 0.44/0.62      inference('cnf', [status(esa)], [d5_pre_topc])).
% 0.44/0.62  thf('47', plain,
% 0.44/0.62      (![X0 : $i]:
% 0.44/0.62         (~ (l1_pre_topc @ X0)
% 0.44/0.62          | ~ (l1_pre_topc @ X0)
% 0.44/0.62          | (r2_hidden @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))
% 0.44/0.62          | ~ (v3_pre_topc @ (u1_struct_0 @ X0) @ X0))),
% 0.44/0.62      inference('sup-', [status(thm)], ['45', '46'])).
% 0.44/0.62  thf('48', plain,
% 0.44/0.62      (![X0 : $i]:
% 0.44/0.62         (~ (v3_pre_topc @ (u1_struct_0 @ X0) @ X0)
% 0.44/0.62          | (r2_hidden @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))
% 0.44/0.62          | ~ (l1_pre_topc @ X0))),
% 0.44/0.62      inference('simplify', [status(thm)], ['47'])).
% 0.44/0.62  thf('49', plain,
% 0.44/0.62      (![X0 : $i]:
% 0.44/0.62         (~ (v3_pre_topc @ (k2_struct_0 @ X0) @ X0)
% 0.44/0.62          | ~ (l1_struct_0 @ X0)
% 0.44/0.62          | ~ (l1_pre_topc @ X0)
% 0.44/0.62          | (r2_hidden @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))),
% 0.44/0.62      inference('sup-', [status(thm)], ['44', '48'])).
% 0.44/0.62  thf('50', plain,
% 0.44/0.62      (![X0 : $i]:
% 0.44/0.62         (~ (v2_pre_topc @ X0)
% 0.44/0.62          | ~ (l1_pre_topc @ X0)
% 0.44/0.62          | (r2_hidden @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))
% 0.44/0.62          | ~ (l1_pre_topc @ X0)
% 0.44/0.62          | ~ (l1_struct_0 @ X0))),
% 0.44/0.62      inference('sup-', [status(thm)], ['43', '49'])).
% 0.44/0.62  thf('51', plain,
% 0.44/0.62      (![X0 : $i]:
% 0.44/0.62         (~ (l1_struct_0 @ X0)
% 0.44/0.62          | (r2_hidden @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))
% 0.44/0.62          | ~ (l1_pre_topc @ X0)
% 0.44/0.62          | ~ (v2_pre_topc @ X0))),
% 0.44/0.62      inference('simplify', [status(thm)], ['50'])).
% 0.44/0.62  thf('52', plain,
% 0.44/0.62      ((m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.44/0.62        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.44/0.62      inference('demod', [status(thm)], ['15', '16', '24'])).
% 0.44/0.62  thf('53', plain,
% 0.44/0.62      (![X2 : $i, X3 : $i]:
% 0.44/0.62         (~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ X3)))
% 0.44/0.62          | ~ (r2_hidden @ X2 @ (u1_pre_topc @ X3))
% 0.44/0.62          | (v3_pre_topc @ X2 @ X3)
% 0.44/0.62          | ~ (l1_pre_topc @ X3))),
% 0.44/0.62      inference('cnf', [status(esa)], [d5_pre_topc])).
% 0.44/0.62  thf('54', plain,
% 0.44/0.62      ((~ (l1_pre_topc @ sk_A)
% 0.44/0.62        | (v3_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A)
% 0.44/0.62        | ~ (r2_hidden @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))),
% 0.44/0.62      inference('sup-', [status(thm)], ['52', '53'])).
% 0.44/0.62  thf('55', plain, ((l1_pre_topc @ sk_A)),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('56', plain,
% 0.44/0.62      (((v3_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A)
% 0.44/0.62        | ~ (r2_hidden @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))),
% 0.44/0.62      inference('demod', [status(thm)], ['54', '55'])).
% 0.44/0.62  thf('57', plain,
% 0.44/0.62      ((~ (v2_pre_topc @ sk_A)
% 0.44/0.62        | ~ (l1_pre_topc @ sk_A)
% 0.44/0.62        | ~ (l1_struct_0 @ sk_A)
% 0.44/0.62        | (v3_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A))),
% 0.44/0.62      inference('sup-', [status(thm)], ['51', '56'])).
% 0.44/0.62  thf('58', plain, ((v2_pre_topc @ sk_A)),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('59', plain, ((l1_pre_topc @ sk_A)),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('60', plain, ((l1_pre_topc @ sk_A)),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('61', plain, (![X4 : $i]: ((l1_struct_0 @ X4) | ~ (l1_pre_topc @ X4))),
% 0.44/0.62      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.44/0.62  thf('62', plain, ((l1_struct_0 @ sk_A)),
% 0.44/0.62      inference('sup-', [status(thm)], ['60', '61'])).
% 0.44/0.62  thf('63', plain, ((v3_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A)),
% 0.44/0.62      inference('demod', [status(thm)], ['57', '58', '59', '62'])).
% 0.44/0.62  thf('64', plain,
% 0.44/0.62      (![X0 : $i]:
% 0.44/0.62         (~ (v3_pre_topc @ (u1_struct_0 @ X0) @ X0)
% 0.44/0.62          | (r2_hidden @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))
% 0.44/0.62          | ~ (l1_pre_topc @ X0))),
% 0.44/0.62      inference('simplify', [status(thm)], ['47'])).
% 0.44/0.62  thf('65', plain,
% 0.44/0.62      ((~ (l1_pre_topc @ sk_A)
% 0.44/0.62        | (r2_hidden @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))),
% 0.44/0.62      inference('sup-', [status(thm)], ['63', '64'])).
% 0.44/0.62  thf('66', plain, ((l1_pre_topc @ sk_A)),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('67', plain, ((r2_hidden @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))),
% 0.44/0.62      inference('demod', [status(thm)], ['65', '66'])).
% 0.44/0.62  thf('68', plain,
% 0.44/0.62      (![X0 : $i]:
% 0.44/0.62         ((m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 0.44/0.62           (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.44/0.62          | ~ (l1_pre_topc @ X0))),
% 0.44/0.62      inference('simplify', [status(thm)], ['13'])).
% 0.44/0.62  thf(t103_tmap_1, axiom,
% 0.44/0.62    (![A:$i]:
% 0.44/0.62     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.44/0.62       ( ![B:$i]:
% 0.44/0.62         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.44/0.62           ( ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) <=>
% 0.44/0.62             ( ( u1_pre_topc @ A ) = ( k5_tmap_1 @ A @ B ) ) ) ) ) ))).
% 0.44/0.62  thf('69', plain,
% 0.44/0.62      (![X13 : $i, X14 : $i]:
% 0.44/0.62         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.44/0.62          | ~ (r2_hidden @ X13 @ (u1_pre_topc @ X14))
% 0.44/0.62          | ((u1_pre_topc @ X14) = (k5_tmap_1 @ X14 @ X13))
% 0.44/0.62          | ~ (l1_pre_topc @ X14)
% 0.44/0.62          | ~ (v2_pre_topc @ X14)
% 0.44/0.62          | (v2_struct_0 @ X14))),
% 0.44/0.62      inference('cnf', [status(esa)], [t103_tmap_1])).
% 0.44/0.62  thf('70', plain,
% 0.44/0.62      (![X0 : $i]:
% 0.44/0.62         (~ (l1_pre_topc @ X0)
% 0.44/0.62          | (v2_struct_0 @ X0)
% 0.44/0.62          | ~ (v2_pre_topc @ X0)
% 0.44/0.62          | ~ (l1_pre_topc @ X0)
% 0.44/0.62          | ((u1_pre_topc @ X0) = (k5_tmap_1 @ X0 @ (u1_struct_0 @ X0)))
% 0.44/0.62          | ~ (r2_hidden @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))),
% 0.44/0.62      inference('sup-', [status(thm)], ['68', '69'])).
% 0.44/0.62  thf('71', plain,
% 0.44/0.62      (![X0 : $i]:
% 0.44/0.62         (~ (r2_hidden @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))
% 0.44/0.62          | ((u1_pre_topc @ X0) = (k5_tmap_1 @ X0 @ (u1_struct_0 @ X0)))
% 0.44/0.62          | ~ (v2_pre_topc @ X0)
% 0.44/0.62          | (v2_struct_0 @ X0)
% 0.44/0.62          | ~ (l1_pre_topc @ X0))),
% 0.44/0.62      inference('simplify', [status(thm)], ['70'])).
% 0.44/0.62  thf('72', plain,
% 0.44/0.62      ((~ (l1_pre_topc @ sk_A)
% 0.44/0.62        | (v2_struct_0 @ sk_A)
% 0.44/0.62        | ~ (v2_pre_topc @ sk_A)
% 0.44/0.62        | ((u1_pre_topc @ sk_A) = (k5_tmap_1 @ sk_A @ (u1_struct_0 @ sk_A))))),
% 0.44/0.62      inference('sup-', [status(thm)], ['67', '71'])).
% 0.44/0.62  thf('73', plain, ((l1_pre_topc @ sk_A)),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('74', plain, ((v2_pre_topc @ sk_A)),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('75', plain,
% 0.44/0.62      (((v2_struct_0 @ sk_A)
% 0.44/0.62        | ((u1_pre_topc @ sk_A) = (k5_tmap_1 @ sk_A @ (u1_struct_0 @ sk_A))))),
% 0.44/0.62      inference('demod', [status(thm)], ['72', '73', '74'])).
% 0.44/0.62  thf('76', plain, (~ (v2_struct_0 @ sk_A)),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('77', plain,
% 0.44/0.62      (((u1_pre_topc @ sk_A) = (k5_tmap_1 @ sk_A @ (u1_struct_0 @ sk_A)))),
% 0.44/0.62      inference('clc', [status(thm)], ['75', '76'])).
% 0.44/0.62  thf('78', plain,
% 0.44/0.62      ((((u1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_A)) = (u1_pre_topc @ sk_A))
% 0.44/0.62        | ~ (m1_pre_topc @ sk_A @ sk_A)
% 0.44/0.62        | (v2_struct_0 @ sk_A))),
% 0.44/0.62      inference('demod', [status(thm)], ['32', '77'])).
% 0.44/0.62  thf('79', plain, (~ (v2_struct_0 @ sk_A)),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('80', plain,
% 0.44/0.62      ((~ (m1_pre_topc @ sk_A @ sk_A)
% 0.44/0.62        | ((u1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_A)) = (u1_pre_topc @ sk_A)))),
% 0.44/0.62      inference('clc', [status(thm)], ['78', '79'])).
% 0.44/0.62  thf('81', plain,
% 0.44/0.62      ((~ (l1_pre_topc @ sk_A)
% 0.44/0.62        | ((u1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_A)) = (u1_pre_topc @ sk_A)))),
% 0.44/0.62      inference('sup-', [status(thm)], ['0', '80'])).
% 0.44/0.62  thf('82', plain, ((l1_pre_topc @ sk_A)),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('83', plain,
% 0.44/0.62      (((u1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_A)) = (u1_pre_topc @ sk_A))),
% 0.44/0.62      inference('demod', [status(thm)], ['81', '82'])).
% 0.44/0.62  thf('84', plain,
% 0.44/0.62      (![X20 : $i]: ((m1_pre_topc @ X20 @ X20) | ~ (l1_pre_topc @ X20))),
% 0.44/0.62      inference('cnf', [status(esa)], [t2_tsep_1])).
% 0.44/0.62  thf('85', plain,
% 0.44/0.62      (![X15 : $i, X16 : $i]:
% 0.44/0.62         ((v2_struct_0 @ X15)
% 0.44/0.62          | ~ (m1_pre_topc @ X15 @ X16)
% 0.44/0.62          | ((u1_struct_0 @ (k8_tmap_1 @ X16 @ X15)) = (u1_struct_0 @ X16))
% 0.44/0.62          | ~ (l1_pre_topc @ X16)
% 0.44/0.62          | ~ (v2_pre_topc @ X16)
% 0.44/0.62          | (v2_struct_0 @ X16))),
% 0.44/0.62      inference('cnf', [status(esa)], [t114_tmap_1])).
% 0.44/0.62  thf('86', plain,
% 0.44/0.62      (![X0 : $i]:
% 0.44/0.62         (~ (l1_pre_topc @ X0)
% 0.44/0.62          | (v2_struct_0 @ X0)
% 0.44/0.62          | ~ (v2_pre_topc @ X0)
% 0.44/0.62          | ~ (l1_pre_topc @ X0)
% 0.44/0.62          | ((u1_struct_0 @ (k8_tmap_1 @ X0 @ X0)) = (u1_struct_0 @ X0))
% 0.44/0.62          | (v2_struct_0 @ X0))),
% 0.44/0.62      inference('sup-', [status(thm)], ['84', '85'])).
% 0.44/0.62  thf('87', plain,
% 0.44/0.62      (![X0 : $i]:
% 0.44/0.62         (((u1_struct_0 @ (k8_tmap_1 @ X0 @ X0)) = (u1_struct_0 @ X0))
% 0.44/0.62          | ~ (v2_pre_topc @ X0)
% 0.44/0.62          | (v2_struct_0 @ X0)
% 0.44/0.62          | ~ (l1_pre_topc @ X0))),
% 0.44/0.62      inference('simplify', [status(thm)], ['86'])).
% 0.44/0.62  thf('88', plain,
% 0.44/0.62      (![X20 : $i]: ((m1_pre_topc @ X20 @ X20) | ~ (l1_pre_topc @ X20))),
% 0.44/0.62      inference('cnf', [status(esa)], [t2_tsep_1])).
% 0.44/0.62  thf('89', plain,
% 0.44/0.62      (![X11 : $i, X12 : $i]:
% 0.44/0.62         (~ (l1_pre_topc @ X11)
% 0.44/0.62          | ~ (v2_pre_topc @ X11)
% 0.44/0.62          | (v2_struct_0 @ X11)
% 0.44/0.62          | ~ (m1_pre_topc @ X12 @ X11)
% 0.44/0.62          | (v1_pre_topc @ (k8_tmap_1 @ X11 @ X12)))),
% 0.44/0.62      inference('cnf', [status(esa)], [dt_k8_tmap_1])).
% 0.44/0.62  thf('90', plain,
% 0.44/0.62      (![X0 : $i]:
% 0.44/0.62         (~ (l1_pre_topc @ X0)
% 0.44/0.62          | (v1_pre_topc @ (k8_tmap_1 @ X0 @ X0))
% 0.44/0.62          | (v2_struct_0 @ X0)
% 0.44/0.62          | ~ (v2_pre_topc @ X0)
% 0.44/0.62          | ~ (l1_pre_topc @ X0))),
% 0.44/0.62      inference('sup-', [status(thm)], ['88', '89'])).
% 0.44/0.62  thf('91', plain,
% 0.44/0.62      (![X0 : $i]:
% 0.44/0.62         (~ (v2_pre_topc @ X0)
% 0.44/0.62          | (v2_struct_0 @ X0)
% 0.44/0.62          | (v1_pre_topc @ (k8_tmap_1 @ X0 @ X0))
% 0.44/0.62          | ~ (l1_pre_topc @ X0))),
% 0.44/0.62      inference('simplify', [status(thm)], ['90'])).
% 0.44/0.62  thf('92', plain,
% 0.44/0.62      (![X20 : $i]: ((m1_pre_topc @ X20 @ X20) | ~ (l1_pre_topc @ X20))),
% 0.44/0.62      inference('cnf', [status(esa)], [t2_tsep_1])).
% 0.44/0.62  thf('93', plain,
% 0.44/0.62      (![X11 : $i, X12 : $i]:
% 0.44/0.62         (~ (l1_pre_topc @ X11)
% 0.44/0.62          | ~ (v2_pre_topc @ X11)
% 0.44/0.62          | (v2_struct_0 @ X11)
% 0.44/0.62          | ~ (m1_pre_topc @ X12 @ X11)
% 0.44/0.62          | (l1_pre_topc @ (k8_tmap_1 @ X11 @ X12)))),
% 0.44/0.62      inference('cnf', [status(esa)], [dt_k8_tmap_1])).
% 0.44/0.62  thf('94', plain,
% 0.44/0.62      (![X0 : $i]:
% 0.44/0.62         (~ (l1_pre_topc @ X0)
% 0.44/0.62          | (l1_pre_topc @ (k8_tmap_1 @ X0 @ X0))
% 0.44/0.62          | (v2_struct_0 @ X0)
% 0.44/0.62          | ~ (v2_pre_topc @ X0)
% 0.44/0.62          | ~ (l1_pre_topc @ X0))),
% 0.44/0.62      inference('sup-', [status(thm)], ['92', '93'])).
% 0.44/0.62  thf('95', plain,
% 0.44/0.62      (![X0 : $i]:
% 0.44/0.62         (~ (v2_pre_topc @ X0)
% 0.44/0.62          | (v2_struct_0 @ X0)
% 0.44/0.62          | (l1_pre_topc @ (k8_tmap_1 @ X0 @ X0))
% 0.44/0.62          | ~ (l1_pre_topc @ X0))),
% 0.44/0.62      inference('simplify', [status(thm)], ['94'])).
% 0.44/0.62  thf('96', plain,
% 0.44/0.62      (((u1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_A)) = (u1_pre_topc @ sk_A))),
% 0.44/0.62      inference('demod', [status(thm)], ['81', '82'])).
% 0.44/0.62  thf(abstractness_v1_pre_topc, axiom,
% 0.44/0.62    (![A:$i]:
% 0.44/0.62     ( ( l1_pre_topc @ A ) =>
% 0.44/0.62       ( ( v1_pre_topc @ A ) =>
% 0.44/0.62         ( ( A ) = ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ))).
% 0.44/0.62  thf('97', plain,
% 0.44/0.62      (![X0 : $i]:
% 0.44/0.62         (~ (v1_pre_topc @ X0)
% 0.44/0.62          | ((X0) = (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.44/0.62          | ~ (l1_pre_topc @ X0))),
% 0.44/0.62      inference('cnf', [status(esa)], [abstractness_v1_pre_topc])).
% 0.44/0.62  thf('98', plain,
% 0.44/0.62      ((((k8_tmap_1 @ sk_A @ sk_A)
% 0.44/0.62          = (g1_pre_topc @ (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_A)) @ 
% 0.44/0.62             (u1_pre_topc @ sk_A)))
% 0.44/0.62        | ~ (l1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_A))
% 0.44/0.62        | ~ (v1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_A)))),
% 0.44/0.62      inference('sup+', [status(thm)], ['96', '97'])).
% 0.44/0.62  thf('99', plain,
% 0.44/0.62      ((~ (l1_pre_topc @ sk_A)
% 0.44/0.62        | (v2_struct_0 @ sk_A)
% 0.44/0.62        | ~ (v2_pre_topc @ sk_A)
% 0.44/0.62        | ~ (v1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_A))
% 0.44/0.62        | ((k8_tmap_1 @ sk_A @ sk_A)
% 0.44/0.62            = (g1_pre_topc @ (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_A)) @ 
% 0.44/0.62               (u1_pre_topc @ sk_A))))),
% 0.44/0.62      inference('sup-', [status(thm)], ['95', '98'])).
% 0.44/0.62  thf('100', plain, ((l1_pre_topc @ sk_A)),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('101', plain, ((v2_pre_topc @ sk_A)),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('102', plain,
% 0.44/0.62      (((v2_struct_0 @ sk_A)
% 0.44/0.62        | ~ (v1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_A))
% 0.44/0.62        | ((k8_tmap_1 @ sk_A @ sk_A)
% 0.44/0.62            = (g1_pre_topc @ (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_A)) @ 
% 0.44/0.62               (u1_pre_topc @ sk_A))))),
% 0.44/0.62      inference('demod', [status(thm)], ['99', '100', '101'])).
% 0.44/0.62  thf('103', plain, (~ (v2_struct_0 @ sk_A)),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('104', plain,
% 0.44/0.62      ((((k8_tmap_1 @ sk_A @ sk_A)
% 0.44/0.62          = (g1_pre_topc @ (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_A)) @ 
% 0.44/0.62             (u1_pre_topc @ sk_A)))
% 0.44/0.62        | ~ (v1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_A)))),
% 0.44/0.62      inference('clc', [status(thm)], ['102', '103'])).
% 0.44/0.62  thf('105', plain,
% 0.44/0.62      ((~ (l1_pre_topc @ sk_A)
% 0.44/0.62        | (v2_struct_0 @ sk_A)
% 0.44/0.62        | ~ (v2_pre_topc @ sk_A)
% 0.44/0.62        | ((k8_tmap_1 @ sk_A @ sk_A)
% 0.44/0.62            = (g1_pre_topc @ (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_A)) @ 
% 0.44/0.62               (u1_pre_topc @ sk_A))))),
% 0.44/0.62      inference('sup-', [status(thm)], ['91', '104'])).
% 0.44/0.62  thf('106', plain, ((l1_pre_topc @ sk_A)),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('107', plain, ((v2_pre_topc @ sk_A)),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('108', plain,
% 0.44/0.62      (((v2_struct_0 @ sk_A)
% 0.44/0.62        | ((k8_tmap_1 @ sk_A @ sk_A)
% 0.44/0.62            = (g1_pre_topc @ (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_A)) @ 
% 0.44/0.62               (u1_pre_topc @ sk_A))))),
% 0.44/0.62      inference('demod', [status(thm)], ['105', '106', '107'])).
% 0.44/0.62  thf('109', plain, (~ (v2_struct_0 @ sk_A)),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('110', plain,
% 0.44/0.62      (((k8_tmap_1 @ sk_A @ sk_A)
% 0.44/0.62         = (g1_pre_topc @ (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_A)) @ 
% 0.44/0.62            (u1_pre_topc @ sk_A)))),
% 0.44/0.62      inference('clc', [status(thm)], ['108', '109'])).
% 0.44/0.62  thf('111', plain,
% 0.44/0.62      ((((k8_tmap_1 @ sk_A @ sk_A)
% 0.44/0.62          = (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.44/0.62        | ~ (l1_pre_topc @ sk_A)
% 0.44/0.62        | (v2_struct_0 @ sk_A)
% 0.44/0.62        | ~ (v2_pre_topc @ sk_A))),
% 0.44/0.62      inference('sup+', [status(thm)], ['87', '110'])).
% 0.44/0.62  thf('112', plain,
% 0.44/0.62      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.44/0.62          = (k8_tmap_1 @ sk_A @ sk_B))
% 0.44/0.62        | (v1_tsep_1 @ sk_B @ sk_A))),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('113', plain,
% 0.44/0.62      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.44/0.62          = (k8_tmap_1 @ sk_A @ sk_B)))
% 0.44/0.62         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.44/0.62                = (k8_tmap_1 @ sk_A @ sk_B))))),
% 0.44/0.62      inference('split', [status(esa)], ['112'])).
% 0.44/0.62  thf('114', plain,
% 0.44/0.62      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.44/0.62          != (k8_tmap_1 @ sk_A @ sk_B))
% 0.44/0.62        | ~ (m1_pre_topc @ sk_B @ sk_A)
% 0.44/0.62        | ~ (v1_tsep_1 @ sk_B @ sk_A))),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('115', plain,
% 0.44/0.62      (~ ((v1_tsep_1 @ sk_B @ sk_A)) | 
% 0.44/0.62       ~
% 0.44/0.62       (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.44/0.62          = (k8_tmap_1 @ sk_A @ sk_B))) | 
% 0.44/0.62       ~ ((m1_pre_topc @ sk_B @ sk_A))),
% 0.44/0.62      inference('split', [status(esa)], ['114'])).
% 0.44/0.62  thf('116', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('117', plain,
% 0.44/0.62      ((~ (m1_pre_topc @ sk_B @ sk_A)) <= (~ ((m1_pre_topc @ sk_B @ sk_A)))),
% 0.44/0.62      inference('split', [status(esa)], ['114'])).
% 0.44/0.62  thf('118', plain, (((m1_pre_topc @ sk_B @ sk_A))),
% 0.44/0.62      inference('sup-', [status(thm)], ['116', '117'])).
% 0.44/0.62  thf('119', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('120', plain,
% 0.44/0.62      (![X18 : $i, X19 : $i]:
% 0.44/0.62         (~ (m1_pre_topc @ X18 @ X19)
% 0.44/0.62          | (m1_subset_1 @ (u1_struct_0 @ X18) @ 
% 0.44/0.62             (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.44/0.62          | ~ (l1_pre_topc @ X19))),
% 0.44/0.62      inference('cnf', [status(esa)], [t1_tsep_1])).
% 0.44/0.62  thf('121', plain,
% 0.44/0.62      ((~ (l1_pre_topc @ sk_A)
% 0.44/0.62        | (m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.44/0.62           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.44/0.62      inference('sup-', [status(thm)], ['119', '120'])).
% 0.44/0.62  thf('122', plain, ((l1_pre_topc @ sk_A)),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('123', plain,
% 0.44/0.62      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.44/0.62        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.44/0.62      inference('demod', [status(thm)], ['121', '122'])).
% 0.44/0.62  thf('124', plain,
% 0.44/0.62      (![X15 : $i, X16 : $i]:
% 0.44/0.62         ((v2_struct_0 @ X16)
% 0.44/0.62          | ~ (v2_pre_topc @ X16)
% 0.44/0.62          | ~ (l1_pre_topc @ X16)
% 0.44/0.62          | ((u1_pre_topc @ (k8_tmap_1 @ X16 @ X15))
% 0.44/0.62              = (k5_tmap_1 @ X16 @ (u1_struct_0 @ X15)))
% 0.44/0.62          | ~ (m1_subset_1 @ (u1_struct_0 @ X15) @ 
% 0.44/0.62               (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.44/0.62          | ~ (m1_pre_topc @ X15 @ X16)
% 0.44/0.62          | (v2_struct_0 @ X15))),
% 0.44/0.62      inference('simplify', [status(thm)], ['26'])).
% 0.44/0.62  thf('125', plain,
% 0.44/0.62      (((v2_struct_0 @ sk_B)
% 0.44/0.62        | ~ (m1_pre_topc @ sk_B @ sk_A)
% 0.44/0.62        | ((u1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.44/0.62            = (k5_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 0.44/0.62        | ~ (l1_pre_topc @ sk_A)
% 0.44/0.62        | ~ (v2_pre_topc @ sk_A)
% 0.44/0.63        | (v2_struct_0 @ sk_A))),
% 0.44/0.63      inference('sup-', [status(thm)], ['123', '124'])).
% 0.44/0.63  thf('126', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.44/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.63  thf('127', plain, ((l1_pre_topc @ sk_A)),
% 0.44/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.63  thf('128', plain, ((v2_pre_topc @ sk_A)),
% 0.44/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.63  thf('129', plain,
% 0.44/0.63      (((v2_struct_0 @ sk_B)
% 0.44/0.63        | ((u1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.44/0.63            = (k5_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 0.44/0.63        | (v2_struct_0 @ sk_A))),
% 0.44/0.63      inference('demod', [status(thm)], ['125', '126', '127', '128'])).
% 0.44/0.63  thf('130', plain, (~ (v2_struct_0 @ sk_B)),
% 0.44/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.63  thf('131', plain,
% 0.44/0.63      (((v2_struct_0 @ sk_A)
% 0.44/0.63        | ((u1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.44/0.63            = (k5_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B))))),
% 0.44/0.63      inference('clc', [status(thm)], ['129', '130'])).
% 0.44/0.63  thf('132', plain, (~ (v2_struct_0 @ sk_A)),
% 0.44/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.63  thf('133', plain,
% 0.44/0.63      (((u1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.44/0.63         = (k5_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))),
% 0.44/0.63      inference('clc', [status(thm)], ['131', '132'])).
% 0.44/0.63  thf('134', plain,
% 0.44/0.63      (((v1_tsep_1 @ sk_B @ sk_A)) <= (((v1_tsep_1 @ sk_B @ sk_A)))),
% 0.44/0.63      inference('split', [status(esa)], ['112'])).
% 0.44/0.63  thf('135', plain,
% 0.44/0.63      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.44/0.63        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.44/0.63      inference('demod', [status(thm)], ['121', '122'])).
% 0.44/0.63  thf(d1_tsep_1, axiom,
% 0.44/0.63    (![A:$i]:
% 0.44/0.63     ( ( l1_pre_topc @ A ) =>
% 0.44/0.63       ( ![B:$i]:
% 0.44/0.63         ( ( m1_pre_topc @ B @ A ) =>
% 0.44/0.63           ( ( v1_tsep_1 @ B @ A ) <=>
% 0.44/0.63             ( ![C:$i]:
% 0.44/0.63               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.44/0.63                 ( ( ( C ) = ( u1_struct_0 @ B ) ) => ( v3_pre_topc @ C @ A ) ) ) ) ) ) ) ))).
% 0.44/0.63  thf('136', plain,
% 0.44/0.63      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.44/0.63         (~ (m1_pre_topc @ X8 @ X9)
% 0.44/0.63          | ~ (v1_tsep_1 @ X8 @ X9)
% 0.44/0.63          | ((X10) != (u1_struct_0 @ X8))
% 0.44/0.63          | (v3_pre_topc @ X10 @ X9)
% 0.44/0.63          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.44/0.63          | ~ (l1_pre_topc @ X9))),
% 0.44/0.63      inference('cnf', [status(esa)], [d1_tsep_1])).
% 0.44/0.63  thf('137', plain,
% 0.44/0.63      (![X8 : $i, X9 : $i]:
% 0.44/0.63         (~ (l1_pre_topc @ X9)
% 0.44/0.63          | ~ (m1_subset_1 @ (u1_struct_0 @ X8) @ 
% 0.44/0.63               (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.44/0.63          | (v3_pre_topc @ (u1_struct_0 @ X8) @ X9)
% 0.44/0.63          | ~ (v1_tsep_1 @ X8 @ X9)
% 0.44/0.63          | ~ (m1_pre_topc @ X8 @ X9))),
% 0.44/0.63      inference('simplify', [status(thm)], ['136'])).
% 0.44/0.63  thf('138', plain,
% 0.44/0.63      ((~ (m1_pre_topc @ sk_B @ sk_A)
% 0.44/0.63        | ~ (v1_tsep_1 @ sk_B @ sk_A)
% 0.44/0.63        | (v3_pre_topc @ (u1_struct_0 @ sk_B) @ sk_A)
% 0.44/0.63        | ~ (l1_pre_topc @ sk_A))),
% 0.44/0.63      inference('sup-', [status(thm)], ['135', '137'])).
% 0.44/0.63  thf('139', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.44/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.63  thf('140', plain, ((l1_pre_topc @ sk_A)),
% 0.44/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.63  thf('141', plain,
% 0.44/0.63      ((~ (v1_tsep_1 @ sk_B @ sk_A)
% 0.44/0.63        | (v3_pre_topc @ (u1_struct_0 @ sk_B) @ sk_A))),
% 0.44/0.63      inference('demod', [status(thm)], ['138', '139', '140'])).
% 0.44/0.63  thf('142', plain,
% 0.44/0.63      (((v3_pre_topc @ (u1_struct_0 @ sk_B) @ sk_A))
% 0.44/0.63         <= (((v1_tsep_1 @ sk_B @ sk_A)))),
% 0.44/0.63      inference('sup-', [status(thm)], ['134', '141'])).
% 0.44/0.63  thf('143', plain,
% 0.44/0.63      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.44/0.63        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.44/0.63      inference('demod', [status(thm)], ['121', '122'])).
% 0.44/0.63  thf('144', plain,
% 0.44/0.63      (![X2 : $i, X3 : $i]:
% 0.44/0.63         (~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ X3)))
% 0.44/0.63          | ~ (v3_pre_topc @ X2 @ X3)
% 0.44/0.63          | (r2_hidden @ X2 @ (u1_pre_topc @ X3))
% 0.44/0.63          | ~ (l1_pre_topc @ X3))),
% 0.44/0.63      inference('cnf', [status(esa)], [d5_pre_topc])).
% 0.44/0.63  thf('145', plain,
% 0.44/0.63      ((~ (l1_pre_topc @ sk_A)
% 0.44/0.63        | (r2_hidden @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_A))
% 0.44/0.63        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_B) @ sk_A))),
% 0.44/0.63      inference('sup-', [status(thm)], ['143', '144'])).
% 0.44/0.63  thf('146', plain, ((l1_pre_topc @ sk_A)),
% 0.44/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.63  thf('147', plain,
% 0.44/0.63      (((r2_hidden @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_A))
% 0.44/0.63        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_B) @ sk_A))),
% 0.44/0.63      inference('demod', [status(thm)], ['145', '146'])).
% 0.44/0.63  thf('148', plain,
% 0.44/0.63      (((r2_hidden @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_A)))
% 0.44/0.63         <= (((v1_tsep_1 @ sk_B @ sk_A)))),
% 0.44/0.63      inference('sup-', [status(thm)], ['142', '147'])).
% 0.44/0.63  thf('149', plain,
% 0.44/0.63      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.44/0.63        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.44/0.63      inference('demod', [status(thm)], ['121', '122'])).
% 0.44/0.63  thf('150', plain,
% 0.44/0.63      (![X13 : $i, X14 : $i]:
% 0.44/0.63         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.44/0.63          | ~ (r2_hidden @ X13 @ (u1_pre_topc @ X14))
% 0.44/0.63          | ((u1_pre_topc @ X14) = (k5_tmap_1 @ X14 @ X13))
% 0.44/0.63          | ~ (l1_pre_topc @ X14)
% 0.44/0.63          | ~ (v2_pre_topc @ X14)
% 0.44/0.63          | (v2_struct_0 @ X14))),
% 0.44/0.63      inference('cnf', [status(esa)], [t103_tmap_1])).
% 0.44/0.63  thf('151', plain,
% 0.44/0.63      (((v2_struct_0 @ sk_A)
% 0.44/0.63        | ~ (v2_pre_topc @ sk_A)
% 0.44/0.63        | ~ (l1_pre_topc @ sk_A)
% 0.44/0.63        | ((u1_pre_topc @ sk_A) = (k5_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 0.44/0.63        | ~ (r2_hidden @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_A)))),
% 0.44/0.63      inference('sup-', [status(thm)], ['149', '150'])).
% 0.44/0.63  thf('152', plain, ((v2_pre_topc @ sk_A)),
% 0.44/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.63  thf('153', plain, ((l1_pre_topc @ sk_A)),
% 0.44/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.63  thf('154', plain,
% 0.44/0.63      (((v2_struct_0 @ sk_A)
% 0.44/0.63        | ((u1_pre_topc @ sk_A) = (k5_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 0.44/0.63        | ~ (r2_hidden @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_A)))),
% 0.44/0.63      inference('demod', [status(thm)], ['151', '152', '153'])).
% 0.44/0.63  thf('155', plain, (~ (v2_struct_0 @ sk_A)),
% 0.44/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.63  thf('156', plain,
% 0.44/0.63      ((~ (r2_hidden @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_A))
% 0.44/0.63        | ((u1_pre_topc @ sk_A) = (k5_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B))))),
% 0.44/0.63      inference('clc', [status(thm)], ['154', '155'])).
% 0.44/0.63  thf('157', plain,
% 0.44/0.63      ((((u1_pre_topc @ sk_A) = (k5_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B))))
% 0.44/0.63         <= (((v1_tsep_1 @ sk_B @ sk_A)))),
% 0.44/0.63      inference('sup-', [status(thm)], ['148', '156'])).
% 0.44/0.63  thf('158', plain,
% 0.44/0.63      ((((u1_pre_topc @ sk_A) = (u1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))))
% 0.44/0.63         <= (((v1_tsep_1 @ sk_B @ sk_A)))),
% 0.44/0.63      inference('sup+', [status(thm)], ['133', '157'])).
% 0.44/0.63  thf('159', plain,
% 0.44/0.63      (((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 0.44/0.63      inference('clc', [status(thm)], ['8', '9'])).
% 0.44/0.63  thf('160', plain,
% 0.44/0.63      (![X0 : $i]:
% 0.44/0.63         (~ (v1_pre_topc @ X0)
% 0.44/0.63          | ((X0) = (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.44/0.63          | ~ (l1_pre_topc @ X0))),
% 0.44/0.63      inference('cnf', [status(esa)], [abstractness_v1_pre_topc])).
% 0.44/0.63  thf('161', plain,
% 0.44/0.63      ((((k8_tmap_1 @ sk_A @ sk_B)
% 0.44/0.63          = (g1_pre_topc @ (u1_struct_0 @ sk_A) @ 
% 0.44/0.63             (u1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))))
% 0.44/0.63        | ~ (l1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.44/0.63        | ~ (v1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B)))),
% 0.44/0.63      inference('sup+', [status(thm)], ['159', '160'])).
% 0.44/0.63  thf('162', plain, ((l1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))),
% 0.44/0.63      inference('clc', [status(thm)], ['22', '23'])).
% 0.44/0.63  thf('163', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.44/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.63  thf('164', plain,
% 0.44/0.63      (![X11 : $i, X12 : $i]:
% 0.44/0.63         (~ (l1_pre_topc @ X11)
% 0.44/0.63          | ~ (v2_pre_topc @ X11)
% 0.44/0.63          | (v2_struct_0 @ X11)
% 0.44/0.63          | ~ (m1_pre_topc @ X12 @ X11)
% 0.44/0.63          | (v1_pre_topc @ (k8_tmap_1 @ X11 @ X12)))),
% 0.44/0.63      inference('cnf', [status(esa)], [dt_k8_tmap_1])).
% 0.44/0.63  thf('165', plain,
% 0.44/0.63      (((v1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.44/0.63        | (v2_struct_0 @ sk_A)
% 0.44/0.63        | ~ (v2_pre_topc @ sk_A)
% 0.44/0.63        | ~ (l1_pre_topc @ sk_A))),
% 0.44/0.63      inference('sup-', [status(thm)], ['163', '164'])).
% 0.44/0.63  thf('166', plain, ((v2_pre_topc @ sk_A)),
% 0.44/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.63  thf('167', plain, ((l1_pre_topc @ sk_A)),
% 0.44/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.63  thf('168', plain,
% 0.44/0.63      (((v1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B)) | (v2_struct_0 @ sk_A))),
% 0.44/0.63      inference('demod', [status(thm)], ['165', '166', '167'])).
% 0.44/0.63  thf('169', plain, (~ (v2_struct_0 @ sk_A)),
% 0.44/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.63  thf('170', plain, ((v1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))),
% 0.44/0.63      inference('clc', [status(thm)], ['168', '169'])).
% 0.44/0.63  thf('171', plain,
% 0.44/0.63      (((k8_tmap_1 @ sk_A @ sk_B)
% 0.44/0.63         = (g1_pre_topc @ (u1_struct_0 @ sk_A) @ 
% 0.44/0.63            (u1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))))),
% 0.44/0.63      inference('demod', [status(thm)], ['161', '162', '170'])).
% 0.44/0.63  thf('172', plain,
% 0.44/0.63      ((((k8_tmap_1 @ sk_A @ sk_B)
% 0.44/0.63          = (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))
% 0.44/0.63         <= (((v1_tsep_1 @ sk_B @ sk_A)))),
% 0.44/0.63      inference('sup+', [status(thm)], ['158', '171'])).
% 0.44/0.63  thf('173', plain,
% 0.44/0.63      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.44/0.63          != (k8_tmap_1 @ sk_A @ sk_B)))
% 0.44/0.63         <= (~
% 0.44/0.63             (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.44/0.63                = (k8_tmap_1 @ sk_A @ sk_B))))),
% 0.44/0.63      inference('split', [status(esa)], ['114'])).
% 0.44/0.63  thf('174', plain,
% 0.44/0.63      ((((k8_tmap_1 @ sk_A @ sk_B) != (k8_tmap_1 @ sk_A @ sk_B)))
% 0.44/0.63         <= (~
% 0.44/0.63             (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.44/0.63                = (k8_tmap_1 @ sk_A @ sk_B))) & 
% 0.44/0.63             ((v1_tsep_1 @ sk_B @ sk_A)))),
% 0.44/0.63      inference('sup-', [status(thm)], ['172', '173'])).
% 0.44/0.63  thf('175', plain,
% 0.44/0.63      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.44/0.63          = (k8_tmap_1 @ sk_A @ sk_B))) | 
% 0.44/0.63       ~ ((v1_tsep_1 @ sk_B @ sk_A))),
% 0.44/0.63      inference('simplify', [status(thm)], ['174'])).
% 0.44/0.63  thf('176', plain,
% 0.44/0.63      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.44/0.63          = (k8_tmap_1 @ sk_A @ sk_B))) | 
% 0.44/0.63       ((v1_tsep_1 @ sk_B @ sk_A))),
% 0.44/0.63      inference('split', [status(esa)], ['112'])).
% 0.44/0.63  thf('177', plain,
% 0.44/0.63      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.44/0.63          = (k8_tmap_1 @ sk_A @ sk_B)))),
% 0.44/0.63      inference('sat_resolution*', [status(thm)], ['115', '118', '175', '176'])).
% 0.44/0.63  thf('178', plain,
% 0.44/0.63      (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.44/0.63         = (k8_tmap_1 @ sk_A @ sk_B))),
% 0.44/0.63      inference('simpl_trail', [status(thm)], ['113', '177'])).
% 0.44/0.63  thf('179', plain, ((l1_pre_topc @ sk_A)),
% 0.44/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.63  thf('180', plain, ((v2_pre_topc @ sk_A)),
% 0.44/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.63  thf('181', plain,
% 0.44/0.63      ((((k8_tmap_1 @ sk_A @ sk_A) = (k8_tmap_1 @ sk_A @ sk_B))
% 0.44/0.63        | (v2_struct_0 @ sk_A))),
% 0.44/0.63      inference('demod', [status(thm)], ['111', '178', '179', '180'])).
% 0.44/0.63  thf('182', plain, (~ (v2_struct_0 @ sk_A)),
% 0.44/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.63  thf('183', plain, (((k8_tmap_1 @ sk_A @ sk_A) = (k8_tmap_1 @ sk_A @ sk_B))),
% 0.44/0.63      inference('clc', [status(thm)], ['181', '182'])).
% 0.44/0.63  thf('184', plain,
% 0.44/0.63      (((u1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B)) = (u1_pre_topc @ sk_A))),
% 0.44/0.63      inference('demod', [status(thm)], ['83', '183'])).
% 0.44/0.63  thf('185', plain,
% 0.44/0.63      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.44/0.63        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.44/0.63      inference('demod', [status(thm)], ['121', '122'])).
% 0.44/0.63  thf('186', plain,
% 0.44/0.63      (![X13 : $i, X14 : $i]:
% 0.44/0.63         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.44/0.63          | ((u1_pre_topc @ X14) != (k5_tmap_1 @ X14 @ X13))
% 0.44/0.63          | (r2_hidden @ X13 @ (u1_pre_topc @ X14))
% 0.44/0.63          | ~ (l1_pre_topc @ X14)
% 0.44/0.63          | ~ (v2_pre_topc @ X14)
% 0.44/0.63          | (v2_struct_0 @ X14))),
% 0.44/0.63      inference('cnf', [status(esa)], [t103_tmap_1])).
% 0.44/0.63  thf('187', plain,
% 0.44/0.63      (((v2_struct_0 @ sk_A)
% 0.44/0.63        | ~ (v2_pre_topc @ sk_A)
% 0.44/0.63        | ~ (l1_pre_topc @ sk_A)
% 0.44/0.63        | (r2_hidden @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_A))
% 0.44/0.63        | ((u1_pre_topc @ sk_A) != (k5_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B))))),
% 0.44/0.63      inference('sup-', [status(thm)], ['185', '186'])).
% 0.44/0.63  thf('188', plain, ((v2_pre_topc @ sk_A)),
% 0.44/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.63  thf('189', plain, ((l1_pre_topc @ sk_A)),
% 0.44/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.63  thf('190', plain,
% 0.44/0.63      (((v2_struct_0 @ sk_A)
% 0.44/0.63        | (r2_hidden @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_A))
% 0.44/0.63        | ((u1_pre_topc @ sk_A) != (k5_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B))))),
% 0.44/0.63      inference('demod', [status(thm)], ['187', '188', '189'])).
% 0.44/0.63  thf('191', plain, (~ (v2_struct_0 @ sk_A)),
% 0.44/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.63  thf('192', plain,
% 0.44/0.63      ((((u1_pre_topc @ sk_A) != (k5_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 0.44/0.63        | (r2_hidden @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_A)))),
% 0.44/0.63      inference('clc', [status(thm)], ['190', '191'])).
% 0.44/0.63  thf('193', plain,
% 0.44/0.63      (((u1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.44/0.63         = (k5_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))),
% 0.44/0.63      inference('clc', [status(thm)], ['131', '132'])).
% 0.44/0.63  thf('194', plain,
% 0.44/0.63      ((((u1_pre_topc @ sk_A) != (u1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B)))
% 0.44/0.63        | (r2_hidden @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_A)))),
% 0.44/0.63      inference('demod', [status(thm)], ['192', '193'])).
% 0.44/0.63  thf('195', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.44/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.63  thf('196', plain,
% 0.44/0.63      (![X8 : $i, X9 : $i]:
% 0.44/0.63         (~ (m1_pre_topc @ X8 @ X9)
% 0.44/0.63          | ((sk_C @ X8 @ X9) = (u1_struct_0 @ X8))
% 0.44/0.63          | (v1_tsep_1 @ X8 @ X9)
% 0.44/0.63          | ~ (l1_pre_topc @ X9))),
% 0.44/0.63      inference('cnf', [status(esa)], [d1_tsep_1])).
% 0.44/0.63  thf('197', plain,
% 0.44/0.63      ((~ (l1_pre_topc @ sk_A)
% 0.44/0.63        | (v1_tsep_1 @ sk_B @ sk_A)
% 0.44/0.63        | ((sk_C @ sk_B @ sk_A) = (u1_struct_0 @ sk_B)))),
% 0.44/0.63      inference('sup-', [status(thm)], ['195', '196'])).
% 0.44/0.63  thf('198', plain, ((l1_pre_topc @ sk_A)),
% 0.44/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.63  thf('199', plain,
% 0.44/0.63      (((v1_tsep_1 @ sk_B @ sk_A)
% 0.44/0.63        | ((sk_C @ sk_B @ sk_A) = (u1_struct_0 @ sk_B)))),
% 0.44/0.63      inference('demod', [status(thm)], ['197', '198'])).
% 0.44/0.63  thf('200', plain,
% 0.44/0.63      ((~ (v1_tsep_1 @ sk_B @ sk_A)) <= (~ ((v1_tsep_1 @ sk_B @ sk_A)))),
% 0.44/0.63      inference('split', [status(esa)], ['114'])).
% 0.44/0.63  thf('201', plain,
% 0.44/0.63      ((((sk_C @ sk_B @ sk_A) = (u1_struct_0 @ sk_B)))
% 0.44/0.63         <= (~ ((v1_tsep_1 @ sk_B @ sk_A)))),
% 0.44/0.63      inference('sup-', [status(thm)], ['199', '200'])).
% 0.44/0.63  thf('202', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.44/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.63  thf('203', plain,
% 0.44/0.63      (![X8 : $i, X9 : $i]:
% 0.44/0.63         (~ (m1_pre_topc @ X8 @ X9)
% 0.44/0.63          | (m1_subset_1 @ (sk_C @ X8 @ X9) @ 
% 0.44/0.63             (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.44/0.63          | (v1_tsep_1 @ X8 @ X9)
% 0.44/0.63          | ~ (l1_pre_topc @ X9))),
% 0.44/0.63      inference('cnf', [status(esa)], [d1_tsep_1])).
% 0.44/0.63  thf('204', plain,
% 0.44/0.63      ((~ (l1_pre_topc @ sk_A)
% 0.44/0.63        | (v1_tsep_1 @ sk_B @ sk_A)
% 0.44/0.63        | (m1_subset_1 @ (sk_C @ sk_B @ sk_A) @ 
% 0.44/0.63           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.44/0.63      inference('sup-', [status(thm)], ['202', '203'])).
% 0.44/0.63  thf('205', plain, ((l1_pre_topc @ sk_A)),
% 0.44/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.63  thf('206', plain,
% 0.44/0.63      (((v1_tsep_1 @ sk_B @ sk_A)
% 0.44/0.63        | (m1_subset_1 @ (sk_C @ sk_B @ sk_A) @ 
% 0.44/0.63           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.44/0.63      inference('demod', [status(thm)], ['204', '205'])).
% 0.44/0.63  thf('207', plain,
% 0.44/0.63      (![X2 : $i, X3 : $i]:
% 0.44/0.63         (~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ X3)))
% 0.44/0.63          | ~ (r2_hidden @ X2 @ (u1_pre_topc @ X3))
% 0.44/0.63          | (v3_pre_topc @ X2 @ X3)
% 0.44/0.63          | ~ (l1_pre_topc @ X3))),
% 0.44/0.63      inference('cnf', [status(esa)], [d5_pre_topc])).
% 0.44/0.63  thf('208', plain,
% 0.44/0.63      (((v1_tsep_1 @ sk_B @ sk_A)
% 0.44/0.63        | ~ (l1_pre_topc @ sk_A)
% 0.44/0.63        | (v3_pre_topc @ (sk_C @ sk_B @ sk_A) @ sk_A)
% 0.44/0.63        | ~ (r2_hidden @ (sk_C @ sk_B @ sk_A) @ (u1_pre_topc @ sk_A)))),
% 0.44/0.63      inference('sup-', [status(thm)], ['206', '207'])).
% 0.44/0.63  thf('209', plain, ((l1_pre_topc @ sk_A)),
% 0.44/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.63  thf('210', plain,
% 0.44/0.63      (((v1_tsep_1 @ sk_B @ sk_A)
% 0.44/0.63        | (v3_pre_topc @ (sk_C @ sk_B @ sk_A) @ sk_A)
% 0.44/0.63        | ~ (r2_hidden @ (sk_C @ sk_B @ sk_A) @ (u1_pre_topc @ sk_A)))),
% 0.44/0.63      inference('demod', [status(thm)], ['208', '209'])).
% 0.44/0.63  thf('211', plain,
% 0.44/0.63      (((~ (r2_hidden @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_A))
% 0.44/0.63         | (v3_pre_topc @ (sk_C @ sk_B @ sk_A) @ sk_A)
% 0.44/0.63         | (v1_tsep_1 @ sk_B @ sk_A))) <= (~ ((v1_tsep_1 @ sk_B @ sk_A)))),
% 0.44/0.63      inference('sup-', [status(thm)], ['201', '210'])).
% 0.44/0.63  thf('212', plain,
% 0.44/0.63      ((((sk_C @ sk_B @ sk_A) = (u1_struct_0 @ sk_B)))
% 0.44/0.63         <= (~ ((v1_tsep_1 @ sk_B @ sk_A)))),
% 0.44/0.63      inference('sup-', [status(thm)], ['199', '200'])).
% 0.44/0.63  thf('213', plain,
% 0.44/0.63      (((~ (r2_hidden @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_A))
% 0.44/0.63         | (v3_pre_topc @ (u1_struct_0 @ sk_B) @ sk_A)
% 0.44/0.63         | (v1_tsep_1 @ sk_B @ sk_A))) <= (~ ((v1_tsep_1 @ sk_B @ sk_A)))),
% 0.44/0.63      inference('demod', [status(thm)], ['211', '212'])).
% 0.44/0.63  thf('214', plain,
% 0.44/0.63      ((((sk_C @ sk_B @ sk_A) = (u1_struct_0 @ sk_B)))
% 0.44/0.63         <= (~ ((v1_tsep_1 @ sk_B @ sk_A)))),
% 0.44/0.63      inference('sup-', [status(thm)], ['199', '200'])).
% 0.44/0.63  thf('215', plain,
% 0.44/0.63      (![X8 : $i, X9 : $i]:
% 0.44/0.63         (~ (m1_pre_topc @ X8 @ X9)
% 0.44/0.63          | ~ (v3_pre_topc @ (sk_C @ X8 @ X9) @ X9)
% 0.44/0.63          | (v1_tsep_1 @ X8 @ X9)
% 0.44/0.63          | ~ (l1_pre_topc @ X9))),
% 0.44/0.63      inference('cnf', [status(esa)], [d1_tsep_1])).
% 0.44/0.63  thf('216', plain,
% 0.44/0.63      (((~ (v3_pre_topc @ (u1_struct_0 @ sk_B) @ sk_A)
% 0.44/0.63         | ~ (l1_pre_topc @ sk_A)
% 0.44/0.63         | (v1_tsep_1 @ sk_B @ sk_A)
% 0.44/0.63         | ~ (m1_pre_topc @ sk_B @ sk_A))) <= (~ ((v1_tsep_1 @ sk_B @ sk_A)))),
% 0.44/0.63      inference('sup-', [status(thm)], ['214', '215'])).
% 0.44/0.63  thf('217', plain, ((l1_pre_topc @ sk_A)),
% 0.44/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.63  thf('218', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.44/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.63  thf('219', plain,
% 0.44/0.63      (((~ (v3_pre_topc @ (u1_struct_0 @ sk_B) @ sk_A)
% 0.44/0.63         | (v1_tsep_1 @ sk_B @ sk_A))) <= (~ ((v1_tsep_1 @ sk_B @ sk_A)))),
% 0.44/0.63      inference('demod', [status(thm)], ['216', '217', '218'])).
% 0.44/0.63  thf('220', plain,
% 0.44/0.63      ((~ (v1_tsep_1 @ sk_B @ sk_A)) <= (~ ((v1_tsep_1 @ sk_B @ sk_A)))),
% 0.44/0.63      inference('split', [status(esa)], ['114'])).
% 0.44/0.63  thf('221', plain,
% 0.44/0.63      ((~ (v3_pre_topc @ (u1_struct_0 @ sk_B) @ sk_A))
% 0.44/0.63         <= (~ ((v1_tsep_1 @ sk_B @ sk_A)))),
% 0.44/0.63      inference('clc', [status(thm)], ['219', '220'])).
% 0.44/0.63  thf('222', plain,
% 0.44/0.63      ((((v1_tsep_1 @ sk_B @ sk_A)
% 0.44/0.63         | ~ (r2_hidden @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_A))))
% 0.44/0.63         <= (~ ((v1_tsep_1 @ sk_B @ sk_A)))),
% 0.44/0.63      inference('clc', [status(thm)], ['213', '221'])).
% 0.44/0.63  thf('223', plain,
% 0.44/0.63      ((~ (v1_tsep_1 @ sk_B @ sk_A)) <= (~ ((v1_tsep_1 @ sk_B @ sk_A)))),
% 0.44/0.63      inference('split', [status(esa)], ['114'])).
% 0.44/0.63  thf('224', plain,
% 0.44/0.63      ((~ (r2_hidden @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_A)))
% 0.44/0.63         <= (~ ((v1_tsep_1 @ sk_B @ sk_A)))),
% 0.44/0.63      inference('clc', [status(thm)], ['222', '223'])).
% 0.44/0.63  thf('225', plain, (~ ((v1_tsep_1 @ sk_B @ sk_A))),
% 0.44/0.63      inference('sat_resolution*', [status(thm)], ['115', '118', '175'])).
% 0.44/0.63  thf('226', plain,
% 0.44/0.63      (~ (r2_hidden @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_A))),
% 0.44/0.63      inference('simpl_trail', [status(thm)], ['224', '225'])).
% 0.44/0.63  thf('227', plain,
% 0.44/0.63      (((u1_pre_topc @ sk_A) != (u1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B)))),
% 0.44/0.63      inference('clc', [status(thm)], ['194', '226'])).
% 0.44/0.63  thf('228', plain, ($false),
% 0.44/0.63      inference('simplify_reflect-', [status(thm)], ['184', '227'])).
% 0.44/0.63  
% 0.44/0.63  % SZS output end Refutation
% 0.44/0.63  
% 0.44/0.63  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
