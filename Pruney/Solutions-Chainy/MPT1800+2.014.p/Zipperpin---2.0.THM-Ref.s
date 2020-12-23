%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.iy3BTtht72

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:10:57 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  140 ( 389 expanded)
%              Number of leaves         :   26 ( 119 expanded)
%              Depth                    :   16
%              Number of atoms          : 1260 (6178 expanded)
%              Number of equality atoms :   65 ( 257 expanded)
%              Maximal formula depth    :   13 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(k6_tmap_1_type,type,(
    k6_tmap_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k5_tmap_1_type,type,(
    k5_tmap_1: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(g1_pre_topc_type,type,(
    g1_pre_topc: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k8_tmap_1_type,type,(
    k8_tmap_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(v1_tsep_1_type,type,(
    v1_tsep_1: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

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

thf(t1_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( m1_subset_1 @ ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('6',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( m1_pre_topc @ X13 @ X14 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X13 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( l1_pre_topc @ X14 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('7',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf(d9_tmap_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k6_tmap_1 @ A @ B )
            = ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( k5_tmap_1 @ A @ B ) ) ) ) ) )).

thf('10',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) )
      | ( ( k6_tmap_1 @ X5 @ X4 )
        = ( g1_pre_topc @ ( u1_struct_0 @ X5 ) @ ( k5_tmap_1 @ X5 @ X4 ) ) )
      | ~ ( l1_pre_topc @ X5 )
      | ~ ( v2_pre_topc @ X5 )
      | ( v2_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d9_tmap_1])).

thf('11',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) )
      = ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( k5_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) )
      = ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( k5_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['11','12','13'])).

thf('15',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( k5_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['14','15'])).

thf('17',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['7','8'])).

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
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( v2_struct_0 @ X10 )
      | ~ ( m1_pre_topc @ X10 @ X11 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ( ( u1_pre_topc @ ( k8_tmap_1 @ X11 @ X10 ) )
        = ( k5_tmap_1 @ X11 @ X12 ) )
      | ( X12
       != ( u1_struct_0 @ X10 ) )
      | ~ ( l1_pre_topc @ X11 )
      | ~ ( v2_pre_topc @ X11 )
      | ( v2_struct_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t114_tmap_1])).

thf('19',plain,(
    ! [X10: $i,X11: $i] :
      ( ( v2_struct_0 @ X11 )
      | ~ ( v2_pre_topc @ X11 )
      | ~ ( l1_pre_topc @ X11 )
      | ( ( u1_pre_topc @ ( k8_tmap_1 @ X11 @ X10 ) )
        = ( k5_tmap_1 @ X11 @ ( u1_struct_0 @ X10 ) ) )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X10 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ~ ( m1_pre_topc @ X10 @ X11 )
      | ( v2_struct_0 @ X10 ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,
    ( ( v2_struct_0 @ sk_B )
    | ~ ( m1_pre_topc @ sk_B @ sk_A )
    | ( ( u1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
      = ( k5_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['17','19'])).

thf('21',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( u1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
      = ( k5_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['20','21','22','23'])).

thf('25',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( u1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
      = ( k5_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['24','25'])).

thf('27',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( ( u1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    = ( k5_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['26','27'])).

thf('29',plain,
    ( ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['16','28'])).

thf('30',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    ! [X10: $i,X11: $i] :
      ( ( v2_struct_0 @ X10 )
      | ~ ( m1_pre_topc @ X10 @ X11 )
      | ( ( u1_struct_0 @ ( k8_tmap_1 @ X11 @ X10 ) )
        = ( u1_struct_0 @ X11 ) )
      | ~ ( l1_pre_topc @ X11 )
      | ~ ( v2_pre_topc @ X11 )
      | ( v2_struct_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t114_tmap_1])).

thf('32',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
      = ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
      = ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['32','33','34'])).

thf('36',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['35','36'])).

thf('38',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['37','38'])).

thf(abstractness_v1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( ( v1_pre_topc @ A )
       => ( A
          = ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ) )).

thf('40',plain,(
    ! [X0: $i] :
      ( ~ ( v1_pre_topc @ X0 )
      | ( X0
        = ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(cnf,[status(esa)],[abstractness_v1_pre_topc])).

thf('41',plain,
    ( ( ( k8_tmap_1 @ sk_A @ sk_B )
      = ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) )
    | ~ ( l1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( v1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('42',plain,(
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

thf('43',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( l1_pre_topc @ X6 )
      | ~ ( v2_pre_topc @ X6 )
      | ( v2_struct_0 @ X6 )
      | ~ ( m1_pre_topc @ X7 @ X6 )
      | ( l1_pre_topc @ ( k8_tmap_1 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k8_tmap_1])).

thf('44',plain,
    ( ( l1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ( l1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['44','45','46'])).

thf('48',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    l1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['47','48'])).

thf('50',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( l1_pre_topc @ X6 )
      | ~ ( v2_pre_topc @ X6 )
      | ( v2_struct_0 @ X6 )
      | ~ ( m1_pre_topc @ X7 @ X6 )
      | ( v1_pre_topc @ ( k8_tmap_1 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k8_tmap_1])).

thf('52',plain,
    ( ( v1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( ( v1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['52','53','54'])).

thf('56',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    v1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['55','56'])).

thf('58',plain,
    ( ( k8_tmap_1 @ sk_A @ sk_B )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['41','49','57'])).

thf('59',plain,
    ( ( k8_tmap_1 @ sk_A @ sk_B )
    = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['29','58'])).

thf('60',plain,
    ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,
    ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k8_tmap_1 @ sk_A @ sk_B ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['60'])).

thf(t106_tmap_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v3_pre_topc @ B @ A )
          <=> ( ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) )
              = ( k6_tmap_1 @ A @ B ) ) ) ) ) )).

thf('62',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ( ( g1_pre_topc @ ( u1_struct_0 @ X9 ) @ ( u1_pre_topc @ X9 ) )
       != ( k6_tmap_1 @ X9 @ X8 ) )
      | ( v3_pre_topc @ X8 @ X9 )
      | ~ ( l1_pre_topc @ X9 )
      | ~ ( v2_pre_topc @ X9 )
      | ( v2_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t106_tmap_1])).

thf('63',plain,
    ( ! [X0: $i] :
        ( ( ( k8_tmap_1 @ sk_A @ sk_B )
         != ( k6_tmap_1 @ sk_A @ X0 ) )
        | ( v2_struct_0 @ sk_A )
        | ~ ( v2_pre_topc @ sk_A )
        | ~ ( l1_pre_topc @ sk_A )
        | ( v3_pre_topc @ X0 @ sk_A )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,
    ( ! [X0: $i] :
        ( ( ( k8_tmap_1 @ sk_A @ sk_B )
         != ( k6_tmap_1 @ sk_A @ X0 ) )
        | ( v2_struct_0 @ sk_A )
        | ( v3_pre_topc @ X0 @ sk_A )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['63','64','65'])).

thf('67',plain,
    ( ( ( ( k8_tmap_1 @ sk_A @ sk_B )
       != ( k8_tmap_1 @ sk_A @ sk_B ) )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v3_pre_topc @ ( u1_struct_0 @ sk_B ) @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['59','66'])).

thf('68',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('69',plain,
    ( ( ( ( k8_tmap_1 @ sk_A @ sk_B )
       != ( k8_tmap_1 @ sk_A @ sk_B ) )
      | ( v3_pre_topc @ ( u1_struct_0 @ sk_B ) @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('70',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v3_pre_topc @ ( u1_struct_0 @ sk_B ) @ sk_A ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['69'])).

thf('71',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,
    ( ( v3_pre_topc @ ( u1_struct_0 @ sk_B ) @ sk_A )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['70','71'])).

thf('73',plain,(
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

thf('74',plain,(
    ! [X1: $i,X2: $i] :
      ( ~ ( m1_pre_topc @ X1 @ X2 )
      | ( ( sk_C @ X1 @ X2 )
        = ( u1_struct_0 @ X1 ) )
      | ( v1_tsep_1 @ X1 @ X2 )
      | ~ ( l1_pre_topc @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_tsep_1])).

thf('75',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v1_tsep_1 @ sk_B @ sk_A )
    | ( ( sk_C @ sk_B @ sk_A )
      = ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,
    ( ( v1_tsep_1 @ sk_B @ sk_A )
    | ( ( sk_C @ sk_B @ sk_A )
      = ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['75','76'])).

thf('78',plain,
    ( ~ ( v1_tsep_1 @ sk_B @ sk_A )
   <= ~ ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('79',plain,
    ( ( ( sk_C @ sk_B @ sk_A )
      = ( u1_struct_0 @ sk_B ) )
   <= ~ ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X1: $i,X2: $i] :
      ( ~ ( m1_pre_topc @ X1 @ X2 )
      | ~ ( v3_pre_topc @ ( sk_C @ X1 @ X2 ) @ X2 )
      | ( v1_tsep_1 @ X1 @ X2 )
      | ~ ( l1_pre_topc @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_tsep_1])).

thf('81',plain,
    ( ( ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_B ) @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v1_tsep_1 @ sk_B @ sk_A )
      | ~ ( m1_pre_topc @ sk_B @ sk_A ) )
   <= ~ ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,
    ( ( ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_B ) @ sk_A )
      | ( v1_tsep_1 @ sk_B @ sk_A ) )
   <= ~ ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['81','82','83'])).

thf('85',plain,
    ( ~ ( v1_tsep_1 @ sk_B @ sk_A )
   <= ~ ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('86',plain,
    ( ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_B ) @ sk_A )
   <= ~ ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['84','85'])).

thf('87',plain,
    ( ( v1_tsep_1 @ sk_B @ sk_A )
    | ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
     != ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['72','86'])).

thf('88',plain,
    ( ( v1_tsep_1 @ sk_B @ sk_A )
    | ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['60'])).

thf('89',plain,
    ( ( v1_tsep_1 @ sk_B @ sk_A )
   <= ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['60'])).

thf('90',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('91',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_pre_topc @ X1 @ X2 )
      | ~ ( v1_tsep_1 @ X1 @ X2 )
      | ( X3
       != ( u1_struct_0 @ X1 ) )
      | ( v3_pre_topc @ X3 @ X2 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X2 ) ) )
      | ~ ( l1_pre_topc @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_tsep_1])).

thf('92',plain,(
    ! [X1: $i,X2: $i] :
      ( ~ ( l1_pre_topc @ X2 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X2 ) ) )
      | ( v3_pre_topc @ ( u1_struct_0 @ X1 ) @ X2 )
      | ~ ( v1_tsep_1 @ X1 @ X2 )
      | ~ ( m1_pre_topc @ X1 @ X2 ) ) ),
    inference(simplify,[status(thm)],['91'])).

thf('93',plain,
    ( ~ ( m1_pre_topc @ sk_B @ sk_A )
    | ~ ( v1_tsep_1 @ sk_B @ sk_A )
    | ( v3_pre_topc @ ( u1_struct_0 @ sk_B ) @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['90','92'])).

thf('94',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,
    ( ~ ( v1_tsep_1 @ sk_B @ sk_A )
    | ( v3_pre_topc @ ( u1_struct_0 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['93','94','95'])).

thf('97',plain,
    ( ( v3_pre_topc @ ( u1_struct_0 @ sk_B ) @ sk_A )
   <= ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['89','96'])).

thf('98',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('99',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ~ ( v3_pre_topc @ X8 @ X9 )
      | ( ( g1_pre_topc @ ( u1_struct_0 @ X9 ) @ ( u1_pre_topc @ X9 ) )
        = ( k6_tmap_1 @ X9 @ X8 ) )
      | ~ ( l1_pre_topc @ X9 )
      | ~ ( v2_pre_topc @ X9 )
      | ( v2_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t106_tmap_1])).

thf('100',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
    | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
    | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['100','101','102'])).

thf('104',plain,
    ( ( k8_tmap_1 @ sk_A @ sk_B )
    = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['29','58'])).

thf('105',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['103','104'])).

thf('106',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,
    ( ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_B ) @ sk_A )
    | ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['105','106'])).

thf('108',plain,
    ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k8_tmap_1 @ sk_A @ sk_B ) )
   <= ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['97','107'])).

thf('109',plain,
    ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
     != ( k8_tmap_1 @ sk_A @ sk_B ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
     != ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('110',plain,
    ( ( ( k8_tmap_1 @ sk_A @ sk_B )
     != ( k8_tmap_1 @ sk_A @ sk_B ) )
   <= ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
       != ( k8_tmap_1 @ sk_A @ sk_B ) )
      & ( v1_tsep_1 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['108','109'])).

thf('111',plain,
    ( ~ ( v1_tsep_1 @ sk_B @ sk_A )
    | ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['110'])).

thf('112',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','4','87','88','111'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.iy3BTtht72
% 0.12/0.34  % Computer   : n005.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 17:57:33 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.20/0.35  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 0.20/0.52  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.52  % Solved by: fo/fo7.sh
% 0.20/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.52  % done 78 iterations in 0.041s
% 0.20/0.52  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.52  % SZS output start Refutation
% 0.20/0.52  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.52  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.20/0.52  thf(k6_tmap_1_type, type, k6_tmap_1: $i > $i > $i).
% 0.20/0.52  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.20/0.52  thf(k5_tmap_1_type, type, k5_tmap_1: $i > $i > $i).
% 0.20/0.52  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.20/0.52  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 0.20/0.52  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.52  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.20/0.52  thf(g1_pre_topc_type, type, g1_pre_topc: $i > $i > $i).
% 0.20/0.52  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.52  thf(k8_tmap_1_type, type, k8_tmap_1: $i > $i > $i).
% 0.20/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.52  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 0.20/0.52  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.20/0.52  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.20/0.52  thf(v1_tsep_1_type, type, v1_tsep_1: $i > $i > $o).
% 0.20/0.52  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.52  thf(t116_tmap_1, conjecture,
% 0.20/0.52    (![A:$i]:
% 0.20/0.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.52       ( ![B:$i]:
% 0.20/0.52         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.20/0.52           ( ( ( v1_tsep_1 @ B @ A ) & ( m1_pre_topc @ B @ A ) ) <=>
% 0.20/0.52             ( ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) =
% 0.20/0.52               ( k8_tmap_1 @ A @ B ) ) ) ) ) ))).
% 0.20/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.52    (~( ![A:$i]:
% 0.20/0.52        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.20/0.52            ( l1_pre_topc @ A ) ) =>
% 0.20/0.52          ( ![B:$i]:
% 0.20/0.52            ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.20/0.52              ( ( ( v1_tsep_1 @ B @ A ) & ( m1_pre_topc @ B @ A ) ) <=>
% 0.20/0.52                ( ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) =
% 0.20/0.52                  ( k8_tmap_1 @ A @ B ) ) ) ) ) ) )),
% 0.20/0.52    inference('cnf.neg', [status(esa)], [t116_tmap_1])).
% 0.20/0.52  thf('0', plain,
% 0.20/0.52      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.20/0.52          != (k8_tmap_1 @ sk_A @ sk_B))
% 0.20/0.52        | ~ (m1_pre_topc @ sk_B @ sk_A)
% 0.20/0.52        | ~ (v1_tsep_1 @ sk_B @ sk_A))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('1', plain,
% 0.20/0.52      (~ ((v1_tsep_1 @ sk_B @ sk_A)) | 
% 0.20/0.52       ~
% 0.20/0.52       (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.20/0.52          = (k8_tmap_1 @ sk_A @ sk_B))) | 
% 0.20/0.52       ~ ((m1_pre_topc @ sk_B @ sk_A))),
% 0.20/0.52      inference('split', [status(esa)], ['0'])).
% 0.20/0.52  thf('2', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('3', plain,
% 0.20/0.52      ((~ (m1_pre_topc @ sk_B @ sk_A)) <= (~ ((m1_pre_topc @ sk_B @ sk_A)))),
% 0.20/0.52      inference('split', [status(esa)], ['0'])).
% 0.20/0.52  thf('4', plain, (((m1_pre_topc @ sk_B @ sk_A))),
% 0.20/0.52      inference('sup-', [status(thm)], ['2', '3'])).
% 0.20/0.52  thf('5', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf(t1_tsep_1, axiom,
% 0.20/0.52    (![A:$i]:
% 0.20/0.52     ( ( l1_pre_topc @ A ) =>
% 0.20/0.52       ( ![B:$i]:
% 0.20/0.52         ( ( m1_pre_topc @ B @ A ) =>
% 0.20/0.52           ( m1_subset_1 @
% 0.20/0.52             ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.20/0.52  thf('6', plain,
% 0.20/0.52      (![X13 : $i, X14 : $i]:
% 0.20/0.52         (~ (m1_pre_topc @ X13 @ X14)
% 0.20/0.52          | (m1_subset_1 @ (u1_struct_0 @ X13) @ 
% 0.20/0.52             (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.20/0.52          | ~ (l1_pre_topc @ X14))),
% 0.20/0.52      inference('cnf', [status(esa)], [t1_tsep_1])).
% 0.20/0.52  thf('7', plain,
% 0.20/0.52      ((~ (l1_pre_topc @ sk_A)
% 0.20/0.52        | (m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.52           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.52      inference('sup-', [status(thm)], ['5', '6'])).
% 0.20/0.52  thf('8', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('9', plain,
% 0.20/0.52      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.52        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.52      inference('demod', [status(thm)], ['7', '8'])).
% 0.20/0.52  thf(d9_tmap_1, axiom,
% 0.20/0.52    (![A:$i]:
% 0.20/0.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.52       ( ![B:$i]:
% 0.20/0.52         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.52           ( ( k6_tmap_1 @ A @ B ) =
% 0.20/0.52             ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( k5_tmap_1 @ A @ B ) ) ) ) ) ))).
% 0.20/0.52  thf('10', plain,
% 0.20/0.52      (![X4 : $i, X5 : $i]:
% 0.20/0.52         (~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (u1_struct_0 @ X5)))
% 0.20/0.52          | ((k6_tmap_1 @ X5 @ X4)
% 0.20/0.52              = (g1_pre_topc @ (u1_struct_0 @ X5) @ (k5_tmap_1 @ X5 @ X4)))
% 0.20/0.52          | ~ (l1_pre_topc @ X5)
% 0.20/0.52          | ~ (v2_pre_topc @ X5)
% 0.20/0.52          | (v2_struct_0 @ X5))),
% 0.20/0.52      inference('cnf', [status(esa)], [d9_tmap_1])).
% 0.20/0.52  thf('11', plain,
% 0.20/0.52      (((v2_struct_0 @ sk_A)
% 0.20/0.52        | ~ (v2_pre_topc @ sk_A)
% 0.20/0.52        | ~ (l1_pre_topc @ sk_A)
% 0.20/0.52        | ((k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B))
% 0.20/0.52            = (g1_pre_topc @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.52               (k5_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))))),
% 0.20/0.52      inference('sup-', [status(thm)], ['9', '10'])).
% 0.20/0.52  thf('12', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('13', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('14', plain,
% 0.20/0.52      (((v2_struct_0 @ sk_A)
% 0.20/0.52        | ((k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B))
% 0.20/0.52            = (g1_pre_topc @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.52               (k5_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))))),
% 0.20/0.52      inference('demod', [status(thm)], ['11', '12', '13'])).
% 0.20/0.52  thf('15', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('16', plain,
% 0.20/0.52      (((k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B))
% 0.20/0.52         = (g1_pre_topc @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.52            (k5_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B))))),
% 0.20/0.52      inference('clc', [status(thm)], ['14', '15'])).
% 0.20/0.52  thf('17', plain,
% 0.20/0.52      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.52        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.52      inference('demod', [status(thm)], ['7', '8'])).
% 0.20/0.52  thf(t114_tmap_1, axiom,
% 0.20/0.52    (![A:$i]:
% 0.20/0.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.52       ( ![B:$i]:
% 0.20/0.52         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.20/0.52           ( ( ( u1_struct_0 @ ( k8_tmap_1 @ A @ B ) ) = ( u1_struct_0 @ A ) ) & 
% 0.20/0.52             ( ![C:$i]:
% 0.20/0.52               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.52                 ( ( ( C ) = ( u1_struct_0 @ B ) ) =>
% 0.20/0.52                   ( ( u1_pre_topc @ ( k8_tmap_1 @ A @ B ) ) =
% 0.20/0.52                     ( k5_tmap_1 @ A @ C ) ) ) ) ) ) ) ) ))).
% 0.20/0.52  thf('18', plain,
% 0.20/0.52      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.20/0.52         ((v2_struct_0 @ X10)
% 0.20/0.52          | ~ (m1_pre_topc @ X10 @ X11)
% 0.20/0.52          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.20/0.52          | ((u1_pre_topc @ (k8_tmap_1 @ X11 @ X10)) = (k5_tmap_1 @ X11 @ X12))
% 0.20/0.52          | ((X12) != (u1_struct_0 @ X10))
% 0.20/0.52          | ~ (l1_pre_topc @ X11)
% 0.20/0.52          | ~ (v2_pre_topc @ X11)
% 0.20/0.52          | (v2_struct_0 @ X11))),
% 0.20/0.52      inference('cnf', [status(esa)], [t114_tmap_1])).
% 0.20/0.52  thf('19', plain,
% 0.20/0.52      (![X10 : $i, X11 : $i]:
% 0.20/0.52         ((v2_struct_0 @ X11)
% 0.20/0.52          | ~ (v2_pre_topc @ X11)
% 0.20/0.52          | ~ (l1_pre_topc @ X11)
% 0.20/0.52          | ((u1_pre_topc @ (k8_tmap_1 @ X11 @ X10))
% 0.20/0.52              = (k5_tmap_1 @ X11 @ (u1_struct_0 @ X10)))
% 0.20/0.52          | ~ (m1_subset_1 @ (u1_struct_0 @ X10) @ 
% 0.20/0.52               (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.20/0.52          | ~ (m1_pre_topc @ X10 @ X11)
% 0.20/0.52          | (v2_struct_0 @ X10))),
% 0.20/0.52      inference('simplify', [status(thm)], ['18'])).
% 0.20/0.52  thf('20', plain,
% 0.20/0.52      (((v2_struct_0 @ sk_B)
% 0.20/0.52        | ~ (m1_pre_topc @ sk_B @ sk_A)
% 0.20/0.52        | ((u1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.20/0.52            = (k5_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 0.20/0.52        | ~ (l1_pre_topc @ sk_A)
% 0.20/0.52        | ~ (v2_pre_topc @ sk_A)
% 0.20/0.52        | (v2_struct_0 @ sk_A))),
% 0.20/0.52      inference('sup-', [status(thm)], ['17', '19'])).
% 0.20/0.52  thf('21', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('22', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('23', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('24', plain,
% 0.20/0.52      (((v2_struct_0 @ sk_B)
% 0.20/0.52        | ((u1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.20/0.52            = (k5_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 0.20/0.52        | (v2_struct_0 @ sk_A))),
% 0.20/0.52      inference('demod', [status(thm)], ['20', '21', '22', '23'])).
% 0.20/0.52  thf('25', plain, (~ (v2_struct_0 @ sk_B)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('26', plain,
% 0.20/0.52      (((v2_struct_0 @ sk_A)
% 0.20/0.52        | ((u1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.20/0.52            = (k5_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B))))),
% 0.20/0.52      inference('clc', [status(thm)], ['24', '25'])).
% 0.20/0.52  thf('27', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('28', plain,
% 0.20/0.52      (((u1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.20/0.52         = (k5_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))),
% 0.20/0.52      inference('clc', [status(thm)], ['26', '27'])).
% 0.20/0.52  thf('29', plain,
% 0.20/0.52      (((k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B))
% 0.20/0.52         = (g1_pre_topc @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.52            (u1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))))),
% 0.20/0.52      inference('demod', [status(thm)], ['16', '28'])).
% 0.20/0.52  thf('30', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('31', plain,
% 0.20/0.52      (![X10 : $i, X11 : $i]:
% 0.20/0.52         ((v2_struct_0 @ X10)
% 0.20/0.52          | ~ (m1_pre_topc @ X10 @ X11)
% 0.20/0.52          | ((u1_struct_0 @ (k8_tmap_1 @ X11 @ X10)) = (u1_struct_0 @ X11))
% 0.20/0.52          | ~ (l1_pre_topc @ X11)
% 0.20/0.52          | ~ (v2_pre_topc @ X11)
% 0.20/0.52          | (v2_struct_0 @ X11))),
% 0.20/0.52      inference('cnf', [status(esa)], [t114_tmap_1])).
% 0.20/0.52  thf('32', plain,
% 0.20/0.52      (((v2_struct_0 @ sk_A)
% 0.20/0.52        | ~ (v2_pre_topc @ sk_A)
% 0.20/0.52        | ~ (l1_pre_topc @ sk_A)
% 0.20/0.52        | ((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))
% 0.20/0.52        | (v2_struct_0 @ sk_B))),
% 0.20/0.52      inference('sup-', [status(thm)], ['30', '31'])).
% 0.20/0.52  thf('33', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('34', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('35', plain,
% 0.20/0.52      (((v2_struct_0 @ sk_A)
% 0.20/0.52        | ((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))
% 0.20/0.52        | (v2_struct_0 @ sk_B))),
% 0.20/0.52      inference('demod', [status(thm)], ['32', '33', '34'])).
% 0.20/0.52  thf('36', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('37', plain,
% 0.20/0.52      (((v2_struct_0 @ sk_B)
% 0.20/0.52        | ((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A)))),
% 0.20/0.52      inference('clc', [status(thm)], ['35', '36'])).
% 0.20/0.52  thf('38', plain, (~ (v2_struct_0 @ sk_B)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('39', plain,
% 0.20/0.52      (((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 0.20/0.52      inference('clc', [status(thm)], ['37', '38'])).
% 0.20/0.52  thf(abstractness_v1_pre_topc, axiom,
% 0.20/0.52    (![A:$i]:
% 0.20/0.52     ( ( l1_pre_topc @ A ) =>
% 0.20/0.52       ( ( v1_pre_topc @ A ) =>
% 0.20/0.52         ( ( A ) = ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ))).
% 0.20/0.52  thf('40', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         (~ (v1_pre_topc @ X0)
% 0.20/0.52          | ((X0) = (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.20/0.52          | ~ (l1_pre_topc @ X0))),
% 0.20/0.52      inference('cnf', [status(esa)], [abstractness_v1_pre_topc])).
% 0.20/0.52  thf('41', plain,
% 0.20/0.52      ((((k8_tmap_1 @ sk_A @ sk_B)
% 0.20/0.52          = (g1_pre_topc @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.52             (u1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))))
% 0.20/0.52        | ~ (l1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.20/0.52        | ~ (v1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B)))),
% 0.20/0.52      inference('sup+', [status(thm)], ['39', '40'])).
% 0.20/0.52  thf('42', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf(dt_k8_tmap_1, axiom,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.20/0.52         ( l1_pre_topc @ A ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.20/0.52       ( ( v1_pre_topc @ ( k8_tmap_1 @ A @ B ) ) & 
% 0.20/0.52         ( v2_pre_topc @ ( k8_tmap_1 @ A @ B ) ) & 
% 0.20/0.52         ( l1_pre_topc @ ( k8_tmap_1 @ A @ B ) ) ) ))).
% 0.20/0.52  thf('43', plain,
% 0.20/0.52      (![X6 : $i, X7 : $i]:
% 0.20/0.52         (~ (l1_pre_topc @ X6)
% 0.20/0.52          | ~ (v2_pre_topc @ X6)
% 0.20/0.52          | (v2_struct_0 @ X6)
% 0.20/0.52          | ~ (m1_pre_topc @ X7 @ X6)
% 0.20/0.52          | (l1_pre_topc @ (k8_tmap_1 @ X6 @ X7)))),
% 0.20/0.52      inference('cnf', [status(esa)], [dt_k8_tmap_1])).
% 0.20/0.52  thf('44', plain,
% 0.20/0.52      (((l1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.20/0.52        | (v2_struct_0 @ sk_A)
% 0.20/0.52        | ~ (v2_pre_topc @ sk_A)
% 0.20/0.52        | ~ (l1_pre_topc @ sk_A))),
% 0.20/0.52      inference('sup-', [status(thm)], ['42', '43'])).
% 0.20/0.52  thf('45', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('46', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('47', plain,
% 0.20/0.52      (((l1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B)) | (v2_struct_0 @ sk_A))),
% 0.20/0.52      inference('demod', [status(thm)], ['44', '45', '46'])).
% 0.20/0.52  thf('48', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('49', plain, ((l1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))),
% 0.20/0.52      inference('clc', [status(thm)], ['47', '48'])).
% 0.20/0.52  thf('50', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('51', plain,
% 0.20/0.52      (![X6 : $i, X7 : $i]:
% 0.20/0.52         (~ (l1_pre_topc @ X6)
% 0.20/0.52          | ~ (v2_pre_topc @ X6)
% 0.20/0.52          | (v2_struct_0 @ X6)
% 0.20/0.52          | ~ (m1_pre_topc @ X7 @ X6)
% 0.20/0.52          | (v1_pre_topc @ (k8_tmap_1 @ X6 @ X7)))),
% 0.20/0.52      inference('cnf', [status(esa)], [dt_k8_tmap_1])).
% 0.20/0.52  thf('52', plain,
% 0.20/0.52      (((v1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.20/0.52        | (v2_struct_0 @ sk_A)
% 0.20/0.52        | ~ (v2_pre_topc @ sk_A)
% 0.20/0.52        | ~ (l1_pre_topc @ sk_A))),
% 0.20/0.52      inference('sup-', [status(thm)], ['50', '51'])).
% 0.20/0.52  thf('53', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('54', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('55', plain,
% 0.20/0.52      (((v1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B)) | (v2_struct_0 @ sk_A))),
% 0.20/0.52      inference('demod', [status(thm)], ['52', '53', '54'])).
% 0.20/0.52  thf('56', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('57', plain, ((v1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))),
% 0.20/0.52      inference('clc', [status(thm)], ['55', '56'])).
% 0.20/0.52  thf('58', plain,
% 0.20/0.52      (((k8_tmap_1 @ sk_A @ sk_B)
% 0.20/0.52         = (g1_pre_topc @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.52            (u1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))))),
% 0.20/0.52      inference('demod', [status(thm)], ['41', '49', '57'])).
% 0.20/0.52  thf('59', plain,
% 0.20/0.52      (((k8_tmap_1 @ sk_A @ sk_B) = (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))),
% 0.20/0.52      inference('sup+', [status(thm)], ['29', '58'])).
% 0.20/0.52  thf('60', plain,
% 0.20/0.52      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.20/0.52          = (k8_tmap_1 @ sk_A @ sk_B))
% 0.20/0.52        | (v1_tsep_1 @ sk_B @ sk_A))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('61', plain,
% 0.20/0.52      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.20/0.52          = (k8_tmap_1 @ sk_A @ sk_B)))
% 0.20/0.52         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.20/0.52                = (k8_tmap_1 @ sk_A @ sk_B))))),
% 0.20/0.52      inference('split', [status(esa)], ['60'])).
% 0.20/0.52  thf(t106_tmap_1, axiom,
% 0.20/0.52    (![A:$i]:
% 0.20/0.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.52       ( ![B:$i]:
% 0.20/0.52         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.52           ( ( v3_pre_topc @ B @ A ) <=>
% 0.20/0.52             ( ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) =
% 0.20/0.52               ( k6_tmap_1 @ A @ B ) ) ) ) ) ))).
% 0.20/0.52  thf('62', plain,
% 0.20/0.52      (![X8 : $i, X9 : $i]:
% 0.20/0.52         (~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.20/0.52          | ((g1_pre_topc @ (u1_struct_0 @ X9) @ (u1_pre_topc @ X9))
% 0.20/0.52              != (k6_tmap_1 @ X9 @ X8))
% 0.20/0.52          | (v3_pre_topc @ X8 @ X9)
% 0.20/0.52          | ~ (l1_pre_topc @ X9)
% 0.20/0.52          | ~ (v2_pre_topc @ X9)
% 0.20/0.52          | (v2_struct_0 @ X9))),
% 0.20/0.52      inference('cnf', [status(esa)], [t106_tmap_1])).
% 0.20/0.52  thf('63', plain,
% 0.20/0.52      ((![X0 : $i]:
% 0.20/0.52          (((k8_tmap_1 @ sk_A @ sk_B) != (k6_tmap_1 @ sk_A @ X0))
% 0.20/0.52           | (v2_struct_0 @ sk_A)
% 0.20/0.52           | ~ (v2_pre_topc @ sk_A)
% 0.20/0.52           | ~ (l1_pre_topc @ sk_A)
% 0.20/0.52           | (v3_pre_topc @ X0 @ sk_A)
% 0.20/0.52           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))
% 0.20/0.52         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.20/0.52                = (k8_tmap_1 @ sk_A @ sk_B))))),
% 0.20/0.52      inference('sup-', [status(thm)], ['61', '62'])).
% 0.20/0.52  thf('64', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('65', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('66', plain,
% 0.20/0.52      ((![X0 : $i]:
% 0.20/0.52          (((k8_tmap_1 @ sk_A @ sk_B) != (k6_tmap_1 @ sk_A @ X0))
% 0.20/0.52           | (v2_struct_0 @ sk_A)
% 0.20/0.52           | (v3_pre_topc @ X0 @ sk_A)
% 0.20/0.52           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))
% 0.20/0.52         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.20/0.52                = (k8_tmap_1 @ sk_A @ sk_B))))),
% 0.20/0.52      inference('demod', [status(thm)], ['63', '64', '65'])).
% 0.20/0.52  thf('67', plain,
% 0.20/0.52      (((((k8_tmap_1 @ sk_A @ sk_B) != (k8_tmap_1 @ sk_A @ sk_B))
% 0.20/0.52         | ~ (m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.52              (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.52         | (v3_pre_topc @ (u1_struct_0 @ sk_B) @ sk_A)
% 0.20/0.52         | (v2_struct_0 @ sk_A)))
% 0.20/0.52         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.20/0.52                = (k8_tmap_1 @ sk_A @ sk_B))))),
% 0.20/0.52      inference('sup-', [status(thm)], ['59', '66'])).
% 0.20/0.52  thf('68', plain,
% 0.20/0.52      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.52        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.52      inference('demod', [status(thm)], ['7', '8'])).
% 0.20/0.52  thf('69', plain,
% 0.20/0.52      (((((k8_tmap_1 @ sk_A @ sk_B) != (k8_tmap_1 @ sk_A @ sk_B))
% 0.20/0.52         | (v3_pre_topc @ (u1_struct_0 @ sk_B) @ sk_A)
% 0.20/0.52         | (v2_struct_0 @ sk_A)))
% 0.20/0.52         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.20/0.52                = (k8_tmap_1 @ sk_A @ sk_B))))),
% 0.20/0.52      inference('demod', [status(thm)], ['67', '68'])).
% 0.20/0.52  thf('70', plain,
% 0.20/0.52      ((((v2_struct_0 @ sk_A) | (v3_pre_topc @ (u1_struct_0 @ sk_B) @ sk_A)))
% 0.20/0.52         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.20/0.52                = (k8_tmap_1 @ sk_A @ sk_B))))),
% 0.20/0.52      inference('simplify', [status(thm)], ['69'])).
% 0.20/0.52  thf('71', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('72', plain,
% 0.20/0.52      (((v3_pre_topc @ (u1_struct_0 @ sk_B) @ sk_A))
% 0.20/0.52         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.20/0.52                = (k8_tmap_1 @ sk_A @ sk_B))))),
% 0.20/0.52      inference('clc', [status(thm)], ['70', '71'])).
% 0.20/0.52  thf('73', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf(d1_tsep_1, axiom,
% 0.20/0.52    (![A:$i]:
% 0.20/0.52     ( ( l1_pre_topc @ A ) =>
% 0.20/0.52       ( ![B:$i]:
% 0.20/0.52         ( ( m1_pre_topc @ B @ A ) =>
% 0.20/0.52           ( ( v1_tsep_1 @ B @ A ) <=>
% 0.20/0.52             ( ![C:$i]:
% 0.20/0.52               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.52                 ( ( ( C ) = ( u1_struct_0 @ B ) ) => ( v3_pre_topc @ C @ A ) ) ) ) ) ) ) ))).
% 0.20/0.52  thf('74', plain,
% 0.20/0.52      (![X1 : $i, X2 : $i]:
% 0.20/0.52         (~ (m1_pre_topc @ X1 @ X2)
% 0.20/0.52          | ((sk_C @ X1 @ X2) = (u1_struct_0 @ X1))
% 0.20/0.52          | (v1_tsep_1 @ X1 @ X2)
% 0.20/0.52          | ~ (l1_pre_topc @ X2))),
% 0.20/0.52      inference('cnf', [status(esa)], [d1_tsep_1])).
% 0.20/0.52  thf('75', plain,
% 0.20/0.52      ((~ (l1_pre_topc @ sk_A)
% 0.20/0.52        | (v1_tsep_1 @ sk_B @ sk_A)
% 0.20/0.52        | ((sk_C @ sk_B @ sk_A) = (u1_struct_0 @ sk_B)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['73', '74'])).
% 0.20/0.52  thf('76', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('77', plain,
% 0.20/0.52      (((v1_tsep_1 @ sk_B @ sk_A)
% 0.20/0.52        | ((sk_C @ sk_B @ sk_A) = (u1_struct_0 @ sk_B)))),
% 0.20/0.52      inference('demod', [status(thm)], ['75', '76'])).
% 0.20/0.52  thf('78', plain,
% 0.20/0.52      ((~ (v1_tsep_1 @ sk_B @ sk_A)) <= (~ ((v1_tsep_1 @ sk_B @ sk_A)))),
% 0.20/0.52      inference('split', [status(esa)], ['0'])).
% 0.20/0.52  thf('79', plain,
% 0.20/0.52      ((((sk_C @ sk_B @ sk_A) = (u1_struct_0 @ sk_B)))
% 0.20/0.52         <= (~ ((v1_tsep_1 @ sk_B @ sk_A)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['77', '78'])).
% 0.20/0.52  thf('80', plain,
% 0.20/0.52      (![X1 : $i, X2 : $i]:
% 0.20/0.52         (~ (m1_pre_topc @ X1 @ X2)
% 0.20/0.52          | ~ (v3_pre_topc @ (sk_C @ X1 @ X2) @ X2)
% 0.20/0.52          | (v1_tsep_1 @ X1 @ X2)
% 0.20/0.52          | ~ (l1_pre_topc @ X2))),
% 0.20/0.52      inference('cnf', [status(esa)], [d1_tsep_1])).
% 0.20/0.52  thf('81', plain,
% 0.20/0.52      (((~ (v3_pre_topc @ (u1_struct_0 @ sk_B) @ sk_A)
% 0.20/0.52         | ~ (l1_pre_topc @ sk_A)
% 0.20/0.52         | (v1_tsep_1 @ sk_B @ sk_A)
% 0.20/0.52         | ~ (m1_pre_topc @ sk_B @ sk_A))) <= (~ ((v1_tsep_1 @ sk_B @ sk_A)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['79', '80'])).
% 0.20/0.52  thf('82', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('83', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('84', plain,
% 0.20/0.52      (((~ (v3_pre_topc @ (u1_struct_0 @ sk_B) @ sk_A)
% 0.20/0.52         | (v1_tsep_1 @ sk_B @ sk_A))) <= (~ ((v1_tsep_1 @ sk_B @ sk_A)))),
% 0.20/0.52      inference('demod', [status(thm)], ['81', '82', '83'])).
% 0.20/0.52  thf('85', plain,
% 0.20/0.52      ((~ (v1_tsep_1 @ sk_B @ sk_A)) <= (~ ((v1_tsep_1 @ sk_B @ sk_A)))),
% 0.20/0.52      inference('split', [status(esa)], ['0'])).
% 0.20/0.52  thf('86', plain,
% 0.20/0.52      ((~ (v3_pre_topc @ (u1_struct_0 @ sk_B) @ sk_A))
% 0.20/0.52         <= (~ ((v1_tsep_1 @ sk_B @ sk_A)))),
% 0.20/0.52      inference('clc', [status(thm)], ['84', '85'])).
% 0.20/0.52  thf('87', plain,
% 0.20/0.52      (((v1_tsep_1 @ sk_B @ sk_A)) | 
% 0.20/0.52       ~
% 0.20/0.52       (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.20/0.52          = (k8_tmap_1 @ sk_A @ sk_B)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['72', '86'])).
% 0.20/0.52  thf('88', plain,
% 0.20/0.52      (((v1_tsep_1 @ sk_B @ sk_A)) | 
% 0.20/0.52       (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.20/0.52          = (k8_tmap_1 @ sk_A @ sk_B)))),
% 0.20/0.52      inference('split', [status(esa)], ['60'])).
% 0.20/0.52  thf('89', plain,
% 0.20/0.52      (((v1_tsep_1 @ sk_B @ sk_A)) <= (((v1_tsep_1 @ sk_B @ sk_A)))),
% 0.20/0.52      inference('split', [status(esa)], ['60'])).
% 0.20/0.52  thf('90', plain,
% 0.20/0.52      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.52        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.52      inference('demod', [status(thm)], ['7', '8'])).
% 0.20/0.52  thf('91', plain,
% 0.20/0.52      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.52         (~ (m1_pre_topc @ X1 @ X2)
% 0.20/0.52          | ~ (v1_tsep_1 @ X1 @ X2)
% 0.20/0.52          | ((X3) != (u1_struct_0 @ X1))
% 0.20/0.52          | (v3_pre_topc @ X3 @ X2)
% 0.20/0.52          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (u1_struct_0 @ X2)))
% 0.20/0.52          | ~ (l1_pre_topc @ X2))),
% 0.20/0.52      inference('cnf', [status(esa)], [d1_tsep_1])).
% 0.20/0.52  thf('92', plain,
% 0.20/0.52      (![X1 : $i, X2 : $i]:
% 0.20/0.52         (~ (l1_pre_topc @ X2)
% 0.20/0.52          | ~ (m1_subset_1 @ (u1_struct_0 @ X1) @ 
% 0.20/0.52               (k1_zfmisc_1 @ (u1_struct_0 @ X2)))
% 0.20/0.52          | (v3_pre_topc @ (u1_struct_0 @ X1) @ X2)
% 0.20/0.52          | ~ (v1_tsep_1 @ X1 @ X2)
% 0.20/0.52          | ~ (m1_pre_topc @ X1 @ X2))),
% 0.20/0.52      inference('simplify', [status(thm)], ['91'])).
% 0.20/0.52  thf('93', plain,
% 0.20/0.52      ((~ (m1_pre_topc @ sk_B @ sk_A)
% 0.20/0.52        | ~ (v1_tsep_1 @ sk_B @ sk_A)
% 0.20/0.52        | (v3_pre_topc @ (u1_struct_0 @ sk_B) @ sk_A)
% 0.20/0.52        | ~ (l1_pre_topc @ sk_A))),
% 0.20/0.52      inference('sup-', [status(thm)], ['90', '92'])).
% 0.20/0.52  thf('94', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('95', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('96', plain,
% 0.20/0.52      ((~ (v1_tsep_1 @ sk_B @ sk_A)
% 0.20/0.52        | (v3_pre_topc @ (u1_struct_0 @ sk_B) @ sk_A))),
% 0.20/0.52      inference('demod', [status(thm)], ['93', '94', '95'])).
% 0.20/0.52  thf('97', plain,
% 0.20/0.52      (((v3_pre_topc @ (u1_struct_0 @ sk_B) @ sk_A))
% 0.20/0.52         <= (((v1_tsep_1 @ sk_B @ sk_A)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['89', '96'])).
% 0.20/0.52  thf('98', plain,
% 0.20/0.52      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.52        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.52      inference('demod', [status(thm)], ['7', '8'])).
% 0.20/0.52  thf('99', plain,
% 0.20/0.52      (![X8 : $i, X9 : $i]:
% 0.20/0.52         (~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.20/0.52          | ~ (v3_pre_topc @ X8 @ X9)
% 0.20/0.52          | ((g1_pre_topc @ (u1_struct_0 @ X9) @ (u1_pre_topc @ X9))
% 0.20/0.52              = (k6_tmap_1 @ X9 @ X8))
% 0.20/0.52          | ~ (l1_pre_topc @ X9)
% 0.20/0.52          | ~ (v2_pre_topc @ X9)
% 0.20/0.52          | (v2_struct_0 @ X9))),
% 0.20/0.52      inference('cnf', [status(esa)], [t106_tmap_1])).
% 0.20/0.52  thf('100', plain,
% 0.20/0.52      (((v2_struct_0 @ sk_A)
% 0.20/0.52        | ~ (v2_pre_topc @ sk_A)
% 0.20/0.52        | ~ (l1_pre_topc @ sk_A)
% 0.20/0.52        | ((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.20/0.52            = (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 0.20/0.52        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_B) @ sk_A))),
% 0.20/0.52      inference('sup-', [status(thm)], ['98', '99'])).
% 0.20/0.52  thf('101', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('102', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('103', plain,
% 0.20/0.52      (((v2_struct_0 @ sk_A)
% 0.20/0.52        | ((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.20/0.52            = (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 0.20/0.52        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_B) @ sk_A))),
% 0.20/0.52      inference('demod', [status(thm)], ['100', '101', '102'])).
% 0.20/0.52  thf('104', plain,
% 0.20/0.52      (((k8_tmap_1 @ sk_A @ sk_B) = (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))),
% 0.20/0.52      inference('sup+', [status(thm)], ['29', '58'])).
% 0.20/0.52  thf('105', plain,
% 0.20/0.52      (((v2_struct_0 @ sk_A)
% 0.20/0.52        | ((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.20/0.52            = (k8_tmap_1 @ sk_A @ sk_B))
% 0.20/0.52        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_B) @ sk_A))),
% 0.20/0.52      inference('demod', [status(thm)], ['103', '104'])).
% 0.20/0.52  thf('106', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('107', plain,
% 0.20/0.52      ((~ (v3_pre_topc @ (u1_struct_0 @ sk_B) @ sk_A)
% 0.20/0.52        | ((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.20/0.52            = (k8_tmap_1 @ sk_A @ sk_B)))),
% 0.20/0.52      inference('clc', [status(thm)], ['105', '106'])).
% 0.20/0.52  thf('108', plain,
% 0.20/0.52      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.20/0.52          = (k8_tmap_1 @ sk_A @ sk_B)))
% 0.20/0.52         <= (((v1_tsep_1 @ sk_B @ sk_A)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['97', '107'])).
% 0.20/0.52  thf('109', plain,
% 0.20/0.52      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.20/0.52          != (k8_tmap_1 @ sk_A @ sk_B)))
% 0.20/0.52         <= (~
% 0.20/0.52             (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.20/0.52                = (k8_tmap_1 @ sk_A @ sk_B))))),
% 0.20/0.52      inference('split', [status(esa)], ['0'])).
% 0.20/0.52  thf('110', plain,
% 0.20/0.52      ((((k8_tmap_1 @ sk_A @ sk_B) != (k8_tmap_1 @ sk_A @ sk_B)))
% 0.20/0.52         <= (~
% 0.20/0.52             (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.20/0.52                = (k8_tmap_1 @ sk_A @ sk_B))) & 
% 0.20/0.52             ((v1_tsep_1 @ sk_B @ sk_A)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['108', '109'])).
% 0.20/0.52  thf('111', plain,
% 0.20/0.52      (~ ((v1_tsep_1 @ sk_B @ sk_A)) | 
% 0.20/0.52       (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.20/0.52          = (k8_tmap_1 @ sk_A @ sk_B)))),
% 0.20/0.52      inference('simplify', [status(thm)], ['110'])).
% 0.20/0.52  thf('112', plain, ($false),
% 0.20/0.52      inference('sat_resolution*', [status(thm)], ['1', '4', '87', '88', '111'])).
% 0.20/0.52  
% 0.20/0.52  % SZS output end Refutation
% 0.20/0.52  
% 0.20/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
