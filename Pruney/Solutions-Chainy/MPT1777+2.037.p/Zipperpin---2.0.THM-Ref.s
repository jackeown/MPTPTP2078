%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ozFgpvtrYL

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:10:32 EST 2020

% Result     : Theorem 44.99s
% Output     : Refutation 44.99s
% Verified   : 
% Statistics : Number of formulae       :  214 (3975 expanded)
%              Number of leaves         :   43 (1183 expanded)
%              Depth                    :   28
%              Number of atoms          : 1835 (99485 expanded)
%              Number of equality atoms :   51 (2706 expanded)
%              Maximal formula depth    :   32 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_G_type,type,(
    sk_G: $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k3_tmap_1_type,type,(
    k3_tmap_1: $i > $i > $i > $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(r1_tmap_1_type,type,(
    r1_tmap_1: $i > $i > $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(g1_pre_topc_type,type,(
    g1_pre_topc: $i > $i > $i )).

thf(m1_connsp_2_type,type,(
    m1_connsp_2: $i > $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(t88_tmap_1,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( v2_pre_topc @ B )
            & ( l1_pre_topc @ B ) )
         => ! [C: $i] :
              ( ( ~ ( v2_struct_0 @ C )
                & ( m1_pre_topc @ C @ A ) )
             => ! [D: $i] :
                  ( ( ~ ( v2_struct_0 @ D )
                    & ( m1_pre_topc @ D @ A ) )
                 => ! [E: $i] :
                      ( ( ( v1_funct_1 @ E )
                        & ( v1_funct_2 @ E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) )
                        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) )
                     => ( ( ( g1_pre_topc @ ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) )
                          = D )
                       => ! [F: $i] :
                            ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) )
                           => ! [G: $i] :
                                ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) )
                               => ( ( ( F = G )
                                    & ( r1_tmap_1 @ C @ B @ ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ G ) )
                                 => ( r1_tmap_1 @ D @ B @ E @ F ) ) ) ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( ~ ( v2_struct_0 @ B )
              & ( v2_pre_topc @ B )
              & ( l1_pre_topc @ B ) )
           => ! [C: $i] :
                ( ( ~ ( v2_struct_0 @ C )
                  & ( m1_pre_topc @ C @ A ) )
               => ! [D: $i] :
                    ( ( ~ ( v2_struct_0 @ D )
                      & ( m1_pre_topc @ D @ A ) )
                   => ! [E: $i] :
                        ( ( ( v1_funct_1 @ E )
                          & ( v1_funct_2 @ E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) )
                          & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) )
                       => ( ( ( g1_pre_topc @ ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) )
                            = D )
                         => ! [F: $i] :
                              ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) )
                             => ! [G: $i] :
                                  ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) )
                                 => ( ( ( F = G )
                                      & ( r1_tmap_1 @ C @ B @ ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ G ) )
                                   => ( r1_tmap_1 @ D @ B @ E @ F ) ) ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t88_tmap_1])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('2',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['1'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('3',plain,(
    ! [X5: $i,X7: $i] :
      ( ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X7 ) )
      | ~ ( r1_tarski @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('4',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    sk_F = sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_F ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) )
    = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( m1_pre_topc @ A @ A ) ) )).

thf('10',plain,(
    ! [X28: $i] :
      ( ( m1_pre_topc @ X28 @ X28 )
      | ~ ( l1_pre_topc @ X28 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf(t65_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( l1_pre_topc @ B )
         => ( ( m1_pre_topc @ A @ B )
          <=> ( m1_pre_topc @ A @ ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ) )).

thf('11',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( l1_pre_topc @ X18 )
      | ~ ( m1_pre_topc @ X19 @ ( g1_pre_topc @ ( u1_struct_0 @ X18 ) @ ( u1_pre_topc @ X18 ) ) )
      | ( m1_pre_topc @ X19 @ X18 )
      | ~ ( l1_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[t65_pre_topc])).

thf('12',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) @ X0 )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,
    ( ~ ( l1_pre_topc @ sk_D )
    | ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) ) @ sk_C )
    | ~ ( l1_pre_topc @ sk_C ) ),
    inference('sup-',[status(thm)],['9','13'])).

thf('15',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('16',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( m1_pre_topc @ X15 @ X16 )
      | ( l1_pre_topc @ X15 )
      | ~ ( l1_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('17',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_D ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) )
    = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( m1_pre_topc @ X15 @ X16 )
      | ( l1_pre_topc @ X15 )
      | ~ ( l1_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('23',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_C ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,(
    m1_pre_topc @ sk_D @ sk_C ),
    inference(demod,[status(thm)],['14','19','20','25'])).

thf(t1_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( m1_subset_1 @ ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('27',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( m1_pre_topc @ X26 @ X27 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X26 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
      | ~ ( l1_pre_topc @ X27 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('28',plain,
    ( ~ ( l1_pre_topc @ sk_C )
    | ( m1_subset_1 @ ( u1_struct_0 @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['23','24'])).

thf('30',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_tarski @ X5 @ X6 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('32',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('34',plain,
    ( ~ ( r1_tarski @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D ) )
    | ( ( u1_struct_0 @ sk_C )
      = ( u1_struct_0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) )
    = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    ! [X28: $i] :
      ( ( m1_pre_topc @ X28 @ X28 )
      | ~ ( l1_pre_topc @ X28 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('37',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( l1_pre_topc @ X18 )
      | ~ ( m1_pre_topc @ X19 @ X18 )
      | ( m1_pre_topc @ X19 @ ( g1_pre_topc @ ( u1_struct_0 @ X18 ) @ ( u1_pre_topc @ X18 ) ) )
      | ~ ( l1_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[t65_pre_topc])).

thf('38',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( m1_pre_topc @ X26 @ X27 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X26 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
      | ~ ( l1_pre_topc @ X27 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('41',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,
    ( ~ ( l1_pre_topc @ sk_D )
    | ( m1_subset_1 @ ( u1_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) ) ) ) )
    | ~ ( l1_pre_topc @ sk_C ) ),
    inference('sup-',[status(thm)],['35','41'])).

thf('43',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['17','18'])).

thf('44',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) )
    = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['23','24'])).

thf('46',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['42','43','44','45'])).

thf('47',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_tarski @ X5 @ X6 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('48',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,
    ( ( u1_struct_0 @ sk_C )
    = ( u1_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['34','48'])).

thf('50',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['8','49'])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('51',plain,(
    ! [X13: $i] :
      ( ( ( k2_struct_0 @ X13 )
        = ( u1_struct_0 @ X13 ) )
      | ~ ( l1_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('52',plain,
    ( ( u1_struct_0 @ sk_C )
    = ( u1_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['34','48'])).

thf('53',plain,
    ( ( ( u1_struct_0 @ sk_C )
      = ( k2_struct_0 @ sk_D ) )
    | ~ ( l1_struct_0 @ sk_D ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf('54',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['17','18'])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('55',plain,(
    ! [X14: $i] :
      ( ( l1_struct_0 @ X14 )
      | ~ ( l1_pre_topc @ X14 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('56',plain,(
    l1_struct_0 @ sk_D ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,
    ( ( u1_struct_0 @ sk_C )
    = ( k2_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['53','56'])).

thf('58',plain,(
    ! [X13: $i] :
      ( ( ( k2_struct_0 @ X13 )
        = ( u1_struct_0 @ X13 ) )
      | ~ ( l1_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('59',plain,
    ( ( u1_struct_0 @ sk_C )
    = ( k2_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['53','56'])).

thf('60',plain,
    ( ( ( k2_struct_0 @ sk_C )
      = ( k2_struct_0 @ sk_D ) )
    | ~ ( l1_struct_0 @ sk_C ) ),
    inference('sup+',[status(thm)],['58','59'])).

thf('61',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['23','24'])).

thf('62',plain,(
    ! [X14: $i] :
      ( ( l1_struct_0 @ X14 )
      | ~ ( l1_pre_topc @ X14 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('63',plain,(
    l1_struct_0 @ sk_C ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,
    ( ( k2_struct_0 @ sk_C )
    = ( k2_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['60','63'])).

thf('65',plain,
    ( ( u1_struct_0 @ sk_C )
    = ( k2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['57','64'])).

thf('66',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['50','65'])).

thf('67',plain,
    ( ( u1_struct_0 @ sk_C )
    = ( u1_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['34','48'])).

thf('68',plain,
    ( ( u1_struct_0 @ sk_C )
    = ( k2_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['53','56'])).

thf('69',plain,
    ( ( k2_struct_0 @ sk_D )
    = ( u1_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('70',plain,
    ( ( k2_struct_0 @ sk_C )
    = ( k2_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['60','63'])).

thf('71',plain,
    ( ( k2_struct_0 @ sk_C )
    = ( u1_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['69','70'])).

thf(t83_tmap_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( v2_pre_topc @ B )
            & ( l1_pre_topc @ B ) )
         => ! [C: $i] :
              ( ( ~ ( v2_struct_0 @ C )
                & ( m1_pre_topc @ C @ A ) )
             => ! [D: $i] :
                  ( ( ~ ( v2_struct_0 @ D )
                    & ( m1_pre_topc @ D @ A ) )
                 => ! [E: $i] :
                      ( ( ( v1_funct_1 @ E )
                        & ( v1_funct_2 @ E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) )
                        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) )
                     => ( ( m1_pre_topc @ C @ D )
                       => ! [F: $i] :
                            ( ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( u1_struct_0 @ D ) ) )
                           => ! [G: $i] :
                                ( ( m1_subset_1 @ G @ ( u1_struct_0 @ D ) )
                               => ! [H: $i] :
                                    ( ( m1_subset_1 @ H @ ( u1_struct_0 @ C ) )
                                   => ( ( ( r1_tarski @ F @ ( u1_struct_0 @ C ) )
                                        & ( m1_connsp_2 @ F @ D @ G )
                                        & ( G = H ) )
                                     => ( ( r1_tmap_1 @ D @ B @ E @ G )
                                      <=> ( r1_tmap_1 @ C @ B @ ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ H ) ) ) ) ) ) ) ) ) ) ) ) )).

thf('72',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i,X36: $i,X37: $i,X38: $i,X39: $i] :
      ( ( v2_struct_0 @ X32 )
      | ~ ( v2_pre_topc @ X32 )
      | ~ ( l1_pre_topc @ X32 )
      | ( v2_struct_0 @ X33 )
      | ~ ( m1_pre_topc @ X33 @ X34 )
      | ~ ( m1_pre_topc @ X35 @ X33 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X33 ) ) )
      | ~ ( m1_subset_1 @ X37 @ ( u1_struct_0 @ X35 ) )
      | ~ ( r1_tmap_1 @ X35 @ X32 @ ( k3_tmap_1 @ X34 @ X32 @ X33 @ X35 @ X38 ) @ X37 )
      | ( r1_tmap_1 @ X33 @ X32 @ X38 @ X39 )
      | ( X39 != X37 )
      | ~ ( m1_connsp_2 @ X36 @ X33 @ X39 )
      | ~ ( r1_tarski @ X36 @ ( u1_struct_0 @ X35 ) )
      | ~ ( m1_subset_1 @ X39 @ ( u1_struct_0 @ X33 ) )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X33 ) @ ( u1_struct_0 @ X32 ) ) ) )
      | ~ ( v1_funct_2 @ X38 @ ( u1_struct_0 @ X33 ) @ ( u1_struct_0 @ X32 ) )
      | ~ ( v1_funct_1 @ X38 )
      | ~ ( m1_pre_topc @ X35 @ X34 )
      | ( v2_struct_0 @ X35 )
      | ~ ( l1_pre_topc @ X34 )
      | ~ ( v2_pre_topc @ X34 )
      | ( v2_struct_0 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t83_tmap_1])).

thf('73',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i,X36: $i,X37: $i,X38: $i] :
      ( ( v2_struct_0 @ X34 )
      | ~ ( v2_pre_topc @ X34 )
      | ~ ( l1_pre_topc @ X34 )
      | ( v2_struct_0 @ X35 )
      | ~ ( m1_pre_topc @ X35 @ X34 )
      | ~ ( v1_funct_1 @ X38 )
      | ~ ( v1_funct_2 @ X38 @ ( u1_struct_0 @ X33 ) @ ( u1_struct_0 @ X32 ) )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X33 ) @ ( u1_struct_0 @ X32 ) ) ) )
      | ~ ( m1_subset_1 @ X37 @ ( u1_struct_0 @ X33 ) )
      | ~ ( r1_tarski @ X36 @ ( u1_struct_0 @ X35 ) )
      | ~ ( m1_connsp_2 @ X36 @ X33 @ X37 )
      | ( r1_tmap_1 @ X33 @ X32 @ X38 @ X37 )
      | ~ ( r1_tmap_1 @ X35 @ X32 @ ( k3_tmap_1 @ X34 @ X32 @ X33 @ X35 @ X38 ) @ X37 )
      | ~ ( m1_subset_1 @ X37 @ ( u1_struct_0 @ X35 ) )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X33 ) ) )
      | ~ ( m1_pre_topc @ X35 @ X33 )
      | ~ ( m1_pre_topc @ X33 @ X34 )
      | ( v2_struct_0 @ X33 )
      | ~ ( l1_pre_topc @ X32 )
      | ~ ( v2_pre_topc @ X32 )
      | ( v2_struct_0 @ X32 ) ) ),
    inference(simplify,[status(thm)],['72'])).

thf('74',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_C ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ sk_D )
      | ~ ( m1_pre_topc @ sk_D @ X2 )
      | ~ ( m1_pre_topc @ X3 @ sk_D )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) )
      | ~ ( m1_subset_1 @ X5 @ ( u1_struct_0 @ X3 ) )
      | ~ ( r1_tmap_1 @ X3 @ X0 @ ( k3_tmap_1 @ X2 @ X0 @ sk_D @ X3 @ X1 ) @ X5 )
      | ( r1_tmap_1 @ sk_D @ X0 @ X1 @ X5 )
      | ~ ( m1_connsp_2 @ X4 @ sk_D @ X5 )
      | ~ ( r1_tarski @ X4 @ ( u1_struct_0 @ X3 ) )
      | ~ ( m1_subset_1 @ X5 @ ( u1_struct_0 @ sk_D ) )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( m1_pre_topc @ X3 @ X2 )
      | ( v2_struct_0 @ X3 )
      | ~ ( l1_pre_topc @ X2 )
      | ~ ( v2_pre_topc @ X2 )
      | ( v2_struct_0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['71','73'])).

thf('75',plain,
    ( ( k2_struct_0 @ sk_C )
    = ( u1_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('76',plain,
    ( ( k2_struct_0 @ sk_C )
    = ( u1_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('77',plain,
    ( ( k2_struct_0 @ sk_C )
    = ( u1_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('78',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_C ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ sk_D )
      | ~ ( m1_pre_topc @ sk_D @ X2 )
      | ~ ( m1_pre_topc @ X3 @ sk_D )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_C ) ) )
      | ~ ( m1_subset_1 @ X5 @ ( u1_struct_0 @ X3 ) )
      | ~ ( r1_tmap_1 @ X3 @ X0 @ ( k3_tmap_1 @ X2 @ X0 @ sk_D @ X3 @ X1 ) @ X5 )
      | ( r1_tmap_1 @ sk_D @ X0 @ X1 @ X5 )
      | ~ ( m1_connsp_2 @ X4 @ sk_D @ X5 )
      | ~ ( r1_tarski @ X4 @ ( u1_struct_0 @ X3 ) )
      | ~ ( m1_subset_1 @ X5 @ ( k2_struct_0 @ sk_C ) )
      | ~ ( v1_funct_2 @ X1 @ ( k2_struct_0 @ sk_C ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( m1_pre_topc @ X3 @ X2 )
      | ( v2_struct_0 @ X3 )
      | ~ ( l1_pre_topc @ X2 )
      | ~ ( v2_pre_topc @ X2 )
      | ( v2_struct_0 @ X2 ) ) ),
    inference(demod,[status(thm)],['74','75','76','77'])).

thf('79',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X1 )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( v1_funct_2 @ sk_E @ ( k2_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( m1_subset_1 @ X2 @ ( k2_struct_0 @ sk_C ) )
      | ~ ( r1_tarski @ X3 @ ( u1_struct_0 @ X1 ) )
      | ~ ( m1_connsp_2 @ X3 @ sk_D @ X2 )
      | ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X2 )
      | ~ ( r1_tmap_1 @ X1 @ sk_B @ ( k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E ) @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X1 ) )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_C ) ) )
      | ~ ( m1_pre_topc @ X1 @ sk_D )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ( v2_struct_0 @ sk_D )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['66','78'])).

thf('80',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,
    ( ( u1_struct_0 @ sk_C )
    = ( u1_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['34','48'])).

thf('83',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['81','82'])).

thf('84',plain,
    ( ( u1_struct_0 @ sk_C )
    = ( k2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['57','64'])).

thf('85',plain,(
    v1_funct_2 @ sk_E @ ( k2_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['83','84'])).

thf('86',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X1 )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ~ ( m1_subset_1 @ X2 @ ( k2_struct_0 @ sk_C ) )
      | ~ ( r1_tarski @ X3 @ ( u1_struct_0 @ X1 ) )
      | ~ ( m1_connsp_2 @ X3 @ sk_D @ X2 )
      | ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X2 )
      | ~ ( r1_tmap_1 @ X1 @ sk_B @ ( k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E ) @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X1 ) )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_C ) ) )
      | ~ ( m1_pre_topc @ X1 @ sk_D )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['79','80','85','86','87'])).

thf('89',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ~ ( m1_pre_topc @ sk_D @ sk_A )
      | ~ ( m1_pre_topc @ sk_C @ sk_D )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_C ) ) )
      | ~ ( m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_C ) )
      | ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F )
      | ~ ( m1_connsp_2 @ X0 @ sk_D @ sk_F )
      | ~ ( r1_tarski @ X0 @ ( u1_struct_0 @ sk_C ) )
      | ~ ( m1_subset_1 @ sk_F @ ( k2_struct_0 @ sk_C ) )
      | ~ ( m1_pre_topc @ sk_C @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['7','88'])).

thf('90',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) )
    = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['38'])).

thf('93',plain,
    ( ( m1_pre_topc @ sk_C @ sk_D )
    | ~ ( l1_pre_topc @ sk_C ) ),
    inference('sup+',[status(thm)],['91','92'])).

thf('94',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['23','24'])).

thf('95',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(demod,[status(thm)],['93','94'])).

thf('96',plain,
    ( ( u1_struct_0 @ sk_C )
    = ( k2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['57','64'])).

thf('97',plain,(
    ! [X13: $i] :
      ( ( ( k2_struct_0 @ X13 )
        = ( u1_struct_0 @ X13 ) )
      | ~ ( l1_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('98',plain,(
    m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    sk_F = sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['98','99'])).

thf('101',plain,
    ( ( m1_subset_1 @ sk_F @ ( k2_struct_0 @ sk_C ) )
    | ~ ( l1_struct_0 @ sk_C ) ),
    inference('sup+',[status(thm)],['97','100'])).

thf('102',plain,(
    l1_struct_0 @ sk_C ),
    inference('sup-',[status(thm)],['61','62'])).

thf('103',plain,(
    m1_subset_1 @ sk_F @ ( k2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['101','102'])).

thf('104',plain,
    ( ( u1_struct_0 @ sk_C )
    = ( k2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['57','64'])).

thf('105',plain,(
    m1_subset_1 @ sk_F @ ( k2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['101','102'])).

thf('106',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_C ) ) )
      | ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F )
      | ~ ( m1_connsp_2 @ X0 @ sk_D @ sk_F )
      | ~ ( r1_tarski @ X0 @ ( k2_struct_0 @ sk_C ) )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['89','90','95','96','103','104','105','106','107','108'])).

thf('110',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ~ ( r1_tarski @ ( k2_struct_0 @ sk_C ) @ ( k2_struct_0 @ sk_C ) )
    | ~ ( m1_connsp_2 @ ( k2_struct_0 @ sk_C ) @ sk_D @ sk_F )
    | ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['4','109'])).

thf('111',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['1'])).

thf('112',plain,(
    ! [X13: $i] :
      ( ( ( k2_struct_0 @ X13 )
        = ( u1_struct_0 @ X13 ) )
      | ~ ( l1_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('113',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,
    ( ( m1_subset_1 @ sk_F @ ( k2_struct_0 @ sk_D ) )
    | ~ ( l1_struct_0 @ sk_D ) ),
    inference('sup+',[status(thm)],['112','113'])).

thf('115',plain,(
    l1_struct_0 @ sk_D ),
    inference('sup-',[status(thm)],['54','55'])).

thf('116',plain,(
    m1_subset_1 @ sk_F @ ( k2_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['114','115'])).

thf('117',plain,(
    ! [X13: $i] :
      ( ( ( k2_struct_0 @ X13 )
        = ( u1_struct_0 @ X13 ) )
      | ~ ( l1_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('118',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t5_connsp_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ( ( ( v3_pre_topc @ B @ A )
                  & ( r2_hidden @ C @ B ) )
               => ( m1_connsp_2 @ B @ A @ C ) ) ) ) ) )).

thf('119',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ~ ( v3_pre_topc @ X21 @ X22 )
      | ~ ( r2_hidden @ X23 @ X21 )
      | ( m1_connsp_2 @ X21 @ X22 @ X23 )
      | ~ ( m1_subset_1 @ X23 @ ( u1_struct_0 @ X22 ) )
      | ~ ( l1_pre_topc @ X22 )
      | ~ ( v2_pre_topc @ X22 )
      | ( v2_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t5_connsp_2])).

thf('120',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ( m1_connsp_2 @ ( u1_struct_0 @ X0 ) @ X0 @ X1 )
      | ~ ( r2_hidden @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['118','119'])).

thf('121',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k2_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( r2_hidden @ X1 @ ( u1_struct_0 @ X0 ) )
      | ( m1_connsp_2 @ ( u1_struct_0 @ X0 ) @ X0 @ X1 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['117','120'])).

thf('122',plain,
    ( ( v2_struct_0 @ sk_D )
    | ~ ( v2_pre_topc @ sk_D )
    | ~ ( l1_pre_topc @ sk_D )
    | ( m1_connsp_2 @ ( u1_struct_0 @ sk_D ) @ sk_D @ sk_F )
    | ~ ( r2_hidden @ sk_F @ ( u1_struct_0 @ sk_D ) )
    | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_D ) @ sk_D )
    | ~ ( l1_struct_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['116','121'])).

thf('123',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( v2_pre_topc @ B ) ) ) )).

thf('124',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_pre_topc @ X11 @ X12 )
      | ( v2_pre_topc @ X11 )
      | ~ ( l1_pre_topc @ X12 )
      | ~ ( v2_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[cc1_pre_topc])).

thf('125',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_pre_topc @ sk_D ) ),
    inference('sup-',[status(thm)],['123','124'])).

thf('126',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('128',plain,(
    v2_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['125','126','127'])).

thf('129',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['17','18'])).

thf('130',plain,
    ( ( u1_struct_0 @ sk_C )
    = ( u1_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['34','48'])).

thf('131',plain,
    ( ( u1_struct_0 @ sk_C )
    = ( u1_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['34','48'])).

thf('132',plain,
    ( ( u1_struct_0 @ sk_C )
    = ( u1_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['34','48'])).

thf('133',plain,(
    l1_struct_0 @ sk_D ),
    inference('sup-',[status(thm)],['54','55'])).

thf('134',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( m1_connsp_2 @ ( u1_struct_0 @ sk_C ) @ sk_D @ sk_F )
    | ~ ( r2_hidden @ sk_F @ ( u1_struct_0 @ sk_C ) )
    | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_C ) @ sk_D ) ),
    inference(demod,[status(thm)],['122','128','129','130','131','132','133'])).

thf('135',plain,
    ( ( u1_struct_0 @ sk_C )
    = ( k2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['57','64'])).

thf('136',plain,
    ( ( u1_struct_0 @ sk_C )
    = ( k2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['57','64'])).

thf('137',plain,(
    ! [X13: $i] :
      ( ( ( k2_struct_0 @ X13 )
        = ( u1_struct_0 @ X13 ) )
      | ~ ( l1_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('138',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['98','99'])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('139',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r2_hidden @ X3 @ X4 )
      | ( v1_xboole_0 @ X4 )
      | ~ ( m1_subset_1 @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('140',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) )
    | ( r2_hidden @ sk_F @ ( u1_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['138','139'])).

thf('141',plain,
    ( ( r2_hidden @ sk_F @ ( k2_struct_0 @ sk_C ) )
    | ~ ( l1_struct_0 @ sk_C )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['137','140'])).

thf('142',plain,(
    l1_struct_0 @ sk_C ),
    inference('sup-',[status(thm)],['61','62'])).

thf('143',plain,
    ( ( r2_hidden @ sk_F @ ( k2_struct_0 @ sk_C ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['141','142'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('144',plain,(
    ! [X17: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X17 ) )
      | ~ ( l1_struct_0 @ X17 )
      | ( v2_struct_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('145',plain,
    ( ( r2_hidden @ sk_F @ ( k2_struct_0 @ sk_C ) )
    | ( v2_struct_0 @ sk_C )
    | ~ ( l1_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['143','144'])).

thf('146',plain,(
    l1_struct_0 @ sk_C ),
    inference('sup-',[status(thm)],['61','62'])).

thf('147',plain,
    ( ( r2_hidden @ sk_F @ ( k2_struct_0 @ sk_C ) )
    | ( v2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['145','146'])).

thf('148',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('149',plain,(
    r2_hidden @ sk_F @ ( k2_struct_0 @ sk_C ) ),
    inference(clc,[status(thm)],['147','148'])).

thf('150',plain,
    ( ( u1_struct_0 @ sk_C )
    = ( k2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['57','64'])).

thf('151',plain,
    ( ( k2_struct_0 @ sk_C )
    = ( k2_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['60','63'])).

thf(fc10_tops_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( v3_pre_topc @ ( k2_struct_0 @ A ) @ A ) ) )).

thf('152',plain,(
    ! [X20: $i] :
      ( ( v3_pre_topc @ ( k2_struct_0 @ X20 ) @ X20 )
      | ~ ( l1_pre_topc @ X20 )
      | ~ ( v2_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[fc10_tops_1])).

thf('153',plain,
    ( ( v3_pre_topc @ ( k2_struct_0 @ sk_C ) @ sk_D )
    | ~ ( v2_pre_topc @ sk_D )
    | ~ ( l1_pre_topc @ sk_D ) ),
    inference('sup+',[status(thm)],['151','152'])).

thf('154',plain,(
    v2_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['125','126','127'])).

thf('155',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['17','18'])).

thf('156',plain,(
    v3_pre_topc @ ( k2_struct_0 @ sk_C ) @ sk_D ),
    inference(demod,[status(thm)],['153','154','155'])).

thf('157',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( m1_connsp_2 @ ( k2_struct_0 @ sk_C ) @ sk_D @ sk_F ) ),
    inference(demod,[status(thm)],['134','135','136','149','150','156'])).

thf('158',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('159',plain,(
    m1_connsp_2 @ ( k2_struct_0 @ sk_C ) @ sk_D @ sk_F ),
    inference(clc,[status(thm)],['157','158'])).

thf('160',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['110','111','159'])).

thf('161',plain,(
    ~ ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('162',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['160','161'])).

thf('163',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('164',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['162','163'])).

thf('165',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('166',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C ) ),
    inference(clc,[status(thm)],['164','165'])).

thf('167',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('168',plain,(
    v2_struct_0 @ sk_C ),
    inference(clc,[status(thm)],['166','167'])).

thf('169',plain,(
    $false ),
    inference(demod,[status(thm)],['0','168'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ozFgpvtrYL
% 0.12/0.32  % Computer   : n021.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % DateTime   : Tue Dec  1 11:36:34 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.12/0.32  % Running portfolio for 600 s
% 0.12/0.32  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.32  % Number of cores: 8
% 0.12/0.33  % Python version: Python 3.6.8
% 0.12/0.33  % Running in FO mode
% 44.99/45.27  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 44.99/45.27  % Solved by: fo/fo7.sh
% 44.99/45.27  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 44.99/45.27  % done 20713 iterations in 44.834s
% 44.99/45.27  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 44.99/45.27  % SZS output start Refutation
% 44.99/45.27  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 44.99/45.27  thf(sk_G_type, type, sk_G: $i).
% 44.99/45.27  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 44.99/45.27  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 44.99/45.27  thf(sk_E_type, type, sk_E: $i).
% 44.99/45.27  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 44.99/45.27  thf(k3_tmap_1_type, type, k3_tmap_1: $i > $i > $i > $i > $i > $i).
% 44.99/45.27  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 44.99/45.27  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 44.99/45.27  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 44.99/45.27  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 44.99/45.27  thf(r1_tmap_1_type, type, r1_tmap_1: $i > $i > $i > $i > $o).
% 44.99/45.27  thf(sk_C_type, type, sk_C: $i).
% 44.99/45.27  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 44.99/45.27  thf(sk_D_type, type, sk_D: $i).
% 44.99/45.27  thf(g1_pre_topc_type, type, g1_pre_topc: $i > $i > $i).
% 44.99/45.27  thf(m1_connsp_2_type, type, m1_connsp_2: $i > $i > $i > $o).
% 44.99/45.27  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 44.99/45.27  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 44.99/45.27  thf(sk_B_type, type, sk_B: $i).
% 44.99/45.27  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 44.99/45.27  thf(sk_A_type, type, sk_A: $i).
% 44.99/45.27  thf(sk_F_type, type, sk_F: $i).
% 44.99/45.27  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 44.99/45.27  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 44.99/45.27  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 44.99/45.27  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 44.99/45.27  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 44.99/45.27  thf(t88_tmap_1, conjecture,
% 44.99/45.27    (![A:$i]:
% 44.99/45.27     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 44.99/45.27       ( ![B:$i]:
% 44.99/45.27         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 44.99/45.27             ( l1_pre_topc @ B ) ) =>
% 44.99/45.27           ( ![C:$i]:
% 44.99/45.27             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 44.99/45.27               ( ![D:$i]:
% 44.99/45.27                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 44.99/45.27                   ( ![E:$i]:
% 44.99/45.27                     ( ( ( v1_funct_1 @ E ) & 
% 44.99/45.27                         ( v1_funct_2 @
% 44.99/45.27                           E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 44.99/45.27                         ( m1_subset_1 @
% 44.99/45.27                           E @ 
% 44.99/45.27                           ( k1_zfmisc_1 @
% 44.99/45.27                             ( k2_zfmisc_1 @
% 44.99/45.27                               ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 44.99/45.27                       ( ( ( g1_pre_topc @
% 44.99/45.27                             ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) ) =
% 44.99/45.27                           ( D ) ) =>
% 44.99/45.27                         ( ![F:$i]:
% 44.99/45.27                           ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 44.99/45.27                             ( ![G:$i]:
% 44.99/45.27                               ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) ) =>
% 44.99/45.27                                 ( ( ( ( F ) = ( G ) ) & 
% 44.99/45.27                                     ( r1_tmap_1 @
% 44.99/45.27                                       C @ B @ 
% 44.99/45.27                                       ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ G ) ) =>
% 44.99/45.27                                   ( r1_tmap_1 @ D @ B @ E @ F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 44.99/45.27  thf(zf_stmt_0, negated_conjecture,
% 44.99/45.27    (~( ![A:$i]:
% 44.99/45.27        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 44.99/45.27            ( l1_pre_topc @ A ) ) =>
% 44.99/45.27          ( ![B:$i]:
% 44.99/45.27            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 44.99/45.27                ( l1_pre_topc @ B ) ) =>
% 44.99/45.27              ( ![C:$i]:
% 44.99/45.27                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 44.99/45.27                  ( ![D:$i]:
% 44.99/45.27                    ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 44.99/45.27                      ( ![E:$i]:
% 44.99/45.27                        ( ( ( v1_funct_1 @ E ) & 
% 44.99/45.27                            ( v1_funct_2 @
% 44.99/45.27                              E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 44.99/45.27                            ( m1_subset_1 @
% 44.99/45.27                              E @ 
% 44.99/45.27                              ( k1_zfmisc_1 @
% 44.99/45.27                                ( k2_zfmisc_1 @
% 44.99/45.27                                  ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 44.99/45.27                          ( ( ( g1_pre_topc @
% 44.99/45.27                                ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) ) =
% 44.99/45.27                              ( D ) ) =>
% 44.99/45.27                            ( ![F:$i]:
% 44.99/45.27                              ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 44.99/45.27                                ( ![G:$i]:
% 44.99/45.27                                  ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) ) =>
% 44.99/45.27                                    ( ( ( ( F ) = ( G ) ) & 
% 44.99/45.27                                        ( r1_tmap_1 @
% 44.99/45.27                                          C @ B @ 
% 44.99/45.27                                          ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ G ) ) =>
% 44.99/45.27                                      ( r1_tmap_1 @ D @ B @ E @ F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 44.99/45.27    inference('cnf.neg', [status(esa)], [t88_tmap_1])).
% 44.99/45.27  thf('0', plain, (~ (v2_struct_0 @ sk_C)),
% 44.99/45.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 44.99/45.27  thf(d10_xboole_0, axiom,
% 44.99/45.27    (![A:$i,B:$i]:
% 44.99/45.27     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 44.99/45.27  thf('1', plain,
% 44.99/45.27      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 44.99/45.27      inference('cnf', [status(esa)], [d10_xboole_0])).
% 44.99/45.27  thf('2', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 44.99/45.27      inference('simplify', [status(thm)], ['1'])).
% 44.99/45.27  thf(t3_subset, axiom,
% 44.99/45.27    (![A:$i,B:$i]:
% 44.99/45.27     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 44.99/45.27  thf('3', plain,
% 44.99/45.27      (![X5 : $i, X7 : $i]:
% 44.99/45.27         ((m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X7)) | ~ (r1_tarski @ X5 @ X7))),
% 44.99/45.27      inference('cnf', [status(esa)], [t3_subset])).
% 44.99/45.27  thf('4', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 44.99/45.27      inference('sup-', [status(thm)], ['2', '3'])).
% 44.99/45.27  thf('5', plain,
% 44.99/45.27      ((r1_tmap_1 @ sk_C @ sk_B @ 
% 44.99/45.27        (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_G)),
% 44.99/45.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 44.99/45.27  thf('6', plain, (((sk_F) = (sk_G))),
% 44.99/45.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 44.99/45.27  thf('7', plain,
% 44.99/45.27      ((r1_tmap_1 @ sk_C @ sk_B @ 
% 44.99/45.27        (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_F)),
% 44.99/45.27      inference('demod', [status(thm)], ['5', '6'])).
% 44.99/45.27  thf('8', plain,
% 44.99/45.27      ((m1_subset_1 @ sk_E @ 
% 44.99/45.27        (k1_zfmisc_1 @ 
% 44.99/45.27         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 44.99/45.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 44.99/45.27  thf('9', plain,
% 44.99/45.27      (((g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) = (sk_D))),
% 44.99/45.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 44.99/45.27  thf(t2_tsep_1, axiom,
% 44.99/45.27    (![A:$i]: ( ( l1_pre_topc @ A ) => ( m1_pre_topc @ A @ A ) ))).
% 44.99/45.27  thf('10', plain,
% 44.99/45.27      (![X28 : $i]: ((m1_pre_topc @ X28 @ X28) | ~ (l1_pre_topc @ X28))),
% 44.99/45.27      inference('cnf', [status(esa)], [t2_tsep_1])).
% 44.99/45.27  thf(t65_pre_topc, axiom,
% 44.99/45.27    (![A:$i]:
% 44.99/45.27     ( ( l1_pre_topc @ A ) =>
% 44.99/45.27       ( ![B:$i]:
% 44.99/45.27         ( ( l1_pre_topc @ B ) =>
% 44.99/45.27           ( ( m1_pre_topc @ A @ B ) <=>
% 44.99/45.27             ( m1_pre_topc @
% 44.99/45.27               A @ ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ) ))).
% 44.99/45.27  thf('11', plain,
% 44.99/45.27      (![X18 : $i, X19 : $i]:
% 44.99/45.27         (~ (l1_pre_topc @ X18)
% 44.99/45.27          | ~ (m1_pre_topc @ X19 @ 
% 44.99/45.27               (g1_pre_topc @ (u1_struct_0 @ X18) @ (u1_pre_topc @ X18)))
% 44.99/45.27          | (m1_pre_topc @ X19 @ X18)
% 44.99/45.27          | ~ (l1_pre_topc @ X19))),
% 44.99/45.27      inference('cnf', [status(esa)], [t65_pre_topc])).
% 44.99/45.27  thf('12', plain,
% 44.99/45.27      (![X0 : $i]:
% 44.99/45.27         (~ (l1_pre_topc @ 
% 44.99/45.27             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 44.99/45.27          | ~ (l1_pre_topc @ 
% 44.99/45.27               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 44.99/45.27          | (m1_pre_topc @ 
% 44.99/45.27             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)) @ X0)
% 44.99/45.27          | ~ (l1_pre_topc @ X0))),
% 44.99/45.27      inference('sup-', [status(thm)], ['10', '11'])).
% 44.99/45.27  thf('13', plain,
% 44.99/45.27      (![X0 : $i]:
% 44.99/45.27         (~ (l1_pre_topc @ X0)
% 44.99/45.27          | (m1_pre_topc @ 
% 44.99/45.27             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)) @ X0)
% 44.99/45.27          | ~ (l1_pre_topc @ 
% 44.99/45.27               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 44.99/45.27      inference('simplify', [status(thm)], ['12'])).
% 44.99/45.27  thf('14', plain,
% 44.99/45.27      ((~ (l1_pre_topc @ sk_D)
% 44.99/45.27        | (m1_pre_topc @ 
% 44.99/45.27           (g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) @ sk_C)
% 44.99/45.27        | ~ (l1_pre_topc @ sk_C))),
% 44.99/45.27      inference('sup-', [status(thm)], ['9', '13'])).
% 44.99/45.27  thf('15', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 44.99/45.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 44.99/45.27  thf(dt_m1_pre_topc, axiom,
% 44.99/45.27    (![A:$i]:
% 44.99/45.27     ( ( l1_pre_topc @ A ) =>
% 44.99/45.27       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 44.99/45.27  thf('16', plain,
% 44.99/45.27      (![X15 : $i, X16 : $i]:
% 44.99/45.27         (~ (m1_pre_topc @ X15 @ X16)
% 44.99/45.27          | (l1_pre_topc @ X15)
% 44.99/45.27          | ~ (l1_pre_topc @ X16))),
% 44.99/45.27      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 44.99/45.27  thf('17', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_D))),
% 44.99/45.27      inference('sup-', [status(thm)], ['15', '16'])).
% 44.99/45.27  thf('18', plain, ((l1_pre_topc @ sk_A)),
% 44.99/45.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 44.99/45.27  thf('19', plain, ((l1_pre_topc @ sk_D)),
% 44.99/45.27      inference('demod', [status(thm)], ['17', '18'])).
% 44.99/45.27  thf('20', plain,
% 44.99/45.27      (((g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) = (sk_D))),
% 44.99/45.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 44.99/45.27  thf('21', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 44.99/45.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 44.99/45.27  thf('22', plain,
% 44.99/45.27      (![X15 : $i, X16 : $i]:
% 44.99/45.27         (~ (m1_pre_topc @ X15 @ X16)
% 44.99/45.27          | (l1_pre_topc @ X15)
% 44.99/45.27          | ~ (l1_pre_topc @ X16))),
% 44.99/45.27      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 44.99/45.27  thf('23', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_C))),
% 44.99/45.27      inference('sup-', [status(thm)], ['21', '22'])).
% 44.99/45.27  thf('24', plain, ((l1_pre_topc @ sk_A)),
% 44.99/45.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 44.99/45.27  thf('25', plain, ((l1_pre_topc @ sk_C)),
% 44.99/45.27      inference('demod', [status(thm)], ['23', '24'])).
% 44.99/45.27  thf('26', plain, ((m1_pre_topc @ sk_D @ sk_C)),
% 44.99/45.27      inference('demod', [status(thm)], ['14', '19', '20', '25'])).
% 44.99/45.27  thf(t1_tsep_1, axiom,
% 44.99/45.27    (![A:$i]:
% 44.99/45.27     ( ( l1_pre_topc @ A ) =>
% 44.99/45.27       ( ![B:$i]:
% 44.99/45.27         ( ( m1_pre_topc @ B @ A ) =>
% 44.99/45.27           ( m1_subset_1 @
% 44.99/45.27             ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 44.99/45.27  thf('27', plain,
% 44.99/45.27      (![X26 : $i, X27 : $i]:
% 44.99/45.27         (~ (m1_pre_topc @ X26 @ X27)
% 44.99/45.27          | (m1_subset_1 @ (u1_struct_0 @ X26) @ 
% 44.99/45.28             (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 44.99/45.28          | ~ (l1_pre_topc @ X27))),
% 44.99/45.28      inference('cnf', [status(esa)], [t1_tsep_1])).
% 44.99/45.28  thf('28', plain,
% 44.99/45.28      ((~ (l1_pre_topc @ sk_C)
% 44.99/45.28        | (m1_subset_1 @ (u1_struct_0 @ sk_D) @ 
% 44.99/45.28           (k1_zfmisc_1 @ (u1_struct_0 @ sk_C))))),
% 44.99/45.28      inference('sup-', [status(thm)], ['26', '27'])).
% 44.99/45.28  thf('29', plain, ((l1_pre_topc @ sk_C)),
% 44.99/45.28      inference('demod', [status(thm)], ['23', '24'])).
% 44.99/45.28  thf('30', plain,
% 44.99/45.28      ((m1_subset_1 @ (u1_struct_0 @ sk_D) @ 
% 44.99/45.28        (k1_zfmisc_1 @ (u1_struct_0 @ sk_C)))),
% 44.99/45.28      inference('demod', [status(thm)], ['28', '29'])).
% 44.99/45.28  thf('31', plain,
% 44.99/45.28      (![X5 : $i, X6 : $i]:
% 44.99/45.28         ((r1_tarski @ X5 @ X6) | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6)))),
% 44.99/45.28      inference('cnf', [status(esa)], [t3_subset])).
% 44.99/45.28  thf('32', plain, ((r1_tarski @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_C))),
% 44.99/45.28      inference('sup-', [status(thm)], ['30', '31'])).
% 44.99/45.28  thf('33', plain,
% 44.99/45.28      (![X0 : $i, X2 : $i]:
% 44.99/45.28         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 44.99/45.28      inference('cnf', [status(esa)], [d10_xboole_0])).
% 44.99/45.28  thf('34', plain,
% 44.99/45.28      ((~ (r1_tarski @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D))
% 44.99/45.28        | ((u1_struct_0 @ sk_C) = (u1_struct_0 @ sk_D)))),
% 44.99/45.28      inference('sup-', [status(thm)], ['32', '33'])).
% 44.99/45.28  thf('35', plain,
% 44.99/45.28      (((g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) = (sk_D))),
% 44.99/45.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 44.99/45.28  thf('36', plain,
% 44.99/45.28      (![X28 : $i]: ((m1_pre_topc @ X28 @ X28) | ~ (l1_pre_topc @ X28))),
% 44.99/45.28      inference('cnf', [status(esa)], [t2_tsep_1])).
% 44.99/45.28  thf('37', plain,
% 44.99/45.28      (![X18 : $i, X19 : $i]:
% 44.99/45.28         (~ (l1_pre_topc @ X18)
% 44.99/45.28          | ~ (m1_pre_topc @ X19 @ X18)
% 44.99/45.28          | (m1_pre_topc @ X19 @ 
% 44.99/45.28             (g1_pre_topc @ (u1_struct_0 @ X18) @ (u1_pre_topc @ X18)))
% 44.99/45.28          | ~ (l1_pre_topc @ X19))),
% 44.99/45.28      inference('cnf', [status(esa)], [t65_pre_topc])).
% 44.99/45.28  thf('38', plain,
% 44.99/45.28      (![X0 : $i]:
% 44.99/45.28         (~ (l1_pre_topc @ X0)
% 44.99/45.28          | ~ (l1_pre_topc @ X0)
% 44.99/45.28          | (m1_pre_topc @ X0 @ 
% 44.99/45.28             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 44.99/45.28          | ~ (l1_pre_topc @ X0))),
% 44.99/45.28      inference('sup-', [status(thm)], ['36', '37'])).
% 44.99/45.28  thf('39', plain,
% 44.99/45.28      (![X0 : $i]:
% 44.99/45.28         ((m1_pre_topc @ X0 @ 
% 44.99/45.28           (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 44.99/45.28          | ~ (l1_pre_topc @ X0))),
% 44.99/45.28      inference('simplify', [status(thm)], ['38'])).
% 44.99/45.28  thf('40', plain,
% 44.99/45.28      (![X26 : $i, X27 : $i]:
% 44.99/45.28         (~ (m1_pre_topc @ X26 @ X27)
% 44.99/45.28          | (m1_subset_1 @ (u1_struct_0 @ X26) @ 
% 44.99/45.28             (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 44.99/45.28          | ~ (l1_pre_topc @ X27))),
% 44.99/45.28      inference('cnf', [status(esa)], [t1_tsep_1])).
% 44.99/45.28  thf('41', plain,
% 44.99/45.28      (![X0 : $i]:
% 44.99/45.28         (~ (l1_pre_topc @ X0)
% 44.99/45.28          | ~ (l1_pre_topc @ 
% 44.99/45.28               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 44.99/45.28          | (m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 44.99/45.28             (k1_zfmisc_1 @ 
% 44.99/45.28              (u1_struct_0 @ 
% 44.99/45.28               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))))),
% 44.99/45.28      inference('sup-', [status(thm)], ['39', '40'])).
% 44.99/45.28  thf('42', plain,
% 44.99/45.28      ((~ (l1_pre_topc @ sk_D)
% 44.99/45.28        | (m1_subset_1 @ (u1_struct_0 @ sk_C) @ 
% 44.99/45.28           (k1_zfmisc_1 @ 
% 44.99/45.28            (u1_struct_0 @ 
% 44.99/45.28             (g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)))))
% 44.99/45.28        | ~ (l1_pre_topc @ sk_C))),
% 44.99/45.28      inference('sup-', [status(thm)], ['35', '41'])).
% 44.99/45.28  thf('43', plain, ((l1_pre_topc @ sk_D)),
% 44.99/45.28      inference('demod', [status(thm)], ['17', '18'])).
% 44.99/45.28  thf('44', plain,
% 44.99/45.28      (((g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) = (sk_D))),
% 44.99/45.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 44.99/45.28  thf('45', plain, ((l1_pre_topc @ sk_C)),
% 44.99/45.28      inference('demod', [status(thm)], ['23', '24'])).
% 44.99/45.28  thf('46', plain,
% 44.99/45.28      ((m1_subset_1 @ (u1_struct_0 @ sk_C) @ 
% 44.99/45.28        (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))),
% 44.99/45.28      inference('demod', [status(thm)], ['42', '43', '44', '45'])).
% 44.99/45.28  thf('47', plain,
% 44.99/45.28      (![X5 : $i, X6 : $i]:
% 44.99/45.28         ((r1_tarski @ X5 @ X6) | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6)))),
% 44.99/45.28      inference('cnf', [status(esa)], [t3_subset])).
% 44.99/45.28  thf('48', plain, ((r1_tarski @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D))),
% 44.99/45.28      inference('sup-', [status(thm)], ['46', '47'])).
% 44.99/45.28  thf('49', plain, (((u1_struct_0 @ sk_C) = (u1_struct_0 @ sk_D))),
% 44.99/45.28      inference('demod', [status(thm)], ['34', '48'])).
% 44.99/45.28  thf('50', plain,
% 44.99/45.28      ((m1_subset_1 @ sk_E @ 
% 44.99/45.28        (k1_zfmisc_1 @ 
% 44.99/45.28         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 44.99/45.28      inference('demod', [status(thm)], ['8', '49'])).
% 44.99/45.28  thf(d3_struct_0, axiom,
% 44.99/45.28    (![A:$i]:
% 44.99/45.28     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 44.99/45.28  thf('51', plain,
% 44.99/45.28      (![X13 : $i]:
% 44.99/45.28         (((k2_struct_0 @ X13) = (u1_struct_0 @ X13)) | ~ (l1_struct_0 @ X13))),
% 44.99/45.28      inference('cnf', [status(esa)], [d3_struct_0])).
% 44.99/45.28  thf('52', plain, (((u1_struct_0 @ sk_C) = (u1_struct_0 @ sk_D))),
% 44.99/45.28      inference('demod', [status(thm)], ['34', '48'])).
% 44.99/45.28  thf('53', plain,
% 44.99/45.28      ((((u1_struct_0 @ sk_C) = (k2_struct_0 @ sk_D)) | ~ (l1_struct_0 @ sk_D))),
% 44.99/45.28      inference('sup+', [status(thm)], ['51', '52'])).
% 44.99/45.28  thf('54', plain, ((l1_pre_topc @ sk_D)),
% 44.99/45.28      inference('demod', [status(thm)], ['17', '18'])).
% 44.99/45.28  thf(dt_l1_pre_topc, axiom,
% 44.99/45.28    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 44.99/45.28  thf('55', plain,
% 44.99/45.28      (![X14 : $i]: ((l1_struct_0 @ X14) | ~ (l1_pre_topc @ X14))),
% 44.99/45.28      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 44.99/45.28  thf('56', plain, ((l1_struct_0 @ sk_D)),
% 44.99/45.28      inference('sup-', [status(thm)], ['54', '55'])).
% 44.99/45.28  thf('57', plain, (((u1_struct_0 @ sk_C) = (k2_struct_0 @ sk_D))),
% 44.99/45.28      inference('demod', [status(thm)], ['53', '56'])).
% 44.99/45.28  thf('58', plain,
% 44.99/45.28      (![X13 : $i]:
% 44.99/45.28         (((k2_struct_0 @ X13) = (u1_struct_0 @ X13)) | ~ (l1_struct_0 @ X13))),
% 44.99/45.28      inference('cnf', [status(esa)], [d3_struct_0])).
% 44.99/45.28  thf('59', plain, (((u1_struct_0 @ sk_C) = (k2_struct_0 @ sk_D))),
% 44.99/45.28      inference('demod', [status(thm)], ['53', '56'])).
% 44.99/45.28  thf('60', plain,
% 44.99/45.28      ((((k2_struct_0 @ sk_C) = (k2_struct_0 @ sk_D)) | ~ (l1_struct_0 @ sk_C))),
% 44.99/45.28      inference('sup+', [status(thm)], ['58', '59'])).
% 44.99/45.28  thf('61', plain, ((l1_pre_topc @ sk_C)),
% 44.99/45.28      inference('demod', [status(thm)], ['23', '24'])).
% 44.99/45.28  thf('62', plain,
% 44.99/45.28      (![X14 : $i]: ((l1_struct_0 @ X14) | ~ (l1_pre_topc @ X14))),
% 44.99/45.28      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 44.99/45.28  thf('63', plain, ((l1_struct_0 @ sk_C)),
% 44.99/45.28      inference('sup-', [status(thm)], ['61', '62'])).
% 44.99/45.28  thf('64', plain, (((k2_struct_0 @ sk_C) = (k2_struct_0 @ sk_D))),
% 44.99/45.28      inference('demod', [status(thm)], ['60', '63'])).
% 44.99/45.28  thf('65', plain, (((u1_struct_0 @ sk_C) = (k2_struct_0 @ sk_C))),
% 44.99/45.28      inference('demod', [status(thm)], ['57', '64'])).
% 44.99/45.28  thf('66', plain,
% 44.99/45.28      ((m1_subset_1 @ sk_E @ 
% 44.99/45.28        (k1_zfmisc_1 @ 
% 44.99/45.28         (k2_zfmisc_1 @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 44.99/45.28      inference('demod', [status(thm)], ['50', '65'])).
% 44.99/45.28  thf('67', plain, (((u1_struct_0 @ sk_C) = (u1_struct_0 @ sk_D))),
% 44.99/45.28      inference('demod', [status(thm)], ['34', '48'])).
% 44.99/45.28  thf('68', plain, (((u1_struct_0 @ sk_C) = (k2_struct_0 @ sk_D))),
% 44.99/45.28      inference('demod', [status(thm)], ['53', '56'])).
% 44.99/45.28  thf('69', plain, (((k2_struct_0 @ sk_D) = (u1_struct_0 @ sk_D))),
% 44.99/45.28      inference('demod', [status(thm)], ['67', '68'])).
% 44.99/45.28  thf('70', plain, (((k2_struct_0 @ sk_C) = (k2_struct_0 @ sk_D))),
% 44.99/45.28      inference('demod', [status(thm)], ['60', '63'])).
% 44.99/45.28  thf('71', plain, (((k2_struct_0 @ sk_C) = (u1_struct_0 @ sk_D))),
% 44.99/45.28      inference('demod', [status(thm)], ['69', '70'])).
% 44.99/45.28  thf(t83_tmap_1, axiom,
% 44.99/45.28    (![A:$i]:
% 44.99/45.28     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 44.99/45.28       ( ![B:$i]:
% 44.99/45.28         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 44.99/45.28             ( l1_pre_topc @ B ) ) =>
% 44.99/45.28           ( ![C:$i]:
% 44.99/45.28             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 44.99/45.28               ( ![D:$i]:
% 44.99/45.28                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 44.99/45.28                   ( ![E:$i]:
% 44.99/45.28                     ( ( ( v1_funct_1 @ E ) & 
% 44.99/45.28                         ( v1_funct_2 @
% 44.99/45.28                           E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 44.99/45.28                         ( m1_subset_1 @
% 44.99/45.28                           E @ 
% 44.99/45.28                           ( k1_zfmisc_1 @
% 44.99/45.28                             ( k2_zfmisc_1 @
% 44.99/45.28                               ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 44.99/45.28                       ( ( m1_pre_topc @ C @ D ) =>
% 44.99/45.28                         ( ![F:$i]:
% 44.99/45.28                           ( ( m1_subset_1 @
% 44.99/45.28                               F @ ( k1_zfmisc_1 @ ( u1_struct_0 @ D ) ) ) =>
% 44.99/45.28                             ( ![G:$i]:
% 44.99/45.28                               ( ( m1_subset_1 @ G @ ( u1_struct_0 @ D ) ) =>
% 44.99/45.28                                 ( ![H:$i]:
% 44.99/45.28                                   ( ( m1_subset_1 @ H @ ( u1_struct_0 @ C ) ) =>
% 44.99/45.28                                     ( ( ( r1_tarski @ F @ ( u1_struct_0 @ C ) ) & 
% 44.99/45.28                                         ( m1_connsp_2 @ F @ D @ G ) & 
% 44.99/45.28                                         ( ( G ) = ( H ) ) ) =>
% 44.99/45.28                                       ( ( r1_tmap_1 @ D @ B @ E @ G ) <=>
% 44.99/45.28                                         ( r1_tmap_1 @
% 44.99/45.28                                           C @ B @ 
% 44.99/45.28                                           ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ 
% 44.99/45.28                                           H ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 44.99/45.28  thf('72', plain,
% 44.99/45.28      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i, X36 : $i, X37 : $i, X38 : $i, 
% 44.99/45.28         X39 : $i]:
% 44.99/45.28         ((v2_struct_0 @ X32)
% 44.99/45.28          | ~ (v2_pre_topc @ X32)
% 44.99/45.28          | ~ (l1_pre_topc @ X32)
% 44.99/45.28          | (v2_struct_0 @ X33)
% 44.99/45.28          | ~ (m1_pre_topc @ X33 @ X34)
% 44.99/45.28          | ~ (m1_pre_topc @ X35 @ X33)
% 44.99/45.28          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (u1_struct_0 @ X33)))
% 44.99/45.28          | ~ (m1_subset_1 @ X37 @ (u1_struct_0 @ X35))
% 44.99/45.28          | ~ (r1_tmap_1 @ X35 @ X32 @ 
% 44.99/45.28               (k3_tmap_1 @ X34 @ X32 @ X33 @ X35 @ X38) @ X37)
% 44.99/45.28          | (r1_tmap_1 @ X33 @ X32 @ X38 @ X39)
% 44.99/45.28          | ((X39) != (X37))
% 44.99/45.28          | ~ (m1_connsp_2 @ X36 @ X33 @ X39)
% 44.99/45.28          | ~ (r1_tarski @ X36 @ (u1_struct_0 @ X35))
% 44.99/45.28          | ~ (m1_subset_1 @ X39 @ (u1_struct_0 @ X33))
% 44.99/45.28          | ~ (m1_subset_1 @ X38 @ 
% 44.99/45.28               (k1_zfmisc_1 @ 
% 44.99/45.28                (k2_zfmisc_1 @ (u1_struct_0 @ X33) @ (u1_struct_0 @ X32))))
% 44.99/45.28          | ~ (v1_funct_2 @ X38 @ (u1_struct_0 @ X33) @ (u1_struct_0 @ X32))
% 44.99/45.28          | ~ (v1_funct_1 @ X38)
% 44.99/45.28          | ~ (m1_pre_topc @ X35 @ X34)
% 44.99/45.28          | (v2_struct_0 @ X35)
% 44.99/45.28          | ~ (l1_pre_topc @ X34)
% 44.99/45.28          | ~ (v2_pre_topc @ X34)
% 44.99/45.28          | (v2_struct_0 @ X34))),
% 44.99/45.28      inference('cnf', [status(esa)], [t83_tmap_1])).
% 44.99/45.28  thf('73', plain,
% 44.99/45.28      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i, X36 : $i, X37 : $i, X38 : $i]:
% 44.99/45.28         ((v2_struct_0 @ X34)
% 44.99/45.28          | ~ (v2_pre_topc @ X34)
% 44.99/45.28          | ~ (l1_pre_topc @ X34)
% 44.99/45.28          | (v2_struct_0 @ X35)
% 44.99/45.28          | ~ (m1_pre_topc @ X35 @ X34)
% 44.99/45.28          | ~ (v1_funct_1 @ X38)
% 44.99/45.28          | ~ (v1_funct_2 @ X38 @ (u1_struct_0 @ X33) @ (u1_struct_0 @ X32))
% 44.99/45.28          | ~ (m1_subset_1 @ X38 @ 
% 44.99/45.28               (k1_zfmisc_1 @ 
% 44.99/45.28                (k2_zfmisc_1 @ (u1_struct_0 @ X33) @ (u1_struct_0 @ X32))))
% 44.99/45.28          | ~ (m1_subset_1 @ X37 @ (u1_struct_0 @ X33))
% 44.99/45.28          | ~ (r1_tarski @ X36 @ (u1_struct_0 @ X35))
% 44.99/45.28          | ~ (m1_connsp_2 @ X36 @ X33 @ X37)
% 44.99/45.28          | (r1_tmap_1 @ X33 @ X32 @ X38 @ X37)
% 44.99/45.28          | ~ (r1_tmap_1 @ X35 @ X32 @ 
% 44.99/45.28               (k3_tmap_1 @ X34 @ X32 @ X33 @ X35 @ X38) @ X37)
% 44.99/45.28          | ~ (m1_subset_1 @ X37 @ (u1_struct_0 @ X35))
% 44.99/45.28          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (u1_struct_0 @ X33)))
% 44.99/45.28          | ~ (m1_pre_topc @ X35 @ X33)
% 44.99/45.28          | ~ (m1_pre_topc @ X33 @ X34)
% 44.99/45.28          | (v2_struct_0 @ X33)
% 44.99/45.28          | ~ (l1_pre_topc @ X32)
% 44.99/45.28          | ~ (v2_pre_topc @ X32)
% 44.99/45.28          | (v2_struct_0 @ X32))),
% 44.99/45.28      inference('simplify', [status(thm)], ['72'])).
% 44.99/45.28  thf('74', plain,
% 44.99/45.28      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 44.99/45.28         (~ (m1_subset_1 @ X1 @ 
% 44.99/45.28             (k1_zfmisc_1 @ 
% 44.99/45.28              (k2_zfmisc_1 @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ X0))))
% 44.99/45.28          | (v2_struct_0 @ X0)
% 44.99/45.28          | ~ (v2_pre_topc @ X0)
% 44.99/45.28          | ~ (l1_pre_topc @ X0)
% 44.99/45.28          | (v2_struct_0 @ sk_D)
% 44.99/45.28          | ~ (m1_pre_topc @ sk_D @ X2)
% 44.99/45.28          | ~ (m1_pre_topc @ X3 @ sk_D)
% 44.99/45.28          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))
% 44.99/45.28          | ~ (m1_subset_1 @ X5 @ (u1_struct_0 @ X3))
% 44.99/45.28          | ~ (r1_tmap_1 @ X3 @ X0 @ (k3_tmap_1 @ X2 @ X0 @ sk_D @ X3 @ X1) @ 
% 44.99/45.28               X5)
% 44.99/45.28          | (r1_tmap_1 @ sk_D @ X0 @ X1 @ X5)
% 44.99/45.28          | ~ (m1_connsp_2 @ X4 @ sk_D @ X5)
% 44.99/45.28          | ~ (r1_tarski @ X4 @ (u1_struct_0 @ X3))
% 44.99/45.28          | ~ (m1_subset_1 @ X5 @ (u1_struct_0 @ sk_D))
% 44.99/45.28          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ X0))
% 44.99/45.28          | ~ (v1_funct_1 @ X1)
% 44.99/45.28          | ~ (m1_pre_topc @ X3 @ X2)
% 44.99/45.28          | (v2_struct_0 @ X3)
% 44.99/45.28          | ~ (l1_pre_topc @ X2)
% 44.99/45.28          | ~ (v2_pre_topc @ X2)
% 44.99/45.28          | (v2_struct_0 @ X2))),
% 44.99/45.28      inference('sup-', [status(thm)], ['71', '73'])).
% 44.99/45.28  thf('75', plain, (((k2_struct_0 @ sk_C) = (u1_struct_0 @ sk_D))),
% 44.99/45.28      inference('demod', [status(thm)], ['69', '70'])).
% 44.99/45.28  thf('76', plain, (((k2_struct_0 @ sk_C) = (u1_struct_0 @ sk_D))),
% 44.99/45.28      inference('demod', [status(thm)], ['69', '70'])).
% 44.99/45.28  thf('77', plain, (((k2_struct_0 @ sk_C) = (u1_struct_0 @ sk_D))),
% 44.99/45.28      inference('demod', [status(thm)], ['69', '70'])).
% 44.99/45.28  thf('78', plain,
% 44.99/45.28      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 44.99/45.28         (~ (m1_subset_1 @ X1 @ 
% 44.99/45.28             (k1_zfmisc_1 @ 
% 44.99/45.28              (k2_zfmisc_1 @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ X0))))
% 44.99/45.28          | (v2_struct_0 @ X0)
% 44.99/45.28          | ~ (v2_pre_topc @ X0)
% 44.99/45.28          | ~ (l1_pre_topc @ X0)
% 44.99/45.28          | (v2_struct_0 @ sk_D)
% 44.99/45.28          | ~ (m1_pre_topc @ sk_D @ X2)
% 44.99/45.28          | ~ (m1_pre_topc @ X3 @ sk_D)
% 44.99/45.28          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_C)))
% 44.99/45.28          | ~ (m1_subset_1 @ X5 @ (u1_struct_0 @ X3))
% 44.99/45.28          | ~ (r1_tmap_1 @ X3 @ X0 @ (k3_tmap_1 @ X2 @ X0 @ sk_D @ X3 @ X1) @ 
% 44.99/45.28               X5)
% 44.99/45.28          | (r1_tmap_1 @ sk_D @ X0 @ X1 @ X5)
% 44.99/45.28          | ~ (m1_connsp_2 @ X4 @ sk_D @ X5)
% 44.99/45.28          | ~ (r1_tarski @ X4 @ (u1_struct_0 @ X3))
% 44.99/45.28          | ~ (m1_subset_1 @ X5 @ (k2_struct_0 @ sk_C))
% 44.99/45.28          | ~ (v1_funct_2 @ X1 @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ X0))
% 44.99/45.28          | ~ (v1_funct_1 @ X1)
% 44.99/45.28          | ~ (m1_pre_topc @ X3 @ X2)
% 44.99/45.28          | (v2_struct_0 @ X3)
% 44.99/45.28          | ~ (l1_pre_topc @ X2)
% 44.99/45.28          | ~ (v2_pre_topc @ X2)
% 44.99/45.28          | (v2_struct_0 @ X2))),
% 44.99/45.28      inference('demod', [status(thm)], ['74', '75', '76', '77'])).
% 44.99/45.28  thf('79', plain,
% 44.99/45.28      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 44.99/45.28         ((v2_struct_0 @ X0)
% 44.99/45.28          | ~ (v2_pre_topc @ X0)
% 44.99/45.28          | ~ (l1_pre_topc @ X0)
% 44.99/45.28          | (v2_struct_0 @ X1)
% 44.99/45.28          | ~ (m1_pre_topc @ X1 @ X0)
% 44.99/45.28          | ~ (v1_funct_1 @ sk_E)
% 44.99/45.28          | ~ (v1_funct_2 @ sk_E @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))
% 44.99/45.28          | ~ (m1_subset_1 @ X2 @ (k2_struct_0 @ sk_C))
% 44.99/45.28          | ~ (r1_tarski @ X3 @ (u1_struct_0 @ X1))
% 44.99/45.28          | ~ (m1_connsp_2 @ X3 @ sk_D @ X2)
% 44.99/45.28          | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X2)
% 44.99/45.28          | ~ (r1_tmap_1 @ X1 @ sk_B @ 
% 44.99/45.28               (k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E) @ X2)
% 44.99/45.28          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1))
% 44.99/45.28          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_C)))
% 44.99/45.28          | ~ (m1_pre_topc @ X1 @ sk_D)
% 44.99/45.28          | ~ (m1_pre_topc @ sk_D @ X0)
% 44.99/45.28          | (v2_struct_0 @ sk_D)
% 44.99/45.28          | ~ (l1_pre_topc @ sk_B)
% 44.99/45.28          | ~ (v2_pre_topc @ sk_B)
% 44.99/45.28          | (v2_struct_0 @ sk_B))),
% 44.99/45.28      inference('sup-', [status(thm)], ['66', '78'])).
% 44.99/45.28  thf('80', plain, ((v1_funct_1 @ sk_E)),
% 44.99/45.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 44.99/45.28  thf('81', plain,
% 44.99/45.28      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 44.99/45.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 44.99/45.28  thf('82', plain, (((u1_struct_0 @ sk_C) = (u1_struct_0 @ sk_D))),
% 44.99/45.28      inference('demod', [status(thm)], ['34', '48'])).
% 44.99/45.28  thf('83', plain,
% 44.99/45.28      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 44.99/45.28      inference('demod', [status(thm)], ['81', '82'])).
% 44.99/45.28  thf('84', plain, (((u1_struct_0 @ sk_C) = (k2_struct_0 @ sk_C))),
% 44.99/45.28      inference('demod', [status(thm)], ['57', '64'])).
% 44.99/45.28  thf('85', plain,
% 44.99/45.28      ((v1_funct_2 @ sk_E @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 44.99/45.28      inference('demod', [status(thm)], ['83', '84'])).
% 44.99/45.28  thf('86', plain, ((l1_pre_topc @ sk_B)),
% 44.99/45.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 44.99/45.28  thf('87', plain, ((v2_pre_topc @ sk_B)),
% 44.99/45.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 44.99/45.28  thf('88', plain,
% 44.99/45.28      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 44.99/45.28         ((v2_struct_0 @ X0)
% 44.99/45.28          | ~ (v2_pre_topc @ X0)
% 44.99/45.28          | ~ (l1_pre_topc @ X0)
% 44.99/45.28          | (v2_struct_0 @ X1)
% 44.99/45.28          | ~ (m1_pre_topc @ X1 @ X0)
% 44.99/45.28          | ~ (m1_subset_1 @ X2 @ (k2_struct_0 @ sk_C))
% 44.99/45.28          | ~ (r1_tarski @ X3 @ (u1_struct_0 @ X1))
% 44.99/45.28          | ~ (m1_connsp_2 @ X3 @ sk_D @ X2)
% 44.99/45.28          | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X2)
% 44.99/45.28          | ~ (r1_tmap_1 @ X1 @ sk_B @ 
% 44.99/45.28               (k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E) @ X2)
% 44.99/45.28          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1))
% 44.99/45.28          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_C)))
% 44.99/45.28          | ~ (m1_pre_topc @ X1 @ sk_D)
% 44.99/45.28          | ~ (m1_pre_topc @ sk_D @ X0)
% 44.99/45.28          | (v2_struct_0 @ sk_D)
% 44.99/45.28          | (v2_struct_0 @ sk_B))),
% 44.99/45.28      inference('demod', [status(thm)], ['79', '80', '85', '86', '87'])).
% 44.99/45.28  thf('89', plain,
% 44.99/45.28      (![X0 : $i]:
% 44.99/45.28         ((v2_struct_0 @ sk_B)
% 44.99/45.28          | (v2_struct_0 @ sk_D)
% 44.99/45.28          | ~ (m1_pre_topc @ sk_D @ sk_A)
% 44.99/45.28          | ~ (m1_pre_topc @ sk_C @ sk_D)
% 44.99/45.28          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_C)))
% 44.99/45.28          | ~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C))
% 44.99/45.28          | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)
% 44.99/45.28          | ~ (m1_connsp_2 @ X0 @ sk_D @ sk_F)
% 44.99/45.28          | ~ (r1_tarski @ X0 @ (u1_struct_0 @ sk_C))
% 44.99/45.28          | ~ (m1_subset_1 @ sk_F @ (k2_struct_0 @ sk_C))
% 44.99/45.28          | ~ (m1_pre_topc @ sk_C @ sk_A)
% 44.99/45.28          | (v2_struct_0 @ sk_C)
% 44.99/45.28          | ~ (l1_pre_topc @ sk_A)
% 44.99/45.28          | ~ (v2_pre_topc @ sk_A)
% 44.99/45.28          | (v2_struct_0 @ sk_A))),
% 44.99/45.28      inference('sup-', [status(thm)], ['7', '88'])).
% 44.99/45.28  thf('90', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 44.99/45.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 44.99/45.28  thf('91', plain,
% 44.99/45.28      (((g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) = (sk_D))),
% 44.99/45.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 44.99/45.28  thf('92', plain,
% 44.99/45.28      (![X0 : $i]:
% 44.99/45.28         ((m1_pre_topc @ X0 @ 
% 44.99/45.28           (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 44.99/45.28          | ~ (l1_pre_topc @ X0))),
% 44.99/45.28      inference('simplify', [status(thm)], ['38'])).
% 44.99/45.28  thf('93', plain, (((m1_pre_topc @ sk_C @ sk_D) | ~ (l1_pre_topc @ sk_C))),
% 44.99/45.28      inference('sup+', [status(thm)], ['91', '92'])).
% 44.99/45.28  thf('94', plain, ((l1_pre_topc @ sk_C)),
% 44.99/45.28      inference('demod', [status(thm)], ['23', '24'])).
% 44.99/45.28  thf('95', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 44.99/45.28      inference('demod', [status(thm)], ['93', '94'])).
% 44.99/45.28  thf('96', plain, (((u1_struct_0 @ sk_C) = (k2_struct_0 @ sk_C))),
% 44.99/45.28      inference('demod', [status(thm)], ['57', '64'])).
% 44.99/45.28  thf('97', plain,
% 44.99/45.28      (![X13 : $i]:
% 44.99/45.28         (((k2_struct_0 @ X13) = (u1_struct_0 @ X13)) | ~ (l1_struct_0 @ X13))),
% 44.99/45.28      inference('cnf', [status(esa)], [d3_struct_0])).
% 44.99/45.28  thf('98', plain, ((m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_C))),
% 44.99/45.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 44.99/45.28  thf('99', plain, (((sk_F) = (sk_G))),
% 44.99/45.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 44.99/45.28  thf('100', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C))),
% 44.99/45.28      inference('demod', [status(thm)], ['98', '99'])).
% 44.99/45.28  thf('101', plain,
% 44.99/45.28      (((m1_subset_1 @ sk_F @ (k2_struct_0 @ sk_C)) | ~ (l1_struct_0 @ sk_C))),
% 44.99/45.28      inference('sup+', [status(thm)], ['97', '100'])).
% 44.99/45.28  thf('102', plain, ((l1_struct_0 @ sk_C)),
% 44.99/45.28      inference('sup-', [status(thm)], ['61', '62'])).
% 44.99/45.28  thf('103', plain, ((m1_subset_1 @ sk_F @ (k2_struct_0 @ sk_C))),
% 44.99/45.28      inference('demod', [status(thm)], ['101', '102'])).
% 44.99/45.28  thf('104', plain, (((u1_struct_0 @ sk_C) = (k2_struct_0 @ sk_C))),
% 44.99/45.28      inference('demod', [status(thm)], ['57', '64'])).
% 44.99/45.28  thf('105', plain, ((m1_subset_1 @ sk_F @ (k2_struct_0 @ sk_C))),
% 44.99/45.28      inference('demod', [status(thm)], ['101', '102'])).
% 44.99/45.28  thf('106', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 44.99/45.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 44.99/45.28  thf('107', plain, ((l1_pre_topc @ sk_A)),
% 44.99/45.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 44.99/45.28  thf('108', plain, ((v2_pre_topc @ sk_A)),
% 44.99/45.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 44.99/45.28  thf('109', plain,
% 44.99/45.28      (![X0 : $i]:
% 44.99/45.28         ((v2_struct_0 @ sk_B)
% 44.99/45.28          | (v2_struct_0 @ sk_D)
% 44.99/45.28          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_C)))
% 44.99/45.28          | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)
% 44.99/45.28          | ~ (m1_connsp_2 @ X0 @ sk_D @ sk_F)
% 44.99/45.28          | ~ (r1_tarski @ X0 @ (k2_struct_0 @ sk_C))
% 44.99/45.28          | (v2_struct_0 @ sk_C)
% 44.99/45.28          | (v2_struct_0 @ sk_A))),
% 44.99/45.28      inference('demod', [status(thm)],
% 44.99/45.28                ['89', '90', '95', '96', '103', '104', '105', '106', '107', 
% 44.99/45.28                 '108'])).
% 44.99/45.28  thf('110', plain,
% 44.99/45.28      (((v2_struct_0 @ sk_A)
% 44.99/45.28        | (v2_struct_0 @ sk_C)
% 44.99/45.28        | ~ (r1_tarski @ (k2_struct_0 @ sk_C) @ (k2_struct_0 @ sk_C))
% 44.99/45.28        | ~ (m1_connsp_2 @ (k2_struct_0 @ sk_C) @ sk_D @ sk_F)
% 44.99/45.28        | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)
% 44.99/45.28        | (v2_struct_0 @ sk_D)
% 44.99/45.28        | (v2_struct_0 @ sk_B))),
% 44.99/45.28      inference('sup-', [status(thm)], ['4', '109'])).
% 44.99/45.28  thf('111', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 44.99/45.28      inference('simplify', [status(thm)], ['1'])).
% 44.99/45.28  thf('112', plain,
% 44.99/45.28      (![X13 : $i]:
% 44.99/45.28         (((k2_struct_0 @ X13) = (u1_struct_0 @ X13)) | ~ (l1_struct_0 @ X13))),
% 44.99/45.28      inference('cnf', [status(esa)], [d3_struct_0])).
% 44.99/45.28  thf('113', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_D))),
% 44.99/45.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 44.99/45.28  thf('114', plain,
% 44.99/45.28      (((m1_subset_1 @ sk_F @ (k2_struct_0 @ sk_D)) | ~ (l1_struct_0 @ sk_D))),
% 44.99/45.28      inference('sup+', [status(thm)], ['112', '113'])).
% 44.99/45.28  thf('115', plain, ((l1_struct_0 @ sk_D)),
% 44.99/45.28      inference('sup-', [status(thm)], ['54', '55'])).
% 44.99/45.28  thf('116', plain, ((m1_subset_1 @ sk_F @ (k2_struct_0 @ sk_D))),
% 44.99/45.28      inference('demod', [status(thm)], ['114', '115'])).
% 44.99/45.28  thf('117', plain,
% 44.99/45.28      (![X13 : $i]:
% 44.99/45.28         (((k2_struct_0 @ X13) = (u1_struct_0 @ X13)) | ~ (l1_struct_0 @ X13))),
% 44.99/45.28      inference('cnf', [status(esa)], [d3_struct_0])).
% 44.99/45.28  thf('118', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 44.99/45.28      inference('sup-', [status(thm)], ['2', '3'])).
% 44.99/45.28  thf(t5_connsp_2, axiom,
% 44.99/45.28    (![A:$i]:
% 44.99/45.28     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 44.99/45.28       ( ![B:$i]:
% 44.99/45.28         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 44.99/45.28           ( ![C:$i]:
% 44.99/45.28             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 44.99/45.28               ( ( ( v3_pre_topc @ B @ A ) & ( r2_hidden @ C @ B ) ) =>
% 44.99/45.28                 ( m1_connsp_2 @ B @ A @ C ) ) ) ) ) ) ))).
% 44.99/45.28  thf('119', plain,
% 44.99/45.28      (![X21 : $i, X22 : $i, X23 : $i]:
% 44.99/45.28         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 44.99/45.28          | ~ (v3_pre_topc @ X21 @ X22)
% 44.99/45.28          | ~ (r2_hidden @ X23 @ X21)
% 44.99/45.28          | (m1_connsp_2 @ X21 @ X22 @ X23)
% 44.99/45.28          | ~ (m1_subset_1 @ X23 @ (u1_struct_0 @ X22))
% 44.99/45.28          | ~ (l1_pre_topc @ X22)
% 44.99/45.28          | ~ (v2_pre_topc @ X22)
% 44.99/45.28          | (v2_struct_0 @ X22))),
% 44.99/45.28      inference('cnf', [status(esa)], [t5_connsp_2])).
% 44.99/45.28  thf('120', plain,
% 44.99/45.28      (![X0 : $i, X1 : $i]:
% 44.99/45.28         ((v2_struct_0 @ X0)
% 44.99/45.28          | ~ (v2_pre_topc @ X0)
% 44.99/45.28          | ~ (l1_pre_topc @ X0)
% 44.99/45.28          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 44.99/45.28          | (m1_connsp_2 @ (u1_struct_0 @ X0) @ X0 @ X1)
% 44.99/45.28          | ~ (r2_hidden @ X1 @ (u1_struct_0 @ X0))
% 44.99/45.28          | ~ (v3_pre_topc @ (u1_struct_0 @ X0) @ X0))),
% 44.99/45.28      inference('sup-', [status(thm)], ['118', '119'])).
% 44.99/45.28  thf('121', plain,
% 44.99/45.28      (![X0 : $i, X1 : $i]:
% 44.99/45.28         (~ (m1_subset_1 @ X1 @ (k2_struct_0 @ X0))
% 44.99/45.28          | ~ (l1_struct_0 @ X0)
% 44.99/45.28          | ~ (v3_pre_topc @ (u1_struct_0 @ X0) @ X0)
% 44.99/45.28          | ~ (r2_hidden @ X1 @ (u1_struct_0 @ X0))
% 44.99/45.28          | (m1_connsp_2 @ (u1_struct_0 @ X0) @ X0 @ X1)
% 44.99/45.28          | ~ (l1_pre_topc @ X0)
% 44.99/45.28          | ~ (v2_pre_topc @ X0)
% 44.99/45.28          | (v2_struct_0 @ X0))),
% 44.99/45.28      inference('sup-', [status(thm)], ['117', '120'])).
% 44.99/45.28  thf('122', plain,
% 44.99/45.28      (((v2_struct_0 @ sk_D)
% 44.99/45.28        | ~ (v2_pre_topc @ sk_D)
% 44.99/45.28        | ~ (l1_pre_topc @ sk_D)
% 44.99/45.28        | (m1_connsp_2 @ (u1_struct_0 @ sk_D) @ sk_D @ sk_F)
% 44.99/45.28        | ~ (r2_hidden @ sk_F @ (u1_struct_0 @ sk_D))
% 44.99/45.28        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_D) @ sk_D)
% 44.99/45.28        | ~ (l1_struct_0 @ sk_D))),
% 44.99/45.28      inference('sup-', [status(thm)], ['116', '121'])).
% 44.99/45.28  thf('123', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 44.99/45.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 44.99/45.28  thf(cc1_pre_topc, axiom,
% 44.99/45.28    (![A:$i]:
% 44.99/45.28     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 44.99/45.28       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( v2_pre_topc @ B ) ) ) ))).
% 44.99/45.28  thf('124', plain,
% 44.99/45.28      (![X11 : $i, X12 : $i]:
% 44.99/45.28         (~ (m1_pre_topc @ X11 @ X12)
% 44.99/45.28          | (v2_pre_topc @ X11)
% 44.99/45.28          | ~ (l1_pre_topc @ X12)
% 44.99/45.28          | ~ (v2_pre_topc @ X12))),
% 44.99/45.28      inference('cnf', [status(esa)], [cc1_pre_topc])).
% 44.99/45.28  thf('125', plain,
% 44.99/45.28      ((~ (v2_pre_topc @ sk_A) | ~ (l1_pre_topc @ sk_A) | (v2_pre_topc @ sk_D))),
% 44.99/45.28      inference('sup-', [status(thm)], ['123', '124'])).
% 44.99/45.28  thf('126', plain, ((v2_pre_topc @ sk_A)),
% 44.99/45.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 44.99/45.28  thf('127', plain, ((l1_pre_topc @ sk_A)),
% 44.99/45.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 44.99/45.28  thf('128', plain, ((v2_pre_topc @ sk_D)),
% 44.99/45.28      inference('demod', [status(thm)], ['125', '126', '127'])).
% 44.99/45.28  thf('129', plain, ((l1_pre_topc @ sk_D)),
% 44.99/45.28      inference('demod', [status(thm)], ['17', '18'])).
% 44.99/45.28  thf('130', plain, (((u1_struct_0 @ sk_C) = (u1_struct_0 @ sk_D))),
% 44.99/45.28      inference('demod', [status(thm)], ['34', '48'])).
% 44.99/45.28  thf('131', plain, (((u1_struct_0 @ sk_C) = (u1_struct_0 @ sk_D))),
% 44.99/45.28      inference('demod', [status(thm)], ['34', '48'])).
% 44.99/45.28  thf('132', plain, (((u1_struct_0 @ sk_C) = (u1_struct_0 @ sk_D))),
% 44.99/45.28      inference('demod', [status(thm)], ['34', '48'])).
% 44.99/45.28  thf('133', plain, ((l1_struct_0 @ sk_D)),
% 44.99/45.28      inference('sup-', [status(thm)], ['54', '55'])).
% 44.99/45.28  thf('134', plain,
% 44.99/45.28      (((v2_struct_0 @ sk_D)
% 44.99/45.28        | (m1_connsp_2 @ (u1_struct_0 @ sk_C) @ sk_D @ sk_F)
% 44.99/45.28        | ~ (r2_hidden @ sk_F @ (u1_struct_0 @ sk_C))
% 44.99/45.28        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_C) @ sk_D))),
% 44.99/45.28      inference('demod', [status(thm)],
% 44.99/45.28                ['122', '128', '129', '130', '131', '132', '133'])).
% 44.99/45.28  thf('135', plain, (((u1_struct_0 @ sk_C) = (k2_struct_0 @ sk_C))),
% 44.99/45.28      inference('demod', [status(thm)], ['57', '64'])).
% 44.99/45.28  thf('136', plain, (((u1_struct_0 @ sk_C) = (k2_struct_0 @ sk_C))),
% 44.99/45.28      inference('demod', [status(thm)], ['57', '64'])).
% 44.99/45.28  thf('137', plain,
% 44.99/45.28      (![X13 : $i]:
% 44.99/45.28         (((k2_struct_0 @ X13) = (u1_struct_0 @ X13)) | ~ (l1_struct_0 @ X13))),
% 44.99/45.28      inference('cnf', [status(esa)], [d3_struct_0])).
% 44.99/45.28  thf('138', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C))),
% 44.99/45.28      inference('demod', [status(thm)], ['98', '99'])).
% 44.99/45.28  thf(t2_subset, axiom,
% 44.99/45.28    (![A:$i,B:$i]:
% 44.99/45.28     ( ( m1_subset_1 @ A @ B ) =>
% 44.99/45.28       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 44.99/45.28  thf('139', plain,
% 44.99/45.28      (![X3 : $i, X4 : $i]:
% 44.99/45.28         ((r2_hidden @ X3 @ X4)
% 44.99/45.28          | (v1_xboole_0 @ X4)
% 44.99/45.28          | ~ (m1_subset_1 @ X3 @ X4))),
% 44.99/45.28      inference('cnf', [status(esa)], [t2_subset])).
% 44.99/45.28  thf('140', plain,
% 44.99/45.28      (((v1_xboole_0 @ (u1_struct_0 @ sk_C))
% 44.99/45.28        | (r2_hidden @ sk_F @ (u1_struct_0 @ sk_C)))),
% 44.99/45.28      inference('sup-', [status(thm)], ['138', '139'])).
% 44.99/45.28  thf('141', plain,
% 44.99/45.28      (((r2_hidden @ sk_F @ (k2_struct_0 @ sk_C))
% 44.99/45.28        | ~ (l1_struct_0 @ sk_C)
% 44.99/45.28        | (v1_xboole_0 @ (u1_struct_0 @ sk_C)))),
% 44.99/45.28      inference('sup+', [status(thm)], ['137', '140'])).
% 44.99/45.28  thf('142', plain, ((l1_struct_0 @ sk_C)),
% 44.99/45.28      inference('sup-', [status(thm)], ['61', '62'])).
% 44.99/45.28  thf('143', plain,
% 44.99/45.28      (((r2_hidden @ sk_F @ (k2_struct_0 @ sk_C))
% 44.99/45.28        | (v1_xboole_0 @ (u1_struct_0 @ sk_C)))),
% 44.99/45.28      inference('demod', [status(thm)], ['141', '142'])).
% 44.99/45.28  thf(fc2_struct_0, axiom,
% 44.99/45.28    (![A:$i]:
% 44.99/45.28     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 44.99/45.28       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 44.99/45.28  thf('144', plain,
% 44.99/45.28      (![X17 : $i]:
% 44.99/45.28         (~ (v1_xboole_0 @ (u1_struct_0 @ X17))
% 44.99/45.28          | ~ (l1_struct_0 @ X17)
% 44.99/45.28          | (v2_struct_0 @ X17))),
% 44.99/45.28      inference('cnf', [status(esa)], [fc2_struct_0])).
% 44.99/45.28  thf('145', plain,
% 44.99/45.28      (((r2_hidden @ sk_F @ (k2_struct_0 @ sk_C))
% 44.99/45.28        | (v2_struct_0 @ sk_C)
% 44.99/45.28        | ~ (l1_struct_0 @ sk_C))),
% 44.99/45.28      inference('sup-', [status(thm)], ['143', '144'])).
% 44.99/45.28  thf('146', plain, ((l1_struct_0 @ sk_C)),
% 44.99/45.28      inference('sup-', [status(thm)], ['61', '62'])).
% 44.99/45.28  thf('147', plain,
% 44.99/45.28      (((r2_hidden @ sk_F @ (k2_struct_0 @ sk_C)) | (v2_struct_0 @ sk_C))),
% 44.99/45.28      inference('demod', [status(thm)], ['145', '146'])).
% 44.99/45.28  thf('148', plain, (~ (v2_struct_0 @ sk_C)),
% 44.99/45.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 44.99/45.28  thf('149', plain, ((r2_hidden @ sk_F @ (k2_struct_0 @ sk_C))),
% 44.99/45.28      inference('clc', [status(thm)], ['147', '148'])).
% 44.99/45.28  thf('150', plain, (((u1_struct_0 @ sk_C) = (k2_struct_0 @ sk_C))),
% 44.99/45.28      inference('demod', [status(thm)], ['57', '64'])).
% 44.99/45.28  thf('151', plain, (((k2_struct_0 @ sk_C) = (k2_struct_0 @ sk_D))),
% 44.99/45.28      inference('demod', [status(thm)], ['60', '63'])).
% 44.99/45.28  thf(fc10_tops_1, axiom,
% 44.99/45.28    (![A:$i]:
% 44.99/45.28     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 44.99/45.28       ( v3_pre_topc @ ( k2_struct_0 @ A ) @ A ) ))).
% 44.99/45.28  thf('152', plain,
% 44.99/45.28      (![X20 : $i]:
% 44.99/45.28         ((v3_pre_topc @ (k2_struct_0 @ X20) @ X20)
% 44.99/45.28          | ~ (l1_pre_topc @ X20)
% 44.99/45.28          | ~ (v2_pre_topc @ X20))),
% 44.99/45.28      inference('cnf', [status(esa)], [fc10_tops_1])).
% 44.99/45.28  thf('153', plain,
% 44.99/45.28      (((v3_pre_topc @ (k2_struct_0 @ sk_C) @ sk_D)
% 44.99/45.28        | ~ (v2_pre_topc @ sk_D)
% 44.99/45.28        | ~ (l1_pre_topc @ sk_D))),
% 44.99/45.28      inference('sup+', [status(thm)], ['151', '152'])).
% 44.99/45.28  thf('154', plain, ((v2_pre_topc @ sk_D)),
% 44.99/45.28      inference('demod', [status(thm)], ['125', '126', '127'])).
% 44.99/45.28  thf('155', plain, ((l1_pre_topc @ sk_D)),
% 44.99/45.28      inference('demod', [status(thm)], ['17', '18'])).
% 44.99/45.28  thf('156', plain, ((v3_pre_topc @ (k2_struct_0 @ sk_C) @ sk_D)),
% 44.99/45.28      inference('demod', [status(thm)], ['153', '154', '155'])).
% 44.99/45.28  thf('157', plain,
% 44.99/45.28      (((v2_struct_0 @ sk_D)
% 44.99/45.28        | (m1_connsp_2 @ (k2_struct_0 @ sk_C) @ sk_D @ sk_F))),
% 44.99/45.28      inference('demod', [status(thm)],
% 44.99/45.28                ['134', '135', '136', '149', '150', '156'])).
% 44.99/45.28  thf('158', plain, (~ (v2_struct_0 @ sk_D)),
% 44.99/45.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 44.99/45.28  thf('159', plain, ((m1_connsp_2 @ (k2_struct_0 @ sk_C) @ sk_D @ sk_F)),
% 44.99/45.28      inference('clc', [status(thm)], ['157', '158'])).
% 44.99/45.28  thf('160', plain,
% 44.99/45.28      (((v2_struct_0 @ sk_A)
% 44.99/45.28        | (v2_struct_0 @ sk_C)
% 44.99/45.28        | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)
% 44.99/45.28        | (v2_struct_0 @ sk_D)
% 44.99/45.28        | (v2_struct_0 @ sk_B))),
% 44.99/45.28      inference('demod', [status(thm)], ['110', '111', '159'])).
% 44.99/45.28  thf('161', plain, (~ (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)),
% 44.99/45.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 44.99/45.28  thf('162', plain,
% 44.99/45.28      (((v2_struct_0 @ sk_B)
% 44.99/45.28        | (v2_struct_0 @ sk_D)
% 44.99/45.28        | (v2_struct_0 @ sk_C)
% 44.99/45.28        | (v2_struct_0 @ sk_A))),
% 44.99/45.28      inference('sup-', [status(thm)], ['160', '161'])).
% 44.99/45.28  thf('163', plain, (~ (v2_struct_0 @ sk_D)),
% 44.99/45.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 44.99/45.28  thf('164', plain,
% 44.99/45.28      (((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_B))),
% 44.99/45.28      inference('sup-', [status(thm)], ['162', '163'])).
% 44.99/45.28  thf('165', plain, (~ (v2_struct_0 @ sk_A)),
% 44.99/45.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 44.99/45.28  thf('166', plain, (((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_C))),
% 44.99/45.28      inference('clc', [status(thm)], ['164', '165'])).
% 44.99/45.28  thf('167', plain, (~ (v2_struct_0 @ sk_B)),
% 44.99/45.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 44.99/45.28  thf('168', plain, ((v2_struct_0 @ sk_C)),
% 44.99/45.28      inference('clc', [status(thm)], ['166', '167'])).
% 44.99/45.28  thf('169', plain, ($false), inference('demod', [status(thm)], ['0', '168'])).
% 44.99/45.28  
% 44.99/45.28  % SZS output end Refutation
% 44.99/45.28  
% 45.07/45.28  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
