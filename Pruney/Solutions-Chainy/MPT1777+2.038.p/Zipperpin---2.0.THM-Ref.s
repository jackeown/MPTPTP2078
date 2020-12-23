%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.mBozJX3xXC

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:10:32 EST 2020

% Result     : Theorem 0.79s
% Output     : Refutation 0.79s
% Verified   : 
% Statistics : Number of formulae       :  209 (3606 expanded)
%              Number of leaves         :   43 (1067 expanded)
%              Depth                    :   27
%              Number of atoms          : 1800 (93169 expanded)
%              Number of equality atoms :   48 (2578 expanded)
%              Maximal formula depth    :   32 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_tmap_1_type,type,(
    r1_tmap_1: $i > $i > $i > $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_G_type,type,(
    sk_G: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k3_tmap_1_type,type,(
    k3_tmap_1: $i > $i > $i > $i > $i > $i )).

thf(g1_pre_topc_type,type,(
    g1_pre_topc: $i > $i > $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(m1_connsp_2_type,type,(
    m1_connsp_2: $i > $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

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
    ! [X24: $i] :
      ( ( m1_pre_topc @ X24 @ X24 )
      | ~ ( l1_pre_topc @ X24 ) ) ),
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

thf(t35_borsuk_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( r1_tarski @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) )).

thf('27',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( m1_pre_topc @ X25 @ X26 )
      | ( r1_tarski @ ( u1_struct_0 @ X25 ) @ ( u1_struct_0 @ X26 ) )
      | ~ ( l1_pre_topc @ X26 ) ) ),
    inference(cnf,[status(esa)],[t35_borsuk_1])).

thf('28',plain,
    ( ~ ( l1_pre_topc @ sk_C )
    | ( r1_tarski @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['23','24'])).

thf('30',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('32',plain,
    ( ~ ( r1_tarski @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D ) )
    | ( ( u1_struct_0 @ sk_C )
      = ( u1_struct_0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) )
    = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    ! [X24: $i] :
      ( ( m1_pre_topc @ X24 @ X24 )
      | ~ ( l1_pre_topc @ X24 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('35',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( l1_pre_topc @ X18 )
      | ~ ( m1_pre_topc @ X19 @ X18 )
      | ( m1_pre_topc @ X19 @ ( g1_pre_topc @ ( u1_struct_0 @ X18 ) @ ( u1_pre_topc @ X18 ) ) )
      | ~ ( l1_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[t65_pre_topc])).

thf('36',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( m1_pre_topc @ X25 @ X26 )
      | ( r1_tarski @ ( u1_struct_0 @ X25 ) @ ( u1_struct_0 @ X26 ) )
      | ~ ( l1_pre_topc @ X26 ) ) ),
    inference(cnf,[status(esa)],[t35_borsuk_1])).

thf('39',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ( r1_tarski @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,
    ( ~ ( l1_pre_topc @ sk_D )
    | ( r1_tarski @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) ) ) )
    | ~ ( l1_pre_topc @ sk_C ) ),
    inference('sup-',[status(thm)],['33','39'])).

thf('41',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['17','18'])).

thf('42',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) )
    = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['23','24'])).

thf('44',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['40','41','42','43'])).

thf('45',plain,
    ( ( u1_struct_0 @ sk_C )
    = ( u1_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['32','44'])).

thf('46',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['8','45'])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('47',plain,(
    ! [X13: $i] :
      ( ( ( k2_struct_0 @ X13 )
        = ( u1_struct_0 @ X13 ) )
      | ~ ( l1_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('48',plain,
    ( ( u1_struct_0 @ sk_C )
    = ( u1_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['32','44'])).

thf('49',plain,
    ( ( ( u1_struct_0 @ sk_C )
      = ( k2_struct_0 @ sk_D ) )
    | ~ ( l1_struct_0 @ sk_D ) ),
    inference('sup+',[status(thm)],['47','48'])).

thf('50',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['17','18'])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('51',plain,(
    ! [X14: $i] :
      ( ( l1_struct_0 @ X14 )
      | ~ ( l1_pre_topc @ X14 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('52',plain,(
    l1_struct_0 @ sk_D ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,
    ( ( u1_struct_0 @ sk_C )
    = ( k2_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['49','52'])).

thf('54',plain,(
    ! [X13: $i] :
      ( ( ( k2_struct_0 @ X13 )
        = ( u1_struct_0 @ X13 ) )
      | ~ ( l1_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('55',plain,
    ( ( u1_struct_0 @ sk_C )
    = ( k2_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['49','52'])).

thf('56',plain,
    ( ( ( k2_struct_0 @ sk_C )
      = ( k2_struct_0 @ sk_D ) )
    | ~ ( l1_struct_0 @ sk_C ) ),
    inference('sup+',[status(thm)],['54','55'])).

thf('57',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['23','24'])).

thf('58',plain,(
    ! [X14: $i] :
      ( ( l1_struct_0 @ X14 )
      | ~ ( l1_pre_topc @ X14 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('59',plain,(
    l1_struct_0 @ sk_C ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,
    ( ( k2_struct_0 @ sk_C )
    = ( k2_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['56','59'])).

thf('61',plain,
    ( ( u1_struct_0 @ sk_C )
    = ( k2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['53','60'])).

thf('62',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['46','61'])).

thf('63',plain,
    ( ( u1_struct_0 @ sk_C )
    = ( u1_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['32','44'])).

thf('64',plain,
    ( ( u1_struct_0 @ sk_C )
    = ( k2_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['49','52'])).

thf('65',plain,
    ( ( k2_struct_0 @ sk_D )
    = ( u1_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('66',plain,
    ( ( k2_struct_0 @ sk_C )
    = ( k2_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['56','59'])).

thf('67',plain,
    ( ( k2_struct_0 @ sk_C )
    = ( u1_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['65','66'])).

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

thf('68',plain,(
    ! [X30: $i,X31: $i,X32: $i,X33: $i,X34: $i,X35: $i,X36: $i,X37: $i] :
      ( ( v2_struct_0 @ X30 )
      | ~ ( v2_pre_topc @ X30 )
      | ~ ( l1_pre_topc @ X30 )
      | ( v2_struct_0 @ X31 )
      | ~ ( m1_pre_topc @ X31 @ X32 )
      | ~ ( m1_pre_topc @ X33 @ X31 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X31 ) ) )
      | ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ X33 ) )
      | ~ ( r1_tmap_1 @ X33 @ X30 @ ( k3_tmap_1 @ X32 @ X30 @ X31 @ X33 @ X36 ) @ X35 )
      | ( r1_tmap_1 @ X31 @ X30 @ X36 @ X37 )
      | ( X37 != X35 )
      | ~ ( m1_connsp_2 @ X34 @ X31 @ X37 )
      | ~ ( r1_tarski @ X34 @ ( u1_struct_0 @ X33 ) )
      | ~ ( m1_subset_1 @ X37 @ ( u1_struct_0 @ X31 ) )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X31 ) @ ( u1_struct_0 @ X30 ) ) ) )
      | ~ ( v1_funct_2 @ X36 @ ( u1_struct_0 @ X31 ) @ ( u1_struct_0 @ X30 ) )
      | ~ ( v1_funct_1 @ X36 )
      | ~ ( m1_pre_topc @ X33 @ X32 )
      | ( v2_struct_0 @ X33 )
      | ~ ( l1_pre_topc @ X32 )
      | ~ ( v2_pre_topc @ X32 )
      | ( v2_struct_0 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t83_tmap_1])).

thf('69',plain,(
    ! [X30: $i,X31: $i,X32: $i,X33: $i,X34: $i,X35: $i,X36: $i] :
      ( ( v2_struct_0 @ X32 )
      | ~ ( v2_pre_topc @ X32 )
      | ~ ( l1_pre_topc @ X32 )
      | ( v2_struct_0 @ X33 )
      | ~ ( m1_pre_topc @ X33 @ X32 )
      | ~ ( v1_funct_1 @ X36 )
      | ~ ( v1_funct_2 @ X36 @ ( u1_struct_0 @ X31 ) @ ( u1_struct_0 @ X30 ) )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X31 ) @ ( u1_struct_0 @ X30 ) ) ) )
      | ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ X31 ) )
      | ~ ( r1_tarski @ X34 @ ( u1_struct_0 @ X33 ) )
      | ~ ( m1_connsp_2 @ X34 @ X31 @ X35 )
      | ( r1_tmap_1 @ X31 @ X30 @ X36 @ X35 )
      | ~ ( r1_tmap_1 @ X33 @ X30 @ ( k3_tmap_1 @ X32 @ X30 @ X31 @ X33 @ X36 ) @ X35 )
      | ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ X33 ) )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X31 ) ) )
      | ~ ( m1_pre_topc @ X33 @ X31 )
      | ~ ( m1_pre_topc @ X31 @ X32 )
      | ( v2_struct_0 @ X31 )
      | ~ ( l1_pre_topc @ X30 )
      | ~ ( v2_pre_topc @ X30 )
      | ( v2_struct_0 @ X30 ) ) ),
    inference(simplify,[status(thm)],['68'])).

thf('70',plain,(
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
    inference('sup-',[status(thm)],['67','69'])).

thf('71',plain,
    ( ( k2_struct_0 @ sk_C )
    = ( u1_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['65','66'])).

thf('72',plain,
    ( ( k2_struct_0 @ sk_C )
    = ( u1_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['65','66'])).

thf('73',plain,
    ( ( k2_struct_0 @ sk_C )
    = ( u1_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['65','66'])).

thf('74',plain,(
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
    inference(demod,[status(thm)],['70','71','72','73'])).

thf('75',plain,(
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
    inference('sup-',[status(thm)],['62','74'])).

thf('76',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    ! [X13: $i] :
      ( ( ( k2_struct_0 @ X13 )
        = ( u1_struct_0 @ X13 ) )
      | ~ ( l1_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('78',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,
    ( ( v1_funct_2 @ sk_E @ ( k2_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_D ) ),
    inference('sup+',[status(thm)],['77','78'])).

thf('80',plain,(
    l1_struct_0 @ sk_D ),
    inference('sup-',[status(thm)],['50','51'])).

thf('81',plain,(
    v1_funct_2 @ sk_E @ ( k2_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['79','80'])).

thf('82',plain,
    ( ( k2_struct_0 @ sk_C )
    = ( k2_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['56','59'])).

thf('83',plain,(
    v1_funct_2 @ sk_E @ ( k2_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['81','82'])).

thf('84',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
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
    inference(demod,[status(thm)],['75','76','83','84','85'])).

thf('87',plain,(
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
    inference('sup-',[status(thm)],['7','86'])).

thf('88',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) )
    = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('91',plain,
    ( ( m1_pre_topc @ sk_C @ sk_D )
    | ~ ( l1_pre_topc @ sk_C ) ),
    inference('sup+',[status(thm)],['89','90'])).

thf('92',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['23','24'])).

thf('93',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(demod,[status(thm)],['91','92'])).

thf('94',plain,
    ( ( u1_struct_0 @ sk_C )
    = ( k2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['53','60'])).

thf('95',plain,(
    ! [X13: $i] :
      ( ( ( k2_struct_0 @ X13 )
        = ( u1_struct_0 @ X13 ) )
      | ~ ( l1_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('96',plain,(
    m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    sk_F = sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['96','97'])).

thf('99',plain,
    ( ( m1_subset_1 @ sk_F @ ( k2_struct_0 @ sk_C ) )
    | ~ ( l1_struct_0 @ sk_C ) ),
    inference('sup+',[status(thm)],['95','98'])).

thf('100',plain,(
    l1_struct_0 @ sk_C ),
    inference('sup-',[status(thm)],['57','58'])).

thf('101',plain,(
    m1_subset_1 @ sk_F @ ( k2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['99','100'])).

thf('102',plain,
    ( ( u1_struct_0 @ sk_C )
    = ( k2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['53','60'])).

thf('103',plain,(
    m1_subset_1 @ sk_F @ ( k2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['99','100'])).

thf('104',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_C ) ) )
      | ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F )
      | ~ ( m1_connsp_2 @ X0 @ sk_D @ sk_F )
      | ~ ( r1_tarski @ X0 @ ( k2_struct_0 @ sk_C ) )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['87','88','93','94','101','102','103','104','105','106'])).

thf('108',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ~ ( r1_tarski @ ( k2_struct_0 @ sk_C ) @ ( k2_struct_0 @ sk_C ) )
    | ~ ( m1_connsp_2 @ ( k2_struct_0 @ sk_C ) @ sk_D @ sk_F )
    | ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['4','107'])).

thf('109',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['1'])).

thf('110',plain,(
    ! [X13: $i] :
      ( ( ( k2_struct_0 @ X13 )
        = ( u1_struct_0 @ X13 ) )
      | ~ ( l1_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('111',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,
    ( ( m1_subset_1 @ sk_F @ ( k2_struct_0 @ sk_D ) )
    | ~ ( l1_struct_0 @ sk_D ) ),
    inference('sup+',[status(thm)],['110','111'])).

thf('113',plain,(
    l1_struct_0 @ sk_D ),
    inference('sup-',[status(thm)],['50','51'])).

thf('114',plain,(
    m1_subset_1 @ sk_F @ ( k2_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['112','113'])).

thf('115',plain,(
    ! [X13: $i] :
      ( ( ( k2_struct_0 @ X13 )
        = ( u1_struct_0 @ X13 ) )
      | ~ ( l1_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('116',plain,(
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

thf('117',plain,(
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

thf('118',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ( m1_connsp_2 @ ( u1_struct_0 @ X0 ) @ X0 @ X1 )
      | ~ ( r2_hidden @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['116','117'])).

thf('119',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k2_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( r2_hidden @ X1 @ ( u1_struct_0 @ X0 ) )
      | ( m1_connsp_2 @ ( u1_struct_0 @ X0 ) @ X0 @ X1 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['115','118'])).

thf('120',plain,
    ( ( v2_struct_0 @ sk_D )
    | ~ ( v2_pre_topc @ sk_D )
    | ~ ( l1_pre_topc @ sk_D )
    | ( m1_connsp_2 @ ( u1_struct_0 @ sk_D ) @ sk_D @ sk_F )
    | ~ ( r2_hidden @ sk_F @ ( u1_struct_0 @ sk_D ) )
    | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_D ) @ sk_D )
    | ~ ( l1_struct_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['114','119'])).

thf('121',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( v2_pre_topc @ B ) ) ) )).

thf('122',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_pre_topc @ X11 @ X12 )
      | ( v2_pre_topc @ X11 )
      | ~ ( l1_pre_topc @ X12 )
      | ~ ( v2_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[cc1_pre_topc])).

thf('123',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_pre_topc @ sk_D ) ),
    inference('sup-',[status(thm)],['121','122'])).

thf('124',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('125',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,(
    v2_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['123','124','125'])).

thf('127',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['17','18'])).

thf('128',plain,(
    l1_struct_0 @ sk_D ),
    inference('sup-',[status(thm)],['50','51'])).

thf('129',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( m1_connsp_2 @ ( u1_struct_0 @ sk_D ) @ sk_D @ sk_F )
    | ~ ( r2_hidden @ sk_F @ ( u1_struct_0 @ sk_D ) )
    | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_D ) @ sk_D ) ),
    inference(demod,[status(thm)],['120','126','127','128'])).

thf('130',plain,
    ( ( k2_struct_0 @ sk_C )
    = ( u1_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['65','66'])).

thf('131',plain,
    ( ( k2_struct_0 @ sk_C )
    = ( u1_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['65','66'])).

thf('132',plain,(
    ! [X13: $i] :
      ( ( ( k2_struct_0 @ X13 )
        = ( u1_struct_0 @ X13 ) )
      | ~ ( l1_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('133',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['96','97'])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('134',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r2_hidden @ X3 @ X4 )
      | ( v1_xboole_0 @ X4 )
      | ~ ( m1_subset_1 @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('135',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) )
    | ( r2_hidden @ sk_F @ ( u1_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['133','134'])).

thf('136',plain,
    ( ( r2_hidden @ sk_F @ ( k2_struct_0 @ sk_C ) )
    | ~ ( l1_struct_0 @ sk_C )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['132','135'])).

thf('137',plain,(
    l1_struct_0 @ sk_C ),
    inference('sup-',[status(thm)],['57','58'])).

thf('138',plain,
    ( ( r2_hidden @ sk_F @ ( k2_struct_0 @ sk_C ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['136','137'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('139',plain,(
    ! [X17: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X17 ) )
      | ~ ( l1_struct_0 @ X17 )
      | ( v2_struct_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('140',plain,
    ( ( r2_hidden @ sk_F @ ( k2_struct_0 @ sk_C ) )
    | ( v2_struct_0 @ sk_C )
    | ~ ( l1_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['138','139'])).

thf('141',plain,(
    l1_struct_0 @ sk_C ),
    inference('sup-',[status(thm)],['57','58'])).

thf('142',plain,
    ( ( r2_hidden @ sk_F @ ( k2_struct_0 @ sk_C ) )
    | ( v2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['140','141'])).

thf('143',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('144',plain,(
    r2_hidden @ sk_F @ ( k2_struct_0 @ sk_C ) ),
    inference(clc,[status(thm)],['142','143'])).

thf('145',plain,
    ( ( k2_struct_0 @ sk_C )
    = ( u1_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['65','66'])).

thf('146',plain,
    ( ( k2_struct_0 @ sk_C )
    = ( k2_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['56','59'])).

thf(fc10_tops_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( v3_pre_topc @ ( k2_struct_0 @ A ) @ A ) ) )).

thf('147',plain,(
    ! [X20: $i] :
      ( ( v3_pre_topc @ ( k2_struct_0 @ X20 ) @ X20 )
      | ~ ( l1_pre_topc @ X20 )
      | ~ ( v2_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[fc10_tops_1])).

thf('148',plain,
    ( ( v3_pre_topc @ ( k2_struct_0 @ sk_C ) @ sk_D )
    | ~ ( v2_pre_topc @ sk_D )
    | ~ ( l1_pre_topc @ sk_D ) ),
    inference('sup+',[status(thm)],['146','147'])).

thf('149',plain,(
    v2_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['123','124','125'])).

thf('150',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['17','18'])).

thf('151',plain,(
    v3_pre_topc @ ( k2_struct_0 @ sk_C ) @ sk_D ),
    inference(demod,[status(thm)],['148','149','150'])).

thf('152',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( m1_connsp_2 @ ( k2_struct_0 @ sk_C ) @ sk_D @ sk_F ) ),
    inference(demod,[status(thm)],['129','130','131','144','145','151'])).

thf('153',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('154',plain,(
    m1_connsp_2 @ ( k2_struct_0 @ sk_C ) @ sk_D @ sk_F ),
    inference(clc,[status(thm)],['152','153'])).

thf('155',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['108','109','154'])).

thf('156',plain,(
    ~ ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('157',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['155','156'])).

thf('158',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('159',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['157','158'])).

thf('160',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('161',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C ) ),
    inference(clc,[status(thm)],['159','160'])).

thf('162',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('163',plain,(
    v2_struct_0 @ sk_C ),
    inference(clc,[status(thm)],['161','162'])).

thf('164',plain,(
    $false ),
    inference(demod,[status(thm)],['0','163'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.mBozJX3xXC
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:22:33 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.79/1.01  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.79/1.01  % Solved by: fo/fo7.sh
% 0.79/1.01  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.79/1.01  % done 516 iterations in 0.529s
% 0.79/1.01  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.79/1.01  % SZS output start Refutation
% 0.79/1.01  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.79/1.01  thf(r1_tmap_1_type, type, r1_tmap_1: $i > $i > $i > $i > $o).
% 0.79/1.01  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.79/1.01  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.79/1.01  thf(sk_E_type, type, sk_E: $i).
% 0.79/1.01  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.79/1.01  thf(sk_B_type, type, sk_B: $i).
% 0.79/1.01  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.79/1.01  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.79/1.01  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.79/1.01  thf(sk_D_type, type, sk_D: $i).
% 0.79/1.01  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.79/1.01  thf(sk_G_type, type, sk_G: $i).
% 0.79/1.01  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.79/1.01  thf(k3_tmap_1_type, type, k3_tmap_1: $i > $i > $i > $i > $i > $i).
% 0.79/1.01  thf(g1_pre_topc_type, type, g1_pre_topc: $i > $i > $i).
% 0.79/1.01  thf(sk_F_type, type, sk_F: $i).
% 0.79/1.01  thf(m1_connsp_2_type, type, m1_connsp_2: $i > $i > $i > $o).
% 0.79/1.01  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.79/1.01  thf(sk_A_type, type, sk_A: $i).
% 0.79/1.01  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.79/1.01  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 0.79/1.01  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.79/1.01  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.79/1.01  thf(sk_C_type, type, sk_C: $i).
% 0.79/1.01  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.79/1.01  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.79/1.01  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.79/1.01  thf(t88_tmap_1, conjecture,
% 0.79/1.01    (![A:$i]:
% 0.79/1.01     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.79/1.01       ( ![B:$i]:
% 0.79/1.01         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.79/1.01             ( l1_pre_topc @ B ) ) =>
% 0.79/1.01           ( ![C:$i]:
% 0.79/1.01             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.79/1.01               ( ![D:$i]:
% 0.79/1.01                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.79/1.01                   ( ![E:$i]:
% 0.79/1.01                     ( ( ( v1_funct_1 @ E ) & 
% 0.79/1.01                         ( v1_funct_2 @
% 0.79/1.01                           E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 0.79/1.01                         ( m1_subset_1 @
% 0.79/1.01                           E @ 
% 0.79/1.01                           ( k1_zfmisc_1 @
% 0.79/1.01                             ( k2_zfmisc_1 @
% 0.79/1.01                               ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.79/1.01                       ( ( ( g1_pre_topc @
% 0.79/1.01                             ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) ) =
% 0.79/1.01                           ( D ) ) =>
% 0.79/1.01                         ( ![F:$i]:
% 0.79/1.01                           ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 0.79/1.01                             ( ![G:$i]:
% 0.79/1.01                               ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) ) =>
% 0.79/1.01                                 ( ( ( ( F ) = ( G ) ) & 
% 0.79/1.01                                     ( r1_tmap_1 @
% 0.79/1.01                                       C @ B @ 
% 0.79/1.01                                       ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ G ) ) =>
% 0.79/1.01                                   ( r1_tmap_1 @ D @ B @ E @ F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.79/1.01  thf(zf_stmt_0, negated_conjecture,
% 0.79/1.01    (~( ![A:$i]:
% 0.79/1.01        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.79/1.01            ( l1_pre_topc @ A ) ) =>
% 0.79/1.01          ( ![B:$i]:
% 0.79/1.01            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.79/1.01                ( l1_pre_topc @ B ) ) =>
% 0.79/1.01              ( ![C:$i]:
% 0.79/1.01                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.79/1.01                  ( ![D:$i]:
% 0.79/1.01                    ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.79/1.01                      ( ![E:$i]:
% 0.79/1.01                        ( ( ( v1_funct_1 @ E ) & 
% 0.79/1.01                            ( v1_funct_2 @
% 0.79/1.01                              E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 0.79/1.01                            ( m1_subset_1 @
% 0.79/1.01                              E @ 
% 0.79/1.01                              ( k1_zfmisc_1 @
% 0.79/1.01                                ( k2_zfmisc_1 @
% 0.79/1.01                                  ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.79/1.01                          ( ( ( g1_pre_topc @
% 0.79/1.01                                ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) ) =
% 0.79/1.01                              ( D ) ) =>
% 0.79/1.01                            ( ![F:$i]:
% 0.79/1.01                              ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 0.79/1.01                                ( ![G:$i]:
% 0.79/1.01                                  ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) ) =>
% 0.79/1.01                                    ( ( ( ( F ) = ( G ) ) & 
% 0.79/1.01                                        ( r1_tmap_1 @
% 0.79/1.01                                          C @ B @ 
% 0.79/1.01                                          ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ G ) ) =>
% 0.79/1.01                                      ( r1_tmap_1 @ D @ B @ E @ F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.79/1.01    inference('cnf.neg', [status(esa)], [t88_tmap_1])).
% 0.79/1.01  thf('0', plain, (~ (v2_struct_0 @ sk_C)),
% 0.79/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.01  thf(d10_xboole_0, axiom,
% 0.79/1.01    (![A:$i,B:$i]:
% 0.79/1.01     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.79/1.01  thf('1', plain,
% 0.79/1.01      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.79/1.01      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.79/1.01  thf('2', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.79/1.01      inference('simplify', [status(thm)], ['1'])).
% 0.79/1.01  thf(t3_subset, axiom,
% 0.79/1.01    (![A:$i,B:$i]:
% 0.79/1.01     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.79/1.01  thf('3', plain,
% 0.79/1.01      (![X5 : $i, X7 : $i]:
% 0.79/1.01         ((m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X7)) | ~ (r1_tarski @ X5 @ X7))),
% 0.79/1.01      inference('cnf', [status(esa)], [t3_subset])).
% 0.79/1.01  thf('4', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.79/1.01      inference('sup-', [status(thm)], ['2', '3'])).
% 0.79/1.01  thf('5', plain,
% 0.79/1.01      ((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.79/1.01        (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_G)),
% 0.79/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.01  thf('6', plain, (((sk_F) = (sk_G))),
% 0.79/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.01  thf('7', plain,
% 0.79/1.01      ((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.79/1.01        (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_F)),
% 0.79/1.01      inference('demod', [status(thm)], ['5', '6'])).
% 0.79/1.01  thf('8', plain,
% 0.79/1.01      ((m1_subset_1 @ sk_E @ 
% 0.79/1.01        (k1_zfmisc_1 @ 
% 0.79/1.01         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 0.79/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.01  thf('9', plain,
% 0.79/1.01      (((g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) = (sk_D))),
% 0.79/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.01  thf(t2_tsep_1, axiom,
% 0.79/1.01    (![A:$i]: ( ( l1_pre_topc @ A ) => ( m1_pre_topc @ A @ A ) ))).
% 0.79/1.01  thf('10', plain,
% 0.79/1.01      (![X24 : $i]: ((m1_pre_topc @ X24 @ X24) | ~ (l1_pre_topc @ X24))),
% 0.79/1.01      inference('cnf', [status(esa)], [t2_tsep_1])).
% 0.79/1.01  thf(t65_pre_topc, axiom,
% 0.79/1.01    (![A:$i]:
% 0.79/1.01     ( ( l1_pre_topc @ A ) =>
% 0.79/1.01       ( ![B:$i]:
% 0.79/1.01         ( ( l1_pre_topc @ B ) =>
% 0.79/1.01           ( ( m1_pre_topc @ A @ B ) <=>
% 0.79/1.01             ( m1_pre_topc @
% 0.79/1.01               A @ ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ) ))).
% 0.79/1.01  thf('11', plain,
% 0.79/1.01      (![X18 : $i, X19 : $i]:
% 0.79/1.01         (~ (l1_pre_topc @ X18)
% 0.79/1.01          | ~ (m1_pre_topc @ X19 @ 
% 0.79/1.01               (g1_pre_topc @ (u1_struct_0 @ X18) @ (u1_pre_topc @ X18)))
% 0.79/1.01          | (m1_pre_topc @ X19 @ X18)
% 0.79/1.01          | ~ (l1_pre_topc @ X19))),
% 0.79/1.01      inference('cnf', [status(esa)], [t65_pre_topc])).
% 0.79/1.01  thf('12', plain,
% 0.79/1.01      (![X0 : $i]:
% 0.79/1.01         (~ (l1_pre_topc @ 
% 0.79/1.01             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.79/1.01          | ~ (l1_pre_topc @ 
% 0.79/1.01               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.79/1.01          | (m1_pre_topc @ 
% 0.79/1.01             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)) @ X0)
% 0.79/1.01          | ~ (l1_pre_topc @ X0))),
% 0.79/1.01      inference('sup-', [status(thm)], ['10', '11'])).
% 0.79/1.01  thf('13', plain,
% 0.79/1.01      (![X0 : $i]:
% 0.79/1.01         (~ (l1_pre_topc @ X0)
% 0.79/1.01          | (m1_pre_topc @ 
% 0.79/1.01             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)) @ X0)
% 0.79/1.01          | ~ (l1_pre_topc @ 
% 0.79/1.01               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 0.79/1.01      inference('simplify', [status(thm)], ['12'])).
% 0.79/1.01  thf('14', plain,
% 0.79/1.01      ((~ (l1_pre_topc @ sk_D)
% 0.79/1.01        | (m1_pre_topc @ 
% 0.79/1.01           (g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) @ sk_C)
% 0.79/1.01        | ~ (l1_pre_topc @ sk_C))),
% 0.79/1.01      inference('sup-', [status(thm)], ['9', '13'])).
% 0.79/1.01  thf('15', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.79/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.01  thf(dt_m1_pre_topc, axiom,
% 0.79/1.01    (![A:$i]:
% 0.79/1.01     ( ( l1_pre_topc @ A ) =>
% 0.79/1.01       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.79/1.01  thf('16', plain,
% 0.79/1.01      (![X15 : $i, X16 : $i]:
% 0.79/1.01         (~ (m1_pre_topc @ X15 @ X16)
% 0.79/1.01          | (l1_pre_topc @ X15)
% 0.79/1.01          | ~ (l1_pre_topc @ X16))),
% 0.79/1.01      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.79/1.01  thf('17', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_D))),
% 0.79/1.01      inference('sup-', [status(thm)], ['15', '16'])).
% 0.79/1.01  thf('18', plain, ((l1_pre_topc @ sk_A)),
% 0.79/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.01  thf('19', plain, ((l1_pre_topc @ sk_D)),
% 0.79/1.01      inference('demod', [status(thm)], ['17', '18'])).
% 0.79/1.01  thf('20', plain,
% 0.79/1.01      (((g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) = (sk_D))),
% 0.79/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.01  thf('21', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.79/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.01  thf('22', plain,
% 0.79/1.01      (![X15 : $i, X16 : $i]:
% 0.79/1.01         (~ (m1_pre_topc @ X15 @ X16)
% 0.79/1.01          | (l1_pre_topc @ X15)
% 0.79/1.01          | ~ (l1_pre_topc @ X16))),
% 0.79/1.01      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.79/1.01  thf('23', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_C))),
% 0.79/1.01      inference('sup-', [status(thm)], ['21', '22'])).
% 0.79/1.01  thf('24', plain, ((l1_pre_topc @ sk_A)),
% 0.79/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.01  thf('25', plain, ((l1_pre_topc @ sk_C)),
% 0.79/1.01      inference('demod', [status(thm)], ['23', '24'])).
% 0.79/1.01  thf('26', plain, ((m1_pre_topc @ sk_D @ sk_C)),
% 0.79/1.01      inference('demod', [status(thm)], ['14', '19', '20', '25'])).
% 0.79/1.01  thf(t35_borsuk_1, axiom,
% 0.79/1.01    (![A:$i]:
% 0.79/1.01     ( ( l1_pre_topc @ A ) =>
% 0.79/1.01       ( ![B:$i]:
% 0.79/1.01         ( ( m1_pre_topc @ B @ A ) =>
% 0.79/1.01           ( r1_tarski @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ))).
% 0.79/1.01  thf('27', plain,
% 0.79/1.01      (![X25 : $i, X26 : $i]:
% 0.79/1.01         (~ (m1_pre_topc @ X25 @ X26)
% 0.79/1.01          | (r1_tarski @ (u1_struct_0 @ X25) @ (u1_struct_0 @ X26))
% 0.79/1.01          | ~ (l1_pre_topc @ X26))),
% 0.79/1.01      inference('cnf', [status(esa)], [t35_borsuk_1])).
% 0.79/1.01  thf('28', plain,
% 0.79/1.01      ((~ (l1_pre_topc @ sk_C)
% 0.79/1.01        | (r1_tarski @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_C)))),
% 0.79/1.01      inference('sup-', [status(thm)], ['26', '27'])).
% 0.79/1.01  thf('29', plain, ((l1_pre_topc @ sk_C)),
% 0.79/1.01      inference('demod', [status(thm)], ['23', '24'])).
% 0.79/1.01  thf('30', plain, ((r1_tarski @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_C))),
% 0.79/1.01      inference('demod', [status(thm)], ['28', '29'])).
% 0.79/1.01  thf('31', plain,
% 0.79/1.01      (![X0 : $i, X2 : $i]:
% 0.79/1.01         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.79/1.01      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.79/1.01  thf('32', plain,
% 0.79/1.01      ((~ (r1_tarski @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D))
% 0.79/1.01        | ((u1_struct_0 @ sk_C) = (u1_struct_0 @ sk_D)))),
% 0.79/1.01      inference('sup-', [status(thm)], ['30', '31'])).
% 0.79/1.01  thf('33', plain,
% 0.79/1.01      (((g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) = (sk_D))),
% 0.79/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.01  thf('34', plain,
% 0.79/1.01      (![X24 : $i]: ((m1_pre_topc @ X24 @ X24) | ~ (l1_pre_topc @ X24))),
% 0.79/1.01      inference('cnf', [status(esa)], [t2_tsep_1])).
% 0.79/1.01  thf('35', plain,
% 0.79/1.01      (![X18 : $i, X19 : $i]:
% 0.79/1.01         (~ (l1_pre_topc @ X18)
% 0.79/1.01          | ~ (m1_pre_topc @ X19 @ X18)
% 0.79/1.01          | (m1_pre_topc @ X19 @ 
% 0.79/1.01             (g1_pre_topc @ (u1_struct_0 @ X18) @ (u1_pre_topc @ X18)))
% 0.79/1.01          | ~ (l1_pre_topc @ X19))),
% 0.79/1.01      inference('cnf', [status(esa)], [t65_pre_topc])).
% 0.79/1.01  thf('36', plain,
% 0.79/1.01      (![X0 : $i]:
% 0.79/1.01         (~ (l1_pre_topc @ X0)
% 0.79/1.01          | ~ (l1_pre_topc @ X0)
% 0.79/1.01          | (m1_pre_topc @ X0 @ 
% 0.79/1.01             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.79/1.01          | ~ (l1_pre_topc @ X0))),
% 0.79/1.01      inference('sup-', [status(thm)], ['34', '35'])).
% 0.79/1.01  thf('37', plain,
% 0.79/1.01      (![X0 : $i]:
% 0.79/1.01         ((m1_pre_topc @ X0 @ 
% 0.79/1.01           (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.79/1.01          | ~ (l1_pre_topc @ X0))),
% 0.79/1.01      inference('simplify', [status(thm)], ['36'])).
% 0.79/1.01  thf('38', plain,
% 0.79/1.01      (![X25 : $i, X26 : $i]:
% 0.79/1.01         (~ (m1_pre_topc @ X25 @ X26)
% 0.79/1.01          | (r1_tarski @ (u1_struct_0 @ X25) @ (u1_struct_0 @ X26))
% 0.79/1.01          | ~ (l1_pre_topc @ X26))),
% 0.79/1.01      inference('cnf', [status(esa)], [t35_borsuk_1])).
% 0.79/1.01  thf('39', plain,
% 0.79/1.01      (![X0 : $i]:
% 0.79/1.01         (~ (l1_pre_topc @ X0)
% 0.79/1.01          | ~ (l1_pre_topc @ 
% 0.79/1.01               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.79/1.01          | (r1_tarski @ (u1_struct_0 @ X0) @ 
% 0.79/1.01             (u1_struct_0 @ 
% 0.79/1.01              (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))))),
% 0.79/1.01      inference('sup-', [status(thm)], ['37', '38'])).
% 0.79/1.01  thf('40', plain,
% 0.79/1.01      ((~ (l1_pre_topc @ sk_D)
% 0.79/1.01        | (r1_tarski @ (u1_struct_0 @ sk_C) @ 
% 0.79/1.01           (u1_struct_0 @ 
% 0.79/1.01            (g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C))))
% 0.79/1.01        | ~ (l1_pre_topc @ sk_C))),
% 0.79/1.01      inference('sup-', [status(thm)], ['33', '39'])).
% 0.79/1.01  thf('41', plain, ((l1_pre_topc @ sk_D)),
% 0.79/1.01      inference('demod', [status(thm)], ['17', '18'])).
% 0.79/1.01  thf('42', plain,
% 0.79/1.01      (((g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) = (sk_D))),
% 0.79/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.01  thf('43', plain, ((l1_pre_topc @ sk_C)),
% 0.79/1.01      inference('demod', [status(thm)], ['23', '24'])).
% 0.79/1.01  thf('44', plain, ((r1_tarski @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D))),
% 0.79/1.01      inference('demod', [status(thm)], ['40', '41', '42', '43'])).
% 0.79/1.01  thf('45', plain, (((u1_struct_0 @ sk_C) = (u1_struct_0 @ sk_D))),
% 0.79/1.01      inference('demod', [status(thm)], ['32', '44'])).
% 0.79/1.01  thf('46', plain,
% 0.79/1.01      ((m1_subset_1 @ sk_E @ 
% 0.79/1.01        (k1_zfmisc_1 @ 
% 0.79/1.01         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 0.79/1.01      inference('demod', [status(thm)], ['8', '45'])).
% 0.79/1.01  thf(d3_struct_0, axiom,
% 0.79/1.01    (![A:$i]:
% 0.79/1.01     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.79/1.01  thf('47', plain,
% 0.79/1.01      (![X13 : $i]:
% 0.79/1.01         (((k2_struct_0 @ X13) = (u1_struct_0 @ X13)) | ~ (l1_struct_0 @ X13))),
% 0.79/1.01      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.79/1.01  thf('48', plain, (((u1_struct_0 @ sk_C) = (u1_struct_0 @ sk_D))),
% 0.79/1.01      inference('demod', [status(thm)], ['32', '44'])).
% 0.79/1.01  thf('49', plain,
% 0.79/1.01      ((((u1_struct_0 @ sk_C) = (k2_struct_0 @ sk_D)) | ~ (l1_struct_0 @ sk_D))),
% 0.79/1.01      inference('sup+', [status(thm)], ['47', '48'])).
% 0.79/1.01  thf('50', plain, ((l1_pre_topc @ sk_D)),
% 0.79/1.01      inference('demod', [status(thm)], ['17', '18'])).
% 0.79/1.01  thf(dt_l1_pre_topc, axiom,
% 0.79/1.01    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.79/1.01  thf('51', plain,
% 0.79/1.01      (![X14 : $i]: ((l1_struct_0 @ X14) | ~ (l1_pre_topc @ X14))),
% 0.79/1.01      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.79/1.01  thf('52', plain, ((l1_struct_0 @ sk_D)),
% 0.79/1.01      inference('sup-', [status(thm)], ['50', '51'])).
% 0.79/1.01  thf('53', plain, (((u1_struct_0 @ sk_C) = (k2_struct_0 @ sk_D))),
% 0.79/1.01      inference('demod', [status(thm)], ['49', '52'])).
% 0.79/1.01  thf('54', plain,
% 0.79/1.01      (![X13 : $i]:
% 0.79/1.01         (((k2_struct_0 @ X13) = (u1_struct_0 @ X13)) | ~ (l1_struct_0 @ X13))),
% 0.79/1.01      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.79/1.01  thf('55', plain, (((u1_struct_0 @ sk_C) = (k2_struct_0 @ sk_D))),
% 0.79/1.01      inference('demod', [status(thm)], ['49', '52'])).
% 0.79/1.01  thf('56', plain,
% 0.79/1.01      ((((k2_struct_0 @ sk_C) = (k2_struct_0 @ sk_D)) | ~ (l1_struct_0 @ sk_C))),
% 0.79/1.01      inference('sup+', [status(thm)], ['54', '55'])).
% 0.79/1.01  thf('57', plain, ((l1_pre_topc @ sk_C)),
% 0.79/1.01      inference('demod', [status(thm)], ['23', '24'])).
% 0.79/1.01  thf('58', plain,
% 0.79/1.01      (![X14 : $i]: ((l1_struct_0 @ X14) | ~ (l1_pre_topc @ X14))),
% 0.79/1.01      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.79/1.01  thf('59', plain, ((l1_struct_0 @ sk_C)),
% 0.79/1.01      inference('sup-', [status(thm)], ['57', '58'])).
% 0.79/1.01  thf('60', plain, (((k2_struct_0 @ sk_C) = (k2_struct_0 @ sk_D))),
% 0.79/1.01      inference('demod', [status(thm)], ['56', '59'])).
% 0.79/1.01  thf('61', plain, (((u1_struct_0 @ sk_C) = (k2_struct_0 @ sk_C))),
% 0.79/1.01      inference('demod', [status(thm)], ['53', '60'])).
% 0.79/1.01  thf('62', plain,
% 0.79/1.01      ((m1_subset_1 @ sk_E @ 
% 0.79/1.01        (k1_zfmisc_1 @ 
% 0.79/1.01         (k2_zfmisc_1 @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 0.79/1.01      inference('demod', [status(thm)], ['46', '61'])).
% 0.79/1.01  thf('63', plain, (((u1_struct_0 @ sk_C) = (u1_struct_0 @ sk_D))),
% 0.79/1.01      inference('demod', [status(thm)], ['32', '44'])).
% 0.79/1.01  thf('64', plain, (((u1_struct_0 @ sk_C) = (k2_struct_0 @ sk_D))),
% 0.79/1.01      inference('demod', [status(thm)], ['49', '52'])).
% 0.79/1.01  thf('65', plain, (((k2_struct_0 @ sk_D) = (u1_struct_0 @ sk_D))),
% 0.79/1.01      inference('demod', [status(thm)], ['63', '64'])).
% 0.79/1.01  thf('66', plain, (((k2_struct_0 @ sk_C) = (k2_struct_0 @ sk_D))),
% 0.79/1.01      inference('demod', [status(thm)], ['56', '59'])).
% 0.79/1.01  thf('67', plain, (((k2_struct_0 @ sk_C) = (u1_struct_0 @ sk_D))),
% 0.79/1.01      inference('demod', [status(thm)], ['65', '66'])).
% 0.79/1.01  thf(t83_tmap_1, axiom,
% 0.79/1.01    (![A:$i]:
% 0.79/1.01     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.79/1.01       ( ![B:$i]:
% 0.79/1.01         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.79/1.01             ( l1_pre_topc @ B ) ) =>
% 0.79/1.01           ( ![C:$i]:
% 0.79/1.01             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.79/1.01               ( ![D:$i]:
% 0.79/1.01                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.79/1.01                   ( ![E:$i]:
% 0.79/1.01                     ( ( ( v1_funct_1 @ E ) & 
% 0.79/1.01                         ( v1_funct_2 @
% 0.79/1.01                           E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 0.79/1.01                         ( m1_subset_1 @
% 0.79/1.01                           E @ 
% 0.79/1.01                           ( k1_zfmisc_1 @
% 0.79/1.01                             ( k2_zfmisc_1 @
% 0.79/1.01                               ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.79/1.01                       ( ( m1_pre_topc @ C @ D ) =>
% 0.79/1.01                         ( ![F:$i]:
% 0.79/1.01                           ( ( m1_subset_1 @
% 0.79/1.01                               F @ ( k1_zfmisc_1 @ ( u1_struct_0 @ D ) ) ) =>
% 0.79/1.01                             ( ![G:$i]:
% 0.79/1.01                               ( ( m1_subset_1 @ G @ ( u1_struct_0 @ D ) ) =>
% 0.79/1.01                                 ( ![H:$i]:
% 0.79/1.01                                   ( ( m1_subset_1 @ H @ ( u1_struct_0 @ C ) ) =>
% 0.79/1.01                                     ( ( ( r1_tarski @ F @ ( u1_struct_0 @ C ) ) & 
% 0.79/1.01                                         ( m1_connsp_2 @ F @ D @ G ) & 
% 0.79/1.01                                         ( ( G ) = ( H ) ) ) =>
% 0.79/1.01                                       ( ( r1_tmap_1 @ D @ B @ E @ G ) <=>
% 0.79/1.01                                         ( r1_tmap_1 @
% 0.79/1.01                                           C @ B @ 
% 0.79/1.01                                           ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ 
% 0.79/1.01                                           H ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.79/1.01  thf('68', plain,
% 0.79/1.01      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i, X34 : $i, X35 : $i, X36 : $i, 
% 0.79/1.01         X37 : $i]:
% 0.79/1.01         ((v2_struct_0 @ X30)
% 0.79/1.01          | ~ (v2_pre_topc @ X30)
% 0.79/1.01          | ~ (l1_pre_topc @ X30)
% 0.79/1.01          | (v2_struct_0 @ X31)
% 0.79/1.01          | ~ (m1_pre_topc @ X31 @ X32)
% 0.79/1.01          | ~ (m1_pre_topc @ X33 @ X31)
% 0.79/1.01          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (u1_struct_0 @ X31)))
% 0.79/1.01          | ~ (m1_subset_1 @ X35 @ (u1_struct_0 @ X33))
% 0.79/1.01          | ~ (r1_tmap_1 @ X33 @ X30 @ 
% 0.79/1.01               (k3_tmap_1 @ X32 @ X30 @ X31 @ X33 @ X36) @ X35)
% 0.79/1.01          | (r1_tmap_1 @ X31 @ X30 @ X36 @ X37)
% 0.79/1.01          | ((X37) != (X35))
% 0.79/1.01          | ~ (m1_connsp_2 @ X34 @ X31 @ X37)
% 0.79/1.01          | ~ (r1_tarski @ X34 @ (u1_struct_0 @ X33))
% 0.79/1.01          | ~ (m1_subset_1 @ X37 @ (u1_struct_0 @ X31))
% 0.79/1.01          | ~ (m1_subset_1 @ X36 @ 
% 0.79/1.01               (k1_zfmisc_1 @ 
% 0.79/1.01                (k2_zfmisc_1 @ (u1_struct_0 @ X31) @ (u1_struct_0 @ X30))))
% 0.79/1.01          | ~ (v1_funct_2 @ X36 @ (u1_struct_0 @ X31) @ (u1_struct_0 @ X30))
% 0.79/1.01          | ~ (v1_funct_1 @ X36)
% 0.79/1.01          | ~ (m1_pre_topc @ X33 @ X32)
% 0.79/1.01          | (v2_struct_0 @ X33)
% 0.79/1.01          | ~ (l1_pre_topc @ X32)
% 0.79/1.01          | ~ (v2_pre_topc @ X32)
% 0.79/1.01          | (v2_struct_0 @ X32))),
% 0.79/1.01      inference('cnf', [status(esa)], [t83_tmap_1])).
% 0.79/1.01  thf('69', plain,
% 0.79/1.01      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 0.79/1.01         ((v2_struct_0 @ X32)
% 0.79/1.01          | ~ (v2_pre_topc @ X32)
% 0.79/1.01          | ~ (l1_pre_topc @ X32)
% 0.79/1.01          | (v2_struct_0 @ X33)
% 0.79/1.01          | ~ (m1_pre_topc @ X33 @ X32)
% 0.79/1.01          | ~ (v1_funct_1 @ X36)
% 0.79/1.01          | ~ (v1_funct_2 @ X36 @ (u1_struct_0 @ X31) @ (u1_struct_0 @ X30))
% 0.79/1.01          | ~ (m1_subset_1 @ X36 @ 
% 0.79/1.01               (k1_zfmisc_1 @ 
% 0.79/1.01                (k2_zfmisc_1 @ (u1_struct_0 @ X31) @ (u1_struct_0 @ X30))))
% 0.79/1.01          | ~ (m1_subset_1 @ X35 @ (u1_struct_0 @ X31))
% 0.79/1.01          | ~ (r1_tarski @ X34 @ (u1_struct_0 @ X33))
% 0.79/1.01          | ~ (m1_connsp_2 @ X34 @ X31 @ X35)
% 0.79/1.01          | (r1_tmap_1 @ X31 @ X30 @ X36 @ X35)
% 0.79/1.01          | ~ (r1_tmap_1 @ X33 @ X30 @ 
% 0.79/1.01               (k3_tmap_1 @ X32 @ X30 @ X31 @ X33 @ X36) @ X35)
% 0.79/1.01          | ~ (m1_subset_1 @ X35 @ (u1_struct_0 @ X33))
% 0.79/1.01          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (u1_struct_0 @ X31)))
% 0.79/1.01          | ~ (m1_pre_topc @ X33 @ X31)
% 0.79/1.01          | ~ (m1_pre_topc @ X31 @ X32)
% 0.79/1.01          | (v2_struct_0 @ X31)
% 0.79/1.01          | ~ (l1_pre_topc @ X30)
% 0.79/1.01          | ~ (v2_pre_topc @ X30)
% 0.79/1.01          | (v2_struct_0 @ X30))),
% 0.79/1.01      inference('simplify', [status(thm)], ['68'])).
% 0.79/1.01  thf('70', plain,
% 0.79/1.01      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.79/1.01         (~ (m1_subset_1 @ X1 @ 
% 0.79/1.01             (k1_zfmisc_1 @ 
% 0.79/1.01              (k2_zfmisc_1 @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ X0))))
% 0.79/1.01          | (v2_struct_0 @ X0)
% 0.79/1.01          | ~ (v2_pre_topc @ X0)
% 0.79/1.01          | ~ (l1_pre_topc @ X0)
% 0.79/1.01          | (v2_struct_0 @ sk_D)
% 0.79/1.01          | ~ (m1_pre_topc @ sk_D @ X2)
% 0.79/1.01          | ~ (m1_pre_topc @ X3 @ sk_D)
% 0.79/1.01          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))
% 0.79/1.01          | ~ (m1_subset_1 @ X5 @ (u1_struct_0 @ X3))
% 0.79/1.01          | ~ (r1_tmap_1 @ X3 @ X0 @ (k3_tmap_1 @ X2 @ X0 @ sk_D @ X3 @ X1) @ 
% 0.79/1.01               X5)
% 0.79/1.01          | (r1_tmap_1 @ sk_D @ X0 @ X1 @ X5)
% 0.79/1.01          | ~ (m1_connsp_2 @ X4 @ sk_D @ X5)
% 0.79/1.01          | ~ (r1_tarski @ X4 @ (u1_struct_0 @ X3))
% 0.79/1.01          | ~ (m1_subset_1 @ X5 @ (u1_struct_0 @ sk_D))
% 0.79/1.01          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ X0))
% 0.79/1.01          | ~ (v1_funct_1 @ X1)
% 0.79/1.01          | ~ (m1_pre_topc @ X3 @ X2)
% 0.79/1.01          | (v2_struct_0 @ X3)
% 0.79/1.01          | ~ (l1_pre_topc @ X2)
% 0.79/1.01          | ~ (v2_pre_topc @ X2)
% 0.79/1.01          | (v2_struct_0 @ X2))),
% 0.79/1.01      inference('sup-', [status(thm)], ['67', '69'])).
% 0.79/1.01  thf('71', plain, (((k2_struct_0 @ sk_C) = (u1_struct_0 @ sk_D))),
% 0.79/1.01      inference('demod', [status(thm)], ['65', '66'])).
% 0.79/1.01  thf('72', plain, (((k2_struct_0 @ sk_C) = (u1_struct_0 @ sk_D))),
% 0.79/1.01      inference('demod', [status(thm)], ['65', '66'])).
% 0.79/1.01  thf('73', plain, (((k2_struct_0 @ sk_C) = (u1_struct_0 @ sk_D))),
% 0.79/1.01      inference('demod', [status(thm)], ['65', '66'])).
% 0.79/1.01  thf('74', plain,
% 0.79/1.01      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.79/1.01         (~ (m1_subset_1 @ X1 @ 
% 0.79/1.01             (k1_zfmisc_1 @ 
% 0.79/1.01              (k2_zfmisc_1 @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ X0))))
% 0.79/1.01          | (v2_struct_0 @ X0)
% 0.79/1.01          | ~ (v2_pre_topc @ X0)
% 0.79/1.01          | ~ (l1_pre_topc @ X0)
% 0.79/1.01          | (v2_struct_0 @ sk_D)
% 0.79/1.01          | ~ (m1_pre_topc @ sk_D @ X2)
% 0.79/1.01          | ~ (m1_pre_topc @ X3 @ sk_D)
% 0.79/1.01          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_C)))
% 0.79/1.01          | ~ (m1_subset_1 @ X5 @ (u1_struct_0 @ X3))
% 0.79/1.01          | ~ (r1_tmap_1 @ X3 @ X0 @ (k3_tmap_1 @ X2 @ X0 @ sk_D @ X3 @ X1) @ 
% 0.79/1.01               X5)
% 0.79/1.01          | (r1_tmap_1 @ sk_D @ X0 @ X1 @ X5)
% 0.79/1.01          | ~ (m1_connsp_2 @ X4 @ sk_D @ X5)
% 0.79/1.01          | ~ (r1_tarski @ X4 @ (u1_struct_0 @ X3))
% 0.79/1.01          | ~ (m1_subset_1 @ X5 @ (k2_struct_0 @ sk_C))
% 0.79/1.01          | ~ (v1_funct_2 @ X1 @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ X0))
% 0.79/1.01          | ~ (v1_funct_1 @ X1)
% 0.79/1.01          | ~ (m1_pre_topc @ X3 @ X2)
% 0.79/1.01          | (v2_struct_0 @ X3)
% 0.79/1.01          | ~ (l1_pre_topc @ X2)
% 0.79/1.01          | ~ (v2_pre_topc @ X2)
% 0.79/1.01          | (v2_struct_0 @ X2))),
% 0.79/1.01      inference('demod', [status(thm)], ['70', '71', '72', '73'])).
% 0.79/1.01  thf('75', plain,
% 0.79/1.01      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.79/1.01         ((v2_struct_0 @ X0)
% 0.79/1.01          | ~ (v2_pre_topc @ X0)
% 0.79/1.01          | ~ (l1_pre_topc @ X0)
% 0.79/1.01          | (v2_struct_0 @ X1)
% 0.79/1.01          | ~ (m1_pre_topc @ X1 @ X0)
% 0.79/1.01          | ~ (v1_funct_1 @ sk_E)
% 0.79/1.01          | ~ (v1_funct_2 @ sk_E @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))
% 0.79/1.01          | ~ (m1_subset_1 @ X2 @ (k2_struct_0 @ sk_C))
% 0.79/1.01          | ~ (r1_tarski @ X3 @ (u1_struct_0 @ X1))
% 0.79/1.01          | ~ (m1_connsp_2 @ X3 @ sk_D @ X2)
% 0.79/1.01          | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X2)
% 0.79/1.01          | ~ (r1_tmap_1 @ X1 @ sk_B @ 
% 0.79/1.01               (k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E) @ X2)
% 0.79/1.01          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1))
% 0.79/1.01          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_C)))
% 0.79/1.01          | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.79/1.01          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.79/1.01          | (v2_struct_0 @ sk_D)
% 0.79/1.01          | ~ (l1_pre_topc @ sk_B)
% 0.79/1.01          | ~ (v2_pre_topc @ sk_B)
% 0.79/1.01          | (v2_struct_0 @ sk_B))),
% 0.79/1.01      inference('sup-', [status(thm)], ['62', '74'])).
% 0.79/1.01  thf('76', plain, ((v1_funct_1 @ sk_E)),
% 0.79/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.01  thf('77', plain,
% 0.79/1.01      (![X13 : $i]:
% 0.79/1.01         (((k2_struct_0 @ X13) = (u1_struct_0 @ X13)) | ~ (l1_struct_0 @ X13))),
% 0.79/1.01      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.79/1.01  thf('78', plain,
% 0.79/1.01      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 0.79/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.01  thf('79', plain,
% 0.79/1.01      (((v1_funct_2 @ sk_E @ (k2_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.79/1.01        | ~ (l1_struct_0 @ sk_D))),
% 0.79/1.01      inference('sup+', [status(thm)], ['77', '78'])).
% 0.79/1.01  thf('80', plain, ((l1_struct_0 @ sk_D)),
% 0.79/1.01      inference('sup-', [status(thm)], ['50', '51'])).
% 0.79/1.01  thf('81', plain,
% 0.79/1.01      ((v1_funct_2 @ sk_E @ (k2_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 0.79/1.01      inference('demod', [status(thm)], ['79', '80'])).
% 0.79/1.01  thf('82', plain, (((k2_struct_0 @ sk_C) = (k2_struct_0 @ sk_D))),
% 0.79/1.01      inference('demod', [status(thm)], ['56', '59'])).
% 0.79/1.01  thf('83', plain,
% 0.79/1.01      ((v1_funct_2 @ sk_E @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 0.79/1.01      inference('demod', [status(thm)], ['81', '82'])).
% 0.79/1.01  thf('84', plain, ((l1_pre_topc @ sk_B)),
% 0.79/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.01  thf('85', plain, ((v2_pre_topc @ sk_B)),
% 0.79/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.01  thf('86', plain,
% 0.79/1.01      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.79/1.01         ((v2_struct_0 @ X0)
% 0.79/1.01          | ~ (v2_pre_topc @ X0)
% 0.79/1.01          | ~ (l1_pre_topc @ X0)
% 0.79/1.01          | (v2_struct_0 @ X1)
% 0.79/1.01          | ~ (m1_pre_topc @ X1 @ X0)
% 0.79/1.01          | ~ (m1_subset_1 @ X2 @ (k2_struct_0 @ sk_C))
% 0.79/1.01          | ~ (r1_tarski @ X3 @ (u1_struct_0 @ X1))
% 0.79/1.01          | ~ (m1_connsp_2 @ X3 @ sk_D @ X2)
% 0.79/1.01          | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X2)
% 0.79/1.01          | ~ (r1_tmap_1 @ X1 @ sk_B @ 
% 0.79/1.01               (k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E) @ X2)
% 0.79/1.01          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1))
% 0.79/1.01          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_C)))
% 0.79/1.01          | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.79/1.01          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.79/1.01          | (v2_struct_0 @ sk_D)
% 0.79/1.01          | (v2_struct_0 @ sk_B))),
% 0.79/1.01      inference('demod', [status(thm)], ['75', '76', '83', '84', '85'])).
% 0.79/1.01  thf('87', plain,
% 0.79/1.01      (![X0 : $i]:
% 0.79/1.01         ((v2_struct_0 @ sk_B)
% 0.79/1.01          | (v2_struct_0 @ sk_D)
% 0.79/1.01          | ~ (m1_pre_topc @ sk_D @ sk_A)
% 0.79/1.01          | ~ (m1_pre_topc @ sk_C @ sk_D)
% 0.79/1.01          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_C)))
% 0.79/1.01          | ~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C))
% 0.79/1.01          | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)
% 0.79/1.01          | ~ (m1_connsp_2 @ X0 @ sk_D @ sk_F)
% 0.79/1.01          | ~ (r1_tarski @ X0 @ (u1_struct_0 @ sk_C))
% 0.79/1.01          | ~ (m1_subset_1 @ sk_F @ (k2_struct_0 @ sk_C))
% 0.79/1.01          | ~ (m1_pre_topc @ sk_C @ sk_A)
% 0.79/1.01          | (v2_struct_0 @ sk_C)
% 0.79/1.01          | ~ (l1_pre_topc @ sk_A)
% 0.79/1.01          | ~ (v2_pre_topc @ sk_A)
% 0.79/1.01          | (v2_struct_0 @ sk_A))),
% 0.79/1.01      inference('sup-', [status(thm)], ['7', '86'])).
% 0.79/1.01  thf('88', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.79/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.01  thf('89', plain,
% 0.79/1.01      (((g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) = (sk_D))),
% 0.79/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.01  thf('90', plain,
% 0.79/1.01      (![X0 : $i]:
% 0.79/1.01         ((m1_pre_topc @ X0 @ 
% 0.79/1.01           (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.79/1.01          | ~ (l1_pre_topc @ X0))),
% 0.79/1.01      inference('simplify', [status(thm)], ['36'])).
% 0.79/1.01  thf('91', plain, (((m1_pre_topc @ sk_C @ sk_D) | ~ (l1_pre_topc @ sk_C))),
% 0.79/1.01      inference('sup+', [status(thm)], ['89', '90'])).
% 0.79/1.01  thf('92', plain, ((l1_pre_topc @ sk_C)),
% 0.79/1.01      inference('demod', [status(thm)], ['23', '24'])).
% 0.79/1.01  thf('93', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 0.79/1.01      inference('demod', [status(thm)], ['91', '92'])).
% 0.79/1.01  thf('94', plain, (((u1_struct_0 @ sk_C) = (k2_struct_0 @ sk_C))),
% 0.79/1.01      inference('demod', [status(thm)], ['53', '60'])).
% 0.79/1.01  thf('95', plain,
% 0.79/1.01      (![X13 : $i]:
% 0.79/1.01         (((k2_struct_0 @ X13) = (u1_struct_0 @ X13)) | ~ (l1_struct_0 @ X13))),
% 0.79/1.01      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.79/1.01  thf('96', plain, ((m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_C))),
% 0.79/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.01  thf('97', plain, (((sk_F) = (sk_G))),
% 0.79/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.01  thf('98', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C))),
% 0.79/1.01      inference('demod', [status(thm)], ['96', '97'])).
% 0.79/1.01  thf('99', plain,
% 0.79/1.01      (((m1_subset_1 @ sk_F @ (k2_struct_0 @ sk_C)) | ~ (l1_struct_0 @ sk_C))),
% 0.79/1.01      inference('sup+', [status(thm)], ['95', '98'])).
% 0.79/1.01  thf('100', plain, ((l1_struct_0 @ sk_C)),
% 0.79/1.01      inference('sup-', [status(thm)], ['57', '58'])).
% 0.79/1.01  thf('101', plain, ((m1_subset_1 @ sk_F @ (k2_struct_0 @ sk_C))),
% 0.79/1.01      inference('demod', [status(thm)], ['99', '100'])).
% 0.79/1.01  thf('102', plain, (((u1_struct_0 @ sk_C) = (k2_struct_0 @ sk_C))),
% 0.79/1.01      inference('demod', [status(thm)], ['53', '60'])).
% 0.79/1.01  thf('103', plain, ((m1_subset_1 @ sk_F @ (k2_struct_0 @ sk_C))),
% 0.79/1.01      inference('demod', [status(thm)], ['99', '100'])).
% 0.79/1.01  thf('104', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.79/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.01  thf('105', plain, ((l1_pre_topc @ sk_A)),
% 0.79/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.01  thf('106', plain, ((v2_pre_topc @ sk_A)),
% 0.79/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.01  thf('107', plain,
% 0.79/1.01      (![X0 : $i]:
% 0.79/1.01         ((v2_struct_0 @ sk_B)
% 0.79/1.01          | (v2_struct_0 @ sk_D)
% 0.79/1.01          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_C)))
% 0.79/1.01          | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)
% 0.79/1.01          | ~ (m1_connsp_2 @ X0 @ sk_D @ sk_F)
% 0.79/1.01          | ~ (r1_tarski @ X0 @ (k2_struct_0 @ sk_C))
% 0.79/1.01          | (v2_struct_0 @ sk_C)
% 0.79/1.01          | (v2_struct_0 @ sk_A))),
% 0.79/1.01      inference('demod', [status(thm)],
% 0.79/1.01                ['87', '88', '93', '94', '101', '102', '103', '104', '105', 
% 0.79/1.01                 '106'])).
% 0.79/1.01  thf('108', plain,
% 0.79/1.01      (((v2_struct_0 @ sk_A)
% 0.79/1.01        | (v2_struct_0 @ sk_C)
% 0.79/1.01        | ~ (r1_tarski @ (k2_struct_0 @ sk_C) @ (k2_struct_0 @ sk_C))
% 0.79/1.01        | ~ (m1_connsp_2 @ (k2_struct_0 @ sk_C) @ sk_D @ sk_F)
% 0.79/1.01        | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)
% 0.79/1.01        | (v2_struct_0 @ sk_D)
% 0.79/1.01        | (v2_struct_0 @ sk_B))),
% 0.79/1.01      inference('sup-', [status(thm)], ['4', '107'])).
% 0.79/1.01  thf('109', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.79/1.01      inference('simplify', [status(thm)], ['1'])).
% 0.79/1.01  thf('110', plain,
% 0.79/1.01      (![X13 : $i]:
% 0.79/1.01         (((k2_struct_0 @ X13) = (u1_struct_0 @ X13)) | ~ (l1_struct_0 @ X13))),
% 0.79/1.01      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.79/1.01  thf('111', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_D))),
% 0.79/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.01  thf('112', plain,
% 0.79/1.01      (((m1_subset_1 @ sk_F @ (k2_struct_0 @ sk_D)) | ~ (l1_struct_0 @ sk_D))),
% 0.79/1.01      inference('sup+', [status(thm)], ['110', '111'])).
% 0.79/1.01  thf('113', plain, ((l1_struct_0 @ sk_D)),
% 0.79/1.01      inference('sup-', [status(thm)], ['50', '51'])).
% 0.79/1.01  thf('114', plain, ((m1_subset_1 @ sk_F @ (k2_struct_0 @ sk_D))),
% 0.79/1.01      inference('demod', [status(thm)], ['112', '113'])).
% 0.79/1.01  thf('115', plain,
% 0.79/1.01      (![X13 : $i]:
% 0.79/1.01         (((k2_struct_0 @ X13) = (u1_struct_0 @ X13)) | ~ (l1_struct_0 @ X13))),
% 0.79/1.01      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.79/1.01  thf('116', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.79/1.01      inference('sup-', [status(thm)], ['2', '3'])).
% 0.79/1.01  thf(t5_connsp_2, axiom,
% 0.79/1.01    (![A:$i]:
% 0.79/1.01     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.79/1.01       ( ![B:$i]:
% 0.79/1.01         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.79/1.01           ( ![C:$i]:
% 0.79/1.01             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.79/1.01               ( ( ( v3_pre_topc @ B @ A ) & ( r2_hidden @ C @ B ) ) =>
% 0.79/1.01                 ( m1_connsp_2 @ B @ A @ C ) ) ) ) ) ) ))).
% 0.79/1.01  thf('117', plain,
% 0.79/1.01      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.79/1.01         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 0.79/1.01          | ~ (v3_pre_topc @ X21 @ X22)
% 0.79/1.01          | ~ (r2_hidden @ X23 @ X21)
% 0.79/1.01          | (m1_connsp_2 @ X21 @ X22 @ X23)
% 0.79/1.01          | ~ (m1_subset_1 @ X23 @ (u1_struct_0 @ X22))
% 0.79/1.01          | ~ (l1_pre_topc @ X22)
% 0.79/1.01          | ~ (v2_pre_topc @ X22)
% 0.79/1.01          | (v2_struct_0 @ X22))),
% 0.79/1.01      inference('cnf', [status(esa)], [t5_connsp_2])).
% 0.79/1.01  thf('118', plain,
% 0.79/1.01      (![X0 : $i, X1 : $i]:
% 0.79/1.01         ((v2_struct_0 @ X0)
% 0.79/1.01          | ~ (v2_pre_topc @ X0)
% 0.79/1.01          | ~ (l1_pre_topc @ X0)
% 0.79/1.01          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.79/1.01          | (m1_connsp_2 @ (u1_struct_0 @ X0) @ X0 @ X1)
% 0.79/1.01          | ~ (r2_hidden @ X1 @ (u1_struct_0 @ X0))
% 0.79/1.01          | ~ (v3_pre_topc @ (u1_struct_0 @ X0) @ X0))),
% 0.79/1.01      inference('sup-', [status(thm)], ['116', '117'])).
% 0.79/1.01  thf('119', plain,
% 0.79/1.01      (![X0 : $i, X1 : $i]:
% 0.79/1.01         (~ (m1_subset_1 @ X1 @ (k2_struct_0 @ X0))
% 0.79/1.01          | ~ (l1_struct_0 @ X0)
% 0.79/1.01          | ~ (v3_pre_topc @ (u1_struct_0 @ X0) @ X0)
% 0.79/1.01          | ~ (r2_hidden @ X1 @ (u1_struct_0 @ X0))
% 0.79/1.01          | (m1_connsp_2 @ (u1_struct_0 @ X0) @ X0 @ X1)
% 0.79/1.01          | ~ (l1_pre_topc @ X0)
% 0.79/1.01          | ~ (v2_pre_topc @ X0)
% 0.79/1.01          | (v2_struct_0 @ X0))),
% 0.79/1.01      inference('sup-', [status(thm)], ['115', '118'])).
% 0.79/1.01  thf('120', plain,
% 0.79/1.01      (((v2_struct_0 @ sk_D)
% 0.79/1.01        | ~ (v2_pre_topc @ sk_D)
% 0.79/1.01        | ~ (l1_pre_topc @ sk_D)
% 0.79/1.01        | (m1_connsp_2 @ (u1_struct_0 @ sk_D) @ sk_D @ sk_F)
% 0.79/1.01        | ~ (r2_hidden @ sk_F @ (u1_struct_0 @ sk_D))
% 0.79/1.01        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_D) @ sk_D)
% 0.79/1.01        | ~ (l1_struct_0 @ sk_D))),
% 0.79/1.01      inference('sup-', [status(thm)], ['114', '119'])).
% 0.79/1.01  thf('121', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.79/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.01  thf(cc1_pre_topc, axiom,
% 0.79/1.01    (![A:$i]:
% 0.79/1.01     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.79/1.01       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( v2_pre_topc @ B ) ) ) ))).
% 0.79/1.01  thf('122', plain,
% 0.79/1.01      (![X11 : $i, X12 : $i]:
% 0.79/1.01         (~ (m1_pre_topc @ X11 @ X12)
% 0.79/1.01          | (v2_pre_topc @ X11)
% 0.79/1.01          | ~ (l1_pre_topc @ X12)
% 0.79/1.01          | ~ (v2_pre_topc @ X12))),
% 0.79/1.01      inference('cnf', [status(esa)], [cc1_pre_topc])).
% 0.79/1.01  thf('123', plain,
% 0.79/1.01      ((~ (v2_pre_topc @ sk_A) | ~ (l1_pre_topc @ sk_A) | (v2_pre_topc @ sk_D))),
% 0.79/1.01      inference('sup-', [status(thm)], ['121', '122'])).
% 0.79/1.01  thf('124', plain, ((v2_pre_topc @ sk_A)),
% 0.79/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.01  thf('125', plain, ((l1_pre_topc @ sk_A)),
% 0.79/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.01  thf('126', plain, ((v2_pre_topc @ sk_D)),
% 0.79/1.01      inference('demod', [status(thm)], ['123', '124', '125'])).
% 0.79/1.01  thf('127', plain, ((l1_pre_topc @ sk_D)),
% 0.79/1.01      inference('demod', [status(thm)], ['17', '18'])).
% 0.79/1.01  thf('128', plain, ((l1_struct_0 @ sk_D)),
% 0.79/1.01      inference('sup-', [status(thm)], ['50', '51'])).
% 0.79/1.01  thf('129', plain,
% 0.79/1.01      (((v2_struct_0 @ sk_D)
% 0.79/1.01        | (m1_connsp_2 @ (u1_struct_0 @ sk_D) @ sk_D @ sk_F)
% 0.79/1.01        | ~ (r2_hidden @ sk_F @ (u1_struct_0 @ sk_D))
% 0.79/1.01        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_D) @ sk_D))),
% 0.79/1.01      inference('demod', [status(thm)], ['120', '126', '127', '128'])).
% 0.79/1.01  thf('130', plain, (((k2_struct_0 @ sk_C) = (u1_struct_0 @ sk_D))),
% 0.79/1.01      inference('demod', [status(thm)], ['65', '66'])).
% 0.79/1.01  thf('131', plain, (((k2_struct_0 @ sk_C) = (u1_struct_0 @ sk_D))),
% 0.79/1.01      inference('demod', [status(thm)], ['65', '66'])).
% 0.79/1.01  thf('132', plain,
% 0.79/1.01      (![X13 : $i]:
% 0.79/1.01         (((k2_struct_0 @ X13) = (u1_struct_0 @ X13)) | ~ (l1_struct_0 @ X13))),
% 0.79/1.01      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.79/1.01  thf('133', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C))),
% 0.79/1.01      inference('demod', [status(thm)], ['96', '97'])).
% 0.79/1.01  thf(t2_subset, axiom,
% 0.79/1.01    (![A:$i,B:$i]:
% 0.79/1.01     ( ( m1_subset_1 @ A @ B ) =>
% 0.79/1.01       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.79/1.01  thf('134', plain,
% 0.79/1.01      (![X3 : $i, X4 : $i]:
% 0.79/1.01         ((r2_hidden @ X3 @ X4)
% 0.79/1.01          | (v1_xboole_0 @ X4)
% 0.79/1.01          | ~ (m1_subset_1 @ X3 @ X4))),
% 0.79/1.01      inference('cnf', [status(esa)], [t2_subset])).
% 0.79/1.01  thf('135', plain,
% 0.79/1.01      (((v1_xboole_0 @ (u1_struct_0 @ sk_C))
% 0.79/1.01        | (r2_hidden @ sk_F @ (u1_struct_0 @ sk_C)))),
% 0.79/1.01      inference('sup-', [status(thm)], ['133', '134'])).
% 0.79/1.01  thf('136', plain,
% 0.79/1.01      (((r2_hidden @ sk_F @ (k2_struct_0 @ sk_C))
% 0.79/1.01        | ~ (l1_struct_0 @ sk_C)
% 0.79/1.01        | (v1_xboole_0 @ (u1_struct_0 @ sk_C)))),
% 0.79/1.01      inference('sup+', [status(thm)], ['132', '135'])).
% 0.79/1.01  thf('137', plain, ((l1_struct_0 @ sk_C)),
% 0.79/1.01      inference('sup-', [status(thm)], ['57', '58'])).
% 0.79/1.01  thf('138', plain,
% 0.79/1.01      (((r2_hidden @ sk_F @ (k2_struct_0 @ sk_C))
% 0.79/1.01        | (v1_xboole_0 @ (u1_struct_0 @ sk_C)))),
% 0.79/1.01      inference('demod', [status(thm)], ['136', '137'])).
% 0.79/1.01  thf(fc2_struct_0, axiom,
% 0.79/1.01    (![A:$i]:
% 0.79/1.01     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.79/1.01       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.79/1.01  thf('139', plain,
% 0.79/1.01      (![X17 : $i]:
% 0.79/1.01         (~ (v1_xboole_0 @ (u1_struct_0 @ X17))
% 0.79/1.01          | ~ (l1_struct_0 @ X17)
% 0.79/1.01          | (v2_struct_0 @ X17))),
% 0.79/1.01      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.79/1.01  thf('140', plain,
% 0.79/1.01      (((r2_hidden @ sk_F @ (k2_struct_0 @ sk_C))
% 0.79/1.01        | (v2_struct_0 @ sk_C)
% 0.79/1.01        | ~ (l1_struct_0 @ sk_C))),
% 0.79/1.01      inference('sup-', [status(thm)], ['138', '139'])).
% 0.79/1.01  thf('141', plain, ((l1_struct_0 @ sk_C)),
% 0.79/1.01      inference('sup-', [status(thm)], ['57', '58'])).
% 0.79/1.01  thf('142', plain,
% 0.79/1.01      (((r2_hidden @ sk_F @ (k2_struct_0 @ sk_C)) | (v2_struct_0 @ sk_C))),
% 0.79/1.01      inference('demod', [status(thm)], ['140', '141'])).
% 0.79/1.01  thf('143', plain, (~ (v2_struct_0 @ sk_C)),
% 0.79/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.01  thf('144', plain, ((r2_hidden @ sk_F @ (k2_struct_0 @ sk_C))),
% 0.79/1.01      inference('clc', [status(thm)], ['142', '143'])).
% 0.79/1.01  thf('145', plain, (((k2_struct_0 @ sk_C) = (u1_struct_0 @ sk_D))),
% 0.79/1.01      inference('demod', [status(thm)], ['65', '66'])).
% 0.79/1.01  thf('146', plain, (((k2_struct_0 @ sk_C) = (k2_struct_0 @ sk_D))),
% 0.79/1.01      inference('demod', [status(thm)], ['56', '59'])).
% 0.79/1.01  thf(fc10_tops_1, axiom,
% 0.79/1.01    (![A:$i]:
% 0.79/1.01     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.79/1.01       ( v3_pre_topc @ ( k2_struct_0 @ A ) @ A ) ))).
% 0.79/1.01  thf('147', plain,
% 0.79/1.01      (![X20 : $i]:
% 0.79/1.01         ((v3_pre_topc @ (k2_struct_0 @ X20) @ X20)
% 0.79/1.01          | ~ (l1_pre_topc @ X20)
% 0.79/1.01          | ~ (v2_pre_topc @ X20))),
% 0.79/1.01      inference('cnf', [status(esa)], [fc10_tops_1])).
% 0.79/1.01  thf('148', plain,
% 0.79/1.01      (((v3_pre_topc @ (k2_struct_0 @ sk_C) @ sk_D)
% 0.79/1.01        | ~ (v2_pre_topc @ sk_D)
% 0.79/1.01        | ~ (l1_pre_topc @ sk_D))),
% 0.79/1.01      inference('sup+', [status(thm)], ['146', '147'])).
% 0.79/1.01  thf('149', plain, ((v2_pre_topc @ sk_D)),
% 0.79/1.01      inference('demod', [status(thm)], ['123', '124', '125'])).
% 0.79/1.01  thf('150', plain, ((l1_pre_topc @ sk_D)),
% 0.79/1.01      inference('demod', [status(thm)], ['17', '18'])).
% 0.79/1.01  thf('151', plain, ((v3_pre_topc @ (k2_struct_0 @ sk_C) @ sk_D)),
% 0.79/1.01      inference('demod', [status(thm)], ['148', '149', '150'])).
% 0.79/1.01  thf('152', plain,
% 0.79/1.01      (((v2_struct_0 @ sk_D)
% 0.79/1.01        | (m1_connsp_2 @ (k2_struct_0 @ sk_C) @ sk_D @ sk_F))),
% 0.79/1.01      inference('demod', [status(thm)],
% 0.79/1.01                ['129', '130', '131', '144', '145', '151'])).
% 0.79/1.01  thf('153', plain, (~ (v2_struct_0 @ sk_D)),
% 0.79/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.01  thf('154', plain, ((m1_connsp_2 @ (k2_struct_0 @ sk_C) @ sk_D @ sk_F)),
% 0.79/1.01      inference('clc', [status(thm)], ['152', '153'])).
% 0.79/1.01  thf('155', plain,
% 0.79/1.01      (((v2_struct_0 @ sk_A)
% 0.79/1.01        | (v2_struct_0 @ sk_C)
% 0.79/1.01        | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)
% 0.79/1.01        | (v2_struct_0 @ sk_D)
% 0.79/1.01        | (v2_struct_0 @ sk_B))),
% 0.79/1.01      inference('demod', [status(thm)], ['108', '109', '154'])).
% 0.79/1.01  thf('156', plain, (~ (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)),
% 0.79/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.01  thf('157', plain,
% 0.79/1.01      (((v2_struct_0 @ sk_B)
% 0.79/1.01        | (v2_struct_0 @ sk_D)
% 0.79/1.01        | (v2_struct_0 @ sk_C)
% 0.79/1.01        | (v2_struct_0 @ sk_A))),
% 0.79/1.01      inference('sup-', [status(thm)], ['155', '156'])).
% 0.79/1.01  thf('158', plain, (~ (v2_struct_0 @ sk_D)),
% 0.79/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.01  thf('159', plain,
% 0.79/1.01      (((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_B))),
% 0.79/1.01      inference('sup-', [status(thm)], ['157', '158'])).
% 0.79/1.01  thf('160', plain, (~ (v2_struct_0 @ sk_A)),
% 0.79/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.01  thf('161', plain, (((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_C))),
% 0.79/1.01      inference('clc', [status(thm)], ['159', '160'])).
% 0.79/1.01  thf('162', plain, (~ (v2_struct_0 @ sk_B)),
% 0.79/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.01  thf('163', plain, ((v2_struct_0 @ sk_C)),
% 0.79/1.01      inference('clc', [status(thm)], ['161', '162'])).
% 0.79/1.01  thf('164', plain, ($false), inference('demod', [status(thm)], ['0', '163'])).
% 0.79/1.01  
% 0.79/1.01  % SZS output end Refutation
% 0.79/1.01  
% 0.79/1.02  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
