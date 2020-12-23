%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.moK85r9vhZ

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:10:31 EST 2020

% Result     : Theorem 1.18s
% Output     : Refutation 1.18s
% Verified   : 
% Statistics : Number of formulae       :  413 (21541 expanded)
%              Number of leaves         :   48 (6177 expanded)
%              Depth                    :   45
%              Number of atoms          : 4199 (572834 expanded)
%              Number of equality atoms :  114 (15194 expanded)
%              Maximal formula depth    :   26 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_tsep_1_type,type,(
    v1_tsep_1: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(k2_partfun1_type,type,(
    k2_partfun1: $i > $i > $i > $i > $i )).

thf(sk_G_type,type,(
    sk_G: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(r1_tmap_1_type,type,(
    r1_tmap_1: $i > $i > $i > $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k3_tmap_1_type,type,(
    k3_tmap_1: $i > $i > $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(k2_tmap_1_type,type,(
    k2_tmap_1: $i > $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(g1_pre_topc_type,type,(
    g1_pre_topc: $i > $i > $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

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
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( m1_pre_topc @ A @ A ) ) )).

thf('1',plain,(
    ! [X36: $i] :
      ( ( m1_pre_topc @ X36 @ X36 )
      | ~ ( l1_pre_topc @ X36 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('2',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) )
    = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t59_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) )
         => ( m1_pre_topc @ B @ A ) ) ) )).

thf('3',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( m1_pre_topc @ X14 @ ( g1_pre_topc @ ( u1_struct_0 @ X15 ) @ ( u1_pre_topc @ X15 ) ) )
      | ( m1_pre_topc @ X14 @ X15 )
      | ~ ( l1_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[t59_pre_topc])).

thf('4',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_D )
      | ~ ( l1_pre_topc @ sk_C )
      | ( m1_pre_topc @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('6',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( m1_pre_topc @ X9 @ X10 )
      | ( l1_pre_topc @ X9 )
      | ~ ( l1_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('7',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_C ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( m1_pre_topc @ X0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['4','9'])).

thf('11',plain,
    ( ~ ( l1_pre_topc @ sk_D )
    | ( m1_pre_topc @ sk_D @ sk_C ) ),
    inference('sup-',[status(thm)],['1','10'])).

thf('12',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( m1_pre_topc @ X9 @ X10 )
      | ( l1_pre_topc @ X9 )
      | ~ ( l1_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('14',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_D ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,(
    m1_pre_topc @ sk_D @ sk_C ),
    inference(demod,[status(thm)],['11','16'])).

thf('18',plain,(
    ! [X36: $i] :
      ( ( m1_pre_topc @ X36 @ X36 )
      | ~ ( l1_pre_topc @ X36 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf(t4_tsep_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ! [C: $i] :
              ( ( m1_pre_topc @ C @ A )
             => ( ( r1_tarski @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ C ) )
              <=> ( m1_pre_topc @ B @ C ) ) ) ) ) )).

thf('19',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ~ ( m1_pre_topc @ X37 @ X38 )
      | ~ ( m1_pre_topc @ X37 @ X39 )
      | ( r1_tarski @ ( u1_struct_0 @ X37 ) @ ( u1_struct_0 @ X39 ) )
      | ~ ( m1_pre_topc @ X39 @ X38 )
      | ~ ( l1_pre_topc @ X38 )
      | ~ ( v2_pre_topc @ X38 ) ) ),
    inference(cnf,[status(esa)],[t4_tsep_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ( r1_tarski @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X1 ) )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_pre_topc @ X0 @ X1 )
      | ( r1_tarski @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X1 ) )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,
    ( ~ ( l1_pre_topc @ sk_D )
    | ~ ( v2_pre_topc @ sk_D )
    | ~ ( m1_pre_topc @ sk_C @ sk_D )
    | ( r1_tarski @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['17','21'])).

thf('23',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['14','15'])).

thf('24',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( v2_pre_topc @ B ) ) ) )).

thf('25',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( m1_pre_topc @ X5 @ X6 )
      | ( v2_pre_topc @ X5 )
      | ~ ( l1_pre_topc @ X6 )
      | ~ ( v2_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[cc1_pre_topc])).

thf('26',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_pre_topc @ sk_D ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    v2_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['26','27','28'])).

thf('30',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) )
    = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    ! [X36: $i] :
      ( ( m1_pre_topc @ X36 @ X36 )
      | ~ ( l1_pre_topc @ X36 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf(t65_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( l1_pre_topc @ B )
         => ( ( m1_pre_topc @ A @ B )
          <=> ( m1_pre_topc @ A @ ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ) )).

thf('32',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( l1_pre_topc @ X19 )
      | ~ ( m1_pre_topc @ X20 @ X19 )
      | ( m1_pre_topc @ X20 @ ( g1_pre_topc @ ( u1_struct_0 @ X19 ) @ ( u1_pre_topc @ X19 ) ) )
      | ~ ( l1_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[t65_pre_topc])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,
    ( ( m1_pre_topc @ sk_C @ sk_D )
    | ~ ( l1_pre_topc @ sk_C ) ),
    inference('sup+',[status(thm)],['30','34'])).

thf('36',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['7','8'])).

thf('37',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['22','23','29','37'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('39',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('40',plain,
    ( ~ ( r1_tarski @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D ) )
    | ( ( u1_struct_0 @ sk_C )
      = ( u1_struct_0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ~ ( m1_pre_topc @ X37 @ X38 )
      | ~ ( m1_pre_topc @ X37 @ X39 )
      | ( r1_tarski @ ( u1_struct_0 @ X37 ) @ ( u1_struct_0 @ X39 ) )
      | ~ ( m1_pre_topc @ X39 @ X38 )
      | ~ ( l1_pre_topc @ X38 )
      | ~ ( v2_pre_topc @ X38 ) ) ),
    inference(cnf,[status(esa)],[t4_tsep_1])).

thf('44',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( r1_tarski @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( r1_tarski @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ sk_C @ X0 ) ) ),
    inference(demod,[status(thm)],['44','45','46'])).

thf('48',plain,
    ( ~ ( m1_pre_topc @ sk_C @ sk_D )
    | ( r1_tarski @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['41','47'])).

thf('49',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(demod,[status(thm)],['35','36'])).

thf('50',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,
    ( ( u1_struct_0 @ sk_C )
    = ( u1_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['40','50'])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('52',plain,(
    ! [X7: $i] :
      ( ( ( k2_struct_0 @ X7 )
        = ( u1_struct_0 @ X7 ) )
      | ~ ( l1_struct_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('53',plain,
    ( ( u1_struct_0 @ sk_C )
    = ( u1_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['40','50'])).

thf('54',plain,
    ( ( ( u1_struct_0 @ sk_C )
      = ( k2_struct_0 @ sk_D ) )
    | ~ ( l1_struct_0 @ sk_D ) ),
    inference('sup+',[status(thm)],['52','53'])).

thf('55',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['14','15'])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('56',plain,(
    ! [X8: $i] :
      ( ( l1_struct_0 @ X8 )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('57',plain,(
    l1_struct_0 @ sk_D ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,
    ( ( u1_struct_0 @ sk_C )
    = ( k2_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['54','57'])).

thf('59',plain,
    ( ( k2_struct_0 @ sk_D )
    = ( u1_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['51','58'])).

thf('60',plain,(
    ! [X7: $i] :
      ( ( ( k2_struct_0 @ X7 )
        = ( u1_struct_0 @ X7 ) )
      | ~ ( l1_struct_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('61',plain,
    ( ( u1_struct_0 @ sk_C )
    = ( k2_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['54','57'])).

thf('62',plain,
    ( ( ( k2_struct_0 @ sk_C )
      = ( k2_struct_0 @ sk_D ) )
    | ~ ( l1_struct_0 @ sk_C ) ),
    inference('sup+',[status(thm)],['60','61'])).

thf('63',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['7','8'])).

thf('64',plain,(
    ! [X8: $i] :
      ( ( l1_struct_0 @ X8 )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('65',plain,(
    l1_struct_0 @ sk_C ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,
    ( ( k2_struct_0 @ sk_C )
    = ( k2_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['62','65'])).

thf('67',plain,
    ( ( k2_struct_0 @ sk_C )
    = ( u1_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['59','66'])).

thf('68',plain,(
    r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    sk_F = sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_F ),
    inference(demod,[status(thm)],['68','69'])).

thf('71',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_tmap_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( v2_pre_topc @ B )
            & ( l1_pre_topc @ B ) )
         => ! [C: $i] :
              ( ( m1_pre_topc @ C @ A )
             => ! [D: $i] :
                  ( ( m1_pre_topc @ D @ A )
                 => ! [E: $i] :
                      ( ( ( v1_funct_1 @ E )
                        & ( v1_funct_2 @ E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) )
                        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) )
                     => ( ( m1_pre_topc @ D @ C )
                       => ( ( k3_tmap_1 @ A @ B @ C @ D @ E )
                          = ( k2_partfun1 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ E @ ( u1_struct_0 @ D ) ) ) ) ) ) ) ) ) )).

thf('74',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ( v2_struct_0 @ X26 )
      | ~ ( v2_pre_topc @ X26 )
      | ~ ( l1_pre_topc @ X26 )
      | ~ ( m1_pre_topc @ X27 @ X28 )
      | ~ ( m1_pre_topc @ X27 @ X29 )
      | ( ( k3_tmap_1 @ X28 @ X26 @ X29 @ X27 @ X30 )
        = ( k2_partfun1 @ ( u1_struct_0 @ X29 ) @ ( u1_struct_0 @ X26 ) @ X30 @ ( u1_struct_0 @ X27 ) ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X29 ) @ ( u1_struct_0 @ X26 ) ) ) )
      | ~ ( v1_funct_2 @ X30 @ ( u1_struct_0 @ X29 ) @ ( u1_struct_0 @ X26 ) )
      | ~ ( v1_funct_1 @ X30 )
      | ~ ( m1_pre_topc @ X29 @ X28 )
      | ~ ( l1_pre_topc @ X28 )
      | ~ ( v2_pre_topc @ X28 )
      | ( v2_struct_0 @ X28 ) ) ),
    inference(cnf,[status(esa)],[d5_tmap_1])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      | ( ( k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( m1_pre_topc @ X1 @ sk_D )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ( ( k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( m1_pre_topc @ X1 @ sk_D )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['75','76','77','78','79'])).

thf('81',plain,
    ( ( k2_struct_0 @ sk_C )
    = ( u1_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['59','66'])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ( ( k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E )
        = ( k2_partfun1 @ ( k2_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( m1_pre_topc @ X1 @ sk_D )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ X0 @ sk_E )
        = ( k2_partfun1 @ ( k2_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['72','82'])).

thf('84',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ X0 @ sk_E )
        = ( k2_partfun1 @ ( k2_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ X0 ) ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['83','84','85'])).

thf('87',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E )
      = ( k2_partfun1 @ ( k2_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ sk_C ) ) )
    | ~ ( m1_pre_topc @ sk_C @ sk_D )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['71','86'])).

thf('88',plain,
    ( ( u1_struct_0 @ sk_C )
    = ( k2_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['54','57'])).

thf('89',plain,
    ( ( k2_struct_0 @ sk_C )
    = ( k2_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['62','65'])).

thf('90',plain,
    ( ( u1_struct_0 @ sk_C )
    = ( k2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['88','89'])).

thf('91',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(demod,[status(thm)],['35','36'])).

thf('92',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d4_tmap_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( v2_pre_topc @ B )
            & ( l1_pre_topc @ B ) )
         => ! [C: $i] :
              ( ( ( v1_funct_1 @ C )
                & ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
                & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) )
             => ! [D: $i] :
                  ( ( m1_pre_topc @ D @ A )
                 => ( ( k2_tmap_1 @ A @ B @ C @ D )
                    = ( k2_partfun1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ ( u1_struct_0 @ D ) ) ) ) ) ) ) )).

thf('93',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ( v2_struct_0 @ X22 )
      | ~ ( v2_pre_topc @ X22 )
      | ~ ( l1_pre_topc @ X22 )
      | ~ ( m1_pre_topc @ X23 @ X24 )
      | ( ( k2_tmap_1 @ X24 @ X22 @ X25 @ X23 )
        = ( k2_partfun1 @ ( u1_struct_0 @ X24 ) @ ( u1_struct_0 @ X22 ) @ X25 @ ( u1_struct_0 @ X23 ) ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X24 ) @ ( u1_struct_0 @ X22 ) ) ) )
      | ~ ( v1_funct_2 @ X25 @ ( u1_struct_0 @ X24 ) @ ( u1_struct_0 @ X22 ) )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( l1_pre_topc @ X24 )
      | ~ ( v2_pre_topc @ X24 )
      | ( v2_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d4_tmap_1])).

thf('94',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_D )
      | ~ ( v2_pre_topc @ sk_D )
      | ~ ( l1_pre_topc @ sk_D )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      | ( ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0 )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,(
    v2_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['26','27','28'])).

thf('96',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['14','15'])).

thf('97',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_D )
      | ( ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0 )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['94','95','96','97','98','99','100'])).

thf('102',plain,
    ( ( k2_struct_0 @ sk_C )
    = ( u1_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['59','66'])).

thf('103',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_D )
      | ( ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0 )
        = ( k2_partfun1 @ ( k2_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['101','102'])).

thf('104',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C )
      = ( k2_partfun1 @ ( k2_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ sk_C ) ) )
    | ( v2_struct_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['91','103'])).

thf('105',plain,
    ( ( u1_struct_0 @ sk_C )
    = ( k2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['88','89'])).

thf('106',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C )
      = ( k2_partfun1 @ ( k2_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( k2_struct_0 @ sk_C ) ) )
    | ( v2_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['104','105'])).

thf('107',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C )
      = ( k2_partfun1 @ ( k2_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( k2_struct_0 @ sk_C ) ) ) ),
    inference(clc,[status(thm)],['106','107'])).

thf('109',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,
    ( ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C )
    = ( k2_partfun1 @ ( k2_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( k2_struct_0 @ sk_C ) ) ),
    inference(clc,[status(thm)],['108','109'])).

thf('111',plain,(
    ! [X36: $i] :
      ( ( m1_pre_topc @ X36 @ X36 )
      | ~ ( l1_pre_topc @ X36 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('112',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,
    ( ( u1_struct_0 @ sk_C )
    = ( u1_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['40','50'])).

thf('114',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['112','113'])).

thf('115',plain,
    ( ( u1_struct_0 @ sk_C )
    = ( k2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['88','89'])).

thf('116',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['114','115'])).

thf('117',plain,(
    ! [X7: $i] :
      ( ( ( k2_struct_0 @ X7 )
        = ( u1_struct_0 @ X7 ) )
      | ~ ( l1_struct_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('118',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ( v2_struct_0 @ X22 )
      | ~ ( v2_pre_topc @ X22 )
      | ~ ( l1_pre_topc @ X22 )
      | ~ ( m1_pre_topc @ X23 @ X24 )
      | ( ( k2_tmap_1 @ X24 @ X22 @ X25 @ X23 )
        = ( k2_partfun1 @ ( u1_struct_0 @ X24 ) @ ( u1_struct_0 @ X22 ) @ X25 @ ( u1_struct_0 @ X23 ) ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X24 ) @ ( u1_struct_0 @ X22 ) ) ) )
      | ~ ( v1_funct_2 @ X25 @ ( u1_struct_0 @ X24 ) @ ( u1_struct_0 @ X22 ) )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( l1_pre_topc @ X24 )
      | ~ ( v2_pre_topc @ X24 )
      | ( v2_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d4_tmap_1])).

thf('119',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ X0 ) @ ( u1_struct_0 @ X1 ) ) ) )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_funct_2 @ X2 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X1 ) )
      | ( ( k2_tmap_1 @ X0 @ X1 @ X2 @ X3 )
        = ( k2_partfun1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X1 ) @ X2 @ ( u1_struct_0 @ X3 ) ) )
      | ~ ( m1_pre_topc @ X3 @ X0 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['117','118'])).

thf('120',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( m1_pre_topc @ X0 @ sk_C )
      | ( ( k2_tmap_1 @ sk_C @ sk_B @ sk_E @ X0 )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( l1_pre_topc @ sk_C )
      | ~ ( v2_pre_topc @ sk_C )
      | ( v2_struct_0 @ sk_C )
      | ~ ( l1_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['116','119'])).

thf('121',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,
    ( ( u1_struct_0 @ sk_C )
    = ( k2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['88','89'])).

thf('124',plain,
    ( ( u1_struct_0 @ sk_C )
    = ( k2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['88','89'])).

thf('125',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,
    ( ( u1_struct_0 @ sk_C )
    = ( u1_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['40','50'])).

thf('127',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['125','126'])).

thf('128',plain,
    ( ( u1_struct_0 @ sk_C )
    = ( k2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['88','89'])).

thf('129',plain,(
    v1_funct_2 @ sk_E @ ( k2_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['127','128'])).

thf('130',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('131',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['7','8'])).

thf('132',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('133',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( m1_pre_topc @ X5 @ X6 )
      | ( v2_pre_topc @ X5 )
      | ~ ( l1_pre_topc @ X6 )
      | ~ ( v2_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[cc1_pre_topc])).

thf('134',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_pre_topc @ sk_C ) ),
    inference('sup-',[status(thm)],['132','133'])).

thf('135',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('136',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('137',plain,(
    v2_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['134','135','136'])).

thf('138',plain,(
    l1_struct_0 @ sk_C ),
    inference('sup-',[status(thm)],['63','64'])).

thf('139',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ X0 @ sk_C )
      | ( ( k2_tmap_1 @ sk_C @ sk_B @ sk_E @ X0 )
        = ( k2_partfun1 @ ( k2_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ X0 ) ) )
      | ( v2_struct_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['120','121','122','123','124','129','130','131','137','138'])).

thf('140',plain,
    ( ~ ( l1_pre_topc @ sk_C )
    | ( v2_struct_0 @ sk_C )
    | ( ( k2_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_C )
      = ( k2_partfun1 @ ( k2_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ sk_C ) ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['111','139'])).

thf('141',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['7','8'])).

thf('142',plain,
    ( ( u1_struct_0 @ sk_C )
    = ( k2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['88','89'])).

thf('143',plain,
    ( ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C )
    = ( k2_partfun1 @ ( k2_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( k2_struct_0 @ sk_C ) ) ),
    inference(clc,[status(thm)],['108','109'])).

thf('144',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( ( k2_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_C )
      = ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['140','141','142','143'])).

thf('145',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('146',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k2_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_C )
      = ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C ) ) ),
    inference(clc,[status(thm)],['144','145'])).

thf('147',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('148',plain,
    ( ( k2_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_C )
    = ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C ) ),
    inference(clc,[status(thm)],['146','147'])).

thf('149',plain,
    ( ( k2_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_C )
    = ( k2_partfun1 @ ( k2_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( k2_struct_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['110','148'])).

thf('150',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(demod,[status(thm)],['35','36'])).

thf('151',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E )
      = ( k2_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_C ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['87','90','149','150'])).

thf('152',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('153',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E )
      = ( k2_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_C ) ) ),
    inference(clc,[status(thm)],['151','152'])).

thf('154',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('155',plain,
    ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E )
    = ( k2_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_C ) ),
    inference(clc,[status(thm)],['153','154'])).

thf('156',plain,(
    r1_tmap_1 @ sk_C @ sk_B @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_C ) @ sk_F ),
    inference(demod,[status(thm)],['70','155'])).

thf('157',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['114','115'])).

thf('158',plain,(
    ! [X7: $i] :
      ( ( ( k2_struct_0 @ X7 )
        = ( u1_struct_0 @ X7 ) )
      | ~ ( l1_struct_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(t67_tmap_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( v2_pre_topc @ B )
            & ( l1_pre_topc @ B ) )
         => ! [C: $i] :
              ( ( ( v1_funct_1 @ C )
                & ( v1_funct_2 @ C @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) )
                & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) )
             => ! [D: $i] :
                  ( ( ~ ( v2_struct_0 @ D )
                    & ( v1_tsep_1 @ D @ B )
                    & ( m1_pre_topc @ D @ B ) )
                 => ! [E: $i] :
                      ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) )
                     => ! [F: $i] :
                          ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) )
                         => ( ( E = F )
                           => ( ( r1_tmap_1 @ B @ A @ C @ E )
                            <=> ( r1_tmap_1 @ D @ A @ ( k2_tmap_1 @ B @ A @ C @ D ) @ F ) ) ) ) ) ) ) ) ) )).

thf('159',plain,(
    ! [X40: $i,X41: $i,X42: $i,X43: $i,X44: $i,X45: $i] :
      ( ( v2_struct_0 @ X40 )
      | ~ ( v2_pre_topc @ X40 )
      | ~ ( l1_pre_topc @ X40 )
      | ( v2_struct_0 @ X41 )
      | ~ ( v1_tsep_1 @ X41 @ X40 )
      | ~ ( m1_pre_topc @ X41 @ X40 )
      | ~ ( m1_subset_1 @ X42 @ ( u1_struct_0 @ X41 ) )
      | ~ ( r1_tmap_1 @ X41 @ X43 @ ( k2_tmap_1 @ X40 @ X43 @ X44 @ X41 ) @ X42 )
      | ( r1_tmap_1 @ X40 @ X43 @ X44 @ X45 )
      | ( X45 != X42 )
      | ~ ( m1_subset_1 @ X45 @ ( u1_struct_0 @ X40 ) )
      | ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X40 ) @ ( u1_struct_0 @ X43 ) ) ) )
      | ~ ( v1_funct_2 @ X44 @ ( u1_struct_0 @ X40 ) @ ( u1_struct_0 @ X43 ) )
      | ~ ( v1_funct_1 @ X44 )
      | ~ ( l1_pre_topc @ X43 )
      | ~ ( v2_pre_topc @ X43 )
      | ( v2_struct_0 @ X43 ) ) ),
    inference(cnf,[status(esa)],[t67_tmap_1])).

thf('160',plain,(
    ! [X40: $i,X41: $i,X42: $i,X43: $i,X44: $i] :
      ( ( v2_struct_0 @ X43 )
      | ~ ( v2_pre_topc @ X43 )
      | ~ ( l1_pre_topc @ X43 )
      | ~ ( v1_funct_1 @ X44 )
      | ~ ( v1_funct_2 @ X44 @ ( u1_struct_0 @ X40 ) @ ( u1_struct_0 @ X43 ) )
      | ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X40 ) @ ( u1_struct_0 @ X43 ) ) ) )
      | ~ ( m1_subset_1 @ X42 @ ( u1_struct_0 @ X40 ) )
      | ( r1_tmap_1 @ X40 @ X43 @ X44 @ X42 )
      | ~ ( r1_tmap_1 @ X41 @ X43 @ ( k2_tmap_1 @ X40 @ X43 @ X44 @ X41 ) @ X42 )
      | ~ ( m1_subset_1 @ X42 @ ( u1_struct_0 @ X41 ) )
      | ~ ( m1_pre_topc @ X41 @ X40 )
      | ~ ( v1_tsep_1 @ X41 @ X40 )
      | ( v2_struct_0 @ X41 )
      | ~ ( l1_pre_topc @ X40 )
      | ~ ( v2_pre_topc @ X40 )
      | ( v2_struct_0 @ X40 ) ) ),
    inference(simplify,[status(thm)],['159'])).

thf('161',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ X0 ) @ ( u1_struct_0 @ X1 ) ) ) )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X3 )
      | ~ ( v1_tsep_1 @ X3 @ X0 )
      | ~ ( m1_pre_topc @ X3 @ X0 )
      | ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ X3 ) )
      | ~ ( r1_tmap_1 @ X3 @ X1 @ ( k2_tmap_1 @ X0 @ X1 @ X2 @ X3 ) @ X4 )
      | ( r1_tmap_1 @ X0 @ X1 @ X2 @ X4 )
      | ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ X0 ) )
      | ~ ( v1_funct_2 @ X2 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X1 ) )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['158','160'])).

thf('162',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_C ) )
      | ( r1_tmap_1 @ sk_C @ sk_B @ sk_E @ X0 )
      | ~ ( r1_tmap_1 @ X1 @ sk_B @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_E @ X1 ) @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ X1 ) )
      | ~ ( m1_pre_topc @ X1 @ sk_C )
      | ~ ( v1_tsep_1 @ X1 @ sk_C )
      | ( v2_struct_0 @ X1 )
      | ~ ( l1_pre_topc @ sk_C )
      | ~ ( v2_pre_topc @ sk_C )
      | ( v2_struct_0 @ sk_C )
      | ~ ( l1_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['157','161'])).

thf('163',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('164',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('165',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('166',plain,
    ( ( u1_struct_0 @ sk_C )
    = ( k2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['88','89'])).

thf('167',plain,(
    v1_funct_2 @ sk_E @ ( k2_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['127','128'])).

thf('168',plain,
    ( ( u1_struct_0 @ sk_C )
    = ( k2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['88','89'])).

thf('169',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['7','8'])).

thf('170',plain,(
    v2_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['134','135','136'])).

thf('171',plain,(
    l1_struct_0 @ sk_C ),
    inference('sup-',[status(thm)],['63','64'])).

thf('172',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k2_struct_0 @ sk_C ) )
      | ( r1_tmap_1 @ sk_C @ sk_B @ sk_E @ X0 )
      | ~ ( r1_tmap_1 @ X1 @ sk_B @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_E @ X1 ) @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ X1 ) )
      | ~ ( m1_pre_topc @ X1 @ sk_C )
      | ~ ( v1_tsep_1 @ X1 @ sk_C )
      | ( v2_struct_0 @ X1 )
      | ( v2_struct_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['162','163','164','165','166','167','168','169','170','171'])).

thf('173',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_C )
    | ~ ( v1_tsep_1 @ sk_C @ sk_C )
    | ~ ( m1_pre_topc @ sk_C @ sk_C )
    | ~ ( m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_C ) )
    | ( r1_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_F )
    | ~ ( m1_subset_1 @ sk_F @ ( k2_struct_0 @ sk_C ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['156','172'])).

thf('174',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) )
    = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc10_tops_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( v3_pre_topc @ ( k2_struct_0 @ A ) @ A ) ) )).

thf('175',plain,(
    ! [X21: $i] :
      ( ( v3_pre_topc @ ( k2_struct_0 @ X21 ) @ X21 )
      | ~ ( l1_pre_topc @ X21 )
      | ~ ( v2_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[fc10_tops_1])).

thf('176',plain,(
    ! [X7: $i] :
      ( ( ( k2_struct_0 @ X7 )
        = ( u1_struct_0 @ X7 ) )
      | ~ ( l1_struct_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('177',plain,(
    ! [X4: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X4 ) @ ( k1_zfmisc_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('178',plain,(
    ! [X3: $i] :
      ( ( k2_subset_1 @ X3 )
      = X3 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('179',plain,(
    ! [X4: $i] :
      ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X4 ) ) ),
    inference(demod,[status(thm)],['177','178'])).

thf(t60_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ( v3_pre_topc @ B @ A )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
        <=> ( ( v3_pre_topc @ B @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ) ) ) ) )).

thf('180',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( v3_pre_topc @ X18 @ X17 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X17 ) @ ( u1_pre_topc @ X17 ) ) ) ) )
      | ~ ( l1_pre_topc @ X17 )
      | ~ ( v2_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[t60_pre_topc])).

thf('181',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['179','180'])).

thf('182',plain,(
    ! [X0: $i] :
      ( ~ ( v3_pre_topc @ ( k2_struct_0 @ X0 ) @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['176','181'])).

thf('183',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['175','182'])).

thf('184',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['183'])).

thf('185',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( v3_pre_topc @ X16 @ ( g1_pre_topc @ ( u1_struct_0 @ X17 ) @ ( u1_pre_topc @ X17 ) ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X17 ) @ ( u1_pre_topc @ X17 ) ) ) ) )
      | ( v3_pre_topc @ X16 @ X17 )
      | ~ ( l1_pre_topc @ X17 )
      | ~ ( v2_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[t60_pre_topc])).

thf('186',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['184','185'])).

thf('187',plain,(
    ! [X0: $i] :
      ( ~ ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['186'])).

thf('188',plain,
    ( ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_C ) @ sk_D )
    | ~ ( v2_pre_topc @ sk_C )
    | ~ ( l1_pre_topc @ sk_C )
    | ~ ( l1_struct_0 @ sk_C )
    | ( v3_pre_topc @ ( u1_struct_0 @ sk_C ) @ sk_C ) ),
    inference('sup-',[status(thm)],['174','187'])).

thf('189',plain,(
    v2_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['134','135','136'])).

thf('190',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['7','8'])).

thf('191',plain,(
    l1_struct_0 @ sk_C ),
    inference('sup-',[status(thm)],['63','64'])).

thf('192',plain,
    ( ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_C ) @ sk_D )
    | ( v3_pre_topc @ ( u1_struct_0 @ sk_C ) @ sk_C ) ),
    inference(demod,[status(thm)],['188','189','190','191'])).

thf('193',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) )
    = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('194',plain,(
    ! [X21: $i] :
      ( ( v3_pre_topc @ ( k2_struct_0 @ X21 ) @ X21 )
      | ~ ( l1_pre_topc @ X21 )
      | ~ ( v2_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[fc10_tops_1])).

thf('195',plain,(
    ! [X7: $i] :
      ( ( ( k2_struct_0 @ X7 )
        = ( u1_struct_0 @ X7 ) )
      | ~ ( l1_struct_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('196',plain,(
    ! [X4: $i] :
      ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X4 ) ) ),
    inference(demod,[status(thm)],['177','178'])).

thf('197',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( v3_pre_topc @ X18 @ X17 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ( v3_pre_topc @ X18 @ ( g1_pre_topc @ ( u1_struct_0 @ X17 ) @ ( u1_pre_topc @ X17 ) ) )
      | ~ ( l1_pre_topc @ X17 )
      | ~ ( v2_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[t60_pre_topc])).

thf('198',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['196','197'])).

thf('199',plain,(
    ! [X0: $i] :
      ( ~ ( v3_pre_topc @ ( k2_struct_0 @ X0 ) @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['195','198'])).

thf('200',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['194','199'])).

thf('201',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['200'])).

thf('202',plain,
    ( ( v3_pre_topc @ ( u1_struct_0 @ sk_C ) @ sk_D )
    | ~ ( v2_pre_topc @ sk_C )
    | ~ ( l1_pre_topc @ sk_C )
    | ~ ( l1_struct_0 @ sk_C ) ),
    inference('sup+',[status(thm)],['193','201'])).

thf('203',plain,(
    v2_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['134','135','136'])).

thf('204',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['7','8'])).

thf('205',plain,(
    l1_struct_0 @ sk_C ),
    inference('sup-',[status(thm)],['63','64'])).

thf('206',plain,(
    v3_pre_topc @ ( u1_struct_0 @ sk_C ) @ sk_D ),
    inference(demod,[status(thm)],['202','203','204','205'])).

thf('207',plain,(
    v3_pre_topc @ ( u1_struct_0 @ sk_C ) @ sk_C ),
    inference(demod,[status(thm)],['192','206'])).

thf('208',plain,(
    ! [X4: $i] :
      ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X4 ) ) ),
    inference(demod,[status(thm)],['177','178'])).

thf(t16_tsep_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( C
                  = ( u1_struct_0 @ B ) )
               => ( ( ( v1_tsep_1 @ B @ A )
                    & ( m1_pre_topc @ B @ A ) )
                <=> ( v3_pre_topc @ C @ A ) ) ) ) ) ) )).

thf('209',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( m1_pre_topc @ X31 @ X32 )
      | ( X33
       != ( u1_struct_0 @ X31 ) )
      | ~ ( v3_pre_topc @ X33 @ X32 )
      | ( v1_tsep_1 @ X31 @ X32 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X32 ) ) )
      | ~ ( l1_pre_topc @ X32 )
      | ~ ( v2_pre_topc @ X32 ) ) ),
    inference(cnf,[status(esa)],[t16_tsep_1])).

thf('210',plain,(
    ! [X31: $i,X32: $i] :
      ( ~ ( v2_pre_topc @ X32 )
      | ~ ( l1_pre_topc @ X32 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X31 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X32 ) ) )
      | ( v1_tsep_1 @ X31 @ X32 )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ X31 ) @ X32 )
      | ~ ( m1_pre_topc @ X31 @ X32 ) ) ),
    inference(simplify,[status(thm)],['209'])).

thf('211',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ X0 )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 )
      | ( v1_tsep_1 @ X0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['208','210'])).

thf('212',plain,
    ( ~ ( v2_pre_topc @ sk_C )
    | ~ ( l1_pre_topc @ sk_C )
    | ( v1_tsep_1 @ sk_C @ sk_C )
    | ~ ( m1_pre_topc @ sk_C @ sk_C ) ),
    inference('sup-',[status(thm)],['207','211'])).

thf('213',plain,(
    v2_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['134','135','136'])).

thf('214',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['7','8'])).

thf('215',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(demod,[status(thm)],['35','36'])).

thf('216',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( m1_pre_topc @ X0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['4','9'])).

thf('217',plain,(
    m1_pre_topc @ sk_C @ sk_C ),
    inference('sup-',[status(thm)],['215','216'])).

thf('218',plain,(
    v1_tsep_1 @ sk_C @ sk_C ),
    inference(demod,[status(thm)],['212','213','214','217'])).

thf('219',plain,(
    m1_pre_topc @ sk_C @ sk_C ),
    inference('sup-',[status(thm)],['215','216'])).

thf('220',plain,
    ( ( u1_struct_0 @ sk_C )
    = ( k2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['88','89'])).

thf('221',plain,(
    ! [X7: $i] :
      ( ( ( k2_struct_0 @ X7 )
        = ( u1_struct_0 @ X7 ) )
      | ~ ( l1_struct_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('222',plain,(
    m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('223',plain,(
    sk_F = sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('224',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['222','223'])).

thf('225',plain,
    ( ( m1_subset_1 @ sk_F @ ( k2_struct_0 @ sk_C ) )
    | ~ ( l1_struct_0 @ sk_C ) ),
    inference('sup+',[status(thm)],['221','224'])).

thf('226',plain,(
    l1_struct_0 @ sk_C ),
    inference('sup-',[status(thm)],['63','64'])).

thf('227',plain,(
    m1_subset_1 @ sk_F @ ( k2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['225','226'])).

thf('228',plain,(
    m1_subset_1 @ sk_F @ ( k2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['225','226'])).

thf('229',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_C )
    | ( r1_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_F )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['173','218','219','220','227','228'])).

thf('230',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( r1_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_F )
    | ( v2_struct_0 @ sk_C ) ),
    inference(simplify,[status(thm)],['229'])).

thf('231',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('232',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( r1_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_F ) ),
    inference(clc,[status(thm)],['230','231'])).

thf('233',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('234',plain,(
    r1_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_F ),
    inference(clc,[status(thm)],['232','233'])).

thf('235',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['114','115'])).

thf('236',plain,(
    ! [X7: $i] :
      ( ( ( k2_struct_0 @ X7 )
        = ( u1_struct_0 @ X7 ) )
      | ~ ( l1_struct_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('237',plain,(
    ! [X40: $i,X41: $i,X42: $i,X43: $i,X44: $i,X45: $i] :
      ( ( v2_struct_0 @ X40 )
      | ~ ( v2_pre_topc @ X40 )
      | ~ ( l1_pre_topc @ X40 )
      | ( v2_struct_0 @ X41 )
      | ~ ( v1_tsep_1 @ X41 @ X40 )
      | ~ ( m1_pre_topc @ X41 @ X40 )
      | ~ ( m1_subset_1 @ X42 @ ( u1_struct_0 @ X41 ) )
      | ~ ( r1_tmap_1 @ X40 @ X43 @ X44 @ X45 )
      | ( r1_tmap_1 @ X41 @ X43 @ ( k2_tmap_1 @ X40 @ X43 @ X44 @ X41 ) @ X42 )
      | ( X45 != X42 )
      | ~ ( m1_subset_1 @ X45 @ ( u1_struct_0 @ X40 ) )
      | ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X40 ) @ ( u1_struct_0 @ X43 ) ) ) )
      | ~ ( v1_funct_2 @ X44 @ ( u1_struct_0 @ X40 ) @ ( u1_struct_0 @ X43 ) )
      | ~ ( v1_funct_1 @ X44 )
      | ~ ( l1_pre_topc @ X43 )
      | ~ ( v2_pre_topc @ X43 )
      | ( v2_struct_0 @ X43 ) ) ),
    inference(cnf,[status(esa)],[t67_tmap_1])).

thf('238',plain,(
    ! [X40: $i,X41: $i,X42: $i,X43: $i,X44: $i] :
      ( ( v2_struct_0 @ X43 )
      | ~ ( v2_pre_topc @ X43 )
      | ~ ( l1_pre_topc @ X43 )
      | ~ ( v1_funct_1 @ X44 )
      | ~ ( v1_funct_2 @ X44 @ ( u1_struct_0 @ X40 ) @ ( u1_struct_0 @ X43 ) )
      | ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X40 ) @ ( u1_struct_0 @ X43 ) ) ) )
      | ~ ( m1_subset_1 @ X42 @ ( u1_struct_0 @ X40 ) )
      | ( r1_tmap_1 @ X41 @ X43 @ ( k2_tmap_1 @ X40 @ X43 @ X44 @ X41 ) @ X42 )
      | ~ ( r1_tmap_1 @ X40 @ X43 @ X44 @ X42 )
      | ~ ( m1_subset_1 @ X42 @ ( u1_struct_0 @ X41 ) )
      | ~ ( m1_pre_topc @ X41 @ X40 )
      | ~ ( v1_tsep_1 @ X41 @ X40 )
      | ( v2_struct_0 @ X41 )
      | ~ ( l1_pre_topc @ X40 )
      | ~ ( v2_pre_topc @ X40 )
      | ( v2_struct_0 @ X40 ) ) ),
    inference(simplify,[status(thm)],['237'])).

thf('239',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ X0 ) @ ( u1_struct_0 @ X1 ) ) ) )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X3 )
      | ~ ( v1_tsep_1 @ X3 @ X0 )
      | ~ ( m1_pre_topc @ X3 @ X0 )
      | ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ X3 ) )
      | ~ ( r1_tmap_1 @ X0 @ X1 @ X2 @ X4 )
      | ( r1_tmap_1 @ X3 @ X1 @ ( k2_tmap_1 @ X0 @ X1 @ X2 @ X3 ) @ X4 )
      | ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ X0 ) )
      | ~ ( v1_funct_2 @ X2 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X1 ) )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['236','238'])).

thf('240',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_C ) )
      | ( r1_tmap_1 @ X1 @ sk_B @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_E @ X1 ) @ X0 )
      | ~ ( r1_tmap_1 @ sk_C @ sk_B @ sk_E @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ X1 ) )
      | ~ ( m1_pre_topc @ X1 @ sk_C )
      | ~ ( v1_tsep_1 @ X1 @ sk_C )
      | ( v2_struct_0 @ X1 )
      | ~ ( l1_pre_topc @ sk_C )
      | ~ ( v2_pre_topc @ sk_C )
      | ( v2_struct_0 @ sk_C )
      | ~ ( l1_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['235','239'])).

thf('241',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('242',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('243',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('244',plain,
    ( ( u1_struct_0 @ sk_C )
    = ( k2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['88','89'])).

thf('245',plain,(
    v1_funct_2 @ sk_E @ ( k2_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['127','128'])).

thf('246',plain,
    ( ( u1_struct_0 @ sk_C )
    = ( k2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['88','89'])).

thf('247',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['7','8'])).

thf('248',plain,(
    v2_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['134','135','136'])).

thf('249',plain,(
    l1_struct_0 @ sk_C ),
    inference('sup-',[status(thm)],['63','64'])).

thf('250',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k2_struct_0 @ sk_C ) )
      | ( r1_tmap_1 @ X1 @ sk_B @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_E @ X1 ) @ X0 )
      | ~ ( r1_tmap_1 @ sk_C @ sk_B @ sk_E @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ X1 ) )
      | ~ ( m1_pre_topc @ X1 @ sk_C )
      | ~ ( v1_tsep_1 @ X1 @ sk_C )
      | ( v2_struct_0 @ X1 )
      | ( v2_struct_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['240','241','242','243','244','245','246','247','248','249'])).

thf('251',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ X0 )
      | ~ ( v1_tsep_1 @ X0 @ sk_C )
      | ~ ( m1_pre_topc @ X0 @ sk_C )
      | ~ ( m1_subset_1 @ sk_F @ ( u1_struct_0 @ X0 ) )
      | ( r1_tmap_1 @ X0 @ sk_B @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_E @ X0 ) @ sk_F )
      | ~ ( m1_subset_1 @ sk_F @ ( k2_struct_0 @ sk_C ) )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['234','250'])).

thf('252',plain,(
    m1_subset_1 @ sk_F @ ( k2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['225','226'])).

thf('253',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ X0 )
      | ~ ( v1_tsep_1 @ X0 @ sk_C )
      | ~ ( m1_pre_topc @ X0 @ sk_C )
      | ~ ( m1_subset_1 @ sk_F @ ( u1_struct_0 @ X0 ) )
      | ( r1_tmap_1 @ X0 @ sk_B @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_E @ X0 ) @ sk_F )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['251','252'])).

thf('254',plain,
    ( ~ ( m1_subset_1 @ sk_F @ ( k2_struct_0 @ sk_C ) )
    | ( v2_struct_0 @ sk_B )
    | ( r1_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_D ) @ sk_F )
    | ~ ( m1_pre_topc @ sk_D @ sk_C )
    | ~ ( v1_tsep_1 @ sk_D @ sk_C )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['67','253'])).

thf('255',plain,(
    m1_subset_1 @ sk_F @ ( k2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['225','226'])).

thf('256',plain,(
    m1_pre_topc @ sk_D @ sk_C ),
    inference(demod,[status(thm)],['11','16'])).

thf('257',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ X0 @ sk_C )
      | ( ( k2_tmap_1 @ sk_C @ sk_B @ sk_E @ X0 )
        = ( k2_partfun1 @ ( k2_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ X0 ) ) )
      | ( v2_struct_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['120','121','122','123','124','129','130','131','137','138'])).

thf('258',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( ( k2_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_D )
      = ( k2_partfun1 @ ( k2_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ sk_D ) ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['256','257'])).

thf('259',plain,
    ( ( k2_struct_0 @ sk_C )
    = ( u1_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['59','66'])).

thf('260',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( ( k2_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_D )
      = ( k2_partfun1 @ ( k2_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( k2_struct_0 @ sk_C ) ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['258','259'])).

thf('261',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('262',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k2_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_D )
      = ( k2_partfun1 @ ( k2_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( k2_struct_0 @ sk_C ) ) ) ),
    inference(clc,[status(thm)],['260','261'])).

thf('263',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('264',plain,
    ( ( k2_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_D )
    = ( k2_partfun1 @ ( k2_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( k2_struct_0 @ sk_C ) ) ),
    inference(clc,[status(thm)],['262','263'])).

thf('265',plain,
    ( ( k2_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_C )
    = ( k2_partfun1 @ ( k2_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( k2_struct_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['110','148'])).

thf('266',plain,
    ( ( k2_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_C )
    = ( k2_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_D ) ),
    inference('sup+',[status(thm)],['264','265'])).

thf('267',plain,(
    m1_pre_topc @ sk_D @ sk_C ),
    inference(demod,[status(thm)],['11','16'])).

thf('268',plain,(
    m1_pre_topc @ sk_D @ sk_C ),
    inference(demod,[status(thm)],['11','16'])).

thf(t1_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( m1_subset_1 @ ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('269',plain,(
    ! [X34: $i,X35: $i] :
      ( ~ ( m1_pre_topc @ X34 @ X35 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X34 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X35 ) ) )
      | ~ ( l1_pre_topc @ X35 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('270',plain,
    ( ~ ( l1_pre_topc @ sk_C )
    | ( m1_subset_1 @ ( u1_struct_0 @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['268','269'])).

thf('271',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['7','8'])).

thf('272',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['270','271'])).

thf('273',plain,(
    ! [X31: $i,X32: $i] :
      ( ~ ( v2_pre_topc @ X32 )
      | ~ ( l1_pre_topc @ X32 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X31 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X32 ) ) )
      | ( v1_tsep_1 @ X31 @ X32 )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ X31 ) @ X32 )
      | ~ ( m1_pre_topc @ X31 @ X32 ) ) ),
    inference(simplify,[status(thm)],['209'])).

thf('274',plain,
    ( ~ ( m1_pre_topc @ sk_D @ sk_C )
    | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_D ) @ sk_C )
    | ( v1_tsep_1 @ sk_D @ sk_C )
    | ~ ( l1_pre_topc @ sk_C )
    | ~ ( v2_pre_topc @ sk_C ) ),
    inference('sup-',[status(thm)],['272','273'])).

thf('275',plain,(
    m1_pre_topc @ sk_D @ sk_C ),
    inference(demod,[status(thm)],['11','16'])).

thf('276',plain,(
    ! [X21: $i] :
      ( ( v3_pre_topc @ ( k2_struct_0 @ X21 ) @ X21 )
      | ~ ( l1_pre_topc @ X21 )
      | ~ ( v2_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[fc10_tops_1])).

thf('277',plain,(
    ! [X7: $i] :
      ( ( ( k2_struct_0 @ X7 )
        = ( u1_struct_0 @ X7 ) )
      | ~ ( l1_struct_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('278',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) )
    = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('279',plain,(
    ! [X4: $i] :
      ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X4 ) ) ),
    inference(demod,[status(thm)],['177','178'])).

thf('280',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( v3_pre_topc @ X16 @ ( g1_pre_topc @ ( u1_struct_0 @ X17 ) @ ( u1_pre_topc @ X17 ) ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X17 ) @ ( u1_pre_topc @ X17 ) ) ) ) )
      | ( v3_pre_topc @ X16 @ X17 )
      | ~ ( l1_pre_topc @ X17 )
      | ~ ( v2_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[t60_pre_topc])).

thf('281',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v3_pre_topc @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) @ X0 )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['279','280'])).

thf('282',plain,
    ( ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_D ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) ) )
    | ( v3_pre_topc @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) ) ) @ sk_C )
    | ~ ( l1_pre_topc @ sk_C )
    | ~ ( v2_pre_topc @ sk_C ) ),
    inference('sup-',[status(thm)],['278','281'])).

thf('283',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) )
    = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('284',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) )
    = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('285',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['7','8'])).

thf('286',plain,(
    v2_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['134','135','136'])).

thf('287',plain,
    ( ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_D ) @ sk_D )
    | ( v3_pre_topc @ ( u1_struct_0 @ sk_D ) @ sk_C ) ),
    inference(demod,[status(thm)],['282','283','284','285','286'])).

thf('288',plain,
    ( ~ ( v3_pre_topc @ ( k2_struct_0 @ sk_D ) @ sk_D )
    | ~ ( l1_struct_0 @ sk_D )
    | ( v3_pre_topc @ ( u1_struct_0 @ sk_D ) @ sk_C ) ),
    inference('sup-',[status(thm)],['277','287'])).

thf('289',plain,(
    l1_struct_0 @ sk_D ),
    inference('sup-',[status(thm)],['55','56'])).

thf('290',plain,
    ( ~ ( v3_pre_topc @ ( k2_struct_0 @ sk_D ) @ sk_D )
    | ( v3_pre_topc @ ( u1_struct_0 @ sk_D ) @ sk_C ) ),
    inference(demod,[status(thm)],['288','289'])).

thf('291',plain,
    ( ~ ( v2_pre_topc @ sk_D )
    | ~ ( l1_pre_topc @ sk_D )
    | ( v3_pre_topc @ ( u1_struct_0 @ sk_D ) @ sk_C ) ),
    inference('sup-',[status(thm)],['276','290'])).

thf('292',plain,(
    v2_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['26','27','28'])).

thf('293',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['14','15'])).

thf('294',plain,(
    v3_pre_topc @ ( u1_struct_0 @ sk_D ) @ sk_C ),
    inference(demod,[status(thm)],['291','292','293'])).

thf('295',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['7','8'])).

thf('296',plain,(
    v2_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['134','135','136'])).

thf('297',plain,(
    v1_tsep_1 @ sk_D @ sk_C ),
    inference(demod,[status(thm)],['274','275','294','295','296'])).

thf('298',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( r1_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_C ) @ sk_F )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['254','255','266','267','297'])).

thf('299',plain,
    ( ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C )
    = ( k2_partfun1 @ ( k2_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( k2_struct_0 @ sk_C ) ) ),
    inference(clc,[status(thm)],['108','109'])).

thf('300',plain,(
    ! [X36: $i] :
      ( ( m1_pre_topc @ X36 @ X36 )
      | ~ ( l1_pre_topc @ X36 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('301',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_D )
      | ( ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0 )
        = ( k2_partfun1 @ ( k2_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['101','102'])).

thf('302',plain,
    ( ~ ( l1_pre_topc @ sk_D )
    | ( v2_struct_0 @ sk_B )
    | ( ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_D )
      = ( k2_partfun1 @ ( k2_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ sk_D ) ) )
    | ( v2_struct_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['300','301'])).

thf('303',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['14','15'])).

thf('304',plain,
    ( ( k2_struct_0 @ sk_C )
    = ( u1_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['59','66'])).

thf('305',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_D )
      = ( k2_partfun1 @ ( k2_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( k2_struct_0 @ sk_C ) ) )
    | ( v2_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['302','303','304'])).

thf('306',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('307',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_D )
      = ( k2_partfun1 @ ( k2_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( k2_struct_0 @ sk_C ) ) ) ),
    inference(clc,[status(thm)],['305','306'])).

thf('308',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('309',plain,
    ( ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_D )
    = ( k2_partfun1 @ ( k2_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( k2_struct_0 @ sk_C ) ) ),
    inference(clc,[status(thm)],['307','308'])).

thf('310',plain,
    ( ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_D )
    = ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C ) ),
    inference('sup+',[status(thm)],['299','309'])).

thf('311',plain,
    ( ( k2_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_C )
    = ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C ) ),
    inference(clc,[status(thm)],['146','147'])).

thf('312',plain,
    ( ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_D )
    = ( k2_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_C ) ),
    inference(demod,[status(thm)],['310','311'])).

thf('313',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['114','115'])).

thf('314',plain,
    ( ( k2_struct_0 @ sk_C )
    = ( u1_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['59','66'])).

thf('315',plain,(
    ! [X40: $i,X41: $i,X42: $i,X43: $i,X44: $i] :
      ( ( v2_struct_0 @ X43 )
      | ~ ( v2_pre_topc @ X43 )
      | ~ ( l1_pre_topc @ X43 )
      | ~ ( v1_funct_1 @ X44 )
      | ~ ( v1_funct_2 @ X44 @ ( u1_struct_0 @ X40 ) @ ( u1_struct_0 @ X43 ) )
      | ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X40 ) @ ( u1_struct_0 @ X43 ) ) ) )
      | ~ ( m1_subset_1 @ X42 @ ( u1_struct_0 @ X40 ) )
      | ( r1_tmap_1 @ X40 @ X43 @ X44 @ X42 )
      | ~ ( r1_tmap_1 @ X41 @ X43 @ ( k2_tmap_1 @ X40 @ X43 @ X44 @ X41 ) @ X42 )
      | ~ ( m1_subset_1 @ X42 @ ( u1_struct_0 @ X41 ) )
      | ~ ( m1_pre_topc @ X41 @ X40 )
      | ~ ( v1_tsep_1 @ X41 @ X40 )
      | ( v2_struct_0 @ X41 )
      | ~ ( l1_pre_topc @ X40 )
      | ~ ( v2_pre_topc @ X40 )
      | ( v2_struct_0 @ X40 ) ) ),
    inference(simplify,[status(thm)],['159'])).

thf('316',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_C ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ( v2_struct_0 @ sk_D )
      | ~ ( v2_pre_topc @ sk_D )
      | ~ ( l1_pre_topc @ sk_D )
      | ( v2_struct_0 @ X2 )
      | ~ ( v1_tsep_1 @ X2 @ sk_D )
      | ~ ( m1_pre_topc @ X2 @ sk_D )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X2 ) )
      | ~ ( r1_tmap_1 @ X2 @ X0 @ ( k2_tmap_1 @ sk_D @ X0 @ X1 @ X2 ) @ X3 )
      | ( r1_tmap_1 @ sk_D @ X0 @ X1 @ X3 )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ sk_D ) )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['314','315'])).

thf('317',plain,(
    v2_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['26','27','28'])).

thf('318',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['14','15'])).

thf('319',plain,
    ( ( k2_struct_0 @ sk_C )
    = ( u1_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['59','66'])).

thf('320',plain,
    ( ( k2_struct_0 @ sk_C )
    = ( u1_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['59','66'])).

thf('321',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_C ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ X2 )
      | ~ ( v1_tsep_1 @ X2 @ sk_D )
      | ~ ( m1_pre_topc @ X2 @ sk_D )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X2 ) )
      | ~ ( r1_tmap_1 @ X2 @ X0 @ ( k2_tmap_1 @ sk_D @ X0 @ X1 @ X2 ) @ X3 )
      | ( r1_tmap_1 @ sk_D @ X0 @ X1 @ X3 )
      | ~ ( m1_subset_1 @ X3 @ ( k2_struct_0 @ sk_C ) )
      | ~ ( v1_funct_2 @ X1 @ ( k2_struct_0 @ sk_C ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['316','317','318','319','320'])).

thf('322',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( v1_funct_2 @ sk_E @ ( k2_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( m1_subset_1 @ X0 @ ( k2_struct_0 @ sk_C ) )
      | ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X0 )
      | ~ ( r1_tmap_1 @ X1 @ sk_B @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X1 ) @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ X1 ) )
      | ~ ( m1_pre_topc @ X1 @ sk_D )
      | ~ ( v1_tsep_1 @ X1 @ sk_D )
      | ( v2_struct_0 @ X1 )
      | ( v2_struct_0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['313','321'])).

thf('323',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('324',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('325',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('326',plain,(
    v1_funct_2 @ sk_E @ ( k2_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['127','128'])).

thf('327',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k2_struct_0 @ sk_C ) )
      | ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X0 )
      | ~ ( r1_tmap_1 @ X1 @ sk_B @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X1 ) @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ X1 ) )
      | ~ ( m1_pre_topc @ X1 @ sk_D )
      | ~ ( v1_tsep_1 @ X1 @ sk_D )
      | ( v2_struct_0 @ X1 )
      | ( v2_struct_0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['322','323','324','325','326'])).

thf('328',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_C ) @ X0 )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_D )
      | ~ ( v1_tsep_1 @ sk_D @ sk_D )
      | ~ ( m1_pre_topc @ sk_D @ sk_D )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_D ) )
      | ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k2_struct_0 @ sk_C ) )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['312','327'])).

thf('329',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['270','271'])).

thf('330',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( v3_pre_topc @ X18 @ X17 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ( v3_pre_topc @ X18 @ ( g1_pre_topc @ ( u1_struct_0 @ X17 ) @ ( u1_pre_topc @ X17 ) ) )
      | ~ ( l1_pre_topc @ X17 )
      | ~ ( v2_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[t60_pre_topc])).

thf('331',plain,
    ( ~ ( v2_pre_topc @ sk_C )
    | ~ ( l1_pre_topc @ sk_C )
    | ( v3_pre_topc @ ( u1_struct_0 @ sk_D ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) ) )
    | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_D ) @ sk_C ) ),
    inference('sup-',[status(thm)],['329','330'])).

thf('332',plain,(
    v2_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['134','135','136'])).

thf('333',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['7','8'])).

thf('334',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) )
    = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('335',plain,(
    v3_pre_topc @ ( u1_struct_0 @ sk_D ) @ sk_C ),
    inference(demod,[status(thm)],['291','292','293'])).

thf('336',plain,(
    v3_pre_topc @ ( u1_struct_0 @ sk_D ) @ sk_D ),
    inference(demod,[status(thm)],['331','332','333','334','335'])).

thf('337',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ X0 )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 )
      | ( v1_tsep_1 @ X0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['208','210'])).

thf('338',plain,
    ( ~ ( v2_pre_topc @ sk_D )
    | ~ ( l1_pre_topc @ sk_D )
    | ( v1_tsep_1 @ sk_D @ sk_D )
    | ~ ( m1_pre_topc @ sk_D @ sk_D ) ),
    inference('sup-',[status(thm)],['336','337'])).

thf('339',plain,(
    v2_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['26','27','28'])).

thf('340',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['14','15'])).

thf('341',plain,(
    m1_pre_topc @ sk_D @ sk_C ),
    inference(demod,[status(thm)],['11','16'])).

thf('342',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( l1_pre_topc @ X19 )
      | ~ ( m1_pre_topc @ X20 @ X19 )
      | ( m1_pre_topc @ X20 @ ( g1_pre_topc @ ( u1_struct_0 @ X19 ) @ ( u1_pre_topc @ X19 ) ) )
      | ~ ( l1_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[t65_pre_topc])).

thf('343',plain,
    ( ~ ( l1_pre_topc @ sk_D )
    | ( m1_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) ) )
    | ~ ( l1_pre_topc @ sk_C ) ),
    inference('sup-',[status(thm)],['341','342'])).

thf('344',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['14','15'])).

thf('345',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) )
    = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('346',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['7','8'])).

thf('347',plain,(
    m1_pre_topc @ sk_D @ sk_D ),
    inference(demod,[status(thm)],['343','344','345','346'])).

thf('348',plain,(
    v1_tsep_1 @ sk_D @ sk_D ),
    inference(demod,[status(thm)],['338','339','340','347'])).

thf('349',plain,(
    m1_pre_topc @ sk_D @ sk_D ),
    inference(demod,[status(thm)],['343','344','345','346'])).

thf('350',plain,
    ( ( k2_struct_0 @ sk_C )
    = ( u1_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['59','66'])).

thf('351',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_C ) @ X0 )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_D )
      | ~ ( m1_subset_1 @ X0 @ ( k2_struct_0 @ sk_C ) )
      | ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k2_struct_0 @ sk_C ) )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['328','348','349','350'])).

thf('352',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k2_struct_0 @ sk_C ) )
      | ( v2_struct_0 @ sk_D )
      | ~ ( r1_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_C ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['351'])).

thf('353',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ~ ( m1_subset_1 @ sk_F @ ( k2_struct_0 @ sk_C ) )
    | ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['298','352'])).

thf('354',plain,(
    m1_subset_1 @ sk_F @ ( k2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['225','226'])).

thf('355',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['353','354'])).

thf('356',plain,
    ( ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C ) ),
    inference(simplify,[status(thm)],['355'])).

thf('357',plain,(
    ~ ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('358',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['356','357'])).

thf('359',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('360',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D ) ),
    inference(clc,[status(thm)],['358','359'])).

thf('361',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('362',plain,(
    v2_struct_0 @ sk_D ),
    inference(clc,[status(thm)],['360','361'])).

thf('363',plain,(
    $false ),
    inference(demod,[status(thm)],['0','362'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.moK85r9vhZ
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:01:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.18/1.36  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.18/1.36  % Solved by: fo/fo7.sh
% 1.18/1.36  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.18/1.36  % done 1504 iterations in 0.905s
% 1.18/1.36  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.18/1.36  % SZS output start Refutation
% 1.18/1.36  thf(sk_C_type, type, sk_C: $i).
% 1.18/1.36  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.18/1.36  thf(v1_tsep_1_type, type, v1_tsep_1: $i > $i > $o).
% 1.18/1.36  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 1.18/1.36  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 1.18/1.36  thf(k2_partfun1_type, type, k2_partfun1: $i > $i > $i > $i > $i).
% 1.18/1.36  thf(sk_G_type, type, sk_G: $i).
% 1.18/1.36  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.18/1.36  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 1.18/1.36  thf(sk_A_type, type, sk_A: $i).
% 1.18/1.36  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 1.18/1.36  thf(r1_tmap_1_type, type, r1_tmap_1: $i > $i > $i > $i > $o).
% 1.18/1.36  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 1.18/1.36  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.18/1.36  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.18/1.36  thf(k3_tmap_1_type, type, k3_tmap_1: $i > $i > $i > $i > $i > $i).
% 1.18/1.36  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.18/1.36  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 1.18/1.36  thf(k2_tmap_1_type, type, k2_tmap_1: $i > $i > $i > $i > $i).
% 1.18/1.36  thf(sk_B_type, type, sk_B: $i).
% 1.18/1.36  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.18/1.36  thf(sk_E_type, type, sk_E: $i).
% 1.18/1.36  thf(g1_pre_topc_type, type, g1_pre_topc: $i > $i > $i).
% 1.18/1.36  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 1.18/1.36  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 1.18/1.36  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 1.18/1.36  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 1.18/1.36  thf(sk_F_type, type, sk_F: $i).
% 1.18/1.36  thf(sk_D_type, type, sk_D: $i).
% 1.18/1.36  thf(t88_tmap_1, conjecture,
% 1.18/1.36    (![A:$i]:
% 1.18/1.36     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.18/1.36       ( ![B:$i]:
% 1.18/1.36         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 1.18/1.36             ( l1_pre_topc @ B ) ) =>
% 1.18/1.36           ( ![C:$i]:
% 1.18/1.36             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 1.18/1.36               ( ![D:$i]:
% 1.18/1.36                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 1.18/1.36                   ( ![E:$i]:
% 1.18/1.36                     ( ( ( v1_funct_1 @ E ) & 
% 1.18/1.36                         ( v1_funct_2 @
% 1.18/1.36                           E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 1.18/1.36                         ( m1_subset_1 @
% 1.18/1.36                           E @ 
% 1.18/1.36                           ( k1_zfmisc_1 @
% 1.18/1.36                             ( k2_zfmisc_1 @
% 1.18/1.36                               ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 1.18/1.36                       ( ( ( g1_pre_topc @
% 1.18/1.36                             ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) ) =
% 1.18/1.36                           ( D ) ) =>
% 1.18/1.36                         ( ![F:$i]:
% 1.18/1.36                           ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 1.18/1.36                             ( ![G:$i]:
% 1.18/1.36                               ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) ) =>
% 1.18/1.36                                 ( ( ( ( F ) = ( G ) ) & 
% 1.18/1.36                                     ( r1_tmap_1 @
% 1.18/1.36                                       C @ B @ 
% 1.18/1.36                                       ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ G ) ) =>
% 1.18/1.36                                   ( r1_tmap_1 @ D @ B @ E @ F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 1.18/1.36  thf(zf_stmt_0, negated_conjecture,
% 1.18/1.36    (~( ![A:$i]:
% 1.18/1.36        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 1.18/1.36            ( l1_pre_topc @ A ) ) =>
% 1.18/1.36          ( ![B:$i]:
% 1.18/1.36            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 1.18/1.36                ( l1_pre_topc @ B ) ) =>
% 1.18/1.36              ( ![C:$i]:
% 1.18/1.36                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 1.18/1.36                  ( ![D:$i]:
% 1.18/1.36                    ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 1.18/1.36                      ( ![E:$i]:
% 1.18/1.36                        ( ( ( v1_funct_1 @ E ) & 
% 1.18/1.36                            ( v1_funct_2 @
% 1.18/1.36                              E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 1.18/1.36                            ( m1_subset_1 @
% 1.18/1.36                              E @ 
% 1.18/1.36                              ( k1_zfmisc_1 @
% 1.18/1.36                                ( k2_zfmisc_1 @
% 1.18/1.36                                  ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 1.18/1.36                          ( ( ( g1_pre_topc @
% 1.18/1.36                                ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) ) =
% 1.18/1.36                              ( D ) ) =>
% 1.18/1.36                            ( ![F:$i]:
% 1.18/1.36                              ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 1.18/1.36                                ( ![G:$i]:
% 1.18/1.36                                  ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) ) =>
% 1.18/1.36                                    ( ( ( ( F ) = ( G ) ) & 
% 1.18/1.36                                        ( r1_tmap_1 @
% 1.18/1.36                                          C @ B @ 
% 1.18/1.36                                          ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ G ) ) =>
% 1.18/1.36                                      ( r1_tmap_1 @ D @ B @ E @ F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 1.18/1.36    inference('cnf.neg', [status(esa)], [t88_tmap_1])).
% 1.18/1.36  thf('0', plain, (~ (v2_struct_0 @ sk_D)),
% 1.18/1.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.36  thf(t2_tsep_1, axiom,
% 1.18/1.36    (![A:$i]: ( ( l1_pre_topc @ A ) => ( m1_pre_topc @ A @ A ) ))).
% 1.18/1.36  thf('1', plain,
% 1.18/1.36      (![X36 : $i]: ((m1_pre_topc @ X36 @ X36) | ~ (l1_pre_topc @ X36))),
% 1.18/1.36      inference('cnf', [status(esa)], [t2_tsep_1])).
% 1.18/1.36  thf('2', plain,
% 1.18/1.36      (((g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) = (sk_D))),
% 1.18/1.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.36  thf(t59_pre_topc, axiom,
% 1.18/1.36    (![A:$i]:
% 1.18/1.36     ( ( l1_pre_topc @ A ) =>
% 1.18/1.36       ( ![B:$i]:
% 1.18/1.36         ( ( m1_pre_topc @
% 1.18/1.36             B @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) =>
% 1.18/1.36           ( m1_pre_topc @ B @ A ) ) ) ))).
% 1.18/1.36  thf('3', plain,
% 1.18/1.36      (![X14 : $i, X15 : $i]:
% 1.18/1.36         (~ (m1_pre_topc @ X14 @ 
% 1.18/1.36             (g1_pre_topc @ (u1_struct_0 @ X15) @ (u1_pre_topc @ X15)))
% 1.18/1.36          | (m1_pre_topc @ X14 @ X15)
% 1.18/1.36          | ~ (l1_pre_topc @ X15))),
% 1.18/1.36      inference('cnf', [status(esa)], [t59_pre_topc])).
% 1.18/1.36  thf('4', plain,
% 1.18/1.36      (![X0 : $i]:
% 1.18/1.36         (~ (m1_pre_topc @ X0 @ sk_D)
% 1.18/1.36          | ~ (l1_pre_topc @ sk_C)
% 1.18/1.36          | (m1_pre_topc @ X0 @ sk_C))),
% 1.18/1.36      inference('sup-', [status(thm)], ['2', '3'])).
% 1.18/1.36  thf('5', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 1.18/1.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.36  thf(dt_m1_pre_topc, axiom,
% 1.18/1.36    (![A:$i]:
% 1.18/1.36     ( ( l1_pre_topc @ A ) =>
% 1.18/1.36       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 1.18/1.36  thf('6', plain,
% 1.18/1.36      (![X9 : $i, X10 : $i]:
% 1.18/1.36         (~ (m1_pre_topc @ X9 @ X10)
% 1.18/1.36          | (l1_pre_topc @ X9)
% 1.18/1.36          | ~ (l1_pre_topc @ X10))),
% 1.18/1.36      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 1.18/1.36  thf('7', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_C))),
% 1.18/1.36      inference('sup-', [status(thm)], ['5', '6'])).
% 1.18/1.36  thf('8', plain, ((l1_pre_topc @ sk_A)),
% 1.18/1.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.36  thf('9', plain, ((l1_pre_topc @ sk_C)),
% 1.18/1.36      inference('demod', [status(thm)], ['7', '8'])).
% 1.18/1.36  thf('10', plain,
% 1.18/1.36      (![X0 : $i]: (~ (m1_pre_topc @ X0 @ sk_D) | (m1_pre_topc @ X0 @ sk_C))),
% 1.18/1.36      inference('demod', [status(thm)], ['4', '9'])).
% 1.18/1.36  thf('11', plain, ((~ (l1_pre_topc @ sk_D) | (m1_pre_topc @ sk_D @ sk_C))),
% 1.18/1.36      inference('sup-', [status(thm)], ['1', '10'])).
% 1.18/1.36  thf('12', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 1.18/1.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.36  thf('13', plain,
% 1.18/1.36      (![X9 : $i, X10 : $i]:
% 1.18/1.36         (~ (m1_pre_topc @ X9 @ X10)
% 1.18/1.36          | (l1_pre_topc @ X9)
% 1.18/1.36          | ~ (l1_pre_topc @ X10))),
% 1.18/1.36      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 1.18/1.36  thf('14', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_D))),
% 1.18/1.36      inference('sup-', [status(thm)], ['12', '13'])).
% 1.18/1.36  thf('15', plain, ((l1_pre_topc @ sk_A)),
% 1.18/1.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.36  thf('16', plain, ((l1_pre_topc @ sk_D)),
% 1.18/1.36      inference('demod', [status(thm)], ['14', '15'])).
% 1.18/1.36  thf('17', plain, ((m1_pre_topc @ sk_D @ sk_C)),
% 1.18/1.36      inference('demod', [status(thm)], ['11', '16'])).
% 1.18/1.36  thf('18', plain,
% 1.18/1.36      (![X36 : $i]: ((m1_pre_topc @ X36 @ X36) | ~ (l1_pre_topc @ X36))),
% 1.18/1.36      inference('cnf', [status(esa)], [t2_tsep_1])).
% 1.18/1.36  thf(t4_tsep_1, axiom,
% 1.18/1.36    (![A:$i]:
% 1.18/1.36     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.18/1.36       ( ![B:$i]:
% 1.18/1.36         ( ( m1_pre_topc @ B @ A ) =>
% 1.18/1.36           ( ![C:$i]:
% 1.18/1.36             ( ( m1_pre_topc @ C @ A ) =>
% 1.18/1.36               ( ( r1_tarski @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ C ) ) <=>
% 1.18/1.36                 ( m1_pre_topc @ B @ C ) ) ) ) ) ) ))).
% 1.18/1.36  thf('19', plain,
% 1.18/1.36      (![X37 : $i, X38 : $i, X39 : $i]:
% 1.18/1.36         (~ (m1_pre_topc @ X37 @ X38)
% 1.18/1.36          | ~ (m1_pre_topc @ X37 @ X39)
% 1.18/1.36          | (r1_tarski @ (u1_struct_0 @ X37) @ (u1_struct_0 @ X39))
% 1.18/1.36          | ~ (m1_pre_topc @ X39 @ X38)
% 1.18/1.36          | ~ (l1_pre_topc @ X38)
% 1.18/1.36          | ~ (v2_pre_topc @ X38))),
% 1.18/1.36      inference('cnf', [status(esa)], [t4_tsep_1])).
% 1.18/1.36  thf('20', plain,
% 1.18/1.36      (![X0 : $i, X1 : $i]:
% 1.18/1.36         (~ (l1_pre_topc @ X0)
% 1.18/1.36          | ~ (v2_pre_topc @ X0)
% 1.18/1.36          | ~ (l1_pre_topc @ X0)
% 1.18/1.36          | ~ (m1_pre_topc @ X1 @ X0)
% 1.18/1.36          | (r1_tarski @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X1))
% 1.18/1.36          | ~ (m1_pre_topc @ X0 @ X1))),
% 1.18/1.36      inference('sup-', [status(thm)], ['18', '19'])).
% 1.18/1.36  thf('21', plain,
% 1.18/1.36      (![X0 : $i, X1 : $i]:
% 1.18/1.36         (~ (m1_pre_topc @ X0 @ X1)
% 1.18/1.36          | (r1_tarski @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X1))
% 1.18/1.36          | ~ (m1_pre_topc @ X1 @ X0)
% 1.18/1.36          | ~ (v2_pre_topc @ X0)
% 1.18/1.37          | ~ (l1_pre_topc @ X0))),
% 1.18/1.37      inference('simplify', [status(thm)], ['20'])).
% 1.18/1.37  thf('22', plain,
% 1.18/1.37      ((~ (l1_pre_topc @ sk_D)
% 1.18/1.37        | ~ (v2_pre_topc @ sk_D)
% 1.18/1.37        | ~ (m1_pre_topc @ sk_C @ sk_D)
% 1.18/1.37        | (r1_tarski @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_C)))),
% 1.18/1.37      inference('sup-', [status(thm)], ['17', '21'])).
% 1.18/1.37  thf('23', plain, ((l1_pre_topc @ sk_D)),
% 1.18/1.37      inference('demod', [status(thm)], ['14', '15'])).
% 1.18/1.37  thf('24', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 1.18/1.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.37  thf(cc1_pre_topc, axiom,
% 1.18/1.37    (![A:$i]:
% 1.18/1.37     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.18/1.37       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( v2_pre_topc @ B ) ) ) ))).
% 1.18/1.37  thf('25', plain,
% 1.18/1.37      (![X5 : $i, X6 : $i]:
% 1.18/1.37         (~ (m1_pre_topc @ X5 @ X6)
% 1.18/1.37          | (v2_pre_topc @ X5)
% 1.18/1.37          | ~ (l1_pre_topc @ X6)
% 1.18/1.37          | ~ (v2_pre_topc @ X6))),
% 1.18/1.37      inference('cnf', [status(esa)], [cc1_pre_topc])).
% 1.18/1.37  thf('26', plain,
% 1.18/1.37      ((~ (v2_pre_topc @ sk_A) | ~ (l1_pre_topc @ sk_A) | (v2_pre_topc @ sk_D))),
% 1.18/1.37      inference('sup-', [status(thm)], ['24', '25'])).
% 1.18/1.37  thf('27', plain, ((v2_pre_topc @ sk_A)),
% 1.18/1.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.37  thf('28', plain, ((l1_pre_topc @ sk_A)),
% 1.18/1.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.37  thf('29', plain, ((v2_pre_topc @ sk_D)),
% 1.18/1.37      inference('demod', [status(thm)], ['26', '27', '28'])).
% 1.18/1.37  thf('30', plain,
% 1.18/1.37      (((g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) = (sk_D))),
% 1.18/1.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.37  thf('31', plain,
% 1.18/1.37      (![X36 : $i]: ((m1_pre_topc @ X36 @ X36) | ~ (l1_pre_topc @ X36))),
% 1.18/1.37      inference('cnf', [status(esa)], [t2_tsep_1])).
% 1.18/1.37  thf(t65_pre_topc, axiom,
% 1.18/1.37    (![A:$i]:
% 1.18/1.37     ( ( l1_pre_topc @ A ) =>
% 1.18/1.37       ( ![B:$i]:
% 1.18/1.37         ( ( l1_pre_topc @ B ) =>
% 1.18/1.37           ( ( m1_pre_topc @ A @ B ) <=>
% 1.18/1.37             ( m1_pre_topc @
% 1.18/1.37               A @ ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ) ))).
% 1.18/1.37  thf('32', plain,
% 1.18/1.37      (![X19 : $i, X20 : $i]:
% 1.18/1.37         (~ (l1_pre_topc @ X19)
% 1.18/1.37          | ~ (m1_pre_topc @ X20 @ X19)
% 1.18/1.37          | (m1_pre_topc @ X20 @ 
% 1.18/1.37             (g1_pre_topc @ (u1_struct_0 @ X19) @ (u1_pre_topc @ X19)))
% 1.18/1.37          | ~ (l1_pre_topc @ X20))),
% 1.18/1.37      inference('cnf', [status(esa)], [t65_pre_topc])).
% 1.18/1.37  thf('33', plain,
% 1.18/1.37      (![X0 : $i]:
% 1.18/1.37         (~ (l1_pre_topc @ X0)
% 1.18/1.37          | ~ (l1_pre_topc @ X0)
% 1.18/1.37          | (m1_pre_topc @ X0 @ 
% 1.18/1.37             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 1.18/1.37          | ~ (l1_pre_topc @ X0))),
% 1.18/1.37      inference('sup-', [status(thm)], ['31', '32'])).
% 1.18/1.37  thf('34', plain,
% 1.18/1.37      (![X0 : $i]:
% 1.18/1.37         ((m1_pre_topc @ X0 @ 
% 1.18/1.37           (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 1.18/1.37          | ~ (l1_pre_topc @ X0))),
% 1.18/1.37      inference('simplify', [status(thm)], ['33'])).
% 1.18/1.37  thf('35', plain, (((m1_pre_topc @ sk_C @ sk_D) | ~ (l1_pre_topc @ sk_C))),
% 1.18/1.37      inference('sup+', [status(thm)], ['30', '34'])).
% 1.18/1.37  thf('36', plain, ((l1_pre_topc @ sk_C)),
% 1.18/1.37      inference('demod', [status(thm)], ['7', '8'])).
% 1.18/1.37  thf('37', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 1.18/1.37      inference('demod', [status(thm)], ['35', '36'])).
% 1.18/1.37  thf('38', plain, ((r1_tarski @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_C))),
% 1.18/1.37      inference('demod', [status(thm)], ['22', '23', '29', '37'])).
% 1.18/1.37  thf(d10_xboole_0, axiom,
% 1.18/1.37    (![A:$i,B:$i]:
% 1.18/1.37     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.18/1.37  thf('39', plain,
% 1.18/1.37      (![X0 : $i, X2 : $i]:
% 1.18/1.37         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 1.18/1.37      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.18/1.37  thf('40', plain,
% 1.18/1.37      ((~ (r1_tarski @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D))
% 1.18/1.37        | ((u1_struct_0 @ sk_C) = (u1_struct_0 @ sk_D)))),
% 1.18/1.37      inference('sup-', [status(thm)], ['38', '39'])).
% 1.18/1.37  thf('41', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 1.18/1.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.37  thf('42', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 1.18/1.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.37  thf('43', plain,
% 1.18/1.37      (![X37 : $i, X38 : $i, X39 : $i]:
% 1.18/1.37         (~ (m1_pre_topc @ X37 @ X38)
% 1.18/1.37          | ~ (m1_pre_topc @ X37 @ X39)
% 1.18/1.37          | (r1_tarski @ (u1_struct_0 @ X37) @ (u1_struct_0 @ X39))
% 1.18/1.37          | ~ (m1_pre_topc @ X39 @ X38)
% 1.18/1.37          | ~ (l1_pre_topc @ X38)
% 1.18/1.37          | ~ (v2_pre_topc @ X38))),
% 1.18/1.37      inference('cnf', [status(esa)], [t4_tsep_1])).
% 1.18/1.37  thf('44', plain,
% 1.18/1.37      (![X0 : $i]:
% 1.18/1.37         (~ (v2_pre_topc @ sk_A)
% 1.18/1.37          | ~ (l1_pre_topc @ sk_A)
% 1.18/1.37          | ~ (m1_pre_topc @ X0 @ sk_A)
% 1.18/1.37          | (r1_tarski @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ X0))
% 1.18/1.37          | ~ (m1_pre_topc @ sk_C @ X0))),
% 1.18/1.37      inference('sup-', [status(thm)], ['42', '43'])).
% 1.18/1.37  thf('45', plain, ((v2_pre_topc @ sk_A)),
% 1.18/1.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.37  thf('46', plain, ((l1_pre_topc @ sk_A)),
% 1.18/1.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.37  thf('47', plain,
% 1.18/1.37      (![X0 : $i]:
% 1.18/1.37         (~ (m1_pre_topc @ X0 @ sk_A)
% 1.18/1.37          | (r1_tarski @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ X0))
% 1.18/1.37          | ~ (m1_pre_topc @ sk_C @ X0))),
% 1.18/1.37      inference('demod', [status(thm)], ['44', '45', '46'])).
% 1.18/1.37  thf('48', plain,
% 1.18/1.37      ((~ (m1_pre_topc @ sk_C @ sk_D)
% 1.18/1.37        | (r1_tarski @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D)))),
% 1.18/1.37      inference('sup-', [status(thm)], ['41', '47'])).
% 1.18/1.37  thf('49', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 1.18/1.37      inference('demod', [status(thm)], ['35', '36'])).
% 1.18/1.37  thf('50', plain, ((r1_tarski @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D))),
% 1.18/1.37      inference('demod', [status(thm)], ['48', '49'])).
% 1.18/1.37  thf('51', plain, (((u1_struct_0 @ sk_C) = (u1_struct_0 @ sk_D))),
% 1.18/1.37      inference('demod', [status(thm)], ['40', '50'])).
% 1.18/1.37  thf(d3_struct_0, axiom,
% 1.18/1.37    (![A:$i]:
% 1.18/1.37     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 1.18/1.37  thf('52', plain,
% 1.18/1.37      (![X7 : $i]:
% 1.18/1.37         (((k2_struct_0 @ X7) = (u1_struct_0 @ X7)) | ~ (l1_struct_0 @ X7))),
% 1.18/1.37      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.18/1.37  thf('53', plain, (((u1_struct_0 @ sk_C) = (u1_struct_0 @ sk_D))),
% 1.18/1.37      inference('demod', [status(thm)], ['40', '50'])).
% 1.18/1.37  thf('54', plain,
% 1.18/1.37      ((((u1_struct_0 @ sk_C) = (k2_struct_0 @ sk_D)) | ~ (l1_struct_0 @ sk_D))),
% 1.18/1.37      inference('sup+', [status(thm)], ['52', '53'])).
% 1.18/1.37  thf('55', plain, ((l1_pre_topc @ sk_D)),
% 1.18/1.37      inference('demod', [status(thm)], ['14', '15'])).
% 1.18/1.37  thf(dt_l1_pre_topc, axiom,
% 1.18/1.37    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 1.18/1.37  thf('56', plain, (![X8 : $i]: ((l1_struct_0 @ X8) | ~ (l1_pre_topc @ X8))),
% 1.18/1.37      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 1.18/1.37  thf('57', plain, ((l1_struct_0 @ sk_D)),
% 1.18/1.37      inference('sup-', [status(thm)], ['55', '56'])).
% 1.18/1.37  thf('58', plain, (((u1_struct_0 @ sk_C) = (k2_struct_0 @ sk_D))),
% 1.18/1.37      inference('demod', [status(thm)], ['54', '57'])).
% 1.18/1.37  thf('59', plain, (((k2_struct_0 @ sk_D) = (u1_struct_0 @ sk_D))),
% 1.18/1.37      inference('demod', [status(thm)], ['51', '58'])).
% 1.18/1.37  thf('60', plain,
% 1.18/1.37      (![X7 : $i]:
% 1.18/1.37         (((k2_struct_0 @ X7) = (u1_struct_0 @ X7)) | ~ (l1_struct_0 @ X7))),
% 1.18/1.37      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.18/1.37  thf('61', plain, (((u1_struct_0 @ sk_C) = (k2_struct_0 @ sk_D))),
% 1.18/1.37      inference('demod', [status(thm)], ['54', '57'])).
% 1.18/1.37  thf('62', plain,
% 1.18/1.37      ((((k2_struct_0 @ sk_C) = (k2_struct_0 @ sk_D)) | ~ (l1_struct_0 @ sk_C))),
% 1.18/1.37      inference('sup+', [status(thm)], ['60', '61'])).
% 1.18/1.37  thf('63', plain, ((l1_pre_topc @ sk_C)),
% 1.18/1.37      inference('demod', [status(thm)], ['7', '8'])).
% 1.18/1.37  thf('64', plain, (![X8 : $i]: ((l1_struct_0 @ X8) | ~ (l1_pre_topc @ X8))),
% 1.18/1.37      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 1.18/1.37  thf('65', plain, ((l1_struct_0 @ sk_C)),
% 1.18/1.37      inference('sup-', [status(thm)], ['63', '64'])).
% 1.18/1.37  thf('66', plain, (((k2_struct_0 @ sk_C) = (k2_struct_0 @ sk_D))),
% 1.18/1.37      inference('demod', [status(thm)], ['62', '65'])).
% 1.18/1.37  thf('67', plain, (((k2_struct_0 @ sk_C) = (u1_struct_0 @ sk_D))),
% 1.18/1.37      inference('demod', [status(thm)], ['59', '66'])).
% 1.18/1.37  thf('68', plain,
% 1.18/1.37      ((r1_tmap_1 @ sk_C @ sk_B @ 
% 1.18/1.37        (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_G)),
% 1.18/1.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.37  thf('69', plain, (((sk_F) = (sk_G))),
% 1.18/1.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.37  thf('70', plain,
% 1.18/1.37      ((r1_tmap_1 @ sk_C @ sk_B @ 
% 1.18/1.37        (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_F)),
% 1.18/1.37      inference('demod', [status(thm)], ['68', '69'])).
% 1.18/1.37  thf('71', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 1.18/1.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.37  thf('72', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 1.18/1.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.37  thf('73', plain,
% 1.18/1.37      ((m1_subset_1 @ sk_E @ 
% 1.18/1.37        (k1_zfmisc_1 @ 
% 1.18/1.37         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 1.18/1.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.37  thf(d5_tmap_1, axiom,
% 1.18/1.37    (![A:$i]:
% 1.18/1.37     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.18/1.37       ( ![B:$i]:
% 1.18/1.37         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 1.18/1.37             ( l1_pre_topc @ B ) ) =>
% 1.18/1.37           ( ![C:$i]:
% 1.18/1.37             ( ( m1_pre_topc @ C @ A ) =>
% 1.18/1.37               ( ![D:$i]:
% 1.18/1.37                 ( ( m1_pre_topc @ D @ A ) =>
% 1.18/1.37                   ( ![E:$i]:
% 1.18/1.37                     ( ( ( v1_funct_1 @ E ) & 
% 1.18/1.37                         ( v1_funct_2 @
% 1.18/1.37                           E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 1.18/1.37                         ( m1_subset_1 @
% 1.18/1.37                           E @ 
% 1.18/1.37                           ( k1_zfmisc_1 @
% 1.18/1.37                             ( k2_zfmisc_1 @
% 1.18/1.37                               ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 1.18/1.37                       ( ( m1_pre_topc @ D @ C ) =>
% 1.18/1.37                         ( ( k3_tmap_1 @ A @ B @ C @ D @ E ) =
% 1.18/1.37                           ( k2_partfun1 @
% 1.18/1.37                             ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ E @ 
% 1.18/1.37                             ( u1_struct_0 @ D ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 1.18/1.37  thf('74', plain,
% 1.18/1.37      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 1.18/1.37         ((v2_struct_0 @ X26)
% 1.18/1.37          | ~ (v2_pre_topc @ X26)
% 1.18/1.37          | ~ (l1_pre_topc @ X26)
% 1.18/1.37          | ~ (m1_pre_topc @ X27 @ X28)
% 1.18/1.37          | ~ (m1_pre_topc @ X27 @ X29)
% 1.18/1.37          | ((k3_tmap_1 @ X28 @ X26 @ X29 @ X27 @ X30)
% 1.18/1.37              = (k2_partfun1 @ (u1_struct_0 @ X29) @ (u1_struct_0 @ X26) @ 
% 1.18/1.37                 X30 @ (u1_struct_0 @ X27)))
% 1.18/1.37          | ~ (m1_subset_1 @ X30 @ 
% 1.18/1.37               (k1_zfmisc_1 @ 
% 1.18/1.37                (k2_zfmisc_1 @ (u1_struct_0 @ X29) @ (u1_struct_0 @ X26))))
% 1.18/1.37          | ~ (v1_funct_2 @ X30 @ (u1_struct_0 @ X29) @ (u1_struct_0 @ X26))
% 1.18/1.37          | ~ (v1_funct_1 @ X30)
% 1.18/1.37          | ~ (m1_pre_topc @ X29 @ X28)
% 1.18/1.37          | ~ (l1_pre_topc @ X28)
% 1.18/1.37          | ~ (v2_pre_topc @ X28)
% 1.18/1.37          | (v2_struct_0 @ X28))),
% 1.18/1.37      inference('cnf', [status(esa)], [d5_tmap_1])).
% 1.18/1.37  thf('75', plain,
% 1.18/1.37      (![X0 : $i, X1 : $i]:
% 1.18/1.37         ((v2_struct_0 @ X0)
% 1.18/1.37          | ~ (v2_pre_topc @ X0)
% 1.18/1.37          | ~ (l1_pre_topc @ X0)
% 1.18/1.37          | ~ (m1_pre_topc @ sk_D @ X0)
% 1.18/1.37          | ~ (v1_funct_1 @ sk_E)
% 1.18/1.37          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 1.18/1.37          | ((k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E)
% 1.18/1.37              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 1.18/1.37                 sk_E @ (u1_struct_0 @ X1)))
% 1.18/1.37          | ~ (m1_pre_topc @ X1 @ sk_D)
% 1.18/1.37          | ~ (m1_pre_topc @ X1 @ X0)
% 1.18/1.37          | ~ (l1_pre_topc @ sk_B)
% 1.18/1.37          | ~ (v2_pre_topc @ sk_B)
% 1.18/1.37          | (v2_struct_0 @ sk_B))),
% 1.18/1.37      inference('sup-', [status(thm)], ['73', '74'])).
% 1.18/1.37  thf('76', plain, ((v1_funct_1 @ sk_E)),
% 1.18/1.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.37  thf('77', plain,
% 1.18/1.37      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 1.18/1.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.37  thf('78', plain, ((l1_pre_topc @ sk_B)),
% 1.18/1.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.37  thf('79', plain, ((v2_pre_topc @ sk_B)),
% 1.18/1.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.37  thf('80', plain,
% 1.18/1.37      (![X0 : $i, X1 : $i]:
% 1.18/1.37         ((v2_struct_0 @ X0)
% 1.18/1.37          | ~ (v2_pre_topc @ X0)
% 1.18/1.37          | ~ (l1_pre_topc @ X0)
% 1.18/1.37          | ~ (m1_pre_topc @ sk_D @ X0)
% 1.18/1.37          | ((k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E)
% 1.18/1.37              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 1.18/1.37                 sk_E @ (u1_struct_0 @ X1)))
% 1.18/1.37          | ~ (m1_pre_topc @ X1 @ sk_D)
% 1.18/1.37          | ~ (m1_pre_topc @ X1 @ X0)
% 1.18/1.37          | (v2_struct_0 @ sk_B))),
% 1.18/1.37      inference('demod', [status(thm)], ['75', '76', '77', '78', '79'])).
% 1.18/1.37  thf('81', plain, (((k2_struct_0 @ sk_C) = (u1_struct_0 @ sk_D))),
% 1.18/1.37      inference('demod', [status(thm)], ['59', '66'])).
% 1.18/1.37  thf('82', plain,
% 1.18/1.37      (![X0 : $i, X1 : $i]:
% 1.18/1.37         ((v2_struct_0 @ X0)
% 1.18/1.37          | ~ (v2_pre_topc @ X0)
% 1.18/1.37          | ~ (l1_pre_topc @ X0)
% 1.18/1.37          | ~ (m1_pre_topc @ sk_D @ X0)
% 1.18/1.37          | ((k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E)
% 1.18/1.37              = (k2_partfun1 @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.18/1.37                 sk_E @ (u1_struct_0 @ X1)))
% 1.18/1.37          | ~ (m1_pre_topc @ X1 @ sk_D)
% 1.18/1.37          | ~ (m1_pre_topc @ X1 @ X0)
% 1.18/1.37          | (v2_struct_0 @ sk_B))),
% 1.18/1.37      inference('demod', [status(thm)], ['80', '81'])).
% 1.18/1.37  thf('83', plain,
% 1.18/1.37      (![X0 : $i]:
% 1.18/1.37         ((v2_struct_0 @ sk_B)
% 1.18/1.37          | ~ (m1_pre_topc @ X0 @ sk_A)
% 1.18/1.37          | ~ (m1_pre_topc @ X0 @ sk_D)
% 1.18/1.37          | ((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ X0 @ sk_E)
% 1.18/1.37              = (k2_partfun1 @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.18/1.37                 sk_E @ (u1_struct_0 @ X0)))
% 1.18/1.37          | ~ (l1_pre_topc @ sk_A)
% 1.18/1.37          | ~ (v2_pre_topc @ sk_A)
% 1.18/1.37          | (v2_struct_0 @ sk_A))),
% 1.18/1.37      inference('sup-', [status(thm)], ['72', '82'])).
% 1.18/1.37  thf('84', plain, ((l1_pre_topc @ sk_A)),
% 1.18/1.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.37  thf('85', plain, ((v2_pre_topc @ sk_A)),
% 1.18/1.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.37  thf('86', plain,
% 1.18/1.37      (![X0 : $i]:
% 1.18/1.37         ((v2_struct_0 @ sk_B)
% 1.18/1.37          | ~ (m1_pre_topc @ X0 @ sk_A)
% 1.18/1.37          | ~ (m1_pre_topc @ X0 @ sk_D)
% 1.18/1.37          | ((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ X0 @ sk_E)
% 1.18/1.37              = (k2_partfun1 @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.18/1.37                 sk_E @ (u1_struct_0 @ X0)))
% 1.18/1.37          | (v2_struct_0 @ sk_A))),
% 1.18/1.37      inference('demod', [status(thm)], ['83', '84', '85'])).
% 1.18/1.37  thf('87', plain,
% 1.18/1.37      (((v2_struct_0 @ sk_A)
% 1.18/1.37        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E)
% 1.18/1.37            = (k2_partfun1 @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.18/1.37               sk_E @ (u1_struct_0 @ sk_C)))
% 1.18/1.37        | ~ (m1_pre_topc @ sk_C @ sk_D)
% 1.18/1.37        | (v2_struct_0 @ sk_B))),
% 1.18/1.37      inference('sup-', [status(thm)], ['71', '86'])).
% 1.18/1.37  thf('88', plain, (((u1_struct_0 @ sk_C) = (k2_struct_0 @ sk_D))),
% 1.18/1.37      inference('demod', [status(thm)], ['54', '57'])).
% 1.18/1.37  thf('89', plain, (((k2_struct_0 @ sk_C) = (k2_struct_0 @ sk_D))),
% 1.18/1.37      inference('demod', [status(thm)], ['62', '65'])).
% 1.18/1.37  thf('90', plain, (((u1_struct_0 @ sk_C) = (k2_struct_0 @ sk_C))),
% 1.18/1.37      inference('demod', [status(thm)], ['88', '89'])).
% 1.18/1.37  thf('91', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 1.18/1.37      inference('demod', [status(thm)], ['35', '36'])).
% 1.18/1.37  thf('92', plain,
% 1.18/1.37      ((m1_subset_1 @ sk_E @ 
% 1.18/1.37        (k1_zfmisc_1 @ 
% 1.18/1.37         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 1.18/1.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.37  thf(d4_tmap_1, axiom,
% 1.18/1.37    (![A:$i]:
% 1.18/1.37     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.18/1.37       ( ![B:$i]:
% 1.18/1.37         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 1.18/1.37             ( l1_pre_topc @ B ) ) =>
% 1.18/1.37           ( ![C:$i]:
% 1.18/1.37             ( ( ( v1_funct_1 @ C ) & 
% 1.18/1.37                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 1.18/1.37                 ( m1_subset_1 @
% 1.18/1.37                   C @ 
% 1.18/1.37                   ( k1_zfmisc_1 @
% 1.18/1.37                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 1.18/1.37               ( ![D:$i]:
% 1.18/1.37                 ( ( m1_pre_topc @ D @ A ) =>
% 1.18/1.37                   ( ( k2_tmap_1 @ A @ B @ C @ D ) =
% 1.18/1.37                     ( k2_partfun1 @
% 1.18/1.37                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ 
% 1.18/1.37                       ( u1_struct_0 @ D ) ) ) ) ) ) ) ) ) ))).
% 1.18/1.37  thf('93', plain,
% 1.18/1.37      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 1.18/1.37         ((v2_struct_0 @ X22)
% 1.18/1.37          | ~ (v2_pre_topc @ X22)
% 1.18/1.37          | ~ (l1_pre_topc @ X22)
% 1.18/1.37          | ~ (m1_pre_topc @ X23 @ X24)
% 1.18/1.37          | ((k2_tmap_1 @ X24 @ X22 @ X25 @ X23)
% 1.18/1.37              = (k2_partfun1 @ (u1_struct_0 @ X24) @ (u1_struct_0 @ X22) @ 
% 1.18/1.37                 X25 @ (u1_struct_0 @ X23)))
% 1.18/1.37          | ~ (m1_subset_1 @ X25 @ 
% 1.18/1.37               (k1_zfmisc_1 @ 
% 1.18/1.37                (k2_zfmisc_1 @ (u1_struct_0 @ X24) @ (u1_struct_0 @ X22))))
% 1.18/1.37          | ~ (v1_funct_2 @ X25 @ (u1_struct_0 @ X24) @ (u1_struct_0 @ X22))
% 1.18/1.37          | ~ (v1_funct_1 @ X25)
% 1.18/1.37          | ~ (l1_pre_topc @ X24)
% 1.18/1.37          | ~ (v2_pre_topc @ X24)
% 1.18/1.37          | (v2_struct_0 @ X24))),
% 1.18/1.37      inference('cnf', [status(esa)], [d4_tmap_1])).
% 1.18/1.37  thf('94', plain,
% 1.18/1.37      (![X0 : $i]:
% 1.18/1.37         ((v2_struct_0 @ sk_D)
% 1.18/1.37          | ~ (v2_pre_topc @ sk_D)
% 1.18/1.37          | ~ (l1_pre_topc @ sk_D)
% 1.18/1.37          | ~ (v1_funct_1 @ sk_E)
% 1.18/1.37          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 1.18/1.37          | ((k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0)
% 1.18/1.37              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 1.18/1.37                 sk_E @ (u1_struct_0 @ X0)))
% 1.18/1.37          | ~ (m1_pre_topc @ X0 @ sk_D)
% 1.18/1.37          | ~ (l1_pre_topc @ sk_B)
% 1.18/1.37          | ~ (v2_pre_topc @ sk_B)
% 1.18/1.37          | (v2_struct_0 @ sk_B))),
% 1.18/1.37      inference('sup-', [status(thm)], ['92', '93'])).
% 1.18/1.37  thf('95', plain, ((v2_pre_topc @ sk_D)),
% 1.18/1.37      inference('demod', [status(thm)], ['26', '27', '28'])).
% 1.18/1.37  thf('96', plain, ((l1_pre_topc @ sk_D)),
% 1.18/1.37      inference('demod', [status(thm)], ['14', '15'])).
% 1.18/1.37  thf('97', plain, ((v1_funct_1 @ sk_E)),
% 1.18/1.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.37  thf('98', plain,
% 1.18/1.37      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 1.18/1.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.37  thf('99', plain, ((l1_pre_topc @ sk_B)),
% 1.18/1.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.37  thf('100', plain, ((v2_pre_topc @ sk_B)),
% 1.18/1.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.37  thf('101', plain,
% 1.18/1.37      (![X0 : $i]:
% 1.18/1.37         ((v2_struct_0 @ sk_D)
% 1.18/1.37          | ((k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0)
% 1.18/1.37              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 1.18/1.37                 sk_E @ (u1_struct_0 @ X0)))
% 1.18/1.37          | ~ (m1_pre_topc @ X0 @ sk_D)
% 1.18/1.37          | (v2_struct_0 @ sk_B))),
% 1.18/1.37      inference('demod', [status(thm)],
% 1.18/1.37                ['94', '95', '96', '97', '98', '99', '100'])).
% 1.18/1.37  thf('102', plain, (((k2_struct_0 @ sk_C) = (u1_struct_0 @ sk_D))),
% 1.18/1.37      inference('demod', [status(thm)], ['59', '66'])).
% 1.18/1.37  thf('103', plain,
% 1.18/1.37      (![X0 : $i]:
% 1.18/1.37         ((v2_struct_0 @ sk_D)
% 1.18/1.37          | ((k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0)
% 1.18/1.37              = (k2_partfun1 @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.18/1.37                 sk_E @ (u1_struct_0 @ X0)))
% 1.18/1.37          | ~ (m1_pre_topc @ X0 @ sk_D)
% 1.18/1.37          | (v2_struct_0 @ sk_B))),
% 1.18/1.37      inference('demod', [status(thm)], ['101', '102'])).
% 1.18/1.37  thf('104', plain,
% 1.18/1.37      (((v2_struct_0 @ sk_B)
% 1.18/1.37        | ((k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C)
% 1.18/1.37            = (k2_partfun1 @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.18/1.37               sk_E @ (u1_struct_0 @ sk_C)))
% 1.18/1.37        | (v2_struct_0 @ sk_D))),
% 1.18/1.37      inference('sup-', [status(thm)], ['91', '103'])).
% 1.18/1.37  thf('105', plain, (((u1_struct_0 @ sk_C) = (k2_struct_0 @ sk_C))),
% 1.18/1.37      inference('demod', [status(thm)], ['88', '89'])).
% 1.18/1.37  thf('106', plain,
% 1.18/1.37      (((v2_struct_0 @ sk_B)
% 1.18/1.37        | ((k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C)
% 1.18/1.37            = (k2_partfun1 @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.18/1.37               sk_E @ (k2_struct_0 @ sk_C)))
% 1.18/1.37        | (v2_struct_0 @ sk_D))),
% 1.18/1.37      inference('demod', [status(thm)], ['104', '105'])).
% 1.18/1.37  thf('107', plain, (~ (v2_struct_0 @ sk_B)),
% 1.18/1.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.37  thf('108', plain,
% 1.18/1.37      (((v2_struct_0 @ sk_D)
% 1.18/1.37        | ((k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C)
% 1.18/1.37            = (k2_partfun1 @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.18/1.37               sk_E @ (k2_struct_0 @ sk_C))))),
% 1.18/1.37      inference('clc', [status(thm)], ['106', '107'])).
% 1.18/1.37  thf('109', plain, (~ (v2_struct_0 @ sk_D)),
% 1.18/1.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.37  thf('110', plain,
% 1.18/1.37      (((k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C)
% 1.18/1.37         = (k2_partfun1 @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_E @ 
% 1.18/1.37            (k2_struct_0 @ sk_C)))),
% 1.18/1.37      inference('clc', [status(thm)], ['108', '109'])).
% 1.18/1.37  thf('111', plain,
% 1.18/1.37      (![X36 : $i]: ((m1_pre_topc @ X36 @ X36) | ~ (l1_pre_topc @ X36))),
% 1.18/1.37      inference('cnf', [status(esa)], [t2_tsep_1])).
% 1.18/1.37  thf('112', plain,
% 1.18/1.37      ((m1_subset_1 @ sk_E @ 
% 1.18/1.37        (k1_zfmisc_1 @ 
% 1.18/1.37         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 1.18/1.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.37  thf('113', plain, (((u1_struct_0 @ sk_C) = (u1_struct_0 @ sk_D))),
% 1.18/1.37      inference('demod', [status(thm)], ['40', '50'])).
% 1.18/1.37  thf('114', plain,
% 1.18/1.37      ((m1_subset_1 @ sk_E @ 
% 1.18/1.37        (k1_zfmisc_1 @ 
% 1.18/1.37         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 1.18/1.37      inference('demod', [status(thm)], ['112', '113'])).
% 1.18/1.37  thf('115', plain, (((u1_struct_0 @ sk_C) = (k2_struct_0 @ sk_C))),
% 1.18/1.37      inference('demod', [status(thm)], ['88', '89'])).
% 1.18/1.37  thf('116', plain,
% 1.18/1.37      ((m1_subset_1 @ sk_E @ 
% 1.18/1.37        (k1_zfmisc_1 @ 
% 1.18/1.37         (k2_zfmisc_1 @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 1.18/1.37      inference('demod', [status(thm)], ['114', '115'])).
% 1.18/1.37  thf('117', plain,
% 1.18/1.37      (![X7 : $i]:
% 1.18/1.37         (((k2_struct_0 @ X7) = (u1_struct_0 @ X7)) | ~ (l1_struct_0 @ X7))),
% 1.18/1.37      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.18/1.37  thf('118', plain,
% 1.18/1.37      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 1.18/1.37         ((v2_struct_0 @ X22)
% 1.18/1.37          | ~ (v2_pre_topc @ X22)
% 1.18/1.37          | ~ (l1_pre_topc @ X22)
% 1.18/1.37          | ~ (m1_pre_topc @ X23 @ X24)
% 1.18/1.37          | ((k2_tmap_1 @ X24 @ X22 @ X25 @ X23)
% 1.18/1.37              = (k2_partfun1 @ (u1_struct_0 @ X24) @ (u1_struct_0 @ X22) @ 
% 1.18/1.37                 X25 @ (u1_struct_0 @ X23)))
% 1.18/1.37          | ~ (m1_subset_1 @ X25 @ 
% 1.18/1.37               (k1_zfmisc_1 @ 
% 1.18/1.37                (k2_zfmisc_1 @ (u1_struct_0 @ X24) @ (u1_struct_0 @ X22))))
% 1.18/1.37          | ~ (v1_funct_2 @ X25 @ (u1_struct_0 @ X24) @ (u1_struct_0 @ X22))
% 1.18/1.37          | ~ (v1_funct_1 @ X25)
% 1.18/1.37          | ~ (l1_pre_topc @ X24)
% 1.18/1.37          | ~ (v2_pre_topc @ X24)
% 1.18/1.37          | (v2_struct_0 @ X24))),
% 1.18/1.37      inference('cnf', [status(esa)], [d4_tmap_1])).
% 1.18/1.37  thf('119', plain,
% 1.18/1.37      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.18/1.37         (~ (m1_subset_1 @ X2 @ 
% 1.18/1.37             (k1_zfmisc_1 @ 
% 1.18/1.37              (k2_zfmisc_1 @ (k2_struct_0 @ X0) @ (u1_struct_0 @ X1))))
% 1.18/1.37          | ~ (l1_struct_0 @ X0)
% 1.18/1.37          | (v2_struct_0 @ X0)
% 1.18/1.37          | ~ (v2_pre_topc @ X0)
% 1.18/1.37          | ~ (l1_pre_topc @ X0)
% 1.18/1.37          | ~ (v1_funct_1 @ X2)
% 1.18/1.37          | ~ (v1_funct_2 @ X2 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X1))
% 1.18/1.37          | ((k2_tmap_1 @ X0 @ X1 @ X2 @ X3)
% 1.18/1.37              = (k2_partfun1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X1) @ X2 @ 
% 1.18/1.37                 (u1_struct_0 @ X3)))
% 1.18/1.37          | ~ (m1_pre_topc @ X3 @ X0)
% 1.18/1.37          | ~ (l1_pre_topc @ X1)
% 1.18/1.37          | ~ (v2_pre_topc @ X1)
% 1.18/1.37          | (v2_struct_0 @ X1))),
% 1.18/1.37      inference('sup-', [status(thm)], ['117', '118'])).
% 1.18/1.37  thf('120', plain,
% 1.18/1.37      (![X0 : $i]:
% 1.18/1.37         ((v2_struct_0 @ sk_B)
% 1.18/1.37          | ~ (v2_pre_topc @ sk_B)
% 1.18/1.37          | ~ (l1_pre_topc @ sk_B)
% 1.18/1.37          | ~ (m1_pre_topc @ X0 @ sk_C)
% 1.18/1.37          | ((k2_tmap_1 @ sk_C @ sk_B @ sk_E @ X0)
% 1.18/1.37              = (k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.18/1.37                 sk_E @ (u1_struct_0 @ X0)))
% 1.18/1.37          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))
% 1.18/1.37          | ~ (v1_funct_1 @ sk_E)
% 1.18/1.37          | ~ (l1_pre_topc @ sk_C)
% 1.18/1.37          | ~ (v2_pre_topc @ sk_C)
% 1.18/1.37          | (v2_struct_0 @ sk_C)
% 1.18/1.37          | ~ (l1_struct_0 @ sk_C))),
% 1.18/1.37      inference('sup-', [status(thm)], ['116', '119'])).
% 1.18/1.37  thf('121', plain, ((v2_pre_topc @ sk_B)),
% 1.18/1.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.37  thf('122', plain, ((l1_pre_topc @ sk_B)),
% 1.18/1.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.37  thf('123', plain, (((u1_struct_0 @ sk_C) = (k2_struct_0 @ sk_C))),
% 1.18/1.37      inference('demod', [status(thm)], ['88', '89'])).
% 1.18/1.37  thf('124', plain, (((u1_struct_0 @ sk_C) = (k2_struct_0 @ sk_C))),
% 1.18/1.37      inference('demod', [status(thm)], ['88', '89'])).
% 1.18/1.37  thf('125', plain,
% 1.18/1.37      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 1.18/1.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.37  thf('126', plain, (((u1_struct_0 @ sk_C) = (u1_struct_0 @ sk_D))),
% 1.18/1.37      inference('demod', [status(thm)], ['40', '50'])).
% 1.18/1.37  thf('127', plain,
% 1.18/1.37      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 1.18/1.37      inference('demod', [status(thm)], ['125', '126'])).
% 1.18/1.37  thf('128', plain, (((u1_struct_0 @ sk_C) = (k2_struct_0 @ sk_C))),
% 1.18/1.37      inference('demod', [status(thm)], ['88', '89'])).
% 1.18/1.37  thf('129', plain,
% 1.18/1.37      ((v1_funct_2 @ sk_E @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 1.18/1.37      inference('demod', [status(thm)], ['127', '128'])).
% 1.18/1.37  thf('130', plain, ((v1_funct_1 @ sk_E)),
% 1.18/1.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.37  thf('131', plain, ((l1_pre_topc @ sk_C)),
% 1.18/1.37      inference('demod', [status(thm)], ['7', '8'])).
% 1.18/1.37  thf('132', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 1.18/1.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.37  thf('133', plain,
% 1.18/1.37      (![X5 : $i, X6 : $i]:
% 1.18/1.37         (~ (m1_pre_topc @ X5 @ X6)
% 1.18/1.37          | (v2_pre_topc @ X5)
% 1.18/1.37          | ~ (l1_pre_topc @ X6)
% 1.18/1.37          | ~ (v2_pre_topc @ X6))),
% 1.18/1.37      inference('cnf', [status(esa)], [cc1_pre_topc])).
% 1.18/1.37  thf('134', plain,
% 1.18/1.37      ((~ (v2_pre_topc @ sk_A) | ~ (l1_pre_topc @ sk_A) | (v2_pre_topc @ sk_C))),
% 1.18/1.37      inference('sup-', [status(thm)], ['132', '133'])).
% 1.18/1.37  thf('135', plain, ((v2_pre_topc @ sk_A)),
% 1.18/1.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.37  thf('136', plain, ((l1_pre_topc @ sk_A)),
% 1.18/1.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.37  thf('137', plain, ((v2_pre_topc @ sk_C)),
% 1.18/1.37      inference('demod', [status(thm)], ['134', '135', '136'])).
% 1.18/1.37  thf('138', plain, ((l1_struct_0 @ sk_C)),
% 1.18/1.37      inference('sup-', [status(thm)], ['63', '64'])).
% 1.18/1.37  thf('139', plain,
% 1.18/1.37      (![X0 : $i]:
% 1.18/1.37         ((v2_struct_0 @ sk_B)
% 1.18/1.37          | ~ (m1_pre_topc @ X0 @ sk_C)
% 1.18/1.37          | ((k2_tmap_1 @ sk_C @ sk_B @ sk_E @ X0)
% 1.18/1.37              = (k2_partfun1 @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.18/1.37                 sk_E @ (u1_struct_0 @ X0)))
% 1.18/1.37          | (v2_struct_0 @ sk_C))),
% 1.18/1.37      inference('demod', [status(thm)],
% 1.18/1.37                ['120', '121', '122', '123', '124', '129', '130', '131', 
% 1.18/1.37                 '137', '138'])).
% 1.18/1.37  thf('140', plain,
% 1.18/1.37      ((~ (l1_pre_topc @ sk_C)
% 1.18/1.37        | (v2_struct_0 @ sk_C)
% 1.18/1.37        | ((k2_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_C)
% 1.18/1.37            = (k2_partfun1 @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.18/1.37               sk_E @ (u1_struct_0 @ sk_C)))
% 1.18/1.37        | (v2_struct_0 @ sk_B))),
% 1.18/1.37      inference('sup-', [status(thm)], ['111', '139'])).
% 1.18/1.37  thf('141', plain, ((l1_pre_topc @ sk_C)),
% 1.18/1.37      inference('demod', [status(thm)], ['7', '8'])).
% 1.18/1.37  thf('142', plain, (((u1_struct_0 @ sk_C) = (k2_struct_0 @ sk_C))),
% 1.18/1.37      inference('demod', [status(thm)], ['88', '89'])).
% 1.18/1.37  thf('143', plain,
% 1.18/1.37      (((k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C)
% 1.18/1.37         = (k2_partfun1 @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_E @ 
% 1.18/1.37            (k2_struct_0 @ sk_C)))),
% 1.18/1.37      inference('clc', [status(thm)], ['108', '109'])).
% 1.18/1.37  thf('144', plain,
% 1.18/1.37      (((v2_struct_0 @ sk_C)
% 1.18/1.37        | ((k2_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_C)
% 1.18/1.37            = (k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C))
% 1.18/1.37        | (v2_struct_0 @ sk_B))),
% 1.18/1.37      inference('demod', [status(thm)], ['140', '141', '142', '143'])).
% 1.18/1.37  thf('145', plain, (~ (v2_struct_0 @ sk_C)),
% 1.18/1.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.37  thf('146', plain,
% 1.18/1.37      (((v2_struct_0 @ sk_B)
% 1.18/1.37        | ((k2_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_C)
% 1.18/1.37            = (k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C)))),
% 1.18/1.37      inference('clc', [status(thm)], ['144', '145'])).
% 1.18/1.37  thf('147', plain, (~ (v2_struct_0 @ sk_B)),
% 1.18/1.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.37  thf('148', plain,
% 1.18/1.37      (((k2_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_C)
% 1.18/1.37         = (k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C))),
% 1.18/1.37      inference('clc', [status(thm)], ['146', '147'])).
% 1.18/1.37  thf('149', plain,
% 1.18/1.37      (((k2_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_C)
% 1.18/1.37         = (k2_partfun1 @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_E @ 
% 1.18/1.37            (k2_struct_0 @ sk_C)))),
% 1.18/1.37      inference('demod', [status(thm)], ['110', '148'])).
% 1.18/1.37  thf('150', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 1.18/1.37      inference('demod', [status(thm)], ['35', '36'])).
% 1.18/1.37  thf('151', plain,
% 1.18/1.37      (((v2_struct_0 @ sk_A)
% 1.18/1.37        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E)
% 1.18/1.37            = (k2_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_C))
% 1.18/1.37        | (v2_struct_0 @ sk_B))),
% 1.18/1.37      inference('demod', [status(thm)], ['87', '90', '149', '150'])).
% 1.18/1.37  thf('152', plain, (~ (v2_struct_0 @ sk_A)),
% 1.18/1.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.37  thf('153', plain,
% 1.18/1.37      (((v2_struct_0 @ sk_B)
% 1.18/1.37        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E)
% 1.18/1.37            = (k2_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_C)))),
% 1.18/1.37      inference('clc', [status(thm)], ['151', '152'])).
% 1.18/1.37  thf('154', plain, (~ (v2_struct_0 @ sk_B)),
% 1.18/1.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.37  thf('155', plain,
% 1.18/1.37      (((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E)
% 1.18/1.37         = (k2_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_C))),
% 1.18/1.37      inference('clc', [status(thm)], ['153', '154'])).
% 1.18/1.37  thf('156', plain,
% 1.18/1.37      ((r1_tmap_1 @ sk_C @ sk_B @ (k2_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_C) @ 
% 1.18/1.37        sk_F)),
% 1.18/1.37      inference('demod', [status(thm)], ['70', '155'])).
% 1.18/1.37  thf('157', plain,
% 1.18/1.37      ((m1_subset_1 @ sk_E @ 
% 1.18/1.37        (k1_zfmisc_1 @ 
% 1.18/1.37         (k2_zfmisc_1 @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 1.18/1.37      inference('demod', [status(thm)], ['114', '115'])).
% 1.18/1.37  thf('158', plain,
% 1.18/1.37      (![X7 : $i]:
% 1.18/1.37         (((k2_struct_0 @ X7) = (u1_struct_0 @ X7)) | ~ (l1_struct_0 @ X7))),
% 1.18/1.37      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.18/1.37  thf(t67_tmap_1, axiom,
% 1.18/1.37    (![A:$i]:
% 1.18/1.37     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.18/1.37       ( ![B:$i]:
% 1.18/1.37         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 1.18/1.37             ( l1_pre_topc @ B ) ) =>
% 1.18/1.37           ( ![C:$i]:
% 1.18/1.37             ( ( ( v1_funct_1 @ C ) & 
% 1.18/1.37                 ( v1_funct_2 @ C @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 1.18/1.37                 ( m1_subset_1 @
% 1.18/1.37                   C @ 
% 1.18/1.37                   ( k1_zfmisc_1 @
% 1.18/1.37                     ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 1.18/1.37               ( ![D:$i]:
% 1.18/1.37                 ( ( ( ~( v2_struct_0 @ D ) ) & ( v1_tsep_1 @ D @ B ) & 
% 1.18/1.37                     ( m1_pre_topc @ D @ B ) ) =>
% 1.18/1.37                   ( ![E:$i]:
% 1.18/1.37                     ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) =>
% 1.18/1.37                       ( ![F:$i]:
% 1.18/1.37                         ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 1.18/1.37                           ( ( ( E ) = ( F ) ) =>
% 1.18/1.37                             ( ( r1_tmap_1 @ B @ A @ C @ E ) <=>
% 1.18/1.37                               ( r1_tmap_1 @
% 1.18/1.37                                 D @ A @ ( k2_tmap_1 @ B @ A @ C @ D ) @ F ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 1.18/1.37  thf('159', plain,
% 1.18/1.37      (![X40 : $i, X41 : $i, X42 : $i, X43 : $i, X44 : $i, X45 : $i]:
% 1.18/1.37         ((v2_struct_0 @ X40)
% 1.18/1.37          | ~ (v2_pre_topc @ X40)
% 1.18/1.37          | ~ (l1_pre_topc @ X40)
% 1.18/1.37          | (v2_struct_0 @ X41)
% 1.18/1.37          | ~ (v1_tsep_1 @ X41 @ X40)
% 1.18/1.37          | ~ (m1_pre_topc @ X41 @ X40)
% 1.18/1.37          | ~ (m1_subset_1 @ X42 @ (u1_struct_0 @ X41))
% 1.18/1.37          | ~ (r1_tmap_1 @ X41 @ X43 @ (k2_tmap_1 @ X40 @ X43 @ X44 @ X41) @ 
% 1.18/1.37               X42)
% 1.18/1.37          | (r1_tmap_1 @ X40 @ X43 @ X44 @ X45)
% 1.18/1.37          | ((X45) != (X42))
% 1.18/1.37          | ~ (m1_subset_1 @ X45 @ (u1_struct_0 @ X40))
% 1.18/1.37          | ~ (m1_subset_1 @ X44 @ 
% 1.18/1.37               (k1_zfmisc_1 @ 
% 1.18/1.37                (k2_zfmisc_1 @ (u1_struct_0 @ X40) @ (u1_struct_0 @ X43))))
% 1.18/1.37          | ~ (v1_funct_2 @ X44 @ (u1_struct_0 @ X40) @ (u1_struct_0 @ X43))
% 1.18/1.37          | ~ (v1_funct_1 @ X44)
% 1.18/1.37          | ~ (l1_pre_topc @ X43)
% 1.18/1.37          | ~ (v2_pre_topc @ X43)
% 1.18/1.37          | (v2_struct_0 @ X43))),
% 1.18/1.37      inference('cnf', [status(esa)], [t67_tmap_1])).
% 1.18/1.37  thf('160', plain,
% 1.18/1.37      (![X40 : $i, X41 : $i, X42 : $i, X43 : $i, X44 : $i]:
% 1.18/1.37         ((v2_struct_0 @ X43)
% 1.18/1.37          | ~ (v2_pre_topc @ X43)
% 1.18/1.37          | ~ (l1_pre_topc @ X43)
% 1.18/1.37          | ~ (v1_funct_1 @ X44)
% 1.18/1.37          | ~ (v1_funct_2 @ X44 @ (u1_struct_0 @ X40) @ (u1_struct_0 @ X43))
% 1.18/1.37          | ~ (m1_subset_1 @ X44 @ 
% 1.18/1.37               (k1_zfmisc_1 @ 
% 1.18/1.37                (k2_zfmisc_1 @ (u1_struct_0 @ X40) @ (u1_struct_0 @ X43))))
% 1.18/1.37          | ~ (m1_subset_1 @ X42 @ (u1_struct_0 @ X40))
% 1.18/1.37          | (r1_tmap_1 @ X40 @ X43 @ X44 @ X42)
% 1.18/1.37          | ~ (r1_tmap_1 @ X41 @ X43 @ (k2_tmap_1 @ X40 @ X43 @ X44 @ X41) @ 
% 1.18/1.37               X42)
% 1.18/1.37          | ~ (m1_subset_1 @ X42 @ (u1_struct_0 @ X41))
% 1.18/1.37          | ~ (m1_pre_topc @ X41 @ X40)
% 1.18/1.37          | ~ (v1_tsep_1 @ X41 @ X40)
% 1.18/1.37          | (v2_struct_0 @ X41)
% 1.18/1.37          | ~ (l1_pre_topc @ X40)
% 1.18/1.37          | ~ (v2_pre_topc @ X40)
% 1.18/1.37          | (v2_struct_0 @ X40))),
% 1.18/1.37      inference('simplify', [status(thm)], ['159'])).
% 1.18/1.37  thf('161', plain,
% 1.18/1.37      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 1.18/1.37         (~ (m1_subset_1 @ X2 @ 
% 1.18/1.37             (k1_zfmisc_1 @ 
% 1.18/1.37              (k2_zfmisc_1 @ (k2_struct_0 @ X0) @ (u1_struct_0 @ X1))))
% 1.18/1.37          | ~ (l1_struct_0 @ X0)
% 1.18/1.37          | (v2_struct_0 @ X0)
% 1.18/1.37          | ~ (v2_pre_topc @ X0)
% 1.18/1.37          | ~ (l1_pre_topc @ X0)
% 1.18/1.37          | (v2_struct_0 @ X3)
% 1.18/1.37          | ~ (v1_tsep_1 @ X3 @ X0)
% 1.18/1.37          | ~ (m1_pre_topc @ X3 @ X0)
% 1.18/1.37          | ~ (m1_subset_1 @ X4 @ (u1_struct_0 @ X3))
% 1.18/1.37          | ~ (r1_tmap_1 @ X3 @ X1 @ (k2_tmap_1 @ X0 @ X1 @ X2 @ X3) @ X4)
% 1.18/1.37          | (r1_tmap_1 @ X0 @ X1 @ X2 @ X4)
% 1.18/1.37          | ~ (m1_subset_1 @ X4 @ (u1_struct_0 @ X0))
% 1.18/1.37          | ~ (v1_funct_2 @ X2 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X1))
% 1.18/1.37          | ~ (v1_funct_1 @ X2)
% 1.18/1.37          | ~ (l1_pre_topc @ X1)
% 1.18/1.37          | ~ (v2_pre_topc @ X1)
% 1.18/1.37          | (v2_struct_0 @ X1))),
% 1.18/1.37      inference('sup-', [status(thm)], ['158', '160'])).
% 1.18/1.37  thf('162', plain,
% 1.18/1.37      (![X0 : $i, X1 : $i]:
% 1.18/1.37         ((v2_struct_0 @ sk_B)
% 1.18/1.37          | ~ (v2_pre_topc @ sk_B)
% 1.18/1.37          | ~ (l1_pre_topc @ sk_B)
% 1.18/1.37          | ~ (v1_funct_1 @ sk_E)
% 1.18/1.37          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))
% 1.18/1.37          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_C))
% 1.18/1.37          | (r1_tmap_1 @ sk_C @ sk_B @ sk_E @ X0)
% 1.18/1.37          | ~ (r1_tmap_1 @ X1 @ sk_B @ (k2_tmap_1 @ sk_C @ sk_B @ sk_E @ X1) @ 
% 1.18/1.37               X0)
% 1.18/1.37          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ X1))
% 1.18/1.37          | ~ (m1_pre_topc @ X1 @ sk_C)
% 1.18/1.37          | ~ (v1_tsep_1 @ X1 @ sk_C)
% 1.18/1.37          | (v2_struct_0 @ X1)
% 1.18/1.37          | ~ (l1_pre_topc @ sk_C)
% 1.18/1.37          | ~ (v2_pre_topc @ sk_C)
% 1.18/1.37          | (v2_struct_0 @ sk_C)
% 1.18/1.37          | ~ (l1_struct_0 @ sk_C))),
% 1.18/1.37      inference('sup-', [status(thm)], ['157', '161'])).
% 1.18/1.37  thf('163', plain, ((v2_pre_topc @ sk_B)),
% 1.18/1.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.37  thf('164', plain, ((l1_pre_topc @ sk_B)),
% 1.18/1.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.37  thf('165', plain, ((v1_funct_1 @ sk_E)),
% 1.18/1.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.37  thf('166', plain, (((u1_struct_0 @ sk_C) = (k2_struct_0 @ sk_C))),
% 1.18/1.37      inference('demod', [status(thm)], ['88', '89'])).
% 1.18/1.37  thf('167', plain,
% 1.18/1.37      ((v1_funct_2 @ sk_E @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 1.18/1.37      inference('demod', [status(thm)], ['127', '128'])).
% 1.18/1.37  thf('168', plain, (((u1_struct_0 @ sk_C) = (k2_struct_0 @ sk_C))),
% 1.18/1.37      inference('demod', [status(thm)], ['88', '89'])).
% 1.18/1.37  thf('169', plain, ((l1_pre_topc @ sk_C)),
% 1.18/1.37      inference('demod', [status(thm)], ['7', '8'])).
% 1.18/1.37  thf('170', plain, ((v2_pre_topc @ sk_C)),
% 1.18/1.37      inference('demod', [status(thm)], ['134', '135', '136'])).
% 1.18/1.37  thf('171', plain, ((l1_struct_0 @ sk_C)),
% 1.18/1.37      inference('sup-', [status(thm)], ['63', '64'])).
% 1.18/1.37  thf('172', plain,
% 1.18/1.37      (![X0 : $i, X1 : $i]:
% 1.18/1.37         ((v2_struct_0 @ sk_B)
% 1.18/1.37          | ~ (m1_subset_1 @ X0 @ (k2_struct_0 @ sk_C))
% 1.18/1.37          | (r1_tmap_1 @ sk_C @ sk_B @ sk_E @ X0)
% 1.18/1.37          | ~ (r1_tmap_1 @ X1 @ sk_B @ (k2_tmap_1 @ sk_C @ sk_B @ sk_E @ X1) @ 
% 1.18/1.37               X0)
% 1.18/1.37          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ X1))
% 1.18/1.37          | ~ (m1_pre_topc @ X1 @ sk_C)
% 1.18/1.37          | ~ (v1_tsep_1 @ X1 @ sk_C)
% 1.18/1.37          | (v2_struct_0 @ X1)
% 1.18/1.37          | (v2_struct_0 @ sk_C))),
% 1.18/1.37      inference('demod', [status(thm)],
% 1.18/1.37                ['162', '163', '164', '165', '166', '167', '168', '169', 
% 1.18/1.37                 '170', '171'])).
% 1.18/1.37  thf('173', plain,
% 1.18/1.37      (((v2_struct_0 @ sk_C)
% 1.18/1.37        | (v2_struct_0 @ sk_C)
% 1.18/1.37        | ~ (v1_tsep_1 @ sk_C @ sk_C)
% 1.18/1.37        | ~ (m1_pre_topc @ sk_C @ sk_C)
% 1.18/1.37        | ~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C))
% 1.18/1.37        | (r1_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_F)
% 1.18/1.37        | ~ (m1_subset_1 @ sk_F @ (k2_struct_0 @ sk_C))
% 1.18/1.37        | (v2_struct_0 @ sk_B))),
% 1.18/1.37      inference('sup-', [status(thm)], ['156', '172'])).
% 1.18/1.37  thf('174', plain,
% 1.18/1.37      (((g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) = (sk_D))),
% 1.18/1.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.37  thf(fc10_tops_1, axiom,
% 1.18/1.37    (![A:$i]:
% 1.18/1.37     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.18/1.37       ( v3_pre_topc @ ( k2_struct_0 @ A ) @ A ) ))).
% 1.18/1.37  thf('175', plain,
% 1.18/1.37      (![X21 : $i]:
% 1.18/1.37         ((v3_pre_topc @ (k2_struct_0 @ X21) @ X21)
% 1.18/1.37          | ~ (l1_pre_topc @ X21)
% 1.18/1.37          | ~ (v2_pre_topc @ X21))),
% 1.18/1.37      inference('cnf', [status(esa)], [fc10_tops_1])).
% 1.18/1.37  thf('176', plain,
% 1.18/1.37      (![X7 : $i]:
% 1.18/1.37         (((k2_struct_0 @ X7) = (u1_struct_0 @ X7)) | ~ (l1_struct_0 @ X7))),
% 1.18/1.37      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.18/1.37  thf(dt_k2_subset_1, axiom,
% 1.18/1.37    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 1.18/1.37  thf('177', plain,
% 1.18/1.37      (![X4 : $i]: (m1_subset_1 @ (k2_subset_1 @ X4) @ (k1_zfmisc_1 @ X4))),
% 1.18/1.37      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 1.18/1.37  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 1.18/1.37  thf('178', plain, (![X3 : $i]: ((k2_subset_1 @ X3) = (X3))),
% 1.18/1.37      inference('cnf', [status(esa)], [d4_subset_1])).
% 1.18/1.37  thf('179', plain, (![X4 : $i]: (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X4))),
% 1.18/1.37      inference('demod', [status(thm)], ['177', '178'])).
% 1.18/1.37  thf(t60_pre_topc, axiom,
% 1.18/1.37    (![A:$i]:
% 1.18/1.37     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.18/1.37       ( ![B:$i]:
% 1.18/1.37         ( ( ( v3_pre_topc @ B @ A ) & 
% 1.18/1.37             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) <=>
% 1.18/1.37           ( ( v3_pre_topc @
% 1.18/1.37               B @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) & 
% 1.18/1.37             ( m1_subset_1 @
% 1.18/1.37               B @ 
% 1.18/1.37               ( k1_zfmisc_1 @
% 1.18/1.37                 ( u1_struct_0 @
% 1.18/1.37                   ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ) ) ) ) ))).
% 1.18/1.37  thf('180', plain,
% 1.18/1.37      (![X17 : $i, X18 : $i]:
% 1.18/1.37         (~ (v3_pre_topc @ X18 @ X17)
% 1.18/1.37          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 1.18/1.37          | (m1_subset_1 @ X18 @ 
% 1.18/1.37             (k1_zfmisc_1 @ 
% 1.18/1.37              (u1_struct_0 @ 
% 1.18/1.37               (g1_pre_topc @ (u1_struct_0 @ X17) @ (u1_pre_topc @ X17)))))
% 1.18/1.37          | ~ (l1_pre_topc @ X17)
% 1.18/1.37          | ~ (v2_pre_topc @ X17))),
% 1.18/1.37      inference('cnf', [status(esa)], [t60_pre_topc])).
% 1.18/1.37  thf('181', plain,
% 1.18/1.37      (![X0 : $i]:
% 1.18/1.37         (~ (v2_pre_topc @ X0)
% 1.18/1.37          | ~ (l1_pre_topc @ X0)
% 1.18/1.37          | (m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 1.18/1.37             (k1_zfmisc_1 @ 
% 1.18/1.37              (u1_struct_0 @ 
% 1.18/1.37               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))))
% 1.18/1.37          | ~ (v3_pre_topc @ (u1_struct_0 @ X0) @ X0))),
% 1.18/1.37      inference('sup-', [status(thm)], ['179', '180'])).
% 1.18/1.37  thf('182', plain,
% 1.18/1.37      (![X0 : $i]:
% 1.18/1.37         (~ (v3_pre_topc @ (k2_struct_0 @ X0) @ X0)
% 1.18/1.37          | ~ (l1_struct_0 @ X0)
% 1.18/1.37          | (m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 1.18/1.37             (k1_zfmisc_1 @ 
% 1.18/1.37              (u1_struct_0 @ 
% 1.18/1.37               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))))
% 1.18/1.37          | ~ (l1_pre_topc @ X0)
% 1.18/1.37          | ~ (v2_pre_topc @ X0))),
% 1.18/1.37      inference('sup-', [status(thm)], ['176', '181'])).
% 1.18/1.37  thf('183', plain,
% 1.18/1.37      (![X0 : $i]:
% 1.18/1.37         (~ (v2_pre_topc @ X0)
% 1.18/1.37          | ~ (l1_pre_topc @ X0)
% 1.18/1.37          | ~ (v2_pre_topc @ X0)
% 1.18/1.37          | ~ (l1_pre_topc @ X0)
% 1.18/1.37          | (m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 1.18/1.37             (k1_zfmisc_1 @ 
% 1.18/1.37              (u1_struct_0 @ 
% 1.18/1.37               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))))
% 1.18/1.37          | ~ (l1_struct_0 @ X0))),
% 1.18/1.37      inference('sup-', [status(thm)], ['175', '182'])).
% 1.18/1.37  thf('184', plain,
% 1.18/1.37      (![X0 : $i]:
% 1.18/1.37         (~ (l1_struct_0 @ X0)
% 1.18/1.37          | (m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 1.18/1.37             (k1_zfmisc_1 @ 
% 1.18/1.37              (u1_struct_0 @ 
% 1.18/1.37               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))))
% 1.18/1.37          | ~ (l1_pre_topc @ X0)
% 1.18/1.37          | ~ (v2_pre_topc @ X0))),
% 1.18/1.37      inference('simplify', [status(thm)], ['183'])).
% 1.18/1.37  thf('185', plain,
% 1.18/1.37      (![X16 : $i, X17 : $i]:
% 1.18/1.37         (~ (v3_pre_topc @ X16 @ 
% 1.18/1.37             (g1_pre_topc @ (u1_struct_0 @ X17) @ (u1_pre_topc @ X17)))
% 1.18/1.37          | ~ (m1_subset_1 @ X16 @ 
% 1.18/1.37               (k1_zfmisc_1 @ 
% 1.18/1.37                (u1_struct_0 @ 
% 1.18/1.37                 (g1_pre_topc @ (u1_struct_0 @ X17) @ (u1_pre_topc @ X17)))))
% 1.18/1.37          | (v3_pre_topc @ X16 @ X17)
% 1.18/1.37          | ~ (l1_pre_topc @ X17)
% 1.18/1.37          | ~ (v2_pre_topc @ X17))),
% 1.18/1.37      inference('cnf', [status(esa)], [t60_pre_topc])).
% 1.18/1.37  thf('186', plain,
% 1.18/1.37      (![X0 : $i]:
% 1.18/1.37         (~ (v2_pre_topc @ X0)
% 1.18/1.37          | ~ (l1_pre_topc @ X0)
% 1.18/1.37          | ~ (l1_struct_0 @ X0)
% 1.18/1.37          | ~ (v2_pre_topc @ X0)
% 1.18/1.37          | ~ (l1_pre_topc @ X0)
% 1.18/1.37          | (v3_pre_topc @ (u1_struct_0 @ X0) @ X0)
% 1.18/1.37          | ~ (v3_pre_topc @ (u1_struct_0 @ X0) @ 
% 1.18/1.37               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 1.18/1.37      inference('sup-', [status(thm)], ['184', '185'])).
% 1.18/1.37  thf('187', plain,
% 1.18/1.37      (![X0 : $i]:
% 1.18/1.37         (~ (v3_pre_topc @ (u1_struct_0 @ X0) @ 
% 1.18/1.37             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 1.18/1.37          | (v3_pre_topc @ (u1_struct_0 @ X0) @ X0)
% 1.18/1.37          | ~ (l1_struct_0 @ X0)
% 1.18/1.37          | ~ (l1_pre_topc @ X0)
% 1.18/1.37          | ~ (v2_pre_topc @ X0))),
% 1.18/1.37      inference('simplify', [status(thm)], ['186'])).
% 1.18/1.37  thf('188', plain,
% 1.18/1.37      ((~ (v3_pre_topc @ (u1_struct_0 @ sk_C) @ sk_D)
% 1.18/1.37        | ~ (v2_pre_topc @ sk_C)
% 1.18/1.37        | ~ (l1_pre_topc @ sk_C)
% 1.18/1.37        | ~ (l1_struct_0 @ sk_C)
% 1.18/1.37        | (v3_pre_topc @ (u1_struct_0 @ sk_C) @ sk_C))),
% 1.18/1.37      inference('sup-', [status(thm)], ['174', '187'])).
% 1.18/1.37  thf('189', plain, ((v2_pre_topc @ sk_C)),
% 1.18/1.37      inference('demod', [status(thm)], ['134', '135', '136'])).
% 1.18/1.37  thf('190', plain, ((l1_pre_topc @ sk_C)),
% 1.18/1.37      inference('demod', [status(thm)], ['7', '8'])).
% 1.18/1.37  thf('191', plain, ((l1_struct_0 @ sk_C)),
% 1.18/1.37      inference('sup-', [status(thm)], ['63', '64'])).
% 1.18/1.37  thf('192', plain,
% 1.18/1.37      ((~ (v3_pre_topc @ (u1_struct_0 @ sk_C) @ sk_D)
% 1.18/1.37        | (v3_pre_topc @ (u1_struct_0 @ sk_C) @ sk_C))),
% 1.18/1.37      inference('demod', [status(thm)], ['188', '189', '190', '191'])).
% 1.18/1.37  thf('193', plain,
% 1.18/1.37      (((g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) = (sk_D))),
% 1.18/1.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.37  thf('194', plain,
% 1.18/1.37      (![X21 : $i]:
% 1.18/1.37         ((v3_pre_topc @ (k2_struct_0 @ X21) @ X21)
% 1.18/1.37          | ~ (l1_pre_topc @ X21)
% 1.18/1.37          | ~ (v2_pre_topc @ X21))),
% 1.18/1.37      inference('cnf', [status(esa)], [fc10_tops_1])).
% 1.18/1.37  thf('195', plain,
% 1.18/1.37      (![X7 : $i]:
% 1.18/1.37         (((k2_struct_0 @ X7) = (u1_struct_0 @ X7)) | ~ (l1_struct_0 @ X7))),
% 1.18/1.37      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.18/1.37  thf('196', plain, (![X4 : $i]: (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X4))),
% 1.18/1.37      inference('demod', [status(thm)], ['177', '178'])).
% 1.18/1.37  thf('197', plain,
% 1.18/1.37      (![X17 : $i, X18 : $i]:
% 1.18/1.37         (~ (v3_pre_topc @ X18 @ X17)
% 1.18/1.37          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 1.18/1.37          | (v3_pre_topc @ X18 @ 
% 1.18/1.37             (g1_pre_topc @ (u1_struct_0 @ X17) @ (u1_pre_topc @ X17)))
% 1.18/1.37          | ~ (l1_pre_topc @ X17)
% 1.18/1.37          | ~ (v2_pre_topc @ X17))),
% 1.18/1.37      inference('cnf', [status(esa)], [t60_pre_topc])).
% 1.18/1.37  thf('198', plain,
% 1.18/1.37      (![X0 : $i]:
% 1.18/1.37         (~ (v2_pre_topc @ X0)
% 1.18/1.37          | ~ (l1_pre_topc @ X0)
% 1.18/1.37          | (v3_pre_topc @ (u1_struct_0 @ X0) @ 
% 1.18/1.37             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 1.18/1.37          | ~ (v3_pre_topc @ (u1_struct_0 @ X0) @ X0))),
% 1.18/1.37      inference('sup-', [status(thm)], ['196', '197'])).
% 1.18/1.37  thf('199', plain,
% 1.18/1.37      (![X0 : $i]:
% 1.18/1.37         (~ (v3_pre_topc @ (k2_struct_0 @ X0) @ X0)
% 1.18/1.37          | ~ (l1_struct_0 @ X0)
% 1.18/1.37          | (v3_pre_topc @ (u1_struct_0 @ X0) @ 
% 1.18/1.37             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 1.18/1.37          | ~ (l1_pre_topc @ X0)
% 1.18/1.37          | ~ (v2_pre_topc @ X0))),
% 1.18/1.37      inference('sup-', [status(thm)], ['195', '198'])).
% 1.18/1.37  thf('200', plain,
% 1.18/1.37      (![X0 : $i]:
% 1.18/1.37         (~ (v2_pre_topc @ X0)
% 1.18/1.37          | ~ (l1_pre_topc @ X0)
% 1.18/1.37          | ~ (v2_pre_topc @ X0)
% 1.18/1.37          | ~ (l1_pre_topc @ X0)
% 1.18/1.37          | (v3_pre_topc @ (u1_struct_0 @ X0) @ 
% 1.18/1.37             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 1.18/1.37          | ~ (l1_struct_0 @ X0))),
% 1.18/1.37      inference('sup-', [status(thm)], ['194', '199'])).
% 1.18/1.37  thf('201', plain,
% 1.18/1.37      (![X0 : $i]:
% 1.18/1.37         (~ (l1_struct_0 @ X0)
% 1.18/1.37          | (v3_pre_topc @ (u1_struct_0 @ X0) @ 
% 1.18/1.37             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 1.18/1.37          | ~ (l1_pre_topc @ X0)
% 1.18/1.37          | ~ (v2_pre_topc @ X0))),
% 1.18/1.37      inference('simplify', [status(thm)], ['200'])).
% 1.18/1.37  thf('202', plain,
% 1.18/1.37      (((v3_pre_topc @ (u1_struct_0 @ sk_C) @ sk_D)
% 1.18/1.37        | ~ (v2_pre_topc @ sk_C)
% 1.18/1.37        | ~ (l1_pre_topc @ sk_C)
% 1.18/1.37        | ~ (l1_struct_0 @ sk_C))),
% 1.18/1.37      inference('sup+', [status(thm)], ['193', '201'])).
% 1.18/1.37  thf('203', plain, ((v2_pre_topc @ sk_C)),
% 1.18/1.37      inference('demod', [status(thm)], ['134', '135', '136'])).
% 1.18/1.37  thf('204', plain, ((l1_pre_topc @ sk_C)),
% 1.18/1.37      inference('demod', [status(thm)], ['7', '8'])).
% 1.18/1.37  thf('205', plain, ((l1_struct_0 @ sk_C)),
% 1.18/1.37      inference('sup-', [status(thm)], ['63', '64'])).
% 1.18/1.37  thf('206', plain, ((v3_pre_topc @ (u1_struct_0 @ sk_C) @ sk_D)),
% 1.18/1.37      inference('demod', [status(thm)], ['202', '203', '204', '205'])).
% 1.18/1.37  thf('207', plain, ((v3_pre_topc @ (u1_struct_0 @ sk_C) @ sk_C)),
% 1.18/1.37      inference('demod', [status(thm)], ['192', '206'])).
% 1.18/1.37  thf('208', plain, (![X4 : $i]: (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X4))),
% 1.18/1.37      inference('demod', [status(thm)], ['177', '178'])).
% 1.18/1.37  thf(t16_tsep_1, axiom,
% 1.18/1.37    (![A:$i]:
% 1.18/1.37     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.18/1.37       ( ![B:$i]:
% 1.18/1.37         ( ( m1_pre_topc @ B @ A ) =>
% 1.18/1.37           ( ![C:$i]:
% 1.18/1.37             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.18/1.37               ( ( ( C ) = ( u1_struct_0 @ B ) ) =>
% 1.18/1.37                 ( ( ( v1_tsep_1 @ B @ A ) & ( m1_pre_topc @ B @ A ) ) <=>
% 1.18/1.37                   ( v3_pre_topc @ C @ A ) ) ) ) ) ) ) ))).
% 1.18/1.37  thf('209', plain,
% 1.18/1.37      (![X31 : $i, X32 : $i, X33 : $i]:
% 1.18/1.37         (~ (m1_pre_topc @ X31 @ X32)
% 1.18/1.37          | ((X33) != (u1_struct_0 @ X31))
% 1.18/1.37          | ~ (v3_pre_topc @ X33 @ X32)
% 1.18/1.37          | (v1_tsep_1 @ X31 @ X32)
% 1.18/1.37          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (u1_struct_0 @ X32)))
% 1.18/1.37          | ~ (l1_pre_topc @ X32)
% 1.18/1.37          | ~ (v2_pre_topc @ X32))),
% 1.18/1.37      inference('cnf', [status(esa)], [t16_tsep_1])).
% 1.18/1.37  thf('210', plain,
% 1.18/1.37      (![X31 : $i, X32 : $i]:
% 1.18/1.37         (~ (v2_pre_topc @ X32)
% 1.18/1.37          | ~ (l1_pre_topc @ X32)
% 1.18/1.37          | ~ (m1_subset_1 @ (u1_struct_0 @ X31) @ 
% 1.18/1.37               (k1_zfmisc_1 @ (u1_struct_0 @ X32)))
% 1.18/1.37          | (v1_tsep_1 @ X31 @ X32)
% 1.18/1.37          | ~ (v3_pre_topc @ (u1_struct_0 @ X31) @ X32)
% 1.18/1.37          | ~ (m1_pre_topc @ X31 @ X32))),
% 1.18/1.37      inference('simplify', [status(thm)], ['209'])).
% 1.18/1.37  thf('211', plain,
% 1.18/1.37      (![X0 : $i]:
% 1.18/1.37         (~ (m1_pre_topc @ X0 @ X0)
% 1.18/1.37          | ~ (v3_pre_topc @ (u1_struct_0 @ X0) @ X0)
% 1.18/1.37          | (v1_tsep_1 @ X0 @ X0)
% 1.18/1.37          | ~ (l1_pre_topc @ X0)
% 1.18/1.37          | ~ (v2_pre_topc @ X0))),
% 1.18/1.37      inference('sup-', [status(thm)], ['208', '210'])).
% 1.18/1.37  thf('212', plain,
% 1.18/1.37      ((~ (v2_pre_topc @ sk_C)
% 1.18/1.37        | ~ (l1_pre_topc @ sk_C)
% 1.18/1.37        | (v1_tsep_1 @ sk_C @ sk_C)
% 1.18/1.37        | ~ (m1_pre_topc @ sk_C @ sk_C))),
% 1.18/1.37      inference('sup-', [status(thm)], ['207', '211'])).
% 1.18/1.37  thf('213', plain, ((v2_pre_topc @ sk_C)),
% 1.18/1.37      inference('demod', [status(thm)], ['134', '135', '136'])).
% 1.18/1.37  thf('214', plain, ((l1_pre_topc @ sk_C)),
% 1.18/1.37      inference('demod', [status(thm)], ['7', '8'])).
% 1.18/1.37  thf('215', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 1.18/1.37      inference('demod', [status(thm)], ['35', '36'])).
% 1.18/1.37  thf('216', plain,
% 1.18/1.37      (![X0 : $i]: (~ (m1_pre_topc @ X0 @ sk_D) | (m1_pre_topc @ X0 @ sk_C))),
% 1.18/1.37      inference('demod', [status(thm)], ['4', '9'])).
% 1.18/1.37  thf('217', plain, ((m1_pre_topc @ sk_C @ sk_C)),
% 1.18/1.37      inference('sup-', [status(thm)], ['215', '216'])).
% 1.18/1.37  thf('218', plain, ((v1_tsep_1 @ sk_C @ sk_C)),
% 1.18/1.37      inference('demod', [status(thm)], ['212', '213', '214', '217'])).
% 1.18/1.37  thf('219', plain, ((m1_pre_topc @ sk_C @ sk_C)),
% 1.18/1.37      inference('sup-', [status(thm)], ['215', '216'])).
% 1.18/1.37  thf('220', plain, (((u1_struct_0 @ sk_C) = (k2_struct_0 @ sk_C))),
% 1.18/1.37      inference('demod', [status(thm)], ['88', '89'])).
% 1.18/1.37  thf('221', plain,
% 1.18/1.37      (![X7 : $i]:
% 1.18/1.37         (((k2_struct_0 @ X7) = (u1_struct_0 @ X7)) | ~ (l1_struct_0 @ X7))),
% 1.18/1.37      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.18/1.37  thf('222', plain, ((m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_C))),
% 1.18/1.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.37  thf('223', plain, (((sk_F) = (sk_G))),
% 1.18/1.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.37  thf('224', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C))),
% 1.18/1.37      inference('demod', [status(thm)], ['222', '223'])).
% 1.18/1.37  thf('225', plain,
% 1.18/1.37      (((m1_subset_1 @ sk_F @ (k2_struct_0 @ sk_C)) | ~ (l1_struct_0 @ sk_C))),
% 1.18/1.37      inference('sup+', [status(thm)], ['221', '224'])).
% 1.18/1.37  thf('226', plain, ((l1_struct_0 @ sk_C)),
% 1.18/1.37      inference('sup-', [status(thm)], ['63', '64'])).
% 1.18/1.37  thf('227', plain, ((m1_subset_1 @ sk_F @ (k2_struct_0 @ sk_C))),
% 1.18/1.37      inference('demod', [status(thm)], ['225', '226'])).
% 1.18/1.37  thf('228', plain, ((m1_subset_1 @ sk_F @ (k2_struct_0 @ sk_C))),
% 1.18/1.37      inference('demod', [status(thm)], ['225', '226'])).
% 1.18/1.37  thf('229', plain,
% 1.18/1.37      (((v2_struct_0 @ sk_C)
% 1.18/1.37        | (v2_struct_0 @ sk_C)
% 1.18/1.37        | (r1_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_F)
% 1.18/1.37        | (v2_struct_0 @ sk_B))),
% 1.18/1.37      inference('demod', [status(thm)],
% 1.18/1.37                ['173', '218', '219', '220', '227', '228'])).
% 1.18/1.37  thf('230', plain,
% 1.18/1.37      (((v2_struct_0 @ sk_B)
% 1.18/1.37        | (r1_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_F)
% 1.18/1.37        | (v2_struct_0 @ sk_C))),
% 1.18/1.37      inference('simplify', [status(thm)], ['229'])).
% 1.18/1.37  thf('231', plain, (~ (v2_struct_0 @ sk_B)),
% 1.18/1.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.37  thf('232', plain,
% 1.18/1.37      (((v2_struct_0 @ sk_C) | (r1_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_F))),
% 1.18/1.37      inference('clc', [status(thm)], ['230', '231'])).
% 1.18/1.37  thf('233', plain, (~ (v2_struct_0 @ sk_C)),
% 1.18/1.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.37  thf('234', plain, ((r1_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_F)),
% 1.18/1.37      inference('clc', [status(thm)], ['232', '233'])).
% 1.18/1.37  thf('235', plain,
% 1.18/1.37      ((m1_subset_1 @ sk_E @ 
% 1.18/1.37        (k1_zfmisc_1 @ 
% 1.18/1.37         (k2_zfmisc_1 @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 1.18/1.37      inference('demod', [status(thm)], ['114', '115'])).
% 1.18/1.37  thf('236', plain,
% 1.18/1.37      (![X7 : $i]:
% 1.18/1.37         (((k2_struct_0 @ X7) = (u1_struct_0 @ X7)) | ~ (l1_struct_0 @ X7))),
% 1.18/1.37      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.18/1.37  thf('237', plain,
% 1.18/1.37      (![X40 : $i, X41 : $i, X42 : $i, X43 : $i, X44 : $i, X45 : $i]:
% 1.18/1.37         ((v2_struct_0 @ X40)
% 1.18/1.37          | ~ (v2_pre_topc @ X40)
% 1.18/1.37          | ~ (l1_pre_topc @ X40)
% 1.18/1.37          | (v2_struct_0 @ X41)
% 1.18/1.37          | ~ (v1_tsep_1 @ X41 @ X40)
% 1.18/1.37          | ~ (m1_pre_topc @ X41 @ X40)
% 1.18/1.37          | ~ (m1_subset_1 @ X42 @ (u1_struct_0 @ X41))
% 1.18/1.37          | ~ (r1_tmap_1 @ X40 @ X43 @ X44 @ X45)
% 1.18/1.37          | (r1_tmap_1 @ X41 @ X43 @ (k2_tmap_1 @ X40 @ X43 @ X44 @ X41) @ X42)
% 1.18/1.37          | ((X45) != (X42))
% 1.18/1.37          | ~ (m1_subset_1 @ X45 @ (u1_struct_0 @ X40))
% 1.18/1.37          | ~ (m1_subset_1 @ X44 @ 
% 1.18/1.37               (k1_zfmisc_1 @ 
% 1.18/1.37                (k2_zfmisc_1 @ (u1_struct_0 @ X40) @ (u1_struct_0 @ X43))))
% 1.18/1.37          | ~ (v1_funct_2 @ X44 @ (u1_struct_0 @ X40) @ (u1_struct_0 @ X43))
% 1.18/1.37          | ~ (v1_funct_1 @ X44)
% 1.18/1.37          | ~ (l1_pre_topc @ X43)
% 1.18/1.37          | ~ (v2_pre_topc @ X43)
% 1.18/1.37          | (v2_struct_0 @ X43))),
% 1.18/1.37      inference('cnf', [status(esa)], [t67_tmap_1])).
% 1.18/1.37  thf('238', plain,
% 1.18/1.37      (![X40 : $i, X41 : $i, X42 : $i, X43 : $i, X44 : $i]:
% 1.18/1.37         ((v2_struct_0 @ X43)
% 1.18/1.37          | ~ (v2_pre_topc @ X43)
% 1.18/1.37          | ~ (l1_pre_topc @ X43)
% 1.18/1.37          | ~ (v1_funct_1 @ X44)
% 1.18/1.37          | ~ (v1_funct_2 @ X44 @ (u1_struct_0 @ X40) @ (u1_struct_0 @ X43))
% 1.18/1.37          | ~ (m1_subset_1 @ X44 @ 
% 1.18/1.37               (k1_zfmisc_1 @ 
% 1.18/1.37                (k2_zfmisc_1 @ (u1_struct_0 @ X40) @ (u1_struct_0 @ X43))))
% 1.18/1.37          | ~ (m1_subset_1 @ X42 @ (u1_struct_0 @ X40))
% 1.18/1.37          | (r1_tmap_1 @ X41 @ X43 @ (k2_tmap_1 @ X40 @ X43 @ X44 @ X41) @ X42)
% 1.18/1.37          | ~ (r1_tmap_1 @ X40 @ X43 @ X44 @ X42)
% 1.18/1.37          | ~ (m1_subset_1 @ X42 @ (u1_struct_0 @ X41))
% 1.18/1.37          | ~ (m1_pre_topc @ X41 @ X40)
% 1.18/1.37          | ~ (v1_tsep_1 @ X41 @ X40)
% 1.18/1.37          | (v2_struct_0 @ X41)
% 1.18/1.37          | ~ (l1_pre_topc @ X40)
% 1.18/1.37          | ~ (v2_pre_topc @ X40)
% 1.18/1.37          | (v2_struct_0 @ X40))),
% 1.18/1.37      inference('simplify', [status(thm)], ['237'])).
% 1.18/1.37  thf('239', plain,
% 1.18/1.37      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 1.18/1.37         (~ (m1_subset_1 @ X2 @ 
% 1.18/1.37             (k1_zfmisc_1 @ 
% 1.18/1.37              (k2_zfmisc_1 @ (k2_struct_0 @ X0) @ (u1_struct_0 @ X1))))
% 1.18/1.37          | ~ (l1_struct_0 @ X0)
% 1.18/1.37          | (v2_struct_0 @ X0)
% 1.18/1.37          | ~ (v2_pre_topc @ X0)
% 1.18/1.37          | ~ (l1_pre_topc @ X0)
% 1.18/1.37          | (v2_struct_0 @ X3)
% 1.18/1.37          | ~ (v1_tsep_1 @ X3 @ X0)
% 1.18/1.37          | ~ (m1_pre_topc @ X3 @ X0)
% 1.18/1.37          | ~ (m1_subset_1 @ X4 @ (u1_struct_0 @ X3))
% 1.18/1.37          | ~ (r1_tmap_1 @ X0 @ X1 @ X2 @ X4)
% 1.18/1.37          | (r1_tmap_1 @ X3 @ X1 @ (k2_tmap_1 @ X0 @ X1 @ X2 @ X3) @ X4)
% 1.18/1.37          | ~ (m1_subset_1 @ X4 @ (u1_struct_0 @ X0))
% 1.18/1.37          | ~ (v1_funct_2 @ X2 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X1))
% 1.18/1.37          | ~ (v1_funct_1 @ X2)
% 1.18/1.37          | ~ (l1_pre_topc @ X1)
% 1.18/1.37          | ~ (v2_pre_topc @ X1)
% 1.18/1.37          | (v2_struct_0 @ X1))),
% 1.18/1.37      inference('sup-', [status(thm)], ['236', '238'])).
% 1.18/1.37  thf('240', plain,
% 1.18/1.37      (![X0 : $i, X1 : $i]:
% 1.18/1.37         ((v2_struct_0 @ sk_B)
% 1.18/1.37          | ~ (v2_pre_topc @ sk_B)
% 1.18/1.37          | ~ (l1_pre_topc @ sk_B)
% 1.18/1.37          | ~ (v1_funct_1 @ sk_E)
% 1.18/1.37          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))
% 1.18/1.37          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_C))
% 1.18/1.37          | (r1_tmap_1 @ X1 @ sk_B @ (k2_tmap_1 @ sk_C @ sk_B @ sk_E @ X1) @ X0)
% 1.18/1.37          | ~ (r1_tmap_1 @ sk_C @ sk_B @ sk_E @ X0)
% 1.18/1.37          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ X1))
% 1.18/1.37          | ~ (m1_pre_topc @ X1 @ sk_C)
% 1.18/1.37          | ~ (v1_tsep_1 @ X1 @ sk_C)
% 1.18/1.37          | (v2_struct_0 @ X1)
% 1.18/1.37          | ~ (l1_pre_topc @ sk_C)
% 1.18/1.37          | ~ (v2_pre_topc @ sk_C)
% 1.18/1.37          | (v2_struct_0 @ sk_C)
% 1.18/1.37          | ~ (l1_struct_0 @ sk_C))),
% 1.18/1.37      inference('sup-', [status(thm)], ['235', '239'])).
% 1.18/1.37  thf('241', plain, ((v2_pre_topc @ sk_B)),
% 1.18/1.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.37  thf('242', plain, ((l1_pre_topc @ sk_B)),
% 1.18/1.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.37  thf('243', plain, ((v1_funct_1 @ sk_E)),
% 1.18/1.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.37  thf('244', plain, (((u1_struct_0 @ sk_C) = (k2_struct_0 @ sk_C))),
% 1.18/1.37      inference('demod', [status(thm)], ['88', '89'])).
% 1.18/1.37  thf('245', plain,
% 1.18/1.37      ((v1_funct_2 @ sk_E @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 1.18/1.37      inference('demod', [status(thm)], ['127', '128'])).
% 1.18/1.37  thf('246', plain, (((u1_struct_0 @ sk_C) = (k2_struct_0 @ sk_C))),
% 1.18/1.37      inference('demod', [status(thm)], ['88', '89'])).
% 1.18/1.37  thf('247', plain, ((l1_pre_topc @ sk_C)),
% 1.18/1.37      inference('demod', [status(thm)], ['7', '8'])).
% 1.18/1.37  thf('248', plain, ((v2_pre_topc @ sk_C)),
% 1.18/1.37      inference('demod', [status(thm)], ['134', '135', '136'])).
% 1.18/1.37  thf('249', plain, ((l1_struct_0 @ sk_C)),
% 1.18/1.37      inference('sup-', [status(thm)], ['63', '64'])).
% 1.18/1.37  thf('250', plain,
% 1.18/1.37      (![X0 : $i, X1 : $i]:
% 1.18/1.37         ((v2_struct_0 @ sk_B)
% 1.18/1.37          | ~ (m1_subset_1 @ X0 @ (k2_struct_0 @ sk_C))
% 1.18/1.37          | (r1_tmap_1 @ X1 @ sk_B @ (k2_tmap_1 @ sk_C @ sk_B @ sk_E @ X1) @ X0)
% 1.18/1.37          | ~ (r1_tmap_1 @ sk_C @ sk_B @ sk_E @ X0)
% 1.18/1.37          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ X1))
% 1.18/1.37          | ~ (m1_pre_topc @ X1 @ sk_C)
% 1.18/1.37          | ~ (v1_tsep_1 @ X1 @ sk_C)
% 1.18/1.37          | (v2_struct_0 @ X1)
% 1.18/1.37          | (v2_struct_0 @ sk_C))),
% 1.18/1.37      inference('demod', [status(thm)],
% 1.18/1.37                ['240', '241', '242', '243', '244', '245', '246', '247', 
% 1.18/1.37                 '248', '249'])).
% 1.18/1.37  thf('251', plain,
% 1.18/1.37      (![X0 : $i]:
% 1.18/1.37         ((v2_struct_0 @ sk_C)
% 1.18/1.37          | (v2_struct_0 @ X0)
% 1.18/1.37          | ~ (v1_tsep_1 @ X0 @ sk_C)
% 1.18/1.37          | ~ (m1_pre_topc @ X0 @ sk_C)
% 1.18/1.37          | ~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ X0))
% 1.18/1.37          | (r1_tmap_1 @ X0 @ sk_B @ (k2_tmap_1 @ sk_C @ sk_B @ sk_E @ X0) @ 
% 1.18/1.37             sk_F)
% 1.18/1.37          | ~ (m1_subset_1 @ sk_F @ (k2_struct_0 @ sk_C))
% 1.18/1.37          | (v2_struct_0 @ sk_B))),
% 1.18/1.37      inference('sup-', [status(thm)], ['234', '250'])).
% 1.18/1.37  thf('252', plain, ((m1_subset_1 @ sk_F @ (k2_struct_0 @ sk_C))),
% 1.18/1.37      inference('demod', [status(thm)], ['225', '226'])).
% 1.18/1.37  thf('253', plain,
% 1.18/1.37      (![X0 : $i]:
% 1.18/1.37         ((v2_struct_0 @ sk_C)
% 1.18/1.37          | (v2_struct_0 @ X0)
% 1.18/1.37          | ~ (v1_tsep_1 @ X0 @ sk_C)
% 1.18/1.37          | ~ (m1_pre_topc @ X0 @ sk_C)
% 1.18/1.37          | ~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ X0))
% 1.18/1.37          | (r1_tmap_1 @ X0 @ sk_B @ (k2_tmap_1 @ sk_C @ sk_B @ sk_E @ X0) @ 
% 1.18/1.37             sk_F)
% 1.18/1.37          | (v2_struct_0 @ sk_B))),
% 1.18/1.37      inference('demod', [status(thm)], ['251', '252'])).
% 1.18/1.37  thf('254', plain,
% 1.18/1.37      ((~ (m1_subset_1 @ sk_F @ (k2_struct_0 @ sk_C))
% 1.18/1.37        | (v2_struct_0 @ sk_B)
% 1.18/1.37        | (r1_tmap_1 @ sk_D @ sk_B @ (k2_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_D) @ 
% 1.18/1.37           sk_F)
% 1.18/1.37        | ~ (m1_pre_topc @ sk_D @ sk_C)
% 1.18/1.37        | ~ (v1_tsep_1 @ sk_D @ sk_C)
% 1.18/1.37        | (v2_struct_0 @ sk_D)
% 1.18/1.37        | (v2_struct_0 @ sk_C))),
% 1.18/1.37      inference('sup-', [status(thm)], ['67', '253'])).
% 1.18/1.37  thf('255', plain, ((m1_subset_1 @ sk_F @ (k2_struct_0 @ sk_C))),
% 1.18/1.37      inference('demod', [status(thm)], ['225', '226'])).
% 1.18/1.37  thf('256', plain, ((m1_pre_topc @ sk_D @ sk_C)),
% 1.18/1.37      inference('demod', [status(thm)], ['11', '16'])).
% 1.18/1.37  thf('257', plain,
% 1.18/1.37      (![X0 : $i]:
% 1.18/1.37         ((v2_struct_0 @ sk_B)
% 1.18/1.37          | ~ (m1_pre_topc @ X0 @ sk_C)
% 1.18/1.37          | ((k2_tmap_1 @ sk_C @ sk_B @ sk_E @ X0)
% 1.18/1.37              = (k2_partfun1 @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.18/1.37                 sk_E @ (u1_struct_0 @ X0)))
% 1.18/1.37          | (v2_struct_0 @ sk_C))),
% 1.18/1.37      inference('demod', [status(thm)],
% 1.18/1.37                ['120', '121', '122', '123', '124', '129', '130', '131', 
% 1.18/1.37                 '137', '138'])).
% 1.18/1.37  thf('258', plain,
% 1.18/1.37      (((v2_struct_0 @ sk_C)
% 1.18/1.37        | ((k2_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_D)
% 1.18/1.37            = (k2_partfun1 @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.18/1.37               sk_E @ (u1_struct_0 @ sk_D)))
% 1.18/1.37        | (v2_struct_0 @ sk_B))),
% 1.18/1.37      inference('sup-', [status(thm)], ['256', '257'])).
% 1.18/1.37  thf('259', plain, (((k2_struct_0 @ sk_C) = (u1_struct_0 @ sk_D))),
% 1.18/1.37      inference('demod', [status(thm)], ['59', '66'])).
% 1.18/1.37  thf('260', plain,
% 1.18/1.37      (((v2_struct_0 @ sk_C)
% 1.18/1.37        | ((k2_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_D)
% 1.18/1.37            = (k2_partfun1 @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.18/1.37               sk_E @ (k2_struct_0 @ sk_C)))
% 1.18/1.37        | (v2_struct_0 @ sk_B))),
% 1.18/1.37      inference('demod', [status(thm)], ['258', '259'])).
% 1.18/1.37  thf('261', plain, (~ (v2_struct_0 @ sk_C)),
% 1.18/1.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.37  thf('262', plain,
% 1.18/1.37      (((v2_struct_0 @ sk_B)
% 1.18/1.37        | ((k2_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_D)
% 1.18/1.37            = (k2_partfun1 @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.18/1.37               sk_E @ (k2_struct_0 @ sk_C))))),
% 1.18/1.37      inference('clc', [status(thm)], ['260', '261'])).
% 1.18/1.37  thf('263', plain, (~ (v2_struct_0 @ sk_B)),
% 1.18/1.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.37  thf('264', plain,
% 1.18/1.37      (((k2_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_D)
% 1.18/1.37         = (k2_partfun1 @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_E @ 
% 1.18/1.37            (k2_struct_0 @ sk_C)))),
% 1.18/1.37      inference('clc', [status(thm)], ['262', '263'])).
% 1.18/1.37  thf('265', plain,
% 1.18/1.37      (((k2_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_C)
% 1.18/1.37         = (k2_partfun1 @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_E @ 
% 1.18/1.37            (k2_struct_0 @ sk_C)))),
% 1.18/1.37      inference('demod', [status(thm)], ['110', '148'])).
% 1.18/1.37  thf('266', plain,
% 1.18/1.37      (((k2_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_C)
% 1.18/1.37         = (k2_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_D))),
% 1.18/1.37      inference('sup+', [status(thm)], ['264', '265'])).
% 1.18/1.37  thf('267', plain, ((m1_pre_topc @ sk_D @ sk_C)),
% 1.18/1.37      inference('demod', [status(thm)], ['11', '16'])).
% 1.18/1.37  thf('268', plain, ((m1_pre_topc @ sk_D @ sk_C)),
% 1.18/1.37      inference('demod', [status(thm)], ['11', '16'])).
% 1.18/1.37  thf(t1_tsep_1, axiom,
% 1.18/1.37    (![A:$i]:
% 1.18/1.37     ( ( l1_pre_topc @ A ) =>
% 1.18/1.37       ( ![B:$i]:
% 1.18/1.37         ( ( m1_pre_topc @ B @ A ) =>
% 1.18/1.37           ( m1_subset_1 @
% 1.18/1.37             ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 1.18/1.37  thf('269', plain,
% 1.18/1.37      (![X34 : $i, X35 : $i]:
% 1.18/1.37         (~ (m1_pre_topc @ X34 @ X35)
% 1.18/1.37          | (m1_subset_1 @ (u1_struct_0 @ X34) @ 
% 1.18/1.37             (k1_zfmisc_1 @ (u1_struct_0 @ X35)))
% 1.18/1.37          | ~ (l1_pre_topc @ X35))),
% 1.18/1.37      inference('cnf', [status(esa)], [t1_tsep_1])).
% 1.18/1.37  thf('270', plain,
% 1.18/1.37      ((~ (l1_pre_topc @ sk_C)
% 1.18/1.37        | (m1_subset_1 @ (u1_struct_0 @ sk_D) @ 
% 1.18/1.37           (k1_zfmisc_1 @ (u1_struct_0 @ sk_C))))),
% 1.18/1.37      inference('sup-', [status(thm)], ['268', '269'])).
% 1.18/1.37  thf('271', plain, ((l1_pre_topc @ sk_C)),
% 1.18/1.37      inference('demod', [status(thm)], ['7', '8'])).
% 1.18/1.37  thf('272', plain,
% 1.18/1.37      ((m1_subset_1 @ (u1_struct_0 @ sk_D) @ 
% 1.18/1.37        (k1_zfmisc_1 @ (u1_struct_0 @ sk_C)))),
% 1.18/1.37      inference('demod', [status(thm)], ['270', '271'])).
% 1.18/1.37  thf('273', plain,
% 1.18/1.37      (![X31 : $i, X32 : $i]:
% 1.18/1.37         (~ (v2_pre_topc @ X32)
% 1.18/1.37          | ~ (l1_pre_topc @ X32)
% 1.18/1.37          | ~ (m1_subset_1 @ (u1_struct_0 @ X31) @ 
% 1.18/1.37               (k1_zfmisc_1 @ (u1_struct_0 @ X32)))
% 1.18/1.37          | (v1_tsep_1 @ X31 @ X32)
% 1.18/1.37          | ~ (v3_pre_topc @ (u1_struct_0 @ X31) @ X32)
% 1.18/1.37          | ~ (m1_pre_topc @ X31 @ X32))),
% 1.18/1.37      inference('simplify', [status(thm)], ['209'])).
% 1.18/1.37  thf('274', plain,
% 1.18/1.37      ((~ (m1_pre_topc @ sk_D @ sk_C)
% 1.18/1.37        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_D) @ sk_C)
% 1.18/1.37        | (v1_tsep_1 @ sk_D @ sk_C)
% 1.18/1.37        | ~ (l1_pre_topc @ sk_C)
% 1.18/1.37        | ~ (v2_pre_topc @ sk_C))),
% 1.18/1.37      inference('sup-', [status(thm)], ['272', '273'])).
% 1.18/1.37  thf('275', plain, ((m1_pre_topc @ sk_D @ sk_C)),
% 1.18/1.37      inference('demod', [status(thm)], ['11', '16'])).
% 1.18/1.37  thf('276', plain,
% 1.18/1.37      (![X21 : $i]:
% 1.18/1.37         ((v3_pre_topc @ (k2_struct_0 @ X21) @ X21)
% 1.18/1.37          | ~ (l1_pre_topc @ X21)
% 1.18/1.37          | ~ (v2_pre_topc @ X21))),
% 1.18/1.37      inference('cnf', [status(esa)], [fc10_tops_1])).
% 1.18/1.37  thf('277', plain,
% 1.18/1.37      (![X7 : $i]:
% 1.18/1.37         (((k2_struct_0 @ X7) = (u1_struct_0 @ X7)) | ~ (l1_struct_0 @ X7))),
% 1.18/1.37      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.18/1.37  thf('278', plain,
% 1.18/1.37      (((g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) = (sk_D))),
% 1.18/1.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.37  thf('279', plain, (![X4 : $i]: (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X4))),
% 1.18/1.37      inference('demod', [status(thm)], ['177', '178'])).
% 1.18/1.37  thf('280', plain,
% 1.18/1.37      (![X16 : $i, X17 : $i]:
% 1.18/1.37         (~ (v3_pre_topc @ X16 @ 
% 1.18/1.37             (g1_pre_topc @ (u1_struct_0 @ X17) @ (u1_pre_topc @ X17)))
% 1.18/1.37          | ~ (m1_subset_1 @ X16 @ 
% 1.18/1.37               (k1_zfmisc_1 @ 
% 1.18/1.37                (u1_struct_0 @ 
% 1.18/1.37                 (g1_pre_topc @ (u1_struct_0 @ X17) @ (u1_pre_topc @ X17)))))
% 1.18/1.37          | (v3_pre_topc @ X16 @ X17)
% 1.18/1.37          | ~ (l1_pre_topc @ X17)
% 1.18/1.37          | ~ (v2_pre_topc @ X17))),
% 1.18/1.37      inference('cnf', [status(esa)], [t60_pre_topc])).
% 1.18/1.37  thf('281', plain,
% 1.18/1.37      (![X0 : $i]:
% 1.18/1.37         (~ (v2_pre_topc @ X0)
% 1.18/1.37          | ~ (l1_pre_topc @ X0)
% 1.18/1.37          | (v3_pre_topc @ 
% 1.18/1.37             (u1_struct_0 @ 
% 1.18/1.37              (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))) @ 
% 1.18/1.37             X0)
% 1.18/1.37          | ~ (v3_pre_topc @ 
% 1.18/1.37               (u1_struct_0 @ 
% 1.18/1.37                (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))) @ 
% 1.18/1.37               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 1.18/1.37      inference('sup-', [status(thm)], ['279', '280'])).
% 1.18/1.37  thf('282', plain,
% 1.18/1.37      ((~ (v3_pre_topc @ (u1_struct_0 @ sk_D) @ 
% 1.18/1.37           (g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)))
% 1.18/1.37        | (v3_pre_topc @ 
% 1.18/1.37           (u1_struct_0 @ 
% 1.18/1.37            (g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C))) @ 
% 1.18/1.37           sk_C)
% 1.18/1.37        | ~ (l1_pre_topc @ sk_C)
% 1.18/1.37        | ~ (v2_pre_topc @ sk_C))),
% 1.18/1.37      inference('sup-', [status(thm)], ['278', '281'])).
% 1.18/1.37  thf('283', plain,
% 1.18/1.37      (((g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) = (sk_D))),
% 1.18/1.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.37  thf('284', plain,
% 1.18/1.37      (((g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) = (sk_D))),
% 1.18/1.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.37  thf('285', plain, ((l1_pre_topc @ sk_C)),
% 1.18/1.37      inference('demod', [status(thm)], ['7', '8'])).
% 1.18/1.37  thf('286', plain, ((v2_pre_topc @ sk_C)),
% 1.18/1.37      inference('demod', [status(thm)], ['134', '135', '136'])).
% 1.18/1.37  thf('287', plain,
% 1.18/1.37      ((~ (v3_pre_topc @ (u1_struct_0 @ sk_D) @ sk_D)
% 1.18/1.37        | (v3_pre_topc @ (u1_struct_0 @ sk_D) @ sk_C))),
% 1.18/1.37      inference('demod', [status(thm)], ['282', '283', '284', '285', '286'])).
% 1.18/1.37  thf('288', plain,
% 1.18/1.37      ((~ (v3_pre_topc @ (k2_struct_0 @ sk_D) @ sk_D)
% 1.18/1.37        | ~ (l1_struct_0 @ sk_D)
% 1.18/1.37        | (v3_pre_topc @ (u1_struct_0 @ sk_D) @ sk_C))),
% 1.18/1.37      inference('sup-', [status(thm)], ['277', '287'])).
% 1.18/1.37  thf('289', plain, ((l1_struct_0 @ sk_D)),
% 1.18/1.37      inference('sup-', [status(thm)], ['55', '56'])).
% 1.18/1.37  thf('290', plain,
% 1.18/1.37      ((~ (v3_pre_topc @ (k2_struct_0 @ sk_D) @ sk_D)
% 1.18/1.37        | (v3_pre_topc @ (u1_struct_0 @ sk_D) @ sk_C))),
% 1.18/1.37      inference('demod', [status(thm)], ['288', '289'])).
% 1.18/1.37  thf('291', plain,
% 1.18/1.37      ((~ (v2_pre_topc @ sk_D)
% 1.18/1.37        | ~ (l1_pre_topc @ sk_D)
% 1.18/1.37        | (v3_pre_topc @ (u1_struct_0 @ sk_D) @ sk_C))),
% 1.18/1.37      inference('sup-', [status(thm)], ['276', '290'])).
% 1.18/1.37  thf('292', plain, ((v2_pre_topc @ sk_D)),
% 1.18/1.37      inference('demod', [status(thm)], ['26', '27', '28'])).
% 1.18/1.37  thf('293', plain, ((l1_pre_topc @ sk_D)),
% 1.18/1.37      inference('demod', [status(thm)], ['14', '15'])).
% 1.18/1.37  thf('294', plain, ((v3_pre_topc @ (u1_struct_0 @ sk_D) @ sk_C)),
% 1.18/1.37      inference('demod', [status(thm)], ['291', '292', '293'])).
% 1.18/1.37  thf('295', plain, ((l1_pre_topc @ sk_C)),
% 1.18/1.37      inference('demod', [status(thm)], ['7', '8'])).
% 1.18/1.37  thf('296', plain, ((v2_pre_topc @ sk_C)),
% 1.18/1.37      inference('demod', [status(thm)], ['134', '135', '136'])).
% 1.18/1.37  thf('297', plain, ((v1_tsep_1 @ sk_D @ sk_C)),
% 1.18/1.37      inference('demod', [status(thm)], ['274', '275', '294', '295', '296'])).
% 1.18/1.37  thf('298', plain,
% 1.18/1.37      (((v2_struct_0 @ sk_B)
% 1.18/1.37        | (r1_tmap_1 @ sk_D @ sk_B @ (k2_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_C) @ 
% 1.18/1.37           sk_F)
% 1.18/1.37        | (v2_struct_0 @ sk_D)
% 1.18/1.37        | (v2_struct_0 @ sk_C))),
% 1.18/1.37      inference('demod', [status(thm)], ['254', '255', '266', '267', '297'])).
% 1.18/1.37  thf('299', plain,
% 1.18/1.37      (((k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C)
% 1.18/1.37         = (k2_partfun1 @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_E @ 
% 1.18/1.37            (k2_struct_0 @ sk_C)))),
% 1.18/1.37      inference('clc', [status(thm)], ['108', '109'])).
% 1.18/1.37  thf('300', plain,
% 1.18/1.37      (![X36 : $i]: ((m1_pre_topc @ X36 @ X36) | ~ (l1_pre_topc @ X36))),
% 1.18/1.37      inference('cnf', [status(esa)], [t2_tsep_1])).
% 1.18/1.37  thf('301', plain,
% 1.18/1.37      (![X0 : $i]:
% 1.18/1.37         ((v2_struct_0 @ sk_D)
% 1.18/1.37          | ((k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0)
% 1.18/1.37              = (k2_partfun1 @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.18/1.37                 sk_E @ (u1_struct_0 @ X0)))
% 1.18/1.37          | ~ (m1_pre_topc @ X0 @ sk_D)
% 1.18/1.37          | (v2_struct_0 @ sk_B))),
% 1.18/1.37      inference('demod', [status(thm)], ['101', '102'])).
% 1.18/1.37  thf('302', plain,
% 1.18/1.37      ((~ (l1_pre_topc @ sk_D)
% 1.18/1.37        | (v2_struct_0 @ sk_B)
% 1.18/1.37        | ((k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_D)
% 1.18/1.37            = (k2_partfun1 @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.18/1.37               sk_E @ (u1_struct_0 @ sk_D)))
% 1.18/1.37        | (v2_struct_0 @ sk_D))),
% 1.18/1.37      inference('sup-', [status(thm)], ['300', '301'])).
% 1.18/1.37  thf('303', plain, ((l1_pre_topc @ sk_D)),
% 1.18/1.37      inference('demod', [status(thm)], ['14', '15'])).
% 1.18/1.37  thf('304', plain, (((k2_struct_0 @ sk_C) = (u1_struct_0 @ sk_D))),
% 1.18/1.37      inference('demod', [status(thm)], ['59', '66'])).
% 1.18/1.37  thf('305', plain,
% 1.18/1.37      (((v2_struct_0 @ sk_B)
% 1.18/1.37        | ((k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_D)
% 1.18/1.37            = (k2_partfun1 @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.18/1.37               sk_E @ (k2_struct_0 @ sk_C)))
% 1.18/1.37        | (v2_struct_0 @ sk_D))),
% 1.18/1.37      inference('demod', [status(thm)], ['302', '303', '304'])).
% 1.18/1.37  thf('306', plain, (~ (v2_struct_0 @ sk_B)),
% 1.18/1.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.37  thf('307', plain,
% 1.18/1.37      (((v2_struct_0 @ sk_D)
% 1.18/1.37        | ((k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_D)
% 1.18/1.37            = (k2_partfun1 @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.18/1.37               sk_E @ (k2_struct_0 @ sk_C))))),
% 1.18/1.37      inference('clc', [status(thm)], ['305', '306'])).
% 1.18/1.37  thf('308', plain, (~ (v2_struct_0 @ sk_D)),
% 1.18/1.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.37  thf('309', plain,
% 1.18/1.37      (((k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_D)
% 1.18/1.37         = (k2_partfun1 @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_E @ 
% 1.18/1.37            (k2_struct_0 @ sk_C)))),
% 1.18/1.37      inference('clc', [status(thm)], ['307', '308'])).
% 1.18/1.37  thf('310', plain,
% 1.18/1.37      (((k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_D)
% 1.18/1.37         = (k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C))),
% 1.18/1.37      inference('sup+', [status(thm)], ['299', '309'])).
% 1.18/1.37  thf('311', plain,
% 1.18/1.37      (((k2_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_C)
% 1.18/1.37         = (k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C))),
% 1.18/1.37      inference('clc', [status(thm)], ['146', '147'])).
% 1.18/1.37  thf('312', plain,
% 1.18/1.37      (((k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_D)
% 1.18/1.37         = (k2_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_C))),
% 1.18/1.37      inference('demod', [status(thm)], ['310', '311'])).
% 1.18/1.37  thf('313', plain,
% 1.18/1.37      ((m1_subset_1 @ sk_E @ 
% 1.18/1.37        (k1_zfmisc_1 @ 
% 1.18/1.37         (k2_zfmisc_1 @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 1.18/1.37      inference('demod', [status(thm)], ['114', '115'])).
% 1.18/1.37  thf('314', plain, (((k2_struct_0 @ sk_C) = (u1_struct_0 @ sk_D))),
% 1.18/1.37      inference('demod', [status(thm)], ['59', '66'])).
% 1.18/1.37  thf('315', plain,
% 1.18/1.37      (![X40 : $i, X41 : $i, X42 : $i, X43 : $i, X44 : $i]:
% 1.18/1.37         ((v2_struct_0 @ X43)
% 1.18/1.37          | ~ (v2_pre_topc @ X43)
% 1.18/1.37          | ~ (l1_pre_topc @ X43)
% 1.18/1.37          | ~ (v1_funct_1 @ X44)
% 1.18/1.37          | ~ (v1_funct_2 @ X44 @ (u1_struct_0 @ X40) @ (u1_struct_0 @ X43))
% 1.18/1.37          | ~ (m1_subset_1 @ X44 @ 
% 1.18/1.37               (k1_zfmisc_1 @ 
% 1.18/1.37                (k2_zfmisc_1 @ (u1_struct_0 @ X40) @ (u1_struct_0 @ X43))))
% 1.18/1.37          | ~ (m1_subset_1 @ X42 @ (u1_struct_0 @ X40))
% 1.18/1.37          | (r1_tmap_1 @ X40 @ X43 @ X44 @ X42)
% 1.18/1.37          | ~ (r1_tmap_1 @ X41 @ X43 @ (k2_tmap_1 @ X40 @ X43 @ X44 @ X41) @ 
% 1.18/1.37               X42)
% 1.18/1.37          | ~ (m1_subset_1 @ X42 @ (u1_struct_0 @ X41))
% 1.18/1.37          | ~ (m1_pre_topc @ X41 @ X40)
% 1.18/1.37          | ~ (v1_tsep_1 @ X41 @ X40)
% 1.18/1.37          | (v2_struct_0 @ X41)
% 1.18/1.37          | ~ (l1_pre_topc @ X40)
% 1.18/1.37          | ~ (v2_pre_topc @ X40)
% 1.18/1.37          | (v2_struct_0 @ X40))),
% 1.18/1.37      inference('simplify', [status(thm)], ['159'])).
% 1.18/1.37  thf('316', plain,
% 1.18/1.37      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.18/1.37         (~ (m1_subset_1 @ X1 @ 
% 1.18/1.37             (k1_zfmisc_1 @ 
% 1.18/1.37              (k2_zfmisc_1 @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ X0))))
% 1.18/1.37          | (v2_struct_0 @ sk_D)
% 1.18/1.37          | ~ (v2_pre_topc @ sk_D)
% 1.18/1.37          | ~ (l1_pre_topc @ sk_D)
% 1.18/1.37          | (v2_struct_0 @ X2)
% 1.18/1.37          | ~ (v1_tsep_1 @ X2 @ sk_D)
% 1.18/1.37          | ~ (m1_pre_topc @ X2 @ sk_D)
% 1.18/1.37          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X2))
% 1.18/1.37          | ~ (r1_tmap_1 @ X2 @ X0 @ (k2_tmap_1 @ sk_D @ X0 @ X1 @ X2) @ X3)
% 1.18/1.37          | (r1_tmap_1 @ sk_D @ X0 @ X1 @ X3)
% 1.18/1.37          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ sk_D))
% 1.18/1.37          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ X0))
% 1.18/1.37          | ~ (v1_funct_1 @ X1)
% 1.18/1.37          | ~ (l1_pre_topc @ X0)
% 1.18/1.37          | ~ (v2_pre_topc @ X0)
% 1.18/1.37          | (v2_struct_0 @ X0))),
% 1.18/1.37      inference('sup-', [status(thm)], ['314', '315'])).
% 1.18/1.37  thf('317', plain, ((v2_pre_topc @ sk_D)),
% 1.18/1.37      inference('demod', [status(thm)], ['26', '27', '28'])).
% 1.18/1.37  thf('318', plain, ((l1_pre_topc @ sk_D)),
% 1.18/1.37      inference('demod', [status(thm)], ['14', '15'])).
% 1.18/1.37  thf('319', plain, (((k2_struct_0 @ sk_C) = (u1_struct_0 @ sk_D))),
% 1.18/1.37      inference('demod', [status(thm)], ['59', '66'])).
% 1.18/1.37  thf('320', plain, (((k2_struct_0 @ sk_C) = (u1_struct_0 @ sk_D))),
% 1.18/1.37      inference('demod', [status(thm)], ['59', '66'])).
% 1.18/1.37  thf('321', plain,
% 1.18/1.37      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.18/1.37         (~ (m1_subset_1 @ X1 @ 
% 1.18/1.37             (k1_zfmisc_1 @ 
% 1.18/1.37              (k2_zfmisc_1 @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ X0))))
% 1.18/1.37          | (v2_struct_0 @ sk_D)
% 1.18/1.37          | (v2_struct_0 @ X2)
% 1.18/1.37          | ~ (v1_tsep_1 @ X2 @ sk_D)
% 1.18/1.37          | ~ (m1_pre_topc @ X2 @ sk_D)
% 1.18/1.37          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X2))
% 1.18/1.37          | ~ (r1_tmap_1 @ X2 @ X0 @ (k2_tmap_1 @ sk_D @ X0 @ X1 @ X2) @ X3)
% 1.18/1.37          | (r1_tmap_1 @ sk_D @ X0 @ X1 @ X3)
% 1.18/1.37          | ~ (m1_subset_1 @ X3 @ (k2_struct_0 @ sk_C))
% 1.18/1.37          | ~ (v1_funct_2 @ X1 @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ X0))
% 1.18/1.37          | ~ (v1_funct_1 @ X1)
% 1.18/1.37          | ~ (l1_pre_topc @ X0)
% 1.18/1.37          | ~ (v2_pre_topc @ X0)
% 1.18/1.37          | (v2_struct_0 @ X0))),
% 1.18/1.37      inference('demod', [status(thm)], ['316', '317', '318', '319', '320'])).
% 1.18/1.37  thf('322', plain,
% 1.18/1.37      (![X0 : $i, X1 : $i]:
% 1.18/1.37         ((v2_struct_0 @ sk_B)
% 1.18/1.37          | ~ (v2_pre_topc @ sk_B)
% 1.18/1.37          | ~ (l1_pre_topc @ sk_B)
% 1.18/1.37          | ~ (v1_funct_1 @ sk_E)
% 1.18/1.37          | ~ (v1_funct_2 @ sk_E @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))
% 1.18/1.37          | ~ (m1_subset_1 @ X0 @ (k2_struct_0 @ sk_C))
% 1.18/1.37          | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X0)
% 1.18/1.37          | ~ (r1_tmap_1 @ X1 @ sk_B @ (k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X1) @ 
% 1.18/1.37               X0)
% 1.18/1.37          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ X1))
% 1.18/1.37          | ~ (m1_pre_topc @ X1 @ sk_D)
% 1.18/1.37          | ~ (v1_tsep_1 @ X1 @ sk_D)
% 1.18/1.37          | (v2_struct_0 @ X1)
% 1.18/1.37          | (v2_struct_0 @ sk_D))),
% 1.18/1.37      inference('sup-', [status(thm)], ['313', '321'])).
% 1.18/1.37  thf('323', plain, ((v2_pre_topc @ sk_B)),
% 1.18/1.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.37  thf('324', plain, ((l1_pre_topc @ sk_B)),
% 1.18/1.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.37  thf('325', plain, ((v1_funct_1 @ sk_E)),
% 1.18/1.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.37  thf('326', plain,
% 1.18/1.37      ((v1_funct_2 @ sk_E @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 1.18/1.37      inference('demod', [status(thm)], ['127', '128'])).
% 1.18/1.37  thf('327', plain,
% 1.18/1.37      (![X0 : $i, X1 : $i]:
% 1.18/1.37         ((v2_struct_0 @ sk_B)
% 1.18/1.37          | ~ (m1_subset_1 @ X0 @ (k2_struct_0 @ sk_C))
% 1.18/1.37          | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X0)
% 1.18/1.37          | ~ (r1_tmap_1 @ X1 @ sk_B @ (k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X1) @ 
% 1.18/1.37               X0)
% 1.18/1.37          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ X1))
% 1.18/1.37          | ~ (m1_pre_topc @ X1 @ sk_D)
% 1.18/1.37          | ~ (v1_tsep_1 @ X1 @ sk_D)
% 1.18/1.37          | (v2_struct_0 @ X1)
% 1.18/1.37          | (v2_struct_0 @ sk_D))),
% 1.18/1.37      inference('demod', [status(thm)], ['322', '323', '324', '325', '326'])).
% 1.18/1.37  thf('328', plain,
% 1.18/1.37      (![X0 : $i]:
% 1.18/1.37         (~ (r1_tmap_1 @ sk_D @ sk_B @ 
% 1.18/1.37             (k2_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_C) @ X0)
% 1.18/1.37          | (v2_struct_0 @ sk_D)
% 1.18/1.37          | (v2_struct_0 @ sk_D)
% 1.18/1.37          | ~ (v1_tsep_1 @ sk_D @ sk_D)
% 1.18/1.37          | ~ (m1_pre_topc @ sk_D @ sk_D)
% 1.18/1.37          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_D))
% 1.18/1.37          | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X0)
% 1.18/1.37          | ~ (m1_subset_1 @ X0 @ (k2_struct_0 @ sk_C))
% 1.18/1.37          | (v2_struct_0 @ sk_B))),
% 1.18/1.37      inference('sup-', [status(thm)], ['312', '327'])).
% 1.18/1.37  thf('329', plain,
% 1.18/1.37      ((m1_subset_1 @ (u1_struct_0 @ sk_D) @ 
% 1.18/1.37        (k1_zfmisc_1 @ (u1_struct_0 @ sk_C)))),
% 1.18/1.37      inference('demod', [status(thm)], ['270', '271'])).
% 1.18/1.37  thf('330', plain,
% 1.18/1.37      (![X17 : $i, X18 : $i]:
% 1.18/1.37         (~ (v3_pre_topc @ X18 @ X17)
% 1.18/1.37          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 1.18/1.37          | (v3_pre_topc @ X18 @ 
% 1.18/1.37             (g1_pre_topc @ (u1_struct_0 @ X17) @ (u1_pre_topc @ X17)))
% 1.18/1.37          | ~ (l1_pre_topc @ X17)
% 1.18/1.37          | ~ (v2_pre_topc @ X17))),
% 1.18/1.37      inference('cnf', [status(esa)], [t60_pre_topc])).
% 1.18/1.37  thf('331', plain,
% 1.18/1.37      ((~ (v2_pre_topc @ sk_C)
% 1.18/1.37        | ~ (l1_pre_topc @ sk_C)
% 1.18/1.37        | (v3_pre_topc @ (u1_struct_0 @ sk_D) @ 
% 1.18/1.37           (g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)))
% 1.18/1.37        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_D) @ sk_C))),
% 1.18/1.37      inference('sup-', [status(thm)], ['329', '330'])).
% 1.18/1.37  thf('332', plain, ((v2_pre_topc @ sk_C)),
% 1.18/1.37      inference('demod', [status(thm)], ['134', '135', '136'])).
% 1.18/1.37  thf('333', plain, ((l1_pre_topc @ sk_C)),
% 1.18/1.37      inference('demod', [status(thm)], ['7', '8'])).
% 1.18/1.37  thf('334', plain,
% 1.18/1.37      (((g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) = (sk_D))),
% 1.18/1.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.37  thf('335', plain, ((v3_pre_topc @ (u1_struct_0 @ sk_D) @ sk_C)),
% 1.18/1.37      inference('demod', [status(thm)], ['291', '292', '293'])).
% 1.18/1.37  thf('336', plain, ((v3_pre_topc @ (u1_struct_0 @ sk_D) @ sk_D)),
% 1.18/1.37      inference('demod', [status(thm)], ['331', '332', '333', '334', '335'])).
% 1.18/1.37  thf('337', plain,
% 1.18/1.37      (![X0 : $i]:
% 1.18/1.37         (~ (m1_pre_topc @ X0 @ X0)
% 1.18/1.37          | ~ (v3_pre_topc @ (u1_struct_0 @ X0) @ X0)
% 1.18/1.37          | (v1_tsep_1 @ X0 @ X0)
% 1.18/1.37          | ~ (l1_pre_topc @ X0)
% 1.18/1.37          | ~ (v2_pre_topc @ X0))),
% 1.18/1.37      inference('sup-', [status(thm)], ['208', '210'])).
% 1.18/1.37  thf('338', plain,
% 1.18/1.37      ((~ (v2_pre_topc @ sk_D)
% 1.18/1.37        | ~ (l1_pre_topc @ sk_D)
% 1.18/1.37        | (v1_tsep_1 @ sk_D @ sk_D)
% 1.18/1.37        | ~ (m1_pre_topc @ sk_D @ sk_D))),
% 1.18/1.37      inference('sup-', [status(thm)], ['336', '337'])).
% 1.18/1.37  thf('339', plain, ((v2_pre_topc @ sk_D)),
% 1.18/1.37      inference('demod', [status(thm)], ['26', '27', '28'])).
% 1.18/1.37  thf('340', plain, ((l1_pre_topc @ sk_D)),
% 1.18/1.37      inference('demod', [status(thm)], ['14', '15'])).
% 1.18/1.37  thf('341', plain, ((m1_pre_topc @ sk_D @ sk_C)),
% 1.18/1.37      inference('demod', [status(thm)], ['11', '16'])).
% 1.18/1.37  thf('342', plain,
% 1.18/1.37      (![X19 : $i, X20 : $i]:
% 1.18/1.37         (~ (l1_pre_topc @ X19)
% 1.18/1.37          | ~ (m1_pre_topc @ X20 @ X19)
% 1.18/1.37          | (m1_pre_topc @ X20 @ 
% 1.18/1.37             (g1_pre_topc @ (u1_struct_0 @ X19) @ (u1_pre_topc @ X19)))
% 1.18/1.37          | ~ (l1_pre_topc @ X20))),
% 1.18/1.37      inference('cnf', [status(esa)], [t65_pre_topc])).
% 1.18/1.37  thf('343', plain,
% 1.18/1.37      ((~ (l1_pre_topc @ sk_D)
% 1.18/1.37        | (m1_pre_topc @ sk_D @ 
% 1.18/1.37           (g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)))
% 1.18/1.37        | ~ (l1_pre_topc @ sk_C))),
% 1.18/1.37      inference('sup-', [status(thm)], ['341', '342'])).
% 1.18/1.37  thf('344', plain, ((l1_pre_topc @ sk_D)),
% 1.18/1.37      inference('demod', [status(thm)], ['14', '15'])).
% 1.18/1.37  thf('345', plain,
% 1.18/1.37      (((g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) = (sk_D))),
% 1.18/1.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.37  thf('346', plain, ((l1_pre_topc @ sk_C)),
% 1.18/1.37      inference('demod', [status(thm)], ['7', '8'])).
% 1.18/1.37  thf('347', plain, ((m1_pre_topc @ sk_D @ sk_D)),
% 1.18/1.37      inference('demod', [status(thm)], ['343', '344', '345', '346'])).
% 1.18/1.37  thf('348', plain, ((v1_tsep_1 @ sk_D @ sk_D)),
% 1.18/1.37      inference('demod', [status(thm)], ['338', '339', '340', '347'])).
% 1.18/1.37  thf('349', plain, ((m1_pre_topc @ sk_D @ sk_D)),
% 1.18/1.37      inference('demod', [status(thm)], ['343', '344', '345', '346'])).
% 1.18/1.37  thf('350', plain, (((k2_struct_0 @ sk_C) = (u1_struct_0 @ sk_D))),
% 1.18/1.37      inference('demod', [status(thm)], ['59', '66'])).
% 1.18/1.37  thf('351', plain,
% 1.18/1.37      (![X0 : $i]:
% 1.18/1.37         (~ (r1_tmap_1 @ sk_D @ sk_B @ 
% 1.18/1.37             (k2_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_C) @ X0)
% 1.18/1.37          | (v2_struct_0 @ sk_D)
% 1.18/1.37          | (v2_struct_0 @ sk_D)
% 1.18/1.37          | ~ (m1_subset_1 @ X0 @ (k2_struct_0 @ sk_C))
% 1.18/1.37          | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X0)
% 1.18/1.37          | ~ (m1_subset_1 @ X0 @ (k2_struct_0 @ sk_C))
% 1.18/1.37          | (v2_struct_0 @ sk_B))),
% 1.18/1.37      inference('demod', [status(thm)], ['328', '348', '349', '350'])).
% 1.18/1.37  thf('352', plain,
% 1.18/1.37      (![X0 : $i]:
% 1.18/1.37         ((v2_struct_0 @ sk_B)
% 1.18/1.37          | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X0)
% 1.18/1.37          | ~ (m1_subset_1 @ X0 @ (k2_struct_0 @ sk_C))
% 1.18/1.37          | (v2_struct_0 @ sk_D)
% 1.18/1.37          | ~ (r1_tmap_1 @ sk_D @ sk_B @ 
% 1.18/1.37               (k2_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_C) @ X0))),
% 1.18/1.37      inference('simplify', [status(thm)], ['351'])).
% 1.18/1.37  thf('353', plain,
% 1.18/1.37      (((v2_struct_0 @ sk_C)
% 1.18/1.37        | (v2_struct_0 @ sk_D)
% 1.18/1.37        | (v2_struct_0 @ sk_B)
% 1.18/1.37        | (v2_struct_0 @ sk_D)
% 1.18/1.37        | ~ (m1_subset_1 @ sk_F @ (k2_struct_0 @ sk_C))
% 1.18/1.37        | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)
% 1.18/1.37        | (v2_struct_0 @ sk_B))),
% 1.18/1.37      inference('sup-', [status(thm)], ['298', '352'])).
% 1.18/1.37  thf('354', plain, ((m1_subset_1 @ sk_F @ (k2_struct_0 @ sk_C))),
% 1.18/1.37      inference('demod', [status(thm)], ['225', '226'])).
% 1.18/1.37  thf('355', plain,
% 1.18/1.37      (((v2_struct_0 @ sk_C)
% 1.18/1.37        | (v2_struct_0 @ sk_D)
% 1.18/1.37        | (v2_struct_0 @ sk_B)
% 1.18/1.37        | (v2_struct_0 @ sk_D)
% 1.18/1.37        | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)
% 1.18/1.37        | (v2_struct_0 @ sk_B))),
% 1.18/1.37      inference('demod', [status(thm)], ['353', '354'])).
% 1.18/1.37  thf('356', plain,
% 1.18/1.37      (((r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)
% 1.18/1.37        | (v2_struct_0 @ sk_B)
% 1.18/1.37        | (v2_struct_0 @ sk_D)
% 1.18/1.37        | (v2_struct_0 @ sk_C))),
% 1.18/1.37      inference('simplify', [status(thm)], ['355'])).
% 1.18/1.37  thf('357', plain, (~ (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)),
% 1.18/1.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.37  thf('358', plain,
% 1.18/1.37      (((v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_B))),
% 1.18/1.37      inference('sup-', [status(thm)], ['356', '357'])).
% 1.18/1.37  thf('359', plain, (~ (v2_struct_0 @ sk_C)),
% 1.18/1.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.37  thf('360', plain, (((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_D))),
% 1.18/1.37      inference('clc', [status(thm)], ['358', '359'])).
% 1.18/1.37  thf('361', plain, (~ (v2_struct_0 @ sk_B)),
% 1.18/1.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.37  thf('362', plain, ((v2_struct_0 @ sk_D)),
% 1.18/1.37      inference('clc', [status(thm)], ['360', '361'])).
% 1.18/1.37  thf('363', plain, ($false), inference('demod', [status(thm)], ['0', '362'])).
% 1.18/1.37  
% 1.18/1.37  % SZS output end Refutation
% 1.18/1.37  
% 1.18/1.38  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
