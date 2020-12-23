%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.wjUTXGuvpl

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:10:33 EST 2020

% Result     : Theorem 0.45s
% Output     : Refutation 0.45s
% Verified   : 
% Statistics : Number of formulae       :  182 (2583 expanded)
%              Number of leaves         :   39 ( 768 expanded)
%              Depth                    :   24
%              Number of atoms          : 1551 (66903 expanded)
%              Number of equality atoms :   44 (1848 expanded)
%              Maximal formula depth    :   29 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_tsep_1_type,type,(
    v1_tsep_1: $i > $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_G_type,type,(
    sk_G: $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(r1_tmap_1_type,type,(
    r1_tmap_1: $i > $i > $i > $i > $o )).

thf(k3_tmap_1_type,type,(
    k3_tmap_1: $i > $i > $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(g1_pre_topc_type,type,(
    g1_pre_topc: $i > $i > $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

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
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    sk_F = sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,(
    r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_F ),
    inference(demod,[status(thm)],['1','2'])).

thf('4',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) )
    = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( m1_pre_topc @ A @ A ) ) )).

thf('6',plain,(
    ! [X17: $i] :
      ( ( m1_pre_topc @ X17 @ X17 )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf(t65_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( l1_pre_topc @ B )
         => ( ( m1_pre_topc @ A @ B )
          <=> ( m1_pre_topc @ A @ ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ) )).

thf('7',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( l1_pre_topc @ X9 )
      | ~ ( m1_pre_topc @ X10 @ X9 )
      | ( m1_pre_topc @ X10 @ ( g1_pre_topc @ ( u1_struct_0 @ X9 ) @ ( u1_pre_topc @ X9 ) ) )
      | ~ ( l1_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[t65_pre_topc])).

thf('8',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf(t35_borsuk_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( r1_tarski @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) )).

thf('10',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( m1_pre_topc @ X18 @ X19 )
      | ( r1_tarski @ ( u1_struct_0 @ X18 ) @ ( u1_struct_0 @ X19 ) )
      | ~ ( l1_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[t35_borsuk_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ( r1_tarski @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,
    ( ~ ( l1_pre_topc @ sk_D )
    | ( r1_tarski @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) ) ) )
    | ~ ( l1_pre_topc @ sk_C ) ),
    inference('sup-',[status(thm)],['5','11'])).

thf('13',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('14',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( m1_pre_topc @ X7 @ X8 )
      | ( l1_pre_topc @ X7 )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('15',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_D ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) )
    = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( m1_pre_topc @ X7 @ X8 )
      | ( l1_pre_topc @ X7 )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('21',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_C ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['12','17','18','23'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('25',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('26',plain,
    ( ~ ( r1_tarski @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_C ) )
    | ( ( u1_struct_0 @ sk_D )
      = ( u1_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) )
    = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ! [X17: $i] :
      ( ( m1_pre_topc @ X17 @ X17 )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('29',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( l1_pre_topc @ X9 )
      | ~ ( m1_pre_topc @ X10 @ ( g1_pre_topc @ ( u1_struct_0 @ X9 ) @ ( u1_pre_topc @ X9 ) ) )
      | ( m1_pre_topc @ X10 @ X9 )
      | ~ ( l1_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[t65_pre_topc])).

thf('30',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) @ X0 )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,
    ( ~ ( l1_pre_topc @ sk_D )
    | ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) ) @ sk_C )
    | ~ ( l1_pre_topc @ sk_C ) ),
    inference('sup-',[status(thm)],['27','31'])).

thf('33',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['15','16'])).

thf('34',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) )
    = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['21','22'])).

thf('36',plain,(
    m1_pre_topc @ sk_D @ sk_C ),
    inference(demod,[status(thm)],['32','33','34','35'])).

thf('37',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( m1_pre_topc @ X18 @ X19 )
      | ( r1_tarski @ ( u1_struct_0 @ X18 ) @ ( u1_struct_0 @ X19 ) )
      | ~ ( l1_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[t35_borsuk_1])).

thf('38',plain,
    ( ~ ( l1_pre_topc @ sk_C )
    | ( r1_tarski @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['21','22'])).

thf('40',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,
    ( ( u1_struct_0 @ sk_D )
    = ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['26','40'])).

thf('42',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['4','41'])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('43',plain,(
    ! [X5: $i] :
      ( ( ( k2_struct_0 @ X5 )
        = ( u1_struct_0 @ X5 ) )
      | ~ ( l1_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('44',plain,
    ( ( u1_struct_0 @ sk_D )
    = ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['26','40'])).

thf('45',plain,
    ( ( ( k2_struct_0 @ sk_D )
      = ( u1_struct_0 @ sk_C ) )
    | ~ ( l1_struct_0 @ sk_D ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('46',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['15','16'])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('47',plain,(
    ! [X6: $i] :
      ( ( l1_struct_0 @ X6 )
      | ~ ( l1_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('48',plain,(
    l1_struct_0 @ sk_D ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,
    ( ( k2_struct_0 @ sk_D )
    = ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['45','48'])).

thf('50',plain,(
    ! [X5: $i] :
      ( ( ( k2_struct_0 @ X5 )
        = ( u1_struct_0 @ X5 ) )
      | ~ ( l1_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('51',plain,
    ( ( k2_struct_0 @ sk_D )
    = ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['45','48'])).

thf('52',plain,
    ( ( ( k2_struct_0 @ sk_D )
      = ( k2_struct_0 @ sk_C ) )
    | ~ ( l1_struct_0 @ sk_C ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf('53',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['21','22'])).

thf('54',plain,(
    ! [X6: $i] :
      ( ( l1_struct_0 @ X6 )
      | ~ ( l1_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('55',plain,(
    l1_struct_0 @ sk_C ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,
    ( ( k2_struct_0 @ sk_D )
    = ( k2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['52','55'])).

thf('57',plain,
    ( ( k2_struct_0 @ sk_C )
    = ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['49','56'])).

thf('58',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['42','57'])).

thf('59',plain,
    ( ( u1_struct_0 @ sk_D )
    = ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['26','40'])).

thf('60',plain,
    ( ( k2_struct_0 @ sk_D )
    = ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['45','48'])).

thf('61',plain,
    ( ( u1_struct_0 @ sk_D )
    = ( k2_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,
    ( ( k2_struct_0 @ sk_D )
    = ( k2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['52','55'])).

thf('63',plain,
    ( ( u1_struct_0 @ sk_D )
    = ( k2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['61','62'])).

thf(t86_tmap_1,axiom,(
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
                     => ( ( ( v1_tsep_1 @ C @ D )
                          & ( m1_pre_topc @ C @ D ) )
                       => ! [F: $i] :
                            ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) )
                           => ! [G: $i] :
                                ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) )
                               => ( ( F = G )
                                 => ( ( r1_tmap_1 @ D @ B @ E @ F )
                                  <=> ( r1_tmap_1 @ C @ B @ ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ G ) ) ) ) ) ) ) ) ) ) ) )).

thf('64',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ( v2_struct_0 @ X23 )
      | ~ ( v2_pre_topc @ X23 )
      | ~ ( l1_pre_topc @ X23 )
      | ( v2_struct_0 @ X24 )
      | ~ ( m1_pre_topc @ X24 @ X25 )
      | ~ ( v1_tsep_1 @ X26 @ X24 )
      | ~ ( m1_pre_topc @ X26 @ X24 )
      | ~ ( m1_subset_1 @ X27 @ ( u1_struct_0 @ X24 ) )
      | ( X27 != X28 )
      | ~ ( r1_tmap_1 @ X26 @ X23 @ ( k3_tmap_1 @ X25 @ X23 @ X24 @ X26 @ X29 ) @ X28 )
      | ( r1_tmap_1 @ X24 @ X23 @ X29 @ X27 )
      | ~ ( m1_subset_1 @ X28 @ ( u1_struct_0 @ X26 ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X24 ) @ ( u1_struct_0 @ X23 ) ) ) )
      | ~ ( v1_funct_2 @ X29 @ ( u1_struct_0 @ X24 ) @ ( u1_struct_0 @ X23 ) )
      | ~ ( v1_funct_1 @ X29 )
      | ~ ( m1_pre_topc @ X26 @ X25 )
      | ( v2_struct_0 @ X26 )
      | ~ ( l1_pre_topc @ X25 )
      | ~ ( v2_pre_topc @ X25 )
      | ( v2_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t86_tmap_1])).

thf('65',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i,X28: $i,X29: $i] :
      ( ( v2_struct_0 @ X25 )
      | ~ ( v2_pre_topc @ X25 )
      | ~ ( l1_pre_topc @ X25 )
      | ( v2_struct_0 @ X26 )
      | ~ ( m1_pre_topc @ X26 @ X25 )
      | ~ ( v1_funct_1 @ X29 )
      | ~ ( v1_funct_2 @ X29 @ ( u1_struct_0 @ X24 ) @ ( u1_struct_0 @ X23 ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X24 ) @ ( u1_struct_0 @ X23 ) ) ) )
      | ~ ( m1_subset_1 @ X28 @ ( u1_struct_0 @ X26 ) )
      | ( r1_tmap_1 @ X24 @ X23 @ X29 @ X28 )
      | ~ ( r1_tmap_1 @ X26 @ X23 @ ( k3_tmap_1 @ X25 @ X23 @ X24 @ X26 @ X29 ) @ X28 )
      | ~ ( m1_subset_1 @ X28 @ ( u1_struct_0 @ X24 ) )
      | ~ ( m1_pre_topc @ X26 @ X24 )
      | ~ ( v1_tsep_1 @ X26 @ X24 )
      | ~ ( m1_pre_topc @ X24 @ X25 )
      | ( v2_struct_0 @ X24 )
      | ~ ( l1_pre_topc @ X23 )
      | ~ ( v2_pre_topc @ X23 )
      | ( v2_struct_0 @ X23 ) ) ),
    inference(simplify,[status(thm)],['64'])).

thf('66',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_C ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ sk_D )
      | ~ ( m1_pre_topc @ sk_D @ X2 )
      | ~ ( v1_tsep_1 @ X3 @ sk_D )
      | ~ ( m1_pre_topc @ X3 @ sk_D )
      | ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ sk_D ) )
      | ~ ( r1_tmap_1 @ X3 @ X0 @ ( k3_tmap_1 @ X2 @ X0 @ sk_D @ X3 @ X1 ) @ X4 )
      | ( r1_tmap_1 @ sk_D @ X0 @ X1 @ X4 )
      | ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ X3 ) )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( m1_pre_topc @ X3 @ X2 )
      | ( v2_struct_0 @ X3 )
      | ~ ( l1_pre_topc @ X2 )
      | ~ ( v2_pre_topc @ X2 )
      | ( v2_struct_0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['63','65'])).

thf('67',plain,
    ( ( u1_struct_0 @ sk_D )
    = ( k2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('68',plain,
    ( ( u1_struct_0 @ sk_D )
    = ( k2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('69',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_C ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ sk_D )
      | ~ ( m1_pre_topc @ sk_D @ X2 )
      | ~ ( v1_tsep_1 @ X3 @ sk_D )
      | ~ ( m1_pre_topc @ X3 @ sk_D )
      | ~ ( m1_subset_1 @ X4 @ ( k2_struct_0 @ sk_C ) )
      | ~ ( r1_tmap_1 @ X3 @ X0 @ ( k3_tmap_1 @ X2 @ X0 @ sk_D @ X3 @ X1 ) @ X4 )
      | ( r1_tmap_1 @ sk_D @ X0 @ X1 @ X4 )
      | ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ X3 ) )
      | ~ ( v1_funct_2 @ X1 @ ( k2_struct_0 @ sk_C ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( m1_pre_topc @ X3 @ X2 )
      | ( v2_struct_0 @ X3 )
      | ~ ( l1_pre_topc @ X2 )
      | ~ ( v2_pre_topc @ X2 )
      | ( v2_struct_0 @ X2 ) ) ),
    inference(demod,[status(thm)],['66','67','68'])).

thf('70',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X1 )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( v1_funct_2 @ sk_E @ ( k2_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X1 ) )
      | ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X2 )
      | ~ ( r1_tmap_1 @ X1 @ sk_B @ ( k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E ) @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( k2_struct_0 @ sk_C ) )
      | ~ ( m1_pre_topc @ X1 @ sk_D )
      | ~ ( v1_tsep_1 @ X1 @ sk_D )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ( v2_struct_0 @ sk_D )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['58','69'])).

thf('71',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    ! [X5: $i] :
      ( ( ( k2_struct_0 @ X5 )
        = ( u1_struct_0 @ X5 ) )
      | ~ ( l1_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('73',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,
    ( ( v1_funct_2 @ sk_E @ ( k2_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_D ) ),
    inference('sup+',[status(thm)],['72','73'])).

thf('75',plain,(
    l1_struct_0 @ sk_D ),
    inference('sup-',[status(thm)],['46','47'])).

thf('76',plain,(
    v1_funct_2 @ sk_E @ ( k2_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['74','75'])).

thf('77',plain,
    ( ( k2_struct_0 @ sk_D )
    = ( k2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['52','55'])).

thf('78',plain,(
    v1_funct_2 @ sk_E @ ( k2_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('79',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X1 )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X1 ) )
      | ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X2 )
      | ~ ( r1_tmap_1 @ X1 @ sk_B @ ( k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E ) @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( k2_struct_0 @ sk_C ) )
      | ~ ( m1_pre_topc @ X1 @ sk_D )
      | ~ ( v1_tsep_1 @ X1 @ sk_D )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['70','71','78','79','80'])).

thf('82',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ~ ( m1_pre_topc @ sk_D @ sk_A )
    | ~ ( v1_tsep_1 @ sk_C @ sk_D )
    | ~ ( m1_pre_topc @ sk_C @ sk_D )
    | ~ ( m1_subset_1 @ sk_F @ ( k2_struct_0 @ sk_C ) )
    | ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F )
    | ~ ( m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_C ) )
    | ~ ( m1_pre_topc @ sk_C @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['3','81'])).

thf('83',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    ! [X5: $i] :
      ( ( ( k2_struct_0 @ X5 )
        = ( u1_struct_0 @ X5 ) )
      | ~ ( l1_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('85',plain,(
    ! [X17: $i] :
      ( ( m1_pre_topc @ X17 @ X17 )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf(t1_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( m1_subset_1 @ ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('86',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( m1_pre_topc @ X15 @ X16 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X15 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( l1_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('87',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['87'])).

thf('89',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_struct_0 @ X0 ) ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup+',[status(thm)],['84','88'])).

thf('90',plain,(
    ! [X6: $i] :
      ( ( l1_struct_0 @ X6 )
      | ~ ( l1_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('91',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_struct_0 @ X0 ) ) ) ) ),
    inference(clc,[status(thm)],['89','90'])).

thf('92',plain,
    ( ( u1_struct_0 @ sk_D )
    = ( k2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['61','62'])).

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

thf('93',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_pre_topc @ X12 @ X13 )
      | ( X14
       != ( u1_struct_0 @ X12 ) )
      | ~ ( v3_pre_topc @ X14 @ X13 )
      | ( v1_tsep_1 @ X12 @ X13 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ~ ( l1_pre_topc @ X13 )
      | ~ ( v2_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[t16_tsep_1])).

thf('94',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v2_pre_topc @ X13 )
      | ~ ( l1_pre_topc @ X13 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X12 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ( v1_tsep_1 @ X12 @ X13 )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ X12 ) @ X13 )
      | ~ ( m1_pre_topc @ X12 @ X13 ) ) ),
    inference(simplify,[status(thm)],['93'])).

thf('95',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_C ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ sk_D )
      | ( v1_tsep_1 @ X0 @ sk_D )
      | ~ ( l1_pre_topc @ sk_D )
      | ~ ( v2_pre_topc @ sk_D ) ) ),
    inference('sup-',[status(thm)],['92','94'])).

thf('96',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['15','16'])).

thf('97',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( v2_pre_topc @ B ) ) ) )).

thf('98',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_pre_topc @ X3 @ X4 )
      | ( v2_pre_topc @ X3 )
      | ~ ( l1_pre_topc @ X4 )
      | ~ ( v2_pre_topc @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc1_pre_topc])).

thf('99',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_pre_topc @ sk_D ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    v2_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['99','100','101'])).

thf('103',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_C ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ sk_D )
      | ( v1_tsep_1 @ X0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['95','96','102'])).

thf('104',plain,
    ( ~ ( l1_pre_topc @ sk_C )
    | ( v1_tsep_1 @ sk_C @ sk_D )
    | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_C ) @ sk_D )
    | ~ ( m1_pre_topc @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['91','103'])).

thf('105',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['21','22'])).

thf('106',plain,
    ( ( k2_struct_0 @ sk_C )
    = ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['49','56'])).

thf('107',plain,
    ( ( k2_struct_0 @ sk_D )
    = ( k2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['52','55'])).

thf(fc10_tops_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( v3_pre_topc @ ( k2_struct_0 @ A ) @ A ) ) )).

thf('108',plain,(
    ! [X11: $i] :
      ( ( v3_pre_topc @ ( k2_struct_0 @ X11 ) @ X11 )
      | ~ ( l1_pre_topc @ X11 )
      | ~ ( v2_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[fc10_tops_1])).

thf('109',plain,
    ( ( v3_pre_topc @ ( k2_struct_0 @ sk_C ) @ sk_D )
    | ~ ( v2_pre_topc @ sk_D )
    | ~ ( l1_pre_topc @ sk_D ) ),
    inference('sup+',[status(thm)],['107','108'])).

thf('110',plain,(
    v2_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['99','100','101'])).

thf('111',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['15','16'])).

thf('112',plain,(
    v3_pre_topc @ ( k2_struct_0 @ sk_C ) @ sk_D ),
    inference(demod,[status(thm)],['109','110','111'])).

thf('113',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) )
    = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('115',plain,
    ( ( m1_pre_topc @ sk_C @ sk_D )
    | ~ ( l1_pre_topc @ sk_C ) ),
    inference('sup+',[status(thm)],['113','114'])).

thf('116',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['21','22'])).

thf('117',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(demod,[status(thm)],['115','116'])).

thf('118',plain,(
    v1_tsep_1 @ sk_C @ sk_D ),
    inference(demod,[status(thm)],['104','105','106','112','117'])).

thf('119',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(demod,[status(thm)],['115','116'])).

thf('120',plain,(
    ! [X5: $i] :
      ( ( ( k2_struct_0 @ X5 )
        = ( u1_struct_0 @ X5 ) )
      | ~ ( l1_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('121',plain,(
    m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,(
    sk_F = sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['121','122'])).

thf('124',plain,
    ( ( m1_subset_1 @ sk_F @ ( k2_struct_0 @ sk_C ) )
    | ~ ( l1_struct_0 @ sk_C ) ),
    inference('sup+',[status(thm)],['120','123'])).

thf('125',plain,(
    l1_struct_0 @ sk_C ),
    inference('sup-',[status(thm)],['53','54'])).

thf('126',plain,(
    m1_subset_1 @ sk_F @ ( k2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['124','125'])).

thf('127',plain,
    ( ( k2_struct_0 @ sk_C )
    = ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['49','56'])).

thf('128',plain,(
    m1_subset_1 @ sk_F @ ( k2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['124','125'])).

thf('129',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('130',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('131',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('132',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['82','83','118','119','126','127','128','129','130','131'])).

thf('133',plain,(
    ~ ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('134',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['132','133'])).

thf('135',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('136',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['134','135'])).

thf('137',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('138',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C ) ),
    inference(clc,[status(thm)],['136','137'])).

thf('139',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('140',plain,(
    v2_struct_0 @ sk_C ),
    inference(clc,[status(thm)],['138','139'])).

thf('141',plain,(
    $false ),
    inference(demod,[status(thm)],['0','140'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.wjUTXGuvpl
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:07:54 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.45/0.63  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.45/0.63  % Solved by: fo/fo7.sh
% 0.45/0.63  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.45/0.63  % done 398 iterations in 0.205s
% 0.45/0.63  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.45/0.63  % SZS output start Refutation
% 0.45/0.63  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.45/0.63  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.45/0.63  thf(v1_tsep_1_type, type, v1_tsep_1: $i > $i > $o).
% 0.45/0.63  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.45/0.63  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 0.45/0.63  thf(sk_A_type, type, sk_A: $i).
% 0.45/0.63  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.45/0.63  thf(sk_G_type, type, sk_G: $i).
% 0.45/0.63  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.45/0.63  thf(sk_C_type, type, sk_C: $i).
% 0.45/0.63  thf(sk_B_type, type, sk_B: $i).
% 0.45/0.63  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.45/0.63  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.45/0.63  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.45/0.63  thf(sk_F_type, type, sk_F: $i).
% 0.45/0.63  thf(r1_tmap_1_type, type, r1_tmap_1: $i > $i > $i > $i > $o).
% 0.45/0.63  thf(k3_tmap_1_type, type, k3_tmap_1: $i > $i > $i > $i > $i > $i).
% 0.45/0.63  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.45/0.63  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.45/0.63  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.45/0.63  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.45/0.63  thf(g1_pre_topc_type, type, g1_pre_topc: $i > $i > $i).
% 0.45/0.63  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.45/0.63  thf(sk_E_type, type, sk_E: $i).
% 0.45/0.63  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.45/0.63  thf(sk_D_type, type, sk_D: $i).
% 0.45/0.63  thf(t88_tmap_1, conjecture,
% 0.45/0.63    (![A:$i]:
% 0.45/0.63     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.45/0.63       ( ![B:$i]:
% 0.45/0.63         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.45/0.63             ( l1_pre_topc @ B ) ) =>
% 0.45/0.63           ( ![C:$i]:
% 0.45/0.63             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.45/0.63               ( ![D:$i]:
% 0.45/0.63                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.45/0.63                   ( ![E:$i]:
% 0.45/0.63                     ( ( ( v1_funct_1 @ E ) & 
% 0.45/0.64                         ( v1_funct_2 @
% 0.45/0.64                           E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 0.45/0.64                         ( m1_subset_1 @
% 0.45/0.64                           E @ 
% 0.45/0.64                           ( k1_zfmisc_1 @
% 0.45/0.64                             ( k2_zfmisc_1 @
% 0.45/0.64                               ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.45/0.64                       ( ( ( g1_pre_topc @
% 0.45/0.64                             ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) ) =
% 0.45/0.64                           ( D ) ) =>
% 0.45/0.64                         ( ![F:$i]:
% 0.45/0.64                           ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 0.45/0.64                             ( ![G:$i]:
% 0.45/0.64                               ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) ) =>
% 0.45/0.64                                 ( ( ( ( F ) = ( G ) ) & 
% 0.45/0.64                                     ( r1_tmap_1 @
% 0.45/0.64                                       C @ B @ 
% 0.45/0.64                                       ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ G ) ) =>
% 0.45/0.64                                   ( r1_tmap_1 @ D @ B @ E @ F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.45/0.64  thf(zf_stmt_0, negated_conjecture,
% 0.45/0.64    (~( ![A:$i]:
% 0.45/0.64        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.45/0.64            ( l1_pre_topc @ A ) ) =>
% 0.45/0.64          ( ![B:$i]:
% 0.45/0.64            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.45/0.64                ( l1_pre_topc @ B ) ) =>
% 0.45/0.64              ( ![C:$i]:
% 0.45/0.64                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.45/0.64                  ( ![D:$i]:
% 0.45/0.64                    ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.45/0.64                      ( ![E:$i]:
% 0.45/0.64                        ( ( ( v1_funct_1 @ E ) & 
% 0.45/0.64                            ( v1_funct_2 @
% 0.45/0.64                              E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 0.45/0.64                            ( m1_subset_1 @
% 0.45/0.64                              E @ 
% 0.45/0.64                              ( k1_zfmisc_1 @
% 0.45/0.64                                ( k2_zfmisc_1 @
% 0.45/0.64                                  ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.45/0.64                          ( ( ( g1_pre_topc @
% 0.45/0.64                                ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) ) =
% 0.45/0.64                              ( D ) ) =>
% 0.45/0.64                            ( ![F:$i]:
% 0.45/0.64                              ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 0.45/0.64                                ( ![G:$i]:
% 0.45/0.64                                  ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) ) =>
% 0.45/0.64                                    ( ( ( ( F ) = ( G ) ) & 
% 0.45/0.64                                        ( r1_tmap_1 @
% 0.45/0.64                                          C @ B @ 
% 0.45/0.64                                          ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ G ) ) =>
% 0.45/0.64                                      ( r1_tmap_1 @ D @ B @ E @ F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.45/0.64    inference('cnf.neg', [status(esa)], [t88_tmap_1])).
% 0.45/0.64  thf('0', plain, (~ (v2_struct_0 @ sk_C)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('1', plain,
% 0.45/0.64      ((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.45/0.64        (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_G)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('2', plain, (((sk_F) = (sk_G))),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('3', plain,
% 0.45/0.64      ((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.45/0.64        (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_F)),
% 0.45/0.64      inference('demod', [status(thm)], ['1', '2'])).
% 0.45/0.64  thf('4', plain,
% 0.45/0.64      ((m1_subset_1 @ sk_E @ 
% 0.45/0.64        (k1_zfmisc_1 @ 
% 0.45/0.64         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('5', plain,
% 0.45/0.64      (((g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) = (sk_D))),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf(t2_tsep_1, axiom,
% 0.45/0.64    (![A:$i]: ( ( l1_pre_topc @ A ) => ( m1_pre_topc @ A @ A ) ))).
% 0.45/0.64  thf('6', plain,
% 0.45/0.64      (![X17 : $i]: ((m1_pre_topc @ X17 @ X17) | ~ (l1_pre_topc @ X17))),
% 0.45/0.64      inference('cnf', [status(esa)], [t2_tsep_1])).
% 0.45/0.64  thf(t65_pre_topc, axiom,
% 0.45/0.64    (![A:$i]:
% 0.45/0.64     ( ( l1_pre_topc @ A ) =>
% 0.45/0.64       ( ![B:$i]:
% 0.45/0.64         ( ( l1_pre_topc @ B ) =>
% 0.45/0.64           ( ( m1_pre_topc @ A @ B ) <=>
% 0.45/0.64             ( m1_pre_topc @
% 0.45/0.64               A @ ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ) ))).
% 0.45/0.64  thf('7', plain,
% 0.45/0.64      (![X9 : $i, X10 : $i]:
% 0.45/0.64         (~ (l1_pre_topc @ X9)
% 0.45/0.64          | ~ (m1_pre_topc @ X10 @ X9)
% 0.45/0.64          | (m1_pre_topc @ X10 @ 
% 0.45/0.64             (g1_pre_topc @ (u1_struct_0 @ X9) @ (u1_pre_topc @ X9)))
% 0.45/0.64          | ~ (l1_pre_topc @ X10))),
% 0.45/0.64      inference('cnf', [status(esa)], [t65_pre_topc])).
% 0.45/0.64  thf('8', plain,
% 0.45/0.64      (![X0 : $i]:
% 0.45/0.64         (~ (l1_pre_topc @ X0)
% 0.45/0.64          | ~ (l1_pre_topc @ X0)
% 0.45/0.64          | (m1_pre_topc @ X0 @ 
% 0.45/0.64             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.45/0.64          | ~ (l1_pre_topc @ X0))),
% 0.45/0.64      inference('sup-', [status(thm)], ['6', '7'])).
% 0.45/0.64  thf('9', plain,
% 0.45/0.64      (![X0 : $i]:
% 0.45/0.64         ((m1_pre_topc @ X0 @ 
% 0.45/0.64           (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.45/0.64          | ~ (l1_pre_topc @ X0))),
% 0.45/0.64      inference('simplify', [status(thm)], ['8'])).
% 0.45/0.64  thf(t35_borsuk_1, axiom,
% 0.45/0.64    (![A:$i]:
% 0.45/0.64     ( ( l1_pre_topc @ A ) =>
% 0.45/0.64       ( ![B:$i]:
% 0.45/0.64         ( ( m1_pre_topc @ B @ A ) =>
% 0.45/0.64           ( r1_tarski @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ))).
% 0.45/0.64  thf('10', plain,
% 0.45/0.64      (![X18 : $i, X19 : $i]:
% 0.45/0.64         (~ (m1_pre_topc @ X18 @ X19)
% 0.45/0.64          | (r1_tarski @ (u1_struct_0 @ X18) @ (u1_struct_0 @ X19))
% 0.45/0.64          | ~ (l1_pre_topc @ X19))),
% 0.45/0.64      inference('cnf', [status(esa)], [t35_borsuk_1])).
% 0.45/0.64  thf('11', plain,
% 0.45/0.64      (![X0 : $i]:
% 0.45/0.64         (~ (l1_pre_topc @ X0)
% 0.45/0.64          | ~ (l1_pre_topc @ 
% 0.45/0.64               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.45/0.64          | (r1_tarski @ (u1_struct_0 @ X0) @ 
% 0.45/0.64             (u1_struct_0 @ 
% 0.45/0.64              (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))))),
% 0.45/0.64      inference('sup-', [status(thm)], ['9', '10'])).
% 0.45/0.64  thf('12', plain,
% 0.45/0.64      ((~ (l1_pre_topc @ sk_D)
% 0.45/0.64        | (r1_tarski @ (u1_struct_0 @ sk_C) @ 
% 0.45/0.64           (u1_struct_0 @ 
% 0.45/0.64            (g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C))))
% 0.45/0.64        | ~ (l1_pre_topc @ sk_C))),
% 0.45/0.64      inference('sup-', [status(thm)], ['5', '11'])).
% 0.45/0.64  thf('13', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf(dt_m1_pre_topc, axiom,
% 0.45/0.64    (![A:$i]:
% 0.45/0.64     ( ( l1_pre_topc @ A ) =>
% 0.45/0.64       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.45/0.64  thf('14', plain,
% 0.45/0.64      (![X7 : $i, X8 : $i]:
% 0.45/0.64         (~ (m1_pre_topc @ X7 @ X8) | (l1_pre_topc @ X7) | ~ (l1_pre_topc @ X8))),
% 0.45/0.64      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.45/0.64  thf('15', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_D))),
% 0.45/0.64      inference('sup-', [status(thm)], ['13', '14'])).
% 0.45/0.64  thf('16', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('17', plain, ((l1_pre_topc @ sk_D)),
% 0.45/0.64      inference('demod', [status(thm)], ['15', '16'])).
% 0.45/0.64  thf('18', plain,
% 0.45/0.64      (((g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) = (sk_D))),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('19', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('20', plain,
% 0.45/0.64      (![X7 : $i, X8 : $i]:
% 0.45/0.64         (~ (m1_pre_topc @ X7 @ X8) | (l1_pre_topc @ X7) | ~ (l1_pre_topc @ X8))),
% 0.45/0.64      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.45/0.64  thf('21', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_C))),
% 0.45/0.64      inference('sup-', [status(thm)], ['19', '20'])).
% 0.45/0.64  thf('22', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('23', plain, ((l1_pre_topc @ sk_C)),
% 0.45/0.64      inference('demod', [status(thm)], ['21', '22'])).
% 0.45/0.64  thf('24', plain, ((r1_tarski @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D))),
% 0.45/0.64      inference('demod', [status(thm)], ['12', '17', '18', '23'])).
% 0.45/0.64  thf(d10_xboole_0, axiom,
% 0.45/0.64    (![A:$i,B:$i]:
% 0.45/0.64     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.45/0.64  thf('25', plain,
% 0.45/0.64      (![X0 : $i, X2 : $i]:
% 0.45/0.64         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.45/0.64      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.45/0.64  thf('26', plain,
% 0.45/0.64      ((~ (r1_tarski @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_C))
% 0.45/0.64        | ((u1_struct_0 @ sk_D) = (u1_struct_0 @ sk_C)))),
% 0.45/0.64      inference('sup-', [status(thm)], ['24', '25'])).
% 0.45/0.64  thf('27', plain,
% 0.45/0.64      (((g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) = (sk_D))),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('28', plain,
% 0.45/0.64      (![X17 : $i]: ((m1_pre_topc @ X17 @ X17) | ~ (l1_pre_topc @ X17))),
% 0.45/0.64      inference('cnf', [status(esa)], [t2_tsep_1])).
% 0.45/0.64  thf('29', plain,
% 0.45/0.64      (![X9 : $i, X10 : $i]:
% 0.45/0.64         (~ (l1_pre_topc @ X9)
% 0.45/0.64          | ~ (m1_pre_topc @ X10 @ 
% 0.45/0.64               (g1_pre_topc @ (u1_struct_0 @ X9) @ (u1_pre_topc @ X9)))
% 0.45/0.64          | (m1_pre_topc @ X10 @ X9)
% 0.45/0.64          | ~ (l1_pre_topc @ X10))),
% 0.45/0.64      inference('cnf', [status(esa)], [t65_pre_topc])).
% 0.45/0.64  thf('30', plain,
% 0.45/0.64      (![X0 : $i]:
% 0.45/0.64         (~ (l1_pre_topc @ 
% 0.45/0.64             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.45/0.64          | ~ (l1_pre_topc @ 
% 0.45/0.64               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.45/0.64          | (m1_pre_topc @ 
% 0.45/0.64             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)) @ X0)
% 0.45/0.64          | ~ (l1_pre_topc @ X0))),
% 0.45/0.64      inference('sup-', [status(thm)], ['28', '29'])).
% 0.45/0.64  thf('31', plain,
% 0.45/0.64      (![X0 : $i]:
% 0.45/0.64         (~ (l1_pre_topc @ X0)
% 0.45/0.64          | (m1_pre_topc @ 
% 0.45/0.64             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)) @ X0)
% 0.45/0.64          | ~ (l1_pre_topc @ 
% 0.45/0.64               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 0.45/0.64      inference('simplify', [status(thm)], ['30'])).
% 0.45/0.64  thf('32', plain,
% 0.45/0.64      ((~ (l1_pre_topc @ sk_D)
% 0.45/0.64        | (m1_pre_topc @ 
% 0.45/0.64           (g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) @ sk_C)
% 0.45/0.64        | ~ (l1_pre_topc @ sk_C))),
% 0.45/0.64      inference('sup-', [status(thm)], ['27', '31'])).
% 0.45/0.64  thf('33', plain, ((l1_pre_topc @ sk_D)),
% 0.45/0.64      inference('demod', [status(thm)], ['15', '16'])).
% 0.45/0.64  thf('34', plain,
% 0.45/0.64      (((g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) = (sk_D))),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('35', plain, ((l1_pre_topc @ sk_C)),
% 0.45/0.64      inference('demod', [status(thm)], ['21', '22'])).
% 0.45/0.64  thf('36', plain, ((m1_pre_topc @ sk_D @ sk_C)),
% 0.45/0.64      inference('demod', [status(thm)], ['32', '33', '34', '35'])).
% 0.45/0.64  thf('37', plain,
% 0.45/0.64      (![X18 : $i, X19 : $i]:
% 0.45/0.64         (~ (m1_pre_topc @ X18 @ X19)
% 0.45/0.64          | (r1_tarski @ (u1_struct_0 @ X18) @ (u1_struct_0 @ X19))
% 0.45/0.64          | ~ (l1_pre_topc @ X19))),
% 0.45/0.64      inference('cnf', [status(esa)], [t35_borsuk_1])).
% 0.45/0.64  thf('38', plain,
% 0.45/0.64      ((~ (l1_pre_topc @ sk_C)
% 0.45/0.64        | (r1_tarski @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_C)))),
% 0.45/0.64      inference('sup-', [status(thm)], ['36', '37'])).
% 0.45/0.64  thf('39', plain, ((l1_pre_topc @ sk_C)),
% 0.45/0.64      inference('demod', [status(thm)], ['21', '22'])).
% 0.45/0.64  thf('40', plain, ((r1_tarski @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_C))),
% 0.45/0.64      inference('demod', [status(thm)], ['38', '39'])).
% 0.45/0.64  thf('41', plain, (((u1_struct_0 @ sk_D) = (u1_struct_0 @ sk_C))),
% 0.45/0.64      inference('demod', [status(thm)], ['26', '40'])).
% 0.45/0.64  thf('42', plain,
% 0.45/0.64      ((m1_subset_1 @ sk_E @ 
% 0.45/0.64        (k1_zfmisc_1 @ 
% 0.45/0.64         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 0.45/0.64      inference('demod', [status(thm)], ['4', '41'])).
% 0.45/0.64  thf(d3_struct_0, axiom,
% 0.45/0.64    (![A:$i]:
% 0.45/0.64     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.45/0.64  thf('43', plain,
% 0.45/0.64      (![X5 : $i]:
% 0.45/0.64         (((k2_struct_0 @ X5) = (u1_struct_0 @ X5)) | ~ (l1_struct_0 @ X5))),
% 0.45/0.64      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.45/0.64  thf('44', plain, (((u1_struct_0 @ sk_D) = (u1_struct_0 @ sk_C))),
% 0.45/0.64      inference('demod', [status(thm)], ['26', '40'])).
% 0.45/0.64  thf('45', plain,
% 0.45/0.64      ((((k2_struct_0 @ sk_D) = (u1_struct_0 @ sk_C)) | ~ (l1_struct_0 @ sk_D))),
% 0.45/0.64      inference('sup+', [status(thm)], ['43', '44'])).
% 0.45/0.64  thf('46', plain, ((l1_pre_topc @ sk_D)),
% 0.45/0.64      inference('demod', [status(thm)], ['15', '16'])).
% 0.45/0.64  thf(dt_l1_pre_topc, axiom,
% 0.45/0.64    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.45/0.64  thf('47', plain, (![X6 : $i]: ((l1_struct_0 @ X6) | ~ (l1_pre_topc @ X6))),
% 0.45/0.64      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.45/0.64  thf('48', plain, ((l1_struct_0 @ sk_D)),
% 0.45/0.64      inference('sup-', [status(thm)], ['46', '47'])).
% 0.45/0.64  thf('49', plain, (((k2_struct_0 @ sk_D) = (u1_struct_0 @ sk_C))),
% 0.45/0.64      inference('demod', [status(thm)], ['45', '48'])).
% 0.45/0.64  thf('50', plain,
% 0.45/0.64      (![X5 : $i]:
% 0.45/0.64         (((k2_struct_0 @ X5) = (u1_struct_0 @ X5)) | ~ (l1_struct_0 @ X5))),
% 0.45/0.64      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.45/0.64  thf('51', plain, (((k2_struct_0 @ sk_D) = (u1_struct_0 @ sk_C))),
% 0.45/0.64      inference('demod', [status(thm)], ['45', '48'])).
% 0.45/0.64  thf('52', plain,
% 0.45/0.64      ((((k2_struct_0 @ sk_D) = (k2_struct_0 @ sk_C)) | ~ (l1_struct_0 @ sk_C))),
% 0.45/0.64      inference('sup+', [status(thm)], ['50', '51'])).
% 0.45/0.64  thf('53', plain, ((l1_pre_topc @ sk_C)),
% 0.45/0.64      inference('demod', [status(thm)], ['21', '22'])).
% 0.45/0.64  thf('54', plain, (![X6 : $i]: ((l1_struct_0 @ X6) | ~ (l1_pre_topc @ X6))),
% 0.45/0.64      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.45/0.64  thf('55', plain, ((l1_struct_0 @ sk_C)),
% 0.45/0.64      inference('sup-', [status(thm)], ['53', '54'])).
% 0.45/0.64  thf('56', plain, (((k2_struct_0 @ sk_D) = (k2_struct_0 @ sk_C))),
% 0.45/0.64      inference('demod', [status(thm)], ['52', '55'])).
% 0.45/0.64  thf('57', plain, (((k2_struct_0 @ sk_C) = (u1_struct_0 @ sk_C))),
% 0.45/0.64      inference('demod', [status(thm)], ['49', '56'])).
% 0.45/0.64  thf('58', plain,
% 0.45/0.64      ((m1_subset_1 @ sk_E @ 
% 0.45/0.64        (k1_zfmisc_1 @ 
% 0.45/0.64         (k2_zfmisc_1 @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 0.45/0.64      inference('demod', [status(thm)], ['42', '57'])).
% 0.45/0.64  thf('59', plain, (((u1_struct_0 @ sk_D) = (u1_struct_0 @ sk_C))),
% 0.45/0.64      inference('demod', [status(thm)], ['26', '40'])).
% 0.45/0.64  thf('60', plain, (((k2_struct_0 @ sk_D) = (u1_struct_0 @ sk_C))),
% 0.45/0.64      inference('demod', [status(thm)], ['45', '48'])).
% 0.45/0.64  thf('61', plain, (((u1_struct_0 @ sk_D) = (k2_struct_0 @ sk_D))),
% 0.45/0.64      inference('demod', [status(thm)], ['59', '60'])).
% 0.45/0.64  thf('62', plain, (((k2_struct_0 @ sk_D) = (k2_struct_0 @ sk_C))),
% 0.45/0.64      inference('demod', [status(thm)], ['52', '55'])).
% 0.45/0.64  thf('63', plain, (((u1_struct_0 @ sk_D) = (k2_struct_0 @ sk_C))),
% 0.45/0.64      inference('demod', [status(thm)], ['61', '62'])).
% 0.45/0.64  thf(t86_tmap_1, axiom,
% 0.45/0.64    (![A:$i]:
% 0.45/0.64     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.45/0.64       ( ![B:$i]:
% 0.45/0.64         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.45/0.64             ( l1_pre_topc @ B ) ) =>
% 0.45/0.64           ( ![C:$i]:
% 0.45/0.64             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.45/0.64               ( ![D:$i]:
% 0.45/0.64                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.45/0.64                   ( ![E:$i]:
% 0.45/0.64                     ( ( ( v1_funct_1 @ E ) & 
% 0.45/0.64                         ( v1_funct_2 @
% 0.45/0.64                           E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 0.45/0.64                         ( m1_subset_1 @
% 0.45/0.64                           E @ 
% 0.45/0.64                           ( k1_zfmisc_1 @
% 0.45/0.64                             ( k2_zfmisc_1 @
% 0.45/0.64                               ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.45/0.64                       ( ( ( v1_tsep_1 @ C @ D ) & ( m1_pre_topc @ C @ D ) ) =>
% 0.45/0.64                         ( ![F:$i]:
% 0.45/0.64                           ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 0.45/0.64                             ( ![G:$i]:
% 0.45/0.64                               ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) ) =>
% 0.45/0.64                                 ( ( ( F ) = ( G ) ) =>
% 0.45/0.64                                   ( ( r1_tmap_1 @ D @ B @ E @ F ) <=>
% 0.45/0.64                                     ( r1_tmap_1 @
% 0.45/0.64                                       C @ B @ 
% 0.45/0.64                                       ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ G ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.45/0.64  thf('64', plain,
% 0.45/0.64      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 0.45/0.64         ((v2_struct_0 @ X23)
% 0.45/0.64          | ~ (v2_pre_topc @ X23)
% 0.45/0.64          | ~ (l1_pre_topc @ X23)
% 0.45/0.64          | (v2_struct_0 @ X24)
% 0.45/0.64          | ~ (m1_pre_topc @ X24 @ X25)
% 0.45/0.64          | ~ (v1_tsep_1 @ X26 @ X24)
% 0.45/0.64          | ~ (m1_pre_topc @ X26 @ X24)
% 0.45/0.64          | ~ (m1_subset_1 @ X27 @ (u1_struct_0 @ X24))
% 0.45/0.64          | ((X27) != (X28))
% 0.45/0.64          | ~ (r1_tmap_1 @ X26 @ X23 @ 
% 0.45/0.64               (k3_tmap_1 @ X25 @ X23 @ X24 @ X26 @ X29) @ X28)
% 0.45/0.64          | (r1_tmap_1 @ X24 @ X23 @ X29 @ X27)
% 0.45/0.64          | ~ (m1_subset_1 @ X28 @ (u1_struct_0 @ X26))
% 0.45/0.64          | ~ (m1_subset_1 @ X29 @ 
% 0.45/0.64               (k1_zfmisc_1 @ 
% 0.45/0.64                (k2_zfmisc_1 @ (u1_struct_0 @ X24) @ (u1_struct_0 @ X23))))
% 0.45/0.64          | ~ (v1_funct_2 @ X29 @ (u1_struct_0 @ X24) @ (u1_struct_0 @ X23))
% 0.45/0.64          | ~ (v1_funct_1 @ X29)
% 0.45/0.64          | ~ (m1_pre_topc @ X26 @ X25)
% 0.45/0.64          | (v2_struct_0 @ X26)
% 0.45/0.64          | ~ (l1_pre_topc @ X25)
% 0.45/0.64          | ~ (v2_pre_topc @ X25)
% 0.45/0.64          | (v2_struct_0 @ X25))),
% 0.45/0.64      inference('cnf', [status(esa)], [t86_tmap_1])).
% 0.45/0.64  thf('65', plain,
% 0.45/0.64      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i, X28 : $i, X29 : $i]:
% 0.45/0.64         ((v2_struct_0 @ X25)
% 0.45/0.64          | ~ (v2_pre_topc @ X25)
% 0.45/0.64          | ~ (l1_pre_topc @ X25)
% 0.45/0.64          | (v2_struct_0 @ X26)
% 0.45/0.64          | ~ (m1_pre_topc @ X26 @ X25)
% 0.45/0.64          | ~ (v1_funct_1 @ X29)
% 0.45/0.64          | ~ (v1_funct_2 @ X29 @ (u1_struct_0 @ X24) @ (u1_struct_0 @ X23))
% 0.45/0.64          | ~ (m1_subset_1 @ X29 @ 
% 0.45/0.64               (k1_zfmisc_1 @ 
% 0.45/0.64                (k2_zfmisc_1 @ (u1_struct_0 @ X24) @ (u1_struct_0 @ X23))))
% 0.45/0.64          | ~ (m1_subset_1 @ X28 @ (u1_struct_0 @ X26))
% 0.45/0.64          | (r1_tmap_1 @ X24 @ X23 @ X29 @ X28)
% 0.45/0.64          | ~ (r1_tmap_1 @ X26 @ X23 @ 
% 0.45/0.64               (k3_tmap_1 @ X25 @ X23 @ X24 @ X26 @ X29) @ X28)
% 0.45/0.64          | ~ (m1_subset_1 @ X28 @ (u1_struct_0 @ X24))
% 0.45/0.64          | ~ (m1_pre_topc @ X26 @ X24)
% 0.45/0.64          | ~ (v1_tsep_1 @ X26 @ X24)
% 0.45/0.64          | ~ (m1_pre_topc @ X24 @ X25)
% 0.45/0.64          | (v2_struct_0 @ X24)
% 0.45/0.64          | ~ (l1_pre_topc @ X23)
% 0.45/0.64          | ~ (v2_pre_topc @ X23)
% 0.45/0.64          | (v2_struct_0 @ X23))),
% 0.45/0.64      inference('simplify', [status(thm)], ['64'])).
% 0.45/0.64  thf('66', plain,
% 0.45/0.64      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.45/0.64         (~ (m1_subset_1 @ X1 @ 
% 0.45/0.64             (k1_zfmisc_1 @ 
% 0.45/0.64              (k2_zfmisc_1 @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ X0))))
% 0.45/0.64          | (v2_struct_0 @ X0)
% 0.45/0.64          | ~ (v2_pre_topc @ X0)
% 0.45/0.64          | ~ (l1_pre_topc @ X0)
% 0.45/0.64          | (v2_struct_0 @ sk_D)
% 0.45/0.64          | ~ (m1_pre_topc @ sk_D @ X2)
% 0.45/0.64          | ~ (v1_tsep_1 @ X3 @ sk_D)
% 0.45/0.64          | ~ (m1_pre_topc @ X3 @ sk_D)
% 0.45/0.64          | ~ (m1_subset_1 @ X4 @ (u1_struct_0 @ sk_D))
% 0.45/0.64          | ~ (r1_tmap_1 @ X3 @ X0 @ (k3_tmap_1 @ X2 @ X0 @ sk_D @ X3 @ X1) @ 
% 0.45/0.64               X4)
% 0.45/0.64          | (r1_tmap_1 @ sk_D @ X0 @ X1 @ X4)
% 0.45/0.64          | ~ (m1_subset_1 @ X4 @ (u1_struct_0 @ X3))
% 0.45/0.64          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ X0))
% 0.45/0.64          | ~ (v1_funct_1 @ X1)
% 0.45/0.64          | ~ (m1_pre_topc @ X3 @ X2)
% 0.45/0.64          | (v2_struct_0 @ X3)
% 0.45/0.64          | ~ (l1_pre_topc @ X2)
% 0.45/0.64          | ~ (v2_pre_topc @ X2)
% 0.45/0.64          | (v2_struct_0 @ X2))),
% 0.45/0.64      inference('sup-', [status(thm)], ['63', '65'])).
% 0.45/0.64  thf('67', plain, (((u1_struct_0 @ sk_D) = (k2_struct_0 @ sk_C))),
% 0.45/0.64      inference('demod', [status(thm)], ['61', '62'])).
% 0.45/0.64  thf('68', plain, (((u1_struct_0 @ sk_D) = (k2_struct_0 @ sk_C))),
% 0.45/0.64      inference('demod', [status(thm)], ['61', '62'])).
% 0.45/0.64  thf('69', plain,
% 0.45/0.64      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.45/0.64         (~ (m1_subset_1 @ X1 @ 
% 0.45/0.64             (k1_zfmisc_1 @ 
% 0.45/0.64              (k2_zfmisc_1 @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ X0))))
% 0.45/0.64          | (v2_struct_0 @ X0)
% 0.45/0.64          | ~ (v2_pre_topc @ X0)
% 0.45/0.64          | ~ (l1_pre_topc @ X0)
% 0.45/0.64          | (v2_struct_0 @ sk_D)
% 0.45/0.64          | ~ (m1_pre_topc @ sk_D @ X2)
% 0.45/0.64          | ~ (v1_tsep_1 @ X3 @ sk_D)
% 0.45/0.64          | ~ (m1_pre_topc @ X3 @ sk_D)
% 0.45/0.64          | ~ (m1_subset_1 @ X4 @ (k2_struct_0 @ sk_C))
% 0.45/0.64          | ~ (r1_tmap_1 @ X3 @ X0 @ (k3_tmap_1 @ X2 @ X0 @ sk_D @ X3 @ X1) @ 
% 0.45/0.64               X4)
% 0.45/0.64          | (r1_tmap_1 @ sk_D @ X0 @ X1 @ X4)
% 0.45/0.64          | ~ (m1_subset_1 @ X4 @ (u1_struct_0 @ X3))
% 0.45/0.64          | ~ (v1_funct_2 @ X1 @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ X0))
% 0.45/0.64          | ~ (v1_funct_1 @ X1)
% 0.45/0.64          | ~ (m1_pre_topc @ X3 @ X2)
% 0.45/0.64          | (v2_struct_0 @ X3)
% 0.45/0.64          | ~ (l1_pre_topc @ X2)
% 0.45/0.64          | ~ (v2_pre_topc @ X2)
% 0.45/0.64          | (v2_struct_0 @ X2))),
% 0.45/0.64      inference('demod', [status(thm)], ['66', '67', '68'])).
% 0.45/0.64  thf('70', plain,
% 0.45/0.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.64         ((v2_struct_0 @ X0)
% 0.45/0.64          | ~ (v2_pre_topc @ X0)
% 0.45/0.64          | ~ (l1_pre_topc @ X0)
% 0.45/0.64          | (v2_struct_0 @ X1)
% 0.45/0.64          | ~ (m1_pre_topc @ X1 @ X0)
% 0.45/0.64          | ~ (v1_funct_1 @ sk_E)
% 0.45/0.64          | ~ (v1_funct_2 @ sk_E @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))
% 0.45/0.64          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1))
% 0.45/0.64          | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X2)
% 0.45/0.64          | ~ (r1_tmap_1 @ X1 @ sk_B @ 
% 0.45/0.64               (k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E) @ X2)
% 0.45/0.64          | ~ (m1_subset_1 @ X2 @ (k2_struct_0 @ sk_C))
% 0.45/0.64          | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.45/0.64          | ~ (v1_tsep_1 @ X1 @ sk_D)
% 0.45/0.64          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.45/0.64          | (v2_struct_0 @ sk_D)
% 0.45/0.64          | ~ (l1_pre_topc @ sk_B)
% 0.45/0.64          | ~ (v2_pre_topc @ sk_B)
% 0.45/0.64          | (v2_struct_0 @ sk_B))),
% 0.45/0.64      inference('sup-', [status(thm)], ['58', '69'])).
% 0.45/0.64  thf('71', plain, ((v1_funct_1 @ sk_E)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('72', plain,
% 0.45/0.64      (![X5 : $i]:
% 0.45/0.64         (((k2_struct_0 @ X5) = (u1_struct_0 @ X5)) | ~ (l1_struct_0 @ X5))),
% 0.45/0.64      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.45/0.64  thf('73', plain,
% 0.45/0.64      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('74', plain,
% 0.45/0.64      (((v1_funct_2 @ sk_E @ (k2_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.45/0.64        | ~ (l1_struct_0 @ sk_D))),
% 0.45/0.64      inference('sup+', [status(thm)], ['72', '73'])).
% 0.45/0.64  thf('75', plain, ((l1_struct_0 @ sk_D)),
% 0.45/0.64      inference('sup-', [status(thm)], ['46', '47'])).
% 0.45/0.64  thf('76', plain,
% 0.45/0.64      ((v1_funct_2 @ sk_E @ (k2_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 0.45/0.64      inference('demod', [status(thm)], ['74', '75'])).
% 0.45/0.64  thf('77', plain, (((k2_struct_0 @ sk_D) = (k2_struct_0 @ sk_C))),
% 0.45/0.64      inference('demod', [status(thm)], ['52', '55'])).
% 0.45/0.64  thf('78', plain,
% 0.45/0.64      ((v1_funct_2 @ sk_E @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 0.45/0.64      inference('demod', [status(thm)], ['76', '77'])).
% 0.45/0.64  thf('79', plain, ((l1_pre_topc @ sk_B)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('80', plain, ((v2_pre_topc @ sk_B)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('81', plain,
% 0.45/0.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.64         ((v2_struct_0 @ X0)
% 0.45/0.64          | ~ (v2_pre_topc @ X0)
% 0.45/0.64          | ~ (l1_pre_topc @ X0)
% 0.45/0.64          | (v2_struct_0 @ X1)
% 0.45/0.64          | ~ (m1_pre_topc @ X1 @ X0)
% 0.45/0.64          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1))
% 0.45/0.64          | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X2)
% 0.45/0.64          | ~ (r1_tmap_1 @ X1 @ sk_B @ 
% 0.45/0.64               (k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E) @ X2)
% 0.45/0.64          | ~ (m1_subset_1 @ X2 @ (k2_struct_0 @ sk_C))
% 0.45/0.64          | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.45/0.64          | ~ (v1_tsep_1 @ X1 @ sk_D)
% 0.45/0.64          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.45/0.64          | (v2_struct_0 @ sk_D)
% 0.45/0.64          | (v2_struct_0 @ sk_B))),
% 0.45/0.64      inference('demod', [status(thm)], ['70', '71', '78', '79', '80'])).
% 0.45/0.64  thf('82', plain,
% 0.45/0.64      (((v2_struct_0 @ sk_B)
% 0.45/0.64        | (v2_struct_0 @ sk_D)
% 0.45/0.64        | ~ (m1_pre_topc @ sk_D @ sk_A)
% 0.45/0.64        | ~ (v1_tsep_1 @ sk_C @ sk_D)
% 0.45/0.64        | ~ (m1_pre_topc @ sk_C @ sk_D)
% 0.45/0.64        | ~ (m1_subset_1 @ sk_F @ (k2_struct_0 @ sk_C))
% 0.45/0.64        | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)
% 0.45/0.64        | ~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C))
% 0.45/0.64        | ~ (m1_pre_topc @ sk_C @ sk_A)
% 0.45/0.64        | (v2_struct_0 @ sk_C)
% 0.45/0.64        | ~ (l1_pre_topc @ sk_A)
% 0.45/0.64        | ~ (v2_pre_topc @ sk_A)
% 0.45/0.64        | (v2_struct_0 @ sk_A))),
% 0.45/0.64      inference('sup-', [status(thm)], ['3', '81'])).
% 0.45/0.64  thf('83', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('84', plain,
% 0.45/0.64      (![X5 : $i]:
% 0.45/0.64         (((k2_struct_0 @ X5) = (u1_struct_0 @ X5)) | ~ (l1_struct_0 @ X5))),
% 0.45/0.64      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.45/0.64  thf('85', plain,
% 0.45/0.64      (![X17 : $i]: ((m1_pre_topc @ X17 @ X17) | ~ (l1_pre_topc @ X17))),
% 0.45/0.64      inference('cnf', [status(esa)], [t2_tsep_1])).
% 0.45/0.64  thf(t1_tsep_1, axiom,
% 0.45/0.64    (![A:$i]:
% 0.45/0.64     ( ( l1_pre_topc @ A ) =>
% 0.45/0.64       ( ![B:$i]:
% 0.45/0.64         ( ( m1_pre_topc @ B @ A ) =>
% 0.45/0.64           ( m1_subset_1 @
% 0.45/0.64             ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.45/0.64  thf('86', plain,
% 0.45/0.64      (![X15 : $i, X16 : $i]:
% 0.45/0.64         (~ (m1_pre_topc @ X15 @ X16)
% 0.45/0.64          | (m1_subset_1 @ (u1_struct_0 @ X15) @ 
% 0.45/0.64             (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.45/0.64          | ~ (l1_pre_topc @ X16))),
% 0.45/0.64      inference('cnf', [status(esa)], [t1_tsep_1])).
% 0.45/0.64  thf('87', plain,
% 0.45/0.64      (![X0 : $i]:
% 0.45/0.64         (~ (l1_pre_topc @ X0)
% 0.45/0.64          | ~ (l1_pre_topc @ X0)
% 0.45/0.64          | (m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 0.45/0.64             (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.45/0.64      inference('sup-', [status(thm)], ['85', '86'])).
% 0.45/0.64  thf('88', plain,
% 0.45/0.64      (![X0 : $i]:
% 0.45/0.64         ((m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 0.45/0.64           (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.45/0.64          | ~ (l1_pre_topc @ X0))),
% 0.45/0.64      inference('simplify', [status(thm)], ['87'])).
% 0.45/0.64  thf('89', plain,
% 0.45/0.64      (![X0 : $i]:
% 0.45/0.64         ((m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 0.45/0.64           (k1_zfmisc_1 @ (k2_struct_0 @ X0)))
% 0.45/0.64          | ~ (l1_struct_0 @ X0)
% 0.45/0.64          | ~ (l1_pre_topc @ X0))),
% 0.45/0.64      inference('sup+', [status(thm)], ['84', '88'])).
% 0.45/0.64  thf('90', plain, (![X6 : $i]: ((l1_struct_0 @ X6) | ~ (l1_pre_topc @ X6))),
% 0.45/0.64      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.45/0.64  thf('91', plain,
% 0.45/0.64      (![X0 : $i]:
% 0.45/0.64         (~ (l1_pre_topc @ X0)
% 0.45/0.64          | (m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 0.45/0.64             (k1_zfmisc_1 @ (k2_struct_0 @ X0))))),
% 0.45/0.64      inference('clc', [status(thm)], ['89', '90'])).
% 0.45/0.64  thf('92', plain, (((u1_struct_0 @ sk_D) = (k2_struct_0 @ sk_C))),
% 0.45/0.64      inference('demod', [status(thm)], ['61', '62'])).
% 0.45/0.64  thf(t16_tsep_1, axiom,
% 0.45/0.64    (![A:$i]:
% 0.45/0.64     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.45/0.64       ( ![B:$i]:
% 0.45/0.64         ( ( m1_pre_topc @ B @ A ) =>
% 0.45/0.64           ( ![C:$i]:
% 0.45/0.64             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.45/0.64               ( ( ( C ) = ( u1_struct_0 @ B ) ) =>
% 0.45/0.64                 ( ( ( v1_tsep_1 @ B @ A ) & ( m1_pre_topc @ B @ A ) ) <=>
% 0.45/0.64                   ( v3_pre_topc @ C @ A ) ) ) ) ) ) ) ))).
% 0.45/0.64  thf('93', plain,
% 0.45/0.64      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.45/0.64         (~ (m1_pre_topc @ X12 @ X13)
% 0.45/0.64          | ((X14) != (u1_struct_0 @ X12))
% 0.45/0.64          | ~ (v3_pre_topc @ X14 @ X13)
% 0.45/0.64          | (v1_tsep_1 @ X12 @ X13)
% 0.45/0.64          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.45/0.64          | ~ (l1_pre_topc @ X13)
% 0.45/0.64          | ~ (v2_pre_topc @ X13))),
% 0.45/0.64      inference('cnf', [status(esa)], [t16_tsep_1])).
% 0.45/0.64  thf('94', plain,
% 0.45/0.64      (![X12 : $i, X13 : $i]:
% 0.45/0.64         (~ (v2_pre_topc @ X13)
% 0.45/0.64          | ~ (l1_pre_topc @ X13)
% 0.45/0.64          | ~ (m1_subset_1 @ (u1_struct_0 @ X12) @ 
% 0.45/0.64               (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.45/0.64          | (v1_tsep_1 @ X12 @ X13)
% 0.45/0.64          | ~ (v3_pre_topc @ (u1_struct_0 @ X12) @ X13)
% 0.45/0.64          | ~ (m1_pre_topc @ X12 @ X13))),
% 0.45/0.64      inference('simplify', [status(thm)], ['93'])).
% 0.45/0.64  thf('95', plain,
% 0.45/0.64      (![X0 : $i]:
% 0.45/0.64         (~ (m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 0.45/0.64             (k1_zfmisc_1 @ (k2_struct_0 @ sk_C)))
% 0.45/0.64          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.45/0.64          | ~ (v3_pre_topc @ (u1_struct_0 @ X0) @ sk_D)
% 0.45/0.64          | (v1_tsep_1 @ X0 @ sk_D)
% 0.45/0.64          | ~ (l1_pre_topc @ sk_D)
% 0.45/0.64          | ~ (v2_pre_topc @ sk_D))),
% 0.45/0.64      inference('sup-', [status(thm)], ['92', '94'])).
% 0.45/0.64  thf('96', plain, ((l1_pre_topc @ sk_D)),
% 0.45/0.64      inference('demod', [status(thm)], ['15', '16'])).
% 0.45/0.64  thf('97', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf(cc1_pre_topc, axiom,
% 0.45/0.64    (![A:$i]:
% 0.45/0.64     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.45/0.64       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( v2_pre_topc @ B ) ) ) ))).
% 0.45/0.64  thf('98', plain,
% 0.45/0.64      (![X3 : $i, X4 : $i]:
% 0.45/0.64         (~ (m1_pre_topc @ X3 @ X4)
% 0.45/0.64          | (v2_pre_topc @ X3)
% 0.45/0.64          | ~ (l1_pre_topc @ X4)
% 0.45/0.64          | ~ (v2_pre_topc @ X4))),
% 0.45/0.64      inference('cnf', [status(esa)], [cc1_pre_topc])).
% 0.45/0.64  thf('99', plain,
% 0.45/0.64      ((~ (v2_pre_topc @ sk_A) | ~ (l1_pre_topc @ sk_A) | (v2_pre_topc @ sk_D))),
% 0.45/0.64      inference('sup-', [status(thm)], ['97', '98'])).
% 0.45/0.64  thf('100', plain, ((v2_pre_topc @ sk_A)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('101', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('102', plain, ((v2_pre_topc @ sk_D)),
% 0.45/0.64      inference('demod', [status(thm)], ['99', '100', '101'])).
% 0.45/0.64  thf('103', plain,
% 0.45/0.64      (![X0 : $i]:
% 0.45/0.64         (~ (m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 0.45/0.64             (k1_zfmisc_1 @ (k2_struct_0 @ sk_C)))
% 0.45/0.64          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.45/0.64          | ~ (v3_pre_topc @ (u1_struct_0 @ X0) @ sk_D)
% 0.45/0.64          | (v1_tsep_1 @ X0 @ sk_D))),
% 0.45/0.64      inference('demod', [status(thm)], ['95', '96', '102'])).
% 0.45/0.64  thf('104', plain,
% 0.45/0.64      ((~ (l1_pre_topc @ sk_C)
% 0.45/0.64        | (v1_tsep_1 @ sk_C @ sk_D)
% 0.45/0.64        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_C) @ sk_D)
% 0.45/0.64        | ~ (m1_pre_topc @ sk_C @ sk_D))),
% 0.45/0.64      inference('sup-', [status(thm)], ['91', '103'])).
% 0.45/0.64  thf('105', plain, ((l1_pre_topc @ sk_C)),
% 0.45/0.64      inference('demod', [status(thm)], ['21', '22'])).
% 0.45/0.64  thf('106', plain, (((k2_struct_0 @ sk_C) = (u1_struct_0 @ sk_C))),
% 0.45/0.64      inference('demod', [status(thm)], ['49', '56'])).
% 0.45/0.64  thf('107', plain, (((k2_struct_0 @ sk_D) = (k2_struct_0 @ sk_C))),
% 0.45/0.64      inference('demod', [status(thm)], ['52', '55'])).
% 0.45/0.64  thf(fc10_tops_1, axiom,
% 0.45/0.64    (![A:$i]:
% 0.45/0.64     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.45/0.64       ( v3_pre_topc @ ( k2_struct_0 @ A ) @ A ) ))).
% 0.45/0.64  thf('108', plain,
% 0.45/0.64      (![X11 : $i]:
% 0.45/0.64         ((v3_pre_topc @ (k2_struct_0 @ X11) @ X11)
% 0.45/0.64          | ~ (l1_pre_topc @ X11)
% 0.45/0.64          | ~ (v2_pre_topc @ X11))),
% 0.45/0.64      inference('cnf', [status(esa)], [fc10_tops_1])).
% 0.45/0.64  thf('109', plain,
% 0.45/0.64      (((v3_pre_topc @ (k2_struct_0 @ sk_C) @ sk_D)
% 0.45/0.64        | ~ (v2_pre_topc @ sk_D)
% 0.45/0.64        | ~ (l1_pre_topc @ sk_D))),
% 0.45/0.64      inference('sup+', [status(thm)], ['107', '108'])).
% 0.45/0.64  thf('110', plain, ((v2_pre_topc @ sk_D)),
% 0.45/0.64      inference('demod', [status(thm)], ['99', '100', '101'])).
% 0.45/0.64  thf('111', plain, ((l1_pre_topc @ sk_D)),
% 0.45/0.64      inference('demod', [status(thm)], ['15', '16'])).
% 0.45/0.64  thf('112', plain, ((v3_pre_topc @ (k2_struct_0 @ sk_C) @ sk_D)),
% 0.45/0.64      inference('demod', [status(thm)], ['109', '110', '111'])).
% 0.45/0.64  thf('113', plain,
% 0.45/0.64      (((g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) = (sk_D))),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('114', plain,
% 0.45/0.64      (![X0 : $i]:
% 0.45/0.64         ((m1_pre_topc @ X0 @ 
% 0.45/0.64           (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.45/0.64          | ~ (l1_pre_topc @ X0))),
% 0.45/0.64      inference('simplify', [status(thm)], ['8'])).
% 0.45/0.64  thf('115', plain, (((m1_pre_topc @ sk_C @ sk_D) | ~ (l1_pre_topc @ sk_C))),
% 0.45/0.64      inference('sup+', [status(thm)], ['113', '114'])).
% 0.45/0.64  thf('116', plain, ((l1_pre_topc @ sk_C)),
% 0.45/0.64      inference('demod', [status(thm)], ['21', '22'])).
% 0.45/0.64  thf('117', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 0.45/0.64      inference('demod', [status(thm)], ['115', '116'])).
% 0.45/0.64  thf('118', plain, ((v1_tsep_1 @ sk_C @ sk_D)),
% 0.45/0.64      inference('demod', [status(thm)], ['104', '105', '106', '112', '117'])).
% 0.45/0.64  thf('119', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 0.45/0.64      inference('demod', [status(thm)], ['115', '116'])).
% 0.45/0.64  thf('120', plain,
% 0.45/0.64      (![X5 : $i]:
% 0.45/0.64         (((k2_struct_0 @ X5) = (u1_struct_0 @ X5)) | ~ (l1_struct_0 @ X5))),
% 0.45/0.64      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.45/0.64  thf('121', plain, ((m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_C))),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('122', plain, (((sk_F) = (sk_G))),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('123', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C))),
% 0.45/0.64      inference('demod', [status(thm)], ['121', '122'])).
% 0.45/0.64  thf('124', plain,
% 0.45/0.64      (((m1_subset_1 @ sk_F @ (k2_struct_0 @ sk_C)) | ~ (l1_struct_0 @ sk_C))),
% 0.45/0.64      inference('sup+', [status(thm)], ['120', '123'])).
% 0.45/0.64  thf('125', plain, ((l1_struct_0 @ sk_C)),
% 0.45/0.64      inference('sup-', [status(thm)], ['53', '54'])).
% 0.45/0.64  thf('126', plain, ((m1_subset_1 @ sk_F @ (k2_struct_0 @ sk_C))),
% 0.45/0.64      inference('demod', [status(thm)], ['124', '125'])).
% 0.45/0.64  thf('127', plain, (((k2_struct_0 @ sk_C) = (u1_struct_0 @ sk_C))),
% 0.45/0.64      inference('demod', [status(thm)], ['49', '56'])).
% 0.45/0.64  thf('128', plain, ((m1_subset_1 @ sk_F @ (k2_struct_0 @ sk_C))),
% 0.45/0.64      inference('demod', [status(thm)], ['124', '125'])).
% 0.45/0.64  thf('129', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('130', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('131', plain, ((v2_pre_topc @ sk_A)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('132', plain,
% 0.45/0.64      (((v2_struct_0 @ sk_B)
% 0.45/0.64        | (v2_struct_0 @ sk_D)
% 0.45/0.64        | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)
% 0.45/0.64        | (v2_struct_0 @ sk_C)
% 0.45/0.64        | (v2_struct_0 @ sk_A))),
% 0.45/0.64      inference('demod', [status(thm)],
% 0.45/0.64                ['82', '83', '118', '119', '126', '127', '128', '129', '130', 
% 0.45/0.64                 '131'])).
% 0.45/0.64  thf('133', plain, (~ (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('134', plain,
% 0.45/0.64      (((v2_struct_0 @ sk_A)
% 0.45/0.64        | (v2_struct_0 @ sk_C)
% 0.45/0.64        | (v2_struct_0 @ sk_D)
% 0.45/0.64        | (v2_struct_0 @ sk_B))),
% 0.45/0.64      inference('sup-', [status(thm)], ['132', '133'])).
% 0.45/0.64  thf('135', plain, (~ (v2_struct_0 @ sk_D)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('136', plain,
% 0.45/0.64      (((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_A))),
% 0.45/0.64      inference('sup-', [status(thm)], ['134', '135'])).
% 0.45/0.64  thf('137', plain, (~ (v2_struct_0 @ sk_B)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('138', plain, (((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_C))),
% 0.45/0.64      inference('clc', [status(thm)], ['136', '137'])).
% 0.45/0.64  thf('139', plain, (~ (v2_struct_0 @ sk_A)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('140', plain, ((v2_struct_0 @ sk_C)),
% 0.45/0.64      inference('clc', [status(thm)], ['138', '139'])).
% 0.45/0.64  thf('141', plain, ($false), inference('demod', [status(thm)], ['0', '140'])).
% 0.45/0.64  
% 0.45/0.64  % SZS output end Refutation
% 0.45/0.64  
% 0.45/0.64  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
