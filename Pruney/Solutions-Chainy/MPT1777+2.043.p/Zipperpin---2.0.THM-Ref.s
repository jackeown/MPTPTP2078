%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.bHF98JTpkU

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:10:33 EST 2020

% Result     : Theorem 0.70s
% Output     : Refutation 0.70s
% Verified   : 
% Statistics : Number of formulae       :  223 (3696 expanded)
%              Number of leaves         :   42 (1057 expanded)
%              Depth                    :   28
%              Number of atoms          : 1945 (107098 expanded)
%              Number of equality atoms :   52 (3016 expanded)
%              Maximal formula depth    :   29 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k3_tmap_1_type,type,(
    k3_tmap_1: $i > $i > $i > $i > $i > $i )).

thf(k1_tsep_1_type,type,(
    k1_tsep_1: $i > $i > $i > $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_tsep_1_type,type,(
    v1_tsep_1: $i > $i > $o )).

thf(r1_tmap_1_type,type,(
    r1_tmap_1: $i > $i > $i > $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(sk_G_type,type,(
    sk_G: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(g1_pre_topc_type,type,(
    g1_pre_topc: $i > $i > $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

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

thf(t2_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( m1_pre_topc @ A @ A ) ) )).

thf('5',plain,(
    ! [X22: $i] :
      ( ( m1_pre_topc @ X22 @ X22 )
      | ~ ( l1_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('6',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) )
    = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t59_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) )
         => ( m1_pre_topc @ B @ A ) ) ) )).

thf('7',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( m1_pre_topc @ X9 @ ( g1_pre_topc @ ( u1_struct_0 @ X10 ) @ ( u1_pre_topc @ X10 ) ) )
      | ( m1_pre_topc @ X9 @ X10 )
      | ~ ( l1_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[t59_pre_topc])).

thf('8',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_D )
      | ~ ( l1_pre_topc @ sk_C )
      | ( m1_pre_topc @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('10',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( m1_pre_topc @ X7 @ X8 )
      | ( l1_pre_topc @ X7 )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('11',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_C ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( m1_pre_topc @ X0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['8','13'])).

thf('15',plain,
    ( ~ ( l1_pre_topc @ sk_D )
    | ( m1_pre_topc @ sk_D @ sk_C ) ),
    inference('sup-',[status(thm)],['5','14'])).

thf('16',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( m1_pre_topc @ X7 @ X8 )
      | ( l1_pre_topc @ X7 )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('18',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_D ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,(
    m1_pre_topc @ sk_D @ sk_C ),
    inference(demod,[status(thm)],['15','20'])).

thf(t35_borsuk_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( r1_tarski @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) )).

thf('22',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( m1_pre_topc @ X23 @ X24 )
      | ( r1_tarski @ ( u1_struct_0 @ X23 ) @ ( u1_struct_0 @ X24 ) )
      | ~ ( l1_pre_topc @ X24 ) ) ),
    inference(cnf,[status(esa)],[t35_borsuk_1])).

thf('23',plain,
    ( ~ ( l1_pre_topc @ sk_C )
    | ( r1_tarski @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['11','12'])).

thf('25',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['23','24'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('26',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('27',plain,
    ( ~ ( r1_tarski @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D ) )
    | ( ( u1_struct_0 @ sk_C )
      = ( u1_struct_0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t22_tsep_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( m1_pre_topc @ B @ A ) )
         => ! [C: $i] :
              ( ( ~ ( v2_struct_0 @ C )
                & ( m1_pre_topc @ C @ A ) )
             => ( m1_pre_topc @ B @ ( k1_tsep_1 @ A @ B @ C ) ) ) ) ) )).

thf('30',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( v2_struct_0 @ X17 )
      | ~ ( m1_pre_topc @ X17 @ X18 )
      | ( m1_pre_topc @ X17 @ ( k1_tsep_1 @ X18 @ X17 @ X19 ) )
      | ~ ( m1_pre_topc @ X19 @ X18 )
      | ( v2_struct_0 @ X19 )
      | ~ ( l1_pre_topc @ X18 )
      | ~ ( v2_pre_topc @ X18 )
      | ( v2_struct_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t22_tsep_1])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( m1_pre_topc @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_C @ X0 ) )
      | ( v2_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( m1_pre_topc @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_C @ X0 ) )
      | ( v2_struct_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['31','32','33'])).

thf('35',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( m1_pre_topc @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_C ) )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['28','34'])).

thf('36',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_pre_topc @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_C ) )
    | ( v2_struct_0 @ sk_C ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t25_tmap_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( m1_pre_topc @ B @ A ) )
         => ( ( k1_tsep_1 @ A @ B @ B )
            = ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) )).

thf('38',plain,(
    ! [X20: $i,X21: $i] :
      ( ( v2_struct_0 @ X20 )
      | ~ ( m1_pre_topc @ X20 @ X21 )
      | ( ( k1_tsep_1 @ X21 @ X20 @ X20 )
        = ( g1_pre_topc @ ( u1_struct_0 @ X20 ) @ ( u1_pre_topc @ X20 ) ) )
      | ~ ( l1_pre_topc @ X21 )
      | ~ ( v2_pre_topc @ X21 )
      | ( v2_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t25_tmap_1])).

thf('39',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tsep_1 @ sk_A @ sk_C @ sk_C )
      = ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) ) )
    | ( v2_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) )
    = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k1_tsep_1 @ sk_A @ sk_C @ sk_C )
      = sk_D )
    | ( v2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['39','40','41','42'])).

thf('44',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( ( k1_tsep_1 @ sk_A @ sk_C @ sk_C )
      = sk_D ) ),
    inference(clc,[status(thm)],['43','44'])).

thf('46',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ( k1_tsep_1 @ sk_A @ sk_C @ sk_C )
    = sk_D ),
    inference(clc,[status(thm)],['45','46'])).

thf('48',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_pre_topc @ sk_C @ sk_D )
    | ( v2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['36','47'])).

thf('49',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( m1_pre_topc @ sk_C @ sk_D ) ),
    inference(clc,[status(thm)],['48','49'])).

thf('51',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(clc,[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( m1_pre_topc @ X23 @ X24 )
      | ( r1_tarski @ ( u1_struct_0 @ X23 ) @ ( u1_struct_0 @ X24 ) )
      | ~ ( l1_pre_topc @ X24 ) ) ),
    inference(cnf,[status(esa)],[t35_borsuk_1])).

thf('54',plain,
    ( ~ ( l1_pre_topc @ sk_D )
    | ( r1_tarski @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['18','19'])).

thf('56',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,
    ( ( u1_struct_0 @ sk_C )
    = ( u1_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['27','56'])).

thf('58',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['4','57'])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('59',plain,(
    ! [X5: $i] :
      ( ( ( k2_struct_0 @ X5 )
        = ( u1_struct_0 @ X5 ) )
      | ~ ( l1_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('60',plain,
    ( ( u1_struct_0 @ sk_C )
    = ( u1_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['27','56'])).

thf('61',plain,
    ( ( ( u1_struct_0 @ sk_C )
      = ( k2_struct_0 @ sk_D ) )
    | ~ ( l1_struct_0 @ sk_D ) ),
    inference('sup+',[status(thm)],['59','60'])).

thf('62',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['18','19'])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('63',plain,(
    ! [X6: $i] :
      ( ( l1_struct_0 @ X6 )
      | ~ ( l1_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('64',plain,(
    l1_struct_0 @ sk_D ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,
    ( ( u1_struct_0 @ sk_C )
    = ( k2_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['61','64'])).

thf('66',plain,(
    ! [X5: $i] :
      ( ( ( k2_struct_0 @ X5 )
        = ( u1_struct_0 @ X5 ) )
      | ~ ( l1_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('67',plain,
    ( ( u1_struct_0 @ sk_C )
    = ( k2_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['61','64'])).

thf('68',plain,
    ( ( ( k2_struct_0 @ sk_C )
      = ( k2_struct_0 @ sk_D ) )
    | ~ ( l1_struct_0 @ sk_C ) ),
    inference('sup+',[status(thm)],['66','67'])).

thf('69',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['11','12'])).

thf('70',plain,(
    ! [X6: $i] :
      ( ( l1_struct_0 @ X6 )
      | ~ ( l1_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('71',plain,(
    l1_struct_0 @ sk_C ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,
    ( ( k2_struct_0 @ sk_C )
    = ( k2_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['68','71'])).

thf('73',plain,
    ( ( u1_struct_0 @ sk_C )
    = ( k2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['65','72'])).

thf('74',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['58','73'])).

thf('75',plain,
    ( ( u1_struct_0 @ sk_C )
    = ( u1_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['27','56'])).

thf('76',plain,
    ( ( u1_struct_0 @ sk_C )
    = ( k2_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['61','64'])).

thf('77',plain,
    ( ( k2_struct_0 @ sk_D )
    = ( u1_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['75','76'])).

thf('78',plain,
    ( ( k2_struct_0 @ sk_C )
    = ( k2_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['68','71'])).

thf('79',plain,
    ( ( k2_struct_0 @ sk_C )
    = ( u1_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['77','78'])).

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

thf('80',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ( v2_struct_0 @ X28 )
      | ~ ( v2_pre_topc @ X28 )
      | ~ ( l1_pre_topc @ X28 )
      | ( v2_struct_0 @ X29 )
      | ~ ( m1_pre_topc @ X29 @ X30 )
      | ~ ( v1_tsep_1 @ X31 @ X29 )
      | ~ ( m1_pre_topc @ X31 @ X29 )
      | ~ ( m1_subset_1 @ X32 @ ( u1_struct_0 @ X29 ) )
      | ( X32 != X33 )
      | ~ ( r1_tmap_1 @ X31 @ X28 @ ( k3_tmap_1 @ X30 @ X28 @ X29 @ X31 @ X34 ) @ X33 )
      | ( r1_tmap_1 @ X29 @ X28 @ X34 @ X32 )
      | ~ ( m1_subset_1 @ X33 @ ( u1_struct_0 @ X31 ) )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X29 ) @ ( u1_struct_0 @ X28 ) ) ) )
      | ~ ( v1_funct_2 @ X34 @ ( u1_struct_0 @ X29 ) @ ( u1_struct_0 @ X28 ) )
      | ~ ( v1_funct_1 @ X34 )
      | ~ ( m1_pre_topc @ X31 @ X30 )
      | ( v2_struct_0 @ X31 )
      | ~ ( l1_pre_topc @ X30 )
      | ~ ( v2_pre_topc @ X30 )
      | ( v2_struct_0 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t86_tmap_1])).

thf('81',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i,X33: $i,X34: $i] :
      ( ( v2_struct_0 @ X30 )
      | ~ ( v2_pre_topc @ X30 )
      | ~ ( l1_pre_topc @ X30 )
      | ( v2_struct_0 @ X31 )
      | ~ ( m1_pre_topc @ X31 @ X30 )
      | ~ ( v1_funct_1 @ X34 )
      | ~ ( v1_funct_2 @ X34 @ ( u1_struct_0 @ X29 ) @ ( u1_struct_0 @ X28 ) )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X29 ) @ ( u1_struct_0 @ X28 ) ) ) )
      | ~ ( m1_subset_1 @ X33 @ ( u1_struct_0 @ X31 ) )
      | ( r1_tmap_1 @ X29 @ X28 @ X34 @ X33 )
      | ~ ( r1_tmap_1 @ X31 @ X28 @ ( k3_tmap_1 @ X30 @ X28 @ X29 @ X31 @ X34 ) @ X33 )
      | ~ ( m1_subset_1 @ X33 @ ( u1_struct_0 @ X29 ) )
      | ~ ( m1_pre_topc @ X31 @ X29 )
      | ~ ( v1_tsep_1 @ X31 @ X29 )
      | ~ ( m1_pre_topc @ X29 @ X30 )
      | ( v2_struct_0 @ X29 )
      | ~ ( l1_pre_topc @ X28 )
      | ~ ( v2_pre_topc @ X28 )
      | ( v2_struct_0 @ X28 ) ) ),
    inference(simplify,[status(thm)],['80'])).

thf('82',plain,(
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
    inference('sup-',[status(thm)],['79','81'])).

thf('83',plain,
    ( ( k2_struct_0 @ sk_C )
    = ( u1_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['77','78'])).

thf('84',plain,
    ( ( k2_struct_0 @ sk_C )
    = ( u1_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['77','78'])).

thf('85',plain,(
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
    inference(demod,[status(thm)],['82','83','84'])).

thf('86',plain,(
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
    inference('sup-',[status(thm)],['74','85'])).

thf('87',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,
    ( ( u1_struct_0 @ sk_C )
    = ( u1_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['27','56'])).

thf('90',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['88','89'])).

thf('91',plain,
    ( ( u1_struct_0 @ sk_C )
    = ( k2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['65','72'])).

thf('92',plain,(
    v1_funct_2 @ sk_E @ ( k2_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['90','91'])).

thf('93',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
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
    inference(demod,[status(thm)],['86','87','92','93','94'])).

thf('96',plain,
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
    inference('sup-',[status(thm)],['3','95'])).

thf('97',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
    ! [X5: $i] :
      ( ( ( k2_struct_0 @ X5 )
        = ( u1_struct_0 @ X5 ) )
      | ~ ( l1_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('99',plain,(
    ! [X22: $i] :
      ( ( m1_pre_topc @ X22 @ X22 )
      | ~ ( l1_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf(t1_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( m1_subset_1 @ ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('100',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( m1_pre_topc @ X15 @ X16 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X15 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( l1_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('101',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['101'])).

thf('103',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_struct_0 @ X0 ) ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup+',[status(thm)],['98','102'])).

thf('104',plain,(
    ! [X6: $i] :
      ( ( l1_struct_0 @ X6 )
      | ~ ( l1_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('105',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_struct_0 @ X0 ) ) ) ) ),
    inference(clc,[status(thm)],['103','104'])).

thf('106',plain,
    ( ( u1_struct_0 @ sk_C )
    = ( u1_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['27','56'])).

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

thf('107',plain,(
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

thf('108',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v2_pre_topc @ X13 )
      | ~ ( l1_pre_topc @ X13 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X12 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ( v1_tsep_1 @ X12 @ X13 )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ X12 ) @ X13 )
      | ~ ( m1_pre_topc @ X12 @ X13 ) ) ),
    inference(simplify,[status(thm)],['107'])).

thf('109',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ sk_D )
      | ( v1_tsep_1 @ X0 @ sk_D )
      | ~ ( l1_pre_topc @ sk_D )
      | ~ ( v2_pre_topc @ sk_D ) ) ),
    inference('sup-',[status(thm)],['106','108'])).

thf('110',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['18','19'])).

thf('111',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( v2_pre_topc @ B ) ) ) )).

thf('112',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_pre_topc @ X3 @ X4 )
      | ( v2_pre_topc @ X3 )
      | ~ ( l1_pre_topc @ X4 )
      | ~ ( v2_pre_topc @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc1_pre_topc])).

thf('113',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_pre_topc @ sk_D ) ),
    inference('sup-',[status(thm)],['111','112'])).

thf('114',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,(
    v2_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['113','114','115'])).

thf('117',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ sk_D )
      | ( v1_tsep_1 @ X0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['109','110','116'])).

thf('118',plain,
    ( ( u1_struct_0 @ sk_C )
    = ( k2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['65','72'])).

thf('119',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_C ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ sk_D )
      | ( v1_tsep_1 @ X0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['117','118'])).

thf('120',plain,
    ( ~ ( l1_pre_topc @ sk_C )
    | ( v1_tsep_1 @ sk_C @ sk_D )
    | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_C ) @ sk_D )
    | ~ ( m1_pre_topc @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['105','119'])).

thf('121',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['11','12'])).

thf('122',plain,
    ( ( u1_struct_0 @ sk_C )
    = ( k2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['65','72'])).

thf('123',plain,
    ( ( u1_struct_0 @ sk_C )
    = ( u1_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['27','56'])).

thf('124',plain,(
    ! [X22: $i] :
      ( ( m1_pre_topc @ X22 @ X22 )
      | ~ ( l1_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('125',plain,(
    ! [X22: $i] :
      ( ( m1_pre_topc @ X22 @ X22 )
      | ~ ( l1_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf(fc10_tops_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( v3_pre_topc @ ( k2_struct_0 @ A ) @ A ) ) )).

thf('126',plain,(
    ! [X11: $i] :
      ( ( v3_pre_topc @ ( k2_struct_0 @ X11 ) @ X11 )
      | ~ ( l1_pre_topc @ X11 )
      | ~ ( v2_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[fc10_tops_1])).

thf('127',plain,(
    ! [X5: $i] :
      ( ( ( k2_struct_0 @ X5 )
        = ( u1_struct_0 @ X5 ) )
      | ~ ( l1_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('128',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['101'])).

thf('129',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v2_pre_topc @ X13 )
      | ~ ( l1_pre_topc @ X13 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X12 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ( v1_tsep_1 @ X12 @ X13 )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ X12 ) @ X13 )
      | ~ ( m1_pre_topc @ X12 @ X13 ) ) ),
    inference(simplify,[status(thm)],['107'])).

thf('130',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X0 )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 )
      | ( v1_tsep_1 @ X0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['128','129'])).

thf('131',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ( v1_tsep_1 @ X0 @ X0 )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['130'])).

thf('132',plain,(
    ! [X0: $i] :
      ( ~ ( v3_pre_topc @ ( k2_struct_0 @ X0 ) @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X0 )
      | ( v1_tsep_1 @ X0 @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['127','131'])).

thf('133',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v1_tsep_1 @ X0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['126','132'])).

thf('134',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X0 )
      | ( v1_tsep_1 @ X0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['133'])).

thf('135',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v1_tsep_1 @ X0 @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['125','134'])).

thf('136',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( v1_tsep_1 @ X0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['135'])).

thf('137',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['101'])).

thf('138',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_pre_topc @ X12 @ X13 )
      | ( X14
       != ( u1_struct_0 @ X12 ) )
      | ~ ( v1_tsep_1 @ X12 @ X13 )
      | ~ ( m1_pre_topc @ X12 @ X13 )
      | ( v3_pre_topc @ X14 @ X13 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ~ ( l1_pre_topc @ X13 )
      | ~ ( v2_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[t16_tsep_1])).

thf('139',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v2_pre_topc @ X13 )
      | ~ ( l1_pre_topc @ X13 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X12 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ( v3_pre_topc @ ( u1_struct_0 @ X12 ) @ X13 )
      | ~ ( v1_tsep_1 @ X12 @ X13 )
      | ~ ( m1_pre_topc @ X12 @ X13 ) ) ),
    inference(simplify,[status(thm)],['138'])).

thf('140',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X0 )
      | ~ ( v1_tsep_1 @ X0 @ X0 )
      | ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['137','139'])).

thf('141',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( v1_tsep_1 @ X0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['140'])).

thf('142',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X0 )
      | ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['136','141'])).

thf('143',plain,(
    ! [X0: $i] :
      ( ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['142'])).

thf('144',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['124','143'])).

thf('145',plain,(
    ! [X0: $i] :
      ( ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['144'])).

thf('146',plain,
    ( ( v3_pre_topc @ ( u1_struct_0 @ sk_C ) @ sk_D )
    | ~ ( l1_pre_topc @ sk_D )
    | ~ ( v2_pre_topc @ sk_D )
    | ~ ( l1_struct_0 @ sk_D ) ),
    inference('sup+',[status(thm)],['123','145'])).

thf('147',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['18','19'])).

thf('148',plain,(
    v2_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['113','114','115'])).

thf('149',plain,(
    l1_struct_0 @ sk_D ),
    inference('sup-',[status(thm)],['62','63'])).

thf('150',plain,(
    v3_pre_topc @ ( u1_struct_0 @ sk_C ) @ sk_D ),
    inference(demod,[status(thm)],['146','147','148','149'])).

thf('151',plain,
    ( ( u1_struct_0 @ sk_C )
    = ( k2_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['61','64'])).

thf('152',plain,(
    v3_pre_topc @ ( k2_struct_0 @ sk_D ) @ sk_D ),
    inference(demod,[status(thm)],['150','151'])).

thf('153',plain,
    ( ( k2_struct_0 @ sk_C )
    = ( k2_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['68','71'])).

thf('154',plain,(
    v3_pre_topc @ ( k2_struct_0 @ sk_C ) @ sk_D ),
    inference(demod,[status(thm)],['152','153'])).

thf('155',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(clc,[status(thm)],['50','51'])).

thf('156',plain,(
    v1_tsep_1 @ sk_C @ sk_D ),
    inference(demod,[status(thm)],['120','121','122','154','155'])).

thf('157',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(clc,[status(thm)],['50','51'])).

thf('158',plain,(
    ! [X5: $i] :
      ( ( ( k2_struct_0 @ X5 )
        = ( u1_struct_0 @ X5 ) )
      | ~ ( l1_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('159',plain,(
    m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('160',plain,(
    sk_F = sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('161',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['159','160'])).

thf('162',plain,
    ( ( m1_subset_1 @ sk_F @ ( k2_struct_0 @ sk_C ) )
    | ~ ( l1_struct_0 @ sk_C ) ),
    inference('sup+',[status(thm)],['158','161'])).

thf('163',plain,(
    l1_struct_0 @ sk_C ),
    inference('sup-',[status(thm)],['69','70'])).

thf('164',plain,(
    m1_subset_1 @ sk_F @ ( k2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['162','163'])).

thf('165',plain,
    ( ( u1_struct_0 @ sk_C )
    = ( k2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['65','72'])).

thf('166',plain,(
    m1_subset_1 @ sk_F @ ( k2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['162','163'])).

thf('167',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('168',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('169',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('170',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['96','97','156','157','164','165','166','167','168','169'])).

thf('171',plain,(
    ~ ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('172',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['170','171'])).

thf('173',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('174',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['172','173'])).

thf('175',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('176',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C ) ),
    inference(clc,[status(thm)],['174','175'])).

thf('177',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('178',plain,(
    v2_struct_0 @ sk_C ),
    inference(clc,[status(thm)],['176','177'])).

thf('179',plain,(
    $false ),
    inference(demod,[status(thm)],['0','178'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.bHF98JTpkU
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:07:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.70/0.91  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.70/0.91  % Solved by: fo/fo7.sh
% 0.70/0.91  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.70/0.91  % done 903 iterations in 0.446s
% 0.70/0.91  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.70/0.91  % SZS output start Refutation
% 0.70/0.91  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.70/0.91  thf(k3_tmap_1_type, type, k3_tmap_1: $i > $i > $i > $i > $i > $i).
% 0.70/0.91  thf(k1_tsep_1_type, type, k1_tsep_1: $i > $i > $i > $i).
% 0.70/0.91  thf(sk_F_type, type, sk_F: $i).
% 0.70/0.91  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.70/0.91  thf(v1_tsep_1_type, type, v1_tsep_1: $i > $i > $o).
% 0.70/0.91  thf(r1_tmap_1_type, type, r1_tmap_1: $i > $i > $i > $i > $o).
% 0.70/0.91  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.70/0.91  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 0.70/0.91  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.70/0.91  thf(sk_D_type, type, sk_D: $i).
% 0.70/0.91  thf(sk_C_type, type, sk_C: $i).
% 0.70/0.91  thf(sk_E_type, type, sk_E: $i).
% 0.70/0.91  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.70/0.91  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.70/0.91  thf(sk_G_type, type, sk_G: $i).
% 0.70/0.91  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.70/0.91  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.70/0.91  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.70/0.91  thf(sk_A_type, type, sk_A: $i).
% 0.70/0.91  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.70/0.91  thf(sk_B_type, type, sk_B: $i).
% 0.70/0.91  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.70/0.91  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.70/0.91  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.70/0.91  thf(g1_pre_topc_type, type, g1_pre_topc: $i > $i > $i).
% 0.70/0.91  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.70/0.91  thf(t88_tmap_1, conjecture,
% 0.70/0.91    (![A:$i]:
% 0.70/0.91     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.70/0.91       ( ![B:$i]:
% 0.70/0.91         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.70/0.91             ( l1_pre_topc @ B ) ) =>
% 0.70/0.91           ( ![C:$i]:
% 0.70/0.91             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.70/0.91               ( ![D:$i]:
% 0.70/0.91                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.70/0.91                   ( ![E:$i]:
% 0.70/0.91                     ( ( ( v1_funct_1 @ E ) & 
% 0.70/0.91                         ( v1_funct_2 @
% 0.70/0.91                           E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 0.70/0.91                         ( m1_subset_1 @
% 0.70/0.91                           E @ 
% 0.70/0.91                           ( k1_zfmisc_1 @
% 0.70/0.91                             ( k2_zfmisc_1 @
% 0.70/0.91                               ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.70/0.91                       ( ( ( g1_pre_topc @
% 0.70/0.91                             ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) ) =
% 0.70/0.91                           ( D ) ) =>
% 0.70/0.91                         ( ![F:$i]:
% 0.70/0.91                           ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 0.70/0.91                             ( ![G:$i]:
% 0.70/0.91                               ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) ) =>
% 0.70/0.91                                 ( ( ( ( F ) = ( G ) ) & 
% 0.70/0.91                                     ( r1_tmap_1 @
% 0.70/0.91                                       C @ B @ 
% 0.70/0.91                                       ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ G ) ) =>
% 0.70/0.91                                   ( r1_tmap_1 @ D @ B @ E @ F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.70/0.91  thf(zf_stmt_0, negated_conjecture,
% 0.70/0.91    (~( ![A:$i]:
% 0.70/0.91        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.70/0.91            ( l1_pre_topc @ A ) ) =>
% 0.70/0.91          ( ![B:$i]:
% 0.70/0.91            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.70/0.91                ( l1_pre_topc @ B ) ) =>
% 0.70/0.91              ( ![C:$i]:
% 0.70/0.91                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.70/0.91                  ( ![D:$i]:
% 0.70/0.91                    ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.70/0.91                      ( ![E:$i]:
% 0.70/0.91                        ( ( ( v1_funct_1 @ E ) & 
% 0.70/0.91                            ( v1_funct_2 @
% 0.70/0.91                              E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 0.70/0.91                            ( m1_subset_1 @
% 0.70/0.91                              E @ 
% 0.70/0.91                              ( k1_zfmisc_1 @
% 0.70/0.91                                ( k2_zfmisc_1 @
% 0.70/0.91                                  ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.70/0.91                          ( ( ( g1_pre_topc @
% 0.70/0.91                                ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) ) =
% 0.70/0.91                              ( D ) ) =>
% 0.70/0.91                            ( ![F:$i]:
% 0.70/0.91                              ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 0.70/0.91                                ( ![G:$i]:
% 0.70/0.91                                  ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) ) =>
% 0.70/0.91                                    ( ( ( ( F ) = ( G ) ) & 
% 0.70/0.91                                        ( r1_tmap_1 @
% 0.70/0.91                                          C @ B @ 
% 0.70/0.91                                          ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ G ) ) =>
% 0.70/0.91                                      ( r1_tmap_1 @ D @ B @ E @ F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.70/0.91    inference('cnf.neg', [status(esa)], [t88_tmap_1])).
% 0.70/0.91  thf('0', plain, (~ (v2_struct_0 @ sk_C)),
% 0.70/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.91  thf('1', plain,
% 0.70/0.91      ((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.70/0.91        (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_G)),
% 0.70/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.91  thf('2', plain, (((sk_F) = (sk_G))),
% 0.70/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.91  thf('3', plain,
% 0.70/0.91      ((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.70/0.91        (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_F)),
% 0.70/0.91      inference('demod', [status(thm)], ['1', '2'])).
% 0.70/0.91  thf('4', plain,
% 0.70/0.91      ((m1_subset_1 @ sk_E @ 
% 0.70/0.91        (k1_zfmisc_1 @ 
% 0.70/0.91         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 0.70/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.91  thf(t2_tsep_1, axiom,
% 0.70/0.91    (![A:$i]: ( ( l1_pre_topc @ A ) => ( m1_pre_topc @ A @ A ) ))).
% 0.70/0.91  thf('5', plain,
% 0.70/0.91      (![X22 : $i]: ((m1_pre_topc @ X22 @ X22) | ~ (l1_pre_topc @ X22))),
% 0.70/0.91      inference('cnf', [status(esa)], [t2_tsep_1])).
% 0.70/0.91  thf('6', plain,
% 0.70/0.91      (((g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) = (sk_D))),
% 0.70/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.91  thf(t59_pre_topc, axiom,
% 0.70/0.91    (![A:$i]:
% 0.70/0.91     ( ( l1_pre_topc @ A ) =>
% 0.70/0.91       ( ![B:$i]:
% 0.70/0.91         ( ( m1_pre_topc @
% 0.70/0.91             B @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) =>
% 0.70/0.91           ( m1_pre_topc @ B @ A ) ) ) ))).
% 0.70/0.91  thf('7', plain,
% 0.70/0.91      (![X9 : $i, X10 : $i]:
% 0.70/0.91         (~ (m1_pre_topc @ X9 @ 
% 0.70/0.91             (g1_pre_topc @ (u1_struct_0 @ X10) @ (u1_pre_topc @ X10)))
% 0.70/0.91          | (m1_pre_topc @ X9 @ X10)
% 0.70/0.91          | ~ (l1_pre_topc @ X10))),
% 0.70/0.91      inference('cnf', [status(esa)], [t59_pre_topc])).
% 0.70/0.91  thf('8', plain,
% 0.70/0.91      (![X0 : $i]:
% 0.70/0.91         (~ (m1_pre_topc @ X0 @ sk_D)
% 0.70/0.91          | ~ (l1_pre_topc @ sk_C)
% 0.70/0.91          | (m1_pre_topc @ X0 @ sk_C))),
% 0.70/0.91      inference('sup-', [status(thm)], ['6', '7'])).
% 0.70/0.91  thf('9', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.70/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.91  thf(dt_m1_pre_topc, axiom,
% 0.70/0.91    (![A:$i]:
% 0.70/0.91     ( ( l1_pre_topc @ A ) =>
% 0.70/0.91       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.70/0.91  thf('10', plain,
% 0.70/0.91      (![X7 : $i, X8 : $i]:
% 0.70/0.91         (~ (m1_pre_topc @ X7 @ X8) | (l1_pre_topc @ X7) | ~ (l1_pre_topc @ X8))),
% 0.70/0.91      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.70/0.91  thf('11', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_C))),
% 0.70/0.91      inference('sup-', [status(thm)], ['9', '10'])).
% 0.70/0.91  thf('12', plain, ((l1_pre_topc @ sk_A)),
% 0.70/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.91  thf('13', plain, ((l1_pre_topc @ sk_C)),
% 0.70/0.91      inference('demod', [status(thm)], ['11', '12'])).
% 0.70/0.91  thf('14', plain,
% 0.70/0.91      (![X0 : $i]: (~ (m1_pre_topc @ X0 @ sk_D) | (m1_pre_topc @ X0 @ sk_C))),
% 0.70/0.91      inference('demod', [status(thm)], ['8', '13'])).
% 0.70/0.91  thf('15', plain, ((~ (l1_pre_topc @ sk_D) | (m1_pre_topc @ sk_D @ sk_C))),
% 0.70/0.91      inference('sup-', [status(thm)], ['5', '14'])).
% 0.70/0.91  thf('16', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.70/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.91  thf('17', plain,
% 0.70/0.91      (![X7 : $i, X8 : $i]:
% 0.70/0.91         (~ (m1_pre_topc @ X7 @ X8) | (l1_pre_topc @ X7) | ~ (l1_pre_topc @ X8))),
% 0.70/0.91      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.70/0.91  thf('18', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_D))),
% 0.70/0.91      inference('sup-', [status(thm)], ['16', '17'])).
% 0.70/0.91  thf('19', plain, ((l1_pre_topc @ sk_A)),
% 0.70/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.91  thf('20', plain, ((l1_pre_topc @ sk_D)),
% 0.70/0.91      inference('demod', [status(thm)], ['18', '19'])).
% 0.70/0.91  thf('21', plain, ((m1_pre_topc @ sk_D @ sk_C)),
% 0.70/0.91      inference('demod', [status(thm)], ['15', '20'])).
% 0.70/0.91  thf(t35_borsuk_1, axiom,
% 0.70/0.91    (![A:$i]:
% 0.70/0.91     ( ( l1_pre_topc @ A ) =>
% 0.70/0.91       ( ![B:$i]:
% 0.70/0.91         ( ( m1_pre_topc @ B @ A ) =>
% 0.70/0.91           ( r1_tarski @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ))).
% 0.70/0.91  thf('22', plain,
% 0.70/0.91      (![X23 : $i, X24 : $i]:
% 0.70/0.91         (~ (m1_pre_topc @ X23 @ X24)
% 0.70/0.91          | (r1_tarski @ (u1_struct_0 @ X23) @ (u1_struct_0 @ X24))
% 0.70/0.91          | ~ (l1_pre_topc @ X24))),
% 0.70/0.91      inference('cnf', [status(esa)], [t35_borsuk_1])).
% 0.70/0.91  thf('23', plain,
% 0.70/0.91      ((~ (l1_pre_topc @ sk_C)
% 0.70/0.91        | (r1_tarski @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_C)))),
% 0.70/0.91      inference('sup-', [status(thm)], ['21', '22'])).
% 0.70/0.91  thf('24', plain, ((l1_pre_topc @ sk_C)),
% 0.70/0.91      inference('demod', [status(thm)], ['11', '12'])).
% 0.70/0.91  thf('25', plain, ((r1_tarski @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_C))),
% 0.70/0.91      inference('demod', [status(thm)], ['23', '24'])).
% 0.70/0.91  thf(d10_xboole_0, axiom,
% 0.70/0.91    (![A:$i,B:$i]:
% 0.70/0.91     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.70/0.91  thf('26', plain,
% 0.70/0.91      (![X0 : $i, X2 : $i]:
% 0.70/0.91         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.70/0.91      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.70/0.91  thf('27', plain,
% 0.70/0.91      ((~ (r1_tarski @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D))
% 0.70/0.91        | ((u1_struct_0 @ sk_C) = (u1_struct_0 @ sk_D)))),
% 0.70/0.91      inference('sup-', [status(thm)], ['25', '26'])).
% 0.70/0.91  thf('28', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.70/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.91  thf('29', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.70/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.91  thf(t22_tsep_1, axiom,
% 0.70/0.91    (![A:$i]:
% 0.70/0.91     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.70/0.91       ( ![B:$i]:
% 0.70/0.91         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.70/0.91           ( ![C:$i]:
% 0.70/0.91             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.70/0.91               ( m1_pre_topc @ B @ ( k1_tsep_1 @ A @ B @ C ) ) ) ) ) ) ))).
% 0.70/0.91  thf('30', plain,
% 0.70/0.91      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.70/0.91         ((v2_struct_0 @ X17)
% 0.70/0.91          | ~ (m1_pre_topc @ X17 @ X18)
% 0.70/0.91          | (m1_pre_topc @ X17 @ (k1_tsep_1 @ X18 @ X17 @ X19))
% 0.70/0.91          | ~ (m1_pre_topc @ X19 @ X18)
% 0.70/0.91          | (v2_struct_0 @ X19)
% 0.70/0.91          | ~ (l1_pre_topc @ X18)
% 0.70/0.91          | ~ (v2_pre_topc @ X18)
% 0.70/0.91          | (v2_struct_0 @ X18))),
% 0.70/0.91      inference('cnf', [status(esa)], [t22_tsep_1])).
% 0.70/0.91  thf('31', plain,
% 0.70/0.91      (![X0 : $i]:
% 0.70/0.91         ((v2_struct_0 @ sk_A)
% 0.70/0.91          | ~ (v2_pre_topc @ sk_A)
% 0.70/0.91          | ~ (l1_pre_topc @ sk_A)
% 0.70/0.91          | (v2_struct_0 @ X0)
% 0.70/0.91          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.70/0.91          | (m1_pre_topc @ sk_C @ (k1_tsep_1 @ sk_A @ sk_C @ X0))
% 0.70/0.91          | (v2_struct_0 @ sk_C))),
% 0.70/0.91      inference('sup-', [status(thm)], ['29', '30'])).
% 0.70/0.91  thf('32', plain, ((v2_pre_topc @ sk_A)),
% 0.70/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.91  thf('33', plain, ((l1_pre_topc @ sk_A)),
% 0.70/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.91  thf('34', plain,
% 0.70/0.91      (![X0 : $i]:
% 0.70/0.91         ((v2_struct_0 @ sk_A)
% 0.70/0.91          | (v2_struct_0 @ X0)
% 0.70/0.91          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.70/0.91          | (m1_pre_topc @ sk_C @ (k1_tsep_1 @ sk_A @ sk_C @ X0))
% 0.70/0.91          | (v2_struct_0 @ sk_C))),
% 0.70/0.91      inference('demod', [status(thm)], ['31', '32', '33'])).
% 0.70/0.91  thf('35', plain,
% 0.70/0.91      (((v2_struct_0 @ sk_C)
% 0.70/0.91        | (m1_pre_topc @ sk_C @ (k1_tsep_1 @ sk_A @ sk_C @ sk_C))
% 0.70/0.91        | (v2_struct_0 @ sk_C)
% 0.70/0.91        | (v2_struct_0 @ sk_A))),
% 0.70/0.91      inference('sup-', [status(thm)], ['28', '34'])).
% 0.70/0.91  thf('36', plain,
% 0.70/0.91      (((v2_struct_0 @ sk_A)
% 0.70/0.91        | (m1_pre_topc @ sk_C @ (k1_tsep_1 @ sk_A @ sk_C @ sk_C))
% 0.70/0.91        | (v2_struct_0 @ sk_C))),
% 0.70/0.91      inference('simplify', [status(thm)], ['35'])).
% 0.70/0.91  thf('37', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.70/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.91  thf(t25_tmap_1, axiom,
% 0.70/0.91    (![A:$i]:
% 0.70/0.91     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.70/0.91       ( ![B:$i]:
% 0.70/0.91         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.70/0.91           ( ( k1_tsep_1 @ A @ B @ B ) =
% 0.70/0.91             ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ))).
% 0.70/0.91  thf('38', plain,
% 0.70/0.91      (![X20 : $i, X21 : $i]:
% 0.70/0.91         ((v2_struct_0 @ X20)
% 0.70/0.91          | ~ (m1_pre_topc @ X20 @ X21)
% 0.70/0.91          | ((k1_tsep_1 @ X21 @ X20 @ X20)
% 0.70/0.91              = (g1_pre_topc @ (u1_struct_0 @ X20) @ (u1_pre_topc @ X20)))
% 0.70/0.91          | ~ (l1_pre_topc @ X21)
% 0.70/0.91          | ~ (v2_pre_topc @ X21)
% 0.70/0.91          | (v2_struct_0 @ X21))),
% 0.70/0.91      inference('cnf', [status(esa)], [t25_tmap_1])).
% 0.70/0.91  thf('39', plain,
% 0.70/0.91      (((v2_struct_0 @ sk_A)
% 0.70/0.91        | ~ (v2_pre_topc @ sk_A)
% 0.70/0.91        | ~ (l1_pre_topc @ sk_A)
% 0.70/0.91        | ((k1_tsep_1 @ sk_A @ sk_C @ sk_C)
% 0.70/0.91            = (g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)))
% 0.70/0.91        | (v2_struct_0 @ sk_C))),
% 0.70/0.91      inference('sup-', [status(thm)], ['37', '38'])).
% 0.70/0.91  thf('40', plain, ((v2_pre_topc @ sk_A)),
% 0.70/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.91  thf('41', plain, ((l1_pre_topc @ sk_A)),
% 0.70/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.91  thf('42', plain,
% 0.70/0.91      (((g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) = (sk_D))),
% 0.70/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.91  thf('43', plain,
% 0.70/0.91      (((v2_struct_0 @ sk_A)
% 0.70/0.91        | ((k1_tsep_1 @ sk_A @ sk_C @ sk_C) = (sk_D))
% 0.70/0.91        | (v2_struct_0 @ sk_C))),
% 0.70/0.91      inference('demod', [status(thm)], ['39', '40', '41', '42'])).
% 0.70/0.91  thf('44', plain, (~ (v2_struct_0 @ sk_A)),
% 0.70/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.91  thf('45', plain,
% 0.70/0.91      (((v2_struct_0 @ sk_C) | ((k1_tsep_1 @ sk_A @ sk_C @ sk_C) = (sk_D)))),
% 0.70/0.91      inference('clc', [status(thm)], ['43', '44'])).
% 0.70/0.91  thf('46', plain, (~ (v2_struct_0 @ sk_C)),
% 0.70/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.91  thf('47', plain, (((k1_tsep_1 @ sk_A @ sk_C @ sk_C) = (sk_D))),
% 0.70/0.91      inference('clc', [status(thm)], ['45', '46'])).
% 0.70/0.91  thf('48', plain,
% 0.70/0.91      (((v2_struct_0 @ sk_A)
% 0.70/0.91        | (m1_pre_topc @ sk_C @ sk_D)
% 0.70/0.91        | (v2_struct_0 @ sk_C))),
% 0.70/0.91      inference('demod', [status(thm)], ['36', '47'])).
% 0.70/0.91  thf('49', plain, (~ (v2_struct_0 @ sk_A)),
% 0.70/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.91  thf('50', plain, (((v2_struct_0 @ sk_C) | (m1_pre_topc @ sk_C @ sk_D))),
% 0.70/0.91      inference('clc', [status(thm)], ['48', '49'])).
% 0.70/0.91  thf('51', plain, (~ (v2_struct_0 @ sk_C)),
% 0.70/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.91  thf('52', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 0.70/0.91      inference('clc', [status(thm)], ['50', '51'])).
% 0.70/0.91  thf('53', plain,
% 0.70/0.91      (![X23 : $i, X24 : $i]:
% 0.70/0.91         (~ (m1_pre_topc @ X23 @ X24)
% 0.70/0.91          | (r1_tarski @ (u1_struct_0 @ X23) @ (u1_struct_0 @ X24))
% 0.70/0.91          | ~ (l1_pre_topc @ X24))),
% 0.70/0.91      inference('cnf', [status(esa)], [t35_borsuk_1])).
% 0.70/0.91  thf('54', plain,
% 0.70/0.91      ((~ (l1_pre_topc @ sk_D)
% 0.70/0.91        | (r1_tarski @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D)))),
% 0.70/0.91      inference('sup-', [status(thm)], ['52', '53'])).
% 0.70/0.91  thf('55', plain, ((l1_pre_topc @ sk_D)),
% 0.70/0.91      inference('demod', [status(thm)], ['18', '19'])).
% 0.70/0.91  thf('56', plain, ((r1_tarski @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D))),
% 0.70/0.91      inference('demod', [status(thm)], ['54', '55'])).
% 0.70/0.91  thf('57', plain, (((u1_struct_0 @ sk_C) = (u1_struct_0 @ sk_D))),
% 0.70/0.91      inference('demod', [status(thm)], ['27', '56'])).
% 0.70/0.91  thf('58', plain,
% 0.70/0.91      ((m1_subset_1 @ sk_E @ 
% 0.70/0.91        (k1_zfmisc_1 @ 
% 0.70/0.91         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 0.70/0.91      inference('demod', [status(thm)], ['4', '57'])).
% 0.70/0.91  thf(d3_struct_0, axiom,
% 0.70/0.91    (![A:$i]:
% 0.70/0.91     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.70/0.91  thf('59', plain,
% 0.70/0.91      (![X5 : $i]:
% 0.70/0.91         (((k2_struct_0 @ X5) = (u1_struct_0 @ X5)) | ~ (l1_struct_0 @ X5))),
% 0.70/0.91      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.70/0.91  thf('60', plain, (((u1_struct_0 @ sk_C) = (u1_struct_0 @ sk_D))),
% 0.70/0.91      inference('demod', [status(thm)], ['27', '56'])).
% 0.70/0.91  thf('61', plain,
% 0.70/0.91      ((((u1_struct_0 @ sk_C) = (k2_struct_0 @ sk_D)) | ~ (l1_struct_0 @ sk_D))),
% 0.70/0.91      inference('sup+', [status(thm)], ['59', '60'])).
% 0.70/0.91  thf('62', plain, ((l1_pre_topc @ sk_D)),
% 0.70/0.91      inference('demod', [status(thm)], ['18', '19'])).
% 0.70/0.91  thf(dt_l1_pre_topc, axiom,
% 0.70/0.91    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.70/0.91  thf('63', plain, (![X6 : $i]: ((l1_struct_0 @ X6) | ~ (l1_pre_topc @ X6))),
% 0.70/0.91      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.70/0.91  thf('64', plain, ((l1_struct_0 @ sk_D)),
% 0.70/0.91      inference('sup-', [status(thm)], ['62', '63'])).
% 0.70/0.91  thf('65', plain, (((u1_struct_0 @ sk_C) = (k2_struct_0 @ sk_D))),
% 0.70/0.91      inference('demod', [status(thm)], ['61', '64'])).
% 0.70/0.91  thf('66', plain,
% 0.70/0.91      (![X5 : $i]:
% 0.70/0.91         (((k2_struct_0 @ X5) = (u1_struct_0 @ X5)) | ~ (l1_struct_0 @ X5))),
% 0.70/0.91      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.70/0.91  thf('67', plain, (((u1_struct_0 @ sk_C) = (k2_struct_0 @ sk_D))),
% 0.70/0.91      inference('demod', [status(thm)], ['61', '64'])).
% 0.70/0.91  thf('68', plain,
% 0.70/0.91      ((((k2_struct_0 @ sk_C) = (k2_struct_0 @ sk_D)) | ~ (l1_struct_0 @ sk_C))),
% 0.70/0.91      inference('sup+', [status(thm)], ['66', '67'])).
% 0.70/0.91  thf('69', plain, ((l1_pre_topc @ sk_C)),
% 0.70/0.91      inference('demod', [status(thm)], ['11', '12'])).
% 0.70/0.91  thf('70', plain, (![X6 : $i]: ((l1_struct_0 @ X6) | ~ (l1_pre_topc @ X6))),
% 0.70/0.91      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.70/0.91  thf('71', plain, ((l1_struct_0 @ sk_C)),
% 0.70/0.91      inference('sup-', [status(thm)], ['69', '70'])).
% 0.70/0.91  thf('72', plain, (((k2_struct_0 @ sk_C) = (k2_struct_0 @ sk_D))),
% 0.70/0.91      inference('demod', [status(thm)], ['68', '71'])).
% 0.70/0.91  thf('73', plain, (((u1_struct_0 @ sk_C) = (k2_struct_0 @ sk_C))),
% 0.70/0.91      inference('demod', [status(thm)], ['65', '72'])).
% 0.70/0.91  thf('74', plain,
% 0.70/0.91      ((m1_subset_1 @ sk_E @ 
% 0.70/0.91        (k1_zfmisc_1 @ 
% 0.70/0.91         (k2_zfmisc_1 @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 0.70/0.91      inference('demod', [status(thm)], ['58', '73'])).
% 0.70/0.91  thf('75', plain, (((u1_struct_0 @ sk_C) = (u1_struct_0 @ sk_D))),
% 0.70/0.91      inference('demod', [status(thm)], ['27', '56'])).
% 0.70/0.91  thf('76', plain, (((u1_struct_0 @ sk_C) = (k2_struct_0 @ sk_D))),
% 0.70/0.91      inference('demod', [status(thm)], ['61', '64'])).
% 0.70/0.91  thf('77', plain, (((k2_struct_0 @ sk_D) = (u1_struct_0 @ sk_D))),
% 0.70/0.91      inference('demod', [status(thm)], ['75', '76'])).
% 0.70/0.91  thf('78', plain, (((k2_struct_0 @ sk_C) = (k2_struct_0 @ sk_D))),
% 0.70/0.91      inference('demod', [status(thm)], ['68', '71'])).
% 0.70/0.91  thf('79', plain, (((k2_struct_0 @ sk_C) = (u1_struct_0 @ sk_D))),
% 0.70/0.91      inference('demod', [status(thm)], ['77', '78'])).
% 0.70/0.91  thf(t86_tmap_1, axiom,
% 0.70/0.91    (![A:$i]:
% 0.70/0.91     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.70/0.91       ( ![B:$i]:
% 0.70/0.91         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.70/0.91             ( l1_pre_topc @ B ) ) =>
% 0.70/0.91           ( ![C:$i]:
% 0.70/0.91             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.70/0.91               ( ![D:$i]:
% 0.70/0.91                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.70/0.91                   ( ![E:$i]:
% 0.70/0.91                     ( ( ( v1_funct_1 @ E ) & 
% 0.70/0.91                         ( v1_funct_2 @
% 0.70/0.91                           E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 0.70/0.91                         ( m1_subset_1 @
% 0.70/0.91                           E @ 
% 0.70/0.91                           ( k1_zfmisc_1 @
% 0.70/0.91                             ( k2_zfmisc_1 @
% 0.70/0.91                               ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.70/0.91                       ( ( ( v1_tsep_1 @ C @ D ) & ( m1_pre_topc @ C @ D ) ) =>
% 0.70/0.91                         ( ![F:$i]:
% 0.70/0.91                           ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 0.70/0.91                             ( ![G:$i]:
% 0.70/0.91                               ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) ) =>
% 0.70/0.91                                 ( ( ( F ) = ( G ) ) =>
% 0.70/0.91                                   ( ( r1_tmap_1 @ D @ B @ E @ F ) <=>
% 0.70/0.91                                     ( r1_tmap_1 @
% 0.70/0.91                                       C @ B @ 
% 0.70/0.91                                       ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ G ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.70/0.91  thf('80', plain,
% 0.70/0.91      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 0.70/0.91         ((v2_struct_0 @ X28)
% 0.70/0.91          | ~ (v2_pre_topc @ X28)
% 0.70/0.91          | ~ (l1_pre_topc @ X28)
% 0.70/0.91          | (v2_struct_0 @ X29)
% 0.70/0.91          | ~ (m1_pre_topc @ X29 @ X30)
% 0.70/0.91          | ~ (v1_tsep_1 @ X31 @ X29)
% 0.70/0.91          | ~ (m1_pre_topc @ X31 @ X29)
% 0.70/0.91          | ~ (m1_subset_1 @ X32 @ (u1_struct_0 @ X29))
% 0.70/0.91          | ((X32) != (X33))
% 0.70/0.91          | ~ (r1_tmap_1 @ X31 @ X28 @ 
% 0.70/0.91               (k3_tmap_1 @ X30 @ X28 @ X29 @ X31 @ X34) @ X33)
% 0.70/0.91          | (r1_tmap_1 @ X29 @ X28 @ X34 @ X32)
% 0.70/0.91          | ~ (m1_subset_1 @ X33 @ (u1_struct_0 @ X31))
% 0.70/0.91          | ~ (m1_subset_1 @ X34 @ 
% 0.70/0.91               (k1_zfmisc_1 @ 
% 0.70/0.91                (k2_zfmisc_1 @ (u1_struct_0 @ X29) @ (u1_struct_0 @ X28))))
% 0.70/0.91          | ~ (v1_funct_2 @ X34 @ (u1_struct_0 @ X29) @ (u1_struct_0 @ X28))
% 0.70/0.91          | ~ (v1_funct_1 @ X34)
% 0.70/0.91          | ~ (m1_pre_topc @ X31 @ X30)
% 0.70/0.91          | (v2_struct_0 @ X31)
% 0.70/0.91          | ~ (l1_pre_topc @ X30)
% 0.70/0.91          | ~ (v2_pre_topc @ X30)
% 0.70/0.91          | (v2_struct_0 @ X30))),
% 0.70/0.91      inference('cnf', [status(esa)], [t86_tmap_1])).
% 0.70/0.91  thf('81', plain,
% 0.70/0.91      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i, X33 : $i, X34 : $i]:
% 0.70/0.91         ((v2_struct_0 @ X30)
% 0.70/0.91          | ~ (v2_pre_topc @ X30)
% 0.70/0.91          | ~ (l1_pre_topc @ X30)
% 0.70/0.91          | (v2_struct_0 @ X31)
% 0.70/0.91          | ~ (m1_pre_topc @ X31 @ X30)
% 0.70/0.91          | ~ (v1_funct_1 @ X34)
% 0.70/0.91          | ~ (v1_funct_2 @ X34 @ (u1_struct_0 @ X29) @ (u1_struct_0 @ X28))
% 0.70/0.91          | ~ (m1_subset_1 @ X34 @ 
% 0.70/0.91               (k1_zfmisc_1 @ 
% 0.70/0.91                (k2_zfmisc_1 @ (u1_struct_0 @ X29) @ (u1_struct_0 @ X28))))
% 0.70/0.91          | ~ (m1_subset_1 @ X33 @ (u1_struct_0 @ X31))
% 0.70/0.91          | (r1_tmap_1 @ X29 @ X28 @ X34 @ X33)
% 0.70/0.91          | ~ (r1_tmap_1 @ X31 @ X28 @ 
% 0.70/0.91               (k3_tmap_1 @ X30 @ X28 @ X29 @ X31 @ X34) @ X33)
% 0.70/0.91          | ~ (m1_subset_1 @ X33 @ (u1_struct_0 @ X29))
% 0.70/0.91          | ~ (m1_pre_topc @ X31 @ X29)
% 0.70/0.91          | ~ (v1_tsep_1 @ X31 @ X29)
% 0.70/0.91          | ~ (m1_pre_topc @ X29 @ X30)
% 0.70/0.91          | (v2_struct_0 @ X29)
% 0.70/0.91          | ~ (l1_pre_topc @ X28)
% 0.70/0.91          | ~ (v2_pre_topc @ X28)
% 0.70/0.91          | (v2_struct_0 @ X28))),
% 0.70/0.91      inference('simplify', [status(thm)], ['80'])).
% 0.70/0.91  thf('82', plain,
% 0.70/0.91      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.70/0.91         (~ (m1_subset_1 @ X1 @ 
% 0.70/0.91             (k1_zfmisc_1 @ 
% 0.70/0.91              (k2_zfmisc_1 @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ X0))))
% 0.70/0.91          | (v2_struct_0 @ X0)
% 0.70/0.91          | ~ (v2_pre_topc @ X0)
% 0.70/0.91          | ~ (l1_pre_topc @ X0)
% 0.70/0.91          | (v2_struct_0 @ sk_D)
% 0.70/0.91          | ~ (m1_pre_topc @ sk_D @ X2)
% 0.70/0.91          | ~ (v1_tsep_1 @ X3 @ sk_D)
% 0.70/0.91          | ~ (m1_pre_topc @ X3 @ sk_D)
% 0.70/0.91          | ~ (m1_subset_1 @ X4 @ (u1_struct_0 @ sk_D))
% 0.70/0.91          | ~ (r1_tmap_1 @ X3 @ X0 @ (k3_tmap_1 @ X2 @ X0 @ sk_D @ X3 @ X1) @ 
% 0.70/0.91               X4)
% 0.70/0.91          | (r1_tmap_1 @ sk_D @ X0 @ X1 @ X4)
% 0.70/0.91          | ~ (m1_subset_1 @ X4 @ (u1_struct_0 @ X3))
% 0.70/0.91          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ X0))
% 0.70/0.91          | ~ (v1_funct_1 @ X1)
% 0.70/0.91          | ~ (m1_pre_topc @ X3 @ X2)
% 0.70/0.91          | (v2_struct_0 @ X3)
% 0.70/0.91          | ~ (l1_pre_topc @ X2)
% 0.70/0.91          | ~ (v2_pre_topc @ X2)
% 0.70/0.91          | (v2_struct_0 @ X2))),
% 0.70/0.91      inference('sup-', [status(thm)], ['79', '81'])).
% 0.70/0.91  thf('83', plain, (((k2_struct_0 @ sk_C) = (u1_struct_0 @ sk_D))),
% 0.70/0.91      inference('demod', [status(thm)], ['77', '78'])).
% 0.70/0.91  thf('84', plain, (((k2_struct_0 @ sk_C) = (u1_struct_0 @ sk_D))),
% 0.70/0.91      inference('demod', [status(thm)], ['77', '78'])).
% 0.70/0.91  thf('85', plain,
% 0.70/0.91      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.70/0.91         (~ (m1_subset_1 @ X1 @ 
% 0.70/0.91             (k1_zfmisc_1 @ 
% 0.70/0.91              (k2_zfmisc_1 @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ X0))))
% 0.70/0.91          | (v2_struct_0 @ X0)
% 0.70/0.91          | ~ (v2_pre_topc @ X0)
% 0.70/0.91          | ~ (l1_pre_topc @ X0)
% 0.70/0.91          | (v2_struct_0 @ sk_D)
% 0.70/0.91          | ~ (m1_pre_topc @ sk_D @ X2)
% 0.70/0.91          | ~ (v1_tsep_1 @ X3 @ sk_D)
% 0.70/0.91          | ~ (m1_pre_topc @ X3 @ sk_D)
% 0.70/0.91          | ~ (m1_subset_1 @ X4 @ (k2_struct_0 @ sk_C))
% 0.70/0.91          | ~ (r1_tmap_1 @ X3 @ X0 @ (k3_tmap_1 @ X2 @ X0 @ sk_D @ X3 @ X1) @ 
% 0.70/0.91               X4)
% 0.70/0.91          | (r1_tmap_1 @ sk_D @ X0 @ X1 @ X4)
% 0.70/0.91          | ~ (m1_subset_1 @ X4 @ (u1_struct_0 @ X3))
% 0.70/0.91          | ~ (v1_funct_2 @ X1 @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ X0))
% 0.70/0.91          | ~ (v1_funct_1 @ X1)
% 0.70/0.91          | ~ (m1_pre_topc @ X3 @ X2)
% 0.70/0.91          | (v2_struct_0 @ X3)
% 0.70/0.91          | ~ (l1_pre_topc @ X2)
% 0.70/0.91          | ~ (v2_pre_topc @ X2)
% 0.70/0.91          | (v2_struct_0 @ X2))),
% 0.70/0.91      inference('demod', [status(thm)], ['82', '83', '84'])).
% 0.70/0.91  thf('86', plain,
% 0.70/0.91      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.70/0.91         ((v2_struct_0 @ X0)
% 0.70/0.91          | ~ (v2_pre_topc @ X0)
% 0.70/0.91          | ~ (l1_pre_topc @ X0)
% 0.70/0.91          | (v2_struct_0 @ X1)
% 0.70/0.91          | ~ (m1_pre_topc @ X1 @ X0)
% 0.70/0.91          | ~ (v1_funct_1 @ sk_E)
% 0.70/0.91          | ~ (v1_funct_2 @ sk_E @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))
% 0.70/0.91          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1))
% 0.70/0.91          | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X2)
% 0.70/0.91          | ~ (r1_tmap_1 @ X1 @ sk_B @ 
% 0.70/0.91               (k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E) @ X2)
% 0.70/0.91          | ~ (m1_subset_1 @ X2 @ (k2_struct_0 @ sk_C))
% 0.70/0.91          | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.70/0.91          | ~ (v1_tsep_1 @ X1 @ sk_D)
% 0.70/0.91          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.70/0.91          | (v2_struct_0 @ sk_D)
% 0.70/0.91          | ~ (l1_pre_topc @ sk_B)
% 0.70/0.91          | ~ (v2_pre_topc @ sk_B)
% 0.70/0.91          | (v2_struct_0 @ sk_B))),
% 0.70/0.91      inference('sup-', [status(thm)], ['74', '85'])).
% 0.70/0.91  thf('87', plain, ((v1_funct_1 @ sk_E)),
% 0.70/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.91  thf('88', plain,
% 0.70/0.91      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 0.70/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.91  thf('89', plain, (((u1_struct_0 @ sk_C) = (u1_struct_0 @ sk_D))),
% 0.70/0.91      inference('demod', [status(thm)], ['27', '56'])).
% 0.70/0.91  thf('90', plain,
% 0.70/0.91      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 0.70/0.91      inference('demod', [status(thm)], ['88', '89'])).
% 0.70/0.91  thf('91', plain, (((u1_struct_0 @ sk_C) = (k2_struct_0 @ sk_C))),
% 0.70/0.91      inference('demod', [status(thm)], ['65', '72'])).
% 0.70/0.91  thf('92', plain,
% 0.70/0.91      ((v1_funct_2 @ sk_E @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 0.70/0.91      inference('demod', [status(thm)], ['90', '91'])).
% 0.70/0.91  thf('93', plain, ((l1_pre_topc @ sk_B)),
% 0.70/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.91  thf('94', plain, ((v2_pre_topc @ sk_B)),
% 0.70/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.91  thf('95', plain,
% 0.70/0.91      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.70/0.91         ((v2_struct_0 @ X0)
% 0.70/0.91          | ~ (v2_pre_topc @ X0)
% 0.70/0.91          | ~ (l1_pre_topc @ X0)
% 0.70/0.91          | (v2_struct_0 @ X1)
% 0.70/0.91          | ~ (m1_pre_topc @ X1 @ X0)
% 0.70/0.91          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1))
% 0.70/0.91          | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X2)
% 0.70/0.91          | ~ (r1_tmap_1 @ X1 @ sk_B @ 
% 0.70/0.91               (k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E) @ X2)
% 0.70/0.91          | ~ (m1_subset_1 @ X2 @ (k2_struct_0 @ sk_C))
% 0.70/0.91          | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.70/0.91          | ~ (v1_tsep_1 @ X1 @ sk_D)
% 0.70/0.91          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.70/0.91          | (v2_struct_0 @ sk_D)
% 0.70/0.91          | (v2_struct_0 @ sk_B))),
% 0.70/0.91      inference('demod', [status(thm)], ['86', '87', '92', '93', '94'])).
% 0.70/0.91  thf('96', plain,
% 0.70/0.91      (((v2_struct_0 @ sk_B)
% 0.70/0.91        | (v2_struct_0 @ sk_D)
% 0.70/0.91        | ~ (m1_pre_topc @ sk_D @ sk_A)
% 0.70/0.91        | ~ (v1_tsep_1 @ sk_C @ sk_D)
% 0.70/0.91        | ~ (m1_pre_topc @ sk_C @ sk_D)
% 0.70/0.91        | ~ (m1_subset_1 @ sk_F @ (k2_struct_0 @ sk_C))
% 0.70/0.91        | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)
% 0.70/0.91        | ~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C))
% 0.70/0.91        | ~ (m1_pre_topc @ sk_C @ sk_A)
% 0.70/0.91        | (v2_struct_0 @ sk_C)
% 0.70/0.91        | ~ (l1_pre_topc @ sk_A)
% 0.70/0.91        | ~ (v2_pre_topc @ sk_A)
% 0.70/0.91        | (v2_struct_0 @ sk_A))),
% 0.70/0.91      inference('sup-', [status(thm)], ['3', '95'])).
% 0.70/0.91  thf('97', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.70/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.91  thf('98', plain,
% 0.70/0.91      (![X5 : $i]:
% 0.70/0.91         (((k2_struct_0 @ X5) = (u1_struct_0 @ X5)) | ~ (l1_struct_0 @ X5))),
% 0.70/0.91      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.70/0.91  thf('99', plain,
% 0.70/0.91      (![X22 : $i]: ((m1_pre_topc @ X22 @ X22) | ~ (l1_pre_topc @ X22))),
% 0.70/0.91      inference('cnf', [status(esa)], [t2_tsep_1])).
% 0.70/0.91  thf(t1_tsep_1, axiom,
% 0.70/0.91    (![A:$i]:
% 0.70/0.91     ( ( l1_pre_topc @ A ) =>
% 0.70/0.91       ( ![B:$i]:
% 0.70/0.91         ( ( m1_pre_topc @ B @ A ) =>
% 0.70/0.91           ( m1_subset_1 @
% 0.70/0.91             ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.70/0.91  thf('100', plain,
% 0.70/0.91      (![X15 : $i, X16 : $i]:
% 0.70/0.91         (~ (m1_pre_topc @ X15 @ X16)
% 0.70/0.91          | (m1_subset_1 @ (u1_struct_0 @ X15) @ 
% 0.70/0.91             (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.70/0.91          | ~ (l1_pre_topc @ X16))),
% 0.70/0.91      inference('cnf', [status(esa)], [t1_tsep_1])).
% 0.70/0.91  thf('101', plain,
% 0.70/0.91      (![X0 : $i]:
% 0.70/0.91         (~ (l1_pre_topc @ X0)
% 0.70/0.91          | ~ (l1_pre_topc @ X0)
% 0.70/0.91          | (m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 0.70/0.91             (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.70/0.91      inference('sup-', [status(thm)], ['99', '100'])).
% 0.70/0.91  thf('102', plain,
% 0.70/0.91      (![X0 : $i]:
% 0.70/0.91         ((m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 0.70/0.91           (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.70/0.91          | ~ (l1_pre_topc @ X0))),
% 0.70/0.91      inference('simplify', [status(thm)], ['101'])).
% 0.70/0.91  thf('103', plain,
% 0.70/0.91      (![X0 : $i]:
% 0.70/0.91         ((m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 0.70/0.91           (k1_zfmisc_1 @ (k2_struct_0 @ X0)))
% 0.70/0.91          | ~ (l1_struct_0 @ X0)
% 0.70/0.91          | ~ (l1_pre_topc @ X0))),
% 0.70/0.91      inference('sup+', [status(thm)], ['98', '102'])).
% 0.70/0.91  thf('104', plain, (![X6 : $i]: ((l1_struct_0 @ X6) | ~ (l1_pre_topc @ X6))),
% 0.70/0.91      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.70/0.91  thf('105', plain,
% 0.70/0.91      (![X0 : $i]:
% 0.70/0.91         (~ (l1_pre_topc @ X0)
% 0.70/0.91          | (m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 0.70/0.91             (k1_zfmisc_1 @ (k2_struct_0 @ X0))))),
% 0.70/0.91      inference('clc', [status(thm)], ['103', '104'])).
% 0.70/0.91  thf('106', plain, (((u1_struct_0 @ sk_C) = (u1_struct_0 @ sk_D))),
% 0.70/0.91      inference('demod', [status(thm)], ['27', '56'])).
% 0.70/0.91  thf(t16_tsep_1, axiom,
% 0.70/0.91    (![A:$i]:
% 0.70/0.91     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.70/0.91       ( ![B:$i]:
% 0.70/0.91         ( ( m1_pre_topc @ B @ A ) =>
% 0.70/0.91           ( ![C:$i]:
% 0.70/0.91             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.70/0.91               ( ( ( C ) = ( u1_struct_0 @ B ) ) =>
% 0.70/0.91                 ( ( ( v1_tsep_1 @ B @ A ) & ( m1_pre_topc @ B @ A ) ) <=>
% 0.70/0.91                   ( v3_pre_topc @ C @ A ) ) ) ) ) ) ) ))).
% 0.70/0.91  thf('107', plain,
% 0.70/0.91      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.70/0.91         (~ (m1_pre_topc @ X12 @ X13)
% 0.70/0.91          | ((X14) != (u1_struct_0 @ X12))
% 0.70/0.91          | ~ (v3_pre_topc @ X14 @ X13)
% 0.70/0.91          | (v1_tsep_1 @ X12 @ X13)
% 0.70/0.91          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.70/0.91          | ~ (l1_pre_topc @ X13)
% 0.70/0.91          | ~ (v2_pre_topc @ X13))),
% 0.70/0.91      inference('cnf', [status(esa)], [t16_tsep_1])).
% 0.70/0.91  thf('108', plain,
% 0.70/0.91      (![X12 : $i, X13 : $i]:
% 0.70/0.91         (~ (v2_pre_topc @ X13)
% 0.70/0.91          | ~ (l1_pre_topc @ X13)
% 0.70/0.91          | ~ (m1_subset_1 @ (u1_struct_0 @ X12) @ 
% 0.70/0.91               (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.70/0.91          | (v1_tsep_1 @ X12 @ X13)
% 0.70/0.91          | ~ (v3_pre_topc @ (u1_struct_0 @ X12) @ X13)
% 0.70/0.91          | ~ (m1_pre_topc @ X12 @ X13))),
% 0.70/0.91      inference('simplify', [status(thm)], ['107'])).
% 0.70/0.91  thf('109', plain,
% 0.70/0.91      (![X0 : $i]:
% 0.70/0.91         (~ (m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 0.70/0.91             (k1_zfmisc_1 @ (u1_struct_0 @ sk_C)))
% 0.70/0.91          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.70/0.91          | ~ (v3_pre_topc @ (u1_struct_0 @ X0) @ sk_D)
% 0.70/0.91          | (v1_tsep_1 @ X0 @ sk_D)
% 0.70/0.91          | ~ (l1_pre_topc @ sk_D)
% 0.70/0.91          | ~ (v2_pre_topc @ sk_D))),
% 0.70/0.91      inference('sup-', [status(thm)], ['106', '108'])).
% 0.70/0.91  thf('110', plain, ((l1_pre_topc @ sk_D)),
% 0.70/0.91      inference('demod', [status(thm)], ['18', '19'])).
% 0.70/0.91  thf('111', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.70/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.91  thf(cc1_pre_topc, axiom,
% 0.70/0.91    (![A:$i]:
% 0.70/0.91     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.70/0.91       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( v2_pre_topc @ B ) ) ) ))).
% 0.70/0.91  thf('112', plain,
% 0.70/0.91      (![X3 : $i, X4 : $i]:
% 0.70/0.91         (~ (m1_pre_topc @ X3 @ X4)
% 0.70/0.91          | (v2_pre_topc @ X3)
% 0.70/0.91          | ~ (l1_pre_topc @ X4)
% 0.70/0.91          | ~ (v2_pre_topc @ X4))),
% 0.70/0.91      inference('cnf', [status(esa)], [cc1_pre_topc])).
% 0.70/0.91  thf('113', plain,
% 0.70/0.91      ((~ (v2_pre_topc @ sk_A) | ~ (l1_pre_topc @ sk_A) | (v2_pre_topc @ sk_D))),
% 0.70/0.91      inference('sup-', [status(thm)], ['111', '112'])).
% 0.70/0.91  thf('114', plain, ((v2_pre_topc @ sk_A)),
% 0.70/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.91  thf('115', plain, ((l1_pre_topc @ sk_A)),
% 0.70/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.91  thf('116', plain, ((v2_pre_topc @ sk_D)),
% 0.70/0.91      inference('demod', [status(thm)], ['113', '114', '115'])).
% 0.70/0.91  thf('117', plain,
% 0.70/0.91      (![X0 : $i]:
% 0.70/0.91         (~ (m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 0.70/0.91             (k1_zfmisc_1 @ (u1_struct_0 @ sk_C)))
% 0.70/0.91          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.70/0.91          | ~ (v3_pre_topc @ (u1_struct_0 @ X0) @ sk_D)
% 0.70/0.91          | (v1_tsep_1 @ X0 @ sk_D))),
% 0.70/0.91      inference('demod', [status(thm)], ['109', '110', '116'])).
% 0.70/0.91  thf('118', plain, (((u1_struct_0 @ sk_C) = (k2_struct_0 @ sk_C))),
% 0.70/0.91      inference('demod', [status(thm)], ['65', '72'])).
% 0.70/0.91  thf('119', plain,
% 0.70/0.91      (![X0 : $i]:
% 0.70/0.91         (~ (m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 0.70/0.91             (k1_zfmisc_1 @ (k2_struct_0 @ sk_C)))
% 0.70/0.91          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.70/0.91          | ~ (v3_pre_topc @ (u1_struct_0 @ X0) @ sk_D)
% 0.70/0.91          | (v1_tsep_1 @ X0 @ sk_D))),
% 0.70/0.91      inference('demod', [status(thm)], ['117', '118'])).
% 0.70/0.91  thf('120', plain,
% 0.70/0.91      ((~ (l1_pre_topc @ sk_C)
% 0.70/0.91        | (v1_tsep_1 @ sk_C @ sk_D)
% 0.70/0.91        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_C) @ sk_D)
% 0.70/0.91        | ~ (m1_pre_topc @ sk_C @ sk_D))),
% 0.70/0.91      inference('sup-', [status(thm)], ['105', '119'])).
% 0.70/0.91  thf('121', plain, ((l1_pre_topc @ sk_C)),
% 0.70/0.91      inference('demod', [status(thm)], ['11', '12'])).
% 0.70/0.91  thf('122', plain, (((u1_struct_0 @ sk_C) = (k2_struct_0 @ sk_C))),
% 0.70/0.91      inference('demod', [status(thm)], ['65', '72'])).
% 0.70/0.91  thf('123', plain, (((u1_struct_0 @ sk_C) = (u1_struct_0 @ sk_D))),
% 0.70/0.91      inference('demod', [status(thm)], ['27', '56'])).
% 0.70/0.91  thf('124', plain,
% 0.70/0.91      (![X22 : $i]: ((m1_pre_topc @ X22 @ X22) | ~ (l1_pre_topc @ X22))),
% 0.70/0.91      inference('cnf', [status(esa)], [t2_tsep_1])).
% 0.70/0.91  thf('125', plain,
% 0.70/0.91      (![X22 : $i]: ((m1_pre_topc @ X22 @ X22) | ~ (l1_pre_topc @ X22))),
% 0.70/0.91      inference('cnf', [status(esa)], [t2_tsep_1])).
% 0.70/0.91  thf(fc10_tops_1, axiom,
% 0.70/0.91    (![A:$i]:
% 0.70/0.91     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.70/0.91       ( v3_pre_topc @ ( k2_struct_0 @ A ) @ A ) ))).
% 0.70/0.91  thf('126', plain,
% 0.70/0.91      (![X11 : $i]:
% 0.70/0.91         ((v3_pre_topc @ (k2_struct_0 @ X11) @ X11)
% 0.70/0.91          | ~ (l1_pre_topc @ X11)
% 0.70/0.91          | ~ (v2_pre_topc @ X11))),
% 0.70/0.91      inference('cnf', [status(esa)], [fc10_tops_1])).
% 0.70/0.91  thf('127', plain,
% 0.70/0.91      (![X5 : $i]:
% 0.70/0.91         (((k2_struct_0 @ X5) = (u1_struct_0 @ X5)) | ~ (l1_struct_0 @ X5))),
% 0.70/0.91      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.70/0.91  thf('128', plain,
% 0.70/0.91      (![X0 : $i]:
% 0.70/0.91         ((m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 0.70/0.91           (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.70/0.91          | ~ (l1_pre_topc @ X0))),
% 0.70/0.91      inference('simplify', [status(thm)], ['101'])).
% 0.70/0.91  thf('129', plain,
% 0.70/0.91      (![X12 : $i, X13 : $i]:
% 0.70/0.91         (~ (v2_pre_topc @ X13)
% 0.70/0.91          | ~ (l1_pre_topc @ X13)
% 0.70/0.91          | ~ (m1_subset_1 @ (u1_struct_0 @ X12) @ 
% 0.70/0.91               (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.70/0.91          | (v1_tsep_1 @ X12 @ X13)
% 0.70/0.91          | ~ (v3_pre_topc @ (u1_struct_0 @ X12) @ X13)
% 0.70/0.91          | ~ (m1_pre_topc @ X12 @ X13))),
% 0.70/0.91      inference('simplify', [status(thm)], ['107'])).
% 0.70/0.91  thf('130', plain,
% 0.70/0.91      (![X0 : $i]:
% 0.70/0.91         (~ (l1_pre_topc @ X0)
% 0.70/0.91          | ~ (m1_pre_topc @ X0 @ X0)
% 0.70/0.91          | ~ (v3_pre_topc @ (u1_struct_0 @ X0) @ X0)
% 0.70/0.91          | (v1_tsep_1 @ X0 @ X0)
% 0.70/0.91          | ~ (l1_pre_topc @ X0)
% 0.70/0.91          | ~ (v2_pre_topc @ X0))),
% 0.70/0.91      inference('sup-', [status(thm)], ['128', '129'])).
% 0.70/0.91  thf('131', plain,
% 0.70/0.91      (![X0 : $i]:
% 0.70/0.91         (~ (v2_pre_topc @ X0)
% 0.70/0.91          | (v1_tsep_1 @ X0 @ X0)
% 0.70/0.91          | ~ (v3_pre_topc @ (u1_struct_0 @ X0) @ X0)
% 0.70/0.91          | ~ (m1_pre_topc @ X0 @ X0)
% 0.70/0.91          | ~ (l1_pre_topc @ X0))),
% 0.70/0.91      inference('simplify', [status(thm)], ['130'])).
% 0.70/0.91  thf('132', plain,
% 0.70/0.91      (![X0 : $i]:
% 0.70/0.91         (~ (v3_pre_topc @ (k2_struct_0 @ X0) @ X0)
% 0.70/0.91          | ~ (l1_struct_0 @ X0)
% 0.70/0.91          | ~ (l1_pre_topc @ X0)
% 0.70/0.91          | ~ (m1_pre_topc @ X0 @ X0)
% 0.70/0.91          | (v1_tsep_1 @ X0 @ X0)
% 0.70/0.91          | ~ (v2_pre_topc @ X0))),
% 0.70/0.91      inference('sup-', [status(thm)], ['127', '131'])).
% 0.70/0.91  thf('133', plain,
% 0.70/0.91      (![X0 : $i]:
% 0.70/0.91         (~ (v2_pre_topc @ X0)
% 0.70/0.91          | ~ (l1_pre_topc @ X0)
% 0.70/0.91          | ~ (v2_pre_topc @ X0)
% 0.70/0.91          | (v1_tsep_1 @ X0 @ X0)
% 0.70/0.91          | ~ (m1_pre_topc @ X0 @ X0)
% 0.70/0.91          | ~ (l1_pre_topc @ X0)
% 0.70/0.91          | ~ (l1_struct_0 @ X0))),
% 0.70/0.91      inference('sup-', [status(thm)], ['126', '132'])).
% 0.70/0.91  thf('134', plain,
% 0.70/0.91      (![X0 : $i]:
% 0.70/0.91         (~ (l1_struct_0 @ X0)
% 0.70/0.91          | ~ (m1_pre_topc @ X0 @ X0)
% 0.70/0.91          | (v1_tsep_1 @ X0 @ X0)
% 0.70/0.91          | ~ (l1_pre_topc @ X0)
% 0.70/0.91          | ~ (v2_pre_topc @ X0))),
% 0.70/0.91      inference('simplify', [status(thm)], ['133'])).
% 0.70/0.91  thf('135', plain,
% 0.70/0.91      (![X0 : $i]:
% 0.70/0.91         (~ (l1_pre_topc @ X0)
% 0.70/0.91          | ~ (v2_pre_topc @ X0)
% 0.70/0.91          | ~ (l1_pre_topc @ X0)
% 0.70/0.91          | (v1_tsep_1 @ X0 @ X0)
% 0.70/0.91          | ~ (l1_struct_0 @ X0))),
% 0.70/0.91      inference('sup-', [status(thm)], ['125', '134'])).
% 0.70/0.91  thf('136', plain,
% 0.70/0.91      (![X0 : $i]:
% 0.70/0.91         (~ (l1_struct_0 @ X0)
% 0.70/0.91          | (v1_tsep_1 @ X0 @ X0)
% 0.70/0.91          | ~ (v2_pre_topc @ X0)
% 0.70/0.91          | ~ (l1_pre_topc @ X0))),
% 0.70/0.91      inference('simplify', [status(thm)], ['135'])).
% 0.70/0.91  thf('137', plain,
% 0.70/0.91      (![X0 : $i]:
% 0.70/0.91         ((m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 0.70/0.91           (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.70/0.91          | ~ (l1_pre_topc @ X0))),
% 0.70/0.91      inference('simplify', [status(thm)], ['101'])).
% 0.70/0.91  thf('138', plain,
% 0.70/0.91      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.70/0.91         (~ (m1_pre_topc @ X12 @ X13)
% 0.70/0.91          | ((X14) != (u1_struct_0 @ X12))
% 0.70/0.91          | ~ (v1_tsep_1 @ X12 @ X13)
% 0.70/0.91          | ~ (m1_pre_topc @ X12 @ X13)
% 0.70/0.91          | (v3_pre_topc @ X14 @ X13)
% 0.70/0.91          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.70/0.91          | ~ (l1_pre_topc @ X13)
% 0.70/0.91          | ~ (v2_pre_topc @ X13))),
% 0.70/0.91      inference('cnf', [status(esa)], [t16_tsep_1])).
% 0.70/0.91  thf('139', plain,
% 0.70/0.91      (![X12 : $i, X13 : $i]:
% 0.70/0.91         (~ (v2_pre_topc @ X13)
% 0.70/0.91          | ~ (l1_pre_topc @ X13)
% 0.70/0.91          | ~ (m1_subset_1 @ (u1_struct_0 @ X12) @ 
% 0.70/0.91               (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.70/0.91          | (v3_pre_topc @ (u1_struct_0 @ X12) @ X13)
% 0.70/0.91          | ~ (v1_tsep_1 @ X12 @ X13)
% 0.70/0.91          | ~ (m1_pre_topc @ X12 @ X13))),
% 0.70/0.91      inference('simplify', [status(thm)], ['138'])).
% 0.70/0.91  thf('140', plain,
% 0.70/0.91      (![X0 : $i]:
% 0.70/0.91         (~ (l1_pre_topc @ X0)
% 0.70/0.91          | ~ (m1_pre_topc @ X0 @ X0)
% 0.70/0.91          | ~ (v1_tsep_1 @ X0 @ X0)
% 0.70/0.91          | (v3_pre_topc @ (u1_struct_0 @ X0) @ X0)
% 0.70/0.91          | ~ (l1_pre_topc @ X0)
% 0.70/0.91          | ~ (v2_pre_topc @ X0))),
% 0.70/0.91      inference('sup-', [status(thm)], ['137', '139'])).
% 0.70/0.91  thf('141', plain,
% 0.70/0.91      (![X0 : $i]:
% 0.70/0.91         (~ (v2_pre_topc @ X0)
% 0.70/0.91          | (v3_pre_topc @ (u1_struct_0 @ X0) @ X0)
% 0.70/0.91          | ~ (v1_tsep_1 @ X0 @ X0)
% 0.70/0.91          | ~ (m1_pre_topc @ X0 @ X0)
% 0.70/0.91          | ~ (l1_pre_topc @ X0))),
% 0.70/0.91      inference('simplify', [status(thm)], ['140'])).
% 0.70/0.91  thf('142', plain,
% 0.70/0.91      (![X0 : $i]:
% 0.70/0.91         (~ (l1_pre_topc @ X0)
% 0.70/0.91          | ~ (v2_pre_topc @ X0)
% 0.70/0.91          | ~ (l1_struct_0 @ X0)
% 0.70/0.91          | ~ (l1_pre_topc @ X0)
% 0.70/0.91          | ~ (m1_pre_topc @ X0 @ X0)
% 0.70/0.91          | (v3_pre_topc @ (u1_struct_0 @ X0) @ X0)
% 0.70/0.91          | ~ (v2_pre_topc @ X0))),
% 0.70/0.91      inference('sup-', [status(thm)], ['136', '141'])).
% 0.70/0.91  thf('143', plain,
% 0.70/0.91      (![X0 : $i]:
% 0.70/0.91         ((v3_pre_topc @ (u1_struct_0 @ X0) @ X0)
% 0.70/0.91          | ~ (m1_pre_topc @ X0 @ X0)
% 0.70/0.91          | ~ (l1_struct_0 @ X0)
% 0.70/0.91          | ~ (v2_pre_topc @ X0)
% 0.70/0.91          | ~ (l1_pre_topc @ X0))),
% 0.70/0.91      inference('simplify', [status(thm)], ['142'])).
% 0.70/0.91  thf('144', plain,
% 0.70/0.91      (![X0 : $i]:
% 0.70/0.91         (~ (l1_pre_topc @ X0)
% 0.70/0.91          | ~ (l1_pre_topc @ X0)
% 0.70/0.91          | ~ (v2_pre_topc @ X0)
% 0.70/0.91          | ~ (l1_struct_0 @ X0)
% 0.70/0.91          | (v3_pre_topc @ (u1_struct_0 @ X0) @ X0))),
% 0.70/0.91      inference('sup-', [status(thm)], ['124', '143'])).
% 0.70/0.91  thf('145', plain,
% 0.70/0.91      (![X0 : $i]:
% 0.70/0.91         ((v3_pre_topc @ (u1_struct_0 @ X0) @ X0)
% 0.70/0.91          | ~ (l1_struct_0 @ X0)
% 0.70/0.91          | ~ (v2_pre_topc @ X0)
% 0.70/0.91          | ~ (l1_pre_topc @ X0))),
% 0.70/0.91      inference('simplify', [status(thm)], ['144'])).
% 0.70/0.91  thf('146', plain,
% 0.70/0.91      (((v3_pre_topc @ (u1_struct_0 @ sk_C) @ sk_D)
% 0.70/0.91        | ~ (l1_pre_topc @ sk_D)
% 0.70/0.91        | ~ (v2_pre_topc @ sk_D)
% 0.70/0.91        | ~ (l1_struct_0 @ sk_D))),
% 0.70/0.91      inference('sup+', [status(thm)], ['123', '145'])).
% 0.70/0.91  thf('147', plain, ((l1_pre_topc @ sk_D)),
% 0.70/0.91      inference('demod', [status(thm)], ['18', '19'])).
% 0.70/0.91  thf('148', plain, ((v2_pre_topc @ sk_D)),
% 0.70/0.91      inference('demod', [status(thm)], ['113', '114', '115'])).
% 0.70/0.91  thf('149', plain, ((l1_struct_0 @ sk_D)),
% 0.70/0.91      inference('sup-', [status(thm)], ['62', '63'])).
% 0.70/0.91  thf('150', plain, ((v3_pre_topc @ (u1_struct_0 @ sk_C) @ sk_D)),
% 0.70/0.91      inference('demod', [status(thm)], ['146', '147', '148', '149'])).
% 0.70/0.91  thf('151', plain, (((u1_struct_0 @ sk_C) = (k2_struct_0 @ sk_D))),
% 0.70/0.91      inference('demod', [status(thm)], ['61', '64'])).
% 0.70/0.91  thf('152', plain, ((v3_pre_topc @ (k2_struct_0 @ sk_D) @ sk_D)),
% 0.70/0.91      inference('demod', [status(thm)], ['150', '151'])).
% 0.70/0.91  thf('153', plain, (((k2_struct_0 @ sk_C) = (k2_struct_0 @ sk_D))),
% 0.70/0.91      inference('demod', [status(thm)], ['68', '71'])).
% 0.70/0.91  thf('154', plain, ((v3_pre_topc @ (k2_struct_0 @ sk_C) @ sk_D)),
% 0.70/0.91      inference('demod', [status(thm)], ['152', '153'])).
% 0.70/0.91  thf('155', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 0.70/0.91      inference('clc', [status(thm)], ['50', '51'])).
% 0.70/0.91  thf('156', plain, ((v1_tsep_1 @ sk_C @ sk_D)),
% 0.70/0.91      inference('demod', [status(thm)], ['120', '121', '122', '154', '155'])).
% 0.70/0.91  thf('157', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 0.70/0.91      inference('clc', [status(thm)], ['50', '51'])).
% 0.70/0.91  thf('158', plain,
% 0.70/0.91      (![X5 : $i]:
% 0.70/0.91         (((k2_struct_0 @ X5) = (u1_struct_0 @ X5)) | ~ (l1_struct_0 @ X5))),
% 0.70/0.91      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.70/0.91  thf('159', plain, ((m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_C))),
% 0.70/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.91  thf('160', plain, (((sk_F) = (sk_G))),
% 0.70/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.91  thf('161', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C))),
% 0.70/0.91      inference('demod', [status(thm)], ['159', '160'])).
% 0.70/0.91  thf('162', plain,
% 0.70/0.91      (((m1_subset_1 @ sk_F @ (k2_struct_0 @ sk_C)) | ~ (l1_struct_0 @ sk_C))),
% 0.70/0.91      inference('sup+', [status(thm)], ['158', '161'])).
% 0.70/0.91  thf('163', plain, ((l1_struct_0 @ sk_C)),
% 0.70/0.91      inference('sup-', [status(thm)], ['69', '70'])).
% 0.70/0.91  thf('164', plain, ((m1_subset_1 @ sk_F @ (k2_struct_0 @ sk_C))),
% 0.70/0.91      inference('demod', [status(thm)], ['162', '163'])).
% 0.70/0.91  thf('165', plain, (((u1_struct_0 @ sk_C) = (k2_struct_0 @ sk_C))),
% 0.70/0.91      inference('demod', [status(thm)], ['65', '72'])).
% 0.70/0.91  thf('166', plain, ((m1_subset_1 @ sk_F @ (k2_struct_0 @ sk_C))),
% 0.70/0.91      inference('demod', [status(thm)], ['162', '163'])).
% 0.70/0.91  thf('167', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.70/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.91  thf('168', plain, ((l1_pre_topc @ sk_A)),
% 0.70/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.91  thf('169', plain, ((v2_pre_topc @ sk_A)),
% 0.70/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.91  thf('170', plain,
% 0.70/0.91      (((v2_struct_0 @ sk_B)
% 0.70/0.91        | (v2_struct_0 @ sk_D)
% 0.70/0.91        | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)
% 0.70/0.91        | (v2_struct_0 @ sk_C)
% 0.70/0.91        | (v2_struct_0 @ sk_A))),
% 0.70/0.91      inference('demod', [status(thm)],
% 0.70/0.91                ['96', '97', '156', '157', '164', '165', '166', '167', '168', 
% 0.70/0.91                 '169'])).
% 0.70/0.91  thf('171', plain, (~ (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)),
% 0.70/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.91  thf('172', plain,
% 0.70/0.91      (((v2_struct_0 @ sk_A)
% 0.70/0.91        | (v2_struct_0 @ sk_C)
% 0.70/0.91        | (v2_struct_0 @ sk_D)
% 0.70/0.91        | (v2_struct_0 @ sk_B))),
% 0.70/0.91      inference('sup-', [status(thm)], ['170', '171'])).
% 0.70/0.91  thf('173', plain, (~ (v2_struct_0 @ sk_D)),
% 0.70/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.91  thf('174', plain,
% 0.70/0.91      (((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_A))),
% 0.70/0.91      inference('sup-', [status(thm)], ['172', '173'])).
% 0.70/0.91  thf('175', plain, (~ (v2_struct_0 @ sk_B)),
% 0.70/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.91  thf('176', plain, (((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_C))),
% 0.70/0.91      inference('clc', [status(thm)], ['174', '175'])).
% 0.70/0.91  thf('177', plain, (~ (v2_struct_0 @ sk_A)),
% 0.70/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.91  thf('178', plain, ((v2_struct_0 @ sk_C)),
% 0.70/0.91      inference('clc', [status(thm)], ['176', '177'])).
% 0.70/0.91  thf('179', plain, ($false), inference('demod', [status(thm)], ['0', '178'])).
% 0.70/0.91  
% 0.70/0.91  % SZS output end Refutation
% 0.70/0.91  
% 0.70/0.92  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
