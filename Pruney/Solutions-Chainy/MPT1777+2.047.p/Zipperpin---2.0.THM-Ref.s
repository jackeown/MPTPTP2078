%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.BZptGvbdQ8

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:10:33 EST 2020

% Result     : Theorem 0.55s
% Output     : Refutation 0.55s
% Verified   : 
% Statistics : Number of formulae       :  216 (4318 expanded)
%              Number of leaves         :   39 (1265 expanded)
%              Depth                    :   27
%              Number of atoms          : 1793 (113969 expanded)
%              Number of equality atoms :   42 (2937 expanded)
%              Maximal formula depth    :   29 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_tsep_1_type,type,(
    v1_tsep_1: $i > $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(sk_G_type,type,(
    sk_G: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(r1_tmap_1_type,type,(
    r1_tmap_1: $i > $i > $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(g1_pre_topc_type,type,(
    g1_pre_topc: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(k3_tmap_1_type,type,(
    k3_tmap_1: $i > $i > $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

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
    ! [X17: $i] :
      ( ( m1_pre_topc @ X17 @ X17 )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('6',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) )
    = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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
      | ~ ( m1_pre_topc @ X10 @ ( g1_pre_topc @ ( u1_struct_0 @ X9 ) @ ( u1_pre_topc @ X9 ) ) )
      | ( m1_pre_topc @ X10 @ X9 )
      | ~ ( l1_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[t65_pre_topc])).

thf('8',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_D )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_pre_topc @ X0 @ sk_C )
      | ~ ( l1_pre_topc @ sk_C ) ) ),
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
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_pre_topc @ X0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['8','13'])).

thf('15',plain,
    ( ~ ( l1_pre_topc @ sk_D )
    | ( m1_pre_topc @ sk_D @ sk_C )
    | ~ ( l1_pre_topc @ sk_D ) ),
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
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['18','19'])).

thf('22',plain,(
    m1_pre_topc @ sk_D @ sk_C ),
    inference(demod,[status(thm)],['15','20','21'])).

thf('23',plain,(
    ! [X17: $i] :
      ( ( m1_pre_topc @ X17 @ X17 )
      | ~ ( l1_pre_topc @ X17 ) ) ),
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

thf('24',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_pre_topc @ X18 @ X19 )
      | ~ ( m1_pre_topc @ X18 @ X20 )
      | ( r1_tarski @ ( u1_struct_0 @ X18 ) @ ( u1_struct_0 @ X20 ) )
      | ~ ( m1_pre_topc @ X20 @ X19 )
      | ~ ( l1_pre_topc @ X19 )
      | ~ ( v2_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[t4_tsep_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ( r1_tarski @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X1 ) )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_pre_topc @ X0 @ X1 )
      | ( r1_tarski @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X1 ) )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,
    ( ~ ( l1_pre_topc @ sk_D )
    | ~ ( v2_pre_topc @ sk_D )
    | ~ ( m1_pre_topc @ sk_C @ sk_D )
    | ( r1_tarski @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['22','26'])).

thf('28',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['18','19'])).

thf('29',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( v2_pre_topc @ B ) ) ) )).

thf('30',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_pre_topc @ X3 @ X4 )
      | ( v2_pre_topc @ X3 )
      | ~ ( l1_pre_topc @ X4 )
      | ~ ( v2_pre_topc @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc1_pre_topc])).

thf('31',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_pre_topc @ sk_D ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    v2_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['31','32','33'])).

thf('35',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) )
    = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    ! [X17: $i] :
      ( ( m1_pre_topc @ X17 @ X17 )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('37',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( l1_pre_topc @ X9 )
      | ~ ( m1_pre_topc @ X10 @ X9 )
      | ( m1_pre_topc @ X10 @ ( g1_pre_topc @ ( u1_struct_0 @ X9 ) @ ( u1_pre_topc @ X9 ) ) )
      | ~ ( l1_pre_topc @ X10 ) ) ),
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

thf('40',plain,
    ( ( m1_pre_topc @ sk_C @ sk_D )
    | ~ ( l1_pre_topc @ sk_C ) ),
    inference('sup+',[status(thm)],['35','39'])).

thf('41',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['11','12'])).

thf('42',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['27','28','34','42'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('44',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('45',plain,
    ( ~ ( r1_tarski @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D ) )
    | ( ( u1_struct_0 @ sk_C )
      = ( u1_struct_0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(demod,[status(thm)],['40','41'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_pre_topc @ X0 @ X1 )
      | ( r1_tarski @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X1 ) )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('48',plain,
    ( ~ ( l1_pre_topc @ sk_C )
    | ~ ( v2_pre_topc @ sk_C )
    | ~ ( m1_pre_topc @ sk_D @ sk_C )
    | ( r1_tarski @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['11','12'])).

thf('50',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_pre_topc @ X3 @ X4 )
      | ( v2_pre_topc @ X3 )
      | ~ ( l1_pre_topc @ X4 )
      | ~ ( v2_pre_topc @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc1_pre_topc])).

thf('52',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_pre_topc @ sk_C ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    v2_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['52','53','54'])).

thf('56',plain,(
    m1_pre_topc @ sk_D @ sk_C ),
    inference(demod,[status(thm)],['15','20','21'])).

thf('57',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['48','49','55','56'])).

thf('58',plain,
    ( ( u1_struct_0 @ sk_C )
    = ( u1_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['45','57'])).

thf('59',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['4','58'])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('60',plain,(
    ! [X5: $i] :
      ( ( ( k2_struct_0 @ X5 )
        = ( u1_struct_0 @ X5 ) )
      | ~ ( l1_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('61',plain,
    ( ( u1_struct_0 @ sk_C )
    = ( u1_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['45','57'])).

thf('62',plain,
    ( ( ( u1_struct_0 @ sk_C )
      = ( k2_struct_0 @ sk_D ) )
    | ~ ( l1_struct_0 @ sk_D ) ),
    inference('sup+',[status(thm)],['60','61'])).

thf('63',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['18','19'])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('64',plain,(
    ! [X6: $i] :
      ( ( l1_struct_0 @ X6 )
      | ~ ( l1_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('65',plain,(
    l1_struct_0 @ sk_D ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,
    ( ( u1_struct_0 @ sk_C )
    = ( k2_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['62','65'])).

thf('67',plain,(
    ! [X5: $i] :
      ( ( ( k2_struct_0 @ X5 )
        = ( u1_struct_0 @ X5 ) )
      | ~ ( l1_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('68',plain,
    ( ( u1_struct_0 @ sk_C )
    = ( k2_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['62','65'])).

thf('69',plain,
    ( ( ( k2_struct_0 @ sk_C )
      = ( k2_struct_0 @ sk_D ) )
    | ~ ( l1_struct_0 @ sk_C ) ),
    inference('sup+',[status(thm)],['67','68'])).

thf('70',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['11','12'])).

thf('71',plain,(
    ! [X6: $i] :
      ( ( l1_struct_0 @ X6 )
      | ~ ( l1_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('72',plain,(
    l1_struct_0 @ sk_C ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,
    ( ( k2_struct_0 @ sk_C )
    = ( k2_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['69','72'])).

thf('74',plain,
    ( ( u1_struct_0 @ sk_C )
    = ( k2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['66','73'])).

thf('75',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['59','74'])).

thf('76',plain,
    ( ( u1_struct_0 @ sk_C )
    = ( u1_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['45','57'])).

thf('77',plain,
    ( ( u1_struct_0 @ sk_C )
    = ( k2_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['62','65'])).

thf('78',plain,
    ( ( k2_struct_0 @ sk_D )
    = ( u1_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('79',plain,
    ( ( k2_struct_0 @ sk_C )
    = ( k2_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['69','72'])).

thf('80',plain,
    ( ( k2_struct_0 @ sk_C )
    = ( u1_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['78','79'])).

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

thf('81',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ( v2_struct_0 @ X24 )
      | ~ ( v2_pre_topc @ X24 )
      | ~ ( l1_pre_topc @ X24 )
      | ( v2_struct_0 @ X25 )
      | ~ ( m1_pre_topc @ X25 @ X26 )
      | ~ ( v1_tsep_1 @ X27 @ X25 )
      | ~ ( m1_pre_topc @ X27 @ X25 )
      | ~ ( m1_subset_1 @ X28 @ ( u1_struct_0 @ X25 ) )
      | ( X28 != X29 )
      | ~ ( r1_tmap_1 @ X27 @ X24 @ ( k3_tmap_1 @ X26 @ X24 @ X25 @ X27 @ X30 ) @ X29 )
      | ( r1_tmap_1 @ X25 @ X24 @ X30 @ X28 )
      | ~ ( m1_subset_1 @ X29 @ ( u1_struct_0 @ X27 ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X25 ) @ ( u1_struct_0 @ X24 ) ) ) )
      | ~ ( v1_funct_2 @ X30 @ ( u1_struct_0 @ X25 ) @ ( u1_struct_0 @ X24 ) )
      | ~ ( v1_funct_1 @ X30 )
      | ~ ( m1_pre_topc @ X27 @ X26 )
      | ( v2_struct_0 @ X27 )
      | ~ ( l1_pre_topc @ X26 )
      | ~ ( v2_pre_topc @ X26 )
      | ( v2_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t86_tmap_1])).

thf('82',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i,X29: $i,X30: $i] :
      ( ( v2_struct_0 @ X26 )
      | ~ ( v2_pre_topc @ X26 )
      | ~ ( l1_pre_topc @ X26 )
      | ( v2_struct_0 @ X27 )
      | ~ ( m1_pre_topc @ X27 @ X26 )
      | ~ ( v1_funct_1 @ X30 )
      | ~ ( v1_funct_2 @ X30 @ ( u1_struct_0 @ X25 ) @ ( u1_struct_0 @ X24 ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X25 ) @ ( u1_struct_0 @ X24 ) ) ) )
      | ~ ( m1_subset_1 @ X29 @ ( u1_struct_0 @ X27 ) )
      | ( r1_tmap_1 @ X25 @ X24 @ X30 @ X29 )
      | ~ ( r1_tmap_1 @ X27 @ X24 @ ( k3_tmap_1 @ X26 @ X24 @ X25 @ X27 @ X30 ) @ X29 )
      | ~ ( m1_subset_1 @ X29 @ ( u1_struct_0 @ X25 ) )
      | ~ ( m1_pre_topc @ X27 @ X25 )
      | ~ ( v1_tsep_1 @ X27 @ X25 )
      | ~ ( m1_pre_topc @ X25 @ X26 )
      | ( v2_struct_0 @ X25 )
      | ~ ( l1_pre_topc @ X24 )
      | ~ ( v2_pre_topc @ X24 )
      | ( v2_struct_0 @ X24 ) ) ),
    inference(simplify,[status(thm)],['81'])).

thf('83',plain,(
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
    inference('sup-',[status(thm)],['80','82'])).

thf('84',plain,
    ( ( k2_struct_0 @ sk_C )
    = ( u1_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['78','79'])).

thf('85',plain,
    ( ( k2_struct_0 @ sk_C )
    = ( u1_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['78','79'])).

thf('86',plain,(
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
    inference(demod,[status(thm)],['83','84','85'])).

thf('87',plain,(
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
    inference('sup-',[status(thm)],['75','86'])).

thf('88',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,
    ( ( u1_struct_0 @ sk_C )
    = ( u1_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['45','57'])).

thf('91',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['89','90'])).

thf('92',plain,
    ( ( u1_struct_0 @ sk_C )
    = ( k2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['66','73'])).

thf('93',plain,(
    v1_funct_2 @ sk_E @ ( k2_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['91','92'])).

thf('94',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
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
    inference(demod,[status(thm)],['87','88','93','94','95'])).

thf('97',plain,
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
    inference('sup-',[status(thm)],['3','96'])).

thf('98',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(demod,[status(thm)],['40','41'])).

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

thf('101',plain,
    ( ~ ( l1_pre_topc @ sk_D )
    | ( m1_subset_1 @ ( u1_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['18','19'])).

thf('103',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['101','102'])).

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

thf('104',plain,(
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

thf('105',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v2_pre_topc @ X13 )
      | ~ ( l1_pre_topc @ X13 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X12 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ( v1_tsep_1 @ X12 @ X13 )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ X12 ) @ X13 )
      | ~ ( m1_pre_topc @ X12 @ X13 ) ) ),
    inference(simplify,[status(thm)],['104'])).

thf('106',plain,
    ( ~ ( m1_pre_topc @ sk_C @ sk_D )
    | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_C ) @ sk_D )
    | ( v1_tsep_1 @ sk_C @ sk_D )
    | ~ ( l1_pre_topc @ sk_D )
    | ~ ( v2_pre_topc @ sk_D ) ),
    inference('sup-',[status(thm)],['103','105'])).

thf('107',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(demod,[status(thm)],['40','41'])).

thf('108',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['18','19'])).

thf('109',plain,(
    v2_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['31','32','33'])).

thf('110',plain,
    ( ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_C ) @ sk_D )
    | ( v1_tsep_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['106','107','108','109'])).

thf('111',plain,
    ( ( u1_struct_0 @ sk_C )
    = ( k2_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['62','65'])).

thf('112',plain,(
    ! [X5: $i] :
      ( ( ( k2_struct_0 @ X5 )
        = ( u1_struct_0 @ X5 ) )
      | ~ ( l1_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('113',plain,(
    m1_pre_topc @ sk_D @ sk_C ),
    inference(demod,[status(thm)],['15','20','21'])).

thf('114',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( l1_pre_topc @ X9 )
      | ~ ( m1_pre_topc @ X10 @ X9 )
      | ( m1_pre_topc @ X10 @ ( g1_pre_topc @ ( u1_struct_0 @ X9 ) @ ( u1_pre_topc @ X9 ) ) )
      | ~ ( l1_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[t65_pre_topc])).

thf('115',plain,
    ( ~ ( l1_pre_topc @ sk_D )
    | ( m1_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) ) )
    | ~ ( l1_pre_topc @ sk_C ) ),
    inference('sup-',[status(thm)],['113','114'])).

thf('116',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['18','19'])).

thf('117',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) )
    = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['11','12'])).

thf('119',plain,(
    m1_pre_topc @ sk_D @ sk_D ),
    inference(demod,[status(thm)],['115','116','117','118'])).

thf('120',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( m1_pre_topc @ X15 @ X16 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X15 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( l1_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('121',plain,
    ( ~ ( l1_pre_topc @ sk_D )
    | ( m1_subset_1 @ ( u1_struct_0 @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['119','120'])).

thf('122',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['18','19'])).

thf('123',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['121','122'])).

thf('124',plain,(
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

thf('125',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v2_pre_topc @ X13 )
      | ~ ( l1_pre_topc @ X13 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X12 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ( v3_pre_topc @ ( u1_struct_0 @ X12 ) @ X13 )
      | ~ ( v1_tsep_1 @ X12 @ X13 )
      | ~ ( m1_pre_topc @ X12 @ X13 ) ) ),
    inference(simplify,[status(thm)],['124'])).

thf('126',plain,
    ( ~ ( m1_pre_topc @ sk_D @ sk_D )
    | ~ ( v1_tsep_1 @ sk_D @ sk_D )
    | ( v3_pre_topc @ ( u1_struct_0 @ sk_D ) @ sk_D )
    | ~ ( l1_pre_topc @ sk_D )
    | ~ ( v2_pre_topc @ sk_D ) ),
    inference('sup-',[status(thm)],['123','125'])).

thf('127',plain,(
    m1_pre_topc @ sk_D @ sk_D ),
    inference(demod,[status(thm)],['115','116','117','118'])).

thf('128',plain,(
    m1_pre_topc @ sk_D @ sk_D ),
    inference(demod,[status(thm)],['115','116','117','118'])).

thf(fc10_tops_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( v3_pre_topc @ ( k2_struct_0 @ A ) @ A ) ) )).

thf('129',plain,(
    ! [X11: $i] :
      ( ( v3_pre_topc @ ( k2_struct_0 @ X11 ) @ X11 )
      | ~ ( l1_pre_topc @ X11 )
      | ~ ( v2_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[fc10_tops_1])).

thf('130',plain,(
    ! [X5: $i] :
      ( ( ( k2_struct_0 @ X5 )
        = ( u1_struct_0 @ X5 ) )
      | ~ ( l1_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('131',plain,(
    ! [X17: $i] :
      ( ( m1_pre_topc @ X17 @ X17 )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('132',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( m1_pre_topc @ X15 @ X16 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X15 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( l1_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('133',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['131','132'])).

thf('134',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['133'])).

thf('135',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v2_pre_topc @ X13 )
      | ~ ( l1_pre_topc @ X13 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X12 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ( v1_tsep_1 @ X12 @ X13 )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ X12 ) @ X13 )
      | ~ ( m1_pre_topc @ X12 @ X13 ) ) ),
    inference(simplify,[status(thm)],['104'])).

thf('136',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X0 )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 )
      | ( v1_tsep_1 @ X0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['134','135'])).

thf('137',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ( v1_tsep_1 @ X0 @ X0 )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['136'])).

thf('138',plain,(
    ! [X0: $i] :
      ( ~ ( v3_pre_topc @ ( k2_struct_0 @ X0 ) @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X0 )
      | ( v1_tsep_1 @ X0 @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['130','137'])).

thf('139',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v1_tsep_1 @ X0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['129','138'])).

thf('140',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X0 )
      | ( v1_tsep_1 @ X0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['139'])).

thf('141',plain,
    ( ~ ( v2_pre_topc @ sk_D )
    | ~ ( l1_pre_topc @ sk_D )
    | ( v1_tsep_1 @ sk_D @ sk_D )
    | ~ ( l1_struct_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['128','140'])).

thf('142',plain,(
    v2_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['31','32','33'])).

thf('143',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['18','19'])).

thf('144',plain,(
    l1_struct_0 @ sk_D ),
    inference('sup-',[status(thm)],['63','64'])).

thf('145',plain,(
    v1_tsep_1 @ sk_D @ sk_D ),
    inference(demod,[status(thm)],['141','142','143','144'])).

thf('146',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['18','19'])).

thf('147',plain,(
    v2_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['31','32','33'])).

thf('148',plain,(
    v3_pre_topc @ ( u1_struct_0 @ sk_D ) @ sk_D ),
    inference(demod,[status(thm)],['126','127','145','146','147'])).

thf('149',plain,
    ( ( v3_pre_topc @ ( k2_struct_0 @ sk_D ) @ sk_D )
    | ~ ( l1_struct_0 @ sk_D ) ),
    inference('sup+',[status(thm)],['112','148'])).

thf('150',plain,(
    l1_struct_0 @ sk_D ),
    inference('sup-',[status(thm)],['63','64'])).

thf('151',plain,(
    v3_pre_topc @ ( k2_struct_0 @ sk_D ) @ sk_D ),
    inference(demod,[status(thm)],['149','150'])).

thf('152',plain,(
    v1_tsep_1 @ sk_C @ sk_D ),
    inference(demod,[status(thm)],['110','111','151'])).

thf('153',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(demod,[status(thm)],['40','41'])).

thf('154',plain,(
    ! [X5: $i] :
      ( ( ( k2_struct_0 @ X5 )
        = ( u1_struct_0 @ X5 ) )
      | ~ ( l1_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('155',plain,(
    m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('156',plain,(
    sk_F = sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('157',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['155','156'])).

thf('158',plain,
    ( ( m1_subset_1 @ sk_F @ ( k2_struct_0 @ sk_C ) )
    | ~ ( l1_struct_0 @ sk_C ) ),
    inference('sup+',[status(thm)],['154','157'])).

thf('159',plain,(
    l1_struct_0 @ sk_C ),
    inference('sup-',[status(thm)],['70','71'])).

thf('160',plain,(
    m1_subset_1 @ sk_F @ ( k2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['158','159'])).

thf('161',plain,
    ( ( u1_struct_0 @ sk_C )
    = ( k2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['66','73'])).

thf('162',plain,(
    m1_subset_1 @ sk_F @ ( k2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['158','159'])).

thf('163',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('164',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('165',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('166',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['97','98','152','153','160','161','162','163','164','165'])).

thf('167',plain,(
    ~ ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('168',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['166','167'])).

thf('169',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('170',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['168','169'])).

thf('171',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('172',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C ) ),
    inference(clc,[status(thm)],['170','171'])).

thf('173',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('174',plain,(
    v2_struct_0 @ sk_C ),
    inference(clc,[status(thm)],['172','173'])).

thf('175',plain,(
    $false ),
    inference(demod,[status(thm)],['0','174'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.BZptGvbdQ8
% 0.13/0.35  % Computer   : n019.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 14:16:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.55/0.73  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.55/0.73  % Solved by: fo/fo7.sh
% 0.55/0.73  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.55/0.73  % done 528 iterations in 0.261s
% 0.55/0.73  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.55/0.73  % SZS output start Refutation
% 0.55/0.73  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.55/0.73  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.55/0.73  thf(v1_tsep_1_type, type, v1_tsep_1: $i > $i > $o).
% 0.55/0.73  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.55/0.73  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 0.55/0.73  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.55/0.73  thf(sk_F_type, type, sk_F: $i).
% 0.55/0.73  thf(sk_G_type, type, sk_G: $i).
% 0.55/0.73  thf(sk_D_type, type, sk_D: $i).
% 0.55/0.73  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.55/0.73  thf(sk_E_type, type, sk_E: $i).
% 0.55/0.73  thf(r1_tmap_1_type, type, r1_tmap_1: $i > $i > $i > $i > $o).
% 0.55/0.73  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.55/0.73  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.55/0.73  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.55/0.73  thf(sk_C_type, type, sk_C: $i).
% 0.55/0.73  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.55/0.73  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.55/0.73  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.55/0.73  thf(g1_pre_topc_type, type, g1_pre_topc: $i > $i > $i).
% 0.55/0.73  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.55/0.73  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.55/0.73  thf(k3_tmap_1_type, type, k3_tmap_1: $i > $i > $i > $i > $i > $i).
% 0.55/0.73  thf(sk_B_type, type, sk_B: $i).
% 0.55/0.73  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.55/0.73  thf(sk_A_type, type, sk_A: $i).
% 0.55/0.73  thf(t88_tmap_1, conjecture,
% 0.55/0.73    (![A:$i]:
% 0.55/0.73     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.55/0.73       ( ![B:$i]:
% 0.55/0.73         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.55/0.73             ( l1_pre_topc @ B ) ) =>
% 0.55/0.73           ( ![C:$i]:
% 0.55/0.73             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.55/0.73               ( ![D:$i]:
% 0.55/0.73                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.55/0.73                   ( ![E:$i]:
% 0.55/0.73                     ( ( ( v1_funct_1 @ E ) & 
% 0.55/0.73                         ( v1_funct_2 @
% 0.55/0.73                           E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 0.55/0.73                         ( m1_subset_1 @
% 0.55/0.73                           E @ 
% 0.55/0.73                           ( k1_zfmisc_1 @
% 0.55/0.73                             ( k2_zfmisc_1 @
% 0.55/0.73                               ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.55/0.73                       ( ( ( g1_pre_topc @
% 0.55/0.73                             ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) ) =
% 0.55/0.73                           ( D ) ) =>
% 0.55/0.73                         ( ![F:$i]:
% 0.55/0.73                           ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 0.55/0.73                             ( ![G:$i]:
% 0.55/0.73                               ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) ) =>
% 0.55/0.73                                 ( ( ( ( F ) = ( G ) ) & 
% 0.55/0.73                                     ( r1_tmap_1 @
% 0.55/0.73                                       C @ B @ 
% 0.55/0.73                                       ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ G ) ) =>
% 0.55/0.73                                   ( r1_tmap_1 @ D @ B @ E @ F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.55/0.73  thf(zf_stmt_0, negated_conjecture,
% 0.55/0.73    (~( ![A:$i]:
% 0.55/0.73        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.55/0.73            ( l1_pre_topc @ A ) ) =>
% 0.55/0.73          ( ![B:$i]:
% 0.55/0.73            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.55/0.73                ( l1_pre_topc @ B ) ) =>
% 0.55/0.73              ( ![C:$i]:
% 0.55/0.73                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.55/0.73                  ( ![D:$i]:
% 0.55/0.73                    ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.55/0.73                      ( ![E:$i]:
% 0.55/0.73                        ( ( ( v1_funct_1 @ E ) & 
% 0.55/0.73                            ( v1_funct_2 @
% 0.55/0.73                              E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 0.55/0.73                            ( m1_subset_1 @
% 0.55/0.73                              E @ 
% 0.55/0.73                              ( k1_zfmisc_1 @
% 0.55/0.73                                ( k2_zfmisc_1 @
% 0.55/0.73                                  ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.55/0.73                          ( ( ( g1_pre_topc @
% 0.55/0.73                                ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) ) =
% 0.55/0.73                              ( D ) ) =>
% 0.55/0.73                            ( ![F:$i]:
% 0.55/0.73                              ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 0.55/0.73                                ( ![G:$i]:
% 0.55/0.73                                  ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) ) =>
% 0.55/0.73                                    ( ( ( ( F ) = ( G ) ) & 
% 0.55/0.73                                        ( r1_tmap_1 @
% 0.55/0.73                                          C @ B @ 
% 0.55/0.73                                          ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ G ) ) =>
% 0.55/0.73                                      ( r1_tmap_1 @ D @ B @ E @ F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.55/0.73    inference('cnf.neg', [status(esa)], [t88_tmap_1])).
% 0.55/0.73  thf('0', plain, (~ (v2_struct_0 @ sk_C)),
% 0.55/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.73  thf('1', plain,
% 0.55/0.73      ((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.55/0.73        (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_G)),
% 0.55/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.73  thf('2', plain, (((sk_F) = (sk_G))),
% 0.55/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.73  thf('3', plain,
% 0.55/0.73      ((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.55/0.73        (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_F)),
% 0.55/0.73      inference('demod', [status(thm)], ['1', '2'])).
% 0.55/0.73  thf('4', plain,
% 0.55/0.73      ((m1_subset_1 @ sk_E @ 
% 0.55/0.73        (k1_zfmisc_1 @ 
% 0.55/0.73         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 0.55/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.73  thf(t2_tsep_1, axiom,
% 0.55/0.73    (![A:$i]: ( ( l1_pre_topc @ A ) => ( m1_pre_topc @ A @ A ) ))).
% 0.55/0.73  thf('5', plain,
% 0.55/0.73      (![X17 : $i]: ((m1_pre_topc @ X17 @ X17) | ~ (l1_pre_topc @ X17))),
% 0.55/0.73      inference('cnf', [status(esa)], [t2_tsep_1])).
% 0.55/0.73  thf('6', plain,
% 0.55/0.73      (((g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) = (sk_D))),
% 0.55/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.73  thf(t65_pre_topc, axiom,
% 0.55/0.73    (![A:$i]:
% 0.55/0.73     ( ( l1_pre_topc @ A ) =>
% 0.55/0.73       ( ![B:$i]:
% 0.55/0.73         ( ( l1_pre_topc @ B ) =>
% 0.55/0.73           ( ( m1_pre_topc @ A @ B ) <=>
% 0.55/0.73             ( m1_pre_topc @
% 0.55/0.73               A @ ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ) ))).
% 0.55/0.73  thf('7', plain,
% 0.55/0.73      (![X9 : $i, X10 : $i]:
% 0.55/0.73         (~ (l1_pre_topc @ X9)
% 0.55/0.73          | ~ (m1_pre_topc @ X10 @ 
% 0.55/0.73               (g1_pre_topc @ (u1_struct_0 @ X9) @ (u1_pre_topc @ X9)))
% 0.55/0.73          | (m1_pre_topc @ X10 @ X9)
% 0.55/0.73          | ~ (l1_pre_topc @ X10))),
% 0.55/0.73      inference('cnf', [status(esa)], [t65_pre_topc])).
% 0.55/0.73  thf('8', plain,
% 0.55/0.73      (![X0 : $i]:
% 0.55/0.73         (~ (m1_pre_topc @ X0 @ sk_D)
% 0.55/0.73          | ~ (l1_pre_topc @ X0)
% 0.55/0.73          | (m1_pre_topc @ X0 @ sk_C)
% 0.55/0.73          | ~ (l1_pre_topc @ sk_C))),
% 0.55/0.73      inference('sup-', [status(thm)], ['6', '7'])).
% 0.55/0.73  thf('9', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.55/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.73  thf(dt_m1_pre_topc, axiom,
% 0.55/0.73    (![A:$i]:
% 0.55/0.73     ( ( l1_pre_topc @ A ) =>
% 0.55/0.73       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.55/0.73  thf('10', plain,
% 0.55/0.73      (![X7 : $i, X8 : $i]:
% 0.55/0.73         (~ (m1_pre_topc @ X7 @ X8) | (l1_pre_topc @ X7) | ~ (l1_pre_topc @ X8))),
% 0.55/0.73      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.55/0.73  thf('11', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_C))),
% 0.55/0.73      inference('sup-', [status(thm)], ['9', '10'])).
% 0.55/0.73  thf('12', plain, ((l1_pre_topc @ sk_A)),
% 0.55/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.73  thf('13', plain, ((l1_pre_topc @ sk_C)),
% 0.55/0.73      inference('demod', [status(thm)], ['11', '12'])).
% 0.55/0.73  thf('14', plain,
% 0.55/0.73      (![X0 : $i]:
% 0.55/0.73         (~ (m1_pre_topc @ X0 @ sk_D)
% 0.55/0.73          | ~ (l1_pre_topc @ X0)
% 0.55/0.73          | (m1_pre_topc @ X0 @ sk_C))),
% 0.55/0.73      inference('demod', [status(thm)], ['8', '13'])).
% 0.55/0.73  thf('15', plain,
% 0.55/0.73      ((~ (l1_pre_topc @ sk_D)
% 0.55/0.73        | (m1_pre_topc @ sk_D @ sk_C)
% 0.55/0.73        | ~ (l1_pre_topc @ sk_D))),
% 0.55/0.73      inference('sup-', [status(thm)], ['5', '14'])).
% 0.55/0.73  thf('16', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.55/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.73  thf('17', plain,
% 0.55/0.73      (![X7 : $i, X8 : $i]:
% 0.55/0.73         (~ (m1_pre_topc @ X7 @ X8) | (l1_pre_topc @ X7) | ~ (l1_pre_topc @ X8))),
% 0.55/0.73      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.55/0.73  thf('18', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_D))),
% 0.55/0.73      inference('sup-', [status(thm)], ['16', '17'])).
% 0.55/0.73  thf('19', plain, ((l1_pre_topc @ sk_A)),
% 0.55/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.73  thf('20', plain, ((l1_pre_topc @ sk_D)),
% 0.55/0.73      inference('demod', [status(thm)], ['18', '19'])).
% 0.55/0.73  thf('21', plain, ((l1_pre_topc @ sk_D)),
% 0.55/0.73      inference('demod', [status(thm)], ['18', '19'])).
% 0.55/0.73  thf('22', plain, ((m1_pre_topc @ sk_D @ sk_C)),
% 0.55/0.73      inference('demod', [status(thm)], ['15', '20', '21'])).
% 0.55/0.73  thf('23', plain,
% 0.55/0.73      (![X17 : $i]: ((m1_pre_topc @ X17 @ X17) | ~ (l1_pre_topc @ X17))),
% 0.55/0.73      inference('cnf', [status(esa)], [t2_tsep_1])).
% 0.55/0.73  thf(t4_tsep_1, axiom,
% 0.55/0.73    (![A:$i]:
% 0.55/0.73     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.55/0.73       ( ![B:$i]:
% 0.55/0.73         ( ( m1_pre_topc @ B @ A ) =>
% 0.55/0.73           ( ![C:$i]:
% 0.55/0.73             ( ( m1_pre_topc @ C @ A ) =>
% 0.55/0.73               ( ( r1_tarski @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ C ) ) <=>
% 0.55/0.73                 ( m1_pre_topc @ B @ C ) ) ) ) ) ) ))).
% 0.55/0.73  thf('24', plain,
% 0.55/0.73      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.55/0.73         (~ (m1_pre_topc @ X18 @ X19)
% 0.55/0.73          | ~ (m1_pre_topc @ X18 @ X20)
% 0.55/0.73          | (r1_tarski @ (u1_struct_0 @ X18) @ (u1_struct_0 @ X20))
% 0.55/0.73          | ~ (m1_pre_topc @ X20 @ X19)
% 0.55/0.73          | ~ (l1_pre_topc @ X19)
% 0.55/0.73          | ~ (v2_pre_topc @ X19))),
% 0.55/0.73      inference('cnf', [status(esa)], [t4_tsep_1])).
% 0.55/0.73  thf('25', plain,
% 0.55/0.73      (![X0 : $i, X1 : $i]:
% 0.55/0.73         (~ (l1_pre_topc @ X0)
% 0.55/0.73          | ~ (v2_pre_topc @ X0)
% 0.55/0.73          | ~ (l1_pre_topc @ X0)
% 0.55/0.73          | ~ (m1_pre_topc @ X1 @ X0)
% 0.55/0.73          | (r1_tarski @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X1))
% 0.55/0.73          | ~ (m1_pre_topc @ X0 @ X1))),
% 0.55/0.73      inference('sup-', [status(thm)], ['23', '24'])).
% 0.55/0.73  thf('26', plain,
% 0.55/0.73      (![X0 : $i, X1 : $i]:
% 0.55/0.73         (~ (m1_pre_topc @ X0 @ X1)
% 0.55/0.73          | (r1_tarski @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X1))
% 0.55/0.73          | ~ (m1_pre_topc @ X1 @ X0)
% 0.55/0.73          | ~ (v2_pre_topc @ X0)
% 0.55/0.73          | ~ (l1_pre_topc @ X0))),
% 0.55/0.73      inference('simplify', [status(thm)], ['25'])).
% 0.55/0.73  thf('27', plain,
% 0.55/0.73      ((~ (l1_pre_topc @ sk_D)
% 0.55/0.73        | ~ (v2_pre_topc @ sk_D)
% 0.55/0.73        | ~ (m1_pre_topc @ sk_C @ sk_D)
% 0.55/0.73        | (r1_tarski @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_C)))),
% 0.55/0.73      inference('sup-', [status(thm)], ['22', '26'])).
% 0.55/0.73  thf('28', plain, ((l1_pre_topc @ sk_D)),
% 0.55/0.73      inference('demod', [status(thm)], ['18', '19'])).
% 0.55/0.73  thf('29', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.55/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.73  thf(cc1_pre_topc, axiom,
% 0.55/0.73    (![A:$i]:
% 0.55/0.73     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.55/0.73       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( v2_pre_topc @ B ) ) ) ))).
% 0.55/0.73  thf('30', plain,
% 0.55/0.73      (![X3 : $i, X4 : $i]:
% 0.55/0.73         (~ (m1_pre_topc @ X3 @ X4)
% 0.55/0.73          | (v2_pre_topc @ X3)
% 0.55/0.73          | ~ (l1_pre_topc @ X4)
% 0.55/0.73          | ~ (v2_pre_topc @ X4))),
% 0.55/0.73      inference('cnf', [status(esa)], [cc1_pre_topc])).
% 0.55/0.73  thf('31', plain,
% 0.55/0.73      ((~ (v2_pre_topc @ sk_A) | ~ (l1_pre_topc @ sk_A) | (v2_pre_topc @ sk_D))),
% 0.55/0.73      inference('sup-', [status(thm)], ['29', '30'])).
% 0.55/0.73  thf('32', plain, ((v2_pre_topc @ sk_A)),
% 0.55/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.73  thf('33', plain, ((l1_pre_topc @ sk_A)),
% 0.55/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.73  thf('34', plain, ((v2_pre_topc @ sk_D)),
% 0.55/0.73      inference('demod', [status(thm)], ['31', '32', '33'])).
% 0.55/0.73  thf('35', plain,
% 0.55/0.73      (((g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) = (sk_D))),
% 0.55/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.73  thf('36', plain,
% 0.55/0.73      (![X17 : $i]: ((m1_pre_topc @ X17 @ X17) | ~ (l1_pre_topc @ X17))),
% 0.55/0.73      inference('cnf', [status(esa)], [t2_tsep_1])).
% 0.55/0.73  thf('37', plain,
% 0.55/0.73      (![X9 : $i, X10 : $i]:
% 0.55/0.73         (~ (l1_pre_topc @ X9)
% 0.55/0.73          | ~ (m1_pre_topc @ X10 @ X9)
% 0.55/0.73          | (m1_pre_topc @ X10 @ 
% 0.55/0.73             (g1_pre_topc @ (u1_struct_0 @ X9) @ (u1_pre_topc @ X9)))
% 0.55/0.73          | ~ (l1_pre_topc @ X10))),
% 0.55/0.73      inference('cnf', [status(esa)], [t65_pre_topc])).
% 0.55/0.73  thf('38', plain,
% 0.55/0.73      (![X0 : $i]:
% 0.55/0.73         (~ (l1_pre_topc @ X0)
% 0.55/0.73          | ~ (l1_pre_topc @ X0)
% 0.55/0.73          | (m1_pre_topc @ X0 @ 
% 0.55/0.73             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.55/0.73          | ~ (l1_pre_topc @ X0))),
% 0.55/0.73      inference('sup-', [status(thm)], ['36', '37'])).
% 0.55/0.73  thf('39', plain,
% 0.55/0.73      (![X0 : $i]:
% 0.55/0.73         ((m1_pre_topc @ X0 @ 
% 0.55/0.73           (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.55/0.73          | ~ (l1_pre_topc @ X0))),
% 0.55/0.73      inference('simplify', [status(thm)], ['38'])).
% 0.55/0.73  thf('40', plain, (((m1_pre_topc @ sk_C @ sk_D) | ~ (l1_pre_topc @ sk_C))),
% 0.55/0.73      inference('sup+', [status(thm)], ['35', '39'])).
% 0.55/0.73  thf('41', plain, ((l1_pre_topc @ sk_C)),
% 0.55/0.73      inference('demod', [status(thm)], ['11', '12'])).
% 0.55/0.73  thf('42', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 0.55/0.73      inference('demod', [status(thm)], ['40', '41'])).
% 0.55/0.73  thf('43', plain, ((r1_tarski @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_C))),
% 0.55/0.73      inference('demod', [status(thm)], ['27', '28', '34', '42'])).
% 0.55/0.73  thf(d10_xboole_0, axiom,
% 0.55/0.73    (![A:$i,B:$i]:
% 0.55/0.73     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.55/0.73  thf('44', plain,
% 0.55/0.73      (![X0 : $i, X2 : $i]:
% 0.55/0.73         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.55/0.73      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.55/0.73  thf('45', plain,
% 0.55/0.73      ((~ (r1_tarski @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D))
% 0.55/0.73        | ((u1_struct_0 @ sk_C) = (u1_struct_0 @ sk_D)))),
% 0.55/0.73      inference('sup-', [status(thm)], ['43', '44'])).
% 0.55/0.73  thf('46', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 0.55/0.73      inference('demod', [status(thm)], ['40', '41'])).
% 0.55/0.73  thf('47', plain,
% 0.55/0.73      (![X0 : $i, X1 : $i]:
% 0.55/0.73         (~ (m1_pre_topc @ X0 @ X1)
% 0.55/0.73          | (r1_tarski @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X1))
% 0.55/0.73          | ~ (m1_pre_topc @ X1 @ X0)
% 0.55/0.73          | ~ (v2_pre_topc @ X0)
% 0.55/0.73          | ~ (l1_pre_topc @ X0))),
% 0.55/0.73      inference('simplify', [status(thm)], ['25'])).
% 0.55/0.73  thf('48', plain,
% 0.55/0.73      ((~ (l1_pre_topc @ sk_C)
% 0.55/0.73        | ~ (v2_pre_topc @ sk_C)
% 0.55/0.73        | ~ (m1_pre_topc @ sk_D @ sk_C)
% 0.55/0.73        | (r1_tarski @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D)))),
% 0.55/0.73      inference('sup-', [status(thm)], ['46', '47'])).
% 0.55/0.73  thf('49', plain, ((l1_pre_topc @ sk_C)),
% 0.55/0.73      inference('demod', [status(thm)], ['11', '12'])).
% 0.55/0.73  thf('50', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.55/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.73  thf('51', plain,
% 0.55/0.73      (![X3 : $i, X4 : $i]:
% 0.55/0.73         (~ (m1_pre_topc @ X3 @ X4)
% 0.55/0.73          | (v2_pre_topc @ X3)
% 0.55/0.73          | ~ (l1_pre_topc @ X4)
% 0.55/0.73          | ~ (v2_pre_topc @ X4))),
% 0.55/0.73      inference('cnf', [status(esa)], [cc1_pre_topc])).
% 0.55/0.73  thf('52', plain,
% 0.55/0.73      ((~ (v2_pre_topc @ sk_A) | ~ (l1_pre_topc @ sk_A) | (v2_pre_topc @ sk_C))),
% 0.55/0.73      inference('sup-', [status(thm)], ['50', '51'])).
% 0.55/0.73  thf('53', plain, ((v2_pre_topc @ sk_A)),
% 0.55/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.73  thf('54', plain, ((l1_pre_topc @ sk_A)),
% 0.55/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.73  thf('55', plain, ((v2_pre_topc @ sk_C)),
% 0.55/0.73      inference('demod', [status(thm)], ['52', '53', '54'])).
% 0.55/0.73  thf('56', plain, ((m1_pre_topc @ sk_D @ sk_C)),
% 0.55/0.73      inference('demod', [status(thm)], ['15', '20', '21'])).
% 0.55/0.73  thf('57', plain, ((r1_tarski @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D))),
% 0.55/0.73      inference('demod', [status(thm)], ['48', '49', '55', '56'])).
% 0.55/0.73  thf('58', plain, (((u1_struct_0 @ sk_C) = (u1_struct_0 @ sk_D))),
% 0.55/0.73      inference('demod', [status(thm)], ['45', '57'])).
% 0.55/0.73  thf('59', plain,
% 0.55/0.73      ((m1_subset_1 @ sk_E @ 
% 0.55/0.73        (k1_zfmisc_1 @ 
% 0.55/0.73         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 0.55/0.73      inference('demod', [status(thm)], ['4', '58'])).
% 0.55/0.73  thf(d3_struct_0, axiom,
% 0.55/0.73    (![A:$i]:
% 0.55/0.73     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.55/0.73  thf('60', plain,
% 0.55/0.73      (![X5 : $i]:
% 0.55/0.73         (((k2_struct_0 @ X5) = (u1_struct_0 @ X5)) | ~ (l1_struct_0 @ X5))),
% 0.55/0.73      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.55/0.73  thf('61', plain, (((u1_struct_0 @ sk_C) = (u1_struct_0 @ sk_D))),
% 0.55/0.73      inference('demod', [status(thm)], ['45', '57'])).
% 0.55/0.73  thf('62', plain,
% 0.55/0.73      ((((u1_struct_0 @ sk_C) = (k2_struct_0 @ sk_D)) | ~ (l1_struct_0 @ sk_D))),
% 0.55/0.73      inference('sup+', [status(thm)], ['60', '61'])).
% 0.55/0.73  thf('63', plain, ((l1_pre_topc @ sk_D)),
% 0.55/0.73      inference('demod', [status(thm)], ['18', '19'])).
% 0.55/0.73  thf(dt_l1_pre_topc, axiom,
% 0.55/0.73    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.55/0.73  thf('64', plain, (![X6 : $i]: ((l1_struct_0 @ X6) | ~ (l1_pre_topc @ X6))),
% 0.55/0.73      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.55/0.73  thf('65', plain, ((l1_struct_0 @ sk_D)),
% 0.55/0.73      inference('sup-', [status(thm)], ['63', '64'])).
% 0.55/0.73  thf('66', plain, (((u1_struct_0 @ sk_C) = (k2_struct_0 @ sk_D))),
% 0.55/0.73      inference('demod', [status(thm)], ['62', '65'])).
% 0.55/0.73  thf('67', plain,
% 0.55/0.73      (![X5 : $i]:
% 0.55/0.73         (((k2_struct_0 @ X5) = (u1_struct_0 @ X5)) | ~ (l1_struct_0 @ X5))),
% 0.55/0.73      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.55/0.73  thf('68', plain, (((u1_struct_0 @ sk_C) = (k2_struct_0 @ sk_D))),
% 0.55/0.73      inference('demod', [status(thm)], ['62', '65'])).
% 0.55/0.73  thf('69', plain,
% 0.55/0.73      ((((k2_struct_0 @ sk_C) = (k2_struct_0 @ sk_D)) | ~ (l1_struct_0 @ sk_C))),
% 0.55/0.73      inference('sup+', [status(thm)], ['67', '68'])).
% 0.55/0.73  thf('70', plain, ((l1_pre_topc @ sk_C)),
% 0.55/0.73      inference('demod', [status(thm)], ['11', '12'])).
% 0.55/0.73  thf('71', plain, (![X6 : $i]: ((l1_struct_0 @ X6) | ~ (l1_pre_topc @ X6))),
% 0.55/0.73      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.55/0.73  thf('72', plain, ((l1_struct_0 @ sk_C)),
% 0.55/0.73      inference('sup-', [status(thm)], ['70', '71'])).
% 0.55/0.73  thf('73', plain, (((k2_struct_0 @ sk_C) = (k2_struct_0 @ sk_D))),
% 0.55/0.73      inference('demod', [status(thm)], ['69', '72'])).
% 0.55/0.73  thf('74', plain, (((u1_struct_0 @ sk_C) = (k2_struct_0 @ sk_C))),
% 0.55/0.73      inference('demod', [status(thm)], ['66', '73'])).
% 0.55/0.73  thf('75', plain,
% 0.55/0.73      ((m1_subset_1 @ sk_E @ 
% 0.55/0.73        (k1_zfmisc_1 @ 
% 0.55/0.73         (k2_zfmisc_1 @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 0.55/0.73      inference('demod', [status(thm)], ['59', '74'])).
% 0.55/0.73  thf('76', plain, (((u1_struct_0 @ sk_C) = (u1_struct_0 @ sk_D))),
% 0.55/0.73      inference('demod', [status(thm)], ['45', '57'])).
% 0.55/0.73  thf('77', plain, (((u1_struct_0 @ sk_C) = (k2_struct_0 @ sk_D))),
% 0.55/0.73      inference('demod', [status(thm)], ['62', '65'])).
% 0.55/0.73  thf('78', plain, (((k2_struct_0 @ sk_D) = (u1_struct_0 @ sk_D))),
% 0.55/0.73      inference('demod', [status(thm)], ['76', '77'])).
% 0.55/0.73  thf('79', plain, (((k2_struct_0 @ sk_C) = (k2_struct_0 @ sk_D))),
% 0.55/0.73      inference('demod', [status(thm)], ['69', '72'])).
% 0.55/0.73  thf('80', plain, (((k2_struct_0 @ sk_C) = (u1_struct_0 @ sk_D))),
% 0.55/0.73      inference('demod', [status(thm)], ['78', '79'])).
% 0.55/0.73  thf(t86_tmap_1, axiom,
% 0.55/0.73    (![A:$i]:
% 0.55/0.73     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.55/0.73       ( ![B:$i]:
% 0.55/0.73         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.55/0.73             ( l1_pre_topc @ B ) ) =>
% 0.55/0.73           ( ![C:$i]:
% 0.55/0.73             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.55/0.73               ( ![D:$i]:
% 0.55/0.73                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.55/0.73                   ( ![E:$i]:
% 0.55/0.73                     ( ( ( v1_funct_1 @ E ) & 
% 0.55/0.73                         ( v1_funct_2 @
% 0.55/0.73                           E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 0.55/0.73                         ( m1_subset_1 @
% 0.55/0.73                           E @ 
% 0.55/0.73                           ( k1_zfmisc_1 @
% 0.55/0.73                             ( k2_zfmisc_1 @
% 0.55/0.73                               ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.55/0.73                       ( ( ( v1_tsep_1 @ C @ D ) & ( m1_pre_topc @ C @ D ) ) =>
% 0.55/0.73                         ( ![F:$i]:
% 0.55/0.73                           ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 0.55/0.73                             ( ![G:$i]:
% 0.55/0.73                               ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) ) =>
% 0.55/0.73                                 ( ( ( F ) = ( G ) ) =>
% 0.55/0.73                                   ( ( r1_tmap_1 @ D @ B @ E @ F ) <=>
% 0.55/0.73                                     ( r1_tmap_1 @
% 0.55/0.73                                       C @ B @ 
% 0.55/0.73                                       ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ G ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.55/0.73  thf('81', plain,
% 0.55/0.73      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 0.55/0.73         ((v2_struct_0 @ X24)
% 0.55/0.73          | ~ (v2_pre_topc @ X24)
% 0.55/0.73          | ~ (l1_pre_topc @ X24)
% 0.55/0.73          | (v2_struct_0 @ X25)
% 0.55/0.73          | ~ (m1_pre_topc @ X25 @ X26)
% 0.55/0.73          | ~ (v1_tsep_1 @ X27 @ X25)
% 0.55/0.73          | ~ (m1_pre_topc @ X27 @ X25)
% 0.55/0.73          | ~ (m1_subset_1 @ X28 @ (u1_struct_0 @ X25))
% 0.55/0.73          | ((X28) != (X29))
% 0.55/0.73          | ~ (r1_tmap_1 @ X27 @ X24 @ 
% 0.55/0.73               (k3_tmap_1 @ X26 @ X24 @ X25 @ X27 @ X30) @ X29)
% 0.55/0.73          | (r1_tmap_1 @ X25 @ X24 @ X30 @ X28)
% 0.55/0.73          | ~ (m1_subset_1 @ X29 @ (u1_struct_0 @ X27))
% 0.55/0.73          | ~ (m1_subset_1 @ X30 @ 
% 0.55/0.73               (k1_zfmisc_1 @ 
% 0.55/0.73                (k2_zfmisc_1 @ (u1_struct_0 @ X25) @ (u1_struct_0 @ X24))))
% 0.55/0.73          | ~ (v1_funct_2 @ X30 @ (u1_struct_0 @ X25) @ (u1_struct_0 @ X24))
% 0.55/0.73          | ~ (v1_funct_1 @ X30)
% 0.55/0.73          | ~ (m1_pre_topc @ X27 @ X26)
% 0.55/0.73          | (v2_struct_0 @ X27)
% 0.55/0.73          | ~ (l1_pre_topc @ X26)
% 0.55/0.73          | ~ (v2_pre_topc @ X26)
% 0.55/0.73          | (v2_struct_0 @ X26))),
% 0.55/0.73      inference('cnf', [status(esa)], [t86_tmap_1])).
% 0.55/0.73  thf('82', plain,
% 0.55/0.73      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i, X29 : $i, X30 : $i]:
% 0.55/0.73         ((v2_struct_0 @ X26)
% 0.55/0.73          | ~ (v2_pre_topc @ X26)
% 0.55/0.73          | ~ (l1_pre_topc @ X26)
% 0.55/0.73          | (v2_struct_0 @ X27)
% 0.55/0.73          | ~ (m1_pre_topc @ X27 @ X26)
% 0.55/0.73          | ~ (v1_funct_1 @ X30)
% 0.55/0.73          | ~ (v1_funct_2 @ X30 @ (u1_struct_0 @ X25) @ (u1_struct_0 @ X24))
% 0.55/0.73          | ~ (m1_subset_1 @ X30 @ 
% 0.55/0.73               (k1_zfmisc_1 @ 
% 0.55/0.73                (k2_zfmisc_1 @ (u1_struct_0 @ X25) @ (u1_struct_0 @ X24))))
% 0.55/0.73          | ~ (m1_subset_1 @ X29 @ (u1_struct_0 @ X27))
% 0.55/0.73          | (r1_tmap_1 @ X25 @ X24 @ X30 @ X29)
% 0.55/0.73          | ~ (r1_tmap_1 @ X27 @ X24 @ 
% 0.55/0.73               (k3_tmap_1 @ X26 @ X24 @ X25 @ X27 @ X30) @ X29)
% 0.55/0.73          | ~ (m1_subset_1 @ X29 @ (u1_struct_0 @ X25))
% 0.55/0.73          | ~ (m1_pre_topc @ X27 @ X25)
% 0.55/0.73          | ~ (v1_tsep_1 @ X27 @ X25)
% 0.55/0.73          | ~ (m1_pre_topc @ X25 @ X26)
% 0.55/0.73          | (v2_struct_0 @ X25)
% 0.55/0.73          | ~ (l1_pre_topc @ X24)
% 0.55/0.73          | ~ (v2_pre_topc @ X24)
% 0.55/0.73          | (v2_struct_0 @ X24))),
% 0.55/0.73      inference('simplify', [status(thm)], ['81'])).
% 0.55/0.73  thf('83', plain,
% 0.55/0.73      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.55/0.73         (~ (m1_subset_1 @ X1 @ 
% 0.55/0.73             (k1_zfmisc_1 @ 
% 0.55/0.73              (k2_zfmisc_1 @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ X0))))
% 0.55/0.73          | (v2_struct_0 @ X0)
% 0.55/0.73          | ~ (v2_pre_topc @ X0)
% 0.55/0.73          | ~ (l1_pre_topc @ X0)
% 0.55/0.73          | (v2_struct_0 @ sk_D)
% 0.55/0.73          | ~ (m1_pre_topc @ sk_D @ X2)
% 0.55/0.73          | ~ (v1_tsep_1 @ X3 @ sk_D)
% 0.55/0.73          | ~ (m1_pre_topc @ X3 @ sk_D)
% 0.55/0.73          | ~ (m1_subset_1 @ X4 @ (u1_struct_0 @ sk_D))
% 0.55/0.73          | ~ (r1_tmap_1 @ X3 @ X0 @ (k3_tmap_1 @ X2 @ X0 @ sk_D @ X3 @ X1) @ 
% 0.55/0.73               X4)
% 0.55/0.73          | (r1_tmap_1 @ sk_D @ X0 @ X1 @ X4)
% 0.55/0.73          | ~ (m1_subset_1 @ X4 @ (u1_struct_0 @ X3))
% 0.55/0.73          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ X0))
% 0.55/0.73          | ~ (v1_funct_1 @ X1)
% 0.55/0.73          | ~ (m1_pre_topc @ X3 @ X2)
% 0.55/0.73          | (v2_struct_0 @ X3)
% 0.55/0.73          | ~ (l1_pre_topc @ X2)
% 0.55/0.73          | ~ (v2_pre_topc @ X2)
% 0.55/0.73          | (v2_struct_0 @ X2))),
% 0.55/0.73      inference('sup-', [status(thm)], ['80', '82'])).
% 0.55/0.73  thf('84', plain, (((k2_struct_0 @ sk_C) = (u1_struct_0 @ sk_D))),
% 0.55/0.73      inference('demod', [status(thm)], ['78', '79'])).
% 0.55/0.73  thf('85', plain, (((k2_struct_0 @ sk_C) = (u1_struct_0 @ sk_D))),
% 0.55/0.73      inference('demod', [status(thm)], ['78', '79'])).
% 0.55/0.73  thf('86', plain,
% 0.55/0.73      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.55/0.73         (~ (m1_subset_1 @ X1 @ 
% 0.55/0.73             (k1_zfmisc_1 @ 
% 0.55/0.73              (k2_zfmisc_1 @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ X0))))
% 0.55/0.73          | (v2_struct_0 @ X0)
% 0.55/0.73          | ~ (v2_pre_topc @ X0)
% 0.55/0.73          | ~ (l1_pre_topc @ X0)
% 0.55/0.73          | (v2_struct_0 @ sk_D)
% 0.55/0.73          | ~ (m1_pre_topc @ sk_D @ X2)
% 0.55/0.73          | ~ (v1_tsep_1 @ X3 @ sk_D)
% 0.55/0.73          | ~ (m1_pre_topc @ X3 @ sk_D)
% 0.55/0.73          | ~ (m1_subset_1 @ X4 @ (k2_struct_0 @ sk_C))
% 0.55/0.73          | ~ (r1_tmap_1 @ X3 @ X0 @ (k3_tmap_1 @ X2 @ X0 @ sk_D @ X3 @ X1) @ 
% 0.55/0.73               X4)
% 0.55/0.73          | (r1_tmap_1 @ sk_D @ X0 @ X1 @ X4)
% 0.55/0.73          | ~ (m1_subset_1 @ X4 @ (u1_struct_0 @ X3))
% 0.55/0.73          | ~ (v1_funct_2 @ X1 @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ X0))
% 0.55/0.73          | ~ (v1_funct_1 @ X1)
% 0.55/0.73          | ~ (m1_pre_topc @ X3 @ X2)
% 0.55/0.73          | (v2_struct_0 @ X3)
% 0.55/0.73          | ~ (l1_pre_topc @ X2)
% 0.55/0.73          | ~ (v2_pre_topc @ X2)
% 0.55/0.73          | (v2_struct_0 @ X2))),
% 0.55/0.73      inference('demod', [status(thm)], ['83', '84', '85'])).
% 0.55/0.73  thf('87', plain,
% 0.55/0.73      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.55/0.73         ((v2_struct_0 @ X0)
% 0.55/0.73          | ~ (v2_pre_topc @ X0)
% 0.55/0.73          | ~ (l1_pre_topc @ X0)
% 0.55/0.73          | (v2_struct_0 @ X1)
% 0.55/0.73          | ~ (m1_pre_topc @ X1 @ X0)
% 0.55/0.73          | ~ (v1_funct_1 @ sk_E)
% 0.55/0.73          | ~ (v1_funct_2 @ sk_E @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))
% 0.55/0.73          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1))
% 0.55/0.73          | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X2)
% 0.55/0.73          | ~ (r1_tmap_1 @ X1 @ sk_B @ 
% 0.55/0.73               (k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E) @ X2)
% 0.55/0.73          | ~ (m1_subset_1 @ X2 @ (k2_struct_0 @ sk_C))
% 0.55/0.73          | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.55/0.73          | ~ (v1_tsep_1 @ X1 @ sk_D)
% 0.55/0.73          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.55/0.73          | (v2_struct_0 @ sk_D)
% 0.55/0.73          | ~ (l1_pre_topc @ sk_B)
% 0.55/0.73          | ~ (v2_pre_topc @ sk_B)
% 0.55/0.73          | (v2_struct_0 @ sk_B))),
% 0.55/0.73      inference('sup-', [status(thm)], ['75', '86'])).
% 0.55/0.73  thf('88', plain, ((v1_funct_1 @ sk_E)),
% 0.55/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.73  thf('89', plain,
% 0.55/0.73      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 0.55/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.73  thf('90', plain, (((u1_struct_0 @ sk_C) = (u1_struct_0 @ sk_D))),
% 0.55/0.73      inference('demod', [status(thm)], ['45', '57'])).
% 0.55/0.73  thf('91', plain,
% 0.55/0.73      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 0.55/0.73      inference('demod', [status(thm)], ['89', '90'])).
% 0.55/0.73  thf('92', plain, (((u1_struct_0 @ sk_C) = (k2_struct_0 @ sk_C))),
% 0.55/0.73      inference('demod', [status(thm)], ['66', '73'])).
% 0.55/0.73  thf('93', plain,
% 0.55/0.73      ((v1_funct_2 @ sk_E @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 0.55/0.73      inference('demod', [status(thm)], ['91', '92'])).
% 0.55/0.73  thf('94', plain, ((l1_pre_topc @ sk_B)),
% 0.55/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.73  thf('95', plain, ((v2_pre_topc @ sk_B)),
% 0.55/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.73  thf('96', plain,
% 0.55/0.73      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.55/0.73         ((v2_struct_0 @ X0)
% 0.55/0.73          | ~ (v2_pre_topc @ X0)
% 0.55/0.73          | ~ (l1_pre_topc @ X0)
% 0.55/0.73          | (v2_struct_0 @ X1)
% 0.55/0.73          | ~ (m1_pre_topc @ X1 @ X0)
% 0.55/0.73          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1))
% 0.55/0.73          | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X2)
% 0.55/0.73          | ~ (r1_tmap_1 @ X1 @ sk_B @ 
% 0.55/0.73               (k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E) @ X2)
% 0.55/0.73          | ~ (m1_subset_1 @ X2 @ (k2_struct_0 @ sk_C))
% 0.55/0.73          | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.55/0.73          | ~ (v1_tsep_1 @ X1 @ sk_D)
% 0.55/0.73          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.55/0.73          | (v2_struct_0 @ sk_D)
% 0.55/0.73          | (v2_struct_0 @ sk_B))),
% 0.55/0.73      inference('demod', [status(thm)], ['87', '88', '93', '94', '95'])).
% 0.55/0.73  thf('97', plain,
% 0.55/0.73      (((v2_struct_0 @ sk_B)
% 0.55/0.73        | (v2_struct_0 @ sk_D)
% 0.55/0.73        | ~ (m1_pre_topc @ sk_D @ sk_A)
% 0.55/0.73        | ~ (v1_tsep_1 @ sk_C @ sk_D)
% 0.55/0.73        | ~ (m1_pre_topc @ sk_C @ sk_D)
% 0.55/0.73        | ~ (m1_subset_1 @ sk_F @ (k2_struct_0 @ sk_C))
% 0.55/0.73        | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)
% 0.55/0.73        | ~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C))
% 0.55/0.73        | ~ (m1_pre_topc @ sk_C @ sk_A)
% 0.55/0.73        | (v2_struct_0 @ sk_C)
% 0.55/0.73        | ~ (l1_pre_topc @ sk_A)
% 0.55/0.73        | ~ (v2_pre_topc @ sk_A)
% 0.55/0.73        | (v2_struct_0 @ sk_A))),
% 0.55/0.73      inference('sup-', [status(thm)], ['3', '96'])).
% 0.55/0.73  thf('98', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.55/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.73  thf('99', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 0.55/0.73      inference('demod', [status(thm)], ['40', '41'])).
% 0.55/0.73  thf(t1_tsep_1, axiom,
% 0.55/0.73    (![A:$i]:
% 0.55/0.73     ( ( l1_pre_topc @ A ) =>
% 0.55/0.73       ( ![B:$i]:
% 0.55/0.73         ( ( m1_pre_topc @ B @ A ) =>
% 0.55/0.73           ( m1_subset_1 @
% 0.55/0.73             ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.55/0.73  thf('100', plain,
% 0.55/0.73      (![X15 : $i, X16 : $i]:
% 0.55/0.73         (~ (m1_pre_topc @ X15 @ X16)
% 0.55/0.73          | (m1_subset_1 @ (u1_struct_0 @ X15) @ 
% 0.55/0.73             (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.55/0.73          | ~ (l1_pre_topc @ X16))),
% 0.55/0.73      inference('cnf', [status(esa)], [t1_tsep_1])).
% 0.55/0.73  thf('101', plain,
% 0.55/0.73      ((~ (l1_pre_topc @ sk_D)
% 0.55/0.73        | (m1_subset_1 @ (u1_struct_0 @ sk_C) @ 
% 0.55/0.73           (k1_zfmisc_1 @ (u1_struct_0 @ sk_D))))),
% 0.55/0.73      inference('sup-', [status(thm)], ['99', '100'])).
% 0.55/0.73  thf('102', plain, ((l1_pre_topc @ sk_D)),
% 0.55/0.73      inference('demod', [status(thm)], ['18', '19'])).
% 0.55/0.73  thf('103', plain,
% 0.55/0.73      ((m1_subset_1 @ (u1_struct_0 @ sk_C) @ 
% 0.55/0.73        (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))),
% 0.55/0.73      inference('demod', [status(thm)], ['101', '102'])).
% 0.55/0.73  thf(t16_tsep_1, axiom,
% 0.55/0.73    (![A:$i]:
% 0.55/0.73     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.55/0.73       ( ![B:$i]:
% 0.55/0.73         ( ( m1_pre_topc @ B @ A ) =>
% 0.55/0.73           ( ![C:$i]:
% 0.55/0.73             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.55/0.73               ( ( ( C ) = ( u1_struct_0 @ B ) ) =>
% 0.55/0.73                 ( ( ( v1_tsep_1 @ B @ A ) & ( m1_pre_topc @ B @ A ) ) <=>
% 0.55/0.73                   ( v3_pre_topc @ C @ A ) ) ) ) ) ) ) ))).
% 0.55/0.73  thf('104', plain,
% 0.55/0.73      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.55/0.73         (~ (m1_pre_topc @ X12 @ X13)
% 0.55/0.73          | ((X14) != (u1_struct_0 @ X12))
% 0.55/0.73          | ~ (v3_pre_topc @ X14 @ X13)
% 0.55/0.73          | (v1_tsep_1 @ X12 @ X13)
% 0.55/0.73          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.55/0.73          | ~ (l1_pre_topc @ X13)
% 0.55/0.73          | ~ (v2_pre_topc @ X13))),
% 0.55/0.73      inference('cnf', [status(esa)], [t16_tsep_1])).
% 0.55/0.73  thf('105', plain,
% 0.55/0.73      (![X12 : $i, X13 : $i]:
% 0.55/0.73         (~ (v2_pre_topc @ X13)
% 0.55/0.73          | ~ (l1_pre_topc @ X13)
% 0.55/0.73          | ~ (m1_subset_1 @ (u1_struct_0 @ X12) @ 
% 0.55/0.73               (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.55/0.73          | (v1_tsep_1 @ X12 @ X13)
% 0.55/0.73          | ~ (v3_pre_topc @ (u1_struct_0 @ X12) @ X13)
% 0.55/0.73          | ~ (m1_pre_topc @ X12 @ X13))),
% 0.55/0.73      inference('simplify', [status(thm)], ['104'])).
% 0.55/0.73  thf('106', plain,
% 0.55/0.73      ((~ (m1_pre_topc @ sk_C @ sk_D)
% 0.55/0.73        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_C) @ sk_D)
% 0.55/0.73        | (v1_tsep_1 @ sk_C @ sk_D)
% 0.55/0.73        | ~ (l1_pre_topc @ sk_D)
% 0.55/0.73        | ~ (v2_pre_topc @ sk_D))),
% 0.55/0.73      inference('sup-', [status(thm)], ['103', '105'])).
% 0.55/0.73  thf('107', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 0.55/0.73      inference('demod', [status(thm)], ['40', '41'])).
% 0.55/0.73  thf('108', plain, ((l1_pre_topc @ sk_D)),
% 0.55/0.73      inference('demod', [status(thm)], ['18', '19'])).
% 0.55/0.73  thf('109', plain, ((v2_pre_topc @ sk_D)),
% 0.55/0.73      inference('demod', [status(thm)], ['31', '32', '33'])).
% 0.55/0.73  thf('110', plain,
% 0.55/0.73      ((~ (v3_pre_topc @ (u1_struct_0 @ sk_C) @ sk_D)
% 0.55/0.73        | (v1_tsep_1 @ sk_C @ sk_D))),
% 0.55/0.73      inference('demod', [status(thm)], ['106', '107', '108', '109'])).
% 0.55/0.73  thf('111', plain, (((u1_struct_0 @ sk_C) = (k2_struct_0 @ sk_D))),
% 0.55/0.73      inference('demod', [status(thm)], ['62', '65'])).
% 0.55/0.73  thf('112', plain,
% 0.55/0.73      (![X5 : $i]:
% 0.55/0.73         (((k2_struct_0 @ X5) = (u1_struct_0 @ X5)) | ~ (l1_struct_0 @ X5))),
% 0.55/0.73      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.55/0.73  thf('113', plain, ((m1_pre_topc @ sk_D @ sk_C)),
% 0.55/0.73      inference('demod', [status(thm)], ['15', '20', '21'])).
% 0.55/0.73  thf('114', plain,
% 0.55/0.73      (![X9 : $i, X10 : $i]:
% 0.55/0.73         (~ (l1_pre_topc @ X9)
% 0.55/0.73          | ~ (m1_pre_topc @ X10 @ X9)
% 0.55/0.73          | (m1_pre_topc @ X10 @ 
% 0.55/0.73             (g1_pre_topc @ (u1_struct_0 @ X9) @ (u1_pre_topc @ X9)))
% 0.55/0.73          | ~ (l1_pre_topc @ X10))),
% 0.55/0.73      inference('cnf', [status(esa)], [t65_pre_topc])).
% 0.55/0.73  thf('115', plain,
% 0.55/0.73      ((~ (l1_pre_topc @ sk_D)
% 0.55/0.73        | (m1_pre_topc @ sk_D @ 
% 0.55/0.73           (g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)))
% 0.55/0.73        | ~ (l1_pre_topc @ sk_C))),
% 0.55/0.73      inference('sup-', [status(thm)], ['113', '114'])).
% 0.55/0.73  thf('116', plain, ((l1_pre_topc @ sk_D)),
% 0.55/0.73      inference('demod', [status(thm)], ['18', '19'])).
% 0.55/0.73  thf('117', plain,
% 0.55/0.73      (((g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) = (sk_D))),
% 0.55/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.73  thf('118', plain, ((l1_pre_topc @ sk_C)),
% 0.55/0.73      inference('demod', [status(thm)], ['11', '12'])).
% 0.55/0.73  thf('119', plain, ((m1_pre_topc @ sk_D @ sk_D)),
% 0.55/0.73      inference('demod', [status(thm)], ['115', '116', '117', '118'])).
% 0.55/0.73  thf('120', plain,
% 0.55/0.73      (![X15 : $i, X16 : $i]:
% 0.55/0.73         (~ (m1_pre_topc @ X15 @ X16)
% 0.55/0.73          | (m1_subset_1 @ (u1_struct_0 @ X15) @ 
% 0.55/0.73             (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.55/0.73          | ~ (l1_pre_topc @ X16))),
% 0.55/0.73      inference('cnf', [status(esa)], [t1_tsep_1])).
% 0.55/0.73  thf('121', plain,
% 0.55/0.73      ((~ (l1_pre_topc @ sk_D)
% 0.55/0.73        | (m1_subset_1 @ (u1_struct_0 @ sk_D) @ 
% 0.55/0.73           (k1_zfmisc_1 @ (u1_struct_0 @ sk_D))))),
% 0.55/0.73      inference('sup-', [status(thm)], ['119', '120'])).
% 0.55/0.73  thf('122', plain, ((l1_pre_topc @ sk_D)),
% 0.55/0.73      inference('demod', [status(thm)], ['18', '19'])).
% 0.55/0.73  thf('123', plain,
% 0.55/0.73      ((m1_subset_1 @ (u1_struct_0 @ sk_D) @ 
% 0.55/0.73        (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))),
% 0.55/0.73      inference('demod', [status(thm)], ['121', '122'])).
% 0.55/0.73  thf('124', plain,
% 0.55/0.73      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.55/0.73         (~ (m1_pre_topc @ X12 @ X13)
% 0.55/0.73          | ((X14) != (u1_struct_0 @ X12))
% 0.55/0.73          | ~ (v1_tsep_1 @ X12 @ X13)
% 0.55/0.73          | ~ (m1_pre_topc @ X12 @ X13)
% 0.55/0.73          | (v3_pre_topc @ X14 @ X13)
% 0.55/0.73          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.55/0.73          | ~ (l1_pre_topc @ X13)
% 0.55/0.73          | ~ (v2_pre_topc @ X13))),
% 0.55/0.73      inference('cnf', [status(esa)], [t16_tsep_1])).
% 0.55/0.73  thf('125', plain,
% 0.55/0.73      (![X12 : $i, X13 : $i]:
% 0.55/0.73         (~ (v2_pre_topc @ X13)
% 0.55/0.73          | ~ (l1_pre_topc @ X13)
% 0.55/0.73          | ~ (m1_subset_1 @ (u1_struct_0 @ X12) @ 
% 0.55/0.73               (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.55/0.73          | (v3_pre_topc @ (u1_struct_0 @ X12) @ X13)
% 0.55/0.73          | ~ (v1_tsep_1 @ X12 @ X13)
% 0.55/0.73          | ~ (m1_pre_topc @ X12 @ X13))),
% 0.55/0.73      inference('simplify', [status(thm)], ['124'])).
% 0.55/0.73  thf('126', plain,
% 0.55/0.73      ((~ (m1_pre_topc @ sk_D @ sk_D)
% 0.55/0.73        | ~ (v1_tsep_1 @ sk_D @ sk_D)
% 0.55/0.73        | (v3_pre_topc @ (u1_struct_0 @ sk_D) @ sk_D)
% 0.55/0.73        | ~ (l1_pre_topc @ sk_D)
% 0.55/0.73        | ~ (v2_pre_topc @ sk_D))),
% 0.55/0.73      inference('sup-', [status(thm)], ['123', '125'])).
% 0.55/0.73  thf('127', plain, ((m1_pre_topc @ sk_D @ sk_D)),
% 0.55/0.73      inference('demod', [status(thm)], ['115', '116', '117', '118'])).
% 0.55/0.73  thf('128', plain, ((m1_pre_topc @ sk_D @ sk_D)),
% 0.55/0.73      inference('demod', [status(thm)], ['115', '116', '117', '118'])).
% 0.55/0.73  thf(fc10_tops_1, axiom,
% 0.55/0.73    (![A:$i]:
% 0.55/0.73     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.55/0.73       ( v3_pre_topc @ ( k2_struct_0 @ A ) @ A ) ))).
% 0.55/0.73  thf('129', plain,
% 0.55/0.73      (![X11 : $i]:
% 0.55/0.73         ((v3_pre_topc @ (k2_struct_0 @ X11) @ X11)
% 0.55/0.73          | ~ (l1_pre_topc @ X11)
% 0.55/0.73          | ~ (v2_pre_topc @ X11))),
% 0.55/0.73      inference('cnf', [status(esa)], [fc10_tops_1])).
% 0.55/0.73  thf('130', plain,
% 0.55/0.73      (![X5 : $i]:
% 0.55/0.73         (((k2_struct_0 @ X5) = (u1_struct_0 @ X5)) | ~ (l1_struct_0 @ X5))),
% 0.55/0.73      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.55/0.73  thf('131', plain,
% 0.55/0.73      (![X17 : $i]: ((m1_pre_topc @ X17 @ X17) | ~ (l1_pre_topc @ X17))),
% 0.55/0.73      inference('cnf', [status(esa)], [t2_tsep_1])).
% 0.55/0.73  thf('132', plain,
% 0.55/0.73      (![X15 : $i, X16 : $i]:
% 0.55/0.73         (~ (m1_pre_topc @ X15 @ X16)
% 0.55/0.73          | (m1_subset_1 @ (u1_struct_0 @ X15) @ 
% 0.55/0.73             (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.55/0.73          | ~ (l1_pre_topc @ X16))),
% 0.55/0.73      inference('cnf', [status(esa)], [t1_tsep_1])).
% 0.55/0.73  thf('133', plain,
% 0.55/0.73      (![X0 : $i]:
% 0.55/0.73         (~ (l1_pre_topc @ X0)
% 0.55/0.73          | ~ (l1_pre_topc @ X0)
% 0.55/0.73          | (m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 0.55/0.73             (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.55/0.73      inference('sup-', [status(thm)], ['131', '132'])).
% 0.55/0.73  thf('134', plain,
% 0.55/0.73      (![X0 : $i]:
% 0.55/0.73         ((m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 0.55/0.73           (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.55/0.73          | ~ (l1_pre_topc @ X0))),
% 0.55/0.73      inference('simplify', [status(thm)], ['133'])).
% 0.55/0.73  thf('135', plain,
% 0.55/0.73      (![X12 : $i, X13 : $i]:
% 0.55/0.73         (~ (v2_pre_topc @ X13)
% 0.55/0.73          | ~ (l1_pre_topc @ X13)
% 0.55/0.73          | ~ (m1_subset_1 @ (u1_struct_0 @ X12) @ 
% 0.55/0.73               (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.55/0.73          | (v1_tsep_1 @ X12 @ X13)
% 0.55/0.73          | ~ (v3_pre_topc @ (u1_struct_0 @ X12) @ X13)
% 0.55/0.73          | ~ (m1_pre_topc @ X12 @ X13))),
% 0.55/0.73      inference('simplify', [status(thm)], ['104'])).
% 0.55/0.73  thf('136', plain,
% 0.55/0.73      (![X0 : $i]:
% 0.55/0.73         (~ (l1_pre_topc @ X0)
% 0.55/0.73          | ~ (m1_pre_topc @ X0 @ X0)
% 0.55/0.73          | ~ (v3_pre_topc @ (u1_struct_0 @ X0) @ X0)
% 0.55/0.73          | (v1_tsep_1 @ X0 @ X0)
% 0.55/0.73          | ~ (l1_pre_topc @ X0)
% 0.55/0.73          | ~ (v2_pre_topc @ X0))),
% 0.55/0.73      inference('sup-', [status(thm)], ['134', '135'])).
% 0.55/0.73  thf('137', plain,
% 0.55/0.73      (![X0 : $i]:
% 0.55/0.73         (~ (v2_pre_topc @ X0)
% 0.55/0.73          | (v1_tsep_1 @ X0 @ X0)
% 0.55/0.73          | ~ (v3_pre_topc @ (u1_struct_0 @ X0) @ X0)
% 0.55/0.73          | ~ (m1_pre_topc @ X0 @ X0)
% 0.55/0.73          | ~ (l1_pre_topc @ X0))),
% 0.55/0.73      inference('simplify', [status(thm)], ['136'])).
% 0.55/0.73  thf('138', plain,
% 0.55/0.73      (![X0 : $i]:
% 0.55/0.73         (~ (v3_pre_topc @ (k2_struct_0 @ X0) @ X0)
% 0.55/0.73          | ~ (l1_struct_0 @ X0)
% 0.55/0.73          | ~ (l1_pre_topc @ X0)
% 0.55/0.73          | ~ (m1_pre_topc @ X0 @ X0)
% 0.55/0.73          | (v1_tsep_1 @ X0 @ X0)
% 0.55/0.73          | ~ (v2_pre_topc @ X0))),
% 0.55/0.73      inference('sup-', [status(thm)], ['130', '137'])).
% 0.55/0.73  thf('139', plain,
% 0.55/0.73      (![X0 : $i]:
% 0.55/0.73         (~ (v2_pre_topc @ X0)
% 0.55/0.73          | ~ (l1_pre_topc @ X0)
% 0.55/0.73          | ~ (v2_pre_topc @ X0)
% 0.55/0.73          | (v1_tsep_1 @ X0 @ X0)
% 0.55/0.73          | ~ (m1_pre_topc @ X0 @ X0)
% 0.55/0.73          | ~ (l1_pre_topc @ X0)
% 0.55/0.73          | ~ (l1_struct_0 @ X0))),
% 0.55/0.73      inference('sup-', [status(thm)], ['129', '138'])).
% 0.55/0.73  thf('140', plain,
% 0.55/0.73      (![X0 : $i]:
% 0.55/0.73         (~ (l1_struct_0 @ X0)
% 0.55/0.73          | ~ (m1_pre_topc @ X0 @ X0)
% 0.55/0.73          | (v1_tsep_1 @ X0 @ X0)
% 0.55/0.73          | ~ (l1_pre_topc @ X0)
% 0.55/0.73          | ~ (v2_pre_topc @ X0))),
% 0.55/0.73      inference('simplify', [status(thm)], ['139'])).
% 0.55/0.73  thf('141', plain,
% 0.55/0.73      ((~ (v2_pre_topc @ sk_D)
% 0.55/0.73        | ~ (l1_pre_topc @ sk_D)
% 0.55/0.73        | (v1_tsep_1 @ sk_D @ sk_D)
% 0.55/0.73        | ~ (l1_struct_0 @ sk_D))),
% 0.55/0.73      inference('sup-', [status(thm)], ['128', '140'])).
% 0.55/0.73  thf('142', plain, ((v2_pre_topc @ sk_D)),
% 0.55/0.73      inference('demod', [status(thm)], ['31', '32', '33'])).
% 0.55/0.73  thf('143', plain, ((l1_pre_topc @ sk_D)),
% 0.55/0.73      inference('demod', [status(thm)], ['18', '19'])).
% 0.55/0.73  thf('144', plain, ((l1_struct_0 @ sk_D)),
% 0.55/0.73      inference('sup-', [status(thm)], ['63', '64'])).
% 0.55/0.73  thf('145', plain, ((v1_tsep_1 @ sk_D @ sk_D)),
% 0.55/0.73      inference('demod', [status(thm)], ['141', '142', '143', '144'])).
% 0.55/0.73  thf('146', plain, ((l1_pre_topc @ sk_D)),
% 0.55/0.73      inference('demod', [status(thm)], ['18', '19'])).
% 0.55/0.73  thf('147', plain, ((v2_pre_topc @ sk_D)),
% 0.55/0.73      inference('demod', [status(thm)], ['31', '32', '33'])).
% 0.55/0.73  thf('148', plain, ((v3_pre_topc @ (u1_struct_0 @ sk_D) @ sk_D)),
% 0.55/0.73      inference('demod', [status(thm)], ['126', '127', '145', '146', '147'])).
% 0.55/0.73  thf('149', plain,
% 0.55/0.73      (((v3_pre_topc @ (k2_struct_0 @ sk_D) @ sk_D) | ~ (l1_struct_0 @ sk_D))),
% 0.55/0.73      inference('sup+', [status(thm)], ['112', '148'])).
% 0.55/0.73  thf('150', plain, ((l1_struct_0 @ sk_D)),
% 0.55/0.73      inference('sup-', [status(thm)], ['63', '64'])).
% 0.55/0.73  thf('151', plain, ((v3_pre_topc @ (k2_struct_0 @ sk_D) @ sk_D)),
% 0.55/0.73      inference('demod', [status(thm)], ['149', '150'])).
% 0.55/0.73  thf('152', plain, ((v1_tsep_1 @ sk_C @ sk_D)),
% 0.55/0.73      inference('demod', [status(thm)], ['110', '111', '151'])).
% 0.55/0.73  thf('153', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 0.55/0.73      inference('demod', [status(thm)], ['40', '41'])).
% 0.55/0.73  thf('154', plain,
% 0.55/0.73      (![X5 : $i]:
% 0.55/0.73         (((k2_struct_0 @ X5) = (u1_struct_0 @ X5)) | ~ (l1_struct_0 @ X5))),
% 0.55/0.73      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.55/0.73  thf('155', plain, ((m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_C))),
% 0.55/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.73  thf('156', plain, (((sk_F) = (sk_G))),
% 0.55/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.73  thf('157', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C))),
% 0.55/0.73      inference('demod', [status(thm)], ['155', '156'])).
% 0.55/0.73  thf('158', plain,
% 0.55/0.73      (((m1_subset_1 @ sk_F @ (k2_struct_0 @ sk_C)) | ~ (l1_struct_0 @ sk_C))),
% 0.55/0.73      inference('sup+', [status(thm)], ['154', '157'])).
% 0.55/0.73  thf('159', plain, ((l1_struct_0 @ sk_C)),
% 0.55/0.73      inference('sup-', [status(thm)], ['70', '71'])).
% 0.55/0.73  thf('160', plain, ((m1_subset_1 @ sk_F @ (k2_struct_0 @ sk_C))),
% 0.55/0.73      inference('demod', [status(thm)], ['158', '159'])).
% 0.55/0.73  thf('161', plain, (((u1_struct_0 @ sk_C) = (k2_struct_0 @ sk_C))),
% 0.55/0.73      inference('demod', [status(thm)], ['66', '73'])).
% 0.55/0.73  thf('162', plain, ((m1_subset_1 @ sk_F @ (k2_struct_0 @ sk_C))),
% 0.55/0.73      inference('demod', [status(thm)], ['158', '159'])).
% 0.55/0.73  thf('163', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.55/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.73  thf('164', plain, ((l1_pre_topc @ sk_A)),
% 0.55/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.73  thf('165', plain, ((v2_pre_topc @ sk_A)),
% 0.55/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.73  thf('166', plain,
% 0.55/0.73      (((v2_struct_0 @ sk_B)
% 0.55/0.73        | (v2_struct_0 @ sk_D)
% 0.55/0.73        | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)
% 0.55/0.73        | (v2_struct_0 @ sk_C)
% 0.55/0.73        | (v2_struct_0 @ sk_A))),
% 0.55/0.73      inference('demod', [status(thm)],
% 0.55/0.73                ['97', '98', '152', '153', '160', '161', '162', '163', '164', 
% 0.55/0.73                 '165'])).
% 0.55/0.73  thf('167', plain, (~ (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)),
% 0.55/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.73  thf('168', plain,
% 0.55/0.73      (((v2_struct_0 @ sk_A)
% 0.55/0.73        | (v2_struct_0 @ sk_C)
% 0.55/0.73        | (v2_struct_0 @ sk_D)
% 0.55/0.73        | (v2_struct_0 @ sk_B))),
% 0.55/0.73      inference('sup-', [status(thm)], ['166', '167'])).
% 0.55/0.73  thf('169', plain, (~ (v2_struct_0 @ sk_D)),
% 0.55/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.73  thf('170', plain,
% 0.55/0.73      (((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_A))),
% 0.55/0.73      inference('sup-', [status(thm)], ['168', '169'])).
% 0.55/0.73  thf('171', plain, (~ (v2_struct_0 @ sk_B)),
% 0.55/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.73  thf('172', plain, (((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_C))),
% 0.55/0.73      inference('clc', [status(thm)], ['170', '171'])).
% 0.55/0.73  thf('173', plain, (~ (v2_struct_0 @ sk_A)),
% 0.55/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.73  thf('174', plain, ((v2_struct_0 @ sk_C)),
% 0.55/0.73      inference('clc', [status(thm)], ['172', '173'])).
% 0.55/0.73  thf('175', plain, ($false), inference('demod', [status(thm)], ['0', '174'])).
% 0.55/0.73  
% 0.55/0.73  % SZS output end Refutation
% 0.55/0.73  
% 0.55/0.74  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
