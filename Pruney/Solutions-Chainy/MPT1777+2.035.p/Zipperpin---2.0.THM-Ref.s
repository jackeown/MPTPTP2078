%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.wMeD5WEE5o

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:10:31 EST 2020

% Result     : Theorem 0.47s
% Output     : Refutation 0.47s
% Verified   : 
% Statistics : Number of formulae       :  443 (49668 expanded)
%              Number of leaves         :   41 (14462 expanded)
%              Depth                    :   59
%              Number of atoms          : 5016 (1290222 expanded)
%              Number of equality atoms :  163 (36104 expanded)
%              Maximal formula depth    :   30 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r1_tmap_1_type,type,(
    r1_tmap_1: $i > $i > $i > $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_partfun1_type,type,(
    k2_partfun1: $i > $i > $i > $i > $i )).

thf(v1_tsep_1_type,type,(
    v1_tsep_1: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k3_tmap_1_type,type,(
    k3_tmap_1: $i > $i > $i > $i > $i > $i )).

thf(g1_pre_topc_type,type,(
    g1_pre_topc: $i > $i > $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_G_type,type,(
    sk_G: $i )).

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

thf(t2_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( m1_pre_topc @ A @ A ) ) )).

thf('1',plain,(
    ! [X22: $i] :
      ( ( m1_pre_topc @ X22 @ X22 )
      | ~ ( l1_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('2',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) )
    = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,(
    ! [X22: $i] :
      ( ( m1_pre_topc @ X22 @ X22 )
      | ~ ( l1_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf(t65_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( l1_pre_topc @ B )
         => ( ( m1_pre_topc @ A @ B )
          <=> ( m1_pre_topc @ A @ ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ) )).

thf('4',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( l1_pre_topc @ X9 )
      | ~ ( m1_pre_topc @ X10 @ X9 )
      | ( m1_pre_topc @ X10 @ ( g1_pre_topc @ ( u1_struct_0 @ X9 ) @ ( u1_pre_topc @ X9 ) ) )
      | ~ ( l1_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[t65_pre_topc])).

thf('5',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf(t35_borsuk_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( r1_tarski @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) )).

thf('7',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( m1_pre_topc @ X23 @ X24 )
      | ( r1_tarski @ ( u1_struct_0 @ X23 ) @ ( u1_struct_0 @ X24 ) )
      | ~ ( l1_pre_topc @ X24 ) ) ),
    inference(cnf,[status(esa)],[t35_borsuk_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ( r1_tarski @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,
    ( ~ ( l1_pre_topc @ sk_D )
    | ( r1_tarski @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) ) ) )
    | ~ ( l1_pre_topc @ sk_C ) ),
    inference('sup-',[status(thm)],['2','8'])).

thf('10',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('11',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( m1_pre_topc @ X7 @ X8 )
      | ( l1_pre_topc @ X7 )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('12',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_D ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) )
    = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( m1_pre_topc @ X7 @ X8 )
      | ( l1_pre_topc @ X7 )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('18',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_C ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['9','14','15','20'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('22',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('23',plain,
    ( ~ ( r1_tarski @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_C ) )
    | ( ( u1_struct_0 @ sk_D )
      = ( u1_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) )
    = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    ! [X22: $i] :
      ( ( m1_pre_topc @ X22 @ X22 )
      | ~ ( l1_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('26',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( l1_pre_topc @ X9 )
      | ~ ( m1_pre_topc @ X10 @ ( g1_pre_topc @ ( u1_struct_0 @ X9 ) @ ( u1_pre_topc @ X9 ) ) )
      | ( m1_pre_topc @ X10 @ X9 )
      | ~ ( l1_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[t65_pre_topc])).

thf('27',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) @ X0 )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,
    ( ~ ( l1_pre_topc @ sk_D )
    | ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) ) @ sk_C )
    | ~ ( l1_pre_topc @ sk_C ) ),
    inference('sup-',[status(thm)],['24','28'])).

thf('30',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['12','13'])).

thf('31',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) )
    = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['18','19'])).

thf('33',plain,(
    m1_pre_topc @ sk_D @ sk_C ),
    inference(demod,[status(thm)],['29','30','31','32'])).

thf('34',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( m1_pre_topc @ X23 @ X24 )
      | ( r1_tarski @ ( u1_struct_0 @ X23 ) @ ( u1_struct_0 @ X24 ) )
      | ~ ( l1_pre_topc @ X24 ) ) ),
    inference(cnf,[status(esa)],[t35_borsuk_1])).

thf('35',plain,
    ( ~ ( l1_pre_topc @ sk_C )
    | ( r1_tarski @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['18','19'])).

thf('37',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,
    ( ( u1_struct_0 @ sk_D )
    = ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['23','37'])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('39',plain,(
    ! [X5: $i] :
      ( ( ( k2_struct_0 @ X5 )
        = ( u1_struct_0 @ X5 ) )
      | ~ ( l1_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('40',plain,
    ( ( u1_struct_0 @ sk_D )
    = ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['23','37'])).

thf('41',plain,
    ( ( ( k2_struct_0 @ sk_D )
      = ( u1_struct_0 @ sk_C ) )
    | ~ ( l1_struct_0 @ sk_D ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('42',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['12','13'])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('43',plain,(
    ! [X6: $i] :
      ( ( l1_struct_0 @ X6 )
      | ~ ( l1_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('44',plain,(
    l1_struct_0 @ sk_D ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,
    ( ( k2_struct_0 @ sk_D )
    = ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['41','44'])).

thf('46',plain,
    ( ( u1_struct_0 @ sk_D )
    = ( k2_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['38','45'])).

thf('47',plain,(
    ! [X5: $i] :
      ( ( ( k2_struct_0 @ X5 )
        = ( u1_struct_0 @ X5 ) )
      | ~ ( l1_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('48',plain,
    ( ( k2_struct_0 @ sk_D )
    = ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['41','44'])).

thf('49',plain,
    ( ( ( k2_struct_0 @ sk_D )
      = ( k2_struct_0 @ sk_C ) )
    | ~ ( l1_struct_0 @ sk_C ) ),
    inference('sup+',[status(thm)],['47','48'])).

thf('50',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['18','19'])).

thf('51',plain,(
    ! [X6: $i] :
      ( ( l1_struct_0 @ X6 )
      | ~ ( l1_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('52',plain,(
    l1_struct_0 @ sk_C ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,
    ( ( k2_struct_0 @ sk_D )
    = ( k2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['49','52'])).

thf('54',plain,
    ( ( u1_struct_0 @ sk_D )
    = ( k2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['46','53'])).

thf('55',plain,(
    r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    sk_F = sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_F ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) )
    = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('61',plain,
    ( ( m1_pre_topc @ sk_C @ sk_D )
    | ~ ( l1_pre_topc @ sk_C ) ),
    inference('sup+',[status(thm)],['59','60'])).

thf('62',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['18','19'])).

thf('63',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,
    ( ( u1_struct_0 @ sk_D )
    = ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['23','37'])).

thf('66',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,
    ( ( k2_struct_0 @ sk_D )
    = ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['41','44'])).

thf('68',plain,
    ( ( k2_struct_0 @ sk_D )
    = ( k2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['49','52'])).

thf('69',plain,
    ( ( k2_struct_0 @ sk_C )
    = ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('70',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['66','69'])).

thf('71',plain,
    ( ( u1_struct_0 @ sk_D )
    = ( k2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['46','53'])).

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

thf('72',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ( v2_struct_0 @ X12 )
      | ~ ( v2_pre_topc @ X12 )
      | ~ ( l1_pre_topc @ X12 )
      | ~ ( m1_pre_topc @ X13 @ X14 )
      | ~ ( m1_pre_topc @ X13 @ X15 )
      | ( ( k3_tmap_1 @ X14 @ X12 @ X15 @ X13 @ X16 )
        = ( k2_partfun1 @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ X12 ) @ X16 @ ( u1_struct_0 @ X13 ) ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ X12 ) ) ) )
      | ~ ( v1_funct_2 @ X16 @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ X12 ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( m1_pre_topc @ X15 @ X14 )
      | ~ ( l1_pre_topc @ X14 )
      | ~ ( v2_pre_topc @ X14 )
      | ( v2_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d5_tmap_1])).

thf('73',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_C ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ( v2_struct_0 @ X2 )
      | ~ ( v2_pre_topc @ X2 )
      | ~ ( l1_pre_topc @ X2 )
      | ~ ( m1_pre_topc @ sk_D @ X2 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ X0 ) )
      | ( ( k3_tmap_1 @ X2 @ X0 @ sk_D @ X3 @ X1 )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ X0 ) @ X1 @ ( u1_struct_0 @ X3 ) ) )
      | ~ ( m1_pre_topc @ X3 @ sk_D )
      | ~ ( m1_pre_topc @ X3 @ X2 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,
    ( ( u1_struct_0 @ sk_D )
    = ( k2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['46','53'])).

thf('75',plain,
    ( ( u1_struct_0 @ sk_D )
    = ( k2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['46','53'])).

thf('76',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_C ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ( v2_struct_0 @ X2 )
      | ~ ( v2_pre_topc @ X2 )
      | ~ ( l1_pre_topc @ X2 )
      | ~ ( m1_pre_topc @ sk_D @ X2 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ ( k2_struct_0 @ sk_C ) @ ( u1_struct_0 @ X0 ) )
      | ( ( k3_tmap_1 @ X2 @ X0 @ sk_D @ X3 @ X1 )
        = ( k2_partfun1 @ ( k2_struct_0 @ sk_C ) @ ( u1_struct_0 @ X0 ) @ X1 @ ( u1_struct_0 @ X3 ) ) )
      | ~ ( m1_pre_topc @ X3 @ sk_D )
      | ~ ( m1_pre_topc @ X3 @ X2 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['73','74','75'])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ~ ( m1_pre_topc @ X1 @ sk_D )
      | ( ( k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E )
        = ( k2_partfun1 @ ( k2_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( v1_funct_2 @ sk_E @ ( k2_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['70','76'])).

thf('78',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    ! [X5: $i] :
      ( ( ( k2_struct_0 @ X5 )
        = ( u1_struct_0 @ X5 ) )
      | ~ ( l1_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('81',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,
    ( ( v1_funct_2 @ sk_E @ ( k2_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_D ) ),
    inference('sup+',[status(thm)],['80','81'])).

thf('83',plain,(
    l1_struct_0 @ sk_D ),
    inference('sup-',[status(thm)],['42','43'])).

thf('84',plain,(
    v1_funct_2 @ sk_E @ ( k2_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['82','83'])).

thf('85',plain,
    ( ( k2_struct_0 @ sk_D )
    = ( k2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['49','52'])).

thf('86',plain,(
    v1_funct_2 @ sk_E @ ( k2_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('87',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ~ ( m1_pre_topc @ X1 @ sk_D )
      | ( ( k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E )
        = ( k2_partfun1 @ ( k2_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['77','78','79','86','87'])).

thf('89',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ( ( k3_tmap_1 @ X0 @ sk_B @ sk_D @ sk_C @ sk_E )
        = ( k2_partfun1 @ ( k2_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ sk_C ) ) )
      | ~ ( m1_pre_topc @ sk_C @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['63','88'])).

thf('90',plain,
    ( ( k2_struct_0 @ sk_C )
    = ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('91',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('92',plain,(
    ! [X22: $i] :
      ( ( m1_pre_topc @ X22 @ X22 )
      | ~ ( l1_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('93',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['66','69'])).

thf('94',plain,(
    ! [X5: $i] :
      ( ( ( k2_struct_0 @ X5 )
        = ( u1_struct_0 @ X5 ) )
      | ~ ( l1_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('95',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ( v2_struct_0 @ X12 )
      | ~ ( v2_pre_topc @ X12 )
      | ~ ( l1_pre_topc @ X12 )
      | ~ ( m1_pre_topc @ X13 @ X14 )
      | ~ ( m1_pre_topc @ X13 @ X15 )
      | ( ( k3_tmap_1 @ X14 @ X12 @ X15 @ X13 @ X16 )
        = ( k2_partfun1 @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ X12 ) @ X16 @ ( u1_struct_0 @ X13 ) ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ X12 ) ) ) )
      | ~ ( v1_funct_2 @ X16 @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ X12 ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( m1_pre_topc @ X15 @ X14 )
      | ~ ( l1_pre_topc @ X14 )
      | ~ ( v2_pre_topc @ X14 )
      | ( v2_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d5_tmap_1])).

thf('96',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ X0 ) @ ( u1_struct_0 @ X1 ) ) ) )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X3 )
      | ~ ( v2_pre_topc @ X3 )
      | ~ ( l1_pre_topc @ X3 )
      | ~ ( m1_pre_topc @ X0 @ X3 )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_funct_2 @ X2 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X1 ) )
      | ( ( k3_tmap_1 @ X3 @ X1 @ X0 @ X4 @ X2 )
        = ( k2_partfun1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X1 ) @ X2 @ ( u1_struct_0 @ X4 ) ) )
      | ~ ( m1_pre_topc @ X4 @ X0 )
      | ~ ( m1_pre_topc @ X4 @ X3 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ~ ( m1_pre_topc @ X1 @ sk_C )
      | ( ( k3_tmap_1 @ X0 @ sk_B @ sk_C @ X1 @ sk_E )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( m1_pre_topc @ sk_C @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['93','96'])).

thf('98',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,
    ( ( k2_struct_0 @ sk_C )
    = ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('101',plain,
    ( ( k2_struct_0 @ sk_C )
    = ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('102',plain,(
    v1_funct_2 @ sk_E @ ( k2_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('103',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,(
    l1_struct_0 @ sk_C ),
    inference('sup-',[status(thm)],['50','51'])).

thf('105',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ~ ( m1_pre_topc @ X1 @ sk_C )
      | ( ( k3_tmap_1 @ X0 @ sk_B @ sk_C @ X1 @ sk_E )
        = ( k2_partfun1 @ ( k2_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( m1_pre_topc @ sk_C @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['97','98','99','100','101','102','103','104'])).

thf('106',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_C )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ sk_C @ X0 )
      | ( ( k3_tmap_1 @ X0 @ sk_B @ sk_C @ sk_C @ sk_E )
        = ( k2_partfun1 @ ( k2_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ sk_C ) ) )
      | ~ ( m1_pre_topc @ sk_C @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['92','105'])).

thf('107',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['18','19'])).

thf('108',plain,
    ( ( k2_struct_0 @ sk_C )
    = ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('109',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ sk_C @ X0 )
      | ( ( k3_tmap_1 @ X0 @ sk_B @ sk_C @ sk_C @ sk_E )
        = ( k2_partfun1 @ ( k2_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( k2_struct_0 @ sk_C ) ) )
      | ~ ( m1_pre_topc @ sk_C @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['106','107','108'])).

thf('110',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( ( k3_tmap_1 @ X0 @ sk_B @ sk_C @ sk_C @ sk_E )
        = ( k2_partfun1 @ ( k2_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( k2_struct_0 @ sk_C ) ) )
      | ~ ( m1_pre_topc @ sk_C @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['109'])).

thf('111',plain,
    ( ~ ( l1_pre_topc @ sk_C )
    | ( v2_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) ) )
    | ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) ) )
    | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) ) )
    | ( ( k3_tmap_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) ) @ sk_B @ sk_C @ sk_C @ sk_E )
      = ( k2_partfun1 @ ( k2_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( k2_struct_0 @ sk_C ) ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['91','110'])).

thf('112',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['18','19'])).

thf('113',plain,
    ( ( k2_struct_0 @ sk_C )
    = ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('114',plain,(
    ! [X5: $i] :
      ( ( ( k2_struct_0 @ X5 )
        = ( u1_struct_0 @ X5 ) )
      | ~ ( l1_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('115',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) )
    = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,
    ( ( ( g1_pre_topc @ ( k2_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) )
      = sk_D )
    | ~ ( l1_struct_0 @ sk_C ) ),
    inference('sup+',[status(thm)],['114','115'])).

thf('117',plain,(
    l1_struct_0 @ sk_C ),
    inference('sup-',[status(thm)],['50','51'])).

thf('118',plain,
    ( ( g1_pre_topc @ ( k2_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) )
    = sk_D ),
    inference(demod,[status(thm)],['116','117'])).

thf('119',plain,
    ( ( k2_struct_0 @ sk_C )
    = ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('120',plain,
    ( ( g1_pre_topc @ ( k2_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) )
    = sk_D ),
    inference(demod,[status(thm)],['116','117'])).

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
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_pre_topc @ X3 @ X4 )
      | ( v2_pre_topc @ X3 )
      | ~ ( l1_pre_topc @ X4 )
      | ~ ( v2_pre_topc @ X4 ) ) ),
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

thf('127',plain,
    ( ( k2_struct_0 @ sk_C )
    = ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('128',plain,
    ( ( g1_pre_topc @ ( k2_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) )
    = sk_D ),
    inference(demod,[status(thm)],['116','117'])).

thf('129',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['12','13'])).

thf('130',plain,
    ( ( k2_struct_0 @ sk_C )
    = ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('131',plain,
    ( ( g1_pre_topc @ ( k2_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) )
    = sk_D ),
    inference(demod,[status(thm)],['116','117'])).

thf('132',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( ( k3_tmap_1 @ sk_D @ sk_B @ sk_C @ sk_C @ sk_E )
      = ( k2_partfun1 @ ( k2_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( k2_struct_0 @ sk_C ) ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['111','112','113','118','119','120','126','127','128','129','130','131'])).

thf('133',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('134',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( ( k3_tmap_1 @ X0 @ sk_B @ sk_C @ sk_C @ sk_E )
        = ( k2_partfun1 @ ( k2_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( k2_struct_0 @ sk_C ) ) )
      | ~ ( m1_pre_topc @ sk_C @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['109'])).

thf('135',plain,(
    ! [X22: $i] :
      ( ( m1_pre_topc @ X22 @ X22 )
      | ~ ( l1_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('136',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( ( k3_tmap_1 @ X0 @ sk_B @ sk_C @ sk_C @ sk_E )
        = ( k2_partfun1 @ ( k2_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( k2_struct_0 @ sk_C ) ) )
      | ~ ( m1_pre_topc @ sk_C @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['109'])).

thf('137',plain,
    ( ~ ( l1_pre_topc @ sk_C )
    | ( v2_struct_0 @ sk_C )
    | ~ ( v2_pre_topc @ sk_C )
    | ~ ( l1_pre_topc @ sk_C )
    | ( ( k3_tmap_1 @ sk_C @ sk_B @ sk_C @ sk_C @ sk_E )
      = ( k2_partfun1 @ ( k2_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( k2_struct_0 @ sk_C ) ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['135','136'])).

thf('138',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['18','19'])).

thf('139',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('140',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_pre_topc @ X3 @ X4 )
      | ( v2_pre_topc @ X3 )
      | ~ ( l1_pre_topc @ X4 )
      | ~ ( v2_pre_topc @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc1_pre_topc])).

thf('141',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_pre_topc @ sk_C ) ),
    inference('sup-',[status(thm)],['139','140'])).

thf('142',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('143',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('144',plain,(
    v2_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['141','142','143'])).

thf('145',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['18','19'])).

thf('146',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( ( k3_tmap_1 @ sk_C @ sk_B @ sk_C @ sk_C @ sk_E )
      = ( k2_partfun1 @ ( k2_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( k2_struct_0 @ sk_C ) ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['137','138','144','145'])).

thf('147',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('148',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k3_tmap_1 @ sk_C @ sk_B @ sk_C @ sk_C @ sk_E )
      = ( k2_partfun1 @ ( k2_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( k2_struct_0 @ sk_C ) ) ) ),
    inference(clc,[status(thm)],['146','147'])).

thf('149',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('150',plain,
    ( ( k3_tmap_1 @ sk_C @ sk_B @ sk_C @ sk_C @ sk_E )
    = ( k2_partfun1 @ ( k2_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( k2_struct_0 @ sk_C ) ) ),
    inference(clc,[status(thm)],['148','149'])).

thf('151',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( ( k3_tmap_1 @ X0 @ sk_B @ sk_C @ sk_C @ sk_E )
        = ( k3_tmap_1 @ sk_C @ sk_B @ sk_C @ sk_C @ sk_E ) )
      | ~ ( m1_pre_topc @ sk_C @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['134','150'])).

thf('152',plain,
    ( ~ ( l1_pre_topc @ sk_C )
    | ( v2_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) ) )
    | ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) ) )
    | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) ) )
    | ( ( k3_tmap_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) ) @ sk_B @ sk_C @ sk_C @ sk_E )
      = ( k3_tmap_1 @ sk_C @ sk_B @ sk_C @ sk_C @ sk_E ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['133','151'])).

thf('153',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['18','19'])).

thf('154',plain,
    ( ( k2_struct_0 @ sk_C )
    = ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('155',plain,
    ( ( g1_pre_topc @ ( k2_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) )
    = sk_D ),
    inference(demod,[status(thm)],['116','117'])).

thf('156',plain,
    ( ( k2_struct_0 @ sk_C )
    = ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('157',plain,
    ( ( g1_pre_topc @ ( k2_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) )
    = sk_D ),
    inference(demod,[status(thm)],['116','117'])).

thf('158',plain,(
    v2_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['123','124','125'])).

thf('159',plain,
    ( ( k2_struct_0 @ sk_C )
    = ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('160',plain,
    ( ( g1_pre_topc @ ( k2_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) )
    = sk_D ),
    inference(demod,[status(thm)],['116','117'])).

thf('161',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['12','13'])).

thf('162',plain,
    ( ( k2_struct_0 @ sk_C )
    = ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('163',plain,
    ( ( g1_pre_topc @ ( k2_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) )
    = sk_D ),
    inference(demod,[status(thm)],['116','117'])).

thf('164',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( ( k3_tmap_1 @ sk_D @ sk_B @ sk_C @ sk_C @ sk_E )
      = ( k3_tmap_1 @ sk_C @ sk_B @ sk_C @ sk_C @ sk_E ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['152','153','154','155','156','157','158','159','160','161','162','163'])).

thf('165',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('166',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k3_tmap_1 @ sk_D @ sk_B @ sk_C @ sk_C @ sk_E )
      = ( k3_tmap_1 @ sk_C @ sk_B @ sk_C @ sk_C @ sk_E ) ) ),
    inference(clc,[status(thm)],['164','165'])).

thf('167',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('168',plain,
    ( ( k3_tmap_1 @ sk_D @ sk_B @ sk_C @ sk_C @ sk_E )
    = ( k3_tmap_1 @ sk_C @ sk_B @ sk_C @ sk_C @ sk_E ) ),
    inference(clc,[status(thm)],['166','167'])).

thf('169',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('170',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( ( k3_tmap_1 @ X0 @ sk_B @ sk_C @ sk_C @ sk_E )
        = ( k3_tmap_1 @ sk_C @ sk_B @ sk_C @ sk_C @ sk_E ) )
      | ~ ( m1_pre_topc @ sk_C @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['134','150'])).

thf('171',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_C @ sk_E )
      = ( k3_tmap_1 @ sk_C @ sk_B @ sk_C @ sk_C @ sk_E ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['169','170'])).

thf('172',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('173',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('174',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_C @ sk_E )
      = ( k3_tmap_1 @ sk_C @ sk_B @ sk_C @ sk_C @ sk_E ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['171','172','173'])).

thf('175',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('176',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_C @ sk_E )
      = ( k3_tmap_1 @ sk_C @ sk_B @ sk_C @ sk_C @ sk_E ) ) ),
    inference(clc,[status(thm)],['174','175'])).

thf('177',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('178',plain,
    ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_C @ sk_E )
    = ( k3_tmap_1 @ sk_C @ sk_B @ sk_C @ sk_C @ sk_E ) ),
    inference(clc,[status(thm)],['176','177'])).

thf('179',plain,
    ( ( k3_tmap_1 @ sk_D @ sk_B @ sk_C @ sk_C @ sk_E )
    = ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_C @ sk_E ) ),
    inference(demod,[status(thm)],['168','178'])).

thf('180',plain,(
    ! [X5: $i] :
      ( ( ( k2_struct_0 @ X5 )
        = ( u1_struct_0 @ X5 ) )
      | ~ ( l1_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('181',plain,
    ( ( k3_tmap_1 @ sk_C @ sk_B @ sk_C @ sk_C @ sk_E )
    = ( k2_partfun1 @ ( k2_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( k2_struct_0 @ sk_C ) ) ),
    inference(clc,[status(thm)],['148','149'])).

thf('182',plain,
    ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_C @ sk_E )
    = ( k3_tmap_1 @ sk_C @ sk_B @ sk_C @ sk_C @ sk_E ) ),
    inference(clc,[status(thm)],['176','177'])).

thf('183',plain,
    ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_C @ sk_E )
    = ( k2_partfun1 @ ( k2_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( k2_struct_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['181','182'])).

thf('184',plain,
    ( ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_C @ sk_E )
      = ( k2_partfun1 @ ( k2_struct_0 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ sk_E @ ( k2_struct_0 @ sk_C ) ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['180','183'])).

thf('185',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('186',plain,(
    ! [X6: $i] :
      ( ( l1_struct_0 @ X6 )
      | ~ ( l1_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('187',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['185','186'])).

thf('188',plain,
    ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_C @ sk_E )
    = ( k2_partfun1 @ ( k2_struct_0 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ sk_E @ ( k2_struct_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['184','187'])).

thf('189',plain,
    ( ( k3_tmap_1 @ sk_D @ sk_B @ sk_C @ sk_C @ sk_E )
    = ( k2_partfun1 @ ( k2_struct_0 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ sk_E @ ( k2_struct_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['179','188'])).

thf('190',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( ( k2_partfun1 @ ( k2_struct_0 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ sk_E @ ( k2_struct_0 @ sk_C ) )
      = ( k2_partfun1 @ ( k2_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( k2_struct_0 @ sk_C ) ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['132','189'])).

thf('191',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('192',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k2_partfun1 @ ( k2_struct_0 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ sk_E @ ( k2_struct_0 @ sk_C ) )
      = ( k2_partfun1 @ ( k2_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( k2_struct_0 @ sk_C ) ) ) ),
    inference(clc,[status(thm)],['190','191'])).

thf('193',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('194',plain,
    ( ( k2_partfun1 @ ( k2_struct_0 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ sk_E @ ( k2_struct_0 @ sk_C ) )
    = ( k2_partfun1 @ ( k2_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( k2_struct_0 @ sk_C ) ) ),
    inference(clc,[status(thm)],['192','193'])).

thf('195',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ( ( k3_tmap_1 @ X0 @ sk_B @ sk_D @ sk_C @ sk_E )
        = ( k2_partfun1 @ ( k2_struct_0 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ sk_E @ ( k2_struct_0 @ sk_C ) ) )
      | ~ ( m1_pre_topc @ sk_C @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['89','90','194'])).

thf('196',plain,
    ( ( v2_struct_0 @ sk_B )
    | ~ ( m1_pre_topc @ sk_C @ sk_A )
    | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E )
      = ( k2_partfun1 @ ( k2_struct_0 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ sk_E @ ( k2_struct_0 @ sk_C ) ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['58','195'])).

thf('197',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('198',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('199',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('200',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E )
      = ( k2_partfun1 @ ( k2_struct_0 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ sk_E @ ( k2_struct_0 @ sk_C ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['196','197','198','199'])).

thf('201',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('202',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E )
      = ( k2_partfun1 @ ( k2_struct_0 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ sk_E @ ( k2_struct_0 @ sk_C ) ) ) ),
    inference(clc,[status(thm)],['200','201'])).

thf('203',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('204',plain,
    ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E )
    = ( k2_partfun1 @ ( k2_struct_0 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ sk_E @ ( k2_struct_0 @ sk_C ) ) ),
    inference(clc,[status(thm)],['202','203'])).

thf('205',plain,(
    r1_tmap_1 @ sk_C @ sk_B @ ( k2_partfun1 @ ( k2_struct_0 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ sk_E @ ( k2_struct_0 @ sk_C ) ) @ sk_F ),
    inference(demod,[status(thm)],['57','204'])).

thf('206',plain,(
    ! [X5: $i] :
      ( ( ( k2_struct_0 @ X5 )
        = ( u1_struct_0 @ X5 ) )
      | ~ ( l1_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('207',plain,
    ( ( k3_tmap_1 @ sk_C @ sk_B @ sk_C @ sk_C @ sk_E )
    = ( k2_partfun1 @ ( k2_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( k2_struct_0 @ sk_C ) ) ),
    inference(clc,[status(thm)],['148','149'])).

thf('208',plain,
    ( ( ( k3_tmap_1 @ sk_C @ sk_B @ sk_C @ sk_C @ sk_E )
      = ( k2_partfun1 @ ( k2_struct_0 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ sk_E @ ( k2_struct_0 @ sk_C ) ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['206','207'])).

thf('209',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['185','186'])).

thf('210',plain,
    ( ( k3_tmap_1 @ sk_C @ sk_B @ sk_C @ sk_C @ sk_E )
    = ( k2_partfun1 @ ( k2_struct_0 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ sk_E @ ( k2_struct_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['208','209'])).

thf('211',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['66','69'])).

thf('212',plain,(
    ! [X5: $i] :
      ( ( ( k2_struct_0 @ X5 )
        = ( u1_struct_0 @ X5 ) )
      | ~ ( l1_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(t87_tmap_1,axiom,(
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
                & ( m1_pre_topc @ C @ B ) )
             => ! [D: $i] :
                  ( ( ~ ( v2_struct_0 @ D )
                    & ( m1_pre_topc @ D @ B ) )
                 => ! [E: $i] :
                      ( ( ( v1_funct_1 @ E )
                        & ( v1_funct_2 @ E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ A ) )
                        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ A ) ) ) ) )
                     => ( ( ( v1_tsep_1 @ C @ B )
                          & ( m1_pre_topc @ C @ B )
                          & ( m1_pre_topc @ C @ D ) )
                       => ! [F: $i] :
                            ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) )
                           => ! [G: $i] :
                                ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) )
                               => ( ( F = G )
                                 => ( ( r1_tmap_1 @ D @ A @ E @ F )
                                  <=> ( r1_tmap_1 @ C @ A @ ( k3_tmap_1 @ B @ A @ D @ C @ E ) @ G ) ) ) ) ) ) ) ) ) ) ) )).

thf('213',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ( v2_struct_0 @ X28 )
      | ~ ( v2_pre_topc @ X28 )
      | ~ ( l1_pre_topc @ X28 )
      | ( v2_struct_0 @ X29 )
      | ~ ( m1_pre_topc @ X29 @ X28 )
      | ~ ( v1_tsep_1 @ X30 @ X28 )
      | ~ ( m1_pre_topc @ X30 @ X28 )
      | ~ ( m1_pre_topc @ X30 @ X29 )
      | ~ ( m1_subset_1 @ X31 @ ( u1_struct_0 @ X29 ) )
      | ( X31 != X32 )
      | ~ ( r1_tmap_1 @ X30 @ X33 @ ( k3_tmap_1 @ X28 @ X33 @ X29 @ X30 @ X34 ) @ X32 )
      | ( r1_tmap_1 @ X29 @ X33 @ X34 @ X31 )
      | ~ ( m1_subset_1 @ X32 @ ( u1_struct_0 @ X30 ) )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X29 ) @ ( u1_struct_0 @ X33 ) ) ) )
      | ~ ( v1_funct_2 @ X34 @ ( u1_struct_0 @ X29 ) @ ( u1_struct_0 @ X33 ) )
      | ~ ( v1_funct_1 @ X34 )
      | ~ ( m1_pre_topc @ X30 @ X28 )
      | ( v2_struct_0 @ X30 )
      | ~ ( l1_pre_topc @ X33 )
      | ~ ( v2_pre_topc @ X33 )
      | ( v2_struct_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t87_tmap_1])).

thf('214',plain,(
    ! [X28: $i,X29: $i,X30: $i,X32: $i,X33: $i,X34: $i] :
      ( ( v2_struct_0 @ X33 )
      | ~ ( v2_pre_topc @ X33 )
      | ~ ( l1_pre_topc @ X33 )
      | ( v2_struct_0 @ X30 )
      | ~ ( v1_funct_1 @ X34 )
      | ~ ( v1_funct_2 @ X34 @ ( u1_struct_0 @ X29 ) @ ( u1_struct_0 @ X33 ) )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X29 ) @ ( u1_struct_0 @ X33 ) ) ) )
      | ~ ( m1_subset_1 @ X32 @ ( u1_struct_0 @ X30 ) )
      | ( r1_tmap_1 @ X29 @ X33 @ X34 @ X32 )
      | ~ ( r1_tmap_1 @ X30 @ X33 @ ( k3_tmap_1 @ X28 @ X33 @ X29 @ X30 @ X34 ) @ X32 )
      | ~ ( m1_subset_1 @ X32 @ ( u1_struct_0 @ X29 ) )
      | ~ ( m1_pre_topc @ X30 @ X29 )
      | ~ ( m1_pre_topc @ X30 @ X28 )
      | ~ ( v1_tsep_1 @ X30 @ X28 )
      | ~ ( m1_pre_topc @ X29 @ X28 )
      | ( v2_struct_0 @ X29 )
      | ~ ( l1_pre_topc @ X28 )
      | ~ ( v2_pre_topc @ X28 )
      | ( v2_struct_0 @ X28 ) ) ),
    inference(simplify,[status(thm)],['213'])).

thf('215',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ X0 ) @ ( u1_struct_0 @ X1 ) ) ) )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X3 )
      | ~ ( v2_pre_topc @ X3 )
      | ~ ( l1_pre_topc @ X3 )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X3 )
      | ~ ( v1_tsep_1 @ X4 @ X3 )
      | ~ ( m1_pre_topc @ X4 @ X3 )
      | ~ ( m1_pre_topc @ X4 @ X0 )
      | ~ ( m1_subset_1 @ X5 @ ( u1_struct_0 @ X0 ) )
      | ~ ( r1_tmap_1 @ X4 @ X1 @ ( k3_tmap_1 @ X3 @ X1 @ X0 @ X4 @ X2 ) @ X5 )
      | ( r1_tmap_1 @ X0 @ X1 @ X2 @ X5 )
      | ~ ( m1_subset_1 @ X5 @ ( u1_struct_0 @ X4 ) )
      | ~ ( v1_funct_2 @ X2 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X1 ) )
      | ~ ( v1_funct_1 @ X2 )
      | ( v2_struct_0 @ X4 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['212','214'])).

thf('216',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ( r1_tmap_1 @ sk_C @ sk_B @ sk_E @ X1 )
      | ~ ( r1_tmap_1 @ X0 @ sk_B @ ( k3_tmap_1 @ X2 @ sk_B @ sk_C @ X0 @ sk_E ) @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_C ) )
      | ~ ( m1_pre_topc @ X0 @ sk_C )
      | ~ ( m1_pre_topc @ X0 @ X2 )
      | ~ ( v1_tsep_1 @ X0 @ X2 )
      | ~ ( m1_pre_topc @ sk_C @ X2 )
      | ( v2_struct_0 @ sk_C )
      | ~ ( l1_pre_topc @ X2 )
      | ~ ( v2_pre_topc @ X2 )
      | ( v2_struct_0 @ X2 )
      | ~ ( l1_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['211','215'])).

thf('217',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('218',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('219',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('220',plain,
    ( ( k2_struct_0 @ sk_C )
    = ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('221',plain,(
    v1_funct_2 @ sk_E @ ( k2_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('222',plain,
    ( ( k2_struct_0 @ sk_C )
    = ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('223',plain,(
    l1_struct_0 @ sk_C ),
    inference('sup-',[status(thm)],['50','51'])).

thf('224',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ( r1_tmap_1 @ sk_C @ sk_B @ sk_E @ X1 )
      | ~ ( r1_tmap_1 @ X0 @ sk_B @ ( k3_tmap_1 @ X2 @ sk_B @ sk_C @ X0 @ sk_E ) @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( k2_struct_0 @ sk_C ) )
      | ~ ( m1_pre_topc @ X0 @ sk_C )
      | ~ ( m1_pre_topc @ X0 @ X2 )
      | ~ ( v1_tsep_1 @ X0 @ X2 )
      | ~ ( m1_pre_topc @ sk_C @ X2 )
      | ( v2_struct_0 @ sk_C )
      | ~ ( l1_pre_topc @ X2 )
      | ~ ( v2_pre_topc @ X2 )
      | ( v2_struct_0 @ X2 ) ) ),
    inference(demod,[status(thm)],['216','217','218','219','220','221','222','223'])).

thf('225',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tmap_1 @ sk_C @ sk_B @ ( k2_partfun1 @ ( k2_struct_0 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ sk_E @ ( k2_struct_0 @ sk_C ) ) @ X0 )
      | ( v2_struct_0 @ sk_C )
      | ~ ( v2_pre_topc @ sk_C )
      | ~ ( l1_pre_topc @ sk_C )
      | ( v2_struct_0 @ sk_C )
      | ~ ( m1_pre_topc @ sk_C @ sk_C )
      | ~ ( v1_tsep_1 @ sk_C @ sk_C )
      | ~ ( m1_pre_topc @ sk_C @ sk_C )
      | ~ ( m1_pre_topc @ sk_C @ sk_C )
      | ~ ( m1_subset_1 @ X0 @ ( k2_struct_0 @ sk_C ) )
      | ( r1_tmap_1 @ sk_C @ sk_B @ sk_E @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_C ) )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['210','224'])).

thf('226',plain,(
    v2_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['141','142','143'])).

thf('227',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['18','19'])).

thf('228',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(demod,[status(thm)],['61','62'])).

thf('229',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) )
    = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('230',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( l1_pre_topc @ X9 )
      | ~ ( m1_pre_topc @ X10 @ ( g1_pre_topc @ ( u1_struct_0 @ X9 ) @ ( u1_pre_topc @ X9 ) ) )
      | ( m1_pre_topc @ X10 @ X9 )
      | ~ ( l1_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[t65_pre_topc])).

thf('231',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_D )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_pre_topc @ X0 @ sk_C )
      | ~ ( l1_pre_topc @ sk_C ) ) ),
    inference('sup-',[status(thm)],['229','230'])).

thf('232',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['18','19'])).

thf('233',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_D )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_pre_topc @ X0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['231','232'])).

thf('234',plain,
    ( ( m1_pre_topc @ sk_C @ sk_C )
    | ~ ( l1_pre_topc @ sk_C ) ),
    inference('sup-',[status(thm)],['228','233'])).

thf('235',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['18','19'])).

thf('236',plain,(
    m1_pre_topc @ sk_C @ sk_C ),
    inference(demod,[status(thm)],['234','235'])).

thf(fc10_tops_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( v3_pre_topc @ ( k2_struct_0 @ A ) @ A ) ) )).

thf('237',plain,(
    ! [X11: $i] :
      ( ( v3_pre_topc @ ( k2_struct_0 @ X11 ) @ X11 )
      | ~ ( l1_pre_topc @ X11 )
      | ~ ( v2_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[fc10_tops_1])).

thf('238',plain,
    ( ( k2_struct_0 @ sk_C )
    = ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('239',plain,(
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

thf('240',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( m1_pre_topc @ X20 @ X21 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X20 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( l1_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('241',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['239','240'])).

thf('242',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['241'])).

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

thf('243',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_pre_topc @ X17 @ X18 )
      | ( X19
       != ( u1_struct_0 @ X17 ) )
      | ~ ( v3_pre_topc @ X19 @ X18 )
      | ( v1_tsep_1 @ X17 @ X18 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( l1_pre_topc @ X18 )
      | ~ ( v2_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[t16_tsep_1])).

thf('244',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( v2_pre_topc @ X18 )
      | ~ ( l1_pre_topc @ X18 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X17 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ( v1_tsep_1 @ X17 @ X18 )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ X17 ) @ X18 )
      | ~ ( m1_pre_topc @ X17 @ X18 ) ) ),
    inference(simplify,[status(thm)],['243'])).

thf('245',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X0 )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 )
      | ( v1_tsep_1 @ X0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['242','244'])).

thf('246',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ( v1_tsep_1 @ X0 @ X0 )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['245'])).

thf('247',plain,
    ( ~ ( v3_pre_topc @ ( k2_struct_0 @ sk_C ) @ sk_C )
    | ~ ( l1_pre_topc @ sk_C )
    | ~ ( m1_pre_topc @ sk_C @ sk_C )
    | ( v1_tsep_1 @ sk_C @ sk_C )
    | ~ ( v2_pre_topc @ sk_C ) ),
    inference('sup-',[status(thm)],['238','246'])).

thf('248',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['18','19'])).

thf('249',plain,(
    m1_pre_topc @ sk_C @ sk_C ),
    inference(demod,[status(thm)],['234','235'])).

thf('250',plain,(
    v2_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['141','142','143'])).

thf('251',plain,
    ( ~ ( v3_pre_topc @ ( k2_struct_0 @ sk_C ) @ sk_C )
    | ( v1_tsep_1 @ sk_C @ sk_C ) ),
    inference(demod,[status(thm)],['247','248','249','250'])).

thf('252',plain,
    ( ~ ( v2_pre_topc @ sk_C )
    | ~ ( l1_pre_topc @ sk_C )
    | ( v1_tsep_1 @ sk_C @ sk_C ) ),
    inference('sup-',[status(thm)],['237','251'])).

thf('253',plain,(
    v2_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['141','142','143'])).

thf('254',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['18','19'])).

thf('255',plain,(
    v1_tsep_1 @ sk_C @ sk_C ),
    inference(demod,[status(thm)],['252','253','254'])).

thf('256',plain,(
    m1_pre_topc @ sk_C @ sk_C ),
    inference(demod,[status(thm)],['234','235'])).

thf('257',plain,(
    m1_pre_topc @ sk_C @ sk_C ),
    inference(demod,[status(thm)],['234','235'])).

thf('258',plain,
    ( ( k2_struct_0 @ sk_C )
    = ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('259',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tmap_1 @ sk_C @ sk_B @ ( k2_partfun1 @ ( k2_struct_0 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ sk_E @ ( k2_struct_0 @ sk_C ) ) @ X0 )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_C )
      | ~ ( m1_subset_1 @ X0 @ ( k2_struct_0 @ sk_C ) )
      | ( r1_tmap_1 @ sk_C @ sk_B @ sk_E @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k2_struct_0 @ sk_C ) )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['225','226','227','236','255','256','257','258'])).

thf('260',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( r1_tmap_1 @ sk_C @ sk_B @ sk_E @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k2_struct_0 @ sk_C ) )
      | ( v2_struct_0 @ sk_C )
      | ~ ( r1_tmap_1 @ sk_C @ sk_B @ ( k2_partfun1 @ ( k2_struct_0 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ sk_E @ ( k2_struct_0 @ sk_C ) ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['259'])).

thf('261',plain,
    ( ( v2_struct_0 @ sk_C )
    | ~ ( m1_subset_1 @ sk_F @ ( k2_struct_0 @ sk_C ) )
    | ( r1_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_F )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['205','260'])).

thf('262',plain,(
    ! [X5: $i] :
      ( ( ( k2_struct_0 @ X5 )
        = ( u1_struct_0 @ X5 ) )
      | ~ ( l1_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('263',plain,(
    m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('264',plain,(
    sk_F = sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('265',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['263','264'])).

thf('266',plain,
    ( ( m1_subset_1 @ sk_F @ ( k2_struct_0 @ sk_C ) )
    | ~ ( l1_struct_0 @ sk_C ) ),
    inference('sup+',[status(thm)],['262','265'])).

thf('267',plain,(
    l1_struct_0 @ sk_C ),
    inference('sup-',[status(thm)],['50','51'])).

thf('268',plain,(
    m1_subset_1 @ sk_F @ ( k2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['266','267'])).

thf('269',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( r1_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_F )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['261','268'])).

thf('270',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('271',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( r1_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_F ) ),
    inference(clc,[status(thm)],['269','270'])).

thf('272',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('273',plain,(
    r1_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_F ),
    inference(clc,[status(thm)],['271','272'])).

thf('274',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['66','69'])).

thf('275',plain,(
    ! [X5: $i] :
      ( ( ( k2_struct_0 @ X5 )
        = ( u1_struct_0 @ X5 ) )
      | ~ ( l1_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('276',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ( v2_struct_0 @ X28 )
      | ~ ( v2_pre_topc @ X28 )
      | ~ ( l1_pre_topc @ X28 )
      | ( v2_struct_0 @ X29 )
      | ~ ( m1_pre_topc @ X29 @ X28 )
      | ~ ( v1_tsep_1 @ X30 @ X28 )
      | ~ ( m1_pre_topc @ X30 @ X28 )
      | ~ ( m1_pre_topc @ X30 @ X29 )
      | ~ ( m1_subset_1 @ X31 @ ( u1_struct_0 @ X29 ) )
      | ( X31 != X32 )
      | ~ ( r1_tmap_1 @ X29 @ X33 @ X34 @ X31 )
      | ( r1_tmap_1 @ X30 @ X33 @ ( k3_tmap_1 @ X28 @ X33 @ X29 @ X30 @ X34 ) @ X32 )
      | ~ ( m1_subset_1 @ X32 @ ( u1_struct_0 @ X30 ) )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X29 ) @ ( u1_struct_0 @ X33 ) ) ) )
      | ~ ( v1_funct_2 @ X34 @ ( u1_struct_0 @ X29 ) @ ( u1_struct_0 @ X33 ) )
      | ~ ( v1_funct_1 @ X34 )
      | ~ ( m1_pre_topc @ X30 @ X28 )
      | ( v2_struct_0 @ X30 )
      | ~ ( l1_pre_topc @ X33 )
      | ~ ( v2_pre_topc @ X33 )
      | ( v2_struct_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t87_tmap_1])).

thf('277',plain,(
    ! [X28: $i,X29: $i,X30: $i,X32: $i,X33: $i,X34: $i] :
      ( ( v2_struct_0 @ X33 )
      | ~ ( v2_pre_topc @ X33 )
      | ~ ( l1_pre_topc @ X33 )
      | ( v2_struct_0 @ X30 )
      | ~ ( v1_funct_1 @ X34 )
      | ~ ( v1_funct_2 @ X34 @ ( u1_struct_0 @ X29 ) @ ( u1_struct_0 @ X33 ) )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X29 ) @ ( u1_struct_0 @ X33 ) ) ) )
      | ~ ( m1_subset_1 @ X32 @ ( u1_struct_0 @ X30 ) )
      | ( r1_tmap_1 @ X30 @ X33 @ ( k3_tmap_1 @ X28 @ X33 @ X29 @ X30 @ X34 ) @ X32 )
      | ~ ( r1_tmap_1 @ X29 @ X33 @ X34 @ X32 )
      | ~ ( m1_subset_1 @ X32 @ ( u1_struct_0 @ X29 ) )
      | ~ ( m1_pre_topc @ X30 @ X29 )
      | ~ ( m1_pre_topc @ X30 @ X28 )
      | ~ ( v1_tsep_1 @ X30 @ X28 )
      | ~ ( m1_pre_topc @ X29 @ X28 )
      | ( v2_struct_0 @ X29 )
      | ~ ( l1_pre_topc @ X28 )
      | ~ ( v2_pre_topc @ X28 )
      | ( v2_struct_0 @ X28 ) ) ),
    inference(simplify,[status(thm)],['276'])).

thf('278',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ X0 ) @ ( u1_struct_0 @ X1 ) ) ) )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X3 )
      | ~ ( v2_pre_topc @ X3 )
      | ~ ( l1_pre_topc @ X3 )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X3 )
      | ~ ( v1_tsep_1 @ X4 @ X3 )
      | ~ ( m1_pre_topc @ X4 @ X3 )
      | ~ ( m1_pre_topc @ X4 @ X0 )
      | ~ ( m1_subset_1 @ X5 @ ( u1_struct_0 @ X0 ) )
      | ~ ( r1_tmap_1 @ X0 @ X1 @ X2 @ X5 )
      | ( r1_tmap_1 @ X4 @ X1 @ ( k3_tmap_1 @ X3 @ X1 @ X0 @ X4 @ X2 ) @ X5 )
      | ~ ( m1_subset_1 @ X5 @ ( u1_struct_0 @ X4 ) )
      | ~ ( v1_funct_2 @ X2 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X1 ) )
      | ~ ( v1_funct_1 @ X2 )
      | ( v2_struct_0 @ X4 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['275','277'])).

thf('279',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ( r1_tmap_1 @ X0 @ sk_B @ ( k3_tmap_1 @ X2 @ sk_B @ sk_C @ X0 @ sk_E ) @ X1 )
      | ~ ( r1_tmap_1 @ sk_C @ sk_B @ sk_E @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_C ) )
      | ~ ( m1_pre_topc @ X0 @ sk_C )
      | ~ ( m1_pre_topc @ X0 @ X2 )
      | ~ ( v1_tsep_1 @ X0 @ X2 )
      | ~ ( m1_pre_topc @ sk_C @ X2 )
      | ( v2_struct_0 @ sk_C )
      | ~ ( l1_pre_topc @ X2 )
      | ~ ( v2_pre_topc @ X2 )
      | ( v2_struct_0 @ X2 )
      | ~ ( l1_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['274','278'])).

thf('280',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('281',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('282',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('283',plain,
    ( ( k2_struct_0 @ sk_C )
    = ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('284',plain,(
    v1_funct_2 @ sk_E @ ( k2_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('285',plain,
    ( ( k2_struct_0 @ sk_C )
    = ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('286',plain,(
    l1_struct_0 @ sk_C ),
    inference('sup-',[status(thm)],['50','51'])).

thf('287',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ( r1_tmap_1 @ X0 @ sk_B @ ( k3_tmap_1 @ X2 @ sk_B @ sk_C @ X0 @ sk_E ) @ X1 )
      | ~ ( r1_tmap_1 @ sk_C @ sk_B @ sk_E @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( k2_struct_0 @ sk_C ) )
      | ~ ( m1_pre_topc @ X0 @ sk_C )
      | ~ ( m1_pre_topc @ X0 @ X2 )
      | ~ ( v1_tsep_1 @ X0 @ X2 )
      | ~ ( m1_pre_topc @ sk_C @ X2 )
      | ( v2_struct_0 @ sk_C )
      | ~ ( l1_pre_topc @ X2 )
      | ~ ( v2_pre_topc @ X2 )
      | ( v2_struct_0 @ X2 ) ) ),
    inference(demod,[status(thm)],['279','280','281','282','283','284','285','286'])).

thf('288',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ sk_C )
      | ~ ( m1_pre_topc @ sk_C @ X0 )
      | ~ ( v1_tsep_1 @ X1 @ X0 )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ~ ( m1_pre_topc @ X1 @ sk_C )
      | ~ ( m1_subset_1 @ sk_F @ ( k2_struct_0 @ sk_C ) )
      | ( r1_tmap_1 @ X1 @ sk_B @ ( k3_tmap_1 @ X0 @ sk_B @ sk_C @ X1 @ sk_E ) @ sk_F )
      | ~ ( m1_subset_1 @ sk_F @ ( u1_struct_0 @ X1 ) )
      | ( v2_struct_0 @ X1 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['273','287'])).

thf('289',plain,(
    m1_subset_1 @ sk_F @ ( k2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['266','267'])).

thf('290',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ sk_C )
      | ~ ( m1_pre_topc @ sk_C @ X0 )
      | ~ ( v1_tsep_1 @ X1 @ X0 )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ~ ( m1_pre_topc @ X1 @ sk_C )
      | ( r1_tmap_1 @ X1 @ sk_B @ ( k3_tmap_1 @ X0 @ sk_B @ sk_C @ X1 @ sk_E ) @ sk_F )
      | ~ ( m1_subset_1 @ sk_F @ ( u1_struct_0 @ X1 ) )
      | ( v2_struct_0 @ X1 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['288','289'])).

thf('291',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ sk_F @ ( k2_struct_0 @ sk_C ) )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ( r1_tmap_1 @ sk_D @ sk_B @ ( k3_tmap_1 @ X0 @ sk_B @ sk_C @ sk_D @ sk_E ) @ sk_F )
      | ~ ( m1_pre_topc @ sk_D @ sk_C )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ~ ( v1_tsep_1 @ sk_D @ X0 )
      | ~ ( m1_pre_topc @ sk_C @ X0 )
      | ( v2_struct_0 @ sk_C )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['54','290'])).

thf('292',plain,(
    m1_subset_1 @ sk_F @ ( k2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['266','267'])).

thf('293',plain,(
    m1_pre_topc @ sk_D @ sk_C ),
    inference(demod,[status(thm)],['29','30','31','32'])).

thf('294',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ( r1_tmap_1 @ sk_D @ sk_B @ ( k3_tmap_1 @ X0 @ sk_B @ sk_C @ sk_D @ sk_E ) @ sk_F )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ~ ( v1_tsep_1 @ sk_D @ X0 )
      | ~ ( m1_pre_topc @ sk_C @ X0 )
      | ( v2_struct_0 @ sk_C )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['291','292','293'])).

thf('295',plain,
    ( ~ ( l1_pre_topc @ sk_D )
    | ( v2_struct_0 @ sk_D )
    | ~ ( v2_pre_topc @ sk_D )
    | ~ ( l1_pre_topc @ sk_D )
    | ( v2_struct_0 @ sk_C )
    | ~ ( m1_pre_topc @ sk_C @ sk_D )
    | ~ ( v1_tsep_1 @ sk_D @ sk_D )
    | ( r1_tmap_1 @ sk_D @ sk_B @ ( k3_tmap_1 @ sk_D @ sk_B @ sk_C @ sk_D @ sk_E ) @ sk_F )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['1','294'])).

thf('296',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['12','13'])).

thf('297',plain,(
    v2_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['123','124','125'])).

thf('298',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['12','13'])).

thf('299',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(demod,[status(thm)],['61','62'])).

thf('300',plain,
    ( ( u1_struct_0 @ sk_D )
    = ( k2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['46','53'])).

thf('301',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ( v1_tsep_1 @ X0 @ X0 )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['245'])).

thf('302',plain,
    ( ~ ( v3_pre_topc @ ( k2_struct_0 @ sk_C ) @ sk_D )
    | ~ ( l1_pre_topc @ sk_D )
    | ~ ( m1_pre_topc @ sk_D @ sk_D )
    | ( v1_tsep_1 @ sk_D @ sk_D )
    | ~ ( v2_pre_topc @ sk_D ) ),
    inference('sup-',[status(thm)],['300','301'])).

thf('303',plain,
    ( ( k2_struct_0 @ sk_D )
    = ( k2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['49','52'])).

thf('304',plain,(
    ! [X11: $i] :
      ( ( v3_pre_topc @ ( k2_struct_0 @ X11 ) @ X11 )
      | ~ ( l1_pre_topc @ X11 )
      | ~ ( v2_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[fc10_tops_1])).

thf('305',plain,
    ( ( v3_pre_topc @ ( k2_struct_0 @ sk_C ) @ sk_D )
    | ~ ( v2_pre_topc @ sk_D )
    | ~ ( l1_pre_topc @ sk_D ) ),
    inference('sup+',[status(thm)],['303','304'])).

thf('306',plain,(
    v2_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['123','124','125'])).

thf('307',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['12','13'])).

thf('308',plain,(
    v3_pre_topc @ ( k2_struct_0 @ sk_C ) @ sk_D ),
    inference(demod,[status(thm)],['305','306','307'])).

thf('309',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['12','13'])).

thf('310',plain,(
    m1_pre_topc @ sk_D @ sk_C ),
    inference(demod,[status(thm)],['29','30','31','32'])).

thf('311',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( l1_pre_topc @ X9 )
      | ~ ( m1_pre_topc @ X10 @ X9 )
      | ( m1_pre_topc @ X10 @ ( g1_pre_topc @ ( u1_struct_0 @ X9 ) @ ( u1_pre_topc @ X9 ) ) )
      | ~ ( l1_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[t65_pre_topc])).

thf('312',plain,
    ( ~ ( l1_pre_topc @ sk_D )
    | ( m1_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) ) )
    | ~ ( l1_pre_topc @ sk_C ) ),
    inference('sup-',[status(thm)],['310','311'])).

thf('313',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['12','13'])).

thf('314',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) )
    = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('315',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['18','19'])).

thf('316',plain,(
    m1_pre_topc @ sk_D @ sk_D ),
    inference(demod,[status(thm)],['312','313','314','315'])).

thf('317',plain,(
    v2_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['123','124','125'])).

thf('318',plain,(
    v1_tsep_1 @ sk_D @ sk_D ),
    inference(demod,[status(thm)],['302','308','309','316','317'])).

thf('319',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('320',plain,(
    m1_pre_topc @ sk_D @ sk_C ),
    inference(demod,[status(thm)],['29','30','31','32'])).

thf('321',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ~ ( m1_pre_topc @ X1 @ sk_C )
      | ( ( k3_tmap_1 @ X0 @ sk_B @ sk_C @ X1 @ sk_E )
        = ( k2_partfun1 @ ( k2_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( m1_pre_topc @ sk_C @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['97','98','99','100','101','102','103','104'])).

thf('322',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ sk_C @ X0 )
      | ( ( k3_tmap_1 @ X0 @ sk_B @ sk_C @ sk_D @ sk_E )
        = ( k2_partfun1 @ ( k2_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ sk_D ) ) )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['320','321'])).

thf('323',plain,
    ( ( u1_struct_0 @ sk_D )
    = ( k2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['46','53'])).

thf('324',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ sk_C @ X0 )
      | ( ( k3_tmap_1 @ X0 @ sk_B @ sk_C @ sk_D @ sk_E )
        = ( k2_partfun1 @ ( k2_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( k2_struct_0 @ sk_C ) ) )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['322','323'])).

thf('325',plain,
    ( ( k2_partfun1 @ ( k2_struct_0 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ sk_E @ ( k2_struct_0 @ sk_C ) )
    = ( k2_partfun1 @ ( k2_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( k2_struct_0 @ sk_C ) ) ),
    inference(clc,[status(thm)],['192','193'])).

thf('326',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ sk_C @ X0 )
      | ( ( k3_tmap_1 @ X0 @ sk_B @ sk_C @ sk_D @ sk_E )
        = ( k2_partfun1 @ ( k2_struct_0 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ sk_E @ ( k2_struct_0 @ sk_C ) ) )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['324','325'])).

thf('327',plain,
    ( ~ ( l1_pre_topc @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ~ ( m1_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) ) )
    | ( ( k3_tmap_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) ) @ sk_B @ sk_C @ sk_D @ sk_E )
      = ( k2_partfun1 @ ( k2_struct_0 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ sk_E @ ( k2_struct_0 @ sk_C ) ) )
    | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) ) )
    | ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) ) )
    | ( v2_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['319','326'])).

thf('328',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['18','19'])).

thf('329',plain,
    ( ( k2_struct_0 @ sk_C )
    = ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('330',plain,
    ( ( g1_pre_topc @ ( k2_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) )
    = sk_D ),
    inference(demod,[status(thm)],['116','117'])).

thf('331',plain,(
    m1_pre_topc @ sk_D @ sk_D ),
    inference(demod,[status(thm)],['312','313','314','315'])).

thf('332',plain,
    ( ( k2_struct_0 @ sk_C )
    = ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('333',plain,
    ( ( g1_pre_topc @ ( k2_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) )
    = sk_D ),
    inference(demod,[status(thm)],['116','117'])).

thf('334',plain,
    ( ( k2_struct_0 @ sk_C )
    = ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('335',plain,
    ( ( g1_pre_topc @ ( k2_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) )
    = sk_D ),
    inference(demod,[status(thm)],['116','117'])).

thf('336',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['12','13'])).

thf('337',plain,
    ( ( k2_struct_0 @ sk_C )
    = ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('338',plain,
    ( ( g1_pre_topc @ ( k2_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) )
    = sk_D ),
    inference(demod,[status(thm)],['116','117'])).

thf('339',plain,(
    v2_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['123','124','125'])).

thf('340',plain,
    ( ( k2_struct_0 @ sk_C )
    = ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('341',plain,
    ( ( g1_pre_topc @ ( k2_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) )
    = sk_D ),
    inference(demod,[status(thm)],['116','117'])).

thf('342',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k3_tmap_1 @ sk_D @ sk_B @ sk_C @ sk_D @ sk_E )
      = ( k2_partfun1 @ ( k2_struct_0 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ sk_E @ ( k2_struct_0 @ sk_C ) ) )
    | ( v2_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['327','328','329','330','331','332','333','334','335','336','337','338','339','340','341'])).

thf('343',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('344',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( ( k3_tmap_1 @ sk_D @ sk_B @ sk_C @ sk_D @ sk_E )
      = ( k2_partfun1 @ ( k2_struct_0 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ sk_E @ ( k2_struct_0 @ sk_C ) ) ) ),
    inference(clc,[status(thm)],['342','343'])).

thf('345',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('346',plain,
    ( ( k3_tmap_1 @ sk_D @ sk_B @ sk_C @ sk_D @ sk_E )
    = ( k2_partfun1 @ ( k2_struct_0 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ sk_E @ ( k2_struct_0 @ sk_C ) ) ),
    inference(clc,[status(thm)],['344','345'])).

thf('347',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C )
    | ( r1_tmap_1 @ sk_D @ sk_B @ ( k2_partfun1 @ ( k2_struct_0 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ sk_E @ ( k2_struct_0 @ sk_C ) ) @ sk_F )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['295','296','297','298','299','318','346'])).

thf('348',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( r1_tmap_1 @ sk_D @ sk_B @ ( k2_partfun1 @ ( k2_struct_0 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ sk_E @ ( k2_struct_0 @ sk_C ) ) @ sk_F )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['347'])).

thf('349',plain,(
    ! [X22: $i] :
      ( ( m1_pre_topc @ X22 @ X22 )
      | ~ ( l1_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('350',plain,(
    ! [X22: $i] :
      ( ( m1_pre_topc @ X22 @ X22 )
      | ~ ( l1_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('351',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ~ ( m1_pre_topc @ X1 @ sk_D )
      | ( ( k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E )
        = ( k2_partfun1 @ ( k2_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['77','78','79','86','87'])).

thf('352',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_D )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ( ( k3_tmap_1 @ X0 @ sk_B @ sk_D @ sk_D @ sk_E )
        = ( k2_partfun1 @ ( k2_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ sk_D ) ) )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['350','351'])).

thf('353',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['12','13'])).

thf('354',plain,
    ( ( u1_struct_0 @ sk_D )
    = ( k2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['46','53'])).

thf('355',plain,
    ( ( k2_partfun1 @ ( k2_struct_0 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ sk_E @ ( k2_struct_0 @ sk_C ) )
    = ( k2_partfun1 @ ( k2_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( k2_struct_0 @ sk_C ) ) ),
    inference(clc,[status(thm)],['192','193'])).

thf('356',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ( ( k3_tmap_1 @ X0 @ sk_B @ sk_D @ sk_D @ sk_E )
        = ( k2_partfun1 @ ( k2_struct_0 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ sk_E @ ( k2_struct_0 @ sk_C ) ) )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['352','353','354','355'])).

thf('357',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( ( k3_tmap_1 @ X0 @ sk_B @ sk_D @ sk_D @ sk_E )
        = ( k2_partfun1 @ ( k2_struct_0 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ sk_E @ ( k2_struct_0 @ sk_C ) ) )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['356'])).

thf('358',plain,
    ( ~ ( l1_pre_topc @ sk_D )
    | ( v2_struct_0 @ sk_D )
    | ~ ( v2_pre_topc @ sk_D )
    | ~ ( l1_pre_topc @ sk_D )
    | ( ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_D @ sk_E )
      = ( k2_partfun1 @ ( k2_struct_0 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ sk_E @ ( k2_struct_0 @ sk_C ) ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['349','357'])).

thf('359',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['12','13'])).

thf('360',plain,(
    v2_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['123','124','125'])).

thf('361',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['12','13'])).

thf('362',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_D @ sk_E )
      = ( k2_partfun1 @ ( k2_struct_0 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ sk_E @ ( k2_struct_0 @ sk_C ) ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['358','359','360','361'])).

thf('363',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('364',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_D @ sk_E )
      = ( k2_partfun1 @ ( k2_struct_0 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ sk_E @ ( k2_struct_0 @ sk_C ) ) ) ),
    inference(clc,[status(thm)],['362','363'])).

thf('365',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('366',plain,
    ( ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_D @ sk_E )
    = ( k2_partfun1 @ ( k2_struct_0 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ sk_E @ ( k2_struct_0 @ sk_C ) ) ),
    inference(clc,[status(thm)],['364','365'])).

thf('367',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['66','69'])).

thf('368',plain,
    ( ( u1_struct_0 @ sk_D )
    = ( k2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['46','53'])).

thf('369',plain,(
    ! [X28: $i,X29: $i,X30: $i,X32: $i,X33: $i,X34: $i] :
      ( ( v2_struct_0 @ X33 )
      | ~ ( v2_pre_topc @ X33 )
      | ~ ( l1_pre_topc @ X33 )
      | ( v2_struct_0 @ X30 )
      | ~ ( v1_funct_1 @ X34 )
      | ~ ( v1_funct_2 @ X34 @ ( u1_struct_0 @ X29 ) @ ( u1_struct_0 @ X33 ) )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X29 ) @ ( u1_struct_0 @ X33 ) ) ) )
      | ~ ( m1_subset_1 @ X32 @ ( u1_struct_0 @ X30 ) )
      | ( r1_tmap_1 @ X29 @ X33 @ X34 @ X32 )
      | ~ ( r1_tmap_1 @ X30 @ X33 @ ( k3_tmap_1 @ X28 @ X33 @ X29 @ X30 @ X34 ) @ X32 )
      | ~ ( m1_subset_1 @ X32 @ ( u1_struct_0 @ X29 ) )
      | ~ ( m1_pre_topc @ X30 @ X29 )
      | ~ ( m1_pre_topc @ X30 @ X28 )
      | ~ ( v1_tsep_1 @ X30 @ X28 )
      | ~ ( m1_pre_topc @ X29 @ X28 )
      | ( v2_struct_0 @ X29 )
      | ~ ( l1_pre_topc @ X28 )
      | ~ ( v2_pre_topc @ X28 )
      | ( v2_struct_0 @ X28 ) ) ),
    inference(simplify,[status(thm)],['213'])).

thf('370',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_C ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ( v2_struct_0 @ X2 )
      | ~ ( v2_pre_topc @ X2 )
      | ~ ( l1_pre_topc @ X2 )
      | ( v2_struct_0 @ sk_D )
      | ~ ( m1_pre_topc @ sk_D @ X2 )
      | ~ ( v1_tsep_1 @ X3 @ X2 )
      | ~ ( m1_pre_topc @ X3 @ X2 )
      | ~ ( m1_pre_topc @ X3 @ sk_D )
      | ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ sk_D ) )
      | ~ ( r1_tmap_1 @ X3 @ X0 @ ( k3_tmap_1 @ X2 @ X0 @ sk_D @ X3 @ X1 ) @ X4 )
      | ( r1_tmap_1 @ sk_D @ X0 @ X1 @ X4 )
      | ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ X3 ) )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ( v2_struct_0 @ X3 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['368','369'])).

thf('371',plain,
    ( ( u1_struct_0 @ sk_D )
    = ( k2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['46','53'])).

thf('372',plain,
    ( ( u1_struct_0 @ sk_D )
    = ( k2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['46','53'])).

thf('373',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_C ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ( v2_struct_0 @ X2 )
      | ~ ( v2_pre_topc @ X2 )
      | ~ ( l1_pre_topc @ X2 )
      | ( v2_struct_0 @ sk_D )
      | ~ ( m1_pre_topc @ sk_D @ X2 )
      | ~ ( v1_tsep_1 @ X3 @ X2 )
      | ~ ( m1_pre_topc @ X3 @ X2 )
      | ~ ( m1_pre_topc @ X3 @ sk_D )
      | ~ ( m1_subset_1 @ X4 @ ( k2_struct_0 @ sk_C ) )
      | ~ ( r1_tmap_1 @ X3 @ X0 @ ( k3_tmap_1 @ X2 @ X0 @ sk_D @ X3 @ X1 ) @ X4 )
      | ( r1_tmap_1 @ sk_D @ X0 @ X1 @ X4 )
      | ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ X3 ) )
      | ~ ( v1_funct_2 @ X1 @ ( k2_struct_0 @ sk_C ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ( v2_struct_0 @ X3 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['370','371','372'])).

thf('374',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( v1_funct_2 @ sk_E @ ( k2_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X1 )
      | ~ ( r1_tmap_1 @ X0 @ sk_B @ ( k3_tmap_1 @ X2 @ sk_B @ sk_D @ X0 @ sk_E ) @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( k2_struct_0 @ sk_C ) )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ~ ( m1_pre_topc @ X0 @ X2 )
      | ~ ( v1_tsep_1 @ X0 @ X2 )
      | ~ ( m1_pre_topc @ sk_D @ X2 )
      | ( v2_struct_0 @ sk_D )
      | ~ ( l1_pre_topc @ X2 )
      | ~ ( v2_pre_topc @ X2 )
      | ( v2_struct_0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['367','373'])).

thf('375',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('376',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('377',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('378',plain,(
    v1_funct_2 @ sk_E @ ( k2_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('379',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X1 )
      | ~ ( r1_tmap_1 @ X0 @ sk_B @ ( k3_tmap_1 @ X2 @ sk_B @ sk_D @ X0 @ sk_E ) @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( k2_struct_0 @ sk_C ) )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ~ ( m1_pre_topc @ X0 @ X2 )
      | ~ ( v1_tsep_1 @ X0 @ X2 )
      | ~ ( m1_pre_topc @ sk_D @ X2 )
      | ( v2_struct_0 @ sk_D )
      | ~ ( l1_pre_topc @ X2 )
      | ~ ( v2_pre_topc @ X2 )
      | ( v2_struct_0 @ X2 ) ) ),
    inference(demod,[status(thm)],['374','375','376','377','378'])).

thf('380',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tmap_1 @ sk_D @ sk_B @ ( k2_partfun1 @ ( k2_struct_0 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ sk_E @ ( k2_struct_0 @ sk_C ) ) @ X0 )
      | ( v2_struct_0 @ sk_D )
      | ~ ( v2_pre_topc @ sk_D )
      | ~ ( l1_pre_topc @ sk_D )
      | ( v2_struct_0 @ sk_D )
      | ~ ( m1_pre_topc @ sk_D @ sk_D )
      | ~ ( v1_tsep_1 @ sk_D @ sk_D )
      | ~ ( m1_pre_topc @ sk_D @ sk_D )
      | ~ ( m1_pre_topc @ sk_D @ sk_D )
      | ~ ( m1_subset_1 @ X0 @ ( k2_struct_0 @ sk_C ) )
      | ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_D ) )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['366','379'])).

thf('381',plain,(
    v2_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['123','124','125'])).

thf('382',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['12','13'])).

thf('383',plain,(
    m1_pre_topc @ sk_D @ sk_D ),
    inference(demod,[status(thm)],['312','313','314','315'])).

thf('384',plain,(
    v1_tsep_1 @ sk_D @ sk_D ),
    inference(demod,[status(thm)],['302','308','309','316','317'])).

thf('385',plain,(
    m1_pre_topc @ sk_D @ sk_D ),
    inference(demod,[status(thm)],['312','313','314','315'])).

thf('386',plain,(
    m1_pre_topc @ sk_D @ sk_D ),
    inference(demod,[status(thm)],['312','313','314','315'])).

thf('387',plain,
    ( ( u1_struct_0 @ sk_D )
    = ( k2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['46','53'])).

thf('388',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tmap_1 @ sk_D @ sk_B @ ( k2_partfun1 @ ( k2_struct_0 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ sk_E @ ( k2_struct_0 @ sk_C ) ) @ X0 )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_D )
      | ~ ( m1_subset_1 @ X0 @ ( k2_struct_0 @ sk_C ) )
      | ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k2_struct_0 @ sk_C ) )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['380','381','382','383','384','385','386','387'])).

thf('389',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k2_struct_0 @ sk_C ) )
      | ( v2_struct_0 @ sk_D )
      | ~ ( r1_tmap_1 @ sk_D @ sk_B @ ( k2_partfun1 @ ( k2_struct_0 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ sk_E @ ( k2_struct_0 @ sk_C ) ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['388'])).

thf('390',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ~ ( m1_subset_1 @ sk_F @ ( k2_struct_0 @ sk_C ) )
    | ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['348','389'])).

thf('391',plain,(
    m1_subset_1 @ sk_F @ ( k2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['266','267'])).

thf('392',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['390','391'])).

thf('393',plain,
    ( ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['392'])).

thf('394',plain,(
    ~ ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('395',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['393','394'])).

thf('396',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('397',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C ) ),
    inference(clc,[status(thm)],['395','396'])).

thf('398',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('399',plain,(
    v2_struct_0 @ sk_C ),
    inference(clc,[status(thm)],['397','398'])).

thf('400',plain,(
    $false ),
    inference(demod,[status(thm)],['0','399'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.wMeD5WEE5o
% 0.12/0.34  % Computer   : n024.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 20:14:21 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.35  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.47/0.70  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.47/0.70  % Solved by: fo/fo7.sh
% 0.47/0.70  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.47/0.70  % done 509 iterations in 0.232s
% 0.47/0.70  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.47/0.70  % SZS output start Refutation
% 0.47/0.70  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.47/0.70  thf(sk_E_type, type, sk_E: $i).
% 0.47/0.70  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.47/0.70  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.47/0.70  thf(r1_tmap_1_type, type, r1_tmap_1: $i > $i > $i > $i > $o).
% 0.47/0.70  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.47/0.70  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 0.47/0.70  thf(sk_C_type, type, sk_C: $i).
% 0.47/0.70  thf(sk_B_type, type, sk_B: $i).
% 0.47/0.70  thf(k2_partfun1_type, type, k2_partfun1: $i > $i > $i > $i > $i).
% 0.47/0.70  thf(v1_tsep_1_type, type, v1_tsep_1: $i > $i > $o).
% 0.47/0.70  thf(sk_D_type, type, sk_D: $i).
% 0.47/0.70  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.47/0.70  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.47/0.70  thf(sk_F_type, type, sk_F: $i).
% 0.47/0.70  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.47/0.70  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.47/0.70  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.47/0.70  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.47/0.70  thf(sk_A_type, type, sk_A: $i).
% 0.47/0.70  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.47/0.70  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.47/0.70  thf(k3_tmap_1_type, type, k3_tmap_1: $i > $i > $i > $i > $i > $i).
% 0.47/0.70  thf(g1_pre_topc_type, type, g1_pre_topc: $i > $i > $i).
% 0.47/0.70  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.47/0.70  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.47/0.70  thf(sk_G_type, type, sk_G: $i).
% 0.47/0.70  thf(t88_tmap_1, conjecture,
% 0.47/0.70    (![A:$i]:
% 0.47/0.70     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.47/0.70       ( ![B:$i]:
% 0.47/0.70         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.47/0.70             ( l1_pre_topc @ B ) ) =>
% 0.47/0.70           ( ![C:$i]:
% 0.47/0.70             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.47/0.70               ( ![D:$i]:
% 0.47/0.70                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.47/0.70                   ( ![E:$i]:
% 0.47/0.70                     ( ( ( v1_funct_1 @ E ) & 
% 0.47/0.70                         ( v1_funct_2 @
% 0.47/0.70                           E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 0.47/0.70                         ( m1_subset_1 @
% 0.47/0.70                           E @ 
% 0.47/0.70                           ( k1_zfmisc_1 @
% 0.47/0.70                             ( k2_zfmisc_1 @
% 0.47/0.70                               ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.47/0.70                       ( ( ( g1_pre_topc @
% 0.47/0.70                             ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) ) =
% 0.47/0.70                           ( D ) ) =>
% 0.47/0.70                         ( ![F:$i]:
% 0.47/0.70                           ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 0.47/0.70                             ( ![G:$i]:
% 0.47/0.70                               ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) ) =>
% 0.47/0.70                                 ( ( ( ( F ) = ( G ) ) & 
% 0.47/0.70                                     ( r1_tmap_1 @
% 0.47/0.70                                       C @ B @ 
% 0.47/0.70                                       ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ G ) ) =>
% 0.47/0.70                                   ( r1_tmap_1 @ D @ B @ E @ F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.47/0.70  thf(zf_stmt_0, negated_conjecture,
% 0.47/0.70    (~( ![A:$i]:
% 0.47/0.70        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.47/0.70            ( l1_pre_topc @ A ) ) =>
% 0.47/0.70          ( ![B:$i]:
% 0.47/0.70            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.47/0.70                ( l1_pre_topc @ B ) ) =>
% 0.47/0.70              ( ![C:$i]:
% 0.47/0.70                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.47/0.70                  ( ![D:$i]:
% 0.47/0.70                    ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.47/0.70                      ( ![E:$i]:
% 0.47/0.70                        ( ( ( v1_funct_1 @ E ) & 
% 0.47/0.70                            ( v1_funct_2 @
% 0.47/0.70                              E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 0.47/0.70                            ( m1_subset_1 @
% 0.47/0.70                              E @ 
% 0.47/0.70                              ( k1_zfmisc_1 @
% 0.47/0.70                                ( k2_zfmisc_1 @
% 0.47/0.70                                  ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.47/0.70                          ( ( ( g1_pre_topc @
% 0.47/0.70                                ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) ) =
% 0.47/0.70                              ( D ) ) =>
% 0.47/0.70                            ( ![F:$i]:
% 0.47/0.70                              ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 0.47/0.70                                ( ![G:$i]:
% 0.47/0.70                                  ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) ) =>
% 0.47/0.70                                    ( ( ( ( F ) = ( G ) ) & 
% 0.47/0.70                                        ( r1_tmap_1 @
% 0.47/0.70                                          C @ B @ 
% 0.47/0.70                                          ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ G ) ) =>
% 0.47/0.70                                      ( r1_tmap_1 @ D @ B @ E @ F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.47/0.70    inference('cnf.neg', [status(esa)], [t88_tmap_1])).
% 0.47/0.70  thf('0', plain, (~ (v2_struct_0 @ sk_C)),
% 0.47/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.70  thf(t2_tsep_1, axiom,
% 0.47/0.70    (![A:$i]: ( ( l1_pre_topc @ A ) => ( m1_pre_topc @ A @ A ) ))).
% 0.47/0.70  thf('1', plain,
% 0.47/0.70      (![X22 : $i]: ((m1_pre_topc @ X22 @ X22) | ~ (l1_pre_topc @ X22))),
% 0.47/0.70      inference('cnf', [status(esa)], [t2_tsep_1])).
% 0.47/0.70  thf('2', plain,
% 0.47/0.70      (((g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) = (sk_D))),
% 0.47/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.70  thf('3', plain,
% 0.47/0.70      (![X22 : $i]: ((m1_pre_topc @ X22 @ X22) | ~ (l1_pre_topc @ X22))),
% 0.47/0.70      inference('cnf', [status(esa)], [t2_tsep_1])).
% 0.47/0.70  thf(t65_pre_topc, axiom,
% 0.47/0.70    (![A:$i]:
% 0.47/0.70     ( ( l1_pre_topc @ A ) =>
% 0.47/0.70       ( ![B:$i]:
% 0.47/0.70         ( ( l1_pre_topc @ B ) =>
% 0.47/0.70           ( ( m1_pre_topc @ A @ B ) <=>
% 0.47/0.70             ( m1_pre_topc @
% 0.47/0.70               A @ ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ) ))).
% 0.47/0.70  thf('4', plain,
% 0.47/0.70      (![X9 : $i, X10 : $i]:
% 0.47/0.70         (~ (l1_pre_topc @ X9)
% 0.47/0.70          | ~ (m1_pre_topc @ X10 @ X9)
% 0.47/0.70          | (m1_pre_topc @ X10 @ 
% 0.47/0.70             (g1_pre_topc @ (u1_struct_0 @ X9) @ (u1_pre_topc @ X9)))
% 0.47/0.70          | ~ (l1_pre_topc @ X10))),
% 0.47/0.70      inference('cnf', [status(esa)], [t65_pre_topc])).
% 0.47/0.70  thf('5', plain,
% 0.47/0.70      (![X0 : $i]:
% 0.47/0.70         (~ (l1_pre_topc @ X0)
% 0.47/0.70          | ~ (l1_pre_topc @ X0)
% 0.47/0.70          | (m1_pre_topc @ X0 @ 
% 0.47/0.70             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.47/0.70          | ~ (l1_pre_topc @ X0))),
% 0.47/0.70      inference('sup-', [status(thm)], ['3', '4'])).
% 0.47/0.70  thf('6', plain,
% 0.47/0.70      (![X0 : $i]:
% 0.47/0.70         ((m1_pre_topc @ X0 @ 
% 0.47/0.70           (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.47/0.70          | ~ (l1_pre_topc @ X0))),
% 0.47/0.70      inference('simplify', [status(thm)], ['5'])).
% 0.47/0.70  thf(t35_borsuk_1, axiom,
% 0.47/0.70    (![A:$i]:
% 0.47/0.70     ( ( l1_pre_topc @ A ) =>
% 0.47/0.70       ( ![B:$i]:
% 0.47/0.70         ( ( m1_pre_topc @ B @ A ) =>
% 0.47/0.70           ( r1_tarski @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ))).
% 0.47/0.70  thf('7', plain,
% 0.47/0.70      (![X23 : $i, X24 : $i]:
% 0.47/0.70         (~ (m1_pre_topc @ X23 @ X24)
% 0.47/0.70          | (r1_tarski @ (u1_struct_0 @ X23) @ (u1_struct_0 @ X24))
% 0.47/0.70          | ~ (l1_pre_topc @ X24))),
% 0.47/0.70      inference('cnf', [status(esa)], [t35_borsuk_1])).
% 0.47/0.70  thf('8', plain,
% 0.47/0.70      (![X0 : $i]:
% 0.47/0.70         (~ (l1_pre_topc @ X0)
% 0.47/0.70          | ~ (l1_pre_topc @ 
% 0.47/0.70               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.47/0.70          | (r1_tarski @ (u1_struct_0 @ X0) @ 
% 0.47/0.70             (u1_struct_0 @ 
% 0.47/0.70              (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))))),
% 0.47/0.70      inference('sup-', [status(thm)], ['6', '7'])).
% 0.47/0.70  thf('9', plain,
% 0.47/0.70      ((~ (l1_pre_topc @ sk_D)
% 0.47/0.70        | (r1_tarski @ (u1_struct_0 @ sk_C) @ 
% 0.47/0.70           (u1_struct_0 @ 
% 0.47/0.70            (g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C))))
% 0.47/0.70        | ~ (l1_pre_topc @ sk_C))),
% 0.47/0.70      inference('sup-', [status(thm)], ['2', '8'])).
% 0.47/0.70  thf('10', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.47/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.70  thf(dt_m1_pre_topc, axiom,
% 0.47/0.70    (![A:$i]:
% 0.47/0.70     ( ( l1_pre_topc @ A ) =>
% 0.47/0.70       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.47/0.70  thf('11', plain,
% 0.47/0.70      (![X7 : $i, X8 : $i]:
% 0.47/0.70         (~ (m1_pre_topc @ X7 @ X8) | (l1_pre_topc @ X7) | ~ (l1_pre_topc @ X8))),
% 0.47/0.70      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.47/0.70  thf('12', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_D))),
% 0.47/0.70      inference('sup-', [status(thm)], ['10', '11'])).
% 0.47/0.70  thf('13', plain, ((l1_pre_topc @ sk_A)),
% 0.47/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.70  thf('14', plain, ((l1_pre_topc @ sk_D)),
% 0.47/0.70      inference('demod', [status(thm)], ['12', '13'])).
% 0.47/0.70  thf('15', plain,
% 0.47/0.70      (((g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) = (sk_D))),
% 0.47/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.70  thf('16', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.47/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.70  thf('17', plain,
% 0.47/0.70      (![X7 : $i, X8 : $i]:
% 0.47/0.70         (~ (m1_pre_topc @ X7 @ X8) | (l1_pre_topc @ X7) | ~ (l1_pre_topc @ X8))),
% 0.47/0.70      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.47/0.70  thf('18', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_C))),
% 0.47/0.70      inference('sup-', [status(thm)], ['16', '17'])).
% 0.47/0.70  thf('19', plain, ((l1_pre_topc @ sk_A)),
% 0.47/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.70  thf('20', plain, ((l1_pre_topc @ sk_C)),
% 0.47/0.70      inference('demod', [status(thm)], ['18', '19'])).
% 0.47/0.70  thf('21', plain, ((r1_tarski @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D))),
% 0.47/0.70      inference('demod', [status(thm)], ['9', '14', '15', '20'])).
% 0.47/0.70  thf(d10_xboole_0, axiom,
% 0.47/0.70    (![A:$i,B:$i]:
% 0.47/0.70     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.47/0.70  thf('22', plain,
% 0.47/0.70      (![X0 : $i, X2 : $i]:
% 0.47/0.70         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.47/0.70      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.47/0.70  thf('23', plain,
% 0.47/0.70      ((~ (r1_tarski @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_C))
% 0.47/0.70        | ((u1_struct_0 @ sk_D) = (u1_struct_0 @ sk_C)))),
% 0.47/0.70      inference('sup-', [status(thm)], ['21', '22'])).
% 0.47/0.70  thf('24', plain,
% 0.47/0.70      (((g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) = (sk_D))),
% 0.47/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.70  thf('25', plain,
% 0.47/0.70      (![X22 : $i]: ((m1_pre_topc @ X22 @ X22) | ~ (l1_pre_topc @ X22))),
% 0.47/0.70      inference('cnf', [status(esa)], [t2_tsep_1])).
% 0.47/0.70  thf('26', plain,
% 0.47/0.70      (![X9 : $i, X10 : $i]:
% 0.47/0.70         (~ (l1_pre_topc @ X9)
% 0.47/0.70          | ~ (m1_pre_topc @ X10 @ 
% 0.47/0.70               (g1_pre_topc @ (u1_struct_0 @ X9) @ (u1_pre_topc @ X9)))
% 0.47/0.70          | (m1_pre_topc @ X10 @ X9)
% 0.47/0.70          | ~ (l1_pre_topc @ X10))),
% 0.47/0.70      inference('cnf', [status(esa)], [t65_pre_topc])).
% 0.47/0.70  thf('27', plain,
% 0.47/0.70      (![X0 : $i]:
% 0.47/0.70         (~ (l1_pre_topc @ 
% 0.47/0.70             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.47/0.70          | ~ (l1_pre_topc @ 
% 0.47/0.70               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.47/0.70          | (m1_pre_topc @ 
% 0.47/0.70             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)) @ X0)
% 0.47/0.70          | ~ (l1_pre_topc @ X0))),
% 0.47/0.70      inference('sup-', [status(thm)], ['25', '26'])).
% 0.47/0.70  thf('28', plain,
% 0.47/0.70      (![X0 : $i]:
% 0.47/0.70         (~ (l1_pre_topc @ X0)
% 0.47/0.70          | (m1_pre_topc @ 
% 0.47/0.70             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)) @ X0)
% 0.47/0.70          | ~ (l1_pre_topc @ 
% 0.47/0.70               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 0.47/0.70      inference('simplify', [status(thm)], ['27'])).
% 0.47/0.70  thf('29', plain,
% 0.47/0.70      ((~ (l1_pre_topc @ sk_D)
% 0.47/0.70        | (m1_pre_topc @ 
% 0.47/0.70           (g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) @ sk_C)
% 0.47/0.70        | ~ (l1_pre_topc @ sk_C))),
% 0.47/0.70      inference('sup-', [status(thm)], ['24', '28'])).
% 0.47/0.70  thf('30', plain, ((l1_pre_topc @ sk_D)),
% 0.47/0.70      inference('demod', [status(thm)], ['12', '13'])).
% 0.47/0.70  thf('31', plain,
% 0.47/0.70      (((g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) = (sk_D))),
% 0.47/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.70  thf('32', plain, ((l1_pre_topc @ sk_C)),
% 0.47/0.70      inference('demod', [status(thm)], ['18', '19'])).
% 0.47/0.70  thf('33', plain, ((m1_pre_topc @ sk_D @ sk_C)),
% 0.47/0.70      inference('demod', [status(thm)], ['29', '30', '31', '32'])).
% 0.47/0.70  thf('34', plain,
% 0.47/0.70      (![X23 : $i, X24 : $i]:
% 0.47/0.70         (~ (m1_pre_topc @ X23 @ X24)
% 0.47/0.70          | (r1_tarski @ (u1_struct_0 @ X23) @ (u1_struct_0 @ X24))
% 0.47/0.70          | ~ (l1_pre_topc @ X24))),
% 0.47/0.70      inference('cnf', [status(esa)], [t35_borsuk_1])).
% 0.47/0.70  thf('35', plain,
% 0.47/0.70      ((~ (l1_pre_topc @ sk_C)
% 0.47/0.70        | (r1_tarski @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_C)))),
% 0.47/0.70      inference('sup-', [status(thm)], ['33', '34'])).
% 0.47/0.70  thf('36', plain, ((l1_pre_topc @ sk_C)),
% 0.47/0.70      inference('demod', [status(thm)], ['18', '19'])).
% 0.47/0.70  thf('37', plain, ((r1_tarski @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_C))),
% 0.47/0.70      inference('demod', [status(thm)], ['35', '36'])).
% 0.47/0.70  thf('38', plain, (((u1_struct_0 @ sk_D) = (u1_struct_0 @ sk_C))),
% 0.47/0.70      inference('demod', [status(thm)], ['23', '37'])).
% 0.47/0.70  thf(d3_struct_0, axiom,
% 0.47/0.70    (![A:$i]:
% 0.47/0.70     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.47/0.70  thf('39', plain,
% 0.47/0.70      (![X5 : $i]:
% 0.47/0.70         (((k2_struct_0 @ X5) = (u1_struct_0 @ X5)) | ~ (l1_struct_0 @ X5))),
% 0.47/0.70      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.47/0.70  thf('40', plain, (((u1_struct_0 @ sk_D) = (u1_struct_0 @ sk_C))),
% 0.47/0.70      inference('demod', [status(thm)], ['23', '37'])).
% 0.47/0.70  thf('41', plain,
% 0.47/0.70      ((((k2_struct_0 @ sk_D) = (u1_struct_0 @ sk_C)) | ~ (l1_struct_0 @ sk_D))),
% 0.47/0.70      inference('sup+', [status(thm)], ['39', '40'])).
% 0.47/0.70  thf('42', plain, ((l1_pre_topc @ sk_D)),
% 0.47/0.70      inference('demod', [status(thm)], ['12', '13'])).
% 0.47/0.70  thf(dt_l1_pre_topc, axiom,
% 0.47/0.70    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.47/0.70  thf('43', plain, (![X6 : $i]: ((l1_struct_0 @ X6) | ~ (l1_pre_topc @ X6))),
% 0.47/0.70      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.47/0.70  thf('44', plain, ((l1_struct_0 @ sk_D)),
% 0.47/0.70      inference('sup-', [status(thm)], ['42', '43'])).
% 0.47/0.70  thf('45', plain, (((k2_struct_0 @ sk_D) = (u1_struct_0 @ sk_C))),
% 0.47/0.70      inference('demod', [status(thm)], ['41', '44'])).
% 0.47/0.70  thf('46', plain, (((u1_struct_0 @ sk_D) = (k2_struct_0 @ sk_D))),
% 0.47/0.70      inference('demod', [status(thm)], ['38', '45'])).
% 0.47/0.70  thf('47', plain,
% 0.47/0.70      (![X5 : $i]:
% 0.47/0.70         (((k2_struct_0 @ X5) = (u1_struct_0 @ X5)) | ~ (l1_struct_0 @ X5))),
% 0.47/0.70      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.47/0.70  thf('48', plain, (((k2_struct_0 @ sk_D) = (u1_struct_0 @ sk_C))),
% 0.47/0.70      inference('demod', [status(thm)], ['41', '44'])).
% 0.47/0.70  thf('49', plain,
% 0.47/0.70      ((((k2_struct_0 @ sk_D) = (k2_struct_0 @ sk_C)) | ~ (l1_struct_0 @ sk_C))),
% 0.47/0.70      inference('sup+', [status(thm)], ['47', '48'])).
% 0.47/0.70  thf('50', plain, ((l1_pre_topc @ sk_C)),
% 0.47/0.70      inference('demod', [status(thm)], ['18', '19'])).
% 0.47/0.70  thf('51', plain, (![X6 : $i]: ((l1_struct_0 @ X6) | ~ (l1_pre_topc @ X6))),
% 0.47/0.70      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.47/0.70  thf('52', plain, ((l1_struct_0 @ sk_C)),
% 0.47/0.70      inference('sup-', [status(thm)], ['50', '51'])).
% 0.47/0.70  thf('53', plain, (((k2_struct_0 @ sk_D) = (k2_struct_0 @ sk_C))),
% 0.47/0.70      inference('demod', [status(thm)], ['49', '52'])).
% 0.47/0.70  thf('54', plain, (((u1_struct_0 @ sk_D) = (k2_struct_0 @ sk_C))),
% 0.47/0.70      inference('demod', [status(thm)], ['46', '53'])).
% 0.47/0.70  thf('55', plain,
% 0.47/0.70      ((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.47/0.70        (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_G)),
% 0.47/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.70  thf('56', plain, (((sk_F) = (sk_G))),
% 0.47/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.70  thf('57', plain,
% 0.47/0.70      ((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.47/0.70        (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_F)),
% 0.47/0.70      inference('demod', [status(thm)], ['55', '56'])).
% 0.47/0.70  thf('58', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.47/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.70  thf('59', plain,
% 0.47/0.70      (((g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) = (sk_D))),
% 0.47/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.70  thf('60', plain,
% 0.47/0.70      (![X0 : $i]:
% 0.47/0.70         ((m1_pre_topc @ X0 @ 
% 0.47/0.70           (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.47/0.70          | ~ (l1_pre_topc @ X0))),
% 0.47/0.70      inference('simplify', [status(thm)], ['5'])).
% 0.47/0.70  thf('61', plain, (((m1_pre_topc @ sk_C @ sk_D) | ~ (l1_pre_topc @ sk_C))),
% 0.47/0.70      inference('sup+', [status(thm)], ['59', '60'])).
% 0.47/0.70  thf('62', plain, ((l1_pre_topc @ sk_C)),
% 0.47/0.70      inference('demod', [status(thm)], ['18', '19'])).
% 0.47/0.70  thf('63', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 0.47/0.70      inference('demod', [status(thm)], ['61', '62'])).
% 0.47/0.70  thf('64', plain,
% 0.47/0.70      ((m1_subset_1 @ sk_E @ 
% 0.47/0.70        (k1_zfmisc_1 @ 
% 0.47/0.70         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 0.47/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.70  thf('65', plain, (((u1_struct_0 @ sk_D) = (u1_struct_0 @ sk_C))),
% 0.47/0.70      inference('demod', [status(thm)], ['23', '37'])).
% 0.47/0.70  thf('66', plain,
% 0.47/0.70      ((m1_subset_1 @ sk_E @ 
% 0.47/0.70        (k1_zfmisc_1 @ 
% 0.47/0.70         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 0.47/0.70      inference('demod', [status(thm)], ['64', '65'])).
% 0.47/0.70  thf('67', plain, (((k2_struct_0 @ sk_D) = (u1_struct_0 @ sk_C))),
% 0.47/0.70      inference('demod', [status(thm)], ['41', '44'])).
% 0.47/0.70  thf('68', plain, (((k2_struct_0 @ sk_D) = (k2_struct_0 @ sk_C))),
% 0.47/0.70      inference('demod', [status(thm)], ['49', '52'])).
% 0.47/0.70  thf('69', plain, (((k2_struct_0 @ sk_C) = (u1_struct_0 @ sk_C))),
% 0.47/0.70      inference('demod', [status(thm)], ['67', '68'])).
% 0.47/0.70  thf('70', plain,
% 0.47/0.70      ((m1_subset_1 @ sk_E @ 
% 0.47/0.70        (k1_zfmisc_1 @ 
% 0.47/0.70         (k2_zfmisc_1 @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 0.47/0.70      inference('demod', [status(thm)], ['66', '69'])).
% 0.47/0.70  thf('71', plain, (((u1_struct_0 @ sk_D) = (k2_struct_0 @ sk_C))),
% 0.47/0.70      inference('demod', [status(thm)], ['46', '53'])).
% 0.47/0.70  thf(d5_tmap_1, axiom,
% 0.47/0.70    (![A:$i]:
% 0.47/0.70     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.47/0.70       ( ![B:$i]:
% 0.47/0.70         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.47/0.70             ( l1_pre_topc @ B ) ) =>
% 0.47/0.70           ( ![C:$i]:
% 0.47/0.70             ( ( m1_pre_topc @ C @ A ) =>
% 0.47/0.70               ( ![D:$i]:
% 0.47/0.70                 ( ( m1_pre_topc @ D @ A ) =>
% 0.47/0.70                   ( ![E:$i]:
% 0.47/0.70                     ( ( ( v1_funct_1 @ E ) & 
% 0.47/0.70                         ( v1_funct_2 @
% 0.47/0.70                           E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 0.47/0.70                         ( m1_subset_1 @
% 0.47/0.70                           E @ 
% 0.47/0.70                           ( k1_zfmisc_1 @
% 0.47/0.70                             ( k2_zfmisc_1 @
% 0.47/0.70                               ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.47/0.70                       ( ( m1_pre_topc @ D @ C ) =>
% 0.47/0.70                         ( ( k3_tmap_1 @ A @ B @ C @ D @ E ) =
% 0.47/0.70                           ( k2_partfun1 @
% 0.47/0.70                             ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ E @ 
% 0.47/0.70                             ( u1_struct_0 @ D ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.47/0.70  thf('72', plain,
% 0.47/0.70      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.47/0.70         ((v2_struct_0 @ X12)
% 0.47/0.70          | ~ (v2_pre_topc @ X12)
% 0.47/0.70          | ~ (l1_pre_topc @ X12)
% 0.47/0.70          | ~ (m1_pre_topc @ X13 @ X14)
% 0.47/0.70          | ~ (m1_pre_topc @ X13 @ X15)
% 0.47/0.70          | ((k3_tmap_1 @ X14 @ X12 @ X15 @ X13 @ X16)
% 0.47/0.70              = (k2_partfun1 @ (u1_struct_0 @ X15) @ (u1_struct_0 @ X12) @ 
% 0.47/0.70                 X16 @ (u1_struct_0 @ X13)))
% 0.47/0.70          | ~ (m1_subset_1 @ X16 @ 
% 0.47/0.70               (k1_zfmisc_1 @ 
% 0.47/0.70                (k2_zfmisc_1 @ (u1_struct_0 @ X15) @ (u1_struct_0 @ X12))))
% 0.47/0.70          | ~ (v1_funct_2 @ X16 @ (u1_struct_0 @ X15) @ (u1_struct_0 @ X12))
% 0.47/0.70          | ~ (v1_funct_1 @ X16)
% 0.47/0.70          | ~ (m1_pre_topc @ X15 @ X14)
% 0.47/0.70          | ~ (l1_pre_topc @ X14)
% 0.47/0.70          | ~ (v2_pre_topc @ X14)
% 0.47/0.70          | (v2_struct_0 @ X14))),
% 0.47/0.70      inference('cnf', [status(esa)], [d5_tmap_1])).
% 0.47/0.70  thf('73', plain,
% 0.47/0.70      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.47/0.70         (~ (m1_subset_1 @ X1 @ 
% 0.47/0.70             (k1_zfmisc_1 @ 
% 0.47/0.70              (k2_zfmisc_1 @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ X0))))
% 0.47/0.70          | (v2_struct_0 @ X2)
% 0.47/0.70          | ~ (v2_pre_topc @ X2)
% 0.47/0.70          | ~ (l1_pre_topc @ X2)
% 0.47/0.70          | ~ (m1_pre_topc @ sk_D @ X2)
% 0.47/0.70          | ~ (v1_funct_1 @ X1)
% 0.47/0.70          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ X0))
% 0.47/0.70          | ((k3_tmap_1 @ X2 @ X0 @ sk_D @ X3 @ X1)
% 0.47/0.70              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ X0) @ 
% 0.47/0.70                 X1 @ (u1_struct_0 @ X3)))
% 0.47/0.70          | ~ (m1_pre_topc @ X3 @ sk_D)
% 0.47/0.70          | ~ (m1_pre_topc @ X3 @ X2)
% 0.47/0.70          | ~ (l1_pre_topc @ X0)
% 0.47/0.70          | ~ (v2_pre_topc @ X0)
% 0.47/0.70          | (v2_struct_0 @ X0))),
% 0.47/0.70      inference('sup-', [status(thm)], ['71', '72'])).
% 0.47/0.70  thf('74', plain, (((u1_struct_0 @ sk_D) = (k2_struct_0 @ sk_C))),
% 0.47/0.70      inference('demod', [status(thm)], ['46', '53'])).
% 0.47/0.70  thf('75', plain, (((u1_struct_0 @ sk_D) = (k2_struct_0 @ sk_C))),
% 0.47/0.70      inference('demod', [status(thm)], ['46', '53'])).
% 0.47/0.70  thf('76', plain,
% 0.47/0.70      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.47/0.70         (~ (m1_subset_1 @ X1 @ 
% 0.47/0.70             (k1_zfmisc_1 @ 
% 0.47/0.70              (k2_zfmisc_1 @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ X0))))
% 0.47/0.70          | (v2_struct_0 @ X2)
% 0.47/0.70          | ~ (v2_pre_topc @ X2)
% 0.47/0.70          | ~ (l1_pre_topc @ X2)
% 0.47/0.70          | ~ (m1_pre_topc @ sk_D @ X2)
% 0.47/0.70          | ~ (v1_funct_1 @ X1)
% 0.47/0.70          | ~ (v1_funct_2 @ X1 @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ X0))
% 0.47/0.70          | ((k3_tmap_1 @ X2 @ X0 @ sk_D @ X3 @ X1)
% 0.47/0.70              = (k2_partfun1 @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ X0) @ 
% 0.47/0.70                 X1 @ (u1_struct_0 @ X3)))
% 0.47/0.70          | ~ (m1_pre_topc @ X3 @ sk_D)
% 0.47/0.70          | ~ (m1_pre_topc @ X3 @ X2)
% 0.47/0.70          | ~ (l1_pre_topc @ X0)
% 0.47/0.70          | ~ (v2_pre_topc @ X0)
% 0.47/0.70          | (v2_struct_0 @ X0))),
% 0.47/0.70      inference('demod', [status(thm)], ['73', '74', '75'])).
% 0.47/0.70  thf('77', plain,
% 0.47/0.70      (![X0 : $i, X1 : $i]:
% 0.47/0.70         ((v2_struct_0 @ sk_B)
% 0.47/0.70          | ~ (v2_pre_topc @ sk_B)
% 0.47/0.70          | ~ (l1_pre_topc @ sk_B)
% 0.47/0.70          | ~ (m1_pre_topc @ X1 @ X0)
% 0.47/0.70          | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.47/0.70          | ((k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E)
% 0.47/0.70              = (k2_partfun1 @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.47/0.70                 sk_E @ (u1_struct_0 @ X1)))
% 0.47/0.70          | ~ (v1_funct_2 @ sk_E @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))
% 0.47/0.70          | ~ (v1_funct_1 @ sk_E)
% 0.47/0.70          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.47/0.70          | ~ (l1_pre_topc @ X0)
% 0.47/0.70          | ~ (v2_pre_topc @ X0)
% 0.47/0.70          | (v2_struct_0 @ X0))),
% 0.47/0.70      inference('sup-', [status(thm)], ['70', '76'])).
% 0.47/0.70  thf('78', plain, ((v2_pre_topc @ sk_B)),
% 0.47/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.70  thf('79', plain, ((l1_pre_topc @ sk_B)),
% 0.47/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.70  thf('80', plain,
% 0.47/0.70      (![X5 : $i]:
% 0.47/0.70         (((k2_struct_0 @ X5) = (u1_struct_0 @ X5)) | ~ (l1_struct_0 @ X5))),
% 0.47/0.70      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.47/0.70  thf('81', plain,
% 0.47/0.70      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 0.47/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.70  thf('82', plain,
% 0.47/0.70      (((v1_funct_2 @ sk_E @ (k2_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.47/0.70        | ~ (l1_struct_0 @ sk_D))),
% 0.47/0.70      inference('sup+', [status(thm)], ['80', '81'])).
% 0.47/0.70  thf('83', plain, ((l1_struct_0 @ sk_D)),
% 0.47/0.70      inference('sup-', [status(thm)], ['42', '43'])).
% 0.47/0.70  thf('84', plain,
% 0.47/0.70      ((v1_funct_2 @ sk_E @ (k2_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 0.47/0.70      inference('demod', [status(thm)], ['82', '83'])).
% 0.47/0.70  thf('85', plain, (((k2_struct_0 @ sk_D) = (k2_struct_0 @ sk_C))),
% 0.47/0.70      inference('demod', [status(thm)], ['49', '52'])).
% 0.47/0.70  thf('86', plain,
% 0.47/0.70      ((v1_funct_2 @ sk_E @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 0.47/0.70      inference('demod', [status(thm)], ['84', '85'])).
% 0.47/0.70  thf('87', plain, ((v1_funct_1 @ sk_E)),
% 0.47/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.70  thf('88', plain,
% 0.47/0.70      (![X0 : $i, X1 : $i]:
% 0.47/0.70         ((v2_struct_0 @ sk_B)
% 0.47/0.70          | ~ (m1_pre_topc @ X1 @ X0)
% 0.47/0.70          | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.47/0.70          | ((k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E)
% 0.47/0.70              = (k2_partfun1 @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.47/0.70                 sk_E @ (u1_struct_0 @ X1)))
% 0.47/0.70          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.47/0.70          | ~ (l1_pre_topc @ X0)
% 0.47/0.70          | ~ (v2_pre_topc @ X0)
% 0.47/0.70          | (v2_struct_0 @ X0))),
% 0.47/0.70      inference('demod', [status(thm)], ['77', '78', '79', '86', '87'])).
% 0.47/0.70  thf('89', plain,
% 0.47/0.70      (![X0 : $i]:
% 0.47/0.70         ((v2_struct_0 @ X0)
% 0.47/0.70          | ~ (v2_pre_topc @ X0)
% 0.47/0.70          | ~ (l1_pre_topc @ X0)
% 0.47/0.70          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.47/0.70          | ((k3_tmap_1 @ X0 @ sk_B @ sk_D @ sk_C @ sk_E)
% 0.47/0.70              = (k2_partfun1 @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.47/0.70                 sk_E @ (u1_struct_0 @ sk_C)))
% 0.47/0.70          | ~ (m1_pre_topc @ sk_C @ X0)
% 0.47/0.70          | (v2_struct_0 @ sk_B))),
% 0.47/0.70      inference('sup-', [status(thm)], ['63', '88'])).
% 0.47/0.70  thf('90', plain, (((k2_struct_0 @ sk_C) = (u1_struct_0 @ sk_C))),
% 0.47/0.70      inference('demod', [status(thm)], ['67', '68'])).
% 0.47/0.70  thf('91', plain,
% 0.47/0.70      (![X0 : $i]:
% 0.47/0.70         ((m1_pre_topc @ X0 @ 
% 0.47/0.70           (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.47/0.70          | ~ (l1_pre_topc @ X0))),
% 0.47/0.70      inference('simplify', [status(thm)], ['5'])).
% 0.47/0.70  thf('92', plain,
% 0.47/0.70      (![X22 : $i]: ((m1_pre_topc @ X22 @ X22) | ~ (l1_pre_topc @ X22))),
% 0.47/0.70      inference('cnf', [status(esa)], [t2_tsep_1])).
% 0.47/0.70  thf('93', plain,
% 0.47/0.70      ((m1_subset_1 @ sk_E @ 
% 0.47/0.70        (k1_zfmisc_1 @ 
% 0.47/0.70         (k2_zfmisc_1 @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 0.47/0.70      inference('demod', [status(thm)], ['66', '69'])).
% 0.47/0.70  thf('94', plain,
% 0.47/0.70      (![X5 : $i]:
% 0.47/0.70         (((k2_struct_0 @ X5) = (u1_struct_0 @ X5)) | ~ (l1_struct_0 @ X5))),
% 0.47/0.70      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.47/0.70  thf('95', plain,
% 0.47/0.70      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.47/0.70         ((v2_struct_0 @ X12)
% 0.47/0.70          | ~ (v2_pre_topc @ X12)
% 0.47/0.70          | ~ (l1_pre_topc @ X12)
% 0.47/0.70          | ~ (m1_pre_topc @ X13 @ X14)
% 0.47/0.70          | ~ (m1_pre_topc @ X13 @ X15)
% 0.47/0.70          | ((k3_tmap_1 @ X14 @ X12 @ X15 @ X13 @ X16)
% 0.47/0.70              = (k2_partfun1 @ (u1_struct_0 @ X15) @ (u1_struct_0 @ X12) @ 
% 0.47/0.70                 X16 @ (u1_struct_0 @ X13)))
% 0.47/0.70          | ~ (m1_subset_1 @ X16 @ 
% 0.47/0.70               (k1_zfmisc_1 @ 
% 0.47/0.70                (k2_zfmisc_1 @ (u1_struct_0 @ X15) @ (u1_struct_0 @ X12))))
% 0.47/0.70          | ~ (v1_funct_2 @ X16 @ (u1_struct_0 @ X15) @ (u1_struct_0 @ X12))
% 0.47/0.70          | ~ (v1_funct_1 @ X16)
% 0.47/0.70          | ~ (m1_pre_topc @ X15 @ X14)
% 0.47/0.70          | ~ (l1_pre_topc @ X14)
% 0.47/0.70          | ~ (v2_pre_topc @ X14)
% 0.47/0.70          | (v2_struct_0 @ X14))),
% 0.47/0.70      inference('cnf', [status(esa)], [d5_tmap_1])).
% 0.47/0.70  thf('96', plain,
% 0.47/0.70      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.47/0.70         (~ (m1_subset_1 @ X2 @ 
% 0.47/0.70             (k1_zfmisc_1 @ 
% 0.47/0.70              (k2_zfmisc_1 @ (k2_struct_0 @ X0) @ (u1_struct_0 @ X1))))
% 0.47/0.70          | ~ (l1_struct_0 @ X0)
% 0.47/0.70          | (v2_struct_0 @ X3)
% 0.47/0.70          | ~ (v2_pre_topc @ X3)
% 0.47/0.70          | ~ (l1_pre_topc @ X3)
% 0.47/0.70          | ~ (m1_pre_topc @ X0 @ X3)
% 0.47/0.70          | ~ (v1_funct_1 @ X2)
% 0.47/0.70          | ~ (v1_funct_2 @ X2 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X1))
% 0.47/0.70          | ((k3_tmap_1 @ X3 @ X1 @ X0 @ X4 @ X2)
% 0.47/0.70              = (k2_partfun1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X1) @ X2 @ 
% 0.47/0.70                 (u1_struct_0 @ X4)))
% 0.47/0.70          | ~ (m1_pre_topc @ X4 @ X0)
% 0.47/0.70          | ~ (m1_pre_topc @ X4 @ X3)
% 0.47/0.70          | ~ (l1_pre_topc @ X1)
% 0.47/0.70          | ~ (v2_pre_topc @ X1)
% 0.47/0.70          | (v2_struct_0 @ X1))),
% 0.47/0.70      inference('sup-', [status(thm)], ['94', '95'])).
% 0.47/0.70  thf('97', plain,
% 0.47/0.70      (![X0 : $i, X1 : $i]:
% 0.47/0.70         ((v2_struct_0 @ sk_B)
% 0.47/0.70          | ~ (v2_pre_topc @ sk_B)
% 0.47/0.70          | ~ (l1_pre_topc @ sk_B)
% 0.47/0.70          | ~ (m1_pre_topc @ X1 @ X0)
% 0.47/0.70          | ~ (m1_pre_topc @ X1 @ sk_C)
% 0.47/0.70          | ((k3_tmap_1 @ X0 @ sk_B @ sk_C @ X1 @ sk_E)
% 0.47/0.70              = (k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.47/0.70                 sk_E @ (u1_struct_0 @ X1)))
% 0.47/0.70          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))
% 0.47/0.70          | ~ (v1_funct_1 @ sk_E)
% 0.47/0.70          | ~ (m1_pre_topc @ sk_C @ X0)
% 0.47/0.70          | ~ (l1_pre_topc @ X0)
% 0.47/0.70          | ~ (v2_pre_topc @ X0)
% 0.47/0.70          | (v2_struct_0 @ X0)
% 0.47/0.70          | ~ (l1_struct_0 @ sk_C))),
% 0.47/0.70      inference('sup-', [status(thm)], ['93', '96'])).
% 0.47/0.70  thf('98', plain, ((v2_pre_topc @ sk_B)),
% 0.47/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.70  thf('99', plain, ((l1_pre_topc @ sk_B)),
% 0.47/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.70  thf('100', plain, (((k2_struct_0 @ sk_C) = (u1_struct_0 @ sk_C))),
% 0.47/0.70      inference('demod', [status(thm)], ['67', '68'])).
% 0.47/0.70  thf('101', plain, (((k2_struct_0 @ sk_C) = (u1_struct_0 @ sk_C))),
% 0.47/0.70      inference('demod', [status(thm)], ['67', '68'])).
% 0.47/0.70  thf('102', plain,
% 0.47/0.70      ((v1_funct_2 @ sk_E @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 0.47/0.70      inference('demod', [status(thm)], ['84', '85'])).
% 0.47/0.70  thf('103', plain, ((v1_funct_1 @ sk_E)),
% 0.47/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.70  thf('104', plain, ((l1_struct_0 @ sk_C)),
% 0.47/0.70      inference('sup-', [status(thm)], ['50', '51'])).
% 0.47/0.70  thf('105', plain,
% 0.47/0.70      (![X0 : $i, X1 : $i]:
% 0.47/0.70         ((v2_struct_0 @ sk_B)
% 0.47/0.70          | ~ (m1_pre_topc @ X1 @ X0)
% 0.47/0.70          | ~ (m1_pre_topc @ X1 @ sk_C)
% 0.47/0.70          | ((k3_tmap_1 @ X0 @ sk_B @ sk_C @ X1 @ sk_E)
% 0.47/0.70              = (k2_partfun1 @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.47/0.70                 sk_E @ (u1_struct_0 @ X1)))
% 0.47/0.70          | ~ (m1_pre_topc @ sk_C @ X0)
% 0.47/0.70          | ~ (l1_pre_topc @ X0)
% 0.47/0.70          | ~ (v2_pre_topc @ X0)
% 0.47/0.70          | (v2_struct_0 @ X0))),
% 0.47/0.70      inference('demod', [status(thm)],
% 0.47/0.70                ['97', '98', '99', '100', '101', '102', '103', '104'])).
% 0.47/0.70  thf('106', plain,
% 0.47/0.70      (![X0 : $i]:
% 0.47/0.70         (~ (l1_pre_topc @ sk_C)
% 0.47/0.70          | (v2_struct_0 @ X0)
% 0.47/0.70          | ~ (v2_pre_topc @ X0)
% 0.47/0.70          | ~ (l1_pre_topc @ X0)
% 0.47/0.70          | ~ (m1_pre_topc @ sk_C @ X0)
% 0.47/0.70          | ((k3_tmap_1 @ X0 @ sk_B @ sk_C @ sk_C @ sk_E)
% 0.47/0.70              = (k2_partfun1 @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.47/0.70                 sk_E @ (u1_struct_0 @ sk_C)))
% 0.47/0.70          | ~ (m1_pre_topc @ sk_C @ X0)
% 0.47/0.70          | (v2_struct_0 @ sk_B))),
% 0.47/0.70      inference('sup-', [status(thm)], ['92', '105'])).
% 0.47/0.70  thf('107', plain, ((l1_pre_topc @ sk_C)),
% 0.47/0.70      inference('demod', [status(thm)], ['18', '19'])).
% 0.47/0.70  thf('108', plain, (((k2_struct_0 @ sk_C) = (u1_struct_0 @ sk_C))),
% 0.47/0.70      inference('demod', [status(thm)], ['67', '68'])).
% 0.47/0.70  thf('109', plain,
% 0.47/0.70      (![X0 : $i]:
% 0.47/0.70         ((v2_struct_0 @ X0)
% 0.47/0.70          | ~ (v2_pre_topc @ X0)
% 0.47/0.70          | ~ (l1_pre_topc @ X0)
% 0.47/0.70          | ~ (m1_pre_topc @ sk_C @ X0)
% 0.47/0.70          | ((k3_tmap_1 @ X0 @ sk_B @ sk_C @ sk_C @ sk_E)
% 0.47/0.70              = (k2_partfun1 @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.47/0.70                 sk_E @ (k2_struct_0 @ sk_C)))
% 0.47/0.70          | ~ (m1_pre_topc @ sk_C @ X0)
% 0.47/0.70          | (v2_struct_0 @ sk_B))),
% 0.47/0.70      inference('demod', [status(thm)], ['106', '107', '108'])).
% 0.47/0.70  thf('110', plain,
% 0.47/0.70      (![X0 : $i]:
% 0.47/0.70         ((v2_struct_0 @ sk_B)
% 0.47/0.70          | ((k3_tmap_1 @ X0 @ sk_B @ sk_C @ sk_C @ sk_E)
% 0.47/0.70              = (k2_partfun1 @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.47/0.70                 sk_E @ (k2_struct_0 @ sk_C)))
% 0.47/0.70          | ~ (m1_pre_topc @ sk_C @ X0)
% 0.47/0.70          | ~ (l1_pre_topc @ X0)
% 0.47/0.70          | ~ (v2_pre_topc @ X0)
% 0.47/0.70          | (v2_struct_0 @ X0))),
% 0.47/0.70      inference('simplify', [status(thm)], ['109'])).
% 0.47/0.70  thf('111', plain,
% 0.47/0.70      ((~ (l1_pre_topc @ sk_C)
% 0.47/0.70        | (v2_struct_0 @ 
% 0.47/0.70           (g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)))
% 0.47/0.70        | ~ (v2_pre_topc @ 
% 0.47/0.70             (g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)))
% 0.47/0.70        | ~ (l1_pre_topc @ 
% 0.47/0.70             (g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)))
% 0.47/0.70        | ((k3_tmap_1 @ 
% 0.47/0.70            (g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) @ 
% 0.47/0.70            sk_B @ sk_C @ sk_C @ sk_E)
% 0.47/0.70            = (k2_partfun1 @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.47/0.70               sk_E @ (k2_struct_0 @ sk_C)))
% 0.47/0.70        | (v2_struct_0 @ sk_B))),
% 0.47/0.70      inference('sup-', [status(thm)], ['91', '110'])).
% 0.47/0.70  thf('112', plain, ((l1_pre_topc @ sk_C)),
% 0.47/0.70      inference('demod', [status(thm)], ['18', '19'])).
% 0.47/0.70  thf('113', plain, (((k2_struct_0 @ sk_C) = (u1_struct_0 @ sk_C))),
% 0.47/0.70      inference('demod', [status(thm)], ['67', '68'])).
% 0.47/0.70  thf('114', plain,
% 0.47/0.70      (![X5 : $i]:
% 0.47/0.70         (((k2_struct_0 @ X5) = (u1_struct_0 @ X5)) | ~ (l1_struct_0 @ X5))),
% 0.47/0.70      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.47/0.70  thf('115', plain,
% 0.47/0.70      (((g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) = (sk_D))),
% 0.47/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.70  thf('116', plain,
% 0.47/0.70      ((((g1_pre_topc @ (k2_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) = (sk_D))
% 0.47/0.70        | ~ (l1_struct_0 @ sk_C))),
% 0.47/0.70      inference('sup+', [status(thm)], ['114', '115'])).
% 0.47/0.70  thf('117', plain, ((l1_struct_0 @ sk_C)),
% 0.47/0.70      inference('sup-', [status(thm)], ['50', '51'])).
% 0.47/0.70  thf('118', plain,
% 0.47/0.70      (((g1_pre_topc @ (k2_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) = (sk_D))),
% 0.47/0.70      inference('demod', [status(thm)], ['116', '117'])).
% 0.47/0.70  thf('119', plain, (((k2_struct_0 @ sk_C) = (u1_struct_0 @ sk_C))),
% 0.47/0.70      inference('demod', [status(thm)], ['67', '68'])).
% 0.47/0.70  thf('120', plain,
% 0.47/0.70      (((g1_pre_topc @ (k2_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) = (sk_D))),
% 0.47/0.70      inference('demod', [status(thm)], ['116', '117'])).
% 0.47/0.70  thf('121', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.47/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.70  thf(cc1_pre_topc, axiom,
% 0.47/0.70    (![A:$i]:
% 0.47/0.70     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.47/0.70       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( v2_pre_topc @ B ) ) ) ))).
% 0.47/0.70  thf('122', plain,
% 0.47/0.70      (![X3 : $i, X4 : $i]:
% 0.47/0.70         (~ (m1_pre_topc @ X3 @ X4)
% 0.47/0.70          | (v2_pre_topc @ X3)
% 0.47/0.70          | ~ (l1_pre_topc @ X4)
% 0.47/0.70          | ~ (v2_pre_topc @ X4))),
% 0.47/0.70      inference('cnf', [status(esa)], [cc1_pre_topc])).
% 0.47/0.70  thf('123', plain,
% 0.47/0.70      ((~ (v2_pre_topc @ sk_A) | ~ (l1_pre_topc @ sk_A) | (v2_pre_topc @ sk_D))),
% 0.47/0.70      inference('sup-', [status(thm)], ['121', '122'])).
% 0.47/0.70  thf('124', plain, ((v2_pre_topc @ sk_A)),
% 0.47/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.70  thf('125', plain, ((l1_pre_topc @ sk_A)),
% 0.47/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.70  thf('126', plain, ((v2_pre_topc @ sk_D)),
% 0.47/0.70      inference('demod', [status(thm)], ['123', '124', '125'])).
% 0.47/0.70  thf('127', plain, (((k2_struct_0 @ sk_C) = (u1_struct_0 @ sk_C))),
% 0.47/0.70      inference('demod', [status(thm)], ['67', '68'])).
% 0.47/0.70  thf('128', plain,
% 0.47/0.70      (((g1_pre_topc @ (k2_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) = (sk_D))),
% 0.47/0.70      inference('demod', [status(thm)], ['116', '117'])).
% 0.47/0.70  thf('129', plain, ((l1_pre_topc @ sk_D)),
% 0.47/0.70      inference('demod', [status(thm)], ['12', '13'])).
% 0.47/0.70  thf('130', plain, (((k2_struct_0 @ sk_C) = (u1_struct_0 @ sk_C))),
% 0.47/0.70      inference('demod', [status(thm)], ['67', '68'])).
% 0.47/0.70  thf('131', plain,
% 0.47/0.70      (((g1_pre_topc @ (k2_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) = (sk_D))),
% 0.47/0.70      inference('demod', [status(thm)], ['116', '117'])).
% 0.47/0.70  thf('132', plain,
% 0.47/0.70      (((v2_struct_0 @ sk_D)
% 0.47/0.70        | ((k3_tmap_1 @ sk_D @ sk_B @ sk_C @ sk_C @ sk_E)
% 0.47/0.70            = (k2_partfun1 @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.47/0.70               sk_E @ (k2_struct_0 @ sk_C)))
% 0.47/0.70        | (v2_struct_0 @ sk_B))),
% 0.47/0.70      inference('demod', [status(thm)],
% 0.47/0.70                ['111', '112', '113', '118', '119', '120', '126', '127', 
% 0.47/0.70                 '128', '129', '130', '131'])).
% 0.47/0.70  thf('133', plain,
% 0.47/0.70      (![X0 : $i]:
% 0.47/0.70         ((m1_pre_topc @ X0 @ 
% 0.47/0.70           (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.47/0.70          | ~ (l1_pre_topc @ X0))),
% 0.47/0.70      inference('simplify', [status(thm)], ['5'])).
% 0.47/0.70  thf('134', plain,
% 0.47/0.70      (![X0 : $i]:
% 0.47/0.70         ((v2_struct_0 @ sk_B)
% 0.47/0.70          | ((k3_tmap_1 @ X0 @ sk_B @ sk_C @ sk_C @ sk_E)
% 0.47/0.70              = (k2_partfun1 @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.47/0.70                 sk_E @ (k2_struct_0 @ sk_C)))
% 0.47/0.70          | ~ (m1_pre_topc @ sk_C @ X0)
% 0.47/0.70          | ~ (l1_pre_topc @ X0)
% 0.47/0.70          | ~ (v2_pre_topc @ X0)
% 0.47/0.70          | (v2_struct_0 @ X0))),
% 0.47/0.70      inference('simplify', [status(thm)], ['109'])).
% 0.47/0.70  thf('135', plain,
% 0.47/0.70      (![X22 : $i]: ((m1_pre_topc @ X22 @ X22) | ~ (l1_pre_topc @ X22))),
% 0.47/0.70      inference('cnf', [status(esa)], [t2_tsep_1])).
% 0.47/0.70  thf('136', plain,
% 0.47/0.70      (![X0 : $i]:
% 0.47/0.70         ((v2_struct_0 @ sk_B)
% 0.47/0.70          | ((k3_tmap_1 @ X0 @ sk_B @ sk_C @ sk_C @ sk_E)
% 0.47/0.70              = (k2_partfun1 @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.47/0.70                 sk_E @ (k2_struct_0 @ sk_C)))
% 0.47/0.70          | ~ (m1_pre_topc @ sk_C @ X0)
% 0.47/0.70          | ~ (l1_pre_topc @ X0)
% 0.47/0.70          | ~ (v2_pre_topc @ X0)
% 0.47/0.70          | (v2_struct_0 @ X0))),
% 0.47/0.70      inference('simplify', [status(thm)], ['109'])).
% 0.47/0.70  thf('137', plain,
% 0.47/0.70      ((~ (l1_pre_topc @ sk_C)
% 0.47/0.70        | (v2_struct_0 @ sk_C)
% 0.47/0.70        | ~ (v2_pre_topc @ sk_C)
% 0.47/0.70        | ~ (l1_pre_topc @ sk_C)
% 0.47/0.70        | ((k3_tmap_1 @ sk_C @ sk_B @ sk_C @ sk_C @ sk_E)
% 0.47/0.70            = (k2_partfun1 @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.47/0.70               sk_E @ (k2_struct_0 @ sk_C)))
% 0.47/0.70        | (v2_struct_0 @ sk_B))),
% 0.47/0.70      inference('sup-', [status(thm)], ['135', '136'])).
% 0.47/0.70  thf('138', plain, ((l1_pre_topc @ sk_C)),
% 0.47/0.70      inference('demod', [status(thm)], ['18', '19'])).
% 0.47/0.70  thf('139', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.47/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.70  thf('140', plain,
% 0.47/0.70      (![X3 : $i, X4 : $i]:
% 0.47/0.70         (~ (m1_pre_topc @ X3 @ X4)
% 0.47/0.70          | (v2_pre_topc @ X3)
% 0.47/0.70          | ~ (l1_pre_topc @ X4)
% 0.47/0.70          | ~ (v2_pre_topc @ X4))),
% 0.47/0.70      inference('cnf', [status(esa)], [cc1_pre_topc])).
% 0.47/0.70  thf('141', plain,
% 0.47/0.70      ((~ (v2_pre_topc @ sk_A) | ~ (l1_pre_topc @ sk_A) | (v2_pre_topc @ sk_C))),
% 0.47/0.70      inference('sup-', [status(thm)], ['139', '140'])).
% 0.47/0.70  thf('142', plain, ((v2_pre_topc @ sk_A)),
% 0.47/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.70  thf('143', plain, ((l1_pre_topc @ sk_A)),
% 0.47/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.70  thf('144', plain, ((v2_pre_topc @ sk_C)),
% 0.47/0.70      inference('demod', [status(thm)], ['141', '142', '143'])).
% 0.47/0.70  thf('145', plain, ((l1_pre_topc @ sk_C)),
% 0.47/0.70      inference('demod', [status(thm)], ['18', '19'])).
% 0.47/0.70  thf('146', plain,
% 0.47/0.70      (((v2_struct_0 @ sk_C)
% 0.47/0.70        | ((k3_tmap_1 @ sk_C @ sk_B @ sk_C @ sk_C @ sk_E)
% 0.47/0.70            = (k2_partfun1 @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.47/0.70               sk_E @ (k2_struct_0 @ sk_C)))
% 0.47/0.70        | (v2_struct_0 @ sk_B))),
% 0.47/0.70      inference('demod', [status(thm)], ['137', '138', '144', '145'])).
% 0.47/0.70  thf('147', plain, (~ (v2_struct_0 @ sk_C)),
% 0.47/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.70  thf('148', plain,
% 0.47/0.70      (((v2_struct_0 @ sk_B)
% 0.47/0.70        | ((k3_tmap_1 @ sk_C @ sk_B @ sk_C @ sk_C @ sk_E)
% 0.47/0.70            = (k2_partfun1 @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.47/0.70               sk_E @ (k2_struct_0 @ sk_C))))),
% 0.47/0.70      inference('clc', [status(thm)], ['146', '147'])).
% 0.47/0.70  thf('149', plain, (~ (v2_struct_0 @ sk_B)),
% 0.47/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.70  thf('150', plain,
% 0.47/0.70      (((k3_tmap_1 @ sk_C @ sk_B @ sk_C @ sk_C @ sk_E)
% 0.47/0.70         = (k2_partfun1 @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_E @ 
% 0.47/0.70            (k2_struct_0 @ sk_C)))),
% 0.47/0.70      inference('clc', [status(thm)], ['148', '149'])).
% 0.47/0.70  thf('151', plain,
% 0.47/0.70      (![X0 : $i]:
% 0.47/0.70         ((v2_struct_0 @ sk_B)
% 0.47/0.70          | ((k3_tmap_1 @ X0 @ sk_B @ sk_C @ sk_C @ sk_E)
% 0.47/0.70              = (k3_tmap_1 @ sk_C @ sk_B @ sk_C @ sk_C @ sk_E))
% 0.47/0.70          | ~ (m1_pre_topc @ sk_C @ X0)
% 0.47/0.70          | ~ (l1_pre_topc @ X0)
% 0.47/0.70          | ~ (v2_pre_topc @ X0)
% 0.47/0.70          | (v2_struct_0 @ X0))),
% 0.47/0.70      inference('demod', [status(thm)], ['134', '150'])).
% 0.47/0.70  thf('152', plain,
% 0.47/0.70      ((~ (l1_pre_topc @ sk_C)
% 0.47/0.70        | (v2_struct_0 @ 
% 0.47/0.70           (g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)))
% 0.47/0.70        | ~ (v2_pre_topc @ 
% 0.47/0.70             (g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)))
% 0.47/0.70        | ~ (l1_pre_topc @ 
% 0.47/0.70             (g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)))
% 0.47/0.70        | ((k3_tmap_1 @ 
% 0.47/0.70            (g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) @ 
% 0.47/0.70            sk_B @ sk_C @ sk_C @ sk_E)
% 0.47/0.70            = (k3_tmap_1 @ sk_C @ sk_B @ sk_C @ sk_C @ sk_E))
% 0.47/0.70        | (v2_struct_0 @ sk_B))),
% 0.47/0.70      inference('sup-', [status(thm)], ['133', '151'])).
% 0.47/0.70  thf('153', plain, ((l1_pre_topc @ sk_C)),
% 0.47/0.70      inference('demod', [status(thm)], ['18', '19'])).
% 0.47/0.70  thf('154', plain, (((k2_struct_0 @ sk_C) = (u1_struct_0 @ sk_C))),
% 0.47/0.70      inference('demod', [status(thm)], ['67', '68'])).
% 0.47/0.70  thf('155', plain,
% 0.47/0.70      (((g1_pre_topc @ (k2_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) = (sk_D))),
% 0.47/0.70      inference('demod', [status(thm)], ['116', '117'])).
% 0.47/0.70  thf('156', plain, (((k2_struct_0 @ sk_C) = (u1_struct_0 @ sk_C))),
% 0.47/0.70      inference('demod', [status(thm)], ['67', '68'])).
% 0.47/0.70  thf('157', plain,
% 0.47/0.70      (((g1_pre_topc @ (k2_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) = (sk_D))),
% 0.47/0.70      inference('demod', [status(thm)], ['116', '117'])).
% 0.47/0.70  thf('158', plain, ((v2_pre_topc @ sk_D)),
% 0.47/0.70      inference('demod', [status(thm)], ['123', '124', '125'])).
% 0.47/0.70  thf('159', plain, (((k2_struct_0 @ sk_C) = (u1_struct_0 @ sk_C))),
% 0.47/0.70      inference('demod', [status(thm)], ['67', '68'])).
% 0.47/0.70  thf('160', plain,
% 0.47/0.70      (((g1_pre_topc @ (k2_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) = (sk_D))),
% 0.47/0.70      inference('demod', [status(thm)], ['116', '117'])).
% 0.47/0.70  thf('161', plain, ((l1_pre_topc @ sk_D)),
% 0.47/0.70      inference('demod', [status(thm)], ['12', '13'])).
% 0.47/0.70  thf('162', plain, (((k2_struct_0 @ sk_C) = (u1_struct_0 @ sk_C))),
% 0.47/0.70      inference('demod', [status(thm)], ['67', '68'])).
% 0.47/0.70  thf('163', plain,
% 0.47/0.70      (((g1_pre_topc @ (k2_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) = (sk_D))),
% 0.47/0.70      inference('demod', [status(thm)], ['116', '117'])).
% 0.47/0.70  thf('164', plain,
% 0.47/0.70      (((v2_struct_0 @ sk_D)
% 0.47/0.70        | ((k3_tmap_1 @ sk_D @ sk_B @ sk_C @ sk_C @ sk_E)
% 0.47/0.70            = (k3_tmap_1 @ sk_C @ sk_B @ sk_C @ sk_C @ sk_E))
% 0.47/0.70        | (v2_struct_0 @ sk_B))),
% 0.47/0.70      inference('demod', [status(thm)],
% 0.47/0.70                ['152', '153', '154', '155', '156', '157', '158', '159', 
% 0.47/0.70                 '160', '161', '162', '163'])).
% 0.47/0.70  thf('165', plain, (~ (v2_struct_0 @ sk_D)),
% 0.47/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.70  thf('166', plain,
% 0.47/0.70      (((v2_struct_0 @ sk_B)
% 0.47/0.70        | ((k3_tmap_1 @ sk_D @ sk_B @ sk_C @ sk_C @ sk_E)
% 0.47/0.70            = (k3_tmap_1 @ sk_C @ sk_B @ sk_C @ sk_C @ sk_E)))),
% 0.47/0.70      inference('clc', [status(thm)], ['164', '165'])).
% 0.47/0.70  thf('167', plain, (~ (v2_struct_0 @ sk_B)),
% 0.47/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.70  thf('168', plain,
% 0.47/0.70      (((k3_tmap_1 @ sk_D @ sk_B @ sk_C @ sk_C @ sk_E)
% 0.47/0.70         = (k3_tmap_1 @ sk_C @ sk_B @ sk_C @ sk_C @ sk_E))),
% 0.47/0.70      inference('clc', [status(thm)], ['166', '167'])).
% 0.47/0.70  thf('169', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.47/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.70  thf('170', plain,
% 0.47/0.70      (![X0 : $i]:
% 0.47/0.70         ((v2_struct_0 @ sk_B)
% 0.47/0.70          | ((k3_tmap_1 @ X0 @ sk_B @ sk_C @ sk_C @ sk_E)
% 0.47/0.70              = (k3_tmap_1 @ sk_C @ sk_B @ sk_C @ sk_C @ sk_E))
% 0.47/0.70          | ~ (m1_pre_topc @ sk_C @ X0)
% 0.47/0.70          | ~ (l1_pre_topc @ X0)
% 0.47/0.70          | ~ (v2_pre_topc @ X0)
% 0.47/0.70          | (v2_struct_0 @ X0))),
% 0.47/0.70      inference('demod', [status(thm)], ['134', '150'])).
% 0.47/0.70  thf('171', plain,
% 0.47/0.70      (((v2_struct_0 @ sk_A)
% 0.47/0.70        | ~ (v2_pre_topc @ sk_A)
% 0.47/0.70        | ~ (l1_pre_topc @ sk_A)
% 0.47/0.70        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_C @ sk_E)
% 0.47/0.70            = (k3_tmap_1 @ sk_C @ sk_B @ sk_C @ sk_C @ sk_E))
% 0.47/0.70        | (v2_struct_0 @ sk_B))),
% 0.47/0.70      inference('sup-', [status(thm)], ['169', '170'])).
% 0.47/0.70  thf('172', plain, ((v2_pre_topc @ sk_A)),
% 0.47/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.70  thf('173', plain, ((l1_pre_topc @ sk_A)),
% 0.47/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.70  thf('174', plain,
% 0.47/0.70      (((v2_struct_0 @ sk_A)
% 0.47/0.70        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_C @ sk_E)
% 0.47/0.70            = (k3_tmap_1 @ sk_C @ sk_B @ sk_C @ sk_C @ sk_E))
% 0.47/0.70        | (v2_struct_0 @ sk_B))),
% 0.47/0.70      inference('demod', [status(thm)], ['171', '172', '173'])).
% 0.47/0.70  thf('175', plain, (~ (v2_struct_0 @ sk_A)),
% 0.47/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.70  thf('176', plain,
% 0.47/0.70      (((v2_struct_0 @ sk_B)
% 0.47/0.70        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_C @ sk_E)
% 0.47/0.70            = (k3_tmap_1 @ sk_C @ sk_B @ sk_C @ sk_C @ sk_E)))),
% 0.47/0.70      inference('clc', [status(thm)], ['174', '175'])).
% 0.47/0.70  thf('177', plain, (~ (v2_struct_0 @ sk_B)),
% 0.47/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.70  thf('178', plain,
% 0.47/0.70      (((k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_C @ sk_E)
% 0.47/0.70         = (k3_tmap_1 @ sk_C @ sk_B @ sk_C @ sk_C @ sk_E))),
% 0.47/0.70      inference('clc', [status(thm)], ['176', '177'])).
% 0.47/0.70  thf('179', plain,
% 0.47/0.70      (((k3_tmap_1 @ sk_D @ sk_B @ sk_C @ sk_C @ sk_E)
% 0.47/0.70         = (k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_C @ sk_E))),
% 0.47/0.70      inference('demod', [status(thm)], ['168', '178'])).
% 0.47/0.70  thf('180', plain,
% 0.47/0.70      (![X5 : $i]:
% 0.47/0.70         (((k2_struct_0 @ X5) = (u1_struct_0 @ X5)) | ~ (l1_struct_0 @ X5))),
% 0.47/0.70      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.47/0.70  thf('181', plain,
% 0.47/0.70      (((k3_tmap_1 @ sk_C @ sk_B @ sk_C @ sk_C @ sk_E)
% 0.47/0.70         = (k2_partfun1 @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_E @ 
% 0.47/0.70            (k2_struct_0 @ sk_C)))),
% 0.47/0.70      inference('clc', [status(thm)], ['148', '149'])).
% 0.47/0.70  thf('182', plain,
% 0.47/0.70      (((k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_C @ sk_E)
% 0.47/0.70         = (k3_tmap_1 @ sk_C @ sk_B @ sk_C @ sk_C @ sk_E))),
% 0.47/0.70      inference('clc', [status(thm)], ['176', '177'])).
% 0.47/0.70  thf('183', plain,
% 0.47/0.70      (((k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_C @ sk_E)
% 0.47/0.70         = (k2_partfun1 @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_E @ 
% 0.47/0.70            (k2_struct_0 @ sk_C)))),
% 0.47/0.70      inference('demod', [status(thm)], ['181', '182'])).
% 0.47/0.70  thf('184', plain,
% 0.47/0.70      ((((k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_C @ sk_E)
% 0.47/0.70          = (k2_partfun1 @ (k2_struct_0 @ sk_C) @ (k2_struct_0 @ sk_B) @ 
% 0.47/0.70             sk_E @ (k2_struct_0 @ sk_C)))
% 0.47/0.70        | ~ (l1_struct_0 @ sk_B))),
% 0.47/0.70      inference('sup+', [status(thm)], ['180', '183'])).
% 0.47/0.70  thf('185', plain, ((l1_pre_topc @ sk_B)),
% 0.47/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.70  thf('186', plain, (![X6 : $i]: ((l1_struct_0 @ X6) | ~ (l1_pre_topc @ X6))),
% 0.47/0.70      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.47/0.70  thf('187', plain, ((l1_struct_0 @ sk_B)),
% 0.47/0.70      inference('sup-', [status(thm)], ['185', '186'])).
% 0.47/0.70  thf('188', plain,
% 0.47/0.70      (((k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_C @ sk_E)
% 0.47/0.70         = (k2_partfun1 @ (k2_struct_0 @ sk_C) @ (k2_struct_0 @ sk_B) @ sk_E @ 
% 0.47/0.70            (k2_struct_0 @ sk_C)))),
% 0.47/0.70      inference('demod', [status(thm)], ['184', '187'])).
% 0.47/0.70  thf('189', plain,
% 0.47/0.70      (((k3_tmap_1 @ sk_D @ sk_B @ sk_C @ sk_C @ sk_E)
% 0.47/0.70         = (k2_partfun1 @ (k2_struct_0 @ sk_C) @ (k2_struct_0 @ sk_B) @ sk_E @ 
% 0.47/0.70            (k2_struct_0 @ sk_C)))),
% 0.47/0.70      inference('demod', [status(thm)], ['179', '188'])).
% 0.47/0.70  thf('190', plain,
% 0.47/0.70      (((v2_struct_0 @ sk_D)
% 0.47/0.70        | ((k2_partfun1 @ (k2_struct_0 @ sk_C) @ (k2_struct_0 @ sk_B) @ sk_E @ 
% 0.47/0.70            (k2_struct_0 @ sk_C))
% 0.47/0.70            = (k2_partfun1 @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.47/0.70               sk_E @ (k2_struct_0 @ sk_C)))
% 0.47/0.70        | (v2_struct_0 @ sk_B))),
% 0.47/0.70      inference('demod', [status(thm)], ['132', '189'])).
% 0.47/0.70  thf('191', plain, (~ (v2_struct_0 @ sk_D)),
% 0.47/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.70  thf('192', plain,
% 0.47/0.70      (((v2_struct_0 @ sk_B)
% 0.47/0.70        | ((k2_partfun1 @ (k2_struct_0 @ sk_C) @ (k2_struct_0 @ sk_B) @ sk_E @ 
% 0.47/0.70            (k2_struct_0 @ sk_C))
% 0.47/0.70            = (k2_partfun1 @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.47/0.70               sk_E @ (k2_struct_0 @ sk_C))))),
% 0.47/0.70      inference('clc', [status(thm)], ['190', '191'])).
% 0.47/0.70  thf('193', plain, (~ (v2_struct_0 @ sk_B)),
% 0.47/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.70  thf('194', plain,
% 0.47/0.70      (((k2_partfun1 @ (k2_struct_0 @ sk_C) @ (k2_struct_0 @ sk_B) @ sk_E @ 
% 0.47/0.70         (k2_struct_0 @ sk_C))
% 0.47/0.70         = (k2_partfun1 @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_E @ 
% 0.47/0.70            (k2_struct_0 @ sk_C)))),
% 0.47/0.70      inference('clc', [status(thm)], ['192', '193'])).
% 0.47/0.70  thf('195', plain,
% 0.47/0.70      (![X0 : $i]:
% 0.47/0.70         ((v2_struct_0 @ X0)
% 0.47/0.70          | ~ (v2_pre_topc @ X0)
% 0.47/0.70          | ~ (l1_pre_topc @ X0)
% 0.47/0.70          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.47/0.70          | ((k3_tmap_1 @ X0 @ sk_B @ sk_D @ sk_C @ sk_E)
% 0.47/0.70              = (k2_partfun1 @ (k2_struct_0 @ sk_C) @ (k2_struct_0 @ sk_B) @ 
% 0.47/0.70                 sk_E @ (k2_struct_0 @ sk_C)))
% 0.47/0.70          | ~ (m1_pre_topc @ sk_C @ X0)
% 0.47/0.70          | (v2_struct_0 @ sk_B))),
% 0.47/0.70      inference('demod', [status(thm)], ['89', '90', '194'])).
% 0.47/0.70  thf('196', plain,
% 0.47/0.70      (((v2_struct_0 @ sk_B)
% 0.47/0.70        | ~ (m1_pre_topc @ sk_C @ sk_A)
% 0.47/0.70        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E)
% 0.47/0.70            = (k2_partfun1 @ (k2_struct_0 @ sk_C) @ (k2_struct_0 @ sk_B) @ 
% 0.47/0.70               sk_E @ (k2_struct_0 @ sk_C)))
% 0.47/0.70        | ~ (l1_pre_topc @ sk_A)
% 0.47/0.70        | ~ (v2_pre_topc @ sk_A)
% 0.47/0.70        | (v2_struct_0 @ sk_A))),
% 0.47/0.70      inference('sup-', [status(thm)], ['58', '195'])).
% 0.47/0.70  thf('197', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.47/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.70  thf('198', plain, ((l1_pre_topc @ sk_A)),
% 0.47/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.70  thf('199', plain, ((v2_pre_topc @ sk_A)),
% 0.47/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.70  thf('200', plain,
% 0.47/0.70      (((v2_struct_0 @ sk_B)
% 0.47/0.70        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E)
% 0.47/0.70            = (k2_partfun1 @ (k2_struct_0 @ sk_C) @ (k2_struct_0 @ sk_B) @ 
% 0.47/0.70               sk_E @ (k2_struct_0 @ sk_C)))
% 0.47/0.70        | (v2_struct_0 @ sk_A))),
% 0.47/0.70      inference('demod', [status(thm)], ['196', '197', '198', '199'])).
% 0.47/0.70  thf('201', plain, (~ (v2_struct_0 @ sk_B)),
% 0.47/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.70  thf('202', plain,
% 0.47/0.70      (((v2_struct_0 @ sk_A)
% 0.47/0.70        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E)
% 0.47/0.70            = (k2_partfun1 @ (k2_struct_0 @ sk_C) @ (k2_struct_0 @ sk_B) @ 
% 0.47/0.70               sk_E @ (k2_struct_0 @ sk_C))))),
% 0.47/0.70      inference('clc', [status(thm)], ['200', '201'])).
% 0.47/0.70  thf('203', plain, (~ (v2_struct_0 @ sk_A)),
% 0.47/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.70  thf('204', plain,
% 0.47/0.70      (((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E)
% 0.47/0.70         = (k2_partfun1 @ (k2_struct_0 @ sk_C) @ (k2_struct_0 @ sk_B) @ sk_E @ 
% 0.47/0.70            (k2_struct_0 @ sk_C)))),
% 0.47/0.70      inference('clc', [status(thm)], ['202', '203'])).
% 0.47/0.70  thf('205', plain,
% 0.47/0.70      ((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.47/0.70        (k2_partfun1 @ (k2_struct_0 @ sk_C) @ (k2_struct_0 @ sk_B) @ sk_E @ 
% 0.47/0.70         (k2_struct_0 @ sk_C)) @ 
% 0.47/0.70        sk_F)),
% 0.47/0.70      inference('demod', [status(thm)], ['57', '204'])).
% 0.47/0.70  thf('206', plain,
% 0.47/0.70      (![X5 : $i]:
% 0.47/0.70         (((k2_struct_0 @ X5) = (u1_struct_0 @ X5)) | ~ (l1_struct_0 @ X5))),
% 0.47/0.70      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.47/0.70  thf('207', plain,
% 0.47/0.70      (((k3_tmap_1 @ sk_C @ sk_B @ sk_C @ sk_C @ sk_E)
% 0.47/0.70         = (k2_partfun1 @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_E @ 
% 0.47/0.70            (k2_struct_0 @ sk_C)))),
% 0.47/0.70      inference('clc', [status(thm)], ['148', '149'])).
% 0.47/0.70  thf('208', plain,
% 0.47/0.70      ((((k3_tmap_1 @ sk_C @ sk_B @ sk_C @ sk_C @ sk_E)
% 0.47/0.70          = (k2_partfun1 @ (k2_struct_0 @ sk_C) @ (k2_struct_0 @ sk_B) @ 
% 0.47/0.70             sk_E @ (k2_struct_0 @ sk_C)))
% 0.47/0.70        | ~ (l1_struct_0 @ sk_B))),
% 0.47/0.70      inference('sup+', [status(thm)], ['206', '207'])).
% 0.47/0.70  thf('209', plain, ((l1_struct_0 @ sk_B)),
% 0.47/0.70      inference('sup-', [status(thm)], ['185', '186'])).
% 0.47/0.70  thf('210', plain,
% 0.47/0.70      (((k3_tmap_1 @ sk_C @ sk_B @ sk_C @ sk_C @ sk_E)
% 0.47/0.70         = (k2_partfun1 @ (k2_struct_0 @ sk_C) @ (k2_struct_0 @ sk_B) @ sk_E @ 
% 0.47/0.70            (k2_struct_0 @ sk_C)))),
% 0.47/0.70      inference('demod', [status(thm)], ['208', '209'])).
% 0.47/0.70  thf('211', plain,
% 0.47/0.70      ((m1_subset_1 @ sk_E @ 
% 0.47/0.70        (k1_zfmisc_1 @ 
% 0.47/0.70         (k2_zfmisc_1 @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 0.47/0.70      inference('demod', [status(thm)], ['66', '69'])).
% 0.47/0.70  thf('212', plain,
% 0.47/0.70      (![X5 : $i]:
% 0.47/0.70         (((k2_struct_0 @ X5) = (u1_struct_0 @ X5)) | ~ (l1_struct_0 @ X5))),
% 0.47/0.70      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.47/0.70  thf(t87_tmap_1, axiom,
% 0.47/0.70    (![A:$i]:
% 0.47/0.70     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.47/0.70       ( ![B:$i]:
% 0.47/0.70         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.47/0.70             ( l1_pre_topc @ B ) ) =>
% 0.47/0.70           ( ![C:$i]:
% 0.47/0.70             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ B ) ) =>
% 0.47/0.70               ( ![D:$i]:
% 0.47/0.70                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ B ) ) =>
% 0.47/0.70                   ( ![E:$i]:
% 0.47/0.70                     ( ( ( v1_funct_1 @ E ) & 
% 0.47/0.70                         ( v1_funct_2 @
% 0.47/0.70                           E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ A ) ) & 
% 0.47/0.70                         ( m1_subset_1 @
% 0.47/0.70                           E @ 
% 0.47/0.70                           ( k1_zfmisc_1 @
% 0.47/0.70                             ( k2_zfmisc_1 @
% 0.47/0.70                               ( u1_struct_0 @ D ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.47/0.70                       ( ( ( v1_tsep_1 @ C @ B ) & ( m1_pre_topc @ C @ B ) & 
% 0.47/0.70                           ( m1_pre_topc @ C @ D ) ) =>
% 0.47/0.70                         ( ![F:$i]:
% 0.47/0.70                           ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 0.47/0.70                             ( ![G:$i]:
% 0.47/0.70                               ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) ) =>
% 0.47/0.70                                 ( ( ( F ) = ( G ) ) =>
% 0.47/0.70                                   ( ( r1_tmap_1 @ D @ A @ E @ F ) <=>
% 0.47/0.70                                     ( r1_tmap_1 @
% 0.47/0.70                                       C @ A @ 
% 0.47/0.70                                       ( k3_tmap_1 @ B @ A @ D @ C @ E ) @ G ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.47/0.70  thf('213', plain,
% 0.47/0.70      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 0.47/0.70         ((v2_struct_0 @ X28)
% 0.47/0.70          | ~ (v2_pre_topc @ X28)
% 0.47/0.70          | ~ (l1_pre_topc @ X28)
% 0.47/0.70          | (v2_struct_0 @ X29)
% 0.47/0.70          | ~ (m1_pre_topc @ X29 @ X28)
% 0.47/0.70          | ~ (v1_tsep_1 @ X30 @ X28)
% 0.47/0.70          | ~ (m1_pre_topc @ X30 @ X28)
% 0.47/0.70          | ~ (m1_pre_topc @ X30 @ X29)
% 0.47/0.70          | ~ (m1_subset_1 @ X31 @ (u1_struct_0 @ X29))
% 0.47/0.70          | ((X31) != (X32))
% 0.47/0.70          | ~ (r1_tmap_1 @ X30 @ X33 @ 
% 0.47/0.70               (k3_tmap_1 @ X28 @ X33 @ X29 @ X30 @ X34) @ X32)
% 0.47/0.70          | (r1_tmap_1 @ X29 @ X33 @ X34 @ X31)
% 0.47/0.70          | ~ (m1_subset_1 @ X32 @ (u1_struct_0 @ X30))
% 0.47/0.70          | ~ (m1_subset_1 @ X34 @ 
% 0.47/0.70               (k1_zfmisc_1 @ 
% 0.47/0.70                (k2_zfmisc_1 @ (u1_struct_0 @ X29) @ (u1_struct_0 @ X33))))
% 0.47/0.70          | ~ (v1_funct_2 @ X34 @ (u1_struct_0 @ X29) @ (u1_struct_0 @ X33))
% 0.47/0.70          | ~ (v1_funct_1 @ X34)
% 0.47/0.70          | ~ (m1_pre_topc @ X30 @ X28)
% 0.47/0.70          | (v2_struct_0 @ X30)
% 0.47/0.70          | ~ (l1_pre_topc @ X33)
% 0.47/0.70          | ~ (v2_pre_topc @ X33)
% 0.47/0.70          | (v2_struct_0 @ X33))),
% 0.47/0.70      inference('cnf', [status(esa)], [t87_tmap_1])).
% 0.47/0.70  thf('214', plain,
% 0.47/0.70      (![X28 : $i, X29 : $i, X30 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 0.47/0.70         ((v2_struct_0 @ X33)
% 0.47/0.70          | ~ (v2_pre_topc @ X33)
% 0.47/0.70          | ~ (l1_pre_topc @ X33)
% 0.47/0.70          | (v2_struct_0 @ X30)
% 0.47/0.70          | ~ (v1_funct_1 @ X34)
% 0.47/0.70          | ~ (v1_funct_2 @ X34 @ (u1_struct_0 @ X29) @ (u1_struct_0 @ X33))
% 0.47/0.70          | ~ (m1_subset_1 @ X34 @ 
% 0.47/0.70               (k1_zfmisc_1 @ 
% 0.47/0.70                (k2_zfmisc_1 @ (u1_struct_0 @ X29) @ (u1_struct_0 @ X33))))
% 0.47/0.70          | ~ (m1_subset_1 @ X32 @ (u1_struct_0 @ X30))
% 0.47/0.70          | (r1_tmap_1 @ X29 @ X33 @ X34 @ X32)
% 0.47/0.70          | ~ (r1_tmap_1 @ X30 @ X33 @ 
% 0.47/0.70               (k3_tmap_1 @ X28 @ X33 @ X29 @ X30 @ X34) @ X32)
% 0.47/0.70          | ~ (m1_subset_1 @ X32 @ (u1_struct_0 @ X29))
% 0.47/0.70          | ~ (m1_pre_topc @ X30 @ X29)
% 0.47/0.70          | ~ (m1_pre_topc @ X30 @ X28)
% 0.47/0.70          | ~ (v1_tsep_1 @ X30 @ X28)
% 0.47/0.70          | ~ (m1_pre_topc @ X29 @ X28)
% 0.47/0.70          | (v2_struct_0 @ X29)
% 0.47/0.70          | ~ (l1_pre_topc @ X28)
% 0.47/0.70          | ~ (v2_pre_topc @ X28)
% 0.47/0.70          | (v2_struct_0 @ X28))),
% 0.47/0.70      inference('simplify', [status(thm)], ['213'])).
% 0.47/0.70  thf('215', plain,
% 0.47/0.70      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.47/0.70         (~ (m1_subset_1 @ X2 @ 
% 0.47/0.70             (k1_zfmisc_1 @ 
% 0.47/0.70              (k2_zfmisc_1 @ (k2_struct_0 @ X0) @ (u1_struct_0 @ X1))))
% 0.47/0.70          | ~ (l1_struct_0 @ X0)
% 0.47/0.70          | (v2_struct_0 @ X3)
% 0.47/0.70          | ~ (v2_pre_topc @ X3)
% 0.47/0.70          | ~ (l1_pre_topc @ X3)
% 0.47/0.70          | (v2_struct_0 @ X0)
% 0.47/0.70          | ~ (m1_pre_topc @ X0 @ X3)
% 0.47/0.70          | ~ (v1_tsep_1 @ X4 @ X3)
% 0.47/0.70          | ~ (m1_pre_topc @ X4 @ X3)
% 0.47/0.70          | ~ (m1_pre_topc @ X4 @ X0)
% 0.47/0.70          | ~ (m1_subset_1 @ X5 @ (u1_struct_0 @ X0))
% 0.47/0.70          | ~ (r1_tmap_1 @ X4 @ X1 @ (k3_tmap_1 @ X3 @ X1 @ X0 @ X4 @ X2) @ X5)
% 0.47/0.70          | (r1_tmap_1 @ X0 @ X1 @ X2 @ X5)
% 0.47/0.70          | ~ (m1_subset_1 @ X5 @ (u1_struct_0 @ X4))
% 0.47/0.70          | ~ (v1_funct_2 @ X2 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X1))
% 0.47/0.70          | ~ (v1_funct_1 @ X2)
% 0.47/0.70          | (v2_struct_0 @ X4)
% 0.47/0.70          | ~ (l1_pre_topc @ X1)
% 0.47/0.70          | ~ (v2_pre_topc @ X1)
% 0.47/0.70          | (v2_struct_0 @ X1))),
% 0.47/0.70      inference('sup-', [status(thm)], ['212', '214'])).
% 0.47/0.70  thf('216', plain,
% 0.47/0.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.47/0.70         ((v2_struct_0 @ sk_B)
% 0.47/0.70          | ~ (v2_pre_topc @ sk_B)
% 0.47/0.70          | ~ (l1_pre_topc @ sk_B)
% 0.47/0.70          | (v2_struct_0 @ X0)
% 0.47/0.70          | ~ (v1_funct_1 @ sk_E)
% 0.47/0.70          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))
% 0.47/0.70          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.47/0.70          | (r1_tmap_1 @ sk_C @ sk_B @ sk_E @ X1)
% 0.47/0.70          | ~ (r1_tmap_1 @ X0 @ sk_B @ 
% 0.47/0.70               (k3_tmap_1 @ X2 @ sk_B @ sk_C @ X0 @ sk_E) @ X1)
% 0.47/0.70          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_C))
% 0.47/0.70          | ~ (m1_pre_topc @ X0 @ sk_C)
% 0.47/0.70          | ~ (m1_pre_topc @ X0 @ X2)
% 0.47/0.70          | ~ (v1_tsep_1 @ X0 @ X2)
% 0.47/0.70          | ~ (m1_pre_topc @ sk_C @ X2)
% 0.47/0.70          | (v2_struct_0 @ sk_C)
% 0.47/0.70          | ~ (l1_pre_topc @ X2)
% 0.47/0.70          | ~ (v2_pre_topc @ X2)
% 0.47/0.70          | (v2_struct_0 @ X2)
% 0.47/0.70          | ~ (l1_struct_0 @ sk_C))),
% 0.47/0.70      inference('sup-', [status(thm)], ['211', '215'])).
% 0.47/0.70  thf('217', plain, ((v2_pre_topc @ sk_B)),
% 0.47/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.70  thf('218', plain, ((l1_pre_topc @ sk_B)),
% 0.47/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.70  thf('219', plain, ((v1_funct_1 @ sk_E)),
% 0.47/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.70  thf('220', plain, (((k2_struct_0 @ sk_C) = (u1_struct_0 @ sk_C))),
% 0.47/0.70      inference('demod', [status(thm)], ['67', '68'])).
% 0.47/0.70  thf('221', plain,
% 0.47/0.70      ((v1_funct_2 @ sk_E @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 0.47/0.70      inference('demod', [status(thm)], ['84', '85'])).
% 0.47/0.70  thf('222', plain, (((k2_struct_0 @ sk_C) = (u1_struct_0 @ sk_C))),
% 0.47/0.70      inference('demod', [status(thm)], ['67', '68'])).
% 0.47/0.70  thf('223', plain, ((l1_struct_0 @ sk_C)),
% 0.47/0.70      inference('sup-', [status(thm)], ['50', '51'])).
% 0.47/0.70  thf('224', plain,
% 0.47/0.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.47/0.70         ((v2_struct_0 @ sk_B)
% 0.47/0.70          | (v2_struct_0 @ X0)
% 0.47/0.70          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.47/0.70          | (r1_tmap_1 @ sk_C @ sk_B @ sk_E @ X1)
% 0.47/0.70          | ~ (r1_tmap_1 @ X0 @ sk_B @ 
% 0.47/0.70               (k3_tmap_1 @ X2 @ sk_B @ sk_C @ X0 @ sk_E) @ X1)
% 0.47/0.70          | ~ (m1_subset_1 @ X1 @ (k2_struct_0 @ sk_C))
% 0.47/0.70          | ~ (m1_pre_topc @ X0 @ sk_C)
% 0.47/0.70          | ~ (m1_pre_topc @ X0 @ X2)
% 0.47/0.70          | ~ (v1_tsep_1 @ X0 @ X2)
% 0.47/0.70          | ~ (m1_pre_topc @ sk_C @ X2)
% 0.47/0.70          | (v2_struct_0 @ sk_C)
% 0.47/0.70          | ~ (l1_pre_topc @ X2)
% 0.47/0.70          | ~ (v2_pre_topc @ X2)
% 0.47/0.70          | (v2_struct_0 @ X2))),
% 0.47/0.70      inference('demod', [status(thm)],
% 0.47/0.70                ['216', '217', '218', '219', '220', '221', '222', '223'])).
% 0.47/0.70  thf('225', plain,
% 0.47/0.70      (![X0 : $i]:
% 0.47/0.70         (~ (r1_tmap_1 @ sk_C @ sk_B @ 
% 0.47/0.70             (k2_partfun1 @ (k2_struct_0 @ sk_C) @ (k2_struct_0 @ sk_B) @ 
% 0.47/0.70              sk_E @ (k2_struct_0 @ sk_C)) @ 
% 0.47/0.70             X0)
% 0.47/0.70          | (v2_struct_0 @ sk_C)
% 0.47/0.70          | ~ (v2_pre_topc @ sk_C)
% 0.47/0.70          | ~ (l1_pre_topc @ sk_C)
% 0.47/0.70          | (v2_struct_0 @ sk_C)
% 0.47/0.70          | ~ (m1_pre_topc @ sk_C @ sk_C)
% 0.47/0.70          | ~ (v1_tsep_1 @ sk_C @ sk_C)
% 0.47/0.70          | ~ (m1_pre_topc @ sk_C @ sk_C)
% 0.47/0.70          | ~ (m1_pre_topc @ sk_C @ sk_C)
% 0.47/0.70          | ~ (m1_subset_1 @ X0 @ (k2_struct_0 @ sk_C))
% 0.47/0.70          | (r1_tmap_1 @ sk_C @ sk_B @ sk_E @ X0)
% 0.47/0.70          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_C))
% 0.47/0.70          | (v2_struct_0 @ sk_C)
% 0.47/0.70          | (v2_struct_0 @ sk_B))),
% 0.47/0.70      inference('sup-', [status(thm)], ['210', '224'])).
% 0.47/0.70  thf('226', plain, ((v2_pre_topc @ sk_C)),
% 0.47/0.70      inference('demod', [status(thm)], ['141', '142', '143'])).
% 0.47/0.70  thf('227', plain, ((l1_pre_topc @ sk_C)),
% 0.47/0.70      inference('demod', [status(thm)], ['18', '19'])).
% 0.47/0.70  thf('228', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 0.47/0.70      inference('demod', [status(thm)], ['61', '62'])).
% 0.47/0.70  thf('229', plain,
% 0.47/0.70      (((g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) = (sk_D))),
% 0.47/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.70  thf('230', plain,
% 0.47/0.70      (![X9 : $i, X10 : $i]:
% 0.47/0.70         (~ (l1_pre_topc @ X9)
% 0.47/0.70          | ~ (m1_pre_topc @ X10 @ 
% 0.47/0.70               (g1_pre_topc @ (u1_struct_0 @ X9) @ (u1_pre_topc @ X9)))
% 0.47/0.70          | (m1_pre_topc @ X10 @ X9)
% 0.47/0.70          | ~ (l1_pre_topc @ X10))),
% 0.47/0.70      inference('cnf', [status(esa)], [t65_pre_topc])).
% 0.47/0.70  thf('231', plain,
% 0.47/0.70      (![X0 : $i]:
% 0.47/0.70         (~ (m1_pre_topc @ X0 @ sk_D)
% 0.47/0.70          | ~ (l1_pre_topc @ X0)
% 0.47/0.70          | (m1_pre_topc @ X0 @ sk_C)
% 0.47/0.70          | ~ (l1_pre_topc @ sk_C))),
% 0.47/0.70      inference('sup-', [status(thm)], ['229', '230'])).
% 0.47/0.70  thf('232', plain, ((l1_pre_topc @ sk_C)),
% 0.47/0.70      inference('demod', [status(thm)], ['18', '19'])).
% 0.47/0.70  thf('233', plain,
% 0.47/0.70      (![X0 : $i]:
% 0.47/0.70         (~ (m1_pre_topc @ X0 @ sk_D)
% 0.47/0.70          | ~ (l1_pre_topc @ X0)
% 0.47/0.70          | (m1_pre_topc @ X0 @ sk_C))),
% 0.47/0.70      inference('demod', [status(thm)], ['231', '232'])).
% 0.47/0.70  thf('234', plain, (((m1_pre_topc @ sk_C @ sk_C) | ~ (l1_pre_topc @ sk_C))),
% 0.47/0.70      inference('sup-', [status(thm)], ['228', '233'])).
% 0.47/0.70  thf('235', plain, ((l1_pre_topc @ sk_C)),
% 0.47/0.70      inference('demod', [status(thm)], ['18', '19'])).
% 0.47/0.70  thf('236', plain, ((m1_pre_topc @ sk_C @ sk_C)),
% 0.47/0.70      inference('demod', [status(thm)], ['234', '235'])).
% 0.47/0.70  thf(fc10_tops_1, axiom,
% 0.47/0.70    (![A:$i]:
% 0.47/0.70     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.47/0.70       ( v3_pre_topc @ ( k2_struct_0 @ A ) @ A ) ))).
% 0.47/0.70  thf('237', plain,
% 0.47/0.70      (![X11 : $i]:
% 0.47/0.70         ((v3_pre_topc @ (k2_struct_0 @ X11) @ X11)
% 0.47/0.70          | ~ (l1_pre_topc @ X11)
% 0.47/0.70          | ~ (v2_pre_topc @ X11))),
% 0.47/0.70      inference('cnf', [status(esa)], [fc10_tops_1])).
% 0.47/0.70  thf('238', plain, (((k2_struct_0 @ sk_C) = (u1_struct_0 @ sk_C))),
% 0.47/0.70      inference('demod', [status(thm)], ['67', '68'])).
% 0.47/0.70  thf('239', plain,
% 0.47/0.70      (![X22 : $i]: ((m1_pre_topc @ X22 @ X22) | ~ (l1_pre_topc @ X22))),
% 0.47/0.70      inference('cnf', [status(esa)], [t2_tsep_1])).
% 0.47/0.70  thf(t1_tsep_1, axiom,
% 0.47/0.70    (![A:$i]:
% 0.47/0.70     ( ( l1_pre_topc @ A ) =>
% 0.47/0.70       ( ![B:$i]:
% 0.47/0.70         ( ( m1_pre_topc @ B @ A ) =>
% 0.47/0.70           ( m1_subset_1 @
% 0.47/0.70             ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.47/0.70  thf('240', plain,
% 0.47/0.70      (![X20 : $i, X21 : $i]:
% 0.47/0.70         (~ (m1_pre_topc @ X20 @ X21)
% 0.47/0.70          | (m1_subset_1 @ (u1_struct_0 @ X20) @ 
% 0.47/0.70             (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.47/0.70          | ~ (l1_pre_topc @ X21))),
% 0.47/0.70      inference('cnf', [status(esa)], [t1_tsep_1])).
% 0.47/0.70  thf('241', plain,
% 0.47/0.70      (![X0 : $i]:
% 0.47/0.70         (~ (l1_pre_topc @ X0)
% 0.47/0.70          | ~ (l1_pre_topc @ X0)
% 0.47/0.70          | (m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 0.47/0.70             (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.47/0.70      inference('sup-', [status(thm)], ['239', '240'])).
% 0.47/0.70  thf('242', plain,
% 0.47/0.70      (![X0 : $i]:
% 0.47/0.70         ((m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 0.47/0.70           (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.47/0.70          | ~ (l1_pre_topc @ X0))),
% 0.47/0.70      inference('simplify', [status(thm)], ['241'])).
% 0.47/0.70  thf(t16_tsep_1, axiom,
% 0.47/0.70    (![A:$i]:
% 0.47/0.70     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.47/0.70       ( ![B:$i]:
% 0.47/0.70         ( ( m1_pre_topc @ B @ A ) =>
% 0.47/0.70           ( ![C:$i]:
% 0.47/0.70             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.47/0.70               ( ( ( C ) = ( u1_struct_0 @ B ) ) =>
% 0.47/0.70                 ( ( ( v1_tsep_1 @ B @ A ) & ( m1_pre_topc @ B @ A ) ) <=>
% 0.47/0.70                   ( v3_pre_topc @ C @ A ) ) ) ) ) ) ) ))).
% 0.47/0.70  thf('243', plain,
% 0.47/0.70      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.47/0.70         (~ (m1_pre_topc @ X17 @ X18)
% 0.47/0.70          | ((X19) != (u1_struct_0 @ X17))
% 0.47/0.70          | ~ (v3_pre_topc @ X19 @ X18)
% 0.47/0.70          | (v1_tsep_1 @ X17 @ X18)
% 0.47/0.70          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.47/0.70          | ~ (l1_pre_topc @ X18)
% 0.47/0.70          | ~ (v2_pre_topc @ X18))),
% 0.47/0.70      inference('cnf', [status(esa)], [t16_tsep_1])).
% 0.47/0.70  thf('244', plain,
% 0.47/0.70      (![X17 : $i, X18 : $i]:
% 0.47/0.70         (~ (v2_pre_topc @ X18)
% 0.47/0.70          | ~ (l1_pre_topc @ X18)
% 0.47/0.70          | ~ (m1_subset_1 @ (u1_struct_0 @ X17) @ 
% 0.47/0.70               (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.47/0.70          | (v1_tsep_1 @ X17 @ X18)
% 0.47/0.70          | ~ (v3_pre_topc @ (u1_struct_0 @ X17) @ X18)
% 0.47/0.70          | ~ (m1_pre_topc @ X17 @ X18))),
% 0.47/0.70      inference('simplify', [status(thm)], ['243'])).
% 0.47/0.70  thf('245', plain,
% 0.47/0.70      (![X0 : $i]:
% 0.47/0.70         (~ (l1_pre_topc @ X0)
% 0.47/0.70          | ~ (m1_pre_topc @ X0 @ X0)
% 0.47/0.70          | ~ (v3_pre_topc @ (u1_struct_0 @ X0) @ X0)
% 0.47/0.70          | (v1_tsep_1 @ X0 @ X0)
% 0.47/0.70          | ~ (l1_pre_topc @ X0)
% 0.47/0.70          | ~ (v2_pre_topc @ X0))),
% 0.47/0.70      inference('sup-', [status(thm)], ['242', '244'])).
% 0.47/0.70  thf('246', plain,
% 0.47/0.70      (![X0 : $i]:
% 0.47/0.70         (~ (v2_pre_topc @ X0)
% 0.47/0.70          | (v1_tsep_1 @ X0 @ X0)
% 0.47/0.70          | ~ (v3_pre_topc @ (u1_struct_0 @ X0) @ X0)
% 0.47/0.70          | ~ (m1_pre_topc @ X0 @ X0)
% 0.47/0.70          | ~ (l1_pre_topc @ X0))),
% 0.47/0.70      inference('simplify', [status(thm)], ['245'])).
% 0.47/0.70  thf('247', plain,
% 0.47/0.70      ((~ (v3_pre_topc @ (k2_struct_0 @ sk_C) @ sk_C)
% 0.47/0.70        | ~ (l1_pre_topc @ sk_C)
% 0.47/0.70        | ~ (m1_pre_topc @ sk_C @ sk_C)
% 0.47/0.70        | (v1_tsep_1 @ sk_C @ sk_C)
% 0.47/0.70        | ~ (v2_pre_topc @ sk_C))),
% 0.47/0.70      inference('sup-', [status(thm)], ['238', '246'])).
% 0.47/0.70  thf('248', plain, ((l1_pre_topc @ sk_C)),
% 0.47/0.70      inference('demod', [status(thm)], ['18', '19'])).
% 0.47/0.70  thf('249', plain, ((m1_pre_topc @ sk_C @ sk_C)),
% 0.47/0.70      inference('demod', [status(thm)], ['234', '235'])).
% 0.47/0.70  thf('250', plain, ((v2_pre_topc @ sk_C)),
% 0.47/0.70      inference('demod', [status(thm)], ['141', '142', '143'])).
% 0.47/0.70  thf('251', plain,
% 0.47/0.70      ((~ (v3_pre_topc @ (k2_struct_0 @ sk_C) @ sk_C)
% 0.47/0.70        | (v1_tsep_1 @ sk_C @ sk_C))),
% 0.47/0.70      inference('demod', [status(thm)], ['247', '248', '249', '250'])).
% 0.47/0.70  thf('252', plain,
% 0.47/0.70      ((~ (v2_pre_topc @ sk_C)
% 0.47/0.70        | ~ (l1_pre_topc @ sk_C)
% 0.47/0.70        | (v1_tsep_1 @ sk_C @ sk_C))),
% 0.47/0.70      inference('sup-', [status(thm)], ['237', '251'])).
% 0.47/0.70  thf('253', plain, ((v2_pre_topc @ sk_C)),
% 0.47/0.70      inference('demod', [status(thm)], ['141', '142', '143'])).
% 0.47/0.70  thf('254', plain, ((l1_pre_topc @ sk_C)),
% 0.47/0.70      inference('demod', [status(thm)], ['18', '19'])).
% 0.47/0.70  thf('255', plain, ((v1_tsep_1 @ sk_C @ sk_C)),
% 0.47/0.70      inference('demod', [status(thm)], ['252', '253', '254'])).
% 0.47/0.70  thf('256', plain, ((m1_pre_topc @ sk_C @ sk_C)),
% 0.47/0.70      inference('demod', [status(thm)], ['234', '235'])).
% 0.47/0.70  thf('257', plain, ((m1_pre_topc @ sk_C @ sk_C)),
% 0.47/0.70      inference('demod', [status(thm)], ['234', '235'])).
% 0.47/0.70  thf('258', plain, (((k2_struct_0 @ sk_C) = (u1_struct_0 @ sk_C))),
% 0.47/0.70      inference('demod', [status(thm)], ['67', '68'])).
% 0.47/0.70  thf('259', plain,
% 0.47/0.70      (![X0 : $i]:
% 0.47/0.70         (~ (r1_tmap_1 @ sk_C @ sk_B @ 
% 0.47/0.70             (k2_partfun1 @ (k2_struct_0 @ sk_C) @ (k2_struct_0 @ sk_B) @ 
% 0.47/0.70              sk_E @ (k2_struct_0 @ sk_C)) @ 
% 0.47/0.70             X0)
% 0.47/0.70          | (v2_struct_0 @ sk_C)
% 0.47/0.70          | (v2_struct_0 @ sk_C)
% 0.47/0.70          | ~ (m1_subset_1 @ X0 @ (k2_struct_0 @ sk_C))
% 0.47/0.70          | (r1_tmap_1 @ sk_C @ sk_B @ sk_E @ X0)
% 0.47/0.70          | ~ (m1_subset_1 @ X0 @ (k2_struct_0 @ sk_C))
% 0.47/0.70          | (v2_struct_0 @ sk_C)
% 0.47/0.70          | (v2_struct_0 @ sk_B))),
% 0.47/0.70      inference('demod', [status(thm)],
% 0.47/0.70                ['225', '226', '227', '236', '255', '256', '257', '258'])).
% 0.47/0.70  thf('260', plain,
% 0.47/0.70      (![X0 : $i]:
% 0.47/0.70         ((v2_struct_0 @ sk_B)
% 0.47/0.70          | (r1_tmap_1 @ sk_C @ sk_B @ sk_E @ X0)
% 0.47/0.70          | ~ (m1_subset_1 @ X0 @ (k2_struct_0 @ sk_C))
% 0.47/0.70          | (v2_struct_0 @ sk_C)
% 0.47/0.70          | ~ (r1_tmap_1 @ sk_C @ sk_B @ 
% 0.47/0.70               (k2_partfun1 @ (k2_struct_0 @ sk_C) @ (k2_struct_0 @ sk_B) @ 
% 0.47/0.70                sk_E @ (k2_struct_0 @ sk_C)) @ 
% 0.47/0.70               X0))),
% 0.47/0.70      inference('simplify', [status(thm)], ['259'])).
% 0.47/0.70  thf('261', plain,
% 0.47/0.70      (((v2_struct_0 @ sk_C)
% 0.47/0.70        | ~ (m1_subset_1 @ sk_F @ (k2_struct_0 @ sk_C))
% 0.47/0.70        | (r1_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_F)
% 0.47/0.70        | (v2_struct_0 @ sk_B))),
% 0.47/0.70      inference('sup-', [status(thm)], ['205', '260'])).
% 0.47/0.70  thf('262', plain,
% 0.47/0.70      (![X5 : $i]:
% 0.47/0.70         (((k2_struct_0 @ X5) = (u1_struct_0 @ X5)) | ~ (l1_struct_0 @ X5))),
% 0.47/0.70      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.47/0.70  thf('263', plain, ((m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_C))),
% 0.47/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.70  thf('264', plain, (((sk_F) = (sk_G))),
% 0.47/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.70  thf('265', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C))),
% 0.47/0.70      inference('demod', [status(thm)], ['263', '264'])).
% 0.47/0.70  thf('266', plain,
% 0.47/0.70      (((m1_subset_1 @ sk_F @ (k2_struct_0 @ sk_C)) | ~ (l1_struct_0 @ sk_C))),
% 0.47/0.70      inference('sup+', [status(thm)], ['262', '265'])).
% 0.47/0.70  thf('267', plain, ((l1_struct_0 @ sk_C)),
% 0.47/0.70      inference('sup-', [status(thm)], ['50', '51'])).
% 0.47/0.70  thf('268', plain, ((m1_subset_1 @ sk_F @ (k2_struct_0 @ sk_C))),
% 0.47/0.70      inference('demod', [status(thm)], ['266', '267'])).
% 0.47/0.70  thf('269', plain,
% 0.47/0.70      (((v2_struct_0 @ sk_C)
% 0.47/0.70        | (r1_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_F)
% 0.47/0.70        | (v2_struct_0 @ sk_B))),
% 0.47/0.70      inference('demod', [status(thm)], ['261', '268'])).
% 0.47/0.70  thf('270', plain, (~ (v2_struct_0 @ sk_C)),
% 0.47/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.70  thf('271', plain,
% 0.47/0.70      (((v2_struct_0 @ sk_B) | (r1_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_F))),
% 0.47/0.70      inference('clc', [status(thm)], ['269', '270'])).
% 0.47/0.70  thf('272', plain, (~ (v2_struct_0 @ sk_B)),
% 0.47/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.70  thf('273', plain, ((r1_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_F)),
% 0.47/0.70      inference('clc', [status(thm)], ['271', '272'])).
% 0.47/0.70  thf('274', plain,
% 0.47/0.70      ((m1_subset_1 @ sk_E @ 
% 0.47/0.70        (k1_zfmisc_1 @ 
% 0.47/0.70         (k2_zfmisc_1 @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 0.47/0.70      inference('demod', [status(thm)], ['66', '69'])).
% 0.47/0.70  thf('275', plain,
% 0.47/0.70      (![X5 : $i]:
% 0.47/0.70         (((k2_struct_0 @ X5) = (u1_struct_0 @ X5)) | ~ (l1_struct_0 @ X5))),
% 0.47/0.70      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.47/0.70  thf('276', plain,
% 0.47/0.70      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 0.47/0.70         ((v2_struct_0 @ X28)
% 0.47/0.70          | ~ (v2_pre_topc @ X28)
% 0.47/0.70          | ~ (l1_pre_topc @ X28)
% 0.47/0.70          | (v2_struct_0 @ X29)
% 0.47/0.70          | ~ (m1_pre_topc @ X29 @ X28)
% 0.47/0.70          | ~ (v1_tsep_1 @ X30 @ X28)
% 0.47/0.70          | ~ (m1_pre_topc @ X30 @ X28)
% 0.47/0.70          | ~ (m1_pre_topc @ X30 @ X29)
% 0.47/0.70          | ~ (m1_subset_1 @ X31 @ (u1_struct_0 @ X29))
% 0.47/0.70          | ((X31) != (X32))
% 0.47/0.70          | ~ (r1_tmap_1 @ X29 @ X33 @ X34 @ X31)
% 0.47/0.70          | (r1_tmap_1 @ X30 @ X33 @ 
% 0.47/0.70             (k3_tmap_1 @ X28 @ X33 @ X29 @ X30 @ X34) @ X32)
% 0.47/0.70          | ~ (m1_subset_1 @ X32 @ (u1_struct_0 @ X30))
% 0.47/0.70          | ~ (m1_subset_1 @ X34 @ 
% 0.47/0.70               (k1_zfmisc_1 @ 
% 0.47/0.70                (k2_zfmisc_1 @ (u1_struct_0 @ X29) @ (u1_struct_0 @ X33))))
% 0.47/0.70          | ~ (v1_funct_2 @ X34 @ (u1_struct_0 @ X29) @ (u1_struct_0 @ X33))
% 0.47/0.70          | ~ (v1_funct_1 @ X34)
% 0.47/0.70          | ~ (m1_pre_topc @ X30 @ X28)
% 0.47/0.70          | (v2_struct_0 @ X30)
% 0.47/0.70          | ~ (l1_pre_topc @ X33)
% 0.47/0.70          | ~ (v2_pre_topc @ X33)
% 0.47/0.70          | (v2_struct_0 @ X33))),
% 0.47/0.70      inference('cnf', [status(esa)], [t87_tmap_1])).
% 0.47/0.70  thf('277', plain,
% 0.47/0.70      (![X28 : $i, X29 : $i, X30 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 0.47/0.70         ((v2_struct_0 @ X33)
% 0.47/0.70          | ~ (v2_pre_topc @ X33)
% 0.47/0.70          | ~ (l1_pre_topc @ X33)
% 0.47/0.70          | (v2_struct_0 @ X30)
% 0.47/0.70          | ~ (v1_funct_1 @ X34)
% 0.47/0.70          | ~ (v1_funct_2 @ X34 @ (u1_struct_0 @ X29) @ (u1_struct_0 @ X33))
% 0.47/0.70          | ~ (m1_subset_1 @ X34 @ 
% 0.47/0.70               (k1_zfmisc_1 @ 
% 0.47/0.70                (k2_zfmisc_1 @ (u1_struct_0 @ X29) @ (u1_struct_0 @ X33))))
% 0.47/0.70          | ~ (m1_subset_1 @ X32 @ (u1_struct_0 @ X30))
% 0.47/0.70          | (r1_tmap_1 @ X30 @ X33 @ 
% 0.47/0.70             (k3_tmap_1 @ X28 @ X33 @ X29 @ X30 @ X34) @ X32)
% 0.47/0.70          | ~ (r1_tmap_1 @ X29 @ X33 @ X34 @ X32)
% 0.47/0.70          | ~ (m1_subset_1 @ X32 @ (u1_struct_0 @ X29))
% 0.47/0.70          | ~ (m1_pre_topc @ X30 @ X29)
% 0.47/0.70          | ~ (m1_pre_topc @ X30 @ X28)
% 0.47/0.70          | ~ (v1_tsep_1 @ X30 @ X28)
% 0.47/0.70          | ~ (m1_pre_topc @ X29 @ X28)
% 0.47/0.70          | (v2_struct_0 @ X29)
% 0.47/0.70          | ~ (l1_pre_topc @ X28)
% 0.47/0.70          | ~ (v2_pre_topc @ X28)
% 0.47/0.70          | (v2_struct_0 @ X28))),
% 0.47/0.70      inference('simplify', [status(thm)], ['276'])).
% 0.47/0.70  thf('278', plain,
% 0.47/0.70      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.47/0.70         (~ (m1_subset_1 @ X2 @ 
% 0.47/0.70             (k1_zfmisc_1 @ 
% 0.47/0.70              (k2_zfmisc_1 @ (k2_struct_0 @ X0) @ (u1_struct_0 @ X1))))
% 0.47/0.70          | ~ (l1_struct_0 @ X0)
% 0.47/0.70          | (v2_struct_0 @ X3)
% 0.47/0.70          | ~ (v2_pre_topc @ X3)
% 0.47/0.70          | ~ (l1_pre_topc @ X3)
% 0.47/0.70          | (v2_struct_0 @ X0)
% 0.47/0.70          | ~ (m1_pre_topc @ X0 @ X3)
% 0.47/0.70          | ~ (v1_tsep_1 @ X4 @ X3)
% 0.47/0.70          | ~ (m1_pre_topc @ X4 @ X3)
% 0.47/0.70          | ~ (m1_pre_topc @ X4 @ X0)
% 0.47/0.70          | ~ (m1_subset_1 @ X5 @ (u1_struct_0 @ X0))
% 0.47/0.70          | ~ (r1_tmap_1 @ X0 @ X1 @ X2 @ X5)
% 0.47/0.70          | (r1_tmap_1 @ X4 @ X1 @ (k3_tmap_1 @ X3 @ X1 @ X0 @ X4 @ X2) @ X5)
% 0.47/0.70          | ~ (m1_subset_1 @ X5 @ (u1_struct_0 @ X4))
% 0.47/0.70          | ~ (v1_funct_2 @ X2 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X1))
% 0.47/0.70          | ~ (v1_funct_1 @ X2)
% 0.47/0.70          | (v2_struct_0 @ X4)
% 0.47/0.70          | ~ (l1_pre_topc @ X1)
% 0.47/0.70          | ~ (v2_pre_topc @ X1)
% 0.47/0.70          | (v2_struct_0 @ X1))),
% 0.47/0.70      inference('sup-', [status(thm)], ['275', '277'])).
% 0.47/0.70  thf('279', plain,
% 0.47/0.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.47/0.70         ((v2_struct_0 @ sk_B)
% 0.47/0.70          | ~ (v2_pre_topc @ sk_B)
% 0.47/0.70          | ~ (l1_pre_topc @ sk_B)
% 0.47/0.70          | (v2_struct_0 @ X0)
% 0.47/0.70          | ~ (v1_funct_1 @ sk_E)
% 0.47/0.70          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))
% 0.47/0.70          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.47/0.70          | (r1_tmap_1 @ X0 @ sk_B @ 
% 0.47/0.70             (k3_tmap_1 @ X2 @ sk_B @ sk_C @ X0 @ sk_E) @ X1)
% 0.47/0.70          | ~ (r1_tmap_1 @ sk_C @ sk_B @ sk_E @ X1)
% 0.47/0.70          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_C))
% 0.47/0.70          | ~ (m1_pre_topc @ X0 @ sk_C)
% 0.47/0.70          | ~ (m1_pre_topc @ X0 @ X2)
% 0.47/0.70          | ~ (v1_tsep_1 @ X0 @ X2)
% 0.47/0.70          | ~ (m1_pre_topc @ sk_C @ X2)
% 0.47/0.70          | (v2_struct_0 @ sk_C)
% 0.47/0.70          | ~ (l1_pre_topc @ X2)
% 0.47/0.70          | ~ (v2_pre_topc @ X2)
% 0.47/0.70          | (v2_struct_0 @ X2)
% 0.47/0.70          | ~ (l1_struct_0 @ sk_C))),
% 0.47/0.70      inference('sup-', [status(thm)], ['274', '278'])).
% 0.47/0.70  thf('280', plain, ((v2_pre_topc @ sk_B)),
% 0.47/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.70  thf('281', plain, ((l1_pre_topc @ sk_B)),
% 0.47/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.70  thf('282', plain, ((v1_funct_1 @ sk_E)),
% 0.47/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.70  thf('283', plain, (((k2_struct_0 @ sk_C) = (u1_struct_0 @ sk_C))),
% 0.47/0.70      inference('demod', [status(thm)], ['67', '68'])).
% 0.47/0.70  thf('284', plain,
% 0.47/0.70      ((v1_funct_2 @ sk_E @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 0.47/0.70      inference('demod', [status(thm)], ['84', '85'])).
% 0.47/0.70  thf('285', plain, (((k2_struct_0 @ sk_C) = (u1_struct_0 @ sk_C))),
% 0.47/0.70      inference('demod', [status(thm)], ['67', '68'])).
% 0.47/0.70  thf('286', plain, ((l1_struct_0 @ sk_C)),
% 0.47/0.70      inference('sup-', [status(thm)], ['50', '51'])).
% 0.47/0.70  thf('287', plain,
% 0.47/0.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.47/0.70         ((v2_struct_0 @ sk_B)
% 0.47/0.70          | (v2_struct_0 @ X0)
% 0.47/0.70          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.47/0.70          | (r1_tmap_1 @ X0 @ sk_B @ 
% 0.47/0.70             (k3_tmap_1 @ X2 @ sk_B @ sk_C @ X0 @ sk_E) @ X1)
% 0.47/0.70          | ~ (r1_tmap_1 @ sk_C @ sk_B @ sk_E @ X1)
% 0.47/0.70          | ~ (m1_subset_1 @ X1 @ (k2_struct_0 @ sk_C))
% 0.47/0.70          | ~ (m1_pre_topc @ X0 @ sk_C)
% 0.47/0.70          | ~ (m1_pre_topc @ X0 @ X2)
% 0.47/0.70          | ~ (v1_tsep_1 @ X0 @ X2)
% 0.47/0.70          | ~ (m1_pre_topc @ sk_C @ X2)
% 0.47/0.70          | (v2_struct_0 @ sk_C)
% 0.47/0.70          | ~ (l1_pre_topc @ X2)
% 0.47/0.70          | ~ (v2_pre_topc @ X2)
% 0.47/0.70          | (v2_struct_0 @ X2))),
% 0.47/0.70      inference('demod', [status(thm)],
% 0.47/0.70                ['279', '280', '281', '282', '283', '284', '285', '286'])).
% 0.47/0.70  thf('288', plain,
% 0.47/0.70      (![X0 : $i, X1 : $i]:
% 0.47/0.70         ((v2_struct_0 @ X0)
% 0.47/0.70          | ~ (v2_pre_topc @ X0)
% 0.47/0.70          | ~ (l1_pre_topc @ X0)
% 0.47/0.70          | (v2_struct_0 @ sk_C)
% 0.47/0.70          | ~ (m1_pre_topc @ sk_C @ X0)
% 0.47/0.70          | ~ (v1_tsep_1 @ X1 @ X0)
% 0.47/0.70          | ~ (m1_pre_topc @ X1 @ X0)
% 0.47/0.70          | ~ (m1_pre_topc @ X1 @ sk_C)
% 0.47/0.70          | ~ (m1_subset_1 @ sk_F @ (k2_struct_0 @ sk_C))
% 0.47/0.70          | (r1_tmap_1 @ X1 @ sk_B @ 
% 0.47/0.70             (k3_tmap_1 @ X0 @ sk_B @ sk_C @ X1 @ sk_E) @ sk_F)
% 0.47/0.70          | ~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ X1))
% 0.47/0.70          | (v2_struct_0 @ X1)
% 0.47/0.70          | (v2_struct_0 @ sk_B))),
% 0.47/0.70      inference('sup-', [status(thm)], ['273', '287'])).
% 0.47/0.70  thf('289', plain, ((m1_subset_1 @ sk_F @ (k2_struct_0 @ sk_C))),
% 0.47/0.70      inference('demod', [status(thm)], ['266', '267'])).
% 0.47/0.70  thf('290', plain,
% 0.47/0.70      (![X0 : $i, X1 : $i]:
% 0.47/0.70         ((v2_struct_0 @ X0)
% 0.47/0.70          | ~ (v2_pre_topc @ X0)
% 0.47/0.70          | ~ (l1_pre_topc @ X0)
% 0.47/0.70          | (v2_struct_0 @ sk_C)
% 0.47/0.70          | ~ (m1_pre_topc @ sk_C @ X0)
% 0.47/0.70          | ~ (v1_tsep_1 @ X1 @ X0)
% 0.47/0.70          | ~ (m1_pre_topc @ X1 @ X0)
% 0.47/0.70          | ~ (m1_pre_topc @ X1 @ sk_C)
% 0.47/0.70          | (r1_tmap_1 @ X1 @ sk_B @ 
% 0.47/0.70             (k3_tmap_1 @ X0 @ sk_B @ sk_C @ X1 @ sk_E) @ sk_F)
% 0.47/0.70          | ~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ X1))
% 0.47/0.70          | (v2_struct_0 @ X1)
% 0.47/0.70          | (v2_struct_0 @ sk_B))),
% 0.47/0.70      inference('demod', [status(thm)], ['288', '289'])).
% 0.47/0.70  thf('291', plain,
% 0.47/0.70      (![X0 : $i]:
% 0.47/0.70         (~ (m1_subset_1 @ sk_F @ (k2_struct_0 @ sk_C))
% 0.47/0.70          | (v2_struct_0 @ sk_B)
% 0.47/0.70          | (v2_struct_0 @ sk_D)
% 0.47/0.70          | (r1_tmap_1 @ sk_D @ sk_B @ 
% 0.47/0.70             (k3_tmap_1 @ X0 @ sk_B @ sk_C @ sk_D @ sk_E) @ sk_F)
% 0.47/0.70          | ~ (m1_pre_topc @ sk_D @ sk_C)
% 0.47/0.70          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.47/0.70          | ~ (v1_tsep_1 @ sk_D @ X0)
% 0.47/0.70          | ~ (m1_pre_topc @ sk_C @ X0)
% 0.47/0.70          | (v2_struct_0 @ sk_C)
% 0.47/0.70          | ~ (l1_pre_topc @ X0)
% 0.47/0.70          | ~ (v2_pre_topc @ X0)
% 0.47/0.70          | (v2_struct_0 @ X0))),
% 0.47/0.70      inference('sup-', [status(thm)], ['54', '290'])).
% 0.47/0.70  thf('292', plain, ((m1_subset_1 @ sk_F @ (k2_struct_0 @ sk_C))),
% 0.47/0.70      inference('demod', [status(thm)], ['266', '267'])).
% 0.47/0.70  thf('293', plain, ((m1_pre_topc @ sk_D @ sk_C)),
% 0.47/0.70      inference('demod', [status(thm)], ['29', '30', '31', '32'])).
% 0.47/0.70  thf('294', plain,
% 0.47/0.70      (![X0 : $i]:
% 0.47/0.70         ((v2_struct_0 @ sk_B)
% 0.47/0.70          | (v2_struct_0 @ sk_D)
% 0.47/0.70          | (r1_tmap_1 @ sk_D @ sk_B @ 
% 0.47/0.70             (k3_tmap_1 @ X0 @ sk_B @ sk_C @ sk_D @ sk_E) @ sk_F)
% 0.47/0.70          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.47/0.70          | ~ (v1_tsep_1 @ sk_D @ X0)
% 0.47/0.70          | ~ (m1_pre_topc @ sk_C @ X0)
% 0.47/0.70          | (v2_struct_0 @ sk_C)
% 0.47/0.70          | ~ (l1_pre_topc @ X0)
% 0.47/0.70          | ~ (v2_pre_topc @ X0)
% 0.47/0.70          | (v2_struct_0 @ X0))),
% 0.47/0.70      inference('demod', [status(thm)], ['291', '292', '293'])).
% 0.47/0.70  thf('295', plain,
% 0.47/0.70      ((~ (l1_pre_topc @ sk_D)
% 0.47/0.70        | (v2_struct_0 @ sk_D)
% 0.47/0.70        | ~ (v2_pre_topc @ sk_D)
% 0.47/0.70        | ~ (l1_pre_topc @ sk_D)
% 0.47/0.70        | (v2_struct_0 @ sk_C)
% 0.47/0.70        | ~ (m1_pre_topc @ sk_C @ sk_D)
% 0.47/0.70        | ~ (v1_tsep_1 @ sk_D @ sk_D)
% 0.47/0.70        | (r1_tmap_1 @ sk_D @ sk_B @ 
% 0.47/0.70           (k3_tmap_1 @ sk_D @ sk_B @ sk_C @ sk_D @ sk_E) @ sk_F)
% 0.47/0.70        | (v2_struct_0 @ sk_D)
% 0.47/0.70        | (v2_struct_0 @ sk_B))),
% 0.47/0.70      inference('sup-', [status(thm)], ['1', '294'])).
% 0.47/0.70  thf('296', plain, ((l1_pre_topc @ sk_D)),
% 0.47/0.70      inference('demod', [status(thm)], ['12', '13'])).
% 0.47/0.70  thf('297', plain, ((v2_pre_topc @ sk_D)),
% 0.47/0.70      inference('demod', [status(thm)], ['123', '124', '125'])).
% 0.47/0.71  thf('298', plain, ((l1_pre_topc @ sk_D)),
% 0.47/0.71      inference('demod', [status(thm)], ['12', '13'])).
% 0.47/0.71  thf('299', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 0.47/0.71      inference('demod', [status(thm)], ['61', '62'])).
% 0.47/0.71  thf('300', plain, (((u1_struct_0 @ sk_D) = (k2_struct_0 @ sk_C))),
% 0.47/0.71      inference('demod', [status(thm)], ['46', '53'])).
% 0.47/0.71  thf('301', plain,
% 0.47/0.71      (![X0 : $i]:
% 0.47/0.71         (~ (v2_pre_topc @ X0)
% 0.47/0.71          | (v1_tsep_1 @ X0 @ X0)
% 0.47/0.71          | ~ (v3_pre_topc @ (u1_struct_0 @ X0) @ X0)
% 0.47/0.71          | ~ (m1_pre_topc @ X0 @ X0)
% 0.47/0.71          | ~ (l1_pre_topc @ X0))),
% 0.47/0.71      inference('simplify', [status(thm)], ['245'])).
% 0.47/0.71  thf('302', plain,
% 0.47/0.71      ((~ (v3_pre_topc @ (k2_struct_0 @ sk_C) @ sk_D)
% 0.47/0.71        | ~ (l1_pre_topc @ sk_D)
% 0.47/0.71        | ~ (m1_pre_topc @ sk_D @ sk_D)
% 0.47/0.71        | (v1_tsep_1 @ sk_D @ sk_D)
% 0.47/0.71        | ~ (v2_pre_topc @ sk_D))),
% 0.47/0.71      inference('sup-', [status(thm)], ['300', '301'])).
% 0.47/0.71  thf('303', plain, (((k2_struct_0 @ sk_D) = (k2_struct_0 @ sk_C))),
% 0.47/0.71      inference('demod', [status(thm)], ['49', '52'])).
% 0.47/0.71  thf('304', plain,
% 0.47/0.71      (![X11 : $i]:
% 0.47/0.71         ((v3_pre_topc @ (k2_struct_0 @ X11) @ X11)
% 0.47/0.71          | ~ (l1_pre_topc @ X11)
% 0.47/0.71          | ~ (v2_pre_topc @ X11))),
% 0.47/0.71      inference('cnf', [status(esa)], [fc10_tops_1])).
% 0.47/0.71  thf('305', plain,
% 0.47/0.71      (((v3_pre_topc @ (k2_struct_0 @ sk_C) @ sk_D)
% 0.47/0.71        | ~ (v2_pre_topc @ sk_D)
% 0.47/0.71        | ~ (l1_pre_topc @ sk_D))),
% 0.47/0.71      inference('sup+', [status(thm)], ['303', '304'])).
% 0.47/0.71  thf('306', plain, ((v2_pre_topc @ sk_D)),
% 0.47/0.71      inference('demod', [status(thm)], ['123', '124', '125'])).
% 0.47/0.71  thf('307', plain, ((l1_pre_topc @ sk_D)),
% 0.47/0.71      inference('demod', [status(thm)], ['12', '13'])).
% 0.47/0.71  thf('308', plain, ((v3_pre_topc @ (k2_struct_0 @ sk_C) @ sk_D)),
% 0.47/0.71      inference('demod', [status(thm)], ['305', '306', '307'])).
% 0.47/0.71  thf('309', plain, ((l1_pre_topc @ sk_D)),
% 0.47/0.71      inference('demod', [status(thm)], ['12', '13'])).
% 0.47/0.71  thf('310', plain, ((m1_pre_topc @ sk_D @ sk_C)),
% 0.47/0.71      inference('demod', [status(thm)], ['29', '30', '31', '32'])).
% 0.47/0.71  thf('311', plain,
% 0.47/0.71      (![X9 : $i, X10 : $i]:
% 0.47/0.71         (~ (l1_pre_topc @ X9)
% 0.47/0.71          | ~ (m1_pre_topc @ X10 @ X9)
% 0.47/0.71          | (m1_pre_topc @ X10 @ 
% 0.47/0.71             (g1_pre_topc @ (u1_struct_0 @ X9) @ (u1_pre_topc @ X9)))
% 0.47/0.71          | ~ (l1_pre_topc @ X10))),
% 0.47/0.71      inference('cnf', [status(esa)], [t65_pre_topc])).
% 0.47/0.71  thf('312', plain,
% 0.47/0.71      ((~ (l1_pre_topc @ sk_D)
% 0.47/0.71        | (m1_pre_topc @ sk_D @ 
% 0.47/0.71           (g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)))
% 0.47/0.71        | ~ (l1_pre_topc @ sk_C))),
% 0.47/0.71      inference('sup-', [status(thm)], ['310', '311'])).
% 0.47/0.71  thf('313', plain, ((l1_pre_topc @ sk_D)),
% 0.47/0.71      inference('demod', [status(thm)], ['12', '13'])).
% 0.47/0.71  thf('314', plain,
% 0.47/0.71      (((g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) = (sk_D))),
% 0.47/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.71  thf('315', plain, ((l1_pre_topc @ sk_C)),
% 0.47/0.71      inference('demod', [status(thm)], ['18', '19'])).
% 0.47/0.71  thf('316', plain, ((m1_pre_topc @ sk_D @ sk_D)),
% 0.47/0.71      inference('demod', [status(thm)], ['312', '313', '314', '315'])).
% 0.47/0.71  thf('317', plain, ((v2_pre_topc @ sk_D)),
% 0.47/0.71      inference('demod', [status(thm)], ['123', '124', '125'])).
% 0.47/0.71  thf('318', plain, ((v1_tsep_1 @ sk_D @ sk_D)),
% 0.47/0.71      inference('demod', [status(thm)], ['302', '308', '309', '316', '317'])).
% 0.47/0.71  thf('319', plain,
% 0.47/0.71      (![X0 : $i]:
% 0.47/0.71         ((m1_pre_topc @ X0 @ 
% 0.47/0.71           (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.47/0.71          | ~ (l1_pre_topc @ X0))),
% 0.47/0.71      inference('simplify', [status(thm)], ['5'])).
% 0.47/0.71  thf('320', plain, ((m1_pre_topc @ sk_D @ sk_C)),
% 0.47/0.71      inference('demod', [status(thm)], ['29', '30', '31', '32'])).
% 0.47/0.71  thf('321', plain,
% 0.47/0.71      (![X0 : $i, X1 : $i]:
% 0.47/0.71         ((v2_struct_0 @ sk_B)
% 0.47/0.71          | ~ (m1_pre_topc @ X1 @ X0)
% 0.47/0.71          | ~ (m1_pre_topc @ X1 @ sk_C)
% 0.47/0.71          | ((k3_tmap_1 @ X0 @ sk_B @ sk_C @ X1 @ sk_E)
% 0.47/0.71              = (k2_partfun1 @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.47/0.71                 sk_E @ (u1_struct_0 @ X1)))
% 0.47/0.71          | ~ (m1_pre_topc @ sk_C @ X0)
% 0.47/0.71          | ~ (l1_pre_topc @ X0)
% 0.47/0.71          | ~ (v2_pre_topc @ X0)
% 0.47/0.71          | (v2_struct_0 @ X0))),
% 0.47/0.71      inference('demod', [status(thm)],
% 0.47/0.71                ['97', '98', '99', '100', '101', '102', '103', '104'])).
% 0.47/0.71  thf('322', plain,
% 0.47/0.71      (![X0 : $i]:
% 0.47/0.71         ((v2_struct_0 @ X0)
% 0.47/0.71          | ~ (v2_pre_topc @ X0)
% 0.47/0.71          | ~ (l1_pre_topc @ X0)
% 0.47/0.71          | ~ (m1_pre_topc @ sk_C @ X0)
% 0.47/0.71          | ((k3_tmap_1 @ X0 @ sk_B @ sk_C @ sk_D @ sk_E)
% 0.47/0.71              = (k2_partfun1 @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.47/0.71                 sk_E @ (u1_struct_0 @ sk_D)))
% 0.47/0.71          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.47/0.71          | (v2_struct_0 @ sk_B))),
% 0.47/0.71      inference('sup-', [status(thm)], ['320', '321'])).
% 0.47/0.71  thf('323', plain, (((u1_struct_0 @ sk_D) = (k2_struct_0 @ sk_C))),
% 0.47/0.71      inference('demod', [status(thm)], ['46', '53'])).
% 0.47/0.71  thf('324', plain,
% 0.47/0.71      (![X0 : $i]:
% 0.47/0.71         ((v2_struct_0 @ X0)
% 0.47/0.71          | ~ (v2_pre_topc @ X0)
% 0.47/0.71          | ~ (l1_pre_topc @ X0)
% 0.47/0.71          | ~ (m1_pre_topc @ sk_C @ X0)
% 0.47/0.71          | ((k3_tmap_1 @ X0 @ sk_B @ sk_C @ sk_D @ sk_E)
% 0.47/0.71              = (k2_partfun1 @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.47/0.71                 sk_E @ (k2_struct_0 @ sk_C)))
% 0.47/0.71          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.47/0.71          | (v2_struct_0 @ sk_B))),
% 0.47/0.71      inference('demod', [status(thm)], ['322', '323'])).
% 0.47/0.71  thf('325', plain,
% 0.47/0.71      (((k2_partfun1 @ (k2_struct_0 @ sk_C) @ (k2_struct_0 @ sk_B) @ sk_E @ 
% 0.47/0.71         (k2_struct_0 @ sk_C))
% 0.47/0.71         = (k2_partfun1 @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_E @ 
% 0.47/0.71            (k2_struct_0 @ sk_C)))),
% 0.47/0.71      inference('clc', [status(thm)], ['192', '193'])).
% 0.47/0.71  thf('326', plain,
% 0.47/0.71      (![X0 : $i]:
% 0.47/0.71         ((v2_struct_0 @ X0)
% 0.47/0.71          | ~ (v2_pre_topc @ X0)
% 0.47/0.71          | ~ (l1_pre_topc @ X0)
% 0.47/0.71          | ~ (m1_pre_topc @ sk_C @ X0)
% 0.47/0.71          | ((k3_tmap_1 @ X0 @ sk_B @ sk_C @ sk_D @ sk_E)
% 0.47/0.71              = (k2_partfun1 @ (k2_struct_0 @ sk_C) @ (k2_struct_0 @ sk_B) @ 
% 0.47/0.71                 sk_E @ (k2_struct_0 @ sk_C)))
% 0.47/0.71          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.47/0.71          | (v2_struct_0 @ sk_B))),
% 0.47/0.71      inference('demod', [status(thm)], ['324', '325'])).
% 0.47/0.71  thf('327', plain,
% 0.47/0.71      ((~ (l1_pre_topc @ sk_C)
% 0.47/0.71        | (v2_struct_0 @ sk_B)
% 0.47/0.71        | ~ (m1_pre_topc @ sk_D @ 
% 0.47/0.71             (g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)))
% 0.47/0.71        | ((k3_tmap_1 @ 
% 0.47/0.71            (g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) @ 
% 0.47/0.71            sk_B @ sk_C @ sk_D @ sk_E)
% 0.47/0.71            = (k2_partfun1 @ (k2_struct_0 @ sk_C) @ (k2_struct_0 @ sk_B) @ 
% 0.47/0.71               sk_E @ (k2_struct_0 @ sk_C)))
% 0.47/0.71        | ~ (l1_pre_topc @ 
% 0.47/0.71             (g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)))
% 0.47/0.71        | ~ (v2_pre_topc @ 
% 0.47/0.71             (g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)))
% 0.47/0.71        | (v2_struct_0 @ 
% 0.47/0.71           (g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C))))),
% 0.47/0.71      inference('sup-', [status(thm)], ['319', '326'])).
% 0.47/0.71  thf('328', plain, ((l1_pre_topc @ sk_C)),
% 0.47/0.71      inference('demod', [status(thm)], ['18', '19'])).
% 0.47/0.71  thf('329', plain, (((k2_struct_0 @ sk_C) = (u1_struct_0 @ sk_C))),
% 0.47/0.71      inference('demod', [status(thm)], ['67', '68'])).
% 0.47/0.71  thf('330', plain,
% 0.47/0.71      (((g1_pre_topc @ (k2_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) = (sk_D))),
% 0.47/0.71      inference('demod', [status(thm)], ['116', '117'])).
% 0.47/0.71  thf('331', plain, ((m1_pre_topc @ sk_D @ sk_D)),
% 0.47/0.71      inference('demod', [status(thm)], ['312', '313', '314', '315'])).
% 0.47/0.71  thf('332', plain, (((k2_struct_0 @ sk_C) = (u1_struct_0 @ sk_C))),
% 0.47/0.71      inference('demod', [status(thm)], ['67', '68'])).
% 0.47/0.71  thf('333', plain,
% 0.47/0.71      (((g1_pre_topc @ (k2_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) = (sk_D))),
% 0.47/0.71      inference('demod', [status(thm)], ['116', '117'])).
% 0.47/0.71  thf('334', plain, (((k2_struct_0 @ sk_C) = (u1_struct_0 @ sk_C))),
% 0.47/0.71      inference('demod', [status(thm)], ['67', '68'])).
% 0.47/0.71  thf('335', plain,
% 0.47/0.71      (((g1_pre_topc @ (k2_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) = (sk_D))),
% 0.47/0.71      inference('demod', [status(thm)], ['116', '117'])).
% 0.47/0.71  thf('336', plain, ((l1_pre_topc @ sk_D)),
% 0.47/0.71      inference('demod', [status(thm)], ['12', '13'])).
% 0.47/0.71  thf('337', plain, (((k2_struct_0 @ sk_C) = (u1_struct_0 @ sk_C))),
% 0.47/0.71      inference('demod', [status(thm)], ['67', '68'])).
% 0.47/0.71  thf('338', plain,
% 0.47/0.71      (((g1_pre_topc @ (k2_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) = (sk_D))),
% 0.47/0.71      inference('demod', [status(thm)], ['116', '117'])).
% 0.47/0.71  thf('339', plain, ((v2_pre_topc @ sk_D)),
% 0.47/0.71      inference('demod', [status(thm)], ['123', '124', '125'])).
% 0.47/0.71  thf('340', plain, (((k2_struct_0 @ sk_C) = (u1_struct_0 @ sk_C))),
% 0.47/0.71      inference('demod', [status(thm)], ['67', '68'])).
% 0.47/0.71  thf('341', plain,
% 0.47/0.71      (((g1_pre_topc @ (k2_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) = (sk_D))),
% 0.47/0.71      inference('demod', [status(thm)], ['116', '117'])).
% 0.47/0.71  thf('342', plain,
% 0.47/0.71      (((v2_struct_0 @ sk_B)
% 0.47/0.71        | ((k3_tmap_1 @ sk_D @ sk_B @ sk_C @ sk_D @ sk_E)
% 0.47/0.71            = (k2_partfun1 @ (k2_struct_0 @ sk_C) @ (k2_struct_0 @ sk_B) @ 
% 0.47/0.71               sk_E @ (k2_struct_0 @ sk_C)))
% 0.47/0.71        | (v2_struct_0 @ sk_D))),
% 0.47/0.71      inference('demod', [status(thm)],
% 0.47/0.71                ['327', '328', '329', '330', '331', '332', '333', '334', 
% 0.47/0.71                 '335', '336', '337', '338', '339', '340', '341'])).
% 0.47/0.71  thf('343', plain, (~ (v2_struct_0 @ sk_B)),
% 0.47/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.71  thf('344', plain,
% 0.47/0.71      (((v2_struct_0 @ sk_D)
% 0.47/0.71        | ((k3_tmap_1 @ sk_D @ sk_B @ sk_C @ sk_D @ sk_E)
% 0.47/0.71            = (k2_partfun1 @ (k2_struct_0 @ sk_C) @ (k2_struct_0 @ sk_B) @ 
% 0.47/0.71               sk_E @ (k2_struct_0 @ sk_C))))),
% 0.47/0.71      inference('clc', [status(thm)], ['342', '343'])).
% 0.47/0.71  thf('345', plain, (~ (v2_struct_0 @ sk_D)),
% 0.47/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.71  thf('346', plain,
% 0.47/0.71      (((k3_tmap_1 @ sk_D @ sk_B @ sk_C @ sk_D @ sk_E)
% 0.47/0.71         = (k2_partfun1 @ (k2_struct_0 @ sk_C) @ (k2_struct_0 @ sk_B) @ sk_E @ 
% 0.47/0.71            (k2_struct_0 @ sk_C)))),
% 0.47/0.71      inference('clc', [status(thm)], ['344', '345'])).
% 0.47/0.71  thf('347', plain,
% 0.47/0.71      (((v2_struct_0 @ sk_D)
% 0.47/0.71        | (v2_struct_0 @ sk_C)
% 0.47/0.71        | (r1_tmap_1 @ sk_D @ sk_B @ 
% 0.47/0.71           (k2_partfun1 @ (k2_struct_0 @ sk_C) @ (k2_struct_0 @ sk_B) @ sk_E @ 
% 0.47/0.71            (k2_struct_0 @ sk_C)) @ 
% 0.47/0.71           sk_F)
% 0.47/0.71        | (v2_struct_0 @ sk_D)
% 0.47/0.71        | (v2_struct_0 @ sk_B))),
% 0.47/0.71      inference('demod', [status(thm)],
% 0.47/0.71                ['295', '296', '297', '298', '299', '318', '346'])).
% 0.47/0.71  thf('348', plain,
% 0.47/0.71      (((v2_struct_0 @ sk_B)
% 0.47/0.71        | (r1_tmap_1 @ sk_D @ sk_B @ 
% 0.47/0.71           (k2_partfun1 @ (k2_struct_0 @ sk_C) @ (k2_struct_0 @ sk_B) @ sk_E @ 
% 0.47/0.71            (k2_struct_0 @ sk_C)) @ 
% 0.47/0.71           sk_F)
% 0.47/0.71        | (v2_struct_0 @ sk_C)
% 0.47/0.71        | (v2_struct_0 @ sk_D))),
% 0.47/0.71      inference('simplify', [status(thm)], ['347'])).
% 0.47/0.71  thf('349', plain,
% 0.47/0.71      (![X22 : $i]: ((m1_pre_topc @ X22 @ X22) | ~ (l1_pre_topc @ X22))),
% 0.47/0.71      inference('cnf', [status(esa)], [t2_tsep_1])).
% 0.47/0.71  thf('350', plain,
% 0.47/0.71      (![X22 : $i]: ((m1_pre_topc @ X22 @ X22) | ~ (l1_pre_topc @ X22))),
% 0.47/0.71      inference('cnf', [status(esa)], [t2_tsep_1])).
% 0.47/0.71  thf('351', plain,
% 0.47/0.71      (![X0 : $i, X1 : $i]:
% 0.47/0.71         ((v2_struct_0 @ sk_B)
% 0.47/0.71          | ~ (m1_pre_topc @ X1 @ X0)
% 0.47/0.71          | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.47/0.71          | ((k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E)
% 0.47/0.71              = (k2_partfun1 @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.47/0.71                 sk_E @ (u1_struct_0 @ X1)))
% 0.47/0.71          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.47/0.71          | ~ (l1_pre_topc @ X0)
% 0.47/0.71          | ~ (v2_pre_topc @ X0)
% 0.47/0.71          | (v2_struct_0 @ X0))),
% 0.47/0.71      inference('demod', [status(thm)], ['77', '78', '79', '86', '87'])).
% 0.47/0.71  thf('352', plain,
% 0.47/0.71      (![X0 : $i]:
% 0.47/0.71         (~ (l1_pre_topc @ sk_D)
% 0.47/0.71          | (v2_struct_0 @ X0)
% 0.47/0.71          | ~ (v2_pre_topc @ X0)
% 0.47/0.71          | ~ (l1_pre_topc @ X0)
% 0.47/0.71          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.47/0.71          | ((k3_tmap_1 @ X0 @ sk_B @ sk_D @ sk_D @ sk_E)
% 0.47/0.71              = (k2_partfun1 @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.47/0.71                 sk_E @ (u1_struct_0 @ sk_D)))
% 0.47/0.71          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.47/0.71          | (v2_struct_0 @ sk_B))),
% 0.47/0.71      inference('sup-', [status(thm)], ['350', '351'])).
% 0.47/0.71  thf('353', plain, ((l1_pre_topc @ sk_D)),
% 0.47/0.71      inference('demod', [status(thm)], ['12', '13'])).
% 0.47/0.71  thf('354', plain, (((u1_struct_0 @ sk_D) = (k2_struct_0 @ sk_C))),
% 0.47/0.71      inference('demod', [status(thm)], ['46', '53'])).
% 0.47/0.71  thf('355', plain,
% 0.47/0.71      (((k2_partfun1 @ (k2_struct_0 @ sk_C) @ (k2_struct_0 @ sk_B) @ sk_E @ 
% 0.47/0.71         (k2_struct_0 @ sk_C))
% 0.47/0.71         = (k2_partfun1 @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_E @ 
% 0.47/0.71            (k2_struct_0 @ sk_C)))),
% 0.47/0.71      inference('clc', [status(thm)], ['192', '193'])).
% 0.47/0.71  thf('356', plain,
% 0.47/0.71      (![X0 : $i]:
% 0.47/0.71         ((v2_struct_0 @ X0)
% 0.47/0.71          | ~ (v2_pre_topc @ X0)
% 0.47/0.71          | ~ (l1_pre_topc @ X0)
% 0.47/0.71          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.47/0.71          | ((k3_tmap_1 @ X0 @ sk_B @ sk_D @ sk_D @ sk_E)
% 0.47/0.71              = (k2_partfun1 @ (k2_struct_0 @ sk_C) @ (k2_struct_0 @ sk_B) @ 
% 0.47/0.71                 sk_E @ (k2_struct_0 @ sk_C)))
% 0.47/0.71          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.47/0.71          | (v2_struct_0 @ sk_B))),
% 0.47/0.71      inference('demod', [status(thm)], ['352', '353', '354', '355'])).
% 0.47/0.71  thf('357', plain,
% 0.47/0.71      (![X0 : $i]:
% 0.47/0.71         ((v2_struct_0 @ sk_B)
% 0.47/0.71          | ((k3_tmap_1 @ X0 @ sk_B @ sk_D @ sk_D @ sk_E)
% 0.47/0.71              = (k2_partfun1 @ (k2_struct_0 @ sk_C) @ (k2_struct_0 @ sk_B) @ 
% 0.47/0.71                 sk_E @ (k2_struct_0 @ sk_C)))
% 0.47/0.71          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.47/0.71          | ~ (l1_pre_topc @ X0)
% 0.47/0.71          | ~ (v2_pre_topc @ X0)
% 0.47/0.71          | (v2_struct_0 @ X0))),
% 0.47/0.71      inference('simplify', [status(thm)], ['356'])).
% 0.47/0.71  thf('358', plain,
% 0.47/0.71      ((~ (l1_pre_topc @ sk_D)
% 0.47/0.71        | (v2_struct_0 @ sk_D)
% 0.47/0.71        | ~ (v2_pre_topc @ sk_D)
% 0.47/0.71        | ~ (l1_pre_topc @ sk_D)
% 0.47/0.71        | ((k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_D @ sk_E)
% 0.47/0.71            = (k2_partfun1 @ (k2_struct_0 @ sk_C) @ (k2_struct_0 @ sk_B) @ 
% 0.47/0.71               sk_E @ (k2_struct_0 @ sk_C)))
% 0.47/0.71        | (v2_struct_0 @ sk_B))),
% 0.47/0.71      inference('sup-', [status(thm)], ['349', '357'])).
% 0.47/0.71  thf('359', plain, ((l1_pre_topc @ sk_D)),
% 0.47/0.71      inference('demod', [status(thm)], ['12', '13'])).
% 0.47/0.71  thf('360', plain, ((v2_pre_topc @ sk_D)),
% 0.47/0.71      inference('demod', [status(thm)], ['123', '124', '125'])).
% 0.47/0.71  thf('361', plain, ((l1_pre_topc @ sk_D)),
% 0.47/0.71      inference('demod', [status(thm)], ['12', '13'])).
% 0.47/0.71  thf('362', plain,
% 0.47/0.71      (((v2_struct_0 @ sk_D)
% 0.47/0.71        | ((k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_D @ sk_E)
% 0.47/0.71            = (k2_partfun1 @ (k2_struct_0 @ sk_C) @ (k2_struct_0 @ sk_B) @ 
% 0.47/0.71               sk_E @ (k2_struct_0 @ sk_C)))
% 0.47/0.71        | (v2_struct_0 @ sk_B))),
% 0.47/0.71      inference('demod', [status(thm)], ['358', '359', '360', '361'])).
% 0.47/0.71  thf('363', plain, (~ (v2_struct_0 @ sk_D)),
% 0.47/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.71  thf('364', plain,
% 0.47/0.71      (((v2_struct_0 @ sk_B)
% 0.47/0.71        | ((k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_D @ sk_E)
% 0.47/0.71            = (k2_partfun1 @ (k2_struct_0 @ sk_C) @ (k2_struct_0 @ sk_B) @ 
% 0.47/0.71               sk_E @ (k2_struct_0 @ sk_C))))),
% 0.47/0.71      inference('clc', [status(thm)], ['362', '363'])).
% 0.47/0.71  thf('365', plain, (~ (v2_struct_0 @ sk_B)),
% 0.47/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.71  thf('366', plain,
% 0.47/0.71      (((k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_D @ sk_E)
% 0.47/0.71         = (k2_partfun1 @ (k2_struct_0 @ sk_C) @ (k2_struct_0 @ sk_B) @ sk_E @ 
% 0.47/0.71            (k2_struct_0 @ sk_C)))),
% 0.47/0.71      inference('clc', [status(thm)], ['364', '365'])).
% 0.47/0.71  thf('367', plain,
% 0.47/0.71      ((m1_subset_1 @ sk_E @ 
% 0.47/0.71        (k1_zfmisc_1 @ 
% 0.47/0.71         (k2_zfmisc_1 @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 0.47/0.71      inference('demod', [status(thm)], ['66', '69'])).
% 0.47/0.71  thf('368', plain, (((u1_struct_0 @ sk_D) = (k2_struct_0 @ sk_C))),
% 0.47/0.71      inference('demod', [status(thm)], ['46', '53'])).
% 0.47/0.71  thf('369', plain,
% 0.47/0.71      (![X28 : $i, X29 : $i, X30 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 0.47/0.71         ((v2_struct_0 @ X33)
% 0.47/0.71          | ~ (v2_pre_topc @ X33)
% 0.47/0.71          | ~ (l1_pre_topc @ X33)
% 0.47/0.71          | (v2_struct_0 @ X30)
% 0.47/0.71          | ~ (v1_funct_1 @ X34)
% 0.47/0.71          | ~ (v1_funct_2 @ X34 @ (u1_struct_0 @ X29) @ (u1_struct_0 @ X33))
% 0.47/0.71          | ~ (m1_subset_1 @ X34 @ 
% 0.47/0.71               (k1_zfmisc_1 @ 
% 0.47/0.71                (k2_zfmisc_1 @ (u1_struct_0 @ X29) @ (u1_struct_0 @ X33))))
% 0.47/0.71          | ~ (m1_subset_1 @ X32 @ (u1_struct_0 @ X30))
% 0.47/0.71          | (r1_tmap_1 @ X29 @ X33 @ X34 @ X32)
% 0.47/0.71          | ~ (r1_tmap_1 @ X30 @ X33 @ 
% 0.47/0.71               (k3_tmap_1 @ X28 @ X33 @ X29 @ X30 @ X34) @ X32)
% 0.47/0.71          | ~ (m1_subset_1 @ X32 @ (u1_struct_0 @ X29))
% 0.47/0.71          | ~ (m1_pre_topc @ X30 @ X29)
% 0.47/0.71          | ~ (m1_pre_topc @ X30 @ X28)
% 0.47/0.71          | ~ (v1_tsep_1 @ X30 @ X28)
% 0.47/0.71          | ~ (m1_pre_topc @ X29 @ X28)
% 0.47/0.71          | (v2_struct_0 @ X29)
% 0.47/0.71          | ~ (l1_pre_topc @ X28)
% 0.47/0.71          | ~ (v2_pre_topc @ X28)
% 0.47/0.71          | (v2_struct_0 @ X28))),
% 0.47/0.71      inference('simplify', [status(thm)], ['213'])).
% 0.47/0.71  thf('370', plain,
% 0.47/0.71      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.47/0.71         (~ (m1_subset_1 @ X1 @ 
% 0.47/0.71             (k1_zfmisc_1 @ 
% 0.47/0.71              (k2_zfmisc_1 @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ X0))))
% 0.47/0.71          | (v2_struct_0 @ X2)
% 0.47/0.71          | ~ (v2_pre_topc @ X2)
% 0.47/0.71          | ~ (l1_pre_topc @ X2)
% 0.47/0.71          | (v2_struct_0 @ sk_D)
% 0.47/0.71          | ~ (m1_pre_topc @ sk_D @ X2)
% 0.47/0.71          | ~ (v1_tsep_1 @ X3 @ X2)
% 0.47/0.71          | ~ (m1_pre_topc @ X3 @ X2)
% 0.47/0.71          | ~ (m1_pre_topc @ X3 @ sk_D)
% 0.47/0.71          | ~ (m1_subset_1 @ X4 @ (u1_struct_0 @ sk_D))
% 0.47/0.71          | ~ (r1_tmap_1 @ X3 @ X0 @ (k3_tmap_1 @ X2 @ X0 @ sk_D @ X3 @ X1) @ 
% 0.47/0.71               X4)
% 0.47/0.71          | (r1_tmap_1 @ sk_D @ X0 @ X1 @ X4)
% 0.47/0.71          | ~ (m1_subset_1 @ X4 @ (u1_struct_0 @ X3))
% 0.47/0.71          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ X0))
% 0.47/0.71          | ~ (v1_funct_1 @ X1)
% 0.47/0.71          | (v2_struct_0 @ X3)
% 0.47/0.71          | ~ (l1_pre_topc @ X0)
% 0.47/0.71          | ~ (v2_pre_topc @ X0)
% 0.47/0.71          | (v2_struct_0 @ X0))),
% 0.47/0.71      inference('sup-', [status(thm)], ['368', '369'])).
% 0.47/0.71  thf('371', plain, (((u1_struct_0 @ sk_D) = (k2_struct_0 @ sk_C))),
% 0.47/0.71      inference('demod', [status(thm)], ['46', '53'])).
% 0.47/0.71  thf('372', plain, (((u1_struct_0 @ sk_D) = (k2_struct_0 @ sk_C))),
% 0.47/0.71      inference('demod', [status(thm)], ['46', '53'])).
% 0.47/0.71  thf('373', plain,
% 0.47/0.71      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.47/0.71         (~ (m1_subset_1 @ X1 @ 
% 0.47/0.71             (k1_zfmisc_1 @ 
% 0.47/0.71              (k2_zfmisc_1 @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ X0))))
% 0.47/0.71          | (v2_struct_0 @ X2)
% 0.47/0.71          | ~ (v2_pre_topc @ X2)
% 0.47/0.71          | ~ (l1_pre_topc @ X2)
% 0.47/0.71          | (v2_struct_0 @ sk_D)
% 0.47/0.71          | ~ (m1_pre_topc @ sk_D @ X2)
% 0.47/0.71          | ~ (v1_tsep_1 @ X3 @ X2)
% 0.47/0.71          | ~ (m1_pre_topc @ X3 @ X2)
% 0.47/0.71          | ~ (m1_pre_topc @ X3 @ sk_D)
% 0.47/0.71          | ~ (m1_subset_1 @ X4 @ (k2_struct_0 @ sk_C))
% 0.47/0.71          | ~ (r1_tmap_1 @ X3 @ X0 @ (k3_tmap_1 @ X2 @ X0 @ sk_D @ X3 @ X1) @ 
% 0.47/0.71               X4)
% 0.47/0.71          | (r1_tmap_1 @ sk_D @ X0 @ X1 @ X4)
% 0.47/0.71          | ~ (m1_subset_1 @ X4 @ (u1_struct_0 @ X3))
% 0.47/0.71          | ~ (v1_funct_2 @ X1 @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ X0))
% 0.47/0.71          | ~ (v1_funct_1 @ X1)
% 0.47/0.71          | (v2_struct_0 @ X3)
% 0.47/0.71          | ~ (l1_pre_topc @ X0)
% 0.47/0.71          | ~ (v2_pre_topc @ X0)
% 0.47/0.71          | (v2_struct_0 @ X0))),
% 0.47/0.71      inference('demod', [status(thm)], ['370', '371', '372'])).
% 0.47/0.71  thf('374', plain,
% 0.47/0.71      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.47/0.71         ((v2_struct_0 @ sk_B)
% 0.47/0.71          | ~ (v2_pre_topc @ sk_B)
% 0.47/0.71          | ~ (l1_pre_topc @ sk_B)
% 0.47/0.71          | (v2_struct_0 @ X0)
% 0.47/0.71          | ~ (v1_funct_1 @ sk_E)
% 0.47/0.71          | ~ (v1_funct_2 @ sk_E @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))
% 0.47/0.71          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.47/0.71          | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X1)
% 0.47/0.71          | ~ (r1_tmap_1 @ X0 @ sk_B @ 
% 0.47/0.71               (k3_tmap_1 @ X2 @ sk_B @ sk_D @ X0 @ sk_E) @ X1)
% 0.47/0.71          | ~ (m1_subset_1 @ X1 @ (k2_struct_0 @ sk_C))
% 0.47/0.71          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.47/0.71          | ~ (m1_pre_topc @ X0 @ X2)
% 0.47/0.71          | ~ (v1_tsep_1 @ X0 @ X2)
% 0.47/0.71          | ~ (m1_pre_topc @ sk_D @ X2)
% 0.47/0.71          | (v2_struct_0 @ sk_D)
% 0.47/0.71          | ~ (l1_pre_topc @ X2)
% 0.47/0.71          | ~ (v2_pre_topc @ X2)
% 0.47/0.71          | (v2_struct_0 @ X2))),
% 0.47/0.71      inference('sup-', [status(thm)], ['367', '373'])).
% 0.47/0.71  thf('375', plain, ((v2_pre_topc @ sk_B)),
% 0.47/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.71  thf('376', plain, ((l1_pre_topc @ sk_B)),
% 0.47/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.71  thf('377', plain, ((v1_funct_1 @ sk_E)),
% 0.47/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.71  thf('378', plain,
% 0.47/0.71      ((v1_funct_2 @ sk_E @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 0.47/0.71      inference('demod', [status(thm)], ['84', '85'])).
% 0.47/0.71  thf('379', plain,
% 0.47/0.71      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.47/0.71         ((v2_struct_0 @ sk_B)
% 0.47/0.71          | (v2_struct_0 @ X0)
% 0.47/0.71          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.47/0.71          | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X1)
% 0.47/0.71          | ~ (r1_tmap_1 @ X0 @ sk_B @ 
% 0.47/0.71               (k3_tmap_1 @ X2 @ sk_B @ sk_D @ X0 @ sk_E) @ X1)
% 0.47/0.71          | ~ (m1_subset_1 @ X1 @ (k2_struct_0 @ sk_C))
% 0.47/0.71          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.47/0.71          | ~ (m1_pre_topc @ X0 @ X2)
% 0.47/0.71          | ~ (v1_tsep_1 @ X0 @ X2)
% 0.47/0.71          | ~ (m1_pre_topc @ sk_D @ X2)
% 0.47/0.71          | (v2_struct_0 @ sk_D)
% 0.47/0.71          | ~ (l1_pre_topc @ X2)
% 0.47/0.71          | ~ (v2_pre_topc @ X2)
% 0.47/0.71          | (v2_struct_0 @ X2))),
% 0.47/0.71      inference('demod', [status(thm)], ['374', '375', '376', '377', '378'])).
% 0.47/0.71  thf('380', plain,
% 0.47/0.71      (![X0 : $i]:
% 0.47/0.71         (~ (r1_tmap_1 @ sk_D @ sk_B @ 
% 0.47/0.71             (k2_partfun1 @ (k2_struct_0 @ sk_C) @ (k2_struct_0 @ sk_B) @ 
% 0.47/0.71              sk_E @ (k2_struct_0 @ sk_C)) @ 
% 0.47/0.71             X0)
% 0.47/0.71          | (v2_struct_0 @ sk_D)
% 0.47/0.71          | ~ (v2_pre_topc @ sk_D)
% 0.47/0.71          | ~ (l1_pre_topc @ sk_D)
% 0.47/0.71          | (v2_struct_0 @ sk_D)
% 0.47/0.71          | ~ (m1_pre_topc @ sk_D @ sk_D)
% 0.47/0.71          | ~ (v1_tsep_1 @ sk_D @ sk_D)
% 0.47/0.71          | ~ (m1_pre_topc @ sk_D @ sk_D)
% 0.47/0.71          | ~ (m1_pre_topc @ sk_D @ sk_D)
% 0.47/0.71          | ~ (m1_subset_1 @ X0 @ (k2_struct_0 @ sk_C))
% 0.47/0.71          | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X0)
% 0.47/0.71          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_D))
% 0.47/0.71          | (v2_struct_0 @ sk_D)
% 0.47/0.71          | (v2_struct_0 @ sk_B))),
% 0.47/0.71      inference('sup-', [status(thm)], ['366', '379'])).
% 0.47/0.71  thf('381', plain, ((v2_pre_topc @ sk_D)),
% 0.47/0.71      inference('demod', [status(thm)], ['123', '124', '125'])).
% 0.47/0.71  thf('382', plain, ((l1_pre_topc @ sk_D)),
% 0.47/0.71      inference('demod', [status(thm)], ['12', '13'])).
% 0.47/0.71  thf('383', plain, ((m1_pre_topc @ sk_D @ sk_D)),
% 0.47/0.71      inference('demod', [status(thm)], ['312', '313', '314', '315'])).
% 0.47/0.71  thf('384', plain, ((v1_tsep_1 @ sk_D @ sk_D)),
% 0.47/0.71      inference('demod', [status(thm)], ['302', '308', '309', '316', '317'])).
% 0.47/0.71  thf('385', plain, ((m1_pre_topc @ sk_D @ sk_D)),
% 0.47/0.71      inference('demod', [status(thm)], ['312', '313', '314', '315'])).
% 0.47/0.71  thf('386', plain, ((m1_pre_topc @ sk_D @ sk_D)),
% 0.47/0.71      inference('demod', [status(thm)], ['312', '313', '314', '315'])).
% 0.47/0.71  thf('387', plain, (((u1_struct_0 @ sk_D) = (k2_struct_0 @ sk_C))),
% 0.47/0.71      inference('demod', [status(thm)], ['46', '53'])).
% 0.47/0.71  thf('388', plain,
% 0.47/0.71      (![X0 : $i]:
% 0.47/0.71         (~ (r1_tmap_1 @ sk_D @ sk_B @ 
% 0.47/0.71             (k2_partfun1 @ (k2_struct_0 @ sk_C) @ (k2_struct_0 @ sk_B) @ 
% 0.47/0.71              sk_E @ (k2_struct_0 @ sk_C)) @ 
% 0.47/0.71             X0)
% 0.47/0.71          | (v2_struct_0 @ sk_D)
% 0.47/0.71          | (v2_struct_0 @ sk_D)
% 0.47/0.71          | ~ (m1_subset_1 @ X0 @ (k2_struct_0 @ sk_C))
% 0.47/0.71          | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X0)
% 0.47/0.71          | ~ (m1_subset_1 @ X0 @ (k2_struct_0 @ sk_C))
% 0.47/0.71          | (v2_struct_0 @ sk_D)
% 0.47/0.71          | (v2_struct_0 @ sk_B))),
% 0.47/0.71      inference('demod', [status(thm)],
% 0.47/0.71                ['380', '381', '382', '383', '384', '385', '386', '387'])).
% 0.47/0.71  thf('389', plain,
% 0.47/0.71      (![X0 : $i]:
% 0.47/0.71         ((v2_struct_0 @ sk_B)
% 0.47/0.71          | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X0)
% 0.47/0.71          | ~ (m1_subset_1 @ X0 @ (k2_struct_0 @ sk_C))
% 0.47/0.71          | (v2_struct_0 @ sk_D)
% 0.47/0.71          | ~ (r1_tmap_1 @ sk_D @ sk_B @ 
% 0.47/0.71               (k2_partfun1 @ (k2_struct_0 @ sk_C) @ (k2_struct_0 @ sk_B) @ 
% 0.47/0.71                sk_E @ (k2_struct_0 @ sk_C)) @ 
% 0.47/0.71               X0))),
% 0.47/0.71      inference('simplify', [status(thm)], ['388'])).
% 0.47/0.71  thf('390', plain,
% 0.47/0.71      (((v2_struct_0 @ sk_D)
% 0.47/0.71        | (v2_struct_0 @ sk_C)
% 0.47/0.71        | (v2_struct_0 @ sk_B)
% 0.47/0.71        | (v2_struct_0 @ sk_D)
% 0.47/0.71        | ~ (m1_subset_1 @ sk_F @ (k2_struct_0 @ sk_C))
% 0.47/0.71        | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)
% 0.47/0.71        | (v2_struct_0 @ sk_B))),
% 0.47/0.71      inference('sup-', [status(thm)], ['348', '389'])).
% 0.47/0.71  thf('391', plain, ((m1_subset_1 @ sk_F @ (k2_struct_0 @ sk_C))),
% 0.47/0.71      inference('demod', [status(thm)], ['266', '267'])).
% 0.47/0.71  thf('392', plain,
% 0.47/0.71      (((v2_struct_0 @ sk_D)
% 0.47/0.71        | (v2_struct_0 @ sk_C)
% 0.47/0.71        | (v2_struct_0 @ sk_B)
% 0.47/0.71        | (v2_struct_0 @ sk_D)
% 0.47/0.71        | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)
% 0.47/0.71        | (v2_struct_0 @ sk_B))),
% 0.47/0.71      inference('demod', [status(thm)], ['390', '391'])).
% 0.47/0.71  thf('393', plain,
% 0.47/0.71      (((r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)
% 0.47/0.71        | (v2_struct_0 @ sk_B)
% 0.47/0.71        | (v2_struct_0 @ sk_C)
% 0.47/0.71        | (v2_struct_0 @ sk_D))),
% 0.47/0.71      inference('simplify', [status(thm)], ['392'])).
% 0.47/0.71  thf('394', plain, (~ (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)),
% 0.47/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.71  thf('395', plain,
% 0.47/0.71      (((v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_B))),
% 0.47/0.71      inference('sup-', [status(thm)], ['393', '394'])).
% 0.47/0.71  thf('396', plain, (~ (v2_struct_0 @ sk_D)),
% 0.47/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.71  thf('397', plain, (((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_C))),
% 0.47/0.71      inference('clc', [status(thm)], ['395', '396'])).
% 0.47/0.71  thf('398', plain, (~ (v2_struct_0 @ sk_B)),
% 0.47/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.71  thf('399', plain, ((v2_struct_0 @ sk_C)),
% 0.47/0.71      inference('clc', [status(thm)], ['397', '398'])).
% 0.47/0.71  thf('400', plain, ($false), inference('demod', [status(thm)], ['0', '399'])).
% 0.47/0.71  
% 0.47/0.71  % SZS output end Refutation
% 0.47/0.71  
% 0.56/0.71  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
