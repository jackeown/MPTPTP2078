%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.gYWMKycWV7

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:10:26 EST 2020

% Result     : Theorem 14.58s
% Output     : Refutation 14.58s
% Verified   : 
% Statistics : Number of formulae       :  188 (1616 expanded)
%              Number of leaves         :   45 ( 495 expanded)
%              Depth                    :   23
%              Number of atoms          : 1666 (40501 expanded)
%              Number of equality atoms :   58 (1359 expanded)
%              Maximal formula depth    :   33 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_G_type,type,(
    sk_G: $i )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(g1_pre_topc_type,type,(
    g1_pre_topc: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r1_tmap_1_type,type,(
    r1_tmap_1: $i > $i > $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k3_tmap_1_type,type,(
    k3_tmap_1: $i > $i > $i > $i > $i > $i )).

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

thf(abstractness_v1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( ( v1_pre_topc @ A )
       => ( A
          = ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ) )).

thf('10',plain,(
    ! [X11: $i] :
      ( ~ ( v1_pre_topc @ X11 )
      | ( X11
        = ( g1_pre_topc @ ( u1_struct_0 @ X11 ) @ ( u1_pre_topc @ X11 ) ) )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[abstractness_v1_pre_topc])).

thf(dt_u1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( m1_subset_1 @ ( u1_pre_topc @ A ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('11',plain,(
    ! [X20: $i] :
      ( ( m1_subset_1 @ ( u1_pre_topc @ X20 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) ) )
      | ~ ( l1_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_pre_topc])).

thf(free_g1_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ! [C: $i,D: $i] :
          ( ( ( g1_pre_topc @ A @ B )
            = ( g1_pre_topc @ C @ D ) )
         => ( ( A = C )
            & ( B = D ) ) ) ) )).

thf('12',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ( ( g1_pre_topc @ X24 @ X25 )
       != ( g1_pre_topc @ X22 @ X23 ) )
      | ( X24 = X22 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[free_g1_pre_topc])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( u1_struct_0 @ X0 )
        = X1 )
      | ( ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) )
       != ( g1_pre_topc @ X1 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0
       != ( g1_pre_topc @ X2 @ X1 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_pre_topc @ X0 )
      | ( ( u1_struct_0 @ X0 )
        = X2 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','13'])).

thf('15',plain,(
    ! [X1: $i,X2: $i] :
      ( ( ( u1_struct_0 @ ( g1_pre_topc @ X2 @ X1 ) )
        = X2 )
      | ~ ( v1_pre_topc @ ( g1_pre_topc @ X2 @ X1 ) )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ X2 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,
    ( ~ ( v1_pre_topc @ sk_D )
    | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) ) )
    | ( ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) ) )
      = ( u1_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['9','15'])).

thf('17',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) )
    = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ! [X20: $i] :
      ( ( m1_subset_1 @ ( u1_pre_topc @ X20 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) ) )
      | ~ ( l1_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_pre_topc])).

thf(dt_g1_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( v1_pre_topc @ ( g1_pre_topc @ A @ B ) )
        & ( l1_pre_topc @ ( g1_pre_topc @ A @ B ) ) ) ) )).

thf('19',plain,(
    ! [X15: $i,X16: $i] :
      ( ( v1_pre_topc @ ( g1_pre_topc @ X15 @ X16 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_g1_pre_topc])).

thf('20',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( v1_pre_topc @ sk_D )
    | ~ ( l1_pre_topc @ sk_C ) ),
    inference('sup+',[status(thm)],['17','20'])).

thf('22',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('23',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( m1_pre_topc @ X18 @ X19 )
      | ( l1_pre_topc @ X18 )
      | ~ ( l1_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('24',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_C ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    v1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['21','26'])).

thf('28',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) )
    = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( m1_pre_topc @ X18 @ X19 )
      | ( l1_pre_topc @ X18 )
      | ~ ( l1_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('31',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_D ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) )
    = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( u1_struct_0 @ sk_D )
    = ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['16','27','28','33','34'])).

thf('36',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['8','35'])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('37',plain,(
    ! [X14: $i] :
      ( ( ( k2_struct_0 @ X14 )
        = ( u1_struct_0 @ X14 ) )
      | ~ ( l1_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('38',plain,
    ( ( u1_struct_0 @ sk_D )
    = ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['16','27','28','33','34'])).

thf('39',plain,
    ( ( ( k2_struct_0 @ sk_D )
      = ( u1_struct_0 @ sk_C ) )
    | ~ ( l1_struct_0 @ sk_D ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['31','32'])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('41',plain,(
    ! [X17: $i] :
      ( ( l1_struct_0 @ X17 )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('42',plain,(
    l1_struct_0 @ sk_D ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,
    ( ( k2_struct_0 @ sk_D )
    = ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['39','42'])).

thf('44',plain,(
    ! [X14: $i] :
      ( ( ( k2_struct_0 @ X14 )
        = ( u1_struct_0 @ X14 ) )
      | ~ ( l1_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('45',plain,(
    ! [X14: $i] :
      ( ( ( k2_struct_0 @ X14 )
        = ( u1_struct_0 @ X14 ) )
      | ~ ( l1_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('46',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) )
    = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ( ( g1_pre_topc @ ( k2_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) )
      = sk_D )
    | ~ ( l1_struct_0 @ sk_C ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('48',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['24','25'])).

thf('49',plain,(
    ! [X17: $i] :
      ( ( l1_struct_0 @ X17 )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('50',plain,(
    l1_struct_0 @ sk_C ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,
    ( ( g1_pre_topc @ ( k2_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) )
    = sk_D ),
    inference(demod,[status(thm)],['47','50'])).

thf('52',plain,(
    ! [X1: $i,X2: $i] :
      ( ( ( u1_struct_0 @ ( g1_pre_topc @ X2 @ X1 ) )
        = X2 )
      | ~ ( v1_pre_topc @ ( g1_pre_topc @ X2 @ X1 ) )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ X2 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('53',plain,
    ( ~ ( v1_pre_topc @ sk_D )
    | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( k2_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) ) )
    | ( ( u1_struct_0 @ ( g1_pre_topc @ ( k2_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) ) )
      = ( k2_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    v1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['21','26'])).

thf('55',plain,
    ( ( g1_pre_topc @ ( k2_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) )
    = sk_D ),
    inference(demod,[status(thm)],['47','50'])).

thf('56',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['31','32'])).

thf('57',plain,
    ( ( g1_pre_topc @ ( k2_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) )
    = sk_D ),
    inference(demod,[status(thm)],['47','50'])).

thf('58',plain,
    ( ( u1_struct_0 @ sk_D )
    = ( k2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['53','54','55','56','57'])).

thf('59',plain,
    ( ( ( k2_struct_0 @ sk_D )
      = ( k2_struct_0 @ sk_C ) )
    | ~ ( l1_struct_0 @ sk_D ) ),
    inference('sup+',[status(thm)],['44','58'])).

thf('60',plain,(
    l1_struct_0 @ sk_D ),
    inference('sup-',[status(thm)],['40','41'])).

thf('61',plain,
    ( ( k2_struct_0 @ sk_D )
    = ( k2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,
    ( ( k2_struct_0 @ sk_C )
    = ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['43','61'])).

thf('63',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['36','62'])).

thf('64',plain,
    ( ( u1_struct_0 @ sk_D )
    = ( k2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['53','54','55','56','57'])).

thf(t84_tmap_1,axiom,(
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
                                   => ( ( ( v3_pre_topc @ F @ D )
                                        & ( r2_hidden @ G @ F )
                                        & ( r1_tarski @ F @ ( u1_struct_0 @ C ) )
                                        & ( G = H ) )
                                     => ( ( r1_tmap_1 @ D @ B @ E @ G )
                                      <=> ( r1_tmap_1 @ C @ B @ ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ H ) ) ) ) ) ) ) ) ) ) ) ) )).

thf('65',plain,(
    ! [X33: $i,X34: $i,X35: $i,X36: $i,X37: $i,X38: $i,X39: $i,X40: $i] :
      ( ( v2_struct_0 @ X33 )
      | ~ ( v2_pre_topc @ X33 )
      | ~ ( l1_pre_topc @ X33 )
      | ( v2_struct_0 @ X34 )
      | ~ ( m1_pre_topc @ X34 @ X35 )
      | ~ ( m1_pre_topc @ X36 @ X34 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X34 ) ) )
      | ~ ( m1_subset_1 @ X38 @ ( u1_struct_0 @ X36 ) )
      | ~ ( r1_tmap_1 @ X36 @ X33 @ ( k3_tmap_1 @ X35 @ X33 @ X34 @ X36 @ X39 ) @ X38 )
      | ( r1_tmap_1 @ X34 @ X33 @ X39 @ X40 )
      | ( X40 != X38 )
      | ~ ( r1_tarski @ X37 @ ( u1_struct_0 @ X36 ) )
      | ~ ( r2_hidden @ X40 @ X37 )
      | ~ ( v3_pre_topc @ X37 @ X34 )
      | ~ ( m1_subset_1 @ X40 @ ( u1_struct_0 @ X34 ) )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X34 ) @ ( u1_struct_0 @ X33 ) ) ) )
      | ~ ( v1_funct_2 @ X39 @ ( u1_struct_0 @ X34 ) @ ( u1_struct_0 @ X33 ) )
      | ~ ( v1_funct_1 @ X39 )
      | ~ ( m1_pre_topc @ X36 @ X35 )
      | ( v2_struct_0 @ X36 )
      | ~ ( l1_pre_topc @ X35 )
      | ~ ( v2_pre_topc @ X35 )
      | ( v2_struct_0 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t84_tmap_1])).

thf('66',plain,(
    ! [X33: $i,X34: $i,X35: $i,X36: $i,X37: $i,X38: $i,X39: $i] :
      ( ( v2_struct_0 @ X35 )
      | ~ ( v2_pre_topc @ X35 )
      | ~ ( l1_pre_topc @ X35 )
      | ( v2_struct_0 @ X36 )
      | ~ ( m1_pre_topc @ X36 @ X35 )
      | ~ ( v1_funct_1 @ X39 )
      | ~ ( v1_funct_2 @ X39 @ ( u1_struct_0 @ X34 ) @ ( u1_struct_0 @ X33 ) )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X34 ) @ ( u1_struct_0 @ X33 ) ) ) )
      | ~ ( m1_subset_1 @ X38 @ ( u1_struct_0 @ X34 ) )
      | ~ ( v3_pre_topc @ X37 @ X34 )
      | ~ ( r2_hidden @ X38 @ X37 )
      | ~ ( r1_tarski @ X37 @ ( u1_struct_0 @ X36 ) )
      | ( r1_tmap_1 @ X34 @ X33 @ X39 @ X38 )
      | ~ ( r1_tmap_1 @ X36 @ X33 @ ( k3_tmap_1 @ X35 @ X33 @ X34 @ X36 @ X39 ) @ X38 )
      | ~ ( m1_subset_1 @ X38 @ ( u1_struct_0 @ X36 ) )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X34 ) ) )
      | ~ ( m1_pre_topc @ X36 @ X34 )
      | ~ ( m1_pre_topc @ X34 @ X35 )
      | ( v2_struct_0 @ X34 )
      | ~ ( l1_pre_topc @ X33 )
      | ~ ( v2_pre_topc @ X33 )
      | ( v2_struct_0 @ X33 ) ) ),
    inference(simplify,[status(thm)],['65'])).

thf('67',plain,(
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
      | ~ ( r1_tarski @ X4 @ ( u1_struct_0 @ X3 ) )
      | ~ ( r2_hidden @ X5 @ X4 )
      | ~ ( v3_pre_topc @ X4 @ sk_D )
      | ~ ( m1_subset_1 @ X5 @ ( u1_struct_0 @ sk_D ) )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( m1_pre_topc @ X3 @ X2 )
      | ( v2_struct_0 @ X3 )
      | ~ ( l1_pre_topc @ X2 )
      | ~ ( v2_pre_topc @ X2 )
      | ( v2_struct_0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['64','66'])).

thf('68',plain,
    ( ( u1_struct_0 @ sk_D )
    = ( k2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['53','54','55','56','57'])).

thf('69',plain,
    ( ( u1_struct_0 @ sk_D )
    = ( k2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['53','54','55','56','57'])).

thf('70',plain,
    ( ( u1_struct_0 @ sk_D )
    = ( k2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['53','54','55','56','57'])).

thf('71',plain,(
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
      | ~ ( r1_tarski @ X4 @ ( u1_struct_0 @ X3 ) )
      | ~ ( r2_hidden @ X5 @ X4 )
      | ~ ( v3_pre_topc @ X4 @ sk_D )
      | ~ ( m1_subset_1 @ X5 @ ( k2_struct_0 @ sk_C ) )
      | ~ ( v1_funct_2 @ X1 @ ( k2_struct_0 @ sk_C ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( m1_pre_topc @ X3 @ X2 )
      | ( v2_struct_0 @ X3 )
      | ~ ( l1_pre_topc @ X2 )
      | ~ ( v2_pre_topc @ X2 )
      | ( v2_struct_0 @ X2 ) ) ),
    inference(demod,[status(thm)],['67','68','69','70'])).

thf('72',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X1 )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( v1_funct_2 @ sk_E @ ( k2_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( m1_subset_1 @ X2 @ ( k2_struct_0 @ sk_C ) )
      | ~ ( v3_pre_topc @ X3 @ sk_D )
      | ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( r1_tarski @ X3 @ ( u1_struct_0 @ X1 ) )
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
    inference('sup-',[status(thm)],['63','71'])).

thf('73',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,
    ( ( u1_struct_0 @ sk_D )
    = ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['16','27','28','33','34'])).

thf('76',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['74','75'])).

thf('77',plain,
    ( ( k2_struct_0 @ sk_C )
    = ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['43','61'])).

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
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X1 )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ~ ( m1_subset_1 @ X2 @ ( k2_struct_0 @ sk_C ) )
      | ~ ( v3_pre_topc @ X3 @ sk_D )
      | ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( r1_tarski @ X3 @ ( u1_struct_0 @ X1 ) )
      | ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X2 )
      | ~ ( r1_tmap_1 @ X1 @ sk_B @ ( k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E ) @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X1 ) )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_C ) ) )
      | ~ ( m1_pre_topc @ X1 @ sk_D )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['72','73','78','79','80'])).

thf('82',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ~ ( m1_pre_topc @ sk_D @ sk_A )
      | ~ ( m1_pre_topc @ sk_C @ sk_D )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_C ) ) )
      | ~ ( m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_C ) )
      | ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F )
      | ~ ( r1_tarski @ X0 @ ( u1_struct_0 @ sk_C ) )
      | ~ ( r2_hidden @ sk_F @ X0 )
      | ~ ( v3_pre_topc @ X0 @ sk_D )
      | ~ ( m1_subset_1 @ sk_F @ ( k2_struct_0 @ sk_C ) )
      | ~ ( m1_pre_topc @ sk_C @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['7','81'])).

thf('83',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) )
    = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( m1_pre_topc @ A @ A ) ) )).

thf('85',plain,(
    ! [X29: $i] :
      ( ( m1_pre_topc @ X29 @ X29 )
      | ~ ( l1_pre_topc @ X29 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf(t65_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( l1_pre_topc @ B )
         => ( ( m1_pre_topc @ A @ B )
          <=> ( m1_pre_topc @ A @ ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ) )).

thf('86',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( l1_pre_topc @ X26 )
      | ~ ( m1_pre_topc @ X27 @ X26 )
      | ( m1_pre_topc @ X27 @ ( g1_pre_topc @ ( u1_struct_0 @ X26 ) @ ( u1_pre_topc @ X26 ) ) )
      | ~ ( l1_pre_topc @ X27 ) ) ),
    inference(cnf,[status(esa)],[t65_pre_topc])).

thf('87',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['87'])).

thf('89',plain,
    ( ( m1_pre_topc @ sk_C @ sk_D )
    | ~ ( l1_pre_topc @ sk_C ) ),
    inference('sup+',[status(thm)],['84','88'])).

thf('90',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['24','25'])).

thf('91',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(demod,[status(thm)],['89','90'])).

thf('92',plain,
    ( ( k2_struct_0 @ sk_C )
    = ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['43','61'])).

thf('93',plain,(
    ! [X14: $i] :
      ( ( ( k2_struct_0 @ X14 )
        = ( u1_struct_0 @ X14 ) )
      | ~ ( l1_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('94',plain,(
    m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    sk_F = sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['94','95'])).

thf('97',plain,
    ( ( m1_subset_1 @ sk_F @ ( k2_struct_0 @ sk_C ) )
    | ~ ( l1_struct_0 @ sk_C ) ),
    inference('sup+',[status(thm)],['93','96'])).

thf('98',plain,(
    l1_struct_0 @ sk_C ),
    inference('sup-',[status(thm)],['48','49'])).

thf('99',plain,(
    m1_subset_1 @ sk_F @ ( k2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['97','98'])).

thf('100',plain,
    ( ( k2_struct_0 @ sk_C )
    = ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['43','61'])).

thf('101',plain,(
    m1_subset_1 @ sk_F @ ( k2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['97','98'])).

thf('102',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_C ) ) )
      | ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F )
      | ~ ( r1_tarski @ X0 @ ( k2_struct_0 @ sk_C ) )
      | ~ ( r2_hidden @ sk_F @ X0 )
      | ~ ( v3_pre_topc @ X0 @ sk_D )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['82','83','91','92','99','100','101','102','103','104'])).

thf('106',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ~ ( v3_pre_topc @ ( k2_struct_0 @ sk_C ) @ sk_D )
    | ~ ( r2_hidden @ sk_F @ ( k2_struct_0 @ sk_C ) )
    | ~ ( r1_tarski @ ( k2_struct_0 @ sk_C ) @ ( k2_struct_0 @ sk_C ) )
    | ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['4','105'])).

thf('107',plain,
    ( ( k2_struct_0 @ sk_D )
    = ( k2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['59','60'])).

thf(fc10_tops_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( v3_pre_topc @ ( k2_struct_0 @ A ) @ A ) ) )).

thf('108',plain,(
    ! [X28: $i] :
      ( ( v3_pre_topc @ ( k2_struct_0 @ X28 ) @ X28 )
      | ~ ( l1_pre_topc @ X28 )
      | ~ ( v2_pre_topc @ X28 ) ) ),
    inference(cnf,[status(esa)],[fc10_tops_1])).

thf('109',plain,
    ( ( v3_pre_topc @ ( k2_struct_0 @ sk_C ) @ sk_D )
    | ~ ( v2_pre_topc @ sk_D )
    | ~ ( l1_pre_topc @ sk_D ) ),
    inference('sup+',[status(thm)],['107','108'])).

thf('110',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( v2_pre_topc @ B ) ) ) )).

thf('111',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( m1_pre_topc @ X12 @ X13 )
      | ( v2_pre_topc @ X12 )
      | ~ ( l1_pre_topc @ X13 )
      | ~ ( v2_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[cc1_pre_topc])).

thf('112',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_pre_topc @ sk_D ) ),
    inference('sup-',[status(thm)],['110','111'])).

thf('113',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,(
    v2_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['112','113','114'])).

thf('116',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['31','32'])).

thf('117',plain,(
    v3_pre_topc @ ( k2_struct_0 @ sk_C ) @ sk_D ),
    inference(demod,[status(thm)],['109','115','116'])).

thf('118',plain,(
    ! [X14: $i] :
      ( ( ( k2_struct_0 @ X14 )
        = ( u1_struct_0 @ X14 ) )
      | ~ ( l1_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('119',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['94','95'])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('120',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r2_hidden @ X3 @ X4 )
      | ( v1_xboole_0 @ X4 )
      | ~ ( m1_subset_1 @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('121',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) )
    | ( r2_hidden @ sk_F @ ( u1_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['119','120'])).

thf('122',plain,
    ( ( r2_hidden @ sk_F @ ( k2_struct_0 @ sk_C ) )
    | ~ ( l1_struct_0 @ sk_C )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['118','121'])).

thf('123',plain,(
    l1_struct_0 @ sk_C ),
    inference('sup-',[status(thm)],['48','49'])).

thf('124',plain,
    ( ( r2_hidden @ sk_F @ ( k2_struct_0 @ sk_C ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['122','123'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('125',plain,(
    ! [X21: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X21 ) )
      | ~ ( l1_struct_0 @ X21 )
      | ( v2_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('126',plain,
    ( ( r2_hidden @ sk_F @ ( k2_struct_0 @ sk_C ) )
    | ( v2_struct_0 @ sk_C )
    | ~ ( l1_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['124','125'])).

thf('127',plain,(
    l1_struct_0 @ sk_C ),
    inference('sup-',[status(thm)],['48','49'])).

thf('128',plain,
    ( ( r2_hidden @ sk_F @ ( k2_struct_0 @ sk_C ) )
    | ( v2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['126','127'])).

thf('129',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('130',plain,(
    r2_hidden @ sk_F @ ( k2_struct_0 @ sk_C ) ),
    inference(clc,[status(thm)],['128','129'])).

thf('131',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['1'])).

thf('132',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['106','117','130','131'])).

thf('133',plain,(
    ~ ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('134',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['132','133'])).

thf('135',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('136',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['134','135'])).

thf('137',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('138',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C ) ),
    inference(clc,[status(thm)],['136','137'])).

thf('139',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('140',plain,(
    v2_struct_0 @ sk_C ),
    inference(clc,[status(thm)],['138','139'])).

thf('141',plain,(
    $false ),
    inference(demod,[status(thm)],['0','140'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.gYWMKycWV7
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 20:30:56 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 14.58/14.76  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 14.58/14.76  % Solved by: fo/fo7.sh
% 14.58/14.76  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 14.58/14.76  % done 9143 iterations in 14.296s
% 14.58/14.76  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 14.58/14.76  % SZS output start Refutation
% 14.58/14.76  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 14.58/14.76  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 14.58/14.76  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 14.58/14.76  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 14.58/14.76  thf(sk_G_type, type, sk_G: $i).
% 14.58/14.76  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 14.58/14.76  thf(sk_A_type, type, sk_A: $i).
% 14.58/14.76  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 14.58/14.76  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 14.58/14.76  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 14.58/14.76  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 14.58/14.76  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 14.58/14.76  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 14.58/14.76  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 14.58/14.76  thf(sk_B_type, type, sk_B: $i).
% 14.58/14.76  thf(sk_E_type, type, sk_E: $i).
% 14.58/14.76  thf(sk_F_type, type, sk_F: $i).
% 14.58/14.76  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 14.58/14.76  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 14.58/14.76  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 14.58/14.76  thf(sk_D_type, type, sk_D: $i).
% 14.58/14.76  thf(g1_pre_topc_type, type, g1_pre_topc: $i > $i > $i).
% 14.58/14.76  thf(sk_C_type, type, sk_C: $i).
% 14.58/14.76  thf(r1_tmap_1_type, type, r1_tmap_1: $i > $i > $i > $i > $o).
% 14.58/14.76  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 14.58/14.76  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 14.58/14.76  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 14.58/14.76  thf(k3_tmap_1_type, type, k3_tmap_1: $i > $i > $i > $i > $i > $i).
% 14.58/14.76  thf(t88_tmap_1, conjecture,
% 14.58/14.76    (![A:$i]:
% 14.58/14.76     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 14.58/14.76       ( ![B:$i]:
% 14.58/14.76         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 14.58/14.76             ( l1_pre_topc @ B ) ) =>
% 14.58/14.76           ( ![C:$i]:
% 14.58/14.76             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 14.58/14.76               ( ![D:$i]:
% 14.58/14.76                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 14.58/14.76                   ( ![E:$i]:
% 14.58/14.76                     ( ( ( v1_funct_1 @ E ) & 
% 14.58/14.76                         ( v1_funct_2 @
% 14.58/14.76                           E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 14.58/14.76                         ( m1_subset_1 @
% 14.58/14.76                           E @ 
% 14.58/14.76                           ( k1_zfmisc_1 @
% 14.58/14.76                             ( k2_zfmisc_1 @
% 14.58/14.76                               ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 14.58/14.76                       ( ( ( g1_pre_topc @
% 14.58/14.76                             ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) ) =
% 14.58/14.76                           ( D ) ) =>
% 14.58/14.76                         ( ![F:$i]:
% 14.58/14.76                           ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 14.58/14.76                             ( ![G:$i]:
% 14.58/14.76                               ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) ) =>
% 14.58/14.76                                 ( ( ( ( F ) = ( G ) ) & 
% 14.58/14.76                                     ( r1_tmap_1 @
% 14.58/14.76                                       C @ B @ 
% 14.58/14.76                                       ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ G ) ) =>
% 14.58/14.76                                   ( r1_tmap_1 @ D @ B @ E @ F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 14.58/14.76  thf(zf_stmt_0, negated_conjecture,
% 14.58/14.76    (~( ![A:$i]:
% 14.58/14.76        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 14.58/14.76            ( l1_pre_topc @ A ) ) =>
% 14.58/14.76          ( ![B:$i]:
% 14.58/14.76            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 14.58/14.76                ( l1_pre_topc @ B ) ) =>
% 14.58/14.76              ( ![C:$i]:
% 14.58/14.76                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 14.58/14.76                  ( ![D:$i]:
% 14.58/14.76                    ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 14.58/14.76                      ( ![E:$i]:
% 14.58/14.76                        ( ( ( v1_funct_1 @ E ) & 
% 14.58/14.76                            ( v1_funct_2 @
% 14.58/14.76                              E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 14.58/14.76                            ( m1_subset_1 @
% 14.58/14.76                              E @ 
% 14.58/14.76                              ( k1_zfmisc_1 @
% 14.58/14.76                                ( k2_zfmisc_1 @
% 14.58/14.76                                  ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 14.58/14.76                          ( ( ( g1_pre_topc @
% 14.58/14.76                                ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) ) =
% 14.58/14.76                              ( D ) ) =>
% 14.58/14.76                            ( ![F:$i]:
% 14.58/14.76                              ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 14.58/14.76                                ( ![G:$i]:
% 14.58/14.76                                  ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) ) =>
% 14.58/14.76                                    ( ( ( ( F ) = ( G ) ) & 
% 14.58/14.76                                        ( r1_tmap_1 @
% 14.58/14.76                                          C @ B @ 
% 14.58/14.76                                          ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ G ) ) =>
% 14.58/14.76                                      ( r1_tmap_1 @ D @ B @ E @ F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 14.58/14.76    inference('cnf.neg', [status(esa)], [t88_tmap_1])).
% 14.58/14.76  thf('0', plain, (~ (v2_struct_0 @ sk_C)),
% 14.58/14.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.58/14.76  thf(d10_xboole_0, axiom,
% 14.58/14.76    (![A:$i,B:$i]:
% 14.58/14.76     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 14.58/14.76  thf('1', plain,
% 14.58/14.76      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 14.58/14.76      inference('cnf', [status(esa)], [d10_xboole_0])).
% 14.58/14.76  thf('2', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 14.58/14.76      inference('simplify', [status(thm)], ['1'])).
% 14.58/14.76  thf(t3_subset, axiom,
% 14.58/14.76    (![A:$i,B:$i]:
% 14.58/14.76     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 14.58/14.76  thf('3', plain,
% 14.58/14.76      (![X5 : $i, X7 : $i]:
% 14.58/14.76         ((m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X7)) | ~ (r1_tarski @ X5 @ X7))),
% 14.58/14.76      inference('cnf', [status(esa)], [t3_subset])).
% 14.58/14.76  thf('4', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 14.58/14.76      inference('sup-', [status(thm)], ['2', '3'])).
% 14.58/14.76  thf('5', plain,
% 14.58/14.76      ((r1_tmap_1 @ sk_C @ sk_B @ 
% 14.58/14.76        (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_G)),
% 14.58/14.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.58/14.76  thf('6', plain, (((sk_F) = (sk_G))),
% 14.58/14.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.58/14.76  thf('7', plain,
% 14.58/14.76      ((r1_tmap_1 @ sk_C @ sk_B @ 
% 14.58/14.76        (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_F)),
% 14.58/14.76      inference('demod', [status(thm)], ['5', '6'])).
% 14.58/14.76  thf('8', plain,
% 14.58/14.76      ((m1_subset_1 @ sk_E @ 
% 14.58/14.76        (k1_zfmisc_1 @ 
% 14.58/14.76         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 14.58/14.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.58/14.76  thf('9', plain,
% 14.58/14.76      (((g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) = (sk_D))),
% 14.58/14.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.58/14.76  thf(abstractness_v1_pre_topc, axiom,
% 14.58/14.76    (![A:$i]:
% 14.58/14.76     ( ( l1_pre_topc @ A ) =>
% 14.58/14.76       ( ( v1_pre_topc @ A ) =>
% 14.58/14.76         ( ( A ) = ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ))).
% 14.58/14.76  thf('10', plain,
% 14.58/14.76      (![X11 : $i]:
% 14.58/14.76         (~ (v1_pre_topc @ X11)
% 14.58/14.76          | ((X11) = (g1_pre_topc @ (u1_struct_0 @ X11) @ (u1_pre_topc @ X11)))
% 14.58/14.76          | ~ (l1_pre_topc @ X11))),
% 14.58/14.76      inference('cnf', [status(esa)], [abstractness_v1_pre_topc])).
% 14.58/14.76  thf(dt_u1_pre_topc, axiom,
% 14.58/14.76    (![A:$i]:
% 14.58/14.76     ( ( l1_pre_topc @ A ) =>
% 14.58/14.76       ( m1_subset_1 @
% 14.58/14.76         ( u1_pre_topc @ A ) @ 
% 14.58/14.76         ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ))).
% 14.58/14.76  thf('11', plain,
% 14.58/14.76      (![X20 : $i]:
% 14.58/14.76         ((m1_subset_1 @ (u1_pre_topc @ X20) @ 
% 14.58/14.76           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20))))
% 14.58/14.76          | ~ (l1_pre_topc @ X20))),
% 14.58/14.76      inference('cnf', [status(esa)], [dt_u1_pre_topc])).
% 14.58/14.76  thf(free_g1_pre_topc, axiom,
% 14.58/14.76    (![A:$i,B:$i]:
% 14.58/14.76     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 14.58/14.76       ( ![C:$i,D:$i]:
% 14.58/14.76         ( ( ( g1_pre_topc @ A @ B ) = ( g1_pre_topc @ C @ D ) ) =>
% 14.58/14.76           ( ( ( A ) = ( C ) ) & ( ( B ) = ( D ) ) ) ) ) ))).
% 14.58/14.76  thf('12', plain,
% 14.58/14.76      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 14.58/14.76         (((g1_pre_topc @ X24 @ X25) != (g1_pre_topc @ X22 @ X23))
% 14.58/14.76          | ((X24) = (X22))
% 14.58/14.76          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X24))))),
% 14.58/14.76      inference('cnf', [status(esa)], [free_g1_pre_topc])).
% 14.58/14.76  thf('13', plain,
% 14.58/14.76      (![X0 : $i, X1 : $i, X2 : $i]:
% 14.58/14.76         (~ (l1_pre_topc @ X0)
% 14.58/14.76          | ((u1_struct_0 @ X0) = (X1))
% 14.58/14.76          | ((g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))
% 14.58/14.76              != (g1_pre_topc @ X1 @ X2)))),
% 14.58/14.76      inference('sup-', [status(thm)], ['11', '12'])).
% 14.58/14.76  thf('14', plain,
% 14.58/14.76      (![X0 : $i, X1 : $i, X2 : $i]:
% 14.58/14.76         (((X0) != (g1_pre_topc @ X2 @ X1))
% 14.58/14.76          | ~ (l1_pre_topc @ X0)
% 14.58/14.76          | ~ (v1_pre_topc @ X0)
% 14.58/14.76          | ((u1_struct_0 @ X0) = (X2))
% 14.58/14.76          | ~ (l1_pre_topc @ X0))),
% 14.58/14.76      inference('sup-', [status(thm)], ['10', '13'])).
% 14.58/14.76  thf('15', plain,
% 14.58/14.76      (![X1 : $i, X2 : $i]:
% 14.58/14.76         (((u1_struct_0 @ (g1_pre_topc @ X2 @ X1)) = (X2))
% 14.58/14.76          | ~ (v1_pre_topc @ (g1_pre_topc @ X2 @ X1))
% 14.58/14.76          | ~ (l1_pre_topc @ (g1_pre_topc @ X2 @ X1)))),
% 14.58/14.76      inference('simplify', [status(thm)], ['14'])).
% 14.58/14.76  thf('16', plain,
% 14.58/14.76      ((~ (v1_pre_topc @ sk_D)
% 14.58/14.76        | ~ (l1_pre_topc @ 
% 14.58/14.76             (g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)))
% 14.58/14.76        | ((u1_struct_0 @ 
% 14.58/14.76            (g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)))
% 14.58/14.76            = (u1_struct_0 @ sk_C)))),
% 14.58/14.76      inference('sup-', [status(thm)], ['9', '15'])).
% 14.58/14.76  thf('17', plain,
% 14.58/14.76      (((g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) = (sk_D))),
% 14.58/14.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.58/14.76  thf('18', plain,
% 14.58/14.76      (![X20 : $i]:
% 14.58/14.76         ((m1_subset_1 @ (u1_pre_topc @ X20) @ 
% 14.58/14.76           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20))))
% 14.58/14.76          | ~ (l1_pre_topc @ X20))),
% 14.58/14.76      inference('cnf', [status(esa)], [dt_u1_pre_topc])).
% 14.58/14.76  thf(dt_g1_pre_topc, axiom,
% 14.58/14.76    (![A:$i,B:$i]:
% 14.58/14.76     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 14.58/14.76       ( ( v1_pre_topc @ ( g1_pre_topc @ A @ B ) ) & 
% 14.58/14.76         ( l1_pre_topc @ ( g1_pre_topc @ A @ B ) ) ) ))).
% 14.58/14.76  thf('19', plain,
% 14.58/14.76      (![X15 : $i, X16 : $i]:
% 14.58/14.76         ((v1_pre_topc @ (g1_pre_topc @ X15 @ X16))
% 14.58/14.76          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X15))))),
% 14.58/14.76      inference('cnf', [status(esa)], [dt_g1_pre_topc])).
% 14.58/14.76  thf('20', plain,
% 14.58/14.76      (![X0 : $i]:
% 14.58/14.76         (~ (l1_pre_topc @ X0)
% 14.58/14.76          | (v1_pre_topc @ 
% 14.58/14.76             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 14.58/14.76      inference('sup-', [status(thm)], ['18', '19'])).
% 14.58/14.76  thf('21', plain, (((v1_pre_topc @ sk_D) | ~ (l1_pre_topc @ sk_C))),
% 14.58/14.76      inference('sup+', [status(thm)], ['17', '20'])).
% 14.58/14.76  thf('22', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 14.58/14.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.58/14.76  thf(dt_m1_pre_topc, axiom,
% 14.58/14.76    (![A:$i]:
% 14.58/14.76     ( ( l1_pre_topc @ A ) =>
% 14.58/14.76       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 14.58/14.76  thf('23', plain,
% 14.58/14.76      (![X18 : $i, X19 : $i]:
% 14.58/14.76         (~ (m1_pre_topc @ X18 @ X19)
% 14.58/14.76          | (l1_pre_topc @ X18)
% 14.58/14.76          | ~ (l1_pre_topc @ X19))),
% 14.58/14.76      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 14.58/14.76  thf('24', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_C))),
% 14.58/14.76      inference('sup-', [status(thm)], ['22', '23'])).
% 14.58/14.76  thf('25', plain, ((l1_pre_topc @ sk_A)),
% 14.58/14.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.58/14.76  thf('26', plain, ((l1_pre_topc @ sk_C)),
% 14.58/14.76      inference('demod', [status(thm)], ['24', '25'])).
% 14.58/14.76  thf('27', plain, ((v1_pre_topc @ sk_D)),
% 14.58/14.76      inference('demod', [status(thm)], ['21', '26'])).
% 14.58/14.76  thf('28', plain,
% 14.58/14.76      (((g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) = (sk_D))),
% 14.58/14.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.58/14.76  thf('29', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 14.58/14.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.58/14.76  thf('30', plain,
% 14.58/14.76      (![X18 : $i, X19 : $i]:
% 14.58/14.76         (~ (m1_pre_topc @ X18 @ X19)
% 14.58/14.76          | (l1_pre_topc @ X18)
% 14.58/14.76          | ~ (l1_pre_topc @ X19))),
% 14.58/14.76      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 14.58/14.76  thf('31', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_D))),
% 14.58/14.76      inference('sup-', [status(thm)], ['29', '30'])).
% 14.58/14.76  thf('32', plain, ((l1_pre_topc @ sk_A)),
% 14.58/14.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.58/14.76  thf('33', plain, ((l1_pre_topc @ sk_D)),
% 14.58/14.76      inference('demod', [status(thm)], ['31', '32'])).
% 14.58/14.76  thf('34', plain,
% 14.58/14.76      (((g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) = (sk_D))),
% 14.58/14.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.58/14.76  thf('35', plain, (((u1_struct_0 @ sk_D) = (u1_struct_0 @ sk_C))),
% 14.58/14.76      inference('demod', [status(thm)], ['16', '27', '28', '33', '34'])).
% 14.58/14.76  thf('36', plain,
% 14.58/14.76      ((m1_subset_1 @ sk_E @ 
% 14.58/14.76        (k1_zfmisc_1 @ 
% 14.58/14.76         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 14.58/14.76      inference('demod', [status(thm)], ['8', '35'])).
% 14.58/14.76  thf(d3_struct_0, axiom,
% 14.58/14.76    (![A:$i]:
% 14.58/14.76     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 14.58/14.76  thf('37', plain,
% 14.58/14.76      (![X14 : $i]:
% 14.58/14.76         (((k2_struct_0 @ X14) = (u1_struct_0 @ X14)) | ~ (l1_struct_0 @ X14))),
% 14.58/14.76      inference('cnf', [status(esa)], [d3_struct_0])).
% 14.58/14.76  thf('38', plain, (((u1_struct_0 @ sk_D) = (u1_struct_0 @ sk_C))),
% 14.58/14.76      inference('demod', [status(thm)], ['16', '27', '28', '33', '34'])).
% 14.58/14.76  thf('39', plain,
% 14.58/14.76      ((((k2_struct_0 @ sk_D) = (u1_struct_0 @ sk_C)) | ~ (l1_struct_0 @ sk_D))),
% 14.58/14.76      inference('sup+', [status(thm)], ['37', '38'])).
% 14.58/14.76  thf('40', plain, ((l1_pre_topc @ sk_D)),
% 14.58/14.76      inference('demod', [status(thm)], ['31', '32'])).
% 14.58/14.76  thf(dt_l1_pre_topc, axiom,
% 14.58/14.76    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 14.58/14.76  thf('41', plain,
% 14.58/14.76      (![X17 : $i]: ((l1_struct_0 @ X17) | ~ (l1_pre_topc @ X17))),
% 14.58/14.76      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 14.58/14.76  thf('42', plain, ((l1_struct_0 @ sk_D)),
% 14.58/14.76      inference('sup-', [status(thm)], ['40', '41'])).
% 14.58/14.76  thf('43', plain, (((k2_struct_0 @ sk_D) = (u1_struct_0 @ sk_C))),
% 14.58/14.76      inference('demod', [status(thm)], ['39', '42'])).
% 14.58/14.76  thf('44', plain,
% 14.58/14.76      (![X14 : $i]:
% 14.58/14.76         (((k2_struct_0 @ X14) = (u1_struct_0 @ X14)) | ~ (l1_struct_0 @ X14))),
% 14.58/14.76      inference('cnf', [status(esa)], [d3_struct_0])).
% 14.58/14.76  thf('45', plain,
% 14.58/14.76      (![X14 : $i]:
% 14.58/14.76         (((k2_struct_0 @ X14) = (u1_struct_0 @ X14)) | ~ (l1_struct_0 @ X14))),
% 14.58/14.76      inference('cnf', [status(esa)], [d3_struct_0])).
% 14.58/14.76  thf('46', plain,
% 14.58/14.76      (((g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) = (sk_D))),
% 14.58/14.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.58/14.76  thf('47', plain,
% 14.58/14.76      ((((g1_pre_topc @ (k2_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) = (sk_D))
% 14.58/14.76        | ~ (l1_struct_0 @ sk_C))),
% 14.58/14.76      inference('sup+', [status(thm)], ['45', '46'])).
% 14.58/14.76  thf('48', plain, ((l1_pre_topc @ sk_C)),
% 14.58/14.76      inference('demod', [status(thm)], ['24', '25'])).
% 14.58/14.76  thf('49', plain,
% 14.58/14.76      (![X17 : $i]: ((l1_struct_0 @ X17) | ~ (l1_pre_topc @ X17))),
% 14.58/14.76      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 14.58/14.76  thf('50', plain, ((l1_struct_0 @ sk_C)),
% 14.58/14.76      inference('sup-', [status(thm)], ['48', '49'])).
% 14.58/14.76  thf('51', plain,
% 14.58/14.76      (((g1_pre_topc @ (k2_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) = (sk_D))),
% 14.58/14.76      inference('demod', [status(thm)], ['47', '50'])).
% 14.58/14.76  thf('52', plain,
% 14.58/14.76      (![X1 : $i, X2 : $i]:
% 14.58/14.76         (((u1_struct_0 @ (g1_pre_topc @ X2 @ X1)) = (X2))
% 14.58/14.76          | ~ (v1_pre_topc @ (g1_pre_topc @ X2 @ X1))
% 14.58/14.76          | ~ (l1_pre_topc @ (g1_pre_topc @ X2 @ X1)))),
% 14.58/14.76      inference('simplify', [status(thm)], ['14'])).
% 14.58/14.76  thf('53', plain,
% 14.58/14.76      ((~ (v1_pre_topc @ sk_D)
% 14.58/14.76        | ~ (l1_pre_topc @ 
% 14.58/14.76             (g1_pre_topc @ (k2_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)))
% 14.58/14.76        | ((u1_struct_0 @ 
% 14.58/14.76            (g1_pre_topc @ (k2_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)))
% 14.58/14.76            = (k2_struct_0 @ sk_C)))),
% 14.58/14.76      inference('sup-', [status(thm)], ['51', '52'])).
% 14.58/14.76  thf('54', plain, ((v1_pre_topc @ sk_D)),
% 14.58/14.76      inference('demod', [status(thm)], ['21', '26'])).
% 14.58/14.76  thf('55', plain,
% 14.58/14.76      (((g1_pre_topc @ (k2_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) = (sk_D))),
% 14.58/14.76      inference('demod', [status(thm)], ['47', '50'])).
% 14.58/14.76  thf('56', plain, ((l1_pre_topc @ sk_D)),
% 14.58/14.76      inference('demod', [status(thm)], ['31', '32'])).
% 14.58/14.76  thf('57', plain,
% 14.58/14.76      (((g1_pre_topc @ (k2_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) = (sk_D))),
% 14.58/14.76      inference('demod', [status(thm)], ['47', '50'])).
% 14.58/14.76  thf('58', plain, (((u1_struct_0 @ sk_D) = (k2_struct_0 @ sk_C))),
% 14.58/14.76      inference('demod', [status(thm)], ['53', '54', '55', '56', '57'])).
% 14.58/14.76  thf('59', plain,
% 14.58/14.76      ((((k2_struct_0 @ sk_D) = (k2_struct_0 @ sk_C)) | ~ (l1_struct_0 @ sk_D))),
% 14.58/14.76      inference('sup+', [status(thm)], ['44', '58'])).
% 14.58/14.76  thf('60', plain, ((l1_struct_0 @ sk_D)),
% 14.58/14.76      inference('sup-', [status(thm)], ['40', '41'])).
% 14.58/14.76  thf('61', plain, (((k2_struct_0 @ sk_D) = (k2_struct_0 @ sk_C))),
% 14.58/14.76      inference('demod', [status(thm)], ['59', '60'])).
% 14.58/14.76  thf('62', plain, (((k2_struct_0 @ sk_C) = (u1_struct_0 @ sk_C))),
% 14.58/14.76      inference('demod', [status(thm)], ['43', '61'])).
% 14.58/14.76  thf('63', plain,
% 14.58/14.76      ((m1_subset_1 @ sk_E @ 
% 14.58/14.76        (k1_zfmisc_1 @ 
% 14.58/14.76         (k2_zfmisc_1 @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 14.58/14.76      inference('demod', [status(thm)], ['36', '62'])).
% 14.58/14.76  thf('64', plain, (((u1_struct_0 @ sk_D) = (k2_struct_0 @ sk_C))),
% 14.58/14.76      inference('demod', [status(thm)], ['53', '54', '55', '56', '57'])).
% 14.58/14.76  thf(t84_tmap_1, axiom,
% 14.58/14.76    (![A:$i]:
% 14.58/14.76     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 14.58/14.76       ( ![B:$i]:
% 14.58/14.76         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 14.58/14.76             ( l1_pre_topc @ B ) ) =>
% 14.58/14.76           ( ![C:$i]:
% 14.58/14.76             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 14.58/14.76               ( ![D:$i]:
% 14.58/14.76                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 14.58/14.76                   ( ![E:$i]:
% 14.58/14.76                     ( ( ( v1_funct_1 @ E ) & 
% 14.58/14.76                         ( v1_funct_2 @
% 14.58/14.76                           E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 14.58/14.76                         ( m1_subset_1 @
% 14.58/14.76                           E @ 
% 14.58/14.76                           ( k1_zfmisc_1 @
% 14.58/14.76                             ( k2_zfmisc_1 @
% 14.58/14.76                               ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 14.58/14.76                       ( ( m1_pre_topc @ C @ D ) =>
% 14.58/14.76                         ( ![F:$i]:
% 14.58/14.76                           ( ( m1_subset_1 @
% 14.58/14.76                               F @ ( k1_zfmisc_1 @ ( u1_struct_0 @ D ) ) ) =>
% 14.58/14.76                             ( ![G:$i]:
% 14.58/14.76                               ( ( m1_subset_1 @ G @ ( u1_struct_0 @ D ) ) =>
% 14.58/14.76                                 ( ![H:$i]:
% 14.58/14.76                                   ( ( m1_subset_1 @ H @ ( u1_struct_0 @ C ) ) =>
% 14.58/14.76                                     ( ( ( v3_pre_topc @ F @ D ) & 
% 14.58/14.76                                         ( r2_hidden @ G @ F ) & 
% 14.58/14.76                                         ( r1_tarski @ F @ ( u1_struct_0 @ C ) ) & 
% 14.58/14.76                                         ( ( G ) = ( H ) ) ) =>
% 14.58/14.76                                       ( ( r1_tmap_1 @ D @ B @ E @ G ) <=>
% 14.58/14.76                                         ( r1_tmap_1 @
% 14.58/14.76                                           C @ B @ 
% 14.58/14.76                                           ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ 
% 14.58/14.76                                           H ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 14.58/14.76  thf('65', plain,
% 14.58/14.76      (![X33 : $i, X34 : $i, X35 : $i, X36 : $i, X37 : $i, X38 : $i, X39 : $i, 
% 14.58/14.76         X40 : $i]:
% 14.58/14.76         ((v2_struct_0 @ X33)
% 14.58/14.76          | ~ (v2_pre_topc @ X33)
% 14.58/14.76          | ~ (l1_pre_topc @ X33)
% 14.58/14.76          | (v2_struct_0 @ X34)
% 14.58/14.76          | ~ (m1_pre_topc @ X34 @ X35)
% 14.58/14.76          | ~ (m1_pre_topc @ X36 @ X34)
% 14.58/14.76          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (u1_struct_0 @ X34)))
% 14.58/14.76          | ~ (m1_subset_1 @ X38 @ (u1_struct_0 @ X36))
% 14.58/14.76          | ~ (r1_tmap_1 @ X36 @ X33 @ 
% 14.58/14.76               (k3_tmap_1 @ X35 @ X33 @ X34 @ X36 @ X39) @ X38)
% 14.58/14.76          | (r1_tmap_1 @ X34 @ X33 @ X39 @ X40)
% 14.58/14.76          | ((X40) != (X38))
% 14.58/14.76          | ~ (r1_tarski @ X37 @ (u1_struct_0 @ X36))
% 14.58/14.76          | ~ (r2_hidden @ X40 @ X37)
% 14.58/14.76          | ~ (v3_pre_topc @ X37 @ X34)
% 14.58/14.76          | ~ (m1_subset_1 @ X40 @ (u1_struct_0 @ X34))
% 14.58/14.76          | ~ (m1_subset_1 @ X39 @ 
% 14.58/14.76               (k1_zfmisc_1 @ 
% 14.58/14.76                (k2_zfmisc_1 @ (u1_struct_0 @ X34) @ (u1_struct_0 @ X33))))
% 14.58/14.76          | ~ (v1_funct_2 @ X39 @ (u1_struct_0 @ X34) @ (u1_struct_0 @ X33))
% 14.58/14.76          | ~ (v1_funct_1 @ X39)
% 14.58/14.76          | ~ (m1_pre_topc @ X36 @ X35)
% 14.58/14.76          | (v2_struct_0 @ X36)
% 14.58/14.76          | ~ (l1_pre_topc @ X35)
% 14.58/14.76          | ~ (v2_pre_topc @ X35)
% 14.58/14.76          | (v2_struct_0 @ X35))),
% 14.58/14.76      inference('cnf', [status(esa)], [t84_tmap_1])).
% 14.58/14.76  thf('66', plain,
% 14.58/14.76      (![X33 : $i, X34 : $i, X35 : $i, X36 : $i, X37 : $i, X38 : $i, X39 : $i]:
% 14.58/14.76         ((v2_struct_0 @ X35)
% 14.58/14.76          | ~ (v2_pre_topc @ X35)
% 14.58/14.76          | ~ (l1_pre_topc @ X35)
% 14.58/14.76          | (v2_struct_0 @ X36)
% 14.58/14.76          | ~ (m1_pre_topc @ X36 @ X35)
% 14.58/14.76          | ~ (v1_funct_1 @ X39)
% 14.58/14.76          | ~ (v1_funct_2 @ X39 @ (u1_struct_0 @ X34) @ (u1_struct_0 @ X33))
% 14.58/14.76          | ~ (m1_subset_1 @ X39 @ 
% 14.58/14.76               (k1_zfmisc_1 @ 
% 14.58/14.76                (k2_zfmisc_1 @ (u1_struct_0 @ X34) @ (u1_struct_0 @ X33))))
% 14.58/14.76          | ~ (m1_subset_1 @ X38 @ (u1_struct_0 @ X34))
% 14.58/14.76          | ~ (v3_pre_topc @ X37 @ X34)
% 14.58/14.76          | ~ (r2_hidden @ X38 @ X37)
% 14.58/14.76          | ~ (r1_tarski @ X37 @ (u1_struct_0 @ X36))
% 14.58/14.76          | (r1_tmap_1 @ X34 @ X33 @ X39 @ X38)
% 14.58/14.76          | ~ (r1_tmap_1 @ X36 @ X33 @ 
% 14.58/14.76               (k3_tmap_1 @ X35 @ X33 @ X34 @ X36 @ X39) @ X38)
% 14.58/14.76          | ~ (m1_subset_1 @ X38 @ (u1_struct_0 @ X36))
% 14.58/14.76          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (u1_struct_0 @ X34)))
% 14.58/14.76          | ~ (m1_pre_topc @ X36 @ X34)
% 14.58/14.76          | ~ (m1_pre_topc @ X34 @ X35)
% 14.58/14.76          | (v2_struct_0 @ X34)
% 14.58/14.76          | ~ (l1_pre_topc @ X33)
% 14.58/14.76          | ~ (v2_pre_topc @ X33)
% 14.58/14.76          | (v2_struct_0 @ X33))),
% 14.58/14.76      inference('simplify', [status(thm)], ['65'])).
% 14.58/14.76  thf('67', plain,
% 14.58/14.76      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 14.58/14.76         (~ (m1_subset_1 @ X1 @ 
% 14.58/14.76             (k1_zfmisc_1 @ 
% 14.58/14.76              (k2_zfmisc_1 @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ X0))))
% 14.58/14.76          | (v2_struct_0 @ X0)
% 14.58/14.76          | ~ (v2_pre_topc @ X0)
% 14.58/14.76          | ~ (l1_pre_topc @ X0)
% 14.58/14.76          | (v2_struct_0 @ sk_D)
% 14.58/14.76          | ~ (m1_pre_topc @ sk_D @ X2)
% 14.58/14.76          | ~ (m1_pre_topc @ X3 @ sk_D)
% 14.58/14.76          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))
% 14.58/14.76          | ~ (m1_subset_1 @ X5 @ (u1_struct_0 @ X3))
% 14.58/14.76          | ~ (r1_tmap_1 @ X3 @ X0 @ (k3_tmap_1 @ X2 @ X0 @ sk_D @ X3 @ X1) @ 
% 14.58/14.76               X5)
% 14.58/14.76          | (r1_tmap_1 @ sk_D @ X0 @ X1 @ X5)
% 14.58/14.76          | ~ (r1_tarski @ X4 @ (u1_struct_0 @ X3))
% 14.58/14.76          | ~ (r2_hidden @ X5 @ X4)
% 14.58/14.76          | ~ (v3_pre_topc @ X4 @ sk_D)
% 14.58/14.76          | ~ (m1_subset_1 @ X5 @ (u1_struct_0 @ sk_D))
% 14.58/14.76          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ X0))
% 14.58/14.76          | ~ (v1_funct_1 @ X1)
% 14.58/14.76          | ~ (m1_pre_topc @ X3 @ X2)
% 14.58/14.76          | (v2_struct_0 @ X3)
% 14.58/14.76          | ~ (l1_pre_topc @ X2)
% 14.58/14.76          | ~ (v2_pre_topc @ X2)
% 14.58/14.76          | (v2_struct_0 @ X2))),
% 14.58/14.76      inference('sup-', [status(thm)], ['64', '66'])).
% 14.58/14.76  thf('68', plain, (((u1_struct_0 @ sk_D) = (k2_struct_0 @ sk_C))),
% 14.58/14.76      inference('demod', [status(thm)], ['53', '54', '55', '56', '57'])).
% 14.58/14.76  thf('69', plain, (((u1_struct_0 @ sk_D) = (k2_struct_0 @ sk_C))),
% 14.58/14.76      inference('demod', [status(thm)], ['53', '54', '55', '56', '57'])).
% 14.58/14.76  thf('70', plain, (((u1_struct_0 @ sk_D) = (k2_struct_0 @ sk_C))),
% 14.58/14.76      inference('demod', [status(thm)], ['53', '54', '55', '56', '57'])).
% 14.58/14.76  thf('71', plain,
% 14.58/14.76      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 14.58/14.76         (~ (m1_subset_1 @ X1 @ 
% 14.58/14.76             (k1_zfmisc_1 @ 
% 14.58/14.76              (k2_zfmisc_1 @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ X0))))
% 14.58/14.76          | (v2_struct_0 @ X0)
% 14.58/14.76          | ~ (v2_pre_topc @ X0)
% 14.58/14.76          | ~ (l1_pre_topc @ X0)
% 14.58/14.76          | (v2_struct_0 @ sk_D)
% 14.58/14.76          | ~ (m1_pre_topc @ sk_D @ X2)
% 14.58/14.76          | ~ (m1_pre_topc @ X3 @ sk_D)
% 14.58/14.76          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_C)))
% 14.58/14.76          | ~ (m1_subset_1 @ X5 @ (u1_struct_0 @ X3))
% 14.58/14.76          | ~ (r1_tmap_1 @ X3 @ X0 @ (k3_tmap_1 @ X2 @ X0 @ sk_D @ X3 @ X1) @ 
% 14.58/14.76               X5)
% 14.58/14.76          | (r1_tmap_1 @ sk_D @ X0 @ X1 @ X5)
% 14.58/14.76          | ~ (r1_tarski @ X4 @ (u1_struct_0 @ X3))
% 14.58/14.76          | ~ (r2_hidden @ X5 @ X4)
% 14.58/14.76          | ~ (v3_pre_topc @ X4 @ sk_D)
% 14.58/14.76          | ~ (m1_subset_1 @ X5 @ (k2_struct_0 @ sk_C))
% 14.58/14.76          | ~ (v1_funct_2 @ X1 @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ X0))
% 14.58/14.76          | ~ (v1_funct_1 @ X1)
% 14.58/14.76          | ~ (m1_pre_topc @ X3 @ X2)
% 14.58/14.76          | (v2_struct_0 @ X3)
% 14.58/14.76          | ~ (l1_pre_topc @ X2)
% 14.58/14.76          | ~ (v2_pre_topc @ X2)
% 14.58/14.76          | (v2_struct_0 @ X2))),
% 14.58/14.76      inference('demod', [status(thm)], ['67', '68', '69', '70'])).
% 14.58/14.76  thf('72', plain,
% 14.58/14.76      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 14.58/14.76         ((v2_struct_0 @ X0)
% 14.58/14.76          | ~ (v2_pre_topc @ X0)
% 14.58/14.76          | ~ (l1_pre_topc @ X0)
% 14.58/14.76          | (v2_struct_0 @ X1)
% 14.58/14.76          | ~ (m1_pre_topc @ X1 @ X0)
% 14.58/14.76          | ~ (v1_funct_1 @ sk_E)
% 14.58/14.76          | ~ (v1_funct_2 @ sk_E @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))
% 14.58/14.76          | ~ (m1_subset_1 @ X2 @ (k2_struct_0 @ sk_C))
% 14.58/14.76          | ~ (v3_pre_topc @ X3 @ sk_D)
% 14.58/14.76          | ~ (r2_hidden @ X2 @ X3)
% 14.58/14.76          | ~ (r1_tarski @ X3 @ (u1_struct_0 @ X1))
% 14.58/14.76          | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X2)
% 14.58/14.76          | ~ (r1_tmap_1 @ X1 @ sk_B @ 
% 14.58/14.76               (k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E) @ X2)
% 14.58/14.76          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1))
% 14.58/14.76          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_C)))
% 14.58/14.76          | ~ (m1_pre_topc @ X1 @ sk_D)
% 14.58/14.76          | ~ (m1_pre_topc @ sk_D @ X0)
% 14.58/14.76          | (v2_struct_0 @ sk_D)
% 14.58/14.76          | ~ (l1_pre_topc @ sk_B)
% 14.58/14.76          | ~ (v2_pre_topc @ sk_B)
% 14.58/14.76          | (v2_struct_0 @ sk_B))),
% 14.58/14.76      inference('sup-', [status(thm)], ['63', '71'])).
% 14.58/14.76  thf('73', plain, ((v1_funct_1 @ sk_E)),
% 14.58/14.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.58/14.76  thf('74', plain,
% 14.58/14.76      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 14.58/14.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.58/14.76  thf('75', plain, (((u1_struct_0 @ sk_D) = (u1_struct_0 @ sk_C))),
% 14.58/14.76      inference('demod', [status(thm)], ['16', '27', '28', '33', '34'])).
% 14.58/14.76  thf('76', plain,
% 14.58/14.76      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 14.58/14.76      inference('demod', [status(thm)], ['74', '75'])).
% 14.58/14.76  thf('77', plain, (((k2_struct_0 @ sk_C) = (u1_struct_0 @ sk_C))),
% 14.58/14.76      inference('demod', [status(thm)], ['43', '61'])).
% 14.58/14.76  thf('78', plain,
% 14.58/14.76      ((v1_funct_2 @ sk_E @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 14.58/14.76      inference('demod', [status(thm)], ['76', '77'])).
% 14.58/14.76  thf('79', plain, ((l1_pre_topc @ sk_B)),
% 14.58/14.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.58/14.76  thf('80', plain, ((v2_pre_topc @ sk_B)),
% 14.58/14.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.58/14.76  thf('81', plain,
% 14.58/14.76      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 14.58/14.76         ((v2_struct_0 @ X0)
% 14.58/14.76          | ~ (v2_pre_topc @ X0)
% 14.58/14.76          | ~ (l1_pre_topc @ X0)
% 14.58/14.76          | (v2_struct_0 @ X1)
% 14.58/14.76          | ~ (m1_pre_topc @ X1 @ X0)
% 14.58/14.76          | ~ (m1_subset_1 @ X2 @ (k2_struct_0 @ sk_C))
% 14.58/14.76          | ~ (v3_pre_topc @ X3 @ sk_D)
% 14.58/14.76          | ~ (r2_hidden @ X2 @ X3)
% 14.58/14.76          | ~ (r1_tarski @ X3 @ (u1_struct_0 @ X1))
% 14.58/14.76          | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X2)
% 14.58/14.76          | ~ (r1_tmap_1 @ X1 @ sk_B @ 
% 14.58/14.76               (k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E) @ X2)
% 14.58/14.76          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1))
% 14.58/14.76          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_C)))
% 14.58/14.76          | ~ (m1_pre_topc @ X1 @ sk_D)
% 14.58/14.76          | ~ (m1_pre_topc @ sk_D @ X0)
% 14.58/14.76          | (v2_struct_0 @ sk_D)
% 14.58/14.76          | (v2_struct_0 @ sk_B))),
% 14.58/14.76      inference('demod', [status(thm)], ['72', '73', '78', '79', '80'])).
% 14.58/14.76  thf('82', plain,
% 14.58/14.76      (![X0 : $i]:
% 14.58/14.76         ((v2_struct_0 @ sk_B)
% 14.58/14.76          | (v2_struct_0 @ sk_D)
% 14.58/14.76          | ~ (m1_pre_topc @ sk_D @ sk_A)
% 14.58/14.76          | ~ (m1_pre_topc @ sk_C @ sk_D)
% 14.58/14.76          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_C)))
% 14.58/14.76          | ~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C))
% 14.58/14.76          | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)
% 14.58/14.76          | ~ (r1_tarski @ X0 @ (u1_struct_0 @ sk_C))
% 14.58/14.76          | ~ (r2_hidden @ sk_F @ X0)
% 14.58/14.76          | ~ (v3_pre_topc @ X0 @ sk_D)
% 14.58/14.76          | ~ (m1_subset_1 @ sk_F @ (k2_struct_0 @ sk_C))
% 14.58/14.76          | ~ (m1_pre_topc @ sk_C @ sk_A)
% 14.58/14.76          | (v2_struct_0 @ sk_C)
% 14.58/14.76          | ~ (l1_pre_topc @ sk_A)
% 14.58/14.76          | ~ (v2_pre_topc @ sk_A)
% 14.58/14.76          | (v2_struct_0 @ sk_A))),
% 14.58/14.76      inference('sup-', [status(thm)], ['7', '81'])).
% 14.58/14.76  thf('83', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 14.58/14.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.58/14.76  thf('84', plain,
% 14.58/14.76      (((g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) = (sk_D))),
% 14.58/14.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.58/14.76  thf(t2_tsep_1, axiom,
% 14.58/14.76    (![A:$i]: ( ( l1_pre_topc @ A ) => ( m1_pre_topc @ A @ A ) ))).
% 14.58/14.76  thf('85', plain,
% 14.58/14.76      (![X29 : $i]: ((m1_pre_topc @ X29 @ X29) | ~ (l1_pre_topc @ X29))),
% 14.58/14.76      inference('cnf', [status(esa)], [t2_tsep_1])).
% 14.58/14.76  thf(t65_pre_topc, axiom,
% 14.58/14.76    (![A:$i]:
% 14.58/14.76     ( ( l1_pre_topc @ A ) =>
% 14.58/14.76       ( ![B:$i]:
% 14.58/14.76         ( ( l1_pre_topc @ B ) =>
% 14.58/14.76           ( ( m1_pre_topc @ A @ B ) <=>
% 14.58/14.76             ( m1_pre_topc @
% 14.58/14.76               A @ ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ) ))).
% 14.58/14.76  thf('86', plain,
% 14.58/14.76      (![X26 : $i, X27 : $i]:
% 14.58/14.76         (~ (l1_pre_topc @ X26)
% 14.58/14.76          | ~ (m1_pre_topc @ X27 @ X26)
% 14.58/14.76          | (m1_pre_topc @ X27 @ 
% 14.58/14.76             (g1_pre_topc @ (u1_struct_0 @ X26) @ (u1_pre_topc @ X26)))
% 14.58/14.76          | ~ (l1_pre_topc @ X27))),
% 14.58/14.76      inference('cnf', [status(esa)], [t65_pre_topc])).
% 14.58/14.76  thf('87', plain,
% 14.58/14.76      (![X0 : $i]:
% 14.58/14.76         (~ (l1_pre_topc @ X0)
% 14.58/14.76          | ~ (l1_pre_topc @ X0)
% 14.58/14.76          | (m1_pre_topc @ X0 @ 
% 14.58/14.76             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 14.58/14.76          | ~ (l1_pre_topc @ X0))),
% 14.58/14.76      inference('sup-', [status(thm)], ['85', '86'])).
% 14.58/14.76  thf('88', plain,
% 14.58/14.76      (![X0 : $i]:
% 14.58/14.76         ((m1_pre_topc @ X0 @ 
% 14.58/14.76           (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 14.58/14.76          | ~ (l1_pre_topc @ X0))),
% 14.58/14.76      inference('simplify', [status(thm)], ['87'])).
% 14.58/14.76  thf('89', plain, (((m1_pre_topc @ sk_C @ sk_D) | ~ (l1_pre_topc @ sk_C))),
% 14.58/14.76      inference('sup+', [status(thm)], ['84', '88'])).
% 14.58/14.76  thf('90', plain, ((l1_pre_topc @ sk_C)),
% 14.58/14.76      inference('demod', [status(thm)], ['24', '25'])).
% 14.58/14.76  thf('91', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 14.58/14.76      inference('demod', [status(thm)], ['89', '90'])).
% 14.58/14.76  thf('92', plain, (((k2_struct_0 @ sk_C) = (u1_struct_0 @ sk_C))),
% 14.58/14.76      inference('demod', [status(thm)], ['43', '61'])).
% 14.58/14.76  thf('93', plain,
% 14.58/14.76      (![X14 : $i]:
% 14.58/14.76         (((k2_struct_0 @ X14) = (u1_struct_0 @ X14)) | ~ (l1_struct_0 @ X14))),
% 14.58/14.76      inference('cnf', [status(esa)], [d3_struct_0])).
% 14.58/14.76  thf('94', plain, ((m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_C))),
% 14.58/14.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.58/14.76  thf('95', plain, (((sk_F) = (sk_G))),
% 14.58/14.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.58/14.76  thf('96', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C))),
% 14.58/14.76      inference('demod', [status(thm)], ['94', '95'])).
% 14.58/14.76  thf('97', plain,
% 14.58/14.76      (((m1_subset_1 @ sk_F @ (k2_struct_0 @ sk_C)) | ~ (l1_struct_0 @ sk_C))),
% 14.58/14.76      inference('sup+', [status(thm)], ['93', '96'])).
% 14.58/14.76  thf('98', plain, ((l1_struct_0 @ sk_C)),
% 14.58/14.76      inference('sup-', [status(thm)], ['48', '49'])).
% 14.58/14.76  thf('99', plain, ((m1_subset_1 @ sk_F @ (k2_struct_0 @ sk_C))),
% 14.58/14.76      inference('demod', [status(thm)], ['97', '98'])).
% 14.58/14.76  thf('100', plain, (((k2_struct_0 @ sk_C) = (u1_struct_0 @ sk_C))),
% 14.58/14.76      inference('demod', [status(thm)], ['43', '61'])).
% 14.58/14.76  thf('101', plain, ((m1_subset_1 @ sk_F @ (k2_struct_0 @ sk_C))),
% 14.58/14.76      inference('demod', [status(thm)], ['97', '98'])).
% 14.58/14.76  thf('102', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 14.58/14.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.58/14.76  thf('103', plain, ((l1_pre_topc @ sk_A)),
% 14.58/14.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.58/14.76  thf('104', plain, ((v2_pre_topc @ sk_A)),
% 14.58/14.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.58/14.76  thf('105', plain,
% 14.58/14.76      (![X0 : $i]:
% 14.58/14.76         ((v2_struct_0 @ sk_B)
% 14.58/14.76          | (v2_struct_0 @ sk_D)
% 14.58/14.76          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_C)))
% 14.58/14.76          | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)
% 14.58/14.76          | ~ (r1_tarski @ X0 @ (k2_struct_0 @ sk_C))
% 14.58/14.76          | ~ (r2_hidden @ sk_F @ X0)
% 14.58/14.76          | ~ (v3_pre_topc @ X0 @ sk_D)
% 14.58/14.76          | (v2_struct_0 @ sk_C)
% 14.58/14.76          | (v2_struct_0 @ sk_A))),
% 14.58/14.76      inference('demod', [status(thm)],
% 14.58/14.76                ['82', '83', '91', '92', '99', '100', '101', '102', '103', 
% 14.58/14.76                 '104'])).
% 14.58/14.76  thf('106', plain,
% 14.58/14.76      (((v2_struct_0 @ sk_A)
% 14.58/14.76        | (v2_struct_0 @ sk_C)
% 14.58/14.76        | ~ (v3_pre_topc @ (k2_struct_0 @ sk_C) @ sk_D)
% 14.58/14.76        | ~ (r2_hidden @ sk_F @ (k2_struct_0 @ sk_C))
% 14.58/14.76        | ~ (r1_tarski @ (k2_struct_0 @ sk_C) @ (k2_struct_0 @ sk_C))
% 14.58/14.76        | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)
% 14.58/14.76        | (v2_struct_0 @ sk_D)
% 14.58/14.76        | (v2_struct_0 @ sk_B))),
% 14.58/14.76      inference('sup-', [status(thm)], ['4', '105'])).
% 14.58/14.76  thf('107', plain, (((k2_struct_0 @ sk_D) = (k2_struct_0 @ sk_C))),
% 14.58/14.76      inference('demod', [status(thm)], ['59', '60'])).
% 14.58/14.76  thf(fc10_tops_1, axiom,
% 14.58/14.76    (![A:$i]:
% 14.58/14.76     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 14.58/14.76       ( v3_pre_topc @ ( k2_struct_0 @ A ) @ A ) ))).
% 14.58/14.76  thf('108', plain,
% 14.58/14.76      (![X28 : $i]:
% 14.58/14.76         ((v3_pre_topc @ (k2_struct_0 @ X28) @ X28)
% 14.58/14.76          | ~ (l1_pre_topc @ X28)
% 14.58/14.76          | ~ (v2_pre_topc @ X28))),
% 14.58/14.76      inference('cnf', [status(esa)], [fc10_tops_1])).
% 14.58/14.76  thf('109', plain,
% 14.58/14.76      (((v3_pre_topc @ (k2_struct_0 @ sk_C) @ sk_D)
% 14.58/14.76        | ~ (v2_pre_topc @ sk_D)
% 14.58/14.76        | ~ (l1_pre_topc @ sk_D))),
% 14.58/14.76      inference('sup+', [status(thm)], ['107', '108'])).
% 14.58/14.76  thf('110', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 14.58/14.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.58/14.76  thf(cc1_pre_topc, axiom,
% 14.58/14.76    (![A:$i]:
% 14.58/14.76     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 14.58/14.76       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( v2_pre_topc @ B ) ) ) ))).
% 14.58/14.76  thf('111', plain,
% 14.58/14.76      (![X12 : $i, X13 : $i]:
% 14.58/14.76         (~ (m1_pre_topc @ X12 @ X13)
% 14.58/14.76          | (v2_pre_topc @ X12)
% 14.58/14.76          | ~ (l1_pre_topc @ X13)
% 14.58/14.76          | ~ (v2_pre_topc @ X13))),
% 14.58/14.76      inference('cnf', [status(esa)], [cc1_pre_topc])).
% 14.58/14.76  thf('112', plain,
% 14.58/14.76      ((~ (v2_pre_topc @ sk_A) | ~ (l1_pre_topc @ sk_A) | (v2_pre_topc @ sk_D))),
% 14.58/14.76      inference('sup-', [status(thm)], ['110', '111'])).
% 14.58/14.76  thf('113', plain, ((v2_pre_topc @ sk_A)),
% 14.58/14.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.58/14.76  thf('114', plain, ((l1_pre_topc @ sk_A)),
% 14.58/14.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.58/14.76  thf('115', plain, ((v2_pre_topc @ sk_D)),
% 14.58/14.76      inference('demod', [status(thm)], ['112', '113', '114'])).
% 14.58/14.76  thf('116', plain, ((l1_pre_topc @ sk_D)),
% 14.58/14.76      inference('demod', [status(thm)], ['31', '32'])).
% 14.58/14.76  thf('117', plain, ((v3_pre_topc @ (k2_struct_0 @ sk_C) @ sk_D)),
% 14.58/14.76      inference('demod', [status(thm)], ['109', '115', '116'])).
% 14.58/14.76  thf('118', plain,
% 14.58/14.76      (![X14 : $i]:
% 14.58/14.76         (((k2_struct_0 @ X14) = (u1_struct_0 @ X14)) | ~ (l1_struct_0 @ X14))),
% 14.58/14.76      inference('cnf', [status(esa)], [d3_struct_0])).
% 14.58/14.76  thf('119', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C))),
% 14.58/14.76      inference('demod', [status(thm)], ['94', '95'])).
% 14.58/14.76  thf(t2_subset, axiom,
% 14.58/14.76    (![A:$i,B:$i]:
% 14.58/14.76     ( ( m1_subset_1 @ A @ B ) =>
% 14.58/14.76       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 14.58/14.76  thf('120', plain,
% 14.58/14.76      (![X3 : $i, X4 : $i]:
% 14.58/14.76         ((r2_hidden @ X3 @ X4)
% 14.58/14.76          | (v1_xboole_0 @ X4)
% 14.58/14.76          | ~ (m1_subset_1 @ X3 @ X4))),
% 14.58/14.76      inference('cnf', [status(esa)], [t2_subset])).
% 14.58/14.76  thf('121', plain,
% 14.58/14.76      (((v1_xboole_0 @ (u1_struct_0 @ sk_C))
% 14.58/14.76        | (r2_hidden @ sk_F @ (u1_struct_0 @ sk_C)))),
% 14.58/14.76      inference('sup-', [status(thm)], ['119', '120'])).
% 14.58/14.76  thf('122', plain,
% 14.58/14.76      (((r2_hidden @ sk_F @ (k2_struct_0 @ sk_C))
% 14.58/14.76        | ~ (l1_struct_0 @ sk_C)
% 14.58/14.76        | (v1_xboole_0 @ (u1_struct_0 @ sk_C)))),
% 14.58/14.76      inference('sup+', [status(thm)], ['118', '121'])).
% 14.58/14.76  thf('123', plain, ((l1_struct_0 @ sk_C)),
% 14.58/14.76      inference('sup-', [status(thm)], ['48', '49'])).
% 14.58/14.76  thf('124', plain,
% 14.58/14.76      (((r2_hidden @ sk_F @ (k2_struct_0 @ sk_C))
% 14.58/14.76        | (v1_xboole_0 @ (u1_struct_0 @ sk_C)))),
% 14.58/14.76      inference('demod', [status(thm)], ['122', '123'])).
% 14.58/14.76  thf(fc2_struct_0, axiom,
% 14.58/14.76    (![A:$i]:
% 14.58/14.76     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 14.58/14.76       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 14.58/14.76  thf('125', plain,
% 14.58/14.76      (![X21 : $i]:
% 14.58/14.76         (~ (v1_xboole_0 @ (u1_struct_0 @ X21))
% 14.58/14.76          | ~ (l1_struct_0 @ X21)
% 14.58/14.76          | (v2_struct_0 @ X21))),
% 14.58/14.76      inference('cnf', [status(esa)], [fc2_struct_0])).
% 14.58/14.76  thf('126', plain,
% 14.58/14.76      (((r2_hidden @ sk_F @ (k2_struct_0 @ sk_C))
% 14.58/14.76        | (v2_struct_0 @ sk_C)
% 14.58/14.76        | ~ (l1_struct_0 @ sk_C))),
% 14.58/14.76      inference('sup-', [status(thm)], ['124', '125'])).
% 14.58/14.76  thf('127', plain, ((l1_struct_0 @ sk_C)),
% 14.58/14.76      inference('sup-', [status(thm)], ['48', '49'])).
% 14.58/14.76  thf('128', plain,
% 14.58/14.76      (((r2_hidden @ sk_F @ (k2_struct_0 @ sk_C)) | (v2_struct_0 @ sk_C))),
% 14.58/14.76      inference('demod', [status(thm)], ['126', '127'])).
% 14.58/14.76  thf('129', plain, (~ (v2_struct_0 @ sk_C)),
% 14.58/14.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.58/14.76  thf('130', plain, ((r2_hidden @ sk_F @ (k2_struct_0 @ sk_C))),
% 14.58/14.76      inference('clc', [status(thm)], ['128', '129'])).
% 14.58/14.76  thf('131', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 14.58/14.76      inference('simplify', [status(thm)], ['1'])).
% 14.58/14.76  thf('132', plain,
% 14.58/14.76      (((v2_struct_0 @ sk_A)
% 14.58/14.76        | (v2_struct_0 @ sk_C)
% 14.58/14.76        | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)
% 14.58/14.76        | (v2_struct_0 @ sk_D)
% 14.58/14.76        | (v2_struct_0 @ sk_B))),
% 14.58/14.76      inference('demod', [status(thm)], ['106', '117', '130', '131'])).
% 14.58/14.76  thf('133', plain, (~ (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)),
% 14.58/14.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.58/14.76  thf('134', plain,
% 14.58/14.76      (((v2_struct_0 @ sk_B)
% 14.58/14.76        | (v2_struct_0 @ sk_D)
% 14.58/14.76        | (v2_struct_0 @ sk_C)
% 14.58/14.76        | (v2_struct_0 @ sk_A))),
% 14.58/14.76      inference('sup-', [status(thm)], ['132', '133'])).
% 14.58/14.76  thf('135', plain, (~ (v2_struct_0 @ sk_D)),
% 14.58/14.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.58/14.76  thf('136', plain,
% 14.58/14.76      (((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_B))),
% 14.58/14.76      inference('sup-', [status(thm)], ['134', '135'])).
% 14.58/14.76  thf('137', plain, (~ (v2_struct_0 @ sk_A)),
% 14.58/14.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.58/14.76  thf('138', plain, (((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_C))),
% 14.58/14.76      inference('clc', [status(thm)], ['136', '137'])).
% 14.58/14.76  thf('139', plain, (~ (v2_struct_0 @ sk_B)),
% 14.58/14.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.58/14.76  thf('140', plain, ((v2_struct_0 @ sk_C)),
% 14.58/14.76      inference('clc', [status(thm)], ['138', '139'])).
% 14.58/14.76  thf('141', plain, ($false), inference('demod', [status(thm)], ['0', '140'])).
% 14.58/14.76  
% 14.58/14.76  % SZS output end Refutation
% 14.58/14.76  
% 14.58/14.77  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
