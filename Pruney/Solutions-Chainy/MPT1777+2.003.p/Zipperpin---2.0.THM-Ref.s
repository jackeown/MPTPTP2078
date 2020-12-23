%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.WTzJZFkh2Q

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:10:26 EST 2020

% Result     : Theorem 22.60s
% Output     : Refutation 22.60s
% Verified   : 
% Statistics : Number of formulae       :  218 (3866 expanded)
%              Number of leaves         :   47 (1131 expanded)
%              Depth                    :   29
%              Number of atoms          : 1886 (96902 expanded)
%              Number of equality atoms :   77 (3374 expanded)
%              Maximal formula depth    :   32 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k3_tmap_1_type,type,(
    k3_tmap_1: $i > $i > $i > $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(m1_connsp_2_type,type,(
    m1_connsp_2: $i > $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(r1_tmap_1_type,type,(
    r1_tmap_1: $i > $i > $i > $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(sk_G_type,type,(
    sk_G: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(g1_pre_topc_type,type,(
    g1_pre_topc: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

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

thf('11',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) )
    = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_u1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( m1_subset_1 @ ( u1_pre_topc @ A ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('12',plain,(
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

thf('13',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ( ( g1_pre_topc @ X24 @ X25 )
       != ( g1_pre_topc @ X22 @ X23 ) )
      | ( X25 = X23 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[free_g1_pre_topc])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( u1_pre_topc @ X0 )
        = X1 )
      | ( ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) )
       != ( g1_pre_topc @ X2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( sk_D
       != ( g1_pre_topc @ X1 @ X0 ) )
      | ( ( u1_pre_topc @ sk_C )
        = X0 )
      | ~ ( l1_pre_topc @ sk_C ) ) ),
    inference('sup-',[status(thm)],['11','14'])).

thf('16',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('17',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( m1_pre_topc @ X18 @ X19 )
      | ( l1_pre_topc @ X18 )
      | ~ ( l1_pre_topc @ X19 ) ) ),
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
    ! [X0: $i,X1: $i] :
      ( ( sk_D
       != ( g1_pre_topc @ X1 @ X0 ) )
      | ( ( u1_pre_topc @ sk_C )
        = X0 ) ) ),
    inference(demod,[status(thm)],['15','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( sk_D != X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_pre_topc @ X0 )
      | ( ( u1_pre_topc @ sk_C )
        = ( u1_pre_topc @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['10','21'])).

thf('23',plain,
    ( ( ( u1_pre_topc @ sk_C )
      = ( u1_pre_topc @ sk_D ) )
    | ~ ( v1_pre_topc @ sk_D )
    | ~ ( l1_pre_topc @ sk_D ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( m1_pre_topc @ X18 @ X19 )
      | ( l1_pre_topc @ X18 )
      | ~ ( l1_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('26',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_D ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) )
    = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    ! [X20: $i] :
      ( ( m1_subset_1 @ ( u1_pre_topc @ X20 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) ) )
      | ~ ( l1_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_pre_topc])).

thf(dt_g1_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( v1_pre_topc @ ( g1_pre_topc @ A @ B ) )
        & ( l1_pre_topc @ ( g1_pre_topc @ A @ B ) ) ) ) )).

thf('31',plain,(
    ! [X15: $i,X16: $i] :
      ( ( v1_pre_topc @ ( g1_pre_topc @ X15 @ X16 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_g1_pre_topc])).

thf('32',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,
    ( ( v1_pre_topc @ sk_D )
    | ~ ( l1_pre_topc @ sk_C ) ),
    inference('sup+',[status(thm)],['29','32'])).

thf('34',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['18','19'])).

thf('35',plain,(
    v1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,
    ( ( u1_pre_topc @ sk_C )
    = ( u1_pre_topc @ sk_D ) ),
    inference('simplify_reflect+',[status(thm)],['23','28','35'])).

thf('37',plain,(
    ! [X20: $i] :
      ( ( m1_subset_1 @ ( u1_pre_topc @ X20 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) ) )
      | ~ ( l1_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_pre_topc])).

thf('38',plain,
    ( ( m1_subset_1 @ ( u1_pre_topc @ sk_C ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) ) )
    | ~ ( l1_pre_topc @ sk_D ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('39',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['26','27'])).

thf('40',plain,(
    m1_subset_1 @ ( u1_pre_topc @ sk_C ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ( ( g1_pre_topc @ X24 @ X25 )
       != ( g1_pre_topc @ X22 @ X23 ) )
      | ( X24 = X22 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[free_g1_pre_topc])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( u1_struct_0 @ sk_D )
        = X0 )
      | ( ( g1_pre_topc @ ( u1_struct_0 @ sk_D ) @ ( u1_pre_topc @ sk_C ) )
       != ( g1_pre_topc @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,
    ( ( u1_pre_topc @ sk_C )
    = ( u1_pre_topc @ sk_D ) ),
    inference('simplify_reflect+',[status(thm)],['23','28','35'])).

thf('44',plain,(
    ! [X11: $i] :
      ( ~ ( v1_pre_topc @ X11 )
      | ( X11
        = ( g1_pre_topc @ ( u1_struct_0 @ X11 ) @ ( u1_pre_topc @ X11 ) ) )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[abstractness_v1_pre_topc])).

thf('45',plain,
    ( ( sk_D
      = ( g1_pre_topc @ ( u1_struct_0 @ sk_D ) @ ( u1_pre_topc @ sk_C ) ) )
    | ~ ( l1_pre_topc @ sk_D )
    | ~ ( v1_pre_topc @ sk_D ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('46',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['26','27'])).

thf('47',plain,(
    v1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['33','34'])).

thf('48',plain,
    ( sk_D
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_D ) @ ( u1_pre_topc @ sk_C ) ) ),
    inference(demod,[status(thm)],['45','46','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( u1_struct_0 @ sk_D )
        = X0 )
      | ( sk_D
       != ( g1_pre_topc @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['42','48'])).

thf('50',plain,
    ( ( sk_D != sk_D )
    | ( ( u1_struct_0 @ sk_D )
      = ( u1_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['9','49'])).

thf('51',plain,
    ( ( u1_struct_0 @ sk_D )
    = ( u1_struct_0 @ sk_C ) ),
    inference(simplify,[status(thm)],['50'])).

thf('52',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['8','51'])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('53',plain,(
    ! [X14: $i] :
      ( ( ( k2_struct_0 @ X14 )
        = ( u1_struct_0 @ X14 ) )
      | ~ ( l1_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('54',plain,
    ( ( u1_struct_0 @ sk_D )
    = ( u1_struct_0 @ sk_C ) ),
    inference(simplify,[status(thm)],['50'])).

thf('55',plain,
    ( ( ( k2_struct_0 @ sk_D )
      = ( u1_struct_0 @ sk_C ) )
    | ~ ( l1_struct_0 @ sk_D ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf('56',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['26','27'])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('57',plain,(
    ! [X17: $i] :
      ( ( l1_struct_0 @ X17 )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('58',plain,(
    l1_struct_0 @ sk_D ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,
    ( ( k2_struct_0 @ sk_D )
    = ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['55','58'])).

thf('60',plain,(
    ! [X14: $i] :
      ( ( ( k2_struct_0 @ X14 )
        = ( u1_struct_0 @ X14 ) )
      | ~ ( l1_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('61',plain,(
    ! [X14: $i] :
      ( ( ( k2_struct_0 @ X14 )
        = ( u1_struct_0 @ X14 ) )
      | ~ ( l1_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('62',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) )
    = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,
    ( ( ( g1_pre_topc @ ( k2_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) )
      = sk_D )
    | ~ ( l1_struct_0 @ sk_C ) ),
    inference('sup+',[status(thm)],['61','62'])).

thf('64',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['18','19'])).

thf('65',plain,(
    ! [X17: $i] :
      ( ( l1_struct_0 @ X17 )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('66',plain,(
    l1_struct_0 @ sk_C ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,
    ( ( g1_pre_topc @ ( k2_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) )
    = sk_D ),
    inference(demod,[status(thm)],['63','66'])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( u1_struct_0 @ sk_D )
        = X0 )
      | ( sk_D
       != ( g1_pre_topc @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['42','48'])).

thf('69',plain,
    ( ( sk_D != sk_D )
    | ( ( u1_struct_0 @ sk_D )
      = ( k2_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,
    ( ( u1_struct_0 @ sk_D )
    = ( k2_struct_0 @ sk_C ) ),
    inference(simplify,[status(thm)],['69'])).

thf('71',plain,
    ( ( ( k2_struct_0 @ sk_D )
      = ( k2_struct_0 @ sk_C ) )
    | ~ ( l1_struct_0 @ sk_D ) ),
    inference('sup+',[status(thm)],['60','70'])).

thf('72',plain,(
    l1_struct_0 @ sk_D ),
    inference('sup-',[status(thm)],['56','57'])).

thf('73',plain,
    ( ( k2_struct_0 @ sk_D )
    = ( k2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('74',plain,
    ( ( k2_struct_0 @ sk_C )
    = ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['59','73'])).

thf('75',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['52','74'])).

thf('76',plain,
    ( ( u1_struct_0 @ sk_D )
    = ( k2_struct_0 @ sk_C ) ),
    inference(simplify,[status(thm)],['69'])).

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

thf('77',plain,(
    ! [X36: $i,X37: $i,X38: $i,X39: $i,X40: $i,X41: $i,X42: $i,X43: $i] :
      ( ( v2_struct_0 @ X36 )
      | ~ ( v2_pre_topc @ X36 )
      | ~ ( l1_pre_topc @ X36 )
      | ( v2_struct_0 @ X37 )
      | ~ ( m1_pre_topc @ X37 @ X38 )
      | ~ ( m1_pre_topc @ X39 @ X37 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X37 ) ) )
      | ~ ( m1_subset_1 @ X41 @ ( u1_struct_0 @ X39 ) )
      | ~ ( r1_tmap_1 @ X39 @ X36 @ ( k3_tmap_1 @ X38 @ X36 @ X37 @ X39 @ X42 ) @ X41 )
      | ( r1_tmap_1 @ X37 @ X36 @ X42 @ X43 )
      | ( X43 != X41 )
      | ~ ( m1_connsp_2 @ X40 @ X37 @ X43 )
      | ~ ( r1_tarski @ X40 @ ( u1_struct_0 @ X39 ) )
      | ~ ( m1_subset_1 @ X43 @ ( u1_struct_0 @ X37 ) )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X37 ) @ ( u1_struct_0 @ X36 ) ) ) )
      | ~ ( v1_funct_2 @ X42 @ ( u1_struct_0 @ X37 ) @ ( u1_struct_0 @ X36 ) )
      | ~ ( v1_funct_1 @ X42 )
      | ~ ( m1_pre_topc @ X39 @ X38 )
      | ( v2_struct_0 @ X39 )
      | ~ ( l1_pre_topc @ X38 )
      | ~ ( v2_pre_topc @ X38 )
      | ( v2_struct_0 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t83_tmap_1])).

thf('78',plain,(
    ! [X36: $i,X37: $i,X38: $i,X39: $i,X40: $i,X41: $i,X42: $i] :
      ( ( v2_struct_0 @ X38 )
      | ~ ( v2_pre_topc @ X38 )
      | ~ ( l1_pre_topc @ X38 )
      | ( v2_struct_0 @ X39 )
      | ~ ( m1_pre_topc @ X39 @ X38 )
      | ~ ( v1_funct_1 @ X42 )
      | ~ ( v1_funct_2 @ X42 @ ( u1_struct_0 @ X37 ) @ ( u1_struct_0 @ X36 ) )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X37 ) @ ( u1_struct_0 @ X36 ) ) ) )
      | ~ ( m1_subset_1 @ X41 @ ( u1_struct_0 @ X37 ) )
      | ~ ( r1_tarski @ X40 @ ( u1_struct_0 @ X39 ) )
      | ~ ( m1_connsp_2 @ X40 @ X37 @ X41 )
      | ( r1_tmap_1 @ X37 @ X36 @ X42 @ X41 )
      | ~ ( r1_tmap_1 @ X39 @ X36 @ ( k3_tmap_1 @ X38 @ X36 @ X37 @ X39 @ X42 ) @ X41 )
      | ~ ( m1_subset_1 @ X41 @ ( u1_struct_0 @ X39 ) )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X37 ) ) )
      | ~ ( m1_pre_topc @ X39 @ X37 )
      | ~ ( m1_pre_topc @ X37 @ X38 )
      | ( v2_struct_0 @ X37 )
      | ~ ( l1_pre_topc @ X36 )
      | ~ ( v2_pre_topc @ X36 )
      | ( v2_struct_0 @ X36 ) ) ),
    inference(simplify,[status(thm)],['77'])).

thf('79',plain,(
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
    inference('sup-',[status(thm)],['76','78'])).

thf('80',plain,
    ( ( u1_struct_0 @ sk_D )
    = ( k2_struct_0 @ sk_C ) ),
    inference(simplify,[status(thm)],['69'])).

thf('81',plain,
    ( ( u1_struct_0 @ sk_D )
    = ( k2_struct_0 @ sk_C ) ),
    inference(simplify,[status(thm)],['69'])).

thf('82',plain,
    ( ( u1_struct_0 @ sk_D )
    = ( k2_struct_0 @ sk_C ) ),
    inference(simplify,[status(thm)],['69'])).

thf('83',plain,(
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
    inference(demod,[status(thm)],['79','80','81','82'])).

thf('84',plain,(
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
    inference('sup-',[status(thm)],['75','83'])).

thf('85',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,
    ( ( u1_struct_0 @ sk_D )
    = ( u1_struct_0 @ sk_C ) ),
    inference(simplify,[status(thm)],['50'])).

thf('88',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['86','87'])).

thf('89',plain,
    ( ( k2_struct_0 @ sk_C )
    = ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['59','73'])).

thf('90',plain,(
    v1_funct_2 @ sk_E @ ( k2_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['88','89'])).

thf('91',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
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
    inference(demod,[status(thm)],['84','85','90','91','92'])).

thf('94',plain,(
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
    inference('sup-',[status(thm)],['7','93'])).

thf('95',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) )
    = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( m1_pre_topc @ A @ A ) ) )).

thf('97',plain,(
    ! [X32: $i] :
      ( ( m1_pre_topc @ X32 @ X32 )
      | ~ ( l1_pre_topc @ X32 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf(t65_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( l1_pre_topc @ B )
         => ( ( m1_pre_topc @ A @ B )
          <=> ( m1_pre_topc @ A @ ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ) )).

thf('98',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( l1_pre_topc @ X26 )
      | ~ ( m1_pre_topc @ X27 @ X26 )
      | ( m1_pre_topc @ X27 @ ( g1_pre_topc @ ( u1_struct_0 @ X26 ) @ ( u1_pre_topc @ X26 ) ) )
      | ~ ( l1_pre_topc @ X27 ) ) ),
    inference(cnf,[status(esa)],[t65_pre_topc])).

thf('99',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['99'])).

thf('101',plain,
    ( ( m1_pre_topc @ sk_C @ sk_D )
    | ~ ( l1_pre_topc @ sk_C ) ),
    inference('sup+',[status(thm)],['96','100'])).

thf('102',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['18','19'])).

thf('103',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(demod,[status(thm)],['101','102'])).

thf('104',plain,
    ( ( k2_struct_0 @ sk_C )
    = ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['59','73'])).

thf('105',plain,(
    ! [X14: $i] :
      ( ( ( k2_struct_0 @ X14 )
        = ( u1_struct_0 @ X14 ) )
      | ~ ( l1_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('106',plain,(
    m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,(
    sk_F = sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['106','107'])).

thf('109',plain,
    ( ( m1_subset_1 @ sk_F @ ( k2_struct_0 @ sk_C ) )
    | ~ ( l1_struct_0 @ sk_C ) ),
    inference('sup+',[status(thm)],['105','108'])).

thf('110',plain,(
    l1_struct_0 @ sk_C ),
    inference('sup-',[status(thm)],['64','65'])).

thf('111',plain,(
    m1_subset_1 @ sk_F @ ( k2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['109','110'])).

thf('112',plain,
    ( ( k2_struct_0 @ sk_C )
    = ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['59','73'])).

thf('113',plain,(
    m1_subset_1 @ sk_F @ ( k2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['109','110'])).

thf('114',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_C ) ) )
      | ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F )
      | ~ ( m1_connsp_2 @ X0 @ sk_D @ sk_F )
      | ~ ( r1_tarski @ X0 @ ( k2_struct_0 @ sk_C ) )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['94','95','103','104','111','112','113','114','115','116'])).

thf('118',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ~ ( r1_tarski @ ( k2_struct_0 @ sk_C ) @ ( k2_struct_0 @ sk_C ) )
    | ~ ( m1_connsp_2 @ ( k2_struct_0 @ sk_C ) @ sk_D @ sk_F )
    | ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['4','117'])).

thf('119',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['1'])).

thf('120',plain,(
    m1_subset_1 @ sk_F @ ( k2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['109','110'])).

thf('121',plain,
    ( ( u1_struct_0 @ sk_D )
    = ( k2_struct_0 @ sk_C ) ),
    inference(simplify,[status(thm)],['69'])).

thf('122',plain,(
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

thf('123',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X30 ) ) )
      | ~ ( v3_pre_topc @ X29 @ X30 )
      | ~ ( r2_hidden @ X31 @ X29 )
      | ( m1_connsp_2 @ X29 @ X30 @ X31 )
      | ~ ( m1_subset_1 @ X31 @ ( u1_struct_0 @ X30 ) )
      | ~ ( l1_pre_topc @ X30 )
      | ~ ( v2_pre_topc @ X30 )
      | ( v2_struct_0 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t5_connsp_2])).

thf('124',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ( m1_connsp_2 @ ( u1_struct_0 @ X0 ) @ X0 @ X1 )
      | ~ ( r2_hidden @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['122','123'])).

thf('125',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k2_struct_0 @ sk_C ) )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_D ) @ sk_D )
      | ~ ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_D ) )
      | ( m1_connsp_2 @ ( u1_struct_0 @ sk_D ) @ sk_D @ X0 )
      | ~ ( l1_pre_topc @ sk_D )
      | ~ ( v2_pre_topc @ sk_D )
      | ( v2_struct_0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['121','124'])).

thf('126',plain,
    ( ( u1_struct_0 @ sk_D )
    = ( k2_struct_0 @ sk_C ) ),
    inference(simplify,[status(thm)],['69'])).

thf('127',plain,
    ( ( k2_struct_0 @ sk_D )
    = ( k2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['71','72'])).

thf(fc10_tops_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( v3_pre_topc @ ( k2_struct_0 @ A ) @ A ) ) )).

thf('128',plain,(
    ! [X28: $i] :
      ( ( v3_pre_topc @ ( k2_struct_0 @ X28 ) @ X28 )
      | ~ ( l1_pre_topc @ X28 )
      | ~ ( v2_pre_topc @ X28 ) ) ),
    inference(cnf,[status(esa)],[fc10_tops_1])).

thf('129',plain,
    ( ( v3_pre_topc @ ( k2_struct_0 @ sk_C ) @ sk_D )
    | ~ ( v2_pre_topc @ sk_D )
    | ~ ( l1_pre_topc @ sk_D ) ),
    inference('sup+',[status(thm)],['127','128'])).

thf('130',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( v2_pre_topc @ B ) ) ) )).

thf('131',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( m1_pre_topc @ X12 @ X13 )
      | ( v2_pre_topc @ X12 )
      | ~ ( l1_pre_topc @ X13 )
      | ~ ( v2_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[cc1_pre_topc])).

thf('132',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_pre_topc @ sk_D ) ),
    inference('sup-',[status(thm)],['130','131'])).

thf('133',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('134',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('135',plain,(
    v2_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['132','133','134'])).

thf('136',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['26','27'])).

thf('137',plain,(
    v3_pre_topc @ ( k2_struct_0 @ sk_C ) @ sk_D ),
    inference(demod,[status(thm)],['129','135','136'])).

thf('138',plain,
    ( ( u1_struct_0 @ sk_D )
    = ( k2_struct_0 @ sk_C ) ),
    inference(simplify,[status(thm)],['69'])).

thf('139',plain,
    ( ( u1_struct_0 @ sk_D )
    = ( k2_struct_0 @ sk_C ) ),
    inference(simplify,[status(thm)],['69'])).

thf('140',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['26','27'])).

thf('141',plain,(
    v2_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['132','133','134'])).

thf('142',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k2_struct_0 @ sk_C ) )
      | ~ ( r2_hidden @ X0 @ ( k2_struct_0 @ sk_C ) )
      | ( m1_connsp_2 @ ( k2_struct_0 @ sk_C ) @ sk_D @ X0 )
      | ( v2_struct_0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['125','126','137','138','139','140','141'])).

thf('143',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( m1_connsp_2 @ ( k2_struct_0 @ sk_C ) @ sk_D @ sk_F )
    | ~ ( r2_hidden @ sk_F @ ( k2_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['120','142'])).

thf('144',plain,(
    ! [X14: $i] :
      ( ( ( k2_struct_0 @ X14 )
        = ( u1_struct_0 @ X14 ) )
      | ~ ( l1_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('145',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['106','107'])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('146',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r2_hidden @ X3 @ X4 )
      | ( v1_xboole_0 @ X4 )
      | ~ ( m1_subset_1 @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('147',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) )
    | ( r2_hidden @ sk_F @ ( u1_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['145','146'])).

thf('148',plain,
    ( ( r2_hidden @ sk_F @ ( k2_struct_0 @ sk_C ) )
    | ~ ( l1_struct_0 @ sk_C )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['144','147'])).

thf('149',plain,(
    l1_struct_0 @ sk_C ),
    inference('sup-',[status(thm)],['64','65'])).

thf('150',plain,
    ( ( r2_hidden @ sk_F @ ( k2_struct_0 @ sk_C ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['148','149'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('151',plain,(
    ! [X21: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X21 ) )
      | ~ ( l1_struct_0 @ X21 )
      | ( v2_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('152',plain,
    ( ( r2_hidden @ sk_F @ ( k2_struct_0 @ sk_C ) )
    | ( v2_struct_0 @ sk_C )
    | ~ ( l1_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['150','151'])).

thf('153',plain,(
    l1_struct_0 @ sk_C ),
    inference('sup-',[status(thm)],['64','65'])).

thf('154',plain,
    ( ( r2_hidden @ sk_F @ ( k2_struct_0 @ sk_C ) )
    | ( v2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['152','153'])).

thf('155',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('156',plain,(
    r2_hidden @ sk_F @ ( k2_struct_0 @ sk_C ) ),
    inference(clc,[status(thm)],['154','155'])).

thf('157',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( m1_connsp_2 @ ( k2_struct_0 @ sk_C ) @ sk_D @ sk_F ) ),
    inference(demod,[status(thm)],['143','156'])).

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
    inference(demod,[status(thm)],['118','119','159'])).

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
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.WTzJZFkh2Q
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:43:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 22.60/22.79  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 22.60/22.79  % Solved by: fo/fo7.sh
% 22.60/22.79  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 22.60/22.79  % done 11991 iterations in 22.323s
% 22.60/22.79  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 22.60/22.79  % SZS output start Refutation
% 22.60/22.79  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 22.60/22.79  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 22.60/22.79  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 22.60/22.79  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 22.60/22.79  thf(k3_tmap_1_type, type, k3_tmap_1: $i > $i > $i > $i > $i > $i).
% 22.60/22.79  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 22.60/22.79  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 22.60/22.79  thf(m1_connsp_2_type, type, m1_connsp_2: $i > $i > $i > $o).
% 22.60/22.79  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 22.60/22.79  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 22.60/22.79  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 22.60/22.79  thf(r1_tmap_1_type, type, r1_tmap_1: $i > $i > $i > $i > $o).
% 22.60/22.79  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 22.60/22.79  thf(sk_A_type, type, sk_A: $i).
% 22.60/22.79  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 22.60/22.79  thf(sk_G_type, type, sk_G: $i).
% 22.60/22.79  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 22.60/22.79  thf(sk_F_type, type, sk_F: $i).
% 22.60/22.79  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 22.60/22.79  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 22.60/22.79  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 22.60/22.79  thf(g1_pre_topc_type, type, g1_pre_topc: $i > $i > $i).
% 22.60/22.79  thf(sk_D_type, type, sk_D: $i).
% 22.60/22.79  thf(sk_E_type, type, sk_E: $i).
% 22.60/22.79  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 22.60/22.79  thf(sk_C_type, type, sk_C: $i).
% 22.60/22.79  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 22.60/22.79  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 22.60/22.79  thf(sk_B_type, type, sk_B: $i).
% 22.60/22.79  thf(t88_tmap_1, conjecture,
% 22.60/22.79    (![A:$i]:
% 22.60/22.79     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 22.60/22.79       ( ![B:$i]:
% 22.60/22.79         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 22.60/22.79             ( l1_pre_topc @ B ) ) =>
% 22.60/22.79           ( ![C:$i]:
% 22.60/22.79             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 22.60/22.79               ( ![D:$i]:
% 22.60/22.79                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 22.60/22.79                   ( ![E:$i]:
% 22.60/22.79                     ( ( ( v1_funct_1 @ E ) & 
% 22.60/22.79                         ( v1_funct_2 @
% 22.60/22.79                           E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 22.60/22.79                         ( m1_subset_1 @
% 22.60/22.79                           E @ 
% 22.60/22.79                           ( k1_zfmisc_1 @
% 22.60/22.79                             ( k2_zfmisc_1 @
% 22.60/22.79                               ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 22.60/22.79                       ( ( ( g1_pre_topc @
% 22.60/22.79                             ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) ) =
% 22.60/22.79                           ( D ) ) =>
% 22.60/22.79                         ( ![F:$i]:
% 22.60/22.79                           ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 22.60/22.79                             ( ![G:$i]:
% 22.60/22.79                               ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) ) =>
% 22.60/22.79                                 ( ( ( ( F ) = ( G ) ) & 
% 22.60/22.79                                     ( r1_tmap_1 @
% 22.60/22.79                                       C @ B @ 
% 22.60/22.79                                       ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ G ) ) =>
% 22.60/22.79                                   ( r1_tmap_1 @ D @ B @ E @ F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 22.60/22.79  thf(zf_stmt_0, negated_conjecture,
% 22.60/22.79    (~( ![A:$i]:
% 22.60/22.79        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 22.60/22.79            ( l1_pre_topc @ A ) ) =>
% 22.60/22.79          ( ![B:$i]:
% 22.60/22.79            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 22.60/22.79                ( l1_pre_topc @ B ) ) =>
% 22.60/22.79              ( ![C:$i]:
% 22.60/22.79                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 22.60/22.79                  ( ![D:$i]:
% 22.60/22.79                    ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 22.60/22.79                      ( ![E:$i]:
% 22.60/22.79                        ( ( ( v1_funct_1 @ E ) & 
% 22.60/22.79                            ( v1_funct_2 @
% 22.60/22.79                              E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 22.60/22.79                            ( m1_subset_1 @
% 22.60/22.79                              E @ 
% 22.60/22.79                              ( k1_zfmisc_1 @
% 22.60/22.79                                ( k2_zfmisc_1 @
% 22.60/22.79                                  ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 22.60/22.79                          ( ( ( g1_pre_topc @
% 22.60/22.79                                ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) ) =
% 22.60/22.79                              ( D ) ) =>
% 22.60/22.79                            ( ![F:$i]:
% 22.60/22.79                              ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 22.60/22.79                                ( ![G:$i]:
% 22.60/22.79                                  ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) ) =>
% 22.60/22.79                                    ( ( ( ( F ) = ( G ) ) & 
% 22.60/22.79                                        ( r1_tmap_1 @
% 22.60/22.79                                          C @ B @ 
% 22.60/22.79                                          ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ G ) ) =>
% 22.60/22.79                                      ( r1_tmap_1 @ D @ B @ E @ F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 22.60/22.79    inference('cnf.neg', [status(esa)], [t88_tmap_1])).
% 22.60/22.79  thf('0', plain, (~ (v2_struct_0 @ sk_C)),
% 22.60/22.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 22.60/22.79  thf(d10_xboole_0, axiom,
% 22.60/22.79    (![A:$i,B:$i]:
% 22.60/22.79     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 22.60/22.79  thf('1', plain,
% 22.60/22.79      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 22.60/22.79      inference('cnf', [status(esa)], [d10_xboole_0])).
% 22.60/22.79  thf('2', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 22.60/22.79      inference('simplify', [status(thm)], ['1'])).
% 22.60/22.79  thf(t3_subset, axiom,
% 22.60/22.79    (![A:$i,B:$i]:
% 22.60/22.79     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 22.60/22.79  thf('3', plain,
% 22.60/22.79      (![X5 : $i, X7 : $i]:
% 22.60/22.79         ((m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X7)) | ~ (r1_tarski @ X5 @ X7))),
% 22.60/22.79      inference('cnf', [status(esa)], [t3_subset])).
% 22.60/22.79  thf('4', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 22.60/22.79      inference('sup-', [status(thm)], ['2', '3'])).
% 22.60/22.79  thf('5', plain,
% 22.60/22.79      ((r1_tmap_1 @ sk_C @ sk_B @ 
% 22.60/22.79        (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_G)),
% 22.60/22.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 22.60/22.79  thf('6', plain, (((sk_F) = (sk_G))),
% 22.60/22.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 22.60/22.79  thf('7', plain,
% 22.60/22.79      ((r1_tmap_1 @ sk_C @ sk_B @ 
% 22.60/22.79        (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_F)),
% 22.60/22.79      inference('demod', [status(thm)], ['5', '6'])).
% 22.60/22.79  thf('8', plain,
% 22.60/22.79      ((m1_subset_1 @ sk_E @ 
% 22.60/22.79        (k1_zfmisc_1 @ 
% 22.60/22.79         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 22.60/22.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 22.60/22.79  thf('9', plain,
% 22.60/22.79      (((g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) = (sk_D))),
% 22.60/22.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 22.60/22.79  thf(abstractness_v1_pre_topc, axiom,
% 22.60/22.79    (![A:$i]:
% 22.60/22.79     ( ( l1_pre_topc @ A ) =>
% 22.60/22.79       ( ( v1_pre_topc @ A ) =>
% 22.60/22.79         ( ( A ) = ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ))).
% 22.60/22.79  thf('10', plain,
% 22.60/22.79      (![X11 : $i]:
% 22.60/22.79         (~ (v1_pre_topc @ X11)
% 22.60/22.79          | ((X11) = (g1_pre_topc @ (u1_struct_0 @ X11) @ (u1_pre_topc @ X11)))
% 22.60/22.79          | ~ (l1_pre_topc @ X11))),
% 22.60/22.79      inference('cnf', [status(esa)], [abstractness_v1_pre_topc])).
% 22.60/22.79  thf('11', plain,
% 22.60/22.79      (((g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) = (sk_D))),
% 22.60/22.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 22.60/22.79  thf(dt_u1_pre_topc, axiom,
% 22.60/22.79    (![A:$i]:
% 22.60/22.79     ( ( l1_pre_topc @ A ) =>
% 22.60/22.79       ( m1_subset_1 @
% 22.60/22.79         ( u1_pre_topc @ A ) @ 
% 22.60/22.79         ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ))).
% 22.60/22.79  thf('12', plain,
% 22.60/22.79      (![X20 : $i]:
% 22.60/22.79         ((m1_subset_1 @ (u1_pre_topc @ X20) @ 
% 22.60/22.79           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20))))
% 22.60/22.79          | ~ (l1_pre_topc @ X20))),
% 22.60/22.79      inference('cnf', [status(esa)], [dt_u1_pre_topc])).
% 22.60/22.79  thf(free_g1_pre_topc, axiom,
% 22.60/22.79    (![A:$i,B:$i]:
% 22.60/22.79     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 22.60/22.79       ( ![C:$i,D:$i]:
% 22.60/22.79         ( ( ( g1_pre_topc @ A @ B ) = ( g1_pre_topc @ C @ D ) ) =>
% 22.60/22.79           ( ( ( A ) = ( C ) ) & ( ( B ) = ( D ) ) ) ) ) ))).
% 22.60/22.79  thf('13', plain,
% 22.60/22.79      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 22.60/22.79         (((g1_pre_topc @ X24 @ X25) != (g1_pre_topc @ X22 @ X23))
% 22.60/22.79          | ((X25) = (X23))
% 22.60/22.79          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X24))))),
% 22.60/22.79      inference('cnf', [status(esa)], [free_g1_pre_topc])).
% 22.60/22.79  thf('14', plain,
% 22.60/22.79      (![X0 : $i, X1 : $i, X2 : $i]:
% 22.60/22.79         (~ (l1_pre_topc @ X0)
% 22.60/22.79          | ((u1_pre_topc @ X0) = (X1))
% 22.60/22.79          | ((g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))
% 22.60/22.79              != (g1_pre_topc @ X2 @ X1)))),
% 22.60/22.79      inference('sup-', [status(thm)], ['12', '13'])).
% 22.60/22.79  thf('15', plain,
% 22.60/22.79      (![X0 : $i, X1 : $i]:
% 22.60/22.79         (((sk_D) != (g1_pre_topc @ X1 @ X0))
% 22.60/22.79          | ((u1_pre_topc @ sk_C) = (X0))
% 22.60/22.79          | ~ (l1_pre_topc @ sk_C))),
% 22.60/22.79      inference('sup-', [status(thm)], ['11', '14'])).
% 22.60/22.79  thf('16', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 22.60/22.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 22.60/22.79  thf(dt_m1_pre_topc, axiom,
% 22.60/22.79    (![A:$i]:
% 22.60/22.79     ( ( l1_pre_topc @ A ) =>
% 22.60/22.79       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 22.60/22.79  thf('17', plain,
% 22.60/22.79      (![X18 : $i, X19 : $i]:
% 22.60/22.79         (~ (m1_pre_topc @ X18 @ X19)
% 22.60/22.79          | (l1_pre_topc @ X18)
% 22.60/22.79          | ~ (l1_pre_topc @ X19))),
% 22.60/22.79      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 22.60/22.79  thf('18', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_C))),
% 22.60/22.79      inference('sup-', [status(thm)], ['16', '17'])).
% 22.60/22.79  thf('19', plain, ((l1_pre_topc @ sk_A)),
% 22.60/22.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 22.60/22.79  thf('20', plain, ((l1_pre_topc @ sk_C)),
% 22.60/22.79      inference('demod', [status(thm)], ['18', '19'])).
% 22.60/22.79  thf('21', plain,
% 22.60/22.79      (![X0 : $i, X1 : $i]:
% 22.60/22.79         (((sk_D) != (g1_pre_topc @ X1 @ X0)) | ((u1_pre_topc @ sk_C) = (X0)))),
% 22.60/22.79      inference('demod', [status(thm)], ['15', '20'])).
% 22.60/22.79  thf('22', plain,
% 22.60/22.79      (![X0 : $i]:
% 22.60/22.79         (((sk_D) != (X0))
% 22.60/22.79          | ~ (l1_pre_topc @ X0)
% 22.60/22.79          | ~ (v1_pre_topc @ X0)
% 22.60/22.79          | ((u1_pre_topc @ sk_C) = (u1_pre_topc @ X0)))),
% 22.60/22.79      inference('sup-', [status(thm)], ['10', '21'])).
% 22.60/22.79  thf('23', plain,
% 22.60/22.79      ((((u1_pre_topc @ sk_C) = (u1_pre_topc @ sk_D))
% 22.60/22.79        | ~ (v1_pre_topc @ sk_D)
% 22.60/22.79        | ~ (l1_pre_topc @ sk_D))),
% 22.60/22.79      inference('simplify', [status(thm)], ['22'])).
% 22.60/22.79  thf('24', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 22.60/22.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 22.60/22.79  thf('25', plain,
% 22.60/22.79      (![X18 : $i, X19 : $i]:
% 22.60/22.79         (~ (m1_pre_topc @ X18 @ X19)
% 22.60/22.79          | (l1_pre_topc @ X18)
% 22.60/22.79          | ~ (l1_pre_topc @ X19))),
% 22.60/22.79      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 22.60/22.79  thf('26', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_D))),
% 22.60/22.79      inference('sup-', [status(thm)], ['24', '25'])).
% 22.60/22.79  thf('27', plain, ((l1_pre_topc @ sk_A)),
% 22.60/22.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 22.60/22.79  thf('28', plain, ((l1_pre_topc @ sk_D)),
% 22.60/22.79      inference('demod', [status(thm)], ['26', '27'])).
% 22.60/22.79  thf('29', plain,
% 22.60/22.79      (((g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) = (sk_D))),
% 22.60/22.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 22.60/22.79  thf('30', plain,
% 22.60/22.79      (![X20 : $i]:
% 22.60/22.79         ((m1_subset_1 @ (u1_pre_topc @ X20) @ 
% 22.60/22.79           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20))))
% 22.60/22.79          | ~ (l1_pre_topc @ X20))),
% 22.60/22.79      inference('cnf', [status(esa)], [dt_u1_pre_topc])).
% 22.60/22.79  thf(dt_g1_pre_topc, axiom,
% 22.60/22.79    (![A:$i,B:$i]:
% 22.60/22.79     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 22.60/22.79       ( ( v1_pre_topc @ ( g1_pre_topc @ A @ B ) ) & 
% 22.60/22.79         ( l1_pre_topc @ ( g1_pre_topc @ A @ B ) ) ) ))).
% 22.60/22.79  thf('31', plain,
% 22.60/22.79      (![X15 : $i, X16 : $i]:
% 22.60/22.79         ((v1_pre_topc @ (g1_pre_topc @ X15 @ X16))
% 22.60/22.79          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X15))))),
% 22.60/22.79      inference('cnf', [status(esa)], [dt_g1_pre_topc])).
% 22.60/22.79  thf('32', plain,
% 22.60/22.79      (![X0 : $i]:
% 22.60/22.79         (~ (l1_pre_topc @ X0)
% 22.60/22.79          | (v1_pre_topc @ 
% 22.60/22.79             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 22.60/22.79      inference('sup-', [status(thm)], ['30', '31'])).
% 22.60/22.79  thf('33', plain, (((v1_pre_topc @ sk_D) | ~ (l1_pre_topc @ sk_C))),
% 22.60/22.79      inference('sup+', [status(thm)], ['29', '32'])).
% 22.60/22.79  thf('34', plain, ((l1_pre_topc @ sk_C)),
% 22.60/22.79      inference('demod', [status(thm)], ['18', '19'])).
% 22.60/22.79  thf('35', plain, ((v1_pre_topc @ sk_D)),
% 22.60/22.79      inference('demod', [status(thm)], ['33', '34'])).
% 22.60/22.79  thf('36', plain, (((u1_pre_topc @ sk_C) = (u1_pre_topc @ sk_D))),
% 22.60/22.79      inference('simplify_reflect+', [status(thm)], ['23', '28', '35'])).
% 22.60/22.79  thf('37', plain,
% 22.60/22.79      (![X20 : $i]:
% 22.60/22.79         ((m1_subset_1 @ (u1_pre_topc @ X20) @ 
% 22.60/22.79           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20))))
% 22.60/22.79          | ~ (l1_pre_topc @ X20))),
% 22.60/22.79      inference('cnf', [status(esa)], [dt_u1_pre_topc])).
% 22.60/22.79  thf('38', plain,
% 22.60/22.79      (((m1_subset_1 @ (u1_pre_topc @ sk_C) @ 
% 22.60/22.79         (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D))))
% 22.60/22.79        | ~ (l1_pre_topc @ sk_D))),
% 22.60/22.79      inference('sup+', [status(thm)], ['36', '37'])).
% 22.60/22.79  thf('39', plain, ((l1_pre_topc @ sk_D)),
% 22.60/22.79      inference('demod', [status(thm)], ['26', '27'])).
% 22.60/22.79  thf('40', plain,
% 22.60/22.79      ((m1_subset_1 @ (u1_pre_topc @ sk_C) @ 
% 22.60/22.79        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D))))),
% 22.60/22.79      inference('demod', [status(thm)], ['38', '39'])).
% 22.60/22.79  thf('41', plain,
% 22.60/22.79      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 22.60/22.79         (((g1_pre_topc @ X24 @ X25) != (g1_pre_topc @ X22 @ X23))
% 22.60/22.79          | ((X24) = (X22))
% 22.60/22.79          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X24))))),
% 22.60/22.79      inference('cnf', [status(esa)], [free_g1_pre_topc])).
% 22.60/22.79  thf('42', plain,
% 22.60/22.79      (![X0 : $i, X1 : $i]:
% 22.60/22.79         (((u1_struct_0 @ sk_D) = (X0))
% 22.60/22.79          | ((g1_pre_topc @ (u1_struct_0 @ sk_D) @ (u1_pre_topc @ sk_C))
% 22.60/22.79              != (g1_pre_topc @ X0 @ X1)))),
% 22.60/22.79      inference('sup-', [status(thm)], ['40', '41'])).
% 22.60/22.79  thf('43', plain, (((u1_pre_topc @ sk_C) = (u1_pre_topc @ sk_D))),
% 22.60/22.79      inference('simplify_reflect+', [status(thm)], ['23', '28', '35'])).
% 22.60/22.79  thf('44', plain,
% 22.60/22.79      (![X11 : $i]:
% 22.60/22.79         (~ (v1_pre_topc @ X11)
% 22.60/22.79          | ((X11) = (g1_pre_topc @ (u1_struct_0 @ X11) @ (u1_pre_topc @ X11)))
% 22.60/22.79          | ~ (l1_pre_topc @ X11))),
% 22.60/22.79      inference('cnf', [status(esa)], [abstractness_v1_pre_topc])).
% 22.60/22.79  thf('45', plain,
% 22.60/22.79      ((((sk_D) = (g1_pre_topc @ (u1_struct_0 @ sk_D) @ (u1_pre_topc @ sk_C)))
% 22.60/22.79        | ~ (l1_pre_topc @ sk_D)
% 22.60/22.79        | ~ (v1_pre_topc @ sk_D))),
% 22.60/22.79      inference('sup+', [status(thm)], ['43', '44'])).
% 22.60/22.79  thf('46', plain, ((l1_pre_topc @ sk_D)),
% 22.60/22.79      inference('demod', [status(thm)], ['26', '27'])).
% 22.60/22.79  thf('47', plain, ((v1_pre_topc @ sk_D)),
% 22.60/22.79      inference('demod', [status(thm)], ['33', '34'])).
% 22.60/22.79  thf('48', plain,
% 22.60/22.79      (((sk_D) = (g1_pre_topc @ (u1_struct_0 @ sk_D) @ (u1_pre_topc @ sk_C)))),
% 22.60/22.79      inference('demod', [status(thm)], ['45', '46', '47'])).
% 22.60/22.79  thf('49', plain,
% 22.60/22.79      (![X0 : $i, X1 : $i]:
% 22.60/22.79         (((u1_struct_0 @ sk_D) = (X0)) | ((sk_D) != (g1_pre_topc @ X0 @ X1)))),
% 22.60/22.79      inference('demod', [status(thm)], ['42', '48'])).
% 22.60/22.79  thf('50', plain,
% 22.60/22.79      ((((sk_D) != (sk_D)) | ((u1_struct_0 @ sk_D) = (u1_struct_0 @ sk_C)))),
% 22.60/22.79      inference('sup-', [status(thm)], ['9', '49'])).
% 22.60/22.79  thf('51', plain, (((u1_struct_0 @ sk_D) = (u1_struct_0 @ sk_C))),
% 22.60/22.79      inference('simplify', [status(thm)], ['50'])).
% 22.60/22.79  thf('52', plain,
% 22.60/22.79      ((m1_subset_1 @ sk_E @ 
% 22.60/22.79        (k1_zfmisc_1 @ 
% 22.60/22.79         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 22.60/22.79      inference('demod', [status(thm)], ['8', '51'])).
% 22.60/22.79  thf(d3_struct_0, axiom,
% 22.60/22.79    (![A:$i]:
% 22.60/22.79     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 22.60/22.79  thf('53', plain,
% 22.60/22.79      (![X14 : $i]:
% 22.60/22.79         (((k2_struct_0 @ X14) = (u1_struct_0 @ X14)) | ~ (l1_struct_0 @ X14))),
% 22.60/22.79      inference('cnf', [status(esa)], [d3_struct_0])).
% 22.60/22.79  thf('54', plain, (((u1_struct_0 @ sk_D) = (u1_struct_0 @ sk_C))),
% 22.60/22.79      inference('simplify', [status(thm)], ['50'])).
% 22.60/22.79  thf('55', plain,
% 22.60/22.79      ((((k2_struct_0 @ sk_D) = (u1_struct_0 @ sk_C)) | ~ (l1_struct_0 @ sk_D))),
% 22.60/22.79      inference('sup+', [status(thm)], ['53', '54'])).
% 22.60/22.79  thf('56', plain, ((l1_pre_topc @ sk_D)),
% 22.60/22.79      inference('demod', [status(thm)], ['26', '27'])).
% 22.60/22.79  thf(dt_l1_pre_topc, axiom,
% 22.60/22.79    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 22.60/22.79  thf('57', plain,
% 22.60/22.79      (![X17 : $i]: ((l1_struct_0 @ X17) | ~ (l1_pre_topc @ X17))),
% 22.60/22.79      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 22.60/22.79  thf('58', plain, ((l1_struct_0 @ sk_D)),
% 22.60/22.79      inference('sup-', [status(thm)], ['56', '57'])).
% 22.60/22.79  thf('59', plain, (((k2_struct_0 @ sk_D) = (u1_struct_0 @ sk_C))),
% 22.60/22.79      inference('demod', [status(thm)], ['55', '58'])).
% 22.60/22.79  thf('60', plain,
% 22.60/22.79      (![X14 : $i]:
% 22.60/22.79         (((k2_struct_0 @ X14) = (u1_struct_0 @ X14)) | ~ (l1_struct_0 @ X14))),
% 22.60/22.79      inference('cnf', [status(esa)], [d3_struct_0])).
% 22.60/22.79  thf('61', plain,
% 22.60/22.79      (![X14 : $i]:
% 22.60/22.79         (((k2_struct_0 @ X14) = (u1_struct_0 @ X14)) | ~ (l1_struct_0 @ X14))),
% 22.60/22.79      inference('cnf', [status(esa)], [d3_struct_0])).
% 22.60/22.79  thf('62', plain,
% 22.60/22.79      (((g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) = (sk_D))),
% 22.60/22.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 22.60/22.79  thf('63', plain,
% 22.60/22.79      ((((g1_pre_topc @ (k2_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) = (sk_D))
% 22.60/22.79        | ~ (l1_struct_0 @ sk_C))),
% 22.60/22.79      inference('sup+', [status(thm)], ['61', '62'])).
% 22.60/22.79  thf('64', plain, ((l1_pre_topc @ sk_C)),
% 22.60/22.79      inference('demod', [status(thm)], ['18', '19'])).
% 22.60/22.79  thf('65', plain,
% 22.60/22.79      (![X17 : $i]: ((l1_struct_0 @ X17) | ~ (l1_pre_topc @ X17))),
% 22.60/22.79      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 22.60/22.79  thf('66', plain, ((l1_struct_0 @ sk_C)),
% 22.60/22.79      inference('sup-', [status(thm)], ['64', '65'])).
% 22.60/22.79  thf('67', plain,
% 22.60/22.79      (((g1_pre_topc @ (k2_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) = (sk_D))),
% 22.60/22.79      inference('demod', [status(thm)], ['63', '66'])).
% 22.60/22.79  thf('68', plain,
% 22.60/22.79      (![X0 : $i, X1 : $i]:
% 22.60/22.79         (((u1_struct_0 @ sk_D) = (X0)) | ((sk_D) != (g1_pre_topc @ X0 @ X1)))),
% 22.60/22.79      inference('demod', [status(thm)], ['42', '48'])).
% 22.60/22.79  thf('69', plain,
% 22.60/22.79      ((((sk_D) != (sk_D)) | ((u1_struct_0 @ sk_D) = (k2_struct_0 @ sk_C)))),
% 22.60/22.79      inference('sup-', [status(thm)], ['67', '68'])).
% 22.60/22.79  thf('70', plain, (((u1_struct_0 @ sk_D) = (k2_struct_0 @ sk_C))),
% 22.60/22.79      inference('simplify', [status(thm)], ['69'])).
% 22.60/22.79  thf('71', plain,
% 22.60/22.79      ((((k2_struct_0 @ sk_D) = (k2_struct_0 @ sk_C)) | ~ (l1_struct_0 @ sk_D))),
% 22.60/22.79      inference('sup+', [status(thm)], ['60', '70'])).
% 22.60/22.79  thf('72', plain, ((l1_struct_0 @ sk_D)),
% 22.60/22.79      inference('sup-', [status(thm)], ['56', '57'])).
% 22.60/22.79  thf('73', plain, (((k2_struct_0 @ sk_D) = (k2_struct_0 @ sk_C))),
% 22.60/22.79      inference('demod', [status(thm)], ['71', '72'])).
% 22.60/22.79  thf('74', plain, (((k2_struct_0 @ sk_C) = (u1_struct_0 @ sk_C))),
% 22.60/22.79      inference('demod', [status(thm)], ['59', '73'])).
% 22.60/22.79  thf('75', plain,
% 22.60/22.79      ((m1_subset_1 @ sk_E @ 
% 22.60/22.79        (k1_zfmisc_1 @ 
% 22.60/22.79         (k2_zfmisc_1 @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 22.60/22.79      inference('demod', [status(thm)], ['52', '74'])).
% 22.60/22.79  thf('76', plain, (((u1_struct_0 @ sk_D) = (k2_struct_0 @ sk_C))),
% 22.60/22.79      inference('simplify', [status(thm)], ['69'])).
% 22.60/22.79  thf(t83_tmap_1, axiom,
% 22.60/22.79    (![A:$i]:
% 22.60/22.79     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 22.60/22.80       ( ![B:$i]:
% 22.60/22.80         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 22.60/22.80             ( l1_pre_topc @ B ) ) =>
% 22.60/22.80           ( ![C:$i]:
% 22.60/22.80             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 22.60/22.80               ( ![D:$i]:
% 22.60/22.80                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 22.60/22.80                   ( ![E:$i]:
% 22.60/22.80                     ( ( ( v1_funct_1 @ E ) & 
% 22.60/22.80                         ( v1_funct_2 @
% 22.60/22.80                           E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 22.60/22.80                         ( m1_subset_1 @
% 22.60/22.80                           E @ 
% 22.60/22.80                           ( k1_zfmisc_1 @
% 22.60/22.80                             ( k2_zfmisc_1 @
% 22.60/22.80                               ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 22.60/22.80                       ( ( m1_pre_topc @ C @ D ) =>
% 22.60/22.80                         ( ![F:$i]:
% 22.60/22.80                           ( ( m1_subset_1 @
% 22.60/22.80                               F @ ( k1_zfmisc_1 @ ( u1_struct_0 @ D ) ) ) =>
% 22.60/22.80                             ( ![G:$i]:
% 22.60/22.80                               ( ( m1_subset_1 @ G @ ( u1_struct_0 @ D ) ) =>
% 22.60/22.80                                 ( ![H:$i]:
% 22.60/22.80                                   ( ( m1_subset_1 @ H @ ( u1_struct_0 @ C ) ) =>
% 22.60/22.80                                     ( ( ( r1_tarski @ F @ ( u1_struct_0 @ C ) ) & 
% 22.60/22.80                                         ( m1_connsp_2 @ F @ D @ G ) & 
% 22.60/22.80                                         ( ( G ) = ( H ) ) ) =>
% 22.60/22.80                                       ( ( r1_tmap_1 @ D @ B @ E @ G ) <=>
% 22.60/22.80                                         ( r1_tmap_1 @
% 22.60/22.80                                           C @ B @ 
% 22.60/22.80                                           ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ 
% 22.60/22.80                                           H ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 22.60/22.80  thf('77', plain,
% 22.60/22.80      (![X36 : $i, X37 : $i, X38 : $i, X39 : $i, X40 : $i, X41 : $i, X42 : $i, 
% 22.60/22.80         X43 : $i]:
% 22.60/22.80         ((v2_struct_0 @ X36)
% 22.60/22.80          | ~ (v2_pre_topc @ X36)
% 22.60/22.80          | ~ (l1_pre_topc @ X36)
% 22.60/22.80          | (v2_struct_0 @ X37)
% 22.60/22.80          | ~ (m1_pre_topc @ X37 @ X38)
% 22.60/22.80          | ~ (m1_pre_topc @ X39 @ X37)
% 22.60/22.80          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (u1_struct_0 @ X37)))
% 22.60/22.80          | ~ (m1_subset_1 @ X41 @ (u1_struct_0 @ X39))
% 22.60/22.80          | ~ (r1_tmap_1 @ X39 @ X36 @ 
% 22.60/22.80               (k3_tmap_1 @ X38 @ X36 @ X37 @ X39 @ X42) @ X41)
% 22.60/22.80          | (r1_tmap_1 @ X37 @ X36 @ X42 @ X43)
% 22.60/22.80          | ((X43) != (X41))
% 22.60/22.80          | ~ (m1_connsp_2 @ X40 @ X37 @ X43)
% 22.60/22.80          | ~ (r1_tarski @ X40 @ (u1_struct_0 @ X39))
% 22.60/22.80          | ~ (m1_subset_1 @ X43 @ (u1_struct_0 @ X37))
% 22.60/22.80          | ~ (m1_subset_1 @ X42 @ 
% 22.60/22.80               (k1_zfmisc_1 @ 
% 22.60/22.80                (k2_zfmisc_1 @ (u1_struct_0 @ X37) @ (u1_struct_0 @ X36))))
% 22.60/22.80          | ~ (v1_funct_2 @ X42 @ (u1_struct_0 @ X37) @ (u1_struct_0 @ X36))
% 22.60/22.80          | ~ (v1_funct_1 @ X42)
% 22.60/22.80          | ~ (m1_pre_topc @ X39 @ X38)
% 22.60/22.80          | (v2_struct_0 @ X39)
% 22.60/22.80          | ~ (l1_pre_topc @ X38)
% 22.60/22.80          | ~ (v2_pre_topc @ X38)
% 22.60/22.80          | (v2_struct_0 @ X38))),
% 22.60/22.80      inference('cnf', [status(esa)], [t83_tmap_1])).
% 22.60/22.80  thf('78', plain,
% 22.60/22.80      (![X36 : $i, X37 : $i, X38 : $i, X39 : $i, X40 : $i, X41 : $i, X42 : $i]:
% 22.60/22.80         ((v2_struct_0 @ X38)
% 22.60/22.80          | ~ (v2_pre_topc @ X38)
% 22.60/22.80          | ~ (l1_pre_topc @ X38)
% 22.60/22.80          | (v2_struct_0 @ X39)
% 22.60/22.80          | ~ (m1_pre_topc @ X39 @ X38)
% 22.60/22.80          | ~ (v1_funct_1 @ X42)
% 22.60/22.80          | ~ (v1_funct_2 @ X42 @ (u1_struct_0 @ X37) @ (u1_struct_0 @ X36))
% 22.60/22.80          | ~ (m1_subset_1 @ X42 @ 
% 22.60/22.80               (k1_zfmisc_1 @ 
% 22.60/22.80                (k2_zfmisc_1 @ (u1_struct_0 @ X37) @ (u1_struct_0 @ X36))))
% 22.60/22.80          | ~ (m1_subset_1 @ X41 @ (u1_struct_0 @ X37))
% 22.60/22.80          | ~ (r1_tarski @ X40 @ (u1_struct_0 @ X39))
% 22.60/22.80          | ~ (m1_connsp_2 @ X40 @ X37 @ X41)
% 22.60/22.80          | (r1_tmap_1 @ X37 @ X36 @ X42 @ X41)
% 22.60/22.80          | ~ (r1_tmap_1 @ X39 @ X36 @ 
% 22.60/22.80               (k3_tmap_1 @ X38 @ X36 @ X37 @ X39 @ X42) @ X41)
% 22.60/22.80          | ~ (m1_subset_1 @ X41 @ (u1_struct_0 @ X39))
% 22.60/22.80          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (u1_struct_0 @ X37)))
% 22.60/22.80          | ~ (m1_pre_topc @ X39 @ X37)
% 22.60/22.80          | ~ (m1_pre_topc @ X37 @ X38)
% 22.60/22.80          | (v2_struct_0 @ X37)
% 22.60/22.80          | ~ (l1_pre_topc @ X36)
% 22.60/22.80          | ~ (v2_pre_topc @ X36)
% 22.60/22.80          | (v2_struct_0 @ X36))),
% 22.60/22.80      inference('simplify', [status(thm)], ['77'])).
% 22.60/22.80  thf('79', plain,
% 22.60/22.80      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 22.60/22.80         (~ (m1_subset_1 @ X1 @ 
% 22.60/22.80             (k1_zfmisc_1 @ 
% 22.60/22.80              (k2_zfmisc_1 @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ X0))))
% 22.60/22.80          | (v2_struct_0 @ X0)
% 22.60/22.80          | ~ (v2_pre_topc @ X0)
% 22.60/22.80          | ~ (l1_pre_topc @ X0)
% 22.60/22.80          | (v2_struct_0 @ sk_D)
% 22.60/22.80          | ~ (m1_pre_topc @ sk_D @ X2)
% 22.60/22.80          | ~ (m1_pre_topc @ X3 @ sk_D)
% 22.60/22.80          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))
% 22.60/22.80          | ~ (m1_subset_1 @ X5 @ (u1_struct_0 @ X3))
% 22.60/22.80          | ~ (r1_tmap_1 @ X3 @ X0 @ (k3_tmap_1 @ X2 @ X0 @ sk_D @ X3 @ X1) @ 
% 22.60/22.80               X5)
% 22.60/22.80          | (r1_tmap_1 @ sk_D @ X0 @ X1 @ X5)
% 22.60/22.80          | ~ (m1_connsp_2 @ X4 @ sk_D @ X5)
% 22.60/22.80          | ~ (r1_tarski @ X4 @ (u1_struct_0 @ X3))
% 22.60/22.80          | ~ (m1_subset_1 @ X5 @ (u1_struct_0 @ sk_D))
% 22.60/22.80          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ X0))
% 22.60/22.80          | ~ (v1_funct_1 @ X1)
% 22.60/22.80          | ~ (m1_pre_topc @ X3 @ X2)
% 22.60/22.80          | (v2_struct_0 @ X3)
% 22.60/22.80          | ~ (l1_pre_topc @ X2)
% 22.60/22.80          | ~ (v2_pre_topc @ X2)
% 22.60/22.80          | (v2_struct_0 @ X2))),
% 22.60/22.80      inference('sup-', [status(thm)], ['76', '78'])).
% 22.60/22.80  thf('80', plain, (((u1_struct_0 @ sk_D) = (k2_struct_0 @ sk_C))),
% 22.60/22.80      inference('simplify', [status(thm)], ['69'])).
% 22.60/22.80  thf('81', plain, (((u1_struct_0 @ sk_D) = (k2_struct_0 @ sk_C))),
% 22.60/22.80      inference('simplify', [status(thm)], ['69'])).
% 22.60/22.80  thf('82', plain, (((u1_struct_0 @ sk_D) = (k2_struct_0 @ sk_C))),
% 22.60/22.80      inference('simplify', [status(thm)], ['69'])).
% 22.60/22.80  thf('83', plain,
% 22.60/22.80      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 22.60/22.80         (~ (m1_subset_1 @ X1 @ 
% 22.60/22.80             (k1_zfmisc_1 @ 
% 22.60/22.80              (k2_zfmisc_1 @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ X0))))
% 22.60/22.80          | (v2_struct_0 @ X0)
% 22.60/22.80          | ~ (v2_pre_topc @ X0)
% 22.60/22.80          | ~ (l1_pre_topc @ X0)
% 22.60/22.80          | (v2_struct_0 @ sk_D)
% 22.60/22.80          | ~ (m1_pre_topc @ sk_D @ X2)
% 22.60/22.80          | ~ (m1_pre_topc @ X3 @ sk_D)
% 22.60/22.80          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_C)))
% 22.60/22.80          | ~ (m1_subset_1 @ X5 @ (u1_struct_0 @ X3))
% 22.60/22.80          | ~ (r1_tmap_1 @ X3 @ X0 @ (k3_tmap_1 @ X2 @ X0 @ sk_D @ X3 @ X1) @ 
% 22.60/22.80               X5)
% 22.60/22.80          | (r1_tmap_1 @ sk_D @ X0 @ X1 @ X5)
% 22.60/22.80          | ~ (m1_connsp_2 @ X4 @ sk_D @ X5)
% 22.60/22.80          | ~ (r1_tarski @ X4 @ (u1_struct_0 @ X3))
% 22.60/22.80          | ~ (m1_subset_1 @ X5 @ (k2_struct_0 @ sk_C))
% 22.60/22.80          | ~ (v1_funct_2 @ X1 @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ X0))
% 22.60/22.80          | ~ (v1_funct_1 @ X1)
% 22.60/22.80          | ~ (m1_pre_topc @ X3 @ X2)
% 22.60/22.80          | (v2_struct_0 @ X3)
% 22.60/22.80          | ~ (l1_pre_topc @ X2)
% 22.60/22.80          | ~ (v2_pre_topc @ X2)
% 22.60/22.80          | (v2_struct_0 @ X2))),
% 22.60/22.80      inference('demod', [status(thm)], ['79', '80', '81', '82'])).
% 22.60/22.80  thf('84', plain,
% 22.60/22.80      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 22.60/22.80         ((v2_struct_0 @ X0)
% 22.60/22.80          | ~ (v2_pre_topc @ X0)
% 22.60/22.80          | ~ (l1_pre_topc @ X0)
% 22.60/22.80          | (v2_struct_0 @ X1)
% 22.60/22.80          | ~ (m1_pre_topc @ X1 @ X0)
% 22.60/22.80          | ~ (v1_funct_1 @ sk_E)
% 22.60/22.80          | ~ (v1_funct_2 @ sk_E @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))
% 22.60/22.80          | ~ (m1_subset_1 @ X2 @ (k2_struct_0 @ sk_C))
% 22.60/22.80          | ~ (r1_tarski @ X3 @ (u1_struct_0 @ X1))
% 22.60/22.80          | ~ (m1_connsp_2 @ X3 @ sk_D @ X2)
% 22.60/22.80          | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X2)
% 22.60/22.80          | ~ (r1_tmap_1 @ X1 @ sk_B @ 
% 22.60/22.80               (k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E) @ X2)
% 22.60/22.80          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1))
% 22.60/22.80          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_C)))
% 22.60/22.80          | ~ (m1_pre_topc @ X1 @ sk_D)
% 22.60/22.80          | ~ (m1_pre_topc @ sk_D @ X0)
% 22.60/22.80          | (v2_struct_0 @ sk_D)
% 22.60/22.80          | ~ (l1_pre_topc @ sk_B)
% 22.60/22.80          | ~ (v2_pre_topc @ sk_B)
% 22.60/22.80          | (v2_struct_0 @ sk_B))),
% 22.60/22.80      inference('sup-', [status(thm)], ['75', '83'])).
% 22.60/22.80  thf('85', plain, ((v1_funct_1 @ sk_E)),
% 22.60/22.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 22.60/22.80  thf('86', plain,
% 22.60/22.80      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 22.60/22.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 22.60/22.80  thf('87', plain, (((u1_struct_0 @ sk_D) = (u1_struct_0 @ sk_C))),
% 22.60/22.80      inference('simplify', [status(thm)], ['50'])).
% 22.60/22.80  thf('88', plain,
% 22.60/22.80      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 22.60/22.80      inference('demod', [status(thm)], ['86', '87'])).
% 22.60/22.80  thf('89', plain, (((k2_struct_0 @ sk_C) = (u1_struct_0 @ sk_C))),
% 22.60/22.80      inference('demod', [status(thm)], ['59', '73'])).
% 22.60/22.80  thf('90', plain,
% 22.60/22.80      ((v1_funct_2 @ sk_E @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 22.60/22.80      inference('demod', [status(thm)], ['88', '89'])).
% 22.60/22.80  thf('91', plain, ((l1_pre_topc @ sk_B)),
% 22.60/22.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 22.60/22.80  thf('92', plain, ((v2_pre_topc @ sk_B)),
% 22.60/22.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 22.60/22.80  thf('93', plain,
% 22.60/22.80      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 22.60/22.80         ((v2_struct_0 @ X0)
% 22.60/22.80          | ~ (v2_pre_topc @ X0)
% 22.60/22.80          | ~ (l1_pre_topc @ X0)
% 22.60/22.80          | (v2_struct_0 @ X1)
% 22.60/22.80          | ~ (m1_pre_topc @ X1 @ X0)
% 22.60/22.80          | ~ (m1_subset_1 @ X2 @ (k2_struct_0 @ sk_C))
% 22.60/22.80          | ~ (r1_tarski @ X3 @ (u1_struct_0 @ X1))
% 22.60/22.80          | ~ (m1_connsp_2 @ X3 @ sk_D @ X2)
% 22.60/22.80          | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X2)
% 22.60/22.80          | ~ (r1_tmap_1 @ X1 @ sk_B @ 
% 22.60/22.80               (k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E) @ X2)
% 22.60/22.80          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1))
% 22.60/22.80          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_C)))
% 22.60/22.80          | ~ (m1_pre_topc @ X1 @ sk_D)
% 22.60/22.80          | ~ (m1_pre_topc @ sk_D @ X0)
% 22.60/22.80          | (v2_struct_0 @ sk_D)
% 22.60/22.80          | (v2_struct_0 @ sk_B))),
% 22.60/22.80      inference('demod', [status(thm)], ['84', '85', '90', '91', '92'])).
% 22.60/22.80  thf('94', plain,
% 22.60/22.80      (![X0 : $i]:
% 22.60/22.80         ((v2_struct_0 @ sk_B)
% 22.60/22.80          | (v2_struct_0 @ sk_D)
% 22.60/22.80          | ~ (m1_pre_topc @ sk_D @ sk_A)
% 22.60/22.80          | ~ (m1_pre_topc @ sk_C @ sk_D)
% 22.60/22.80          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_C)))
% 22.60/22.80          | ~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C))
% 22.60/22.80          | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)
% 22.60/22.80          | ~ (m1_connsp_2 @ X0 @ sk_D @ sk_F)
% 22.60/22.80          | ~ (r1_tarski @ X0 @ (u1_struct_0 @ sk_C))
% 22.60/22.80          | ~ (m1_subset_1 @ sk_F @ (k2_struct_0 @ sk_C))
% 22.60/22.80          | ~ (m1_pre_topc @ sk_C @ sk_A)
% 22.60/22.80          | (v2_struct_0 @ sk_C)
% 22.60/22.80          | ~ (l1_pre_topc @ sk_A)
% 22.60/22.80          | ~ (v2_pre_topc @ sk_A)
% 22.60/22.80          | (v2_struct_0 @ sk_A))),
% 22.60/22.80      inference('sup-', [status(thm)], ['7', '93'])).
% 22.60/22.80  thf('95', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 22.60/22.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 22.60/22.80  thf('96', plain,
% 22.60/22.80      (((g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) = (sk_D))),
% 22.60/22.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 22.60/22.80  thf(t2_tsep_1, axiom,
% 22.60/22.80    (![A:$i]: ( ( l1_pre_topc @ A ) => ( m1_pre_topc @ A @ A ) ))).
% 22.60/22.80  thf('97', plain,
% 22.60/22.80      (![X32 : $i]: ((m1_pre_topc @ X32 @ X32) | ~ (l1_pre_topc @ X32))),
% 22.60/22.80      inference('cnf', [status(esa)], [t2_tsep_1])).
% 22.60/22.80  thf(t65_pre_topc, axiom,
% 22.60/22.80    (![A:$i]:
% 22.60/22.80     ( ( l1_pre_topc @ A ) =>
% 22.60/22.80       ( ![B:$i]:
% 22.60/22.80         ( ( l1_pre_topc @ B ) =>
% 22.60/22.80           ( ( m1_pre_topc @ A @ B ) <=>
% 22.60/22.80             ( m1_pre_topc @
% 22.60/22.80               A @ ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ) ))).
% 22.60/22.80  thf('98', plain,
% 22.60/22.80      (![X26 : $i, X27 : $i]:
% 22.60/22.80         (~ (l1_pre_topc @ X26)
% 22.60/22.80          | ~ (m1_pre_topc @ X27 @ X26)
% 22.60/22.80          | (m1_pre_topc @ X27 @ 
% 22.60/22.80             (g1_pre_topc @ (u1_struct_0 @ X26) @ (u1_pre_topc @ X26)))
% 22.60/22.80          | ~ (l1_pre_topc @ X27))),
% 22.60/22.80      inference('cnf', [status(esa)], [t65_pre_topc])).
% 22.60/22.80  thf('99', plain,
% 22.60/22.80      (![X0 : $i]:
% 22.60/22.80         (~ (l1_pre_topc @ X0)
% 22.60/22.80          | ~ (l1_pre_topc @ X0)
% 22.60/22.80          | (m1_pre_topc @ X0 @ 
% 22.60/22.80             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 22.60/22.80          | ~ (l1_pre_topc @ X0))),
% 22.60/22.80      inference('sup-', [status(thm)], ['97', '98'])).
% 22.60/22.80  thf('100', plain,
% 22.60/22.80      (![X0 : $i]:
% 22.60/22.80         ((m1_pre_topc @ X0 @ 
% 22.60/22.80           (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 22.60/22.80          | ~ (l1_pre_topc @ X0))),
% 22.60/22.80      inference('simplify', [status(thm)], ['99'])).
% 22.60/22.80  thf('101', plain, (((m1_pre_topc @ sk_C @ sk_D) | ~ (l1_pre_topc @ sk_C))),
% 22.60/22.80      inference('sup+', [status(thm)], ['96', '100'])).
% 22.60/22.80  thf('102', plain, ((l1_pre_topc @ sk_C)),
% 22.60/22.80      inference('demod', [status(thm)], ['18', '19'])).
% 22.60/22.80  thf('103', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 22.60/22.80      inference('demod', [status(thm)], ['101', '102'])).
% 22.60/22.80  thf('104', plain, (((k2_struct_0 @ sk_C) = (u1_struct_0 @ sk_C))),
% 22.60/22.80      inference('demod', [status(thm)], ['59', '73'])).
% 22.60/22.80  thf('105', plain,
% 22.60/22.80      (![X14 : $i]:
% 22.60/22.80         (((k2_struct_0 @ X14) = (u1_struct_0 @ X14)) | ~ (l1_struct_0 @ X14))),
% 22.60/22.80      inference('cnf', [status(esa)], [d3_struct_0])).
% 22.60/22.80  thf('106', plain, ((m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_C))),
% 22.60/22.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 22.60/22.80  thf('107', plain, (((sk_F) = (sk_G))),
% 22.60/22.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 22.60/22.80  thf('108', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C))),
% 22.60/22.80      inference('demod', [status(thm)], ['106', '107'])).
% 22.60/22.80  thf('109', plain,
% 22.60/22.80      (((m1_subset_1 @ sk_F @ (k2_struct_0 @ sk_C)) | ~ (l1_struct_0 @ sk_C))),
% 22.60/22.80      inference('sup+', [status(thm)], ['105', '108'])).
% 22.60/22.80  thf('110', plain, ((l1_struct_0 @ sk_C)),
% 22.60/22.80      inference('sup-', [status(thm)], ['64', '65'])).
% 22.60/22.80  thf('111', plain, ((m1_subset_1 @ sk_F @ (k2_struct_0 @ sk_C))),
% 22.60/22.80      inference('demod', [status(thm)], ['109', '110'])).
% 22.60/22.80  thf('112', plain, (((k2_struct_0 @ sk_C) = (u1_struct_0 @ sk_C))),
% 22.60/22.80      inference('demod', [status(thm)], ['59', '73'])).
% 22.60/22.80  thf('113', plain, ((m1_subset_1 @ sk_F @ (k2_struct_0 @ sk_C))),
% 22.60/22.80      inference('demod', [status(thm)], ['109', '110'])).
% 22.60/22.80  thf('114', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 22.60/22.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 22.60/22.80  thf('115', plain, ((l1_pre_topc @ sk_A)),
% 22.60/22.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 22.60/22.80  thf('116', plain, ((v2_pre_topc @ sk_A)),
% 22.60/22.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 22.60/22.80  thf('117', plain,
% 22.60/22.80      (![X0 : $i]:
% 22.60/22.80         ((v2_struct_0 @ sk_B)
% 22.60/22.80          | (v2_struct_0 @ sk_D)
% 22.60/22.80          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_C)))
% 22.60/22.80          | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)
% 22.60/22.80          | ~ (m1_connsp_2 @ X0 @ sk_D @ sk_F)
% 22.60/22.80          | ~ (r1_tarski @ X0 @ (k2_struct_0 @ sk_C))
% 22.60/22.80          | (v2_struct_0 @ sk_C)
% 22.60/22.80          | (v2_struct_0 @ sk_A))),
% 22.60/22.80      inference('demod', [status(thm)],
% 22.60/22.80                ['94', '95', '103', '104', '111', '112', '113', '114', '115', 
% 22.60/22.80                 '116'])).
% 22.60/22.80  thf('118', plain,
% 22.60/22.80      (((v2_struct_0 @ sk_A)
% 22.60/22.80        | (v2_struct_0 @ sk_C)
% 22.60/22.80        | ~ (r1_tarski @ (k2_struct_0 @ sk_C) @ (k2_struct_0 @ sk_C))
% 22.60/22.80        | ~ (m1_connsp_2 @ (k2_struct_0 @ sk_C) @ sk_D @ sk_F)
% 22.60/22.80        | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)
% 22.60/22.80        | (v2_struct_0 @ sk_D)
% 22.60/22.80        | (v2_struct_0 @ sk_B))),
% 22.60/22.80      inference('sup-', [status(thm)], ['4', '117'])).
% 22.60/22.80  thf('119', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 22.60/22.80      inference('simplify', [status(thm)], ['1'])).
% 22.60/22.80  thf('120', plain, ((m1_subset_1 @ sk_F @ (k2_struct_0 @ sk_C))),
% 22.60/22.80      inference('demod', [status(thm)], ['109', '110'])).
% 22.60/22.80  thf('121', plain, (((u1_struct_0 @ sk_D) = (k2_struct_0 @ sk_C))),
% 22.60/22.80      inference('simplify', [status(thm)], ['69'])).
% 22.60/22.80  thf('122', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 22.60/22.80      inference('sup-', [status(thm)], ['2', '3'])).
% 22.60/22.80  thf(t5_connsp_2, axiom,
% 22.60/22.80    (![A:$i]:
% 22.60/22.80     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 22.60/22.80       ( ![B:$i]:
% 22.60/22.80         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 22.60/22.80           ( ![C:$i]:
% 22.60/22.80             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 22.60/22.80               ( ( ( v3_pre_topc @ B @ A ) & ( r2_hidden @ C @ B ) ) =>
% 22.60/22.80                 ( m1_connsp_2 @ B @ A @ C ) ) ) ) ) ) ))).
% 22.60/22.80  thf('123', plain,
% 22.60/22.80      (![X29 : $i, X30 : $i, X31 : $i]:
% 22.60/22.80         (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X30)))
% 22.60/22.80          | ~ (v3_pre_topc @ X29 @ X30)
% 22.60/22.80          | ~ (r2_hidden @ X31 @ X29)
% 22.60/22.80          | (m1_connsp_2 @ X29 @ X30 @ X31)
% 22.60/22.80          | ~ (m1_subset_1 @ X31 @ (u1_struct_0 @ X30))
% 22.60/22.80          | ~ (l1_pre_topc @ X30)
% 22.60/22.80          | ~ (v2_pre_topc @ X30)
% 22.60/22.80          | (v2_struct_0 @ X30))),
% 22.60/22.80      inference('cnf', [status(esa)], [t5_connsp_2])).
% 22.60/22.80  thf('124', plain,
% 22.60/22.80      (![X0 : $i, X1 : $i]:
% 22.60/22.80         ((v2_struct_0 @ X0)
% 22.60/22.80          | ~ (v2_pre_topc @ X0)
% 22.60/22.80          | ~ (l1_pre_topc @ X0)
% 22.60/22.80          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 22.60/22.80          | (m1_connsp_2 @ (u1_struct_0 @ X0) @ X0 @ X1)
% 22.60/22.80          | ~ (r2_hidden @ X1 @ (u1_struct_0 @ X0))
% 22.60/22.80          | ~ (v3_pre_topc @ (u1_struct_0 @ X0) @ X0))),
% 22.60/22.80      inference('sup-', [status(thm)], ['122', '123'])).
% 22.60/22.80  thf('125', plain,
% 22.60/22.80      (![X0 : $i]:
% 22.60/22.80         (~ (m1_subset_1 @ X0 @ (k2_struct_0 @ sk_C))
% 22.60/22.80          | ~ (v3_pre_topc @ (u1_struct_0 @ sk_D) @ sk_D)
% 22.60/22.80          | ~ (r2_hidden @ X0 @ (u1_struct_0 @ sk_D))
% 22.60/22.80          | (m1_connsp_2 @ (u1_struct_0 @ sk_D) @ sk_D @ X0)
% 22.60/22.80          | ~ (l1_pre_topc @ sk_D)
% 22.60/22.80          | ~ (v2_pre_topc @ sk_D)
% 22.60/22.80          | (v2_struct_0 @ sk_D))),
% 22.60/22.80      inference('sup-', [status(thm)], ['121', '124'])).
% 22.60/22.80  thf('126', plain, (((u1_struct_0 @ sk_D) = (k2_struct_0 @ sk_C))),
% 22.60/22.80      inference('simplify', [status(thm)], ['69'])).
% 22.60/22.80  thf('127', plain, (((k2_struct_0 @ sk_D) = (k2_struct_0 @ sk_C))),
% 22.60/22.80      inference('demod', [status(thm)], ['71', '72'])).
% 22.60/22.80  thf(fc10_tops_1, axiom,
% 22.60/22.80    (![A:$i]:
% 22.60/22.80     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 22.60/22.80       ( v3_pre_topc @ ( k2_struct_0 @ A ) @ A ) ))).
% 22.60/22.80  thf('128', plain,
% 22.60/22.80      (![X28 : $i]:
% 22.60/22.80         ((v3_pre_topc @ (k2_struct_0 @ X28) @ X28)
% 22.60/22.80          | ~ (l1_pre_topc @ X28)
% 22.60/22.80          | ~ (v2_pre_topc @ X28))),
% 22.60/22.80      inference('cnf', [status(esa)], [fc10_tops_1])).
% 22.60/22.80  thf('129', plain,
% 22.60/22.80      (((v3_pre_topc @ (k2_struct_0 @ sk_C) @ sk_D)
% 22.60/22.80        | ~ (v2_pre_topc @ sk_D)
% 22.60/22.80        | ~ (l1_pre_topc @ sk_D))),
% 22.60/22.80      inference('sup+', [status(thm)], ['127', '128'])).
% 22.60/22.80  thf('130', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 22.60/22.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 22.60/22.80  thf(cc1_pre_topc, axiom,
% 22.60/22.80    (![A:$i]:
% 22.60/22.80     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 22.60/22.80       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( v2_pre_topc @ B ) ) ) ))).
% 22.60/22.80  thf('131', plain,
% 22.60/22.80      (![X12 : $i, X13 : $i]:
% 22.60/22.80         (~ (m1_pre_topc @ X12 @ X13)
% 22.60/22.80          | (v2_pre_topc @ X12)
% 22.60/22.80          | ~ (l1_pre_topc @ X13)
% 22.60/22.80          | ~ (v2_pre_topc @ X13))),
% 22.60/22.80      inference('cnf', [status(esa)], [cc1_pre_topc])).
% 22.60/22.80  thf('132', plain,
% 22.60/22.80      ((~ (v2_pre_topc @ sk_A) | ~ (l1_pre_topc @ sk_A) | (v2_pre_topc @ sk_D))),
% 22.60/22.80      inference('sup-', [status(thm)], ['130', '131'])).
% 22.60/22.80  thf('133', plain, ((v2_pre_topc @ sk_A)),
% 22.60/22.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 22.60/22.80  thf('134', plain, ((l1_pre_topc @ sk_A)),
% 22.60/22.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 22.60/22.80  thf('135', plain, ((v2_pre_topc @ sk_D)),
% 22.60/22.80      inference('demod', [status(thm)], ['132', '133', '134'])).
% 22.60/22.80  thf('136', plain, ((l1_pre_topc @ sk_D)),
% 22.60/22.80      inference('demod', [status(thm)], ['26', '27'])).
% 22.60/22.80  thf('137', plain, ((v3_pre_topc @ (k2_struct_0 @ sk_C) @ sk_D)),
% 22.60/22.80      inference('demod', [status(thm)], ['129', '135', '136'])).
% 22.60/22.80  thf('138', plain, (((u1_struct_0 @ sk_D) = (k2_struct_0 @ sk_C))),
% 22.60/22.80      inference('simplify', [status(thm)], ['69'])).
% 22.60/22.80  thf('139', plain, (((u1_struct_0 @ sk_D) = (k2_struct_0 @ sk_C))),
% 22.60/22.80      inference('simplify', [status(thm)], ['69'])).
% 22.60/22.80  thf('140', plain, ((l1_pre_topc @ sk_D)),
% 22.60/22.80      inference('demod', [status(thm)], ['26', '27'])).
% 22.60/22.80  thf('141', plain, ((v2_pre_topc @ sk_D)),
% 22.60/22.80      inference('demod', [status(thm)], ['132', '133', '134'])).
% 22.60/22.80  thf('142', plain,
% 22.60/22.80      (![X0 : $i]:
% 22.60/22.80         (~ (m1_subset_1 @ X0 @ (k2_struct_0 @ sk_C))
% 22.60/22.80          | ~ (r2_hidden @ X0 @ (k2_struct_0 @ sk_C))
% 22.60/22.80          | (m1_connsp_2 @ (k2_struct_0 @ sk_C) @ sk_D @ X0)
% 22.60/22.80          | (v2_struct_0 @ sk_D))),
% 22.60/22.80      inference('demod', [status(thm)],
% 22.60/22.80                ['125', '126', '137', '138', '139', '140', '141'])).
% 22.60/22.80  thf('143', plain,
% 22.60/22.80      (((v2_struct_0 @ sk_D)
% 22.60/22.80        | (m1_connsp_2 @ (k2_struct_0 @ sk_C) @ sk_D @ sk_F)
% 22.60/22.80        | ~ (r2_hidden @ sk_F @ (k2_struct_0 @ sk_C)))),
% 22.60/22.80      inference('sup-', [status(thm)], ['120', '142'])).
% 22.60/22.80  thf('144', plain,
% 22.60/22.80      (![X14 : $i]:
% 22.60/22.80         (((k2_struct_0 @ X14) = (u1_struct_0 @ X14)) | ~ (l1_struct_0 @ X14))),
% 22.60/22.80      inference('cnf', [status(esa)], [d3_struct_0])).
% 22.60/22.80  thf('145', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C))),
% 22.60/22.80      inference('demod', [status(thm)], ['106', '107'])).
% 22.60/22.80  thf(t2_subset, axiom,
% 22.60/22.80    (![A:$i,B:$i]:
% 22.60/22.80     ( ( m1_subset_1 @ A @ B ) =>
% 22.60/22.80       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 22.60/22.80  thf('146', plain,
% 22.60/22.80      (![X3 : $i, X4 : $i]:
% 22.60/22.80         ((r2_hidden @ X3 @ X4)
% 22.60/22.80          | (v1_xboole_0 @ X4)
% 22.60/22.80          | ~ (m1_subset_1 @ X3 @ X4))),
% 22.60/22.80      inference('cnf', [status(esa)], [t2_subset])).
% 22.60/22.80  thf('147', plain,
% 22.60/22.80      (((v1_xboole_0 @ (u1_struct_0 @ sk_C))
% 22.60/22.80        | (r2_hidden @ sk_F @ (u1_struct_0 @ sk_C)))),
% 22.60/22.80      inference('sup-', [status(thm)], ['145', '146'])).
% 22.60/22.80  thf('148', plain,
% 22.60/22.80      (((r2_hidden @ sk_F @ (k2_struct_0 @ sk_C))
% 22.60/22.80        | ~ (l1_struct_0 @ sk_C)
% 22.60/22.80        | (v1_xboole_0 @ (u1_struct_0 @ sk_C)))),
% 22.60/22.80      inference('sup+', [status(thm)], ['144', '147'])).
% 22.60/22.80  thf('149', plain, ((l1_struct_0 @ sk_C)),
% 22.60/22.80      inference('sup-', [status(thm)], ['64', '65'])).
% 22.60/22.80  thf('150', plain,
% 22.60/22.80      (((r2_hidden @ sk_F @ (k2_struct_0 @ sk_C))
% 22.60/22.80        | (v1_xboole_0 @ (u1_struct_0 @ sk_C)))),
% 22.60/22.80      inference('demod', [status(thm)], ['148', '149'])).
% 22.60/22.80  thf(fc2_struct_0, axiom,
% 22.60/22.80    (![A:$i]:
% 22.60/22.80     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 22.60/22.80       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 22.60/22.80  thf('151', plain,
% 22.60/22.80      (![X21 : $i]:
% 22.60/22.80         (~ (v1_xboole_0 @ (u1_struct_0 @ X21))
% 22.60/22.80          | ~ (l1_struct_0 @ X21)
% 22.60/22.80          | (v2_struct_0 @ X21))),
% 22.60/22.80      inference('cnf', [status(esa)], [fc2_struct_0])).
% 22.60/22.80  thf('152', plain,
% 22.60/22.80      (((r2_hidden @ sk_F @ (k2_struct_0 @ sk_C))
% 22.60/22.80        | (v2_struct_0 @ sk_C)
% 22.60/22.80        | ~ (l1_struct_0 @ sk_C))),
% 22.60/22.80      inference('sup-', [status(thm)], ['150', '151'])).
% 22.60/22.80  thf('153', plain, ((l1_struct_0 @ sk_C)),
% 22.60/22.80      inference('sup-', [status(thm)], ['64', '65'])).
% 22.60/22.80  thf('154', plain,
% 22.60/22.80      (((r2_hidden @ sk_F @ (k2_struct_0 @ sk_C)) | (v2_struct_0 @ sk_C))),
% 22.60/22.80      inference('demod', [status(thm)], ['152', '153'])).
% 22.60/22.80  thf('155', plain, (~ (v2_struct_0 @ sk_C)),
% 22.60/22.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 22.60/22.80  thf('156', plain, ((r2_hidden @ sk_F @ (k2_struct_0 @ sk_C))),
% 22.60/22.80      inference('clc', [status(thm)], ['154', '155'])).
% 22.60/22.80  thf('157', plain,
% 22.60/22.80      (((v2_struct_0 @ sk_D)
% 22.60/22.80        | (m1_connsp_2 @ (k2_struct_0 @ sk_C) @ sk_D @ sk_F))),
% 22.60/22.80      inference('demod', [status(thm)], ['143', '156'])).
% 22.60/22.80  thf('158', plain, (~ (v2_struct_0 @ sk_D)),
% 22.60/22.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 22.60/22.80  thf('159', plain, ((m1_connsp_2 @ (k2_struct_0 @ sk_C) @ sk_D @ sk_F)),
% 22.60/22.80      inference('clc', [status(thm)], ['157', '158'])).
% 22.60/22.80  thf('160', plain,
% 22.60/22.80      (((v2_struct_0 @ sk_A)
% 22.60/22.80        | (v2_struct_0 @ sk_C)
% 22.60/22.80        | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)
% 22.60/22.80        | (v2_struct_0 @ sk_D)
% 22.60/22.80        | (v2_struct_0 @ sk_B))),
% 22.60/22.80      inference('demod', [status(thm)], ['118', '119', '159'])).
% 22.60/22.80  thf('161', plain, (~ (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)),
% 22.60/22.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 22.60/22.80  thf('162', plain,
% 22.60/22.80      (((v2_struct_0 @ sk_B)
% 22.60/22.80        | (v2_struct_0 @ sk_D)
% 22.60/22.80        | (v2_struct_0 @ sk_C)
% 22.60/22.80        | (v2_struct_0 @ sk_A))),
% 22.60/22.80      inference('sup-', [status(thm)], ['160', '161'])).
% 22.60/22.80  thf('163', plain, (~ (v2_struct_0 @ sk_D)),
% 22.60/22.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 22.60/22.80  thf('164', plain,
% 22.60/22.80      (((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_B))),
% 22.60/22.80      inference('sup-', [status(thm)], ['162', '163'])).
% 22.60/22.80  thf('165', plain, (~ (v2_struct_0 @ sk_A)),
% 22.60/22.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 22.60/22.80  thf('166', plain, (((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_C))),
% 22.60/22.80      inference('clc', [status(thm)], ['164', '165'])).
% 22.60/22.80  thf('167', plain, (~ (v2_struct_0 @ sk_B)),
% 22.60/22.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 22.60/22.80  thf('168', plain, ((v2_struct_0 @ sk_C)),
% 22.60/22.80      inference('clc', [status(thm)], ['166', '167'])).
% 22.60/22.80  thf('169', plain, ($false), inference('demod', [status(thm)], ['0', '168'])).
% 22.60/22.80  
% 22.60/22.80  % SZS output end Refutation
% 22.60/22.80  
% 22.60/22.80  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
