%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.iQI8Cv0UJR

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:10:31 EST 2020

% Result     : Theorem 0.90s
% Output     : Refutation 0.90s
% Verified   : 
% Statistics : Number of formulae       :  381 (20723 expanded)
%              Number of leaves         :   45 (6131 expanded)
%              Depth                    :   45
%              Number of atoms          : 3954 (514140 expanded)
%              Number of equality atoms :  117 (14272 expanded)
%              Maximal formula depth    :   26 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_G_type,type,(
    sk_G: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(g1_pre_topc_type,type,(
    g1_pre_topc: $i > $i > $i )).

thf(r1_tmap_1_type,type,(
    r1_tmap_1: $i > $i > $i > $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(v1_tsep_1_type,type,(
    v1_tsep_1: $i > $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(k2_partfun1_type,type,(
    k2_partfun1: $i > $i > $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k3_tmap_1_type,type,(
    k3_tmap_1: $i > $i > $i > $i > $i > $i )).

thf(k2_tmap_1_type,type,(
    k2_tmap_1: $i > $i > $i > $i > $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

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
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) )
    = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( m1_pre_topc @ A @ A ) ) )).

thf('2',plain,(
    ! [X37: $i] :
      ( ( m1_pre_topc @ X37 @ X37 )
      | ~ ( l1_pre_topc @ X37 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf(t59_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) )
         => ( m1_pre_topc @ B @ A ) ) ) )).

thf('3',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( m1_pre_topc @ X15 @ ( g1_pre_topc @ ( u1_struct_0 @ X16 ) @ ( u1_pre_topc @ X16 ) ) )
      | ( m1_pre_topc @ X15 @ X16 )
      | ~ ( l1_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[t59_pre_topc])).

thf('4',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,
    ( ~ ( l1_pre_topc @ sk_D )
    | ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) ) @ sk_C )
    | ~ ( l1_pre_topc @ sk_C ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf('6',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('7',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( m1_pre_topc @ X10 @ X11 )
      | ( l1_pre_topc @ X10 )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('8',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_D ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) )
    = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( m1_pre_topc @ X10 @ X11 )
      | ( l1_pre_topc @ X10 )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('14',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_C ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,(
    m1_pre_topc @ sk_D @ sk_C ),
    inference(demod,[status(thm)],['5','10','11','16'])).

thf(t35_borsuk_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( r1_tarski @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) )).

thf('18',plain,(
    ! [X38: $i,X39: $i] :
      ( ~ ( m1_pre_topc @ X38 @ X39 )
      | ( r1_tarski @ ( u1_struct_0 @ X38 ) @ ( u1_struct_0 @ X39 ) )
      | ~ ( l1_pre_topc @ X39 ) ) ),
    inference(cnf,[status(esa)],[t35_borsuk_1])).

thf('19',plain,
    ( ~ ( l1_pre_topc @ sk_C )
    | ( r1_tarski @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['14','15'])).

thf('21',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['19','20'])).

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
    ( ~ ( r1_tarski @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D ) )
    | ( ( u1_struct_0 @ sk_C )
      = ( u1_struct_0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) )
    = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc10_tops_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( v3_pre_topc @ ( k2_struct_0 @ A ) @ A ) ) )).

thf('25',plain,(
    ! [X22: $i] :
      ( ( v3_pre_topc @ ( k2_struct_0 @ X22 ) @ X22 )
      | ~ ( l1_pre_topc @ X22 )
      | ~ ( v2_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[fc10_tops_1])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('26',plain,(
    ! [X8: $i] :
      ( ( ( k2_struct_0 @ X8 )
        = ( u1_struct_0 @ X8 ) )
      | ~ ( l1_struct_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('28',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['27'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('29',plain,(
    ! [X3: $i,X5: $i] :
      ( ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X5 ) )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('30',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf(t60_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ( v3_pre_topc @ B @ A )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
        <=> ( ( v3_pre_topc @ B @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ) ) ) ) )).

thf('31',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( v3_pre_topc @ X19 @ X18 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X18 ) @ ( u1_pre_topc @ X18 ) ) ) ) )
      | ~ ( l1_pre_topc @ X18 )
      | ~ ( v2_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[t60_pre_topc])).

thf('32',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( v3_pre_topc @ ( k2_struct_0 @ X0 ) @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['26','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['25','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,
    ( ( m1_subset_1 @ ( u1_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) )
    | ~ ( v2_pre_topc @ sk_C )
    | ~ ( l1_pre_topc @ sk_C )
    | ~ ( l1_struct_0 @ sk_C ) ),
    inference('sup+',[status(thm)],['24','35'])).

thf('37',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( v2_pre_topc @ B ) ) ) )).

thf('38',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( m1_pre_topc @ X6 @ X7 )
      | ( v2_pre_topc @ X6 )
      | ~ ( l1_pre_topc @ X7 )
      | ~ ( v2_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[cc1_pre_topc])).

thf('39',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_pre_topc @ sk_C ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    v2_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['39','40','41'])).

thf('43',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['14','15'])).

thf('44',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['14','15'])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('45',plain,(
    ! [X9: $i] :
      ( ( l1_struct_0 @ X9 )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('46',plain,(
    l1_struct_0 @ sk_C ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['36','42','43','46'])).

thf('48',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('49',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,
    ( ( u1_struct_0 @ sk_C )
    = ( u1_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['23','49'])).

thf('51',plain,(
    ! [X8: $i] :
      ( ( ( k2_struct_0 @ X8 )
        = ( u1_struct_0 @ X8 ) )
      | ~ ( l1_struct_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('52',plain,
    ( ( u1_struct_0 @ sk_C )
    = ( u1_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['23','49'])).

thf('53',plain,
    ( ( ( u1_struct_0 @ sk_C )
      = ( k2_struct_0 @ sk_D ) )
    | ~ ( l1_struct_0 @ sk_D ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf('54',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['8','9'])).

thf('55',plain,(
    ! [X9: $i] :
      ( ( l1_struct_0 @ X9 )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('56',plain,(
    l1_struct_0 @ sk_D ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,
    ( ( u1_struct_0 @ sk_C )
    = ( k2_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['53','56'])).

thf('58',plain,
    ( ( k2_struct_0 @ sk_D )
    = ( u1_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['50','57'])).

thf('59',plain,(
    ! [X8: $i] :
      ( ( ( k2_struct_0 @ X8 )
        = ( u1_struct_0 @ X8 ) )
      | ~ ( l1_struct_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('60',plain,
    ( ( u1_struct_0 @ sk_C )
    = ( k2_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['53','56'])).

thf('61',plain,
    ( ( ( k2_struct_0 @ sk_C )
      = ( k2_struct_0 @ sk_D ) )
    | ~ ( l1_struct_0 @ sk_C ) ),
    inference('sup+',[status(thm)],['59','60'])).

thf('62',plain,(
    l1_struct_0 @ sk_C ),
    inference('sup-',[status(thm)],['44','45'])).

thf('63',plain,
    ( ( k2_struct_0 @ sk_C )
    = ( k2_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,
    ( ( k2_struct_0 @ sk_C )
    = ( u1_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['58','63'])).

thf('65',plain,(
    r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    sk_F = sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_F ),
    inference(demod,[status(thm)],['65','66'])).

thf('68',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,
    ( ( u1_struct_0 @ sk_C )
    = ( k2_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['53','56'])).

thf('70',plain,
    ( ( k2_struct_0 @ sk_C )
    = ( k2_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('71',plain,
    ( ( u1_struct_0 @ sk_C )
    = ( k2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X37: $i] :
      ( ( m1_pre_topc @ X37 @ X37 )
      | ~ ( l1_pre_topc @ X37 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf(t65_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( l1_pre_topc @ B )
         => ( ( m1_pre_topc @ A @ B )
          <=> ( m1_pre_topc @ A @ ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ) )).

thf('73',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( l1_pre_topc @ X20 )
      | ~ ( m1_pre_topc @ X21 @ X20 )
      | ( m1_pre_topc @ X21 @ ( g1_pre_topc @ ( u1_struct_0 @ X20 ) @ ( u1_pre_topc @ X20 ) ) )
      | ~ ( l1_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[t65_pre_topc])).

thf('74',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['74'])).

thf('76',plain,
    ( ( m1_pre_topc @ sk_C @ ( g1_pre_topc @ ( k2_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) ) )
    | ~ ( l1_pre_topc @ sk_C ) ),
    inference('sup+',[status(thm)],['71','75'])).

thf('77',plain,(
    ! [X8: $i] :
      ( ( ( k2_struct_0 @ X8 )
        = ( u1_struct_0 @ X8 ) )
      | ~ ( l1_struct_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('78',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) )
    = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,
    ( ( ( g1_pre_topc @ ( k2_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) )
      = sk_D )
    | ~ ( l1_struct_0 @ sk_C ) ),
    inference('sup+',[status(thm)],['77','78'])).

thf('80',plain,(
    l1_struct_0 @ sk_C ),
    inference('sup-',[status(thm)],['44','45'])).

thf('81',plain,
    ( ( g1_pre_topc @ ( k2_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) )
    = sk_D ),
    inference(demod,[status(thm)],['79','80'])).

thf('82',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['14','15'])).

thf('83',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(demod,[status(thm)],['76','81','82'])).

thf('84',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,
    ( ( u1_struct_0 @ sk_C )
    = ( u1_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['23','49'])).

thf('86',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('87',plain,
    ( ( u1_struct_0 @ sk_C )
    = ( k2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('88',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['86','87'])).

thf('89',plain,
    ( ( k2_struct_0 @ sk_C )
    = ( u1_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['58','63'])).

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

thf('90',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ( v2_struct_0 @ X27 )
      | ~ ( v2_pre_topc @ X27 )
      | ~ ( l1_pre_topc @ X27 )
      | ~ ( m1_pre_topc @ X28 @ X29 )
      | ~ ( m1_pre_topc @ X28 @ X30 )
      | ( ( k3_tmap_1 @ X29 @ X27 @ X30 @ X28 @ X31 )
        = ( k2_partfun1 @ ( u1_struct_0 @ X30 ) @ ( u1_struct_0 @ X27 ) @ X31 @ ( u1_struct_0 @ X28 ) ) )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X30 ) @ ( u1_struct_0 @ X27 ) ) ) )
      | ~ ( v1_funct_2 @ X31 @ ( u1_struct_0 @ X30 ) @ ( u1_struct_0 @ X27 ) )
      | ~ ( v1_funct_1 @ X31 )
      | ~ ( m1_pre_topc @ X30 @ X29 )
      | ~ ( l1_pre_topc @ X29 )
      | ~ ( v2_pre_topc @ X29 )
      | ( v2_struct_0 @ X29 ) ) ),
    inference(cnf,[status(esa)],[d5_tmap_1])).

thf('91',plain,(
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
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,
    ( ( k2_struct_0 @ sk_C )
    = ( u1_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['58','63'])).

thf('93',plain,
    ( ( k2_struct_0 @ sk_C )
    = ( u1_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['58','63'])).

thf('94',plain,(
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
    inference(demod,[status(thm)],['91','92','93'])).

thf('95',plain,(
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
    inference('sup-',[status(thm)],['88','94'])).

thf('96',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
    ! [X8: $i] :
      ( ( ( k2_struct_0 @ X8 )
        = ( u1_struct_0 @ X8 ) )
      | ~ ( l1_struct_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('99',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,
    ( ( v1_funct_2 @ sk_E @ ( k2_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_D ) ),
    inference('sup+',[status(thm)],['98','99'])).

thf('101',plain,(
    l1_struct_0 @ sk_D ),
    inference('sup-',[status(thm)],['54','55'])).

thf('102',plain,(
    v1_funct_2 @ sk_E @ ( k2_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['100','101'])).

thf('103',plain,
    ( ( k2_struct_0 @ sk_C )
    = ( k2_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('104',plain,(
    v1_funct_2 @ sk_E @ ( k2_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['102','103'])).

thf('105',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,(
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
    inference(demod,[status(thm)],['95','96','97','104','105'])).

thf('107',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ( ( k3_tmap_1 @ X0 @ sk_B @ sk_D @ sk_C @ sk_E )
        = ( k2_partfun1 @ ( k2_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ sk_C ) ) )
      | ~ ( m1_pre_topc @ sk_C @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['83','106'])).

thf('108',plain,
    ( ( u1_struct_0 @ sk_C )
    = ( k2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('109',plain,(
    ! [X37: $i] :
      ( ( m1_pre_topc @ X37 @ X37 )
      | ~ ( l1_pre_topc @ X37 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('110',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['86','87'])).

thf('111',plain,(
    ! [X8: $i] :
      ( ( ( k2_struct_0 @ X8 )
        = ( u1_struct_0 @ X8 ) )
      | ~ ( l1_struct_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

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

thf('112',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ( v2_struct_0 @ X23 )
      | ~ ( v2_pre_topc @ X23 )
      | ~ ( l1_pre_topc @ X23 )
      | ~ ( m1_pre_topc @ X24 @ X25 )
      | ( ( k2_tmap_1 @ X25 @ X23 @ X26 @ X24 )
        = ( k2_partfun1 @ ( u1_struct_0 @ X25 ) @ ( u1_struct_0 @ X23 ) @ X26 @ ( u1_struct_0 @ X24 ) ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X25 ) @ ( u1_struct_0 @ X23 ) ) ) )
      | ~ ( v1_funct_2 @ X26 @ ( u1_struct_0 @ X25 ) @ ( u1_struct_0 @ X23 ) )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( l1_pre_topc @ X25 )
      | ~ ( v2_pre_topc @ X25 )
      | ( v2_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d4_tmap_1])).

thf('113',plain,(
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
    inference('sup-',[status(thm)],['111','112'])).

thf('114',plain,(
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
    inference('sup-',[status(thm)],['110','113'])).

thf('115',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,
    ( ( u1_struct_0 @ sk_C )
    = ( k2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('118',plain,
    ( ( u1_struct_0 @ sk_C )
    = ( k2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('119',plain,(
    v1_funct_2 @ sk_E @ ( k2_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['102','103'])).

thf('120',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('121',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['14','15'])).

thf('122',plain,(
    v2_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['39','40','41'])).

thf('123',plain,(
    l1_struct_0 @ sk_C ),
    inference('sup-',[status(thm)],['44','45'])).

thf('124',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ X0 @ sk_C )
      | ( ( k2_tmap_1 @ sk_C @ sk_B @ sk_E @ X0 )
        = ( k2_partfun1 @ ( k2_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ X0 ) ) )
      | ( v2_struct_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['114','115','116','117','118','119','120','121','122','123'])).

thf('125',plain,
    ( ~ ( l1_pre_topc @ sk_C )
    | ( v2_struct_0 @ sk_C )
    | ( ( k2_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_C )
      = ( k2_partfun1 @ ( k2_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ sk_C ) ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['109','124'])).

thf('126',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['14','15'])).

thf('127',plain,
    ( ( u1_struct_0 @ sk_C )
    = ( k2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('128',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( ( k2_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_C )
      = ( k2_partfun1 @ ( k2_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( k2_struct_0 @ sk_C ) ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['125','126','127'])).

thf('129',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('130',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k2_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_C )
      = ( k2_partfun1 @ ( k2_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( k2_struct_0 @ sk_C ) ) ) ),
    inference(clc,[status(thm)],['128','129'])).

thf('131',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('132',plain,
    ( ( k2_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_C )
    = ( k2_partfun1 @ ( k2_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( k2_struct_0 @ sk_C ) ) ),
    inference(clc,[status(thm)],['130','131'])).

thf('133',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ( ( k3_tmap_1 @ X0 @ sk_B @ sk_D @ sk_C @ sk_E )
        = ( k2_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_C ) )
      | ~ ( m1_pre_topc @ sk_C @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['107','108','132'])).

thf('134',plain,
    ( ( v2_struct_0 @ sk_B )
    | ~ ( m1_pre_topc @ sk_C @ sk_A )
    | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E )
      = ( k2_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_C ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['68','133'])).

thf('135',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('136',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('137',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('138',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E )
      = ( k2_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_C ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['134','135','136','137'])).

thf('139',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('140',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E )
      = ( k2_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_C ) ) ),
    inference(clc,[status(thm)],['138','139'])).

thf('141',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('142',plain,
    ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E )
    = ( k2_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_C ) ),
    inference(clc,[status(thm)],['140','141'])).

thf('143',plain,(
    r1_tmap_1 @ sk_C @ sk_B @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_C ) @ sk_F ),
    inference(demod,[status(thm)],['67','142'])).

thf('144',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['86','87'])).

thf('145',plain,(
    ! [X8: $i] :
      ( ( ( k2_struct_0 @ X8 )
        = ( u1_struct_0 @ X8 ) )
      | ~ ( l1_struct_0 @ X8 ) ) ),
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

thf('146',plain,(
    ! [X43: $i,X44: $i,X45: $i,X46: $i,X47: $i,X48: $i] :
      ( ( v2_struct_0 @ X43 )
      | ~ ( v2_pre_topc @ X43 )
      | ~ ( l1_pre_topc @ X43 )
      | ( v2_struct_0 @ X44 )
      | ~ ( v1_tsep_1 @ X44 @ X43 )
      | ~ ( m1_pre_topc @ X44 @ X43 )
      | ~ ( m1_subset_1 @ X45 @ ( u1_struct_0 @ X44 ) )
      | ~ ( r1_tmap_1 @ X44 @ X46 @ ( k2_tmap_1 @ X43 @ X46 @ X47 @ X44 ) @ X45 )
      | ( r1_tmap_1 @ X43 @ X46 @ X47 @ X48 )
      | ( X48 != X45 )
      | ~ ( m1_subset_1 @ X48 @ ( u1_struct_0 @ X43 ) )
      | ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X43 ) @ ( u1_struct_0 @ X46 ) ) ) )
      | ~ ( v1_funct_2 @ X47 @ ( u1_struct_0 @ X43 ) @ ( u1_struct_0 @ X46 ) )
      | ~ ( v1_funct_1 @ X47 )
      | ~ ( l1_pre_topc @ X46 )
      | ~ ( v2_pre_topc @ X46 )
      | ( v2_struct_0 @ X46 ) ) ),
    inference(cnf,[status(esa)],[t67_tmap_1])).

thf('147',plain,(
    ! [X43: $i,X44: $i,X45: $i,X46: $i,X47: $i] :
      ( ( v2_struct_0 @ X46 )
      | ~ ( v2_pre_topc @ X46 )
      | ~ ( l1_pre_topc @ X46 )
      | ~ ( v1_funct_1 @ X47 )
      | ~ ( v1_funct_2 @ X47 @ ( u1_struct_0 @ X43 ) @ ( u1_struct_0 @ X46 ) )
      | ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X43 ) @ ( u1_struct_0 @ X46 ) ) ) )
      | ~ ( m1_subset_1 @ X45 @ ( u1_struct_0 @ X43 ) )
      | ( r1_tmap_1 @ X43 @ X46 @ X47 @ X45 )
      | ~ ( r1_tmap_1 @ X44 @ X46 @ ( k2_tmap_1 @ X43 @ X46 @ X47 @ X44 ) @ X45 )
      | ~ ( m1_subset_1 @ X45 @ ( u1_struct_0 @ X44 ) )
      | ~ ( m1_pre_topc @ X44 @ X43 )
      | ~ ( v1_tsep_1 @ X44 @ X43 )
      | ( v2_struct_0 @ X44 )
      | ~ ( l1_pre_topc @ X43 )
      | ~ ( v2_pre_topc @ X43 )
      | ( v2_struct_0 @ X43 ) ) ),
    inference(simplify,[status(thm)],['146'])).

thf('148',plain,(
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
    inference('sup-',[status(thm)],['145','147'])).

thf('149',plain,(
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
    inference('sup-',[status(thm)],['144','148'])).

thf('150',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('151',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('152',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('153',plain,
    ( ( u1_struct_0 @ sk_C )
    = ( k2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('154',plain,(
    v1_funct_2 @ sk_E @ ( k2_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['102','103'])).

thf('155',plain,
    ( ( u1_struct_0 @ sk_C )
    = ( k2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('156',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['14','15'])).

thf('157',plain,(
    v2_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['39','40','41'])).

thf('158',plain,(
    l1_struct_0 @ sk_C ),
    inference('sup-',[status(thm)],['44','45'])).

thf('159',plain,(
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
    inference(demod,[status(thm)],['149','150','151','152','153','154','155','156','157','158'])).

thf('160',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_C )
    | ~ ( v1_tsep_1 @ sk_C @ sk_C )
    | ~ ( m1_pre_topc @ sk_C @ sk_C )
    | ~ ( m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_C ) )
    | ( r1_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_F )
    | ~ ( m1_subset_1 @ sk_F @ ( k2_struct_0 @ sk_C ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['143','159'])).

thf('161',plain,
    ( ( u1_struct_0 @ sk_C )
    = ( k2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('162',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

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

thf('163',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ~ ( m1_pre_topc @ X32 @ X33 )
      | ( X34
       != ( u1_struct_0 @ X32 ) )
      | ~ ( v3_pre_topc @ X34 @ X33 )
      | ( v1_tsep_1 @ X32 @ X33 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X33 ) ) )
      | ~ ( l1_pre_topc @ X33 )
      | ~ ( v2_pre_topc @ X33 ) ) ),
    inference(cnf,[status(esa)],[t16_tsep_1])).

thf('164',plain,(
    ! [X32: $i,X33: $i] :
      ( ~ ( v2_pre_topc @ X33 )
      | ~ ( l1_pre_topc @ X33 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X32 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X33 ) ) )
      | ( v1_tsep_1 @ X32 @ X33 )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ X32 ) @ X33 )
      | ~ ( m1_pre_topc @ X32 @ X33 ) ) ),
    inference(simplify,[status(thm)],['163'])).

thf('165',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ X0 )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 )
      | ( v1_tsep_1 @ X0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['162','164'])).

thf('166',plain,
    ( ~ ( v3_pre_topc @ ( k2_struct_0 @ sk_C ) @ sk_C )
    | ~ ( v2_pre_topc @ sk_C )
    | ~ ( l1_pre_topc @ sk_C )
    | ( v1_tsep_1 @ sk_C @ sk_C )
    | ~ ( m1_pre_topc @ sk_C @ sk_C ) ),
    inference('sup-',[status(thm)],['161','165'])).

thf('167',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) )
    = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('168',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['34'])).

thf('169',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( v3_pre_topc @ X17 @ ( g1_pre_topc @ ( u1_struct_0 @ X18 ) @ ( u1_pre_topc @ X18 ) ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X18 ) @ ( u1_pre_topc @ X18 ) ) ) ) )
      | ( v3_pre_topc @ X17 @ X18 )
      | ~ ( l1_pre_topc @ X18 )
      | ~ ( v2_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[t60_pre_topc])).

thf('170',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['168','169'])).

thf('171',plain,(
    ! [X0: $i] :
      ( ~ ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['170'])).

thf('172',plain,
    ( ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_C ) @ sk_D )
    | ~ ( v2_pre_topc @ sk_C )
    | ~ ( l1_pre_topc @ sk_C )
    | ~ ( l1_struct_0 @ sk_C )
    | ( v3_pre_topc @ ( u1_struct_0 @ sk_C ) @ sk_C ) ),
    inference('sup-',[status(thm)],['167','171'])).

thf('173',plain,(
    v2_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['39','40','41'])).

thf('174',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['14','15'])).

thf('175',plain,(
    l1_struct_0 @ sk_C ),
    inference('sup-',[status(thm)],['44','45'])).

thf('176',plain,
    ( ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_C ) @ sk_D )
    | ( v3_pre_topc @ ( u1_struct_0 @ sk_C ) @ sk_C ) ),
    inference(demod,[status(thm)],['172','173','174','175'])).

thf('177',plain,
    ( ( u1_struct_0 @ sk_C )
    = ( k2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('178',plain,
    ( ( k2_struct_0 @ sk_C )
    = ( k2_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('179',plain,(
    ! [X22: $i] :
      ( ( v3_pre_topc @ ( k2_struct_0 @ X22 ) @ X22 )
      | ~ ( l1_pre_topc @ X22 )
      | ~ ( v2_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[fc10_tops_1])).

thf('180',plain,
    ( ( v3_pre_topc @ ( k2_struct_0 @ sk_C ) @ sk_D )
    | ~ ( v2_pre_topc @ sk_D )
    | ~ ( l1_pre_topc @ sk_D ) ),
    inference('sup+',[status(thm)],['178','179'])).

thf('181',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('182',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( m1_pre_topc @ X6 @ X7 )
      | ( v2_pre_topc @ X6 )
      | ~ ( l1_pre_topc @ X7 )
      | ~ ( v2_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[cc1_pre_topc])).

thf('183',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_pre_topc @ sk_D ) ),
    inference('sup-',[status(thm)],['181','182'])).

thf('184',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('185',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('186',plain,(
    v2_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['183','184','185'])).

thf('187',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['8','9'])).

thf('188',plain,(
    v3_pre_topc @ ( k2_struct_0 @ sk_C ) @ sk_D ),
    inference(demod,[status(thm)],['180','186','187'])).

thf('189',plain,
    ( ( u1_struct_0 @ sk_C )
    = ( k2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('190',plain,(
    v3_pre_topc @ ( k2_struct_0 @ sk_C ) @ sk_C ),
    inference(demod,[status(thm)],['176','177','188','189'])).

thf('191',plain,(
    v2_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['39','40','41'])).

thf('192',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['14','15'])).

thf('193',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(demod,[status(thm)],['76','81','82'])).

thf('194',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) )
    = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('195',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( m1_pre_topc @ X15 @ ( g1_pre_topc @ ( u1_struct_0 @ X16 ) @ ( u1_pre_topc @ X16 ) ) )
      | ( m1_pre_topc @ X15 @ X16 )
      | ~ ( l1_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[t59_pre_topc])).

thf('196',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_D )
      | ~ ( l1_pre_topc @ sk_C )
      | ( m1_pre_topc @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['194','195'])).

thf('197',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['14','15'])).

thf('198',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( m1_pre_topc @ X0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['196','197'])).

thf('199',plain,(
    m1_pre_topc @ sk_C @ sk_C ),
    inference('sup-',[status(thm)],['193','198'])).

thf('200',plain,(
    v1_tsep_1 @ sk_C @ sk_C ),
    inference(demod,[status(thm)],['166','190','191','192','199'])).

thf('201',plain,(
    m1_pre_topc @ sk_C @ sk_C ),
    inference('sup-',[status(thm)],['193','198'])).

thf('202',plain,
    ( ( u1_struct_0 @ sk_C )
    = ( k2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('203',plain,(
    ! [X8: $i] :
      ( ( ( k2_struct_0 @ X8 )
        = ( u1_struct_0 @ X8 ) )
      | ~ ( l1_struct_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('204',plain,(
    m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('205',plain,(
    sk_F = sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('206',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['204','205'])).

thf('207',plain,
    ( ( m1_subset_1 @ sk_F @ ( k2_struct_0 @ sk_C ) )
    | ~ ( l1_struct_0 @ sk_C ) ),
    inference('sup+',[status(thm)],['203','206'])).

thf('208',plain,(
    l1_struct_0 @ sk_C ),
    inference('sup-',[status(thm)],['44','45'])).

thf('209',plain,(
    m1_subset_1 @ sk_F @ ( k2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['207','208'])).

thf('210',plain,(
    m1_subset_1 @ sk_F @ ( k2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['207','208'])).

thf('211',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_C )
    | ( r1_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_F )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['160','200','201','202','209','210'])).

thf('212',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( r1_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_F )
    | ( v2_struct_0 @ sk_C ) ),
    inference(simplify,[status(thm)],['211'])).

thf('213',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('214',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( r1_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_F ) ),
    inference(clc,[status(thm)],['212','213'])).

thf('215',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('216',plain,(
    r1_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_F ),
    inference(clc,[status(thm)],['214','215'])).

thf('217',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['86','87'])).

thf('218',plain,(
    ! [X8: $i] :
      ( ( ( k2_struct_0 @ X8 )
        = ( u1_struct_0 @ X8 ) )
      | ~ ( l1_struct_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('219',plain,(
    ! [X43: $i,X44: $i,X45: $i,X46: $i,X47: $i,X48: $i] :
      ( ( v2_struct_0 @ X43 )
      | ~ ( v2_pre_topc @ X43 )
      | ~ ( l1_pre_topc @ X43 )
      | ( v2_struct_0 @ X44 )
      | ~ ( v1_tsep_1 @ X44 @ X43 )
      | ~ ( m1_pre_topc @ X44 @ X43 )
      | ~ ( m1_subset_1 @ X45 @ ( u1_struct_0 @ X44 ) )
      | ~ ( r1_tmap_1 @ X43 @ X46 @ X47 @ X48 )
      | ( r1_tmap_1 @ X44 @ X46 @ ( k2_tmap_1 @ X43 @ X46 @ X47 @ X44 ) @ X45 )
      | ( X48 != X45 )
      | ~ ( m1_subset_1 @ X48 @ ( u1_struct_0 @ X43 ) )
      | ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X43 ) @ ( u1_struct_0 @ X46 ) ) ) )
      | ~ ( v1_funct_2 @ X47 @ ( u1_struct_0 @ X43 ) @ ( u1_struct_0 @ X46 ) )
      | ~ ( v1_funct_1 @ X47 )
      | ~ ( l1_pre_topc @ X46 )
      | ~ ( v2_pre_topc @ X46 )
      | ( v2_struct_0 @ X46 ) ) ),
    inference(cnf,[status(esa)],[t67_tmap_1])).

thf('220',plain,(
    ! [X43: $i,X44: $i,X45: $i,X46: $i,X47: $i] :
      ( ( v2_struct_0 @ X46 )
      | ~ ( v2_pre_topc @ X46 )
      | ~ ( l1_pre_topc @ X46 )
      | ~ ( v1_funct_1 @ X47 )
      | ~ ( v1_funct_2 @ X47 @ ( u1_struct_0 @ X43 ) @ ( u1_struct_0 @ X46 ) )
      | ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X43 ) @ ( u1_struct_0 @ X46 ) ) ) )
      | ~ ( m1_subset_1 @ X45 @ ( u1_struct_0 @ X43 ) )
      | ( r1_tmap_1 @ X44 @ X46 @ ( k2_tmap_1 @ X43 @ X46 @ X47 @ X44 ) @ X45 )
      | ~ ( r1_tmap_1 @ X43 @ X46 @ X47 @ X45 )
      | ~ ( m1_subset_1 @ X45 @ ( u1_struct_0 @ X44 ) )
      | ~ ( m1_pre_topc @ X44 @ X43 )
      | ~ ( v1_tsep_1 @ X44 @ X43 )
      | ( v2_struct_0 @ X44 )
      | ~ ( l1_pre_topc @ X43 )
      | ~ ( v2_pre_topc @ X43 )
      | ( v2_struct_0 @ X43 ) ) ),
    inference(simplify,[status(thm)],['219'])).

thf('221',plain,(
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
    inference('sup-',[status(thm)],['218','220'])).

thf('222',plain,(
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
    inference('sup-',[status(thm)],['217','221'])).

thf('223',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('224',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('225',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('226',plain,
    ( ( u1_struct_0 @ sk_C )
    = ( k2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('227',plain,(
    v1_funct_2 @ sk_E @ ( k2_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['102','103'])).

thf('228',plain,
    ( ( u1_struct_0 @ sk_C )
    = ( k2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('229',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['14','15'])).

thf('230',plain,(
    v2_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['39','40','41'])).

thf('231',plain,(
    l1_struct_0 @ sk_C ),
    inference('sup-',[status(thm)],['44','45'])).

thf('232',plain,(
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
    inference(demod,[status(thm)],['222','223','224','225','226','227','228','229','230','231'])).

thf('233',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ X0 )
      | ~ ( v1_tsep_1 @ X0 @ sk_C )
      | ~ ( m1_pre_topc @ X0 @ sk_C )
      | ~ ( m1_subset_1 @ sk_F @ ( u1_struct_0 @ X0 ) )
      | ( r1_tmap_1 @ X0 @ sk_B @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_E @ X0 ) @ sk_F )
      | ~ ( m1_subset_1 @ sk_F @ ( k2_struct_0 @ sk_C ) )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['216','232'])).

thf('234',plain,(
    m1_subset_1 @ sk_F @ ( k2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['207','208'])).

thf('235',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ X0 )
      | ~ ( v1_tsep_1 @ X0 @ sk_C )
      | ~ ( m1_pre_topc @ X0 @ sk_C )
      | ~ ( m1_subset_1 @ sk_F @ ( u1_struct_0 @ X0 ) )
      | ( r1_tmap_1 @ X0 @ sk_B @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_E @ X0 ) @ sk_F )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['233','234'])).

thf('236',plain,
    ( ~ ( m1_subset_1 @ sk_F @ ( k2_struct_0 @ sk_C ) )
    | ( v2_struct_0 @ sk_B )
    | ( r1_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_D ) @ sk_F )
    | ~ ( m1_pre_topc @ sk_D @ sk_C )
    | ~ ( v1_tsep_1 @ sk_D @ sk_C )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['64','235'])).

thf('237',plain,(
    m1_subset_1 @ sk_F @ ( k2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['207','208'])).

thf('238',plain,(
    m1_pre_topc @ sk_D @ sk_C ),
    inference(demod,[status(thm)],['5','10','11','16'])).

thf('239',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ X0 @ sk_C )
      | ( ( k2_tmap_1 @ sk_C @ sk_B @ sk_E @ X0 )
        = ( k2_partfun1 @ ( k2_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ X0 ) ) )
      | ( v2_struct_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['114','115','116','117','118','119','120','121','122','123'])).

thf('240',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( ( k2_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_D )
      = ( k2_partfun1 @ ( k2_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ sk_D ) ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['238','239'])).

thf('241',plain,
    ( ( k2_struct_0 @ sk_C )
    = ( u1_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['58','63'])).

thf('242',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( ( k2_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_D )
      = ( k2_partfun1 @ ( k2_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( k2_struct_0 @ sk_C ) ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['240','241'])).

thf('243',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('244',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k2_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_D )
      = ( k2_partfun1 @ ( k2_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( k2_struct_0 @ sk_C ) ) ) ),
    inference(clc,[status(thm)],['242','243'])).

thf('245',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('246',plain,
    ( ( k2_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_D )
    = ( k2_partfun1 @ ( k2_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( k2_struct_0 @ sk_C ) ) ),
    inference(clc,[status(thm)],['244','245'])).

thf('247',plain,
    ( ( k2_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_C )
    = ( k2_partfun1 @ ( k2_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( k2_struct_0 @ sk_C ) ) ),
    inference(clc,[status(thm)],['130','131'])).

thf('248',plain,
    ( ( k2_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_C )
    = ( k2_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_D ) ),
    inference('sup+',[status(thm)],['246','247'])).

thf('249',plain,(
    m1_pre_topc @ sk_D @ sk_C ),
    inference(demod,[status(thm)],['5','10','11','16'])).

thf('250',plain,
    ( ( k2_struct_0 @ sk_C )
    = ( u1_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['58','63'])).

thf('251',plain,
    ( ( u1_struct_0 @ sk_C )
    = ( k2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('252',plain,(
    ! [X32: $i,X33: $i] :
      ( ~ ( v2_pre_topc @ X33 )
      | ~ ( l1_pre_topc @ X33 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X32 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X33 ) ) )
      | ( v1_tsep_1 @ X32 @ X33 )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ X32 ) @ X33 )
      | ~ ( m1_pre_topc @ X32 @ X33 ) ) ),
    inference(simplify,[status(thm)],['163'])).

thf('253',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_C ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_C )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ sk_C )
      | ( v1_tsep_1 @ X0 @ sk_C )
      | ~ ( l1_pre_topc @ sk_C )
      | ~ ( v2_pre_topc @ sk_C ) ) ),
    inference('sup-',[status(thm)],['251','252'])).

thf('254',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['14','15'])).

thf('255',plain,(
    v2_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['39','40','41'])).

thf('256',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_C ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_C )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ sk_C )
      | ( v1_tsep_1 @ X0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['253','254','255'])).

thf('257',plain,
    ( ~ ( m1_subset_1 @ ( k2_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_C ) ) )
    | ( v1_tsep_1 @ sk_D @ sk_C )
    | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_D ) @ sk_C )
    | ~ ( m1_pre_topc @ sk_D @ sk_C ) ),
    inference('sup-',[status(thm)],['250','256'])).

thf('258',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('259',plain,
    ( ( k2_struct_0 @ sk_C )
    = ( u1_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['58','63'])).

thf('260',plain,(
    v3_pre_topc @ ( k2_struct_0 @ sk_C ) @ sk_C ),
    inference(demod,[status(thm)],['176','177','188','189'])).

thf('261',plain,(
    m1_pre_topc @ sk_D @ sk_C ),
    inference(demod,[status(thm)],['5','10','11','16'])).

thf('262',plain,(
    v1_tsep_1 @ sk_D @ sk_C ),
    inference(demod,[status(thm)],['257','258','259','260','261'])).

thf('263',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( r1_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_C ) @ sk_F )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['236','237','248','249','262'])).

thf('264',plain,(
    ! [X37: $i] :
      ( ( m1_pre_topc @ X37 @ X37 )
      | ~ ( l1_pre_topc @ X37 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('265',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['86','87'])).

thf('266',plain,
    ( ( k2_struct_0 @ sk_C )
    = ( u1_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['58','63'])).

thf('267',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ( v2_struct_0 @ X23 )
      | ~ ( v2_pre_topc @ X23 )
      | ~ ( l1_pre_topc @ X23 )
      | ~ ( m1_pre_topc @ X24 @ X25 )
      | ( ( k2_tmap_1 @ X25 @ X23 @ X26 @ X24 )
        = ( k2_partfun1 @ ( u1_struct_0 @ X25 ) @ ( u1_struct_0 @ X23 ) @ X26 @ ( u1_struct_0 @ X24 ) ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X25 ) @ ( u1_struct_0 @ X23 ) ) ) )
      | ~ ( v1_funct_2 @ X26 @ ( u1_struct_0 @ X25 ) @ ( u1_struct_0 @ X23 ) )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( l1_pre_topc @ X25 )
      | ~ ( v2_pre_topc @ X25 )
      | ( v2_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d4_tmap_1])).

thf('268',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_C ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ( v2_struct_0 @ sk_D )
      | ~ ( v2_pre_topc @ sk_D )
      | ~ ( l1_pre_topc @ sk_D )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ X0 ) )
      | ( ( k2_tmap_1 @ sk_D @ X0 @ X1 @ X2 )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ X0 ) @ X1 @ ( u1_struct_0 @ X2 ) ) )
      | ~ ( m1_pre_topc @ X2 @ sk_D )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['266','267'])).

thf('269',plain,(
    v2_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['183','184','185'])).

thf('270',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['8','9'])).

thf('271',plain,
    ( ( k2_struct_0 @ sk_C )
    = ( u1_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['58','63'])).

thf('272',plain,
    ( ( k2_struct_0 @ sk_C )
    = ( u1_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['58','63'])).

thf('273',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_C ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ( v2_struct_0 @ sk_D )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ ( k2_struct_0 @ sk_C ) @ ( u1_struct_0 @ X0 ) )
      | ( ( k2_tmap_1 @ sk_D @ X0 @ X1 @ X2 )
        = ( k2_partfun1 @ ( k2_struct_0 @ sk_C ) @ ( u1_struct_0 @ X0 ) @ X1 @ ( u1_struct_0 @ X2 ) ) )
      | ~ ( m1_pre_topc @ X2 @ sk_D )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['268','269','270','271','272'])).

thf('274',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0 )
        = ( k2_partfun1 @ ( k2_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( v1_funct_2 @ sk_E @ ( k2_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ sk_E )
      | ( v2_struct_0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['265','273'])).

thf('275',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('276',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('277',plain,(
    v1_funct_2 @ sk_E @ ( k2_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['102','103'])).

thf('278',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('279',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0 )
        = ( k2_partfun1 @ ( k2_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ X0 ) ) )
      | ( v2_struct_0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['274','275','276','277','278'])).

thf('280',plain,
    ( ~ ( l1_pre_topc @ sk_D )
    | ( v2_struct_0 @ sk_D )
    | ( ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_D )
      = ( k2_partfun1 @ ( k2_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ sk_D ) ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['264','279'])).

thf('281',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['8','9'])).

thf('282',plain,
    ( ( k2_struct_0 @ sk_C )
    = ( u1_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['58','63'])).

thf('283',plain,
    ( ( k2_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_C )
    = ( k2_partfun1 @ ( k2_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( k2_struct_0 @ sk_C ) ) ),
    inference(clc,[status(thm)],['130','131'])).

thf('284',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_D )
      = ( k2_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_C ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['280','281','282','283'])).

thf('285',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('286',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_D )
      = ( k2_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_C ) ) ),
    inference(clc,[status(thm)],['284','285'])).

thf('287',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('288',plain,
    ( ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_D )
    = ( k2_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_C ) ),
    inference(clc,[status(thm)],['286','287'])).

thf('289',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['86','87'])).

thf('290',plain,
    ( ( k2_struct_0 @ sk_C )
    = ( u1_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['58','63'])).

thf('291',plain,(
    ! [X43: $i,X44: $i,X45: $i,X46: $i,X47: $i] :
      ( ( v2_struct_0 @ X46 )
      | ~ ( v2_pre_topc @ X46 )
      | ~ ( l1_pre_topc @ X46 )
      | ~ ( v1_funct_1 @ X47 )
      | ~ ( v1_funct_2 @ X47 @ ( u1_struct_0 @ X43 ) @ ( u1_struct_0 @ X46 ) )
      | ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X43 ) @ ( u1_struct_0 @ X46 ) ) ) )
      | ~ ( m1_subset_1 @ X45 @ ( u1_struct_0 @ X43 ) )
      | ( r1_tmap_1 @ X43 @ X46 @ X47 @ X45 )
      | ~ ( r1_tmap_1 @ X44 @ X46 @ ( k2_tmap_1 @ X43 @ X46 @ X47 @ X44 ) @ X45 )
      | ~ ( m1_subset_1 @ X45 @ ( u1_struct_0 @ X44 ) )
      | ~ ( m1_pre_topc @ X44 @ X43 )
      | ~ ( v1_tsep_1 @ X44 @ X43 )
      | ( v2_struct_0 @ X44 )
      | ~ ( l1_pre_topc @ X43 )
      | ~ ( v2_pre_topc @ X43 )
      | ( v2_struct_0 @ X43 ) ) ),
    inference(simplify,[status(thm)],['146'])).

thf('292',plain,(
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
    inference('sup-',[status(thm)],['290','291'])).

thf('293',plain,(
    v2_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['183','184','185'])).

thf('294',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['8','9'])).

thf('295',plain,
    ( ( k2_struct_0 @ sk_C )
    = ( u1_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['58','63'])).

thf('296',plain,
    ( ( k2_struct_0 @ sk_C )
    = ( u1_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['58','63'])).

thf('297',plain,(
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
    inference(demod,[status(thm)],['292','293','294','295','296'])).

thf('298',plain,(
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
    inference('sup-',[status(thm)],['289','297'])).

thf('299',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('300',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('301',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('302',plain,(
    v1_funct_2 @ sk_E @ ( k2_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['102','103'])).

thf('303',plain,(
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
    inference(demod,[status(thm)],['298','299','300','301','302'])).

thf('304',plain,(
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
    inference('sup-',[status(thm)],['288','303'])).

thf('305',plain,
    ( ( k2_struct_0 @ sk_C )
    = ( u1_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['58','63'])).

thf('306',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ X0 )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 )
      | ( v1_tsep_1 @ X0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['162','164'])).

thf('307',plain,
    ( ~ ( v3_pre_topc @ ( k2_struct_0 @ sk_C ) @ sk_D )
    | ~ ( v2_pre_topc @ sk_D )
    | ~ ( l1_pre_topc @ sk_D )
    | ( v1_tsep_1 @ sk_D @ sk_D )
    | ~ ( m1_pre_topc @ sk_D @ sk_D ) ),
    inference('sup-',[status(thm)],['305','306'])).

thf('308',plain,(
    v3_pre_topc @ ( k2_struct_0 @ sk_C ) @ sk_D ),
    inference(demod,[status(thm)],['180','186','187'])).

thf('309',plain,(
    v2_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['183','184','185'])).

thf('310',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['8','9'])).

thf('311',plain,(
    m1_pre_topc @ sk_D @ sk_C ),
    inference(demod,[status(thm)],['5','10','11','16'])).

thf('312',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( l1_pre_topc @ X20 )
      | ~ ( m1_pre_topc @ X21 @ X20 )
      | ( m1_pre_topc @ X21 @ ( g1_pre_topc @ ( u1_struct_0 @ X20 ) @ ( u1_pre_topc @ X20 ) ) )
      | ~ ( l1_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[t65_pre_topc])).

thf('313',plain,
    ( ~ ( l1_pre_topc @ sk_D )
    | ( m1_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) ) )
    | ~ ( l1_pre_topc @ sk_C ) ),
    inference('sup-',[status(thm)],['311','312'])).

thf('314',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['8','9'])).

thf('315',plain,
    ( ( u1_struct_0 @ sk_C )
    = ( k2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('316',plain,
    ( ( g1_pre_topc @ ( k2_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) )
    = sk_D ),
    inference(demod,[status(thm)],['79','80'])).

thf('317',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['14','15'])).

thf('318',plain,(
    m1_pre_topc @ sk_D @ sk_D ),
    inference(demod,[status(thm)],['313','314','315','316','317'])).

thf('319',plain,(
    v1_tsep_1 @ sk_D @ sk_D ),
    inference(demod,[status(thm)],['307','308','309','310','318'])).

thf('320',plain,(
    m1_pre_topc @ sk_D @ sk_D ),
    inference(demod,[status(thm)],['313','314','315','316','317'])).

thf('321',plain,
    ( ( k2_struct_0 @ sk_C )
    = ( u1_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['58','63'])).

thf('322',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_C ) @ X0 )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_D )
      | ~ ( m1_subset_1 @ X0 @ ( k2_struct_0 @ sk_C ) )
      | ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k2_struct_0 @ sk_C ) )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['304','319','320','321'])).

thf('323',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k2_struct_0 @ sk_C ) )
      | ( v2_struct_0 @ sk_D )
      | ~ ( r1_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_C ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['322'])).

thf('324',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ~ ( m1_subset_1 @ sk_F @ ( k2_struct_0 @ sk_C ) )
    | ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['263','323'])).

thf('325',plain,(
    m1_subset_1 @ sk_F @ ( k2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['207','208'])).

thf('326',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['324','325'])).

thf('327',plain,
    ( ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C ) ),
    inference(simplify,[status(thm)],['326'])).

thf('328',plain,(
    ~ ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('329',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['327','328'])).

thf('330',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('331',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D ) ),
    inference(clc,[status(thm)],['329','330'])).

thf('332',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('333',plain,(
    v2_struct_0 @ sk_D ),
    inference(clc,[status(thm)],['331','332'])).

thf('334',plain,(
    $false ),
    inference(demod,[status(thm)],['0','333'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.iQI8Cv0UJR
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 17:36:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.21/0.35  % Number of cores: 8
% 0.21/0.36  % Python version: Python 3.6.8
% 0.21/0.36  % Running in FO mode
% 0.90/1.13  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.90/1.13  % Solved by: fo/fo7.sh
% 0.90/1.13  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.90/1.13  % done 1335 iterations in 0.678s
% 0.90/1.13  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.90/1.13  % SZS output start Refutation
% 0.90/1.13  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.90/1.13  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.90/1.13  thf(sk_C_type, type, sk_C: $i).
% 0.90/1.13  thf(sk_G_type, type, sk_G: $i).
% 0.90/1.13  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.90/1.13  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.90/1.13  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.90/1.13  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.90/1.13  thf(g1_pre_topc_type, type, g1_pre_topc: $i > $i > $i).
% 0.90/1.13  thf(r1_tmap_1_type, type, r1_tmap_1: $i > $i > $i > $i > $o).
% 0.90/1.13  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.90/1.13  thf(v1_tsep_1_type, type, v1_tsep_1: $i > $i > $o).
% 0.90/1.13  thf(sk_E_type, type, sk_E: $i).
% 0.90/1.13  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.90/1.13  thf(sk_A_type, type, sk_A: $i).
% 0.90/1.13  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 0.90/1.13  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.90/1.13  thf(sk_F_type, type, sk_F: $i).
% 0.90/1.13  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.90/1.13  thf(k2_partfun1_type, type, k2_partfun1: $i > $i > $i > $i > $i).
% 0.90/1.13  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.90/1.13  thf(k3_tmap_1_type, type, k3_tmap_1: $i > $i > $i > $i > $i > $i).
% 0.90/1.13  thf(k2_tmap_1_type, type, k2_tmap_1: $i > $i > $i > $i > $i).
% 0.90/1.13  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.90/1.13  thf(sk_D_type, type, sk_D: $i).
% 0.90/1.13  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.90/1.13  thf(sk_B_type, type, sk_B: $i).
% 0.90/1.13  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.90/1.13  thf(t88_tmap_1, conjecture,
% 0.90/1.13    (![A:$i]:
% 0.90/1.13     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.90/1.13       ( ![B:$i]:
% 0.90/1.13         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.90/1.13             ( l1_pre_topc @ B ) ) =>
% 0.90/1.13           ( ![C:$i]:
% 0.90/1.13             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.90/1.13               ( ![D:$i]:
% 0.90/1.13                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.90/1.13                   ( ![E:$i]:
% 0.90/1.13                     ( ( ( v1_funct_1 @ E ) & 
% 0.90/1.13                         ( v1_funct_2 @
% 0.90/1.13                           E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 0.90/1.13                         ( m1_subset_1 @
% 0.90/1.13                           E @ 
% 0.90/1.13                           ( k1_zfmisc_1 @
% 0.90/1.13                             ( k2_zfmisc_1 @
% 0.90/1.13                               ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.90/1.13                       ( ( ( g1_pre_topc @
% 0.90/1.13                             ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) ) =
% 0.90/1.13                           ( D ) ) =>
% 0.90/1.13                         ( ![F:$i]:
% 0.90/1.13                           ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 0.90/1.13                             ( ![G:$i]:
% 0.90/1.13                               ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) ) =>
% 0.90/1.13                                 ( ( ( ( F ) = ( G ) ) & 
% 0.90/1.13                                     ( r1_tmap_1 @
% 0.90/1.13                                       C @ B @ 
% 0.90/1.13                                       ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ G ) ) =>
% 0.90/1.13                                   ( r1_tmap_1 @ D @ B @ E @ F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.90/1.13  thf(zf_stmt_0, negated_conjecture,
% 0.90/1.13    (~( ![A:$i]:
% 0.90/1.13        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.90/1.13            ( l1_pre_topc @ A ) ) =>
% 0.90/1.13          ( ![B:$i]:
% 0.90/1.13            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.90/1.13                ( l1_pre_topc @ B ) ) =>
% 0.90/1.13              ( ![C:$i]:
% 0.90/1.13                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.90/1.13                  ( ![D:$i]:
% 0.90/1.13                    ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.90/1.13                      ( ![E:$i]:
% 0.90/1.13                        ( ( ( v1_funct_1 @ E ) & 
% 0.90/1.13                            ( v1_funct_2 @
% 0.90/1.13                              E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 0.90/1.13                            ( m1_subset_1 @
% 0.90/1.13                              E @ 
% 0.90/1.13                              ( k1_zfmisc_1 @
% 0.90/1.13                                ( k2_zfmisc_1 @
% 0.90/1.13                                  ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.90/1.13                          ( ( ( g1_pre_topc @
% 0.90/1.13                                ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) ) =
% 0.90/1.13                              ( D ) ) =>
% 0.90/1.13                            ( ![F:$i]:
% 0.90/1.13                              ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 0.90/1.13                                ( ![G:$i]:
% 0.90/1.13                                  ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) ) =>
% 0.90/1.13                                    ( ( ( ( F ) = ( G ) ) & 
% 0.90/1.13                                        ( r1_tmap_1 @
% 0.90/1.13                                          C @ B @ 
% 0.90/1.13                                          ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ G ) ) =>
% 0.90/1.13                                      ( r1_tmap_1 @ D @ B @ E @ F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.90/1.13    inference('cnf.neg', [status(esa)], [t88_tmap_1])).
% 0.90/1.13  thf('0', plain, (~ (v2_struct_0 @ sk_D)),
% 0.90/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.13  thf('1', plain,
% 0.90/1.13      (((g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) = (sk_D))),
% 0.90/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.13  thf(t2_tsep_1, axiom,
% 0.90/1.13    (![A:$i]: ( ( l1_pre_topc @ A ) => ( m1_pre_topc @ A @ A ) ))).
% 0.90/1.13  thf('2', plain,
% 0.90/1.13      (![X37 : $i]: ((m1_pre_topc @ X37 @ X37) | ~ (l1_pre_topc @ X37))),
% 0.90/1.13      inference('cnf', [status(esa)], [t2_tsep_1])).
% 0.90/1.13  thf(t59_pre_topc, axiom,
% 0.90/1.13    (![A:$i]:
% 0.90/1.13     ( ( l1_pre_topc @ A ) =>
% 0.90/1.13       ( ![B:$i]:
% 0.90/1.13         ( ( m1_pre_topc @
% 0.90/1.13             B @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) =>
% 0.90/1.13           ( m1_pre_topc @ B @ A ) ) ) ))).
% 0.90/1.13  thf('3', plain,
% 0.90/1.13      (![X15 : $i, X16 : $i]:
% 0.90/1.13         (~ (m1_pre_topc @ X15 @ 
% 0.90/1.13             (g1_pre_topc @ (u1_struct_0 @ X16) @ (u1_pre_topc @ X16)))
% 0.90/1.13          | (m1_pre_topc @ X15 @ X16)
% 0.90/1.13          | ~ (l1_pre_topc @ X16))),
% 0.90/1.13      inference('cnf', [status(esa)], [t59_pre_topc])).
% 0.90/1.13  thf('4', plain,
% 0.90/1.13      (![X0 : $i]:
% 0.90/1.13         (~ (l1_pre_topc @ 
% 0.90/1.13             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.90/1.13          | ~ (l1_pre_topc @ X0)
% 0.90/1.13          | (m1_pre_topc @ 
% 0.90/1.13             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)) @ X0))),
% 0.90/1.13      inference('sup-', [status(thm)], ['2', '3'])).
% 0.90/1.13  thf('5', plain,
% 0.90/1.13      ((~ (l1_pre_topc @ sk_D)
% 0.90/1.13        | (m1_pre_topc @ 
% 0.90/1.13           (g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) @ sk_C)
% 0.90/1.13        | ~ (l1_pre_topc @ sk_C))),
% 0.90/1.13      inference('sup-', [status(thm)], ['1', '4'])).
% 0.90/1.13  thf('6', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.90/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.13  thf(dt_m1_pre_topc, axiom,
% 0.90/1.13    (![A:$i]:
% 0.90/1.13     ( ( l1_pre_topc @ A ) =>
% 0.90/1.13       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.90/1.13  thf('7', plain,
% 0.90/1.13      (![X10 : $i, X11 : $i]:
% 0.90/1.13         (~ (m1_pre_topc @ X10 @ X11)
% 0.90/1.13          | (l1_pre_topc @ X10)
% 0.90/1.13          | ~ (l1_pre_topc @ X11))),
% 0.90/1.13      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.90/1.13  thf('8', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_D))),
% 0.90/1.13      inference('sup-', [status(thm)], ['6', '7'])).
% 0.90/1.13  thf('9', plain, ((l1_pre_topc @ sk_A)),
% 0.90/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.13  thf('10', plain, ((l1_pre_topc @ sk_D)),
% 0.90/1.13      inference('demod', [status(thm)], ['8', '9'])).
% 0.90/1.13  thf('11', plain,
% 0.90/1.13      (((g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) = (sk_D))),
% 0.90/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.13  thf('12', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.90/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.13  thf('13', plain,
% 0.90/1.13      (![X10 : $i, X11 : $i]:
% 0.90/1.13         (~ (m1_pre_topc @ X10 @ X11)
% 0.90/1.13          | (l1_pre_topc @ X10)
% 0.90/1.13          | ~ (l1_pre_topc @ X11))),
% 0.90/1.13      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.90/1.13  thf('14', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_C))),
% 0.90/1.13      inference('sup-', [status(thm)], ['12', '13'])).
% 0.90/1.13  thf('15', plain, ((l1_pre_topc @ sk_A)),
% 0.90/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.13  thf('16', plain, ((l1_pre_topc @ sk_C)),
% 0.90/1.13      inference('demod', [status(thm)], ['14', '15'])).
% 0.90/1.13  thf('17', plain, ((m1_pre_topc @ sk_D @ sk_C)),
% 0.90/1.13      inference('demod', [status(thm)], ['5', '10', '11', '16'])).
% 0.90/1.13  thf(t35_borsuk_1, axiom,
% 0.90/1.13    (![A:$i]:
% 0.90/1.13     ( ( l1_pre_topc @ A ) =>
% 0.90/1.13       ( ![B:$i]:
% 0.90/1.13         ( ( m1_pre_topc @ B @ A ) =>
% 0.90/1.13           ( r1_tarski @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ))).
% 0.90/1.13  thf('18', plain,
% 0.90/1.13      (![X38 : $i, X39 : $i]:
% 0.90/1.13         (~ (m1_pre_topc @ X38 @ X39)
% 0.90/1.13          | (r1_tarski @ (u1_struct_0 @ X38) @ (u1_struct_0 @ X39))
% 0.90/1.13          | ~ (l1_pre_topc @ X39))),
% 0.90/1.13      inference('cnf', [status(esa)], [t35_borsuk_1])).
% 0.90/1.13  thf('19', plain,
% 0.90/1.13      ((~ (l1_pre_topc @ sk_C)
% 0.90/1.13        | (r1_tarski @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_C)))),
% 0.90/1.13      inference('sup-', [status(thm)], ['17', '18'])).
% 0.90/1.13  thf('20', plain, ((l1_pre_topc @ sk_C)),
% 0.90/1.13      inference('demod', [status(thm)], ['14', '15'])).
% 0.90/1.13  thf('21', plain, ((r1_tarski @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_C))),
% 0.90/1.13      inference('demod', [status(thm)], ['19', '20'])).
% 0.90/1.13  thf(d10_xboole_0, axiom,
% 0.90/1.13    (![A:$i,B:$i]:
% 0.90/1.13     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.90/1.13  thf('22', plain,
% 0.90/1.13      (![X0 : $i, X2 : $i]:
% 0.90/1.13         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.90/1.13      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.90/1.13  thf('23', plain,
% 0.90/1.13      ((~ (r1_tarski @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D))
% 0.90/1.14        | ((u1_struct_0 @ sk_C) = (u1_struct_0 @ sk_D)))),
% 0.90/1.14      inference('sup-', [status(thm)], ['21', '22'])).
% 0.90/1.14  thf('24', plain,
% 0.90/1.14      (((g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) = (sk_D))),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf(fc10_tops_1, axiom,
% 0.90/1.14    (![A:$i]:
% 0.90/1.14     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.90/1.14       ( v3_pre_topc @ ( k2_struct_0 @ A ) @ A ) ))).
% 0.90/1.14  thf('25', plain,
% 0.90/1.14      (![X22 : $i]:
% 0.90/1.14         ((v3_pre_topc @ (k2_struct_0 @ X22) @ X22)
% 0.90/1.14          | ~ (l1_pre_topc @ X22)
% 0.90/1.14          | ~ (v2_pre_topc @ X22))),
% 0.90/1.14      inference('cnf', [status(esa)], [fc10_tops_1])).
% 0.90/1.14  thf(d3_struct_0, axiom,
% 0.90/1.14    (![A:$i]:
% 0.90/1.14     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.90/1.14  thf('26', plain,
% 0.90/1.14      (![X8 : $i]:
% 0.90/1.14         (((k2_struct_0 @ X8) = (u1_struct_0 @ X8)) | ~ (l1_struct_0 @ X8))),
% 0.90/1.14      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.90/1.14  thf('27', plain,
% 0.90/1.14      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.90/1.14      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.90/1.14  thf('28', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.90/1.14      inference('simplify', [status(thm)], ['27'])).
% 0.90/1.14  thf(t3_subset, axiom,
% 0.90/1.14    (![A:$i,B:$i]:
% 0.90/1.14     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.90/1.14  thf('29', plain,
% 0.90/1.14      (![X3 : $i, X5 : $i]:
% 0.90/1.14         ((m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X5)) | ~ (r1_tarski @ X3 @ X5))),
% 0.90/1.14      inference('cnf', [status(esa)], [t3_subset])).
% 0.90/1.14  thf('30', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.90/1.14      inference('sup-', [status(thm)], ['28', '29'])).
% 0.90/1.14  thf(t60_pre_topc, axiom,
% 0.90/1.14    (![A:$i]:
% 0.90/1.14     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.90/1.14       ( ![B:$i]:
% 0.90/1.14         ( ( ( v3_pre_topc @ B @ A ) & 
% 0.90/1.14             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) <=>
% 0.90/1.14           ( ( v3_pre_topc @
% 0.90/1.14               B @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) & 
% 0.90/1.14             ( m1_subset_1 @
% 0.90/1.14               B @ 
% 0.90/1.14               ( k1_zfmisc_1 @
% 0.90/1.14                 ( u1_struct_0 @
% 0.90/1.14                   ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ) ) ) ) ))).
% 0.90/1.14  thf('31', plain,
% 0.90/1.14      (![X18 : $i, X19 : $i]:
% 0.90/1.14         (~ (v3_pre_topc @ X19 @ X18)
% 0.90/1.14          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.90/1.14          | (m1_subset_1 @ X19 @ 
% 0.90/1.14             (k1_zfmisc_1 @ 
% 0.90/1.14              (u1_struct_0 @ 
% 0.90/1.14               (g1_pre_topc @ (u1_struct_0 @ X18) @ (u1_pre_topc @ X18)))))
% 0.90/1.14          | ~ (l1_pre_topc @ X18)
% 0.90/1.14          | ~ (v2_pre_topc @ X18))),
% 0.90/1.14      inference('cnf', [status(esa)], [t60_pre_topc])).
% 0.90/1.14  thf('32', plain,
% 0.90/1.14      (![X0 : $i]:
% 0.90/1.14         (~ (v2_pre_topc @ X0)
% 0.90/1.14          | ~ (l1_pre_topc @ X0)
% 0.90/1.14          | (m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 0.90/1.14             (k1_zfmisc_1 @ 
% 0.90/1.14              (u1_struct_0 @ 
% 0.90/1.14               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))))
% 0.90/1.14          | ~ (v3_pre_topc @ (u1_struct_0 @ X0) @ X0))),
% 0.90/1.14      inference('sup-', [status(thm)], ['30', '31'])).
% 0.90/1.14  thf('33', plain,
% 0.90/1.14      (![X0 : $i]:
% 0.90/1.14         (~ (v3_pre_topc @ (k2_struct_0 @ X0) @ X0)
% 0.90/1.14          | ~ (l1_struct_0 @ X0)
% 0.90/1.14          | (m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 0.90/1.14             (k1_zfmisc_1 @ 
% 0.90/1.14              (u1_struct_0 @ 
% 0.90/1.14               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))))
% 0.90/1.14          | ~ (l1_pre_topc @ X0)
% 0.90/1.14          | ~ (v2_pre_topc @ X0))),
% 0.90/1.14      inference('sup-', [status(thm)], ['26', '32'])).
% 0.90/1.14  thf('34', plain,
% 0.90/1.14      (![X0 : $i]:
% 0.90/1.14         (~ (v2_pre_topc @ X0)
% 0.90/1.14          | ~ (l1_pre_topc @ X0)
% 0.90/1.14          | ~ (v2_pre_topc @ X0)
% 0.90/1.14          | ~ (l1_pre_topc @ X0)
% 0.90/1.14          | (m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 0.90/1.14             (k1_zfmisc_1 @ 
% 0.90/1.14              (u1_struct_0 @ 
% 0.90/1.14               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))))
% 0.90/1.14          | ~ (l1_struct_0 @ X0))),
% 0.90/1.14      inference('sup-', [status(thm)], ['25', '33'])).
% 0.90/1.14  thf('35', plain,
% 0.90/1.14      (![X0 : $i]:
% 0.90/1.14         (~ (l1_struct_0 @ X0)
% 0.90/1.14          | (m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 0.90/1.14             (k1_zfmisc_1 @ 
% 0.90/1.14              (u1_struct_0 @ 
% 0.90/1.14               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))))
% 0.90/1.14          | ~ (l1_pre_topc @ X0)
% 0.90/1.14          | ~ (v2_pre_topc @ X0))),
% 0.90/1.14      inference('simplify', [status(thm)], ['34'])).
% 0.90/1.14  thf('36', plain,
% 0.90/1.14      (((m1_subset_1 @ (u1_struct_0 @ sk_C) @ 
% 0.90/1.14         (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))
% 0.90/1.14        | ~ (v2_pre_topc @ sk_C)
% 0.90/1.14        | ~ (l1_pre_topc @ sk_C)
% 0.90/1.14        | ~ (l1_struct_0 @ sk_C))),
% 0.90/1.14      inference('sup+', [status(thm)], ['24', '35'])).
% 0.90/1.14  thf('37', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf(cc1_pre_topc, axiom,
% 0.90/1.14    (![A:$i]:
% 0.90/1.14     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.90/1.14       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( v2_pre_topc @ B ) ) ) ))).
% 0.90/1.14  thf('38', plain,
% 0.90/1.14      (![X6 : $i, X7 : $i]:
% 0.90/1.14         (~ (m1_pre_topc @ X6 @ X7)
% 0.90/1.14          | (v2_pre_topc @ X6)
% 0.90/1.14          | ~ (l1_pre_topc @ X7)
% 0.90/1.14          | ~ (v2_pre_topc @ X7))),
% 0.90/1.14      inference('cnf', [status(esa)], [cc1_pre_topc])).
% 0.90/1.14  thf('39', plain,
% 0.90/1.14      ((~ (v2_pre_topc @ sk_A) | ~ (l1_pre_topc @ sk_A) | (v2_pre_topc @ sk_C))),
% 0.90/1.14      inference('sup-', [status(thm)], ['37', '38'])).
% 0.90/1.14  thf('40', plain, ((v2_pre_topc @ sk_A)),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf('41', plain, ((l1_pre_topc @ sk_A)),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf('42', plain, ((v2_pre_topc @ sk_C)),
% 0.90/1.14      inference('demod', [status(thm)], ['39', '40', '41'])).
% 0.90/1.14  thf('43', plain, ((l1_pre_topc @ sk_C)),
% 0.90/1.14      inference('demod', [status(thm)], ['14', '15'])).
% 0.90/1.14  thf('44', plain, ((l1_pre_topc @ sk_C)),
% 0.90/1.14      inference('demod', [status(thm)], ['14', '15'])).
% 0.90/1.14  thf(dt_l1_pre_topc, axiom,
% 0.90/1.14    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.90/1.14  thf('45', plain, (![X9 : $i]: ((l1_struct_0 @ X9) | ~ (l1_pre_topc @ X9))),
% 0.90/1.14      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.90/1.14  thf('46', plain, ((l1_struct_0 @ sk_C)),
% 0.90/1.14      inference('sup-', [status(thm)], ['44', '45'])).
% 0.90/1.14  thf('47', plain,
% 0.90/1.14      ((m1_subset_1 @ (u1_struct_0 @ sk_C) @ 
% 0.90/1.14        (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))),
% 0.90/1.14      inference('demod', [status(thm)], ['36', '42', '43', '46'])).
% 0.90/1.14  thf('48', plain,
% 0.90/1.14      (![X3 : $i, X4 : $i]:
% 0.90/1.14         ((r1_tarski @ X3 @ X4) | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4)))),
% 0.90/1.14      inference('cnf', [status(esa)], [t3_subset])).
% 0.90/1.14  thf('49', plain, ((r1_tarski @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D))),
% 0.90/1.14      inference('sup-', [status(thm)], ['47', '48'])).
% 0.90/1.14  thf('50', plain, (((u1_struct_0 @ sk_C) = (u1_struct_0 @ sk_D))),
% 0.90/1.14      inference('demod', [status(thm)], ['23', '49'])).
% 0.90/1.14  thf('51', plain,
% 0.90/1.14      (![X8 : $i]:
% 0.90/1.14         (((k2_struct_0 @ X8) = (u1_struct_0 @ X8)) | ~ (l1_struct_0 @ X8))),
% 0.90/1.14      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.90/1.14  thf('52', plain, (((u1_struct_0 @ sk_C) = (u1_struct_0 @ sk_D))),
% 0.90/1.14      inference('demod', [status(thm)], ['23', '49'])).
% 0.90/1.14  thf('53', plain,
% 0.90/1.14      ((((u1_struct_0 @ sk_C) = (k2_struct_0 @ sk_D)) | ~ (l1_struct_0 @ sk_D))),
% 0.90/1.14      inference('sup+', [status(thm)], ['51', '52'])).
% 0.90/1.14  thf('54', plain, ((l1_pre_topc @ sk_D)),
% 0.90/1.14      inference('demod', [status(thm)], ['8', '9'])).
% 0.90/1.14  thf('55', plain, (![X9 : $i]: ((l1_struct_0 @ X9) | ~ (l1_pre_topc @ X9))),
% 0.90/1.14      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.90/1.14  thf('56', plain, ((l1_struct_0 @ sk_D)),
% 0.90/1.14      inference('sup-', [status(thm)], ['54', '55'])).
% 0.90/1.14  thf('57', plain, (((u1_struct_0 @ sk_C) = (k2_struct_0 @ sk_D))),
% 0.90/1.14      inference('demod', [status(thm)], ['53', '56'])).
% 0.90/1.14  thf('58', plain, (((k2_struct_0 @ sk_D) = (u1_struct_0 @ sk_D))),
% 0.90/1.14      inference('demod', [status(thm)], ['50', '57'])).
% 0.90/1.14  thf('59', plain,
% 0.90/1.14      (![X8 : $i]:
% 0.90/1.14         (((k2_struct_0 @ X8) = (u1_struct_0 @ X8)) | ~ (l1_struct_0 @ X8))),
% 0.90/1.14      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.90/1.14  thf('60', plain, (((u1_struct_0 @ sk_C) = (k2_struct_0 @ sk_D))),
% 0.90/1.14      inference('demod', [status(thm)], ['53', '56'])).
% 0.90/1.14  thf('61', plain,
% 0.90/1.14      ((((k2_struct_0 @ sk_C) = (k2_struct_0 @ sk_D)) | ~ (l1_struct_0 @ sk_C))),
% 0.90/1.14      inference('sup+', [status(thm)], ['59', '60'])).
% 0.90/1.14  thf('62', plain, ((l1_struct_0 @ sk_C)),
% 0.90/1.14      inference('sup-', [status(thm)], ['44', '45'])).
% 0.90/1.14  thf('63', plain, (((k2_struct_0 @ sk_C) = (k2_struct_0 @ sk_D))),
% 0.90/1.14      inference('demod', [status(thm)], ['61', '62'])).
% 0.90/1.14  thf('64', plain, (((k2_struct_0 @ sk_C) = (u1_struct_0 @ sk_D))),
% 0.90/1.14      inference('demod', [status(thm)], ['58', '63'])).
% 0.90/1.14  thf('65', plain,
% 0.90/1.14      ((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.90/1.14        (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_G)),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf('66', plain, (((sk_F) = (sk_G))),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf('67', plain,
% 0.90/1.14      ((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.90/1.14        (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_F)),
% 0.90/1.14      inference('demod', [status(thm)], ['65', '66'])).
% 0.90/1.14  thf('68', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf('69', plain, (((u1_struct_0 @ sk_C) = (k2_struct_0 @ sk_D))),
% 0.90/1.14      inference('demod', [status(thm)], ['53', '56'])).
% 0.90/1.14  thf('70', plain, (((k2_struct_0 @ sk_C) = (k2_struct_0 @ sk_D))),
% 0.90/1.14      inference('demod', [status(thm)], ['61', '62'])).
% 0.90/1.14  thf('71', plain, (((u1_struct_0 @ sk_C) = (k2_struct_0 @ sk_C))),
% 0.90/1.14      inference('demod', [status(thm)], ['69', '70'])).
% 0.90/1.14  thf('72', plain,
% 0.90/1.14      (![X37 : $i]: ((m1_pre_topc @ X37 @ X37) | ~ (l1_pre_topc @ X37))),
% 0.90/1.14      inference('cnf', [status(esa)], [t2_tsep_1])).
% 0.90/1.14  thf(t65_pre_topc, axiom,
% 0.90/1.14    (![A:$i]:
% 0.90/1.14     ( ( l1_pre_topc @ A ) =>
% 0.90/1.14       ( ![B:$i]:
% 0.90/1.14         ( ( l1_pre_topc @ B ) =>
% 0.90/1.14           ( ( m1_pre_topc @ A @ B ) <=>
% 0.90/1.14             ( m1_pre_topc @
% 0.90/1.14               A @ ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ) ))).
% 0.90/1.14  thf('73', plain,
% 0.90/1.14      (![X20 : $i, X21 : $i]:
% 0.90/1.14         (~ (l1_pre_topc @ X20)
% 0.90/1.14          | ~ (m1_pre_topc @ X21 @ X20)
% 0.90/1.14          | (m1_pre_topc @ X21 @ 
% 0.90/1.14             (g1_pre_topc @ (u1_struct_0 @ X20) @ (u1_pre_topc @ X20)))
% 0.90/1.14          | ~ (l1_pre_topc @ X21))),
% 0.90/1.14      inference('cnf', [status(esa)], [t65_pre_topc])).
% 0.90/1.14  thf('74', plain,
% 0.90/1.14      (![X0 : $i]:
% 0.90/1.14         (~ (l1_pre_topc @ X0)
% 0.90/1.14          | ~ (l1_pre_topc @ X0)
% 0.90/1.14          | (m1_pre_topc @ X0 @ 
% 0.90/1.14             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.90/1.14          | ~ (l1_pre_topc @ X0))),
% 0.90/1.14      inference('sup-', [status(thm)], ['72', '73'])).
% 0.90/1.14  thf('75', plain,
% 0.90/1.14      (![X0 : $i]:
% 0.90/1.14         ((m1_pre_topc @ X0 @ 
% 0.90/1.14           (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.90/1.14          | ~ (l1_pre_topc @ X0))),
% 0.90/1.14      inference('simplify', [status(thm)], ['74'])).
% 0.90/1.14  thf('76', plain,
% 0.90/1.14      (((m1_pre_topc @ sk_C @ 
% 0.90/1.14         (g1_pre_topc @ (k2_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)))
% 0.90/1.14        | ~ (l1_pre_topc @ sk_C))),
% 0.90/1.14      inference('sup+', [status(thm)], ['71', '75'])).
% 0.90/1.14  thf('77', plain,
% 0.90/1.14      (![X8 : $i]:
% 0.90/1.14         (((k2_struct_0 @ X8) = (u1_struct_0 @ X8)) | ~ (l1_struct_0 @ X8))),
% 0.90/1.14      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.90/1.14  thf('78', plain,
% 0.90/1.14      (((g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) = (sk_D))),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf('79', plain,
% 0.90/1.14      ((((g1_pre_topc @ (k2_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) = (sk_D))
% 0.90/1.14        | ~ (l1_struct_0 @ sk_C))),
% 0.90/1.14      inference('sup+', [status(thm)], ['77', '78'])).
% 0.90/1.14  thf('80', plain, ((l1_struct_0 @ sk_C)),
% 0.90/1.14      inference('sup-', [status(thm)], ['44', '45'])).
% 0.90/1.14  thf('81', plain,
% 0.90/1.14      (((g1_pre_topc @ (k2_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) = (sk_D))),
% 0.90/1.14      inference('demod', [status(thm)], ['79', '80'])).
% 0.90/1.14  thf('82', plain, ((l1_pre_topc @ sk_C)),
% 0.90/1.14      inference('demod', [status(thm)], ['14', '15'])).
% 0.90/1.14  thf('83', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 0.90/1.14      inference('demod', [status(thm)], ['76', '81', '82'])).
% 0.90/1.14  thf('84', plain,
% 0.90/1.14      ((m1_subset_1 @ sk_E @ 
% 0.90/1.14        (k1_zfmisc_1 @ 
% 0.90/1.14         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf('85', plain, (((u1_struct_0 @ sk_C) = (u1_struct_0 @ sk_D))),
% 0.90/1.14      inference('demod', [status(thm)], ['23', '49'])).
% 0.90/1.14  thf('86', plain,
% 0.90/1.14      ((m1_subset_1 @ sk_E @ 
% 0.90/1.14        (k1_zfmisc_1 @ 
% 0.90/1.14         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 0.90/1.14      inference('demod', [status(thm)], ['84', '85'])).
% 0.90/1.14  thf('87', plain, (((u1_struct_0 @ sk_C) = (k2_struct_0 @ sk_C))),
% 0.90/1.14      inference('demod', [status(thm)], ['69', '70'])).
% 0.90/1.14  thf('88', plain,
% 0.90/1.14      ((m1_subset_1 @ sk_E @ 
% 0.90/1.14        (k1_zfmisc_1 @ 
% 0.90/1.14         (k2_zfmisc_1 @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 0.90/1.14      inference('demod', [status(thm)], ['86', '87'])).
% 0.90/1.14  thf('89', plain, (((k2_struct_0 @ sk_C) = (u1_struct_0 @ sk_D))),
% 0.90/1.14      inference('demod', [status(thm)], ['58', '63'])).
% 0.90/1.14  thf(d5_tmap_1, axiom,
% 0.90/1.14    (![A:$i]:
% 0.90/1.14     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.90/1.14       ( ![B:$i]:
% 0.90/1.14         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.90/1.14             ( l1_pre_topc @ B ) ) =>
% 0.90/1.14           ( ![C:$i]:
% 0.90/1.14             ( ( m1_pre_topc @ C @ A ) =>
% 0.90/1.14               ( ![D:$i]:
% 0.90/1.14                 ( ( m1_pre_topc @ D @ A ) =>
% 0.90/1.14                   ( ![E:$i]:
% 0.90/1.14                     ( ( ( v1_funct_1 @ E ) & 
% 0.90/1.14                         ( v1_funct_2 @
% 0.90/1.14                           E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 0.90/1.14                         ( m1_subset_1 @
% 0.90/1.14                           E @ 
% 0.90/1.14                           ( k1_zfmisc_1 @
% 0.90/1.14                             ( k2_zfmisc_1 @
% 0.90/1.14                               ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.90/1.14                       ( ( m1_pre_topc @ D @ C ) =>
% 0.90/1.14                         ( ( k3_tmap_1 @ A @ B @ C @ D @ E ) =
% 0.90/1.14                           ( k2_partfun1 @
% 0.90/1.14                             ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ E @ 
% 0.90/1.14                             ( u1_struct_0 @ D ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.90/1.14  thf('90', plain,
% 0.90/1.14      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 0.90/1.14         ((v2_struct_0 @ X27)
% 0.90/1.14          | ~ (v2_pre_topc @ X27)
% 0.90/1.14          | ~ (l1_pre_topc @ X27)
% 0.90/1.14          | ~ (m1_pre_topc @ X28 @ X29)
% 0.90/1.14          | ~ (m1_pre_topc @ X28 @ X30)
% 0.90/1.14          | ((k3_tmap_1 @ X29 @ X27 @ X30 @ X28 @ X31)
% 0.90/1.14              = (k2_partfun1 @ (u1_struct_0 @ X30) @ (u1_struct_0 @ X27) @ 
% 0.90/1.14                 X31 @ (u1_struct_0 @ X28)))
% 0.90/1.14          | ~ (m1_subset_1 @ X31 @ 
% 0.90/1.14               (k1_zfmisc_1 @ 
% 0.90/1.14                (k2_zfmisc_1 @ (u1_struct_0 @ X30) @ (u1_struct_0 @ X27))))
% 0.90/1.14          | ~ (v1_funct_2 @ X31 @ (u1_struct_0 @ X30) @ (u1_struct_0 @ X27))
% 0.90/1.14          | ~ (v1_funct_1 @ X31)
% 0.90/1.14          | ~ (m1_pre_topc @ X30 @ X29)
% 0.90/1.14          | ~ (l1_pre_topc @ X29)
% 0.90/1.14          | ~ (v2_pre_topc @ X29)
% 0.90/1.14          | (v2_struct_0 @ X29))),
% 0.90/1.14      inference('cnf', [status(esa)], [d5_tmap_1])).
% 0.90/1.14  thf('91', plain,
% 0.90/1.14      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.90/1.14         (~ (m1_subset_1 @ X1 @ 
% 0.90/1.14             (k1_zfmisc_1 @ 
% 0.90/1.14              (k2_zfmisc_1 @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ X0))))
% 0.90/1.14          | (v2_struct_0 @ X2)
% 0.90/1.14          | ~ (v2_pre_topc @ X2)
% 0.90/1.14          | ~ (l1_pre_topc @ X2)
% 0.90/1.14          | ~ (m1_pre_topc @ sk_D @ X2)
% 0.90/1.14          | ~ (v1_funct_1 @ X1)
% 0.90/1.14          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ X0))
% 0.90/1.14          | ((k3_tmap_1 @ X2 @ X0 @ sk_D @ X3 @ X1)
% 0.90/1.14              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ X0) @ 
% 0.90/1.14                 X1 @ (u1_struct_0 @ X3)))
% 0.90/1.14          | ~ (m1_pre_topc @ X3 @ sk_D)
% 0.90/1.14          | ~ (m1_pre_topc @ X3 @ X2)
% 0.90/1.14          | ~ (l1_pre_topc @ X0)
% 0.90/1.14          | ~ (v2_pre_topc @ X0)
% 0.90/1.14          | (v2_struct_0 @ X0))),
% 0.90/1.14      inference('sup-', [status(thm)], ['89', '90'])).
% 0.90/1.14  thf('92', plain, (((k2_struct_0 @ sk_C) = (u1_struct_0 @ sk_D))),
% 0.90/1.14      inference('demod', [status(thm)], ['58', '63'])).
% 0.90/1.14  thf('93', plain, (((k2_struct_0 @ sk_C) = (u1_struct_0 @ sk_D))),
% 0.90/1.14      inference('demod', [status(thm)], ['58', '63'])).
% 0.90/1.14  thf('94', plain,
% 0.90/1.14      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.90/1.14         (~ (m1_subset_1 @ X1 @ 
% 0.90/1.14             (k1_zfmisc_1 @ 
% 0.90/1.14              (k2_zfmisc_1 @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ X0))))
% 0.90/1.14          | (v2_struct_0 @ X2)
% 0.90/1.14          | ~ (v2_pre_topc @ X2)
% 0.90/1.14          | ~ (l1_pre_topc @ X2)
% 0.90/1.14          | ~ (m1_pre_topc @ sk_D @ X2)
% 0.90/1.14          | ~ (v1_funct_1 @ X1)
% 0.90/1.14          | ~ (v1_funct_2 @ X1 @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ X0))
% 0.90/1.14          | ((k3_tmap_1 @ X2 @ X0 @ sk_D @ X3 @ X1)
% 0.90/1.14              = (k2_partfun1 @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ X0) @ 
% 0.90/1.14                 X1 @ (u1_struct_0 @ X3)))
% 0.90/1.14          | ~ (m1_pre_topc @ X3 @ sk_D)
% 0.90/1.14          | ~ (m1_pre_topc @ X3 @ X2)
% 0.90/1.14          | ~ (l1_pre_topc @ X0)
% 0.90/1.14          | ~ (v2_pre_topc @ X0)
% 0.90/1.14          | (v2_struct_0 @ X0))),
% 0.90/1.14      inference('demod', [status(thm)], ['91', '92', '93'])).
% 0.90/1.14  thf('95', plain,
% 0.90/1.14      (![X0 : $i, X1 : $i]:
% 0.90/1.14         ((v2_struct_0 @ sk_B)
% 0.90/1.14          | ~ (v2_pre_topc @ sk_B)
% 0.90/1.14          | ~ (l1_pre_topc @ sk_B)
% 0.90/1.14          | ~ (m1_pre_topc @ X1 @ X0)
% 0.90/1.14          | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.90/1.14          | ((k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E)
% 0.90/1.14              = (k2_partfun1 @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.90/1.14                 sk_E @ (u1_struct_0 @ X1)))
% 0.90/1.14          | ~ (v1_funct_2 @ sk_E @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))
% 0.90/1.14          | ~ (v1_funct_1 @ sk_E)
% 0.90/1.14          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.90/1.14          | ~ (l1_pre_topc @ X0)
% 0.90/1.14          | ~ (v2_pre_topc @ X0)
% 0.90/1.14          | (v2_struct_0 @ X0))),
% 0.90/1.14      inference('sup-', [status(thm)], ['88', '94'])).
% 0.90/1.14  thf('96', plain, ((v2_pre_topc @ sk_B)),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf('97', plain, ((l1_pre_topc @ sk_B)),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf('98', plain,
% 0.90/1.14      (![X8 : $i]:
% 0.90/1.14         (((k2_struct_0 @ X8) = (u1_struct_0 @ X8)) | ~ (l1_struct_0 @ X8))),
% 0.90/1.14      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.90/1.14  thf('99', plain,
% 0.90/1.14      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf('100', plain,
% 0.90/1.14      (((v1_funct_2 @ sk_E @ (k2_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.90/1.14        | ~ (l1_struct_0 @ sk_D))),
% 0.90/1.14      inference('sup+', [status(thm)], ['98', '99'])).
% 0.90/1.14  thf('101', plain, ((l1_struct_0 @ sk_D)),
% 0.90/1.14      inference('sup-', [status(thm)], ['54', '55'])).
% 0.90/1.14  thf('102', plain,
% 0.90/1.14      ((v1_funct_2 @ sk_E @ (k2_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 0.90/1.14      inference('demod', [status(thm)], ['100', '101'])).
% 0.90/1.14  thf('103', plain, (((k2_struct_0 @ sk_C) = (k2_struct_0 @ sk_D))),
% 0.90/1.14      inference('demod', [status(thm)], ['61', '62'])).
% 0.90/1.14  thf('104', plain,
% 0.90/1.14      ((v1_funct_2 @ sk_E @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 0.90/1.14      inference('demod', [status(thm)], ['102', '103'])).
% 0.90/1.14  thf('105', plain, ((v1_funct_1 @ sk_E)),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf('106', plain,
% 0.90/1.14      (![X0 : $i, X1 : $i]:
% 0.90/1.14         ((v2_struct_0 @ sk_B)
% 0.90/1.14          | ~ (m1_pre_topc @ X1 @ X0)
% 0.90/1.14          | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.90/1.14          | ((k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E)
% 0.90/1.14              = (k2_partfun1 @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.90/1.14                 sk_E @ (u1_struct_0 @ X1)))
% 0.90/1.14          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.90/1.14          | ~ (l1_pre_topc @ X0)
% 0.90/1.14          | ~ (v2_pre_topc @ X0)
% 0.90/1.14          | (v2_struct_0 @ X0))),
% 0.90/1.14      inference('demod', [status(thm)], ['95', '96', '97', '104', '105'])).
% 0.90/1.14  thf('107', plain,
% 0.90/1.14      (![X0 : $i]:
% 0.90/1.14         ((v2_struct_0 @ X0)
% 0.90/1.14          | ~ (v2_pre_topc @ X0)
% 0.90/1.14          | ~ (l1_pre_topc @ X0)
% 0.90/1.14          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.90/1.14          | ((k3_tmap_1 @ X0 @ sk_B @ sk_D @ sk_C @ sk_E)
% 0.90/1.14              = (k2_partfun1 @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.90/1.14                 sk_E @ (u1_struct_0 @ sk_C)))
% 0.90/1.14          | ~ (m1_pre_topc @ sk_C @ X0)
% 0.90/1.14          | (v2_struct_0 @ sk_B))),
% 0.90/1.14      inference('sup-', [status(thm)], ['83', '106'])).
% 0.90/1.14  thf('108', plain, (((u1_struct_0 @ sk_C) = (k2_struct_0 @ sk_C))),
% 0.90/1.14      inference('demod', [status(thm)], ['69', '70'])).
% 0.90/1.14  thf('109', plain,
% 0.90/1.14      (![X37 : $i]: ((m1_pre_topc @ X37 @ X37) | ~ (l1_pre_topc @ X37))),
% 0.90/1.14      inference('cnf', [status(esa)], [t2_tsep_1])).
% 0.90/1.14  thf('110', plain,
% 0.90/1.14      ((m1_subset_1 @ sk_E @ 
% 0.90/1.14        (k1_zfmisc_1 @ 
% 0.90/1.14         (k2_zfmisc_1 @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 0.90/1.14      inference('demod', [status(thm)], ['86', '87'])).
% 0.90/1.14  thf('111', plain,
% 0.90/1.14      (![X8 : $i]:
% 0.90/1.14         (((k2_struct_0 @ X8) = (u1_struct_0 @ X8)) | ~ (l1_struct_0 @ X8))),
% 0.90/1.14      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.90/1.14  thf(d4_tmap_1, axiom,
% 0.90/1.14    (![A:$i]:
% 0.90/1.14     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.90/1.14       ( ![B:$i]:
% 0.90/1.14         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.90/1.14             ( l1_pre_topc @ B ) ) =>
% 0.90/1.14           ( ![C:$i]:
% 0.90/1.14             ( ( ( v1_funct_1 @ C ) & 
% 0.90/1.14                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.90/1.14                 ( m1_subset_1 @
% 0.90/1.14                   C @ 
% 0.90/1.14                   ( k1_zfmisc_1 @
% 0.90/1.14                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.90/1.14               ( ![D:$i]:
% 0.90/1.14                 ( ( m1_pre_topc @ D @ A ) =>
% 0.90/1.14                   ( ( k2_tmap_1 @ A @ B @ C @ D ) =
% 0.90/1.14                     ( k2_partfun1 @
% 0.90/1.14                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ 
% 0.90/1.14                       ( u1_struct_0 @ D ) ) ) ) ) ) ) ) ) ))).
% 0.90/1.14  thf('112', plain,
% 0.90/1.14      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 0.90/1.14         ((v2_struct_0 @ X23)
% 0.90/1.14          | ~ (v2_pre_topc @ X23)
% 0.90/1.14          | ~ (l1_pre_topc @ X23)
% 0.90/1.14          | ~ (m1_pre_topc @ X24 @ X25)
% 0.90/1.14          | ((k2_tmap_1 @ X25 @ X23 @ X26 @ X24)
% 0.90/1.14              = (k2_partfun1 @ (u1_struct_0 @ X25) @ (u1_struct_0 @ X23) @ 
% 0.90/1.14                 X26 @ (u1_struct_0 @ X24)))
% 0.90/1.14          | ~ (m1_subset_1 @ X26 @ 
% 0.90/1.14               (k1_zfmisc_1 @ 
% 0.90/1.14                (k2_zfmisc_1 @ (u1_struct_0 @ X25) @ (u1_struct_0 @ X23))))
% 0.90/1.14          | ~ (v1_funct_2 @ X26 @ (u1_struct_0 @ X25) @ (u1_struct_0 @ X23))
% 0.90/1.14          | ~ (v1_funct_1 @ X26)
% 0.90/1.14          | ~ (l1_pre_topc @ X25)
% 0.90/1.14          | ~ (v2_pre_topc @ X25)
% 0.90/1.14          | (v2_struct_0 @ X25))),
% 0.90/1.14      inference('cnf', [status(esa)], [d4_tmap_1])).
% 0.90/1.14  thf('113', plain,
% 0.90/1.14      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.90/1.14         (~ (m1_subset_1 @ X2 @ 
% 0.90/1.14             (k1_zfmisc_1 @ 
% 0.90/1.14              (k2_zfmisc_1 @ (k2_struct_0 @ X0) @ (u1_struct_0 @ X1))))
% 0.90/1.14          | ~ (l1_struct_0 @ X0)
% 0.90/1.14          | (v2_struct_0 @ X0)
% 0.90/1.14          | ~ (v2_pre_topc @ X0)
% 0.90/1.14          | ~ (l1_pre_topc @ X0)
% 0.90/1.14          | ~ (v1_funct_1 @ X2)
% 0.90/1.14          | ~ (v1_funct_2 @ X2 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X1))
% 0.90/1.14          | ((k2_tmap_1 @ X0 @ X1 @ X2 @ X3)
% 0.90/1.14              = (k2_partfun1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X1) @ X2 @ 
% 0.90/1.14                 (u1_struct_0 @ X3)))
% 0.90/1.14          | ~ (m1_pre_topc @ X3 @ X0)
% 0.90/1.14          | ~ (l1_pre_topc @ X1)
% 0.90/1.14          | ~ (v2_pre_topc @ X1)
% 0.90/1.14          | (v2_struct_0 @ X1))),
% 0.90/1.14      inference('sup-', [status(thm)], ['111', '112'])).
% 0.90/1.14  thf('114', plain,
% 0.90/1.14      (![X0 : $i]:
% 0.90/1.14         ((v2_struct_0 @ sk_B)
% 0.90/1.14          | ~ (v2_pre_topc @ sk_B)
% 0.90/1.14          | ~ (l1_pre_topc @ sk_B)
% 0.90/1.14          | ~ (m1_pre_topc @ X0 @ sk_C)
% 0.90/1.14          | ((k2_tmap_1 @ sk_C @ sk_B @ sk_E @ X0)
% 0.90/1.14              = (k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.90/1.14                 sk_E @ (u1_struct_0 @ X0)))
% 0.90/1.14          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))
% 0.90/1.14          | ~ (v1_funct_1 @ sk_E)
% 0.90/1.14          | ~ (l1_pre_topc @ sk_C)
% 0.90/1.14          | ~ (v2_pre_topc @ sk_C)
% 0.90/1.14          | (v2_struct_0 @ sk_C)
% 0.90/1.14          | ~ (l1_struct_0 @ sk_C))),
% 0.90/1.14      inference('sup-', [status(thm)], ['110', '113'])).
% 0.90/1.14  thf('115', plain, ((v2_pre_topc @ sk_B)),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf('116', plain, ((l1_pre_topc @ sk_B)),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf('117', plain, (((u1_struct_0 @ sk_C) = (k2_struct_0 @ sk_C))),
% 0.90/1.14      inference('demod', [status(thm)], ['69', '70'])).
% 0.90/1.14  thf('118', plain, (((u1_struct_0 @ sk_C) = (k2_struct_0 @ sk_C))),
% 0.90/1.14      inference('demod', [status(thm)], ['69', '70'])).
% 0.90/1.14  thf('119', plain,
% 0.90/1.14      ((v1_funct_2 @ sk_E @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 0.90/1.14      inference('demod', [status(thm)], ['102', '103'])).
% 0.90/1.14  thf('120', plain, ((v1_funct_1 @ sk_E)),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf('121', plain, ((l1_pre_topc @ sk_C)),
% 0.90/1.14      inference('demod', [status(thm)], ['14', '15'])).
% 0.90/1.14  thf('122', plain, ((v2_pre_topc @ sk_C)),
% 0.90/1.14      inference('demod', [status(thm)], ['39', '40', '41'])).
% 0.90/1.14  thf('123', plain, ((l1_struct_0 @ sk_C)),
% 0.90/1.14      inference('sup-', [status(thm)], ['44', '45'])).
% 0.90/1.14  thf('124', plain,
% 0.90/1.14      (![X0 : $i]:
% 0.90/1.14         ((v2_struct_0 @ sk_B)
% 0.90/1.14          | ~ (m1_pre_topc @ X0 @ sk_C)
% 0.90/1.14          | ((k2_tmap_1 @ sk_C @ sk_B @ sk_E @ X0)
% 0.90/1.14              = (k2_partfun1 @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.90/1.14                 sk_E @ (u1_struct_0 @ X0)))
% 0.90/1.14          | (v2_struct_0 @ sk_C))),
% 0.90/1.14      inference('demod', [status(thm)],
% 0.90/1.14                ['114', '115', '116', '117', '118', '119', '120', '121', 
% 0.90/1.14                 '122', '123'])).
% 0.90/1.14  thf('125', plain,
% 0.90/1.14      ((~ (l1_pre_topc @ sk_C)
% 0.90/1.14        | (v2_struct_0 @ sk_C)
% 0.90/1.14        | ((k2_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_C)
% 0.90/1.14            = (k2_partfun1 @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.90/1.14               sk_E @ (u1_struct_0 @ sk_C)))
% 0.90/1.14        | (v2_struct_0 @ sk_B))),
% 0.90/1.14      inference('sup-', [status(thm)], ['109', '124'])).
% 0.90/1.14  thf('126', plain, ((l1_pre_topc @ sk_C)),
% 0.90/1.14      inference('demod', [status(thm)], ['14', '15'])).
% 0.90/1.14  thf('127', plain, (((u1_struct_0 @ sk_C) = (k2_struct_0 @ sk_C))),
% 0.90/1.14      inference('demod', [status(thm)], ['69', '70'])).
% 0.90/1.14  thf('128', plain,
% 0.90/1.14      (((v2_struct_0 @ sk_C)
% 0.90/1.14        | ((k2_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_C)
% 0.90/1.14            = (k2_partfun1 @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.90/1.14               sk_E @ (k2_struct_0 @ sk_C)))
% 0.90/1.14        | (v2_struct_0 @ sk_B))),
% 0.90/1.14      inference('demod', [status(thm)], ['125', '126', '127'])).
% 0.90/1.14  thf('129', plain, (~ (v2_struct_0 @ sk_C)),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf('130', plain,
% 0.90/1.14      (((v2_struct_0 @ sk_B)
% 0.90/1.14        | ((k2_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_C)
% 0.90/1.14            = (k2_partfun1 @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.90/1.14               sk_E @ (k2_struct_0 @ sk_C))))),
% 0.90/1.14      inference('clc', [status(thm)], ['128', '129'])).
% 0.90/1.14  thf('131', plain, (~ (v2_struct_0 @ sk_B)),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf('132', plain,
% 0.90/1.14      (((k2_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_C)
% 0.90/1.14         = (k2_partfun1 @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_E @ 
% 0.90/1.14            (k2_struct_0 @ sk_C)))),
% 0.90/1.14      inference('clc', [status(thm)], ['130', '131'])).
% 0.90/1.14  thf('133', plain,
% 0.90/1.14      (![X0 : $i]:
% 0.90/1.14         ((v2_struct_0 @ X0)
% 0.90/1.14          | ~ (v2_pre_topc @ X0)
% 0.90/1.14          | ~ (l1_pre_topc @ X0)
% 0.90/1.14          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.90/1.14          | ((k3_tmap_1 @ X0 @ sk_B @ sk_D @ sk_C @ sk_E)
% 0.90/1.14              = (k2_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_C))
% 0.90/1.14          | ~ (m1_pre_topc @ sk_C @ X0)
% 0.90/1.14          | (v2_struct_0 @ sk_B))),
% 0.90/1.14      inference('demod', [status(thm)], ['107', '108', '132'])).
% 0.90/1.14  thf('134', plain,
% 0.90/1.14      (((v2_struct_0 @ sk_B)
% 0.90/1.14        | ~ (m1_pre_topc @ sk_C @ sk_A)
% 0.90/1.14        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E)
% 0.90/1.14            = (k2_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_C))
% 0.90/1.14        | ~ (l1_pre_topc @ sk_A)
% 0.90/1.14        | ~ (v2_pre_topc @ sk_A)
% 0.90/1.14        | (v2_struct_0 @ sk_A))),
% 0.90/1.14      inference('sup-', [status(thm)], ['68', '133'])).
% 0.90/1.14  thf('135', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf('136', plain, ((l1_pre_topc @ sk_A)),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf('137', plain, ((v2_pre_topc @ sk_A)),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf('138', plain,
% 0.90/1.14      (((v2_struct_0 @ sk_B)
% 0.90/1.14        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E)
% 0.90/1.14            = (k2_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_C))
% 0.90/1.14        | (v2_struct_0 @ sk_A))),
% 0.90/1.14      inference('demod', [status(thm)], ['134', '135', '136', '137'])).
% 0.90/1.14  thf('139', plain, (~ (v2_struct_0 @ sk_B)),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf('140', plain,
% 0.90/1.14      (((v2_struct_0 @ sk_A)
% 0.90/1.14        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E)
% 0.90/1.14            = (k2_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_C)))),
% 0.90/1.14      inference('clc', [status(thm)], ['138', '139'])).
% 0.90/1.14  thf('141', plain, (~ (v2_struct_0 @ sk_A)),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf('142', plain,
% 0.90/1.14      (((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E)
% 0.90/1.14         = (k2_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_C))),
% 0.90/1.14      inference('clc', [status(thm)], ['140', '141'])).
% 0.90/1.14  thf('143', plain,
% 0.90/1.14      ((r1_tmap_1 @ sk_C @ sk_B @ (k2_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_C) @ 
% 0.90/1.14        sk_F)),
% 0.90/1.14      inference('demod', [status(thm)], ['67', '142'])).
% 0.90/1.14  thf('144', plain,
% 0.90/1.14      ((m1_subset_1 @ sk_E @ 
% 0.90/1.14        (k1_zfmisc_1 @ 
% 0.90/1.14         (k2_zfmisc_1 @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 0.90/1.14      inference('demod', [status(thm)], ['86', '87'])).
% 0.90/1.14  thf('145', plain,
% 0.90/1.14      (![X8 : $i]:
% 0.90/1.14         (((k2_struct_0 @ X8) = (u1_struct_0 @ X8)) | ~ (l1_struct_0 @ X8))),
% 0.90/1.14      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.90/1.14  thf(t67_tmap_1, axiom,
% 0.90/1.14    (![A:$i]:
% 0.90/1.14     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.90/1.14       ( ![B:$i]:
% 0.90/1.14         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.90/1.14             ( l1_pre_topc @ B ) ) =>
% 0.90/1.14           ( ![C:$i]:
% 0.90/1.14             ( ( ( v1_funct_1 @ C ) & 
% 0.90/1.14                 ( v1_funct_2 @ C @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 0.90/1.14                 ( m1_subset_1 @
% 0.90/1.14                   C @ 
% 0.90/1.14                   ( k1_zfmisc_1 @
% 0.90/1.14                     ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.90/1.14               ( ![D:$i]:
% 0.90/1.14                 ( ( ( ~( v2_struct_0 @ D ) ) & ( v1_tsep_1 @ D @ B ) & 
% 0.90/1.14                     ( m1_pre_topc @ D @ B ) ) =>
% 0.90/1.14                   ( ![E:$i]:
% 0.90/1.14                     ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) =>
% 0.90/1.14                       ( ![F:$i]:
% 0.90/1.14                         ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 0.90/1.14                           ( ( ( E ) = ( F ) ) =>
% 0.90/1.14                             ( ( r1_tmap_1 @ B @ A @ C @ E ) <=>
% 0.90/1.14                               ( r1_tmap_1 @
% 0.90/1.14                                 D @ A @ ( k2_tmap_1 @ B @ A @ C @ D ) @ F ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.90/1.14  thf('146', plain,
% 0.90/1.14      (![X43 : $i, X44 : $i, X45 : $i, X46 : $i, X47 : $i, X48 : $i]:
% 0.90/1.14         ((v2_struct_0 @ X43)
% 0.90/1.14          | ~ (v2_pre_topc @ X43)
% 0.90/1.14          | ~ (l1_pre_topc @ X43)
% 0.90/1.14          | (v2_struct_0 @ X44)
% 0.90/1.14          | ~ (v1_tsep_1 @ X44 @ X43)
% 0.90/1.14          | ~ (m1_pre_topc @ X44 @ X43)
% 0.90/1.14          | ~ (m1_subset_1 @ X45 @ (u1_struct_0 @ X44))
% 0.90/1.14          | ~ (r1_tmap_1 @ X44 @ X46 @ (k2_tmap_1 @ X43 @ X46 @ X47 @ X44) @ 
% 0.90/1.14               X45)
% 0.90/1.14          | (r1_tmap_1 @ X43 @ X46 @ X47 @ X48)
% 0.90/1.14          | ((X48) != (X45))
% 0.90/1.14          | ~ (m1_subset_1 @ X48 @ (u1_struct_0 @ X43))
% 0.90/1.14          | ~ (m1_subset_1 @ X47 @ 
% 0.90/1.14               (k1_zfmisc_1 @ 
% 0.90/1.14                (k2_zfmisc_1 @ (u1_struct_0 @ X43) @ (u1_struct_0 @ X46))))
% 0.90/1.14          | ~ (v1_funct_2 @ X47 @ (u1_struct_0 @ X43) @ (u1_struct_0 @ X46))
% 0.90/1.14          | ~ (v1_funct_1 @ X47)
% 0.90/1.14          | ~ (l1_pre_topc @ X46)
% 0.90/1.14          | ~ (v2_pre_topc @ X46)
% 0.90/1.14          | (v2_struct_0 @ X46))),
% 0.90/1.14      inference('cnf', [status(esa)], [t67_tmap_1])).
% 0.90/1.14  thf('147', plain,
% 0.90/1.14      (![X43 : $i, X44 : $i, X45 : $i, X46 : $i, X47 : $i]:
% 0.90/1.14         ((v2_struct_0 @ X46)
% 0.90/1.14          | ~ (v2_pre_topc @ X46)
% 0.90/1.14          | ~ (l1_pre_topc @ X46)
% 0.90/1.14          | ~ (v1_funct_1 @ X47)
% 0.90/1.14          | ~ (v1_funct_2 @ X47 @ (u1_struct_0 @ X43) @ (u1_struct_0 @ X46))
% 0.90/1.14          | ~ (m1_subset_1 @ X47 @ 
% 0.90/1.14               (k1_zfmisc_1 @ 
% 0.90/1.14                (k2_zfmisc_1 @ (u1_struct_0 @ X43) @ (u1_struct_0 @ X46))))
% 0.90/1.14          | ~ (m1_subset_1 @ X45 @ (u1_struct_0 @ X43))
% 0.90/1.14          | (r1_tmap_1 @ X43 @ X46 @ X47 @ X45)
% 0.90/1.14          | ~ (r1_tmap_1 @ X44 @ X46 @ (k2_tmap_1 @ X43 @ X46 @ X47 @ X44) @ 
% 0.90/1.14               X45)
% 0.90/1.14          | ~ (m1_subset_1 @ X45 @ (u1_struct_0 @ X44))
% 0.90/1.14          | ~ (m1_pre_topc @ X44 @ X43)
% 0.90/1.14          | ~ (v1_tsep_1 @ X44 @ X43)
% 0.90/1.14          | (v2_struct_0 @ X44)
% 0.90/1.14          | ~ (l1_pre_topc @ X43)
% 0.90/1.14          | ~ (v2_pre_topc @ X43)
% 0.90/1.14          | (v2_struct_0 @ X43))),
% 0.90/1.14      inference('simplify', [status(thm)], ['146'])).
% 0.90/1.14  thf('148', plain,
% 0.90/1.14      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.90/1.14         (~ (m1_subset_1 @ X2 @ 
% 0.90/1.14             (k1_zfmisc_1 @ 
% 0.90/1.14              (k2_zfmisc_1 @ (k2_struct_0 @ X0) @ (u1_struct_0 @ X1))))
% 0.90/1.14          | ~ (l1_struct_0 @ X0)
% 0.90/1.14          | (v2_struct_0 @ X0)
% 0.90/1.14          | ~ (v2_pre_topc @ X0)
% 0.90/1.14          | ~ (l1_pre_topc @ X0)
% 0.90/1.14          | (v2_struct_0 @ X3)
% 0.90/1.14          | ~ (v1_tsep_1 @ X3 @ X0)
% 0.90/1.14          | ~ (m1_pre_topc @ X3 @ X0)
% 0.90/1.14          | ~ (m1_subset_1 @ X4 @ (u1_struct_0 @ X3))
% 0.90/1.14          | ~ (r1_tmap_1 @ X3 @ X1 @ (k2_tmap_1 @ X0 @ X1 @ X2 @ X3) @ X4)
% 0.90/1.14          | (r1_tmap_1 @ X0 @ X1 @ X2 @ X4)
% 0.90/1.14          | ~ (m1_subset_1 @ X4 @ (u1_struct_0 @ X0))
% 0.90/1.14          | ~ (v1_funct_2 @ X2 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X1))
% 0.90/1.14          | ~ (v1_funct_1 @ X2)
% 0.90/1.14          | ~ (l1_pre_topc @ X1)
% 0.90/1.14          | ~ (v2_pre_topc @ X1)
% 0.90/1.14          | (v2_struct_0 @ X1))),
% 0.90/1.14      inference('sup-', [status(thm)], ['145', '147'])).
% 0.90/1.14  thf('149', plain,
% 0.90/1.14      (![X0 : $i, X1 : $i]:
% 0.90/1.14         ((v2_struct_0 @ sk_B)
% 0.90/1.14          | ~ (v2_pre_topc @ sk_B)
% 0.90/1.14          | ~ (l1_pre_topc @ sk_B)
% 0.90/1.14          | ~ (v1_funct_1 @ sk_E)
% 0.90/1.14          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))
% 0.90/1.14          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_C))
% 0.90/1.14          | (r1_tmap_1 @ sk_C @ sk_B @ sk_E @ X0)
% 0.90/1.14          | ~ (r1_tmap_1 @ X1 @ sk_B @ (k2_tmap_1 @ sk_C @ sk_B @ sk_E @ X1) @ 
% 0.90/1.14               X0)
% 0.90/1.14          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ X1))
% 0.90/1.14          | ~ (m1_pre_topc @ X1 @ sk_C)
% 0.90/1.14          | ~ (v1_tsep_1 @ X1 @ sk_C)
% 0.90/1.14          | (v2_struct_0 @ X1)
% 0.90/1.14          | ~ (l1_pre_topc @ sk_C)
% 0.90/1.14          | ~ (v2_pre_topc @ sk_C)
% 0.90/1.14          | (v2_struct_0 @ sk_C)
% 0.90/1.14          | ~ (l1_struct_0 @ sk_C))),
% 0.90/1.14      inference('sup-', [status(thm)], ['144', '148'])).
% 0.90/1.14  thf('150', plain, ((v2_pre_topc @ sk_B)),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf('151', plain, ((l1_pre_topc @ sk_B)),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf('152', plain, ((v1_funct_1 @ sk_E)),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf('153', plain, (((u1_struct_0 @ sk_C) = (k2_struct_0 @ sk_C))),
% 0.90/1.14      inference('demod', [status(thm)], ['69', '70'])).
% 0.90/1.14  thf('154', plain,
% 0.90/1.14      ((v1_funct_2 @ sk_E @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 0.90/1.14      inference('demod', [status(thm)], ['102', '103'])).
% 0.90/1.14  thf('155', plain, (((u1_struct_0 @ sk_C) = (k2_struct_0 @ sk_C))),
% 0.90/1.14      inference('demod', [status(thm)], ['69', '70'])).
% 0.90/1.14  thf('156', plain, ((l1_pre_topc @ sk_C)),
% 0.90/1.14      inference('demod', [status(thm)], ['14', '15'])).
% 0.90/1.14  thf('157', plain, ((v2_pre_topc @ sk_C)),
% 0.90/1.14      inference('demod', [status(thm)], ['39', '40', '41'])).
% 0.90/1.14  thf('158', plain, ((l1_struct_0 @ sk_C)),
% 0.90/1.14      inference('sup-', [status(thm)], ['44', '45'])).
% 0.90/1.14  thf('159', plain,
% 0.90/1.14      (![X0 : $i, X1 : $i]:
% 0.90/1.14         ((v2_struct_0 @ sk_B)
% 0.90/1.14          | ~ (m1_subset_1 @ X0 @ (k2_struct_0 @ sk_C))
% 0.90/1.14          | (r1_tmap_1 @ sk_C @ sk_B @ sk_E @ X0)
% 0.90/1.14          | ~ (r1_tmap_1 @ X1 @ sk_B @ (k2_tmap_1 @ sk_C @ sk_B @ sk_E @ X1) @ 
% 0.90/1.14               X0)
% 0.90/1.14          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ X1))
% 0.90/1.14          | ~ (m1_pre_topc @ X1 @ sk_C)
% 0.90/1.14          | ~ (v1_tsep_1 @ X1 @ sk_C)
% 0.90/1.14          | (v2_struct_0 @ X1)
% 0.90/1.14          | (v2_struct_0 @ sk_C))),
% 0.90/1.14      inference('demod', [status(thm)],
% 0.90/1.14                ['149', '150', '151', '152', '153', '154', '155', '156', 
% 0.90/1.14                 '157', '158'])).
% 0.90/1.14  thf('160', plain,
% 0.90/1.14      (((v2_struct_0 @ sk_C)
% 0.90/1.14        | (v2_struct_0 @ sk_C)
% 0.90/1.14        | ~ (v1_tsep_1 @ sk_C @ sk_C)
% 0.90/1.14        | ~ (m1_pre_topc @ sk_C @ sk_C)
% 0.90/1.14        | ~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C))
% 0.90/1.14        | (r1_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_F)
% 0.90/1.14        | ~ (m1_subset_1 @ sk_F @ (k2_struct_0 @ sk_C))
% 0.90/1.14        | (v2_struct_0 @ sk_B))),
% 0.90/1.14      inference('sup-', [status(thm)], ['143', '159'])).
% 0.90/1.14  thf('161', plain, (((u1_struct_0 @ sk_C) = (k2_struct_0 @ sk_C))),
% 0.90/1.14      inference('demod', [status(thm)], ['69', '70'])).
% 0.90/1.14  thf('162', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.90/1.14      inference('sup-', [status(thm)], ['28', '29'])).
% 0.90/1.14  thf(t16_tsep_1, axiom,
% 0.90/1.14    (![A:$i]:
% 0.90/1.14     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.90/1.14       ( ![B:$i]:
% 0.90/1.14         ( ( m1_pre_topc @ B @ A ) =>
% 0.90/1.14           ( ![C:$i]:
% 0.90/1.14             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.90/1.14               ( ( ( C ) = ( u1_struct_0 @ B ) ) =>
% 0.90/1.14                 ( ( ( v1_tsep_1 @ B @ A ) & ( m1_pre_topc @ B @ A ) ) <=>
% 0.90/1.14                   ( v3_pre_topc @ C @ A ) ) ) ) ) ) ) ))).
% 0.90/1.14  thf('163', plain,
% 0.90/1.14      (![X32 : $i, X33 : $i, X34 : $i]:
% 0.90/1.14         (~ (m1_pre_topc @ X32 @ X33)
% 0.90/1.14          | ((X34) != (u1_struct_0 @ X32))
% 0.90/1.14          | ~ (v3_pre_topc @ X34 @ X33)
% 0.90/1.14          | (v1_tsep_1 @ X32 @ X33)
% 0.90/1.14          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (u1_struct_0 @ X33)))
% 0.90/1.14          | ~ (l1_pre_topc @ X33)
% 0.90/1.14          | ~ (v2_pre_topc @ X33))),
% 0.90/1.14      inference('cnf', [status(esa)], [t16_tsep_1])).
% 0.90/1.14  thf('164', plain,
% 0.90/1.14      (![X32 : $i, X33 : $i]:
% 0.90/1.14         (~ (v2_pre_topc @ X33)
% 0.90/1.14          | ~ (l1_pre_topc @ X33)
% 0.90/1.14          | ~ (m1_subset_1 @ (u1_struct_0 @ X32) @ 
% 0.90/1.14               (k1_zfmisc_1 @ (u1_struct_0 @ X33)))
% 0.90/1.14          | (v1_tsep_1 @ X32 @ X33)
% 0.90/1.14          | ~ (v3_pre_topc @ (u1_struct_0 @ X32) @ X33)
% 0.90/1.14          | ~ (m1_pre_topc @ X32 @ X33))),
% 0.90/1.14      inference('simplify', [status(thm)], ['163'])).
% 0.90/1.14  thf('165', plain,
% 0.90/1.14      (![X0 : $i]:
% 0.90/1.14         (~ (m1_pre_topc @ X0 @ X0)
% 0.90/1.14          | ~ (v3_pre_topc @ (u1_struct_0 @ X0) @ X0)
% 0.90/1.14          | (v1_tsep_1 @ X0 @ X0)
% 0.90/1.14          | ~ (l1_pre_topc @ X0)
% 0.90/1.14          | ~ (v2_pre_topc @ X0))),
% 0.90/1.14      inference('sup-', [status(thm)], ['162', '164'])).
% 0.90/1.14  thf('166', plain,
% 0.90/1.14      ((~ (v3_pre_topc @ (k2_struct_0 @ sk_C) @ sk_C)
% 0.90/1.14        | ~ (v2_pre_topc @ sk_C)
% 0.90/1.14        | ~ (l1_pre_topc @ sk_C)
% 0.90/1.14        | (v1_tsep_1 @ sk_C @ sk_C)
% 0.90/1.14        | ~ (m1_pre_topc @ sk_C @ sk_C))),
% 0.90/1.14      inference('sup-', [status(thm)], ['161', '165'])).
% 0.90/1.14  thf('167', plain,
% 0.90/1.14      (((g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) = (sk_D))),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf('168', plain,
% 0.90/1.14      (![X0 : $i]:
% 0.90/1.14         (~ (l1_struct_0 @ X0)
% 0.90/1.14          | (m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 0.90/1.14             (k1_zfmisc_1 @ 
% 0.90/1.14              (u1_struct_0 @ 
% 0.90/1.14               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))))
% 0.90/1.14          | ~ (l1_pre_topc @ X0)
% 0.90/1.14          | ~ (v2_pre_topc @ X0))),
% 0.90/1.14      inference('simplify', [status(thm)], ['34'])).
% 0.90/1.14  thf('169', plain,
% 0.90/1.14      (![X17 : $i, X18 : $i]:
% 0.90/1.14         (~ (v3_pre_topc @ X17 @ 
% 0.90/1.14             (g1_pre_topc @ (u1_struct_0 @ X18) @ (u1_pre_topc @ X18)))
% 0.90/1.14          | ~ (m1_subset_1 @ X17 @ 
% 0.90/1.14               (k1_zfmisc_1 @ 
% 0.90/1.14                (u1_struct_0 @ 
% 0.90/1.14                 (g1_pre_topc @ (u1_struct_0 @ X18) @ (u1_pre_topc @ X18)))))
% 0.90/1.14          | (v3_pre_topc @ X17 @ X18)
% 0.90/1.14          | ~ (l1_pre_topc @ X18)
% 0.90/1.14          | ~ (v2_pre_topc @ X18))),
% 0.90/1.14      inference('cnf', [status(esa)], [t60_pre_topc])).
% 0.90/1.14  thf('170', plain,
% 0.90/1.14      (![X0 : $i]:
% 0.90/1.14         (~ (v2_pre_topc @ X0)
% 0.90/1.14          | ~ (l1_pre_topc @ X0)
% 0.90/1.14          | ~ (l1_struct_0 @ X0)
% 0.90/1.14          | ~ (v2_pre_topc @ X0)
% 0.90/1.14          | ~ (l1_pre_topc @ X0)
% 0.90/1.14          | (v3_pre_topc @ (u1_struct_0 @ X0) @ X0)
% 0.90/1.14          | ~ (v3_pre_topc @ (u1_struct_0 @ X0) @ 
% 0.90/1.14               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 0.90/1.14      inference('sup-', [status(thm)], ['168', '169'])).
% 0.90/1.14  thf('171', plain,
% 0.90/1.14      (![X0 : $i]:
% 0.90/1.14         (~ (v3_pre_topc @ (u1_struct_0 @ X0) @ 
% 0.90/1.14             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.90/1.14          | (v3_pre_topc @ (u1_struct_0 @ X0) @ X0)
% 0.90/1.14          | ~ (l1_struct_0 @ X0)
% 0.90/1.14          | ~ (l1_pre_topc @ X0)
% 0.90/1.14          | ~ (v2_pre_topc @ X0))),
% 0.90/1.14      inference('simplify', [status(thm)], ['170'])).
% 0.90/1.14  thf('172', plain,
% 0.90/1.14      ((~ (v3_pre_topc @ (u1_struct_0 @ sk_C) @ sk_D)
% 0.90/1.14        | ~ (v2_pre_topc @ sk_C)
% 0.90/1.14        | ~ (l1_pre_topc @ sk_C)
% 0.90/1.14        | ~ (l1_struct_0 @ sk_C)
% 0.90/1.14        | (v3_pre_topc @ (u1_struct_0 @ sk_C) @ sk_C))),
% 0.90/1.14      inference('sup-', [status(thm)], ['167', '171'])).
% 0.90/1.14  thf('173', plain, ((v2_pre_topc @ sk_C)),
% 0.90/1.14      inference('demod', [status(thm)], ['39', '40', '41'])).
% 0.90/1.14  thf('174', plain, ((l1_pre_topc @ sk_C)),
% 0.90/1.14      inference('demod', [status(thm)], ['14', '15'])).
% 0.90/1.14  thf('175', plain, ((l1_struct_0 @ sk_C)),
% 0.90/1.14      inference('sup-', [status(thm)], ['44', '45'])).
% 0.90/1.14  thf('176', plain,
% 0.90/1.14      ((~ (v3_pre_topc @ (u1_struct_0 @ sk_C) @ sk_D)
% 0.90/1.14        | (v3_pre_topc @ (u1_struct_0 @ sk_C) @ sk_C))),
% 0.90/1.14      inference('demod', [status(thm)], ['172', '173', '174', '175'])).
% 0.90/1.14  thf('177', plain, (((u1_struct_0 @ sk_C) = (k2_struct_0 @ sk_C))),
% 0.90/1.14      inference('demod', [status(thm)], ['69', '70'])).
% 0.90/1.14  thf('178', plain, (((k2_struct_0 @ sk_C) = (k2_struct_0 @ sk_D))),
% 0.90/1.14      inference('demod', [status(thm)], ['61', '62'])).
% 0.90/1.14  thf('179', plain,
% 0.90/1.14      (![X22 : $i]:
% 0.90/1.14         ((v3_pre_topc @ (k2_struct_0 @ X22) @ X22)
% 0.90/1.14          | ~ (l1_pre_topc @ X22)
% 0.90/1.14          | ~ (v2_pre_topc @ X22))),
% 0.90/1.14      inference('cnf', [status(esa)], [fc10_tops_1])).
% 0.90/1.14  thf('180', plain,
% 0.90/1.14      (((v3_pre_topc @ (k2_struct_0 @ sk_C) @ sk_D)
% 0.90/1.14        | ~ (v2_pre_topc @ sk_D)
% 0.90/1.14        | ~ (l1_pre_topc @ sk_D))),
% 0.90/1.14      inference('sup+', [status(thm)], ['178', '179'])).
% 0.90/1.14  thf('181', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf('182', plain,
% 0.90/1.14      (![X6 : $i, X7 : $i]:
% 0.90/1.14         (~ (m1_pre_topc @ X6 @ X7)
% 0.90/1.14          | (v2_pre_topc @ X6)
% 0.90/1.14          | ~ (l1_pre_topc @ X7)
% 0.90/1.14          | ~ (v2_pre_topc @ X7))),
% 0.90/1.14      inference('cnf', [status(esa)], [cc1_pre_topc])).
% 0.90/1.14  thf('183', plain,
% 0.90/1.14      ((~ (v2_pre_topc @ sk_A) | ~ (l1_pre_topc @ sk_A) | (v2_pre_topc @ sk_D))),
% 0.90/1.14      inference('sup-', [status(thm)], ['181', '182'])).
% 0.90/1.14  thf('184', plain, ((v2_pre_topc @ sk_A)),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf('185', plain, ((l1_pre_topc @ sk_A)),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf('186', plain, ((v2_pre_topc @ sk_D)),
% 0.90/1.14      inference('demod', [status(thm)], ['183', '184', '185'])).
% 0.90/1.14  thf('187', plain, ((l1_pre_topc @ sk_D)),
% 0.90/1.14      inference('demod', [status(thm)], ['8', '9'])).
% 0.90/1.14  thf('188', plain, ((v3_pre_topc @ (k2_struct_0 @ sk_C) @ sk_D)),
% 0.90/1.14      inference('demod', [status(thm)], ['180', '186', '187'])).
% 0.90/1.14  thf('189', plain, (((u1_struct_0 @ sk_C) = (k2_struct_0 @ sk_C))),
% 0.90/1.14      inference('demod', [status(thm)], ['69', '70'])).
% 0.90/1.14  thf('190', plain, ((v3_pre_topc @ (k2_struct_0 @ sk_C) @ sk_C)),
% 0.90/1.14      inference('demod', [status(thm)], ['176', '177', '188', '189'])).
% 0.90/1.14  thf('191', plain, ((v2_pre_topc @ sk_C)),
% 0.90/1.14      inference('demod', [status(thm)], ['39', '40', '41'])).
% 0.90/1.14  thf('192', plain, ((l1_pre_topc @ sk_C)),
% 0.90/1.14      inference('demod', [status(thm)], ['14', '15'])).
% 0.90/1.14  thf('193', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 0.90/1.14      inference('demod', [status(thm)], ['76', '81', '82'])).
% 0.90/1.14  thf('194', plain,
% 0.90/1.14      (((g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) = (sk_D))),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf('195', plain,
% 0.90/1.14      (![X15 : $i, X16 : $i]:
% 0.90/1.14         (~ (m1_pre_topc @ X15 @ 
% 0.90/1.14             (g1_pre_topc @ (u1_struct_0 @ X16) @ (u1_pre_topc @ X16)))
% 0.90/1.14          | (m1_pre_topc @ X15 @ X16)
% 0.90/1.14          | ~ (l1_pre_topc @ X16))),
% 0.90/1.14      inference('cnf', [status(esa)], [t59_pre_topc])).
% 0.90/1.14  thf('196', plain,
% 0.90/1.14      (![X0 : $i]:
% 0.90/1.14         (~ (m1_pre_topc @ X0 @ sk_D)
% 0.90/1.14          | ~ (l1_pre_topc @ sk_C)
% 0.90/1.14          | (m1_pre_topc @ X0 @ sk_C))),
% 0.90/1.14      inference('sup-', [status(thm)], ['194', '195'])).
% 0.90/1.14  thf('197', plain, ((l1_pre_topc @ sk_C)),
% 0.90/1.14      inference('demod', [status(thm)], ['14', '15'])).
% 0.90/1.14  thf('198', plain,
% 0.90/1.14      (![X0 : $i]: (~ (m1_pre_topc @ X0 @ sk_D) | (m1_pre_topc @ X0 @ sk_C))),
% 0.90/1.14      inference('demod', [status(thm)], ['196', '197'])).
% 0.90/1.14  thf('199', plain, ((m1_pre_topc @ sk_C @ sk_C)),
% 0.90/1.14      inference('sup-', [status(thm)], ['193', '198'])).
% 0.90/1.14  thf('200', plain, ((v1_tsep_1 @ sk_C @ sk_C)),
% 0.90/1.14      inference('demod', [status(thm)], ['166', '190', '191', '192', '199'])).
% 0.90/1.14  thf('201', plain, ((m1_pre_topc @ sk_C @ sk_C)),
% 0.90/1.14      inference('sup-', [status(thm)], ['193', '198'])).
% 0.90/1.14  thf('202', plain, (((u1_struct_0 @ sk_C) = (k2_struct_0 @ sk_C))),
% 0.90/1.14      inference('demod', [status(thm)], ['69', '70'])).
% 0.90/1.14  thf('203', plain,
% 0.90/1.14      (![X8 : $i]:
% 0.90/1.14         (((k2_struct_0 @ X8) = (u1_struct_0 @ X8)) | ~ (l1_struct_0 @ X8))),
% 0.90/1.14      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.90/1.14  thf('204', plain, ((m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_C))),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf('205', plain, (((sk_F) = (sk_G))),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf('206', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C))),
% 0.90/1.14      inference('demod', [status(thm)], ['204', '205'])).
% 0.90/1.14  thf('207', plain,
% 0.90/1.14      (((m1_subset_1 @ sk_F @ (k2_struct_0 @ sk_C)) | ~ (l1_struct_0 @ sk_C))),
% 0.90/1.14      inference('sup+', [status(thm)], ['203', '206'])).
% 0.90/1.14  thf('208', plain, ((l1_struct_0 @ sk_C)),
% 0.90/1.14      inference('sup-', [status(thm)], ['44', '45'])).
% 0.90/1.14  thf('209', plain, ((m1_subset_1 @ sk_F @ (k2_struct_0 @ sk_C))),
% 0.90/1.14      inference('demod', [status(thm)], ['207', '208'])).
% 0.90/1.14  thf('210', plain, ((m1_subset_1 @ sk_F @ (k2_struct_0 @ sk_C))),
% 0.90/1.14      inference('demod', [status(thm)], ['207', '208'])).
% 0.90/1.14  thf('211', plain,
% 0.90/1.14      (((v2_struct_0 @ sk_C)
% 0.90/1.14        | (v2_struct_0 @ sk_C)
% 0.90/1.14        | (r1_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_F)
% 0.90/1.14        | (v2_struct_0 @ sk_B))),
% 0.90/1.14      inference('demod', [status(thm)],
% 0.90/1.14                ['160', '200', '201', '202', '209', '210'])).
% 0.90/1.14  thf('212', plain,
% 0.90/1.14      (((v2_struct_0 @ sk_B)
% 0.90/1.14        | (r1_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_F)
% 0.90/1.14        | (v2_struct_0 @ sk_C))),
% 0.90/1.14      inference('simplify', [status(thm)], ['211'])).
% 0.90/1.14  thf('213', plain, (~ (v2_struct_0 @ sk_B)),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf('214', plain,
% 0.90/1.14      (((v2_struct_0 @ sk_C) | (r1_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_F))),
% 0.90/1.14      inference('clc', [status(thm)], ['212', '213'])).
% 0.90/1.14  thf('215', plain, (~ (v2_struct_0 @ sk_C)),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf('216', plain, ((r1_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_F)),
% 0.90/1.14      inference('clc', [status(thm)], ['214', '215'])).
% 0.90/1.14  thf('217', plain,
% 0.90/1.14      ((m1_subset_1 @ sk_E @ 
% 0.90/1.14        (k1_zfmisc_1 @ 
% 0.90/1.14         (k2_zfmisc_1 @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 0.90/1.14      inference('demod', [status(thm)], ['86', '87'])).
% 0.90/1.14  thf('218', plain,
% 0.90/1.14      (![X8 : $i]:
% 0.90/1.14         (((k2_struct_0 @ X8) = (u1_struct_0 @ X8)) | ~ (l1_struct_0 @ X8))),
% 0.90/1.14      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.90/1.14  thf('219', plain,
% 0.90/1.14      (![X43 : $i, X44 : $i, X45 : $i, X46 : $i, X47 : $i, X48 : $i]:
% 0.90/1.14         ((v2_struct_0 @ X43)
% 0.90/1.14          | ~ (v2_pre_topc @ X43)
% 0.90/1.14          | ~ (l1_pre_topc @ X43)
% 0.90/1.14          | (v2_struct_0 @ X44)
% 0.90/1.14          | ~ (v1_tsep_1 @ X44 @ X43)
% 0.90/1.14          | ~ (m1_pre_topc @ X44 @ X43)
% 0.90/1.14          | ~ (m1_subset_1 @ X45 @ (u1_struct_0 @ X44))
% 0.90/1.14          | ~ (r1_tmap_1 @ X43 @ X46 @ X47 @ X48)
% 0.90/1.14          | (r1_tmap_1 @ X44 @ X46 @ (k2_tmap_1 @ X43 @ X46 @ X47 @ X44) @ X45)
% 0.90/1.14          | ((X48) != (X45))
% 0.90/1.14          | ~ (m1_subset_1 @ X48 @ (u1_struct_0 @ X43))
% 0.90/1.14          | ~ (m1_subset_1 @ X47 @ 
% 0.90/1.14               (k1_zfmisc_1 @ 
% 0.90/1.14                (k2_zfmisc_1 @ (u1_struct_0 @ X43) @ (u1_struct_0 @ X46))))
% 0.90/1.14          | ~ (v1_funct_2 @ X47 @ (u1_struct_0 @ X43) @ (u1_struct_0 @ X46))
% 0.90/1.14          | ~ (v1_funct_1 @ X47)
% 0.90/1.14          | ~ (l1_pre_topc @ X46)
% 0.90/1.14          | ~ (v2_pre_topc @ X46)
% 0.90/1.14          | (v2_struct_0 @ X46))),
% 0.90/1.14      inference('cnf', [status(esa)], [t67_tmap_1])).
% 0.90/1.14  thf('220', plain,
% 0.90/1.14      (![X43 : $i, X44 : $i, X45 : $i, X46 : $i, X47 : $i]:
% 0.90/1.14         ((v2_struct_0 @ X46)
% 0.90/1.14          | ~ (v2_pre_topc @ X46)
% 0.90/1.14          | ~ (l1_pre_topc @ X46)
% 0.90/1.14          | ~ (v1_funct_1 @ X47)
% 0.90/1.14          | ~ (v1_funct_2 @ X47 @ (u1_struct_0 @ X43) @ (u1_struct_0 @ X46))
% 0.90/1.14          | ~ (m1_subset_1 @ X47 @ 
% 0.90/1.14               (k1_zfmisc_1 @ 
% 0.90/1.14                (k2_zfmisc_1 @ (u1_struct_0 @ X43) @ (u1_struct_0 @ X46))))
% 0.90/1.14          | ~ (m1_subset_1 @ X45 @ (u1_struct_0 @ X43))
% 0.90/1.14          | (r1_tmap_1 @ X44 @ X46 @ (k2_tmap_1 @ X43 @ X46 @ X47 @ X44) @ X45)
% 0.90/1.14          | ~ (r1_tmap_1 @ X43 @ X46 @ X47 @ X45)
% 0.90/1.14          | ~ (m1_subset_1 @ X45 @ (u1_struct_0 @ X44))
% 0.90/1.14          | ~ (m1_pre_topc @ X44 @ X43)
% 0.90/1.14          | ~ (v1_tsep_1 @ X44 @ X43)
% 0.90/1.14          | (v2_struct_0 @ X44)
% 0.90/1.14          | ~ (l1_pre_topc @ X43)
% 0.90/1.14          | ~ (v2_pre_topc @ X43)
% 0.90/1.14          | (v2_struct_0 @ X43))),
% 0.90/1.14      inference('simplify', [status(thm)], ['219'])).
% 0.90/1.14  thf('221', plain,
% 0.90/1.14      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.90/1.14         (~ (m1_subset_1 @ X2 @ 
% 0.90/1.14             (k1_zfmisc_1 @ 
% 0.90/1.14              (k2_zfmisc_1 @ (k2_struct_0 @ X0) @ (u1_struct_0 @ X1))))
% 0.90/1.14          | ~ (l1_struct_0 @ X0)
% 0.90/1.14          | (v2_struct_0 @ X0)
% 0.90/1.14          | ~ (v2_pre_topc @ X0)
% 0.90/1.14          | ~ (l1_pre_topc @ X0)
% 0.90/1.14          | (v2_struct_0 @ X3)
% 0.90/1.14          | ~ (v1_tsep_1 @ X3 @ X0)
% 0.90/1.14          | ~ (m1_pre_topc @ X3 @ X0)
% 0.90/1.14          | ~ (m1_subset_1 @ X4 @ (u1_struct_0 @ X3))
% 0.90/1.14          | ~ (r1_tmap_1 @ X0 @ X1 @ X2 @ X4)
% 0.90/1.14          | (r1_tmap_1 @ X3 @ X1 @ (k2_tmap_1 @ X0 @ X1 @ X2 @ X3) @ X4)
% 0.90/1.14          | ~ (m1_subset_1 @ X4 @ (u1_struct_0 @ X0))
% 0.90/1.14          | ~ (v1_funct_2 @ X2 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X1))
% 0.90/1.14          | ~ (v1_funct_1 @ X2)
% 0.90/1.14          | ~ (l1_pre_topc @ X1)
% 0.90/1.14          | ~ (v2_pre_topc @ X1)
% 0.90/1.14          | (v2_struct_0 @ X1))),
% 0.90/1.14      inference('sup-', [status(thm)], ['218', '220'])).
% 0.90/1.14  thf('222', plain,
% 0.90/1.14      (![X0 : $i, X1 : $i]:
% 0.90/1.14         ((v2_struct_0 @ sk_B)
% 0.90/1.14          | ~ (v2_pre_topc @ sk_B)
% 0.90/1.14          | ~ (l1_pre_topc @ sk_B)
% 0.90/1.14          | ~ (v1_funct_1 @ sk_E)
% 0.90/1.14          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))
% 0.90/1.14          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_C))
% 0.90/1.14          | (r1_tmap_1 @ X1 @ sk_B @ (k2_tmap_1 @ sk_C @ sk_B @ sk_E @ X1) @ X0)
% 0.90/1.14          | ~ (r1_tmap_1 @ sk_C @ sk_B @ sk_E @ X0)
% 0.90/1.14          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ X1))
% 0.90/1.14          | ~ (m1_pre_topc @ X1 @ sk_C)
% 0.90/1.14          | ~ (v1_tsep_1 @ X1 @ sk_C)
% 0.90/1.14          | (v2_struct_0 @ X1)
% 0.90/1.14          | ~ (l1_pre_topc @ sk_C)
% 0.90/1.14          | ~ (v2_pre_topc @ sk_C)
% 0.90/1.14          | (v2_struct_0 @ sk_C)
% 0.90/1.14          | ~ (l1_struct_0 @ sk_C))),
% 0.90/1.14      inference('sup-', [status(thm)], ['217', '221'])).
% 0.90/1.14  thf('223', plain, ((v2_pre_topc @ sk_B)),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf('224', plain, ((l1_pre_topc @ sk_B)),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf('225', plain, ((v1_funct_1 @ sk_E)),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf('226', plain, (((u1_struct_0 @ sk_C) = (k2_struct_0 @ sk_C))),
% 0.90/1.14      inference('demod', [status(thm)], ['69', '70'])).
% 0.90/1.14  thf('227', plain,
% 0.90/1.14      ((v1_funct_2 @ sk_E @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 0.90/1.14      inference('demod', [status(thm)], ['102', '103'])).
% 0.90/1.14  thf('228', plain, (((u1_struct_0 @ sk_C) = (k2_struct_0 @ sk_C))),
% 0.90/1.14      inference('demod', [status(thm)], ['69', '70'])).
% 0.90/1.14  thf('229', plain, ((l1_pre_topc @ sk_C)),
% 0.90/1.14      inference('demod', [status(thm)], ['14', '15'])).
% 0.90/1.14  thf('230', plain, ((v2_pre_topc @ sk_C)),
% 0.90/1.14      inference('demod', [status(thm)], ['39', '40', '41'])).
% 0.90/1.14  thf('231', plain, ((l1_struct_0 @ sk_C)),
% 0.90/1.14      inference('sup-', [status(thm)], ['44', '45'])).
% 0.90/1.14  thf('232', plain,
% 0.90/1.14      (![X0 : $i, X1 : $i]:
% 0.90/1.14         ((v2_struct_0 @ sk_B)
% 0.90/1.14          | ~ (m1_subset_1 @ X0 @ (k2_struct_0 @ sk_C))
% 0.90/1.14          | (r1_tmap_1 @ X1 @ sk_B @ (k2_tmap_1 @ sk_C @ sk_B @ sk_E @ X1) @ X0)
% 0.90/1.14          | ~ (r1_tmap_1 @ sk_C @ sk_B @ sk_E @ X0)
% 0.90/1.14          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ X1))
% 0.90/1.14          | ~ (m1_pre_topc @ X1 @ sk_C)
% 0.90/1.14          | ~ (v1_tsep_1 @ X1 @ sk_C)
% 0.90/1.14          | (v2_struct_0 @ X1)
% 0.90/1.14          | (v2_struct_0 @ sk_C))),
% 0.90/1.14      inference('demod', [status(thm)],
% 0.90/1.14                ['222', '223', '224', '225', '226', '227', '228', '229', 
% 0.90/1.14                 '230', '231'])).
% 0.90/1.14  thf('233', plain,
% 0.90/1.14      (![X0 : $i]:
% 0.90/1.14         ((v2_struct_0 @ sk_C)
% 0.90/1.14          | (v2_struct_0 @ X0)
% 0.90/1.14          | ~ (v1_tsep_1 @ X0 @ sk_C)
% 0.90/1.14          | ~ (m1_pre_topc @ X0 @ sk_C)
% 0.90/1.14          | ~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ X0))
% 0.90/1.14          | (r1_tmap_1 @ X0 @ sk_B @ (k2_tmap_1 @ sk_C @ sk_B @ sk_E @ X0) @ 
% 0.90/1.14             sk_F)
% 0.90/1.14          | ~ (m1_subset_1 @ sk_F @ (k2_struct_0 @ sk_C))
% 0.90/1.14          | (v2_struct_0 @ sk_B))),
% 0.90/1.14      inference('sup-', [status(thm)], ['216', '232'])).
% 0.90/1.14  thf('234', plain, ((m1_subset_1 @ sk_F @ (k2_struct_0 @ sk_C))),
% 0.90/1.14      inference('demod', [status(thm)], ['207', '208'])).
% 0.90/1.14  thf('235', plain,
% 0.90/1.14      (![X0 : $i]:
% 0.90/1.14         ((v2_struct_0 @ sk_C)
% 0.90/1.14          | (v2_struct_0 @ X0)
% 0.90/1.14          | ~ (v1_tsep_1 @ X0 @ sk_C)
% 0.90/1.14          | ~ (m1_pre_topc @ X0 @ sk_C)
% 0.90/1.14          | ~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ X0))
% 0.90/1.14          | (r1_tmap_1 @ X0 @ sk_B @ (k2_tmap_1 @ sk_C @ sk_B @ sk_E @ X0) @ 
% 0.90/1.14             sk_F)
% 0.90/1.14          | (v2_struct_0 @ sk_B))),
% 0.90/1.14      inference('demod', [status(thm)], ['233', '234'])).
% 0.90/1.14  thf('236', plain,
% 0.90/1.14      ((~ (m1_subset_1 @ sk_F @ (k2_struct_0 @ sk_C))
% 0.90/1.14        | (v2_struct_0 @ sk_B)
% 0.90/1.14        | (r1_tmap_1 @ sk_D @ sk_B @ (k2_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_D) @ 
% 0.90/1.14           sk_F)
% 0.90/1.14        | ~ (m1_pre_topc @ sk_D @ sk_C)
% 0.90/1.14        | ~ (v1_tsep_1 @ sk_D @ sk_C)
% 0.90/1.14        | (v2_struct_0 @ sk_D)
% 0.90/1.14        | (v2_struct_0 @ sk_C))),
% 0.90/1.14      inference('sup-', [status(thm)], ['64', '235'])).
% 0.90/1.14  thf('237', plain, ((m1_subset_1 @ sk_F @ (k2_struct_0 @ sk_C))),
% 0.90/1.14      inference('demod', [status(thm)], ['207', '208'])).
% 0.90/1.14  thf('238', plain, ((m1_pre_topc @ sk_D @ sk_C)),
% 0.90/1.14      inference('demod', [status(thm)], ['5', '10', '11', '16'])).
% 0.90/1.14  thf('239', plain,
% 0.90/1.14      (![X0 : $i]:
% 0.90/1.14         ((v2_struct_0 @ sk_B)
% 0.90/1.14          | ~ (m1_pre_topc @ X0 @ sk_C)
% 0.90/1.14          | ((k2_tmap_1 @ sk_C @ sk_B @ sk_E @ X0)
% 0.90/1.14              = (k2_partfun1 @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.90/1.14                 sk_E @ (u1_struct_0 @ X0)))
% 0.90/1.14          | (v2_struct_0 @ sk_C))),
% 0.90/1.14      inference('demod', [status(thm)],
% 0.90/1.14                ['114', '115', '116', '117', '118', '119', '120', '121', 
% 0.90/1.14                 '122', '123'])).
% 0.90/1.14  thf('240', plain,
% 0.90/1.14      (((v2_struct_0 @ sk_C)
% 0.90/1.14        | ((k2_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_D)
% 0.90/1.14            = (k2_partfun1 @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.90/1.14               sk_E @ (u1_struct_0 @ sk_D)))
% 0.90/1.14        | (v2_struct_0 @ sk_B))),
% 0.90/1.14      inference('sup-', [status(thm)], ['238', '239'])).
% 0.90/1.14  thf('241', plain, (((k2_struct_0 @ sk_C) = (u1_struct_0 @ sk_D))),
% 0.90/1.14      inference('demod', [status(thm)], ['58', '63'])).
% 0.90/1.14  thf('242', plain,
% 0.90/1.14      (((v2_struct_0 @ sk_C)
% 0.90/1.14        | ((k2_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_D)
% 0.90/1.14            = (k2_partfun1 @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.90/1.14               sk_E @ (k2_struct_0 @ sk_C)))
% 0.90/1.14        | (v2_struct_0 @ sk_B))),
% 0.90/1.14      inference('demod', [status(thm)], ['240', '241'])).
% 0.90/1.14  thf('243', plain, (~ (v2_struct_0 @ sk_C)),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf('244', plain,
% 0.90/1.14      (((v2_struct_0 @ sk_B)
% 0.90/1.14        | ((k2_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_D)
% 0.90/1.14            = (k2_partfun1 @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.90/1.14               sk_E @ (k2_struct_0 @ sk_C))))),
% 0.90/1.14      inference('clc', [status(thm)], ['242', '243'])).
% 0.90/1.14  thf('245', plain, (~ (v2_struct_0 @ sk_B)),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf('246', plain,
% 0.90/1.14      (((k2_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_D)
% 0.90/1.14         = (k2_partfun1 @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_E @ 
% 0.90/1.14            (k2_struct_0 @ sk_C)))),
% 0.90/1.14      inference('clc', [status(thm)], ['244', '245'])).
% 0.90/1.14  thf('247', plain,
% 0.90/1.14      (((k2_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_C)
% 0.90/1.14         = (k2_partfun1 @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_E @ 
% 0.90/1.14            (k2_struct_0 @ sk_C)))),
% 0.90/1.14      inference('clc', [status(thm)], ['130', '131'])).
% 0.90/1.14  thf('248', plain,
% 0.90/1.14      (((k2_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_C)
% 0.90/1.14         = (k2_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_D))),
% 0.90/1.14      inference('sup+', [status(thm)], ['246', '247'])).
% 0.90/1.14  thf('249', plain, ((m1_pre_topc @ sk_D @ sk_C)),
% 0.90/1.14      inference('demod', [status(thm)], ['5', '10', '11', '16'])).
% 0.90/1.14  thf('250', plain, (((k2_struct_0 @ sk_C) = (u1_struct_0 @ sk_D))),
% 0.90/1.14      inference('demod', [status(thm)], ['58', '63'])).
% 0.90/1.14  thf('251', plain, (((u1_struct_0 @ sk_C) = (k2_struct_0 @ sk_C))),
% 0.90/1.14      inference('demod', [status(thm)], ['69', '70'])).
% 0.90/1.14  thf('252', plain,
% 0.90/1.14      (![X32 : $i, X33 : $i]:
% 0.90/1.14         (~ (v2_pre_topc @ X33)
% 0.90/1.14          | ~ (l1_pre_topc @ X33)
% 0.90/1.14          | ~ (m1_subset_1 @ (u1_struct_0 @ X32) @ 
% 0.90/1.14               (k1_zfmisc_1 @ (u1_struct_0 @ X33)))
% 0.90/1.14          | (v1_tsep_1 @ X32 @ X33)
% 0.90/1.14          | ~ (v3_pre_topc @ (u1_struct_0 @ X32) @ X33)
% 0.90/1.14          | ~ (m1_pre_topc @ X32 @ X33))),
% 0.90/1.14      inference('simplify', [status(thm)], ['163'])).
% 0.90/1.14  thf('253', plain,
% 0.90/1.14      (![X0 : $i]:
% 0.90/1.14         (~ (m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 0.90/1.14             (k1_zfmisc_1 @ (k2_struct_0 @ sk_C)))
% 0.90/1.14          | ~ (m1_pre_topc @ X0 @ sk_C)
% 0.90/1.14          | ~ (v3_pre_topc @ (u1_struct_0 @ X0) @ sk_C)
% 0.90/1.14          | (v1_tsep_1 @ X0 @ sk_C)
% 0.90/1.14          | ~ (l1_pre_topc @ sk_C)
% 0.90/1.14          | ~ (v2_pre_topc @ sk_C))),
% 0.90/1.14      inference('sup-', [status(thm)], ['251', '252'])).
% 0.90/1.14  thf('254', plain, ((l1_pre_topc @ sk_C)),
% 0.90/1.14      inference('demod', [status(thm)], ['14', '15'])).
% 0.90/1.14  thf('255', plain, ((v2_pre_topc @ sk_C)),
% 0.90/1.14      inference('demod', [status(thm)], ['39', '40', '41'])).
% 0.90/1.14  thf('256', plain,
% 0.90/1.14      (![X0 : $i]:
% 0.90/1.14         (~ (m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 0.90/1.14             (k1_zfmisc_1 @ (k2_struct_0 @ sk_C)))
% 0.90/1.14          | ~ (m1_pre_topc @ X0 @ sk_C)
% 0.90/1.14          | ~ (v3_pre_topc @ (u1_struct_0 @ X0) @ sk_C)
% 0.90/1.14          | (v1_tsep_1 @ X0 @ sk_C))),
% 0.90/1.14      inference('demod', [status(thm)], ['253', '254', '255'])).
% 0.90/1.14  thf('257', plain,
% 0.90/1.14      ((~ (m1_subset_1 @ (k2_struct_0 @ sk_C) @ 
% 0.90/1.14           (k1_zfmisc_1 @ (k2_struct_0 @ sk_C)))
% 0.90/1.14        | (v1_tsep_1 @ sk_D @ sk_C)
% 0.90/1.14        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_D) @ sk_C)
% 0.90/1.14        | ~ (m1_pre_topc @ sk_D @ sk_C))),
% 0.90/1.14      inference('sup-', [status(thm)], ['250', '256'])).
% 0.90/1.14  thf('258', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.90/1.14      inference('sup-', [status(thm)], ['28', '29'])).
% 0.90/1.14  thf('259', plain, (((k2_struct_0 @ sk_C) = (u1_struct_0 @ sk_D))),
% 0.90/1.14      inference('demod', [status(thm)], ['58', '63'])).
% 0.90/1.14  thf('260', plain, ((v3_pre_topc @ (k2_struct_0 @ sk_C) @ sk_C)),
% 0.90/1.14      inference('demod', [status(thm)], ['176', '177', '188', '189'])).
% 0.90/1.14  thf('261', plain, ((m1_pre_topc @ sk_D @ sk_C)),
% 0.90/1.14      inference('demod', [status(thm)], ['5', '10', '11', '16'])).
% 0.90/1.14  thf('262', plain, ((v1_tsep_1 @ sk_D @ sk_C)),
% 0.90/1.14      inference('demod', [status(thm)], ['257', '258', '259', '260', '261'])).
% 0.90/1.14  thf('263', plain,
% 0.90/1.14      (((v2_struct_0 @ sk_B)
% 0.90/1.14        | (r1_tmap_1 @ sk_D @ sk_B @ (k2_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_C) @ 
% 0.90/1.14           sk_F)
% 0.90/1.14        | (v2_struct_0 @ sk_D)
% 0.90/1.14        | (v2_struct_0 @ sk_C))),
% 0.90/1.14      inference('demod', [status(thm)], ['236', '237', '248', '249', '262'])).
% 0.90/1.14  thf('264', plain,
% 0.90/1.14      (![X37 : $i]: ((m1_pre_topc @ X37 @ X37) | ~ (l1_pre_topc @ X37))),
% 0.90/1.14      inference('cnf', [status(esa)], [t2_tsep_1])).
% 0.90/1.14  thf('265', plain,
% 0.90/1.14      ((m1_subset_1 @ sk_E @ 
% 0.90/1.14        (k1_zfmisc_1 @ 
% 0.90/1.14         (k2_zfmisc_1 @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 0.90/1.14      inference('demod', [status(thm)], ['86', '87'])).
% 0.90/1.14  thf('266', plain, (((k2_struct_0 @ sk_C) = (u1_struct_0 @ sk_D))),
% 0.90/1.14      inference('demod', [status(thm)], ['58', '63'])).
% 0.90/1.14  thf('267', plain,
% 0.90/1.14      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 0.90/1.14         ((v2_struct_0 @ X23)
% 0.90/1.14          | ~ (v2_pre_topc @ X23)
% 0.90/1.14          | ~ (l1_pre_topc @ X23)
% 0.90/1.14          | ~ (m1_pre_topc @ X24 @ X25)
% 0.90/1.14          | ((k2_tmap_1 @ X25 @ X23 @ X26 @ X24)
% 0.90/1.14              = (k2_partfun1 @ (u1_struct_0 @ X25) @ (u1_struct_0 @ X23) @ 
% 0.90/1.14                 X26 @ (u1_struct_0 @ X24)))
% 0.90/1.14          | ~ (m1_subset_1 @ X26 @ 
% 0.90/1.14               (k1_zfmisc_1 @ 
% 0.90/1.14                (k2_zfmisc_1 @ (u1_struct_0 @ X25) @ (u1_struct_0 @ X23))))
% 0.90/1.14          | ~ (v1_funct_2 @ X26 @ (u1_struct_0 @ X25) @ (u1_struct_0 @ X23))
% 0.90/1.14          | ~ (v1_funct_1 @ X26)
% 0.90/1.14          | ~ (l1_pre_topc @ X25)
% 0.90/1.14          | ~ (v2_pre_topc @ X25)
% 0.90/1.14          | (v2_struct_0 @ X25))),
% 0.90/1.14      inference('cnf', [status(esa)], [d4_tmap_1])).
% 0.90/1.14  thf('268', plain,
% 0.90/1.14      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.90/1.14         (~ (m1_subset_1 @ X1 @ 
% 0.90/1.14             (k1_zfmisc_1 @ 
% 0.90/1.14              (k2_zfmisc_1 @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ X0))))
% 0.90/1.14          | (v2_struct_0 @ sk_D)
% 0.90/1.14          | ~ (v2_pre_topc @ sk_D)
% 0.90/1.14          | ~ (l1_pre_topc @ sk_D)
% 0.90/1.14          | ~ (v1_funct_1 @ X1)
% 0.90/1.14          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ X0))
% 0.90/1.14          | ((k2_tmap_1 @ sk_D @ X0 @ X1 @ X2)
% 0.90/1.14              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ X0) @ 
% 0.90/1.14                 X1 @ (u1_struct_0 @ X2)))
% 0.90/1.14          | ~ (m1_pre_topc @ X2 @ sk_D)
% 0.90/1.14          | ~ (l1_pre_topc @ X0)
% 0.90/1.14          | ~ (v2_pre_topc @ X0)
% 0.90/1.14          | (v2_struct_0 @ X0))),
% 0.90/1.14      inference('sup-', [status(thm)], ['266', '267'])).
% 0.90/1.14  thf('269', plain, ((v2_pre_topc @ sk_D)),
% 0.90/1.14      inference('demod', [status(thm)], ['183', '184', '185'])).
% 0.90/1.14  thf('270', plain, ((l1_pre_topc @ sk_D)),
% 0.90/1.14      inference('demod', [status(thm)], ['8', '9'])).
% 0.90/1.14  thf('271', plain, (((k2_struct_0 @ sk_C) = (u1_struct_0 @ sk_D))),
% 0.90/1.14      inference('demod', [status(thm)], ['58', '63'])).
% 0.90/1.14  thf('272', plain, (((k2_struct_0 @ sk_C) = (u1_struct_0 @ sk_D))),
% 0.90/1.14      inference('demod', [status(thm)], ['58', '63'])).
% 0.90/1.14  thf('273', plain,
% 0.90/1.14      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.90/1.14         (~ (m1_subset_1 @ X1 @ 
% 0.90/1.14             (k1_zfmisc_1 @ 
% 0.90/1.14              (k2_zfmisc_1 @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ X0))))
% 0.90/1.14          | (v2_struct_0 @ sk_D)
% 0.90/1.14          | ~ (v1_funct_1 @ X1)
% 0.90/1.14          | ~ (v1_funct_2 @ X1 @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ X0))
% 0.90/1.14          | ((k2_tmap_1 @ sk_D @ X0 @ X1 @ X2)
% 0.90/1.14              = (k2_partfun1 @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ X0) @ 
% 0.90/1.14                 X1 @ (u1_struct_0 @ X2)))
% 0.90/1.14          | ~ (m1_pre_topc @ X2 @ sk_D)
% 0.90/1.14          | ~ (l1_pre_topc @ X0)
% 0.90/1.14          | ~ (v2_pre_topc @ X0)
% 0.90/1.14          | (v2_struct_0 @ X0))),
% 0.90/1.14      inference('demod', [status(thm)], ['268', '269', '270', '271', '272'])).
% 0.90/1.14  thf('274', plain,
% 0.90/1.14      (![X0 : $i]:
% 0.90/1.14         ((v2_struct_0 @ sk_B)
% 0.90/1.14          | ~ (v2_pre_topc @ sk_B)
% 0.90/1.14          | ~ (l1_pre_topc @ sk_B)
% 0.90/1.14          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.90/1.14          | ((k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0)
% 0.90/1.14              = (k2_partfun1 @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.90/1.14                 sk_E @ (u1_struct_0 @ X0)))
% 0.90/1.14          | ~ (v1_funct_2 @ sk_E @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))
% 0.90/1.14          | ~ (v1_funct_1 @ sk_E)
% 0.90/1.14          | (v2_struct_0 @ sk_D))),
% 0.90/1.14      inference('sup-', [status(thm)], ['265', '273'])).
% 0.90/1.14  thf('275', plain, ((v2_pre_topc @ sk_B)),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf('276', plain, ((l1_pre_topc @ sk_B)),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf('277', plain,
% 0.90/1.14      ((v1_funct_2 @ sk_E @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 0.90/1.14      inference('demod', [status(thm)], ['102', '103'])).
% 0.90/1.14  thf('278', plain, ((v1_funct_1 @ sk_E)),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf('279', plain,
% 0.90/1.14      (![X0 : $i]:
% 0.90/1.14         ((v2_struct_0 @ sk_B)
% 0.90/1.14          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.90/1.14          | ((k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0)
% 0.90/1.14              = (k2_partfun1 @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.90/1.14                 sk_E @ (u1_struct_0 @ X0)))
% 0.90/1.14          | (v2_struct_0 @ sk_D))),
% 0.90/1.14      inference('demod', [status(thm)], ['274', '275', '276', '277', '278'])).
% 0.90/1.14  thf('280', plain,
% 0.90/1.14      ((~ (l1_pre_topc @ sk_D)
% 0.90/1.14        | (v2_struct_0 @ sk_D)
% 0.90/1.14        | ((k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_D)
% 0.90/1.14            = (k2_partfun1 @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.90/1.14               sk_E @ (u1_struct_0 @ sk_D)))
% 0.90/1.14        | (v2_struct_0 @ sk_B))),
% 0.90/1.14      inference('sup-', [status(thm)], ['264', '279'])).
% 0.90/1.14  thf('281', plain, ((l1_pre_topc @ sk_D)),
% 0.90/1.14      inference('demod', [status(thm)], ['8', '9'])).
% 0.90/1.14  thf('282', plain, (((k2_struct_0 @ sk_C) = (u1_struct_0 @ sk_D))),
% 0.90/1.14      inference('demod', [status(thm)], ['58', '63'])).
% 0.90/1.14  thf('283', plain,
% 0.90/1.14      (((k2_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_C)
% 0.90/1.14         = (k2_partfun1 @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_E @ 
% 0.90/1.14            (k2_struct_0 @ sk_C)))),
% 0.90/1.14      inference('clc', [status(thm)], ['130', '131'])).
% 0.90/1.14  thf('284', plain,
% 0.90/1.14      (((v2_struct_0 @ sk_D)
% 0.90/1.14        | ((k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_D)
% 0.90/1.14            = (k2_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_C))
% 0.90/1.14        | (v2_struct_0 @ sk_B))),
% 0.90/1.14      inference('demod', [status(thm)], ['280', '281', '282', '283'])).
% 0.90/1.14  thf('285', plain, (~ (v2_struct_0 @ sk_D)),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf('286', plain,
% 0.90/1.14      (((v2_struct_0 @ sk_B)
% 0.90/1.14        | ((k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_D)
% 0.90/1.14            = (k2_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_C)))),
% 0.90/1.14      inference('clc', [status(thm)], ['284', '285'])).
% 0.90/1.14  thf('287', plain, (~ (v2_struct_0 @ sk_B)),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf('288', plain,
% 0.90/1.14      (((k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_D)
% 0.90/1.14         = (k2_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_C))),
% 0.90/1.14      inference('clc', [status(thm)], ['286', '287'])).
% 0.90/1.14  thf('289', plain,
% 0.90/1.14      ((m1_subset_1 @ sk_E @ 
% 0.90/1.14        (k1_zfmisc_1 @ 
% 0.90/1.14         (k2_zfmisc_1 @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 0.90/1.14      inference('demod', [status(thm)], ['86', '87'])).
% 0.90/1.14  thf('290', plain, (((k2_struct_0 @ sk_C) = (u1_struct_0 @ sk_D))),
% 0.90/1.14      inference('demod', [status(thm)], ['58', '63'])).
% 0.90/1.14  thf('291', plain,
% 0.90/1.14      (![X43 : $i, X44 : $i, X45 : $i, X46 : $i, X47 : $i]:
% 0.90/1.14         ((v2_struct_0 @ X46)
% 0.90/1.14          | ~ (v2_pre_topc @ X46)
% 0.90/1.14          | ~ (l1_pre_topc @ X46)
% 0.90/1.14          | ~ (v1_funct_1 @ X47)
% 0.90/1.14          | ~ (v1_funct_2 @ X47 @ (u1_struct_0 @ X43) @ (u1_struct_0 @ X46))
% 0.90/1.14          | ~ (m1_subset_1 @ X47 @ 
% 0.90/1.14               (k1_zfmisc_1 @ 
% 0.90/1.14                (k2_zfmisc_1 @ (u1_struct_0 @ X43) @ (u1_struct_0 @ X46))))
% 0.90/1.14          | ~ (m1_subset_1 @ X45 @ (u1_struct_0 @ X43))
% 0.90/1.14          | (r1_tmap_1 @ X43 @ X46 @ X47 @ X45)
% 0.90/1.14          | ~ (r1_tmap_1 @ X44 @ X46 @ (k2_tmap_1 @ X43 @ X46 @ X47 @ X44) @ 
% 0.90/1.14               X45)
% 0.90/1.14          | ~ (m1_subset_1 @ X45 @ (u1_struct_0 @ X44))
% 0.90/1.14          | ~ (m1_pre_topc @ X44 @ X43)
% 0.90/1.14          | ~ (v1_tsep_1 @ X44 @ X43)
% 0.90/1.14          | (v2_struct_0 @ X44)
% 0.90/1.14          | ~ (l1_pre_topc @ X43)
% 0.90/1.14          | ~ (v2_pre_topc @ X43)
% 0.90/1.14          | (v2_struct_0 @ X43))),
% 0.90/1.14      inference('simplify', [status(thm)], ['146'])).
% 0.90/1.14  thf('292', plain,
% 0.90/1.14      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.90/1.14         (~ (m1_subset_1 @ X1 @ 
% 0.90/1.14             (k1_zfmisc_1 @ 
% 0.90/1.14              (k2_zfmisc_1 @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ X0))))
% 0.90/1.14          | (v2_struct_0 @ sk_D)
% 0.90/1.14          | ~ (v2_pre_topc @ sk_D)
% 0.90/1.14          | ~ (l1_pre_topc @ sk_D)
% 0.90/1.14          | (v2_struct_0 @ X2)
% 0.90/1.14          | ~ (v1_tsep_1 @ X2 @ sk_D)
% 0.90/1.14          | ~ (m1_pre_topc @ X2 @ sk_D)
% 0.90/1.14          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X2))
% 0.90/1.14          | ~ (r1_tmap_1 @ X2 @ X0 @ (k2_tmap_1 @ sk_D @ X0 @ X1 @ X2) @ X3)
% 0.90/1.14          | (r1_tmap_1 @ sk_D @ X0 @ X1 @ X3)
% 0.90/1.14          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ sk_D))
% 0.90/1.14          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ X0))
% 0.90/1.14          | ~ (v1_funct_1 @ X1)
% 0.90/1.14          | ~ (l1_pre_topc @ X0)
% 0.90/1.14          | ~ (v2_pre_topc @ X0)
% 0.90/1.14          | (v2_struct_0 @ X0))),
% 0.90/1.14      inference('sup-', [status(thm)], ['290', '291'])).
% 0.90/1.14  thf('293', plain, ((v2_pre_topc @ sk_D)),
% 0.90/1.14      inference('demod', [status(thm)], ['183', '184', '185'])).
% 0.90/1.14  thf('294', plain, ((l1_pre_topc @ sk_D)),
% 0.90/1.14      inference('demod', [status(thm)], ['8', '9'])).
% 0.90/1.14  thf('295', plain, (((k2_struct_0 @ sk_C) = (u1_struct_0 @ sk_D))),
% 0.90/1.14      inference('demod', [status(thm)], ['58', '63'])).
% 0.90/1.14  thf('296', plain, (((k2_struct_0 @ sk_C) = (u1_struct_0 @ sk_D))),
% 0.90/1.14      inference('demod', [status(thm)], ['58', '63'])).
% 0.90/1.14  thf('297', plain,
% 0.90/1.14      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.90/1.14         (~ (m1_subset_1 @ X1 @ 
% 0.90/1.14             (k1_zfmisc_1 @ 
% 0.90/1.14              (k2_zfmisc_1 @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ X0))))
% 0.90/1.14          | (v2_struct_0 @ sk_D)
% 0.90/1.14          | (v2_struct_0 @ X2)
% 0.90/1.14          | ~ (v1_tsep_1 @ X2 @ sk_D)
% 0.90/1.14          | ~ (m1_pre_topc @ X2 @ sk_D)
% 0.90/1.14          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X2))
% 0.90/1.14          | ~ (r1_tmap_1 @ X2 @ X0 @ (k2_tmap_1 @ sk_D @ X0 @ X1 @ X2) @ X3)
% 0.90/1.14          | (r1_tmap_1 @ sk_D @ X0 @ X1 @ X3)
% 0.90/1.14          | ~ (m1_subset_1 @ X3 @ (k2_struct_0 @ sk_C))
% 0.90/1.14          | ~ (v1_funct_2 @ X1 @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ X0))
% 0.90/1.14          | ~ (v1_funct_1 @ X1)
% 0.90/1.14          | ~ (l1_pre_topc @ X0)
% 0.90/1.14          | ~ (v2_pre_topc @ X0)
% 0.90/1.14          | (v2_struct_0 @ X0))),
% 0.90/1.14      inference('demod', [status(thm)], ['292', '293', '294', '295', '296'])).
% 0.90/1.14  thf('298', plain,
% 0.90/1.14      (![X0 : $i, X1 : $i]:
% 0.90/1.14         ((v2_struct_0 @ sk_B)
% 0.90/1.14          | ~ (v2_pre_topc @ sk_B)
% 0.90/1.14          | ~ (l1_pre_topc @ sk_B)
% 0.90/1.14          | ~ (v1_funct_1 @ sk_E)
% 0.90/1.14          | ~ (v1_funct_2 @ sk_E @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))
% 0.90/1.14          | ~ (m1_subset_1 @ X0 @ (k2_struct_0 @ sk_C))
% 0.90/1.14          | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X0)
% 0.90/1.14          | ~ (r1_tmap_1 @ X1 @ sk_B @ (k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X1) @ 
% 0.90/1.14               X0)
% 0.90/1.14          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ X1))
% 0.90/1.14          | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.90/1.14          | ~ (v1_tsep_1 @ X1 @ sk_D)
% 0.90/1.14          | (v2_struct_0 @ X1)
% 0.90/1.14          | (v2_struct_0 @ sk_D))),
% 0.90/1.14      inference('sup-', [status(thm)], ['289', '297'])).
% 0.90/1.14  thf('299', plain, ((v2_pre_topc @ sk_B)),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf('300', plain, ((l1_pre_topc @ sk_B)),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf('301', plain, ((v1_funct_1 @ sk_E)),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf('302', plain,
% 0.90/1.14      ((v1_funct_2 @ sk_E @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 0.90/1.14      inference('demod', [status(thm)], ['102', '103'])).
% 0.90/1.14  thf('303', plain,
% 0.90/1.14      (![X0 : $i, X1 : $i]:
% 0.90/1.14         ((v2_struct_0 @ sk_B)
% 0.90/1.14          | ~ (m1_subset_1 @ X0 @ (k2_struct_0 @ sk_C))
% 0.90/1.14          | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X0)
% 0.90/1.14          | ~ (r1_tmap_1 @ X1 @ sk_B @ (k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X1) @ 
% 0.90/1.14               X0)
% 0.90/1.14          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ X1))
% 0.90/1.14          | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.90/1.14          | ~ (v1_tsep_1 @ X1 @ sk_D)
% 0.90/1.14          | (v2_struct_0 @ X1)
% 0.90/1.14          | (v2_struct_0 @ sk_D))),
% 0.90/1.14      inference('demod', [status(thm)], ['298', '299', '300', '301', '302'])).
% 0.90/1.14  thf('304', plain,
% 0.90/1.14      (![X0 : $i]:
% 0.90/1.14         (~ (r1_tmap_1 @ sk_D @ sk_B @ 
% 0.90/1.14             (k2_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_C) @ X0)
% 0.90/1.14          | (v2_struct_0 @ sk_D)
% 0.90/1.14          | (v2_struct_0 @ sk_D)
% 0.90/1.14          | ~ (v1_tsep_1 @ sk_D @ sk_D)
% 0.90/1.14          | ~ (m1_pre_topc @ sk_D @ sk_D)
% 0.90/1.14          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_D))
% 0.90/1.14          | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X0)
% 0.90/1.14          | ~ (m1_subset_1 @ X0 @ (k2_struct_0 @ sk_C))
% 0.90/1.14          | (v2_struct_0 @ sk_B))),
% 0.90/1.14      inference('sup-', [status(thm)], ['288', '303'])).
% 0.90/1.14  thf('305', plain, (((k2_struct_0 @ sk_C) = (u1_struct_0 @ sk_D))),
% 0.90/1.14      inference('demod', [status(thm)], ['58', '63'])).
% 0.90/1.14  thf('306', plain,
% 0.90/1.14      (![X0 : $i]:
% 0.90/1.14         (~ (m1_pre_topc @ X0 @ X0)
% 0.90/1.14          | ~ (v3_pre_topc @ (u1_struct_0 @ X0) @ X0)
% 0.90/1.14          | (v1_tsep_1 @ X0 @ X0)
% 0.90/1.14          | ~ (l1_pre_topc @ X0)
% 0.90/1.14          | ~ (v2_pre_topc @ X0))),
% 0.90/1.14      inference('sup-', [status(thm)], ['162', '164'])).
% 0.90/1.14  thf('307', plain,
% 0.90/1.14      ((~ (v3_pre_topc @ (k2_struct_0 @ sk_C) @ sk_D)
% 0.90/1.14        | ~ (v2_pre_topc @ sk_D)
% 0.90/1.14        | ~ (l1_pre_topc @ sk_D)
% 0.90/1.14        | (v1_tsep_1 @ sk_D @ sk_D)
% 0.90/1.14        | ~ (m1_pre_topc @ sk_D @ sk_D))),
% 0.90/1.14      inference('sup-', [status(thm)], ['305', '306'])).
% 0.90/1.14  thf('308', plain, ((v3_pre_topc @ (k2_struct_0 @ sk_C) @ sk_D)),
% 0.90/1.14      inference('demod', [status(thm)], ['180', '186', '187'])).
% 0.90/1.14  thf('309', plain, ((v2_pre_topc @ sk_D)),
% 0.90/1.14      inference('demod', [status(thm)], ['183', '184', '185'])).
% 0.90/1.14  thf('310', plain, ((l1_pre_topc @ sk_D)),
% 0.90/1.14      inference('demod', [status(thm)], ['8', '9'])).
% 0.90/1.14  thf('311', plain, ((m1_pre_topc @ sk_D @ sk_C)),
% 0.90/1.14      inference('demod', [status(thm)], ['5', '10', '11', '16'])).
% 0.90/1.14  thf('312', plain,
% 0.90/1.14      (![X20 : $i, X21 : $i]:
% 0.90/1.14         (~ (l1_pre_topc @ X20)
% 0.90/1.14          | ~ (m1_pre_topc @ X21 @ X20)
% 0.90/1.14          | (m1_pre_topc @ X21 @ 
% 0.90/1.14             (g1_pre_topc @ (u1_struct_0 @ X20) @ (u1_pre_topc @ X20)))
% 0.90/1.14          | ~ (l1_pre_topc @ X21))),
% 0.90/1.14      inference('cnf', [status(esa)], [t65_pre_topc])).
% 0.90/1.14  thf('313', plain,
% 0.90/1.14      ((~ (l1_pre_topc @ sk_D)
% 0.90/1.14        | (m1_pre_topc @ sk_D @ 
% 0.90/1.14           (g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)))
% 0.90/1.14        | ~ (l1_pre_topc @ sk_C))),
% 0.90/1.14      inference('sup-', [status(thm)], ['311', '312'])).
% 0.90/1.14  thf('314', plain, ((l1_pre_topc @ sk_D)),
% 0.90/1.14      inference('demod', [status(thm)], ['8', '9'])).
% 0.90/1.14  thf('315', plain, (((u1_struct_0 @ sk_C) = (k2_struct_0 @ sk_C))),
% 0.90/1.14      inference('demod', [status(thm)], ['69', '70'])).
% 0.90/1.14  thf('316', plain,
% 0.90/1.14      (((g1_pre_topc @ (k2_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) = (sk_D))),
% 0.90/1.14      inference('demod', [status(thm)], ['79', '80'])).
% 0.90/1.14  thf('317', plain, ((l1_pre_topc @ sk_C)),
% 0.90/1.14      inference('demod', [status(thm)], ['14', '15'])).
% 0.90/1.14  thf('318', plain, ((m1_pre_topc @ sk_D @ sk_D)),
% 0.90/1.14      inference('demod', [status(thm)], ['313', '314', '315', '316', '317'])).
% 0.90/1.14  thf('319', plain, ((v1_tsep_1 @ sk_D @ sk_D)),
% 0.90/1.14      inference('demod', [status(thm)], ['307', '308', '309', '310', '318'])).
% 0.90/1.14  thf('320', plain, ((m1_pre_topc @ sk_D @ sk_D)),
% 0.90/1.14      inference('demod', [status(thm)], ['313', '314', '315', '316', '317'])).
% 0.90/1.14  thf('321', plain, (((k2_struct_0 @ sk_C) = (u1_struct_0 @ sk_D))),
% 0.90/1.14      inference('demod', [status(thm)], ['58', '63'])).
% 0.90/1.14  thf('322', plain,
% 0.90/1.14      (![X0 : $i]:
% 0.90/1.14         (~ (r1_tmap_1 @ sk_D @ sk_B @ 
% 0.90/1.14             (k2_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_C) @ X0)
% 0.90/1.14          | (v2_struct_0 @ sk_D)
% 0.90/1.14          | (v2_struct_0 @ sk_D)
% 0.90/1.14          | ~ (m1_subset_1 @ X0 @ (k2_struct_0 @ sk_C))
% 0.90/1.14          | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X0)
% 0.90/1.14          | ~ (m1_subset_1 @ X0 @ (k2_struct_0 @ sk_C))
% 0.90/1.14          | (v2_struct_0 @ sk_B))),
% 0.90/1.14      inference('demod', [status(thm)], ['304', '319', '320', '321'])).
% 0.90/1.14  thf('323', plain,
% 0.90/1.14      (![X0 : $i]:
% 0.90/1.14         ((v2_struct_0 @ sk_B)
% 0.90/1.14          | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X0)
% 0.90/1.14          | ~ (m1_subset_1 @ X0 @ (k2_struct_0 @ sk_C))
% 0.90/1.14          | (v2_struct_0 @ sk_D)
% 0.90/1.14          | ~ (r1_tmap_1 @ sk_D @ sk_B @ 
% 0.90/1.14               (k2_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_C) @ X0))),
% 0.90/1.14      inference('simplify', [status(thm)], ['322'])).
% 0.90/1.14  thf('324', plain,
% 0.90/1.14      (((v2_struct_0 @ sk_C)
% 0.90/1.14        | (v2_struct_0 @ sk_D)
% 0.90/1.14        | (v2_struct_0 @ sk_B)
% 0.90/1.14        | (v2_struct_0 @ sk_D)
% 0.90/1.14        | ~ (m1_subset_1 @ sk_F @ (k2_struct_0 @ sk_C))
% 0.90/1.14        | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)
% 0.90/1.14        | (v2_struct_0 @ sk_B))),
% 0.90/1.14      inference('sup-', [status(thm)], ['263', '323'])).
% 0.90/1.14  thf('325', plain, ((m1_subset_1 @ sk_F @ (k2_struct_0 @ sk_C))),
% 0.90/1.14      inference('demod', [status(thm)], ['207', '208'])).
% 0.90/1.14  thf('326', plain,
% 0.90/1.14      (((v2_struct_0 @ sk_C)
% 0.90/1.14        | (v2_struct_0 @ sk_D)
% 0.90/1.14        | (v2_struct_0 @ sk_B)
% 0.90/1.14        | (v2_struct_0 @ sk_D)
% 0.90/1.14        | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)
% 0.90/1.14        | (v2_struct_0 @ sk_B))),
% 0.90/1.14      inference('demod', [status(thm)], ['324', '325'])).
% 0.90/1.14  thf('327', plain,
% 0.90/1.14      (((r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)
% 0.90/1.14        | (v2_struct_0 @ sk_B)
% 0.90/1.14        | (v2_struct_0 @ sk_D)
% 0.90/1.14        | (v2_struct_0 @ sk_C))),
% 0.90/1.14      inference('simplify', [status(thm)], ['326'])).
% 0.90/1.14  thf('328', plain, (~ (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf('329', plain,
% 0.90/1.14      (((v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_B))),
% 0.90/1.14      inference('sup-', [status(thm)], ['327', '328'])).
% 0.90/1.14  thf('330', plain, (~ (v2_struct_0 @ sk_C)),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf('331', plain, (((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_D))),
% 0.90/1.14      inference('clc', [status(thm)], ['329', '330'])).
% 0.90/1.14  thf('332', plain, (~ (v2_struct_0 @ sk_B)),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf('333', plain, ((v2_struct_0 @ sk_D)),
% 0.90/1.14      inference('clc', [status(thm)], ['331', '332'])).
% 0.90/1.14  thf('334', plain, ($false), inference('demod', [status(thm)], ['0', '333'])).
% 0.90/1.14  
% 0.90/1.14  % SZS output end Refutation
% 0.90/1.14  
% 0.90/1.15  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
