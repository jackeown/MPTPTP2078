%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.PAOTOL9hWo

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:10:32 EST 2020

% Result     : Theorem 0.83s
% Output     : Refutation 0.83s
% Verified   : 
% Statistics : Number of formulae       :  195 (3386 expanded)
%              Number of leaves         :   42 ( 996 expanded)
%              Depth                    :   26
%              Number of atoms          : 1757 (91108 expanded)
%              Number of equality atoms :   43 (2422 expanded)
%              Maximal formula depth    :   33 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_G_type,type,(
    sk_G: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_tmap_1_type,type,(
    k3_tmap_1: $i > $i > $i > $i > $i > $i )).

thf(r1_tmap_1_type,type,(
    r1_tmap_1: $i > $i > $i > $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(g1_pre_topc_type,type,(
    g1_pre_topc: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

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

thf(sk_C_type,type,(
    sk_C: $i )).

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
    ! [X23: $i] :
      ( ( m1_pre_topc @ X23 @ X23 )
      | ~ ( l1_pre_topc @ X23 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf(t59_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) )
         => ( m1_pre_topc @ B @ A ) ) ) )).

thf('11',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( m1_pre_topc @ X18 @ ( g1_pre_topc @ ( u1_struct_0 @ X19 ) @ ( u1_pre_topc @ X19 ) ) )
      | ( m1_pre_topc @ X18 @ X19 )
      | ~ ( l1_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[t59_pre_topc])).

thf('12',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,
    ( ~ ( l1_pre_topc @ sk_D )
    | ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) ) @ sk_C )
    | ~ ( l1_pre_topc @ sk_C ) ),
    inference('sup-',[status(thm)],['9','12'])).

thf('14',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('15',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( m1_pre_topc @ X15 @ X16 )
      | ( l1_pre_topc @ X15 )
      | ~ ( l1_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('16',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_D ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) )
    = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( m1_pre_topc @ X15 @ X16 )
      | ( l1_pre_topc @ X15 )
      | ~ ( l1_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('22',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_C ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,(
    m1_pre_topc @ sk_D @ sk_C ),
    inference(demod,[status(thm)],['13','18','19','24'])).

thf('26',plain,(
    ! [X23: $i] :
      ( ( m1_pre_topc @ X23 @ X23 )
      | ~ ( l1_pre_topc @ X23 ) ) ),
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

thf('27',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( m1_pre_topc @ X24 @ X25 )
      | ~ ( m1_pre_topc @ X24 @ X26 )
      | ( r1_tarski @ ( u1_struct_0 @ X24 ) @ ( u1_struct_0 @ X26 ) )
      | ~ ( m1_pre_topc @ X26 @ X25 )
      | ~ ( l1_pre_topc @ X25 )
      | ~ ( v2_pre_topc @ X25 ) ) ),
    inference(cnf,[status(esa)],[t4_tsep_1])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ( r1_tarski @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X1 ) )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_pre_topc @ X0 @ X1 )
      | ( r1_tarski @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X1 ) )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,
    ( ~ ( l1_pre_topc @ sk_D )
    | ~ ( v2_pre_topc @ sk_D )
    | ~ ( m1_pre_topc @ sk_C @ sk_D )
    | ( r1_tarski @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['25','29'])).

thf('31',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['16','17'])).

thf('32',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( v2_pre_topc @ B ) ) ) )).

thf('33',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_pre_topc @ X11 @ X12 )
      | ( v2_pre_topc @ X11 )
      | ~ ( l1_pre_topc @ X12 )
      | ~ ( v2_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[cc1_pre_topc])).

thf('34',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_pre_topc @ sk_D ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    v2_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['34','35','36'])).

thf('38',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) )
    = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    ! [X23: $i] :
      ( ( m1_pre_topc @ X23 @ X23 )
      | ~ ( l1_pre_topc @ X23 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf(t65_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( l1_pre_topc @ B )
         => ( ( m1_pre_topc @ A @ B )
          <=> ( m1_pre_topc @ A @ ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ) )).

thf('40',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( l1_pre_topc @ X20 )
      | ~ ( m1_pre_topc @ X21 @ X20 )
      | ( m1_pre_topc @ X21 @ ( g1_pre_topc @ ( u1_struct_0 @ X20 ) @ ( u1_pre_topc @ X20 ) ) )
      | ~ ( l1_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[t65_pre_topc])).

thf('41',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,
    ( ( m1_pre_topc @ sk_C @ sk_D )
    | ~ ( l1_pre_topc @ sk_C ) ),
    inference('sup+',[status(thm)],['38','42'])).

thf('44',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['22','23'])).

thf('45',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['30','31','37','45'])).

thf('47',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('48',plain,
    ( ~ ( r1_tarski @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D ) )
    | ( ( u1_struct_0 @ sk_C )
      = ( u1_struct_0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( m1_pre_topc @ X24 @ X25 )
      | ~ ( m1_pre_topc @ X24 @ X26 )
      | ( r1_tarski @ ( u1_struct_0 @ X24 ) @ ( u1_struct_0 @ X26 ) )
      | ~ ( m1_pre_topc @ X26 @ X25 )
      | ~ ( l1_pre_topc @ X25 )
      | ~ ( v2_pre_topc @ X25 ) ) ),
    inference(cnf,[status(esa)],[t4_tsep_1])).

thf('52',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( r1_tarski @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( r1_tarski @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ sk_C @ X0 ) ) ),
    inference(demod,[status(thm)],['52','53','54'])).

thf('56',plain,
    ( ~ ( m1_pre_topc @ sk_C @ sk_D )
    | ( r1_tarski @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['49','55'])).

thf('57',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(demod,[status(thm)],['43','44'])).

thf('58',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,
    ( ( u1_struct_0 @ sk_C )
    = ( u1_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['48','58'])).

thf('60',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['8','59'])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('61',plain,(
    ! [X13: $i] :
      ( ( ( k2_struct_0 @ X13 )
        = ( u1_struct_0 @ X13 ) )
      | ~ ( l1_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('62',plain,
    ( ( u1_struct_0 @ sk_C )
    = ( u1_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['48','58'])).

thf('63',plain,
    ( ( ( u1_struct_0 @ sk_C )
      = ( k2_struct_0 @ sk_D ) )
    | ~ ( l1_struct_0 @ sk_D ) ),
    inference('sup+',[status(thm)],['61','62'])).

thf('64',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['16','17'])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('65',plain,(
    ! [X14: $i] :
      ( ( l1_struct_0 @ X14 )
      | ~ ( l1_pre_topc @ X14 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('66',plain,(
    l1_struct_0 @ sk_D ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,
    ( ( u1_struct_0 @ sk_C )
    = ( k2_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['63','66'])).

thf('68',plain,(
    ! [X13: $i] :
      ( ( ( k2_struct_0 @ X13 )
        = ( u1_struct_0 @ X13 ) )
      | ~ ( l1_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('69',plain,
    ( ( u1_struct_0 @ sk_C )
    = ( k2_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['63','66'])).

thf('70',plain,
    ( ( ( k2_struct_0 @ sk_C )
      = ( k2_struct_0 @ sk_D ) )
    | ~ ( l1_struct_0 @ sk_C ) ),
    inference('sup+',[status(thm)],['68','69'])).

thf('71',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['22','23'])).

thf('72',plain,(
    ! [X14: $i] :
      ( ( l1_struct_0 @ X14 )
      | ~ ( l1_pre_topc @ X14 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('73',plain,(
    l1_struct_0 @ sk_C ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,
    ( ( k2_struct_0 @ sk_C )
    = ( k2_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['70','73'])).

thf('75',plain,
    ( ( u1_struct_0 @ sk_C )
    = ( k2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['67','74'])).

thf('76',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['60','75'])).

thf('77',plain,
    ( ( u1_struct_0 @ sk_C )
    = ( u1_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['48','58'])).

thf('78',plain,
    ( ( u1_struct_0 @ sk_C )
    = ( k2_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['63','66'])).

thf('79',plain,
    ( ( k2_struct_0 @ sk_D )
    = ( u1_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['77','78'])).

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

thf('80',plain,(
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
      | ~ ( r1_tarski @ X34 @ ( u1_struct_0 @ X33 ) )
      | ~ ( r2_hidden @ X37 @ X34 )
      | ~ ( v3_pre_topc @ X34 @ X31 )
      | ~ ( m1_subset_1 @ X37 @ ( u1_struct_0 @ X31 ) )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X31 ) @ ( u1_struct_0 @ X30 ) ) ) )
      | ~ ( v1_funct_2 @ X36 @ ( u1_struct_0 @ X31 ) @ ( u1_struct_0 @ X30 ) )
      | ~ ( v1_funct_1 @ X36 )
      | ~ ( m1_pre_topc @ X33 @ X32 )
      | ( v2_struct_0 @ X33 )
      | ~ ( l1_pre_topc @ X32 )
      | ~ ( v2_pre_topc @ X32 )
      | ( v2_struct_0 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t84_tmap_1])).

thf('81',plain,(
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
      | ~ ( v3_pre_topc @ X34 @ X31 )
      | ~ ( r2_hidden @ X35 @ X34 )
      | ~ ( r1_tarski @ X34 @ ( u1_struct_0 @ X33 ) )
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
    inference(simplify,[status(thm)],['80'])).

thf('82',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_D ) @ ( u1_struct_0 @ X0 ) ) ) )
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
    inference('sup-',[status(thm)],['79','81'])).

thf('83',plain,
    ( ( k2_struct_0 @ sk_D )
    = ( u1_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['77','78'])).

thf('84',plain,
    ( ( k2_struct_0 @ sk_D )
    = ( u1_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['77','78'])).

thf('85',plain,
    ( ( k2_struct_0 @ sk_D )
    = ( u1_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['77','78'])).

thf('86',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_D ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ sk_D )
      | ~ ( m1_pre_topc @ sk_D @ X2 )
      | ~ ( m1_pre_topc @ X3 @ sk_D )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_D ) ) )
      | ~ ( m1_subset_1 @ X5 @ ( u1_struct_0 @ X3 ) )
      | ~ ( r1_tmap_1 @ X3 @ X0 @ ( k3_tmap_1 @ X2 @ X0 @ sk_D @ X3 @ X1 ) @ X5 )
      | ( r1_tmap_1 @ sk_D @ X0 @ X1 @ X5 )
      | ~ ( r1_tarski @ X4 @ ( u1_struct_0 @ X3 ) )
      | ~ ( r2_hidden @ X5 @ X4 )
      | ~ ( v3_pre_topc @ X4 @ sk_D )
      | ~ ( m1_subset_1 @ X5 @ ( k2_struct_0 @ sk_D ) )
      | ~ ( v1_funct_2 @ X1 @ ( k2_struct_0 @ sk_D ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( m1_pre_topc @ X3 @ X2 )
      | ( v2_struct_0 @ X3 )
      | ~ ( l1_pre_topc @ X2 )
      | ~ ( v2_pre_topc @ X2 )
      | ( v2_struct_0 @ X2 ) ) ),
    inference(demod,[status(thm)],['82','83','84','85'])).

thf('87',plain,
    ( ( k2_struct_0 @ sk_C )
    = ( k2_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['70','73'])).

thf('88',plain,
    ( ( k2_struct_0 @ sk_C )
    = ( k2_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['70','73'])).

thf('89',plain,
    ( ( k2_struct_0 @ sk_C )
    = ( k2_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['70','73'])).

thf('90',plain,
    ( ( k2_struct_0 @ sk_C )
    = ( k2_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['70','73'])).

thf('91',plain,(
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
    inference(demod,[status(thm)],['86','87','88','89','90'])).

thf('92',plain,(
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
    inference('sup-',[status(thm)],['76','91'])).

thf('93',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    ! [X13: $i] :
      ( ( ( k2_struct_0 @ X13 )
        = ( u1_struct_0 @ X13 ) )
      | ~ ( l1_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('95',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,
    ( ( v1_funct_2 @ sk_E @ ( k2_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_D ) ),
    inference('sup+',[status(thm)],['94','95'])).

thf('97',plain,(
    l1_struct_0 @ sk_D ),
    inference('sup-',[status(thm)],['64','65'])).

thf('98',plain,(
    v1_funct_2 @ sk_E @ ( k2_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['96','97'])).

thf('99',plain,
    ( ( k2_struct_0 @ sk_C )
    = ( k2_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['70','73'])).

thf('100',plain,(
    v1_funct_2 @ sk_E @ ( k2_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['98','99'])).

thf('101',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,(
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
    inference(demod,[status(thm)],['92','93','100','101','102'])).

thf('104',plain,(
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
    inference('sup-',[status(thm)],['7','103'])).

thf('105',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(demod,[status(thm)],['43','44'])).

thf('107',plain,
    ( ( u1_struct_0 @ sk_C )
    = ( k2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['67','74'])).

thf('108',plain,(
    ! [X13: $i] :
      ( ( ( k2_struct_0 @ X13 )
        = ( u1_struct_0 @ X13 ) )
      | ~ ( l1_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('109',plain,(
    m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,(
    sk_F = sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['109','110'])).

thf('112',plain,
    ( ( m1_subset_1 @ sk_F @ ( k2_struct_0 @ sk_C ) )
    | ~ ( l1_struct_0 @ sk_C ) ),
    inference('sup+',[status(thm)],['108','111'])).

thf('113',plain,(
    l1_struct_0 @ sk_C ),
    inference('sup-',[status(thm)],['71','72'])).

thf('114',plain,(
    m1_subset_1 @ sk_F @ ( k2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['112','113'])).

thf('115',plain,
    ( ( u1_struct_0 @ sk_C )
    = ( k2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['67','74'])).

thf('116',plain,(
    m1_subset_1 @ sk_F @ ( k2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['112','113'])).

thf('117',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,(
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
    inference(demod,[status(thm)],['104','105','106','107','114','115','116','117','118','119'])).

thf('121',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ~ ( v3_pre_topc @ ( k2_struct_0 @ sk_C ) @ sk_D )
    | ~ ( r2_hidden @ sk_F @ ( k2_struct_0 @ sk_C ) )
    | ~ ( r1_tarski @ ( k2_struct_0 @ sk_C ) @ ( k2_struct_0 @ sk_C ) )
    | ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['4','120'])).

thf('122',plain,
    ( ( k2_struct_0 @ sk_C )
    = ( k2_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['70','73'])).

thf(fc10_tops_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( v3_pre_topc @ ( k2_struct_0 @ A ) @ A ) ) )).

thf('123',plain,(
    ! [X22: $i] :
      ( ( v3_pre_topc @ ( k2_struct_0 @ X22 ) @ X22 )
      | ~ ( l1_pre_topc @ X22 )
      | ~ ( v2_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[fc10_tops_1])).

thf('124',plain,
    ( ( v3_pre_topc @ ( k2_struct_0 @ sk_C ) @ sk_D )
    | ~ ( v2_pre_topc @ sk_D )
    | ~ ( l1_pre_topc @ sk_D ) ),
    inference('sup+',[status(thm)],['122','123'])).

thf('125',plain,(
    v2_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['34','35','36'])).

thf('126',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['16','17'])).

thf('127',plain,(
    v3_pre_topc @ ( k2_struct_0 @ sk_C ) @ sk_D ),
    inference(demod,[status(thm)],['124','125','126'])).

thf('128',plain,(
    ! [X13: $i] :
      ( ( ( k2_struct_0 @ X13 )
        = ( u1_struct_0 @ X13 ) )
      | ~ ( l1_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('129',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['109','110'])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('130',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r2_hidden @ X3 @ X4 )
      | ( v1_xboole_0 @ X4 )
      | ~ ( m1_subset_1 @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('131',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) )
    | ( r2_hidden @ sk_F @ ( u1_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['129','130'])).

thf('132',plain,
    ( ( r2_hidden @ sk_F @ ( k2_struct_0 @ sk_C ) )
    | ~ ( l1_struct_0 @ sk_C )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['128','131'])).

thf('133',plain,(
    l1_struct_0 @ sk_C ),
    inference('sup-',[status(thm)],['71','72'])).

thf('134',plain,
    ( ( r2_hidden @ sk_F @ ( k2_struct_0 @ sk_C ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['132','133'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('135',plain,(
    ! [X17: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X17 ) )
      | ~ ( l1_struct_0 @ X17 )
      | ( v2_struct_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('136',plain,
    ( ( r2_hidden @ sk_F @ ( k2_struct_0 @ sk_C ) )
    | ( v2_struct_0 @ sk_C )
    | ~ ( l1_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['134','135'])).

thf('137',plain,(
    l1_struct_0 @ sk_C ),
    inference('sup-',[status(thm)],['71','72'])).

thf('138',plain,
    ( ( r2_hidden @ sk_F @ ( k2_struct_0 @ sk_C ) )
    | ( v2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['136','137'])).

thf('139',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('140',plain,(
    r2_hidden @ sk_F @ ( k2_struct_0 @ sk_C ) ),
    inference(clc,[status(thm)],['138','139'])).

thf('141',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['1'])).

thf('142',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['121','127','140','141'])).

thf('143',plain,(
    ~ ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('144',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['142','143'])).

thf('145',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('146',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['144','145'])).

thf('147',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('148',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C ) ),
    inference(clc,[status(thm)],['146','147'])).

thf('149',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('150',plain,(
    v2_struct_0 @ sk_C ),
    inference(clc,[status(thm)],['148','149'])).

thf('151',plain,(
    $false ),
    inference(demod,[status(thm)],['0','150'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.PAOTOL9hWo
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 17:02:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.83/1.05  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.83/1.05  % Solved by: fo/fo7.sh
% 0.83/1.05  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.83/1.05  % done 552 iterations in 0.582s
% 0.83/1.05  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.83/1.05  % SZS output start Refutation
% 0.83/1.05  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.83/1.05  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.83/1.05  thf(sk_A_type, type, sk_A: $i).
% 0.83/1.05  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.83/1.05  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.83/1.05  thf(sk_D_type, type, sk_D: $i).
% 0.83/1.05  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.83/1.05  thf(sk_G_type, type, sk_G: $i).
% 0.83/1.05  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.83/1.05  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.83/1.05  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.83/1.05  thf(sk_B_type, type, sk_B: $i).
% 0.83/1.05  thf(k3_tmap_1_type, type, k3_tmap_1: $i > $i > $i > $i > $i > $i).
% 0.83/1.05  thf(r1_tmap_1_type, type, r1_tmap_1: $i > $i > $i > $i > $o).
% 0.83/1.05  thf(sk_E_type, type, sk_E: $i).
% 0.83/1.05  thf(g1_pre_topc_type, type, g1_pre_topc: $i > $i > $i).
% 0.83/1.05  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.83/1.05  thf(sk_F_type, type, sk_F: $i).
% 0.83/1.05  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.83/1.05  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.83/1.05  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.83/1.05  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 0.83/1.05  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.83/1.05  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.83/1.05  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.83/1.05  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.83/1.05  thf(sk_C_type, type, sk_C: $i).
% 0.83/1.05  thf(t88_tmap_1, conjecture,
% 0.83/1.05    (![A:$i]:
% 0.83/1.05     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.83/1.05       ( ![B:$i]:
% 0.83/1.05         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.83/1.05             ( l1_pre_topc @ B ) ) =>
% 0.83/1.05           ( ![C:$i]:
% 0.83/1.05             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.83/1.05               ( ![D:$i]:
% 0.83/1.05                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.83/1.05                   ( ![E:$i]:
% 0.83/1.05                     ( ( ( v1_funct_1 @ E ) & 
% 0.83/1.05                         ( v1_funct_2 @
% 0.83/1.05                           E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 0.83/1.05                         ( m1_subset_1 @
% 0.83/1.05                           E @ 
% 0.83/1.05                           ( k1_zfmisc_1 @
% 0.83/1.05                             ( k2_zfmisc_1 @
% 0.83/1.05                               ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.83/1.05                       ( ( ( g1_pre_topc @
% 0.83/1.05                             ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) ) =
% 0.83/1.05                           ( D ) ) =>
% 0.83/1.05                         ( ![F:$i]:
% 0.83/1.05                           ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 0.83/1.05                             ( ![G:$i]:
% 0.83/1.05                               ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) ) =>
% 0.83/1.05                                 ( ( ( ( F ) = ( G ) ) & 
% 0.83/1.05                                     ( r1_tmap_1 @
% 0.83/1.05                                       C @ B @ 
% 0.83/1.05                                       ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ G ) ) =>
% 0.83/1.05                                   ( r1_tmap_1 @ D @ B @ E @ F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.83/1.05  thf(zf_stmt_0, negated_conjecture,
% 0.83/1.05    (~( ![A:$i]:
% 0.83/1.05        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.83/1.05            ( l1_pre_topc @ A ) ) =>
% 0.83/1.05          ( ![B:$i]:
% 0.83/1.05            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.83/1.05                ( l1_pre_topc @ B ) ) =>
% 0.83/1.05              ( ![C:$i]:
% 0.83/1.05                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.83/1.05                  ( ![D:$i]:
% 0.83/1.05                    ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.83/1.05                      ( ![E:$i]:
% 0.83/1.05                        ( ( ( v1_funct_1 @ E ) & 
% 0.83/1.05                            ( v1_funct_2 @
% 0.83/1.05                              E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 0.83/1.05                            ( m1_subset_1 @
% 0.83/1.05                              E @ 
% 0.83/1.05                              ( k1_zfmisc_1 @
% 0.83/1.05                                ( k2_zfmisc_1 @
% 0.83/1.05                                  ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.83/1.05                          ( ( ( g1_pre_topc @
% 0.83/1.05                                ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) ) =
% 0.83/1.05                              ( D ) ) =>
% 0.83/1.05                            ( ![F:$i]:
% 0.83/1.05                              ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 0.83/1.05                                ( ![G:$i]:
% 0.83/1.05                                  ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) ) =>
% 0.83/1.05                                    ( ( ( ( F ) = ( G ) ) & 
% 0.83/1.05                                        ( r1_tmap_1 @
% 0.83/1.05                                          C @ B @ 
% 0.83/1.05                                          ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ G ) ) =>
% 0.83/1.05                                      ( r1_tmap_1 @ D @ B @ E @ F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.83/1.05    inference('cnf.neg', [status(esa)], [t88_tmap_1])).
% 0.83/1.05  thf('0', plain, (~ (v2_struct_0 @ sk_C)),
% 0.83/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.05  thf(d10_xboole_0, axiom,
% 0.83/1.05    (![A:$i,B:$i]:
% 0.83/1.05     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.83/1.05  thf('1', plain,
% 0.83/1.05      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.83/1.05      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.83/1.05  thf('2', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.83/1.05      inference('simplify', [status(thm)], ['1'])).
% 0.83/1.05  thf(t3_subset, axiom,
% 0.83/1.05    (![A:$i,B:$i]:
% 0.83/1.05     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.83/1.05  thf('3', plain,
% 0.83/1.05      (![X5 : $i, X7 : $i]:
% 0.83/1.05         ((m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X7)) | ~ (r1_tarski @ X5 @ X7))),
% 0.83/1.05      inference('cnf', [status(esa)], [t3_subset])).
% 0.83/1.05  thf('4', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.83/1.05      inference('sup-', [status(thm)], ['2', '3'])).
% 0.83/1.05  thf('5', plain,
% 0.83/1.05      ((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.83/1.05        (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_G)),
% 0.83/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.05  thf('6', plain, (((sk_F) = (sk_G))),
% 0.83/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.05  thf('7', plain,
% 0.83/1.05      ((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.83/1.05        (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_F)),
% 0.83/1.05      inference('demod', [status(thm)], ['5', '6'])).
% 0.83/1.05  thf('8', plain,
% 0.83/1.05      ((m1_subset_1 @ sk_E @ 
% 0.83/1.05        (k1_zfmisc_1 @ 
% 0.83/1.05         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 0.83/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.05  thf('9', plain,
% 0.83/1.05      (((g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) = (sk_D))),
% 0.83/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.05  thf(t2_tsep_1, axiom,
% 0.83/1.05    (![A:$i]: ( ( l1_pre_topc @ A ) => ( m1_pre_topc @ A @ A ) ))).
% 0.83/1.05  thf('10', plain,
% 0.83/1.05      (![X23 : $i]: ((m1_pre_topc @ X23 @ X23) | ~ (l1_pre_topc @ X23))),
% 0.83/1.05      inference('cnf', [status(esa)], [t2_tsep_1])).
% 0.83/1.05  thf(t59_pre_topc, axiom,
% 0.83/1.05    (![A:$i]:
% 0.83/1.05     ( ( l1_pre_topc @ A ) =>
% 0.83/1.05       ( ![B:$i]:
% 0.83/1.05         ( ( m1_pre_topc @
% 0.83/1.05             B @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) =>
% 0.83/1.05           ( m1_pre_topc @ B @ A ) ) ) ))).
% 0.83/1.05  thf('11', plain,
% 0.83/1.05      (![X18 : $i, X19 : $i]:
% 0.83/1.05         (~ (m1_pre_topc @ X18 @ 
% 0.83/1.05             (g1_pre_topc @ (u1_struct_0 @ X19) @ (u1_pre_topc @ X19)))
% 0.83/1.05          | (m1_pre_topc @ X18 @ X19)
% 0.83/1.05          | ~ (l1_pre_topc @ X19))),
% 0.83/1.05      inference('cnf', [status(esa)], [t59_pre_topc])).
% 0.83/1.05  thf('12', plain,
% 0.83/1.05      (![X0 : $i]:
% 0.83/1.05         (~ (l1_pre_topc @ 
% 0.83/1.05             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.83/1.05          | ~ (l1_pre_topc @ X0)
% 0.83/1.05          | (m1_pre_topc @ 
% 0.83/1.05             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)) @ X0))),
% 0.83/1.05      inference('sup-', [status(thm)], ['10', '11'])).
% 0.83/1.05  thf('13', plain,
% 0.83/1.05      ((~ (l1_pre_topc @ sk_D)
% 0.83/1.05        | (m1_pre_topc @ 
% 0.83/1.05           (g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) @ sk_C)
% 0.83/1.05        | ~ (l1_pre_topc @ sk_C))),
% 0.83/1.05      inference('sup-', [status(thm)], ['9', '12'])).
% 0.83/1.05  thf('14', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.83/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.05  thf(dt_m1_pre_topc, axiom,
% 0.83/1.05    (![A:$i]:
% 0.83/1.05     ( ( l1_pre_topc @ A ) =>
% 0.83/1.05       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.83/1.05  thf('15', plain,
% 0.83/1.05      (![X15 : $i, X16 : $i]:
% 0.83/1.05         (~ (m1_pre_topc @ X15 @ X16)
% 0.83/1.05          | (l1_pre_topc @ X15)
% 0.83/1.05          | ~ (l1_pre_topc @ X16))),
% 0.83/1.05      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.83/1.05  thf('16', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_D))),
% 0.83/1.05      inference('sup-', [status(thm)], ['14', '15'])).
% 0.83/1.05  thf('17', plain, ((l1_pre_topc @ sk_A)),
% 0.83/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.05  thf('18', plain, ((l1_pre_topc @ sk_D)),
% 0.83/1.05      inference('demod', [status(thm)], ['16', '17'])).
% 0.83/1.05  thf('19', plain,
% 0.83/1.05      (((g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) = (sk_D))),
% 0.83/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.05  thf('20', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.83/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.05  thf('21', plain,
% 0.83/1.05      (![X15 : $i, X16 : $i]:
% 0.83/1.05         (~ (m1_pre_topc @ X15 @ X16)
% 0.83/1.05          | (l1_pre_topc @ X15)
% 0.83/1.05          | ~ (l1_pre_topc @ X16))),
% 0.83/1.05      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.83/1.05  thf('22', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_C))),
% 0.83/1.05      inference('sup-', [status(thm)], ['20', '21'])).
% 0.83/1.05  thf('23', plain, ((l1_pre_topc @ sk_A)),
% 0.83/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.05  thf('24', plain, ((l1_pre_topc @ sk_C)),
% 0.83/1.05      inference('demod', [status(thm)], ['22', '23'])).
% 0.83/1.05  thf('25', plain, ((m1_pre_topc @ sk_D @ sk_C)),
% 0.83/1.05      inference('demod', [status(thm)], ['13', '18', '19', '24'])).
% 0.83/1.05  thf('26', plain,
% 0.83/1.05      (![X23 : $i]: ((m1_pre_topc @ X23 @ X23) | ~ (l1_pre_topc @ X23))),
% 0.83/1.05      inference('cnf', [status(esa)], [t2_tsep_1])).
% 0.83/1.05  thf(t4_tsep_1, axiom,
% 0.83/1.05    (![A:$i]:
% 0.83/1.05     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.83/1.05       ( ![B:$i]:
% 0.83/1.05         ( ( m1_pre_topc @ B @ A ) =>
% 0.83/1.05           ( ![C:$i]:
% 0.83/1.05             ( ( m1_pre_topc @ C @ A ) =>
% 0.83/1.05               ( ( r1_tarski @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ C ) ) <=>
% 0.83/1.05                 ( m1_pre_topc @ B @ C ) ) ) ) ) ) ))).
% 0.83/1.05  thf('27', plain,
% 0.83/1.05      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.83/1.05         (~ (m1_pre_topc @ X24 @ X25)
% 0.83/1.05          | ~ (m1_pre_topc @ X24 @ X26)
% 0.83/1.05          | (r1_tarski @ (u1_struct_0 @ X24) @ (u1_struct_0 @ X26))
% 0.83/1.05          | ~ (m1_pre_topc @ X26 @ X25)
% 0.83/1.05          | ~ (l1_pre_topc @ X25)
% 0.83/1.05          | ~ (v2_pre_topc @ X25))),
% 0.83/1.05      inference('cnf', [status(esa)], [t4_tsep_1])).
% 0.83/1.05  thf('28', plain,
% 0.83/1.05      (![X0 : $i, X1 : $i]:
% 0.83/1.05         (~ (l1_pre_topc @ X0)
% 0.83/1.05          | ~ (v2_pre_topc @ X0)
% 0.83/1.05          | ~ (l1_pre_topc @ X0)
% 0.83/1.05          | ~ (m1_pre_topc @ X1 @ X0)
% 0.83/1.05          | (r1_tarski @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X1))
% 0.83/1.05          | ~ (m1_pre_topc @ X0 @ X1))),
% 0.83/1.05      inference('sup-', [status(thm)], ['26', '27'])).
% 0.83/1.05  thf('29', plain,
% 0.83/1.05      (![X0 : $i, X1 : $i]:
% 0.83/1.05         (~ (m1_pre_topc @ X0 @ X1)
% 0.83/1.05          | (r1_tarski @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X1))
% 0.83/1.05          | ~ (m1_pre_topc @ X1 @ X0)
% 0.83/1.05          | ~ (v2_pre_topc @ X0)
% 0.83/1.05          | ~ (l1_pre_topc @ X0))),
% 0.83/1.05      inference('simplify', [status(thm)], ['28'])).
% 0.83/1.05  thf('30', plain,
% 0.83/1.05      ((~ (l1_pre_topc @ sk_D)
% 0.83/1.05        | ~ (v2_pre_topc @ sk_D)
% 0.83/1.05        | ~ (m1_pre_topc @ sk_C @ sk_D)
% 0.83/1.05        | (r1_tarski @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_C)))),
% 0.83/1.05      inference('sup-', [status(thm)], ['25', '29'])).
% 0.83/1.05  thf('31', plain, ((l1_pre_topc @ sk_D)),
% 0.83/1.05      inference('demod', [status(thm)], ['16', '17'])).
% 0.83/1.05  thf('32', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.83/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.05  thf(cc1_pre_topc, axiom,
% 0.83/1.05    (![A:$i]:
% 0.83/1.05     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.83/1.05       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( v2_pre_topc @ B ) ) ) ))).
% 0.83/1.05  thf('33', plain,
% 0.83/1.05      (![X11 : $i, X12 : $i]:
% 0.83/1.05         (~ (m1_pre_topc @ X11 @ X12)
% 0.83/1.05          | (v2_pre_topc @ X11)
% 0.83/1.05          | ~ (l1_pre_topc @ X12)
% 0.83/1.05          | ~ (v2_pre_topc @ X12))),
% 0.83/1.05      inference('cnf', [status(esa)], [cc1_pre_topc])).
% 0.83/1.05  thf('34', plain,
% 0.83/1.05      ((~ (v2_pre_topc @ sk_A) | ~ (l1_pre_topc @ sk_A) | (v2_pre_topc @ sk_D))),
% 0.83/1.05      inference('sup-', [status(thm)], ['32', '33'])).
% 0.83/1.05  thf('35', plain, ((v2_pre_topc @ sk_A)),
% 0.83/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.05  thf('36', plain, ((l1_pre_topc @ sk_A)),
% 0.83/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.05  thf('37', plain, ((v2_pre_topc @ sk_D)),
% 0.83/1.05      inference('demod', [status(thm)], ['34', '35', '36'])).
% 0.83/1.05  thf('38', plain,
% 0.83/1.05      (((g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) = (sk_D))),
% 0.83/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.05  thf('39', plain,
% 0.83/1.05      (![X23 : $i]: ((m1_pre_topc @ X23 @ X23) | ~ (l1_pre_topc @ X23))),
% 0.83/1.05      inference('cnf', [status(esa)], [t2_tsep_1])).
% 0.83/1.05  thf(t65_pre_topc, axiom,
% 0.83/1.05    (![A:$i]:
% 0.83/1.05     ( ( l1_pre_topc @ A ) =>
% 0.83/1.05       ( ![B:$i]:
% 0.83/1.05         ( ( l1_pre_topc @ B ) =>
% 0.83/1.05           ( ( m1_pre_topc @ A @ B ) <=>
% 0.83/1.05             ( m1_pre_topc @
% 0.83/1.05               A @ ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ) ))).
% 0.83/1.05  thf('40', plain,
% 0.83/1.05      (![X20 : $i, X21 : $i]:
% 0.83/1.05         (~ (l1_pre_topc @ X20)
% 0.83/1.05          | ~ (m1_pre_topc @ X21 @ X20)
% 0.83/1.05          | (m1_pre_topc @ X21 @ 
% 0.83/1.05             (g1_pre_topc @ (u1_struct_0 @ X20) @ (u1_pre_topc @ X20)))
% 0.83/1.05          | ~ (l1_pre_topc @ X21))),
% 0.83/1.05      inference('cnf', [status(esa)], [t65_pre_topc])).
% 0.83/1.05  thf('41', plain,
% 0.83/1.05      (![X0 : $i]:
% 0.83/1.05         (~ (l1_pre_topc @ X0)
% 0.83/1.05          | ~ (l1_pre_topc @ X0)
% 0.83/1.05          | (m1_pre_topc @ X0 @ 
% 0.83/1.05             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.83/1.05          | ~ (l1_pre_topc @ X0))),
% 0.83/1.05      inference('sup-', [status(thm)], ['39', '40'])).
% 0.83/1.05  thf('42', plain,
% 0.83/1.05      (![X0 : $i]:
% 0.83/1.05         ((m1_pre_topc @ X0 @ 
% 0.83/1.05           (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.83/1.05          | ~ (l1_pre_topc @ X0))),
% 0.83/1.05      inference('simplify', [status(thm)], ['41'])).
% 0.83/1.05  thf('43', plain, (((m1_pre_topc @ sk_C @ sk_D) | ~ (l1_pre_topc @ sk_C))),
% 0.83/1.05      inference('sup+', [status(thm)], ['38', '42'])).
% 0.83/1.05  thf('44', plain, ((l1_pre_topc @ sk_C)),
% 0.83/1.05      inference('demod', [status(thm)], ['22', '23'])).
% 0.83/1.05  thf('45', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 0.83/1.05      inference('demod', [status(thm)], ['43', '44'])).
% 0.83/1.05  thf('46', plain, ((r1_tarski @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_C))),
% 0.83/1.05      inference('demod', [status(thm)], ['30', '31', '37', '45'])).
% 0.83/1.05  thf('47', plain,
% 0.83/1.05      (![X0 : $i, X2 : $i]:
% 0.83/1.05         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.83/1.05      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.83/1.05  thf('48', plain,
% 0.83/1.05      ((~ (r1_tarski @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D))
% 0.83/1.05        | ((u1_struct_0 @ sk_C) = (u1_struct_0 @ sk_D)))),
% 0.83/1.05      inference('sup-', [status(thm)], ['46', '47'])).
% 0.83/1.05  thf('49', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.83/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.05  thf('50', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.83/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.05  thf('51', plain,
% 0.83/1.05      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.83/1.05         (~ (m1_pre_topc @ X24 @ X25)
% 0.83/1.05          | ~ (m1_pre_topc @ X24 @ X26)
% 0.83/1.05          | (r1_tarski @ (u1_struct_0 @ X24) @ (u1_struct_0 @ X26))
% 0.83/1.05          | ~ (m1_pre_topc @ X26 @ X25)
% 0.83/1.05          | ~ (l1_pre_topc @ X25)
% 0.83/1.05          | ~ (v2_pre_topc @ X25))),
% 0.83/1.05      inference('cnf', [status(esa)], [t4_tsep_1])).
% 0.83/1.05  thf('52', plain,
% 0.83/1.05      (![X0 : $i]:
% 0.83/1.05         (~ (v2_pre_topc @ sk_A)
% 0.83/1.05          | ~ (l1_pre_topc @ sk_A)
% 0.83/1.05          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.83/1.05          | (r1_tarski @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ X0))
% 0.83/1.05          | ~ (m1_pre_topc @ sk_C @ X0))),
% 0.83/1.05      inference('sup-', [status(thm)], ['50', '51'])).
% 0.83/1.05  thf('53', plain, ((v2_pre_topc @ sk_A)),
% 0.83/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.05  thf('54', plain, ((l1_pre_topc @ sk_A)),
% 0.83/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.05  thf('55', plain,
% 0.83/1.05      (![X0 : $i]:
% 0.83/1.05         (~ (m1_pre_topc @ X0 @ sk_A)
% 0.83/1.05          | (r1_tarski @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ X0))
% 0.83/1.05          | ~ (m1_pre_topc @ sk_C @ X0))),
% 0.83/1.05      inference('demod', [status(thm)], ['52', '53', '54'])).
% 0.83/1.05  thf('56', plain,
% 0.83/1.05      ((~ (m1_pre_topc @ sk_C @ sk_D)
% 0.83/1.05        | (r1_tarski @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D)))),
% 0.83/1.05      inference('sup-', [status(thm)], ['49', '55'])).
% 0.83/1.05  thf('57', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 0.83/1.05      inference('demod', [status(thm)], ['43', '44'])).
% 0.83/1.05  thf('58', plain, ((r1_tarski @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D))),
% 0.83/1.05      inference('demod', [status(thm)], ['56', '57'])).
% 0.83/1.05  thf('59', plain, (((u1_struct_0 @ sk_C) = (u1_struct_0 @ sk_D))),
% 0.83/1.05      inference('demod', [status(thm)], ['48', '58'])).
% 0.83/1.05  thf('60', plain,
% 0.83/1.05      ((m1_subset_1 @ sk_E @ 
% 0.83/1.05        (k1_zfmisc_1 @ 
% 0.83/1.05         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 0.83/1.05      inference('demod', [status(thm)], ['8', '59'])).
% 0.83/1.05  thf(d3_struct_0, axiom,
% 0.83/1.05    (![A:$i]:
% 0.83/1.05     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.83/1.05  thf('61', plain,
% 0.83/1.05      (![X13 : $i]:
% 0.83/1.05         (((k2_struct_0 @ X13) = (u1_struct_0 @ X13)) | ~ (l1_struct_0 @ X13))),
% 0.83/1.05      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.83/1.05  thf('62', plain, (((u1_struct_0 @ sk_C) = (u1_struct_0 @ sk_D))),
% 0.83/1.05      inference('demod', [status(thm)], ['48', '58'])).
% 0.83/1.05  thf('63', plain,
% 0.83/1.05      ((((u1_struct_0 @ sk_C) = (k2_struct_0 @ sk_D)) | ~ (l1_struct_0 @ sk_D))),
% 0.83/1.05      inference('sup+', [status(thm)], ['61', '62'])).
% 0.83/1.05  thf('64', plain, ((l1_pre_topc @ sk_D)),
% 0.83/1.05      inference('demod', [status(thm)], ['16', '17'])).
% 0.83/1.05  thf(dt_l1_pre_topc, axiom,
% 0.83/1.05    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.83/1.05  thf('65', plain,
% 0.83/1.05      (![X14 : $i]: ((l1_struct_0 @ X14) | ~ (l1_pre_topc @ X14))),
% 0.83/1.05      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.83/1.05  thf('66', plain, ((l1_struct_0 @ sk_D)),
% 0.83/1.05      inference('sup-', [status(thm)], ['64', '65'])).
% 0.83/1.05  thf('67', plain, (((u1_struct_0 @ sk_C) = (k2_struct_0 @ sk_D))),
% 0.83/1.05      inference('demod', [status(thm)], ['63', '66'])).
% 0.83/1.05  thf('68', plain,
% 0.83/1.05      (![X13 : $i]:
% 0.83/1.05         (((k2_struct_0 @ X13) = (u1_struct_0 @ X13)) | ~ (l1_struct_0 @ X13))),
% 0.83/1.05      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.83/1.05  thf('69', plain, (((u1_struct_0 @ sk_C) = (k2_struct_0 @ sk_D))),
% 0.83/1.05      inference('demod', [status(thm)], ['63', '66'])).
% 0.83/1.05  thf('70', plain,
% 0.83/1.05      ((((k2_struct_0 @ sk_C) = (k2_struct_0 @ sk_D)) | ~ (l1_struct_0 @ sk_C))),
% 0.83/1.05      inference('sup+', [status(thm)], ['68', '69'])).
% 0.83/1.05  thf('71', plain, ((l1_pre_topc @ sk_C)),
% 0.83/1.05      inference('demod', [status(thm)], ['22', '23'])).
% 0.83/1.05  thf('72', plain,
% 0.83/1.05      (![X14 : $i]: ((l1_struct_0 @ X14) | ~ (l1_pre_topc @ X14))),
% 0.83/1.05      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.83/1.05  thf('73', plain, ((l1_struct_0 @ sk_C)),
% 0.83/1.05      inference('sup-', [status(thm)], ['71', '72'])).
% 0.83/1.05  thf('74', plain, (((k2_struct_0 @ sk_C) = (k2_struct_0 @ sk_D))),
% 0.83/1.05      inference('demod', [status(thm)], ['70', '73'])).
% 0.83/1.05  thf('75', plain, (((u1_struct_0 @ sk_C) = (k2_struct_0 @ sk_C))),
% 0.83/1.05      inference('demod', [status(thm)], ['67', '74'])).
% 0.83/1.05  thf('76', plain,
% 0.83/1.05      ((m1_subset_1 @ sk_E @ 
% 0.83/1.05        (k1_zfmisc_1 @ 
% 0.83/1.05         (k2_zfmisc_1 @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 0.83/1.05      inference('demod', [status(thm)], ['60', '75'])).
% 0.83/1.05  thf('77', plain, (((u1_struct_0 @ sk_C) = (u1_struct_0 @ sk_D))),
% 0.83/1.05      inference('demod', [status(thm)], ['48', '58'])).
% 0.83/1.05  thf('78', plain, (((u1_struct_0 @ sk_C) = (k2_struct_0 @ sk_D))),
% 0.83/1.05      inference('demod', [status(thm)], ['63', '66'])).
% 0.83/1.05  thf('79', plain, (((k2_struct_0 @ sk_D) = (u1_struct_0 @ sk_D))),
% 0.83/1.05      inference('demod', [status(thm)], ['77', '78'])).
% 0.83/1.05  thf(t84_tmap_1, axiom,
% 0.83/1.05    (![A:$i]:
% 0.83/1.05     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.83/1.05       ( ![B:$i]:
% 0.83/1.05         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.83/1.05             ( l1_pre_topc @ B ) ) =>
% 0.83/1.05           ( ![C:$i]:
% 0.83/1.05             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.83/1.05               ( ![D:$i]:
% 0.83/1.05                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.83/1.05                   ( ![E:$i]:
% 0.83/1.05                     ( ( ( v1_funct_1 @ E ) & 
% 0.83/1.05                         ( v1_funct_2 @
% 0.83/1.05                           E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 0.83/1.05                         ( m1_subset_1 @
% 0.83/1.05                           E @ 
% 0.83/1.05                           ( k1_zfmisc_1 @
% 0.83/1.05                             ( k2_zfmisc_1 @
% 0.83/1.05                               ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.83/1.05                       ( ( m1_pre_topc @ C @ D ) =>
% 0.83/1.05                         ( ![F:$i]:
% 0.83/1.05                           ( ( m1_subset_1 @
% 0.83/1.05                               F @ ( k1_zfmisc_1 @ ( u1_struct_0 @ D ) ) ) =>
% 0.83/1.05                             ( ![G:$i]:
% 0.83/1.05                               ( ( m1_subset_1 @ G @ ( u1_struct_0 @ D ) ) =>
% 0.83/1.05                                 ( ![H:$i]:
% 0.83/1.05                                   ( ( m1_subset_1 @ H @ ( u1_struct_0 @ C ) ) =>
% 0.83/1.05                                     ( ( ( v3_pre_topc @ F @ D ) & 
% 0.83/1.05                                         ( r2_hidden @ G @ F ) & 
% 0.83/1.05                                         ( r1_tarski @ F @ ( u1_struct_0 @ C ) ) & 
% 0.83/1.05                                         ( ( G ) = ( H ) ) ) =>
% 0.83/1.05                                       ( ( r1_tmap_1 @ D @ B @ E @ G ) <=>
% 0.83/1.05                                         ( r1_tmap_1 @
% 0.83/1.05                                           C @ B @ 
% 0.83/1.05                                           ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ 
% 0.83/1.05                                           H ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.83/1.05  thf('80', plain,
% 0.83/1.05      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i, X34 : $i, X35 : $i, X36 : $i, 
% 0.83/1.05         X37 : $i]:
% 0.83/1.05         ((v2_struct_0 @ X30)
% 0.83/1.05          | ~ (v2_pre_topc @ X30)
% 0.83/1.05          | ~ (l1_pre_topc @ X30)
% 0.83/1.05          | (v2_struct_0 @ X31)
% 0.83/1.05          | ~ (m1_pre_topc @ X31 @ X32)
% 0.83/1.05          | ~ (m1_pre_topc @ X33 @ X31)
% 0.83/1.05          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (u1_struct_0 @ X31)))
% 0.83/1.05          | ~ (m1_subset_1 @ X35 @ (u1_struct_0 @ X33))
% 0.83/1.05          | ~ (r1_tmap_1 @ X33 @ X30 @ 
% 0.83/1.05               (k3_tmap_1 @ X32 @ X30 @ X31 @ X33 @ X36) @ X35)
% 0.83/1.05          | (r1_tmap_1 @ X31 @ X30 @ X36 @ X37)
% 0.83/1.05          | ((X37) != (X35))
% 0.83/1.05          | ~ (r1_tarski @ X34 @ (u1_struct_0 @ X33))
% 0.83/1.05          | ~ (r2_hidden @ X37 @ X34)
% 0.83/1.05          | ~ (v3_pre_topc @ X34 @ X31)
% 0.83/1.05          | ~ (m1_subset_1 @ X37 @ (u1_struct_0 @ X31))
% 0.83/1.05          | ~ (m1_subset_1 @ X36 @ 
% 0.83/1.05               (k1_zfmisc_1 @ 
% 0.83/1.05                (k2_zfmisc_1 @ (u1_struct_0 @ X31) @ (u1_struct_0 @ X30))))
% 0.83/1.05          | ~ (v1_funct_2 @ X36 @ (u1_struct_0 @ X31) @ (u1_struct_0 @ X30))
% 0.83/1.05          | ~ (v1_funct_1 @ X36)
% 0.83/1.05          | ~ (m1_pre_topc @ X33 @ X32)
% 0.83/1.05          | (v2_struct_0 @ X33)
% 0.83/1.05          | ~ (l1_pre_topc @ X32)
% 0.83/1.05          | ~ (v2_pre_topc @ X32)
% 0.83/1.05          | (v2_struct_0 @ X32))),
% 0.83/1.05      inference('cnf', [status(esa)], [t84_tmap_1])).
% 0.83/1.05  thf('81', plain,
% 0.83/1.05      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 0.83/1.05         ((v2_struct_0 @ X32)
% 0.83/1.05          | ~ (v2_pre_topc @ X32)
% 0.83/1.05          | ~ (l1_pre_topc @ X32)
% 0.83/1.05          | (v2_struct_0 @ X33)
% 0.83/1.05          | ~ (m1_pre_topc @ X33 @ X32)
% 0.83/1.05          | ~ (v1_funct_1 @ X36)
% 0.83/1.05          | ~ (v1_funct_2 @ X36 @ (u1_struct_0 @ X31) @ (u1_struct_0 @ X30))
% 0.83/1.05          | ~ (m1_subset_1 @ X36 @ 
% 0.83/1.05               (k1_zfmisc_1 @ 
% 0.83/1.05                (k2_zfmisc_1 @ (u1_struct_0 @ X31) @ (u1_struct_0 @ X30))))
% 0.83/1.05          | ~ (m1_subset_1 @ X35 @ (u1_struct_0 @ X31))
% 0.83/1.05          | ~ (v3_pre_topc @ X34 @ X31)
% 0.83/1.05          | ~ (r2_hidden @ X35 @ X34)
% 0.83/1.05          | ~ (r1_tarski @ X34 @ (u1_struct_0 @ X33))
% 0.83/1.05          | (r1_tmap_1 @ X31 @ X30 @ X36 @ X35)
% 0.83/1.05          | ~ (r1_tmap_1 @ X33 @ X30 @ 
% 0.83/1.05               (k3_tmap_1 @ X32 @ X30 @ X31 @ X33 @ X36) @ X35)
% 0.83/1.05          | ~ (m1_subset_1 @ X35 @ (u1_struct_0 @ X33))
% 0.83/1.05          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (u1_struct_0 @ X31)))
% 0.83/1.05          | ~ (m1_pre_topc @ X33 @ X31)
% 0.83/1.05          | ~ (m1_pre_topc @ X31 @ X32)
% 0.83/1.05          | (v2_struct_0 @ X31)
% 0.83/1.05          | ~ (l1_pre_topc @ X30)
% 0.83/1.05          | ~ (v2_pre_topc @ X30)
% 0.83/1.05          | (v2_struct_0 @ X30))),
% 0.83/1.05      inference('simplify', [status(thm)], ['80'])).
% 0.83/1.05  thf('82', plain,
% 0.83/1.05      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.83/1.05         (~ (m1_subset_1 @ X1 @ 
% 0.83/1.05             (k1_zfmisc_1 @ 
% 0.83/1.05              (k2_zfmisc_1 @ (k2_struct_0 @ sk_D) @ (u1_struct_0 @ X0))))
% 0.83/1.05          | (v2_struct_0 @ X0)
% 0.83/1.05          | ~ (v2_pre_topc @ X0)
% 0.83/1.05          | ~ (l1_pre_topc @ X0)
% 0.83/1.05          | (v2_struct_0 @ sk_D)
% 0.83/1.05          | ~ (m1_pre_topc @ sk_D @ X2)
% 0.83/1.05          | ~ (m1_pre_topc @ X3 @ sk_D)
% 0.83/1.05          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))
% 0.83/1.05          | ~ (m1_subset_1 @ X5 @ (u1_struct_0 @ X3))
% 0.83/1.05          | ~ (r1_tmap_1 @ X3 @ X0 @ (k3_tmap_1 @ X2 @ X0 @ sk_D @ X3 @ X1) @ 
% 0.83/1.05               X5)
% 0.83/1.05          | (r1_tmap_1 @ sk_D @ X0 @ X1 @ X5)
% 0.83/1.05          | ~ (r1_tarski @ X4 @ (u1_struct_0 @ X3))
% 0.83/1.05          | ~ (r2_hidden @ X5 @ X4)
% 0.83/1.05          | ~ (v3_pre_topc @ X4 @ sk_D)
% 0.83/1.05          | ~ (m1_subset_1 @ X5 @ (u1_struct_0 @ sk_D))
% 0.83/1.05          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ X0))
% 0.83/1.05          | ~ (v1_funct_1 @ X1)
% 0.83/1.05          | ~ (m1_pre_topc @ X3 @ X2)
% 0.83/1.05          | (v2_struct_0 @ X3)
% 0.83/1.05          | ~ (l1_pre_topc @ X2)
% 0.83/1.05          | ~ (v2_pre_topc @ X2)
% 0.83/1.05          | (v2_struct_0 @ X2))),
% 0.83/1.05      inference('sup-', [status(thm)], ['79', '81'])).
% 0.83/1.05  thf('83', plain, (((k2_struct_0 @ sk_D) = (u1_struct_0 @ sk_D))),
% 0.83/1.05      inference('demod', [status(thm)], ['77', '78'])).
% 0.83/1.05  thf('84', plain, (((k2_struct_0 @ sk_D) = (u1_struct_0 @ sk_D))),
% 0.83/1.05      inference('demod', [status(thm)], ['77', '78'])).
% 0.83/1.05  thf('85', plain, (((k2_struct_0 @ sk_D) = (u1_struct_0 @ sk_D))),
% 0.83/1.05      inference('demod', [status(thm)], ['77', '78'])).
% 0.83/1.05  thf('86', plain,
% 0.83/1.05      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.83/1.05         (~ (m1_subset_1 @ X1 @ 
% 0.83/1.05             (k1_zfmisc_1 @ 
% 0.83/1.05              (k2_zfmisc_1 @ (k2_struct_0 @ sk_D) @ (u1_struct_0 @ X0))))
% 0.83/1.05          | (v2_struct_0 @ X0)
% 0.83/1.05          | ~ (v2_pre_topc @ X0)
% 0.83/1.05          | ~ (l1_pre_topc @ X0)
% 0.83/1.05          | (v2_struct_0 @ sk_D)
% 0.83/1.05          | ~ (m1_pre_topc @ sk_D @ X2)
% 0.83/1.05          | ~ (m1_pre_topc @ X3 @ sk_D)
% 0.83/1.05          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_D)))
% 0.83/1.05          | ~ (m1_subset_1 @ X5 @ (u1_struct_0 @ X3))
% 0.83/1.05          | ~ (r1_tmap_1 @ X3 @ X0 @ (k3_tmap_1 @ X2 @ X0 @ sk_D @ X3 @ X1) @ 
% 0.83/1.05               X5)
% 0.83/1.05          | (r1_tmap_1 @ sk_D @ X0 @ X1 @ X5)
% 0.83/1.05          | ~ (r1_tarski @ X4 @ (u1_struct_0 @ X3))
% 0.83/1.05          | ~ (r2_hidden @ X5 @ X4)
% 0.83/1.05          | ~ (v3_pre_topc @ X4 @ sk_D)
% 0.83/1.05          | ~ (m1_subset_1 @ X5 @ (k2_struct_0 @ sk_D))
% 0.83/1.05          | ~ (v1_funct_2 @ X1 @ (k2_struct_0 @ sk_D) @ (u1_struct_0 @ X0))
% 0.83/1.05          | ~ (v1_funct_1 @ X1)
% 0.83/1.05          | ~ (m1_pre_topc @ X3 @ X2)
% 0.83/1.05          | (v2_struct_0 @ X3)
% 0.83/1.05          | ~ (l1_pre_topc @ X2)
% 0.83/1.05          | ~ (v2_pre_topc @ X2)
% 0.83/1.05          | (v2_struct_0 @ X2))),
% 0.83/1.05      inference('demod', [status(thm)], ['82', '83', '84', '85'])).
% 0.83/1.05  thf('87', plain, (((k2_struct_0 @ sk_C) = (k2_struct_0 @ sk_D))),
% 0.83/1.05      inference('demod', [status(thm)], ['70', '73'])).
% 0.83/1.05  thf('88', plain, (((k2_struct_0 @ sk_C) = (k2_struct_0 @ sk_D))),
% 0.83/1.05      inference('demod', [status(thm)], ['70', '73'])).
% 0.83/1.05  thf('89', plain, (((k2_struct_0 @ sk_C) = (k2_struct_0 @ sk_D))),
% 0.83/1.05      inference('demod', [status(thm)], ['70', '73'])).
% 0.83/1.05  thf('90', plain, (((k2_struct_0 @ sk_C) = (k2_struct_0 @ sk_D))),
% 0.83/1.05      inference('demod', [status(thm)], ['70', '73'])).
% 0.83/1.05  thf('91', plain,
% 0.83/1.05      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.83/1.05         (~ (m1_subset_1 @ X1 @ 
% 0.83/1.05             (k1_zfmisc_1 @ 
% 0.83/1.05              (k2_zfmisc_1 @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ X0))))
% 0.83/1.05          | (v2_struct_0 @ X0)
% 0.83/1.05          | ~ (v2_pre_topc @ X0)
% 0.83/1.05          | ~ (l1_pre_topc @ X0)
% 0.83/1.05          | (v2_struct_0 @ sk_D)
% 0.83/1.05          | ~ (m1_pre_topc @ sk_D @ X2)
% 0.83/1.05          | ~ (m1_pre_topc @ X3 @ sk_D)
% 0.83/1.05          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_C)))
% 0.83/1.05          | ~ (m1_subset_1 @ X5 @ (u1_struct_0 @ X3))
% 0.83/1.05          | ~ (r1_tmap_1 @ X3 @ X0 @ (k3_tmap_1 @ X2 @ X0 @ sk_D @ X3 @ X1) @ 
% 0.83/1.05               X5)
% 0.83/1.05          | (r1_tmap_1 @ sk_D @ X0 @ X1 @ X5)
% 0.83/1.05          | ~ (r1_tarski @ X4 @ (u1_struct_0 @ X3))
% 0.83/1.05          | ~ (r2_hidden @ X5 @ X4)
% 0.83/1.05          | ~ (v3_pre_topc @ X4 @ sk_D)
% 0.83/1.05          | ~ (m1_subset_1 @ X5 @ (k2_struct_0 @ sk_C))
% 0.83/1.05          | ~ (v1_funct_2 @ X1 @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ X0))
% 0.83/1.05          | ~ (v1_funct_1 @ X1)
% 0.83/1.05          | ~ (m1_pre_topc @ X3 @ X2)
% 0.83/1.05          | (v2_struct_0 @ X3)
% 0.83/1.05          | ~ (l1_pre_topc @ X2)
% 0.83/1.05          | ~ (v2_pre_topc @ X2)
% 0.83/1.05          | (v2_struct_0 @ X2))),
% 0.83/1.05      inference('demod', [status(thm)], ['86', '87', '88', '89', '90'])).
% 0.83/1.05  thf('92', plain,
% 0.83/1.05      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.83/1.05         ((v2_struct_0 @ X0)
% 0.83/1.05          | ~ (v2_pre_topc @ X0)
% 0.83/1.05          | ~ (l1_pre_topc @ X0)
% 0.83/1.05          | (v2_struct_0 @ X1)
% 0.83/1.05          | ~ (m1_pre_topc @ X1 @ X0)
% 0.83/1.05          | ~ (v1_funct_1 @ sk_E)
% 0.83/1.05          | ~ (v1_funct_2 @ sk_E @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))
% 0.83/1.05          | ~ (m1_subset_1 @ X2 @ (k2_struct_0 @ sk_C))
% 0.83/1.05          | ~ (v3_pre_topc @ X3 @ sk_D)
% 0.83/1.05          | ~ (r2_hidden @ X2 @ X3)
% 0.83/1.05          | ~ (r1_tarski @ X3 @ (u1_struct_0 @ X1))
% 0.83/1.05          | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X2)
% 0.83/1.05          | ~ (r1_tmap_1 @ X1 @ sk_B @ 
% 0.83/1.05               (k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E) @ X2)
% 0.83/1.05          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1))
% 0.83/1.05          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_C)))
% 0.83/1.05          | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.83/1.05          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.83/1.05          | (v2_struct_0 @ sk_D)
% 0.83/1.05          | ~ (l1_pre_topc @ sk_B)
% 0.83/1.05          | ~ (v2_pre_topc @ sk_B)
% 0.83/1.05          | (v2_struct_0 @ sk_B))),
% 0.83/1.05      inference('sup-', [status(thm)], ['76', '91'])).
% 0.83/1.05  thf('93', plain, ((v1_funct_1 @ sk_E)),
% 0.83/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.05  thf('94', plain,
% 0.83/1.05      (![X13 : $i]:
% 0.83/1.05         (((k2_struct_0 @ X13) = (u1_struct_0 @ X13)) | ~ (l1_struct_0 @ X13))),
% 0.83/1.05      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.83/1.05  thf('95', plain,
% 0.83/1.05      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 0.83/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.05  thf('96', plain,
% 0.83/1.05      (((v1_funct_2 @ sk_E @ (k2_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.83/1.05        | ~ (l1_struct_0 @ sk_D))),
% 0.83/1.05      inference('sup+', [status(thm)], ['94', '95'])).
% 0.83/1.05  thf('97', plain, ((l1_struct_0 @ sk_D)),
% 0.83/1.05      inference('sup-', [status(thm)], ['64', '65'])).
% 0.83/1.05  thf('98', plain,
% 0.83/1.05      ((v1_funct_2 @ sk_E @ (k2_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 0.83/1.05      inference('demod', [status(thm)], ['96', '97'])).
% 0.83/1.05  thf('99', plain, (((k2_struct_0 @ sk_C) = (k2_struct_0 @ sk_D))),
% 0.83/1.05      inference('demod', [status(thm)], ['70', '73'])).
% 0.83/1.05  thf('100', plain,
% 0.83/1.05      ((v1_funct_2 @ sk_E @ (k2_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 0.83/1.05      inference('demod', [status(thm)], ['98', '99'])).
% 0.83/1.05  thf('101', plain, ((l1_pre_topc @ sk_B)),
% 0.83/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.05  thf('102', plain, ((v2_pre_topc @ sk_B)),
% 0.83/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.05  thf('103', plain,
% 0.83/1.05      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.83/1.05         ((v2_struct_0 @ X0)
% 0.83/1.05          | ~ (v2_pre_topc @ X0)
% 0.83/1.05          | ~ (l1_pre_topc @ X0)
% 0.83/1.05          | (v2_struct_0 @ X1)
% 0.83/1.05          | ~ (m1_pre_topc @ X1 @ X0)
% 0.83/1.05          | ~ (m1_subset_1 @ X2 @ (k2_struct_0 @ sk_C))
% 0.83/1.05          | ~ (v3_pre_topc @ X3 @ sk_D)
% 0.83/1.05          | ~ (r2_hidden @ X2 @ X3)
% 0.83/1.05          | ~ (r1_tarski @ X3 @ (u1_struct_0 @ X1))
% 0.83/1.05          | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X2)
% 0.83/1.05          | ~ (r1_tmap_1 @ X1 @ sk_B @ 
% 0.83/1.05               (k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E) @ X2)
% 0.83/1.05          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1))
% 0.83/1.05          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_C)))
% 0.83/1.05          | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.83/1.05          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.83/1.05          | (v2_struct_0 @ sk_D)
% 0.83/1.05          | (v2_struct_0 @ sk_B))),
% 0.83/1.05      inference('demod', [status(thm)], ['92', '93', '100', '101', '102'])).
% 0.83/1.05  thf('104', plain,
% 0.83/1.05      (![X0 : $i]:
% 0.83/1.05         ((v2_struct_0 @ sk_B)
% 0.83/1.05          | (v2_struct_0 @ sk_D)
% 0.83/1.05          | ~ (m1_pre_topc @ sk_D @ sk_A)
% 0.83/1.05          | ~ (m1_pre_topc @ sk_C @ sk_D)
% 0.83/1.05          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_C)))
% 0.83/1.05          | ~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C))
% 0.83/1.05          | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)
% 0.83/1.05          | ~ (r1_tarski @ X0 @ (u1_struct_0 @ sk_C))
% 0.83/1.05          | ~ (r2_hidden @ sk_F @ X0)
% 0.83/1.05          | ~ (v3_pre_topc @ X0 @ sk_D)
% 0.83/1.05          | ~ (m1_subset_1 @ sk_F @ (k2_struct_0 @ sk_C))
% 0.83/1.05          | ~ (m1_pre_topc @ sk_C @ sk_A)
% 0.83/1.05          | (v2_struct_0 @ sk_C)
% 0.83/1.05          | ~ (l1_pre_topc @ sk_A)
% 0.83/1.05          | ~ (v2_pre_topc @ sk_A)
% 0.83/1.05          | (v2_struct_0 @ sk_A))),
% 0.83/1.05      inference('sup-', [status(thm)], ['7', '103'])).
% 0.83/1.05  thf('105', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.83/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.05  thf('106', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 0.83/1.05      inference('demod', [status(thm)], ['43', '44'])).
% 0.83/1.05  thf('107', plain, (((u1_struct_0 @ sk_C) = (k2_struct_0 @ sk_C))),
% 0.83/1.05      inference('demod', [status(thm)], ['67', '74'])).
% 0.83/1.05  thf('108', plain,
% 0.83/1.05      (![X13 : $i]:
% 0.83/1.05         (((k2_struct_0 @ X13) = (u1_struct_0 @ X13)) | ~ (l1_struct_0 @ X13))),
% 0.83/1.05      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.83/1.05  thf('109', plain, ((m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_C))),
% 0.83/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.05  thf('110', plain, (((sk_F) = (sk_G))),
% 0.83/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.05  thf('111', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C))),
% 0.83/1.05      inference('demod', [status(thm)], ['109', '110'])).
% 0.83/1.05  thf('112', plain,
% 0.83/1.05      (((m1_subset_1 @ sk_F @ (k2_struct_0 @ sk_C)) | ~ (l1_struct_0 @ sk_C))),
% 0.83/1.05      inference('sup+', [status(thm)], ['108', '111'])).
% 0.83/1.05  thf('113', plain, ((l1_struct_0 @ sk_C)),
% 0.83/1.05      inference('sup-', [status(thm)], ['71', '72'])).
% 0.83/1.05  thf('114', plain, ((m1_subset_1 @ sk_F @ (k2_struct_0 @ sk_C))),
% 0.83/1.05      inference('demod', [status(thm)], ['112', '113'])).
% 0.83/1.05  thf('115', plain, (((u1_struct_0 @ sk_C) = (k2_struct_0 @ sk_C))),
% 0.83/1.05      inference('demod', [status(thm)], ['67', '74'])).
% 0.83/1.05  thf('116', plain, ((m1_subset_1 @ sk_F @ (k2_struct_0 @ sk_C))),
% 0.83/1.05      inference('demod', [status(thm)], ['112', '113'])).
% 0.83/1.05  thf('117', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.83/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.05  thf('118', plain, ((l1_pre_topc @ sk_A)),
% 0.83/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.05  thf('119', plain, ((v2_pre_topc @ sk_A)),
% 0.83/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.05  thf('120', plain,
% 0.83/1.05      (![X0 : $i]:
% 0.83/1.05         ((v2_struct_0 @ sk_B)
% 0.83/1.05          | (v2_struct_0 @ sk_D)
% 0.83/1.05          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_C)))
% 0.83/1.05          | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)
% 0.83/1.05          | ~ (r1_tarski @ X0 @ (k2_struct_0 @ sk_C))
% 0.83/1.05          | ~ (r2_hidden @ sk_F @ X0)
% 0.83/1.05          | ~ (v3_pre_topc @ X0 @ sk_D)
% 0.83/1.05          | (v2_struct_0 @ sk_C)
% 0.83/1.05          | (v2_struct_0 @ sk_A))),
% 0.83/1.05      inference('demod', [status(thm)],
% 0.83/1.05                ['104', '105', '106', '107', '114', '115', '116', '117', 
% 0.83/1.05                 '118', '119'])).
% 0.83/1.05  thf('121', plain,
% 0.83/1.05      (((v2_struct_0 @ sk_A)
% 0.83/1.05        | (v2_struct_0 @ sk_C)
% 0.83/1.05        | ~ (v3_pre_topc @ (k2_struct_0 @ sk_C) @ sk_D)
% 0.83/1.05        | ~ (r2_hidden @ sk_F @ (k2_struct_0 @ sk_C))
% 0.83/1.05        | ~ (r1_tarski @ (k2_struct_0 @ sk_C) @ (k2_struct_0 @ sk_C))
% 0.83/1.05        | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)
% 0.83/1.05        | (v2_struct_0 @ sk_D)
% 0.83/1.05        | (v2_struct_0 @ sk_B))),
% 0.83/1.05      inference('sup-', [status(thm)], ['4', '120'])).
% 0.83/1.05  thf('122', plain, (((k2_struct_0 @ sk_C) = (k2_struct_0 @ sk_D))),
% 0.83/1.05      inference('demod', [status(thm)], ['70', '73'])).
% 0.83/1.05  thf(fc10_tops_1, axiom,
% 0.83/1.05    (![A:$i]:
% 0.83/1.05     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.83/1.05       ( v3_pre_topc @ ( k2_struct_0 @ A ) @ A ) ))).
% 0.83/1.05  thf('123', plain,
% 0.83/1.05      (![X22 : $i]:
% 0.83/1.05         ((v3_pre_topc @ (k2_struct_0 @ X22) @ X22)
% 0.83/1.05          | ~ (l1_pre_topc @ X22)
% 0.83/1.05          | ~ (v2_pre_topc @ X22))),
% 0.83/1.05      inference('cnf', [status(esa)], [fc10_tops_1])).
% 0.83/1.05  thf('124', plain,
% 0.83/1.05      (((v3_pre_topc @ (k2_struct_0 @ sk_C) @ sk_D)
% 0.83/1.05        | ~ (v2_pre_topc @ sk_D)
% 0.83/1.05        | ~ (l1_pre_topc @ sk_D))),
% 0.83/1.05      inference('sup+', [status(thm)], ['122', '123'])).
% 0.83/1.05  thf('125', plain, ((v2_pre_topc @ sk_D)),
% 0.83/1.05      inference('demod', [status(thm)], ['34', '35', '36'])).
% 0.83/1.05  thf('126', plain, ((l1_pre_topc @ sk_D)),
% 0.83/1.05      inference('demod', [status(thm)], ['16', '17'])).
% 0.83/1.05  thf('127', plain, ((v3_pre_topc @ (k2_struct_0 @ sk_C) @ sk_D)),
% 0.83/1.05      inference('demod', [status(thm)], ['124', '125', '126'])).
% 0.83/1.05  thf('128', plain,
% 0.83/1.05      (![X13 : $i]:
% 0.83/1.05         (((k2_struct_0 @ X13) = (u1_struct_0 @ X13)) | ~ (l1_struct_0 @ X13))),
% 0.83/1.05      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.83/1.05  thf('129', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C))),
% 0.83/1.05      inference('demod', [status(thm)], ['109', '110'])).
% 0.83/1.05  thf(t2_subset, axiom,
% 0.83/1.05    (![A:$i,B:$i]:
% 0.83/1.05     ( ( m1_subset_1 @ A @ B ) =>
% 0.83/1.05       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.83/1.05  thf('130', plain,
% 0.83/1.05      (![X3 : $i, X4 : $i]:
% 0.83/1.05         ((r2_hidden @ X3 @ X4)
% 0.83/1.05          | (v1_xboole_0 @ X4)
% 0.83/1.05          | ~ (m1_subset_1 @ X3 @ X4))),
% 0.83/1.05      inference('cnf', [status(esa)], [t2_subset])).
% 0.83/1.05  thf('131', plain,
% 0.83/1.05      (((v1_xboole_0 @ (u1_struct_0 @ sk_C))
% 0.83/1.05        | (r2_hidden @ sk_F @ (u1_struct_0 @ sk_C)))),
% 0.83/1.05      inference('sup-', [status(thm)], ['129', '130'])).
% 0.83/1.05  thf('132', plain,
% 0.83/1.05      (((r2_hidden @ sk_F @ (k2_struct_0 @ sk_C))
% 0.83/1.05        | ~ (l1_struct_0 @ sk_C)
% 0.83/1.05        | (v1_xboole_0 @ (u1_struct_0 @ sk_C)))),
% 0.83/1.05      inference('sup+', [status(thm)], ['128', '131'])).
% 0.83/1.05  thf('133', plain, ((l1_struct_0 @ sk_C)),
% 0.83/1.05      inference('sup-', [status(thm)], ['71', '72'])).
% 0.83/1.05  thf('134', plain,
% 0.83/1.05      (((r2_hidden @ sk_F @ (k2_struct_0 @ sk_C))
% 0.83/1.05        | (v1_xboole_0 @ (u1_struct_0 @ sk_C)))),
% 0.83/1.05      inference('demod', [status(thm)], ['132', '133'])).
% 0.83/1.05  thf(fc2_struct_0, axiom,
% 0.83/1.05    (![A:$i]:
% 0.83/1.05     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.83/1.05       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.83/1.05  thf('135', plain,
% 0.83/1.05      (![X17 : $i]:
% 0.83/1.05         (~ (v1_xboole_0 @ (u1_struct_0 @ X17))
% 0.83/1.05          | ~ (l1_struct_0 @ X17)
% 0.83/1.05          | (v2_struct_0 @ X17))),
% 0.83/1.05      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.83/1.05  thf('136', plain,
% 0.83/1.05      (((r2_hidden @ sk_F @ (k2_struct_0 @ sk_C))
% 0.83/1.05        | (v2_struct_0 @ sk_C)
% 0.83/1.05        | ~ (l1_struct_0 @ sk_C))),
% 0.83/1.05      inference('sup-', [status(thm)], ['134', '135'])).
% 0.83/1.05  thf('137', plain, ((l1_struct_0 @ sk_C)),
% 0.83/1.05      inference('sup-', [status(thm)], ['71', '72'])).
% 0.83/1.05  thf('138', plain,
% 0.83/1.05      (((r2_hidden @ sk_F @ (k2_struct_0 @ sk_C)) | (v2_struct_0 @ sk_C))),
% 0.83/1.05      inference('demod', [status(thm)], ['136', '137'])).
% 0.83/1.05  thf('139', plain, (~ (v2_struct_0 @ sk_C)),
% 0.83/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.05  thf('140', plain, ((r2_hidden @ sk_F @ (k2_struct_0 @ sk_C))),
% 0.83/1.05      inference('clc', [status(thm)], ['138', '139'])).
% 0.83/1.05  thf('141', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.83/1.05      inference('simplify', [status(thm)], ['1'])).
% 0.83/1.05  thf('142', plain,
% 0.83/1.05      (((v2_struct_0 @ sk_A)
% 0.83/1.05        | (v2_struct_0 @ sk_C)
% 0.83/1.05        | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)
% 0.83/1.05        | (v2_struct_0 @ sk_D)
% 0.83/1.05        | (v2_struct_0 @ sk_B))),
% 0.83/1.05      inference('demod', [status(thm)], ['121', '127', '140', '141'])).
% 0.83/1.05  thf('143', plain, (~ (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)),
% 0.83/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.05  thf('144', plain,
% 0.83/1.05      (((v2_struct_0 @ sk_B)
% 0.83/1.05        | (v2_struct_0 @ sk_D)
% 0.83/1.05        | (v2_struct_0 @ sk_C)
% 0.83/1.05        | (v2_struct_0 @ sk_A))),
% 0.83/1.05      inference('sup-', [status(thm)], ['142', '143'])).
% 0.83/1.05  thf('145', plain, (~ (v2_struct_0 @ sk_D)),
% 0.83/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.05  thf('146', plain,
% 0.83/1.05      (((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_B))),
% 0.83/1.05      inference('sup-', [status(thm)], ['144', '145'])).
% 0.83/1.05  thf('147', plain, (~ (v2_struct_0 @ sk_A)),
% 0.83/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.05  thf('148', plain, (((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_C))),
% 0.83/1.05      inference('clc', [status(thm)], ['146', '147'])).
% 0.83/1.05  thf('149', plain, (~ (v2_struct_0 @ sk_B)),
% 0.83/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.05  thf('150', plain, ((v2_struct_0 @ sk_C)),
% 0.83/1.05      inference('clc', [status(thm)], ['148', '149'])).
% 0.83/1.05  thf('151', plain, ($false), inference('demod', [status(thm)], ['0', '150'])).
% 0.83/1.05  
% 0.83/1.05  % SZS output end Refutation
% 0.83/1.05  
% 0.83/1.06  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
