%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.DoCHOD4vEc

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:10:30 EST 2020

% Result     : Theorem 1.94s
% Output     : Refutation 1.94s
% Verified   : 
% Statistics : Number of formulae       :  206 (1427 expanded)
%              Number of leaves         :   59 ( 447 expanded)
%              Depth                    :   23
%              Number of atoms          : 1791 (38993 expanded)
%              Number of equality atoms :   25 ( 982 expanded)
%              Maximal formula depth    :   29 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(zip_tseitin_4_type,type,(
    zip_tseitin_4: $i > $i > $o )).

thf(zip_tseitin_5_type,type,(
    zip_tseitin_5: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $o )).

thf(zip_tseitin_3_type,type,(
    zip_tseitin_3: $i > $i > $o )).

thf(sk_G_type,type,(
    sk_G: $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(r1_tmap_1_type,type,(
    r1_tmap_1: $i > $i > $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(v1_tsep_1_type,type,(
    v1_tsep_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(zip_tseitin_2_type,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(g1_pre_topc_type,type,(
    g1_pre_topc: $i > $i > $i )).

thf(k3_tmap_1_type,type,(
    k3_tmap_1: $i > $i > $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k5_setfam_1_type,type,(
    k5_setfam_1: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

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
    ~ ( v2_struct_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r1_tmap_1 @ sk_C_1 @ sk_B_2 @ ( k3_tmap_1 @ sk_A @ sk_B_2 @ sk_D @ sk_C_1 @ sk_E ) @ sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    sk_F = sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,(
    r1_tmap_1 @ sk_C_1 @ sk_B_2 @ ( k3_tmap_1 @ sk_A @ sk_B_2 @ sk_D @ sk_C_1 @ sk_E ) @ sk_F ),
    inference(demod,[status(thm)],['1','2'])).

thf('4',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B_2 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_pre_topc @ sk_C_1 ) )
    = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( m1_pre_topc @ A @ A ) ) )).

thf('6',plain,(
    ! [X43: $i] :
      ( ( m1_pre_topc @ X43 @ X43 )
      | ~ ( l1_pre_topc @ X43 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf(t59_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) )
         => ( m1_pre_topc @ B @ A ) ) ) )).

thf('7',plain,(
    ! [X34: $i,X35: $i] :
      ( ~ ( m1_pre_topc @ X34 @ ( g1_pre_topc @ ( u1_struct_0 @ X35 ) @ ( u1_pre_topc @ X35 ) ) )
      | ( m1_pre_topc @ X34 @ X35 )
      | ~ ( l1_pre_topc @ X35 ) ) ),
    inference(cnf,[status(esa)],[t59_pre_topc])).

thf('8',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,
    ( ~ ( l1_pre_topc @ sk_D )
    | ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_pre_topc @ sk_C_1 ) ) @ sk_C_1 )
    | ~ ( l1_pre_topc @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['5','8'])).

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
    ! [X32: $i,X33: $i] :
      ( ~ ( m1_pre_topc @ X32 @ X33 )
      | ( l1_pre_topc @ X32 )
      | ~ ( l1_pre_topc @ X33 ) ) ),
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
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_pre_topc @ sk_C_1 ) )
    = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    m1_pre_topc @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    ! [X32: $i,X33: $i] :
      ( ~ ( m1_pre_topc @ X32 @ X33 )
      | ( l1_pre_topc @ X32 )
      | ~ ( l1_pre_topc @ X33 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('18',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,(
    m1_pre_topc @ sk_D @ sk_C_1 ),
    inference(demod,[status(thm)],['9','14','15','20'])).

thf('22',plain,(
    ! [X43: $i] :
      ( ( m1_pre_topc @ X43 @ X43 )
      | ~ ( l1_pre_topc @ X43 ) ) ),
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

thf('23',plain,(
    ! [X44: $i,X45: $i,X46: $i] :
      ( ~ ( m1_pre_topc @ X44 @ X45 )
      | ~ ( m1_pre_topc @ X44 @ X46 )
      | ( r1_tarski @ ( u1_struct_0 @ X44 ) @ ( u1_struct_0 @ X46 ) )
      | ~ ( m1_pre_topc @ X46 @ X45 )
      | ~ ( l1_pre_topc @ X45 )
      | ~ ( v2_pre_topc @ X45 ) ) ),
    inference(cnf,[status(esa)],[t4_tsep_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ( r1_tarski @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X1 ) )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_pre_topc @ X0 @ X1 )
      | ( r1_tarski @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X1 ) )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,
    ( ~ ( l1_pre_topc @ sk_D )
    | ~ ( v2_pre_topc @ sk_D )
    | ~ ( m1_pre_topc @ sk_C_1 @ sk_D )
    | ( r1_tarski @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['21','25'])).

thf('27',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['12','13'])).

thf('28',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( v2_pre_topc @ B ) ) ) )).

thf('29',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_pre_topc @ X3 @ X4 )
      | ( v2_pre_topc @ X3 )
      | ~ ( l1_pre_topc @ X4 )
      | ~ ( v2_pre_topc @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc1_pre_topc])).

thf('30',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_pre_topc @ sk_D ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    v2_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['30','31','32'])).

thf('34',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_pre_topc @ sk_C_1 ) )
    = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    ! [X43: $i] :
      ( ( m1_pre_topc @ X43 @ X43 )
      | ~ ( l1_pre_topc @ X43 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf(t65_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( l1_pre_topc @ B )
         => ( ( m1_pre_topc @ A @ B )
          <=> ( m1_pre_topc @ A @ ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ) )).

thf('36',plain,(
    ! [X36: $i,X37: $i] :
      ( ~ ( l1_pre_topc @ X36 )
      | ~ ( m1_pre_topc @ X37 @ X36 )
      | ( m1_pre_topc @ X37 @ ( g1_pre_topc @ ( u1_struct_0 @ X36 ) @ ( u1_pre_topc @ X36 ) ) )
      | ~ ( l1_pre_topc @ X37 ) ) ),
    inference(cnf,[status(esa)],[t65_pre_topc])).

thf('37',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,
    ( ( m1_pre_topc @ sk_C_1 @ sk_D )
    | ~ ( l1_pre_topc @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['34','38'])).

thf('40',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['18','19'])).

thf('41',plain,(
    m1_pre_topc @ sk_C_1 @ sk_D ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['26','27','33','41'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('43',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('44',plain,
    ( ~ ( r1_tarski @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_D ) )
    | ( ( u1_struct_0 @ sk_C_1 )
      = ( u1_struct_0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    m1_pre_topc @ sk_C_1 @ sk_D ),
    inference(demod,[status(thm)],['39','40'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_pre_topc @ X0 @ X1 )
      | ( r1_tarski @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X1 ) )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('47',plain,
    ( ~ ( l1_pre_topc @ sk_C_1 )
    | ~ ( v2_pre_topc @ sk_C_1 )
    | ~ ( m1_pre_topc @ sk_D @ sk_C_1 )
    | ( r1_tarski @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['18','19'])).

thf('49',plain,(
    m1_pre_topc @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_pre_topc @ X3 @ X4 )
      | ( v2_pre_topc @ X3 )
      | ~ ( l1_pre_topc @ X4 )
      | ~ ( v2_pre_topc @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc1_pre_topc])).

thf('51',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_pre_topc @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    v2_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['51','52','53'])).

thf('55',plain,(
    m1_pre_topc @ sk_D @ sk_C_1 ),
    inference(demod,[status(thm)],['9','14','15','20'])).

thf('56',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['47','48','54','55'])).

thf('57',plain,
    ( ( u1_struct_0 @ sk_C_1 )
    = ( u1_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['44','56'])).

thf('58',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_2 ) ) ) ),
    inference(demod,[status(thm)],['4','57'])).

thf('59',plain,
    ( ( u1_struct_0 @ sk_C_1 )
    = ( u1_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['44','56'])).

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

thf('60',plain,(
    ! [X50: $i,X51: $i,X52: $i,X53: $i,X54: $i,X55: $i,X56: $i] :
      ( ( v2_struct_0 @ X50 )
      | ~ ( v2_pre_topc @ X50 )
      | ~ ( l1_pre_topc @ X50 )
      | ( v2_struct_0 @ X51 )
      | ~ ( m1_pre_topc @ X51 @ X52 )
      | ~ ( v1_tsep_1 @ X53 @ X51 )
      | ~ ( m1_pre_topc @ X53 @ X51 )
      | ~ ( m1_subset_1 @ X54 @ ( u1_struct_0 @ X51 ) )
      | ( X54 != X55 )
      | ~ ( r1_tmap_1 @ X53 @ X50 @ ( k3_tmap_1 @ X52 @ X50 @ X51 @ X53 @ X56 ) @ X55 )
      | ( r1_tmap_1 @ X51 @ X50 @ X56 @ X54 )
      | ~ ( m1_subset_1 @ X55 @ ( u1_struct_0 @ X53 ) )
      | ~ ( m1_subset_1 @ X56 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X51 ) @ ( u1_struct_0 @ X50 ) ) ) )
      | ~ ( v1_funct_2 @ X56 @ ( u1_struct_0 @ X51 ) @ ( u1_struct_0 @ X50 ) )
      | ~ ( v1_funct_1 @ X56 )
      | ~ ( m1_pre_topc @ X53 @ X52 )
      | ( v2_struct_0 @ X53 )
      | ~ ( l1_pre_topc @ X52 )
      | ~ ( v2_pre_topc @ X52 )
      | ( v2_struct_0 @ X52 ) ) ),
    inference(cnf,[status(esa)],[t86_tmap_1])).

thf('61',plain,(
    ! [X50: $i,X51: $i,X52: $i,X53: $i,X55: $i,X56: $i] :
      ( ( v2_struct_0 @ X52 )
      | ~ ( v2_pre_topc @ X52 )
      | ~ ( l1_pre_topc @ X52 )
      | ( v2_struct_0 @ X53 )
      | ~ ( m1_pre_topc @ X53 @ X52 )
      | ~ ( v1_funct_1 @ X56 )
      | ~ ( v1_funct_2 @ X56 @ ( u1_struct_0 @ X51 ) @ ( u1_struct_0 @ X50 ) )
      | ~ ( m1_subset_1 @ X56 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X51 ) @ ( u1_struct_0 @ X50 ) ) ) )
      | ~ ( m1_subset_1 @ X55 @ ( u1_struct_0 @ X53 ) )
      | ( r1_tmap_1 @ X51 @ X50 @ X56 @ X55 )
      | ~ ( r1_tmap_1 @ X53 @ X50 @ ( k3_tmap_1 @ X52 @ X50 @ X51 @ X53 @ X56 ) @ X55 )
      | ~ ( m1_subset_1 @ X55 @ ( u1_struct_0 @ X51 ) )
      | ~ ( m1_pre_topc @ X53 @ X51 )
      | ~ ( v1_tsep_1 @ X53 @ X51 )
      | ~ ( m1_pre_topc @ X51 @ X52 )
      | ( v2_struct_0 @ X51 )
      | ~ ( l1_pre_topc @ X50 )
      | ~ ( v2_pre_topc @ X50 )
      | ( v2_struct_0 @ X50 ) ) ),
    inference(simplify,[status(thm)],['60'])).

thf('62',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ X0 ) ) ) )
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
    inference('sup-',[status(thm)],['59','61'])).

thf('63',plain,
    ( ( u1_struct_0 @ sk_C_1 )
    = ( u1_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['44','56'])).

thf('64',plain,
    ( ( u1_struct_0 @ sk_C_1 )
    = ( u1_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['44','56'])).

thf('65',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ sk_D )
      | ~ ( m1_pre_topc @ sk_D @ X2 )
      | ~ ( v1_tsep_1 @ X3 @ sk_D )
      | ~ ( m1_pre_topc @ X3 @ sk_D )
      | ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ sk_C_1 ) )
      | ~ ( r1_tmap_1 @ X3 @ X0 @ ( k3_tmap_1 @ X2 @ X0 @ sk_D @ X3 @ X1 ) @ X4 )
      | ( r1_tmap_1 @ sk_D @ X0 @ X1 @ X4 )
      | ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ X3 ) )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( m1_pre_topc @ X3 @ X2 )
      | ( v2_struct_0 @ X3 )
      | ~ ( l1_pre_topc @ X2 )
      | ~ ( v2_pre_topc @ X2 )
      | ( v2_struct_0 @ X2 ) ) ),
    inference(demod,[status(thm)],['62','63','64'])).

thf('66',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X1 )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_2 ) )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X1 ) )
      | ( r1_tmap_1 @ sk_D @ sk_B_2 @ sk_E @ X2 )
      | ~ ( r1_tmap_1 @ X1 @ sk_B_2 @ ( k3_tmap_1 @ X0 @ sk_B_2 @ sk_D @ X1 @ sk_E ) @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ sk_C_1 ) )
      | ~ ( m1_pre_topc @ X1 @ sk_D )
      | ~ ( v1_tsep_1 @ X1 @ sk_D )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ( v2_struct_0 @ sk_D )
      | ~ ( l1_pre_topc @ sk_B_2 )
      | ~ ( v2_pre_topc @ sk_B_2 )
      | ( v2_struct_0 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['58','65'])).

thf('67',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,
    ( ( u1_struct_0 @ sk_C_1 )
    = ( u1_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['44','56'])).

thf('70',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_2 ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('71',plain,(
    l1_pre_topc @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    v2_pre_topc @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X1 )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X1 ) )
      | ( r1_tmap_1 @ sk_D @ sk_B_2 @ sk_E @ X2 )
      | ~ ( r1_tmap_1 @ X1 @ sk_B_2 @ ( k3_tmap_1 @ X0 @ sk_B_2 @ sk_D @ X1 @ sk_E ) @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ sk_C_1 ) )
      | ~ ( m1_pre_topc @ X1 @ sk_D )
      | ~ ( v1_tsep_1 @ X1 @ sk_D )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B_2 ) ) ),
    inference(demod,[status(thm)],['66','67','70','71','72'])).

thf('74',plain,
    ( ( v2_struct_0 @ sk_B_2 )
    | ( v2_struct_0 @ sk_D )
    | ~ ( m1_pre_topc @ sk_D @ sk_A )
    | ~ ( v1_tsep_1 @ sk_C_1 @ sk_D )
    | ~ ( m1_pre_topc @ sk_C_1 @ sk_D )
    | ~ ( m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_C_1 ) )
    | ( r1_tmap_1 @ sk_D @ sk_B_2 @ sk_E @ sk_F )
    | ~ ( m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_C_1 ) )
    | ~ ( m1_pre_topc @ sk_C_1 @ sk_A )
    | ( v2_struct_0 @ sk_C_1 )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['3','73'])).

thf('75',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_pre_topc @ sk_C_1 ) )
    = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf(t1_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( m1_subset_1 @ ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('78',plain,(
    ! [X41: $i,X42: $i] :
      ( ~ ( m1_pre_topc @ X41 @ X42 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X41 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X42 ) ) )
      | ~ ( l1_pre_topc @ X42 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('79',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,
    ( ~ ( l1_pre_topc @ sk_D )
    | ( m1_subset_1 @ ( u1_struct_0 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_pre_topc @ sk_C_1 ) ) ) ) )
    | ~ ( l1_pre_topc @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['76','79'])).

thf('81',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['12','13'])).

thf('82',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_pre_topc @ sk_C_1 ) )
    = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['18','19'])).

thf('84',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['80','81','82','83'])).

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

thf('85',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ~ ( m1_pre_topc @ X38 @ X39 )
      | ( X40
       != ( u1_struct_0 @ X38 ) )
      | ~ ( v3_pre_topc @ X40 @ X39 )
      | ( v1_tsep_1 @ X38 @ X39 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X39 ) ) )
      | ~ ( l1_pre_topc @ X39 )
      | ~ ( v2_pre_topc @ X39 ) ) ),
    inference(cnf,[status(esa)],[t16_tsep_1])).

thf('86',plain,(
    ! [X38: $i,X39: $i] :
      ( ~ ( v2_pre_topc @ X39 )
      | ~ ( l1_pre_topc @ X39 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X38 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X39 ) ) )
      | ( v1_tsep_1 @ X38 @ X39 )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ X38 ) @ X39 )
      | ~ ( m1_pre_topc @ X38 @ X39 ) ) ),
    inference(simplify,[status(thm)],['85'])).

thf('87',plain,
    ( ~ ( m1_pre_topc @ sk_C_1 @ sk_D )
    | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_C_1 ) @ sk_D )
    | ( v1_tsep_1 @ sk_C_1 @ sk_D )
    | ~ ( l1_pre_topc @ sk_D )
    | ~ ( v2_pre_topc @ sk_D ) ),
    inference('sup-',[status(thm)],['84','86'])).

thf('88',plain,(
    m1_pre_topc @ sk_C_1 @ sk_D ),
    inference(demod,[status(thm)],['39','40'])).

thf('89',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['12','13'])).

thf('90',plain,(
    v2_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['30','31','32'])).

thf('91',plain,
    ( ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_C_1 ) @ sk_D )
    | ( v1_tsep_1 @ sk_C_1 @ sk_D ) ),
    inference(demod,[status(thm)],['87','88','89','90'])).

thf(d1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( ( v2_pre_topc @ A )
      <=> ( ! [B: $i] :
              ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ! [C: $i] :
                  ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                 => ( ( ( r2_hidden @ C @ ( u1_pre_topc @ A ) )
                      & ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) )
                   => ( r2_hidden @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ ( u1_pre_topc @ A ) ) ) ) )
          & ! [B: $i] :
              ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
             => ( ( r1_tarski @ B @ ( u1_pre_topc @ A ) )
               => ( r2_hidden @ ( k5_setfam_1 @ ( u1_struct_0 @ A ) @ B ) @ ( u1_pre_topc @ A ) ) ) )
          & ( r2_hidden @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ) )).

thf(zf_stmt_1,type,(
    zip_tseitin_5: $i > $i > $o )).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( zip_tseitin_5 @ B @ A )
    <=> ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
       => ( zip_tseitin_4 @ B @ A ) ) ) )).

thf(zf_stmt_3,type,(
    zip_tseitin_4: $i > $i > $o )).

thf(zf_stmt_4,axiom,(
    ! [B: $i,A: $i] :
      ( ( zip_tseitin_4 @ B @ A )
    <=> ( ( r1_tarski @ B @ ( u1_pre_topc @ A ) )
       => ( r2_hidden @ ( k5_setfam_1 @ ( u1_struct_0 @ A ) @ B ) @ ( u1_pre_topc @ A ) ) ) ) )).

thf(zf_stmt_5,type,(
    zip_tseitin_3: $i > $i > $o )).

thf(zf_stmt_6,axiom,(
    ! [B: $i,A: $i] :
      ( ( zip_tseitin_3 @ B @ A )
    <=> ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
       => ! [C: $i] :
            ( zip_tseitin_2 @ C @ B @ A ) ) ) )).

thf(zf_stmt_7,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(zf_stmt_8,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_2 @ C @ B @ A )
    <=> ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
       => ( zip_tseitin_1 @ C @ B @ A ) ) ) )).

thf(zf_stmt_9,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zf_stmt_10,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_1 @ C @ B @ A )
    <=> ( ( zip_tseitin_0 @ C @ B @ A )
       => ( r2_hidden @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ ( u1_pre_topc @ A ) ) ) ) )).

thf(zf_stmt_11,type,(
    zip_tseitin_0: $i > $i > $i > $o )).

thf(zf_stmt_12,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ C @ B @ A )
    <=> ( ( r2_hidden @ B @ ( u1_pre_topc @ A ) )
        & ( r2_hidden @ C @ ( u1_pre_topc @ A ) ) ) ) )).

thf(zf_stmt_13,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( ( v2_pre_topc @ A )
      <=> ( ( r2_hidden @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) )
          & ! [B: $i] :
              ( zip_tseitin_5 @ B @ A )
          & ! [B: $i] :
              ( zip_tseitin_3 @ B @ A ) ) ) ) )).

thf('92',plain,(
    ! [X27: $i] :
      ( ~ ( v2_pre_topc @ X27 )
      | ( r2_hidden @ ( u1_struct_0 @ X27 ) @ ( u1_pre_topc @ X27 ) )
      | ~ ( l1_pre_topc @ X27 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_13])).

thf('93',plain,(
    ! [X43: $i] :
      ( ( m1_pre_topc @ X43 @ X43 )
      | ~ ( l1_pre_topc @ X43 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('94',plain,(
    ! [X41: $i,X42: $i] :
      ( ~ ( m1_pre_topc @ X41 @ X42 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X41 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X42 ) ) )
      | ~ ( l1_pre_topc @ X42 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('95',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['95'])).

thf(d5_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v3_pre_topc @ B @ A )
          <=> ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) ) ) ) )).

thf('97',plain,(
    ! [X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X31 ) ) )
      | ~ ( r2_hidden @ X30 @ ( u1_pre_topc @ X31 ) )
      | ( v3_pre_topc @ X30 @ X31 )
      | ~ ( l1_pre_topc @ X31 ) ) ),
    inference(cnf,[status(esa)],[d5_pre_topc])).

thf('98',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( r2_hidden @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) )
      | ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['98'])).

thf('100',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['92','99'])).

thf('101',plain,(
    ! [X0: $i] :
      ( ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['100'])).

thf('102',plain,(
    m1_pre_topc @ sk_D @ sk_C_1 ),
    inference(demod,[status(thm)],['9','14','15','20'])).

thf('103',plain,(
    ! [X36: $i,X37: $i] :
      ( ~ ( l1_pre_topc @ X36 )
      | ~ ( m1_pre_topc @ X37 @ X36 )
      | ( m1_pre_topc @ X37 @ ( g1_pre_topc @ ( u1_struct_0 @ X36 ) @ ( u1_pre_topc @ X36 ) ) )
      | ~ ( l1_pre_topc @ X37 ) ) ),
    inference(cnf,[status(esa)],[t65_pre_topc])).

thf('104',plain,
    ( ~ ( l1_pre_topc @ sk_D )
    | ( m1_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_pre_topc @ sk_C_1 ) ) )
    | ~ ( l1_pre_topc @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['102','103'])).

thf('105',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['12','13'])).

thf('106',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_pre_topc @ sk_C_1 ) )
    = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['18','19'])).

thf('108',plain,(
    m1_pre_topc @ sk_D @ sk_D ),
    inference(demod,[status(thm)],['104','105','106','107'])).

thf('109',plain,(
    ! [X41: $i,X42: $i] :
      ( ~ ( m1_pre_topc @ X41 @ X42 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X41 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X42 ) ) )
      | ~ ( l1_pre_topc @ X42 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('110',plain,
    ( ~ ( l1_pre_topc @ sk_D )
    | ( m1_subset_1 @ ( u1_struct_0 @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['108','109'])).

thf('111',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['12','13'])).

thf('112',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['110','111'])).

thf('113',plain,(
    ! [X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X31 ) ) )
      | ~ ( v3_pre_topc @ X30 @ X31 )
      | ( r2_hidden @ X30 @ ( u1_pre_topc @ X31 ) )
      | ~ ( l1_pre_topc @ X31 ) ) ),
    inference(cnf,[status(esa)],[d5_pre_topc])).

thf('114',plain,
    ( ~ ( l1_pre_topc @ sk_D )
    | ( r2_hidden @ ( u1_struct_0 @ sk_D ) @ ( u1_pre_topc @ sk_D ) )
    | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_D ) @ sk_D ) ),
    inference('sup-',[status(thm)],['112','113'])).

thf('115',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['12','13'])).

thf('116',plain,
    ( ( r2_hidden @ ( u1_struct_0 @ sk_D ) @ ( u1_pre_topc @ sk_D ) )
    | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_D ) @ sk_D ) ),
    inference(demod,[status(thm)],['114','115'])).

thf('117',plain,
    ( ~ ( l1_pre_topc @ sk_D )
    | ~ ( v2_pre_topc @ sk_D )
    | ( r2_hidden @ ( u1_struct_0 @ sk_D ) @ ( u1_pre_topc @ sk_D ) ) ),
    inference('sup-',[status(thm)],['101','116'])).

thf('118',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['12','13'])).

thf('119',plain,(
    v2_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['30','31','32'])).

thf('120',plain,(
    r2_hidden @ ( u1_struct_0 @ sk_D ) @ ( u1_pre_topc @ sk_D ) ),
    inference(demod,[status(thm)],['117','118','119'])).

thf('121',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) )
      | ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['98'])).

thf('122',plain,
    ( ~ ( l1_pre_topc @ sk_D )
    | ( v3_pre_topc @ ( u1_struct_0 @ sk_D ) @ sk_D ) ),
    inference('sup-',[status(thm)],['120','121'])).

thf('123',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['12','13'])).

thf('124',plain,(
    v3_pre_topc @ ( u1_struct_0 @ sk_D ) @ sk_D ),
    inference(demod,[status(thm)],['122','123'])).

thf('125',plain,
    ( ( u1_struct_0 @ sk_C_1 )
    = ( u1_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['44','56'])).

thf('126',plain,(
    v3_pre_topc @ ( u1_struct_0 @ sk_C_1 ) @ sk_D ),
    inference(demod,[status(thm)],['124','125'])).

thf('127',plain,(
    v1_tsep_1 @ sk_C_1 @ sk_D ),
    inference(demod,[status(thm)],['91','126'])).

thf('128',plain,(
    m1_pre_topc @ sk_C_1 @ sk_D ),
    inference(demod,[status(thm)],['39','40'])).

thf('129',plain,(
    m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('130',plain,(
    sk_F = sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('131',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['129','130'])).

thf('132',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['129','130'])).

thf('133',plain,(
    m1_pre_topc @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('134',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('135',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('136',plain,
    ( ( v2_struct_0 @ sk_B_2 )
    | ( v2_struct_0 @ sk_D )
    | ( r1_tmap_1 @ sk_D @ sk_B_2 @ sk_E @ sk_F )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['74','75','127','128','131','132','133','134','135'])).

thf('137',plain,(
    ~ ( r1_tmap_1 @ sk_D @ sk_B_2 @ sk_E @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('138',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['136','137'])).

thf('139',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('140',plain,
    ( ( v2_struct_0 @ sk_B_2 )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['138','139'])).

thf('141',plain,(
    ~ ( v2_struct_0 @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('142',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C_1 ) ),
    inference(clc,[status(thm)],['140','141'])).

thf('143',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('144',plain,(
    v2_struct_0 @ sk_C_1 ),
    inference(clc,[status(thm)],['142','143'])).

thf('145',plain,(
    $false ),
    inference(demod,[status(thm)],['0','144'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.DoCHOD4vEc
% 0.13/0.35  % Computer   : n002.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 14:10:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.94/2.17  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.94/2.17  % Solved by: fo/fo7.sh
% 1.94/2.17  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.94/2.17  % done 2707 iterations in 1.705s
% 1.94/2.17  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.94/2.17  % SZS output start Refutation
% 1.94/2.17  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 1.94/2.17  thf(zip_tseitin_4_type, type, zip_tseitin_4: $i > $i > $o).
% 1.94/2.17  thf(zip_tseitin_5_type, type, zip_tseitin_5: $i > $i > $o).
% 1.94/2.17  thf(sk_D_type, type, sk_D: $i).
% 1.94/2.17  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.94/2.17  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 1.94/2.17  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $o).
% 1.94/2.17  thf(zip_tseitin_3_type, type, zip_tseitin_3: $i > $i > $o).
% 1.94/2.17  thf(sk_G_type, type, sk_G: $i).
% 1.94/2.17  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 1.94/2.17  thf(sk_F_type, type, sk_F: $i).
% 1.94/2.17  thf(sk_E_type, type, sk_E: $i).
% 1.94/2.17  thf(sk_C_1_type, type, sk_C_1: $i).
% 1.94/2.17  thf(r1_tmap_1_type, type, r1_tmap_1: $i > $i > $i > $i > $o).
% 1.94/2.17  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 1.94/2.17  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 1.94/2.17  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 1.94/2.17  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.94/2.17  thf(sk_B_2_type, type, sk_B_2: $i).
% 1.94/2.17  thf(v1_tsep_1_type, type, v1_tsep_1: $i > $i > $o).
% 1.94/2.17  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.94/2.17  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 1.94/2.17  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.94/2.17  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 1.94/2.17  thf(zip_tseitin_2_type, type, zip_tseitin_2: $i > $i > $i > $o).
% 1.94/2.17  thf(g1_pre_topc_type, type, g1_pre_topc: $i > $i > $i).
% 1.94/2.17  thf(k3_tmap_1_type, type, k3_tmap_1: $i > $i > $i > $i > $i > $i).
% 1.94/2.17  thf(sk_A_type, type, sk_A: $i).
% 1.94/2.17  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.94/2.17  thf(k5_setfam_1_type, type, k5_setfam_1: $i > $i > $i).
% 1.94/2.17  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.94/2.17  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.94/2.17  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 1.94/2.17  thf(t88_tmap_1, conjecture,
% 1.94/2.17    (![A:$i]:
% 1.94/2.17     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.94/2.17       ( ![B:$i]:
% 1.94/2.17         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 1.94/2.17             ( l1_pre_topc @ B ) ) =>
% 1.94/2.17           ( ![C:$i]:
% 1.94/2.17             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 1.94/2.17               ( ![D:$i]:
% 1.94/2.17                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 1.94/2.17                   ( ![E:$i]:
% 1.94/2.17                     ( ( ( v1_funct_1 @ E ) & 
% 1.94/2.17                         ( v1_funct_2 @
% 1.94/2.17                           E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 1.94/2.17                         ( m1_subset_1 @
% 1.94/2.17                           E @ 
% 1.94/2.17                           ( k1_zfmisc_1 @
% 1.94/2.17                             ( k2_zfmisc_1 @
% 1.94/2.17                               ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 1.94/2.17                       ( ( ( g1_pre_topc @
% 1.94/2.17                             ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) ) =
% 1.94/2.17                           ( D ) ) =>
% 1.94/2.17                         ( ![F:$i]:
% 1.94/2.17                           ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 1.94/2.17                             ( ![G:$i]:
% 1.94/2.17                               ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) ) =>
% 1.94/2.17                                 ( ( ( ( F ) = ( G ) ) & 
% 1.94/2.17                                     ( r1_tmap_1 @
% 1.94/2.17                                       C @ B @ 
% 1.94/2.17                                       ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ G ) ) =>
% 1.94/2.17                                   ( r1_tmap_1 @ D @ B @ E @ F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 1.94/2.17  thf(zf_stmt_0, negated_conjecture,
% 1.94/2.17    (~( ![A:$i]:
% 1.94/2.17        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 1.94/2.17            ( l1_pre_topc @ A ) ) =>
% 1.94/2.17          ( ![B:$i]:
% 1.94/2.17            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 1.94/2.17                ( l1_pre_topc @ B ) ) =>
% 1.94/2.17              ( ![C:$i]:
% 1.94/2.17                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 1.94/2.17                  ( ![D:$i]:
% 1.94/2.17                    ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 1.94/2.17                      ( ![E:$i]:
% 1.94/2.17                        ( ( ( v1_funct_1 @ E ) & 
% 1.94/2.17                            ( v1_funct_2 @
% 1.94/2.17                              E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 1.94/2.17                            ( m1_subset_1 @
% 1.94/2.17                              E @ 
% 1.94/2.17                              ( k1_zfmisc_1 @
% 1.94/2.17                                ( k2_zfmisc_1 @
% 1.94/2.17                                  ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 1.94/2.17                          ( ( ( g1_pre_topc @
% 1.94/2.17                                ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) ) =
% 1.94/2.17                              ( D ) ) =>
% 1.94/2.17                            ( ![F:$i]:
% 1.94/2.17                              ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 1.94/2.17                                ( ![G:$i]:
% 1.94/2.17                                  ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) ) =>
% 1.94/2.17                                    ( ( ( ( F ) = ( G ) ) & 
% 1.94/2.17                                        ( r1_tmap_1 @
% 1.94/2.17                                          C @ B @ 
% 1.94/2.17                                          ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ G ) ) =>
% 1.94/2.17                                      ( r1_tmap_1 @ D @ B @ E @ F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 1.94/2.17    inference('cnf.neg', [status(esa)], [t88_tmap_1])).
% 1.94/2.17  thf('0', plain, (~ (v2_struct_0 @ sk_C_1)),
% 1.94/2.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.94/2.17  thf('1', plain,
% 1.94/2.17      ((r1_tmap_1 @ sk_C_1 @ sk_B_2 @ 
% 1.94/2.17        (k3_tmap_1 @ sk_A @ sk_B_2 @ sk_D @ sk_C_1 @ sk_E) @ sk_G)),
% 1.94/2.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.94/2.17  thf('2', plain, (((sk_F) = (sk_G))),
% 1.94/2.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.94/2.17  thf('3', plain,
% 1.94/2.17      ((r1_tmap_1 @ sk_C_1 @ sk_B_2 @ 
% 1.94/2.17        (k3_tmap_1 @ sk_A @ sk_B_2 @ sk_D @ sk_C_1 @ sk_E) @ sk_F)),
% 1.94/2.17      inference('demod', [status(thm)], ['1', '2'])).
% 1.94/2.17  thf('4', plain,
% 1.94/2.17      ((m1_subset_1 @ sk_E @ 
% 1.94/2.17        (k1_zfmisc_1 @ 
% 1.94/2.17         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B_2))))),
% 1.94/2.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.94/2.17  thf('5', plain,
% 1.94/2.17      (((g1_pre_topc @ (u1_struct_0 @ sk_C_1) @ (u1_pre_topc @ sk_C_1))
% 1.94/2.17         = (sk_D))),
% 1.94/2.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.94/2.17  thf(t2_tsep_1, axiom,
% 1.94/2.17    (![A:$i]: ( ( l1_pre_topc @ A ) => ( m1_pre_topc @ A @ A ) ))).
% 1.94/2.17  thf('6', plain,
% 1.94/2.17      (![X43 : $i]: ((m1_pre_topc @ X43 @ X43) | ~ (l1_pre_topc @ X43))),
% 1.94/2.17      inference('cnf', [status(esa)], [t2_tsep_1])).
% 1.94/2.17  thf(t59_pre_topc, axiom,
% 1.94/2.17    (![A:$i]:
% 1.94/2.17     ( ( l1_pre_topc @ A ) =>
% 1.94/2.17       ( ![B:$i]:
% 1.94/2.17         ( ( m1_pre_topc @
% 1.94/2.17             B @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) =>
% 1.94/2.17           ( m1_pre_topc @ B @ A ) ) ) ))).
% 1.94/2.17  thf('7', plain,
% 1.94/2.17      (![X34 : $i, X35 : $i]:
% 1.94/2.17         (~ (m1_pre_topc @ X34 @ 
% 1.94/2.17             (g1_pre_topc @ (u1_struct_0 @ X35) @ (u1_pre_topc @ X35)))
% 1.94/2.17          | (m1_pre_topc @ X34 @ X35)
% 1.94/2.17          | ~ (l1_pre_topc @ X35))),
% 1.94/2.17      inference('cnf', [status(esa)], [t59_pre_topc])).
% 1.94/2.17  thf('8', plain,
% 1.94/2.17      (![X0 : $i]:
% 1.94/2.17         (~ (l1_pre_topc @ 
% 1.94/2.17             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 1.94/2.17          | ~ (l1_pre_topc @ X0)
% 1.94/2.17          | (m1_pre_topc @ 
% 1.94/2.17             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)) @ X0))),
% 1.94/2.17      inference('sup-', [status(thm)], ['6', '7'])).
% 1.94/2.17  thf('9', plain,
% 1.94/2.17      ((~ (l1_pre_topc @ sk_D)
% 1.94/2.17        | (m1_pre_topc @ 
% 1.94/2.17           (g1_pre_topc @ (u1_struct_0 @ sk_C_1) @ (u1_pre_topc @ sk_C_1)) @ 
% 1.94/2.17           sk_C_1)
% 1.94/2.17        | ~ (l1_pre_topc @ sk_C_1))),
% 1.94/2.17      inference('sup-', [status(thm)], ['5', '8'])).
% 1.94/2.17  thf('10', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 1.94/2.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.94/2.17  thf(dt_m1_pre_topc, axiom,
% 1.94/2.17    (![A:$i]:
% 1.94/2.17     ( ( l1_pre_topc @ A ) =>
% 1.94/2.17       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 1.94/2.17  thf('11', plain,
% 1.94/2.17      (![X32 : $i, X33 : $i]:
% 1.94/2.17         (~ (m1_pre_topc @ X32 @ X33)
% 1.94/2.17          | (l1_pre_topc @ X32)
% 1.94/2.17          | ~ (l1_pre_topc @ X33))),
% 1.94/2.17      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 1.94/2.17  thf('12', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_D))),
% 1.94/2.17      inference('sup-', [status(thm)], ['10', '11'])).
% 1.94/2.17  thf('13', plain, ((l1_pre_topc @ sk_A)),
% 1.94/2.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.94/2.17  thf('14', plain, ((l1_pre_topc @ sk_D)),
% 1.94/2.17      inference('demod', [status(thm)], ['12', '13'])).
% 1.94/2.17  thf('15', plain,
% 1.94/2.17      (((g1_pre_topc @ (u1_struct_0 @ sk_C_1) @ (u1_pre_topc @ sk_C_1))
% 1.94/2.17         = (sk_D))),
% 1.94/2.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.94/2.17  thf('16', plain, ((m1_pre_topc @ sk_C_1 @ sk_A)),
% 1.94/2.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.94/2.17  thf('17', plain,
% 1.94/2.17      (![X32 : $i, X33 : $i]:
% 1.94/2.17         (~ (m1_pre_topc @ X32 @ X33)
% 1.94/2.17          | (l1_pre_topc @ X32)
% 1.94/2.17          | ~ (l1_pre_topc @ X33))),
% 1.94/2.17      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 1.94/2.17  thf('18', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_C_1))),
% 1.94/2.17      inference('sup-', [status(thm)], ['16', '17'])).
% 1.94/2.17  thf('19', plain, ((l1_pre_topc @ sk_A)),
% 1.94/2.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.94/2.17  thf('20', plain, ((l1_pre_topc @ sk_C_1)),
% 1.94/2.17      inference('demod', [status(thm)], ['18', '19'])).
% 1.94/2.17  thf('21', plain, ((m1_pre_topc @ sk_D @ sk_C_1)),
% 1.94/2.17      inference('demod', [status(thm)], ['9', '14', '15', '20'])).
% 1.94/2.17  thf('22', plain,
% 1.94/2.17      (![X43 : $i]: ((m1_pre_topc @ X43 @ X43) | ~ (l1_pre_topc @ X43))),
% 1.94/2.17      inference('cnf', [status(esa)], [t2_tsep_1])).
% 1.94/2.17  thf(t4_tsep_1, axiom,
% 1.94/2.17    (![A:$i]:
% 1.94/2.17     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.94/2.17       ( ![B:$i]:
% 1.94/2.17         ( ( m1_pre_topc @ B @ A ) =>
% 1.94/2.17           ( ![C:$i]:
% 1.94/2.17             ( ( m1_pre_topc @ C @ A ) =>
% 1.94/2.17               ( ( r1_tarski @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ C ) ) <=>
% 1.94/2.17                 ( m1_pre_topc @ B @ C ) ) ) ) ) ) ))).
% 1.94/2.17  thf('23', plain,
% 1.94/2.17      (![X44 : $i, X45 : $i, X46 : $i]:
% 1.94/2.17         (~ (m1_pre_topc @ X44 @ X45)
% 1.94/2.17          | ~ (m1_pre_topc @ X44 @ X46)
% 1.94/2.17          | (r1_tarski @ (u1_struct_0 @ X44) @ (u1_struct_0 @ X46))
% 1.94/2.17          | ~ (m1_pre_topc @ X46 @ X45)
% 1.94/2.17          | ~ (l1_pre_topc @ X45)
% 1.94/2.17          | ~ (v2_pre_topc @ X45))),
% 1.94/2.17      inference('cnf', [status(esa)], [t4_tsep_1])).
% 1.94/2.17  thf('24', plain,
% 1.94/2.17      (![X0 : $i, X1 : $i]:
% 1.94/2.17         (~ (l1_pre_topc @ X0)
% 1.94/2.17          | ~ (v2_pre_topc @ X0)
% 1.94/2.17          | ~ (l1_pre_topc @ X0)
% 1.94/2.17          | ~ (m1_pre_topc @ X1 @ X0)
% 1.94/2.17          | (r1_tarski @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X1))
% 1.94/2.17          | ~ (m1_pre_topc @ X0 @ X1))),
% 1.94/2.17      inference('sup-', [status(thm)], ['22', '23'])).
% 1.94/2.17  thf('25', plain,
% 1.94/2.17      (![X0 : $i, X1 : $i]:
% 1.94/2.17         (~ (m1_pre_topc @ X0 @ X1)
% 1.94/2.17          | (r1_tarski @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X1))
% 1.94/2.17          | ~ (m1_pre_topc @ X1 @ X0)
% 1.94/2.17          | ~ (v2_pre_topc @ X0)
% 1.94/2.17          | ~ (l1_pre_topc @ X0))),
% 1.94/2.17      inference('simplify', [status(thm)], ['24'])).
% 1.94/2.17  thf('26', plain,
% 1.94/2.17      ((~ (l1_pre_topc @ sk_D)
% 1.94/2.17        | ~ (v2_pre_topc @ sk_D)
% 1.94/2.17        | ~ (m1_pre_topc @ sk_C_1 @ sk_D)
% 1.94/2.17        | (r1_tarski @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_C_1)))),
% 1.94/2.17      inference('sup-', [status(thm)], ['21', '25'])).
% 1.94/2.17  thf('27', plain, ((l1_pre_topc @ sk_D)),
% 1.94/2.17      inference('demod', [status(thm)], ['12', '13'])).
% 1.94/2.17  thf('28', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 1.94/2.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.94/2.17  thf(cc1_pre_topc, axiom,
% 1.94/2.17    (![A:$i]:
% 1.94/2.17     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.94/2.17       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( v2_pre_topc @ B ) ) ) ))).
% 1.94/2.17  thf('29', plain,
% 1.94/2.17      (![X3 : $i, X4 : $i]:
% 1.94/2.17         (~ (m1_pre_topc @ X3 @ X4)
% 1.94/2.17          | (v2_pre_topc @ X3)
% 1.94/2.17          | ~ (l1_pre_topc @ X4)
% 1.94/2.17          | ~ (v2_pre_topc @ X4))),
% 1.94/2.17      inference('cnf', [status(esa)], [cc1_pre_topc])).
% 1.94/2.17  thf('30', plain,
% 1.94/2.17      ((~ (v2_pre_topc @ sk_A) | ~ (l1_pre_topc @ sk_A) | (v2_pre_topc @ sk_D))),
% 1.94/2.17      inference('sup-', [status(thm)], ['28', '29'])).
% 1.94/2.17  thf('31', plain, ((v2_pre_topc @ sk_A)),
% 1.94/2.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.94/2.17  thf('32', plain, ((l1_pre_topc @ sk_A)),
% 1.94/2.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.94/2.17  thf('33', plain, ((v2_pre_topc @ sk_D)),
% 1.94/2.17      inference('demod', [status(thm)], ['30', '31', '32'])).
% 1.94/2.17  thf('34', plain,
% 1.94/2.17      (((g1_pre_topc @ (u1_struct_0 @ sk_C_1) @ (u1_pre_topc @ sk_C_1))
% 1.94/2.17         = (sk_D))),
% 1.94/2.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.94/2.17  thf('35', plain,
% 1.94/2.17      (![X43 : $i]: ((m1_pre_topc @ X43 @ X43) | ~ (l1_pre_topc @ X43))),
% 1.94/2.17      inference('cnf', [status(esa)], [t2_tsep_1])).
% 1.94/2.17  thf(t65_pre_topc, axiom,
% 1.94/2.17    (![A:$i]:
% 1.94/2.17     ( ( l1_pre_topc @ A ) =>
% 1.94/2.17       ( ![B:$i]:
% 1.94/2.17         ( ( l1_pre_topc @ B ) =>
% 1.94/2.17           ( ( m1_pre_topc @ A @ B ) <=>
% 1.94/2.17             ( m1_pre_topc @
% 1.94/2.17               A @ ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ) ))).
% 1.94/2.17  thf('36', plain,
% 1.94/2.17      (![X36 : $i, X37 : $i]:
% 1.94/2.17         (~ (l1_pre_topc @ X36)
% 1.94/2.17          | ~ (m1_pre_topc @ X37 @ X36)
% 1.94/2.17          | (m1_pre_topc @ X37 @ 
% 1.94/2.17             (g1_pre_topc @ (u1_struct_0 @ X36) @ (u1_pre_topc @ X36)))
% 1.94/2.17          | ~ (l1_pre_topc @ X37))),
% 1.94/2.17      inference('cnf', [status(esa)], [t65_pre_topc])).
% 1.94/2.17  thf('37', plain,
% 1.94/2.17      (![X0 : $i]:
% 1.94/2.17         (~ (l1_pre_topc @ X0)
% 1.94/2.17          | ~ (l1_pre_topc @ X0)
% 1.94/2.17          | (m1_pre_topc @ X0 @ 
% 1.94/2.17             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 1.94/2.17          | ~ (l1_pre_topc @ X0))),
% 1.94/2.17      inference('sup-', [status(thm)], ['35', '36'])).
% 1.94/2.17  thf('38', plain,
% 1.94/2.17      (![X0 : $i]:
% 1.94/2.17         ((m1_pre_topc @ X0 @ 
% 1.94/2.17           (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 1.94/2.17          | ~ (l1_pre_topc @ X0))),
% 1.94/2.17      inference('simplify', [status(thm)], ['37'])).
% 1.94/2.17  thf('39', plain,
% 1.94/2.17      (((m1_pre_topc @ sk_C_1 @ sk_D) | ~ (l1_pre_topc @ sk_C_1))),
% 1.94/2.17      inference('sup+', [status(thm)], ['34', '38'])).
% 1.94/2.17  thf('40', plain, ((l1_pre_topc @ sk_C_1)),
% 1.94/2.17      inference('demod', [status(thm)], ['18', '19'])).
% 1.94/2.17  thf('41', plain, ((m1_pre_topc @ sk_C_1 @ sk_D)),
% 1.94/2.17      inference('demod', [status(thm)], ['39', '40'])).
% 1.94/2.17  thf('42', plain,
% 1.94/2.17      ((r1_tarski @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_C_1))),
% 1.94/2.17      inference('demod', [status(thm)], ['26', '27', '33', '41'])).
% 1.94/2.17  thf(d10_xboole_0, axiom,
% 1.94/2.17    (![A:$i,B:$i]:
% 1.94/2.17     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.94/2.17  thf('43', plain,
% 1.94/2.17      (![X0 : $i, X2 : $i]:
% 1.94/2.17         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 1.94/2.17      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.94/2.17  thf('44', plain,
% 1.94/2.17      ((~ (r1_tarski @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_D))
% 1.94/2.17        | ((u1_struct_0 @ sk_C_1) = (u1_struct_0 @ sk_D)))),
% 1.94/2.17      inference('sup-', [status(thm)], ['42', '43'])).
% 1.94/2.17  thf('45', plain, ((m1_pre_topc @ sk_C_1 @ sk_D)),
% 1.94/2.17      inference('demod', [status(thm)], ['39', '40'])).
% 1.94/2.17  thf('46', plain,
% 1.94/2.17      (![X0 : $i, X1 : $i]:
% 1.94/2.17         (~ (m1_pre_topc @ X0 @ X1)
% 1.94/2.17          | (r1_tarski @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X1))
% 1.94/2.17          | ~ (m1_pre_topc @ X1 @ X0)
% 1.94/2.17          | ~ (v2_pre_topc @ X0)
% 1.94/2.17          | ~ (l1_pre_topc @ X0))),
% 1.94/2.17      inference('simplify', [status(thm)], ['24'])).
% 1.94/2.17  thf('47', plain,
% 1.94/2.17      ((~ (l1_pre_topc @ sk_C_1)
% 1.94/2.17        | ~ (v2_pre_topc @ sk_C_1)
% 1.94/2.17        | ~ (m1_pre_topc @ sk_D @ sk_C_1)
% 1.94/2.17        | (r1_tarski @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_D)))),
% 1.94/2.17      inference('sup-', [status(thm)], ['45', '46'])).
% 1.94/2.17  thf('48', plain, ((l1_pre_topc @ sk_C_1)),
% 1.94/2.17      inference('demod', [status(thm)], ['18', '19'])).
% 1.94/2.17  thf('49', plain, ((m1_pre_topc @ sk_C_1 @ sk_A)),
% 1.94/2.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.94/2.17  thf('50', plain,
% 1.94/2.17      (![X3 : $i, X4 : $i]:
% 1.94/2.17         (~ (m1_pre_topc @ X3 @ X4)
% 1.94/2.17          | (v2_pre_topc @ X3)
% 1.94/2.17          | ~ (l1_pre_topc @ X4)
% 1.94/2.17          | ~ (v2_pre_topc @ X4))),
% 1.94/2.17      inference('cnf', [status(esa)], [cc1_pre_topc])).
% 1.94/2.17  thf('51', plain,
% 1.94/2.17      ((~ (v2_pre_topc @ sk_A)
% 1.94/2.17        | ~ (l1_pre_topc @ sk_A)
% 1.94/2.17        | (v2_pre_topc @ sk_C_1))),
% 1.94/2.17      inference('sup-', [status(thm)], ['49', '50'])).
% 1.94/2.17  thf('52', plain, ((v2_pre_topc @ sk_A)),
% 1.94/2.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.94/2.17  thf('53', plain, ((l1_pre_topc @ sk_A)),
% 1.94/2.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.94/2.17  thf('54', plain, ((v2_pre_topc @ sk_C_1)),
% 1.94/2.17      inference('demod', [status(thm)], ['51', '52', '53'])).
% 1.94/2.17  thf('55', plain, ((m1_pre_topc @ sk_D @ sk_C_1)),
% 1.94/2.17      inference('demod', [status(thm)], ['9', '14', '15', '20'])).
% 1.94/2.17  thf('56', plain,
% 1.94/2.17      ((r1_tarski @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_D))),
% 1.94/2.17      inference('demod', [status(thm)], ['47', '48', '54', '55'])).
% 1.94/2.17  thf('57', plain, (((u1_struct_0 @ sk_C_1) = (u1_struct_0 @ sk_D))),
% 1.94/2.17      inference('demod', [status(thm)], ['44', '56'])).
% 1.94/2.17  thf('58', plain,
% 1.94/2.17      ((m1_subset_1 @ sk_E @ 
% 1.94/2.17        (k1_zfmisc_1 @ 
% 1.94/2.17         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B_2))))),
% 1.94/2.17      inference('demod', [status(thm)], ['4', '57'])).
% 1.94/2.17  thf('59', plain, (((u1_struct_0 @ sk_C_1) = (u1_struct_0 @ sk_D))),
% 1.94/2.17      inference('demod', [status(thm)], ['44', '56'])).
% 1.94/2.17  thf(t86_tmap_1, axiom,
% 1.94/2.17    (![A:$i]:
% 1.94/2.17     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.94/2.17       ( ![B:$i]:
% 1.94/2.17         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 1.94/2.17             ( l1_pre_topc @ B ) ) =>
% 1.94/2.17           ( ![C:$i]:
% 1.94/2.17             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 1.94/2.17               ( ![D:$i]:
% 1.94/2.17                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 1.94/2.17                   ( ![E:$i]:
% 1.94/2.17                     ( ( ( v1_funct_1 @ E ) & 
% 1.94/2.17                         ( v1_funct_2 @
% 1.94/2.17                           E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 1.94/2.17                         ( m1_subset_1 @
% 1.94/2.17                           E @ 
% 1.94/2.17                           ( k1_zfmisc_1 @
% 1.94/2.17                             ( k2_zfmisc_1 @
% 1.94/2.17                               ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 1.94/2.17                       ( ( ( v1_tsep_1 @ C @ D ) & ( m1_pre_topc @ C @ D ) ) =>
% 1.94/2.17                         ( ![F:$i]:
% 1.94/2.17                           ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 1.94/2.17                             ( ![G:$i]:
% 1.94/2.17                               ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) ) =>
% 1.94/2.17                                 ( ( ( F ) = ( G ) ) =>
% 1.94/2.17                                   ( ( r1_tmap_1 @ D @ B @ E @ F ) <=>
% 1.94/2.17                                     ( r1_tmap_1 @
% 1.94/2.17                                       C @ B @ 
% 1.94/2.17                                       ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ G ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 1.94/2.17  thf('60', plain,
% 1.94/2.17      (![X50 : $i, X51 : $i, X52 : $i, X53 : $i, X54 : $i, X55 : $i, X56 : $i]:
% 1.94/2.17         ((v2_struct_0 @ X50)
% 1.94/2.17          | ~ (v2_pre_topc @ X50)
% 1.94/2.17          | ~ (l1_pre_topc @ X50)
% 1.94/2.17          | (v2_struct_0 @ X51)
% 1.94/2.17          | ~ (m1_pre_topc @ X51 @ X52)
% 1.94/2.17          | ~ (v1_tsep_1 @ X53 @ X51)
% 1.94/2.17          | ~ (m1_pre_topc @ X53 @ X51)
% 1.94/2.17          | ~ (m1_subset_1 @ X54 @ (u1_struct_0 @ X51))
% 1.94/2.17          | ((X54) != (X55))
% 1.94/2.17          | ~ (r1_tmap_1 @ X53 @ X50 @ 
% 1.94/2.17               (k3_tmap_1 @ X52 @ X50 @ X51 @ X53 @ X56) @ X55)
% 1.94/2.17          | (r1_tmap_1 @ X51 @ X50 @ X56 @ X54)
% 1.94/2.17          | ~ (m1_subset_1 @ X55 @ (u1_struct_0 @ X53))
% 1.94/2.17          | ~ (m1_subset_1 @ X56 @ 
% 1.94/2.17               (k1_zfmisc_1 @ 
% 1.94/2.17                (k2_zfmisc_1 @ (u1_struct_0 @ X51) @ (u1_struct_0 @ X50))))
% 1.94/2.17          | ~ (v1_funct_2 @ X56 @ (u1_struct_0 @ X51) @ (u1_struct_0 @ X50))
% 1.94/2.17          | ~ (v1_funct_1 @ X56)
% 1.94/2.17          | ~ (m1_pre_topc @ X53 @ X52)
% 1.94/2.17          | (v2_struct_0 @ X53)
% 1.94/2.17          | ~ (l1_pre_topc @ X52)
% 1.94/2.17          | ~ (v2_pre_topc @ X52)
% 1.94/2.17          | (v2_struct_0 @ X52))),
% 1.94/2.17      inference('cnf', [status(esa)], [t86_tmap_1])).
% 1.94/2.17  thf('61', plain,
% 1.94/2.17      (![X50 : $i, X51 : $i, X52 : $i, X53 : $i, X55 : $i, X56 : $i]:
% 1.94/2.17         ((v2_struct_0 @ X52)
% 1.94/2.17          | ~ (v2_pre_topc @ X52)
% 1.94/2.17          | ~ (l1_pre_topc @ X52)
% 1.94/2.17          | (v2_struct_0 @ X53)
% 1.94/2.17          | ~ (m1_pre_topc @ X53 @ X52)
% 1.94/2.17          | ~ (v1_funct_1 @ X56)
% 1.94/2.17          | ~ (v1_funct_2 @ X56 @ (u1_struct_0 @ X51) @ (u1_struct_0 @ X50))
% 1.94/2.17          | ~ (m1_subset_1 @ X56 @ 
% 1.94/2.17               (k1_zfmisc_1 @ 
% 1.94/2.17                (k2_zfmisc_1 @ (u1_struct_0 @ X51) @ (u1_struct_0 @ X50))))
% 1.94/2.17          | ~ (m1_subset_1 @ X55 @ (u1_struct_0 @ X53))
% 1.94/2.17          | (r1_tmap_1 @ X51 @ X50 @ X56 @ X55)
% 1.94/2.17          | ~ (r1_tmap_1 @ X53 @ X50 @ 
% 1.94/2.17               (k3_tmap_1 @ X52 @ X50 @ X51 @ X53 @ X56) @ X55)
% 1.94/2.17          | ~ (m1_subset_1 @ X55 @ (u1_struct_0 @ X51))
% 1.94/2.17          | ~ (m1_pre_topc @ X53 @ X51)
% 1.94/2.17          | ~ (v1_tsep_1 @ X53 @ X51)
% 1.94/2.17          | ~ (m1_pre_topc @ X51 @ X52)
% 1.94/2.17          | (v2_struct_0 @ X51)
% 1.94/2.17          | ~ (l1_pre_topc @ X50)
% 1.94/2.17          | ~ (v2_pre_topc @ X50)
% 1.94/2.17          | (v2_struct_0 @ X50))),
% 1.94/2.17      inference('simplify', [status(thm)], ['60'])).
% 1.94/2.17  thf('62', plain,
% 1.94/2.17      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 1.94/2.17         (~ (m1_subset_1 @ X1 @ 
% 1.94/2.17             (k1_zfmisc_1 @ 
% 1.94/2.17              (k2_zfmisc_1 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ X0))))
% 1.94/2.17          | (v2_struct_0 @ X0)
% 1.94/2.17          | ~ (v2_pre_topc @ X0)
% 1.94/2.17          | ~ (l1_pre_topc @ X0)
% 1.94/2.17          | (v2_struct_0 @ sk_D)
% 1.94/2.17          | ~ (m1_pre_topc @ sk_D @ X2)
% 1.94/2.17          | ~ (v1_tsep_1 @ X3 @ sk_D)
% 1.94/2.17          | ~ (m1_pre_topc @ X3 @ sk_D)
% 1.94/2.17          | ~ (m1_subset_1 @ X4 @ (u1_struct_0 @ sk_D))
% 1.94/2.17          | ~ (r1_tmap_1 @ X3 @ X0 @ (k3_tmap_1 @ X2 @ X0 @ sk_D @ X3 @ X1) @ 
% 1.94/2.17               X4)
% 1.94/2.17          | (r1_tmap_1 @ sk_D @ X0 @ X1 @ X4)
% 1.94/2.17          | ~ (m1_subset_1 @ X4 @ (u1_struct_0 @ X3))
% 1.94/2.17          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ X0))
% 1.94/2.17          | ~ (v1_funct_1 @ X1)
% 1.94/2.17          | ~ (m1_pre_topc @ X3 @ X2)
% 1.94/2.17          | (v2_struct_0 @ X3)
% 1.94/2.17          | ~ (l1_pre_topc @ X2)
% 1.94/2.17          | ~ (v2_pre_topc @ X2)
% 1.94/2.17          | (v2_struct_0 @ X2))),
% 1.94/2.17      inference('sup-', [status(thm)], ['59', '61'])).
% 1.94/2.17  thf('63', plain, (((u1_struct_0 @ sk_C_1) = (u1_struct_0 @ sk_D))),
% 1.94/2.17      inference('demod', [status(thm)], ['44', '56'])).
% 1.94/2.17  thf('64', plain, (((u1_struct_0 @ sk_C_1) = (u1_struct_0 @ sk_D))),
% 1.94/2.17      inference('demod', [status(thm)], ['44', '56'])).
% 1.94/2.17  thf('65', plain,
% 1.94/2.17      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 1.94/2.17         (~ (m1_subset_1 @ X1 @ 
% 1.94/2.17             (k1_zfmisc_1 @ 
% 1.94/2.17              (k2_zfmisc_1 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ X0))))
% 1.94/2.17          | (v2_struct_0 @ X0)
% 1.94/2.17          | ~ (v2_pre_topc @ X0)
% 1.94/2.17          | ~ (l1_pre_topc @ X0)
% 1.94/2.17          | (v2_struct_0 @ sk_D)
% 1.94/2.17          | ~ (m1_pre_topc @ sk_D @ X2)
% 1.94/2.17          | ~ (v1_tsep_1 @ X3 @ sk_D)
% 1.94/2.17          | ~ (m1_pre_topc @ X3 @ sk_D)
% 1.94/2.17          | ~ (m1_subset_1 @ X4 @ (u1_struct_0 @ sk_C_1))
% 1.94/2.17          | ~ (r1_tmap_1 @ X3 @ X0 @ (k3_tmap_1 @ X2 @ X0 @ sk_D @ X3 @ X1) @ 
% 1.94/2.17               X4)
% 1.94/2.17          | (r1_tmap_1 @ sk_D @ X0 @ X1 @ X4)
% 1.94/2.17          | ~ (m1_subset_1 @ X4 @ (u1_struct_0 @ X3))
% 1.94/2.17          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ X0))
% 1.94/2.17          | ~ (v1_funct_1 @ X1)
% 1.94/2.17          | ~ (m1_pre_topc @ X3 @ X2)
% 1.94/2.17          | (v2_struct_0 @ X3)
% 1.94/2.17          | ~ (l1_pre_topc @ X2)
% 1.94/2.17          | ~ (v2_pre_topc @ X2)
% 1.94/2.17          | (v2_struct_0 @ X2))),
% 1.94/2.17      inference('demod', [status(thm)], ['62', '63', '64'])).
% 1.94/2.17  thf('66', plain,
% 1.94/2.17      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.94/2.17         ((v2_struct_0 @ X0)
% 1.94/2.17          | ~ (v2_pre_topc @ X0)
% 1.94/2.17          | ~ (l1_pre_topc @ X0)
% 1.94/2.17          | (v2_struct_0 @ X1)
% 1.94/2.17          | ~ (m1_pre_topc @ X1 @ X0)
% 1.94/2.17          | ~ (v1_funct_1 @ sk_E)
% 1.94/2.17          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_C_1) @ 
% 1.94/2.17               (u1_struct_0 @ sk_B_2))
% 1.94/2.17          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1))
% 1.94/2.17          | (r1_tmap_1 @ sk_D @ sk_B_2 @ sk_E @ X2)
% 1.94/2.17          | ~ (r1_tmap_1 @ X1 @ sk_B_2 @ 
% 1.94/2.17               (k3_tmap_1 @ X0 @ sk_B_2 @ sk_D @ X1 @ sk_E) @ X2)
% 1.94/2.17          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ sk_C_1))
% 1.94/2.17          | ~ (m1_pre_topc @ X1 @ sk_D)
% 1.94/2.17          | ~ (v1_tsep_1 @ X1 @ sk_D)
% 1.94/2.17          | ~ (m1_pre_topc @ sk_D @ X0)
% 1.94/2.17          | (v2_struct_0 @ sk_D)
% 1.94/2.17          | ~ (l1_pre_topc @ sk_B_2)
% 1.94/2.17          | ~ (v2_pre_topc @ sk_B_2)
% 1.94/2.17          | (v2_struct_0 @ sk_B_2))),
% 1.94/2.17      inference('sup-', [status(thm)], ['58', '65'])).
% 1.94/2.17  thf('67', plain, ((v1_funct_1 @ sk_E)),
% 1.94/2.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.94/2.17  thf('68', plain,
% 1.94/2.17      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B_2))),
% 1.94/2.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.94/2.17  thf('69', plain, (((u1_struct_0 @ sk_C_1) = (u1_struct_0 @ sk_D))),
% 1.94/2.17      inference('demod', [status(thm)], ['44', '56'])).
% 1.94/2.17  thf('70', plain,
% 1.94/2.17      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B_2))),
% 1.94/2.17      inference('demod', [status(thm)], ['68', '69'])).
% 1.94/2.17  thf('71', plain, ((l1_pre_topc @ sk_B_2)),
% 1.94/2.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.94/2.17  thf('72', plain, ((v2_pre_topc @ sk_B_2)),
% 1.94/2.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.94/2.17  thf('73', plain,
% 1.94/2.17      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.94/2.17         ((v2_struct_0 @ X0)
% 1.94/2.17          | ~ (v2_pre_topc @ X0)
% 1.94/2.17          | ~ (l1_pre_topc @ X0)
% 1.94/2.17          | (v2_struct_0 @ X1)
% 1.94/2.17          | ~ (m1_pre_topc @ X1 @ X0)
% 1.94/2.17          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1))
% 1.94/2.17          | (r1_tmap_1 @ sk_D @ sk_B_2 @ sk_E @ X2)
% 1.94/2.17          | ~ (r1_tmap_1 @ X1 @ sk_B_2 @ 
% 1.94/2.17               (k3_tmap_1 @ X0 @ sk_B_2 @ sk_D @ X1 @ sk_E) @ X2)
% 1.94/2.17          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ sk_C_1))
% 1.94/2.17          | ~ (m1_pre_topc @ X1 @ sk_D)
% 1.94/2.17          | ~ (v1_tsep_1 @ X1 @ sk_D)
% 1.94/2.17          | ~ (m1_pre_topc @ sk_D @ X0)
% 1.94/2.17          | (v2_struct_0 @ sk_D)
% 1.94/2.17          | (v2_struct_0 @ sk_B_2))),
% 1.94/2.17      inference('demod', [status(thm)], ['66', '67', '70', '71', '72'])).
% 1.94/2.17  thf('74', plain,
% 1.94/2.17      (((v2_struct_0 @ sk_B_2)
% 1.94/2.17        | (v2_struct_0 @ sk_D)
% 1.94/2.17        | ~ (m1_pre_topc @ sk_D @ sk_A)
% 1.94/2.17        | ~ (v1_tsep_1 @ sk_C_1 @ sk_D)
% 1.94/2.17        | ~ (m1_pre_topc @ sk_C_1 @ sk_D)
% 1.94/2.17        | ~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C_1))
% 1.94/2.17        | (r1_tmap_1 @ sk_D @ sk_B_2 @ sk_E @ sk_F)
% 1.94/2.17        | ~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C_1))
% 1.94/2.17        | ~ (m1_pre_topc @ sk_C_1 @ sk_A)
% 1.94/2.17        | (v2_struct_0 @ sk_C_1)
% 1.94/2.17        | ~ (l1_pre_topc @ sk_A)
% 1.94/2.17        | ~ (v2_pre_topc @ sk_A)
% 1.94/2.17        | (v2_struct_0 @ sk_A))),
% 1.94/2.17      inference('sup-', [status(thm)], ['3', '73'])).
% 1.94/2.17  thf('75', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 1.94/2.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.94/2.17  thf('76', plain,
% 1.94/2.17      (((g1_pre_topc @ (u1_struct_0 @ sk_C_1) @ (u1_pre_topc @ sk_C_1))
% 1.94/2.17         = (sk_D))),
% 1.94/2.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.94/2.17  thf('77', plain,
% 1.94/2.17      (![X0 : $i]:
% 1.94/2.17         ((m1_pre_topc @ X0 @ 
% 1.94/2.17           (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 1.94/2.17          | ~ (l1_pre_topc @ X0))),
% 1.94/2.17      inference('simplify', [status(thm)], ['37'])).
% 1.94/2.17  thf(t1_tsep_1, axiom,
% 1.94/2.17    (![A:$i]:
% 1.94/2.17     ( ( l1_pre_topc @ A ) =>
% 1.94/2.17       ( ![B:$i]:
% 1.94/2.17         ( ( m1_pre_topc @ B @ A ) =>
% 1.94/2.17           ( m1_subset_1 @
% 1.94/2.17             ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 1.94/2.17  thf('78', plain,
% 1.94/2.17      (![X41 : $i, X42 : $i]:
% 1.94/2.17         (~ (m1_pre_topc @ X41 @ X42)
% 1.94/2.17          | (m1_subset_1 @ (u1_struct_0 @ X41) @ 
% 1.94/2.17             (k1_zfmisc_1 @ (u1_struct_0 @ X42)))
% 1.94/2.17          | ~ (l1_pre_topc @ X42))),
% 1.94/2.17      inference('cnf', [status(esa)], [t1_tsep_1])).
% 1.94/2.17  thf('79', plain,
% 1.94/2.17      (![X0 : $i]:
% 1.94/2.17         (~ (l1_pre_topc @ X0)
% 1.94/2.17          | ~ (l1_pre_topc @ 
% 1.94/2.17               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 1.94/2.17          | (m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 1.94/2.17             (k1_zfmisc_1 @ 
% 1.94/2.17              (u1_struct_0 @ 
% 1.94/2.17               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))))),
% 1.94/2.17      inference('sup-', [status(thm)], ['77', '78'])).
% 1.94/2.17  thf('80', plain,
% 1.94/2.17      ((~ (l1_pre_topc @ sk_D)
% 1.94/2.17        | (m1_subset_1 @ (u1_struct_0 @ sk_C_1) @ 
% 1.94/2.17           (k1_zfmisc_1 @ 
% 1.94/2.17            (u1_struct_0 @ 
% 1.94/2.17             (g1_pre_topc @ (u1_struct_0 @ sk_C_1) @ (u1_pre_topc @ sk_C_1)))))
% 1.94/2.17        | ~ (l1_pre_topc @ sk_C_1))),
% 1.94/2.17      inference('sup-', [status(thm)], ['76', '79'])).
% 1.94/2.17  thf('81', plain, ((l1_pre_topc @ sk_D)),
% 1.94/2.17      inference('demod', [status(thm)], ['12', '13'])).
% 1.94/2.17  thf('82', plain,
% 1.94/2.17      (((g1_pre_topc @ (u1_struct_0 @ sk_C_1) @ (u1_pre_topc @ sk_C_1))
% 1.94/2.17         = (sk_D))),
% 1.94/2.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.94/2.17  thf('83', plain, ((l1_pre_topc @ sk_C_1)),
% 1.94/2.17      inference('demod', [status(thm)], ['18', '19'])).
% 1.94/2.17  thf('84', plain,
% 1.94/2.17      ((m1_subset_1 @ (u1_struct_0 @ sk_C_1) @ 
% 1.94/2.17        (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))),
% 1.94/2.17      inference('demod', [status(thm)], ['80', '81', '82', '83'])).
% 1.94/2.17  thf(t16_tsep_1, axiom,
% 1.94/2.17    (![A:$i]:
% 1.94/2.17     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.94/2.17       ( ![B:$i]:
% 1.94/2.17         ( ( m1_pre_topc @ B @ A ) =>
% 1.94/2.17           ( ![C:$i]:
% 1.94/2.17             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.94/2.17               ( ( ( C ) = ( u1_struct_0 @ B ) ) =>
% 1.94/2.17                 ( ( ( v1_tsep_1 @ B @ A ) & ( m1_pre_topc @ B @ A ) ) <=>
% 1.94/2.17                   ( v3_pre_topc @ C @ A ) ) ) ) ) ) ) ))).
% 1.94/2.17  thf('85', plain,
% 1.94/2.17      (![X38 : $i, X39 : $i, X40 : $i]:
% 1.94/2.17         (~ (m1_pre_topc @ X38 @ X39)
% 1.94/2.17          | ((X40) != (u1_struct_0 @ X38))
% 1.94/2.17          | ~ (v3_pre_topc @ X40 @ X39)
% 1.94/2.17          | (v1_tsep_1 @ X38 @ X39)
% 1.94/2.17          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (u1_struct_0 @ X39)))
% 1.94/2.17          | ~ (l1_pre_topc @ X39)
% 1.94/2.17          | ~ (v2_pre_topc @ X39))),
% 1.94/2.17      inference('cnf', [status(esa)], [t16_tsep_1])).
% 1.94/2.17  thf('86', plain,
% 1.94/2.17      (![X38 : $i, X39 : $i]:
% 1.94/2.17         (~ (v2_pre_topc @ X39)
% 1.94/2.17          | ~ (l1_pre_topc @ X39)
% 1.94/2.17          | ~ (m1_subset_1 @ (u1_struct_0 @ X38) @ 
% 1.94/2.17               (k1_zfmisc_1 @ (u1_struct_0 @ X39)))
% 1.94/2.17          | (v1_tsep_1 @ X38 @ X39)
% 1.94/2.17          | ~ (v3_pre_topc @ (u1_struct_0 @ X38) @ X39)
% 1.94/2.17          | ~ (m1_pre_topc @ X38 @ X39))),
% 1.94/2.17      inference('simplify', [status(thm)], ['85'])).
% 1.94/2.17  thf('87', plain,
% 1.94/2.17      ((~ (m1_pre_topc @ sk_C_1 @ sk_D)
% 1.94/2.17        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_C_1) @ sk_D)
% 1.94/2.17        | (v1_tsep_1 @ sk_C_1 @ sk_D)
% 1.94/2.17        | ~ (l1_pre_topc @ sk_D)
% 1.94/2.17        | ~ (v2_pre_topc @ sk_D))),
% 1.94/2.17      inference('sup-', [status(thm)], ['84', '86'])).
% 1.94/2.17  thf('88', plain, ((m1_pre_topc @ sk_C_1 @ sk_D)),
% 1.94/2.17      inference('demod', [status(thm)], ['39', '40'])).
% 1.94/2.17  thf('89', plain, ((l1_pre_topc @ sk_D)),
% 1.94/2.17      inference('demod', [status(thm)], ['12', '13'])).
% 1.94/2.17  thf('90', plain, ((v2_pre_topc @ sk_D)),
% 1.94/2.17      inference('demod', [status(thm)], ['30', '31', '32'])).
% 1.94/2.17  thf('91', plain,
% 1.94/2.17      ((~ (v3_pre_topc @ (u1_struct_0 @ sk_C_1) @ sk_D)
% 1.94/2.17        | (v1_tsep_1 @ sk_C_1 @ sk_D))),
% 1.94/2.17      inference('demod', [status(thm)], ['87', '88', '89', '90'])).
% 1.94/2.17  thf(d1_pre_topc, axiom,
% 1.94/2.17    (![A:$i]:
% 1.94/2.17     ( ( l1_pre_topc @ A ) =>
% 1.94/2.17       ( ( v2_pre_topc @ A ) <=>
% 1.94/2.17         ( ( ![B:$i]:
% 1.94/2.17             ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.94/2.17               ( ![C:$i]:
% 1.94/2.17                 ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.94/2.17                   ( ( ( r2_hidden @ C @ ( u1_pre_topc @ A ) ) & 
% 1.94/2.17                       ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) ) =>
% 1.94/2.17                     ( r2_hidden @
% 1.94/2.17                       ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ 
% 1.94/2.17                       ( u1_pre_topc @ A ) ) ) ) ) ) ) & 
% 1.94/2.17           ( ![B:$i]:
% 1.94/2.17             ( ( m1_subset_1 @
% 1.94/2.17                 B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 1.94/2.17               ( ( r1_tarski @ B @ ( u1_pre_topc @ A ) ) =>
% 1.94/2.17                 ( r2_hidden @
% 1.94/2.17                   ( k5_setfam_1 @ ( u1_struct_0 @ A ) @ B ) @ 
% 1.94/2.17                   ( u1_pre_topc @ A ) ) ) ) ) & 
% 1.94/2.17           ( r2_hidden @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ))).
% 1.94/2.17  thf(zf_stmt_1, type, zip_tseitin_5 : $i > $i > $o).
% 1.94/2.17  thf(zf_stmt_2, axiom,
% 1.94/2.17    (![B:$i,A:$i]:
% 1.94/2.17     ( ( zip_tseitin_5 @ B @ A ) <=>
% 1.94/2.17       ( ( m1_subset_1 @
% 1.94/2.17           B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 1.94/2.17         ( zip_tseitin_4 @ B @ A ) ) ))).
% 1.94/2.17  thf(zf_stmt_3, type, zip_tseitin_4 : $i > $i > $o).
% 1.94/2.17  thf(zf_stmt_4, axiom,
% 1.94/2.17    (![B:$i,A:$i]:
% 1.94/2.17     ( ( zip_tseitin_4 @ B @ A ) <=>
% 1.94/2.17       ( ( r1_tarski @ B @ ( u1_pre_topc @ A ) ) =>
% 1.94/2.17         ( r2_hidden @
% 1.94/2.17           ( k5_setfam_1 @ ( u1_struct_0 @ A ) @ B ) @ ( u1_pre_topc @ A ) ) ) ))).
% 1.94/2.17  thf(zf_stmt_5, type, zip_tseitin_3 : $i > $i > $o).
% 1.94/2.17  thf(zf_stmt_6, axiom,
% 1.94/2.17    (![B:$i,A:$i]:
% 1.94/2.17     ( ( zip_tseitin_3 @ B @ A ) <=>
% 1.94/2.17       ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.94/2.17         ( ![C:$i]: ( zip_tseitin_2 @ C @ B @ A ) ) ) ))).
% 1.94/2.17  thf(zf_stmt_7, type, zip_tseitin_2 : $i > $i > $i > $o).
% 1.94/2.17  thf(zf_stmt_8, axiom,
% 1.94/2.17    (![C:$i,B:$i,A:$i]:
% 1.94/2.17     ( ( zip_tseitin_2 @ C @ B @ A ) <=>
% 1.94/2.17       ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.94/2.17         ( zip_tseitin_1 @ C @ B @ A ) ) ))).
% 1.94/2.17  thf(zf_stmt_9, type, zip_tseitin_1 : $i > $i > $i > $o).
% 1.94/2.17  thf(zf_stmt_10, axiom,
% 1.94/2.17    (![C:$i,B:$i,A:$i]:
% 1.94/2.17     ( ( zip_tseitin_1 @ C @ B @ A ) <=>
% 1.94/2.17       ( ( zip_tseitin_0 @ C @ B @ A ) =>
% 1.94/2.17         ( r2_hidden @
% 1.94/2.17           ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ ( u1_pre_topc @ A ) ) ) ))).
% 1.94/2.17  thf(zf_stmt_11, type, zip_tseitin_0 : $i > $i > $i > $o).
% 1.94/2.17  thf(zf_stmt_12, axiom,
% 1.94/2.17    (![C:$i,B:$i,A:$i]:
% 1.94/2.17     ( ( zip_tseitin_0 @ C @ B @ A ) <=>
% 1.94/2.17       ( ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) & 
% 1.94/2.17         ( r2_hidden @ C @ ( u1_pre_topc @ A ) ) ) ))).
% 1.94/2.17  thf(zf_stmt_13, axiom,
% 1.94/2.17    (![A:$i]:
% 1.94/2.17     ( ( l1_pre_topc @ A ) =>
% 1.94/2.17       ( ( v2_pre_topc @ A ) <=>
% 1.94/2.17         ( ( r2_hidden @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) & 
% 1.94/2.17           ( ![B:$i]: ( zip_tseitin_5 @ B @ A ) ) & 
% 1.94/2.17           ( ![B:$i]: ( zip_tseitin_3 @ B @ A ) ) ) ) ))).
% 1.94/2.17  thf('92', plain,
% 1.94/2.17      (![X27 : $i]:
% 1.94/2.17         (~ (v2_pre_topc @ X27)
% 1.94/2.17          | (r2_hidden @ (u1_struct_0 @ X27) @ (u1_pre_topc @ X27))
% 1.94/2.17          | ~ (l1_pre_topc @ X27))),
% 1.94/2.17      inference('cnf', [status(esa)], [zf_stmt_13])).
% 1.94/2.17  thf('93', plain,
% 1.94/2.17      (![X43 : $i]: ((m1_pre_topc @ X43 @ X43) | ~ (l1_pre_topc @ X43))),
% 1.94/2.17      inference('cnf', [status(esa)], [t2_tsep_1])).
% 1.94/2.17  thf('94', plain,
% 1.94/2.17      (![X41 : $i, X42 : $i]:
% 1.94/2.17         (~ (m1_pre_topc @ X41 @ X42)
% 1.94/2.17          | (m1_subset_1 @ (u1_struct_0 @ X41) @ 
% 1.94/2.17             (k1_zfmisc_1 @ (u1_struct_0 @ X42)))
% 1.94/2.17          | ~ (l1_pre_topc @ X42))),
% 1.94/2.17      inference('cnf', [status(esa)], [t1_tsep_1])).
% 1.94/2.17  thf('95', plain,
% 1.94/2.17      (![X0 : $i]:
% 1.94/2.17         (~ (l1_pre_topc @ X0)
% 1.94/2.17          | ~ (l1_pre_topc @ X0)
% 1.94/2.17          | (m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 1.94/2.17             (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 1.94/2.17      inference('sup-', [status(thm)], ['93', '94'])).
% 1.94/2.17  thf('96', plain,
% 1.94/2.17      (![X0 : $i]:
% 1.94/2.17         ((m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 1.94/2.17           (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 1.94/2.17          | ~ (l1_pre_topc @ X0))),
% 1.94/2.17      inference('simplify', [status(thm)], ['95'])).
% 1.94/2.17  thf(d5_pre_topc, axiom,
% 1.94/2.17    (![A:$i]:
% 1.94/2.17     ( ( l1_pre_topc @ A ) =>
% 1.94/2.17       ( ![B:$i]:
% 1.94/2.17         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.94/2.17           ( ( v3_pre_topc @ B @ A ) <=>
% 1.94/2.17             ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) ) ) ) ))).
% 1.94/2.17  thf('97', plain,
% 1.94/2.17      (![X30 : $i, X31 : $i]:
% 1.94/2.17         (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ X31)))
% 1.94/2.17          | ~ (r2_hidden @ X30 @ (u1_pre_topc @ X31))
% 1.94/2.17          | (v3_pre_topc @ X30 @ X31)
% 1.94/2.17          | ~ (l1_pre_topc @ X31))),
% 1.94/2.17      inference('cnf', [status(esa)], [d5_pre_topc])).
% 1.94/2.17  thf('98', plain,
% 1.94/2.17      (![X0 : $i]:
% 1.94/2.17         (~ (l1_pre_topc @ X0)
% 1.94/2.17          | ~ (l1_pre_topc @ X0)
% 1.94/2.17          | (v3_pre_topc @ (u1_struct_0 @ X0) @ X0)
% 1.94/2.17          | ~ (r2_hidden @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))),
% 1.94/2.17      inference('sup-', [status(thm)], ['96', '97'])).
% 1.94/2.17  thf('99', plain,
% 1.94/2.17      (![X0 : $i]:
% 1.94/2.17         (~ (r2_hidden @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))
% 1.94/2.17          | (v3_pre_topc @ (u1_struct_0 @ X0) @ X0)
% 1.94/2.17          | ~ (l1_pre_topc @ X0))),
% 1.94/2.17      inference('simplify', [status(thm)], ['98'])).
% 1.94/2.17  thf('100', plain,
% 1.94/2.17      (![X0 : $i]:
% 1.94/2.17         (~ (l1_pre_topc @ X0)
% 1.94/2.17          | ~ (v2_pre_topc @ X0)
% 1.94/2.17          | ~ (l1_pre_topc @ X0)
% 1.94/2.17          | (v3_pre_topc @ (u1_struct_0 @ X0) @ X0))),
% 1.94/2.17      inference('sup-', [status(thm)], ['92', '99'])).
% 1.94/2.17  thf('101', plain,
% 1.94/2.17      (![X0 : $i]:
% 1.94/2.17         ((v3_pre_topc @ (u1_struct_0 @ X0) @ X0)
% 1.94/2.17          | ~ (v2_pre_topc @ X0)
% 1.94/2.17          | ~ (l1_pre_topc @ X0))),
% 1.94/2.17      inference('simplify', [status(thm)], ['100'])).
% 1.94/2.17  thf('102', plain, ((m1_pre_topc @ sk_D @ sk_C_1)),
% 1.94/2.17      inference('demod', [status(thm)], ['9', '14', '15', '20'])).
% 1.94/2.17  thf('103', plain,
% 1.94/2.17      (![X36 : $i, X37 : $i]:
% 1.94/2.17         (~ (l1_pre_topc @ X36)
% 1.94/2.17          | ~ (m1_pre_topc @ X37 @ X36)
% 1.94/2.17          | (m1_pre_topc @ X37 @ 
% 1.94/2.17             (g1_pre_topc @ (u1_struct_0 @ X36) @ (u1_pre_topc @ X36)))
% 1.94/2.17          | ~ (l1_pre_topc @ X37))),
% 1.94/2.17      inference('cnf', [status(esa)], [t65_pre_topc])).
% 1.94/2.17  thf('104', plain,
% 1.94/2.17      ((~ (l1_pre_topc @ sk_D)
% 1.94/2.17        | (m1_pre_topc @ sk_D @ 
% 1.94/2.17           (g1_pre_topc @ (u1_struct_0 @ sk_C_1) @ (u1_pre_topc @ sk_C_1)))
% 1.94/2.17        | ~ (l1_pre_topc @ sk_C_1))),
% 1.94/2.17      inference('sup-', [status(thm)], ['102', '103'])).
% 1.94/2.17  thf('105', plain, ((l1_pre_topc @ sk_D)),
% 1.94/2.17      inference('demod', [status(thm)], ['12', '13'])).
% 1.94/2.17  thf('106', plain,
% 1.94/2.17      (((g1_pre_topc @ (u1_struct_0 @ sk_C_1) @ (u1_pre_topc @ sk_C_1))
% 1.94/2.17         = (sk_D))),
% 1.94/2.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.94/2.17  thf('107', plain, ((l1_pre_topc @ sk_C_1)),
% 1.94/2.17      inference('demod', [status(thm)], ['18', '19'])).
% 1.94/2.17  thf('108', plain, ((m1_pre_topc @ sk_D @ sk_D)),
% 1.94/2.17      inference('demod', [status(thm)], ['104', '105', '106', '107'])).
% 1.94/2.17  thf('109', plain,
% 1.94/2.17      (![X41 : $i, X42 : $i]:
% 1.94/2.17         (~ (m1_pre_topc @ X41 @ X42)
% 1.94/2.17          | (m1_subset_1 @ (u1_struct_0 @ X41) @ 
% 1.94/2.17             (k1_zfmisc_1 @ (u1_struct_0 @ X42)))
% 1.94/2.17          | ~ (l1_pre_topc @ X42))),
% 1.94/2.17      inference('cnf', [status(esa)], [t1_tsep_1])).
% 1.94/2.17  thf('110', plain,
% 1.94/2.17      ((~ (l1_pre_topc @ sk_D)
% 1.94/2.17        | (m1_subset_1 @ (u1_struct_0 @ sk_D) @ 
% 1.94/2.17           (k1_zfmisc_1 @ (u1_struct_0 @ sk_D))))),
% 1.94/2.17      inference('sup-', [status(thm)], ['108', '109'])).
% 1.94/2.17  thf('111', plain, ((l1_pre_topc @ sk_D)),
% 1.94/2.17      inference('demod', [status(thm)], ['12', '13'])).
% 1.94/2.17  thf('112', plain,
% 1.94/2.17      ((m1_subset_1 @ (u1_struct_0 @ sk_D) @ 
% 1.94/2.17        (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))),
% 1.94/2.17      inference('demod', [status(thm)], ['110', '111'])).
% 1.94/2.17  thf('113', plain,
% 1.94/2.17      (![X30 : $i, X31 : $i]:
% 1.94/2.17         (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ X31)))
% 1.94/2.17          | ~ (v3_pre_topc @ X30 @ X31)
% 1.94/2.17          | (r2_hidden @ X30 @ (u1_pre_topc @ X31))
% 1.94/2.17          | ~ (l1_pre_topc @ X31))),
% 1.94/2.17      inference('cnf', [status(esa)], [d5_pre_topc])).
% 1.94/2.17  thf('114', plain,
% 1.94/2.17      ((~ (l1_pre_topc @ sk_D)
% 1.94/2.17        | (r2_hidden @ (u1_struct_0 @ sk_D) @ (u1_pre_topc @ sk_D))
% 1.94/2.17        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_D) @ sk_D))),
% 1.94/2.17      inference('sup-', [status(thm)], ['112', '113'])).
% 1.94/2.17  thf('115', plain, ((l1_pre_topc @ sk_D)),
% 1.94/2.17      inference('demod', [status(thm)], ['12', '13'])).
% 1.94/2.17  thf('116', plain,
% 1.94/2.17      (((r2_hidden @ (u1_struct_0 @ sk_D) @ (u1_pre_topc @ sk_D))
% 1.94/2.17        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_D) @ sk_D))),
% 1.94/2.17      inference('demod', [status(thm)], ['114', '115'])).
% 1.94/2.17  thf('117', plain,
% 1.94/2.17      ((~ (l1_pre_topc @ sk_D)
% 1.94/2.17        | ~ (v2_pre_topc @ sk_D)
% 1.94/2.17        | (r2_hidden @ (u1_struct_0 @ sk_D) @ (u1_pre_topc @ sk_D)))),
% 1.94/2.17      inference('sup-', [status(thm)], ['101', '116'])).
% 1.94/2.17  thf('118', plain, ((l1_pre_topc @ sk_D)),
% 1.94/2.17      inference('demod', [status(thm)], ['12', '13'])).
% 1.94/2.17  thf('119', plain, ((v2_pre_topc @ sk_D)),
% 1.94/2.17      inference('demod', [status(thm)], ['30', '31', '32'])).
% 1.94/2.17  thf('120', plain,
% 1.94/2.17      ((r2_hidden @ (u1_struct_0 @ sk_D) @ (u1_pre_topc @ sk_D))),
% 1.94/2.17      inference('demod', [status(thm)], ['117', '118', '119'])).
% 1.94/2.17  thf('121', plain,
% 1.94/2.17      (![X0 : $i]:
% 1.94/2.17         (~ (r2_hidden @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))
% 1.94/2.17          | (v3_pre_topc @ (u1_struct_0 @ X0) @ X0)
% 1.94/2.17          | ~ (l1_pre_topc @ X0))),
% 1.94/2.17      inference('simplify', [status(thm)], ['98'])).
% 1.94/2.17  thf('122', plain,
% 1.94/2.17      ((~ (l1_pre_topc @ sk_D) | (v3_pre_topc @ (u1_struct_0 @ sk_D) @ sk_D))),
% 1.94/2.17      inference('sup-', [status(thm)], ['120', '121'])).
% 1.94/2.17  thf('123', plain, ((l1_pre_topc @ sk_D)),
% 1.94/2.17      inference('demod', [status(thm)], ['12', '13'])).
% 1.94/2.17  thf('124', plain, ((v3_pre_topc @ (u1_struct_0 @ sk_D) @ sk_D)),
% 1.94/2.17      inference('demod', [status(thm)], ['122', '123'])).
% 1.94/2.17  thf('125', plain, (((u1_struct_0 @ sk_C_1) = (u1_struct_0 @ sk_D))),
% 1.94/2.17      inference('demod', [status(thm)], ['44', '56'])).
% 1.94/2.17  thf('126', plain, ((v3_pre_topc @ (u1_struct_0 @ sk_C_1) @ sk_D)),
% 1.94/2.17      inference('demod', [status(thm)], ['124', '125'])).
% 1.94/2.17  thf('127', plain, ((v1_tsep_1 @ sk_C_1 @ sk_D)),
% 1.94/2.17      inference('demod', [status(thm)], ['91', '126'])).
% 1.94/2.17  thf('128', plain, ((m1_pre_topc @ sk_C_1 @ sk_D)),
% 1.94/2.17      inference('demod', [status(thm)], ['39', '40'])).
% 1.94/2.17  thf('129', plain, ((m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_C_1))),
% 1.94/2.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.94/2.17  thf('130', plain, (((sk_F) = (sk_G))),
% 1.94/2.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.94/2.17  thf('131', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C_1))),
% 1.94/2.17      inference('demod', [status(thm)], ['129', '130'])).
% 1.94/2.17  thf('132', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C_1))),
% 1.94/2.17      inference('demod', [status(thm)], ['129', '130'])).
% 1.94/2.17  thf('133', plain, ((m1_pre_topc @ sk_C_1 @ sk_A)),
% 1.94/2.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.94/2.17  thf('134', plain, ((l1_pre_topc @ sk_A)),
% 1.94/2.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.94/2.17  thf('135', plain, ((v2_pre_topc @ sk_A)),
% 1.94/2.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.94/2.17  thf('136', plain,
% 1.94/2.17      (((v2_struct_0 @ sk_B_2)
% 1.94/2.17        | (v2_struct_0 @ sk_D)
% 1.94/2.17        | (r1_tmap_1 @ sk_D @ sk_B_2 @ sk_E @ sk_F)
% 1.94/2.17        | (v2_struct_0 @ sk_C_1)
% 1.94/2.17        | (v2_struct_0 @ sk_A))),
% 1.94/2.17      inference('demod', [status(thm)],
% 1.94/2.17                ['74', '75', '127', '128', '131', '132', '133', '134', '135'])).
% 1.94/2.17  thf('137', plain, (~ (r1_tmap_1 @ sk_D @ sk_B_2 @ sk_E @ sk_F)),
% 1.94/2.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.94/2.17  thf('138', plain,
% 1.94/2.17      (((v2_struct_0 @ sk_A)
% 1.94/2.17        | (v2_struct_0 @ sk_C_1)
% 1.94/2.17        | (v2_struct_0 @ sk_D)
% 1.94/2.17        | (v2_struct_0 @ sk_B_2))),
% 1.94/2.17      inference('sup-', [status(thm)], ['136', '137'])).
% 1.94/2.17  thf('139', plain, (~ (v2_struct_0 @ sk_D)),
% 1.94/2.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.94/2.17  thf('140', plain,
% 1.94/2.17      (((v2_struct_0 @ sk_B_2) | (v2_struct_0 @ sk_C_1) | (v2_struct_0 @ sk_A))),
% 1.94/2.17      inference('sup-', [status(thm)], ['138', '139'])).
% 1.94/2.17  thf('141', plain, (~ (v2_struct_0 @ sk_B_2)),
% 1.94/2.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.94/2.17  thf('142', plain, (((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_C_1))),
% 1.94/2.17      inference('clc', [status(thm)], ['140', '141'])).
% 1.94/2.17  thf('143', plain, (~ (v2_struct_0 @ sk_A)),
% 1.94/2.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.94/2.17  thf('144', plain, ((v2_struct_0 @ sk_C_1)),
% 1.94/2.17      inference('clc', [status(thm)], ['142', '143'])).
% 1.94/2.17  thf('145', plain, ($false), inference('demod', [status(thm)], ['0', '144'])).
% 1.94/2.17  
% 1.94/2.17  % SZS output end Refutation
% 1.94/2.17  
% 1.94/2.18  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
