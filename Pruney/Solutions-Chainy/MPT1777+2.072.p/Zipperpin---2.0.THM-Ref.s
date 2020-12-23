%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.8VlFTQrJ5Z

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:10:38 EST 2020

% Result     : Theorem 0.77s
% Output     : Refutation 0.77s
% Verified   : 
% Statistics : Number of formulae       :  208 (1051 expanded)
%              Number of leaves         :   42 ( 313 expanded)
%              Depth                    :   28
%              Number of atoms          : 1819 (36467 expanded)
%              Number of equality atoms :   36 (1050 expanded)
%              Maximal formula depth    :   29 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(v1_tsep_1_type,type,(
    v1_tsep_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(g1_pre_topc_type,type,(
    g1_pre_topc: $i > $i > $i )).

thf(r1_tmap_1_type,type,(
    r1_tmap_1: $i > $i > $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_tsep_1_type,type,(
    k1_tsep_1: $i > $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(sk_G_type,type,(
    sk_G: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

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

thf('5',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i,X36: $i,X37: $i,X38: $i] :
      ( ( v2_struct_0 @ X32 )
      | ~ ( v2_pre_topc @ X32 )
      | ~ ( l1_pre_topc @ X32 )
      | ( v2_struct_0 @ X33 )
      | ~ ( m1_pre_topc @ X33 @ X34 )
      | ~ ( v1_tsep_1 @ X35 @ X33 )
      | ~ ( m1_pre_topc @ X35 @ X33 )
      | ~ ( m1_subset_1 @ X36 @ ( u1_struct_0 @ X33 ) )
      | ( X36 != X37 )
      | ~ ( r1_tmap_1 @ X35 @ X32 @ ( k3_tmap_1 @ X34 @ X32 @ X33 @ X35 @ X38 ) @ X37 )
      | ( r1_tmap_1 @ X33 @ X32 @ X38 @ X36 )
      | ~ ( m1_subset_1 @ X37 @ ( u1_struct_0 @ X35 ) )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X33 ) @ ( u1_struct_0 @ X32 ) ) ) )
      | ~ ( v1_funct_2 @ X38 @ ( u1_struct_0 @ X33 ) @ ( u1_struct_0 @ X32 ) )
      | ~ ( v1_funct_1 @ X38 )
      | ~ ( m1_pre_topc @ X35 @ X34 )
      | ( v2_struct_0 @ X35 )
      | ~ ( l1_pre_topc @ X34 )
      | ~ ( v2_pre_topc @ X34 )
      | ( v2_struct_0 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t86_tmap_1])).

thf('6',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i,X37: $i,X38: $i] :
      ( ( v2_struct_0 @ X34 )
      | ~ ( v2_pre_topc @ X34 )
      | ~ ( l1_pre_topc @ X34 )
      | ( v2_struct_0 @ X35 )
      | ~ ( m1_pre_topc @ X35 @ X34 )
      | ~ ( v1_funct_1 @ X38 )
      | ~ ( v1_funct_2 @ X38 @ ( u1_struct_0 @ X33 ) @ ( u1_struct_0 @ X32 ) )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X33 ) @ ( u1_struct_0 @ X32 ) ) ) )
      | ~ ( m1_subset_1 @ X37 @ ( u1_struct_0 @ X35 ) )
      | ( r1_tmap_1 @ X33 @ X32 @ X38 @ X37 )
      | ~ ( r1_tmap_1 @ X35 @ X32 @ ( k3_tmap_1 @ X34 @ X32 @ X33 @ X35 @ X38 ) @ X37 )
      | ~ ( m1_subset_1 @ X37 @ ( u1_struct_0 @ X33 ) )
      | ~ ( m1_pre_topc @ X35 @ X33 )
      | ~ ( v1_tsep_1 @ X35 @ X33 )
      | ~ ( m1_pre_topc @ X33 @ X34 )
      | ( v2_struct_0 @ X33 )
      | ~ ( l1_pre_topc @ X32 )
      | ~ ( v2_pre_topc @ X32 )
      | ( v2_struct_0 @ X32 ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ~ ( v1_tsep_1 @ X1 @ sk_D )
      | ~ ( m1_pre_topc @ X1 @ sk_D )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ sk_D ) )
      | ~ ( r1_tmap_1 @ X1 @ sk_B @ ( k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E ) @ X2 )
      | ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X1 ) )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ( v2_struct_0 @ X1 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','6'])).

thf('8',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ~ ( v1_tsep_1 @ X1 @ sk_D )
      | ~ ( m1_pre_topc @ X1 @ sk_D )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ sk_D ) )
      | ~ ( r1_tmap_1 @ X1 @ sk_B @ ( k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E ) @ X2 )
      | ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X1 ) )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ( v2_struct_0 @ X1 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['7','8','9','10','11'])).

thf('13',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ~ ( m1_pre_topc @ sk_C @ sk_A )
    | ~ ( m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_C ) )
    | ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F )
    | ~ ( m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_D ) )
    | ~ ( m1_pre_topc @ sk_C @ sk_D )
    | ~ ( v1_tsep_1 @ sk_C @ sk_D )
    | ~ ( m1_pre_topc @ sk_D @ sk_A )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['3','12'])).

thf('14',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    sk_F = sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
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

thf('23',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( v2_struct_0 @ X21 )
      | ~ ( m1_pre_topc @ X21 @ X22 )
      | ( m1_pre_topc @ X21 @ ( k1_tsep_1 @ X22 @ X21 @ X23 ) )
      | ~ ( m1_pre_topc @ X23 @ X22 )
      | ( v2_struct_0 @ X23 )
      | ~ ( l1_pre_topc @ X22 )
      | ~ ( v2_pre_topc @ X22 )
      | ( v2_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t22_tsep_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( m1_pre_topc @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_C @ X0 ) )
      | ( v2_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( m1_pre_topc @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_C @ X0 ) )
      | ( v2_struct_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['24','25','26'])).

thf('28',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( m1_pre_topc @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_C ) )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['21','27'])).

thf('29',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_pre_topc @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_C ) )
    | ( v2_struct_0 @ sk_C ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( m1_pre_topc @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_C ) ) ),
    inference(clc,[status(thm)],['29','30'])).

thf('32',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    m1_pre_topc @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_C ) ),
    inference(clc,[status(thm)],['31','32'])).

thf('34',plain,(
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

thf('35',plain,(
    ! [X27: $i,X28: $i] :
      ( ( v2_struct_0 @ X27 )
      | ~ ( m1_pre_topc @ X27 @ X28 )
      | ( ( k1_tsep_1 @ X28 @ X27 @ X27 )
        = ( g1_pre_topc @ ( u1_struct_0 @ X27 ) @ ( u1_pre_topc @ X27 ) ) )
      | ~ ( l1_pre_topc @ X28 )
      | ~ ( v2_pre_topc @ X28 )
      | ( v2_struct_0 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t25_tmap_1])).

thf('36',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tsep_1 @ sk_A @ sk_C @ sk_C )
      = ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) ) )
    | ( v2_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) )
    = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k1_tsep_1 @ sk_A @ sk_C @ sk_C )
      = sk_D )
    | ( v2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['36','37','38','39'])).

thf('41',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( ( k1_tsep_1 @ sk_A @ sk_C @ sk_C )
      = sk_D ) ),
    inference(clc,[status(thm)],['40','41'])).

thf('43',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,
    ( ( k1_tsep_1 @ sk_A @ sk_C @ sk_C )
    = sk_D ),
    inference(clc,[status(thm)],['42','43'])).

thf('45',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(demod,[status(thm)],['33','44'])).

thf('46',plain,(
    m1_pre_topc @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_C ) ),
    inference(clc,[status(thm)],['31','32'])).

thf(t1_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( m1_subset_1 @ ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('47',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( m1_pre_topc @ X19 @ X20 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X19 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ~ ( l1_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('48',plain,
    ( ~ ( l1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_C ) )
    | ( m1_subset_1 @ ( u1_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,
    ( ( k1_tsep_1 @ sk_A @ sk_C @ sk_C )
    = sk_D ),
    inference(clc,[status(thm)],['42','43'])).

thf('50',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('51',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( m1_pre_topc @ X4 @ X5 )
      | ( l1_pre_topc @ X4 )
      | ~ ( l1_pre_topc @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('52',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_D ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,
    ( ( k1_tsep_1 @ sk_A @ sk_C @ sk_C )
    = sk_D ),
    inference(clc,[status(thm)],['42','43'])).

thf('56',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['48','49','54','55'])).

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

thf('57',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_pre_topc @ X16 @ X17 )
      | ( X18
       != ( u1_struct_0 @ X16 ) )
      | ~ ( v3_pre_topc @ X18 @ X17 )
      | ( v1_tsep_1 @ X16 @ X17 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ~ ( l1_pre_topc @ X17 )
      | ~ ( v2_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[t16_tsep_1])).

thf('58',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( v2_pre_topc @ X17 )
      | ~ ( l1_pre_topc @ X17 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X16 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ( v1_tsep_1 @ X16 @ X17 )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ X16 ) @ X17 )
      | ~ ( m1_pre_topc @ X16 @ X17 ) ) ),
    inference(simplify,[status(thm)],['57'])).

thf('59',plain,
    ( ~ ( m1_pre_topc @ sk_C @ sk_D )
    | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_C ) @ sk_D )
    | ( v1_tsep_1 @ sk_C @ sk_D )
    | ~ ( l1_pre_topc @ sk_D )
    | ~ ( v2_pre_topc @ sk_D ) ),
    inference('sup-',[status(thm)],['56','58'])).

thf('60',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(demod,[status(thm)],['33','44'])).

thf('61',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['52','53'])).

thf('62',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( v2_pre_topc @ B ) ) ) )).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_pre_topc @ X0 @ X1 )
      | ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v2_pre_topc @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc1_pre_topc])).

thf('64',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_pre_topc @ sk_D ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    v2_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['64','65','66'])).

thf('68',plain,
    ( ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_C ) @ sk_D )
    | ( v1_tsep_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['59','60','61','67'])).

thf('69',plain,
    ( ( k1_tsep_1 @ sk_A @ sk_C @ sk_C )
    = sk_D ),
    inference(clc,[status(thm)],['42','43'])).

thf('70',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) )
    = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t23_tsep_1,axiom,(
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
             => ( ( m1_pre_topc @ B @ C )
              <=> ( ( k1_tsep_1 @ A @ B @ C )
                  = ( g1_pre_topc @ ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) ) ) ) ) ) ) )).

thf('72',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( v2_struct_0 @ X24 )
      | ~ ( m1_pre_topc @ X24 @ X25 )
      | ( ( k1_tsep_1 @ X25 @ X24 @ X26 )
       != ( g1_pre_topc @ ( u1_struct_0 @ X26 ) @ ( u1_pre_topc @ X26 ) ) )
      | ( m1_pre_topc @ X24 @ X26 )
      | ~ ( m1_pre_topc @ X26 @ X25 )
      | ( v2_struct_0 @ X26 )
      | ~ ( l1_pre_topc @ X25 )
      | ~ ( v2_pre_topc @ X25 )
      | ( v2_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t23_tsep_1])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_tsep_1 @ X1 @ X0 @ sk_C )
       != sk_D )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ sk_C )
      | ~ ( m1_pre_topc @ sk_C @ X1 )
      | ( m1_pre_topc @ X0 @ sk_C )
      | ~ ( m1_pre_topc @ X0 @ X1 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( m1_pre_topc @ X0 @ sk_C )
      | ( v2_struct_0 @ sk_C )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( ( k1_tsep_1 @ sk_A @ X0 @ sk_C )
       != sk_D ) ) ),
    inference('sup-',[status(thm)],['70','73'])).

thf('75',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( m1_pre_topc @ X0 @ sk_C )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( ( k1_tsep_1 @ sk_A @ X0 @ sk_C )
       != sk_D ) ) ),
    inference(demod,[status(thm)],['74','75','76'])).

thf('78',plain,
    ( ( sk_D != sk_D )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( m1_pre_topc @ sk_C @ sk_C )
    | ~ ( m1_pre_topc @ sk_C @ sk_A )
    | ( v2_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['69','77'])).

thf('79',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,
    ( ( sk_D != sk_D )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( m1_pre_topc @ sk_C @ sk_C )
    | ( v2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['78','79'])).

thf('81',plain,
    ( ( m1_pre_topc @ sk_C @ sk_C )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['80'])).

thf('82',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_pre_topc @ sk_C @ sk_C ) ),
    inference(clc,[status(thm)],['81','82'])).

thf('84',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    m1_pre_topc @ sk_C @ sk_C ),
    inference(clc,[status(thm)],['83','84'])).

thf(t11_tmap_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( ( v1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) )
            & ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) @ A ) ) ) ) )).

thf('86',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( m1_pre_topc @ X14 @ X15 )
      | ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X14 ) @ ( u1_pre_topc @ X14 ) ) @ X15 )
      | ~ ( l1_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[t11_tmap_1])).

thf('87',plain,
    ( ~ ( l1_pre_topc @ sk_C )
    | ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) ) @ sk_C ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( m1_pre_topc @ X4 @ X5 )
      | ( l1_pre_topc @ X4 )
      | ~ ( l1_pre_topc @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('90',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_C ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['90','91'])).

thf('93',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) )
    = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    m1_pre_topc @ sk_D @ sk_C ),
    inference(demod,[status(thm)],['87','92','93'])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('95',plain,(
    ! [X2: $i] :
      ( ( ( k2_struct_0 @ X2 )
        = ( u1_struct_0 @ X2 ) )
      | ~ ( l1_struct_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('96',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['48','49','54','55'])).

thf('97',plain,
    ( ( m1_subset_1 @ ( k2_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) )
    | ~ ( l1_struct_0 @ sk_C ) ),
    inference('sup+',[status(thm)],['95','96'])).

thf('98',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['90','91'])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('99',plain,(
    ! [X3: $i] :
      ( ( l1_struct_0 @ X3 )
      | ~ ( l1_pre_topc @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('100',plain,(
    l1_struct_0 @ sk_C ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,(
    m1_subset_1 @ ( k2_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['97','100'])).

thf(t39_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) )
             => ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) )).

thf('102',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( m1_pre_topc @ X6 @ X7 )
      | ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[t39_pre_topc])).

thf('103',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( m1_subset_1 @ ( k2_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,
    ( ( m1_subset_1 @ ( k2_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C ) ) )
    | ~ ( l1_pre_topc @ sk_C ) ),
    inference('sup-',[status(thm)],['94','103'])).

thf('105',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['90','91'])).

thf('106',plain,(
    m1_subset_1 @ ( k2_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['104','105'])).

thf('107',plain,(
    ! [X2: $i] :
      ( ( ( k2_struct_0 @ X2 )
        = ( u1_struct_0 @ X2 ) )
      | ~ ( l1_struct_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('108',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['48','49','54','55'])).

thf(t33_tops_2,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_pre_topc @ C @ A )
             => ( ( v3_pre_topc @ B @ A )
               => ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ C ) ) )
                   => ( ( D = B )
                     => ( v3_pre_topc @ D @ C ) ) ) ) ) ) ) )).

thf('109',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ~ ( v3_pre_topc @ X10 @ X11 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ( v3_pre_topc @ X12 @ X13 )
      | ( X12 != X10 )
      | ~ ( m1_pre_topc @ X13 @ X11 )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[t33_tops_2])).

thf('110',plain,(
    ! [X10: $i,X11: $i,X13: $i] :
      ( ~ ( l1_pre_topc @ X11 )
      | ~ ( m1_pre_topc @ X13 @ X11 )
      | ( v3_pre_topc @ X10 @ X13 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ~ ( v3_pre_topc @ X10 @ X11 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) ) ) ),
    inference(simplify,[status(thm)],['109'])).

thf('111',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_C ) @ X0 )
      | ( v3_pre_topc @ ( u1_struct_0 @ sk_C ) @ sk_D )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['108','110'])).

thf('112',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ ( k2_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_struct_0 @ sk_C )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ( v3_pre_topc @ ( u1_struct_0 @ sk_C ) @ sk_D )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_C ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['107','111'])).

thf('113',plain,(
    l1_struct_0 @ sk_C ),
    inference('sup-',[status(thm)],['98','99'])).

thf('114',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ ( k2_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ( v3_pre_topc @ ( u1_struct_0 @ sk_C ) @ sk_D )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_C ) @ X0 ) ) ),
    inference(demod,[status(thm)],['112','113'])).

thf('115',plain,
    ( ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_C ) @ sk_C )
    | ( v3_pre_topc @ ( u1_struct_0 @ sk_C ) @ sk_D )
    | ~ ( m1_pre_topc @ sk_D @ sk_C )
    | ~ ( l1_pre_topc @ sk_C ) ),
    inference('sup-',[status(thm)],['106','114'])).

thf('116',plain,(
    m1_pre_topc @ sk_C @ sk_C ),
    inference(clc,[status(thm)],['83','84'])).

thf('117',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( m1_pre_topc @ X19 @ X20 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X19 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ~ ( l1_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('118',plain,
    ( ~ ( l1_pre_topc @ sk_C )
    | ( m1_subset_1 @ ( u1_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['116','117'])).

thf('119',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['90','91'])).

thf('120',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['118','119'])).

thf('121',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_pre_topc @ X16 @ X17 )
      | ( X18
       != ( u1_struct_0 @ X16 ) )
      | ~ ( v1_tsep_1 @ X16 @ X17 )
      | ~ ( m1_pre_topc @ X16 @ X17 )
      | ( v3_pre_topc @ X18 @ X17 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ~ ( l1_pre_topc @ X17 )
      | ~ ( v2_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[t16_tsep_1])).

thf('122',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( v2_pre_topc @ X17 )
      | ~ ( l1_pre_topc @ X17 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X16 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ( v3_pre_topc @ ( u1_struct_0 @ X16 ) @ X17 )
      | ~ ( v1_tsep_1 @ X16 @ X17 )
      | ~ ( m1_pre_topc @ X16 @ X17 ) ) ),
    inference(simplify,[status(thm)],['121'])).

thf('123',plain,
    ( ~ ( m1_pre_topc @ sk_C @ sk_C )
    | ~ ( v1_tsep_1 @ sk_C @ sk_C )
    | ( v3_pre_topc @ ( u1_struct_0 @ sk_C ) @ sk_C )
    | ~ ( l1_pre_topc @ sk_C )
    | ~ ( v2_pre_topc @ sk_C ) ),
    inference('sup-',[status(thm)],['120','122'])).

thf('124',plain,(
    m1_pre_topc @ sk_C @ sk_C ),
    inference(clc,[status(thm)],['83','84'])).

thf('125',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['90','91'])).

thf('126',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_pre_topc @ X0 @ X1 )
      | ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v2_pre_topc @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc1_pre_topc])).

thf('128',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_pre_topc @ sk_C ) ),
    inference('sup-',[status(thm)],['126','127'])).

thf('129',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('130',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('131',plain,(
    v2_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['128','129','130'])).

thf('132',plain,
    ( ~ ( v1_tsep_1 @ sk_C @ sk_C )
    | ( v3_pre_topc @ ( u1_struct_0 @ sk_C ) @ sk_C ) ),
    inference(demod,[status(thm)],['123','124','125','131'])).

thf(fc10_tops_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( v3_pre_topc @ ( k2_struct_0 @ A ) @ A ) ) )).

thf('133',plain,(
    ! [X9: $i] :
      ( ( v3_pre_topc @ ( k2_struct_0 @ X9 ) @ X9 )
      | ~ ( l1_pre_topc @ X9 )
      | ~ ( v2_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[fc10_tops_1])).

thf('134',plain,(
    ! [X2: $i] :
      ( ( ( k2_struct_0 @ X2 )
        = ( u1_struct_0 @ X2 ) )
      | ~ ( l1_struct_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('135',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['118','119'])).

thf('136',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( v2_pre_topc @ X17 )
      | ~ ( l1_pre_topc @ X17 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X16 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ( v1_tsep_1 @ X16 @ X17 )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ X16 ) @ X17 )
      | ~ ( m1_pre_topc @ X16 @ X17 ) ) ),
    inference(simplify,[status(thm)],['57'])).

thf('137',plain,
    ( ~ ( m1_pre_topc @ sk_C @ sk_C )
    | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_C ) @ sk_C )
    | ( v1_tsep_1 @ sk_C @ sk_C )
    | ~ ( l1_pre_topc @ sk_C )
    | ~ ( v2_pre_topc @ sk_C ) ),
    inference('sup-',[status(thm)],['135','136'])).

thf('138',plain,(
    m1_pre_topc @ sk_C @ sk_C ),
    inference(clc,[status(thm)],['83','84'])).

thf('139',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['90','91'])).

thf('140',plain,(
    v2_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['128','129','130'])).

thf('141',plain,
    ( ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_C ) @ sk_C )
    | ( v1_tsep_1 @ sk_C @ sk_C ) ),
    inference(demod,[status(thm)],['137','138','139','140'])).

thf('142',plain,
    ( ~ ( v3_pre_topc @ ( k2_struct_0 @ sk_C ) @ sk_C )
    | ~ ( l1_struct_0 @ sk_C )
    | ( v1_tsep_1 @ sk_C @ sk_C ) ),
    inference('sup-',[status(thm)],['134','141'])).

thf('143',plain,(
    l1_struct_0 @ sk_C ),
    inference('sup-',[status(thm)],['98','99'])).

thf('144',plain,
    ( ~ ( v3_pre_topc @ ( k2_struct_0 @ sk_C ) @ sk_C )
    | ( v1_tsep_1 @ sk_C @ sk_C ) ),
    inference(demod,[status(thm)],['142','143'])).

thf('145',plain,
    ( ~ ( v2_pre_topc @ sk_C )
    | ~ ( l1_pre_topc @ sk_C )
    | ( v1_tsep_1 @ sk_C @ sk_C ) ),
    inference('sup-',[status(thm)],['133','144'])).

thf('146',plain,(
    v2_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['128','129','130'])).

thf('147',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['90','91'])).

thf('148',plain,(
    v1_tsep_1 @ sk_C @ sk_C ),
    inference(demod,[status(thm)],['145','146','147'])).

thf('149',plain,(
    v3_pre_topc @ ( u1_struct_0 @ sk_C ) @ sk_C ),
    inference(demod,[status(thm)],['132','148'])).

thf('150',plain,(
    m1_pre_topc @ sk_D @ sk_C ),
    inference(demod,[status(thm)],['87','92','93'])).

thf('151',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['90','91'])).

thf('152',plain,(
    v3_pre_topc @ ( u1_struct_0 @ sk_C ) @ sk_D ),
    inference(demod,[status(thm)],['115','149','150','151'])).

thf('153',plain,(
    v1_tsep_1 @ sk_C @ sk_D ),
    inference(demod,[status(thm)],['68','152'])).

thf('154',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('155',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['13','14','15','16','19','20','45','153','154'])).

thf('156',plain,(
    ~ ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('157',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['155','156'])).

thf('158',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('159',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['157','158'])).

thf('160',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('161',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C ) ),
    inference(clc,[status(thm)],['159','160'])).

thf('162',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('163',plain,(
    v2_struct_0 @ sk_C ),
    inference(clc,[status(thm)],['161','162'])).

thf('164',plain,(
    $false ),
    inference(demod,[status(thm)],['0','163'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.8VlFTQrJ5Z
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:02:16 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.77/0.96  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.77/0.96  % Solved by: fo/fo7.sh
% 0.77/0.96  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.77/0.96  % done 1211 iterations in 0.504s
% 0.77/0.96  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.77/0.96  % SZS output start Refutation
% 0.77/0.96  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 0.77/0.96  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.77/0.96  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.77/0.96  thf(sk_B_type, type, sk_B: $i).
% 0.77/0.96  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.77/0.96  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.77/0.96  thf(sk_E_type, type, sk_E: $i).
% 0.77/0.96  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.77/0.96  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.77/0.96  thf(v1_tsep_1_type, type, v1_tsep_1: $i > $i > $o).
% 0.77/0.96  thf(sk_A_type, type, sk_A: $i).
% 0.77/0.96  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.77/0.96  thf(sk_D_type, type, sk_D: $i).
% 0.77/0.96  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.77/0.96  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.77/0.96  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.77/0.96  thf(sk_F_type, type, sk_F: $i).
% 0.77/0.96  thf(g1_pre_topc_type, type, g1_pre_topc: $i > $i > $i).
% 0.77/0.96  thf(r1_tmap_1_type, type, r1_tmap_1: $i > $i > $i > $i > $o).
% 0.77/0.96  thf(sk_C_type, type, sk_C: $i).
% 0.77/0.96  thf(k1_tsep_1_type, type, k1_tsep_1: $i > $i > $i > $i).
% 0.77/0.96  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.77/0.96  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.77/0.96  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 0.77/0.96  thf(sk_G_type, type, sk_G: $i).
% 0.77/0.96  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.77/0.96  thf(k3_tmap_1_type, type, k3_tmap_1: $i > $i > $i > $i > $i > $i).
% 0.77/0.96  thf(t88_tmap_1, conjecture,
% 0.77/0.96    (![A:$i]:
% 0.77/0.96     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.77/0.96       ( ![B:$i]:
% 0.77/0.96         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.77/0.96             ( l1_pre_topc @ B ) ) =>
% 0.77/0.96           ( ![C:$i]:
% 0.77/0.96             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.77/0.96               ( ![D:$i]:
% 0.77/0.96                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.77/0.96                   ( ![E:$i]:
% 0.77/0.96                     ( ( ( v1_funct_1 @ E ) & 
% 0.77/0.96                         ( v1_funct_2 @
% 0.77/0.96                           E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 0.77/0.96                         ( m1_subset_1 @
% 0.77/0.96                           E @ 
% 0.77/0.96                           ( k1_zfmisc_1 @
% 0.77/0.96                             ( k2_zfmisc_1 @
% 0.77/0.96                               ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.77/0.96                       ( ( ( g1_pre_topc @
% 0.77/0.96                             ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) ) =
% 0.77/0.96                           ( D ) ) =>
% 0.77/0.96                         ( ![F:$i]:
% 0.77/0.96                           ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 0.77/0.96                             ( ![G:$i]:
% 0.77/0.96                               ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) ) =>
% 0.77/0.96                                 ( ( ( ( F ) = ( G ) ) & 
% 0.77/0.96                                     ( r1_tmap_1 @
% 0.77/0.96                                       C @ B @ 
% 0.77/0.96                                       ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ G ) ) =>
% 0.77/0.96                                   ( r1_tmap_1 @ D @ B @ E @ F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.77/0.96  thf(zf_stmt_0, negated_conjecture,
% 0.77/0.96    (~( ![A:$i]:
% 0.77/0.96        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.77/0.96            ( l1_pre_topc @ A ) ) =>
% 0.77/0.96          ( ![B:$i]:
% 0.77/0.96            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.77/0.96                ( l1_pre_topc @ B ) ) =>
% 0.77/0.96              ( ![C:$i]:
% 0.77/0.96                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.77/0.96                  ( ![D:$i]:
% 0.77/0.96                    ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.77/0.96                      ( ![E:$i]:
% 0.77/0.96                        ( ( ( v1_funct_1 @ E ) & 
% 0.77/0.96                            ( v1_funct_2 @
% 0.77/0.96                              E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 0.77/0.96                            ( m1_subset_1 @
% 0.77/0.96                              E @ 
% 0.77/0.96                              ( k1_zfmisc_1 @
% 0.77/0.96                                ( k2_zfmisc_1 @
% 0.77/0.96                                  ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.77/0.96                          ( ( ( g1_pre_topc @
% 0.77/0.96                                ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) ) =
% 0.77/0.96                              ( D ) ) =>
% 0.77/0.96                            ( ![F:$i]:
% 0.77/0.96                              ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 0.77/0.96                                ( ![G:$i]:
% 0.77/0.96                                  ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) ) =>
% 0.77/0.96                                    ( ( ( ( F ) = ( G ) ) & 
% 0.77/0.96                                        ( r1_tmap_1 @
% 0.77/0.96                                          C @ B @ 
% 0.77/0.96                                          ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ G ) ) =>
% 0.77/0.96                                      ( r1_tmap_1 @ D @ B @ E @ F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.77/0.96    inference('cnf.neg', [status(esa)], [t88_tmap_1])).
% 0.77/0.96  thf('0', plain, (~ (v2_struct_0 @ sk_C)),
% 0.77/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.96  thf('1', plain,
% 0.77/0.96      ((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.77/0.96        (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_G)),
% 0.77/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.96  thf('2', plain, (((sk_F) = (sk_G))),
% 0.77/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.96  thf('3', plain,
% 0.77/0.96      ((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.77/0.96        (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_F)),
% 0.77/0.96      inference('demod', [status(thm)], ['1', '2'])).
% 0.77/0.96  thf('4', plain,
% 0.77/0.96      ((m1_subset_1 @ sk_E @ 
% 0.77/0.96        (k1_zfmisc_1 @ 
% 0.77/0.96         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 0.77/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.96  thf(t86_tmap_1, axiom,
% 0.77/0.96    (![A:$i]:
% 0.77/0.96     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.77/0.96       ( ![B:$i]:
% 0.77/0.96         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.77/0.96             ( l1_pre_topc @ B ) ) =>
% 0.77/0.96           ( ![C:$i]:
% 0.77/0.96             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.77/0.96               ( ![D:$i]:
% 0.77/0.96                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.77/0.96                   ( ![E:$i]:
% 0.77/0.96                     ( ( ( v1_funct_1 @ E ) & 
% 0.77/0.96                         ( v1_funct_2 @
% 0.77/0.96                           E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 0.77/0.96                         ( m1_subset_1 @
% 0.77/0.96                           E @ 
% 0.77/0.96                           ( k1_zfmisc_1 @
% 0.77/0.96                             ( k2_zfmisc_1 @
% 0.77/0.96                               ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.77/0.96                       ( ( ( v1_tsep_1 @ C @ D ) & ( m1_pre_topc @ C @ D ) ) =>
% 0.77/0.96                         ( ![F:$i]:
% 0.77/0.96                           ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 0.77/0.96                             ( ![G:$i]:
% 0.77/0.96                               ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) ) =>
% 0.77/0.96                                 ( ( ( F ) = ( G ) ) =>
% 0.77/0.96                                   ( ( r1_tmap_1 @ D @ B @ E @ F ) <=>
% 0.77/0.96                                     ( r1_tmap_1 @
% 0.77/0.96                                       C @ B @ 
% 0.77/0.96                                       ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ G ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.77/0.96  thf('5', plain,
% 0.77/0.96      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i, X36 : $i, X37 : $i, X38 : $i]:
% 0.77/0.96         ((v2_struct_0 @ X32)
% 0.77/0.96          | ~ (v2_pre_topc @ X32)
% 0.77/0.96          | ~ (l1_pre_topc @ X32)
% 0.77/0.96          | (v2_struct_0 @ X33)
% 0.77/0.96          | ~ (m1_pre_topc @ X33 @ X34)
% 0.77/0.96          | ~ (v1_tsep_1 @ X35 @ X33)
% 0.77/0.96          | ~ (m1_pre_topc @ X35 @ X33)
% 0.77/0.96          | ~ (m1_subset_1 @ X36 @ (u1_struct_0 @ X33))
% 0.77/0.96          | ((X36) != (X37))
% 0.77/0.96          | ~ (r1_tmap_1 @ X35 @ X32 @ 
% 0.77/0.96               (k3_tmap_1 @ X34 @ X32 @ X33 @ X35 @ X38) @ X37)
% 0.77/0.96          | (r1_tmap_1 @ X33 @ X32 @ X38 @ X36)
% 0.77/0.96          | ~ (m1_subset_1 @ X37 @ (u1_struct_0 @ X35))
% 0.77/0.96          | ~ (m1_subset_1 @ X38 @ 
% 0.77/0.96               (k1_zfmisc_1 @ 
% 0.77/0.96                (k2_zfmisc_1 @ (u1_struct_0 @ X33) @ (u1_struct_0 @ X32))))
% 0.77/0.96          | ~ (v1_funct_2 @ X38 @ (u1_struct_0 @ X33) @ (u1_struct_0 @ X32))
% 0.77/0.96          | ~ (v1_funct_1 @ X38)
% 0.77/0.96          | ~ (m1_pre_topc @ X35 @ X34)
% 0.77/0.96          | (v2_struct_0 @ X35)
% 0.77/0.96          | ~ (l1_pre_topc @ X34)
% 0.77/0.96          | ~ (v2_pre_topc @ X34)
% 0.77/0.96          | (v2_struct_0 @ X34))),
% 0.77/0.96      inference('cnf', [status(esa)], [t86_tmap_1])).
% 0.77/0.96  thf('6', plain,
% 0.77/0.96      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i, X37 : $i, X38 : $i]:
% 0.77/0.96         ((v2_struct_0 @ X34)
% 0.77/0.96          | ~ (v2_pre_topc @ X34)
% 0.77/0.96          | ~ (l1_pre_topc @ X34)
% 0.77/0.96          | (v2_struct_0 @ X35)
% 0.77/0.96          | ~ (m1_pre_topc @ X35 @ X34)
% 0.77/0.96          | ~ (v1_funct_1 @ X38)
% 0.77/0.96          | ~ (v1_funct_2 @ X38 @ (u1_struct_0 @ X33) @ (u1_struct_0 @ X32))
% 0.77/0.96          | ~ (m1_subset_1 @ X38 @ 
% 0.77/0.96               (k1_zfmisc_1 @ 
% 0.77/0.96                (k2_zfmisc_1 @ (u1_struct_0 @ X33) @ (u1_struct_0 @ X32))))
% 0.77/0.96          | ~ (m1_subset_1 @ X37 @ (u1_struct_0 @ X35))
% 0.77/0.96          | (r1_tmap_1 @ X33 @ X32 @ X38 @ X37)
% 0.77/0.96          | ~ (r1_tmap_1 @ X35 @ X32 @ 
% 0.77/0.96               (k3_tmap_1 @ X34 @ X32 @ X33 @ X35 @ X38) @ X37)
% 0.77/0.96          | ~ (m1_subset_1 @ X37 @ (u1_struct_0 @ X33))
% 0.77/0.96          | ~ (m1_pre_topc @ X35 @ X33)
% 0.77/0.96          | ~ (v1_tsep_1 @ X35 @ X33)
% 0.77/0.96          | ~ (m1_pre_topc @ X33 @ X34)
% 0.77/0.96          | (v2_struct_0 @ X33)
% 0.77/0.96          | ~ (l1_pre_topc @ X32)
% 0.77/0.96          | ~ (v2_pre_topc @ X32)
% 0.77/0.96          | (v2_struct_0 @ X32))),
% 0.77/0.96      inference('simplify', [status(thm)], ['5'])).
% 0.77/0.96  thf('7', plain,
% 0.77/0.96      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.77/0.96         ((v2_struct_0 @ sk_B)
% 0.77/0.96          | ~ (v2_pre_topc @ sk_B)
% 0.77/0.96          | ~ (l1_pre_topc @ sk_B)
% 0.77/0.96          | (v2_struct_0 @ sk_D)
% 0.77/0.96          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.77/0.96          | ~ (v1_tsep_1 @ X1 @ sk_D)
% 0.77/0.96          | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.77/0.96          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ sk_D))
% 0.77/0.96          | ~ (r1_tmap_1 @ X1 @ sk_B @ 
% 0.77/0.96               (k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E) @ X2)
% 0.77/0.96          | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X2)
% 0.77/0.96          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1))
% 0.77/0.96          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.77/0.96          | ~ (v1_funct_1 @ sk_E)
% 0.77/0.96          | ~ (m1_pre_topc @ X1 @ X0)
% 0.77/0.96          | (v2_struct_0 @ X1)
% 0.77/0.96          | ~ (l1_pre_topc @ X0)
% 0.77/0.96          | ~ (v2_pre_topc @ X0)
% 0.77/0.96          | (v2_struct_0 @ X0))),
% 0.77/0.96      inference('sup-', [status(thm)], ['4', '6'])).
% 0.77/0.96  thf('8', plain, ((v2_pre_topc @ sk_B)),
% 0.77/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.96  thf('9', plain, ((l1_pre_topc @ sk_B)),
% 0.77/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.96  thf('10', plain,
% 0.77/0.96      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 0.77/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.96  thf('11', plain, ((v1_funct_1 @ sk_E)),
% 0.77/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.96  thf('12', plain,
% 0.77/0.96      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.77/0.96         ((v2_struct_0 @ sk_B)
% 0.77/0.96          | (v2_struct_0 @ sk_D)
% 0.77/0.96          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.77/0.96          | ~ (v1_tsep_1 @ X1 @ sk_D)
% 0.77/0.96          | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.77/0.96          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ sk_D))
% 0.77/0.96          | ~ (r1_tmap_1 @ X1 @ sk_B @ 
% 0.77/0.96               (k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E) @ X2)
% 0.77/0.96          | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X2)
% 0.77/0.96          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1))
% 0.77/0.96          | ~ (m1_pre_topc @ X1 @ X0)
% 0.77/0.96          | (v2_struct_0 @ X1)
% 0.77/0.96          | ~ (l1_pre_topc @ X0)
% 0.77/0.96          | ~ (v2_pre_topc @ X0)
% 0.77/0.96          | (v2_struct_0 @ X0))),
% 0.77/0.96      inference('demod', [status(thm)], ['7', '8', '9', '10', '11'])).
% 0.77/0.96  thf('13', plain,
% 0.77/0.96      (((v2_struct_0 @ sk_A)
% 0.77/0.96        | ~ (v2_pre_topc @ sk_A)
% 0.77/0.96        | ~ (l1_pre_topc @ sk_A)
% 0.77/0.96        | (v2_struct_0 @ sk_C)
% 0.77/0.96        | ~ (m1_pre_topc @ sk_C @ sk_A)
% 0.77/0.96        | ~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C))
% 0.77/0.96        | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)
% 0.77/0.96        | ~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_D))
% 0.77/0.96        | ~ (m1_pre_topc @ sk_C @ sk_D)
% 0.77/0.96        | ~ (v1_tsep_1 @ sk_C @ sk_D)
% 0.77/0.96        | ~ (m1_pre_topc @ sk_D @ sk_A)
% 0.77/0.96        | (v2_struct_0 @ sk_D)
% 0.77/0.96        | (v2_struct_0 @ sk_B))),
% 0.77/0.96      inference('sup-', [status(thm)], ['3', '12'])).
% 0.77/0.96  thf('14', plain, ((v2_pre_topc @ sk_A)),
% 0.77/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.96  thf('15', plain, ((l1_pre_topc @ sk_A)),
% 0.77/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.96  thf('16', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.77/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.96  thf('17', plain, ((m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_C))),
% 0.77/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.96  thf('18', plain, (((sk_F) = (sk_G))),
% 0.77/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.96  thf('19', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C))),
% 0.77/0.96      inference('demod', [status(thm)], ['17', '18'])).
% 0.77/0.96  thf('20', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_D))),
% 0.77/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.96  thf('21', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.77/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.96  thf('22', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.77/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.96  thf(t22_tsep_1, axiom,
% 0.77/0.96    (![A:$i]:
% 0.77/0.96     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.77/0.96       ( ![B:$i]:
% 0.77/0.96         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.77/0.96           ( ![C:$i]:
% 0.77/0.96             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.77/0.96               ( m1_pre_topc @ B @ ( k1_tsep_1 @ A @ B @ C ) ) ) ) ) ) ))).
% 0.77/0.96  thf('23', plain,
% 0.77/0.96      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.77/0.96         ((v2_struct_0 @ X21)
% 0.77/0.96          | ~ (m1_pre_topc @ X21 @ X22)
% 0.77/0.96          | (m1_pre_topc @ X21 @ (k1_tsep_1 @ X22 @ X21 @ X23))
% 0.77/0.96          | ~ (m1_pre_topc @ X23 @ X22)
% 0.77/0.96          | (v2_struct_0 @ X23)
% 0.77/0.96          | ~ (l1_pre_topc @ X22)
% 0.77/0.96          | ~ (v2_pre_topc @ X22)
% 0.77/0.96          | (v2_struct_0 @ X22))),
% 0.77/0.96      inference('cnf', [status(esa)], [t22_tsep_1])).
% 0.77/0.96  thf('24', plain,
% 0.77/0.96      (![X0 : $i]:
% 0.77/0.96         ((v2_struct_0 @ sk_A)
% 0.77/0.96          | ~ (v2_pre_topc @ sk_A)
% 0.77/0.96          | ~ (l1_pre_topc @ sk_A)
% 0.77/0.96          | (v2_struct_0 @ X0)
% 0.77/0.96          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.77/0.96          | (m1_pre_topc @ sk_C @ (k1_tsep_1 @ sk_A @ sk_C @ X0))
% 0.77/0.96          | (v2_struct_0 @ sk_C))),
% 0.77/0.96      inference('sup-', [status(thm)], ['22', '23'])).
% 0.77/0.96  thf('25', plain, ((v2_pre_topc @ sk_A)),
% 0.77/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.96  thf('26', plain, ((l1_pre_topc @ sk_A)),
% 0.77/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.96  thf('27', plain,
% 0.77/0.96      (![X0 : $i]:
% 0.77/0.96         ((v2_struct_0 @ sk_A)
% 0.77/0.96          | (v2_struct_0 @ X0)
% 0.77/0.96          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.77/0.96          | (m1_pre_topc @ sk_C @ (k1_tsep_1 @ sk_A @ sk_C @ X0))
% 0.77/0.96          | (v2_struct_0 @ sk_C))),
% 0.77/0.96      inference('demod', [status(thm)], ['24', '25', '26'])).
% 0.77/0.96  thf('28', plain,
% 0.77/0.96      (((v2_struct_0 @ sk_C)
% 0.77/0.96        | (m1_pre_topc @ sk_C @ (k1_tsep_1 @ sk_A @ sk_C @ sk_C))
% 0.77/0.96        | (v2_struct_0 @ sk_C)
% 0.77/0.96        | (v2_struct_0 @ sk_A))),
% 0.77/0.96      inference('sup-', [status(thm)], ['21', '27'])).
% 0.77/0.96  thf('29', plain,
% 0.77/0.96      (((v2_struct_0 @ sk_A)
% 0.77/0.96        | (m1_pre_topc @ sk_C @ (k1_tsep_1 @ sk_A @ sk_C @ sk_C))
% 0.77/0.96        | (v2_struct_0 @ sk_C))),
% 0.77/0.96      inference('simplify', [status(thm)], ['28'])).
% 0.77/0.96  thf('30', plain, (~ (v2_struct_0 @ sk_A)),
% 0.77/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.96  thf('31', plain,
% 0.77/0.96      (((v2_struct_0 @ sk_C)
% 0.77/0.96        | (m1_pre_topc @ sk_C @ (k1_tsep_1 @ sk_A @ sk_C @ sk_C)))),
% 0.77/0.96      inference('clc', [status(thm)], ['29', '30'])).
% 0.77/0.96  thf('32', plain, (~ (v2_struct_0 @ sk_C)),
% 0.77/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.96  thf('33', plain, ((m1_pre_topc @ sk_C @ (k1_tsep_1 @ sk_A @ sk_C @ sk_C))),
% 0.77/0.96      inference('clc', [status(thm)], ['31', '32'])).
% 0.77/0.96  thf('34', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.77/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.96  thf(t25_tmap_1, axiom,
% 0.77/0.96    (![A:$i]:
% 0.77/0.96     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.77/0.96       ( ![B:$i]:
% 0.77/0.96         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.77/0.96           ( ( k1_tsep_1 @ A @ B @ B ) =
% 0.77/0.96             ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ))).
% 0.77/0.96  thf('35', plain,
% 0.77/0.96      (![X27 : $i, X28 : $i]:
% 0.77/0.96         ((v2_struct_0 @ X27)
% 0.77/0.96          | ~ (m1_pre_topc @ X27 @ X28)
% 0.77/0.96          | ((k1_tsep_1 @ X28 @ X27 @ X27)
% 0.77/0.96              = (g1_pre_topc @ (u1_struct_0 @ X27) @ (u1_pre_topc @ X27)))
% 0.77/0.96          | ~ (l1_pre_topc @ X28)
% 0.77/0.96          | ~ (v2_pre_topc @ X28)
% 0.77/0.96          | (v2_struct_0 @ X28))),
% 0.77/0.96      inference('cnf', [status(esa)], [t25_tmap_1])).
% 0.77/0.96  thf('36', plain,
% 0.77/0.96      (((v2_struct_0 @ sk_A)
% 0.77/0.96        | ~ (v2_pre_topc @ sk_A)
% 0.77/0.96        | ~ (l1_pre_topc @ sk_A)
% 0.77/0.96        | ((k1_tsep_1 @ sk_A @ sk_C @ sk_C)
% 0.77/0.96            = (g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)))
% 0.77/0.96        | (v2_struct_0 @ sk_C))),
% 0.77/0.96      inference('sup-', [status(thm)], ['34', '35'])).
% 0.77/0.96  thf('37', plain, ((v2_pre_topc @ sk_A)),
% 0.77/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.96  thf('38', plain, ((l1_pre_topc @ sk_A)),
% 0.77/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.96  thf('39', plain,
% 0.77/0.96      (((g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) = (sk_D))),
% 0.77/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.96  thf('40', plain,
% 0.77/0.96      (((v2_struct_0 @ sk_A)
% 0.77/0.96        | ((k1_tsep_1 @ sk_A @ sk_C @ sk_C) = (sk_D))
% 0.77/0.96        | (v2_struct_0 @ sk_C))),
% 0.77/0.96      inference('demod', [status(thm)], ['36', '37', '38', '39'])).
% 0.77/0.96  thf('41', plain, (~ (v2_struct_0 @ sk_A)),
% 0.77/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.96  thf('42', plain,
% 0.77/0.96      (((v2_struct_0 @ sk_C) | ((k1_tsep_1 @ sk_A @ sk_C @ sk_C) = (sk_D)))),
% 0.77/0.96      inference('clc', [status(thm)], ['40', '41'])).
% 0.77/0.96  thf('43', plain, (~ (v2_struct_0 @ sk_C)),
% 0.77/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.96  thf('44', plain, (((k1_tsep_1 @ sk_A @ sk_C @ sk_C) = (sk_D))),
% 0.77/0.96      inference('clc', [status(thm)], ['42', '43'])).
% 0.77/0.96  thf('45', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 0.77/0.96      inference('demod', [status(thm)], ['33', '44'])).
% 0.77/0.96  thf('46', plain, ((m1_pre_topc @ sk_C @ (k1_tsep_1 @ sk_A @ sk_C @ sk_C))),
% 0.77/0.96      inference('clc', [status(thm)], ['31', '32'])).
% 0.77/0.96  thf(t1_tsep_1, axiom,
% 0.77/0.96    (![A:$i]:
% 0.77/0.96     ( ( l1_pre_topc @ A ) =>
% 0.77/0.96       ( ![B:$i]:
% 0.77/0.96         ( ( m1_pre_topc @ B @ A ) =>
% 0.77/0.96           ( m1_subset_1 @
% 0.77/0.96             ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.77/0.96  thf('47', plain,
% 0.77/0.96      (![X19 : $i, X20 : $i]:
% 0.77/0.96         (~ (m1_pre_topc @ X19 @ X20)
% 0.77/0.96          | (m1_subset_1 @ (u1_struct_0 @ X19) @ 
% 0.77/0.96             (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.77/0.96          | ~ (l1_pre_topc @ X20))),
% 0.77/0.96      inference('cnf', [status(esa)], [t1_tsep_1])).
% 0.77/0.96  thf('48', plain,
% 0.77/0.96      ((~ (l1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_C @ sk_C))
% 0.77/0.96        | (m1_subset_1 @ (u1_struct_0 @ sk_C) @ 
% 0.77/0.96           (k1_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_C @ sk_C)))))),
% 0.77/0.96      inference('sup-', [status(thm)], ['46', '47'])).
% 0.77/0.96  thf('49', plain, (((k1_tsep_1 @ sk_A @ sk_C @ sk_C) = (sk_D))),
% 0.77/0.96      inference('clc', [status(thm)], ['42', '43'])).
% 0.77/0.96  thf('50', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.77/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.96  thf(dt_m1_pre_topc, axiom,
% 0.77/0.96    (![A:$i]:
% 0.77/0.96     ( ( l1_pre_topc @ A ) =>
% 0.77/0.96       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.77/0.96  thf('51', plain,
% 0.77/0.96      (![X4 : $i, X5 : $i]:
% 0.77/0.96         (~ (m1_pre_topc @ X4 @ X5) | (l1_pre_topc @ X4) | ~ (l1_pre_topc @ X5))),
% 0.77/0.96      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.77/0.96  thf('52', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_D))),
% 0.77/0.96      inference('sup-', [status(thm)], ['50', '51'])).
% 0.77/0.96  thf('53', plain, ((l1_pre_topc @ sk_A)),
% 0.77/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.96  thf('54', plain, ((l1_pre_topc @ sk_D)),
% 0.77/0.96      inference('demod', [status(thm)], ['52', '53'])).
% 0.77/0.96  thf('55', plain, (((k1_tsep_1 @ sk_A @ sk_C @ sk_C) = (sk_D))),
% 0.77/0.96      inference('clc', [status(thm)], ['42', '43'])).
% 0.77/0.96  thf('56', plain,
% 0.77/0.96      ((m1_subset_1 @ (u1_struct_0 @ sk_C) @ 
% 0.77/0.96        (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))),
% 0.77/0.96      inference('demod', [status(thm)], ['48', '49', '54', '55'])).
% 0.77/0.96  thf(t16_tsep_1, axiom,
% 0.77/0.96    (![A:$i]:
% 0.77/0.96     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.77/0.96       ( ![B:$i]:
% 0.77/0.96         ( ( m1_pre_topc @ B @ A ) =>
% 0.77/0.96           ( ![C:$i]:
% 0.77/0.96             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.77/0.96               ( ( ( C ) = ( u1_struct_0 @ B ) ) =>
% 0.77/0.96                 ( ( ( v1_tsep_1 @ B @ A ) & ( m1_pre_topc @ B @ A ) ) <=>
% 0.77/0.96                   ( v3_pre_topc @ C @ A ) ) ) ) ) ) ) ))).
% 0.77/0.96  thf('57', plain,
% 0.77/0.96      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.77/0.96         (~ (m1_pre_topc @ X16 @ X17)
% 0.77/0.96          | ((X18) != (u1_struct_0 @ X16))
% 0.77/0.96          | ~ (v3_pre_topc @ X18 @ X17)
% 0.77/0.96          | (v1_tsep_1 @ X16 @ X17)
% 0.77/0.96          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.77/0.96          | ~ (l1_pre_topc @ X17)
% 0.77/0.96          | ~ (v2_pre_topc @ X17))),
% 0.77/0.96      inference('cnf', [status(esa)], [t16_tsep_1])).
% 0.77/0.96  thf('58', plain,
% 0.77/0.96      (![X16 : $i, X17 : $i]:
% 0.77/0.96         (~ (v2_pre_topc @ X17)
% 0.77/0.96          | ~ (l1_pre_topc @ X17)
% 0.77/0.96          | ~ (m1_subset_1 @ (u1_struct_0 @ X16) @ 
% 0.77/0.96               (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.77/0.96          | (v1_tsep_1 @ X16 @ X17)
% 0.77/0.96          | ~ (v3_pre_topc @ (u1_struct_0 @ X16) @ X17)
% 0.77/0.96          | ~ (m1_pre_topc @ X16 @ X17))),
% 0.77/0.96      inference('simplify', [status(thm)], ['57'])).
% 0.77/0.96  thf('59', plain,
% 0.77/0.96      ((~ (m1_pre_topc @ sk_C @ sk_D)
% 0.77/0.96        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_C) @ sk_D)
% 0.77/0.96        | (v1_tsep_1 @ sk_C @ sk_D)
% 0.77/0.96        | ~ (l1_pre_topc @ sk_D)
% 0.77/0.96        | ~ (v2_pre_topc @ sk_D))),
% 0.77/0.96      inference('sup-', [status(thm)], ['56', '58'])).
% 0.77/0.96  thf('60', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 0.77/0.96      inference('demod', [status(thm)], ['33', '44'])).
% 0.77/0.96  thf('61', plain, ((l1_pre_topc @ sk_D)),
% 0.77/0.96      inference('demod', [status(thm)], ['52', '53'])).
% 0.77/0.96  thf('62', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.77/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.96  thf(cc1_pre_topc, axiom,
% 0.77/0.96    (![A:$i]:
% 0.77/0.96     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.77/0.96       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( v2_pre_topc @ B ) ) ) ))).
% 0.77/0.96  thf('63', plain,
% 0.77/0.96      (![X0 : $i, X1 : $i]:
% 0.77/0.96         (~ (m1_pre_topc @ X0 @ X1)
% 0.77/0.96          | (v2_pre_topc @ X0)
% 0.77/0.96          | ~ (l1_pre_topc @ X1)
% 0.77/0.96          | ~ (v2_pre_topc @ X1))),
% 0.77/0.96      inference('cnf', [status(esa)], [cc1_pre_topc])).
% 0.77/0.96  thf('64', plain,
% 0.77/0.96      ((~ (v2_pre_topc @ sk_A) | ~ (l1_pre_topc @ sk_A) | (v2_pre_topc @ sk_D))),
% 0.77/0.96      inference('sup-', [status(thm)], ['62', '63'])).
% 0.77/0.96  thf('65', plain, ((v2_pre_topc @ sk_A)),
% 0.77/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.96  thf('66', plain, ((l1_pre_topc @ sk_A)),
% 0.77/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.96  thf('67', plain, ((v2_pre_topc @ sk_D)),
% 0.77/0.96      inference('demod', [status(thm)], ['64', '65', '66'])).
% 0.77/0.96  thf('68', plain,
% 0.77/0.96      ((~ (v3_pre_topc @ (u1_struct_0 @ sk_C) @ sk_D)
% 0.77/0.96        | (v1_tsep_1 @ sk_C @ sk_D))),
% 0.77/0.96      inference('demod', [status(thm)], ['59', '60', '61', '67'])).
% 0.77/0.96  thf('69', plain, (((k1_tsep_1 @ sk_A @ sk_C @ sk_C) = (sk_D))),
% 0.77/0.96      inference('clc', [status(thm)], ['42', '43'])).
% 0.77/0.96  thf('70', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.77/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.96  thf('71', plain,
% 0.77/0.96      (((g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) = (sk_D))),
% 0.77/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.96  thf(t23_tsep_1, axiom,
% 0.77/0.96    (![A:$i]:
% 0.77/0.96     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.77/0.96       ( ![B:$i]:
% 0.77/0.96         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.77/0.96           ( ![C:$i]:
% 0.77/0.96             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.77/0.96               ( ( m1_pre_topc @ B @ C ) <=>
% 0.77/0.96                 ( ( k1_tsep_1 @ A @ B @ C ) =
% 0.77/0.96                   ( g1_pre_topc @ ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) ) ) ) ) ) ) ) ))).
% 0.77/0.96  thf('72', plain,
% 0.77/0.96      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.77/0.96         ((v2_struct_0 @ X24)
% 0.77/0.96          | ~ (m1_pre_topc @ X24 @ X25)
% 0.77/0.96          | ((k1_tsep_1 @ X25 @ X24 @ X26)
% 0.77/0.96              != (g1_pre_topc @ (u1_struct_0 @ X26) @ (u1_pre_topc @ X26)))
% 0.77/0.96          | (m1_pre_topc @ X24 @ X26)
% 0.77/0.96          | ~ (m1_pre_topc @ X26 @ X25)
% 0.77/0.96          | (v2_struct_0 @ X26)
% 0.77/0.96          | ~ (l1_pre_topc @ X25)
% 0.77/0.96          | ~ (v2_pre_topc @ X25)
% 0.77/0.96          | (v2_struct_0 @ X25))),
% 0.77/0.96      inference('cnf', [status(esa)], [t23_tsep_1])).
% 0.77/0.96  thf('73', plain,
% 0.77/0.96      (![X0 : $i, X1 : $i]:
% 0.77/0.96         (((k1_tsep_1 @ X1 @ X0 @ sk_C) != (sk_D))
% 0.77/0.96          | (v2_struct_0 @ X1)
% 0.77/0.96          | ~ (v2_pre_topc @ X1)
% 0.77/0.96          | ~ (l1_pre_topc @ X1)
% 0.77/0.96          | (v2_struct_0 @ sk_C)
% 0.77/0.96          | ~ (m1_pre_topc @ sk_C @ X1)
% 0.77/0.96          | (m1_pre_topc @ X0 @ sk_C)
% 0.77/0.96          | ~ (m1_pre_topc @ X0 @ X1)
% 0.77/0.96          | (v2_struct_0 @ X0))),
% 0.77/0.96      inference('sup-', [status(thm)], ['71', '72'])).
% 0.77/0.96  thf('74', plain,
% 0.77/0.96      (![X0 : $i]:
% 0.77/0.96         ((v2_struct_0 @ X0)
% 0.77/0.96          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.77/0.96          | (m1_pre_topc @ X0 @ sk_C)
% 0.77/0.96          | (v2_struct_0 @ sk_C)
% 0.77/0.96          | ~ (l1_pre_topc @ sk_A)
% 0.77/0.96          | ~ (v2_pre_topc @ sk_A)
% 0.77/0.96          | (v2_struct_0 @ sk_A)
% 0.77/0.96          | ((k1_tsep_1 @ sk_A @ X0 @ sk_C) != (sk_D)))),
% 0.77/0.96      inference('sup-', [status(thm)], ['70', '73'])).
% 0.77/0.96  thf('75', plain, ((l1_pre_topc @ sk_A)),
% 0.77/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.96  thf('76', plain, ((v2_pre_topc @ sk_A)),
% 0.77/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.96  thf('77', plain,
% 0.77/0.96      (![X0 : $i]:
% 0.77/0.96         ((v2_struct_0 @ X0)
% 0.77/0.96          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.77/0.96          | (m1_pre_topc @ X0 @ sk_C)
% 0.77/0.96          | (v2_struct_0 @ sk_C)
% 0.77/0.96          | (v2_struct_0 @ sk_A)
% 0.77/0.96          | ((k1_tsep_1 @ sk_A @ X0 @ sk_C) != (sk_D)))),
% 0.77/0.96      inference('demod', [status(thm)], ['74', '75', '76'])).
% 0.77/0.96  thf('78', plain,
% 0.77/0.96      ((((sk_D) != (sk_D))
% 0.77/0.96        | (v2_struct_0 @ sk_A)
% 0.77/0.96        | (v2_struct_0 @ sk_C)
% 0.77/0.96        | (m1_pre_topc @ sk_C @ sk_C)
% 0.77/0.96        | ~ (m1_pre_topc @ sk_C @ sk_A)
% 0.77/0.96        | (v2_struct_0 @ sk_C))),
% 0.77/0.96      inference('sup-', [status(thm)], ['69', '77'])).
% 0.77/0.96  thf('79', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.77/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.96  thf('80', plain,
% 0.77/0.96      ((((sk_D) != (sk_D))
% 0.77/0.96        | (v2_struct_0 @ sk_A)
% 0.77/0.96        | (v2_struct_0 @ sk_C)
% 0.77/0.96        | (m1_pre_topc @ sk_C @ sk_C)
% 0.77/0.96        | (v2_struct_0 @ sk_C))),
% 0.77/0.96      inference('demod', [status(thm)], ['78', '79'])).
% 0.77/0.96  thf('81', plain,
% 0.77/0.96      (((m1_pre_topc @ sk_C @ sk_C)
% 0.77/0.96        | (v2_struct_0 @ sk_C)
% 0.77/0.96        | (v2_struct_0 @ sk_A))),
% 0.77/0.96      inference('simplify', [status(thm)], ['80'])).
% 0.77/0.96  thf('82', plain, (~ (v2_struct_0 @ sk_C)),
% 0.77/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.96  thf('83', plain, (((v2_struct_0 @ sk_A) | (m1_pre_topc @ sk_C @ sk_C))),
% 0.77/0.96      inference('clc', [status(thm)], ['81', '82'])).
% 0.77/0.96  thf('84', plain, (~ (v2_struct_0 @ sk_A)),
% 0.77/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.96  thf('85', plain, ((m1_pre_topc @ sk_C @ sk_C)),
% 0.77/0.96      inference('clc', [status(thm)], ['83', '84'])).
% 0.77/0.96  thf(t11_tmap_1, axiom,
% 0.77/0.96    (![A:$i]:
% 0.77/0.96     ( ( l1_pre_topc @ A ) =>
% 0.77/0.96       ( ![B:$i]:
% 0.77/0.96         ( ( m1_pre_topc @ B @ A ) =>
% 0.77/0.96           ( ( v1_pre_topc @
% 0.77/0.96               ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) & 
% 0.77/0.96             ( m1_pre_topc @
% 0.77/0.96               ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) @ A ) ) ) ) ))).
% 0.77/0.96  thf('86', plain,
% 0.77/0.96      (![X14 : $i, X15 : $i]:
% 0.77/0.96         (~ (m1_pre_topc @ X14 @ X15)
% 0.77/0.96          | (m1_pre_topc @ 
% 0.77/0.96             (g1_pre_topc @ (u1_struct_0 @ X14) @ (u1_pre_topc @ X14)) @ X15)
% 0.77/0.96          | ~ (l1_pre_topc @ X15))),
% 0.77/0.96      inference('cnf', [status(esa)], [t11_tmap_1])).
% 0.77/0.96  thf('87', plain,
% 0.77/0.96      ((~ (l1_pre_topc @ sk_C)
% 0.77/0.96        | (m1_pre_topc @ 
% 0.77/0.96           (g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) @ sk_C))),
% 0.77/0.96      inference('sup-', [status(thm)], ['85', '86'])).
% 0.77/0.96  thf('88', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.77/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.96  thf('89', plain,
% 0.77/0.96      (![X4 : $i, X5 : $i]:
% 0.77/0.96         (~ (m1_pre_topc @ X4 @ X5) | (l1_pre_topc @ X4) | ~ (l1_pre_topc @ X5))),
% 0.77/0.96      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.77/0.96  thf('90', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_C))),
% 0.77/0.96      inference('sup-', [status(thm)], ['88', '89'])).
% 0.77/0.96  thf('91', plain, ((l1_pre_topc @ sk_A)),
% 0.77/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.96  thf('92', plain, ((l1_pre_topc @ sk_C)),
% 0.77/0.96      inference('demod', [status(thm)], ['90', '91'])).
% 0.77/0.96  thf('93', plain,
% 0.77/0.96      (((g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) = (sk_D))),
% 0.77/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.96  thf('94', plain, ((m1_pre_topc @ sk_D @ sk_C)),
% 0.77/0.96      inference('demod', [status(thm)], ['87', '92', '93'])).
% 0.77/0.96  thf(d3_struct_0, axiom,
% 0.77/0.96    (![A:$i]:
% 0.77/0.96     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.77/0.96  thf('95', plain,
% 0.77/0.96      (![X2 : $i]:
% 0.77/0.96         (((k2_struct_0 @ X2) = (u1_struct_0 @ X2)) | ~ (l1_struct_0 @ X2))),
% 0.77/0.96      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.77/0.96  thf('96', plain,
% 0.77/0.96      ((m1_subset_1 @ (u1_struct_0 @ sk_C) @ 
% 0.77/0.96        (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))),
% 0.77/0.96      inference('demod', [status(thm)], ['48', '49', '54', '55'])).
% 0.77/0.96  thf('97', plain,
% 0.77/0.96      (((m1_subset_1 @ (k2_struct_0 @ sk_C) @ 
% 0.77/0.96         (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))
% 0.77/0.96        | ~ (l1_struct_0 @ sk_C))),
% 0.77/0.96      inference('sup+', [status(thm)], ['95', '96'])).
% 0.77/0.96  thf('98', plain, ((l1_pre_topc @ sk_C)),
% 0.77/0.96      inference('demod', [status(thm)], ['90', '91'])).
% 0.77/0.96  thf(dt_l1_pre_topc, axiom,
% 0.77/0.96    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.77/0.96  thf('99', plain, (![X3 : $i]: ((l1_struct_0 @ X3) | ~ (l1_pre_topc @ X3))),
% 0.77/0.96      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.77/0.96  thf('100', plain, ((l1_struct_0 @ sk_C)),
% 0.77/0.96      inference('sup-', [status(thm)], ['98', '99'])).
% 0.77/0.96  thf('101', plain,
% 0.77/0.96      ((m1_subset_1 @ (k2_struct_0 @ sk_C) @ 
% 0.77/0.96        (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))),
% 0.77/0.96      inference('demod', [status(thm)], ['97', '100'])).
% 0.77/0.96  thf(t39_pre_topc, axiom,
% 0.77/0.96    (![A:$i]:
% 0.77/0.96     ( ( l1_pre_topc @ A ) =>
% 0.77/0.96       ( ![B:$i]:
% 0.77/0.96         ( ( m1_pre_topc @ B @ A ) =>
% 0.77/0.96           ( ![C:$i]:
% 0.77/0.96             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.77/0.96               ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ))).
% 0.77/0.96  thf('102', plain,
% 0.77/0.96      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.77/0.96         (~ (m1_pre_topc @ X6 @ X7)
% 0.77/0.96          | (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (u1_struct_0 @ X7)))
% 0.77/0.96          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (u1_struct_0 @ X6)))
% 0.77/0.96          | ~ (l1_pre_topc @ X7))),
% 0.77/0.96      inference('cnf', [status(esa)], [t39_pre_topc])).
% 0.77/0.96  thf('103', plain,
% 0.77/0.96      (![X0 : $i]:
% 0.77/0.96         (~ (l1_pre_topc @ X0)
% 0.77/0.96          | (m1_subset_1 @ (k2_struct_0 @ sk_C) @ 
% 0.77/0.96             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.77/0.96          | ~ (m1_pre_topc @ sk_D @ X0))),
% 0.77/0.96      inference('sup-', [status(thm)], ['101', '102'])).
% 0.77/0.96  thf('104', plain,
% 0.77/0.96      (((m1_subset_1 @ (k2_struct_0 @ sk_C) @ 
% 0.77/0.96         (k1_zfmisc_1 @ (u1_struct_0 @ sk_C)))
% 0.77/0.96        | ~ (l1_pre_topc @ sk_C))),
% 0.77/0.96      inference('sup-', [status(thm)], ['94', '103'])).
% 0.77/0.96  thf('105', plain, ((l1_pre_topc @ sk_C)),
% 0.77/0.96      inference('demod', [status(thm)], ['90', '91'])).
% 0.77/0.96  thf('106', plain,
% 0.77/0.96      ((m1_subset_1 @ (k2_struct_0 @ sk_C) @ 
% 0.77/0.96        (k1_zfmisc_1 @ (u1_struct_0 @ sk_C)))),
% 0.77/0.96      inference('demod', [status(thm)], ['104', '105'])).
% 0.77/0.96  thf('107', plain,
% 0.77/0.96      (![X2 : $i]:
% 0.77/0.96         (((k2_struct_0 @ X2) = (u1_struct_0 @ X2)) | ~ (l1_struct_0 @ X2))),
% 0.77/0.96      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.77/0.96  thf('108', plain,
% 0.77/0.96      ((m1_subset_1 @ (u1_struct_0 @ sk_C) @ 
% 0.77/0.96        (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))),
% 0.77/0.96      inference('demod', [status(thm)], ['48', '49', '54', '55'])).
% 0.77/0.96  thf(t33_tops_2, axiom,
% 0.77/0.96    (![A:$i]:
% 0.77/0.96     ( ( l1_pre_topc @ A ) =>
% 0.77/0.96       ( ![B:$i]:
% 0.77/0.96         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.77/0.96           ( ![C:$i]:
% 0.77/0.96             ( ( m1_pre_topc @ C @ A ) =>
% 0.77/0.96               ( ( v3_pre_topc @ B @ A ) =>
% 0.77/0.96                 ( ![D:$i]:
% 0.77/0.96                   ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ C ) ) ) =>
% 0.77/0.96                     ( ( ( D ) = ( B ) ) => ( v3_pre_topc @ D @ C ) ) ) ) ) ) ) ) ) ))).
% 0.77/0.96  thf('109', plain,
% 0.77/0.96      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.77/0.96         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.77/0.96          | ~ (v3_pre_topc @ X10 @ X11)
% 0.77/0.96          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.77/0.96          | (v3_pre_topc @ X12 @ X13)
% 0.77/0.96          | ((X12) != (X10))
% 0.77/0.96          | ~ (m1_pre_topc @ X13 @ X11)
% 0.77/0.96          | ~ (l1_pre_topc @ X11))),
% 0.77/0.96      inference('cnf', [status(esa)], [t33_tops_2])).
% 0.77/0.96  thf('110', plain,
% 0.77/0.96      (![X10 : $i, X11 : $i, X13 : $i]:
% 0.77/0.96         (~ (l1_pre_topc @ X11)
% 0.77/0.96          | ~ (m1_pre_topc @ X13 @ X11)
% 0.77/0.96          | (v3_pre_topc @ X10 @ X13)
% 0.77/0.96          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.77/0.96          | ~ (v3_pre_topc @ X10 @ X11)
% 0.77/0.96          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11))))),
% 0.77/0.96      inference('simplify', [status(thm)], ['109'])).
% 0.77/0.96  thf('111', plain,
% 0.77/0.96      (![X0 : $i]:
% 0.77/0.96         (~ (m1_subset_1 @ (u1_struct_0 @ sk_C) @ 
% 0.77/0.96             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.77/0.96          | ~ (v3_pre_topc @ (u1_struct_0 @ sk_C) @ X0)
% 0.77/0.96          | (v3_pre_topc @ (u1_struct_0 @ sk_C) @ sk_D)
% 0.77/0.96          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.77/0.96          | ~ (l1_pre_topc @ X0))),
% 0.77/0.96      inference('sup-', [status(thm)], ['108', '110'])).
% 0.77/0.96  thf('112', plain,
% 0.77/0.96      (![X0 : $i]:
% 0.77/0.96         (~ (m1_subset_1 @ (k2_struct_0 @ sk_C) @ 
% 0.77/0.96             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.77/0.96          | ~ (l1_struct_0 @ sk_C)
% 0.77/0.96          | ~ (l1_pre_topc @ X0)
% 0.77/0.96          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.77/0.96          | (v3_pre_topc @ (u1_struct_0 @ sk_C) @ sk_D)
% 0.77/0.96          | ~ (v3_pre_topc @ (u1_struct_0 @ sk_C) @ X0))),
% 0.77/0.96      inference('sup-', [status(thm)], ['107', '111'])).
% 0.77/0.96  thf('113', plain, ((l1_struct_0 @ sk_C)),
% 0.77/0.96      inference('sup-', [status(thm)], ['98', '99'])).
% 0.77/0.96  thf('114', plain,
% 0.77/0.96      (![X0 : $i]:
% 0.77/0.96         (~ (m1_subset_1 @ (k2_struct_0 @ sk_C) @ 
% 0.77/0.96             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.77/0.96          | ~ (l1_pre_topc @ X0)
% 0.77/0.96          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.77/0.96          | (v3_pre_topc @ (u1_struct_0 @ sk_C) @ sk_D)
% 0.77/0.96          | ~ (v3_pre_topc @ (u1_struct_0 @ sk_C) @ X0))),
% 0.77/0.96      inference('demod', [status(thm)], ['112', '113'])).
% 0.77/0.96  thf('115', plain,
% 0.77/0.96      ((~ (v3_pre_topc @ (u1_struct_0 @ sk_C) @ sk_C)
% 0.77/0.96        | (v3_pre_topc @ (u1_struct_0 @ sk_C) @ sk_D)
% 0.77/0.96        | ~ (m1_pre_topc @ sk_D @ sk_C)
% 0.77/0.96        | ~ (l1_pre_topc @ sk_C))),
% 0.77/0.96      inference('sup-', [status(thm)], ['106', '114'])).
% 0.77/0.96  thf('116', plain, ((m1_pre_topc @ sk_C @ sk_C)),
% 0.77/0.96      inference('clc', [status(thm)], ['83', '84'])).
% 0.77/0.96  thf('117', plain,
% 0.77/0.96      (![X19 : $i, X20 : $i]:
% 0.77/0.96         (~ (m1_pre_topc @ X19 @ X20)
% 0.77/0.96          | (m1_subset_1 @ (u1_struct_0 @ X19) @ 
% 0.77/0.96             (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.77/0.96          | ~ (l1_pre_topc @ X20))),
% 0.77/0.96      inference('cnf', [status(esa)], [t1_tsep_1])).
% 0.77/0.96  thf('118', plain,
% 0.77/0.96      ((~ (l1_pre_topc @ sk_C)
% 0.77/0.96        | (m1_subset_1 @ (u1_struct_0 @ sk_C) @ 
% 0.77/0.96           (k1_zfmisc_1 @ (u1_struct_0 @ sk_C))))),
% 0.77/0.96      inference('sup-', [status(thm)], ['116', '117'])).
% 0.77/0.96  thf('119', plain, ((l1_pre_topc @ sk_C)),
% 0.77/0.96      inference('demod', [status(thm)], ['90', '91'])).
% 0.77/0.96  thf('120', plain,
% 0.77/0.96      ((m1_subset_1 @ (u1_struct_0 @ sk_C) @ 
% 0.77/0.96        (k1_zfmisc_1 @ (u1_struct_0 @ sk_C)))),
% 0.77/0.96      inference('demod', [status(thm)], ['118', '119'])).
% 0.77/0.96  thf('121', plain,
% 0.77/0.96      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.77/0.96         (~ (m1_pre_topc @ X16 @ X17)
% 0.77/0.96          | ((X18) != (u1_struct_0 @ X16))
% 0.77/0.96          | ~ (v1_tsep_1 @ X16 @ X17)
% 0.77/0.96          | ~ (m1_pre_topc @ X16 @ X17)
% 0.77/0.96          | (v3_pre_topc @ X18 @ X17)
% 0.77/0.96          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.77/0.96          | ~ (l1_pre_topc @ X17)
% 0.77/0.96          | ~ (v2_pre_topc @ X17))),
% 0.77/0.96      inference('cnf', [status(esa)], [t16_tsep_1])).
% 0.77/0.96  thf('122', plain,
% 0.77/0.96      (![X16 : $i, X17 : $i]:
% 0.77/0.96         (~ (v2_pre_topc @ X17)
% 0.77/0.96          | ~ (l1_pre_topc @ X17)
% 0.77/0.96          | ~ (m1_subset_1 @ (u1_struct_0 @ X16) @ 
% 0.77/0.96               (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.77/0.96          | (v3_pre_topc @ (u1_struct_0 @ X16) @ X17)
% 0.77/0.96          | ~ (v1_tsep_1 @ X16 @ X17)
% 0.77/0.96          | ~ (m1_pre_topc @ X16 @ X17))),
% 0.77/0.96      inference('simplify', [status(thm)], ['121'])).
% 0.77/0.96  thf('123', plain,
% 0.77/0.96      ((~ (m1_pre_topc @ sk_C @ sk_C)
% 0.77/0.96        | ~ (v1_tsep_1 @ sk_C @ sk_C)
% 0.77/0.96        | (v3_pre_topc @ (u1_struct_0 @ sk_C) @ sk_C)
% 0.77/0.96        | ~ (l1_pre_topc @ sk_C)
% 0.77/0.96        | ~ (v2_pre_topc @ sk_C))),
% 0.77/0.96      inference('sup-', [status(thm)], ['120', '122'])).
% 0.77/0.96  thf('124', plain, ((m1_pre_topc @ sk_C @ sk_C)),
% 0.77/0.96      inference('clc', [status(thm)], ['83', '84'])).
% 0.77/0.96  thf('125', plain, ((l1_pre_topc @ sk_C)),
% 0.77/0.96      inference('demod', [status(thm)], ['90', '91'])).
% 0.77/0.96  thf('126', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.77/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.96  thf('127', plain,
% 0.77/0.96      (![X0 : $i, X1 : $i]:
% 0.77/0.96         (~ (m1_pre_topc @ X0 @ X1)
% 0.77/0.96          | (v2_pre_topc @ X0)
% 0.77/0.96          | ~ (l1_pre_topc @ X1)
% 0.77/0.96          | ~ (v2_pre_topc @ X1))),
% 0.77/0.96      inference('cnf', [status(esa)], [cc1_pre_topc])).
% 0.77/0.96  thf('128', plain,
% 0.77/0.96      ((~ (v2_pre_topc @ sk_A) | ~ (l1_pre_topc @ sk_A) | (v2_pre_topc @ sk_C))),
% 0.77/0.96      inference('sup-', [status(thm)], ['126', '127'])).
% 0.77/0.96  thf('129', plain, ((v2_pre_topc @ sk_A)),
% 0.77/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.96  thf('130', plain, ((l1_pre_topc @ sk_A)),
% 0.77/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.96  thf('131', plain, ((v2_pre_topc @ sk_C)),
% 0.77/0.96      inference('demod', [status(thm)], ['128', '129', '130'])).
% 0.77/0.96  thf('132', plain,
% 0.77/0.96      ((~ (v1_tsep_1 @ sk_C @ sk_C)
% 0.77/0.96        | (v3_pre_topc @ (u1_struct_0 @ sk_C) @ sk_C))),
% 0.77/0.96      inference('demod', [status(thm)], ['123', '124', '125', '131'])).
% 0.77/0.96  thf(fc10_tops_1, axiom,
% 0.77/0.96    (![A:$i]:
% 0.77/0.96     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.77/0.96       ( v3_pre_topc @ ( k2_struct_0 @ A ) @ A ) ))).
% 0.77/0.96  thf('133', plain,
% 0.77/0.96      (![X9 : $i]:
% 0.77/0.96         ((v3_pre_topc @ (k2_struct_0 @ X9) @ X9)
% 0.77/0.96          | ~ (l1_pre_topc @ X9)
% 0.77/0.96          | ~ (v2_pre_topc @ X9))),
% 0.77/0.96      inference('cnf', [status(esa)], [fc10_tops_1])).
% 0.77/0.96  thf('134', plain,
% 0.77/0.96      (![X2 : $i]:
% 0.77/0.96         (((k2_struct_0 @ X2) = (u1_struct_0 @ X2)) | ~ (l1_struct_0 @ X2))),
% 0.77/0.96      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.77/0.96  thf('135', plain,
% 0.77/0.96      ((m1_subset_1 @ (u1_struct_0 @ sk_C) @ 
% 0.77/0.96        (k1_zfmisc_1 @ (u1_struct_0 @ sk_C)))),
% 0.77/0.96      inference('demod', [status(thm)], ['118', '119'])).
% 0.77/0.96  thf('136', plain,
% 0.77/0.96      (![X16 : $i, X17 : $i]:
% 0.77/0.96         (~ (v2_pre_topc @ X17)
% 0.77/0.96          | ~ (l1_pre_topc @ X17)
% 0.77/0.96          | ~ (m1_subset_1 @ (u1_struct_0 @ X16) @ 
% 0.77/0.96               (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.77/0.96          | (v1_tsep_1 @ X16 @ X17)
% 0.77/0.96          | ~ (v3_pre_topc @ (u1_struct_0 @ X16) @ X17)
% 0.77/0.96          | ~ (m1_pre_topc @ X16 @ X17))),
% 0.77/0.96      inference('simplify', [status(thm)], ['57'])).
% 0.77/0.96  thf('137', plain,
% 0.77/0.96      ((~ (m1_pre_topc @ sk_C @ sk_C)
% 0.77/0.96        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_C) @ sk_C)
% 0.77/0.96        | (v1_tsep_1 @ sk_C @ sk_C)
% 0.77/0.96        | ~ (l1_pre_topc @ sk_C)
% 0.77/0.96        | ~ (v2_pre_topc @ sk_C))),
% 0.77/0.96      inference('sup-', [status(thm)], ['135', '136'])).
% 0.77/0.96  thf('138', plain, ((m1_pre_topc @ sk_C @ sk_C)),
% 0.77/0.96      inference('clc', [status(thm)], ['83', '84'])).
% 0.77/0.96  thf('139', plain, ((l1_pre_topc @ sk_C)),
% 0.77/0.96      inference('demod', [status(thm)], ['90', '91'])).
% 0.77/0.96  thf('140', plain, ((v2_pre_topc @ sk_C)),
% 0.77/0.96      inference('demod', [status(thm)], ['128', '129', '130'])).
% 0.77/0.96  thf('141', plain,
% 0.77/0.96      ((~ (v3_pre_topc @ (u1_struct_0 @ sk_C) @ sk_C)
% 0.77/0.96        | (v1_tsep_1 @ sk_C @ sk_C))),
% 0.77/0.96      inference('demod', [status(thm)], ['137', '138', '139', '140'])).
% 0.77/0.96  thf('142', plain,
% 0.77/0.96      ((~ (v3_pre_topc @ (k2_struct_0 @ sk_C) @ sk_C)
% 0.77/0.96        | ~ (l1_struct_0 @ sk_C)
% 0.77/0.96        | (v1_tsep_1 @ sk_C @ sk_C))),
% 0.77/0.96      inference('sup-', [status(thm)], ['134', '141'])).
% 0.77/0.96  thf('143', plain, ((l1_struct_0 @ sk_C)),
% 0.77/0.96      inference('sup-', [status(thm)], ['98', '99'])).
% 0.77/0.96  thf('144', plain,
% 0.77/0.96      ((~ (v3_pre_topc @ (k2_struct_0 @ sk_C) @ sk_C)
% 0.77/0.96        | (v1_tsep_1 @ sk_C @ sk_C))),
% 0.77/0.96      inference('demod', [status(thm)], ['142', '143'])).
% 0.77/0.96  thf('145', plain,
% 0.77/0.96      ((~ (v2_pre_topc @ sk_C)
% 0.77/0.96        | ~ (l1_pre_topc @ sk_C)
% 0.77/0.96        | (v1_tsep_1 @ sk_C @ sk_C))),
% 0.77/0.96      inference('sup-', [status(thm)], ['133', '144'])).
% 0.77/0.96  thf('146', plain, ((v2_pre_topc @ sk_C)),
% 0.77/0.96      inference('demod', [status(thm)], ['128', '129', '130'])).
% 0.77/0.96  thf('147', plain, ((l1_pre_topc @ sk_C)),
% 0.77/0.96      inference('demod', [status(thm)], ['90', '91'])).
% 0.77/0.96  thf('148', plain, ((v1_tsep_1 @ sk_C @ sk_C)),
% 0.77/0.96      inference('demod', [status(thm)], ['145', '146', '147'])).
% 0.77/0.96  thf('149', plain, ((v3_pre_topc @ (u1_struct_0 @ sk_C) @ sk_C)),
% 0.77/0.96      inference('demod', [status(thm)], ['132', '148'])).
% 0.77/0.96  thf('150', plain, ((m1_pre_topc @ sk_D @ sk_C)),
% 0.77/0.96      inference('demod', [status(thm)], ['87', '92', '93'])).
% 0.77/0.96  thf('151', plain, ((l1_pre_topc @ sk_C)),
% 0.77/0.96      inference('demod', [status(thm)], ['90', '91'])).
% 0.77/0.96  thf('152', plain, ((v3_pre_topc @ (u1_struct_0 @ sk_C) @ sk_D)),
% 0.77/0.96      inference('demod', [status(thm)], ['115', '149', '150', '151'])).
% 0.77/0.96  thf('153', plain, ((v1_tsep_1 @ sk_C @ sk_D)),
% 0.77/0.96      inference('demod', [status(thm)], ['68', '152'])).
% 0.77/0.96  thf('154', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.77/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.96  thf('155', plain,
% 0.77/0.96      (((v2_struct_0 @ sk_A)
% 0.77/0.96        | (v2_struct_0 @ sk_C)
% 0.77/0.96        | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)
% 0.77/0.96        | (v2_struct_0 @ sk_D)
% 0.77/0.96        | (v2_struct_0 @ sk_B))),
% 0.77/0.96      inference('demod', [status(thm)],
% 0.77/0.96                ['13', '14', '15', '16', '19', '20', '45', '153', '154'])).
% 0.77/0.96  thf('156', plain, (~ (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)),
% 0.77/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.96  thf('157', plain,
% 0.77/0.96      (((v2_struct_0 @ sk_B)
% 0.77/0.96        | (v2_struct_0 @ sk_D)
% 0.77/0.96        | (v2_struct_0 @ sk_C)
% 0.77/0.96        | (v2_struct_0 @ sk_A))),
% 0.77/0.96      inference('sup-', [status(thm)], ['155', '156'])).
% 0.77/0.96  thf('158', plain, (~ (v2_struct_0 @ sk_D)),
% 0.77/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.96  thf('159', plain,
% 0.77/0.96      (((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_B))),
% 0.77/0.96      inference('sup-', [status(thm)], ['157', '158'])).
% 0.77/0.96  thf('160', plain, (~ (v2_struct_0 @ sk_A)),
% 0.77/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.96  thf('161', plain, (((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_C))),
% 0.77/0.96      inference('clc', [status(thm)], ['159', '160'])).
% 0.77/0.96  thf('162', plain, (~ (v2_struct_0 @ sk_B)),
% 0.77/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.96  thf('163', plain, ((v2_struct_0 @ sk_C)),
% 0.77/0.96      inference('clc', [status(thm)], ['161', '162'])).
% 0.77/0.96  thf('164', plain, ($false), inference('demod', [status(thm)], ['0', '163'])).
% 0.77/0.96  
% 0.77/0.96  % SZS output end Refutation
% 0.77/0.96  
% 0.77/0.97  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
