%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.KRHv1yBY97

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:10:32 EST 2020

% Result     : Theorem 1.74s
% Output     : Refutation 1.74s
% Verified   : 
% Statistics : Number of formulae       :  247 (2601 expanded)
%              Number of leaves         :   44 ( 752 expanded)
%              Depth                    :   30
%              Number of atoms          : 2049 (70599 expanded)
%              Number of equality atoms :   46 (1918 expanded)
%              Maximal formula depth    :   29 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_G_type,type,(
    sk_G: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_tmap_1_type,type,(
    r1_tmap_1: $i > $i > $i > $i > $o )).

thf(g1_pre_topc_type,type,(
    g1_pre_topc: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_tsep_1_type,type,(
    k1_tsep_1: $i > $i > $i > $i )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v1_tsep_1_type,type,(
    v1_tsep_1: $i > $i > $o )).

thf(k3_tmap_1_type,type,(
    k3_tmap_1: $i > $i > $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

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
    ! [X31: $i,X32: $i,X33: $i,X34: $i,X35: $i,X36: $i,X37: $i] :
      ( ( v2_struct_0 @ X31 )
      | ~ ( v2_pre_topc @ X31 )
      | ~ ( l1_pre_topc @ X31 )
      | ( v2_struct_0 @ X32 )
      | ~ ( m1_pre_topc @ X32 @ X33 )
      | ~ ( v1_tsep_1 @ X34 @ X32 )
      | ~ ( m1_pre_topc @ X34 @ X32 )
      | ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ X32 ) )
      | ( X35 != X36 )
      | ~ ( r1_tmap_1 @ X34 @ X31 @ ( k3_tmap_1 @ X33 @ X31 @ X32 @ X34 @ X37 ) @ X36 )
      | ( r1_tmap_1 @ X32 @ X31 @ X37 @ X35 )
      | ~ ( m1_subset_1 @ X36 @ ( u1_struct_0 @ X34 ) )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X32 ) @ ( u1_struct_0 @ X31 ) ) ) )
      | ~ ( v1_funct_2 @ X37 @ ( u1_struct_0 @ X32 ) @ ( u1_struct_0 @ X31 ) )
      | ~ ( v1_funct_1 @ X37 )
      | ~ ( m1_pre_topc @ X34 @ X33 )
      | ( v2_struct_0 @ X34 )
      | ~ ( l1_pre_topc @ X33 )
      | ~ ( v2_pre_topc @ X33 )
      | ( v2_struct_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t86_tmap_1])).

thf('6',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i,X36: $i,X37: $i] :
      ( ( v2_struct_0 @ X33 )
      | ~ ( v2_pre_topc @ X33 )
      | ~ ( l1_pre_topc @ X33 )
      | ( v2_struct_0 @ X34 )
      | ~ ( m1_pre_topc @ X34 @ X33 )
      | ~ ( v1_funct_1 @ X37 )
      | ~ ( v1_funct_2 @ X37 @ ( u1_struct_0 @ X32 ) @ ( u1_struct_0 @ X31 ) )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X32 ) @ ( u1_struct_0 @ X31 ) ) ) )
      | ~ ( m1_subset_1 @ X36 @ ( u1_struct_0 @ X34 ) )
      | ( r1_tmap_1 @ X32 @ X31 @ X37 @ X36 )
      | ~ ( r1_tmap_1 @ X34 @ X31 @ ( k3_tmap_1 @ X33 @ X31 @ X32 @ X34 @ X37 ) @ X36 )
      | ~ ( m1_subset_1 @ X36 @ ( u1_struct_0 @ X32 ) )
      | ~ ( m1_pre_topc @ X34 @ X32 )
      | ~ ( v1_tsep_1 @ X34 @ X32 )
      | ~ ( m1_pre_topc @ X32 @ X33 )
      | ( v2_struct_0 @ X32 )
      | ~ ( l1_pre_topc @ X31 )
      | ~ ( v2_pre_topc @ X31 )
      | ( v2_struct_0 @ X31 ) ) ),
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
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) )
    = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( m1_pre_topc @ A @ A ) ) )).

thf('14',plain,(
    ! [X22: $i] :
      ( ( m1_pre_topc @ X22 @ X22 )
      | ~ ( l1_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf(t11_tmap_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( ( v1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) )
            & ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) @ A ) ) ) ) )).

thf('15',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( m1_pre_topc @ X10 @ X11 )
      | ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X10 ) @ ( u1_pre_topc @ X10 ) ) @ X11 )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[t11_tmap_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,
    ( ( m1_pre_topc @ sk_D @ sk_C )
    | ~ ( l1_pre_topc @ sk_C ) ),
    inference('sup+',[status(thm)],['13','17'])).

thf('19',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

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
    m1_pre_topc @ sk_D @ sk_C ),
    inference(demod,[status(thm)],['18','23'])).

thf(t35_borsuk_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( r1_tarski @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) )).

thf('25',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( m1_pre_topc @ X23 @ X24 )
      | ( r1_tarski @ ( u1_struct_0 @ X23 ) @ ( u1_struct_0 @ X24 ) )
      | ~ ( l1_pre_topc @ X24 ) ) ),
    inference(cnf,[status(esa)],[t35_borsuk_1])).

thf('26',plain,
    ( ~ ( l1_pre_topc @ sk_C )
    | ( r1_tarski @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['21','22'])).

thf('28',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['26','27'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('29',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('30',plain,
    ( ~ ( r1_tarski @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D ) )
    | ( ( u1_struct_0 @ sk_C )
      = ( u1_struct_0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('33',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['32'])).

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

thf('34',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( m1_pre_topc @ X25 @ X26 )
      | ~ ( r1_tarski @ ( u1_struct_0 @ X25 ) @ ( u1_struct_0 @ X27 ) )
      | ( m1_pre_topc @ X25 @ X27 )
      | ~ ( m1_pre_topc @ X27 @ X26 )
      | ~ ( l1_pre_topc @ X26 )
      | ~ ( v2_pre_topc @ X26 ) ) ),
    inference(cnf,[status(esa)],[t4_tsep_1])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 )
      | ( m1_pre_topc @ X0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_pre_topc @ X0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v2_pre_topc @ X1 ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( m1_pre_topc @ sk_C @ sk_C ) ),
    inference('sup-',[status(thm)],['31','36'])).

thf('38',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    m1_pre_topc @ sk_C @ sk_C ),
    inference(demod,[status(thm)],['37','38','39'])).

thf('41',plain,(
    ! [X22: $i] :
      ( ( m1_pre_topc @ X22 @ X22 )
      | ~ ( l1_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

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

thf('42',plain,(
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

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X1 )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ( m1_pre_topc @ X0 @ ( k1_tsep_1 @ X0 @ X0 @ X1 ) )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_pre_topc @ X0 @ ( k1_tsep_1 @ X0 @ X0 @ X1 ) )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,
    ( ~ ( l1_pre_topc @ sk_C )
    | ( v2_struct_0 @ sk_C )
    | ~ ( v2_pre_topc @ sk_C )
    | ( v2_struct_0 @ sk_C )
    | ( m1_pre_topc @ sk_C @ ( k1_tsep_1 @ sk_C @ sk_C @ sk_C ) ) ),
    inference('sup-',[status(thm)],['40','44'])).

thf('46',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['21','22'])).

thf('47',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( v2_pre_topc @ B ) ) ) )).

thf('48',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_pre_topc @ X3 @ X4 )
      | ( v2_pre_topc @ X3 )
      | ~ ( l1_pre_topc @ X4 )
      | ~ ( v2_pre_topc @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc1_pre_topc])).

thf('49',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_pre_topc @ sk_C ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    v2_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['49','50','51'])).

thf('53',plain,(
    m1_pre_topc @ sk_C @ sk_C ),
    inference(demod,[status(thm)],['37','38','39'])).

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

thf('54',plain,(
    ! [X20: $i,X21: $i] :
      ( ( v2_struct_0 @ X20 )
      | ~ ( m1_pre_topc @ X20 @ X21 )
      | ( ( k1_tsep_1 @ X21 @ X20 @ X20 )
        = ( g1_pre_topc @ ( u1_struct_0 @ X20 ) @ ( u1_pre_topc @ X20 ) ) )
      | ~ ( l1_pre_topc @ X21 )
      | ~ ( v2_pre_topc @ X21 )
      | ( v2_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t25_tmap_1])).

thf('55',plain,
    ( ( v2_struct_0 @ sk_C )
    | ~ ( v2_pre_topc @ sk_C )
    | ~ ( l1_pre_topc @ sk_C )
    | ( ( k1_tsep_1 @ sk_C @ sk_C @ sk_C )
      = ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) ) )
    | ( v2_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    v2_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['49','50','51'])).

thf('57',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['21','22'])).

thf('58',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) )
    = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( ( k1_tsep_1 @ sk_C @ sk_C @ sk_C )
      = sk_D )
    | ( v2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['55','56','57','58'])).

thf('60',plain,
    ( ( ( k1_tsep_1 @ sk_C @ sk_C @ sk_C )
      = sk_D )
    | ( v2_struct_0 @ sk_C ) ),
    inference(simplify,[status(thm)],['59'])).

thf('61',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,
    ( ( k1_tsep_1 @ sk_C @ sk_C @ sk_C )
    = sk_D ),
    inference(clc,[status(thm)],['60','61'])).

thf('63',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_C )
    | ( m1_pre_topc @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['45','46','52','62'])).

thf('64',plain,
    ( ( m1_pre_topc @ sk_C @ sk_D )
    | ( v2_struct_0 @ sk_C ) ),
    inference(simplify,[status(thm)],['63'])).

thf('65',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(clc,[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( m1_pre_topc @ X23 @ X24 )
      | ( r1_tarski @ ( u1_struct_0 @ X23 ) @ ( u1_struct_0 @ X24 ) )
      | ~ ( l1_pre_topc @ X24 ) ) ),
    inference(cnf,[status(esa)],[t35_borsuk_1])).

thf('68',plain,
    ( ~ ( l1_pre_topc @ sk_D )
    | ( r1_tarski @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( m1_pre_topc @ X7 @ X8 )
      | ( l1_pre_topc @ X7 )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('71',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_D ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['71','72'])).

thf('74',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['68','73'])).

thf('75',plain,
    ( ( u1_struct_0 @ sk_C )
    = ( u1_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['30','74'])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('76',plain,(
    ! [X5: $i] :
      ( ( ( k2_struct_0 @ X5 )
        = ( u1_struct_0 @ X5 ) )
      | ~ ( l1_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('77',plain,
    ( ( u1_struct_0 @ sk_C )
    = ( u1_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['30','74'])).

thf('78',plain,
    ( ( ( u1_struct_0 @ sk_C )
      = ( k2_struct_0 @ sk_D ) )
    | ~ ( l1_struct_0 @ sk_D ) ),
    inference('sup+',[status(thm)],['76','77'])).

thf('79',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['71','72'])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('80',plain,(
    ! [X6: $i] :
      ( ( l1_struct_0 @ X6 )
      | ~ ( l1_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('81',plain,(
    l1_struct_0 @ sk_D ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,
    ( ( u1_struct_0 @ sk_C )
    = ( k2_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['78','81'])).

thf('83',plain,
    ( ( k2_struct_0 @ sk_D )
    = ( u1_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['75','82'])).

thf('84',plain,(
    ! [X5: $i] :
      ( ( ( k2_struct_0 @ X5 )
        = ( u1_struct_0 @ X5 ) )
      | ~ ( l1_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('85',plain,
    ( ( u1_struct_0 @ sk_C )
    = ( k2_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['78','81'])).

thf('86',plain,
    ( ( ( k2_struct_0 @ sk_C )
      = ( k2_struct_0 @ sk_D ) )
    | ~ ( l1_struct_0 @ sk_C ) ),
    inference('sup+',[status(thm)],['84','85'])).

thf('87',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['21','22'])).

thf('88',plain,(
    ! [X6: $i] :
      ( ( l1_struct_0 @ X6 )
      | ~ ( l1_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('89',plain,(
    l1_struct_0 @ sk_C ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,
    ( ( k2_struct_0 @ sk_C )
    = ( k2_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['86','89'])).

thf('91',plain,
    ( ( k2_struct_0 @ sk_C )
    = ( u1_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['83','90'])).

thf('92',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ~ ( v1_tsep_1 @ X1 @ sk_D )
      | ~ ( m1_pre_topc @ X1 @ sk_D )
      | ~ ( m1_subset_1 @ X2 @ ( k2_struct_0 @ sk_C ) )
      | ~ ( r1_tmap_1 @ X1 @ sk_B @ ( k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E ) @ X2 )
      | ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X1 ) )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ( v2_struct_0 @ X1 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['12','91'])).

thf('93',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ~ ( m1_pre_topc @ sk_C @ sk_A )
    | ~ ( m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_C ) )
    | ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F )
    | ~ ( m1_subset_1 @ sk_F @ ( k2_struct_0 @ sk_C ) )
    | ~ ( m1_pre_topc @ sk_C @ sk_D )
    | ~ ( v1_tsep_1 @ sk_C @ sk_D )
    | ~ ( m1_pre_topc @ sk_D @ sk_A )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['3','92'])).

thf('94',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,
    ( ( u1_struct_0 @ sk_C )
    = ( k2_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['78','81'])).

thf('98',plain,
    ( ( k2_struct_0 @ sk_C )
    = ( k2_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['86','89'])).

thf('99',plain,
    ( ( u1_struct_0 @ sk_C )
    = ( k2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['97','98'])).

thf('100',plain,(
    ! [X5: $i] :
      ( ( ( k2_struct_0 @ X5 )
        = ( u1_struct_0 @ X5 ) )
      | ~ ( l1_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('101',plain,(
    m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    sk_F = sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['101','102'])).

thf('104',plain,
    ( ( m1_subset_1 @ sk_F @ ( k2_struct_0 @ sk_C ) )
    | ~ ( l1_struct_0 @ sk_C ) ),
    inference('sup+',[status(thm)],['100','103'])).

thf('105',plain,(
    l1_struct_0 @ sk_C ),
    inference('sup-',[status(thm)],['87','88'])).

thf('106',plain,(
    m1_subset_1 @ sk_F @ ( k2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['104','105'])).

thf('107',plain,(
    m1_subset_1 @ sk_F @ ( k2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['104','105'])).

thf('108',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(clc,[status(thm)],['64','65'])).

thf('109',plain,(
    ! [X5: $i] :
      ( ( ( k2_struct_0 @ X5 )
        = ( u1_struct_0 @ X5 ) )
      | ~ ( l1_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('110',plain,(
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

thf('111',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( m1_pre_topc @ X15 @ X16 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X15 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( l1_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('112',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['110','111'])).

thf('113',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['112'])).

thf('114',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_struct_0 @ X0 ) ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup+',[status(thm)],['109','113'])).

thf('115',plain,(
    ! [X6: $i] :
      ( ( l1_struct_0 @ X6 )
      | ~ ( l1_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('116',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_struct_0 @ X0 ) ) ) ) ),
    inference(clc,[status(thm)],['114','115'])).

thf('117',plain,
    ( ( u1_struct_0 @ sk_C )
    = ( u1_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['30','74'])).

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

thf('118',plain,(
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

thf('119',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v2_pre_topc @ X13 )
      | ~ ( l1_pre_topc @ X13 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X12 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ( v1_tsep_1 @ X12 @ X13 )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ X12 ) @ X13 )
      | ~ ( m1_pre_topc @ X12 @ X13 ) ) ),
    inference(simplify,[status(thm)],['118'])).

thf('120',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ sk_D )
      | ( v1_tsep_1 @ X0 @ sk_D )
      | ~ ( l1_pre_topc @ sk_D )
      | ~ ( v2_pre_topc @ sk_D ) ) ),
    inference('sup-',[status(thm)],['117','119'])).

thf('121',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['71','72'])).

thf('122',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_pre_topc @ X3 @ X4 )
      | ( v2_pre_topc @ X3 )
      | ~ ( l1_pre_topc @ X4 )
      | ~ ( v2_pre_topc @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc1_pre_topc])).

thf('124',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_pre_topc @ sk_D ) ),
    inference('sup-',[status(thm)],['122','123'])).

thf('125',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,(
    v2_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['124','125','126'])).

thf('128',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ sk_D )
      | ( v1_tsep_1 @ X0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['120','121','127'])).

thf('129',plain,
    ( ( u1_struct_0 @ sk_C )
    = ( k2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['97','98'])).

thf('130',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_C ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ sk_D )
      | ( v1_tsep_1 @ X0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['128','129'])).

thf('131',plain,
    ( ~ ( l1_pre_topc @ sk_C )
    | ( v1_tsep_1 @ sk_C @ sk_D )
    | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_C ) @ sk_D )
    | ~ ( m1_pre_topc @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['116','130'])).

thf('132',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['21','22'])).

thf('133',plain,
    ( ( u1_struct_0 @ sk_C )
    = ( k2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['97','98'])).

thf('134',plain,(
    ! [X5: $i] :
      ( ( ( k2_struct_0 @ X5 )
        = ( u1_struct_0 @ X5 ) )
      | ~ ( l1_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('135',plain,(
    ! [X22: $i] :
      ( ( m1_pre_topc @ X22 @ X22 )
      | ~ ( l1_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('136',plain,(
    ! [X22: $i] :
      ( ( m1_pre_topc @ X22 @ X22 )
      | ~ ( l1_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf(fc10_tops_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( v3_pre_topc @ ( k2_struct_0 @ A ) @ A ) ) )).

thf('137',plain,(
    ! [X9: $i] :
      ( ( v3_pre_topc @ ( k2_struct_0 @ X9 ) @ X9 )
      | ~ ( l1_pre_topc @ X9 )
      | ~ ( v2_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[fc10_tops_1])).

thf('138',plain,(
    ! [X5: $i] :
      ( ( ( k2_struct_0 @ X5 )
        = ( u1_struct_0 @ X5 ) )
      | ~ ( l1_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('139',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['112'])).

thf('140',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v2_pre_topc @ X13 )
      | ~ ( l1_pre_topc @ X13 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X12 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ( v1_tsep_1 @ X12 @ X13 )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ X12 ) @ X13 )
      | ~ ( m1_pre_topc @ X12 @ X13 ) ) ),
    inference(simplify,[status(thm)],['118'])).

thf('141',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X0 )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 )
      | ( v1_tsep_1 @ X0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['139','140'])).

thf('142',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ( v1_tsep_1 @ X0 @ X0 )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['141'])).

thf('143',plain,(
    ! [X0: $i] :
      ( ~ ( v3_pre_topc @ ( k2_struct_0 @ X0 ) @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X0 )
      | ( v1_tsep_1 @ X0 @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['138','142'])).

thf('144',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v1_tsep_1 @ X0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['137','143'])).

thf('145',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X0 )
      | ( v1_tsep_1 @ X0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['144'])).

thf('146',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v1_tsep_1 @ X0 @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['136','145'])).

thf('147',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( v1_tsep_1 @ X0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['146'])).

thf('148',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['112'])).

thf('149',plain,(
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

thf('150',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v2_pre_topc @ X13 )
      | ~ ( l1_pre_topc @ X13 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X12 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ( v3_pre_topc @ ( u1_struct_0 @ X12 ) @ X13 )
      | ~ ( v1_tsep_1 @ X12 @ X13 )
      | ~ ( m1_pre_topc @ X12 @ X13 ) ) ),
    inference(simplify,[status(thm)],['149'])).

thf('151',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X0 )
      | ~ ( v1_tsep_1 @ X0 @ X0 )
      | ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['148','150'])).

thf('152',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( v1_tsep_1 @ X0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['151'])).

thf('153',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X0 )
      | ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['147','152'])).

thf('154',plain,(
    ! [X0: $i] :
      ( ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['153'])).

thf('155',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['135','154'])).

thf('156',plain,(
    ! [X0: $i] :
      ( ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['155'])).

thf('157',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('158',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_pre_topc @ X0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v2_pre_topc @ X1 ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf('159',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( m1_pre_topc @ sk_D @ sk_D ) ),
    inference('sup-',[status(thm)],['157','158'])).

thf('160',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('161',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('162',plain,(
    m1_pre_topc @ sk_D @ sk_D ),
    inference(demod,[status(thm)],['159','160','161'])).

thf('163',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( m1_pre_topc @ X15 @ X16 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X15 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( l1_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('164',plain,
    ( ~ ( l1_pre_topc @ sk_D )
    | ( m1_subset_1 @ ( u1_struct_0 @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['162','163'])).

thf('165',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['71','72'])).

thf('166',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['164','165'])).

thf('167',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v2_pre_topc @ X13 )
      | ~ ( l1_pre_topc @ X13 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X12 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ( v1_tsep_1 @ X12 @ X13 )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ X12 ) @ X13 )
      | ~ ( m1_pre_topc @ X12 @ X13 ) ) ),
    inference(simplify,[status(thm)],['118'])).

thf('168',plain,
    ( ~ ( m1_pre_topc @ sk_D @ sk_D )
    | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_D ) @ sk_D )
    | ( v1_tsep_1 @ sk_D @ sk_D )
    | ~ ( l1_pre_topc @ sk_D )
    | ~ ( v2_pre_topc @ sk_D ) ),
    inference('sup-',[status(thm)],['166','167'])).

thf('169',plain,(
    m1_pre_topc @ sk_D @ sk_D ),
    inference(demod,[status(thm)],['159','160','161'])).

thf('170',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['71','72'])).

thf('171',plain,(
    v2_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['124','125','126'])).

thf('172',plain,
    ( ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_D ) @ sk_D )
    | ( v1_tsep_1 @ sk_D @ sk_D ) ),
    inference(demod,[status(thm)],['168','169','170','171'])).

thf('173',plain,
    ( ~ ( l1_pre_topc @ sk_D )
    | ~ ( v2_pre_topc @ sk_D )
    | ~ ( l1_struct_0 @ sk_D )
    | ( v1_tsep_1 @ sk_D @ sk_D ) ),
    inference('sup-',[status(thm)],['156','172'])).

thf('174',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['71','72'])).

thf('175',plain,(
    v2_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['124','125','126'])).

thf('176',plain,(
    l1_struct_0 @ sk_D ),
    inference('sup-',[status(thm)],['79','80'])).

thf('177',plain,(
    v1_tsep_1 @ sk_D @ sk_D ),
    inference(demod,[status(thm)],['173','174','175','176'])).

thf('178',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( v1_tsep_1 @ X0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['151'])).

thf('179',plain,
    ( ~ ( l1_pre_topc @ sk_D )
    | ~ ( m1_pre_topc @ sk_D @ sk_D )
    | ( v3_pre_topc @ ( u1_struct_0 @ sk_D ) @ sk_D )
    | ~ ( v2_pre_topc @ sk_D ) ),
    inference('sup-',[status(thm)],['177','178'])).

thf('180',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['71','72'])).

thf('181',plain,(
    m1_pre_topc @ sk_D @ sk_D ),
    inference(demod,[status(thm)],['159','160','161'])).

thf('182',plain,(
    v2_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['124','125','126'])).

thf('183',plain,(
    v3_pre_topc @ ( u1_struct_0 @ sk_D ) @ sk_D ),
    inference(demod,[status(thm)],['179','180','181','182'])).

thf('184',plain,
    ( ( u1_struct_0 @ sk_C )
    = ( u1_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['30','74'])).

thf('185',plain,(
    v3_pre_topc @ ( u1_struct_0 @ sk_C ) @ sk_D ),
    inference(demod,[status(thm)],['183','184'])).

thf('186',plain,
    ( ( v3_pre_topc @ ( k2_struct_0 @ sk_C ) @ sk_D )
    | ~ ( l1_struct_0 @ sk_C ) ),
    inference('sup+',[status(thm)],['134','185'])).

thf('187',plain,(
    l1_struct_0 @ sk_C ),
    inference('sup-',[status(thm)],['87','88'])).

thf('188',plain,(
    v3_pre_topc @ ( k2_struct_0 @ sk_C ) @ sk_D ),
    inference(demod,[status(thm)],['186','187'])).

thf('189',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(clc,[status(thm)],['64','65'])).

thf('190',plain,(
    v1_tsep_1 @ sk_C @ sk_D ),
    inference(demod,[status(thm)],['131','132','133','188','189'])).

thf('191',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('192',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['93','94','95','96','99','106','107','108','190','191'])).

thf('193',plain,(
    ~ ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('194',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['192','193'])).

thf('195',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('196',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['194','195'])).

thf('197',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('198',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C ) ),
    inference(clc,[status(thm)],['196','197'])).

thf('199',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('200',plain,(
    v2_struct_0 @ sk_C ),
    inference(clc,[status(thm)],['198','199'])).

thf('201',plain,(
    $false ),
    inference(demod,[status(thm)],['0','200'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.KRHv1yBY97
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:10:12 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 1.74/1.94  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.74/1.94  % Solved by: fo/fo7.sh
% 1.74/1.94  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.74/1.94  % done 2224 iterations in 1.485s
% 1.74/1.94  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.74/1.94  % SZS output start Refutation
% 1.74/1.94  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 1.74/1.94  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.74/1.94  thf(sk_C_type, type, sk_C: $i).
% 1.74/1.94  thf(sk_F_type, type, sk_F: $i).
% 1.74/1.94  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 1.74/1.94  thf(sk_B_type, type, sk_B: $i).
% 1.74/1.94  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 1.74/1.94  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.74/1.94  thf(sk_E_type, type, sk_E: $i).
% 1.74/1.94  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 1.74/1.94  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.74/1.94  thf(sk_G_type, type, sk_G: $i).
% 1.74/1.94  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 1.74/1.94  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.74/1.94  thf(r1_tmap_1_type, type, r1_tmap_1: $i > $i > $i > $i > $o).
% 1.74/1.94  thf(g1_pre_topc_type, type, g1_pre_topc: $i > $i > $i).
% 1.74/1.94  thf(sk_D_type, type, sk_D: $i).
% 1.74/1.94  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.74/1.94  thf(k1_tsep_1_type, type, k1_tsep_1: $i > $i > $i > $i).
% 1.74/1.94  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 1.74/1.94  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.74/1.94  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 1.74/1.94  thf(v1_tsep_1_type, type, v1_tsep_1: $i > $i > $o).
% 1.74/1.94  thf(k3_tmap_1_type, type, k3_tmap_1: $i > $i > $i > $i > $i > $i).
% 1.74/1.94  thf(sk_A_type, type, sk_A: $i).
% 1.74/1.94  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 1.74/1.94  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 1.74/1.94  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 1.74/1.94  thf(t88_tmap_1, conjecture,
% 1.74/1.94    (![A:$i]:
% 1.74/1.94     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.74/1.94       ( ![B:$i]:
% 1.74/1.94         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 1.74/1.94             ( l1_pre_topc @ B ) ) =>
% 1.74/1.94           ( ![C:$i]:
% 1.74/1.94             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 1.74/1.94               ( ![D:$i]:
% 1.74/1.94                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 1.74/1.94                   ( ![E:$i]:
% 1.74/1.94                     ( ( ( v1_funct_1 @ E ) & 
% 1.74/1.94                         ( v1_funct_2 @
% 1.74/1.94                           E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 1.74/1.94                         ( m1_subset_1 @
% 1.74/1.94                           E @ 
% 1.74/1.94                           ( k1_zfmisc_1 @
% 1.74/1.94                             ( k2_zfmisc_1 @
% 1.74/1.94                               ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 1.74/1.94                       ( ( ( g1_pre_topc @
% 1.74/1.94                             ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) ) =
% 1.74/1.94                           ( D ) ) =>
% 1.74/1.94                         ( ![F:$i]:
% 1.74/1.94                           ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 1.74/1.94                             ( ![G:$i]:
% 1.74/1.94                               ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) ) =>
% 1.74/1.94                                 ( ( ( ( F ) = ( G ) ) & 
% 1.74/1.94                                     ( r1_tmap_1 @
% 1.74/1.94                                       C @ B @ 
% 1.74/1.94                                       ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ G ) ) =>
% 1.74/1.94                                   ( r1_tmap_1 @ D @ B @ E @ F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 1.74/1.94  thf(zf_stmt_0, negated_conjecture,
% 1.74/1.94    (~( ![A:$i]:
% 1.74/1.94        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 1.74/1.94            ( l1_pre_topc @ A ) ) =>
% 1.74/1.94          ( ![B:$i]:
% 1.74/1.94            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 1.74/1.94                ( l1_pre_topc @ B ) ) =>
% 1.74/1.94              ( ![C:$i]:
% 1.74/1.94                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 1.74/1.94                  ( ![D:$i]:
% 1.74/1.94                    ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 1.74/1.94                      ( ![E:$i]:
% 1.74/1.94                        ( ( ( v1_funct_1 @ E ) & 
% 1.74/1.94                            ( v1_funct_2 @
% 1.74/1.94                              E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 1.74/1.94                            ( m1_subset_1 @
% 1.74/1.94                              E @ 
% 1.74/1.94                              ( k1_zfmisc_1 @
% 1.74/1.94                                ( k2_zfmisc_1 @
% 1.74/1.94                                  ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 1.74/1.94                          ( ( ( g1_pre_topc @
% 1.74/1.94                                ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) ) =
% 1.74/1.94                              ( D ) ) =>
% 1.74/1.94                            ( ![F:$i]:
% 1.74/1.94                              ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 1.74/1.94                                ( ![G:$i]:
% 1.74/1.94                                  ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) ) =>
% 1.74/1.94                                    ( ( ( ( F ) = ( G ) ) & 
% 1.74/1.94                                        ( r1_tmap_1 @
% 1.74/1.94                                          C @ B @ 
% 1.74/1.94                                          ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ G ) ) =>
% 1.74/1.94                                      ( r1_tmap_1 @ D @ B @ E @ F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 1.74/1.94    inference('cnf.neg', [status(esa)], [t88_tmap_1])).
% 1.74/1.94  thf('0', plain, (~ (v2_struct_0 @ sk_C)),
% 1.74/1.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.74/1.94  thf('1', plain,
% 1.74/1.94      ((r1_tmap_1 @ sk_C @ sk_B @ 
% 1.74/1.94        (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_G)),
% 1.74/1.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.74/1.94  thf('2', plain, (((sk_F) = (sk_G))),
% 1.74/1.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.74/1.94  thf('3', plain,
% 1.74/1.94      ((r1_tmap_1 @ sk_C @ sk_B @ 
% 1.74/1.94        (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_F)),
% 1.74/1.94      inference('demod', [status(thm)], ['1', '2'])).
% 1.74/1.94  thf('4', plain,
% 1.74/1.94      ((m1_subset_1 @ sk_E @ 
% 1.74/1.94        (k1_zfmisc_1 @ 
% 1.74/1.94         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 1.74/1.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.74/1.94  thf(t86_tmap_1, axiom,
% 1.74/1.94    (![A:$i]:
% 1.74/1.94     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.74/1.94       ( ![B:$i]:
% 1.74/1.94         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 1.74/1.94             ( l1_pre_topc @ B ) ) =>
% 1.74/1.94           ( ![C:$i]:
% 1.74/1.94             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 1.74/1.94               ( ![D:$i]:
% 1.74/1.94                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 1.74/1.94                   ( ![E:$i]:
% 1.74/1.94                     ( ( ( v1_funct_1 @ E ) & 
% 1.74/1.94                         ( v1_funct_2 @
% 1.74/1.94                           E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 1.74/1.94                         ( m1_subset_1 @
% 1.74/1.94                           E @ 
% 1.74/1.94                           ( k1_zfmisc_1 @
% 1.74/1.94                             ( k2_zfmisc_1 @
% 1.74/1.94                               ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 1.74/1.94                       ( ( ( v1_tsep_1 @ C @ D ) & ( m1_pre_topc @ C @ D ) ) =>
% 1.74/1.94                         ( ![F:$i]:
% 1.74/1.94                           ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 1.74/1.94                             ( ![G:$i]:
% 1.74/1.94                               ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) ) =>
% 1.74/1.94                                 ( ( ( F ) = ( G ) ) =>
% 1.74/1.94                                   ( ( r1_tmap_1 @ D @ B @ E @ F ) <=>
% 1.74/1.94                                     ( r1_tmap_1 @
% 1.74/1.94                                       C @ B @ 
% 1.74/1.94                                       ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ G ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 1.74/1.94  thf('5', plain,
% 1.74/1.94      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i, X35 : $i, X36 : $i, X37 : $i]:
% 1.74/1.94         ((v2_struct_0 @ X31)
% 1.74/1.94          | ~ (v2_pre_topc @ X31)
% 1.74/1.94          | ~ (l1_pre_topc @ X31)
% 1.74/1.94          | (v2_struct_0 @ X32)
% 1.74/1.94          | ~ (m1_pre_topc @ X32 @ X33)
% 1.74/1.94          | ~ (v1_tsep_1 @ X34 @ X32)
% 1.74/1.94          | ~ (m1_pre_topc @ X34 @ X32)
% 1.74/1.94          | ~ (m1_subset_1 @ X35 @ (u1_struct_0 @ X32))
% 1.74/1.94          | ((X35) != (X36))
% 1.74/1.94          | ~ (r1_tmap_1 @ X34 @ X31 @ 
% 1.74/1.94               (k3_tmap_1 @ X33 @ X31 @ X32 @ X34 @ X37) @ X36)
% 1.74/1.94          | (r1_tmap_1 @ X32 @ X31 @ X37 @ X35)
% 1.74/1.94          | ~ (m1_subset_1 @ X36 @ (u1_struct_0 @ X34))
% 1.74/1.94          | ~ (m1_subset_1 @ X37 @ 
% 1.74/1.94               (k1_zfmisc_1 @ 
% 1.74/1.94                (k2_zfmisc_1 @ (u1_struct_0 @ X32) @ (u1_struct_0 @ X31))))
% 1.74/1.94          | ~ (v1_funct_2 @ X37 @ (u1_struct_0 @ X32) @ (u1_struct_0 @ X31))
% 1.74/1.94          | ~ (v1_funct_1 @ X37)
% 1.74/1.94          | ~ (m1_pre_topc @ X34 @ X33)
% 1.74/1.94          | (v2_struct_0 @ X34)
% 1.74/1.94          | ~ (l1_pre_topc @ X33)
% 1.74/1.94          | ~ (v2_pre_topc @ X33)
% 1.74/1.94          | (v2_struct_0 @ X33))),
% 1.74/1.94      inference('cnf', [status(esa)], [t86_tmap_1])).
% 1.74/1.94  thf('6', plain,
% 1.74/1.94      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i, X36 : $i, X37 : $i]:
% 1.74/1.94         ((v2_struct_0 @ X33)
% 1.74/1.94          | ~ (v2_pre_topc @ X33)
% 1.74/1.94          | ~ (l1_pre_topc @ X33)
% 1.74/1.94          | (v2_struct_0 @ X34)
% 1.74/1.94          | ~ (m1_pre_topc @ X34 @ X33)
% 1.74/1.94          | ~ (v1_funct_1 @ X37)
% 1.74/1.94          | ~ (v1_funct_2 @ X37 @ (u1_struct_0 @ X32) @ (u1_struct_0 @ X31))
% 1.74/1.94          | ~ (m1_subset_1 @ X37 @ 
% 1.74/1.94               (k1_zfmisc_1 @ 
% 1.74/1.94                (k2_zfmisc_1 @ (u1_struct_0 @ X32) @ (u1_struct_0 @ X31))))
% 1.74/1.94          | ~ (m1_subset_1 @ X36 @ (u1_struct_0 @ X34))
% 1.74/1.94          | (r1_tmap_1 @ X32 @ X31 @ X37 @ X36)
% 1.74/1.94          | ~ (r1_tmap_1 @ X34 @ X31 @ 
% 1.74/1.94               (k3_tmap_1 @ X33 @ X31 @ X32 @ X34 @ X37) @ X36)
% 1.74/1.94          | ~ (m1_subset_1 @ X36 @ (u1_struct_0 @ X32))
% 1.74/1.94          | ~ (m1_pre_topc @ X34 @ X32)
% 1.74/1.94          | ~ (v1_tsep_1 @ X34 @ X32)
% 1.74/1.94          | ~ (m1_pre_topc @ X32 @ X33)
% 1.74/1.94          | (v2_struct_0 @ X32)
% 1.74/1.94          | ~ (l1_pre_topc @ X31)
% 1.74/1.94          | ~ (v2_pre_topc @ X31)
% 1.74/1.94          | (v2_struct_0 @ X31))),
% 1.74/1.94      inference('simplify', [status(thm)], ['5'])).
% 1.74/1.94  thf('7', plain,
% 1.74/1.94      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.74/1.94         ((v2_struct_0 @ sk_B)
% 1.74/1.94          | ~ (v2_pre_topc @ sk_B)
% 1.74/1.94          | ~ (l1_pre_topc @ sk_B)
% 1.74/1.94          | (v2_struct_0 @ sk_D)
% 1.74/1.94          | ~ (m1_pre_topc @ sk_D @ X0)
% 1.74/1.94          | ~ (v1_tsep_1 @ X1 @ sk_D)
% 1.74/1.94          | ~ (m1_pre_topc @ X1 @ sk_D)
% 1.74/1.94          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ sk_D))
% 1.74/1.94          | ~ (r1_tmap_1 @ X1 @ sk_B @ 
% 1.74/1.94               (k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E) @ X2)
% 1.74/1.94          | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X2)
% 1.74/1.94          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1))
% 1.74/1.94          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 1.74/1.94          | ~ (v1_funct_1 @ sk_E)
% 1.74/1.94          | ~ (m1_pre_topc @ X1 @ X0)
% 1.74/1.94          | (v2_struct_0 @ X1)
% 1.74/1.94          | ~ (l1_pre_topc @ X0)
% 1.74/1.94          | ~ (v2_pre_topc @ X0)
% 1.74/1.94          | (v2_struct_0 @ X0))),
% 1.74/1.94      inference('sup-', [status(thm)], ['4', '6'])).
% 1.74/1.94  thf('8', plain, ((v2_pre_topc @ sk_B)),
% 1.74/1.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.74/1.94  thf('9', plain, ((l1_pre_topc @ sk_B)),
% 1.74/1.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.74/1.94  thf('10', plain,
% 1.74/1.94      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 1.74/1.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.74/1.94  thf('11', plain, ((v1_funct_1 @ sk_E)),
% 1.74/1.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.74/1.94  thf('12', plain,
% 1.74/1.94      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.74/1.94         ((v2_struct_0 @ sk_B)
% 1.74/1.94          | (v2_struct_0 @ sk_D)
% 1.74/1.94          | ~ (m1_pre_topc @ sk_D @ X0)
% 1.74/1.94          | ~ (v1_tsep_1 @ X1 @ sk_D)
% 1.74/1.94          | ~ (m1_pre_topc @ X1 @ sk_D)
% 1.74/1.94          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ sk_D))
% 1.74/1.94          | ~ (r1_tmap_1 @ X1 @ sk_B @ 
% 1.74/1.94               (k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E) @ X2)
% 1.74/1.94          | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X2)
% 1.74/1.94          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1))
% 1.74/1.94          | ~ (m1_pre_topc @ X1 @ X0)
% 1.74/1.94          | (v2_struct_0 @ X1)
% 1.74/1.94          | ~ (l1_pre_topc @ X0)
% 1.74/1.94          | ~ (v2_pre_topc @ X0)
% 1.74/1.94          | (v2_struct_0 @ X0))),
% 1.74/1.94      inference('demod', [status(thm)], ['7', '8', '9', '10', '11'])).
% 1.74/1.94  thf('13', plain,
% 1.74/1.94      (((g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) = (sk_D))),
% 1.74/1.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.74/1.94  thf(t2_tsep_1, axiom,
% 1.74/1.94    (![A:$i]: ( ( l1_pre_topc @ A ) => ( m1_pre_topc @ A @ A ) ))).
% 1.74/1.94  thf('14', plain,
% 1.74/1.94      (![X22 : $i]: ((m1_pre_topc @ X22 @ X22) | ~ (l1_pre_topc @ X22))),
% 1.74/1.94      inference('cnf', [status(esa)], [t2_tsep_1])).
% 1.74/1.94  thf(t11_tmap_1, axiom,
% 1.74/1.94    (![A:$i]:
% 1.74/1.94     ( ( l1_pre_topc @ A ) =>
% 1.74/1.94       ( ![B:$i]:
% 1.74/1.94         ( ( m1_pre_topc @ B @ A ) =>
% 1.74/1.94           ( ( v1_pre_topc @
% 1.74/1.94               ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) & 
% 1.74/1.94             ( m1_pre_topc @
% 1.74/1.94               ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) @ A ) ) ) ) ))).
% 1.74/1.94  thf('15', plain,
% 1.74/1.94      (![X10 : $i, X11 : $i]:
% 1.74/1.94         (~ (m1_pre_topc @ X10 @ X11)
% 1.74/1.94          | (m1_pre_topc @ 
% 1.74/1.94             (g1_pre_topc @ (u1_struct_0 @ X10) @ (u1_pre_topc @ X10)) @ X11)
% 1.74/1.94          | ~ (l1_pre_topc @ X11))),
% 1.74/1.94      inference('cnf', [status(esa)], [t11_tmap_1])).
% 1.74/1.94  thf('16', plain,
% 1.74/1.94      (![X0 : $i]:
% 1.74/1.94         (~ (l1_pre_topc @ X0)
% 1.74/1.94          | ~ (l1_pre_topc @ X0)
% 1.74/1.94          | (m1_pre_topc @ 
% 1.74/1.94             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)) @ X0))),
% 1.74/1.95      inference('sup-', [status(thm)], ['14', '15'])).
% 1.74/1.95  thf('17', plain,
% 1.74/1.95      (![X0 : $i]:
% 1.74/1.95         ((m1_pre_topc @ 
% 1.74/1.95           (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)) @ X0)
% 1.74/1.95          | ~ (l1_pre_topc @ X0))),
% 1.74/1.95      inference('simplify', [status(thm)], ['16'])).
% 1.74/1.95  thf('18', plain, (((m1_pre_topc @ sk_D @ sk_C) | ~ (l1_pre_topc @ sk_C))),
% 1.74/1.95      inference('sup+', [status(thm)], ['13', '17'])).
% 1.74/1.95  thf('19', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 1.74/1.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.74/1.95  thf(dt_m1_pre_topc, axiom,
% 1.74/1.95    (![A:$i]:
% 1.74/1.95     ( ( l1_pre_topc @ A ) =>
% 1.74/1.95       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 1.74/1.95  thf('20', plain,
% 1.74/1.95      (![X7 : $i, X8 : $i]:
% 1.74/1.95         (~ (m1_pre_topc @ X7 @ X8) | (l1_pre_topc @ X7) | ~ (l1_pre_topc @ X8))),
% 1.74/1.95      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 1.74/1.95  thf('21', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_C))),
% 1.74/1.95      inference('sup-', [status(thm)], ['19', '20'])).
% 1.74/1.95  thf('22', plain, ((l1_pre_topc @ sk_A)),
% 1.74/1.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.74/1.95  thf('23', plain, ((l1_pre_topc @ sk_C)),
% 1.74/1.95      inference('demod', [status(thm)], ['21', '22'])).
% 1.74/1.95  thf('24', plain, ((m1_pre_topc @ sk_D @ sk_C)),
% 1.74/1.95      inference('demod', [status(thm)], ['18', '23'])).
% 1.74/1.95  thf(t35_borsuk_1, axiom,
% 1.74/1.95    (![A:$i]:
% 1.74/1.95     ( ( l1_pre_topc @ A ) =>
% 1.74/1.95       ( ![B:$i]:
% 1.74/1.95         ( ( m1_pre_topc @ B @ A ) =>
% 1.74/1.95           ( r1_tarski @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ))).
% 1.74/1.95  thf('25', plain,
% 1.74/1.95      (![X23 : $i, X24 : $i]:
% 1.74/1.95         (~ (m1_pre_topc @ X23 @ X24)
% 1.74/1.95          | (r1_tarski @ (u1_struct_0 @ X23) @ (u1_struct_0 @ X24))
% 1.74/1.95          | ~ (l1_pre_topc @ X24))),
% 1.74/1.95      inference('cnf', [status(esa)], [t35_borsuk_1])).
% 1.74/1.95  thf('26', plain,
% 1.74/1.95      ((~ (l1_pre_topc @ sk_C)
% 1.74/1.95        | (r1_tarski @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_C)))),
% 1.74/1.95      inference('sup-', [status(thm)], ['24', '25'])).
% 1.74/1.95  thf('27', plain, ((l1_pre_topc @ sk_C)),
% 1.74/1.95      inference('demod', [status(thm)], ['21', '22'])).
% 1.74/1.95  thf('28', plain, ((r1_tarski @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_C))),
% 1.74/1.95      inference('demod', [status(thm)], ['26', '27'])).
% 1.74/1.95  thf(d10_xboole_0, axiom,
% 1.74/1.95    (![A:$i,B:$i]:
% 1.74/1.95     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.74/1.95  thf('29', plain,
% 1.74/1.95      (![X0 : $i, X2 : $i]:
% 1.74/1.95         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 1.74/1.95      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.74/1.95  thf('30', plain,
% 1.74/1.95      ((~ (r1_tarski @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D))
% 1.74/1.95        | ((u1_struct_0 @ sk_C) = (u1_struct_0 @ sk_D)))),
% 1.74/1.95      inference('sup-', [status(thm)], ['28', '29'])).
% 1.74/1.95  thf('31', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 1.74/1.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.74/1.95  thf('32', plain,
% 1.74/1.95      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 1.74/1.95      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.74/1.95  thf('33', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 1.74/1.95      inference('simplify', [status(thm)], ['32'])).
% 1.74/1.95  thf(t4_tsep_1, axiom,
% 1.74/1.95    (![A:$i]:
% 1.74/1.95     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.74/1.95       ( ![B:$i]:
% 1.74/1.95         ( ( m1_pre_topc @ B @ A ) =>
% 1.74/1.95           ( ![C:$i]:
% 1.74/1.95             ( ( m1_pre_topc @ C @ A ) =>
% 1.74/1.95               ( ( r1_tarski @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ C ) ) <=>
% 1.74/1.95                 ( m1_pre_topc @ B @ C ) ) ) ) ) ) ))).
% 1.74/1.95  thf('34', plain,
% 1.74/1.95      (![X25 : $i, X26 : $i, X27 : $i]:
% 1.74/1.95         (~ (m1_pre_topc @ X25 @ X26)
% 1.74/1.95          | ~ (r1_tarski @ (u1_struct_0 @ X25) @ (u1_struct_0 @ X27))
% 1.74/1.95          | (m1_pre_topc @ X25 @ X27)
% 1.74/1.95          | ~ (m1_pre_topc @ X27 @ X26)
% 1.74/1.95          | ~ (l1_pre_topc @ X26)
% 1.74/1.95          | ~ (v2_pre_topc @ X26))),
% 1.74/1.95      inference('cnf', [status(esa)], [t4_tsep_1])).
% 1.74/1.95  thf('35', plain,
% 1.74/1.95      (![X0 : $i, X1 : $i]:
% 1.74/1.95         (~ (v2_pre_topc @ X1)
% 1.74/1.95          | ~ (l1_pre_topc @ X1)
% 1.74/1.95          | ~ (m1_pre_topc @ X0 @ X1)
% 1.74/1.95          | (m1_pre_topc @ X0 @ X0)
% 1.74/1.95          | ~ (m1_pre_topc @ X0 @ X1))),
% 1.74/1.95      inference('sup-', [status(thm)], ['33', '34'])).
% 1.74/1.95  thf('36', plain,
% 1.74/1.95      (![X0 : $i, X1 : $i]:
% 1.74/1.95         ((m1_pre_topc @ X0 @ X0)
% 1.74/1.95          | ~ (m1_pre_topc @ X0 @ X1)
% 1.74/1.95          | ~ (l1_pre_topc @ X1)
% 1.74/1.95          | ~ (v2_pre_topc @ X1))),
% 1.74/1.95      inference('simplify', [status(thm)], ['35'])).
% 1.74/1.95  thf('37', plain,
% 1.74/1.95      ((~ (v2_pre_topc @ sk_A)
% 1.74/1.95        | ~ (l1_pre_topc @ sk_A)
% 1.74/1.95        | (m1_pre_topc @ sk_C @ sk_C))),
% 1.74/1.95      inference('sup-', [status(thm)], ['31', '36'])).
% 1.74/1.95  thf('38', plain, ((v2_pre_topc @ sk_A)),
% 1.74/1.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.74/1.95  thf('39', plain, ((l1_pre_topc @ sk_A)),
% 1.74/1.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.74/1.95  thf('40', plain, ((m1_pre_topc @ sk_C @ sk_C)),
% 1.74/1.95      inference('demod', [status(thm)], ['37', '38', '39'])).
% 1.74/1.95  thf('41', plain,
% 1.74/1.95      (![X22 : $i]: ((m1_pre_topc @ X22 @ X22) | ~ (l1_pre_topc @ X22))),
% 1.74/1.95      inference('cnf', [status(esa)], [t2_tsep_1])).
% 1.74/1.95  thf(t22_tsep_1, axiom,
% 1.74/1.95    (![A:$i]:
% 1.74/1.95     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.74/1.95       ( ![B:$i]:
% 1.74/1.95         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 1.74/1.95           ( ![C:$i]:
% 1.74/1.95             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 1.74/1.95               ( m1_pre_topc @ B @ ( k1_tsep_1 @ A @ B @ C ) ) ) ) ) ) ))).
% 1.74/1.95  thf('42', plain,
% 1.74/1.95      (![X17 : $i, X18 : $i, X19 : $i]:
% 1.74/1.95         ((v2_struct_0 @ X17)
% 1.74/1.95          | ~ (m1_pre_topc @ X17 @ X18)
% 1.74/1.95          | (m1_pre_topc @ X17 @ (k1_tsep_1 @ X18 @ X17 @ X19))
% 1.74/1.95          | ~ (m1_pre_topc @ X19 @ X18)
% 1.74/1.95          | (v2_struct_0 @ X19)
% 1.74/1.95          | ~ (l1_pre_topc @ X18)
% 1.74/1.95          | ~ (v2_pre_topc @ X18)
% 1.74/1.95          | (v2_struct_0 @ X18))),
% 1.74/1.95      inference('cnf', [status(esa)], [t22_tsep_1])).
% 1.74/1.95  thf('43', plain,
% 1.74/1.95      (![X0 : $i, X1 : $i]:
% 1.74/1.95         (~ (l1_pre_topc @ X0)
% 1.74/1.95          | (v2_struct_0 @ X0)
% 1.74/1.95          | ~ (v2_pre_topc @ X0)
% 1.74/1.95          | ~ (l1_pre_topc @ X0)
% 1.74/1.95          | (v2_struct_0 @ X1)
% 1.74/1.95          | ~ (m1_pre_topc @ X1 @ X0)
% 1.74/1.95          | (m1_pre_topc @ X0 @ (k1_tsep_1 @ X0 @ X0 @ X1))
% 1.74/1.95          | (v2_struct_0 @ X0))),
% 1.74/1.95      inference('sup-', [status(thm)], ['41', '42'])).
% 1.74/1.95  thf('44', plain,
% 1.74/1.95      (![X0 : $i, X1 : $i]:
% 1.74/1.95         ((m1_pre_topc @ X0 @ (k1_tsep_1 @ X0 @ X0 @ X1))
% 1.74/1.95          | ~ (m1_pre_topc @ X1 @ X0)
% 1.74/1.95          | (v2_struct_0 @ X1)
% 1.74/1.95          | ~ (v2_pre_topc @ X0)
% 1.74/1.95          | (v2_struct_0 @ X0)
% 1.74/1.95          | ~ (l1_pre_topc @ X0))),
% 1.74/1.95      inference('simplify', [status(thm)], ['43'])).
% 1.74/1.95  thf('45', plain,
% 1.74/1.95      ((~ (l1_pre_topc @ sk_C)
% 1.74/1.95        | (v2_struct_0 @ sk_C)
% 1.74/1.95        | ~ (v2_pre_topc @ sk_C)
% 1.74/1.95        | (v2_struct_0 @ sk_C)
% 1.74/1.95        | (m1_pre_topc @ sk_C @ (k1_tsep_1 @ sk_C @ sk_C @ sk_C)))),
% 1.74/1.95      inference('sup-', [status(thm)], ['40', '44'])).
% 1.74/1.95  thf('46', plain, ((l1_pre_topc @ sk_C)),
% 1.74/1.95      inference('demod', [status(thm)], ['21', '22'])).
% 1.74/1.95  thf('47', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 1.74/1.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.74/1.95  thf(cc1_pre_topc, axiom,
% 1.74/1.95    (![A:$i]:
% 1.74/1.95     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.74/1.95       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( v2_pre_topc @ B ) ) ) ))).
% 1.74/1.95  thf('48', plain,
% 1.74/1.95      (![X3 : $i, X4 : $i]:
% 1.74/1.95         (~ (m1_pre_topc @ X3 @ X4)
% 1.74/1.95          | (v2_pre_topc @ X3)
% 1.74/1.95          | ~ (l1_pre_topc @ X4)
% 1.74/1.95          | ~ (v2_pre_topc @ X4))),
% 1.74/1.95      inference('cnf', [status(esa)], [cc1_pre_topc])).
% 1.74/1.95  thf('49', plain,
% 1.74/1.95      ((~ (v2_pre_topc @ sk_A) | ~ (l1_pre_topc @ sk_A) | (v2_pre_topc @ sk_C))),
% 1.74/1.95      inference('sup-', [status(thm)], ['47', '48'])).
% 1.74/1.95  thf('50', plain, ((v2_pre_topc @ sk_A)),
% 1.74/1.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.74/1.95  thf('51', plain, ((l1_pre_topc @ sk_A)),
% 1.74/1.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.74/1.95  thf('52', plain, ((v2_pre_topc @ sk_C)),
% 1.74/1.95      inference('demod', [status(thm)], ['49', '50', '51'])).
% 1.74/1.95  thf('53', plain, ((m1_pre_topc @ sk_C @ sk_C)),
% 1.74/1.95      inference('demod', [status(thm)], ['37', '38', '39'])).
% 1.74/1.95  thf(t25_tmap_1, axiom,
% 1.74/1.95    (![A:$i]:
% 1.74/1.95     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.74/1.95       ( ![B:$i]:
% 1.74/1.95         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 1.74/1.95           ( ( k1_tsep_1 @ A @ B @ B ) =
% 1.74/1.95             ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ))).
% 1.74/1.95  thf('54', plain,
% 1.74/1.95      (![X20 : $i, X21 : $i]:
% 1.74/1.95         ((v2_struct_0 @ X20)
% 1.74/1.95          | ~ (m1_pre_topc @ X20 @ X21)
% 1.74/1.95          | ((k1_tsep_1 @ X21 @ X20 @ X20)
% 1.74/1.95              = (g1_pre_topc @ (u1_struct_0 @ X20) @ (u1_pre_topc @ X20)))
% 1.74/1.95          | ~ (l1_pre_topc @ X21)
% 1.74/1.95          | ~ (v2_pre_topc @ X21)
% 1.74/1.95          | (v2_struct_0 @ X21))),
% 1.74/1.95      inference('cnf', [status(esa)], [t25_tmap_1])).
% 1.74/1.95  thf('55', plain,
% 1.74/1.95      (((v2_struct_0 @ sk_C)
% 1.74/1.95        | ~ (v2_pre_topc @ sk_C)
% 1.74/1.95        | ~ (l1_pre_topc @ sk_C)
% 1.74/1.95        | ((k1_tsep_1 @ sk_C @ sk_C @ sk_C)
% 1.74/1.95            = (g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)))
% 1.74/1.95        | (v2_struct_0 @ sk_C))),
% 1.74/1.95      inference('sup-', [status(thm)], ['53', '54'])).
% 1.74/1.95  thf('56', plain, ((v2_pre_topc @ sk_C)),
% 1.74/1.95      inference('demod', [status(thm)], ['49', '50', '51'])).
% 1.74/1.95  thf('57', plain, ((l1_pre_topc @ sk_C)),
% 1.74/1.95      inference('demod', [status(thm)], ['21', '22'])).
% 1.74/1.95  thf('58', plain,
% 1.74/1.95      (((g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) = (sk_D))),
% 1.74/1.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.74/1.95  thf('59', plain,
% 1.74/1.95      (((v2_struct_0 @ sk_C)
% 1.74/1.95        | ((k1_tsep_1 @ sk_C @ sk_C @ sk_C) = (sk_D))
% 1.74/1.95        | (v2_struct_0 @ sk_C))),
% 1.74/1.95      inference('demod', [status(thm)], ['55', '56', '57', '58'])).
% 1.74/1.95  thf('60', plain,
% 1.74/1.95      ((((k1_tsep_1 @ sk_C @ sk_C @ sk_C) = (sk_D)) | (v2_struct_0 @ sk_C))),
% 1.74/1.95      inference('simplify', [status(thm)], ['59'])).
% 1.74/1.95  thf('61', plain, (~ (v2_struct_0 @ sk_C)),
% 1.74/1.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.74/1.95  thf('62', plain, (((k1_tsep_1 @ sk_C @ sk_C @ sk_C) = (sk_D))),
% 1.74/1.95      inference('clc', [status(thm)], ['60', '61'])).
% 1.74/1.95  thf('63', plain,
% 1.74/1.95      (((v2_struct_0 @ sk_C)
% 1.74/1.95        | (v2_struct_0 @ sk_C)
% 1.74/1.95        | (m1_pre_topc @ sk_C @ sk_D))),
% 1.74/1.95      inference('demod', [status(thm)], ['45', '46', '52', '62'])).
% 1.74/1.95  thf('64', plain, (((m1_pre_topc @ sk_C @ sk_D) | (v2_struct_0 @ sk_C))),
% 1.74/1.95      inference('simplify', [status(thm)], ['63'])).
% 1.74/1.95  thf('65', plain, (~ (v2_struct_0 @ sk_C)),
% 1.74/1.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.74/1.95  thf('66', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 1.74/1.95      inference('clc', [status(thm)], ['64', '65'])).
% 1.74/1.95  thf('67', plain,
% 1.74/1.95      (![X23 : $i, X24 : $i]:
% 1.74/1.95         (~ (m1_pre_topc @ X23 @ X24)
% 1.74/1.95          | (r1_tarski @ (u1_struct_0 @ X23) @ (u1_struct_0 @ X24))
% 1.74/1.95          | ~ (l1_pre_topc @ X24))),
% 1.74/1.95      inference('cnf', [status(esa)], [t35_borsuk_1])).
% 1.74/1.95  thf('68', plain,
% 1.74/1.95      ((~ (l1_pre_topc @ sk_D)
% 1.74/1.95        | (r1_tarski @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D)))),
% 1.74/1.95      inference('sup-', [status(thm)], ['66', '67'])).
% 1.74/1.95  thf('69', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 1.74/1.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.74/1.95  thf('70', plain,
% 1.74/1.95      (![X7 : $i, X8 : $i]:
% 1.74/1.95         (~ (m1_pre_topc @ X7 @ X8) | (l1_pre_topc @ X7) | ~ (l1_pre_topc @ X8))),
% 1.74/1.95      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 1.74/1.95  thf('71', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_D))),
% 1.74/1.95      inference('sup-', [status(thm)], ['69', '70'])).
% 1.74/1.95  thf('72', plain, ((l1_pre_topc @ sk_A)),
% 1.74/1.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.74/1.95  thf('73', plain, ((l1_pre_topc @ sk_D)),
% 1.74/1.95      inference('demod', [status(thm)], ['71', '72'])).
% 1.74/1.95  thf('74', plain, ((r1_tarski @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D))),
% 1.74/1.95      inference('demod', [status(thm)], ['68', '73'])).
% 1.74/1.95  thf('75', plain, (((u1_struct_0 @ sk_C) = (u1_struct_0 @ sk_D))),
% 1.74/1.95      inference('demod', [status(thm)], ['30', '74'])).
% 1.74/1.95  thf(d3_struct_0, axiom,
% 1.74/1.95    (![A:$i]:
% 1.74/1.95     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 1.74/1.95  thf('76', plain,
% 1.74/1.95      (![X5 : $i]:
% 1.74/1.95         (((k2_struct_0 @ X5) = (u1_struct_0 @ X5)) | ~ (l1_struct_0 @ X5))),
% 1.74/1.95      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.74/1.95  thf('77', plain, (((u1_struct_0 @ sk_C) = (u1_struct_0 @ sk_D))),
% 1.74/1.95      inference('demod', [status(thm)], ['30', '74'])).
% 1.74/1.95  thf('78', plain,
% 1.74/1.95      ((((u1_struct_0 @ sk_C) = (k2_struct_0 @ sk_D)) | ~ (l1_struct_0 @ sk_D))),
% 1.74/1.95      inference('sup+', [status(thm)], ['76', '77'])).
% 1.74/1.95  thf('79', plain, ((l1_pre_topc @ sk_D)),
% 1.74/1.95      inference('demod', [status(thm)], ['71', '72'])).
% 1.74/1.95  thf(dt_l1_pre_topc, axiom,
% 1.74/1.95    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 1.74/1.95  thf('80', plain, (![X6 : $i]: ((l1_struct_0 @ X6) | ~ (l1_pre_topc @ X6))),
% 1.74/1.95      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 1.74/1.95  thf('81', plain, ((l1_struct_0 @ sk_D)),
% 1.74/1.95      inference('sup-', [status(thm)], ['79', '80'])).
% 1.74/1.95  thf('82', plain, (((u1_struct_0 @ sk_C) = (k2_struct_0 @ sk_D))),
% 1.74/1.95      inference('demod', [status(thm)], ['78', '81'])).
% 1.74/1.95  thf('83', plain, (((k2_struct_0 @ sk_D) = (u1_struct_0 @ sk_D))),
% 1.74/1.95      inference('demod', [status(thm)], ['75', '82'])).
% 1.74/1.95  thf('84', plain,
% 1.74/1.95      (![X5 : $i]:
% 1.74/1.95         (((k2_struct_0 @ X5) = (u1_struct_0 @ X5)) | ~ (l1_struct_0 @ X5))),
% 1.74/1.95      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.74/1.95  thf('85', plain, (((u1_struct_0 @ sk_C) = (k2_struct_0 @ sk_D))),
% 1.74/1.95      inference('demod', [status(thm)], ['78', '81'])).
% 1.74/1.95  thf('86', plain,
% 1.74/1.95      ((((k2_struct_0 @ sk_C) = (k2_struct_0 @ sk_D)) | ~ (l1_struct_0 @ sk_C))),
% 1.74/1.95      inference('sup+', [status(thm)], ['84', '85'])).
% 1.74/1.95  thf('87', plain, ((l1_pre_topc @ sk_C)),
% 1.74/1.95      inference('demod', [status(thm)], ['21', '22'])).
% 1.74/1.95  thf('88', plain, (![X6 : $i]: ((l1_struct_0 @ X6) | ~ (l1_pre_topc @ X6))),
% 1.74/1.95      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 1.74/1.95  thf('89', plain, ((l1_struct_0 @ sk_C)),
% 1.74/1.95      inference('sup-', [status(thm)], ['87', '88'])).
% 1.74/1.95  thf('90', plain, (((k2_struct_0 @ sk_C) = (k2_struct_0 @ sk_D))),
% 1.74/1.95      inference('demod', [status(thm)], ['86', '89'])).
% 1.74/1.95  thf('91', plain, (((k2_struct_0 @ sk_C) = (u1_struct_0 @ sk_D))),
% 1.74/1.95      inference('demod', [status(thm)], ['83', '90'])).
% 1.74/1.95  thf('92', plain,
% 1.74/1.95      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.74/1.95         ((v2_struct_0 @ sk_B)
% 1.74/1.95          | (v2_struct_0 @ sk_D)
% 1.74/1.95          | ~ (m1_pre_topc @ sk_D @ X0)
% 1.74/1.95          | ~ (v1_tsep_1 @ X1 @ sk_D)
% 1.74/1.95          | ~ (m1_pre_topc @ X1 @ sk_D)
% 1.74/1.95          | ~ (m1_subset_1 @ X2 @ (k2_struct_0 @ sk_C))
% 1.74/1.95          | ~ (r1_tmap_1 @ X1 @ sk_B @ 
% 1.74/1.95               (k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E) @ X2)
% 1.74/1.95          | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X2)
% 1.74/1.95          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1))
% 1.74/1.95          | ~ (m1_pre_topc @ X1 @ X0)
% 1.74/1.95          | (v2_struct_0 @ X1)
% 1.74/1.95          | ~ (l1_pre_topc @ X0)
% 1.74/1.95          | ~ (v2_pre_topc @ X0)
% 1.74/1.95          | (v2_struct_0 @ X0))),
% 1.74/1.95      inference('demod', [status(thm)], ['12', '91'])).
% 1.74/1.95  thf('93', plain,
% 1.74/1.95      (((v2_struct_0 @ sk_A)
% 1.74/1.95        | ~ (v2_pre_topc @ sk_A)
% 1.74/1.95        | ~ (l1_pre_topc @ sk_A)
% 1.74/1.95        | (v2_struct_0 @ sk_C)
% 1.74/1.95        | ~ (m1_pre_topc @ sk_C @ sk_A)
% 1.74/1.95        | ~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C))
% 1.74/1.95        | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)
% 1.74/1.95        | ~ (m1_subset_1 @ sk_F @ (k2_struct_0 @ sk_C))
% 1.74/1.95        | ~ (m1_pre_topc @ sk_C @ sk_D)
% 1.74/1.95        | ~ (v1_tsep_1 @ sk_C @ sk_D)
% 1.74/1.95        | ~ (m1_pre_topc @ sk_D @ sk_A)
% 1.74/1.95        | (v2_struct_0 @ sk_D)
% 1.74/1.95        | (v2_struct_0 @ sk_B))),
% 1.74/1.95      inference('sup-', [status(thm)], ['3', '92'])).
% 1.74/1.95  thf('94', plain, ((v2_pre_topc @ sk_A)),
% 1.74/1.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.74/1.95  thf('95', plain, ((l1_pre_topc @ sk_A)),
% 1.74/1.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.74/1.95  thf('96', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 1.74/1.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.74/1.95  thf('97', plain, (((u1_struct_0 @ sk_C) = (k2_struct_0 @ sk_D))),
% 1.74/1.95      inference('demod', [status(thm)], ['78', '81'])).
% 1.74/1.95  thf('98', plain, (((k2_struct_0 @ sk_C) = (k2_struct_0 @ sk_D))),
% 1.74/1.95      inference('demod', [status(thm)], ['86', '89'])).
% 1.74/1.95  thf('99', plain, (((u1_struct_0 @ sk_C) = (k2_struct_0 @ sk_C))),
% 1.74/1.95      inference('demod', [status(thm)], ['97', '98'])).
% 1.74/1.95  thf('100', plain,
% 1.74/1.95      (![X5 : $i]:
% 1.74/1.95         (((k2_struct_0 @ X5) = (u1_struct_0 @ X5)) | ~ (l1_struct_0 @ X5))),
% 1.74/1.95      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.74/1.95  thf('101', plain, ((m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_C))),
% 1.74/1.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.74/1.95  thf('102', plain, (((sk_F) = (sk_G))),
% 1.74/1.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.74/1.95  thf('103', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C))),
% 1.74/1.95      inference('demod', [status(thm)], ['101', '102'])).
% 1.74/1.95  thf('104', plain,
% 1.74/1.95      (((m1_subset_1 @ sk_F @ (k2_struct_0 @ sk_C)) | ~ (l1_struct_0 @ sk_C))),
% 1.74/1.95      inference('sup+', [status(thm)], ['100', '103'])).
% 1.74/1.95  thf('105', plain, ((l1_struct_0 @ sk_C)),
% 1.74/1.95      inference('sup-', [status(thm)], ['87', '88'])).
% 1.74/1.95  thf('106', plain, ((m1_subset_1 @ sk_F @ (k2_struct_0 @ sk_C))),
% 1.74/1.95      inference('demod', [status(thm)], ['104', '105'])).
% 1.74/1.95  thf('107', plain, ((m1_subset_1 @ sk_F @ (k2_struct_0 @ sk_C))),
% 1.74/1.95      inference('demod', [status(thm)], ['104', '105'])).
% 1.74/1.95  thf('108', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 1.74/1.95      inference('clc', [status(thm)], ['64', '65'])).
% 1.74/1.95  thf('109', plain,
% 1.74/1.95      (![X5 : $i]:
% 1.74/1.95         (((k2_struct_0 @ X5) = (u1_struct_0 @ X5)) | ~ (l1_struct_0 @ X5))),
% 1.74/1.95      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.74/1.95  thf('110', plain,
% 1.74/1.95      (![X22 : $i]: ((m1_pre_topc @ X22 @ X22) | ~ (l1_pre_topc @ X22))),
% 1.74/1.95      inference('cnf', [status(esa)], [t2_tsep_1])).
% 1.74/1.95  thf(t1_tsep_1, axiom,
% 1.74/1.95    (![A:$i]:
% 1.74/1.95     ( ( l1_pre_topc @ A ) =>
% 1.74/1.95       ( ![B:$i]:
% 1.74/1.95         ( ( m1_pre_topc @ B @ A ) =>
% 1.74/1.95           ( m1_subset_1 @
% 1.74/1.95             ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 1.74/1.95  thf('111', plain,
% 1.74/1.95      (![X15 : $i, X16 : $i]:
% 1.74/1.95         (~ (m1_pre_topc @ X15 @ X16)
% 1.74/1.95          | (m1_subset_1 @ (u1_struct_0 @ X15) @ 
% 1.74/1.95             (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 1.74/1.95          | ~ (l1_pre_topc @ X16))),
% 1.74/1.95      inference('cnf', [status(esa)], [t1_tsep_1])).
% 1.74/1.95  thf('112', plain,
% 1.74/1.95      (![X0 : $i]:
% 1.74/1.95         (~ (l1_pre_topc @ X0)
% 1.74/1.95          | ~ (l1_pre_topc @ X0)
% 1.74/1.95          | (m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 1.74/1.95             (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 1.74/1.95      inference('sup-', [status(thm)], ['110', '111'])).
% 1.74/1.95  thf('113', plain,
% 1.74/1.95      (![X0 : $i]:
% 1.74/1.95         ((m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 1.74/1.95           (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 1.74/1.95          | ~ (l1_pre_topc @ X0))),
% 1.74/1.95      inference('simplify', [status(thm)], ['112'])).
% 1.74/1.95  thf('114', plain,
% 1.74/1.95      (![X0 : $i]:
% 1.74/1.95         ((m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 1.74/1.95           (k1_zfmisc_1 @ (k2_struct_0 @ X0)))
% 1.74/1.95          | ~ (l1_struct_0 @ X0)
% 1.74/1.95          | ~ (l1_pre_topc @ X0))),
% 1.74/1.95      inference('sup+', [status(thm)], ['109', '113'])).
% 1.74/1.95  thf('115', plain, (![X6 : $i]: ((l1_struct_0 @ X6) | ~ (l1_pre_topc @ X6))),
% 1.74/1.95      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 1.74/1.95  thf('116', plain,
% 1.74/1.95      (![X0 : $i]:
% 1.74/1.95         (~ (l1_pre_topc @ X0)
% 1.74/1.95          | (m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 1.74/1.95             (k1_zfmisc_1 @ (k2_struct_0 @ X0))))),
% 1.74/1.95      inference('clc', [status(thm)], ['114', '115'])).
% 1.74/1.95  thf('117', plain, (((u1_struct_0 @ sk_C) = (u1_struct_0 @ sk_D))),
% 1.74/1.95      inference('demod', [status(thm)], ['30', '74'])).
% 1.74/1.95  thf(t16_tsep_1, axiom,
% 1.74/1.95    (![A:$i]:
% 1.74/1.95     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.74/1.95       ( ![B:$i]:
% 1.74/1.95         ( ( m1_pre_topc @ B @ A ) =>
% 1.74/1.95           ( ![C:$i]:
% 1.74/1.95             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.74/1.95               ( ( ( C ) = ( u1_struct_0 @ B ) ) =>
% 1.74/1.95                 ( ( ( v1_tsep_1 @ B @ A ) & ( m1_pre_topc @ B @ A ) ) <=>
% 1.74/1.95                   ( v3_pre_topc @ C @ A ) ) ) ) ) ) ) ))).
% 1.74/1.95  thf('118', plain,
% 1.74/1.95      (![X12 : $i, X13 : $i, X14 : $i]:
% 1.74/1.95         (~ (m1_pre_topc @ X12 @ X13)
% 1.74/1.95          | ((X14) != (u1_struct_0 @ X12))
% 1.74/1.95          | ~ (v3_pre_topc @ X14 @ X13)
% 1.74/1.95          | (v1_tsep_1 @ X12 @ X13)
% 1.74/1.95          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 1.74/1.95          | ~ (l1_pre_topc @ X13)
% 1.74/1.95          | ~ (v2_pre_topc @ X13))),
% 1.74/1.95      inference('cnf', [status(esa)], [t16_tsep_1])).
% 1.74/1.95  thf('119', plain,
% 1.74/1.95      (![X12 : $i, X13 : $i]:
% 1.74/1.95         (~ (v2_pre_topc @ X13)
% 1.74/1.95          | ~ (l1_pre_topc @ X13)
% 1.74/1.95          | ~ (m1_subset_1 @ (u1_struct_0 @ X12) @ 
% 1.74/1.95               (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 1.74/1.95          | (v1_tsep_1 @ X12 @ X13)
% 1.74/1.95          | ~ (v3_pre_topc @ (u1_struct_0 @ X12) @ X13)
% 1.74/1.95          | ~ (m1_pre_topc @ X12 @ X13))),
% 1.74/1.95      inference('simplify', [status(thm)], ['118'])).
% 1.74/1.95  thf('120', plain,
% 1.74/1.95      (![X0 : $i]:
% 1.74/1.95         (~ (m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 1.74/1.95             (k1_zfmisc_1 @ (u1_struct_0 @ sk_C)))
% 1.74/1.95          | ~ (m1_pre_topc @ X0 @ sk_D)
% 1.74/1.95          | ~ (v3_pre_topc @ (u1_struct_0 @ X0) @ sk_D)
% 1.74/1.95          | (v1_tsep_1 @ X0 @ sk_D)
% 1.74/1.95          | ~ (l1_pre_topc @ sk_D)
% 1.74/1.95          | ~ (v2_pre_topc @ sk_D))),
% 1.74/1.95      inference('sup-', [status(thm)], ['117', '119'])).
% 1.74/1.95  thf('121', plain, ((l1_pre_topc @ sk_D)),
% 1.74/1.95      inference('demod', [status(thm)], ['71', '72'])).
% 1.74/1.95  thf('122', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 1.74/1.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.74/1.95  thf('123', plain,
% 1.74/1.95      (![X3 : $i, X4 : $i]:
% 1.74/1.95         (~ (m1_pre_topc @ X3 @ X4)
% 1.74/1.95          | (v2_pre_topc @ X3)
% 1.74/1.95          | ~ (l1_pre_topc @ X4)
% 1.74/1.95          | ~ (v2_pre_topc @ X4))),
% 1.74/1.95      inference('cnf', [status(esa)], [cc1_pre_topc])).
% 1.74/1.95  thf('124', plain,
% 1.74/1.95      ((~ (v2_pre_topc @ sk_A) | ~ (l1_pre_topc @ sk_A) | (v2_pre_topc @ sk_D))),
% 1.74/1.95      inference('sup-', [status(thm)], ['122', '123'])).
% 1.74/1.95  thf('125', plain, ((v2_pre_topc @ sk_A)),
% 1.74/1.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.74/1.95  thf('126', plain, ((l1_pre_topc @ sk_A)),
% 1.74/1.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.74/1.95  thf('127', plain, ((v2_pre_topc @ sk_D)),
% 1.74/1.95      inference('demod', [status(thm)], ['124', '125', '126'])).
% 1.74/1.95  thf('128', plain,
% 1.74/1.95      (![X0 : $i]:
% 1.74/1.95         (~ (m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 1.74/1.95             (k1_zfmisc_1 @ (u1_struct_0 @ sk_C)))
% 1.74/1.95          | ~ (m1_pre_topc @ X0 @ sk_D)
% 1.74/1.95          | ~ (v3_pre_topc @ (u1_struct_0 @ X0) @ sk_D)
% 1.74/1.95          | (v1_tsep_1 @ X0 @ sk_D))),
% 1.74/1.95      inference('demod', [status(thm)], ['120', '121', '127'])).
% 1.74/1.95  thf('129', plain, (((u1_struct_0 @ sk_C) = (k2_struct_0 @ sk_C))),
% 1.74/1.95      inference('demod', [status(thm)], ['97', '98'])).
% 1.74/1.95  thf('130', plain,
% 1.74/1.95      (![X0 : $i]:
% 1.74/1.95         (~ (m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 1.74/1.95             (k1_zfmisc_1 @ (k2_struct_0 @ sk_C)))
% 1.74/1.95          | ~ (m1_pre_topc @ X0 @ sk_D)
% 1.74/1.95          | ~ (v3_pre_topc @ (u1_struct_0 @ X0) @ sk_D)
% 1.74/1.95          | (v1_tsep_1 @ X0 @ sk_D))),
% 1.74/1.95      inference('demod', [status(thm)], ['128', '129'])).
% 1.74/1.95  thf('131', plain,
% 1.74/1.95      ((~ (l1_pre_topc @ sk_C)
% 1.74/1.95        | (v1_tsep_1 @ sk_C @ sk_D)
% 1.74/1.95        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_C) @ sk_D)
% 1.74/1.95        | ~ (m1_pre_topc @ sk_C @ sk_D))),
% 1.74/1.95      inference('sup-', [status(thm)], ['116', '130'])).
% 1.74/1.95  thf('132', plain, ((l1_pre_topc @ sk_C)),
% 1.74/1.95      inference('demod', [status(thm)], ['21', '22'])).
% 1.74/1.95  thf('133', plain, (((u1_struct_0 @ sk_C) = (k2_struct_0 @ sk_C))),
% 1.74/1.95      inference('demod', [status(thm)], ['97', '98'])).
% 1.74/1.95  thf('134', plain,
% 1.74/1.95      (![X5 : $i]:
% 1.74/1.95         (((k2_struct_0 @ X5) = (u1_struct_0 @ X5)) | ~ (l1_struct_0 @ X5))),
% 1.74/1.95      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.74/1.95  thf('135', plain,
% 1.74/1.95      (![X22 : $i]: ((m1_pre_topc @ X22 @ X22) | ~ (l1_pre_topc @ X22))),
% 1.74/1.95      inference('cnf', [status(esa)], [t2_tsep_1])).
% 1.74/1.95  thf('136', plain,
% 1.74/1.95      (![X22 : $i]: ((m1_pre_topc @ X22 @ X22) | ~ (l1_pre_topc @ X22))),
% 1.74/1.95      inference('cnf', [status(esa)], [t2_tsep_1])).
% 1.74/1.95  thf(fc10_tops_1, axiom,
% 1.74/1.95    (![A:$i]:
% 1.74/1.95     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.74/1.95       ( v3_pre_topc @ ( k2_struct_0 @ A ) @ A ) ))).
% 1.74/1.95  thf('137', plain,
% 1.74/1.95      (![X9 : $i]:
% 1.74/1.95         ((v3_pre_topc @ (k2_struct_0 @ X9) @ X9)
% 1.74/1.95          | ~ (l1_pre_topc @ X9)
% 1.74/1.95          | ~ (v2_pre_topc @ X9))),
% 1.74/1.95      inference('cnf', [status(esa)], [fc10_tops_1])).
% 1.74/1.95  thf('138', plain,
% 1.74/1.95      (![X5 : $i]:
% 1.74/1.95         (((k2_struct_0 @ X5) = (u1_struct_0 @ X5)) | ~ (l1_struct_0 @ X5))),
% 1.74/1.95      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.74/1.95  thf('139', plain,
% 1.74/1.95      (![X0 : $i]:
% 1.74/1.95         ((m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 1.74/1.95           (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 1.74/1.95          | ~ (l1_pre_topc @ X0))),
% 1.74/1.95      inference('simplify', [status(thm)], ['112'])).
% 1.74/1.95  thf('140', plain,
% 1.74/1.95      (![X12 : $i, X13 : $i]:
% 1.74/1.95         (~ (v2_pre_topc @ X13)
% 1.74/1.95          | ~ (l1_pre_topc @ X13)
% 1.74/1.95          | ~ (m1_subset_1 @ (u1_struct_0 @ X12) @ 
% 1.74/1.95               (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 1.74/1.95          | (v1_tsep_1 @ X12 @ X13)
% 1.74/1.95          | ~ (v3_pre_topc @ (u1_struct_0 @ X12) @ X13)
% 1.74/1.95          | ~ (m1_pre_topc @ X12 @ X13))),
% 1.74/1.95      inference('simplify', [status(thm)], ['118'])).
% 1.74/1.95  thf('141', plain,
% 1.74/1.95      (![X0 : $i]:
% 1.74/1.95         (~ (l1_pre_topc @ X0)
% 1.74/1.95          | ~ (m1_pre_topc @ X0 @ X0)
% 1.74/1.95          | ~ (v3_pre_topc @ (u1_struct_0 @ X0) @ X0)
% 1.74/1.95          | (v1_tsep_1 @ X0 @ X0)
% 1.74/1.95          | ~ (l1_pre_topc @ X0)
% 1.74/1.95          | ~ (v2_pre_topc @ X0))),
% 1.74/1.95      inference('sup-', [status(thm)], ['139', '140'])).
% 1.74/1.95  thf('142', plain,
% 1.74/1.95      (![X0 : $i]:
% 1.74/1.95         (~ (v2_pre_topc @ X0)
% 1.74/1.95          | (v1_tsep_1 @ X0 @ X0)
% 1.74/1.95          | ~ (v3_pre_topc @ (u1_struct_0 @ X0) @ X0)
% 1.74/1.95          | ~ (m1_pre_topc @ X0 @ X0)
% 1.74/1.95          | ~ (l1_pre_topc @ X0))),
% 1.74/1.95      inference('simplify', [status(thm)], ['141'])).
% 1.74/1.95  thf('143', plain,
% 1.74/1.95      (![X0 : $i]:
% 1.74/1.95         (~ (v3_pre_topc @ (k2_struct_0 @ X0) @ X0)
% 1.74/1.95          | ~ (l1_struct_0 @ X0)
% 1.74/1.95          | ~ (l1_pre_topc @ X0)
% 1.74/1.95          | ~ (m1_pre_topc @ X0 @ X0)
% 1.74/1.95          | (v1_tsep_1 @ X0 @ X0)
% 1.74/1.95          | ~ (v2_pre_topc @ X0))),
% 1.74/1.95      inference('sup-', [status(thm)], ['138', '142'])).
% 1.74/1.95  thf('144', plain,
% 1.74/1.95      (![X0 : $i]:
% 1.74/1.95         (~ (v2_pre_topc @ X0)
% 1.74/1.95          | ~ (l1_pre_topc @ X0)
% 1.74/1.95          | ~ (v2_pre_topc @ X0)
% 1.74/1.95          | (v1_tsep_1 @ X0 @ X0)
% 1.74/1.95          | ~ (m1_pre_topc @ X0 @ X0)
% 1.74/1.95          | ~ (l1_pre_topc @ X0)
% 1.74/1.95          | ~ (l1_struct_0 @ X0))),
% 1.74/1.95      inference('sup-', [status(thm)], ['137', '143'])).
% 1.74/1.95  thf('145', plain,
% 1.74/1.95      (![X0 : $i]:
% 1.74/1.95         (~ (l1_struct_0 @ X0)
% 1.74/1.95          | ~ (m1_pre_topc @ X0 @ X0)
% 1.74/1.95          | (v1_tsep_1 @ X0 @ X0)
% 1.74/1.95          | ~ (l1_pre_topc @ X0)
% 1.74/1.95          | ~ (v2_pre_topc @ X0))),
% 1.74/1.95      inference('simplify', [status(thm)], ['144'])).
% 1.74/1.95  thf('146', plain,
% 1.74/1.95      (![X0 : $i]:
% 1.74/1.95         (~ (l1_pre_topc @ X0)
% 1.74/1.95          | ~ (v2_pre_topc @ X0)
% 1.74/1.95          | ~ (l1_pre_topc @ X0)
% 1.74/1.95          | (v1_tsep_1 @ X0 @ X0)
% 1.74/1.95          | ~ (l1_struct_0 @ X0))),
% 1.74/1.95      inference('sup-', [status(thm)], ['136', '145'])).
% 1.74/1.95  thf('147', plain,
% 1.74/1.95      (![X0 : $i]:
% 1.74/1.95         (~ (l1_struct_0 @ X0)
% 1.74/1.95          | (v1_tsep_1 @ X0 @ X0)
% 1.74/1.95          | ~ (v2_pre_topc @ X0)
% 1.74/1.95          | ~ (l1_pre_topc @ X0))),
% 1.74/1.95      inference('simplify', [status(thm)], ['146'])).
% 1.74/1.95  thf('148', plain,
% 1.74/1.95      (![X0 : $i]:
% 1.74/1.95         ((m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 1.74/1.95           (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 1.74/1.95          | ~ (l1_pre_topc @ X0))),
% 1.74/1.95      inference('simplify', [status(thm)], ['112'])).
% 1.74/1.95  thf('149', plain,
% 1.74/1.95      (![X12 : $i, X13 : $i, X14 : $i]:
% 1.74/1.95         (~ (m1_pre_topc @ X12 @ X13)
% 1.74/1.95          | ((X14) != (u1_struct_0 @ X12))
% 1.74/1.95          | ~ (v1_tsep_1 @ X12 @ X13)
% 1.74/1.95          | ~ (m1_pre_topc @ X12 @ X13)
% 1.74/1.95          | (v3_pre_topc @ X14 @ X13)
% 1.74/1.95          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 1.74/1.95          | ~ (l1_pre_topc @ X13)
% 1.74/1.95          | ~ (v2_pre_topc @ X13))),
% 1.74/1.95      inference('cnf', [status(esa)], [t16_tsep_1])).
% 1.74/1.95  thf('150', plain,
% 1.74/1.95      (![X12 : $i, X13 : $i]:
% 1.74/1.95         (~ (v2_pre_topc @ X13)
% 1.74/1.95          | ~ (l1_pre_topc @ X13)
% 1.74/1.95          | ~ (m1_subset_1 @ (u1_struct_0 @ X12) @ 
% 1.74/1.95               (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 1.74/1.95          | (v3_pre_topc @ (u1_struct_0 @ X12) @ X13)
% 1.74/1.95          | ~ (v1_tsep_1 @ X12 @ X13)
% 1.74/1.95          | ~ (m1_pre_topc @ X12 @ X13))),
% 1.74/1.95      inference('simplify', [status(thm)], ['149'])).
% 1.74/1.95  thf('151', plain,
% 1.74/1.95      (![X0 : $i]:
% 1.74/1.95         (~ (l1_pre_topc @ X0)
% 1.74/1.95          | ~ (m1_pre_topc @ X0 @ X0)
% 1.74/1.95          | ~ (v1_tsep_1 @ X0 @ X0)
% 1.74/1.95          | (v3_pre_topc @ (u1_struct_0 @ X0) @ X0)
% 1.74/1.95          | ~ (l1_pre_topc @ X0)
% 1.74/1.95          | ~ (v2_pre_topc @ X0))),
% 1.74/1.95      inference('sup-', [status(thm)], ['148', '150'])).
% 1.74/1.95  thf('152', plain,
% 1.74/1.95      (![X0 : $i]:
% 1.74/1.95         (~ (v2_pre_topc @ X0)
% 1.74/1.95          | (v3_pre_topc @ (u1_struct_0 @ X0) @ X0)
% 1.74/1.95          | ~ (v1_tsep_1 @ X0 @ X0)
% 1.74/1.95          | ~ (m1_pre_topc @ X0 @ X0)
% 1.74/1.95          | ~ (l1_pre_topc @ X0))),
% 1.74/1.95      inference('simplify', [status(thm)], ['151'])).
% 1.74/1.95  thf('153', plain,
% 1.74/1.95      (![X0 : $i]:
% 1.74/1.95         (~ (l1_pre_topc @ X0)
% 1.74/1.95          | ~ (v2_pre_topc @ X0)
% 1.74/1.95          | ~ (l1_struct_0 @ X0)
% 1.74/1.95          | ~ (l1_pre_topc @ X0)
% 1.74/1.95          | ~ (m1_pre_topc @ X0 @ X0)
% 1.74/1.95          | (v3_pre_topc @ (u1_struct_0 @ X0) @ X0)
% 1.74/1.95          | ~ (v2_pre_topc @ X0))),
% 1.74/1.95      inference('sup-', [status(thm)], ['147', '152'])).
% 1.74/1.95  thf('154', plain,
% 1.74/1.95      (![X0 : $i]:
% 1.74/1.95         ((v3_pre_topc @ (u1_struct_0 @ X0) @ X0)
% 1.74/1.95          | ~ (m1_pre_topc @ X0 @ X0)
% 1.74/1.95          | ~ (l1_struct_0 @ X0)
% 1.74/1.95          | ~ (v2_pre_topc @ X0)
% 1.74/1.95          | ~ (l1_pre_topc @ X0))),
% 1.74/1.95      inference('simplify', [status(thm)], ['153'])).
% 1.74/1.95  thf('155', plain,
% 1.74/1.95      (![X0 : $i]:
% 1.74/1.95         (~ (l1_pre_topc @ X0)
% 1.74/1.95          | ~ (l1_pre_topc @ X0)
% 1.74/1.95          | ~ (v2_pre_topc @ X0)
% 1.74/1.95          | ~ (l1_struct_0 @ X0)
% 1.74/1.95          | (v3_pre_topc @ (u1_struct_0 @ X0) @ X0))),
% 1.74/1.95      inference('sup-', [status(thm)], ['135', '154'])).
% 1.74/1.95  thf('156', plain,
% 1.74/1.95      (![X0 : $i]:
% 1.74/1.95         ((v3_pre_topc @ (u1_struct_0 @ X0) @ X0)
% 1.74/1.95          | ~ (l1_struct_0 @ X0)
% 1.74/1.95          | ~ (v2_pre_topc @ X0)
% 1.74/1.95          | ~ (l1_pre_topc @ X0))),
% 1.74/1.95      inference('simplify', [status(thm)], ['155'])).
% 1.74/1.95  thf('157', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 1.74/1.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.74/1.95  thf('158', plain,
% 1.74/1.95      (![X0 : $i, X1 : $i]:
% 1.74/1.95         ((m1_pre_topc @ X0 @ X0)
% 1.74/1.95          | ~ (m1_pre_topc @ X0 @ X1)
% 1.74/1.95          | ~ (l1_pre_topc @ X1)
% 1.74/1.95          | ~ (v2_pre_topc @ X1))),
% 1.74/1.95      inference('simplify', [status(thm)], ['35'])).
% 1.74/1.95  thf('159', plain,
% 1.74/1.95      ((~ (v2_pre_topc @ sk_A)
% 1.74/1.95        | ~ (l1_pre_topc @ sk_A)
% 1.74/1.95        | (m1_pre_topc @ sk_D @ sk_D))),
% 1.74/1.95      inference('sup-', [status(thm)], ['157', '158'])).
% 1.74/1.95  thf('160', plain, ((v2_pre_topc @ sk_A)),
% 1.74/1.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.74/1.95  thf('161', plain, ((l1_pre_topc @ sk_A)),
% 1.74/1.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.74/1.95  thf('162', plain, ((m1_pre_topc @ sk_D @ sk_D)),
% 1.74/1.95      inference('demod', [status(thm)], ['159', '160', '161'])).
% 1.74/1.95  thf('163', plain,
% 1.74/1.95      (![X15 : $i, X16 : $i]:
% 1.74/1.95         (~ (m1_pre_topc @ X15 @ X16)
% 1.74/1.95          | (m1_subset_1 @ (u1_struct_0 @ X15) @ 
% 1.74/1.95             (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 1.74/1.95          | ~ (l1_pre_topc @ X16))),
% 1.74/1.95      inference('cnf', [status(esa)], [t1_tsep_1])).
% 1.74/1.95  thf('164', plain,
% 1.74/1.95      ((~ (l1_pre_topc @ sk_D)
% 1.74/1.95        | (m1_subset_1 @ (u1_struct_0 @ sk_D) @ 
% 1.74/1.95           (k1_zfmisc_1 @ (u1_struct_0 @ sk_D))))),
% 1.74/1.95      inference('sup-', [status(thm)], ['162', '163'])).
% 1.74/1.95  thf('165', plain, ((l1_pre_topc @ sk_D)),
% 1.74/1.95      inference('demod', [status(thm)], ['71', '72'])).
% 1.74/1.95  thf('166', plain,
% 1.74/1.95      ((m1_subset_1 @ (u1_struct_0 @ sk_D) @ 
% 1.74/1.95        (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))),
% 1.74/1.95      inference('demod', [status(thm)], ['164', '165'])).
% 1.74/1.95  thf('167', plain,
% 1.74/1.95      (![X12 : $i, X13 : $i]:
% 1.74/1.95         (~ (v2_pre_topc @ X13)
% 1.74/1.95          | ~ (l1_pre_topc @ X13)
% 1.74/1.95          | ~ (m1_subset_1 @ (u1_struct_0 @ X12) @ 
% 1.74/1.95               (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 1.74/1.95          | (v1_tsep_1 @ X12 @ X13)
% 1.74/1.95          | ~ (v3_pre_topc @ (u1_struct_0 @ X12) @ X13)
% 1.74/1.95          | ~ (m1_pre_topc @ X12 @ X13))),
% 1.74/1.95      inference('simplify', [status(thm)], ['118'])).
% 1.74/1.95  thf('168', plain,
% 1.74/1.95      ((~ (m1_pre_topc @ sk_D @ sk_D)
% 1.74/1.95        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_D) @ sk_D)
% 1.74/1.95        | (v1_tsep_1 @ sk_D @ sk_D)
% 1.74/1.95        | ~ (l1_pre_topc @ sk_D)
% 1.74/1.95        | ~ (v2_pre_topc @ sk_D))),
% 1.74/1.95      inference('sup-', [status(thm)], ['166', '167'])).
% 1.74/1.95  thf('169', plain, ((m1_pre_topc @ sk_D @ sk_D)),
% 1.74/1.95      inference('demod', [status(thm)], ['159', '160', '161'])).
% 1.74/1.95  thf('170', plain, ((l1_pre_topc @ sk_D)),
% 1.74/1.95      inference('demod', [status(thm)], ['71', '72'])).
% 1.74/1.95  thf('171', plain, ((v2_pre_topc @ sk_D)),
% 1.74/1.95      inference('demod', [status(thm)], ['124', '125', '126'])).
% 1.74/1.95  thf('172', plain,
% 1.74/1.95      ((~ (v3_pre_topc @ (u1_struct_0 @ sk_D) @ sk_D)
% 1.74/1.95        | (v1_tsep_1 @ sk_D @ sk_D))),
% 1.74/1.95      inference('demod', [status(thm)], ['168', '169', '170', '171'])).
% 1.74/1.95  thf('173', plain,
% 1.74/1.95      ((~ (l1_pre_topc @ sk_D)
% 1.74/1.95        | ~ (v2_pre_topc @ sk_D)
% 1.74/1.95        | ~ (l1_struct_0 @ sk_D)
% 1.74/1.95        | (v1_tsep_1 @ sk_D @ sk_D))),
% 1.74/1.95      inference('sup-', [status(thm)], ['156', '172'])).
% 1.74/1.95  thf('174', plain, ((l1_pre_topc @ sk_D)),
% 1.74/1.95      inference('demod', [status(thm)], ['71', '72'])).
% 1.74/1.95  thf('175', plain, ((v2_pre_topc @ sk_D)),
% 1.74/1.95      inference('demod', [status(thm)], ['124', '125', '126'])).
% 1.74/1.95  thf('176', plain, ((l1_struct_0 @ sk_D)),
% 1.74/1.95      inference('sup-', [status(thm)], ['79', '80'])).
% 1.74/1.95  thf('177', plain, ((v1_tsep_1 @ sk_D @ sk_D)),
% 1.74/1.95      inference('demod', [status(thm)], ['173', '174', '175', '176'])).
% 1.74/1.95  thf('178', plain,
% 1.74/1.95      (![X0 : $i]:
% 1.74/1.95         (~ (v2_pre_topc @ X0)
% 1.74/1.95          | (v3_pre_topc @ (u1_struct_0 @ X0) @ X0)
% 1.74/1.95          | ~ (v1_tsep_1 @ X0 @ X0)
% 1.74/1.95          | ~ (m1_pre_topc @ X0 @ X0)
% 1.74/1.95          | ~ (l1_pre_topc @ X0))),
% 1.74/1.95      inference('simplify', [status(thm)], ['151'])).
% 1.74/1.95  thf('179', plain,
% 1.74/1.95      ((~ (l1_pre_topc @ sk_D)
% 1.74/1.95        | ~ (m1_pre_topc @ sk_D @ sk_D)
% 1.74/1.95        | (v3_pre_topc @ (u1_struct_0 @ sk_D) @ sk_D)
% 1.74/1.95        | ~ (v2_pre_topc @ sk_D))),
% 1.74/1.95      inference('sup-', [status(thm)], ['177', '178'])).
% 1.74/1.95  thf('180', plain, ((l1_pre_topc @ sk_D)),
% 1.74/1.95      inference('demod', [status(thm)], ['71', '72'])).
% 1.74/1.95  thf('181', plain, ((m1_pre_topc @ sk_D @ sk_D)),
% 1.74/1.95      inference('demod', [status(thm)], ['159', '160', '161'])).
% 1.74/1.95  thf('182', plain, ((v2_pre_topc @ sk_D)),
% 1.74/1.95      inference('demod', [status(thm)], ['124', '125', '126'])).
% 1.74/1.95  thf('183', plain, ((v3_pre_topc @ (u1_struct_0 @ sk_D) @ sk_D)),
% 1.74/1.95      inference('demod', [status(thm)], ['179', '180', '181', '182'])).
% 1.74/1.95  thf('184', plain, (((u1_struct_0 @ sk_C) = (u1_struct_0 @ sk_D))),
% 1.74/1.95      inference('demod', [status(thm)], ['30', '74'])).
% 1.74/1.95  thf('185', plain, ((v3_pre_topc @ (u1_struct_0 @ sk_C) @ sk_D)),
% 1.74/1.95      inference('demod', [status(thm)], ['183', '184'])).
% 1.74/1.95  thf('186', plain,
% 1.74/1.95      (((v3_pre_topc @ (k2_struct_0 @ sk_C) @ sk_D) | ~ (l1_struct_0 @ sk_C))),
% 1.74/1.95      inference('sup+', [status(thm)], ['134', '185'])).
% 1.74/1.95  thf('187', plain, ((l1_struct_0 @ sk_C)),
% 1.74/1.95      inference('sup-', [status(thm)], ['87', '88'])).
% 1.74/1.95  thf('188', plain, ((v3_pre_topc @ (k2_struct_0 @ sk_C) @ sk_D)),
% 1.74/1.95      inference('demod', [status(thm)], ['186', '187'])).
% 1.74/1.95  thf('189', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 1.74/1.95      inference('clc', [status(thm)], ['64', '65'])).
% 1.74/1.95  thf('190', plain, ((v1_tsep_1 @ sk_C @ sk_D)),
% 1.74/1.95      inference('demod', [status(thm)], ['131', '132', '133', '188', '189'])).
% 1.74/1.95  thf('191', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 1.74/1.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.74/1.95  thf('192', plain,
% 1.74/1.95      (((v2_struct_0 @ sk_A)
% 1.74/1.95        | (v2_struct_0 @ sk_C)
% 1.74/1.95        | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)
% 1.74/1.95        | (v2_struct_0 @ sk_D)
% 1.74/1.95        | (v2_struct_0 @ sk_B))),
% 1.74/1.95      inference('demod', [status(thm)],
% 1.74/1.95                ['93', '94', '95', '96', '99', '106', '107', '108', '190', 
% 1.74/1.95                 '191'])).
% 1.74/1.95  thf('193', plain, (~ (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)),
% 1.74/1.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.74/1.95  thf('194', plain,
% 1.74/1.95      (((v2_struct_0 @ sk_B)
% 1.74/1.95        | (v2_struct_0 @ sk_D)
% 1.74/1.95        | (v2_struct_0 @ sk_C)
% 1.74/1.95        | (v2_struct_0 @ sk_A))),
% 1.74/1.95      inference('sup-', [status(thm)], ['192', '193'])).
% 1.74/1.95  thf('195', plain, (~ (v2_struct_0 @ sk_D)),
% 1.74/1.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.74/1.95  thf('196', plain,
% 1.74/1.95      (((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_B))),
% 1.74/1.95      inference('sup-', [status(thm)], ['194', '195'])).
% 1.74/1.95  thf('197', plain, (~ (v2_struct_0 @ sk_A)),
% 1.74/1.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.74/1.95  thf('198', plain, (((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_C))),
% 1.74/1.95      inference('clc', [status(thm)], ['196', '197'])).
% 1.74/1.95  thf('199', plain, (~ (v2_struct_0 @ sk_B)),
% 1.74/1.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.74/1.95  thf('200', plain, ((v2_struct_0 @ sk_C)),
% 1.74/1.95      inference('clc', [status(thm)], ['198', '199'])).
% 1.74/1.95  thf('201', plain, ($false), inference('demod', [status(thm)], ['0', '200'])).
% 1.74/1.95  
% 1.74/1.95  % SZS output end Refutation
% 1.74/1.95  
% 1.74/1.95  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
