%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.58oCyH4TUf

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:10:20 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  171 ( 355 expanded)
%              Number of leaves         :   37 ( 116 expanded)
%              Depth                    :   17
%              Number of atoms          : 2163 (12482 expanded)
%              Number of equality atoms :   13 ( 161 expanded)
%              Maximal formula depth    :   33 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_connsp_2_type,type,(
    k1_connsp_2: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_G_type,type,(
    sk_G: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(r1_tmap_1_type,type,(
    r1_tmap_1: $i > $i > $i > $i > $o )).

thf(k3_tmap_1_type,type,(
    k3_tmap_1: $i > $i > $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_tsep_1_type,type,(
    v1_tsep_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(t86_tmap_1,conjecture,(
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
                       => ( ( ( v1_tsep_1 @ C @ D )
                            & ( m1_pre_topc @ C @ D ) )
                         => ! [F: $i] :
                              ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) )
                             => ! [G: $i] :
                                  ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) )
                                 => ( ( F = G )
                                   => ( ( r1_tmap_1 @ D @ B @ E @ F )
                                    <=> ( r1_tmap_1 @ C @ B @ ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ G ) ) ) ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t86_tmap_1])).

thf('0',plain,
    ( ~ ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_G )
    | ~ ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F )
    | ~ ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_G ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,(
    sk_F = sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(t30_connsp_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ( r2_hidden @ B @ ( k1_connsp_2 @ A @ B ) ) ) ) )).

thf('5',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( u1_struct_0 @ X15 ) )
      | ( r2_hidden @ X14 @ ( k1_connsp_2 @ X15 @ X14 ) )
      | ~ ( l1_pre_topc @ X15 )
      | ~ ( v2_pre_topc @ X15 )
      | ( v2_struct_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t30_connsp_2])).

thf('6',plain,
    ( ( v2_struct_0 @ sk_C )
    | ~ ( v2_pre_topc @ sk_C )
    | ~ ( l1_pre_topc @ sk_C )
    | ( r2_hidden @ sk_F @ ( k1_connsp_2 @ sk_C @ sk_F ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( v2_pre_topc @ B ) ) ) )).

thf('8',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( m1_pre_topc @ X8 @ X9 )
      | ( v2_pre_topc @ X8 )
      | ~ ( l1_pre_topc @ X9 )
      | ~ ( v2_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[cc1_pre_topc])).

thf('9',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_pre_topc @ sk_C ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    v2_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['9','10','11'])).

thf('13',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('14',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( m1_pre_topc @ X10 @ X11 )
      | ( l1_pre_topc @ X10 )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('15',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_C ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( r2_hidden @ sk_F @ ( k1_connsp_2 @ sk_C @ sk_F ) ) ),
    inference(demod,[status(thm)],['6','12','17'])).

thf('19',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    r2_hidden @ sk_F @ ( k1_connsp_2 @ sk_C @ sk_F ) ),
    inference(clc,[status(thm)],['18','19'])).

thf('21',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('22',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r2_hidden @ X3 @ X4 )
      | ( v1_xboole_0 @ X4 )
      | ~ ( m1_subset_1 @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('23',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) )
    | ( r2_hidden @ sk_F @ ( u1_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t1_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( m1_subset_1 @ ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('25',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( m1_pre_topc @ X19 @ X20 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X19 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ~ ( l1_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('26',plain,
    ( ~ ( l1_pre_topc @ sk_D )
    | ( m1_subset_1 @ ( u1_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( m1_pre_topc @ X10 @ X11 )
      | ( l1_pre_topc @ X10 )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('29',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_D ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['26','31'])).

thf('33',plain,
    ( ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_G )
    | ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_G )
   <= ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_G ) ),
    inference(split,[status(esa)],['33'])).

thf('35',plain,(
    sk_F = sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_F )
   <= ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_G ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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

thf('38',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i,X35: $i,X36: $i,X37: $i,X38: $i] :
      ( ( v2_struct_0 @ X31 )
      | ~ ( v2_pre_topc @ X31 )
      | ~ ( l1_pre_topc @ X31 )
      | ( v2_struct_0 @ X32 )
      | ~ ( m1_pre_topc @ X32 @ X33 )
      | ~ ( m1_pre_topc @ X34 @ X32 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X32 ) ) )
      | ~ ( m1_subset_1 @ X36 @ ( u1_struct_0 @ X34 ) )
      | ~ ( r1_tmap_1 @ X34 @ X31 @ ( k3_tmap_1 @ X33 @ X31 @ X32 @ X34 @ X37 ) @ X36 )
      | ( r1_tmap_1 @ X32 @ X31 @ X37 @ X38 )
      | ( X38 != X36 )
      | ~ ( r1_tarski @ X35 @ ( u1_struct_0 @ X34 ) )
      | ~ ( r2_hidden @ X38 @ X35 )
      | ~ ( v3_pre_topc @ X35 @ X32 )
      | ~ ( m1_subset_1 @ X38 @ ( u1_struct_0 @ X32 ) )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X32 ) @ ( u1_struct_0 @ X31 ) ) ) )
      | ~ ( v1_funct_2 @ X37 @ ( u1_struct_0 @ X32 ) @ ( u1_struct_0 @ X31 ) )
      | ~ ( v1_funct_1 @ X37 )
      | ~ ( m1_pre_topc @ X34 @ X33 )
      | ( v2_struct_0 @ X34 )
      | ~ ( l1_pre_topc @ X33 )
      | ~ ( v2_pre_topc @ X33 )
      | ( v2_struct_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t84_tmap_1])).

thf('39',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i,X35: $i,X36: $i,X37: $i] :
      ( ( v2_struct_0 @ X33 )
      | ~ ( v2_pre_topc @ X33 )
      | ~ ( l1_pre_topc @ X33 )
      | ( v2_struct_0 @ X34 )
      | ~ ( m1_pre_topc @ X34 @ X33 )
      | ~ ( v1_funct_1 @ X37 )
      | ~ ( v1_funct_2 @ X37 @ ( u1_struct_0 @ X32 ) @ ( u1_struct_0 @ X31 ) )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X32 ) @ ( u1_struct_0 @ X31 ) ) ) )
      | ~ ( m1_subset_1 @ X36 @ ( u1_struct_0 @ X32 ) )
      | ~ ( v3_pre_topc @ X35 @ X32 )
      | ~ ( r2_hidden @ X36 @ X35 )
      | ~ ( r1_tarski @ X35 @ ( u1_struct_0 @ X34 ) )
      | ( r1_tmap_1 @ X32 @ X31 @ X37 @ X36 )
      | ~ ( r1_tmap_1 @ X34 @ X31 @ ( k3_tmap_1 @ X33 @ X31 @ X32 @ X34 @ X37 ) @ X36 )
      | ~ ( m1_subset_1 @ X36 @ ( u1_struct_0 @ X34 ) )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X32 ) ) )
      | ~ ( m1_pre_topc @ X34 @ X32 )
      | ~ ( m1_pre_topc @ X32 @ X33 )
      | ( v2_struct_0 @ X32 )
      | ~ ( l1_pre_topc @ X31 )
      | ~ ( v2_pre_topc @ X31 )
      | ( v2_struct_0 @ X31 ) ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ~ ( m1_pre_topc @ X1 @ sk_D )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X1 ) )
      | ~ ( r1_tmap_1 @ X1 @ sk_B @ ( k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E ) @ X3 )
      | ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X3 )
      | ~ ( r1_tarski @ X2 @ ( u1_struct_0 @ X1 ) )
      | ~ ( r2_hidden @ X3 @ X2 )
      | ~ ( v3_pre_topc @ X2 @ sk_D )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ sk_D ) )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ( v2_struct_0 @ X1 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['37','39'])).

thf('41',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ~ ( m1_pre_topc @ X1 @ sk_D )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X1 ) )
      | ~ ( r1_tmap_1 @ X1 @ sk_B @ ( k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E ) @ X3 )
      | ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X3 )
      | ~ ( r1_tarski @ X2 @ ( u1_struct_0 @ X1 ) )
      | ~ ( r2_hidden @ X3 @ X2 )
      | ~ ( v3_pre_topc @ X2 @ sk_D )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ sk_D ) )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ( v2_struct_0 @ X1 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['40','41','42','43','44'])).

thf('46',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ~ ( v2_pre_topc @ sk_A )
        | ~ ( l1_pre_topc @ sk_A )
        | ( v2_struct_0 @ sk_C )
        | ~ ( m1_pre_topc @ sk_C @ sk_A )
        | ~ ( m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_D ) )
        | ~ ( v3_pre_topc @ X0 @ sk_D )
        | ~ ( r2_hidden @ sk_F @ X0 )
        | ~ ( r1_tarski @ X0 @ ( u1_struct_0 @ sk_C ) )
        | ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F )
        | ~ ( m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_C ) )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) )
        | ~ ( m1_pre_topc @ sk_C @ sk_D )
        | ~ ( m1_pre_topc @ sk_D @ sk_A )
        | ( v2_struct_0 @ sk_D )
        | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_G ) ),
    inference('sup-',[status(thm)],['36','45'])).

thf('47',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('52',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ sk_C )
        | ~ ( v3_pre_topc @ X0 @ sk_D )
        | ~ ( r2_hidden @ sk_F @ X0 )
        | ~ ( r1_tarski @ X0 @ ( u1_struct_0 @ sk_C ) )
        | ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) )
        | ( v2_struct_0 @ sk_D )
        | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_G ) ),
    inference(demod,[status(thm)],['46','47','48','49','50','51','52','53'])).

thf('55',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F )
      | ~ ( r1_tarski @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_C ) )
      | ~ ( r2_hidden @ sk_F @ ( u1_struct_0 @ sk_C ) )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_C ) @ sk_D )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_G ) ),
    inference('sup-',[status(thm)],['32','54'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('57',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['56'])).

thf('58',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['26','31'])).

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

thf('59',plain,(
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

thf('60',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( v2_pre_topc @ X17 )
      | ~ ( l1_pre_topc @ X17 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X16 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ( v3_pre_topc @ ( u1_struct_0 @ X16 ) @ X17 )
      | ~ ( v1_tsep_1 @ X16 @ X17 )
      | ~ ( m1_pre_topc @ X16 @ X17 ) ) ),
    inference(simplify,[status(thm)],['59'])).

thf('61',plain,
    ( ~ ( m1_pre_topc @ sk_C @ sk_D )
    | ~ ( v1_tsep_1 @ sk_C @ sk_D )
    | ( v3_pre_topc @ ( u1_struct_0 @ sk_C ) @ sk_D )
    | ~ ( l1_pre_topc @ sk_D )
    | ~ ( v2_pre_topc @ sk_D ) ),
    inference('sup-',[status(thm)],['58','60'])).

thf('62',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    v1_tsep_1 @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['29','30'])).

thf('65',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( m1_pre_topc @ X8 @ X9 )
      | ( v2_pre_topc @ X8 )
      | ~ ( l1_pre_topc @ X9 )
      | ~ ( v2_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[cc1_pre_topc])).

thf('67',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_pre_topc @ sk_D ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    v2_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['67','68','69'])).

thf('71',plain,(
    v3_pre_topc @ ( u1_struct_0 @ sk_C ) @ sk_D ),
    inference(demod,[status(thm)],['61','62','63','64','70'])).

thf('72',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F )
      | ~ ( r2_hidden @ sk_F @ ( u1_struct_0 @ sk_C ) )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_G ) ),
    inference(demod,[status(thm)],['55','57','71'])).

thf('73',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_G ) ),
    inference('sup-',[status(thm)],['23','72'])).

thf('74',plain,
    ( ~ ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F )
   <= ~ ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F ) ),
    inference(split,[status(esa)],['0'])).

thf('75',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) ) )
   <= ( ~ ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F )
      & ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_G ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(dt_k1_connsp_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) )
     => ( m1_subset_1 @ ( k1_connsp_2 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('77',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( l1_pre_topc @ X12 )
      | ~ ( v2_pre_topc @ X12 )
      | ( v2_struct_0 @ X12 )
      | ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ X12 ) )
      | ( m1_subset_1 @ ( k1_connsp_2 @ X12 @ X13 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_connsp_2])).

thf('78',plain,
    ( ( m1_subset_1 @ ( k1_connsp_2 @ sk_C @ sk_F ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C ) ) )
    | ( v2_struct_0 @ sk_C )
    | ~ ( v2_pre_topc @ sk_C )
    | ~ ( l1_pre_topc @ sk_C ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    v2_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['9','10','11'])).

thf('80',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['15','16'])).

thf('81',plain,
    ( ( m1_subset_1 @ ( k1_connsp_2 @ sk_C @ sk_F ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C ) ) )
    | ( v2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['78','79','80'])).

thf('82',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    m1_subset_1 @ ( k1_connsp_2 @ sk_C @ sk_F ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C ) ) ),
    inference(clc,[status(thm)],['81','82'])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('84',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X5 @ X6 )
      | ~ ( v1_xboole_0 @ X7 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('85',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) )
      | ~ ( r2_hidden @ X0 @ ( k1_connsp_2 @ sk_C @ sk_F ) ) ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ sk_C )
        | ( v2_struct_0 @ sk_D )
        | ( v2_struct_0 @ sk_B )
        | ~ ( r2_hidden @ X0 @ ( k1_connsp_2 @ sk_C @ sk_F ) ) )
   <= ( ~ ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F )
      & ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_G ) ) ),
    inference('sup-',[status(thm)],['75','85'])).

thf('87',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ~ ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F )
      & ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_G ) ) ),
    inference('sup-',[status(thm)],['20','86'])).

thf('88',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ~ ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F )
      & ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_G ) ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_C ) )
   <= ( ~ ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F )
      & ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_G ) ) ),
    inference(clc,[status(thm)],['89','90'])).

thf('92',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,
    ( ( v2_struct_0 @ sk_C )
   <= ( ~ ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F )
      & ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_G ) ) ),
    inference(clc,[status(thm)],['91','92'])).

thf('94',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,
    ( ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F )
    | ~ ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_G ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,
    ( ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F )
    | ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_G ) ),
    inference(split,[status(esa)],['33'])).

thf('97',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('99',plain,
    ( ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F )
   <= ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F ) ),
    inference(split,[status(esa)],['33'])).

thf('100',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t81_tmap_1,axiom,(
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
                        & ( v1_funct_2 @ E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) )
                        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) )
                     => ! [F: $i] :
                          ( ( m1_subset_1 @ F @ ( u1_struct_0 @ C ) )
                         => ! [G: $i] :
                              ( ( m1_subset_1 @ G @ ( u1_struct_0 @ D ) )
                             => ( ( ( F = G )
                                  & ( m1_pre_topc @ D @ C )
                                  & ( r1_tmap_1 @ C @ B @ E @ F ) )
                               => ( r1_tmap_1 @ D @ B @ ( k3_tmap_1 @ A @ B @ C @ D @ E ) @ G ) ) ) ) ) ) ) ) ) )).

thf('101',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ( v2_struct_0 @ X24 )
      | ~ ( v2_pre_topc @ X24 )
      | ~ ( l1_pre_topc @ X24 )
      | ( v2_struct_0 @ X25 )
      | ~ ( m1_pre_topc @ X25 @ X26 )
      | ~ ( m1_subset_1 @ X27 @ ( u1_struct_0 @ X28 ) )
      | ~ ( m1_pre_topc @ X25 @ X28 )
      | ~ ( r1_tmap_1 @ X28 @ X24 @ X29 @ X27 )
      | ( X27 != X30 )
      | ( r1_tmap_1 @ X25 @ X24 @ ( k3_tmap_1 @ X26 @ X24 @ X28 @ X25 @ X29 ) @ X30 )
      | ~ ( m1_subset_1 @ X30 @ ( u1_struct_0 @ X25 ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X28 ) @ ( u1_struct_0 @ X24 ) ) ) )
      | ~ ( v1_funct_2 @ X29 @ ( u1_struct_0 @ X28 ) @ ( u1_struct_0 @ X24 ) )
      | ~ ( v1_funct_1 @ X29 )
      | ~ ( m1_pre_topc @ X28 @ X26 )
      | ( v2_struct_0 @ X28 )
      | ~ ( l1_pre_topc @ X26 )
      | ~ ( v2_pre_topc @ X26 )
      | ( v2_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t81_tmap_1])).

thf('102',plain,(
    ! [X24: $i,X25: $i,X26: $i,X28: $i,X29: $i,X30: $i] :
      ( ( v2_struct_0 @ X26 )
      | ~ ( v2_pre_topc @ X26 )
      | ~ ( l1_pre_topc @ X26 )
      | ( v2_struct_0 @ X28 )
      | ~ ( m1_pre_topc @ X28 @ X26 )
      | ~ ( v1_funct_1 @ X29 )
      | ~ ( v1_funct_2 @ X29 @ ( u1_struct_0 @ X28 ) @ ( u1_struct_0 @ X24 ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X28 ) @ ( u1_struct_0 @ X24 ) ) ) )
      | ~ ( m1_subset_1 @ X30 @ ( u1_struct_0 @ X25 ) )
      | ( r1_tmap_1 @ X25 @ X24 @ ( k3_tmap_1 @ X26 @ X24 @ X28 @ X25 @ X29 ) @ X30 )
      | ~ ( r1_tmap_1 @ X28 @ X24 @ X29 @ X30 )
      | ~ ( m1_pre_topc @ X25 @ X28 )
      | ~ ( m1_subset_1 @ X30 @ ( u1_struct_0 @ X28 ) )
      | ~ ( m1_pre_topc @ X25 @ X26 )
      | ( v2_struct_0 @ X25 )
      | ~ ( l1_pre_topc @ X24 )
      | ~ ( v2_pre_topc @ X24 )
      | ( v2_struct_0 @ X24 ) ) ),
    inference(simplify,[status(thm)],['101'])).

thf('103',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X1 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ sk_D ) )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ~ ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X2 )
      | ( r1_tmap_1 @ X0 @ sk_B @ ( k3_tmap_1 @ X1 @ sk_B @ sk_D @ X0 @ sk_E ) @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( m1_pre_topc @ sk_D @ X1 )
      | ( v2_struct_0 @ sk_D )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['100','102'])).

thf('104',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X1 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ sk_D ) )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ~ ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X2 )
      | ( r1_tmap_1 @ X0 @ sk_B @ ( k3_tmap_1 @ X1 @ sk_B @ sk_D @ X0 @ sk_E ) @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ sk_D @ X1 )
      | ( v2_struct_0 @ sk_D )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(demod,[status(thm)],['103','104','105','106','107'])).

thf('109',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( v2_struct_0 @ X0 )
        | ~ ( v2_pre_topc @ X0 )
        | ~ ( l1_pre_topc @ X0 )
        | ( v2_struct_0 @ sk_D )
        | ~ ( m1_pre_topc @ sk_D @ X0 )
        | ~ ( m1_subset_1 @ sk_F @ ( u1_struct_0 @ X1 ) )
        | ( r1_tmap_1 @ X1 @ sk_B @ ( k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E ) @ sk_F )
        | ~ ( m1_pre_topc @ X1 @ sk_D )
        | ~ ( m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_D ) )
        | ~ ( m1_pre_topc @ X1 @ X0 )
        | ( v2_struct_0 @ X1 )
        | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F ) ),
    inference('sup-',[status(thm)],['99','108'])).

thf('110',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( v2_struct_0 @ X0 )
        | ~ ( v2_pre_topc @ X0 )
        | ~ ( l1_pre_topc @ X0 )
        | ( v2_struct_0 @ sk_D )
        | ~ ( m1_pre_topc @ sk_D @ X0 )
        | ~ ( m1_subset_1 @ sk_F @ ( u1_struct_0 @ X1 ) )
        | ( r1_tmap_1 @ X1 @ sk_B @ ( k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E ) @ sk_F )
        | ~ ( m1_pre_topc @ X1 @ sk_D )
        | ~ ( m1_pre_topc @ X1 @ X0 )
        | ( v2_struct_0 @ X1 )
        | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F ) ),
    inference(demod,[status(thm)],['109','110'])).

thf('112',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_B )
        | ( v2_struct_0 @ sk_C )
        | ~ ( m1_pre_topc @ sk_C @ X0 )
        | ~ ( m1_pre_topc @ sk_C @ sk_D )
        | ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ X0 @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_F )
        | ~ ( m1_pre_topc @ sk_D @ X0 )
        | ( v2_struct_0 @ sk_D )
        | ~ ( l1_pre_topc @ X0 )
        | ~ ( v2_pre_topc @ X0 )
        | ( v2_struct_0 @ X0 ) )
   <= ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F ) ),
    inference('sup-',[status(thm)],['98','111'])).

thf('113',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_B )
        | ( v2_struct_0 @ sk_C )
        | ~ ( m1_pre_topc @ sk_C @ X0 )
        | ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ X0 @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_F )
        | ~ ( m1_pre_topc @ sk_D @ X0 )
        | ( v2_struct_0 @ sk_D )
        | ~ ( l1_pre_topc @ X0 )
        | ~ ( v2_pre_topc @ X0 )
        | ( v2_struct_0 @ X0 ) )
   <= ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F ) ),
    inference(demod,[status(thm)],['112','113'])).

thf('115',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ~ ( m1_pre_topc @ sk_D @ sk_A )
      | ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_F )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F ) ),
    inference('sup-',[status(thm)],['97','114'])).

thf('116',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_F )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F ) ),
    inference(demod,[status(thm)],['115','116','117','118'])).

thf('120',plain,
    ( ~ ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_G )
   <= ~ ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_G ) ),
    inference(split,[status(esa)],['0'])).

thf('121',plain,(
    sk_F = sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,
    ( ~ ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_F )
   <= ~ ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_G ) ),
    inference(demod,[status(thm)],['120','121'])).

thf('123',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ~ ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_G )
      & ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F ) ) ),
    inference('sup-',[status(thm)],['119','122'])).

thf('124',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('125',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ~ ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_G )
      & ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F ) ) ),
    inference('sup-',[status(thm)],['123','124'])).

thf('126',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_C ) )
   <= ( ~ ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_G )
      & ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F ) ) ),
    inference(clc,[status(thm)],['125','126'])).

thf('128',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('129',plain,
    ( ( v2_struct_0 @ sk_C )
   <= ( ~ ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_G )
      & ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F ) ) ),
    inference(clc,[status(thm)],['127','128'])).

thf('130',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('131',plain,
    ( ~ ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F )
    | ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_G ) ),
    inference('sup-',[status(thm)],['129','130'])).

thf('132',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','95','96','131'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.58oCyH4TUf
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:50:34 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.20/0.35  % Number of cores: 8
% 0.20/0.35  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 0.22/0.50  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.22/0.50  % Solved by: fo/fo7.sh
% 0.22/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.50  % done 98 iterations in 0.043s
% 0.22/0.50  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.22/0.50  % SZS output start Refutation
% 0.22/0.50  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.22/0.50  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.22/0.50  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.22/0.50  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.22/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.50  thf(k1_connsp_2_type, type, k1_connsp_2: $i > $i > $i).
% 0.22/0.50  thf(sk_D_type, type, sk_D: $i).
% 0.22/0.50  thf(sk_G_type, type, sk_G: $i).
% 0.22/0.50  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.22/0.50  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.22/0.50  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.22/0.50  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.22/0.50  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.50  thf(sk_E_type, type, sk_E: $i).
% 0.22/0.50  thf(r1_tmap_1_type, type, r1_tmap_1: $i > $i > $i > $i > $o).
% 0.22/0.50  thf(k3_tmap_1_type, type, k3_tmap_1: $i > $i > $i > $i > $i > $i).
% 0.22/0.50  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.50  thf(sk_F_type, type, sk_F: $i).
% 0.22/0.50  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.22/0.50  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.22/0.50  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.22/0.50  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.50  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.22/0.50  thf(v1_tsep_1_type, type, v1_tsep_1: $i > $i > $o).
% 0.22/0.50  thf(sk_C_type, type, sk_C: $i).
% 0.22/0.50  thf(t86_tmap_1, conjecture,
% 0.22/0.50    (![A:$i]:
% 0.22/0.50     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.22/0.50       ( ![B:$i]:
% 0.22/0.50         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.22/0.50             ( l1_pre_topc @ B ) ) =>
% 0.22/0.50           ( ![C:$i]:
% 0.22/0.50             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.22/0.50               ( ![D:$i]:
% 0.22/0.50                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.22/0.50                   ( ![E:$i]:
% 0.22/0.50                     ( ( ( v1_funct_1 @ E ) & 
% 0.22/0.50                         ( v1_funct_2 @
% 0.22/0.50                           E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 0.22/0.50                         ( m1_subset_1 @
% 0.22/0.50                           E @ 
% 0.22/0.50                           ( k1_zfmisc_1 @
% 0.22/0.50                             ( k2_zfmisc_1 @
% 0.22/0.50                               ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.22/0.50                       ( ( ( v1_tsep_1 @ C @ D ) & ( m1_pre_topc @ C @ D ) ) =>
% 0.22/0.50                         ( ![F:$i]:
% 0.22/0.50                           ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 0.22/0.50                             ( ![G:$i]:
% 0.22/0.50                               ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) ) =>
% 0.22/0.50                                 ( ( ( F ) = ( G ) ) =>
% 0.22/0.50                                   ( ( r1_tmap_1 @ D @ B @ E @ F ) <=>
% 0.22/0.50                                     ( r1_tmap_1 @
% 0.22/0.50                                       C @ B @ 
% 0.22/0.50                                       ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ G ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.22/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.50    (~( ![A:$i]:
% 0.22/0.50        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.22/0.50            ( l1_pre_topc @ A ) ) =>
% 0.22/0.50          ( ![B:$i]:
% 0.22/0.50            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.22/0.50                ( l1_pre_topc @ B ) ) =>
% 0.22/0.50              ( ![C:$i]:
% 0.22/0.50                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.22/0.50                  ( ![D:$i]:
% 0.22/0.50                    ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.22/0.50                      ( ![E:$i]:
% 0.22/0.50                        ( ( ( v1_funct_1 @ E ) & 
% 0.22/0.50                            ( v1_funct_2 @
% 0.22/0.50                              E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 0.22/0.50                            ( m1_subset_1 @
% 0.22/0.50                              E @ 
% 0.22/0.50                              ( k1_zfmisc_1 @
% 0.22/0.50                                ( k2_zfmisc_1 @
% 0.22/0.50                                  ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.22/0.50                          ( ( ( v1_tsep_1 @ C @ D ) & ( m1_pre_topc @ C @ D ) ) =>
% 0.22/0.50                            ( ![F:$i]:
% 0.22/0.50                              ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 0.22/0.50                                ( ![G:$i]:
% 0.22/0.50                                  ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) ) =>
% 0.22/0.50                                    ( ( ( F ) = ( G ) ) =>
% 0.22/0.50                                      ( ( r1_tmap_1 @ D @ B @ E @ F ) <=>
% 0.22/0.50                                        ( r1_tmap_1 @
% 0.22/0.50                                          C @ B @ 
% 0.22/0.50                                          ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ G ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.22/0.50    inference('cnf.neg', [status(esa)], [t86_tmap_1])).
% 0.22/0.50  thf('0', plain,
% 0.22/0.50      ((~ (r1_tmap_1 @ sk_C @ sk_B @ 
% 0.22/0.50           (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_G)
% 0.22/0.50        | ~ (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('1', plain,
% 0.22/0.50      (~ ((r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)) | 
% 0.22/0.50       ~
% 0.22/0.50       ((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.22/0.50         (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_G))),
% 0.22/0.50      inference('split', [status(esa)], ['0'])).
% 0.22/0.50  thf('2', plain, ((m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_C))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('3', plain, (((sk_F) = (sk_G))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('4', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C))),
% 0.22/0.50      inference('demod', [status(thm)], ['2', '3'])).
% 0.22/0.50  thf(t30_connsp_2, axiom,
% 0.22/0.50    (![A:$i]:
% 0.22/0.50     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.22/0.50       ( ![B:$i]:
% 0.22/0.50         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.22/0.50           ( r2_hidden @ B @ ( k1_connsp_2 @ A @ B ) ) ) ) ))).
% 0.22/0.50  thf('5', plain,
% 0.22/0.50      (![X14 : $i, X15 : $i]:
% 0.22/0.50         (~ (m1_subset_1 @ X14 @ (u1_struct_0 @ X15))
% 0.22/0.50          | (r2_hidden @ X14 @ (k1_connsp_2 @ X15 @ X14))
% 0.22/0.50          | ~ (l1_pre_topc @ X15)
% 0.22/0.50          | ~ (v2_pre_topc @ X15)
% 0.22/0.50          | (v2_struct_0 @ X15))),
% 0.22/0.50      inference('cnf', [status(esa)], [t30_connsp_2])).
% 0.22/0.50  thf('6', plain,
% 0.22/0.50      (((v2_struct_0 @ sk_C)
% 0.22/0.50        | ~ (v2_pre_topc @ sk_C)
% 0.22/0.50        | ~ (l1_pre_topc @ sk_C)
% 0.22/0.50        | (r2_hidden @ sk_F @ (k1_connsp_2 @ sk_C @ sk_F)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['4', '5'])).
% 0.22/0.50  thf('7', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf(cc1_pre_topc, axiom,
% 0.22/0.50    (![A:$i]:
% 0.22/0.50     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.22/0.50       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( v2_pre_topc @ B ) ) ) ))).
% 0.22/0.50  thf('8', plain,
% 0.22/0.50      (![X8 : $i, X9 : $i]:
% 0.22/0.50         (~ (m1_pre_topc @ X8 @ X9)
% 0.22/0.50          | (v2_pre_topc @ X8)
% 0.22/0.50          | ~ (l1_pre_topc @ X9)
% 0.22/0.50          | ~ (v2_pre_topc @ X9))),
% 0.22/0.50      inference('cnf', [status(esa)], [cc1_pre_topc])).
% 0.22/0.50  thf('9', plain,
% 0.22/0.50      ((~ (v2_pre_topc @ sk_A) | ~ (l1_pre_topc @ sk_A) | (v2_pre_topc @ sk_C))),
% 0.22/0.50      inference('sup-', [status(thm)], ['7', '8'])).
% 0.22/0.50  thf('10', plain, ((v2_pre_topc @ sk_A)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('11', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('12', plain, ((v2_pre_topc @ sk_C)),
% 0.22/0.50      inference('demod', [status(thm)], ['9', '10', '11'])).
% 0.22/0.50  thf('13', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf(dt_m1_pre_topc, axiom,
% 0.22/0.50    (![A:$i]:
% 0.22/0.50     ( ( l1_pre_topc @ A ) =>
% 0.22/0.50       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.22/0.50  thf('14', plain,
% 0.22/0.50      (![X10 : $i, X11 : $i]:
% 0.22/0.50         (~ (m1_pre_topc @ X10 @ X11)
% 0.22/0.50          | (l1_pre_topc @ X10)
% 0.22/0.50          | ~ (l1_pre_topc @ X11))),
% 0.22/0.50      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.22/0.50  thf('15', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_C))),
% 0.22/0.50      inference('sup-', [status(thm)], ['13', '14'])).
% 0.22/0.50  thf('16', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('17', plain, ((l1_pre_topc @ sk_C)),
% 0.22/0.50      inference('demod', [status(thm)], ['15', '16'])).
% 0.22/0.50  thf('18', plain,
% 0.22/0.50      (((v2_struct_0 @ sk_C) | (r2_hidden @ sk_F @ (k1_connsp_2 @ sk_C @ sk_F)))),
% 0.22/0.50      inference('demod', [status(thm)], ['6', '12', '17'])).
% 0.22/0.50  thf('19', plain, (~ (v2_struct_0 @ sk_C)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('20', plain, ((r2_hidden @ sk_F @ (k1_connsp_2 @ sk_C @ sk_F))),
% 0.22/0.50      inference('clc', [status(thm)], ['18', '19'])).
% 0.22/0.50  thf('21', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C))),
% 0.22/0.50      inference('demod', [status(thm)], ['2', '3'])).
% 0.22/0.50  thf(t2_subset, axiom,
% 0.22/0.50    (![A:$i,B:$i]:
% 0.22/0.50     ( ( m1_subset_1 @ A @ B ) =>
% 0.22/0.50       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.22/0.50  thf('22', plain,
% 0.22/0.50      (![X3 : $i, X4 : $i]:
% 0.22/0.50         ((r2_hidden @ X3 @ X4)
% 0.22/0.50          | (v1_xboole_0 @ X4)
% 0.22/0.50          | ~ (m1_subset_1 @ X3 @ X4))),
% 0.22/0.50      inference('cnf', [status(esa)], [t2_subset])).
% 0.22/0.50  thf('23', plain,
% 0.22/0.50      (((v1_xboole_0 @ (u1_struct_0 @ sk_C))
% 0.22/0.50        | (r2_hidden @ sk_F @ (u1_struct_0 @ sk_C)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['21', '22'])).
% 0.22/0.50  thf('24', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf(t1_tsep_1, axiom,
% 0.22/0.50    (![A:$i]:
% 0.22/0.50     ( ( l1_pre_topc @ A ) =>
% 0.22/0.50       ( ![B:$i]:
% 0.22/0.50         ( ( m1_pre_topc @ B @ A ) =>
% 0.22/0.50           ( m1_subset_1 @
% 0.22/0.50             ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.22/0.50  thf('25', plain,
% 0.22/0.50      (![X19 : $i, X20 : $i]:
% 0.22/0.50         (~ (m1_pre_topc @ X19 @ X20)
% 0.22/0.50          | (m1_subset_1 @ (u1_struct_0 @ X19) @ 
% 0.22/0.50             (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.22/0.50          | ~ (l1_pre_topc @ X20))),
% 0.22/0.50      inference('cnf', [status(esa)], [t1_tsep_1])).
% 0.22/0.50  thf('26', plain,
% 0.22/0.50      ((~ (l1_pre_topc @ sk_D)
% 0.22/0.50        | (m1_subset_1 @ (u1_struct_0 @ sk_C) @ 
% 0.22/0.50           (k1_zfmisc_1 @ (u1_struct_0 @ sk_D))))),
% 0.22/0.50      inference('sup-', [status(thm)], ['24', '25'])).
% 0.22/0.50  thf('27', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('28', plain,
% 0.22/0.50      (![X10 : $i, X11 : $i]:
% 0.22/0.50         (~ (m1_pre_topc @ X10 @ X11)
% 0.22/0.50          | (l1_pre_topc @ X10)
% 0.22/0.50          | ~ (l1_pre_topc @ X11))),
% 0.22/0.50      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.22/0.50  thf('29', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_D))),
% 0.22/0.50      inference('sup-', [status(thm)], ['27', '28'])).
% 0.22/0.50  thf('30', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('31', plain, ((l1_pre_topc @ sk_D)),
% 0.22/0.50      inference('demod', [status(thm)], ['29', '30'])).
% 0.22/0.50  thf('32', plain,
% 0.22/0.50      ((m1_subset_1 @ (u1_struct_0 @ sk_C) @ 
% 0.22/0.50        (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))),
% 0.22/0.50      inference('demod', [status(thm)], ['26', '31'])).
% 0.22/0.50  thf('33', plain,
% 0.22/0.50      (((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.22/0.50         (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_G)
% 0.22/0.50        | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('34', plain,
% 0.22/0.50      (((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.22/0.50         (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_G))
% 0.22/0.50         <= (((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.22/0.50               (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_G)))),
% 0.22/0.50      inference('split', [status(esa)], ['33'])).
% 0.22/0.50  thf('35', plain, (((sk_F) = (sk_G))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('36', plain,
% 0.22/0.50      (((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.22/0.50         (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_F))
% 0.22/0.50         <= (((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.22/0.50               (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_G)))),
% 0.22/0.50      inference('demod', [status(thm)], ['34', '35'])).
% 0.22/0.50  thf('37', plain,
% 0.22/0.50      ((m1_subset_1 @ sk_E @ 
% 0.22/0.50        (k1_zfmisc_1 @ 
% 0.22/0.50         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf(t84_tmap_1, axiom,
% 0.22/0.50    (![A:$i]:
% 0.22/0.50     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.22/0.50       ( ![B:$i]:
% 0.22/0.50         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.22/0.50             ( l1_pre_topc @ B ) ) =>
% 0.22/0.50           ( ![C:$i]:
% 0.22/0.50             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.22/0.50               ( ![D:$i]:
% 0.22/0.50                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.22/0.50                   ( ![E:$i]:
% 0.22/0.50                     ( ( ( v1_funct_1 @ E ) & 
% 0.22/0.50                         ( v1_funct_2 @
% 0.22/0.50                           E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 0.22/0.50                         ( m1_subset_1 @
% 0.22/0.50                           E @ 
% 0.22/0.50                           ( k1_zfmisc_1 @
% 0.22/0.50                             ( k2_zfmisc_1 @
% 0.22/0.50                               ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.22/0.50                       ( ( m1_pre_topc @ C @ D ) =>
% 0.22/0.50                         ( ![F:$i]:
% 0.22/0.50                           ( ( m1_subset_1 @
% 0.22/0.50                               F @ ( k1_zfmisc_1 @ ( u1_struct_0 @ D ) ) ) =>
% 0.22/0.50                             ( ![G:$i]:
% 0.22/0.50                               ( ( m1_subset_1 @ G @ ( u1_struct_0 @ D ) ) =>
% 0.22/0.50                                 ( ![H:$i]:
% 0.22/0.50                                   ( ( m1_subset_1 @ H @ ( u1_struct_0 @ C ) ) =>
% 0.22/0.50                                     ( ( ( v3_pre_topc @ F @ D ) & 
% 0.22/0.50                                         ( r2_hidden @ G @ F ) & 
% 0.22/0.50                                         ( r1_tarski @ F @ ( u1_struct_0 @ C ) ) & 
% 0.22/0.50                                         ( ( G ) = ( H ) ) ) =>
% 0.22/0.50                                       ( ( r1_tmap_1 @ D @ B @ E @ G ) <=>
% 0.22/0.50                                         ( r1_tmap_1 @
% 0.22/0.50                                           C @ B @ 
% 0.22/0.50                                           ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ 
% 0.22/0.50                                           H ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.22/0.50  thf('38', plain,
% 0.22/0.50      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i, X35 : $i, X36 : $i, X37 : $i, 
% 0.22/0.50         X38 : $i]:
% 0.22/0.50         ((v2_struct_0 @ X31)
% 0.22/0.50          | ~ (v2_pre_topc @ X31)
% 0.22/0.50          | ~ (l1_pre_topc @ X31)
% 0.22/0.50          | (v2_struct_0 @ X32)
% 0.22/0.50          | ~ (m1_pre_topc @ X32 @ X33)
% 0.22/0.50          | ~ (m1_pre_topc @ X34 @ X32)
% 0.22/0.50          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (u1_struct_0 @ X32)))
% 0.22/0.50          | ~ (m1_subset_1 @ X36 @ (u1_struct_0 @ X34))
% 0.22/0.50          | ~ (r1_tmap_1 @ X34 @ X31 @ 
% 0.22/0.50               (k3_tmap_1 @ X33 @ X31 @ X32 @ X34 @ X37) @ X36)
% 0.22/0.50          | (r1_tmap_1 @ X32 @ X31 @ X37 @ X38)
% 0.22/0.50          | ((X38) != (X36))
% 0.22/0.50          | ~ (r1_tarski @ X35 @ (u1_struct_0 @ X34))
% 0.22/0.50          | ~ (r2_hidden @ X38 @ X35)
% 0.22/0.50          | ~ (v3_pre_topc @ X35 @ X32)
% 0.22/0.50          | ~ (m1_subset_1 @ X38 @ (u1_struct_0 @ X32))
% 0.22/0.50          | ~ (m1_subset_1 @ X37 @ 
% 0.22/0.50               (k1_zfmisc_1 @ 
% 0.22/0.50                (k2_zfmisc_1 @ (u1_struct_0 @ X32) @ (u1_struct_0 @ X31))))
% 0.22/0.50          | ~ (v1_funct_2 @ X37 @ (u1_struct_0 @ X32) @ (u1_struct_0 @ X31))
% 0.22/0.50          | ~ (v1_funct_1 @ X37)
% 0.22/0.50          | ~ (m1_pre_topc @ X34 @ X33)
% 0.22/0.50          | (v2_struct_0 @ X34)
% 0.22/0.50          | ~ (l1_pre_topc @ X33)
% 0.22/0.50          | ~ (v2_pre_topc @ X33)
% 0.22/0.50          | (v2_struct_0 @ X33))),
% 0.22/0.50      inference('cnf', [status(esa)], [t84_tmap_1])).
% 0.22/0.50  thf('39', plain,
% 0.22/0.50      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i, X35 : $i, X36 : $i, X37 : $i]:
% 0.22/0.50         ((v2_struct_0 @ X33)
% 0.22/0.50          | ~ (v2_pre_topc @ X33)
% 0.22/0.50          | ~ (l1_pre_topc @ X33)
% 0.22/0.50          | (v2_struct_0 @ X34)
% 0.22/0.50          | ~ (m1_pre_topc @ X34 @ X33)
% 0.22/0.50          | ~ (v1_funct_1 @ X37)
% 0.22/0.50          | ~ (v1_funct_2 @ X37 @ (u1_struct_0 @ X32) @ (u1_struct_0 @ X31))
% 0.22/0.50          | ~ (m1_subset_1 @ X37 @ 
% 0.22/0.50               (k1_zfmisc_1 @ 
% 0.22/0.50                (k2_zfmisc_1 @ (u1_struct_0 @ X32) @ (u1_struct_0 @ X31))))
% 0.22/0.50          | ~ (m1_subset_1 @ X36 @ (u1_struct_0 @ X32))
% 0.22/0.50          | ~ (v3_pre_topc @ X35 @ X32)
% 0.22/0.50          | ~ (r2_hidden @ X36 @ X35)
% 0.22/0.50          | ~ (r1_tarski @ X35 @ (u1_struct_0 @ X34))
% 0.22/0.50          | (r1_tmap_1 @ X32 @ X31 @ X37 @ X36)
% 0.22/0.50          | ~ (r1_tmap_1 @ X34 @ X31 @ 
% 0.22/0.50               (k3_tmap_1 @ X33 @ X31 @ X32 @ X34 @ X37) @ X36)
% 0.22/0.50          | ~ (m1_subset_1 @ X36 @ (u1_struct_0 @ X34))
% 0.22/0.50          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (u1_struct_0 @ X32)))
% 0.22/0.50          | ~ (m1_pre_topc @ X34 @ X32)
% 0.22/0.50          | ~ (m1_pre_topc @ X32 @ X33)
% 0.22/0.50          | (v2_struct_0 @ X32)
% 0.22/0.50          | ~ (l1_pre_topc @ X31)
% 0.22/0.50          | ~ (v2_pre_topc @ X31)
% 0.22/0.50          | (v2_struct_0 @ X31))),
% 0.22/0.50      inference('simplify', [status(thm)], ['38'])).
% 0.22/0.50  thf('40', plain,
% 0.22/0.50      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.22/0.50         ((v2_struct_0 @ sk_B)
% 0.22/0.50          | ~ (v2_pre_topc @ sk_B)
% 0.22/0.50          | ~ (l1_pre_topc @ sk_B)
% 0.22/0.50          | (v2_struct_0 @ sk_D)
% 0.22/0.50          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.22/0.50          | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.22/0.50          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))
% 0.22/0.50          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X1))
% 0.22/0.50          | ~ (r1_tmap_1 @ X1 @ sk_B @ 
% 0.22/0.50               (k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E) @ X3)
% 0.22/0.50          | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X3)
% 0.22/0.50          | ~ (r1_tarski @ X2 @ (u1_struct_0 @ X1))
% 0.22/0.50          | ~ (r2_hidden @ X3 @ X2)
% 0.22/0.50          | ~ (v3_pre_topc @ X2 @ sk_D)
% 0.22/0.50          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ sk_D))
% 0.22/0.50          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.22/0.50          | ~ (v1_funct_1 @ sk_E)
% 0.22/0.50          | ~ (m1_pre_topc @ X1 @ X0)
% 0.22/0.50          | (v2_struct_0 @ X1)
% 0.22/0.50          | ~ (l1_pre_topc @ X0)
% 0.22/0.50          | ~ (v2_pre_topc @ X0)
% 0.22/0.50          | (v2_struct_0 @ X0))),
% 0.22/0.50      inference('sup-', [status(thm)], ['37', '39'])).
% 0.22/0.50  thf('41', plain, ((v2_pre_topc @ sk_B)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('42', plain, ((l1_pre_topc @ sk_B)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('43', plain,
% 0.22/0.50      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('44', plain, ((v1_funct_1 @ sk_E)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('45', plain,
% 0.22/0.50      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.22/0.50         ((v2_struct_0 @ sk_B)
% 0.22/0.50          | (v2_struct_0 @ sk_D)
% 0.22/0.50          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.22/0.50          | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.22/0.50          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))
% 0.22/0.50          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X1))
% 0.22/0.50          | ~ (r1_tmap_1 @ X1 @ sk_B @ 
% 0.22/0.50               (k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E) @ X3)
% 0.22/0.50          | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X3)
% 0.22/0.50          | ~ (r1_tarski @ X2 @ (u1_struct_0 @ X1))
% 0.22/0.50          | ~ (r2_hidden @ X3 @ X2)
% 0.22/0.50          | ~ (v3_pre_topc @ X2 @ sk_D)
% 0.22/0.50          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ sk_D))
% 0.22/0.50          | ~ (m1_pre_topc @ X1 @ X0)
% 0.22/0.50          | (v2_struct_0 @ X1)
% 0.22/0.50          | ~ (l1_pre_topc @ X0)
% 0.22/0.50          | ~ (v2_pre_topc @ X0)
% 0.22/0.50          | (v2_struct_0 @ X0))),
% 0.22/0.50      inference('demod', [status(thm)], ['40', '41', '42', '43', '44'])).
% 0.22/0.50  thf('46', plain,
% 0.22/0.50      ((![X0 : $i]:
% 0.22/0.50          ((v2_struct_0 @ sk_A)
% 0.22/0.50           | ~ (v2_pre_topc @ sk_A)
% 0.22/0.50           | ~ (l1_pre_topc @ sk_A)
% 0.22/0.50           | (v2_struct_0 @ sk_C)
% 0.22/0.50           | ~ (m1_pre_topc @ sk_C @ sk_A)
% 0.22/0.50           | ~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_D))
% 0.22/0.50           | ~ (v3_pre_topc @ X0 @ sk_D)
% 0.22/0.50           | ~ (r2_hidden @ sk_F @ X0)
% 0.22/0.50           | ~ (r1_tarski @ X0 @ (u1_struct_0 @ sk_C))
% 0.22/0.50           | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)
% 0.22/0.50           | ~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C))
% 0.22/0.50           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))
% 0.22/0.50           | ~ (m1_pre_topc @ sk_C @ sk_D)
% 0.22/0.50           | ~ (m1_pre_topc @ sk_D @ sk_A)
% 0.22/0.50           | (v2_struct_0 @ sk_D)
% 0.22/0.50           | (v2_struct_0 @ sk_B)))
% 0.22/0.50         <= (((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.22/0.50               (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_G)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['36', '45'])).
% 0.22/0.50  thf('47', plain, ((v2_pre_topc @ sk_A)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('48', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('49', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('50', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_D))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('51', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C))),
% 0.22/0.50      inference('demod', [status(thm)], ['2', '3'])).
% 0.22/0.50  thf('52', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('53', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('54', plain,
% 0.22/0.50      ((![X0 : $i]:
% 0.22/0.50          ((v2_struct_0 @ sk_A)
% 0.22/0.50           | (v2_struct_0 @ sk_C)
% 0.22/0.50           | ~ (v3_pre_topc @ X0 @ sk_D)
% 0.22/0.50           | ~ (r2_hidden @ sk_F @ X0)
% 0.22/0.50           | ~ (r1_tarski @ X0 @ (u1_struct_0 @ sk_C))
% 0.22/0.50           | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)
% 0.22/0.50           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))
% 0.22/0.50           | (v2_struct_0 @ sk_D)
% 0.22/0.50           | (v2_struct_0 @ sk_B)))
% 0.22/0.50         <= (((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.22/0.50               (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_G)))),
% 0.22/0.50      inference('demod', [status(thm)],
% 0.22/0.50                ['46', '47', '48', '49', '50', '51', '52', '53'])).
% 0.22/0.50  thf('55', plain,
% 0.22/0.50      ((((v2_struct_0 @ sk_B)
% 0.22/0.50         | (v2_struct_0 @ sk_D)
% 0.22/0.50         | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)
% 0.22/0.50         | ~ (r1_tarski @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_C))
% 0.22/0.50         | ~ (r2_hidden @ sk_F @ (u1_struct_0 @ sk_C))
% 0.22/0.50         | ~ (v3_pre_topc @ (u1_struct_0 @ sk_C) @ sk_D)
% 0.22/0.50         | (v2_struct_0 @ sk_C)
% 0.22/0.50         | (v2_struct_0 @ sk_A)))
% 0.22/0.50         <= (((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.22/0.50               (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_G)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['32', '54'])).
% 0.22/0.50  thf(d10_xboole_0, axiom,
% 0.22/0.50    (![A:$i,B:$i]:
% 0.22/0.50     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.22/0.50  thf('56', plain,
% 0.22/0.50      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.22/0.50      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.22/0.50  thf('57', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.22/0.50      inference('simplify', [status(thm)], ['56'])).
% 0.22/0.50  thf('58', plain,
% 0.22/0.50      ((m1_subset_1 @ (u1_struct_0 @ sk_C) @ 
% 0.22/0.50        (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))),
% 0.22/0.50      inference('demod', [status(thm)], ['26', '31'])).
% 0.22/0.50  thf(t16_tsep_1, axiom,
% 0.22/0.50    (![A:$i]:
% 0.22/0.50     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.22/0.50       ( ![B:$i]:
% 0.22/0.50         ( ( m1_pre_topc @ B @ A ) =>
% 0.22/0.50           ( ![C:$i]:
% 0.22/0.50             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.50               ( ( ( C ) = ( u1_struct_0 @ B ) ) =>
% 0.22/0.50                 ( ( ( v1_tsep_1 @ B @ A ) & ( m1_pre_topc @ B @ A ) ) <=>
% 0.22/0.50                   ( v3_pre_topc @ C @ A ) ) ) ) ) ) ) ))).
% 0.22/0.50  thf('59', plain,
% 0.22/0.50      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.22/0.50         (~ (m1_pre_topc @ X16 @ X17)
% 0.22/0.50          | ((X18) != (u1_struct_0 @ X16))
% 0.22/0.50          | ~ (v1_tsep_1 @ X16 @ X17)
% 0.22/0.50          | ~ (m1_pre_topc @ X16 @ X17)
% 0.22/0.50          | (v3_pre_topc @ X18 @ X17)
% 0.22/0.50          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.22/0.50          | ~ (l1_pre_topc @ X17)
% 0.22/0.50          | ~ (v2_pre_topc @ X17))),
% 0.22/0.50      inference('cnf', [status(esa)], [t16_tsep_1])).
% 0.22/0.50  thf('60', plain,
% 0.22/0.50      (![X16 : $i, X17 : $i]:
% 0.22/0.50         (~ (v2_pre_topc @ X17)
% 0.22/0.50          | ~ (l1_pre_topc @ X17)
% 0.22/0.50          | ~ (m1_subset_1 @ (u1_struct_0 @ X16) @ 
% 0.22/0.50               (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.22/0.50          | (v3_pre_topc @ (u1_struct_0 @ X16) @ X17)
% 0.22/0.50          | ~ (v1_tsep_1 @ X16 @ X17)
% 0.22/0.50          | ~ (m1_pre_topc @ X16 @ X17))),
% 0.22/0.50      inference('simplify', [status(thm)], ['59'])).
% 0.22/0.50  thf('61', plain,
% 0.22/0.50      ((~ (m1_pre_topc @ sk_C @ sk_D)
% 0.22/0.50        | ~ (v1_tsep_1 @ sk_C @ sk_D)
% 0.22/0.50        | (v3_pre_topc @ (u1_struct_0 @ sk_C) @ sk_D)
% 0.22/0.50        | ~ (l1_pre_topc @ sk_D)
% 0.22/0.50        | ~ (v2_pre_topc @ sk_D))),
% 0.22/0.50      inference('sup-', [status(thm)], ['58', '60'])).
% 0.22/0.50  thf('62', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('63', plain, ((v1_tsep_1 @ sk_C @ sk_D)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('64', plain, ((l1_pre_topc @ sk_D)),
% 0.22/0.50      inference('demod', [status(thm)], ['29', '30'])).
% 0.22/0.50  thf('65', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('66', plain,
% 0.22/0.50      (![X8 : $i, X9 : $i]:
% 0.22/0.50         (~ (m1_pre_topc @ X8 @ X9)
% 0.22/0.50          | (v2_pre_topc @ X8)
% 0.22/0.50          | ~ (l1_pre_topc @ X9)
% 0.22/0.50          | ~ (v2_pre_topc @ X9))),
% 0.22/0.50      inference('cnf', [status(esa)], [cc1_pre_topc])).
% 0.22/0.50  thf('67', plain,
% 0.22/0.50      ((~ (v2_pre_topc @ sk_A) | ~ (l1_pre_topc @ sk_A) | (v2_pre_topc @ sk_D))),
% 0.22/0.50      inference('sup-', [status(thm)], ['65', '66'])).
% 0.22/0.50  thf('68', plain, ((v2_pre_topc @ sk_A)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('69', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('70', plain, ((v2_pre_topc @ sk_D)),
% 0.22/0.50      inference('demod', [status(thm)], ['67', '68', '69'])).
% 0.22/0.50  thf('71', plain, ((v3_pre_topc @ (u1_struct_0 @ sk_C) @ sk_D)),
% 0.22/0.50      inference('demod', [status(thm)], ['61', '62', '63', '64', '70'])).
% 0.22/0.50  thf('72', plain,
% 0.22/0.50      ((((v2_struct_0 @ sk_B)
% 0.22/0.50         | (v2_struct_0 @ sk_D)
% 0.22/0.50         | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)
% 0.22/0.50         | ~ (r2_hidden @ sk_F @ (u1_struct_0 @ sk_C))
% 0.22/0.50         | (v2_struct_0 @ sk_C)
% 0.22/0.50         | (v2_struct_0 @ sk_A)))
% 0.22/0.50         <= (((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.22/0.50               (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_G)))),
% 0.22/0.50      inference('demod', [status(thm)], ['55', '57', '71'])).
% 0.22/0.50  thf('73', plain,
% 0.22/0.50      ((((v1_xboole_0 @ (u1_struct_0 @ sk_C))
% 0.22/0.50         | (v2_struct_0 @ sk_A)
% 0.22/0.50         | (v2_struct_0 @ sk_C)
% 0.22/0.50         | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)
% 0.22/0.50         | (v2_struct_0 @ sk_D)
% 0.22/0.50         | (v2_struct_0 @ sk_B)))
% 0.22/0.50         <= (((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.22/0.50               (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_G)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['23', '72'])).
% 0.22/0.50  thf('74', plain,
% 0.22/0.50      ((~ (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F))
% 0.22/0.50         <= (~ ((r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)))),
% 0.22/0.50      inference('split', [status(esa)], ['0'])).
% 0.22/0.50  thf('75', plain,
% 0.22/0.50      ((((v2_struct_0 @ sk_B)
% 0.22/0.50         | (v2_struct_0 @ sk_D)
% 0.22/0.50         | (v2_struct_0 @ sk_C)
% 0.22/0.50         | (v2_struct_0 @ sk_A)
% 0.22/0.50         | (v1_xboole_0 @ (u1_struct_0 @ sk_C))))
% 0.22/0.50         <= (~ ((r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)) & 
% 0.22/0.50             ((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.22/0.50               (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_G)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['73', '74'])).
% 0.22/0.50  thf('76', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C))),
% 0.22/0.50      inference('demod', [status(thm)], ['2', '3'])).
% 0.22/0.50  thf(dt_k1_connsp_2, axiom,
% 0.22/0.50    (![A:$i,B:$i]:
% 0.22/0.50     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.22/0.50         ( l1_pre_topc @ A ) & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.50       ( m1_subset_1 @
% 0.22/0.50         ( k1_connsp_2 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.22/0.50  thf('77', plain,
% 0.22/0.50      (![X12 : $i, X13 : $i]:
% 0.22/0.50         (~ (l1_pre_topc @ X12)
% 0.22/0.50          | ~ (v2_pre_topc @ X12)
% 0.22/0.50          | (v2_struct_0 @ X12)
% 0.22/0.50          | ~ (m1_subset_1 @ X13 @ (u1_struct_0 @ X12))
% 0.22/0.50          | (m1_subset_1 @ (k1_connsp_2 @ X12 @ X13) @ 
% 0.22/0.50             (k1_zfmisc_1 @ (u1_struct_0 @ X12))))),
% 0.22/0.50      inference('cnf', [status(esa)], [dt_k1_connsp_2])).
% 0.22/0.50  thf('78', plain,
% 0.22/0.50      (((m1_subset_1 @ (k1_connsp_2 @ sk_C @ sk_F) @ 
% 0.22/0.50         (k1_zfmisc_1 @ (u1_struct_0 @ sk_C)))
% 0.22/0.50        | (v2_struct_0 @ sk_C)
% 0.22/0.50        | ~ (v2_pre_topc @ sk_C)
% 0.22/0.50        | ~ (l1_pre_topc @ sk_C))),
% 0.22/0.50      inference('sup-', [status(thm)], ['76', '77'])).
% 0.22/0.50  thf('79', plain, ((v2_pre_topc @ sk_C)),
% 0.22/0.50      inference('demod', [status(thm)], ['9', '10', '11'])).
% 0.22/0.50  thf('80', plain, ((l1_pre_topc @ sk_C)),
% 0.22/0.50      inference('demod', [status(thm)], ['15', '16'])).
% 0.22/0.50  thf('81', plain,
% 0.22/0.50      (((m1_subset_1 @ (k1_connsp_2 @ sk_C @ sk_F) @ 
% 0.22/0.50         (k1_zfmisc_1 @ (u1_struct_0 @ sk_C)))
% 0.22/0.50        | (v2_struct_0 @ sk_C))),
% 0.22/0.50      inference('demod', [status(thm)], ['78', '79', '80'])).
% 0.22/0.50  thf('82', plain, (~ (v2_struct_0 @ sk_C)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('83', plain,
% 0.22/0.50      ((m1_subset_1 @ (k1_connsp_2 @ sk_C @ sk_F) @ 
% 0.22/0.50        (k1_zfmisc_1 @ (u1_struct_0 @ sk_C)))),
% 0.22/0.50      inference('clc', [status(thm)], ['81', '82'])).
% 0.22/0.50  thf(t5_subset, axiom,
% 0.22/0.50    (![A:$i,B:$i,C:$i]:
% 0.22/0.50     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 0.22/0.50          ( v1_xboole_0 @ C ) ) ))).
% 0.22/0.50  thf('84', plain,
% 0.22/0.50      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.22/0.50         (~ (r2_hidden @ X5 @ X6)
% 0.22/0.50          | ~ (v1_xboole_0 @ X7)
% 0.22/0.50          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7)))),
% 0.22/0.50      inference('cnf', [status(esa)], [t5_subset])).
% 0.22/0.50  thf('85', plain,
% 0.22/0.50      (![X0 : $i]:
% 0.22/0.50         (~ (v1_xboole_0 @ (u1_struct_0 @ sk_C))
% 0.22/0.50          | ~ (r2_hidden @ X0 @ (k1_connsp_2 @ sk_C @ sk_F)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['83', '84'])).
% 0.22/0.50  thf('86', plain,
% 0.22/0.50      ((![X0 : $i]:
% 0.22/0.50          ((v2_struct_0 @ sk_A)
% 0.22/0.50           | (v2_struct_0 @ sk_C)
% 0.22/0.50           | (v2_struct_0 @ sk_D)
% 0.22/0.50           | (v2_struct_0 @ sk_B)
% 0.22/0.50           | ~ (r2_hidden @ X0 @ (k1_connsp_2 @ sk_C @ sk_F))))
% 0.22/0.50         <= (~ ((r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)) & 
% 0.22/0.50             ((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.22/0.50               (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_G)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['75', '85'])).
% 0.22/0.50  thf('87', plain,
% 0.22/0.50      ((((v2_struct_0 @ sk_B)
% 0.22/0.50         | (v2_struct_0 @ sk_D)
% 0.22/0.50         | (v2_struct_0 @ sk_C)
% 0.22/0.50         | (v2_struct_0 @ sk_A)))
% 0.22/0.50         <= (~ ((r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)) & 
% 0.22/0.50             ((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.22/0.50               (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_G)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['20', '86'])).
% 0.22/0.50  thf('88', plain, (~ (v2_struct_0 @ sk_D)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('89', plain,
% 0.22/0.50      ((((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_B)))
% 0.22/0.50         <= (~ ((r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)) & 
% 0.22/0.50             ((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.22/0.50               (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_G)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['87', '88'])).
% 0.22/0.50  thf('90', plain, (~ (v2_struct_0 @ sk_A)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('91', plain,
% 0.22/0.50      ((((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_C)))
% 0.22/0.50         <= (~ ((r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)) & 
% 0.22/0.50             ((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.22/0.50               (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_G)))),
% 0.22/0.50      inference('clc', [status(thm)], ['89', '90'])).
% 0.22/0.50  thf('92', plain, (~ (v2_struct_0 @ sk_B)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('93', plain,
% 0.22/0.50      (((v2_struct_0 @ sk_C))
% 0.22/0.50         <= (~ ((r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)) & 
% 0.22/0.50             ((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.22/0.50               (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_G)))),
% 0.22/0.50      inference('clc', [status(thm)], ['91', '92'])).
% 0.22/0.50  thf('94', plain, (~ (v2_struct_0 @ sk_C)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('95', plain,
% 0.22/0.50      (((r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)) | 
% 0.22/0.50       ~
% 0.22/0.50       ((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.22/0.50         (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_G))),
% 0.22/0.50      inference('sup-', [status(thm)], ['93', '94'])).
% 0.22/0.50  thf('96', plain,
% 0.22/0.50      (((r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)) | 
% 0.22/0.50       ((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.22/0.50         (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_G))),
% 0.22/0.50      inference('split', [status(esa)], ['33'])).
% 0.22/0.50  thf('97', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('98', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C))),
% 0.22/0.50      inference('demod', [status(thm)], ['2', '3'])).
% 0.22/0.50  thf('99', plain,
% 0.22/0.50      (((r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F))
% 0.22/0.50         <= (((r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)))),
% 0.22/0.50      inference('split', [status(esa)], ['33'])).
% 0.22/0.50  thf('100', plain,
% 0.22/0.50      ((m1_subset_1 @ sk_E @ 
% 0.22/0.50        (k1_zfmisc_1 @ 
% 0.22/0.50         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf(t81_tmap_1, axiom,
% 0.22/0.50    (![A:$i]:
% 0.22/0.50     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.22/0.50       ( ![B:$i]:
% 0.22/0.50         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.22/0.50             ( l1_pre_topc @ B ) ) =>
% 0.22/0.50           ( ![C:$i]:
% 0.22/0.50             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.22/0.50               ( ![D:$i]:
% 0.22/0.50                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.22/0.50                   ( ![E:$i]:
% 0.22/0.50                     ( ( ( v1_funct_1 @ E ) & 
% 0.22/0.50                         ( v1_funct_2 @
% 0.22/0.50                           E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 0.22/0.50                         ( m1_subset_1 @
% 0.22/0.50                           E @ 
% 0.22/0.50                           ( k1_zfmisc_1 @
% 0.22/0.50                             ( k2_zfmisc_1 @
% 0.22/0.50                               ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.22/0.50                       ( ![F:$i]:
% 0.22/0.50                         ( ( m1_subset_1 @ F @ ( u1_struct_0 @ C ) ) =>
% 0.22/0.50                           ( ![G:$i]:
% 0.22/0.50                             ( ( m1_subset_1 @ G @ ( u1_struct_0 @ D ) ) =>
% 0.22/0.50                               ( ( ( ( F ) = ( G ) ) & 
% 0.22/0.50                                   ( m1_pre_topc @ D @ C ) & 
% 0.22/0.50                                   ( r1_tmap_1 @ C @ B @ E @ F ) ) =>
% 0.22/0.50                                 ( r1_tmap_1 @
% 0.22/0.50                                   D @ B @ ( k3_tmap_1 @ A @ B @ C @ D @ E ) @ 
% 0.22/0.50                                   G ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.22/0.50  thf('101', plain,
% 0.22/0.50      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 0.22/0.50         ((v2_struct_0 @ X24)
% 0.22/0.50          | ~ (v2_pre_topc @ X24)
% 0.22/0.50          | ~ (l1_pre_topc @ X24)
% 0.22/0.50          | (v2_struct_0 @ X25)
% 0.22/0.50          | ~ (m1_pre_topc @ X25 @ X26)
% 0.22/0.50          | ~ (m1_subset_1 @ X27 @ (u1_struct_0 @ X28))
% 0.22/0.50          | ~ (m1_pre_topc @ X25 @ X28)
% 0.22/0.50          | ~ (r1_tmap_1 @ X28 @ X24 @ X29 @ X27)
% 0.22/0.50          | ((X27) != (X30))
% 0.22/0.50          | (r1_tmap_1 @ X25 @ X24 @ 
% 0.22/0.50             (k3_tmap_1 @ X26 @ X24 @ X28 @ X25 @ X29) @ X30)
% 0.22/0.50          | ~ (m1_subset_1 @ X30 @ (u1_struct_0 @ X25))
% 0.22/0.50          | ~ (m1_subset_1 @ X29 @ 
% 0.22/0.50               (k1_zfmisc_1 @ 
% 0.22/0.50                (k2_zfmisc_1 @ (u1_struct_0 @ X28) @ (u1_struct_0 @ X24))))
% 0.22/0.50          | ~ (v1_funct_2 @ X29 @ (u1_struct_0 @ X28) @ (u1_struct_0 @ X24))
% 0.22/0.50          | ~ (v1_funct_1 @ X29)
% 0.22/0.50          | ~ (m1_pre_topc @ X28 @ X26)
% 0.22/0.50          | (v2_struct_0 @ X28)
% 0.22/0.50          | ~ (l1_pre_topc @ X26)
% 0.22/0.50          | ~ (v2_pre_topc @ X26)
% 0.22/0.50          | (v2_struct_0 @ X26))),
% 0.22/0.50      inference('cnf', [status(esa)], [t81_tmap_1])).
% 0.22/0.50  thf('102', plain,
% 0.22/0.50      (![X24 : $i, X25 : $i, X26 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 0.22/0.50         ((v2_struct_0 @ X26)
% 0.22/0.50          | ~ (v2_pre_topc @ X26)
% 0.22/0.50          | ~ (l1_pre_topc @ X26)
% 0.22/0.50          | (v2_struct_0 @ X28)
% 0.22/0.50          | ~ (m1_pre_topc @ X28 @ X26)
% 0.22/0.50          | ~ (v1_funct_1 @ X29)
% 0.22/0.50          | ~ (v1_funct_2 @ X29 @ (u1_struct_0 @ X28) @ (u1_struct_0 @ X24))
% 0.22/0.50          | ~ (m1_subset_1 @ X29 @ 
% 0.22/0.50               (k1_zfmisc_1 @ 
% 0.22/0.50                (k2_zfmisc_1 @ (u1_struct_0 @ X28) @ (u1_struct_0 @ X24))))
% 0.22/0.50          | ~ (m1_subset_1 @ X30 @ (u1_struct_0 @ X25))
% 0.22/0.50          | (r1_tmap_1 @ X25 @ X24 @ 
% 0.22/0.50             (k3_tmap_1 @ X26 @ X24 @ X28 @ X25 @ X29) @ X30)
% 0.22/0.50          | ~ (r1_tmap_1 @ X28 @ X24 @ X29 @ X30)
% 0.22/0.50          | ~ (m1_pre_topc @ X25 @ X28)
% 0.22/0.50          | ~ (m1_subset_1 @ X30 @ (u1_struct_0 @ X28))
% 0.22/0.50          | ~ (m1_pre_topc @ X25 @ X26)
% 0.22/0.50          | (v2_struct_0 @ X25)
% 0.22/0.50          | ~ (l1_pre_topc @ X24)
% 0.22/0.50          | ~ (v2_pre_topc @ X24)
% 0.22/0.50          | (v2_struct_0 @ X24))),
% 0.22/0.50      inference('simplify', [status(thm)], ['101'])).
% 0.22/0.50  thf('103', plain,
% 0.22/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.50         ((v2_struct_0 @ sk_B)
% 0.22/0.50          | ~ (v2_pre_topc @ sk_B)
% 0.22/0.50          | ~ (l1_pre_topc @ sk_B)
% 0.22/0.50          | (v2_struct_0 @ X0)
% 0.22/0.50          | ~ (m1_pre_topc @ X0 @ X1)
% 0.22/0.50          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ sk_D))
% 0.22/0.50          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.22/0.50          | ~ (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X2)
% 0.22/0.50          | (r1_tmap_1 @ X0 @ sk_B @ 
% 0.22/0.50             (k3_tmap_1 @ X1 @ sk_B @ sk_D @ X0 @ sk_E) @ X2)
% 0.22/0.50          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.22/0.50          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.22/0.50          | ~ (v1_funct_1 @ sk_E)
% 0.22/0.50          | ~ (m1_pre_topc @ sk_D @ X1)
% 0.22/0.50          | (v2_struct_0 @ sk_D)
% 0.22/0.50          | ~ (l1_pre_topc @ X1)
% 0.22/0.50          | ~ (v2_pre_topc @ X1)
% 0.22/0.50          | (v2_struct_0 @ X1))),
% 0.22/0.50      inference('sup-', [status(thm)], ['100', '102'])).
% 0.22/0.50  thf('104', plain, ((v2_pre_topc @ sk_B)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('105', plain, ((l1_pre_topc @ sk_B)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('106', plain,
% 0.22/0.50      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('107', plain, ((v1_funct_1 @ sk_E)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('108', plain,
% 0.22/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.50         ((v2_struct_0 @ sk_B)
% 0.22/0.50          | (v2_struct_0 @ X0)
% 0.22/0.50          | ~ (m1_pre_topc @ X0 @ X1)
% 0.22/0.50          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ sk_D))
% 0.22/0.50          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.22/0.50          | ~ (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X2)
% 0.22/0.50          | (r1_tmap_1 @ X0 @ sk_B @ 
% 0.22/0.50             (k3_tmap_1 @ X1 @ sk_B @ sk_D @ X0 @ sk_E) @ X2)
% 0.22/0.50          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.22/0.50          | ~ (m1_pre_topc @ sk_D @ X1)
% 0.22/0.50          | (v2_struct_0 @ sk_D)
% 0.22/0.50          | ~ (l1_pre_topc @ X1)
% 0.22/0.50          | ~ (v2_pre_topc @ X1)
% 0.22/0.50          | (v2_struct_0 @ X1))),
% 0.22/0.50      inference('demod', [status(thm)], ['103', '104', '105', '106', '107'])).
% 0.22/0.50  thf('109', plain,
% 0.22/0.50      ((![X0 : $i, X1 : $i]:
% 0.22/0.50          ((v2_struct_0 @ X0)
% 0.22/0.50           | ~ (v2_pre_topc @ X0)
% 0.22/0.50           | ~ (l1_pre_topc @ X0)
% 0.22/0.50           | (v2_struct_0 @ sk_D)
% 0.22/0.50           | ~ (m1_pre_topc @ sk_D @ X0)
% 0.22/0.50           | ~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ X1))
% 0.22/0.50           | (r1_tmap_1 @ X1 @ sk_B @ 
% 0.22/0.50              (k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E) @ sk_F)
% 0.22/0.50           | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.22/0.50           | ~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_D))
% 0.22/0.50           | ~ (m1_pre_topc @ X1 @ X0)
% 0.22/0.50           | (v2_struct_0 @ X1)
% 0.22/0.50           | (v2_struct_0 @ sk_B)))
% 0.22/0.50         <= (((r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['99', '108'])).
% 0.22/0.50  thf('110', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_D))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('111', plain,
% 0.22/0.50      ((![X0 : $i, X1 : $i]:
% 0.22/0.50          ((v2_struct_0 @ X0)
% 0.22/0.50           | ~ (v2_pre_topc @ X0)
% 0.22/0.50           | ~ (l1_pre_topc @ X0)
% 0.22/0.50           | (v2_struct_0 @ sk_D)
% 0.22/0.50           | ~ (m1_pre_topc @ sk_D @ X0)
% 0.22/0.50           | ~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ X1))
% 0.22/0.50           | (r1_tmap_1 @ X1 @ sk_B @ 
% 0.22/0.50              (k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E) @ sk_F)
% 0.22/0.50           | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.22/0.50           | ~ (m1_pre_topc @ X1 @ X0)
% 0.22/0.50           | (v2_struct_0 @ X1)
% 0.22/0.50           | (v2_struct_0 @ sk_B)))
% 0.22/0.50         <= (((r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)))),
% 0.22/0.50      inference('demod', [status(thm)], ['109', '110'])).
% 0.22/0.50  thf('112', plain,
% 0.22/0.50      ((![X0 : $i]:
% 0.22/0.50          ((v2_struct_0 @ sk_B)
% 0.22/0.50           | (v2_struct_0 @ sk_C)
% 0.22/0.50           | ~ (m1_pre_topc @ sk_C @ X0)
% 0.22/0.50           | ~ (m1_pre_topc @ sk_C @ sk_D)
% 0.22/0.50           | (r1_tmap_1 @ sk_C @ sk_B @ 
% 0.22/0.50              (k3_tmap_1 @ X0 @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_F)
% 0.22/0.50           | ~ (m1_pre_topc @ sk_D @ X0)
% 0.22/0.50           | (v2_struct_0 @ sk_D)
% 0.22/0.50           | ~ (l1_pre_topc @ X0)
% 0.22/0.50           | ~ (v2_pre_topc @ X0)
% 0.22/0.50           | (v2_struct_0 @ X0)))
% 0.22/0.50         <= (((r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['98', '111'])).
% 0.22/0.50  thf('113', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('114', plain,
% 0.22/0.50      ((![X0 : $i]:
% 0.22/0.50          ((v2_struct_0 @ sk_B)
% 0.22/0.50           | (v2_struct_0 @ sk_C)
% 0.22/0.50           | ~ (m1_pre_topc @ sk_C @ X0)
% 0.22/0.50           | (r1_tmap_1 @ sk_C @ sk_B @ 
% 0.22/0.50              (k3_tmap_1 @ X0 @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_F)
% 0.22/0.50           | ~ (m1_pre_topc @ sk_D @ X0)
% 0.22/0.50           | (v2_struct_0 @ sk_D)
% 0.22/0.50           | ~ (l1_pre_topc @ X0)
% 0.22/0.50           | ~ (v2_pre_topc @ X0)
% 0.22/0.50           | (v2_struct_0 @ X0)))
% 0.22/0.50         <= (((r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)))),
% 0.22/0.50      inference('demod', [status(thm)], ['112', '113'])).
% 0.22/0.50  thf('115', plain,
% 0.22/0.50      ((((v2_struct_0 @ sk_A)
% 0.22/0.50         | ~ (v2_pre_topc @ sk_A)
% 0.22/0.50         | ~ (l1_pre_topc @ sk_A)
% 0.22/0.50         | (v2_struct_0 @ sk_D)
% 0.22/0.50         | ~ (m1_pre_topc @ sk_D @ sk_A)
% 0.22/0.50         | (r1_tmap_1 @ sk_C @ sk_B @ 
% 0.22/0.50            (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_F)
% 0.22/0.50         | (v2_struct_0 @ sk_C)
% 0.22/0.50         | (v2_struct_0 @ sk_B)))
% 0.22/0.50         <= (((r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['97', '114'])).
% 0.22/0.50  thf('116', plain, ((v2_pre_topc @ sk_A)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('117', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('118', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('119', plain,
% 0.22/0.50      ((((v2_struct_0 @ sk_A)
% 0.22/0.50         | (v2_struct_0 @ sk_D)
% 0.22/0.50         | (r1_tmap_1 @ sk_C @ sk_B @ 
% 0.22/0.50            (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_F)
% 0.22/0.50         | (v2_struct_0 @ sk_C)
% 0.22/0.50         | (v2_struct_0 @ sk_B)))
% 0.22/0.50         <= (((r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)))),
% 0.22/0.50      inference('demod', [status(thm)], ['115', '116', '117', '118'])).
% 0.22/0.50  thf('120', plain,
% 0.22/0.50      ((~ (r1_tmap_1 @ sk_C @ sk_B @ 
% 0.22/0.50           (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_G))
% 0.22/0.50         <= (~
% 0.22/0.50             ((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.22/0.50               (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_G)))),
% 0.22/0.50      inference('split', [status(esa)], ['0'])).
% 0.22/0.50  thf('121', plain, (((sk_F) = (sk_G))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('122', plain,
% 0.22/0.50      ((~ (r1_tmap_1 @ sk_C @ sk_B @ 
% 0.22/0.50           (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_F))
% 0.22/0.50         <= (~
% 0.22/0.50             ((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.22/0.50               (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_G)))),
% 0.22/0.50      inference('demod', [status(thm)], ['120', '121'])).
% 0.22/0.50  thf('123', plain,
% 0.22/0.50      ((((v2_struct_0 @ sk_B)
% 0.22/0.50         | (v2_struct_0 @ sk_C)
% 0.22/0.50         | (v2_struct_0 @ sk_D)
% 0.22/0.50         | (v2_struct_0 @ sk_A)))
% 0.22/0.50         <= (~
% 0.22/0.50             ((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.22/0.50               (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_G)) & 
% 0.22/0.50             ((r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['119', '122'])).
% 0.22/0.50  thf('124', plain, (~ (v2_struct_0 @ sk_D)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('125', plain,
% 0.22/0.50      ((((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_B)))
% 0.22/0.50         <= (~
% 0.22/0.50             ((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.22/0.50               (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_G)) & 
% 0.22/0.50             ((r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['123', '124'])).
% 0.22/0.50  thf('126', plain, (~ (v2_struct_0 @ sk_A)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('127', plain,
% 0.22/0.50      ((((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_C)))
% 0.22/0.50         <= (~
% 0.22/0.50             ((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.22/0.50               (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_G)) & 
% 0.22/0.50             ((r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)))),
% 0.22/0.50      inference('clc', [status(thm)], ['125', '126'])).
% 0.22/0.50  thf('128', plain, (~ (v2_struct_0 @ sk_B)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('129', plain,
% 0.22/0.50      (((v2_struct_0 @ sk_C))
% 0.22/0.50         <= (~
% 0.22/0.50             ((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.22/0.50               (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_G)) & 
% 0.22/0.50             ((r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)))),
% 0.22/0.50      inference('clc', [status(thm)], ['127', '128'])).
% 0.22/0.50  thf('130', plain, (~ (v2_struct_0 @ sk_C)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('131', plain,
% 0.22/0.50      (~ ((r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)) | 
% 0.22/0.50       ((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.22/0.50         (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_G))),
% 0.22/0.50      inference('sup-', [status(thm)], ['129', '130'])).
% 0.22/0.50  thf('132', plain, ($false),
% 0.22/0.50      inference('sat_resolution*', [status(thm)], ['1', '95', '96', '131'])).
% 0.22/0.50  
% 0.22/0.50  % SZS output end Refutation
% 0.22/0.50  
% 0.22/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
