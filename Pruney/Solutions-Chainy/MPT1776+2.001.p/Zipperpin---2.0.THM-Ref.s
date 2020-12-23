%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.kMOuFoDDlA

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:10:23 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  162 ( 324 expanded)
%              Number of leaves         :   37 ( 107 expanded)
%              Depth                    :   17
%              Number of atoms          : 2131 (12090 expanded)
%              Number of equality atoms :   13 ( 151 expanded)
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

thf(t87_tmap_1,conjecture,(
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
                                    <=> ( r1_tmap_1 @ C @ A @ ( k3_tmap_1 @ B @ A @ D @ C @ E ) @ G ) ) ) ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t87_tmap_1])).

thf('0',plain,
    ( ~ ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_G )
    | ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F )
    | ~ ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_G ) ),
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
    m1_pre_topc @ sk_C @ sk_B ),
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
    ( ~ ( v2_pre_topc @ sk_B )
    | ~ ( l1_pre_topc @ sk_B )
    | ( v2_pre_topc @ sk_C ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    v2_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['9','10','11'])).

thf('13',plain,(
    m1_pre_topc @ sk_C @ sk_B ),
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
    ( ~ ( l1_pre_topc @ sk_B )
    | ( l1_pre_topc @ sk_C ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    l1_pre_topc @ sk_B ),
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
    m1_pre_topc @ sk_C @ sk_B ),
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
    ( ~ ( l1_pre_topc @ sk_B )
    | ( m1_subset_1 @ ( u1_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,
    ( ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_G )
    | ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_G )
   <= ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_G ) ),
    inference(split,[status(esa)],['29'])).

thf('31',plain,(
    sk_F = sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_F )
   <= ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_G ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t85_tmap_1,axiom,(
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
                     => ( ( m1_pre_topc @ C @ D )
                       => ! [F: $i] :
                            ( ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) )
                           => ! [G: $i] :
                                ( ( m1_subset_1 @ G @ ( u1_struct_0 @ D ) )
                               => ! [H: $i] :
                                    ( ( m1_subset_1 @ H @ ( u1_struct_0 @ C ) )
                                   => ( ( ( v3_pre_topc @ F @ B )
                                        & ( r2_hidden @ G @ F )
                                        & ( r1_tarski @ F @ ( u1_struct_0 @ C ) )
                                        & ( G = H ) )
                                     => ( ( r1_tmap_1 @ D @ A @ E @ G )
                                      <=> ( r1_tmap_1 @ C @ A @ ( k3_tmap_1 @ B @ A @ D @ C @ E ) @ H ) ) ) ) ) ) ) ) ) ) ) ) )).

thf('34',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i,X35: $i,X36: $i,X37: $i,X38: $i] :
      ( ( v2_struct_0 @ X31 )
      | ~ ( v2_pre_topc @ X31 )
      | ~ ( l1_pre_topc @ X31 )
      | ( v2_struct_0 @ X32 )
      | ~ ( m1_pre_topc @ X32 @ X31 )
      | ~ ( m1_pre_topc @ X33 @ X32 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X31 ) ) )
      | ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ X33 ) )
      | ~ ( r1_tmap_1 @ X33 @ X36 @ ( k3_tmap_1 @ X31 @ X36 @ X32 @ X33 @ X37 ) @ X35 )
      | ( r1_tmap_1 @ X32 @ X36 @ X37 @ X38 )
      | ( X38 != X35 )
      | ~ ( r1_tarski @ X34 @ ( u1_struct_0 @ X33 ) )
      | ~ ( r2_hidden @ X38 @ X34 )
      | ~ ( v3_pre_topc @ X34 @ X31 )
      | ~ ( m1_subset_1 @ X38 @ ( u1_struct_0 @ X32 ) )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X32 ) @ ( u1_struct_0 @ X36 ) ) ) )
      | ~ ( v1_funct_2 @ X37 @ ( u1_struct_0 @ X32 ) @ ( u1_struct_0 @ X36 ) )
      | ~ ( v1_funct_1 @ X37 )
      | ~ ( m1_pre_topc @ X33 @ X31 )
      | ( v2_struct_0 @ X33 )
      | ~ ( l1_pre_topc @ X36 )
      | ~ ( v2_pre_topc @ X36 )
      | ( v2_struct_0 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t85_tmap_1])).

thf('35',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i,X35: $i,X36: $i,X37: $i] :
      ( ( v2_struct_0 @ X36 )
      | ~ ( v2_pre_topc @ X36 )
      | ~ ( l1_pre_topc @ X36 )
      | ( v2_struct_0 @ X33 )
      | ~ ( m1_pre_topc @ X33 @ X31 )
      | ~ ( v1_funct_1 @ X37 )
      | ~ ( v1_funct_2 @ X37 @ ( u1_struct_0 @ X32 ) @ ( u1_struct_0 @ X36 ) )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X32 ) @ ( u1_struct_0 @ X36 ) ) ) )
      | ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ X32 ) )
      | ~ ( v3_pre_topc @ X34 @ X31 )
      | ~ ( r2_hidden @ X35 @ X34 )
      | ~ ( r1_tarski @ X34 @ ( u1_struct_0 @ X33 ) )
      | ( r1_tmap_1 @ X32 @ X36 @ X37 @ X35 )
      | ~ ( r1_tmap_1 @ X33 @ X36 @ ( k3_tmap_1 @ X31 @ X36 @ X32 @ X33 @ X37 ) @ X35 )
      | ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ X33 ) )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X31 ) ) )
      | ~ ( m1_pre_topc @ X33 @ X32 )
      | ~ ( m1_pre_topc @ X32 @ X31 )
      | ( v2_struct_0 @ X32 )
      | ~ ( l1_pre_topc @ X31 )
      | ~ ( v2_pre_topc @ X31 )
      | ( v2_struct_0 @ X31 ) ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ sk_D )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ~ ( m1_pre_topc @ X1 @ sk_D )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X1 ) )
      | ~ ( r1_tmap_1 @ X1 @ sk_A @ ( k3_tmap_1 @ X0 @ sk_A @ sk_D @ X1 @ sk_E ) @ X3 )
      | ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ X3 )
      | ~ ( r1_tarski @ X2 @ ( u1_struct_0 @ X1 ) )
      | ~ ( r2_hidden @ X3 @ X2 )
      | ~ ( v3_pre_topc @ X2 @ X0 )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ sk_D ) )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ( v2_struct_0 @ X1 )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['33','35'])).

thf('37',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ sk_D )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ~ ( m1_pre_topc @ X1 @ sk_D )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X1 ) )
      | ~ ( r1_tmap_1 @ X1 @ sk_A @ ( k3_tmap_1 @ X0 @ sk_A @ sk_D @ X1 @ sk_E ) @ X3 )
      | ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ X3 )
      | ~ ( r1_tarski @ X2 @ ( u1_struct_0 @ X1 ) )
      | ~ ( r2_hidden @ X3 @ X2 )
      | ~ ( v3_pre_topc @ X2 @ X0 )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ sk_D ) )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ( v2_struct_0 @ X1 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['36','37','38','39','40'])).

thf('42',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ sk_C )
        | ~ ( m1_pre_topc @ sk_C @ sk_B )
        | ~ ( m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_D ) )
        | ~ ( v3_pre_topc @ X0 @ sk_B )
        | ~ ( r2_hidden @ sk_F @ X0 )
        | ~ ( r1_tarski @ X0 @ ( u1_struct_0 @ sk_C ) )
        | ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F )
        | ~ ( m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_C ) )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
        | ~ ( m1_pre_topc @ sk_C @ sk_D )
        | ~ ( m1_pre_topc @ sk_D @ sk_B )
        | ( v2_struct_0 @ sk_D )
        | ~ ( l1_pre_topc @ sk_B )
        | ~ ( v2_pre_topc @ sk_B )
        | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_G ) ),
    inference('sup-',[status(thm)],['32','41'])).

thf('43',plain,(
    m1_pre_topc @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('46',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    m1_pre_topc @ sk_D @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ sk_C )
        | ~ ( v3_pre_topc @ X0 @ sk_B )
        | ~ ( r2_hidden @ sk_F @ X0 )
        | ~ ( r1_tarski @ X0 @ ( u1_struct_0 @ sk_C ) )
        | ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
        | ( v2_struct_0 @ sk_D )
        | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_G ) ),
    inference(demod,[status(thm)],['42','43','44','45','46','47','48','49'])).

thf('51',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F )
      | ~ ( r1_tarski @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_C ) )
      | ~ ( r2_hidden @ sk_F @ ( u1_struct_0 @ sk_C ) )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_C ) @ sk_B )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_G ) ),
    inference('sup-',[status(thm)],['28','50'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('53',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['52'])).

thf('54',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['26','27'])).

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

thf('55',plain,(
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

thf('56',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( v2_pre_topc @ X17 )
      | ~ ( l1_pre_topc @ X17 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X16 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ( v3_pre_topc @ ( u1_struct_0 @ X16 ) @ X17 )
      | ~ ( v1_tsep_1 @ X16 @ X17 )
      | ~ ( m1_pre_topc @ X16 @ X17 ) ) ),
    inference(simplify,[status(thm)],['55'])).

thf('57',plain,
    ( ~ ( m1_pre_topc @ sk_C @ sk_B )
    | ~ ( v1_tsep_1 @ sk_C @ sk_B )
    | ( v3_pre_topc @ ( u1_struct_0 @ sk_C ) @ sk_B )
    | ~ ( l1_pre_topc @ sk_B )
    | ~ ( v2_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['54','56'])).

thf('58',plain,(
    m1_pre_topc @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    v1_tsep_1 @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    v3_pre_topc @ ( u1_struct_0 @ sk_C ) @ sk_B ),
    inference(demod,[status(thm)],['57','58','59','60','61'])).

thf('63',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F )
      | ~ ( r2_hidden @ sk_F @ ( u1_struct_0 @ sk_C ) )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_G ) ),
    inference(demod,[status(thm)],['51','53','62'])).

thf('64',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_G ) ),
    inference('sup-',[status(thm)],['23','63'])).

thf('65',plain,
    ( ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F )
   <= ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F ) ),
    inference(split,[status(esa)],['0'])).

thf('66',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) ) )
   <= ( ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F )
      & ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_G ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(dt_k1_connsp_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) )
     => ( m1_subset_1 @ ( k1_connsp_2 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('68',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( l1_pre_topc @ X12 )
      | ~ ( v2_pre_topc @ X12 )
      | ( v2_struct_0 @ X12 )
      | ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ X12 ) )
      | ( m1_subset_1 @ ( k1_connsp_2 @ X12 @ X13 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_connsp_2])).

thf('69',plain,
    ( ( m1_subset_1 @ ( k1_connsp_2 @ sk_C @ sk_F ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C ) ) )
    | ( v2_struct_0 @ sk_C )
    | ~ ( v2_pre_topc @ sk_C )
    | ~ ( l1_pre_topc @ sk_C ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    v2_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['9','10','11'])).

thf('71',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['15','16'])).

thf('72',plain,
    ( ( m1_subset_1 @ ( k1_connsp_2 @ sk_C @ sk_F ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C ) ) )
    | ( v2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['69','70','71'])).

thf('73',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    m1_subset_1 @ ( k1_connsp_2 @ sk_C @ sk_F ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C ) ) ),
    inference(clc,[status(thm)],['72','73'])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('75',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X5 @ X6 )
      | ~ ( v1_xboole_0 @ X7 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('76',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) )
      | ~ ( r2_hidden @ X0 @ ( k1_connsp_2 @ sk_C @ sk_F ) ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ sk_C )
        | ( v2_struct_0 @ sk_D )
        | ( v2_struct_0 @ sk_B )
        | ~ ( r2_hidden @ X0 @ ( k1_connsp_2 @ sk_C @ sk_F ) ) )
   <= ( ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F )
      & ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_G ) ) ),
    inference('sup-',[status(thm)],['66','76'])).

thf('78',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F )
      & ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_G ) ) ),
    inference('sup-',[status(thm)],['20','77'])).

thf('79',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,
    ( ( ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F )
      & ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_G ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D ) )
   <= ( ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F )
      & ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_G ) ) ),
    inference(clc,[status(thm)],['80','81'])).

thf('83',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,
    ( ( v2_struct_0 @ sk_D )
   <= ( ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F )
      & ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_G ) ) ),
    inference(clc,[status(thm)],['82','83'])).

thf('85',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,
    ( ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F )
    | ~ ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_G ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,
    ( ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F )
    | ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_G ) ),
    inference(split,[status(esa)],['29'])).

thf('88',plain,(
    m1_pre_topc @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('90',plain,
    ( ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F )
   <= ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F ) ),
    inference(split,[status(esa)],['29'])).

thf('91',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) ) ) ),
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

thf('92',plain,(
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

thf('93',plain,(
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
    inference(simplify,[status(thm)],['92'])).

thf('94',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X1 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ sk_D ) )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ X2 )
      | ( r1_tmap_1 @ X0 @ sk_A @ ( k3_tmap_1 @ X1 @ sk_A @ sk_D @ X0 @ sk_E ) @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( m1_pre_topc @ sk_D @ X1 )
      | ( v2_struct_0 @ sk_D )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['91','93'])).

thf('95',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X1 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ sk_D ) )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ X2 )
      | ( r1_tmap_1 @ X0 @ sk_A @ ( k3_tmap_1 @ X1 @ sk_A @ sk_D @ X0 @ sk_E ) @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ sk_D @ X1 )
      | ( v2_struct_0 @ sk_D )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(demod,[status(thm)],['94','95','96','97','98'])).

thf('100',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( v2_struct_0 @ X0 )
        | ~ ( v2_pre_topc @ X0 )
        | ~ ( l1_pre_topc @ X0 )
        | ( v2_struct_0 @ sk_D )
        | ~ ( m1_pre_topc @ sk_D @ X0 )
        | ~ ( m1_subset_1 @ sk_F @ ( u1_struct_0 @ X1 ) )
        | ( r1_tmap_1 @ X1 @ sk_A @ ( k3_tmap_1 @ X0 @ sk_A @ sk_D @ X1 @ sk_E ) @ sk_F )
        | ~ ( m1_pre_topc @ X1 @ sk_D )
        | ~ ( m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_D ) )
        | ~ ( m1_pre_topc @ X1 @ X0 )
        | ( v2_struct_0 @ X1 )
        | ( v2_struct_0 @ sk_A ) )
   <= ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F ) ),
    inference('sup-',[status(thm)],['90','99'])).

thf('101',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( v2_struct_0 @ X0 )
        | ~ ( v2_pre_topc @ X0 )
        | ~ ( l1_pre_topc @ X0 )
        | ( v2_struct_0 @ sk_D )
        | ~ ( m1_pre_topc @ sk_D @ X0 )
        | ~ ( m1_subset_1 @ sk_F @ ( u1_struct_0 @ X1 ) )
        | ( r1_tmap_1 @ X1 @ sk_A @ ( k3_tmap_1 @ X0 @ sk_A @ sk_D @ X1 @ sk_E ) @ sk_F )
        | ~ ( m1_pre_topc @ X1 @ sk_D )
        | ~ ( m1_pre_topc @ X1 @ X0 )
        | ( v2_struct_0 @ X1 )
        | ( v2_struct_0 @ sk_A ) )
   <= ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F ) ),
    inference(demod,[status(thm)],['100','101'])).

thf('103',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ sk_C )
        | ~ ( m1_pre_topc @ sk_C @ X0 )
        | ~ ( m1_pre_topc @ sk_C @ sk_D )
        | ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ X0 @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_F )
        | ~ ( m1_pre_topc @ sk_D @ X0 )
        | ( v2_struct_0 @ sk_D )
        | ~ ( l1_pre_topc @ X0 )
        | ~ ( v2_pre_topc @ X0 )
        | ( v2_struct_0 @ X0 ) )
   <= ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F ) ),
    inference('sup-',[status(thm)],['89','102'])).

thf('104',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ sk_C )
        | ~ ( m1_pre_topc @ sk_C @ X0 )
        | ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ X0 @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_F )
        | ~ ( m1_pre_topc @ sk_D @ X0 )
        | ( v2_struct_0 @ sk_D )
        | ~ ( l1_pre_topc @ X0 )
        | ~ ( v2_pre_topc @ X0 )
        | ( v2_struct_0 @ X0 ) )
   <= ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F ) ),
    inference(demod,[status(thm)],['103','104'])).

thf('106',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ~ ( m1_pre_topc @ sk_D @ sk_B )
      | ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_F )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F ) ),
    inference('sup-',[status(thm)],['88','105'])).

thf('107',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,(
    m1_pre_topc @ sk_D @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_F )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F ) ),
    inference(demod,[status(thm)],['106','107','108','109'])).

thf('111',plain,
    ( ~ ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_G )
   <= ~ ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_G ) ),
    inference(split,[status(esa)],['0'])).

thf('112',plain,(
    sk_F = sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,
    ( ~ ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_F )
   <= ~ ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_G ) ),
    inference(demod,[status(thm)],['111','112'])).

thf('114',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ~ ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_G )
      & ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F ) ) ),
    inference('sup-',[status(thm)],['110','113'])).

thf('115',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_C ) )
   <= ( ~ ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_G )
      & ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F ) ) ),
    inference('sup-',[status(thm)],['114','115'])).

thf('117',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,
    ( ( ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_D ) )
   <= ( ~ ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_G )
      & ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F ) ) ),
    inference(clc,[status(thm)],['116','117'])).

thf('119',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,
    ( ( v2_struct_0 @ sk_D )
   <= ( ~ ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_G )
      & ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F ) ) ),
    inference(clc,[status(thm)],['118','119'])).

thf('121',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,
    ( ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F )
    | ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_G ) ),
    inference('sup-',[status(thm)],['120','121'])).

thf('123',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','86','87','122'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.kMOuFoDDlA
% 0.13/0.35  % Computer   : n020.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 12:53:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.53  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.53  % Solved by: fo/fo7.sh
% 0.20/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.53  % done 99 iterations in 0.059s
% 0.20/0.53  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.53  % SZS output start Refutation
% 0.20/0.53  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.53  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.20/0.53  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.53  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.20/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.53  thf(k1_connsp_2_type, type, k1_connsp_2: $i > $i > $i).
% 0.20/0.53  thf(sk_D_type, type, sk_D: $i).
% 0.20/0.53  thf(sk_G_type, type, sk_G: $i).
% 0.20/0.53  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.53  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.20/0.53  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.53  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.53  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.53  thf(sk_E_type, type, sk_E: $i).
% 0.20/0.53  thf(r1_tmap_1_type, type, r1_tmap_1: $i > $i > $i > $i > $o).
% 0.20/0.53  thf(k3_tmap_1_type, type, k3_tmap_1: $i > $i > $i > $i > $i > $i).
% 0.20/0.53  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.53  thf(sk_F_type, type, sk_F: $i).
% 0.20/0.53  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.20/0.53  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.20/0.53  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.20/0.53  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.53  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.20/0.53  thf(v1_tsep_1_type, type, v1_tsep_1: $i > $i > $o).
% 0.20/0.53  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.53  thf(t87_tmap_1, conjecture,
% 0.20/0.53    (![A:$i]:
% 0.20/0.53     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.53       ( ![B:$i]:
% 0.20/0.53         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.20/0.53             ( l1_pre_topc @ B ) ) =>
% 0.20/0.53           ( ![C:$i]:
% 0.20/0.53             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ B ) ) =>
% 0.20/0.53               ( ![D:$i]:
% 0.20/0.53                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ B ) ) =>
% 0.20/0.53                   ( ![E:$i]:
% 0.20/0.53                     ( ( ( v1_funct_1 @ E ) & 
% 0.20/0.53                         ( v1_funct_2 @
% 0.20/0.53                           E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ A ) ) & 
% 0.20/0.53                         ( m1_subset_1 @
% 0.20/0.53                           E @ 
% 0.20/0.53                           ( k1_zfmisc_1 @
% 0.20/0.53                             ( k2_zfmisc_1 @
% 0.20/0.53                               ( u1_struct_0 @ D ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.20/0.53                       ( ( ( v1_tsep_1 @ C @ B ) & ( m1_pre_topc @ C @ B ) & 
% 0.20/0.53                           ( m1_pre_topc @ C @ D ) ) =>
% 0.20/0.53                         ( ![F:$i]:
% 0.20/0.53                           ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 0.20/0.53                             ( ![G:$i]:
% 0.20/0.53                               ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) ) =>
% 0.20/0.53                                 ( ( ( F ) = ( G ) ) =>
% 0.20/0.53                                   ( ( r1_tmap_1 @ D @ A @ E @ F ) <=>
% 0.20/0.53                                     ( r1_tmap_1 @
% 0.20/0.53                                       C @ A @ 
% 0.20/0.53                                       ( k3_tmap_1 @ B @ A @ D @ C @ E ) @ G ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.53    (~( ![A:$i]:
% 0.20/0.53        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.20/0.53            ( l1_pre_topc @ A ) ) =>
% 0.20/0.53          ( ![B:$i]:
% 0.20/0.53            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.20/0.53                ( l1_pre_topc @ B ) ) =>
% 0.20/0.53              ( ![C:$i]:
% 0.20/0.53                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ B ) ) =>
% 0.20/0.53                  ( ![D:$i]:
% 0.20/0.53                    ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ B ) ) =>
% 0.20/0.53                      ( ![E:$i]:
% 0.20/0.53                        ( ( ( v1_funct_1 @ E ) & 
% 0.20/0.53                            ( v1_funct_2 @
% 0.20/0.53                              E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ A ) ) & 
% 0.20/0.53                            ( m1_subset_1 @
% 0.20/0.53                              E @ 
% 0.20/0.53                              ( k1_zfmisc_1 @
% 0.20/0.53                                ( k2_zfmisc_1 @
% 0.20/0.53                                  ( u1_struct_0 @ D ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.20/0.53                          ( ( ( v1_tsep_1 @ C @ B ) & 
% 0.20/0.53                              ( m1_pre_topc @ C @ B ) & ( m1_pre_topc @ C @ D ) ) =>
% 0.20/0.53                            ( ![F:$i]:
% 0.20/0.53                              ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 0.20/0.53                                ( ![G:$i]:
% 0.20/0.53                                  ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) ) =>
% 0.20/0.53                                    ( ( ( F ) = ( G ) ) =>
% 0.20/0.53                                      ( ( r1_tmap_1 @ D @ A @ E @ F ) <=>
% 0.20/0.53                                        ( r1_tmap_1 @
% 0.20/0.53                                          C @ A @ 
% 0.20/0.53                                          ( k3_tmap_1 @ B @ A @ D @ C @ E ) @ G ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.20/0.53    inference('cnf.neg', [status(esa)], [t87_tmap_1])).
% 0.20/0.53  thf('0', plain,
% 0.20/0.53      ((~ (r1_tmap_1 @ sk_C @ sk_A @ 
% 0.20/0.53           (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_G)
% 0.20/0.53        | ~ (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('1', plain,
% 0.20/0.53      (~ ((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F)) | 
% 0.20/0.53       ~
% 0.20/0.53       ((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.20/0.53         (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_G))),
% 0.20/0.53      inference('split', [status(esa)], ['0'])).
% 0.20/0.53  thf('2', plain, ((m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_C))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('3', plain, (((sk_F) = (sk_G))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('4', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C))),
% 0.20/0.53      inference('demod', [status(thm)], ['2', '3'])).
% 0.20/0.53  thf(t30_connsp_2, axiom,
% 0.20/0.53    (![A:$i]:
% 0.20/0.53     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.53       ( ![B:$i]:
% 0.20/0.53         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.53           ( r2_hidden @ B @ ( k1_connsp_2 @ A @ B ) ) ) ) ))).
% 0.20/0.53  thf('5', plain,
% 0.20/0.53      (![X14 : $i, X15 : $i]:
% 0.20/0.53         (~ (m1_subset_1 @ X14 @ (u1_struct_0 @ X15))
% 0.20/0.53          | (r2_hidden @ X14 @ (k1_connsp_2 @ X15 @ X14))
% 0.20/0.53          | ~ (l1_pre_topc @ X15)
% 0.20/0.53          | ~ (v2_pre_topc @ X15)
% 0.20/0.53          | (v2_struct_0 @ X15))),
% 0.20/0.53      inference('cnf', [status(esa)], [t30_connsp_2])).
% 0.20/0.53  thf('6', plain,
% 0.20/0.53      (((v2_struct_0 @ sk_C)
% 0.20/0.53        | ~ (v2_pre_topc @ sk_C)
% 0.20/0.53        | ~ (l1_pre_topc @ sk_C)
% 0.20/0.53        | (r2_hidden @ sk_F @ (k1_connsp_2 @ sk_C @ sk_F)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['4', '5'])).
% 0.20/0.53  thf('7', plain, ((m1_pre_topc @ sk_C @ sk_B)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf(cc1_pre_topc, axiom,
% 0.20/0.53    (![A:$i]:
% 0.20/0.53     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.53       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( v2_pre_topc @ B ) ) ) ))).
% 0.20/0.53  thf('8', plain,
% 0.20/0.53      (![X8 : $i, X9 : $i]:
% 0.20/0.53         (~ (m1_pre_topc @ X8 @ X9)
% 0.20/0.53          | (v2_pre_topc @ X8)
% 0.20/0.53          | ~ (l1_pre_topc @ X9)
% 0.20/0.53          | ~ (v2_pre_topc @ X9))),
% 0.20/0.53      inference('cnf', [status(esa)], [cc1_pre_topc])).
% 0.20/0.53  thf('9', plain,
% 0.20/0.53      ((~ (v2_pre_topc @ sk_B) | ~ (l1_pre_topc @ sk_B) | (v2_pre_topc @ sk_C))),
% 0.20/0.53      inference('sup-', [status(thm)], ['7', '8'])).
% 0.20/0.53  thf('10', plain, ((v2_pre_topc @ sk_B)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('11', plain, ((l1_pre_topc @ sk_B)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('12', plain, ((v2_pre_topc @ sk_C)),
% 0.20/0.53      inference('demod', [status(thm)], ['9', '10', '11'])).
% 0.20/0.53  thf('13', plain, ((m1_pre_topc @ sk_C @ sk_B)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf(dt_m1_pre_topc, axiom,
% 0.20/0.53    (![A:$i]:
% 0.20/0.53     ( ( l1_pre_topc @ A ) =>
% 0.20/0.53       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.20/0.53  thf('14', plain,
% 0.20/0.53      (![X10 : $i, X11 : $i]:
% 0.20/0.53         (~ (m1_pre_topc @ X10 @ X11)
% 0.20/0.53          | (l1_pre_topc @ X10)
% 0.20/0.53          | ~ (l1_pre_topc @ X11))),
% 0.20/0.53      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.20/0.53  thf('15', plain, ((~ (l1_pre_topc @ sk_B) | (l1_pre_topc @ sk_C))),
% 0.20/0.53      inference('sup-', [status(thm)], ['13', '14'])).
% 0.20/0.53  thf('16', plain, ((l1_pre_topc @ sk_B)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('17', plain, ((l1_pre_topc @ sk_C)),
% 0.20/0.53      inference('demod', [status(thm)], ['15', '16'])).
% 0.20/0.53  thf('18', plain,
% 0.20/0.53      (((v2_struct_0 @ sk_C) | (r2_hidden @ sk_F @ (k1_connsp_2 @ sk_C @ sk_F)))),
% 0.20/0.53      inference('demod', [status(thm)], ['6', '12', '17'])).
% 0.20/0.53  thf('19', plain, (~ (v2_struct_0 @ sk_C)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('20', plain, ((r2_hidden @ sk_F @ (k1_connsp_2 @ sk_C @ sk_F))),
% 0.20/0.53      inference('clc', [status(thm)], ['18', '19'])).
% 0.20/0.53  thf('21', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C))),
% 0.20/0.53      inference('demod', [status(thm)], ['2', '3'])).
% 0.20/0.53  thf(t2_subset, axiom,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( m1_subset_1 @ A @ B ) =>
% 0.20/0.53       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.20/0.53  thf('22', plain,
% 0.20/0.53      (![X3 : $i, X4 : $i]:
% 0.20/0.53         ((r2_hidden @ X3 @ X4)
% 0.20/0.53          | (v1_xboole_0 @ X4)
% 0.20/0.53          | ~ (m1_subset_1 @ X3 @ X4))),
% 0.20/0.53      inference('cnf', [status(esa)], [t2_subset])).
% 0.20/0.53  thf('23', plain,
% 0.20/0.53      (((v1_xboole_0 @ (u1_struct_0 @ sk_C))
% 0.20/0.53        | (r2_hidden @ sk_F @ (u1_struct_0 @ sk_C)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['21', '22'])).
% 0.20/0.53  thf('24', plain, ((m1_pre_topc @ sk_C @ sk_B)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf(t1_tsep_1, axiom,
% 0.20/0.53    (![A:$i]:
% 0.20/0.53     ( ( l1_pre_topc @ A ) =>
% 0.20/0.53       ( ![B:$i]:
% 0.20/0.53         ( ( m1_pre_topc @ B @ A ) =>
% 0.20/0.53           ( m1_subset_1 @
% 0.20/0.53             ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.20/0.53  thf('25', plain,
% 0.20/0.53      (![X19 : $i, X20 : $i]:
% 0.20/0.53         (~ (m1_pre_topc @ X19 @ X20)
% 0.20/0.53          | (m1_subset_1 @ (u1_struct_0 @ X19) @ 
% 0.20/0.53             (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.20/0.53          | ~ (l1_pre_topc @ X20))),
% 0.20/0.53      inference('cnf', [status(esa)], [t1_tsep_1])).
% 0.20/0.53  thf('26', plain,
% 0.20/0.53      ((~ (l1_pre_topc @ sk_B)
% 0.20/0.53        | (m1_subset_1 @ (u1_struct_0 @ sk_C) @ 
% 0.20/0.53           (k1_zfmisc_1 @ (u1_struct_0 @ sk_B))))),
% 0.20/0.53      inference('sup-', [status(thm)], ['24', '25'])).
% 0.20/0.53  thf('27', plain, ((l1_pre_topc @ sk_B)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('28', plain,
% 0.20/0.53      ((m1_subset_1 @ (u1_struct_0 @ sk_C) @ 
% 0.20/0.53        (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.20/0.53      inference('demod', [status(thm)], ['26', '27'])).
% 0.20/0.53  thf('29', plain,
% 0.20/0.53      (((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.20/0.53         (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_G)
% 0.20/0.53        | (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('30', plain,
% 0.20/0.53      (((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.20/0.53         (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_G))
% 0.20/0.53         <= (((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.20/0.53               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_G)))),
% 0.20/0.53      inference('split', [status(esa)], ['29'])).
% 0.20/0.53  thf('31', plain, (((sk_F) = (sk_G))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('32', plain,
% 0.20/0.53      (((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.20/0.53         (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_F))
% 0.20/0.53         <= (((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.20/0.53               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_G)))),
% 0.20/0.53      inference('demod', [status(thm)], ['30', '31'])).
% 0.20/0.53  thf('33', plain,
% 0.20/0.53      ((m1_subset_1 @ sk_E @ 
% 0.20/0.53        (k1_zfmisc_1 @ 
% 0.20/0.53         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A))))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf(t85_tmap_1, axiom,
% 0.20/0.53    (![A:$i]:
% 0.20/0.53     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.53       ( ![B:$i]:
% 0.20/0.53         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.20/0.53             ( l1_pre_topc @ B ) ) =>
% 0.20/0.53           ( ![C:$i]:
% 0.20/0.53             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ B ) ) =>
% 0.20/0.53               ( ![D:$i]:
% 0.20/0.53                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ B ) ) =>
% 0.20/0.53                   ( ![E:$i]:
% 0.20/0.53                     ( ( ( v1_funct_1 @ E ) & 
% 0.20/0.53                         ( v1_funct_2 @
% 0.20/0.53                           E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ A ) ) & 
% 0.20/0.53                         ( m1_subset_1 @
% 0.20/0.53                           E @ 
% 0.20/0.53                           ( k1_zfmisc_1 @
% 0.20/0.53                             ( k2_zfmisc_1 @
% 0.20/0.53                               ( u1_struct_0 @ D ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.20/0.53                       ( ( m1_pre_topc @ C @ D ) =>
% 0.20/0.53                         ( ![F:$i]:
% 0.20/0.53                           ( ( m1_subset_1 @
% 0.20/0.53                               F @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.20/0.53                             ( ![G:$i]:
% 0.20/0.53                               ( ( m1_subset_1 @ G @ ( u1_struct_0 @ D ) ) =>
% 0.20/0.53                                 ( ![H:$i]:
% 0.20/0.53                                   ( ( m1_subset_1 @ H @ ( u1_struct_0 @ C ) ) =>
% 0.20/0.53                                     ( ( ( v3_pre_topc @ F @ B ) & 
% 0.20/0.53                                         ( r2_hidden @ G @ F ) & 
% 0.20/0.53                                         ( r1_tarski @ F @ ( u1_struct_0 @ C ) ) & 
% 0.20/0.53                                         ( ( G ) = ( H ) ) ) =>
% 0.20/0.53                                       ( ( r1_tmap_1 @ D @ A @ E @ G ) <=>
% 0.20/0.53                                         ( r1_tmap_1 @
% 0.20/0.53                                           C @ A @ 
% 0.20/0.53                                           ( k3_tmap_1 @ B @ A @ D @ C @ E ) @ 
% 0.20/0.53                                           H ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.53  thf('34', plain,
% 0.20/0.53      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i, X35 : $i, X36 : $i, X37 : $i, 
% 0.20/0.53         X38 : $i]:
% 0.20/0.53         ((v2_struct_0 @ X31)
% 0.20/0.53          | ~ (v2_pre_topc @ X31)
% 0.20/0.53          | ~ (l1_pre_topc @ X31)
% 0.20/0.53          | (v2_struct_0 @ X32)
% 0.20/0.53          | ~ (m1_pre_topc @ X32 @ X31)
% 0.20/0.53          | ~ (m1_pre_topc @ X33 @ X32)
% 0.20/0.53          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (u1_struct_0 @ X31)))
% 0.20/0.53          | ~ (m1_subset_1 @ X35 @ (u1_struct_0 @ X33))
% 0.20/0.53          | ~ (r1_tmap_1 @ X33 @ X36 @ 
% 0.20/0.53               (k3_tmap_1 @ X31 @ X36 @ X32 @ X33 @ X37) @ X35)
% 0.20/0.53          | (r1_tmap_1 @ X32 @ X36 @ X37 @ X38)
% 0.20/0.53          | ((X38) != (X35))
% 0.20/0.53          | ~ (r1_tarski @ X34 @ (u1_struct_0 @ X33))
% 0.20/0.53          | ~ (r2_hidden @ X38 @ X34)
% 0.20/0.53          | ~ (v3_pre_topc @ X34 @ X31)
% 0.20/0.53          | ~ (m1_subset_1 @ X38 @ (u1_struct_0 @ X32))
% 0.20/0.53          | ~ (m1_subset_1 @ X37 @ 
% 0.20/0.53               (k1_zfmisc_1 @ 
% 0.20/0.53                (k2_zfmisc_1 @ (u1_struct_0 @ X32) @ (u1_struct_0 @ X36))))
% 0.20/0.53          | ~ (v1_funct_2 @ X37 @ (u1_struct_0 @ X32) @ (u1_struct_0 @ X36))
% 0.20/0.53          | ~ (v1_funct_1 @ X37)
% 0.20/0.53          | ~ (m1_pre_topc @ X33 @ X31)
% 0.20/0.53          | (v2_struct_0 @ X33)
% 0.20/0.53          | ~ (l1_pre_topc @ X36)
% 0.20/0.53          | ~ (v2_pre_topc @ X36)
% 0.20/0.53          | (v2_struct_0 @ X36))),
% 0.20/0.53      inference('cnf', [status(esa)], [t85_tmap_1])).
% 0.20/0.53  thf('35', plain,
% 0.20/0.53      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i, X35 : $i, X36 : $i, X37 : $i]:
% 0.20/0.53         ((v2_struct_0 @ X36)
% 0.20/0.53          | ~ (v2_pre_topc @ X36)
% 0.20/0.53          | ~ (l1_pre_topc @ X36)
% 0.20/0.53          | (v2_struct_0 @ X33)
% 0.20/0.53          | ~ (m1_pre_topc @ X33 @ X31)
% 0.20/0.53          | ~ (v1_funct_1 @ X37)
% 0.20/0.53          | ~ (v1_funct_2 @ X37 @ (u1_struct_0 @ X32) @ (u1_struct_0 @ X36))
% 0.20/0.53          | ~ (m1_subset_1 @ X37 @ 
% 0.20/0.53               (k1_zfmisc_1 @ 
% 0.20/0.53                (k2_zfmisc_1 @ (u1_struct_0 @ X32) @ (u1_struct_0 @ X36))))
% 0.20/0.53          | ~ (m1_subset_1 @ X35 @ (u1_struct_0 @ X32))
% 0.20/0.53          | ~ (v3_pre_topc @ X34 @ X31)
% 0.20/0.53          | ~ (r2_hidden @ X35 @ X34)
% 0.20/0.53          | ~ (r1_tarski @ X34 @ (u1_struct_0 @ X33))
% 0.20/0.53          | (r1_tmap_1 @ X32 @ X36 @ X37 @ X35)
% 0.20/0.53          | ~ (r1_tmap_1 @ X33 @ X36 @ 
% 0.20/0.53               (k3_tmap_1 @ X31 @ X36 @ X32 @ X33 @ X37) @ X35)
% 0.20/0.53          | ~ (m1_subset_1 @ X35 @ (u1_struct_0 @ X33))
% 0.20/0.53          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (u1_struct_0 @ X31)))
% 0.20/0.53          | ~ (m1_pre_topc @ X33 @ X32)
% 0.20/0.53          | ~ (m1_pre_topc @ X32 @ X31)
% 0.20/0.53          | (v2_struct_0 @ X32)
% 0.20/0.53          | ~ (l1_pre_topc @ X31)
% 0.20/0.53          | ~ (v2_pre_topc @ X31)
% 0.20/0.53          | (v2_struct_0 @ X31))),
% 0.20/0.53      inference('simplify', [status(thm)], ['34'])).
% 0.20/0.53  thf('36', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.53         ((v2_struct_0 @ X0)
% 0.20/0.53          | ~ (v2_pre_topc @ X0)
% 0.20/0.53          | ~ (l1_pre_topc @ X0)
% 0.20/0.53          | (v2_struct_0 @ sk_D)
% 0.20/0.53          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.20/0.53          | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.20/0.53          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.20/0.53          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X1))
% 0.20/0.53          | ~ (r1_tmap_1 @ X1 @ sk_A @ 
% 0.20/0.53               (k3_tmap_1 @ X0 @ sk_A @ sk_D @ X1 @ sk_E) @ X3)
% 0.20/0.53          | (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ X3)
% 0.20/0.53          | ~ (r1_tarski @ X2 @ (u1_struct_0 @ X1))
% 0.20/0.53          | ~ (r2_hidden @ X3 @ X2)
% 0.20/0.53          | ~ (v3_pre_topc @ X2 @ X0)
% 0.20/0.53          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ sk_D))
% 0.20/0.53          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A))
% 0.20/0.53          | ~ (v1_funct_1 @ sk_E)
% 0.20/0.53          | ~ (m1_pre_topc @ X1 @ X0)
% 0.20/0.53          | (v2_struct_0 @ X1)
% 0.20/0.53          | ~ (l1_pre_topc @ sk_A)
% 0.20/0.53          | ~ (v2_pre_topc @ sk_A)
% 0.20/0.53          | (v2_struct_0 @ sk_A))),
% 0.20/0.53      inference('sup-', [status(thm)], ['33', '35'])).
% 0.20/0.53  thf('37', plain,
% 0.20/0.53      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('38', plain, ((v1_funct_1 @ sk_E)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('39', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('40', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('41', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.53         ((v2_struct_0 @ X0)
% 0.20/0.53          | ~ (v2_pre_topc @ X0)
% 0.20/0.53          | ~ (l1_pre_topc @ X0)
% 0.20/0.53          | (v2_struct_0 @ sk_D)
% 0.20/0.53          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.20/0.53          | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.20/0.53          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.20/0.53          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X1))
% 0.20/0.53          | ~ (r1_tmap_1 @ X1 @ sk_A @ 
% 0.20/0.53               (k3_tmap_1 @ X0 @ sk_A @ sk_D @ X1 @ sk_E) @ X3)
% 0.20/0.53          | (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ X3)
% 0.20/0.53          | ~ (r1_tarski @ X2 @ (u1_struct_0 @ X1))
% 0.20/0.53          | ~ (r2_hidden @ X3 @ X2)
% 0.20/0.53          | ~ (v3_pre_topc @ X2 @ X0)
% 0.20/0.53          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ sk_D))
% 0.20/0.53          | ~ (m1_pre_topc @ X1 @ X0)
% 0.20/0.53          | (v2_struct_0 @ X1)
% 0.20/0.53          | (v2_struct_0 @ sk_A))),
% 0.20/0.53      inference('demod', [status(thm)], ['36', '37', '38', '39', '40'])).
% 0.20/0.53  thf('42', plain,
% 0.20/0.53      ((![X0 : $i]:
% 0.20/0.53          ((v2_struct_0 @ sk_A)
% 0.20/0.53           | (v2_struct_0 @ sk_C)
% 0.20/0.53           | ~ (m1_pre_topc @ sk_C @ sk_B)
% 0.20/0.53           | ~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_D))
% 0.20/0.53           | ~ (v3_pre_topc @ X0 @ sk_B)
% 0.20/0.53           | ~ (r2_hidden @ sk_F @ X0)
% 0.20/0.53           | ~ (r1_tarski @ X0 @ (u1_struct_0 @ sk_C))
% 0.20/0.53           | (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F)
% 0.20/0.53           | ~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C))
% 0.20/0.53           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.20/0.53           | ~ (m1_pre_topc @ sk_C @ sk_D)
% 0.20/0.53           | ~ (m1_pre_topc @ sk_D @ sk_B)
% 0.20/0.53           | (v2_struct_0 @ sk_D)
% 0.20/0.53           | ~ (l1_pre_topc @ sk_B)
% 0.20/0.53           | ~ (v2_pre_topc @ sk_B)
% 0.20/0.53           | (v2_struct_0 @ sk_B)))
% 0.20/0.53         <= (((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.20/0.53               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_G)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['32', '41'])).
% 0.20/0.53  thf('43', plain, ((m1_pre_topc @ sk_C @ sk_B)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('44', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_D))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('45', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C))),
% 0.20/0.53      inference('demod', [status(thm)], ['2', '3'])).
% 0.20/0.53  thf('46', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('47', plain, ((m1_pre_topc @ sk_D @ sk_B)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('48', plain, ((l1_pre_topc @ sk_B)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('49', plain, ((v2_pre_topc @ sk_B)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('50', plain,
% 0.20/0.53      ((![X0 : $i]:
% 0.20/0.53          ((v2_struct_0 @ sk_A)
% 0.20/0.53           | (v2_struct_0 @ sk_C)
% 0.20/0.53           | ~ (v3_pre_topc @ X0 @ sk_B)
% 0.20/0.53           | ~ (r2_hidden @ sk_F @ X0)
% 0.20/0.53           | ~ (r1_tarski @ X0 @ (u1_struct_0 @ sk_C))
% 0.20/0.53           | (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F)
% 0.20/0.53           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.20/0.53           | (v2_struct_0 @ sk_D)
% 0.20/0.53           | (v2_struct_0 @ sk_B)))
% 0.20/0.53         <= (((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.20/0.53               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_G)))),
% 0.20/0.53      inference('demod', [status(thm)],
% 0.20/0.53                ['42', '43', '44', '45', '46', '47', '48', '49'])).
% 0.20/0.53  thf('51', plain,
% 0.20/0.53      ((((v2_struct_0 @ sk_B)
% 0.20/0.53         | (v2_struct_0 @ sk_D)
% 0.20/0.53         | (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F)
% 0.20/0.53         | ~ (r1_tarski @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_C))
% 0.20/0.53         | ~ (r2_hidden @ sk_F @ (u1_struct_0 @ sk_C))
% 0.20/0.53         | ~ (v3_pre_topc @ (u1_struct_0 @ sk_C) @ sk_B)
% 0.20/0.53         | (v2_struct_0 @ sk_C)
% 0.20/0.53         | (v2_struct_0 @ sk_A)))
% 0.20/0.53         <= (((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.20/0.53               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_G)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['28', '50'])).
% 0.20/0.53  thf(d10_xboole_0, axiom,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.20/0.53  thf('52', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.20/0.53      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.20/0.53  thf('53', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.20/0.53      inference('simplify', [status(thm)], ['52'])).
% 0.20/0.53  thf('54', plain,
% 0.20/0.53      ((m1_subset_1 @ (u1_struct_0 @ sk_C) @ 
% 0.20/0.53        (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.20/0.53      inference('demod', [status(thm)], ['26', '27'])).
% 0.20/0.53  thf(t16_tsep_1, axiom,
% 0.20/0.53    (![A:$i]:
% 0.20/0.53     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.53       ( ![B:$i]:
% 0.20/0.53         ( ( m1_pre_topc @ B @ A ) =>
% 0.20/0.53           ( ![C:$i]:
% 0.20/0.53             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.53               ( ( ( C ) = ( u1_struct_0 @ B ) ) =>
% 0.20/0.53                 ( ( ( v1_tsep_1 @ B @ A ) & ( m1_pre_topc @ B @ A ) ) <=>
% 0.20/0.53                   ( v3_pre_topc @ C @ A ) ) ) ) ) ) ) ))).
% 0.20/0.53  thf('55', plain,
% 0.20/0.53      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.20/0.53         (~ (m1_pre_topc @ X16 @ X17)
% 0.20/0.53          | ((X18) != (u1_struct_0 @ X16))
% 0.20/0.53          | ~ (v1_tsep_1 @ X16 @ X17)
% 0.20/0.53          | ~ (m1_pre_topc @ X16 @ X17)
% 0.20/0.53          | (v3_pre_topc @ X18 @ X17)
% 0.20/0.53          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.20/0.53          | ~ (l1_pre_topc @ X17)
% 0.20/0.53          | ~ (v2_pre_topc @ X17))),
% 0.20/0.53      inference('cnf', [status(esa)], [t16_tsep_1])).
% 0.20/0.53  thf('56', plain,
% 0.20/0.53      (![X16 : $i, X17 : $i]:
% 0.20/0.53         (~ (v2_pre_topc @ X17)
% 0.20/0.53          | ~ (l1_pre_topc @ X17)
% 0.20/0.53          | ~ (m1_subset_1 @ (u1_struct_0 @ X16) @ 
% 0.20/0.53               (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.20/0.53          | (v3_pre_topc @ (u1_struct_0 @ X16) @ X17)
% 0.20/0.53          | ~ (v1_tsep_1 @ X16 @ X17)
% 0.20/0.53          | ~ (m1_pre_topc @ X16 @ X17))),
% 0.20/0.53      inference('simplify', [status(thm)], ['55'])).
% 0.20/0.53  thf('57', plain,
% 0.20/0.53      ((~ (m1_pre_topc @ sk_C @ sk_B)
% 0.20/0.53        | ~ (v1_tsep_1 @ sk_C @ sk_B)
% 0.20/0.53        | (v3_pre_topc @ (u1_struct_0 @ sk_C) @ sk_B)
% 0.20/0.53        | ~ (l1_pre_topc @ sk_B)
% 0.20/0.53        | ~ (v2_pre_topc @ sk_B))),
% 0.20/0.53      inference('sup-', [status(thm)], ['54', '56'])).
% 0.20/0.53  thf('58', plain, ((m1_pre_topc @ sk_C @ sk_B)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('59', plain, ((v1_tsep_1 @ sk_C @ sk_B)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('60', plain, ((l1_pre_topc @ sk_B)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('61', plain, ((v2_pre_topc @ sk_B)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('62', plain, ((v3_pre_topc @ (u1_struct_0 @ sk_C) @ sk_B)),
% 0.20/0.53      inference('demod', [status(thm)], ['57', '58', '59', '60', '61'])).
% 0.20/0.53  thf('63', plain,
% 0.20/0.53      ((((v2_struct_0 @ sk_B)
% 0.20/0.53         | (v2_struct_0 @ sk_D)
% 0.20/0.53         | (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F)
% 0.20/0.53         | ~ (r2_hidden @ sk_F @ (u1_struct_0 @ sk_C))
% 0.20/0.53         | (v2_struct_0 @ sk_C)
% 0.20/0.53         | (v2_struct_0 @ sk_A)))
% 0.20/0.53         <= (((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.20/0.53               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_G)))),
% 0.20/0.53      inference('demod', [status(thm)], ['51', '53', '62'])).
% 0.20/0.53  thf('64', plain,
% 0.20/0.53      ((((v1_xboole_0 @ (u1_struct_0 @ sk_C))
% 0.20/0.53         | (v2_struct_0 @ sk_A)
% 0.20/0.53         | (v2_struct_0 @ sk_C)
% 0.20/0.53         | (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F)
% 0.20/0.53         | (v2_struct_0 @ sk_D)
% 0.20/0.53         | (v2_struct_0 @ sk_B)))
% 0.20/0.53         <= (((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.20/0.53               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_G)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['23', '63'])).
% 0.20/0.53  thf('65', plain,
% 0.20/0.53      ((~ (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F))
% 0.20/0.53         <= (~ ((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F)))),
% 0.20/0.53      inference('split', [status(esa)], ['0'])).
% 0.20/0.53  thf('66', plain,
% 0.20/0.53      ((((v2_struct_0 @ sk_B)
% 0.20/0.53         | (v2_struct_0 @ sk_D)
% 0.20/0.53         | (v2_struct_0 @ sk_C)
% 0.20/0.53         | (v2_struct_0 @ sk_A)
% 0.20/0.53         | (v1_xboole_0 @ (u1_struct_0 @ sk_C))))
% 0.20/0.53         <= (~ ((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F)) & 
% 0.20/0.53             ((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.20/0.53               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_G)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['64', '65'])).
% 0.20/0.53  thf('67', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C))),
% 0.20/0.53      inference('demod', [status(thm)], ['2', '3'])).
% 0.20/0.53  thf(dt_k1_connsp_2, axiom,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.20/0.53         ( l1_pre_topc @ A ) & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.53       ( m1_subset_1 @
% 0.20/0.53         ( k1_connsp_2 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.20/0.53  thf('68', plain,
% 0.20/0.53      (![X12 : $i, X13 : $i]:
% 0.20/0.53         (~ (l1_pre_topc @ X12)
% 0.20/0.53          | ~ (v2_pre_topc @ X12)
% 0.20/0.53          | (v2_struct_0 @ X12)
% 0.20/0.53          | ~ (m1_subset_1 @ X13 @ (u1_struct_0 @ X12))
% 0.20/0.53          | (m1_subset_1 @ (k1_connsp_2 @ X12 @ X13) @ 
% 0.20/0.53             (k1_zfmisc_1 @ (u1_struct_0 @ X12))))),
% 0.20/0.53      inference('cnf', [status(esa)], [dt_k1_connsp_2])).
% 0.20/0.53  thf('69', plain,
% 0.20/0.53      (((m1_subset_1 @ (k1_connsp_2 @ sk_C @ sk_F) @ 
% 0.20/0.53         (k1_zfmisc_1 @ (u1_struct_0 @ sk_C)))
% 0.20/0.53        | (v2_struct_0 @ sk_C)
% 0.20/0.53        | ~ (v2_pre_topc @ sk_C)
% 0.20/0.53        | ~ (l1_pre_topc @ sk_C))),
% 0.20/0.53      inference('sup-', [status(thm)], ['67', '68'])).
% 0.20/0.53  thf('70', plain, ((v2_pre_topc @ sk_C)),
% 0.20/0.53      inference('demod', [status(thm)], ['9', '10', '11'])).
% 0.20/0.53  thf('71', plain, ((l1_pre_topc @ sk_C)),
% 0.20/0.53      inference('demod', [status(thm)], ['15', '16'])).
% 0.20/0.53  thf('72', plain,
% 0.20/0.53      (((m1_subset_1 @ (k1_connsp_2 @ sk_C @ sk_F) @ 
% 0.20/0.53         (k1_zfmisc_1 @ (u1_struct_0 @ sk_C)))
% 0.20/0.53        | (v2_struct_0 @ sk_C))),
% 0.20/0.53      inference('demod', [status(thm)], ['69', '70', '71'])).
% 0.20/0.53  thf('73', plain, (~ (v2_struct_0 @ sk_C)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('74', plain,
% 0.20/0.53      ((m1_subset_1 @ (k1_connsp_2 @ sk_C @ sk_F) @ 
% 0.20/0.53        (k1_zfmisc_1 @ (u1_struct_0 @ sk_C)))),
% 0.20/0.53      inference('clc', [status(thm)], ['72', '73'])).
% 0.20/0.53  thf(t5_subset, axiom,
% 0.20/0.53    (![A:$i,B:$i,C:$i]:
% 0.20/0.53     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 0.20/0.53          ( v1_xboole_0 @ C ) ) ))).
% 0.20/0.53  thf('75', plain,
% 0.20/0.53      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.20/0.53         (~ (r2_hidden @ X5 @ X6)
% 0.20/0.53          | ~ (v1_xboole_0 @ X7)
% 0.20/0.53          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7)))),
% 0.20/0.53      inference('cnf', [status(esa)], [t5_subset])).
% 0.20/0.53  thf('76', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         (~ (v1_xboole_0 @ (u1_struct_0 @ sk_C))
% 0.20/0.53          | ~ (r2_hidden @ X0 @ (k1_connsp_2 @ sk_C @ sk_F)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['74', '75'])).
% 0.20/0.53  thf('77', plain,
% 0.20/0.53      ((![X0 : $i]:
% 0.20/0.53          ((v2_struct_0 @ sk_A)
% 0.20/0.53           | (v2_struct_0 @ sk_C)
% 0.20/0.53           | (v2_struct_0 @ sk_D)
% 0.20/0.53           | (v2_struct_0 @ sk_B)
% 0.20/0.53           | ~ (r2_hidden @ X0 @ (k1_connsp_2 @ sk_C @ sk_F))))
% 0.20/0.53         <= (~ ((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F)) & 
% 0.20/0.53             ((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.20/0.53               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_G)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['66', '76'])).
% 0.20/0.53  thf('78', plain,
% 0.20/0.53      ((((v2_struct_0 @ sk_B)
% 0.20/0.53         | (v2_struct_0 @ sk_D)
% 0.20/0.53         | (v2_struct_0 @ sk_C)
% 0.20/0.53         | (v2_struct_0 @ sk_A)))
% 0.20/0.53         <= (~ ((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F)) & 
% 0.20/0.53             ((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.20/0.53               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_G)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['20', '77'])).
% 0.20/0.53  thf('79', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('80', plain,
% 0.20/0.53      ((((v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_B)))
% 0.20/0.53         <= (~ ((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F)) & 
% 0.20/0.53             ((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.20/0.53               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_G)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['78', '79'])).
% 0.20/0.53  thf('81', plain, (~ (v2_struct_0 @ sk_C)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('82', plain,
% 0.20/0.53      ((((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_D)))
% 0.20/0.53         <= (~ ((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F)) & 
% 0.20/0.53             ((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.20/0.53               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_G)))),
% 0.20/0.53      inference('clc', [status(thm)], ['80', '81'])).
% 0.20/0.53  thf('83', plain, (~ (v2_struct_0 @ sk_B)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('84', plain,
% 0.20/0.53      (((v2_struct_0 @ sk_D))
% 0.20/0.53         <= (~ ((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F)) & 
% 0.20/0.53             ((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.20/0.53               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_G)))),
% 0.20/0.53      inference('clc', [status(thm)], ['82', '83'])).
% 0.20/0.53  thf('85', plain, (~ (v2_struct_0 @ sk_D)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('86', plain,
% 0.20/0.53      (((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F)) | 
% 0.20/0.53       ~
% 0.20/0.53       ((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.20/0.53         (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_G))),
% 0.20/0.53      inference('sup-', [status(thm)], ['84', '85'])).
% 0.20/0.53  thf('87', plain,
% 0.20/0.53      (((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F)) | 
% 0.20/0.53       ((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.20/0.53         (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_G))),
% 0.20/0.53      inference('split', [status(esa)], ['29'])).
% 0.20/0.53  thf('88', plain, ((m1_pre_topc @ sk_C @ sk_B)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('89', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C))),
% 0.20/0.53      inference('demod', [status(thm)], ['2', '3'])).
% 0.20/0.53  thf('90', plain,
% 0.20/0.53      (((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F))
% 0.20/0.53         <= (((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F)))),
% 0.20/0.53      inference('split', [status(esa)], ['29'])).
% 0.20/0.53  thf('91', plain,
% 0.20/0.53      ((m1_subset_1 @ sk_E @ 
% 0.20/0.53        (k1_zfmisc_1 @ 
% 0.20/0.53         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A))))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf(t81_tmap_1, axiom,
% 0.20/0.53    (![A:$i]:
% 0.20/0.53     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.53       ( ![B:$i]:
% 0.20/0.53         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.20/0.53             ( l1_pre_topc @ B ) ) =>
% 0.20/0.53           ( ![C:$i]:
% 0.20/0.53             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.20/0.53               ( ![D:$i]:
% 0.20/0.53                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.20/0.53                   ( ![E:$i]:
% 0.20/0.53                     ( ( ( v1_funct_1 @ E ) & 
% 0.20/0.53                         ( v1_funct_2 @
% 0.20/0.53                           E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 0.20/0.53                         ( m1_subset_1 @
% 0.20/0.53                           E @ 
% 0.20/0.53                           ( k1_zfmisc_1 @
% 0.20/0.53                             ( k2_zfmisc_1 @
% 0.20/0.53                               ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.20/0.53                       ( ![F:$i]:
% 0.20/0.53                         ( ( m1_subset_1 @ F @ ( u1_struct_0 @ C ) ) =>
% 0.20/0.53                           ( ![G:$i]:
% 0.20/0.53                             ( ( m1_subset_1 @ G @ ( u1_struct_0 @ D ) ) =>
% 0.20/0.53                               ( ( ( ( F ) = ( G ) ) & 
% 0.20/0.53                                   ( m1_pre_topc @ D @ C ) & 
% 0.20/0.53                                   ( r1_tmap_1 @ C @ B @ E @ F ) ) =>
% 0.20/0.53                                 ( r1_tmap_1 @
% 0.20/0.53                                   D @ B @ ( k3_tmap_1 @ A @ B @ C @ D @ E ) @ 
% 0.20/0.53                                   G ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.53  thf('92', plain,
% 0.20/0.53      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 0.20/0.53         ((v2_struct_0 @ X24)
% 0.20/0.53          | ~ (v2_pre_topc @ X24)
% 0.20/0.53          | ~ (l1_pre_topc @ X24)
% 0.20/0.53          | (v2_struct_0 @ X25)
% 0.20/0.53          | ~ (m1_pre_topc @ X25 @ X26)
% 0.20/0.53          | ~ (m1_subset_1 @ X27 @ (u1_struct_0 @ X28))
% 0.20/0.53          | ~ (m1_pre_topc @ X25 @ X28)
% 0.20/0.53          | ~ (r1_tmap_1 @ X28 @ X24 @ X29 @ X27)
% 0.20/0.53          | ((X27) != (X30))
% 0.20/0.53          | (r1_tmap_1 @ X25 @ X24 @ 
% 0.20/0.53             (k3_tmap_1 @ X26 @ X24 @ X28 @ X25 @ X29) @ X30)
% 0.20/0.53          | ~ (m1_subset_1 @ X30 @ (u1_struct_0 @ X25))
% 0.20/0.53          | ~ (m1_subset_1 @ X29 @ 
% 0.20/0.53               (k1_zfmisc_1 @ 
% 0.20/0.53                (k2_zfmisc_1 @ (u1_struct_0 @ X28) @ (u1_struct_0 @ X24))))
% 0.20/0.53          | ~ (v1_funct_2 @ X29 @ (u1_struct_0 @ X28) @ (u1_struct_0 @ X24))
% 0.20/0.53          | ~ (v1_funct_1 @ X29)
% 0.20/0.53          | ~ (m1_pre_topc @ X28 @ X26)
% 0.20/0.53          | (v2_struct_0 @ X28)
% 0.20/0.53          | ~ (l1_pre_topc @ X26)
% 0.20/0.53          | ~ (v2_pre_topc @ X26)
% 0.20/0.53          | (v2_struct_0 @ X26))),
% 0.20/0.53      inference('cnf', [status(esa)], [t81_tmap_1])).
% 0.20/0.53  thf('93', plain,
% 0.20/0.53      (![X24 : $i, X25 : $i, X26 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 0.20/0.53         ((v2_struct_0 @ X26)
% 0.20/0.53          | ~ (v2_pre_topc @ X26)
% 0.20/0.53          | ~ (l1_pre_topc @ X26)
% 0.20/0.53          | (v2_struct_0 @ X28)
% 0.20/0.53          | ~ (m1_pre_topc @ X28 @ X26)
% 0.20/0.53          | ~ (v1_funct_1 @ X29)
% 0.20/0.53          | ~ (v1_funct_2 @ X29 @ (u1_struct_0 @ X28) @ (u1_struct_0 @ X24))
% 0.20/0.53          | ~ (m1_subset_1 @ X29 @ 
% 0.20/0.53               (k1_zfmisc_1 @ 
% 0.20/0.53                (k2_zfmisc_1 @ (u1_struct_0 @ X28) @ (u1_struct_0 @ X24))))
% 0.20/0.53          | ~ (m1_subset_1 @ X30 @ (u1_struct_0 @ X25))
% 0.20/0.53          | (r1_tmap_1 @ X25 @ X24 @ 
% 0.20/0.53             (k3_tmap_1 @ X26 @ X24 @ X28 @ X25 @ X29) @ X30)
% 0.20/0.53          | ~ (r1_tmap_1 @ X28 @ X24 @ X29 @ X30)
% 0.20/0.53          | ~ (m1_pre_topc @ X25 @ X28)
% 0.20/0.53          | ~ (m1_subset_1 @ X30 @ (u1_struct_0 @ X28))
% 0.20/0.53          | ~ (m1_pre_topc @ X25 @ X26)
% 0.20/0.53          | (v2_struct_0 @ X25)
% 0.20/0.53          | ~ (l1_pre_topc @ X24)
% 0.20/0.53          | ~ (v2_pre_topc @ X24)
% 0.20/0.53          | (v2_struct_0 @ X24))),
% 0.20/0.53      inference('simplify', [status(thm)], ['92'])).
% 0.20/0.53  thf('94', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.53         ((v2_struct_0 @ sk_A)
% 0.20/0.53          | ~ (v2_pre_topc @ sk_A)
% 0.20/0.53          | ~ (l1_pre_topc @ sk_A)
% 0.20/0.53          | (v2_struct_0 @ X0)
% 0.20/0.53          | ~ (m1_pre_topc @ X0 @ X1)
% 0.20/0.53          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ sk_D))
% 0.20/0.53          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.20/0.53          | ~ (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ X2)
% 0.20/0.53          | (r1_tmap_1 @ X0 @ sk_A @ 
% 0.20/0.53             (k3_tmap_1 @ X1 @ sk_A @ sk_D @ X0 @ sk_E) @ X2)
% 0.20/0.53          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.20/0.53          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A))
% 0.20/0.53          | ~ (v1_funct_1 @ sk_E)
% 0.20/0.53          | ~ (m1_pre_topc @ sk_D @ X1)
% 0.20/0.53          | (v2_struct_0 @ sk_D)
% 0.20/0.53          | ~ (l1_pre_topc @ X1)
% 0.20/0.53          | ~ (v2_pre_topc @ X1)
% 0.20/0.53          | (v2_struct_0 @ X1))),
% 0.20/0.53      inference('sup-', [status(thm)], ['91', '93'])).
% 0.20/0.53  thf('95', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('96', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('97', plain,
% 0.20/0.53      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('98', plain, ((v1_funct_1 @ sk_E)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('99', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.53         ((v2_struct_0 @ sk_A)
% 0.20/0.53          | (v2_struct_0 @ X0)
% 0.20/0.53          | ~ (m1_pre_topc @ X0 @ X1)
% 0.20/0.53          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ sk_D))
% 0.20/0.53          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.20/0.53          | ~ (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ X2)
% 0.20/0.53          | (r1_tmap_1 @ X0 @ sk_A @ 
% 0.20/0.53             (k3_tmap_1 @ X1 @ sk_A @ sk_D @ X0 @ sk_E) @ X2)
% 0.20/0.53          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.20/0.53          | ~ (m1_pre_topc @ sk_D @ X1)
% 0.20/0.53          | (v2_struct_0 @ sk_D)
% 0.20/0.53          | ~ (l1_pre_topc @ X1)
% 0.20/0.53          | ~ (v2_pre_topc @ X1)
% 0.20/0.53          | (v2_struct_0 @ X1))),
% 0.20/0.53      inference('demod', [status(thm)], ['94', '95', '96', '97', '98'])).
% 0.20/0.53  thf('100', plain,
% 0.20/0.53      ((![X0 : $i, X1 : $i]:
% 0.20/0.53          ((v2_struct_0 @ X0)
% 0.20/0.53           | ~ (v2_pre_topc @ X0)
% 0.20/0.53           | ~ (l1_pre_topc @ X0)
% 0.20/0.53           | (v2_struct_0 @ sk_D)
% 0.20/0.53           | ~ (m1_pre_topc @ sk_D @ X0)
% 0.20/0.53           | ~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ X1))
% 0.20/0.53           | (r1_tmap_1 @ X1 @ sk_A @ 
% 0.20/0.53              (k3_tmap_1 @ X0 @ sk_A @ sk_D @ X1 @ sk_E) @ sk_F)
% 0.20/0.53           | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.20/0.53           | ~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_D))
% 0.20/0.53           | ~ (m1_pre_topc @ X1 @ X0)
% 0.20/0.53           | (v2_struct_0 @ X1)
% 0.20/0.53           | (v2_struct_0 @ sk_A)))
% 0.20/0.53         <= (((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['90', '99'])).
% 0.20/0.53  thf('101', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_D))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('102', plain,
% 0.20/0.53      ((![X0 : $i, X1 : $i]:
% 0.20/0.53          ((v2_struct_0 @ X0)
% 0.20/0.53           | ~ (v2_pre_topc @ X0)
% 0.20/0.53           | ~ (l1_pre_topc @ X0)
% 0.20/0.53           | (v2_struct_0 @ sk_D)
% 0.20/0.53           | ~ (m1_pre_topc @ sk_D @ X0)
% 0.20/0.53           | ~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ X1))
% 0.20/0.53           | (r1_tmap_1 @ X1 @ sk_A @ 
% 0.20/0.53              (k3_tmap_1 @ X0 @ sk_A @ sk_D @ X1 @ sk_E) @ sk_F)
% 0.20/0.53           | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.20/0.53           | ~ (m1_pre_topc @ X1 @ X0)
% 0.20/0.53           | (v2_struct_0 @ X1)
% 0.20/0.53           | (v2_struct_0 @ sk_A)))
% 0.20/0.53         <= (((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F)))),
% 0.20/0.53      inference('demod', [status(thm)], ['100', '101'])).
% 0.20/0.53  thf('103', plain,
% 0.20/0.53      ((![X0 : $i]:
% 0.20/0.53          ((v2_struct_0 @ sk_A)
% 0.20/0.53           | (v2_struct_0 @ sk_C)
% 0.20/0.53           | ~ (m1_pre_topc @ sk_C @ X0)
% 0.20/0.53           | ~ (m1_pre_topc @ sk_C @ sk_D)
% 0.20/0.53           | (r1_tmap_1 @ sk_C @ sk_A @ 
% 0.20/0.53              (k3_tmap_1 @ X0 @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_F)
% 0.20/0.53           | ~ (m1_pre_topc @ sk_D @ X0)
% 0.20/0.53           | (v2_struct_0 @ sk_D)
% 0.20/0.53           | ~ (l1_pre_topc @ X0)
% 0.20/0.53           | ~ (v2_pre_topc @ X0)
% 0.20/0.53           | (v2_struct_0 @ X0)))
% 0.20/0.53         <= (((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['89', '102'])).
% 0.20/0.53  thf('104', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('105', plain,
% 0.20/0.53      ((![X0 : $i]:
% 0.20/0.53          ((v2_struct_0 @ sk_A)
% 0.20/0.53           | (v2_struct_0 @ sk_C)
% 0.20/0.53           | ~ (m1_pre_topc @ sk_C @ X0)
% 0.20/0.53           | (r1_tmap_1 @ sk_C @ sk_A @ 
% 0.20/0.53              (k3_tmap_1 @ X0 @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_F)
% 0.20/0.53           | ~ (m1_pre_topc @ sk_D @ X0)
% 0.20/0.53           | (v2_struct_0 @ sk_D)
% 0.20/0.53           | ~ (l1_pre_topc @ X0)
% 0.20/0.53           | ~ (v2_pre_topc @ X0)
% 0.20/0.53           | (v2_struct_0 @ X0)))
% 0.20/0.53         <= (((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F)))),
% 0.20/0.53      inference('demod', [status(thm)], ['103', '104'])).
% 0.20/0.53  thf('106', plain,
% 0.20/0.53      ((((v2_struct_0 @ sk_B)
% 0.20/0.53         | ~ (v2_pre_topc @ sk_B)
% 0.20/0.53         | ~ (l1_pre_topc @ sk_B)
% 0.20/0.53         | (v2_struct_0 @ sk_D)
% 0.20/0.53         | ~ (m1_pre_topc @ sk_D @ sk_B)
% 0.20/0.53         | (r1_tmap_1 @ sk_C @ sk_A @ 
% 0.20/0.53            (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_F)
% 0.20/0.53         | (v2_struct_0 @ sk_C)
% 0.20/0.53         | (v2_struct_0 @ sk_A)))
% 0.20/0.53         <= (((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['88', '105'])).
% 0.20/0.53  thf('107', plain, ((v2_pre_topc @ sk_B)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('108', plain, ((l1_pre_topc @ sk_B)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('109', plain, ((m1_pre_topc @ sk_D @ sk_B)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('110', plain,
% 0.20/0.53      ((((v2_struct_0 @ sk_B)
% 0.20/0.53         | (v2_struct_0 @ sk_D)
% 0.20/0.53         | (r1_tmap_1 @ sk_C @ sk_A @ 
% 0.20/0.53            (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_F)
% 0.20/0.53         | (v2_struct_0 @ sk_C)
% 0.20/0.53         | (v2_struct_0 @ sk_A)))
% 0.20/0.53         <= (((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F)))),
% 0.20/0.53      inference('demod', [status(thm)], ['106', '107', '108', '109'])).
% 0.20/0.53  thf('111', plain,
% 0.20/0.53      ((~ (r1_tmap_1 @ sk_C @ sk_A @ 
% 0.20/0.53           (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_G))
% 0.20/0.53         <= (~
% 0.20/0.53             ((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.20/0.53               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_G)))),
% 0.20/0.53      inference('split', [status(esa)], ['0'])).
% 0.20/0.53  thf('112', plain, (((sk_F) = (sk_G))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('113', plain,
% 0.20/0.53      ((~ (r1_tmap_1 @ sk_C @ sk_A @ 
% 0.20/0.53           (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_F))
% 0.20/0.53         <= (~
% 0.20/0.53             ((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.20/0.53               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_G)))),
% 0.20/0.53      inference('demod', [status(thm)], ['111', '112'])).
% 0.20/0.53  thf('114', plain,
% 0.20/0.53      ((((v2_struct_0 @ sk_A)
% 0.20/0.53         | (v2_struct_0 @ sk_C)
% 0.20/0.53         | (v2_struct_0 @ sk_D)
% 0.20/0.53         | (v2_struct_0 @ sk_B)))
% 0.20/0.53         <= (~
% 0.20/0.53             ((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.20/0.53               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_G)) & 
% 0.20/0.53             ((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['110', '113'])).
% 0.20/0.53  thf('115', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('116', plain,
% 0.20/0.53      ((((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_C)))
% 0.20/0.53         <= (~
% 0.20/0.53             ((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.20/0.53               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_G)) & 
% 0.20/0.53             ((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['114', '115'])).
% 0.20/0.53  thf('117', plain, (~ (v2_struct_0 @ sk_B)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('118', plain,
% 0.20/0.53      ((((v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_D)))
% 0.20/0.53         <= (~
% 0.20/0.53             ((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.20/0.53               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_G)) & 
% 0.20/0.53             ((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F)))),
% 0.20/0.53      inference('clc', [status(thm)], ['116', '117'])).
% 0.20/0.53  thf('119', plain, (~ (v2_struct_0 @ sk_C)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('120', plain,
% 0.20/0.53      (((v2_struct_0 @ sk_D))
% 0.20/0.53         <= (~
% 0.20/0.53             ((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.20/0.53               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_G)) & 
% 0.20/0.53             ((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F)))),
% 0.20/0.53      inference('clc', [status(thm)], ['118', '119'])).
% 0.20/0.53  thf('121', plain, (~ (v2_struct_0 @ sk_D)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('122', plain,
% 0.20/0.53      (~ ((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F)) | 
% 0.20/0.53       ((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.20/0.53         (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_G))),
% 0.20/0.53      inference('sup-', [status(thm)], ['120', '121'])).
% 0.20/0.53  thf('123', plain, ($false),
% 0.20/0.53      inference('sat_resolution*', [status(thm)], ['1', '86', '87', '122'])).
% 0.20/0.53  
% 0.20/0.53  % SZS output end Refutation
% 0.20/0.53  
% 0.20/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
