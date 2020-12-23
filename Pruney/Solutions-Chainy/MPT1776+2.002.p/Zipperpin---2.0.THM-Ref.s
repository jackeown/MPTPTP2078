%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.slEkXTUu3T

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:10:23 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  189 ( 493 expanded)
%              Number of leaves         :   39 ( 157 expanded)
%              Depth                    :   22
%              Number of atoms          : 2284 (18496 expanded)
%              Number of equality atoms :   29 ( 256 expanded)
%              Maximal formula depth    :   26 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tmap_1_type,type,(
    r1_tmap_1: $i > $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_tmap_1_type,type,(
    k2_tmap_1: $i > $i > $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_tmap_1_type,type,(
    k3_tmap_1: $i > $i > $i > $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k2_partfun1_type,type,(
    k2_partfun1: $i > $i > $i > $i > $i )).

thf(sk_G_type,type,(
    sk_G: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_tsep_1_type,type,(
    v1_tsep_1: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

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
    ( ~ ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E ) @ sk_G )
    | ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E ) @ sk_G )
    | ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,(
    sk_F = sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('5',plain,
    ( ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E ) @ sk_G )
    | ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F )
   <= ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F ) ),
    inference(split,[status(esa)],['5'])).

thf('7',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t64_tmap_1,axiom,(
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
                    & ( m1_pre_topc @ D @ B ) )
                 => ! [E: $i] :
                      ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) )
                     => ! [F: $i] :
                          ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) )
                         => ( ( ( E = F )
                              & ( r1_tmap_1 @ B @ A @ C @ E ) )
                           => ( r1_tmap_1 @ D @ A @ ( k2_tmap_1 @ B @ A @ C @ D ) @ F ) ) ) ) ) ) ) ) )).

thf('8',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i,X35: $i,X36: $i] :
      ( ( v2_struct_0 @ X31 )
      | ~ ( v2_pre_topc @ X31 )
      | ~ ( l1_pre_topc @ X31 )
      | ( v2_struct_0 @ X32 )
      | ~ ( m1_pre_topc @ X32 @ X31 )
      | ~ ( m1_subset_1 @ X33 @ ( u1_struct_0 @ X32 ) )
      | ( r1_tmap_1 @ X32 @ X34 @ ( k2_tmap_1 @ X31 @ X34 @ X35 @ X32 ) @ X33 )
      | ( X36 != X33 )
      | ~ ( r1_tmap_1 @ X31 @ X34 @ X35 @ X36 )
      | ~ ( m1_subset_1 @ X36 @ ( u1_struct_0 @ X31 ) )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X31 ) @ ( u1_struct_0 @ X34 ) ) ) )
      | ~ ( v1_funct_2 @ X35 @ ( u1_struct_0 @ X31 ) @ ( u1_struct_0 @ X34 ) )
      | ~ ( v1_funct_1 @ X35 )
      | ~ ( l1_pre_topc @ X34 )
      | ~ ( v2_pre_topc @ X34 )
      | ( v2_struct_0 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t64_tmap_1])).

thf('9',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ( v2_struct_0 @ X34 )
      | ~ ( v2_pre_topc @ X34 )
      | ~ ( l1_pre_topc @ X34 )
      | ~ ( v1_funct_1 @ X35 )
      | ~ ( v1_funct_2 @ X35 @ ( u1_struct_0 @ X31 ) @ ( u1_struct_0 @ X34 ) )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X31 ) @ ( u1_struct_0 @ X34 ) ) ) )
      | ~ ( m1_subset_1 @ X33 @ ( u1_struct_0 @ X31 ) )
      | ~ ( r1_tmap_1 @ X31 @ X34 @ X35 @ X33 )
      | ( r1_tmap_1 @ X32 @ X34 @ ( k2_tmap_1 @ X31 @ X34 @ X35 @ X32 ) @ X33 )
      | ~ ( m1_subset_1 @ X33 @ ( u1_struct_0 @ X32 ) )
      | ~ ( m1_pre_topc @ X32 @ X31 )
      | ( v2_struct_0 @ X32 )
      | ~ ( l1_pre_topc @ X31 )
      | ~ ( v2_pre_topc @ X31 )
      | ( v2_struct_0 @ X31 ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_D )
      | ~ ( v2_pre_topc @ sk_D )
      | ~ ( l1_pre_topc @ sk_D )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ( r1_tmap_1 @ X0 @ sk_A @ ( k2_tmap_1 @ sk_D @ sk_A @ sk_E @ X0 ) @ X1 )
      | ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_D ) )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['7','9'])).

thf('11',plain,(
    m1_pre_topc @ sk_D @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( v2_pre_topc @ B ) ) ) )).

thf('12',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( m1_pre_topc @ X8 @ X9 )
      | ( v2_pre_topc @ X8 )
      | ~ ( l1_pre_topc @ X9 )
      | ~ ( v2_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[cc1_pre_topc])).

thf('13',plain,
    ( ~ ( v2_pre_topc @ sk_B )
    | ~ ( l1_pre_topc @ sk_B )
    | ( v2_pre_topc @ sk_D ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    v2_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['13','14','15'])).

thf('17',plain,(
    m1_pre_topc @ sk_D @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('18',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_pre_topc @ X11 @ X12 )
      | ( l1_pre_topc @ X11 )
      | ~ ( l1_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('19',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( l1_pre_topc @ sk_D ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ( r1_tmap_1 @ X0 @ sk_A @ ( k2_tmap_1 @ sk_D @ sk_A @ sk_E @ X0 ) @ X1 )
      | ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_D ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['10','16','21','22','23','24','25'])).

thf('27',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ~ ( m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_D ) )
        | ( r1_tmap_1 @ X0 @ sk_A @ ( k2_tmap_1 @ sk_D @ sk_A @ sk_E @ X0 ) @ sk_F )
        | ~ ( m1_subset_1 @ sk_F @ ( u1_struct_0 @ X0 ) )
        | ~ ( m1_pre_topc @ X0 @ sk_D )
        | ( v2_struct_0 @ X0 )
        | ( v2_struct_0 @ sk_D ) )
   <= ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F ) ),
    inference('sup-',[status(thm)],['6','26'])).

thf('28',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( r1_tmap_1 @ X0 @ sk_A @ ( k2_tmap_1 @ sk_D @ sk_A @ sk_E @ X0 ) @ sk_F )
        | ~ ( m1_subset_1 @ sk_F @ ( u1_struct_0 @ X0 ) )
        | ~ ( m1_pre_topc @ X0 @ sk_D )
        | ( v2_struct_0 @ X0 )
        | ( v2_struct_0 @ sk_D ) )
   <= ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,
    ( ( ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_C_1 )
      | ~ ( m1_pre_topc @ sk_C_1 @ sk_D )
      | ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C_1 ) @ sk_F )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F ) ),
    inference('sup-',[status(thm)],['4','29'])).

thf('31',plain,(
    m1_pre_topc @ sk_C_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ( ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_C_1 )
      | ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C_1 ) @ sk_F )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,(
    m1_pre_topc @ sk_C_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    m1_pre_topc @ sk_D @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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

thf('36',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ( v2_struct_0 @ X21 )
      | ~ ( v2_pre_topc @ X21 )
      | ~ ( l1_pre_topc @ X21 )
      | ~ ( m1_pre_topc @ X22 @ X23 )
      | ~ ( m1_pre_topc @ X22 @ X24 )
      | ( ( k3_tmap_1 @ X23 @ X21 @ X24 @ X22 @ X25 )
        = ( k2_partfun1 @ ( u1_struct_0 @ X24 ) @ ( u1_struct_0 @ X21 ) @ X25 @ ( u1_struct_0 @ X22 ) ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X24 ) @ ( u1_struct_0 @ X21 ) ) ) )
      | ~ ( v1_funct_2 @ X25 @ ( u1_struct_0 @ X24 ) @ ( u1_struct_0 @ X21 ) )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( m1_pre_topc @ X24 @ X23 )
      | ~ ( l1_pre_topc @ X23 )
      | ~ ( v2_pre_topc @ X23 )
      | ( v2_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[d5_tmap_1])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) )
      | ( ( k3_tmap_1 @ X0 @ sk_A @ sk_D @ X1 @ sk_E )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) @ sk_E @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( m1_pre_topc @ X1 @ sk_D )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ( ( k3_tmap_1 @ X0 @ sk_A @ sk_D @ X1 @ sk_E )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) @ sk_E @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( m1_pre_topc @ X1 @ sk_D )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['37','38','39','40','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ X0 @ sk_E )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) @ sk_E @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['34','42'])).

thf('44',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ X0 @ sk_E )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) @ sk_E @ ( u1_struct_0 @ X0 ) ) )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['43','44','45'])).

thf('47',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) @ sk_E @ ( u1_struct_0 @ sk_C_1 ) ) )
    | ~ ( m1_pre_topc @ sk_C_1 @ sk_D )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['33','46'])).

thf('48',plain,(
    m1_pre_topc @ sk_C_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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

thf('50',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ( v2_struct_0 @ X17 )
      | ~ ( v2_pre_topc @ X17 )
      | ~ ( l1_pre_topc @ X17 )
      | ~ ( m1_pre_topc @ X18 @ X19 )
      | ( ( k2_tmap_1 @ X19 @ X17 @ X20 @ X18 )
        = ( k2_partfun1 @ ( u1_struct_0 @ X19 ) @ ( u1_struct_0 @ X17 ) @ X20 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X19 ) @ ( u1_struct_0 @ X17 ) ) ) )
      | ~ ( v1_funct_2 @ X20 @ ( u1_struct_0 @ X19 ) @ ( u1_struct_0 @ X17 ) )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( l1_pre_topc @ X19 )
      | ~ ( v2_pre_topc @ X19 )
      | ( v2_struct_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[d4_tmap_1])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_D )
      | ~ ( v2_pre_topc @ sk_D )
      | ~ ( l1_pre_topc @ sk_D )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) )
      | ( ( k2_tmap_1 @ sk_D @ sk_A @ sk_E @ X0 )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) @ sk_E @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    v2_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['13','14','15'])).

thf('53',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['19','20'])).

thf('54',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_D )
      | ( ( k2_tmap_1 @ sk_D @ sk_A @ sk_E @ X0 )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) @ sk_E @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['51','52','53','54','55','56','57'])).

thf('59',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C_1 )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) @ sk_E @ ( u1_struct_0 @ sk_C_1 ) ) )
    | ( v2_struct_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['48','58'])).

thf('60',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( ( k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C_1 )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) @ sk_E @ ( u1_struct_0 @ sk_C_1 ) ) ) ),
    inference(clc,[status(thm)],['59','60'])).

thf('62',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,
    ( ( k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C_1 )
    = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) @ sk_E @ ( u1_struct_0 @ sk_C_1 ) ) ),
    inference(clc,[status(thm)],['61','62'])).

thf('64',plain,(
    m1_pre_topc @ sk_C_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E )
      = ( k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C_1 ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['47','63','64'])).

thf('66',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E )
      = ( k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C_1 ) ) ),
    inference(clc,[status(thm)],['65','66'])).

thf('68',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,
    ( ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E )
    = ( k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C_1 ) ),
    inference(clc,[status(thm)],['67','68'])).

thf('70',plain,
    ( ~ ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E ) @ sk_G )
   <= ~ ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E ) @ sk_G ) ),
    inference(split,[status(esa)],['0'])).

thf('71',plain,(
    sk_F = sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,
    ( ~ ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E ) @ sk_F )
   <= ~ ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E ) @ sk_G ) ),
    inference(demod,[status(thm)],['70','71'])).

thf('73',plain,
    ( ~ ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C_1 ) @ sk_F )
   <= ~ ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E ) @ sk_G ) ),
    inference('sup-',[status(thm)],['69','72'])).

thf('74',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C_1 )
      | ( v2_struct_0 @ sk_D ) )
   <= ( ~ ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E ) @ sk_G )
      & ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F ) ) ),
    inference('sup-',[status(thm)],['32','73'])).

thf('75',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,
    ( ( ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_C_1 ) )
   <= ( ~ ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E ) @ sk_G )
      & ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F ) ) ),
    inference(clc,[status(thm)],['74','75'])).

thf('77',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,
    ( ( v2_struct_0 @ sk_C_1 )
   <= ( ~ ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E ) @ sk_G )
      & ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F ) ) ),
    inference(clc,[status(thm)],['76','77'])).

thf('79',plain,(
    ~ ( v2_struct_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,
    ( ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E ) @ sk_G )
    | ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,
    ( ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E ) @ sk_G )
    | ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F ) ),
    inference(split,[status(esa)],['5'])).

thf('82',plain,(
    m1_pre_topc @ sk_D @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    m1_pre_topc @ sk_C_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t1_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( m1_subset_1 @ ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('84',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( m1_pre_topc @ X29 @ X30 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X29 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X30 ) ) )
      | ~ ( l1_pre_topc @ X30 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('85',plain,
    ( ~ ( l1_pre_topc @ sk_D )
    | ( m1_subset_1 @ ( u1_struct_0 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['19','20'])).

thf('87',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['85','86'])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('88',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X5 @ X6 )
      | ( r2_hidden @ X5 @ X6 )
      | ( v1_xboole_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('89',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) )
    | ( r2_hidden @ ( u1_struct_0 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('90',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ X2 )
      | ( r1_tarski @ X3 @ X1 )
      | ( X2
       != ( k1_zfmisc_1 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('91',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X3 @ X1 )
      | ~ ( r2_hidden @ X3 @ ( k1_zfmisc_1 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['90'])).

thf('92',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) )
    | ( r1_tarski @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['89','91'])).

thf(t19_tsep_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ( v1_tsep_1 @ B @ A )
            & ( m1_pre_topc @ B @ A ) )
         => ! [C: $i] :
              ( ( ~ ( v2_struct_0 @ C )
                & ( m1_pre_topc @ C @ A ) )
             => ( ( r1_tarski @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ C ) )
               => ( ( v1_tsep_1 @ B @ C )
                  & ( m1_pre_topc @ B @ C ) ) ) ) ) ) )).

thf('93',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( v1_tsep_1 @ X26 @ X27 )
      | ~ ( m1_pre_topc @ X26 @ X27 )
      | ~ ( r1_tarski @ ( u1_struct_0 @ X26 ) @ ( u1_struct_0 @ X28 ) )
      | ( v1_tsep_1 @ X26 @ X28 )
      | ~ ( m1_pre_topc @ X28 @ X27 )
      | ( v2_struct_0 @ X28 )
      | ~ ( l1_pre_topc @ X27 )
      | ~ ( v2_pre_topc @ X27 )
      | ( v2_struct_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t19_tsep_1])).

thf('94',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ sk_D )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ( v1_tsep_1 @ sk_C_1 @ sk_D )
      | ~ ( m1_pre_topc @ sk_C_1 @ X0 )
      | ~ ( v1_tsep_1 @ sk_C_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,
    ( ~ ( v1_tsep_1 @ sk_C_1 @ sk_B )
    | ~ ( m1_pre_topc @ sk_C_1 @ sk_B )
    | ( v1_tsep_1 @ sk_C_1 @ sk_D )
    | ( v2_struct_0 @ sk_D )
    | ~ ( l1_pre_topc @ sk_B )
    | ~ ( v2_pre_topc @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( v1_xboole_0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['82','94'])).

thf('96',plain,(
    v1_tsep_1 @ sk_C_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    m1_pre_topc @ sk_C_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,
    ( ( v1_tsep_1 @ sk_C_1 @ sk_D )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B )
    | ( v1_xboole_0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['95','96','97','98','99'])).

thf('101',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['85','86'])).

thf('102',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X7 @ X6 )
      | ( v1_xboole_0 @ X7 )
      | ~ ( v1_xboole_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('103',plain,
    ( ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( v1_tsep_1 @ sk_C_1 @ sk_D )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['100','103'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('105',plain,(
    ! [X13: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X13 ) )
      | ~ ( l1_struct_0 @ X13 )
      | ( v2_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('106',plain,
    ( ( v1_tsep_1 @ sk_C_1 @ sk_D )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C_1 )
    | ~ ( l1_struct_0 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['104','105'])).

thf('107',plain,(
    m1_pre_topc @ sk_C_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_pre_topc @ X11 @ X12 )
      | ( l1_pre_topc @ X11 )
      | ~ ( l1_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('109',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( l1_pre_topc @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['107','108'])).

thf('110',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['109','110'])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('112',plain,(
    ! [X10: $i] :
      ( ( l1_struct_0 @ X10 )
      | ~ ( l1_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('113',plain,(
    l1_struct_0 @ sk_C_1 ),
    inference('sup-',[status(thm)],['111','112'])).

thf('114',plain,
    ( ( v1_tsep_1 @ sk_C_1 @ sk_D )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['106','113'])).

thf('115',plain,
    ( ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E )
    = ( k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C_1 ) ),
    inference(clc,[status(thm)],['67','68'])).

thf('116',plain,
    ( ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E ) @ sk_G )
   <= ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E ) @ sk_G ) ),
    inference(split,[status(esa)],['5'])).

thf('117',plain,(
    sk_F = sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,
    ( ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E ) @ sk_F )
   <= ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E ) @ sk_G ) ),
    inference(demod,[status(thm)],['116','117'])).

thf('119',plain,
    ( ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C_1 ) @ sk_F )
   <= ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E ) @ sk_G ) ),
    inference('sup+',[status(thm)],['115','118'])).

thf('120',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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

thf('121',plain,(
    ! [X37: $i,X38: $i,X39: $i,X40: $i,X41: $i,X42: $i] :
      ( ( v2_struct_0 @ X37 )
      | ~ ( v2_pre_topc @ X37 )
      | ~ ( l1_pre_topc @ X37 )
      | ( v2_struct_0 @ X38 )
      | ~ ( v1_tsep_1 @ X38 @ X37 )
      | ~ ( m1_pre_topc @ X38 @ X37 )
      | ~ ( m1_subset_1 @ X39 @ ( u1_struct_0 @ X38 ) )
      | ~ ( r1_tmap_1 @ X38 @ X40 @ ( k2_tmap_1 @ X37 @ X40 @ X41 @ X38 ) @ X39 )
      | ( r1_tmap_1 @ X37 @ X40 @ X41 @ X42 )
      | ( X42 != X39 )
      | ~ ( m1_subset_1 @ X42 @ ( u1_struct_0 @ X37 ) )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X37 ) @ ( u1_struct_0 @ X40 ) ) ) )
      | ~ ( v1_funct_2 @ X41 @ ( u1_struct_0 @ X37 ) @ ( u1_struct_0 @ X40 ) )
      | ~ ( v1_funct_1 @ X41 )
      | ~ ( l1_pre_topc @ X40 )
      | ~ ( v2_pre_topc @ X40 )
      | ( v2_struct_0 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t67_tmap_1])).

thf('122',plain,(
    ! [X37: $i,X38: $i,X39: $i,X40: $i,X41: $i] :
      ( ( v2_struct_0 @ X40 )
      | ~ ( v2_pre_topc @ X40 )
      | ~ ( l1_pre_topc @ X40 )
      | ~ ( v1_funct_1 @ X41 )
      | ~ ( v1_funct_2 @ X41 @ ( u1_struct_0 @ X37 ) @ ( u1_struct_0 @ X40 ) )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X37 ) @ ( u1_struct_0 @ X40 ) ) ) )
      | ~ ( m1_subset_1 @ X39 @ ( u1_struct_0 @ X37 ) )
      | ( r1_tmap_1 @ X37 @ X40 @ X41 @ X39 )
      | ~ ( r1_tmap_1 @ X38 @ X40 @ ( k2_tmap_1 @ X37 @ X40 @ X41 @ X38 ) @ X39 )
      | ~ ( m1_subset_1 @ X39 @ ( u1_struct_0 @ X38 ) )
      | ~ ( m1_pre_topc @ X38 @ X37 )
      | ~ ( v1_tsep_1 @ X38 @ X37 )
      | ( v2_struct_0 @ X38 )
      | ~ ( l1_pre_topc @ X37 )
      | ~ ( v2_pre_topc @ X37 )
      | ( v2_struct_0 @ X37 ) ) ),
    inference(simplify,[status(thm)],['121'])).

thf('123',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_D )
      | ~ ( v2_pre_topc @ sk_D )
      | ~ ( l1_pre_topc @ sk_D )
      | ( v2_struct_0 @ X0 )
      | ~ ( v1_tsep_1 @ X0 @ sk_D )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( r1_tmap_1 @ X0 @ sk_A @ ( k2_tmap_1 @ sk_D @ sk_A @ sk_E @ X0 ) @ X1 )
      | ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_D ) )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['120','122'])).

thf('124',plain,(
    v2_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['13','14','15'])).

thf('125',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['19','20'])).

thf('126',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('128',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('129',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('130',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ X0 )
      | ~ ( v1_tsep_1 @ X0 @ sk_D )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( r1_tmap_1 @ X0 @ sk_A @ ( k2_tmap_1 @ sk_D @ sk_A @ sk_E @ X0 ) @ X1 )
      | ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_D ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['123','124','125','126','127','128','129'])).

thf('131',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_D ) )
      | ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F )
      | ~ ( m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_C_1 ) )
      | ~ ( m1_pre_topc @ sk_C_1 @ sk_D )
      | ~ ( v1_tsep_1 @ sk_C_1 @ sk_D )
      | ( v2_struct_0 @ sk_C_1 )
      | ( v2_struct_0 @ sk_D ) )
   <= ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E ) @ sk_G ) ),
    inference('sup-',[status(thm)],['119','130'])).

thf('132',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('133',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('134',plain,(
    m1_pre_topc @ sk_C_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('135',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F )
      | ~ ( v1_tsep_1 @ sk_C_1 @ sk_D )
      | ( v2_struct_0 @ sk_C_1 )
      | ( v2_struct_0 @ sk_D ) )
   <= ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E ) @ sk_G ) ),
    inference(demod,[status(thm)],['131','132','133','134'])).

thf('136',plain,
    ( ( ( v2_struct_0 @ sk_C_1 )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_C_1 )
      | ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E ) @ sk_G ) ),
    inference('sup-',[status(thm)],['114','135'])).

thf('137',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_C_1 ) )
   <= ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E ) @ sk_G ) ),
    inference(simplify,[status(thm)],['136'])).

thf('138',plain,
    ( ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F )
   <= ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F ) ),
    inference(split,[status(esa)],['0'])).

thf('139',plain,
    ( ( ( v2_struct_0 @ sk_C_1 )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F )
      & ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E ) @ sk_G ) ) ),
    inference('sup-',[status(thm)],['137','138'])).

thf('140',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('141',plain,
    ( ( ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_C_1 ) )
   <= ( ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F )
      & ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E ) @ sk_G ) ) ),
    inference('sup-',[status(thm)],['139','140'])).

thf('142',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('143',plain,
    ( ( ( v2_struct_0 @ sk_C_1 )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F )
      & ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E ) @ sk_G ) ) ),
    inference(clc,[status(thm)],['141','142'])).

thf('144',plain,(
    ~ ( v2_struct_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('145',plain,
    ( ( v2_struct_0 @ sk_B )
   <= ( ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F )
      & ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E ) @ sk_G ) ) ),
    inference(clc,[status(thm)],['143','144'])).

thf('146',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('147',plain,
    ( ~ ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E ) @ sk_G )
    | ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F ) ),
    inference('sup-',[status(thm)],['145','146'])).

thf('148',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','80','81','147'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.slEkXTUu3T
% 0.12/0.34  % Computer   : n006.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 18:44:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.19/0.56  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.19/0.56  % Solved by: fo/fo7.sh
% 0.19/0.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.56  % done 213 iterations in 0.107s
% 0.19/0.56  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.19/0.56  % SZS output start Refutation
% 0.19/0.56  thf(r1_tmap_1_type, type, r1_tmap_1: $i > $i > $i > $i > $o).
% 0.19/0.56  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.19/0.56  thf(k2_tmap_1_type, type, k2_tmap_1: $i > $i > $i > $i > $i).
% 0.19/0.56  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.19/0.56  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.19/0.56  thf(sk_B_type, type, sk_B: $i).
% 0.19/0.56  thf(k3_tmap_1_type, type, k3_tmap_1: $i > $i > $i > $i > $i > $i).
% 0.19/0.56  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.19/0.56  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.56  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.19/0.56  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.19/0.56  thf(k2_partfun1_type, type, k2_partfun1: $i > $i > $i > $i > $i).
% 0.19/0.56  thf(sk_G_type, type, sk_G: $i).
% 0.19/0.56  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.19/0.56  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.19/0.56  thf(sk_E_type, type, sk_E: $i).
% 0.19/0.56  thf(sk_F_type, type, sk_F: $i).
% 0.19/0.56  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.19/0.56  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.19/0.56  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.19/0.56  thf(v1_tsep_1_type, type, v1_tsep_1: $i > $i > $o).
% 0.19/0.56  thf(sk_D_type, type, sk_D: $i).
% 0.19/0.56  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.19/0.56  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.19/0.56  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.19/0.56  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.19/0.56  thf(t87_tmap_1, conjecture,
% 0.19/0.56    (![A:$i]:
% 0.19/0.56     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.19/0.56       ( ![B:$i]:
% 0.19/0.56         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.19/0.56             ( l1_pre_topc @ B ) ) =>
% 0.19/0.56           ( ![C:$i]:
% 0.19/0.56             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ B ) ) =>
% 0.19/0.56               ( ![D:$i]:
% 0.19/0.56                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ B ) ) =>
% 0.19/0.56                   ( ![E:$i]:
% 0.19/0.56                     ( ( ( v1_funct_1 @ E ) & 
% 0.19/0.56                         ( v1_funct_2 @
% 0.19/0.56                           E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ A ) ) & 
% 0.19/0.56                         ( m1_subset_1 @
% 0.19/0.56                           E @ 
% 0.19/0.56                           ( k1_zfmisc_1 @
% 0.19/0.56                             ( k2_zfmisc_1 @
% 0.19/0.56                               ( u1_struct_0 @ D ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.19/0.56                       ( ( ( v1_tsep_1 @ C @ B ) & ( m1_pre_topc @ C @ B ) & 
% 0.19/0.56                           ( m1_pre_topc @ C @ D ) ) =>
% 0.19/0.56                         ( ![F:$i]:
% 0.19/0.56                           ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 0.19/0.56                             ( ![G:$i]:
% 0.19/0.56                               ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) ) =>
% 0.19/0.56                                 ( ( ( F ) = ( G ) ) =>
% 0.19/0.56                                   ( ( r1_tmap_1 @ D @ A @ E @ F ) <=>
% 0.19/0.56                                     ( r1_tmap_1 @
% 0.19/0.56                                       C @ A @ 
% 0.19/0.56                                       ( k3_tmap_1 @ B @ A @ D @ C @ E ) @ G ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.19/0.56  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.56    (~( ![A:$i]:
% 0.19/0.56        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.19/0.56            ( l1_pre_topc @ A ) ) =>
% 0.19/0.56          ( ![B:$i]:
% 0.19/0.56            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.19/0.56                ( l1_pre_topc @ B ) ) =>
% 0.19/0.56              ( ![C:$i]:
% 0.19/0.56                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ B ) ) =>
% 0.19/0.56                  ( ![D:$i]:
% 0.19/0.56                    ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ B ) ) =>
% 0.19/0.56                      ( ![E:$i]:
% 0.19/0.56                        ( ( ( v1_funct_1 @ E ) & 
% 0.19/0.56                            ( v1_funct_2 @
% 0.19/0.56                              E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ A ) ) & 
% 0.19/0.56                            ( m1_subset_1 @
% 0.19/0.56                              E @ 
% 0.19/0.56                              ( k1_zfmisc_1 @
% 0.19/0.56                                ( k2_zfmisc_1 @
% 0.19/0.56                                  ( u1_struct_0 @ D ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.19/0.56                          ( ( ( v1_tsep_1 @ C @ B ) & 
% 0.19/0.56                              ( m1_pre_topc @ C @ B ) & ( m1_pre_topc @ C @ D ) ) =>
% 0.19/0.56                            ( ![F:$i]:
% 0.19/0.56                              ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 0.19/0.56                                ( ![G:$i]:
% 0.19/0.56                                  ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) ) =>
% 0.19/0.56                                    ( ( ( F ) = ( G ) ) =>
% 0.19/0.56                                      ( ( r1_tmap_1 @ D @ A @ E @ F ) <=>
% 0.19/0.56                                        ( r1_tmap_1 @
% 0.19/0.56                                          C @ A @ 
% 0.19/0.56                                          ( k3_tmap_1 @ B @ A @ D @ C @ E ) @ G ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.19/0.56    inference('cnf.neg', [status(esa)], [t87_tmap_1])).
% 0.19/0.56  thf('0', plain,
% 0.19/0.56      ((~ (r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.19/0.56           (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_G)
% 0.19/0.56        | ~ (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F))),
% 0.19/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.56  thf('1', plain,
% 0.19/0.56      (~
% 0.19/0.56       ((r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.19/0.56         (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_G)) | 
% 0.19/0.56       ~ ((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F))),
% 0.19/0.56      inference('split', [status(esa)], ['0'])).
% 0.19/0.56  thf('2', plain, ((m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_C_1))),
% 0.19/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.56  thf('3', plain, (((sk_F) = (sk_G))),
% 0.19/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.56  thf('4', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C_1))),
% 0.19/0.56      inference('demod', [status(thm)], ['2', '3'])).
% 0.19/0.56  thf('5', plain,
% 0.19/0.56      (((r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.19/0.56         (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_G)
% 0.19/0.56        | (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F))),
% 0.19/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.56  thf('6', plain,
% 0.19/0.56      (((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F))
% 0.19/0.56         <= (((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F)))),
% 0.19/0.56      inference('split', [status(esa)], ['5'])).
% 0.19/0.56  thf('7', plain,
% 0.19/0.56      ((m1_subset_1 @ sk_E @ 
% 0.19/0.56        (k1_zfmisc_1 @ 
% 0.19/0.56         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A))))),
% 0.19/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.56  thf(t64_tmap_1, axiom,
% 0.19/0.56    (![A:$i]:
% 0.19/0.56     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.19/0.56       ( ![B:$i]:
% 0.19/0.56         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.19/0.56             ( l1_pre_topc @ B ) ) =>
% 0.19/0.56           ( ![C:$i]:
% 0.19/0.56             ( ( ( v1_funct_1 @ C ) & 
% 0.19/0.56                 ( v1_funct_2 @ C @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 0.19/0.56                 ( m1_subset_1 @
% 0.19/0.56                   C @ 
% 0.19/0.56                   ( k1_zfmisc_1 @
% 0.19/0.56                     ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.19/0.56               ( ![D:$i]:
% 0.19/0.56                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ B ) ) =>
% 0.19/0.56                   ( ![E:$i]:
% 0.19/0.56                     ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) =>
% 0.19/0.56                       ( ![F:$i]:
% 0.19/0.56                         ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 0.19/0.56                           ( ( ( ( E ) = ( F ) ) & 
% 0.19/0.56                               ( r1_tmap_1 @ B @ A @ C @ E ) ) =>
% 0.19/0.56                             ( r1_tmap_1 @
% 0.19/0.56                               D @ A @ ( k2_tmap_1 @ B @ A @ C @ D ) @ F ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.19/0.56  thf('8', plain,
% 0.19/0.56      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 0.19/0.56         ((v2_struct_0 @ X31)
% 0.19/0.56          | ~ (v2_pre_topc @ X31)
% 0.19/0.56          | ~ (l1_pre_topc @ X31)
% 0.19/0.56          | (v2_struct_0 @ X32)
% 0.19/0.56          | ~ (m1_pre_topc @ X32 @ X31)
% 0.19/0.56          | ~ (m1_subset_1 @ X33 @ (u1_struct_0 @ X32))
% 0.19/0.56          | (r1_tmap_1 @ X32 @ X34 @ (k2_tmap_1 @ X31 @ X34 @ X35 @ X32) @ X33)
% 0.19/0.56          | ((X36) != (X33))
% 0.19/0.56          | ~ (r1_tmap_1 @ X31 @ X34 @ X35 @ X36)
% 0.19/0.56          | ~ (m1_subset_1 @ X36 @ (u1_struct_0 @ X31))
% 0.19/0.56          | ~ (m1_subset_1 @ X35 @ 
% 0.19/0.56               (k1_zfmisc_1 @ 
% 0.19/0.56                (k2_zfmisc_1 @ (u1_struct_0 @ X31) @ (u1_struct_0 @ X34))))
% 0.19/0.56          | ~ (v1_funct_2 @ X35 @ (u1_struct_0 @ X31) @ (u1_struct_0 @ X34))
% 0.19/0.56          | ~ (v1_funct_1 @ X35)
% 0.19/0.56          | ~ (l1_pre_topc @ X34)
% 0.19/0.56          | ~ (v2_pre_topc @ X34)
% 0.19/0.56          | (v2_struct_0 @ X34))),
% 0.19/0.56      inference('cnf', [status(esa)], [t64_tmap_1])).
% 0.19/0.56  thf('9', plain,
% 0.19/0.56      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 0.19/0.56         ((v2_struct_0 @ X34)
% 0.19/0.56          | ~ (v2_pre_topc @ X34)
% 0.19/0.56          | ~ (l1_pre_topc @ X34)
% 0.19/0.56          | ~ (v1_funct_1 @ X35)
% 0.19/0.56          | ~ (v1_funct_2 @ X35 @ (u1_struct_0 @ X31) @ (u1_struct_0 @ X34))
% 0.19/0.56          | ~ (m1_subset_1 @ X35 @ 
% 0.19/0.56               (k1_zfmisc_1 @ 
% 0.19/0.56                (k2_zfmisc_1 @ (u1_struct_0 @ X31) @ (u1_struct_0 @ X34))))
% 0.19/0.56          | ~ (m1_subset_1 @ X33 @ (u1_struct_0 @ X31))
% 0.19/0.56          | ~ (r1_tmap_1 @ X31 @ X34 @ X35 @ X33)
% 0.19/0.56          | (r1_tmap_1 @ X32 @ X34 @ (k2_tmap_1 @ X31 @ X34 @ X35 @ X32) @ X33)
% 0.19/0.56          | ~ (m1_subset_1 @ X33 @ (u1_struct_0 @ X32))
% 0.19/0.56          | ~ (m1_pre_topc @ X32 @ X31)
% 0.19/0.56          | (v2_struct_0 @ X32)
% 0.19/0.56          | ~ (l1_pre_topc @ X31)
% 0.19/0.56          | ~ (v2_pre_topc @ X31)
% 0.19/0.56          | (v2_struct_0 @ X31))),
% 0.19/0.56      inference('simplify', [status(thm)], ['8'])).
% 0.19/0.56  thf('10', plain,
% 0.19/0.56      (![X0 : $i, X1 : $i]:
% 0.19/0.56         ((v2_struct_0 @ sk_D)
% 0.19/0.56          | ~ (v2_pre_topc @ sk_D)
% 0.19/0.56          | ~ (l1_pre_topc @ sk_D)
% 0.19/0.56          | (v2_struct_0 @ X0)
% 0.19/0.56          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.19/0.56          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.19/0.56          | (r1_tmap_1 @ X0 @ sk_A @ (k2_tmap_1 @ sk_D @ sk_A @ sk_E @ X0) @ X1)
% 0.19/0.56          | ~ (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ X1)
% 0.19/0.56          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_D))
% 0.19/0.56          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A))
% 0.19/0.56          | ~ (v1_funct_1 @ sk_E)
% 0.19/0.56          | ~ (l1_pre_topc @ sk_A)
% 0.19/0.56          | ~ (v2_pre_topc @ sk_A)
% 0.19/0.56          | (v2_struct_0 @ sk_A))),
% 0.19/0.56      inference('sup-', [status(thm)], ['7', '9'])).
% 0.19/0.56  thf('11', plain, ((m1_pre_topc @ sk_D @ sk_B)),
% 0.19/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.56  thf(cc1_pre_topc, axiom,
% 0.19/0.56    (![A:$i]:
% 0.19/0.56     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.19/0.56       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( v2_pre_topc @ B ) ) ) ))).
% 0.19/0.56  thf('12', plain,
% 0.19/0.56      (![X8 : $i, X9 : $i]:
% 0.19/0.56         (~ (m1_pre_topc @ X8 @ X9)
% 0.19/0.56          | (v2_pre_topc @ X8)
% 0.19/0.56          | ~ (l1_pre_topc @ X9)
% 0.19/0.56          | ~ (v2_pre_topc @ X9))),
% 0.19/0.56      inference('cnf', [status(esa)], [cc1_pre_topc])).
% 0.19/0.56  thf('13', plain,
% 0.19/0.56      ((~ (v2_pre_topc @ sk_B) | ~ (l1_pre_topc @ sk_B) | (v2_pre_topc @ sk_D))),
% 0.19/0.56      inference('sup-', [status(thm)], ['11', '12'])).
% 0.19/0.56  thf('14', plain, ((v2_pre_topc @ sk_B)),
% 0.19/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.56  thf('15', plain, ((l1_pre_topc @ sk_B)),
% 0.19/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.56  thf('16', plain, ((v2_pre_topc @ sk_D)),
% 0.19/0.56      inference('demod', [status(thm)], ['13', '14', '15'])).
% 0.19/0.56  thf('17', plain, ((m1_pre_topc @ sk_D @ sk_B)),
% 0.19/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.56  thf(dt_m1_pre_topc, axiom,
% 0.19/0.56    (![A:$i]:
% 0.19/0.56     ( ( l1_pre_topc @ A ) =>
% 0.19/0.56       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.19/0.56  thf('18', plain,
% 0.19/0.56      (![X11 : $i, X12 : $i]:
% 0.19/0.56         (~ (m1_pre_topc @ X11 @ X12)
% 0.19/0.56          | (l1_pre_topc @ X11)
% 0.19/0.56          | ~ (l1_pre_topc @ X12))),
% 0.19/0.56      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.19/0.56  thf('19', plain, ((~ (l1_pre_topc @ sk_B) | (l1_pre_topc @ sk_D))),
% 0.19/0.56      inference('sup-', [status(thm)], ['17', '18'])).
% 0.19/0.56  thf('20', plain, ((l1_pre_topc @ sk_B)),
% 0.19/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.56  thf('21', plain, ((l1_pre_topc @ sk_D)),
% 0.19/0.56      inference('demod', [status(thm)], ['19', '20'])).
% 0.19/0.56  thf('22', plain,
% 0.19/0.56      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A))),
% 0.19/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.56  thf('23', plain, ((v1_funct_1 @ sk_E)),
% 0.19/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.56  thf('24', plain, ((l1_pre_topc @ sk_A)),
% 0.19/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.56  thf('25', plain, ((v2_pre_topc @ sk_A)),
% 0.19/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.56  thf('26', plain,
% 0.19/0.56      (![X0 : $i, X1 : $i]:
% 0.19/0.56         ((v2_struct_0 @ sk_D)
% 0.19/0.56          | (v2_struct_0 @ X0)
% 0.19/0.56          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.19/0.56          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.19/0.56          | (r1_tmap_1 @ X0 @ sk_A @ (k2_tmap_1 @ sk_D @ sk_A @ sk_E @ X0) @ X1)
% 0.19/0.56          | ~ (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ X1)
% 0.19/0.56          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_D))
% 0.19/0.56          | (v2_struct_0 @ sk_A))),
% 0.19/0.56      inference('demod', [status(thm)],
% 0.19/0.56                ['10', '16', '21', '22', '23', '24', '25'])).
% 0.19/0.56  thf('27', plain,
% 0.19/0.56      ((![X0 : $i]:
% 0.19/0.56          ((v2_struct_0 @ sk_A)
% 0.19/0.56           | ~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_D))
% 0.19/0.56           | (r1_tmap_1 @ X0 @ sk_A @ (k2_tmap_1 @ sk_D @ sk_A @ sk_E @ X0) @ 
% 0.19/0.56              sk_F)
% 0.19/0.56           | ~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ X0))
% 0.19/0.56           | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.19/0.56           | (v2_struct_0 @ X0)
% 0.19/0.56           | (v2_struct_0 @ sk_D)))
% 0.19/0.56         <= (((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F)))),
% 0.19/0.56      inference('sup-', [status(thm)], ['6', '26'])).
% 0.19/0.56  thf('28', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_D))),
% 0.19/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.56  thf('29', plain,
% 0.19/0.56      ((![X0 : $i]:
% 0.19/0.56          ((v2_struct_0 @ sk_A)
% 0.19/0.56           | (r1_tmap_1 @ X0 @ sk_A @ (k2_tmap_1 @ sk_D @ sk_A @ sk_E @ X0) @ 
% 0.19/0.56              sk_F)
% 0.19/0.56           | ~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ X0))
% 0.19/0.56           | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.19/0.56           | (v2_struct_0 @ X0)
% 0.19/0.56           | (v2_struct_0 @ sk_D)))
% 0.19/0.56         <= (((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F)))),
% 0.19/0.56      inference('demod', [status(thm)], ['27', '28'])).
% 0.19/0.56  thf('30', plain,
% 0.19/0.56      ((((v2_struct_0 @ sk_D)
% 0.19/0.56         | (v2_struct_0 @ sk_C_1)
% 0.19/0.56         | ~ (m1_pre_topc @ sk_C_1 @ sk_D)
% 0.19/0.56         | (r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.19/0.56            (k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C_1) @ sk_F)
% 0.19/0.56         | (v2_struct_0 @ sk_A)))
% 0.19/0.56         <= (((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F)))),
% 0.19/0.56      inference('sup-', [status(thm)], ['4', '29'])).
% 0.19/0.56  thf('31', plain, ((m1_pre_topc @ sk_C_1 @ sk_D)),
% 0.19/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.56  thf('32', plain,
% 0.19/0.56      ((((v2_struct_0 @ sk_D)
% 0.19/0.56         | (v2_struct_0 @ sk_C_1)
% 0.19/0.56         | (r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.19/0.56            (k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C_1) @ sk_F)
% 0.19/0.56         | (v2_struct_0 @ sk_A)))
% 0.19/0.56         <= (((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F)))),
% 0.19/0.56      inference('demod', [status(thm)], ['30', '31'])).
% 0.19/0.56  thf('33', plain, ((m1_pre_topc @ sk_C_1 @ sk_B)),
% 0.19/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.56  thf('34', plain, ((m1_pre_topc @ sk_D @ sk_B)),
% 0.19/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.56  thf('35', plain,
% 0.19/0.56      ((m1_subset_1 @ sk_E @ 
% 0.19/0.56        (k1_zfmisc_1 @ 
% 0.19/0.56         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A))))),
% 0.19/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.56  thf(d5_tmap_1, axiom,
% 0.19/0.56    (![A:$i]:
% 0.19/0.56     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.19/0.56       ( ![B:$i]:
% 0.19/0.56         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.19/0.56             ( l1_pre_topc @ B ) ) =>
% 0.19/0.56           ( ![C:$i]:
% 0.19/0.56             ( ( m1_pre_topc @ C @ A ) =>
% 0.19/0.56               ( ![D:$i]:
% 0.19/0.56                 ( ( m1_pre_topc @ D @ A ) =>
% 0.19/0.56                   ( ![E:$i]:
% 0.19/0.56                     ( ( ( v1_funct_1 @ E ) & 
% 0.19/0.56                         ( v1_funct_2 @
% 0.19/0.56                           E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 0.19/0.56                         ( m1_subset_1 @
% 0.19/0.56                           E @ 
% 0.19/0.56                           ( k1_zfmisc_1 @
% 0.19/0.56                             ( k2_zfmisc_1 @
% 0.19/0.56                               ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.19/0.56                       ( ( m1_pre_topc @ D @ C ) =>
% 0.19/0.56                         ( ( k3_tmap_1 @ A @ B @ C @ D @ E ) =
% 0.19/0.56                           ( k2_partfun1 @
% 0.19/0.56                             ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ E @ 
% 0.19/0.56                             ( u1_struct_0 @ D ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.19/0.56  thf('36', plain,
% 0.19/0.56      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 0.19/0.56         ((v2_struct_0 @ X21)
% 0.19/0.56          | ~ (v2_pre_topc @ X21)
% 0.19/0.56          | ~ (l1_pre_topc @ X21)
% 0.19/0.56          | ~ (m1_pre_topc @ X22 @ X23)
% 0.19/0.56          | ~ (m1_pre_topc @ X22 @ X24)
% 0.19/0.56          | ((k3_tmap_1 @ X23 @ X21 @ X24 @ X22 @ X25)
% 0.19/0.56              = (k2_partfun1 @ (u1_struct_0 @ X24) @ (u1_struct_0 @ X21) @ 
% 0.19/0.56                 X25 @ (u1_struct_0 @ X22)))
% 0.19/0.56          | ~ (m1_subset_1 @ X25 @ 
% 0.19/0.56               (k1_zfmisc_1 @ 
% 0.19/0.56                (k2_zfmisc_1 @ (u1_struct_0 @ X24) @ (u1_struct_0 @ X21))))
% 0.19/0.56          | ~ (v1_funct_2 @ X25 @ (u1_struct_0 @ X24) @ (u1_struct_0 @ X21))
% 0.19/0.56          | ~ (v1_funct_1 @ X25)
% 0.19/0.56          | ~ (m1_pre_topc @ X24 @ X23)
% 0.19/0.56          | ~ (l1_pre_topc @ X23)
% 0.19/0.56          | ~ (v2_pre_topc @ X23)
% 0.19/0.56          | (v2_struct_0 @ X23))),
% 0.19/0.56      inference('cnf', [status(esa)], [d5_tmap_1])).
% 0.19/0.56  thf('37', plain,
% 0.19/0.56      (![X0 : $i, X1 : $i]:
% 0.19/0.56         ((v2_struct_0 @ X0)
% 0.19/0.56          | ~ (v2_pre_topc @ X0)
% 0.19/0.56          | ~ (l1_pre_topc @ X0)
% 0.19/0.56          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.19/0.56          | ~ (v1_funct_1 @ sk_E)
% 0.19/0.56          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A))
% 0.19/0.56          | ((k3_tmap_1 @ X0 @ sk_A @ sk_D @ X1 @ sk_E)
% 0.19/0.56              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A) @ 
% 0.19/0.56                 sk_E @ (u1_struct_0 @ X1)))
% 0.19/0.56          | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.19/0.56          | ~ (m1_pre_topc @ X1 @ X0)
% 0.19/0.56          | ~ (l1_pre_topc @ sk_A)
% 0.19/0.56          | ~ (v2_pre_topc @ sk_A)
% 0.19/0.56          | (v2_struct_0 @ sk_A))),
% 0.19/0.56      inference('sup-', [status(thm)], ['35', '36'])).
% 0.19/0.56  thf('38', plain, ((v1_funct_1 @ sk_E)),
% 0.19/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.56  thf('39', plain,
% 0.19/0.56      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A))),
% 0.19/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.56  thf('40', plain, ((l1_pre_topc @ sk_A)),
% 0.19/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.56  thf('41', plain, ((v2_pre_topc @ sk_A)),
% 0.19/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.56  thf('42', plain,
% 0.19/0.56      (![X0 : $i, X1 : $i]:
% 0.19/0.56         ((v2_struct_0 @ X0)
% 0.19/0.56          | ~ (v2_pre_topc @ X0)
% 0.19/0.56          | ~ (l1_pre_topc @ X0)
% 0.19/0.56          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.19/0.56          | ((k3_tmap_1 @ X0 @ sk_A @ sk_D @ X1 @ sk_E)
% 0.19/0.56              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A) @ 
% 0.19/0.56                 sk_E @ (u1_struct_0 @ X1)))
% 0.19/0.56          | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.19/0.56          | ~ (m1_pre_topc @ X1 @ X0)
% 0.19/0.56          | (v2_struct_0 @ sk_A))),
% 0.19/0.56      inference('demod', [status(thm)], ['37', '38', '39', '40', '41'])).
% 0.19/0.56  thf('43', plain,
% 0.19/0.56      (![X0 : $i]:
% 0.19/0.56         ((v2_struct_0 @ sk_A)
% 0.19/0.56          | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.19/0.56          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.19/0.56          | ((k3_tmap_1 @ sk_B @ sk_A @ sk_D @ X0 @ sk_E)
% 0.19/0.56              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A) @ 
% 0.19/0.56                 sk_E @ (u1_struct_0 @ X0)))
% 0.19/0.56          | ~ (l1_pre_topc @ sk_B)
% 0.19/0.56          | ~ (v2_pre_topc @ sk_B)
% 0.19/0.56          | (v2_struct_0 @ sk_B))),
% 0.19/0.56      inference('sup-', [status(thm)], ['34', '42'])).
% 0.19/0.56  thf('44', plain, ((l1_pre_topc @ sk_B)),
% 0.19/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.56  thf('45', plain, ((v2_pre_topc @ sk_B)),
% 0.19/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.56  thf('46', plain,
% 0.19/0.56      (![X0 : $i]:
% 0.19/0.56         ((v2_struct_0 @ sk_A)
% 0.19/0.56          | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.19/0.56          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.19/0.56          | ((k3_tmap_1 @ sk_B @ sk_A @ sk_D @ X0 @ sk_E)
% 0.19/0.56              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A) @ 
% 0.19/0.56                 sk_E @ (u1_struct_0 @ X0)))
% 0.19/0.56          | (v2_struct_0 @ sk_B))),
% 0.19/0.56      inference('demod', [status(thm)], ['43', '44', '45'])).
% 0.19/0.56  thf('47', plain,
% 0.19/0.56      (((v2_struct_0 @ sk_B)
% 0.19/0.56        | ((k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E)
% 0.19/0.56            = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A) @ 
% 0.19/0.56               sk_E @ (u1_struct_0 @ sk_C_1)))
% 0.19/0.56        | ~ (m1_pre_topc @ sk_C_1 @ sk_D)
% 0.19/0.56        | (v2_struct_0 @ sk_A))),
% 0.19/0.56      inference('sup-', [status(thm)], ['33', '46'])).
% 0.19/0.56  thf('48', plain, ((m1_pre_topc @ sk_C_1 @ sk_D)),
% 0.19/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.56  thf('49', plain,
% 0.19/0.56      ((m1_subset_1 @ sk_E @ 
% 0.19/0.56        (k1_zfmisc_1 @ 
% 0.19/0.56         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A))))),
% 0.19/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.56  thf(d4_tmap_1, axiom,
% 0.19/0.56    (![A:$i]:
% 0.19/0.56     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.19/0.56       ( ![B:$i]:
% 0.19/0.56         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.19/0.56             ( l1_pre_topc @ B ) ) =>
% 0.19/0.56           ( ![C:$i]:
% 0.19/0.56             ( ( ( v1_funct_1 @ C ) & 
% 0.19/0.56                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.19/0.56                 ( m1_subset_1 @
% 0.19/0.56                   C @ 
% 0.19/0.56                   ( k1_zfmisc_1 @
% 0.19/0.56                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.19/0.56               ( ![D:$i]:
% 0.19/0.56                 ( ( m1_pre_topc @ D @ A ) =>
% 0.19/0.56                   ( ( k2_tmap_1 @ A @ B @ C @ D ) =
% 0.19/0.56                     ( k2_partfun1 @
% 0.19/0.56                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ 
% 0.19/0.56                       ( u1_struct_0 @ D ) ) ) ) ) ) ) ) ) ))).
% 0.19/0.56  thf('50', plain,
% 0.19/0.56      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.19/0.56         ((v2_struct_0 @ X17)
% 0.19/0.56          | ~ (v2_pre_topc @ X17)
% 0.19/0.56          | ~ (l1_pre_topc @ X17)
% 0.19/0.56          | ~ (m1_pre_topc @ X18 @ X19)
% 0.19/0.56          | ((k2_tmap_1 @ X19 @ X17 @ X20 @ X18)
% 0.19/0.56              = (k2_partfun1 @ (u1_struct_0 @ X19) @ (u1_struct_0 @ X17) @ 
% 0.19/0.56                 X20 @ (u1_struct_0 @ X18)))
% 0.19/0.56          | ~ (m1_subset_1 @ X20 @ 
% 0.19/0.56               (k1_zfmisc_1 @ 
% 0.19/0.56                (k2_zfmisc_1 @ (u1_struct_0 @ X19) @ (u1_struct_0 @ X17))))
% 0.19/0.56          | ~ (v1_funct_2 @ X20 @ (u1_struct_0 @ X19) @ (u1_struct_0 @ X17))
% 0.19/0.56          | ~ (v1_funct_1 @ X20)
% 0.19/0.56          | ~ (l1_pre_topc @ X19)
% 0.19/0.56          | ~ (v2_pre_topc @ X19)
% 0.19/0.56          | (v2_struct_0 @ X19))),
% 0.19/0.56      inference('cnf', [status(esa)], [d4_tmap_1])).
% 0.19/0.56  thf('51', plain,
% 0.19/0.56      (![X0 : $i]:
% 0.19/0.56         ((v2_struct_0 @ sk_D)
% 0.19/0.56          | ~ (v2_pre_topc @ sk_D)
% 0.19/0.56          | ~ (l1_pre_topc @ sk_D)
% 0.19/0.56          | ~ (v1_funct_1 @ sk_E)
% 0.19/0.56          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A))
% 0.19/0.56          | ((k2_tmap_1 @ sk_D @ sk_A @ sk_E @ X0)
% 0.19/0.56              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A) @ 
% 0.19/0.56                 sk_E @ (u1_struct_0 @ X0)))
% 0.19/0.56          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.19/0.56          | ~ (l1_pre_topc @ sk_A)
% 0.19/0.56          | ~ (v2_pre_topc @ sk_A)
% 0.19/0.56          | (v2_struct_0 @ sk_A))),
% 0.19/0.56      inference('sup-', [status(thm)], ['49', '50'])).
% 0.19/0.56  thf('52', plain, ((v2_pre_topc @ sk_D)),
% 0.19/0.56      inference('demod', [status(thm)], ['13', '14', '15'])).
% 0.19/0.56  thf('53', plain, ((l1_pre_topc @ sk_D)),
% 0.19/0.56      inference('demod', [status(thm)], ['19', '20'])).
% 0.19/0.56  thf('54', plain, ((v1_funct_1 @ sk_E)),
% 0.19/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.56  thf('55', plain,
% 0.19/0.56      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A))),
% 0.19/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.56  thf('56', plain, ((l1_pre_topc @ sk_A)),
% 0.19/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.56  thf('57', plain, ((v2_pre_topc @ sk_A)),
% 0.19/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.56  thf('58', plain,
% 0.19/0.56      (![X0 : $i]:
% 0.19/0.56         ((v2_struct_0 @ sk_D)
% 0.19/0.56          | ((k2_tmap_1 @ sk_D @ sk_A @ sk_E @ X0)
% 0.19/0.56              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A) @ 
% 0.19/0.56                 sk_E @ (u1_struct_0 @ X0)))
% 0.19/0.56          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.19/0.56          | (v2_struct_0 @ sk_A))),
% 0.19/0.56      inference('demod', [status(thm)],
% 0.19/0.56                ['51', '52', '53', '54', '55', '56', '57'])).
% 0.19/0.56  thf('59', plain,
% 0.19/0.56      (((v2_struct_0 @ sk_A)
% 0.19/0.56        | ((k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C_1)
% 0.19/0.56            = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A) @ 
% 0.19/0.56               sk_E @ (u1_struct_0 @ sk_C_1)))
% 0.19/0.56        | (v2_struct_0 @ sk_D))),
% 0.19/0.56      inference('sup-', [status(thm)], ['48', '58'])).
% 0.19/0.56  thf('60', plain, (~ (v2_struct_0 @ sk_A)),
% 0.19/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.56  thf('61', plain,
% 0.19/0.56      (((v2_struct_0 @ sk_D)
% 0.19/0.56        | ((k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C_1)
% 0.19/0.56            = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A) @ 
% 0.19/0.56               sk_E @ (u1_struct_0 @ sk_C_1))))),
% 0.19/0.56      inference('clc', [status(thm)], ['59', '60'])).
% 0.19/0.56  thf('62', plain, (~ (v2_struct_0 @ sk_D)),
% 0.19/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.56  thf('63', plain,
% 0.19/0.56      (((k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C_1)
% 0.19/0.56         = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A) @ sk_E @ 
% 0.19/0.56            (u1_struct_0 @ sk_C_1)))),
% 0.19/0.56      inference('clc', [status(thm)], ['61', '62'])).
% 0.19/0.56  thf('64', plain, ((m1_pre_topc @ sk_C_1 @ sk_D)),
% 0.19/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.56  thf('65', plain,
% 0.19/0.56      (((v2_struct_0 @ sk_B)
% 0.19/0.56        | ((k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E)
% 0.19/0.56            = (k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C_1))
% 0.19/0.56        | (v2_struct_0 @ sk_A))),
% 0.19/0.56      inference('demod', [status(thm)], ['47', '63', '64'])).
% 0.19/0.56  thf('66', plain, (~ (v2_struct_0 @ sk_B)),
% 0.19/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.56  thf('67', plain,
% 0.19/0.56      (((v2_struct_0 @ sk_A)
% 0.19/0.56        | ((k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E)
% 0.19/0.56            = (k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C_1)))),
% 0.19/0.56      inference('clc', [status(thm)], ['65', '66'])).
% 0.19/0.56  thf('68', plain, (~ (v2_struct_0 @ sk_A)),
% 0.19/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.56  thf('69', plain,
% 0.19/0.56      (((k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E)
% 0.19/0.56         = (k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C_1))),
% 0.19/0.56      inference('clc', [status(thm)], ['67', '68'])).
% 0.19/0.56  thf('70', plain,
% 0.19/0.56      ((~ (r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.19/0.56           (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_G))
% 0.19/0.56         <= (~
% 0.19/0.56             ((r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.19/0.56               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_G)))),
% 0.19/0.56      inference('split', [status(esa)], ['0'])).
% 0.19/0.56  thf('71', plain, (((sk_F) = (sk_G))),
% 0.19/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.56  thf('72', plain,
% 0.19/0.56      ((~ (r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.19/0.56           (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_F))
% 0.19/0.56         <= (~
% 0.19/0.56             ((r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.19/0.56               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_G)))),
% 0.19/0.56      inference('demod', [status(thm)], ['70', '71'])).
% 0.19/0.56  thf('73', plain,
% 0.19/0.56      ((~ (r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.19/0.56           (k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C_1) @ sk_F))
% 0.19/0.56         <= (~
% 0.19/0.56             ((r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.19/0.56               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_G)))),
% 0.19/0.56      inference('sup-', [status(thm)], ['69', '72'])).
% 0.19/0.56  thf('74', plain,
% 0.19/0.56      ((((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_C_1) | (v2_struct_0 @ sk_D)))
% 0.19/0.56         <= (~
% 0.19/0.56             ((r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.19/0.56               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_G)) & 
% 0.19/0.56             ((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F)))),
% 0.19/0.56      inference('sup-', [status(thm)], ['32', '73'])).
% 0.19/0.56  thf('75', plain, (~ (v2_struct_0 @ sk_A)),
% 0.19/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.56  thf('76', plain,
% 0.19/0.56      ((((v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_C_1)))
% 0.19/0.56         <= (~
% 0.19/0.56             ((r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.19/0.56               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_G)) & 
% 0.19/0.56             ((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F)))),
% 0.19/0.56      inference('clc', [status(thm)], ['74', '75'])).
% 0.19/0.56  thf('77', plain, (~ (v2_struct_0 @ sk_D)),
% 0.19/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.56  thf('78', plain,
% 0.19/0.56      (((v2_struct_0 @ sk_C_1))
% 0.19/0.56         <= (~
% 0.19/0.56             ((r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.19/0.56               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_G)) & 
% 0.19/0.56             ((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F)))),
% 0.19/0.56      inference('clc', [status(thm)], ['76', '77'])).
% 0.19/0.56  thf('79', plain, (~ (v2_struct_0 @ sk_C_1)),
% 0.19/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.56  thf('80', plain,
% 0.19/0.56      (((r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.19/0.56         (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_G)) | 
% 0.19/0.56       ~ ((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F))),
% 0.19/0.56      inference('sup-', [status(thm)], ['78', '79'])).
% 0.19/0.56  thf('81', plain,
% 0.19/0.56      (((r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.19/0.56         (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_G)) | 
% 0.19/0.56       ((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F))),
% 0.19/0.56      inference('split', [status(esa)], ['5'])).
% 0.19/0.56  thf('82', plain, ((m1_pre_topc @ sk_D @ sk_B)),
% 0.19/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.56  thf('83', plain, ((m1_pre_topc @ sk_C_1 @ sk_D)),
% 0.19/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.56  thf(t1_tsep_1, axiom,
% 0.19/0.56    (![A:$i]:
% 0.19/0.56     ( ( l1_pre_topc @ A ) =>
% 0.19/0.56       ( ![B:$i]:
% 0.19/0.56         ( ( m1_pre_topc @ B @ A ) =>
% 0.19/0.56           ( m1_subset_1 @
% 0.19/0.56             ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.19/0.56  thf('84', plain,
% 0.19/0.56      (![X29 : $i, X30 : $i]:
% 0.19/0.56         (~ (m1_pre_topc @ X29 @ X30)
% 0.19/0.56          | (m1_subset_1 @ (u1_struct_0 @ X29) @ 
% 0.19/0.56             (k1_zfmisc_1 @ (u1_struct_0 @ X30)))
% 0.19/0.56          | ~ (l1_pre_topc @ X30))),
% 0.19/0.56      inference('cnf', [status(esa)], [t1_tsep_1])).
% 0.19/0.56  thf('85', plain,
% 0.19/0.56      ((~ (l1_pre_topc @ sk_D)
% 0.19/0.56        | (m1_subset_1 @ (u1_struct_0 @ sk_C_1) @ 
% 0.19/0.56           (k1_zfmisc_1 @ (u1_struct_0 @ sk_D))))),
% 0.19/0.56      inference('sup-', [status(thm)], ['83', '84'])).
% 0.19/0.56  thf('86', plain, ((l1_pre_topc @ sk_D)),
% 0.19/0.56      inference('demod', [status(thm)], ['19', '20'])).
% 0.19/0.56  thf('87', plain,
% 0.19/0.56      ((m1_subset_1 @ (u1_struct_0 @ sk_C_1) @ 
% 0.19/0.56        (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))),
% 0.19/0.56      inference('demod', [status(thm)], ['85', '86'])).
% 0.19/0.56  thf(d2_subset_1, axiom,
% 0.19/0.56    (![A:$i,B:$i]:
% 0.19/0.56     ( ( ( v1_xboole_0 @ A ) =>
% 0.19/0.56         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.19/0.56       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.19/0.56         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.19/0.56  thf('88', plain,
% 0.19/0.56      (![X5 : $i, X6 : $i]:
% 0.19/0.56         (~ (m1_subset_1 @ X5 @ X6)
% 0.19/0.56          | (r2_hidden @ X5 @ X6)
% 0.19/0.56          | (v1_xboole_0 @ X6))),
% 0.19/0.56      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.19/0.56  thf('89', plain,
% 0.19/0.56      (((v1_xboole_0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))
% 0.19/0.56        | (r2_hidden @ (u1_struct_0 @ sk_C_1) @ 
% 0.19/0.56           (k1_zfmisc_1 @ (u1_struct_0 @ sk_D))))),
% 0.19/0.56      inference('sup-', [status(thm)], ['87', '88'])).
% 0.19/0.56  thf(d1_zfmisc_1, axiom,
% 0.19/0.56    (![A:$i,B:$i]:
% 0.19/0.56     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.19/0.56       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.19/0.56  thf('90', plain,
% 0.19/0.56      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.19/0.56         (~ (r2_hidden @ X3 @ X2)
% 0.19/0.56          | (r1_tarski @ X3 @ X1)
% 0.19/0.56          | ((X2) != (k1_zfmisc_1 @ X1)))),
% 0.19/0.56      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.19/0.56  thf('91', plain,
% 0.19/0.56      (![X1 : $i, X3 : $i]:
% 0.19/0.56         ((r1_tarski @ X3 @ X1) | ~ (r2_hidden @ X3 @ (k1_zfmisc_1 @ X1)))),
% 0.19/0.56      inference('simplify', [status(thm)], ['90'])).
% 0.19/0.56  thf('92', plain,
% 0.19/0.56      (((v1_xboole_0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))
% 0.19/0.56        | (r1_tarski @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_D)))),
% 0.19/0.56      inference('sup-', [status(thm)], ['89', '91'])).
% 0.19/0.56  thf(t19_tsep_1, axiom,
% 0.19/0.56    (![A:$i]:
% 0.19/0.56     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.19/0.56       ( ![B:$i]:
% 0.19/0.56         ( ( ( v1_tsep_1 @ B @ A ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.19/0.56           ( ![C:$i]:
% 0.19/0.56             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.19/0.56               ( ( r1_tarski @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ C ) ) =>
% 0.19/0.56                 ( ( v1_tsep_1 @ B @ C ) & ( m1_pre_topc @ B @ C ) ) ) ) ) ) ) ))).
% 0.19/0.56  thf('93', plain,
% 0.19/0.56      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.19/0.56         (~ (v1_tsep_1 @ X26 @ X27)
% 0.19/0.56          | ~ (m1_pre_topc @ X26 @ X27)
% 0.19/0.56          | ~ (r1_tarski @ (u1_struct_0 @ X26) @ (u1_struct_0 @ X28))
% 0.19/0.56          | (v1_tsep_1 @ X26 @ X28)
% 0.19/0.56          | ~ (m1_pre_topc @ X28 @ X27)
% 0.19/0.56          | (v2_struct_0 @ X28)
% 0.19/0.56          | ~ (l1_pre_topc @ X27)
% 0.19/0.56          | ~ (v2_pre_topc @ X27)
% 0.19/0.56          | (v2_struct_0 @ X27))),
% 0.19/0.56      inference('cnf', [status(esa)], [t19_tsep_1])).
% 0.19/0.56  thf('94', plain,
% 0.19/0.56      (![X0 : $i]:
% 0.19/0.56         ((v1_xboole_0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))
% 0.19/0.56          | (v2_struct_0 @ X0)
% 0.19/0.56          | ~ (v2_pre_topc @ X0)
% 0.19/0.56          | ~ (l1_pre_topc @ X0)
% 0.19/0.56          | (v2_struct_0 @ sk_D)
% 0.19/0.56          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.19/0.56          | (v1_tsep_1 @ sk_C_1 @ sk_D)
% 0.19/0.56          | ~ (m1_pre_topc @ sk_C_1 @ X0)
% 0.19/0.56          | ~ (v1_tsep_1 @ sk_C_1 @ X0))),
% 0.19/0.56      inference('sup-', [status(thm)], ['92', '93'])).
% 0.19/0.56  thf('95', plain,
% 0.19/0.56      ((~ (v1_tsep_1 @ sk_C_1 @ sk_B)
% 0.19/0.56        | ~ (m1_pre_topc @ sk_C_1 @ sk_B)
% 0.19/0.56        | (v1_tsep_1 @ sk_C_1 @ sk_D)
% 0.19/0.56        | (v2_struct_0 @ sk_D)
% 0.19/0.56        | ~ (l1_pre_topc @ sk_B)
% 0.19/0.56        | ~ (v2_pre_topc @ sk_B)
% 0.19/0.56        | (v2_struct_0 @ sk_B)
% 0.19/0.56        | (v1_xboole_0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D))))),
% 0.19/0.56      inference('sup-', [status(thm)], ['82', '94'])).
% 0.19/0.56  thf('96', plain, ((v1_tsep_1 @ sk_C_1 @ sk_B)),
% 0.19/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.56  thf('97', plain, ((m1_pre_topc @ sk_C_1 @ sk_B)),
% 0.19/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.56  thf('98', plain, ((l1_pre_topc @ sk_B)),
% 0.19/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.56  thf('99', plain, ((v2_pre_topc @ sk_B)),
% 0.19/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.56  thf('100', plain,
% 0.19/0.56      (((v1_tsep_1 @ sk_C_1 @ sk_D)
% 0.19/0.56        | (v2_struct_0 @ sk_D)
% 0.19/0.56        | (v2_struct_0 @ sk_B)
% 0.19/0.56        | (v1_xboole_0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D))))),
% 0.19/0.56      inference('demod', [status(thm)], ['95', '96', '97', '98', '99'])).
% 0.19/0.56  thf('101', plain,
% 0.19/0.56      ((m1_subset_1 @ (u1_struct_0 @ sk_C_1) @ 
% 0.19/0.56        (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))),
% 0.19/0.56      inference('demod', [status(thm)], ['85', '86'])).
% 0.19/0.56  thf('102', plain,
% 0.19/0.56      (![X6 : $i, X7 : $i]:
% 0.19/0.56         (~ (m1_subset_1 @ X7 @ X6) | (v1_xboole_0 @ X7) | ~ (v1_xboole_0 @ X6))),
% 0.19/0.56      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.19/0.56  thf('103', plain,
% 0.19/0.56      ((~ (v1_xboole_0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))
% 0.19/0.56        | (v1_xboole_0 @ (u1_struct_0 @ sk_C_1)))),
% 0.19/0.56      inference('sup-', [status(thm)], ['101', '102'])).
% 0.19/0.56  thf('104', plain,
% 0.19/0.56      (((v2_struct_0 @ sk_B)
% 0.19/0.56        | (v2_struct_0 @ sk_D)
% 0.19/0.56        | (v1_tsep_1 @ sk_C_1 @ sk_D)
% 0.19/0.56        | (v1_xboole_0 @ (u1_struct_0 @ sk_C_1)))),
% 0.19/0.56      inference('sup-', [status(thm)], ['100', '103'])).
% 0.19/0.56  thf(fc2_struct_0, axiom,
% 0.19/0.56    (![A:$i]:
% 0.19/0.56     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.19/0.56       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.19/0.56  thf('105', plain,
% 0.19/0.56      (![X13 : $i]:
% 0.19/0.56         (~ (v1_xboole_0 @ (u1_struct_0 @ X13))
% 0.19/0.56          | ~ (l1_struct_0 @ X13)
% 0.19/0.56          | (v2_struct_0 @ X13))),
% 0.19/0.56      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.19/0.56  thf('106', plain,
% 0.19/0.56      (((v1_tsep_1 @ sk_C_1 @ sk_D)
% 0.19/0.56        | (v2_struct_0 @ sk_D)
% 0.19/0.56        | (v2_struct_0 @ sk_B)
% 0.19/0.56        | (v2_struct_0 @ sk_C_1)
% 0.19/0.56        | ~ (l1_struct_0 @ sk_C_1))),
% 0.19/0.56      inference('sup-', [status(thm)], ['104', '105'])).
% 0.19/0.56  thf('107', plain, ((m1_pre_topc @ sk_C_1 @ sk_B)),
% 0.19/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.56  thf('108', plain,
% 0.19/0.56      (![X11 : $i, X12 : $i]:
% 0.19/0.56         (~ (m1_pre_topc @ X11 @ X12)
% 0.19/0.56          | (l1_pre_topc @ X11)
% 0.19/0.56          | ~ (l1_pre_topc @ X12))),
% 0.19/0.56      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.19/0.56  thf('109', plain, ((~ (l1_pre_topc @ sk_B) | (l1_pre_topc @ sk_C_1))),
% 0.19/0.56      inference('sup-', [status(thm)], ['107', '108'])).
% 0.19/0.56  thf('110', plain, ((l1_pre_topc @ sk_B)),
% 0.19/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.56  thf('111', plain, ((l1_pre_topc @ sk_C_1)),
% 0.19/0.56      inference('demod', [status(thm)], ['109', '110'])).
% 0.19/0.56  thf(dt_l1_pre_topc, axiom,
% 0.19/0.56    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.19/0.56  thf('112', plain,
% 0.19/0.56      (![X10 : $i]: ((l1_struct_0 @ X10) | ~ (l1_pre_topc @ X10))),
% 0.19/0.56      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.19/0.56  thf('113', plain, ((l1_struct_0 @ sk_C_1)),
% 0.19/0.56      inference('sup-', [status(thm)], ['111', '112'])).
% 0.19/0.56  thf('114', plain,
% 0.19/0.56      (((v1_tsep_1 @ sk_C_1 @ sk_D)
% 0.19/0.56        | (v2_struct_0 @ sk_D)
% 0.19/0.56        | (v2_struct_0 @ sk_B)
% 0.19/0.56        | (v2_struct_0 @ sk_C_1))),
% 0.19/0.56      inference('demod', [status(thm)], ['106', '113'])).
% 0.19/0.56  thf('115', plain,
% 0.19/0.56      (((k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E)
% 0.19/0.56         = (k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C_1))),
% 0.19/0.56      inference('clc', [status(thm)], ['67', '68'])).
% 0.19/0.56  thf('116', plain,
% 0.19/0.56      (((r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.19/0.56         (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_G))
% 0.19/0.56         <= (((r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.19/0.56               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_G)))),
% 0.19/0.56      inference('split', [status(esa)], ['5'])).
% 0.19/0.56  thf('117', plain, (((sk_F) = (sk_G))),
% 0.19/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.56  thf('118', plain,
% 0.19/0.56      (((r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.19/0.56         (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_F))
% 0.19/0.56         <= (((r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.19/0.56               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_G)))),
% 0.19/0.56      inference('demod', [status(thm)], ['116', '117'])).
% 0.19/0.56  thf('119', plain,
% 0.19/0.56      (((r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.19/0.56         (k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C_1) @ sk_F))
% 0.19/0.56         <= (((r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.19/0.56               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_G)))),
% 0.19/0.56      inference('sup+', [status(thm)], ['115', '118'])).
% 0.19/0.56  thf('120', plain,
% 0.19/0.56      ((m1_subset_1 @ sk_E @ 
% 0.19/0.56        (k1_zfmisc_1 @ 
% 0.19/0.56         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A))))),
% 0.19/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.56  thf(t67_tmap_1, axiom,
% 0.19/0.56    (![A:$i]:
% 0.19/0.56     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.19/0.56       ( ![B:$i]:
% 0.19/0.56         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.19/0.56             ( l1_pre_topc @ B ) ) =>
% 0.19/0.56           ( ![C:$i]:
% 0.19/0.56             ( ( ( v1_funct_1 @ C ) & 
% 0.19/0.56                 ( v1_funct_2 @ C @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 0.19/0.56                 ( m1_subset_1 @
% 0.19/0.56                   C @ 
% 0.19/0.56                   ( k1_zfmisc_1 @
% 0.19/0.56                     ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.19/0.56               ( ![D:$i]:
% 0.19/0.56                 ( ( ( ~( v2_struct_0 @ D ) ) & ( v1_tsep_1 @ D @ B ) & 
% 0.19/0.56                     ( m1_pre_topc @ D @ B ) ) =>
% 0.19/0.56                   ( ![E:$i]:
% 0.19/0.56                     ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) =>
% 0.19/0.56                       ( ![F:$i]:
% 0.19/0.56                         ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 0.19/0.56                           ( ( ( E ) = ( F ) ) =>
% 0.19/0.56                             ( ( r1_tmap_1 @ B @ A @ C @ E ) <=>
% 0.19/0.56                               ( r1_tmap_1 @
% 0.19/0.56                                 D @ A @ ( k2_tmap_1 @ B @ A @ C @ D ) @ F ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.19/0.56  thf('121', plain,
% 0.19/0.56      (![X37 : $i, X38 : $i, X39 : $i, X40 : $i, X41 : $i, X42 : $i]:
% 0.19/0.56         ((v2_struct_0 @ X37)
% 0.19/0.56          | ~ (v2_pre_topc @ X37)
% 0.19/0.56          | ~ (l1_pre_topc @ X37)
% 0.19/0.56          | (v2_struct_0 @ X38)
% 0.19/0.56          | ~ (v1_tsep_1 @ X38 @ X37)
% 0.19/0.56          | ~ (m1_pre_topc @ X38 @ X37)
% 0.19/0.56          | ~ (m1_subset_1 @ X39 @ (u1_struct_0 @ X38))
% 0.19/0.56          | ~ (r1_tmap_1 @ X38 @ X40 @ (k2_tmap_1 @ X37 @ X40 @ X41 @ X38) @ 
% 0.19/0.56               X39)
% 0.19/0.56          | (r1_tmap_1 @ X37 @ X40 @ X41 @ X42)
% 0.19/0.56          | ((X42) != (X39))
% 0.19/0.56          | ~ (m1_subset_1 @ X42 @ (u1_struct_0 @ X37))
% 0.19/0.56          | ~ (m1_subset_1 @ X41 @ 
% 0.19/0.56               (k1_zfmisc_1 @ 
% 0.19/0.56                (k2_zfmisc_1 @ (u1_struct_0 @ X37) @ (u1_struct_0 @ X40))))
% 0.19/0.56          | ~ (v1_funct_2 @ X41 @ (u1_struct_0 @ X37) @ (u1_struct_0 @ X40))
% 0.19/0.56          | ~ (v1_funct_1 @ X41)
% 0.19/0.56          | ~ (l1_pre_topc @ X40)
% 0.19/0.56          | ~ (v2_pre_topc @ X40)
% 0.19/0.56          | (v2_struct_0 @ X40))),
% 0.19/0.56      inference('cnf', [status(esa)], [t67_tmap_1])).
% 0.19/0.56  thf('122', plain,
% 0.19/0.56      (![X37 : $i, X38 : $i, X39 : $i, X40 : $i, X41 : $i]:
% 0.19/0.56         ((v2_struct_0 @ X40)
% 0.19/0.56          | ~ (v2_pre_topc @ X40)
% 0.19/0.56          | ~ (l1_pre_topc @ X40)
% 0.19/0.56          | ~ (v1_funct_1 @ X41)
% 0.19/0.56          | ~ (v1_funct_2 @ X41 @ (u1_struct_0 @ X37) @ (u1_struct_0 @ X40))
% 0.19/0.56          | ~ (m1_subset_1 @ X41 @ 
% 0.19/0.56               (k1_zfmisc_1 @ 
% 0.19/0.56                (k2_zfmisc_1 @ (u1_struct_0 @ X37) @ (u1_struct_0 @ X40))))
% 0.19/0.56          | ~ (m1_subset_1 @ X39 @ (u1_struct_0 @ X37))
% 0.19/0.56          | (r1_tmap_1 @ X37 @ X40 @ X41 @ X39)
% 0.19/0.56          | ~ (r1_tmap_1 @ X38 @ X40 @ (k2_tmap_1 @ X37 @ X40 @ X41 @ X38) @ 
% 0.19/0.56               X39)
% 0.19/0.56          | ~ (m1_subset_1 @ X39 @ (u1_struct_0 @ X38))
% 0.19/0.56          | ~ (m1_pre_topc @ X38 @ X37)
% 0.19/0.56          | ~ (v1_tsep_1 @ X38 @ X37)
% 0.19/0.56          | (v2_struct_0 @ X38)
% 0.19/0.56          | ~ (l1_pre_topc @ X37)
% 0.19/0.56          | ~ (v2_pre_topc @ X37)
% 0.19/0.56          | (v2_struct_0 @ X37))),
% 0.19/0.56      inference('simplify', [status(thm)], ['121'])).
% 0.19/0.56  thf('123', plain,
% 0.19/0.56      (![X0 : $i, X1 : $i]:
% 0.19/0.56         ((v2_struct_0 @ sk_D)
% 0.19/0.56          | ~ (v2_pre_topc @ sk_D)
% 0.19/0.56          | ~ (l1_pre_topc @ sk_D)
% 0.19/0.56          | (v2_struct_0 @ X0)
% 0.19/0.56          | ~ (v1_tsep_1 @ X0 @ sk_D)
% 0.19/0.56          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.19/0.56          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.19/0.56          | ~ (r1_tmap_1 @ X0 @ sk_A @ (k2_tmap_1 @ sk_D @ sk_A @ sk_E @ X0) @ 
% 0.19/0.56               X1)
% 0.19/0.56          | (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ X1)
% 0.19/0.56          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_D))
% 0.19/0.56          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A))
% 0.19/0.56          | ~ (v1_funct_1 @ sk_E)
% 0.19/0.56          | ~ (l1_pre_topc @ sk_A)
% 0.19/0.56          | ~ (v2_pre_topc @ sk_A)
% 0.19/0.56          | (v2_struct_0 @ sk_A))),
% 0.19/0.56      inference('sup-', [status(thm)], ['120', '122'])).
% 0.19/0.56  thf('124', plain, ((v2_pre_topc @ sk_D)),
% 0.19/0.56      inference('demod', [status(thm)], ['13', '14', '15'])).
% 0.19/0.56  thf('125', plain, ((l1_pre_topc @ sk_D)),
% 0.19/0.56      inference('demod', [status(thm)], ['19', '20'])).
% 0.19/0.56  thf('126', plain,
% 0.19/0.56      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A))),
% 0.19/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.56  thf('127', plain, ((v1_funct_1 @ sk_E)),
% 0.19/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.56  thf('128', plain, ((l1_pre_topc @ sk_A)),
% 0.19/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.56  thf('129', plain, ((v2_pre_topc @ sk_A)),
% 0.19/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.56  thf('130', plain,
% 0.19/0.56      (![X0 : $i, X1 : $i]:
% 0.19/0.56         ((v2_struct_0 @ sk_D)
% 0.19/0.56          | (v2_struct_0 @ X0)
% 0.19/0.56          | ~ (v1_tsep_1 @ X0 @ sk_D)
% 0.19/0.56          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.19/0.56          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.19/0.56          | ~ (r1_tmap_1 @ X0 @ sk_A @ (k2_tmap_1 @ sk_D @ sk_A @ sk_E @ X0) @ 
% 0.19/0.56               X1)
% 0.19/0.56          | (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ X1)
% 0.19/0.56          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_D))
% 0.19/0.56          | (v2_struct_0 @ sk_A))),
% 0.19/0.56      inference('demod', [status(thm)],
% 0.19/0.56                ['123', '124', '125', '126', '127', '128', '129'])).
% 0.19/0.56  thf('131', plain,
% 0.19/0.56      ((((v2_struct_0 @ sk_A)
% 0.19/0.56         | ~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_D))
% 0.19/0.56         | (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F)
% 0.19/0.56         | ~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C_1))
% 0.19/0.56         | ~ (m1_pre_topc @ sk_C_1 @ sk_D)
% 0.19/0.56         | ~ (v1_tsep_1 @ sk_C_1 @ sk_D)
% 0.19/0.56         | (v2_struct_0 @ sk_C_1)
% 0.19/0.56         | (v2_struct_0 @ sk_D)))
% 0.19/0.56         <= (((r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.19/0.56               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_G)))),
% 0.19/0.56      inference('sup-', [status(thm)], ['119', '130'])).
% 0.19/0.56  thf('132', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_D))),
% 0.19/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.56  thf('133', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C_1))),
% 0.19/0.56      inference('demod', [status(thm)], ['2', '3'])).
% 0.19/0.56  thf('134', plain, ((m1_pre_topc @ sk_C_1 @ sk_D)),
% 0.19/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.56  thf('135', plain,
% 0.19/0.56      ((((v2_struct_0 @ sk_A)
% 0.19/0.56         | (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F)
% 0.19/0.56         | ~ (v1_tsep_1 @ sk_C_1 @ sk_D)
% 0.19/0.56         | (v2_struct_0 @ sk_C_1)
% 0.19/0.56         | (v2_struct_0 @ sk_D)))
% 0.19/0.56         <= (((r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.19/0.56               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_G)))),
% 0.19/0.56      inference('demod', [status(thm)], ['131', '132', '133', '134'])).
% 0.19/0.56  thf('136', plain,
% 0.19/0.56      ((((v2_struct_0 @ sk_C_1)
% 0.19/0.56         | (v2_struct_0 @ sk_B)
% 0.19/0.56         | (v2_struct_0 @ sk_D)
% 0.19/0.56         | (v2_struct_0 @ sk_D)
% 0.19/0.56         | (v2_struct_0 @ sk_C_1)
% 0.19/0.56         | (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F)
% 0.19/0.56         | (v2_struct_0 @ sk_A)))
% 0.19/0.56         <= (((r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.19/0.56               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_G)))),
% 0.19/0.56      inference('sup-', [status(thm)], ['114', '135'])).
% 0.19/0.56  thf('137', plain,
% 0.19/0.56      ((((v2_struct_0 @ sk_A)
% 0.19/0.56         | (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F)
% 0.19/0.56         | (v2_struct_0 @ sk_D)
% 0.19/0.56         | (v2_struct_0 @ sk_B)
% 0.19/0.56         | (v2_struct_0 @ sk_C_1)))
% 0.19/0.56         <= (((r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.19/0.56               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_G)))),
% 0.19/0.56      inference('simplify', [status(thm)], ['136'])).
% 0.19/0.56  thf('138', plain,
% 0.19/0.56      ((~ (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F))
% 0.19/0.56         <= (~ ((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F)))),
% 0.19/0.56      inference('split', [status(esa)], ['0'])).
% 0.19/0.56  thf('139', plain,
% 0.19/0.56      ((((v2_struct_0 @ sk_C_1)
% 0.19/0.56         | (v2_struct_0 @ sk_B)
% 0.19/0.56         | (v2_struct_0 @ sk_D)
% 0.19/0.56         | (v2_struct_0 @ sk_A)))
% 0.19/0.56         <= (~ ((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F)) & 
% 0.19/0.56             ((r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.19/0.56               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_G)))),
% 0.19/0.56      inference('sup-', [status(thm)], ['137', '138'])).
% 0.19/0.56  thf('140', plain, (~ (v2_struct_0 @ sk_A)),
% 0.19/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.56  thf('141', plain,
% 0.19/0.56      ((((v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_C_1)))
% 0.19/0.56         <= (~ ((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F)) & 
% 0.19/0.56             ((r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.19/0.56               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_G)))),
% 0.19/0.56      inference('sup-', [status(thm)], ['139', '140'])).
% 0.19/0.56  thf('142', plain, (~ (v2_struct_0 @ sk_D)),
% 0.19/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.56  thf('143', plain,
% 0.19/0.56      ((((v2_struct_0 @ sk_C_1) | (v2_struct_0 @ sk_B)))
% 0.19/0.56         <= (~ ((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F)) & 
% 0.19/0.56             ((r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.19/0.56               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_G)))),
% 0.19/0.56      inference('clc', [status(thm)], ['141', '142'])).
% 0.19/0.56  thf('144', plain, (~ (v2_struct_0 @ sk_C_1)),
% 0.19/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.56  thf('145', plain,
% 0.19/0.56      (((v2_struct_0 @ sk_B))
% 0.19/0.56         <= (~ ((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F)) & 
% 0.19/0.56             ((r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.19/0.56               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_G)))),
% 0.19/0.56      inference('clc', [status(thm)], ['143', '144'])).
% 0.19/0.56  thf('146', plain, (~ (v2_struct_0 @ sk_B)),
% 0.19/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.56  thf('147', plain,
% 0.19/0.56      (~
% 0.19/0.56       ((r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.19/0.56         (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_G)) | 
% 0.19/0.56       ((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F))),
% 0.19/0.56      inference('sup-', [status(thm)], ['145', '146'])).
% 0.19/0.56  thf('148', plain, ($false),
% 0.19/0.56      inference('sat_resolution*', [status(thm)], ['1', '80', '81', '147'])).
% 0.19/0.56  
% 0.19/0.56  % SZS output end Refutation
% 0.19/0.56  
% 0.19/0.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
