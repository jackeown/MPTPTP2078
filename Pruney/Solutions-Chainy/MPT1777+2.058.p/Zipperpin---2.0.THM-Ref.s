%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.pfDh7W0j9C

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:10:35 EST 2020

% Result     : Theorem 1.12s
% Output     : Refutation 1.12s
% Verified   : 
% Statistics : Number of formulae       :  155 ( 321 expanded)
%              Number of leaves         :   44 ( 114 expanded)
%              Depth                    :   18
%              Number of atoms          : 1353 (8898 expanded)
%              Number of equality atoms :   17 ( 225 expanded)
%              Maximal formula depth    :   32 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tmap_1_type,type,(
    r1_tmap_1: $i > $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(sk_G_type,type,(
    sk_G: $i )).

thf(m1_connsp_2_type,type,(
    m1_connsp_2: $i > $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(g1_pre_topc_type,type,(
    g1_pre_topc: $i > $i > $i )).

thf(k3_tmap_1_type,type,(
    k3_tmap_1: $i > $i > $i > $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

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

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('1',plain,(
    ! [X1: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X1 ) @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('2',plain,(
    ! [X0: $i] :
      ( ( k2_subset_1 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('3',plain,(
    ! [X1: $i] :
      ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('4',plain,(
    r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    sk_F = sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_F ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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

thf('8',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i,X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ( v2_struct_0 @ X25 )
      | ~ ( v2_pre_topc @ X25 )
      | ~ ( l1_pre_topc @ X25 )
      | ( v2_struct_0 @ X26 )
      | ~ ( m1_pre_topc @ X26 @ X27 )
      | ~ ( m1_pre_topc @ X28 @ X26 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) )
      | ~ ( m1_subset_1 @ X30 @ ( u1_struct_0 @ X28 ) )
      | ~ ( r1_tmap_1 @ X28 @ X25 @ ( k3_tmap_1 @ X27 @ X25 @ X26 @ X28 @ X31 ) @ X30 )
      | ( r1_tmap_1 @ X26 @ X25 @ X31 @ X32 )
      | ( X32 != X30 )
      | ~ ( m1_connsp_2 @ X29 @ X26 @ X32 )
      | ~ ( r1_tarski @ X29 @ ( u1_struct_0 @ X28 ) )
      | ~ ( m1_subset_1 @ X32 @ ( u1_struct_0 @ X26 ) )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X26 ) @ ( u1_struct_0 @ X25 ) ) ) )
      | ~ ( v1_funct_2 @ X31 @ ( u1_struct_0 @ X26 ) @ ( u1_struct_0 @ X25 ) )
      | ~ ( v1_funct_1 @ X31 )
      | ~ ( m1_pre_topc @ X28 @ X27 )
      | ( v2_struct_0 @ X28 )
      | ~ ( l1_pre_topc @ X27 )
      | ~ ( v2_pre_topc @ X27 )
      | ( v2_struct_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t83_tmap_1])).

thf('9',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ( v2_struct_0 @ X27 )
      | ~ ( v2_pre_topc @ X27 )
      | ~ ( l1_pre_topc @ X27 )
      | ( v2_struct_0 @ X28 )
      | ~ ( m1_pre_topc @ X28 @ X27 )
      | ~ ( v1_funct_1 @ X31 )
      | ~ ( v1_funct_2 @ X31 @ ( u1_struct_0 @ X26 ) @ ( u1_struct_0 @ X25 ) )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X26 ) @ ( u1_struct_0 @ X25 ) ) ) )
      | ~ ( m1_subset_1 @ X30 @ ( u1_struct_0 @ X26 ) )
      | ~ ( r1_tarski @ X29 @ ( u1_struct_0 @ X28 ) )
      | ~ ( m1_connsp_2 @ X29 @ X26 @ X30 )
      | ( r1_tmap_1 @ X26 @ X25 @ X31 @ X30 )
      | ~ ( r1_tmap_1 @ X28 @ X25 @ ( k3_tmap_1 @ X27 @ X25 @ X26 @ X28 @ X31 ) @ X30 )
      | ~ ( m1_subset_1 @ X30 @ ( u1_struct_0 @ X28 ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) )
      | ~ ( m1_pre_topc @ X28 @ X26 )
      | ~ ( m1_pre_topc @ X26 @ X27 )
      | ( v2_struct_0 @ X26 )
      | ~ ( l1_pre_topc @ X25 )
      | ~ ( v2_pre_topc @ X25 )
      | ( v2_struct_0 @ X25 ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,(
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
      | ~ ( m1_connsp_2 @ X2 @ sk_D @ X3 )
      | ~ ( r1_tarski @ X2 @ ( u1_struct_0 @ X1 ) )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ sk_D ) )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ( v2_struct_0 @ X1 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','9'])).

thf('11',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ~ ( m1_pre_topc @ X1 @ sk_D )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X1 ) )
      | ~ ( r1_tmap_1 @ X1 @ sk_B @ ( k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E ) @ X3 )
      | ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X3 )
      | ~ ( m1_connsp_2 @ X2 @ sk_D @ X3 )
      | ~ ( r1_tarski @ X2 @ ( u1_struct_0 @ X1 ) )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ sk_D ) )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ( v2_struct_0 @ X1 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['10','11','12','13','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ~ ( m1_pre_topc @ sk_C @ sk_A )
      | ~ ( m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_D ) )
      | ~ ( r1_tarski @ X0 @ ( u1_struct_0 @ sk_C ) )
      | ~ ( m1_connsp_2 @ X0 @ sk_D @ sk_F )
      | ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F )
      | ~ ( m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_C ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) )
      | ~ ( m1_pre_topc @ sk_C @ sk_D )
      | ~ ( m1_pre_topc @ sk_D @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['6','15'])).

thf('17',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    sk_F = sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) )
    = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( m1_pre_topc @ A @ A ) ) )).

thf('25',plain,(
    ! [X19: $i] :
      ( ( m1_pre_topc @ X19 @ X19 )
      | ~ ( l1_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf(t65_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( l1_pre_topc @ B )
         => ( ( m1_pre_topc @ A @ B )
          <=> ( m1_pre_topc @ A @ ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ) )).

thf('26',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( l1_pre_topc @ X11 )
      | ~ ( m1_pre_topc @ X12 @ X11 )
      | ( m1_pre_topc @ X12 @ ( g1_pre_topc @ ( u1_struct_0 @ X11 ) @ ( u1_pre_topc @ X11 ) ) )
      | ~ ( l1_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[t65_pre_topc])).

thf('27',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,
    ( ( m1_pre_topc @ sk_C @ sk_D )
    | ~ ( l1_pre_topc @ sk_C ) ),
    inference('sup+',[status(thm)],['24','28'])).

thf('30',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('31',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( m1_pre_topc @ X8 @ X9 )
      | ( l1_pre_topc @ X8 )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('32',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_C ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(demod,[status(thm)],['29','34'])).

thf('36',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ~ ( r1_tarski @ X0 @ ( u1_struct_0 @ sk_C ) )
      | ~ ( m1_connsp_2 @ X0 @ sk_D @ sk_F )
      | ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['16','17','18','19','20','23','35','36'])).

thf('38',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F )
    | ~ ( m1_connsp_2 @ ( u1_struct_0 @ sk_D ) @ sk_D @ sk_F )
    | ~ ( r1_tarski @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_C ) )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['3','37'])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('39',plain,(
    ! [X6: $i] :
      ( ( ( k2_struct_0 @ X6 )
        = ( u1_struct_0 @ X6 ) )
      | ~ ( l1_struct_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(fc10_tops_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( v3_pre_topc @ ( k2_struct_0 @ A ) @ A ) ) )).

thf('40',plain,(
    ! [X13: $i] :
      ( ( v3_pre_topc @ ( k2_struct_0 @ X13 ) @ X13 )
      | ~ ( l1_pre_topc @ X13 )
      | ~ ( v2_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[fc10_tops_1])).

thf('41',plain,(
    ! [X6: $i] :
      ( ( ( k2_struct_0 @ X6 )
        = ( u1_struct_0 @ X6 ) )
      | ~ ( l1_struct_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('42',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    ! [X1: $i] :
      ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['1','2'])).

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

thf('44',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ~ ( v3_pre_topc @ X14 @ X15 )
      | ~ ( r2_hidden @ X16 @ X14 )
      | ( m1_connsp_2 @ X14 @ X15 @ X16 )
      | ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ X15 ) )
      | ~ ( l1_pre_topc @ X15 )
      | ~ ( v2_pre_topc @ X15 )
      | ( v2_struct_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t5_connsp_2])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ( m1_connsp_2 @ ( u1_struct_0 @ X0 ) @ X0 @ X1 )
      | ~ ( r2_hidden @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,
    ( ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_D ) @ sk_D )
    | ~ ( r2_hidden @ sk_F @ ( u1_struct_0 @ sk_D ) )
    | ( m1_connsp_2 @ ( u1_struct_0 @ sk_D ) @ sk_D @ sk_F )
    | ~ ( l1_pre_topc @ sk_D )
    | ~ ( v2_pre_topc @ sk_D )
    | ( v2_struct_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['42','45'])).

thf('47',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( m1_pre_topc @ X8 @ X9 )
      | ( l1_pre_topc @ X8 )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('49',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_D ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( v2_pre_topc @ B ) ) ) )).

thf('53',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( m1_pre_topc @ X4 @ X5 )
      | ( v2_pre_topc @ X4 )
      | ~ ( l1_pre_topc @ X5 )
      | ~ ( v2_pre_topc @ X5 ) ) ),
    inference(cnf,[status(esa)],[cc1_pre_topc])).

thf('54',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_pre_topc @ sk_D ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    v2_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['54','55','56'])).

thf('58',plain,
    ( ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_D ) @ sk_D )
    | ~ ( r2_hidden @ sk_F @ ( u1_struct_0 @ sk_D ) )
    | ( m1_connsp_2 @ ( u1_struct_0 @ sk_D ) @ sk_D @ sk_F )
    | ( v2_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['46','51','57'])).

thf('59',plain,
    ( ~ ( v3_pre_topc @ ( k2_struct_0 @ sk_D ) @ sk_D )
    | ~ ( l1_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_D )
    | ( m1_connsp_2 @ ( u1_struct_0 @ sk_D ) @ sk_D @ sk_F )
    | ~ ( r2_hidden @ sk_F @ ( u1_struct_0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['41','58'])).

thf('60',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['49','50'])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('61',plain,(
    ! [X7: $i] :
      ( ( l1_struct_0 @ X7 )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('62',plain,(
    l1_struct_0 @ sk_D ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,
    ( ~ ( v3_pre_topc @ ( k2_struct_0 @ sk_D ) @ sk_D )
    | ( v2_struct_0 @ sk_D )
    | ( m1_connsp_2 @ ( u1_struct_0 @ sk_D ) @ sk_D @ sk_F )
    | ~ ( r2_hidden @ sk_F @ ( u1_struct_0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['59','62'])).

thf('64',plain,
    ( ~ ( v2_pre_topc @ sk_D )
    | ~ ( l1_pre_topc @ sk_D )
    | ~ ( r2_hidden @ sk_F @ ( u1_struct_0 @ sk_D ) )
    | ( m1_connsp_2 @ ( u1_struct_0 @ sk_D ) @ sk_D @ sk_F )
    | ( v2_struct_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['40','63'])).

thf('65',plain,(
    v2_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['54','55','56'])).

thf('66',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['49','50'])).

thf('67',plain,
    ( ~ ( r2_hidden @ sk_F @ ( u1_struct_0 @ sk_D ) )
    | ( m1_connsp_2 @ ( u1_struct_0 @ sk_D ) @ sk_D @ sk_F )
    | ( v2_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['64','65','66'])).

thf('68',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,
    ( ( m1_connsp_2 @ ( u1_struct_0 @ sk_D ) @ sk_D @ sk_F )
    | ~ ( r2_hidden @ sk_F @ ( u1_struct_0 @ sk_D ) ) ),
    inference(clc,[status(thm)],['67','68'])).

thf('70',plain,
    ( ~ ( r2_hidden @ sk_F @ ( k2_struct_0 @ sk_D ) )
    | ~ ( l1_struct_0 @ sk_D )
    | ( m1_connsp_2 @ ( u1_struct_0 @ sk_D ) @ sk_D @ sk_F ) ),
    inference('sup-',[status(thm)],['39','69'])).

thf('71',plain,(
    ! [X6: $i] :
      ( ( ( k2_struct_0 @ X6 )
        = ( u1_struct_0 @ X6 ) )
      | ~ ( l1_struct_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('72',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('73',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r2_hidden @ X2 @ X3 )
      | ( v1_xboole_0 @ X3 )
      | ~ ( m1_subset_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('74',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_D ) )
    | ( r2_hidden @ sk_F @ ( u1_struct_0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,
    ( ( r2_hidden @ sk_F @ ( k2_struct_0 @ sk_D ) )
    | ~ ( l1_struct_0 @ sk_D )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_D ) ) ),
    inference('sup+',[status(thm)],['71','74'])).

thf('76',plain,(
    l1_struct_0 @ sk_D ),
    inference('sup-',[status(thm)],['60','61'])).

thf('77',plain,
    ( ( r2_hidden @ sk_F @ ( k2_struct_0 @ sk_D ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['75','76'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('78',plain,(
    ! [X10: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X10 ) )
      | ~ ( l1_struct_0 @ X10 )
      | ( v2_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('79',plain,
    ( ( r2_hidden @ sk_F @ ( k2_struct_0 @ sk_D ) )
    | ( v2_struct_0 @ sk_D )
    | ~ ( l1_struct_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    l1_struct_0 @ sk_D ),
    inference('sup-',[status(thm)],['60','61'])).

thf('81',plain,
    ( ( r2_hidden @ sk_F @ ( k2_struct_0 @ sk_D ) )
    | ( v2_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['79','80'])).

thf('82',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    r2_hidden @ sk_F @ ( k2_struct_0 @ sk_D ) ),
    inference(clc,[status(thm)],['81','82'])).

thf('84',plain,(
    l1_struct_0 @ sk_D ),
    inference('sup-',[status(thm)],['60','61'])).

thf('85',plain,(
    m1_connsp_2 @ ( u1_struct_0 @ sk_D ) @ sk_D @ sk_F ),
    inference(demod,[status(thm)],['70','83','84'])).

thf('86',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) )
    = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    ! [X19: $i] :
      ( ( m1_pre_topc @ X19 @ X19 )
      | ~ ( l1_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('88',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( l1_pre_topc @ X11 )
      | ~ ( m1_pre_topc @ X12 @ ( g1_pre_topc @ ( u1_struct_0 @ X11 ) @ ( u1_pre_topc @ X11 ) ) )
      | ( m1_pre_topc @ X12 @ X11 )
      | ~ ( l1_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[t65_pre_topc])).

thf('89',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) @ X0 )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['89'])).

thf('91',plain,
    ( ~ ( l1_pre_topc @ sk_D )
    | ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) ) @ sk_C )
    | ~ ( l1_pre_topc @ sk_C ) ),
    inference('sup-',[status(thm)],['86','90'])).

thf('92',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['49','50'])).

thf('93',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) )
    = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['32','33'])).

thf('95',plain,(
    m1_pre_topc @ sk_D @ sk_C ),
    inference(demod,[status(thm)],['91','92','93','94'])).

thf(t35_borsuk_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( r1_tarski @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) )).

thf('96',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( m1_pre_topc @ X20 @ X21 )
      | ( r1_tarski @ ( u1_struct_0 @ X20 ) @ ( u1_struct_0 @ X21 ) )
      | ~ ( l1_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[t35_borsuk_1])).

thf('97',plain,
    ( ~ ( l1_pre_topc @ sk_C )
    | ( r1_tarski @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['32','33'])).

thf('99',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['97','98'])).

thf('100',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['38','85','99'])).

thf('101',plain,(
    ~ ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['102','103'])).

thf('105',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C ) ),
    inference(clc,[status(thm)],['104','105'])).

thf('107',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,(
    v2_struct_0 @ sk_C ),
    inference(clc,[status(thm)],['106','107'])).

thf('109',plain,(
    $false ),
    inference(demod,[status(thm)],['0','108'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.pfDh7W0j9C
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 13:53:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.12/1.35  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.12/1.35  % Solved by: fo/fo7.sh
% 1.12/1.35  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.12/1.35  % done 1750 iterations in 0.883s
% 1.12/1.35  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.12/1.35  % SZS output start Refutation
% 1.12/1.35  thf(r1_tmap_1_type, type, r1_tmap_1: $i > $i > $i > $i > $o).
% 1.12/1.35  thf(sk_A_type, type, sk_A: $i).
% 1.12/1.35  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 1.12/1.35  thf(sk_D_type, type, sk_D: $i).
% 1.12/1.35  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.12/1.35  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.12/1.35  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 1.12/1.35  thf(sk_G_type, type, sk_G: $i).
% 1.12/1.35  thf(m1_connsp_2_type, type, m1_connsp_2: $i > $i > $i > $o).
% 1.12/1.35  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 1.12/1.35  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.12/1.35  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.12/1.35  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 1.12/1.35  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.12/1.35  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.12/1.35  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 1.12/1.35  thf(sk_B_type, type, sk_B: $i).
% 1.12/1.35  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 1.12/1.35  thf(g1_pre_topc_type, type, g1_pre_topc: $i > $i > $i).
% 1.12/1.35  thf(k3_tmap_1_type, type, k3_tmap_1: $i > $i > $i > $i > $i > $i).
% 1.12/1.35  thf(sk_E_type, type, sk_E: $i).
% 1.12/1.35  thf(sk_F_type, type, sk_F: $i).
% 1.12/1.35  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.12/1.35  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 1.12/1.35  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 1.12/1.35  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 1.12/1.35  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 1.12/1.35  thf(sk_C_type, type, sk_C: $i).
% 1.12/1.35  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.12/1.35  thf(t88_tmap_1, conjecture,
% 1.12/1.35    (![A:$i]:
% 1.12/1.35     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.12/1.35       ( ![B:$i]:
% 1.12/1.35         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 1.12/1.35             ( l1_pre_topc @ B ) ) =>
% 1.12/1.35           ( ![C:$i]:
% 1.12/1.35             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 1.12/1.35               ( ![D:$i]:
% 1.12/1.35                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 1.12/1.35                   ( ![E:$i]:
% 1.12/1.35                     ( ( ( v1_funct_1 @ E ) & 
% 1.12/1.35                         ( v1_funct_2 @
% 1.12/1.35                           E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 1.12/1.35                         ( m1_subset_1 @
% 1.12/1.35                           E @ 
% 1.12/1.35                           ( k1_zfmisc_1 @
% 1.12/1.35                             ( k2_zfmisc_1 @
% 1.12/1.35                               ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 1.12/1.35                       ( ( ( g1_pre_topc @
% 1.12/1.35                             ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) ) =
% 1.12/1.35                           ( D ) ) =>
% 1.12/1.35                         ( ![F:$i]:
% 1.12/1.35                           ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 1.12/1.35                             ( ![G:$i]:
% 1.12/1.35                               ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) ) =>
% 1.12/1.35                                 ( ( ( ( F ) = ( G ) ) & 
% 1.12/1.35                                     ( r1_tmap_1 @
% 1.12/1.35                                       C @ B @ 
% 1.12/1.35                                       ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ G ) ) =>
% 1.12/1.35                                   ( r1_tmap_1 @ D @ B @ E @ F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 1.12/1.35  thf(zf_stmt_0, negated_conjecture,
% 1.12/1.35    (~( ![A:$i]:
% 1.12/1.35        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 1.12/1.35            ( l1_pre_topc @ A ) ) =>
% 1.12/1.35          ( ![B:$i]:
% 1.12/1.35            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 1.12/1.35                ( l1_pre_topc @ B ) ) =>
% 1.12/1.35              ( ![C:$i]:
% 1.12/1.35                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 1.12/1.35                  ( ![D:$i]:
% 1.12/1.35                    ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 1.12/1.35                      ( ![E:$i]:
% 1.12/1.35                        ( ( ( v1_funct_1 @ E ) & 
% 1.12/1.35                            ( v1_funct_2 @
% 1.12/1.35                              E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 1.12/1.35                            ( m1_subset_1 @
% 1.12/1.35                              E @ 
% 1.12/1.35                              ( k1_zfmisc_1 @
% 1.12/1.35                                ( k2_zfmisc_1 @
% 1.12/1.35                                  ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 1.12/1.35                          ( ( ( g1_pre_topc @
% 1.12/1.35                                ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) ) =
% 1.12/1.35                              ( D ) ) =>
% 1.12/1.35                            ( ![F:$i]:
% 1.12/1.35                              ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 1.12/1.35                                ( ![G:$i]:
% 1.12/1.35                                  ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) ) =>
% 1.12/1.35                                    ( ( ( ( F ) = ( G ) ) & 
% 1.12/1.35                                        ( r1_tmap_1 @
% 1.12/1.35                                          C @ B @ 
% 1.12/1.35                                          ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ G ) ) =>
% 1.12/1.35                                      ( r1_tmap_1 @ D @ B @ E @ F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 1.12/1.35    inference('cnf.neg', [status(esa)], [t88_tmap_1])).
% 1.12/1.35  thf('0', plain, (~ (v2_struct_0 @ sk_C)),
% 1.12/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.12/1.35  thf(dt_k2_subset_1, axiom,
% 1.12/1.35    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 1.12/1.35  thf('1', plain,
% 1.12/1.35      (![X1 : $i]: (m1_subset_1 @ (k2_subset_1 @ X1) @ (k1_zfmisc_1 @ X1))),
% 1.12/1.35      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 1.12/1.35  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 1.12/1.35  thf('2', plain, (![X0 : $i]: ((k2_subset_1 @ X0) = (X0))),
% 1.12/1.35      inference('cnf', [status(esa)], [d4_subset_1])).
% 1.12/1.35  thf('3', plain, (![X1 : $i]: (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X1))),
% 1.12/1.35      inference('demod', [status(thm)], ['1', '2'])).
% 1.12/1.35  thf('4', plain,
% 1.12/1.35      ((r1_tmap_1 @ sk_C @ sk_B @ 
% 1.12/1.35        (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_G)),
% 1.12/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.12/1.35  thf('5', plain, (((sk_F) = (sk_G))),
% 1.12/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.12/1.35  thf('6', plain,
% 1.12/1.35      ((r1_tmap_1 @ sk_C @ sk_B @ 
% 1.12/1.35        (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_F)),
% 1.12/1.35      inference('demod', [status(thm)], ['4', '5'])).
% 1.12/1.35  thf('7', plain,
% 1.12/1.35      ((m1_subset_1 @ sk_E @ 
% 1.12/1.35        (k1_zfmisc_1 @ 
% 1.12/1.35         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 1.12/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.12/1.35  thf(t83_tmap_1, axiom,
% 1.12/1.35    (![A:$i]:
% 1.12/1.35     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.12/1.35       ( ![B:$i]:
% 1.12/1.35         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 1.12/1.35             ( l1_pre_topc @ B ) ) =>
% 1.12/1.35           ( ![C:$i]:
% 1.12/1.35             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 1.12/1.35               ( ![D:$i]:
% 1.12/1.35                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 1.12/1.35                   ( ![E:$i]:
% 1.12/1.35                     ( ( ( v1_funct_1 @ E ) & 
% 1.12/1.35                         ( v1_funct_2 @
% 1.12/1.35                           E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 1.12/1.35                         ( m1_subset_1 @
% 1.12/1.35                           E @ 
% 1.12/1.35                           ( k1_zfmisc_1 @
% 1.12/1.35                             ( k2_zfmisc_1 @
% 1.12/1.35                               ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 1.12/1.35                       ( ( m1_pre_topc @ C @ D ) =>
% 1.12/1.35                         ( ![F:$i]:
% 1.12/1.35                           ( ( m1_subset_1 @
% 1.12/1.35                               F @ ( k1_zfmisc_1 @ ( u1_struct_0 @ D ) ) ) =>
% 1.12/1.35                             ( ![G:$i]:
% 1.12/1.35                               ( ( m1_subset_1 @ G @ ( u1_struct_0 @ D ) ) =>
% 1.12/1.35                                 ( ![H:$i]:
% 1.12/1.35                                   ( ( m1_subset_1 @ H @ ( u1_struct_0 @ C ) ) =>
% 1.12/1.35                                     ( ( ( r1_tarski @ F @ ( u1_struct_0 @ C ) ) & 
% 1.12/1.35                                         ( m1_connsp_2 @ F @ D @ G ) & 
% 1.12/1.35                                         ( ( G ) = ( H ) ) ) =>
% 1.12/1.35                                       ( ( r1_tmap_1 @ D @ B @ E @ G ) <=>
% 1.12/1.35                                         ( r1_tmap_1 @
% 1.12/1.35                                           C @ B @ 
% 1.12/1.35                                           ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ 
% 1.12/1.35                                           H ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 1.12/1.35  thf('8', plain,
% 1.12/1.35      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i, X30 : $i, X31 : $i, 
% 1.12/1.35         X32 : $i]:
% 1.12/1.35         ((v2_struct_0 @ X25)
% 1.12/1.35          | ~ (v2_pre_topc @ X25)
% 1.12/1.35          | ~ (l1_pre_topc @ X25)
% 1.12/1.35          | (v2_struct_0 @ X26)
% 1.12/1.35          | ~ (m1_pre_topc @ X26 @ X27)
% 1.12/1.35          | ~ (m1_pre_topc @ X28 @ X26)
% 1.12/1.35          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X26)))
% 1.12/1.35          | ~ (m1_subset_1 @ X30 @ (u1_struct_0 @ X28))
% 1.12/1.35          | ~ (r1_tmap_1 @ X28 @ X25 @ 
% 1.12/1.35               (k3_tmap_1 @ X27 @ X25 @ X26 @ X28 @ X31) @ X30)
% 1.12/1.35          | (r1_tmap_1 @ X26 @ X25 @ X31 @ X32)
% 1.12/1.35          | ((X32) != (X30))
% 1.12/1.35          | ~ (m1_connsp_2 @ X29 @ X26 @ X32)
% 1.12/1.35          | ~ (r1_tarski @ X29 @ (u1_struct_0 @ X28))
% 1.12/1.35          | ~ (m1_subset_1 @ X32 @ (u1_struct_0 @ X26))
% 1.12/1.35          | ~ (m1_subset_1 @ X31 @ 
% 1.12/1.35               (k1_zfmisc_1 @ 
% 1.12/1.35                (k2_zfmisc_1 @ (u1_struct_0 @ X26) @ (u1_struct_0 @ X25))))
% 1.12/1.35          | ~ (v1_funct_2 @ X31 @ (u1_struct_0 @ X26) @ (u1_struct_0 @ X25))
% 1.12/1.35          | ~ (v1_funct_1 @ X31)
% 1.12/1.35          | ~ (m1_pre_topc @ X28 @ X27)
% 1.12/1.35          | (v2_struct_0 @ X28)
% 1.12/1.35          | ~ (l1_pre_topc @ X27)
% 1.12/1.35          | ~ (v2_pre_topc @ X27)
% 1.12/1.35          | (v2_struct_0 @ X27))),
% 1.12/1.35      inference('cnf', [status(esa)], [t83_tmap_1])).
% 1.12/1.35  thf('9', plain,
% 1.12/1.35      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 1.12/1.35         ((v2_struct_0 @ X27)
% 1.12/1.35          | ~ (v2_pre_topc @ X27)
% 1.12/1.35          | ~ (l1_pre_topc @ X27)
% 1.12/1.35          | (v2_struct_0 @ X28)
% 1.12/1.35          | ~ (m1_pre_topc @ X28 @ X27)
% 1.12/1.35          | ~ (v1_funct_1 @ X31)
% 1.12/1.35          | ~ (v1_funct_2 @ X31 @ (u1_struct_0 @ X26) @ (u1_struct_0 @ X25))
% 1.12/1.35          | ~ (m1_subset_1 @ X31 @ 
% 1.12/1.35               (k1_zfmisc_1 @ 
% 1.12/1.35                (k2_zfmisc_1 @ (u1_struct_0 @ X26) @ (u1_struct_0 @ X25))))
% 1.12/1.35          | ~ (m1_subset_1 @ X30 @ (u1_struct_0 @ X26))
% 1.12/1.35          | ~ (r1_tarski @ X29 @ (u1_struct_0 @ X28))
% 1.12/1.35          | ~ (m1_connsp_2 @ X29 @ X26 @ X30)
% 1.12/1.35          | (r1_tmap_1 @ X26 @ X25 @ X31 @ X30)
% 1.12/1.35          | ~ (r1_tmap_1 @ X28 @ X25 @ 
% 1.12/1.35               (k3_tmap_1 @ X27 @ X25 @ X26 @ X28 @ X31) @ X30)
% 1.12/1.35          | ~ (m1_subset_1 @ X30 @ (u1_struct_0 @ X28))
% 1.12/1.35          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X26)))
% 1.12/1.35          | ~ (m1_pre_topc @ X28 @ X26)
% 1.12/1.35          | ~ (m1_pre_topc @ X26 @ X27)
% 1.12/1.35          | (v2_struct_0 @ X26)
% 1.12/1.35          | ~ (l1_pre_topc @ X25)
% 1.12/1.35          | ~ (v2_pre_topc @ X25)
% 1.12/1.35          | (v2_struct_0 @ X25))),
% 1.12/1.35      inference('simplify', [status(thm)], ['8'])).
% 1.12/1.35  thf('10', plain,
% 1.12/1.35      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.12/1.35         ((v2_struct_0 @ sk_B)
% 1.12/1.35          | ~ (v2_pre_topc @ sk_B)
% 1.12/1.35          | ~ (l1_pre_topc @ sk_B)
% 1.12/1.35          | (v2_struct_0 @ sk_D)
% 1.12/1.35          | ~ (m1_pre_topc @ sk_D @ X0)
% 1.12/1.35          | ~ (m1_pre_topc @ X1 @ sk_D)
% 1.12/1.35          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))
% 1.12/1.35          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X1))
% 1.12/1.35          | ~ (r1_tmap_1 @ X1 @ sk_B @ 
% 1.12/1.35               (k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E) @ X3)
% 1.12/1.35          | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X3)
% 1.12/1.35          | ~ (m1_connsp_2 @ X2 @ sk_D @ X3)
% 1.12/1.35          | ~ (r1_tarski @ X2 @ (u1_struct_0 @ X1))
% 1.12/1.35          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ sk_D))
% 1.12/1.35          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 1.12/1.35          | ~ (v1_funct_1 @ sk_E)
% 1.12/1.35          | ~ (m1_pre_topc @ X1 @ X0)
% 1.12/1.35          | (v2_struct_0 @ X1)
% 1.12/1.35          | ~ (l1_pre_topc @ X0)
% 1.12/1.35          | ~ (v2_pre_topc @ X0)
% 1.12/1.35          | (v2_struct_0 @ X0))),
% 1.12/1.35      inference('sup-', [status(thm)], ['7', '9'])).
% 1.12/1.35  thf('11', plain, ((v2_pre_topc @ sk_B)),
% 1.12/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.12/1.35  thf('12', plain, ((l1_pre_topc @ sk_B)),
% 1.12/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.12/1.35  thf('13', plain,
% 1.12/1.35      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 1.12/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.12/1.35  thf('14', plain, ((v1_funct_1 @ sk_E)),
% 1.12/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.12/1.35  thf('15', plain,
% 1.12/1.35      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.12/1.35         ((v2_struct_0 @ sk_B)
% 1.12/1.35          | (v2_struct_0 @ sk_D)
% 1.12/1.35          | ~ (m1_pre_topc @ sk_D @ X0)
% 1.12/1.35          | ~ (m1_pre_topc @ X1 @ sk_D)
% 1.12/1.35          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))
% 1.12/1.35          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X1))
% 1.12/1.35          | ~ (r1_tmap_1 @ X1 @ sk_B @ 
% 1.12/1.35               (k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E) @ X3)
% 1.12/1.35          | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X3)
% 1.12/1.35          | ~ (m1_connsp_2 @ X2 @ sk_D @ X3)
% 1.12/1.35          | ~ (r1_tarski @ X2 @ (u1_struct_0 @ X1))
% 1.12/1.35          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ sk_D))
% 1.12/1.35          | ~ (m1_pre_topc @ X1 @ X0)
% 1.12/1.35          | (v2_struct_0 @ X1)
% 1.12/1.35          | ~ (l1_pre_topc @ X0)
% 1.12/1.35          | ~ (v2_pre_topc @ X0)
% 1.12/1.35          | (v2_struct_0 @ X0))),
% 1.12/1.35      inference('demod', [status(thm)], ['10', '11', '12', '13', '14'])).
% 1.12/1.35  thf('16', plain,
% 1.12/1.35      (![X0 : $i]:
% 1.12/1.35         ((v2_struct_0 @ sk_A)
% 1.12/1.35          | ~ (v2_pre_topc @ sk_A)
% 1.12/1.35          | ~ (l1_pre_topc @ sk_A)
% 1.12/1.35          | (v2_struct_0 @ sk_C)
% 1.12/1.35          | ~ (m1_pre_topc @ sk_C @ sk_A)
% 1.12/1.35          | ~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_D))
% 1.12/1.35          | ~ (r1_tarski @ X0 @ (u1_struct_0 @ sk_C))
% 1.12/1.35          | ~ (m1_connsp_2 @ X0 @ sk_D @ sk_F)
% 1.12/1.35          | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)
% 1.12/1.35          | ~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C))
% 1.12/1.35          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))
% 1.12/1.35          | ~ (m1_pre_topc @ sk_C @ sk_D)
% 1.12/1.35          | ~ (m1_pre_topc @ sk_D @ sk_A)
% 1.12/1.35          | (v2_struct_0 @ sk_D)
% 1.12/1.35          | (v2_struct_0 @ sk_B))),
% 1.12/1.35      inference('sup-', [status(thm)], ['6', '15'])).
% 1.12/1.35  thf('17', plain, ((v2_pre_topc @ sk_A)),
% 1.12/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.12/1.35  thf('18', plain, ((l1_pre_topc @ sk_A)),
% 1.12/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.12/1.35  thf('19', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 1.12/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.12/1.35  thf('20', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_D))),
% 1.12/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.12/1.35  thf('21', plain, ((m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_C))),
% 1.12/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.12/1.35  thf('22', plain, (((sk_F) = (sk_G))),
% 1.12/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.12/1.35  thf('23', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C))),
% 1.12/1.35      inference('demod', [status(thm)], ['21', '22'])).
% 1.12/1.35  thf('24', plain,
% 1.12/1.35      (((g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) = (sk_D))),
% 1.12/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.12/1.35  thf(t2_tsep_1, axiom,
% 1.12/1.35    (![A:$i]: ( ( l1_pre_topc @ A ) => ( m1_pre_topc @ A @ A ) ))).
% 1.12/1.35  thf('25', plain,
% 1.12/1.35      (![X19 : $i]: ((m1_pre_topc @ X19 @ X19) | ~ (l1_pre_topc @ X19))),
% 1.12/1.35      inference('cnf', [status(esa)], [t2_tsep_1])).
% 1.12/1.35  thf(t65_pre_topc, axiom,
% 1.12/1.35    (![A:$i]:
% 1.12/1.35     ( ( l1_pre_topc @ A ) =>
% 1.12/1.35       ( ![B:$i]:
% 1.12/1.35         ( ( l1_pre_topc @ B ) =>
% 1.12/1.35           ( ( m1_pre_topc @ A @ B ) <=>
% 1.12/1.35             ( m1_pre_topc @
% 1.12/1.35               A @ ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ) ))).
% 1.12/1.35  thf('26', plain,
% 1.12/1.35      (![X11 : $i, X12 : $i]:
% 1.12/1.35         (~ (l1_pre_topc @ X11)
% 1.12/1.35          | ~ (m1_pre_topc @ X12 @ X11)
% 1.12/1.35          | (m1_pre_topc @ X12 @ 
% 1.12/1.35             (g1_pre_topc @ (u1_struct_0 @ X11) @ (u1_pre_topc @ X11)))
% 1.12/1.35          | ~ (l1_pre_topc @ X12))),
% 1.12/1.35      inference('cnf', [status(esa)], [t65_pre_topc])).
% 1.12/1.35  thf('27', plain,
% 1.12/1.35      (![X0 : $i]:
% 1.12/1.35         (~ (l1_pre_topc @ X0)
% 1.12/1.35          | ~ (l1_pre_topc @ X0)
% 1.12/1.35          | (m1_pre_topc @ X0 @ 
% 1.12/1.35             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 1.12/1.35          | ~ (l1_pre_topc @ X0))),
% 1.12/1.35      inference('sup-', [status(thm)], ['25', '26'])).
% 1.12/1.35  thf('28', plain,
% 1.12/1.35      (![X0 : $i]:
% 1.12/1.35         ((m1_pre_topc @ X0 @ 
% 1.12/1.35           (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 1.12/1.35          | ~ (l1_pre_topc @ X0))),
% 1.12/1.35      inference('simplify', [status(thm)], ['27'])).
% 1.12/1.35  thf('29', plain, (((m1_pre_topc @ sk_C @ sk_D) | ~ (l1_pre_topc @ sk_C))),
% 1.12/1.35      inference('sup+', [status(thm)], ['24', '28'])).
% 1.12/1.35  thf('30', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 1.12/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.12/1.35  thf(dt_m1_pre_topc, axiom,
% 1.12/1.35    (![A:$i]:
% 1.12/1.35     ( ( l1_pre_topc @ A ) =>
% 1.12/1.35       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 1.12/1.35  thf('31', plain,
% 1.12/1.35      (![X8 : $i, X9 : $i]:
% 1.12/1.35         (~ (m1_pre_topc @ X8 @ X9) | (l1_pre_topc @ X8) | ~ (l1_pre_topc @ X9))),
% 1.12/1.35      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 1.12/1.35  thf('32', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_C))),
% 1.12/1.35      inference('sup-', [status(thm)], ['30', '31'])).
% 1.12/1.35  thf('33', plain, ((l1_pre_topc @ sk_A)),
% 1.12/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.12/1.35  thf('34', plain, ((l1_pre_topc @ sk_C)),
% 1.12/1.35      inference('demod', [status(thm)], ['32', '33'])).
% 1.12/1.35  thf('35', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 1.12/1.35      inference('demod', [status(thm)], ['29', '34'])).
% 1.12/1.35  thf('36', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 1.12/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.12/1.35  thf('37', plain,
% 1.12/1.35      (![X0 : $i]:
% 1.12/1.35         ((v2_struct_0 @ sk_A)
% 1.12/1.35          | (v2_struct_0 @ sk_C)
% 1.12/1.35          | ~ (r1_tarski @ X0 @ (u1_struct_0 @ sk_C))
% 1.12/1.35          | ~ (m1_connsp_2 @ X0 @ sk_D @ sk_F)
% 1.12/1.35          | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)
% 1.12/1.35          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))
% 1.12/1.35          | (v2_struct_0 @ sk_D)
% 1.12/1.35          | (v2_struct_0 @ sk_B))),
% 1.12/1.35      inference('demod', [status(thm)],
% 1.12/1.35                ['16', '17', '18', '19', '20', '23', '35', '36'])).
% 1.12/1.35  thf('38', plain,
% 1.12/1.35      (((v2_struct_0 @ sk_B)
% 1.12/1.35        | (v2_struct_0 @ sk_D)
% 1.12/1.35        | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)
% 1.12/1.35        | ~ (m1_connsp_2 @ (u1_struct_0 @ sk_D) @ sk_D @ sk_F)
% 1.12/1.35        | ~ (r1_tarski @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_C))
% 1.12/1.35        | (v2_struct_0 @ sk_C)
% 1.12/1.35        | (v2_struct_0 @ sk_A))),
% 1.12/1.35      inference('sup-', [status(thm)], ['3', '37'])).
% 1.12/1.35  thf(d3_struct_0, axiom,
% 1.12/1.35    (![A:$i]:
% 1.12/1.35     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 1.12/1.35  thf('39', plain,
% 1.12/1.35      (![X6 : $i]:
% 1.12/1.35         (((k2_struct_0 @ X6) = (u1_struct_0 @ X6)) | ~ (l1_struct_0 @ X6))),
% 1.12/1.35      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.12/1.35  thf(fc10_tops_1, axiom,
% 1.12/1.35    (![A:$i]:
% 1.12/1.35     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.12/1.35       ( v3_pre_topc @ ( k2_struct_0 @ A ) @ A ) ))).
% 1.12/1.35  thf('40', plain,
% 1.12/1.35      (![X13 : $i]:
% 1.12/1.35         ((v3_pre_topc @ (k2_struct_0 @ X13) @ X13)
% 1.12/1.35          | ~ (l1_pre_topc @ X13)
% 1.12/1.35          | ~ (v2_pre_topc @ X13))),
% 1.12/1.35      inference('cnf', [status(esa)], [fc10_tops_1])).
% 1.12/1.35  thf('41', plain,
% 1.12/1.35      (![X6 : $i]:
% 1.12/1.35         (((k2_struct_0 @ X6) = (u1_struct_0 @ X6)) | ~ (l1_struct_0 @ X6))),
% 1.12/1.35      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.12/1.35  thf('42', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_D))),
% 1.12/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.12/1.35  thf('43', plain, (![X1 : $i]: (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X1))),
% 1.12/1.35      inference('demod', [status(thm)], ['1', '2'])).
% 1.12/1.35  thf(t5_connsp_2, axiom,
% 1.12/1.35    (![A:$i]:
% 1.12/1.35     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.12/1.35       ( ![B:$i]:
% 1.12/1.35         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.12/1.35           ( ![C:$i]:
% 1.12/1.35             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 1.12/1.35               ( ( ( v3_pre_topc @ B @ A ) & ( r2_hidden @ C @ B ) ) =>
% 1.12/1.35                 ( m1_connsp_2 @ B @ A @ C ) ) ) ) ) ) ))).
% 1.12/1.35  thf('44', plain,
% 1.12/1.35      (![X14 : $i, X15 : $i, X16 : $i]:
% 1.12/1.35         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 1.12/1.35          | ~ (v3_pre_topc @ X14 @ X15)
% 1.12/1.35          | ~ (r2_hidden @ X16 @ X14)
% 1.12/1.35          | (m1_connsp_2 @ X14 @ X15 @ X16)
% 1.12/1.35          | ~ (m1_subset_1 @ X16 @ (u1_struct_0 @ X15))
% 1.12/1.35          | ~ (l1_pre_topc @ X15)
% 1.12/1.35          | ~ (v2_pre_topc @ X15)
% 1.12/1.35          | (v2_struct_0 @ X15))),
% 1.12/1.35      inference('cnf', [status(esa)], [t5_connsp_2])).
% 1.12/1.35  thf('45', plain,
% 1.12/1.35      (![X0 : $i, X1 : $i]:
% 1.12/1.35         ((v2_struct_0 @ X0)
% 1.12/1.35          | ~ (v2_pre_topc @ X0)
% 1.12/1.35          | ~ (l1_pre_topc @ X0)
% 1.12/1.35          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 1.12/1.35          | (m1_connsp_2 @ (u1_struct_0 @ X0) @ X0 @ X1)
% 1.12/1.35          | ~ (r2_hidden @ X1 @ (u1_struct_0 @ X0))
% 1.12/1.35          | ~ (v3_pre_topc @ (u1_struct_0 @ X0) @ X0))),
% 1.12/1.35      inference('sup-', [status(thm)], ['43', '44'])).
% 1.12/1.35  thf('46', plain,
% 1.12/1.35      ((~ (v3_pre_topc @ (u1_struct_0 @ sk_D) @ sk_D)
% 1.12/1.35        | ~ (r2_hidden @ sk_F @ (u1_struct_0 @ sk_D))
% 1.12/1.35        | (m1_connsp_2 @ (u1_struct_0 @ sk_D) @ sk_D @ sk_F)
% 1.12/1.35        | ~ (l1_pre_topc @ sk_D)
% 1.12/1.35        | ~ (v2_pre_topc @ sk_D)
% 1.12/1.35        | (v2_struct_0 @ sk_D))),
% 1.12/1.35      inference('sup-', [status(thm)], ['42', '45'])).
% 1.12/1.35  thf('47', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 1.12/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.12/1.35  thf('48', plain,
% 1.12/1.35      (![X8 : $i, X9 : $i]:
% 1.12/1.35         (~ (m1_pre_topc @ X8 @ X9) | (l1_pre_topc @ X8) | ~ (l1_pre_topc @ X9))),
% 1.12/1.35      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 1.12/1.35  thf('49', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_D))),
% 1.12/1.35      inference('sup-', [status(thm)], ['47', '48'])).
% 1.12/1.35  thf('50', plain, ((l1_pre_topc @ sk_A)),
% 1.12/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.12/1.35  thf('51', plain, ((l1_pre_topc @ sk_D)),
% 1.12/1.35      inference('demod', [status(thm)], ['49', '50'])).
% 1.12/1.35  thf('52', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 1.12/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.12/1.35  thf(cc1_pre_topc, axiom,
% 1.12/1.35    (![A:$i]:
% 1.12/1.35     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.12/1.35       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( v2_pre_topc @ B ) ) ) ))).
% 1.12/1.35  thf('53', plain,
% 1.12/1.35      (![X4 : $i, X5 : $i]:
% 1.12/1.35         (~ (m1_pre_topc @ X4 @ X5)
% 1.12/1.35          | (v2_pre_topc @ X4)
% 1.12/1.35          | ~ (l1_pre_topc @ X5)
% 1.12/1.35          | ~ (v2_pre_topc @ X5))),
% 1.12/1.35      inference('cnf', [status(esa)], [cc1_pre_topc])).
% 1.12/1.35  thf('54', plain,
% 1.12/1.35      ((~ (v2_pre_topc @ sk_A) | ~ (l1_pre_topc @ sk_A) | (v2_pre_topc @ sk_D))),
% 1.12/1.35      inference('sup-', [status(thm)], ['52', '53'])).
% 1.12/1.35  thf('55', plain, ((v2_pre_topc @ sk_A)),
% 1.12/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.12/1.35  thf('56', plain, ((l1_pre_topc @ sk_A)),
% 1.12/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.12/1.35  thf('57', plain, ((v2_pre_topc @ sk_D)),
% 1.12/1.35      inference('demod', [status(thm)], ['54', '55', '56'])).
% 1.12/1.35  thf('58', plain,
% 1.12/1.35      ((~ (v3_pre_topc @ (u1_struct_0 @ sk_D) @ sk_D)
% 1.12/1.35        | ~ (r2_hidden @ sk_F @ (u1_struct_0 @ sk_D))
% 1.12/1.35        | (m1_connsp_2 @ (u1_struct_0 @ sk_D) @ sk_D @ sk_F)
% 1.12/1.35        | (v2_struct_0 @ sk_D))),
% 1.12/1.35      inference('demod', [status(thm)], ['46', '51', '57'])).
% 1.12/1.35  thf('59', plain,
% 1.12/1.35      ((~ (v3_pre_topc @ (k2_struct_0 @ sk_D) @ sk_D)
% 1.12/1.35        | ~ (l1_struct_0 @ sk_D)
% 1.12/1.35        | (v2_struct_0 @ sk_D)
% 1.12/1.35        | (m1_connsp_2 @ (u1_struct_0 @ sk_D) @ sk_D @ sk_F)
% 1.12/1.35        | ~ (r2_hidden @ sk_F @ (u1_struct_0 @ sk_D)))),
% 1.12/1.35      inference('sup-', [status(thm)], ['41', '58'])).
% 1.12/1.35  thf('60', plain, ((l1_pre_topc @ sk_D)),
% 1.12/1.35      inference('demod', [status(thm)], ['49', '50'])).
% 1.12/1.35  thf(dt_l1_pre_topc, axiom,
% 1.12/1.35    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 1.12/1.35  thf('61', plain, (![X7 : $i]: ((l1_struct_0 @ X7) | ~ (l1_pre_topc @ X7))),
% 1.12/1.35      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 1.12/1.35  thf('62', plain, ((l1_struct_0 @ sk_D)),
% 1.12/1.35      inference('sup-', [status(thm)], ['60', '61'])).
% 1.12/1.35  thf('63', plain,
% 1.12/1.35      ((~ (v3_pre_topc @ (k2_struct_0 @ sk_D) @ sk_D)
% 1.12/1.35        | (v2_struct_0 @ sk_D)
% 1.12/1.35        | (m1_connsp_2 @ (u1_struct_0 @ sk_D) @ sk_D @ sk_F)
% 1.12/1.35        | ~ (r2_hidden @ sk_F @ (u1_struct_0 @ sk_D)))),
% 1.12/1.35      inference('demod', [status(thm)], ['59', '62'])).
% 1.12/1.35  thf('64', plain,
% 1.12/1.35      ((~ (v2_pre_topc @ sk_D)
% 1.12/1.35        | ~ (l1_pre_topc @ sk_D)
% 1.12/1.35        | ~ (r2_hidden @ sk_F @ (u1_struct_0 @ sk_D))
% 1.12/1.35        | (m1_connsp_2 @ (u1_struct_0 @ sk_D) @ sk_D @ sk_F)
% 1.12/1.35        | (v2_struct_0 @ sk_D))),
% 1.12/1.35      inference('sup-', [status(thm)], ['40', '63'])).
% 1.12/1.35  thf('65', plain, ((v2_pre_topc @ sk_D)),
% 1.12/1.35      inference('demod', [status(thm)], ['54', '55', '56'])).
% 1.12/1.35  thf('66', plain, ((l1_pre_topc @ sk_D)),
% 1.12/1.35      inference('demod', [status(thm)], ['49', '50'])).
% 1.12/1.35  thf('67', plain,
% 1.12/1.35      ((~ (r2_hidden @ sk_F @ (u1_struct_0 @ sk_D))
% 1.12/1.35        | (m1_connsp_2 @ (u1_struct_0 @ sk_D) @ sk_D @ sk_F)
% 1.12/1.35        | (v2_struct_0 @ sk_D))),
% 1.12/1.35      inference('demod', [status(thm)], ['64', '65', '66'])).
% 1.12/1.35  thf('68', plain, (~ (v2_struct_0 @ sk_D)),
% 1.12/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.12/1.35  thf('69', plain,
% 1.12/1.35      (((m1_connsp_2 @ (u1_struct_0 @ sk_D) @ sk_D @ sk_F)
% 1.12/1.35        | ~ (r2_hidden @ sk_F @ (u1_struct_0 @ sk_D)))),
% 1.12/1.35      inference('clc', [status(thm)], ['67', '68'])).
% 1.12/1.35  thf('70', plain,
% 1.12/1.35      ((~ (r2_hidden @ sk_F @ (k2_struct_0 @ sk_D))
% 1.12/1.35        | ~ (l1_struct_0 @ sk_D)
% 1.12/1.35        | (m1_connsp_2 @ (u1_struct_0 @ sk_D) @ sk_D @ sk_F))),
% 1.12/1.35      inference('sup-', [status(thm)], ['39', '69'])).
% 1.12/1.35  thf('71', plain,
% 1.12/1.35      (![X6 : $i]:
% 1.12/1.35         (((k2_struct_0 @ X6) = (u1_struct_0 @ X6)) | ~ (l1_struct_0 @ X6))),
% 1.12/1.35      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.12/1.35  thf('72', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_D))),
% 1.12/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.12/1.35  thf(t2_subset, axiom,
% 1.12/1.35    (![A:$i,B:$i]:
% 1.12/1.35     ( ( m1_subset_1 @ A @ B ) =>
% 1.12/1.35       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 1.12/1.35  thf('73', plain,
% 1.12/1.35      (![X2 : $i, X3 : $i]:
% 1.12/1.35         ((r2_hidden @ X2 @ X3)
% 1.12/1.35          | (v1_xboole_0 @ X3)
% 1.12/1.35          | ~ (m1_subset_1 @ X2 @ X3))),
% 1.12/1.35      inference('cnf', [status(esa)], [t2_subset])).
% 1.12/1.35  thf('74', plain,
% 1.12/1.35      (((v1_xboole_0 @ (u1_struct_0 @ sk_D))
% 1.12/1.35        | (r2_hidden @ sk_F @ (u1_struct_0 @ sk_D)))),
% 1.12/1.35      inference('sup-', [status(thm)], ['72', '73'])).
% 1.12/1.35  thf('75', plain,
% 1.12/1.35      (((r2_hidden @ sk_F @ (k2_struct_0 @ sk_D))
% 1.12/1.35        | ~ (l1_struct_0 @ sk_D)
% 1.12/1.35        | (v1_xboole_0 @ (u1_struct_0 @ sk_D)))),
% 1.12/1.35      inference('sup+', [status(thm)], ['71', '74'])).
% 1.12/1.35  thf('76', plain, ((l1_struct_0 @ sk_D)),
% 1.12/1.35      inference('sup-', [status(thm)], ['60', '61'])).
% 1.12/1.35  thf('77', plain,
% 1.12/1.35      (((r2_hidden @ sk_F @ (k2_struct_0 @ sk_D))
% 1.12/1.35        | (v1_xboole_0 @ (u1_struct_0 @ sk_D)))),
% 1.12/1.35      inference('demod', [status(thm)], ['75', '76'])).
% 1.12/1.35  thf(fc2_struct_0, axiom,
% 1.12/1.35    (![A:$i]:
% 1.12/1.35     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 1.12/1.35       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 1.12/1.35  thf('78', plain,
% 1.12/1.35      (![X10 : $i]:
% 1.12/1.35         (~ (v1_xboole_0 @ (u1_struct_0 @ X10))
% 1.12/1.35          | ~ (l1_struct_0 @ X10)
% 1.12/1.35          | (v2_struct_0 @ X10))),
% 1.12/1.35      inference('cnf', [status(esa)], [fc2_struct_0])).
% 1.12/1.35  thf('79', plain,
% 1.12/1.35      (((r2_hidden @ sk_F @ (k2_struct_0 @ sk_D))
% 1.12/1.35        | (v2_struct_0 @ sk_D)
% 1.12/1.35        | ~ (l1_struct_0 @ sk_D))),
% 1.12/1.35      inference('sup-', [status(thm)], ['77', '78'])).
% 1.12/1.35  thf('80', plain, ((l1_struct_0 @ sk_D)),
% 1.12/1.35      inference('sup-', [status(thm)], ['60', '61'])).
% 1.12/1.35  thf('81', plain,
% 1.12/1.35      (((r2_hidden @ sk_F @ (k2_struct_0 @ sk_D)) | (v2_struct_0 @ sk_D))),
% 1.12/1.35      inference('demod', [status(thm)], ['79', '80'])).
% 1.12/1.35  thf('82', plain, (~ (v2_struct_0 @ sk_D)),
% 1.12/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.12/1.35  thf('83', plain, ((r2_hidden @ sk_F @ (k2_struct_0 @ sk_D))),
% 1.12/1.35      inference('clc', [status(thm)], ['81', '82'])).
% 1.12/1.35  thf('84', plain, ((l1_struct_0 @ sk_D)),
% 1.12/1.35      inference('sup-', [status(thm)], ['60', '61'])).
% 1.12/1.35  thf('85', plain, ((m1_connsp_2 @ (u1_struct_0 @ sk_D) @ sk_D @ sk_F)),
% 1.12/1.35      inference('demod', [status(thm)], ['70', '83', '84'])).
% 1.12/1.35  thf('86', plain,
% 1.12/1.35      (((g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) = (sk_D))),
% 1.12/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.12/1.35  thf('87', plain,
% 1.12/1.35      (![X19 : $i]: ((m1_pre_topc @ X19 @ X19) | ~ (l1_pre_topc @ X19))),
% 1.12/1.35      inference('cnf', [status(esa)], [t2_tsep_1])).
% 1.12/1.35  thf('88', plain,
% 1.12/1.35      (![X11 : $i, X12 : $i]:
% 1.12/1.35         (~ (l1_pre_topc @ X11)
% 1.12/1.35          | ~ (m1_pre_topc @ X12 @ 
% 1.12/1.35               (g1_pre_topc @ (u1_struct_0 @ X11) @ (u1_pre_topc @ X11)))
% 1.12/1.35          | (m1_pre_topc @ X12 @ X11)
% 1.12/1.35          | ~ (l1_pre_topc @ X12))),
% 1.12/1.35      inference('cnf', [status(esa)], [t65_pre_topc])).
% 1.12/1.35  thf('89', plain,
% 1.12/1.35      (![X0 : $i]:
% 1.12/1.35         (~ (l1_pre_topc @ 
% 1.12/1.35             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 1.12/1.35          | ~ (l1_pre_topc @ 
% 1.12/1.35               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 1.12/1.35          | (m1_pre_topc @ 
% 1.12/1.35             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)) @ X0)
% 1.12/1.35          | ~ (l1_pre_topc @ X0))),
% 1.12/1.35      inference('sup-', [status(thm)], ['87', '88'])).
% 1.12/1.35  thf('90', plain,
% 1.12/1.35      (![X0 : $i]:
% 1.12/1.35         (~ (l1_pre_topc @ X0)
% 1.12/1.35          | (m1_pre_topc @ 
% 1.12/1.35             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)) @ X0)
% 1.12/1.35          | ~ (l1_pre_topc @ 
% 1.12/1.35               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 1.12/1.35      inference('simplify', [status(thm)], ['89'])).
% 1.12/1.35  thf('91', plain,
% 1.12/1.35      ((~ (l1_pre_topc @ sk_D)
% 1.12/1.35        | (m1_pre_topc @ 
% 1.12/1.35           (g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) @ sk_C)
% 1.12/1.35        | ~ (l1_pre_topc @ sk_C))),
% 1.12/1.35      inference('sup-', [status(thm)], ['86', '90'])).
% 1.12/1.35  thf('92', plain, ((l1_pre_topc @ sk_D)),
% 1.12/1.35      inference('demod', [status(thm)], ['49', '50'])).
% 1.12/1.35  thf('93', plain,
% 1.12/1.35      (((g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) = (sk_D))),
% 1.12/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.12/1.35  thf('94', plain, ((l1_pre_topc @ sk_C)),
% 1.12/1.35      inference('demod', [status(thm)], ['32', '33'])).
% 1.12/1.35  thf('95', plain, ((m1_pre_topc @ sk_D @ sk_C)),
% 1.12/1.35      inference('demod', [status(thm)], ['91', '92', '93', '94'])).
% 1.12/1.35  thf(t35_borsuk_1, axiom,
% 1.12/1.35    (![A:$i]:
% 1.12/1.35     ( ( l1_pre_topc @ A ) =>
% 1.12/1.35       ( ![B:$i]:
% 1.12/1.35         ( ( m1_pre_topc @ B @ A ) =>
% 1.12/1.35           ( r1_tarski @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ))).
% 1.12/1.35  thf('96', plain,
% 1.12/1.35      (![X20 : $i, X21 : $i]:
% 1.12/1.35         (~ (m1_pre_topc @ X20 @ X21)
% 1.12/1.35          | (r1_tarski @ (u1_struct_0 @ X20) @ (u1_struct_0 @ X21))
% 1.12/1.35          | ~ (l1_pre_topc @ X21))),
% 1.12/1.35      inference('cnf', [status(esa)], [t35_borsuk_1])).
% 1.12/1.35  thf('97', plain,
% 1.12/1.35      ((~ (l1_pre_topc @ sk_C)
% 1.12/1.35        | (r1_tarski @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_C)))),
% 1.12/1.35      inference('sup-', [status(thm)], ['95', '96'])).
% 1.12/1.35  thf('98', plain, ((l1_pre_topc @ sk_C)),
% 1.12/1.35      inference('demod', [status(thm)], ['32', '33'])).
% 1.12/1.35  thf('99', plain, ((r1_tarski @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_C))),
% 1.12/1.35      inference('demod', [status(thm)], ['97', '98'])).
% 1.12/1.35  thf('100', plain,
% 1.12/1.35      (((v2_struct_0 @ sk_B)
% 1.12/1.35        | (v2_struct_0 @ sk_D)
% 1.12/1.35        | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)
% 1.12/1.35        | (v2_struct_0 @ sk_C)
% 1.12/1.35        | (v2_struct_0 @ sk_A))),
% 1.12/1.35      inference('demod', [status(thm)], ['38', '85', '99'])).
% 1.12/1.35  thf('101', plain, (~ (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)),
% 1.12/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.12/1.35  thf('102', plain,
% 1.12/1.35      (((v2_struct_0 @ sk_A)
% 1.12/1.35        | (v2_struct_0 @ sk_C)
% 1.12/1.35        | (v2_struct_0 @ sk_D)
% 1.12/1.35        | (v2_struct_0 @ sk_B))),
% 1.12/1.35      inference('sup-', [status(thm)], ['100', '101'])).
% 1.12/1.35  thf('103', plain, (~ (v2_struct_0 @ sk_D)),
% 1.12/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.12/1.35  thf('104', plain,
% 1.12/1.35      (((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_A))),
% 1.12/1.35      inference('sup-', [status(thm)], ['102', '103'])).
% 1.12/1.35  thf('105', plain, (~ (v2_struct_0 @ sk_B)),
% 1.12/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.12/1.35  thf('106', plain, (((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_C))),
% 1.12/1.35      inference('clc', [status(thm)], ['104', '105'])).
% 1.12/1.35  thf('107', plain, (~ (v2_struct_0 @ sk_A)),
% 1.12/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.12/1.35  thf('108', plain, ((v2_struct_0 @ sk_C)),
% 1.12/1.35      inference('clc', [status(thm)], ['106', '107'])).
% 1.12/1.35  thf('109', plain, ($false), inference('demod', [status(thm)], ['0', '108'])).
% 1.12/1.35  
% 1.12/1.35  % SZS output end Refutation
% 1.12/1.35  
% 1.12/1.35  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
