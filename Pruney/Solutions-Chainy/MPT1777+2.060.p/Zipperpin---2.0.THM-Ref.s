%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.OE8ONsIj2W

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:10:35 EST 2020

% Result     : Theorem 0.60s
% Output     : Refutation 0.60s
% Verified   : 
% Statistics : Number of formulae       :  158 ( 321 expanded)
%              Number of leaves         :   46 ( 114 expanded)
%              Depth                    :   18
%              Number of atoms          : 1351 (8740 expanded)
%              Number of equality atoms :   16 ( 220 expanded)
%              Maximal formula depth    :   32 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k3_tmap_1_type,type,(
    k3_tmap_1: $i > $i > $i > $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r1_tmap_1_type,type,(
    r1_tmap_1: $i > $i > $i > $i > $o )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_G_type,type,(
    sk_G: $i )).

thf(g1_pre_topc_type,type,(
    g1_pre_topc: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(m1_connsp_2_type,type,(
    m1_connsp_2: $i > $i > $i > $o )).

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
      | ~ ( m1_connsp_2 @ X35 @ X32 @ X38 )
      | ~ ( r1_tarski @ X35 @ ( u1_struct_0 @ X34 ) )
      | ~ ( m1_subset_1 @ X38 @ ( u1_struct_0 @ X32 ) )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X32 ) @ ( u1_struct_0 @ X31 ) ) ) )
      | ~ ( v1_funct_2 @ X37 @ ( u1_struct_0 @ X32 ) @ ( u1_struct_0 @ X31 ) )
      | ~ ( v1_funct_1 @ X37 )
      | ~ ( m1_pre_topc @ X34 @ X33 )
      | ( v2_struct_0 @ X34 )
      | ~ ( l1_pre_topc @ X33 )
      | ~ ( v2_pre_topc @ X33 )
      | ( v2_struct_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t83_tmap_1])).

thf('9',plain,(
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
      | ~ ( r1_tarski @ X35 @ ( u1_struct_0 @ X34 ) )
      | ~ ( m1_connsp_2 @ X35 @ X32 @ X36 )
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
    ! [X27: $i] :
      ( ( m1_pre_topc @ X27 @ X27 )
      | ~ ( l1_pre_topc @ X27 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf(t65_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( l1_pre_topc @ B )
         => ( ( m1_pre_topc @ A @ B )
          <=> ( m1_pre_topc @ A @ ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ) )).

thf('26',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( l1_pre_topc @ X19 )
      | ~ ( m1_pre_topc @ X20 @ X19 )
      | ( m1_pre_topc @ X20 @ ( g1_pre_topc @ ( u1_struct_0 @ X19 ) @ ( u1_pre_topc @ X19 ) ) )
      | ~ ( l1_pre_topc @ X20 ) ) ),
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
    ! [X14: $i,X15: $i] :
      ( ~ ( m1_pre_topc @ X14 @ X15 )
      | ( l1_pre_topc @ X14 )
      | ~ ( l1_pre_topc @ X15 ) ) ),
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
    ! [X12: $i] :
      ( ( ( k2_struct_0 @ X12 )
        = ( u1_struct_0 @ X12 ) )
      | ~ ( l1_struct_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(fc10_tops_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( v3_pre_topc @ ( k2_struct_0 @ A ) @ A ) ) )).

thf('40',plain,(
    ! [X21: $i] :
      ( ( v3_pre_topc @ ( k2_struct_0 @ X21 ) @ X21 )
      | ~ ( l1_pre_topc @ X21 )
      | ~ ( v2_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[fc10_tops_1])).

thf('41',plain,(
    ! [X12: $i] :
      ( ( ( k2_struct_0 @ X12 )
        = ( u1_struct_0 @ X12 ) )
      | ~ ( l1_struct_0 @ X12 ) ) ),
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
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ~ ( v3_pre_topc @ X22 @ X23 )
      | ~ ( r2_hidden @ X24 @ X22 )
      | ( m1_connsp_2 @ X22 @ X23 @ X24 )
      | ~ ( m1_subset_1 @ X24 @ ( u1_struct_0 @ X23 ) )
      | ~ ( l1_pre_topc @ X23 )
      | ~ ( v2_pre_topc @ X23 )
      | ( v2_struct_0 @ X23 ) ) ),
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
    ! [X14: $i,X15: $i] :
      ( ~ ( m1_pre_topc @ X14 @ X15 )
      | ( l1_pre_topc @ X14 )
      | ~ ( l1_pre_topc @ X15 ) ) ),
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
    ! [X10: $i,X11: $i] :
      ( ~ ( m1_pre_topc @ X10 @ X11 )
      | ( v2_pre_topc @ X10 )
      | ~ ( l1_pre_topc @ X11 )
      | ~ ( v2_pre_topc @ X11 ) ) ),
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
    ! [X13: $i] :
      ( ( l1_struct_0 @ X13 )
      | ~ ( l1_pre_topc @ X13 ) ) ),
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
    ! [X12: $i] :
      ( ( ( k2_struct_0 @ X12 )
        = ( u1_struct_0 @ X12 ) )
      | ~ ( l1_struct_0 @ X12 ) ) ),
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
    ! [X16: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X16 ) )
      | ~ ( l1_struct_0 @ X16 )
      | ( v2_struct_0 @ X16 ) ) ),
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

thf('86',plain,(
    ! [X27: $i] :
      ( ( m1_pre_topc @ X27 @ X27 )
      | ~ ( l1_pre_topc @ X27 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('87',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) )
    = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t59_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) )
         => ( m1_pre_topc @ B @ A ) ) ) )).

thf('88',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( m1_pre_topc @ X17 @ ( g1_pre_topc @ ( u1_struct_0 @ X18 ) @ ( u1_pre_topc @ X18 ) ) )
      | ( m1_pre_topc @ X17 @ X18 )
      | ~ ( l1_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[t59_pre_topc])).

thf('89',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_D )
      | ~ ( l1_pre_topc @ sk_C )
      | ( m1_pre_topc @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['32','33'])).

thf('91',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( m1_pre_topc @ X0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['89','90'])).

thf('92',plain,
    ( ~ ( l1_pre_topc @ sk_D )
    | ( m1_pre_topc @ sk_D @ sk_C ) ),
    inference('sup-',[status(thm)],['86','91'])).

thf('93',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['49','50'])).

thf('94',plain,(
    m1_pre_topc @ sk_D @ sk_C ),
    inference(demod,[status(thm)],['92','93'])).

thf(t1_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( m1_subset_1 @ ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('95',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( m1_pre_topc @ X25 @ X26 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X25 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) )
      | ~ ( l1_pre_topc @ X26 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('96',plain,
    ( ~ ( l1_pre_topc @ sk_C )
    | ( m1_subset_1 @ ( u1_struct_0 @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['32','33'])).

thf('98',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['96','97'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('99',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('100',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['38','85','100'])).

thf('102',plain,(
    ~ ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C ) ),
    inference(clc,[status(thm)],['105','106'])).

thf('108',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,(
    v2_struct_0 @ sk_C ),
    inference(clc,[status(thm)],['107','108'])).

thf('110',plain,(
    $false ),
    inference(demod,[status(thm)],['0','109'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.OE8ONsIj2W
% 0.14/0.35  % Computer   : n019.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 16:26:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.22/0.35  % Python version: Python 3.6.8
% 0.22/0.35  % Running in FO mode
% 0.60/0.78  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.60/0.78  % Solved by: fo/fo7.sh
% 0.60/0.78  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.60/0.78  % done 558 iterations in 0.314s
% 0.60/0.78  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.60/0.78  % SZS output start Refutation
% 0.60/0.78  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.60/0.78  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.60/0.78  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.60/0.78  thf(sk_F_type, type, sk_F: $i).
% 0.60/0.78  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.60/0.78  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.60/0.78  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.60/0.78  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.60/0.78  thf(k3_tmap_1_type, type, k3_tmap_1: $i > $i > $i > $i > $i > $i).
% 0.60/0.78  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.60/0.78  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.60/0.78  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.60/0.78  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.60/0.78  thf(sk_A_type, type, sk_A: $i).
% 0.60/0.78  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.60/0.78  thf(r1_tmap_1_type, type, r1_tmap_1: $i > $i > $i > $i > $o).
% 0.60/0.78  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 0.60/0.78  thf(sk_D_type, type, sk_D: $i).
% 0.60/0.78  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.60/0.78  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.60/0.78  thf(sk_E_type, type, sk_E: $i).
% 0.60/0.78  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.60/0.78  thf(sk_C_type, type, sk_C: $i).
% 0.60/0.78  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.60/0.78  thf(sk_B_type, type, sk_B: $i).
% 0.60/0.78  thf(sk_G_type, type, sk_G: $i).
% 0.60/0.78  thf(g1_pre_topc_type, type, g1_pre_topc: $i > $i > $i).
% 0.60/0.78  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.60/0.78  thf(m1_connsp_2_type, type, m1_connsp_2: $i > $i > $i > $o).
% 0.60/0.78  thf(t88_tmap_1, conjecture,
% 0.60/0.78    (![A:$i]:
% 0.60/0.78     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.60/0.78       ( ![B:$i]:
% 0.60/0.78         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.60/0.78             ( l1_pre_topc @ B ) ) =>
% 0.60/0.78           ( ![C:$i]:
% 0.60/0.78             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.60/0.78               ( ![D:$i]:
% 0.60/0.78                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.60/0.78                   ( ![E:$i]:
% 0.60/0.78                     ( ( ( v1_funct_1 @ E ) & 
% 0.60/0.78                         ( v1_funct_2 @
% 0.60/0.78                           E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 0.60/0.78                         ( m1_subset_1 @
% 0.60/0.78                           E @ 
% 0.60/0.78                           ( k1_zfmisc_1 @
% 0.60/0.78                             ( k2_zfmisc_1 @
% 0.60/0.78                               ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.60/0.78                       ( ( ( g1_pre_topc @
% 0.60/0.78                             ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) ) =
% 0.60/0.78                           ( D ) ) =>
% 0.60/0.78                         ( ![F:$i]:
% 0.60/0.78                           ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 0.60/0.78                             ( ![G:$i]:
% 0.60/0.78                               ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) ) =>
% 0.60/0.78                                 ( ( ( ( F ) = ( G ) ) & 
% 0.60/0.78                                     ( r1_tmap_1 @
% 0.60/0.78                                       C @ B @ 
% 0.60/0.78                                       ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ G ) ) =>
% 0.60/0.78                                   ( r1_tmap_1 @ D @ B @ E @ F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.60/0.78  thf(zf_stmt_0, negated_conjecture,
% 0.60/0.78    (~( ![A:$i]:
% 0.60/0.78        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.60/0.78            ( l1_pre_topc @ A ) ) =>
% 0.60/0.78          ( ![B:$i]:
% 0.60/0.78            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.60/0.78                ( l1_pre_topc @ B ) ) =>
% 0.60/0.78              ( ![C:$i]:
% 0.60/0.78                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.60/0.78                  ( ![D:$i]:
% 0.60/0.78                    ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.60/0.78                      ( ![E:$i]:
% 0.60/0.78                        ( ( ( v1_funct_1 @ E ) & 
% 0.60/0.78                            ( v1_funct_2 @
% 0.60/0.78                              E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 0.60/0.78                            ( m1_subset_1 @
% 0.60/0.78                              E @ 
% 0.60/0.78                              ( k1_zfmisc_1 @
% 0.60/0.78                                ( k2_zfmisc_1 @
% 0.60/0.78                                  ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.60/0.78                          ( ( ( g1_pre_topc @
% 0.60/0.78                                ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) ) =
% 0.60/0.78                              ( D ) ) =>
% 0.60/0.78                            ( ![F:$i]:
% 0.60/0.78                              ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 0.60/0.78                                ( ![G:$i]:
% 0.60/0.78                                  ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) ) =>
% 0.60/0.78                                    ( ( ( ( F ) = ( G ) ) & 
% 0.60/0.78                                        ( r1_tmap_1 @
% 0.60/0.78                                          C @ B @ 
% 0.60/0.78                                          ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ G ) ) =>
% 0.60/0.78                                      ( r1_tmap_1 @ D @ B @ E @ F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.60/0.78    inference('cnf.neg', [status(esa)], [t88_tmap_1])).
% 0.60/0.78  thf('0', plain, (~ (v2_struct_0 @ sk_C)),
% 0.60/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.78  thf(dt_k2_subset_1, axiom,
% 0.60/0.78    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.60/0.78  thf('1', plain,
% 0.60/0.78      (![X1 : $i]: (m1_subset_1 @ (k2_subset_1 @ X1) @ (k1_zfmisc_1 @ X1))),
% 0.60/0.78      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 0.60/0.78  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.60/0.78  thf('2', plain, (![X0 : $i]: ((k2_subset_1 @ X0) = (X0))),
% 0.60/0.78      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.60/0.78  thf('3', plain, (![X1 : $i]: (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X1))),
% 0.60/0.78      inference('demod', [status(thm)], ['1', '2'])).
% 0.60/0.78  thf('4', plain,
% 0.60/0.78      ((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.60/0.78        (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_G)),
% 0.60/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.78  thf('5', plain, (((sk_F) = (sk_G))),
% 0.60/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.78  thf('6', plain,
% 0.60/0.78      ((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.60/0.78        (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_F)),
% 0.60/0.78      inference('demod', [status(thm)], ['4', '5'])).
% 0.60/0.78  thf('7', plain,
% 0.60/0.78      ((m1_subset_1 @ sk_E @ 
% 0.60/0.78        (k1_zfmisc_1 @ 
% 0.60/0.78         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 0.60/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.78  thf(t83_tmap_1, axiom,
% 0.60/0.78    (![A:$i]:
% 0.60/0.78     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.60/0.78       ( ![B:$i]:
% 0.60/0.78         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.60/0.78             ( l1_pre_topc @ B ) ) =>
% 0.60/0.78           ( ![C:$i]:
% 0.60/0.78             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.60/0.78               ( ![D:$i]:
% 0.60/0.78                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.60/0.78                   ( ![E:$i]:
% 0.60/0.78                     ( ( ( v1_funct_1 @ E ) & 
% 0.60/0.78                         ( v1_funct_2 @
% 0.60/0.78                           E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 0.60/0.78                         ( m1_subset_1 @
% 0.60/0.78                           E @ 
% 0.60/0.78                           ( k1_zfmisc_1 @
% 0.60/0.78                             ( k2_zfmisc_1 @
% 0.60/0.78                               ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.60/0.78                       ( ( m1_pre_topc @ C @ D ) =>
% 0.60/0.78                         ( ![F:$i]:
% 0.60/0.78                           ( ( m1_subset_1 @
% 0.60/0.78                               F @ ( k1_zfmisc_1 @ ( u1_struct_0 @ D ) ) ) =>
% 0.60/0.78                             ( ![G:$i]:
% 0.60/0.78                               ( ( m1_subset_1 @ G @ ( u1_struct_0 @ D ) ) =>
% 0.60/0.78                                 ( ![H:$i]:
% 0.60/0.78                                   ( ( m1_subset_1 @ H @ ( u1_struct_0 @ C ) ) =>
% 0.60/0.78                                     ( ( ( r1_tarski @ F @ ( u1_struct_0 @ C ) ) & 
% 0.60/0.78                                         ( m1_connsp_2 @ F @ D @ G ) & 
% 0.60/0.78                                         ( ( G ) = ( H ) ) ) =>
% 0.60/0.78                                       ( ( r1_tmap_1 @ D @ B @ E @ G ) <=>
% 0.60/0.78                                         ( r1_tmap_1 @
% 0.60/0.78                                           C @ B @ 
% 0.60/0.78                                           ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ 
% 0.60/0.78                                           H ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.60/0.78  thf('8', plain,
% 0.60/0.78      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i, X35 : $i, X36 : $i, X37 : $i, 
% 0.60/0.78         X38 : $i]:
% 0.60/0.78         ((v2_struct_0 @ X31)
% 0.60/0.78          | ~ (v2_pre_topc @ X31)
% 0.60/0.78          | ~ (l1_pre_topc @ X31)
% 0.60/0.78          | (v2_struct_0 @ X32)
% 0.60/0.78          | ~ (m1_pre_topc @ X32 @ X33)
% 0.60/0.78          | ~ (m1_pre_topc @ X34 @ X32)
% 0.60/0.78          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (u1_struct_0 @ X32)))
% 0.60/0.78          | ~ (m1_subset_1 @ X36 @ (u1_struct_0 @ X34))
% 0.60/0.78          | ~ (r1_tmap_1 @ X34 @ X31 @ 
% 0.60/0.78               (k3_tmap_1 @ X33 @ X31 @ X32 @ X34 @ X37) @ X36)
% 0.60/0.78          | (r1_tmap_1 @ X32 @ X31 @ X37 @ X38)
% 0.60/0.78          | ((X38) != (X36))
% 0.60/0.78          | ~ (m1_connsp_2 @ X35 @ X32 @ X38)
% 0.60/0.78          | ~ (r1_tarski @ X35 @ (u1_struct_0 @ X34))
% 0.60/0.78          | ~ (m1_subset_1 @ X38 @ (u1_struct_0 @ X32))
% 0.60/0.78          | ~ (m1_subset_1 @ X37 @ 
% 0.60/0.78               (k1_zfmisc_1 @ 
% 0.60/0.78                (k2_zfmisc_1 @ (u1_struct_0 @ X32) @ (u1_struct_0 @ X31))))
% 0.60/0.78          | ~ (v1_funct_2 @ X37 @ (u1_struct_0 @ X32) @ (u1_struct_0 @ X31))
% 0.60/0.78          | ~ (v1_funct_1 @ X37)
% 0.60/0.78          | ~ (m1_pre_topc @ X34 @ X33)
% 0.60/0.78          | (v2_struct_0 @ X34)
% 0.60/0.78          | ~ (l1_pre_topc @ X33)
% 0.60/0.78          | ~ (v2_pre_topc @ X33)
% 0.60/0.78          | (v2_struct_0 @ X33))),
% 0.60/0.78      inference('cnf', [status(esa)], [t83_tmap_1])).
% 0.60/0.78  thf('9', plain,
% 0.60/0.78      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i, X35 : $i, X36 : $i, X37 : $i]:
% 0.60/0.78         ((v2_struct_0 @ X33)
% 0.60/0.78          | ~ (v2_pre_topc @ X33)
% 0.60/0.78          | ~ (l1_pre_topc @ X33)
% 0.60/0.78          | (v2_struct_0 @ X34)
% 0.60/0.78          | ~ (m1_pre_topc @ X34 @ X33)
% 0.60/0.78          | ~ (v1_funct_1 @ X37)
% 0.60/0.78          | ~ (v1_funct_2 @ X37 @ (u1_struct_0 @ X32) @ (u1_struct_0 @ X31))
% 0.60/0.78          | ~ (m1_subset_1 @ X37 @ 
% 0.60/0.78               (k1_zfmisc_1 @ 
% 0.60/0.78                (k2_zfmisc_1 @ (u1_struct_0 @ X32) @ (u1_struct_0 @ X31))))
% 0.60/0.78          | ~ (m1_subset_1 @ X36 @ (u1_struct_0 @ X32))
% 0.60/0.78          | ~ (r1_tarski @ X35 @ (u1_struct_0 @ X34))
% 0.60/0.78          | ~ (m1_connsp_2 @ X35 @ X32 @ X36)
% 0.60/0.78          | (r1_tmap_1 @ X32 @ X31 @ X37 @ X36)
% 0.60/0.78          | ~ (r1_tmap_1 @ X34 @ X31 @ 
% 0.60/0.78               (k3_tmap_1 @ X33 @ X31 @ X32 @ X34 @ X37) @ X36)
% 0.60/0.78          | ~ (m1_subset_1 @ X36 @ (u1_struct_0 @ X34))
% 0.60/0.78          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (u1_struct_0 @ X32)))
% 0.60/0.78          | ~ (m1_pre_topc @ X34 @ X32)
% 0.60/0.78          | ~ (m1_pre_topc @ X32 @ X33)
% 0.60/0.78          | (v2_struct_0 @ X32)
% 0.60/0.78          | ~ (l1_pre_topc @ X31)
% 0.60/0.78          | ~ (v2_pre_topc @ X31)
% 0.60/0.78          | (v2_struct_0 @ X31))),
% 0.60/0.78      inference('simplify', [status(thm)], ['8'])).
% 0.60/0.78  thf('10', plain,
% 0.60/0.78      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.60/0.78         ((v2_struct_0 @ sk_B)
% 0.60/0.78          | ~ (v2_pre_topc @ sk_B)
% 0.60/0.78          | ~ (l1_pre_topc @ sk_B)
% 0.60/0.78          | (v2_struct_0 @ sk_D)
% 0.60/0.78          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.60/0.78          | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.60/0.78          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))
% 0.60/0.78          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X1))
% 0.60/0.78          | ~ (r1_tmap_1 @ X1 @ sk_B @ 
% 0.60/0.78               (k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E) @ X3)
% 0.60/0.78          | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X3)
% 0.60/0.78          | ~ (m1_connsp_2 @ X2 @ sk_D @ X3)
% 0.60/0.78          | ~ (r1_tarski @ X2 @ (u1_struct_0 @ X1))
% 0.60/0.78          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ sk_D))
% 0.60/0.78          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.60/0.78          | ~ (v1_funct_1 @ sk_E)
% 0.60/0.78          | ~ (m1_pre_topc @ X1 @ X0)
% 0.60/0.78          | (v2_struct_0 @ X1)
% 0.60/0.78          | ~ (l1_pre_topc @ X0)
% 0.60/0.78          | ~ (v2_pre_topc @ X0)
% 0.60/0.78          | (v2_struct_0 @ X0))),
% 0.60/0.78      inference('sup-', [status(thm)], ['7', '9'])).
% 0.60/0.78  thf('11', plain, ((v2_pre_topc @ sk_B)),
% 0.60/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.78  thf('12', plain, ((l1_pre_topc @ sk_B)),
% 0.60/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.78  thf('13', plain,
% 0.60/0.78      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 0.60/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.78  thf('14', plain, ((v1_funct_1 @ sk_E)),
% 0.60/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.78  thf('15', plain,
% 0.60/0.78      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.60/0.78         ((v2_struct_0 @ sk_B)
% 0.60/0.78          | (v2_struct_0 @ sk_D)
% 0.60/0.78          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.60/0.78          | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.60/0.78          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))
% 0.60/0.78          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X1))
% 0.60/0.78          | ~ (r1_tmap_1 @ X1 @ sk_B @ 
% 0.60/0.78               (k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E) @ X3)
% 0.60/0.78          | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X3)
% 0.60/0.78          | ~ (m1_connsp_2 @ X2 @ sk_D @ X3)
% 0.60/0.78          | ~ (r1_tarski @ X2 @ (u1_struct_0 @ X1))
% 0.60/0.78          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ sk_D))
% 0.60/0.78          | ~ (m1_pre_topc @ X1 @ X0)
% 0.60/0.78          | (v2_struct_0 @ X1)
% 0.60/0.78          | ~ (l1_pre_topc @ X0)
% 0.60/0.78          | ~ (v2_pre_topc @ X0)
% 0.60/0.78          | (v2_struct_0 @ X0))),
% 0.60/0.78      inference('demod', [status(thm)], ['10', '11', '12', '13', '14'])).
% 0.60/0.78  thf('16', plain,
% 0.60/0.78      (![X0 : $i]:
% 0.60/0.78         ((v2_struct_0 @ sk_A)
% 0.60/0.78          | ~ (v2_pre_topc @ sk_A)
% 0.60/0.78          | ~ (l1_pre_topc @ sk_A)
% 0.60/0.78          | (v2_struct_0 @ sk_C)
% 0.60/0.78          | ~ (m1_pre_topc @ sk_C @ sk_A)
% 0.60/0.78          | ~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_D))
% 0.60/0.78          | ~ (r1_tarski @ X0 @ (u1_struct_0 @ sk_C))
% 0.60/0.78          | ~ (m1_connsp_2 @ X0 @ sk_D @ sk_F)
% 0.60/0.78          | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)
% 0.60/0.78          | ~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C))
% 0.60/0.78          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))
% 0.60/0.78          | ~ (m1_pre_topc @ sk_C @ sk_D)
% 0.60/0.78          | ~ (m1_pre_topc @ sk_D @ sk_A)
% 0.60/0.78          | (v2_struct_0 @ sk_D)
% 0.60/0.78          | (v2_struct_0 @ sk_B))),
% 0.60/0.78      inference('sup-', [status(thm)], ['6', '15'])).
% 0.60/0.78  thf('17', plain, ((v2_pre_topc @ sk_A)),
% 0.60/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.78  thf('18', plain, ((l1_pre_topc @ sk_A)),
% 0.60/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.78  thf('19', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.60/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.78  thf('20', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_D))),
% 0.60/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.78  thf('21', plain, ((m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_C))),
% 0.60/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.78  thf('22', plain, (((sk_F) = (sk_G))),
% 0.60/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.78  thf('23', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C))),
% 0.60/0.78      inference('demod', [status(thm)], ['21', '22'])).
% 0.60/0.78  thf('24', plain,
% 0.60/0.78      (((g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) = (sk_D))),
% 0.60/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.78  thf(t2_tsep_1, axiom,
% 0.60/0.78    (![A:$i]: ( ( l1_pre_topc @ A ) => ( m1_pre_topc @ A @ A ) ))).
% 0.60/0.78  thf('25', plain,
% 0.60/0.78      (![X27 : $i]: ((m1_pre_topc @ X27 @ X27) | ~ (l1_pre_topc @ X27))),
% 0.60/0.78      inference('cnf', [status(esa)], [t2_tsep_1])).
% 0.60/0.78  thf(t65_pre_topc, axiom,
% 0.60/0.78    (![A:$i]:
% 0.60/0.78     ( ( l1_pre_topc @ A ) =>
% 0.60/0.78       ( ![B:$i]:
% 0.60/0.78         ( ( l1_pre_topc @ B ) =>
% 0.60/0.78           ( ( m1_pre_topc @ A @ B ) <=>
% 0.60/0.78             ( m1_pre_topc @
% 0.60/0.78               A @ ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ) ))).
% 0.60/0.78  thf('26', plain,
% 0.60/0.78      (![X19 : $i, X20 : $i]:
% 0.60/0.78         (~ (l1_pre_topc @ X19)
% 0.60/0.78          | ~ (m1_pre_topc @ X20 @ X19)
% 0.60/0.78          | (m1_pre_topc @ X20 @ 
% 0.60/0.78             (g1_pre_topc @ (u1_struct_0 @ X19) @ (u1_pre_topc @ X19)))
% 0.60/0.78          | ~ (l1_pre_topc @ X20))),
% 0.60/0.78      inference('cnf', [status(esa)], [t65_pre_topc])).
% 0.60/0.78  thf('27', plain,
% 0.60/0.78      (![X0 : $i]:
% 0.60/0.78         (~ (l1_pre_topc @ X0)
% 0.60/0.78          | ~ (l1_pre_topc @ X0)
% 0.60/0.78          | (m1_pre_topc @ X0 @ 
% 0.60/0.78             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.60/0.78          | ~ (l1_pre_topc @ X0))),
% 0.60/0.78      inference('sup-', [status(thm)], ['25', '26'])).
% 0.60/0.78  thf('28', plain,
% 0.60/0.78      (![X0 : $i]:
% 0.60/0.78         ((m1_pre_topc @ X0 @ 
% 0.60/0.78           (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.60/0.78          | ~ (l1_pre_topc @ X0))),
% 0.60/0.78      inference('simplify', [status(thm)], ['27'])).
% 0.60/0.78  thf('29', plain, (((m1_pre_topc @ sk_C @ sk_D) | ~ (l1_pre_topc @ sk_C))),
% 0.60/0.78      inference('sup+', [status(thm)], ['24', '28'])).
% 0.60/0.78  thf('30', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.60/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.78  thf(dt_m1_pre_topc, axiom,
% 0.60/0.78    (![A:$i]:
% 0.60/0.78     ( ( l1_pre_topc @ A ) =>
% 0.60/0.78       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.60/0.78  thf('31', plain,
% 0.60/0.78      (![X14 : $i, X15 : $i]:
% 0.60/0.78         (~ (m1_pre_topc @ X14 @ X15)
% 0.60/0.78          | (l1_pre_topc @ X14)
% 0.60/0.78          | ~ (l1_pre_topc @ X15))),
% 0.60/0.78      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.60/0.78  thf('32', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_C))),
% 0.60/0.78      inference('sup-', [status(thm)], ['30', '31'])).
% 0.60/0.78  thf('33', plain, ((l1_pre_topc @ sk_A)),
% 0.60/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.78  thf('34', plain, ((l1_pre_topc @ sk_C)),
% 0.60/0.78      inference('demod', [status(thm)], ['32', '33'])).
% 0.60/0.78  thf('35', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 0.60/0.78      inference('demod', [status(thm)], ['29', '34'])).
% 0.60/0.78  thf('36', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.60/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.78  thf('37', plain,
% 0.60/0.78      (![X0 : $i]:
% 0.60/0.78         ((v2_struct_0 @ sk_A)
% 0.60/0.78          | (v2_struct_0 @ sk_C)
% 0.60/0.78          | ~ (r1_tarski @ X0 @ (u1_struct_0 @ sk_C))
% 0.60/0.78          | ~ (m1_connsp_2 @ X0 @ sk_D @ sk_F)
% 0.60/0.78          | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)
% 0.60/0.78          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))
% 0.60/0.78          | (v2_struct_0 @ sk_D)
% 0.60/0.78          | (v2_struct_0 @ sk_B))),
% 0.60/0.78      inference('demod', [status(thm)],
% 0.60/0.78                ['16', '17', '18', '19', '20', '23', '35', '36'])).
% 0.60/0.78  thf('38', plain,
% 0.60/0.78      (((v2_struct_0 @ sk_B)
% 0.60/0.78        | (v2_struct_0 @ sk_D)
% 0.60/0.78        | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)
% 0.60/0.78        | ~ (m1_connsp_2 @ (u1_struct_0 @ sk_D) @ sk_D @ sk_F)
% 0.60/0.78        | ~ (r1_tarski @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_C))
% 0.60/0.78        | (v2_struct_0 @ sk_C)
% 0.60/0.78        | (v2_struct_0 @ sk_A))),
% 0.60/0.78      inference('sup-', [status(thm)], ['3', '37'])).
% 0.60/0.78  thf(d3_struct_0, axiom,
% 0.60/0.78    (![A:$i]:
% 0.60/0.78     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.60/0.78  thf('39', plain,
% 0.60/0.78      (![X12 : $i]:
% 0.60/0.78         (((k2_struct_0 @ X12) = (u1_struct_0 @ X12)) | ~ (l1_struct_0 @ X12))),
% 0.60/0.78      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.60/0.78  thf(fc10_tops_1, axiom,
% 0.60/0.78    (![A:$i]:
% 0.60/0.78     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.60/0.78       ( v3_pre_topc @ ( k2_struct_0 @ A ) @ A ) ))).
% 0.60/0.78  thf('40', plain,
% 0.60/0.78      (![X21 : $i]:
% 0.60/0.78         ((v3_pre_topc @ (k2_struct_0 @ X21) @ X21)
% 0.60/0.78          | ~ (l1_pre_topc @ X21)
% 0.60/0.78          | ~ (v2_pre_topc @ X21))),
% 0.60/0.78      inference('cnf', [status(esa)], [fc10_tops_1])).
% 0.60/0.78  thf('41', plain,
% 0.60/0.78      (![X12 : $i]:
% 0.60/0.78         (((k2_struct_0 @ X12) = (u1_struct_0 @ X12)) | ~ (l1_struct_0 @ X12))),
% 0.60/0.78      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.60/0.78  thf('42', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_D))),
% 0.60/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.78  thf('43', plain, (![X1 : $i]: (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X1))),
% 0.60/0.78      inference('demod', [status(thm)], ['1', '2'])).
% 0.60/0.78  thf(t5_connsp_2, axiom,
% 0.60/0.78    (![A:$i]:
% 0.60/0.78     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.60/0.78       ( ![B:$i]:
% 0.60/0.78         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.60/0.78           ( ![C:$i]:
% 0.60/0.78             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.60/0.78               ( ( ( v3_pre_topc @ B @ A ) & ( r2_hidden @ C @ B ) ) =>
% 0.60/0.78                 ( m1_connsp_2 @ B @ A @ C ) ) ) ) ) ) ))).
% 0.60/0.78  thf('44', plain,
% 0.60/0.78      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.60/0.78         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 0.60/0.78          | ~ (v3_pre_topc @ X22 @ X23)
% 0.60/0.78          | ~ (r2_hidden @ X24 @ X22)
% 0.60/0.78          | (m1_connsp_2 @ X22 @ X23 @ X24)
% 0.60/0.78          | ~ (m1_subset_1 @ X24 @ (u1_struct_0 @ X23))
% 0.60/0.78          | ~ (l1_pre_topc @ X23)
% 0.60/0.78          | ~ (v2_pre_topc @ X23)
% 0.60/0.78          | (v2_struct_0 @ X23))),
% 0.60/0.78      inference('cnf', [status(esa)], [t5_connsp_2])).
% 0.60/0.78  thf('45', plain,
% 0.60/0.78      (![X0 : $i, X1 : $i]:
% 0.60/0.78         ((v2_struct_0 @ X0)
% 0.60/0.78          | ~ (v2_pre_topc @ X0)
% 0.60/0.78          | ~ (l1_pre_topc @ X0)
% 0.60/0.78          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.60/0.78          | (m1_connsp_2 @ (u1_struct_0 @ X0) @ X0 @ X1)
% 0.60/0.78          | ~ (r2_hidden @ X1 @ (u1_struct_0 @ X0))
% 0.60/0.78          | ~ (v3_pre_topc @ (u1_struct_0 @ X0) @ X0))),
% 0.60/0.78      inference('sup-', [status(thm)], ['43', '44'])).
% 0.60/0.78  thf('46', plain,
% 0.60/0.78      ((~ (v3_pre_topc @ (u1_struct_0 @ sk_D) @ sk_D)
% 0.60/0.78        | ~ (r2_hidden @ sk_F @ (u1_struct_0 @ sk_D))
% 0.60/0.78        | (m1_connsp_2 @ (u1_struct_0 @ sk_D) @ sk_D @ sk_F)
% 0.60/0.78        | ~ (l1_pre_topc @ sk_D)
% 0.60/0.78        | ~ (v2_pre_topc @ sk_D)
% 0.60/0.78        | (v2_struct_0 @ sk_D))),
% 0.60/0.78      inference('sup-', [status(thm)], ['42', '45'])).
% 0.60/0.78  thf('47', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.60/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.78  thf('48', plain,
% 0.60/0.78      (![X14 : $i, X15 : $i]:
% 0.60/0.78         (~ (m1_pre_topc @ X14 @ X15)
% 0.60/0.78          | (l1_pre_topc @ X14)
% 0.60/0.78          | ~ (l1_pre_topc @ X15))),
% 0.60/0.78      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.60/0.78  thf('49', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_D))),
% 0.60/0.78      inference('sup-', [status(thm)], ['47', '48'])).
% 0.60/0.78  thf('50', plain, ((l1_pre_topc @ sk_A)),
% 0.60/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.78  thf('51', plain, ((l1_pre_topc @ sk_D)),
% 0.60/0.78      inference('demod', [status(thm)], ['49', '50'])).
% 0.60/0.78  thf('52', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.60/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.78  thf(cc1_pre_topc, axiom,
% 0.60/0.78    (![A:$i]:
% 0.60/0.78     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.60/0.78       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( v2_pre_topc @ B ) ) ) ))).
% 0.60/0.78  thf('53', plain,
% 0.60/0.78      (![X10 : $i, X11 : $i]:
% 0.60/0.78         (~ (m1_pre_topc @ X10 @ X11)
% 0.60/0.78          | (v2_pre_topc @ X10)
% 0.60/0.78          | ~ (l1_pre_topc @ X11)
% 0.60/0.78          | ~ (v2_pre_topc @ X11))),
% 0.60/0.78      inference('cnf', [status(esa)], [cc1_pre_topc])).
% 0.60/0.78  thf('54', plain,
% 0.60/0.78      ((~ (v2_pre_topc @ sk_A) | ~ (l1_pre_topc @ sk_A) | (v2_pre_topc @ sk_D))),
% 0.60/0.78      inference('sup-', [status(thm)], ['52', '53'])).
% 0.60/0.78  thf('55', plain, ((v2_pre_topc @ sk_A)),
% 0.60/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.78  thf('56', plain, ((l1_pre_topc @ sk_A)),
% 0.60/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.78  thf('57', plain, ((v2_pre_topc @ sk_D)),
% 0.60/0.78      inference('demod', [status(thm)], ['54', '55', '56'])).
% 0.60/0.78  thf('58', plain,
% 0.60/0.78      ((~ (v3_pre_topc @ (u1_struct_0 @ sk_D) @ sk_D)
% 0.60/0.78        | ~ (r2_hidden @ sk_F @ (u1_struct_0 @ sk_D))
% 0.60/0.78        | (m1_connsp_2 @ (u1_struct_0 @ sk_D) @ sk_D @ sk_F)
% 0.60/0.78        | (v2_struct_0 @ sk_D))),
% 0.60/0.78      inference('demod', [status(thm)], ['46', '51', '57'])).
% 0.60/0.78  thf('59', plain,
% 0.60/0.78      ((~ (v3_pre_topc @ (k2_struct_0 @ sk_D) @ sk_D)
% 0.60/0.78        | ~ (l1_struct_0 @ sk_D)
% 0.60/0.78        | (v2_struct_0 @ sk_D)
% 0.60/0.78        | (m1_connsp_2 @ (u1_struct_0 @ sk_D) @ sk_D @ sk_F)
% 0.60/0.78        | ~ (r2_hidden @ sk_F @ (u1_struct_0 @ sk_D)))),
% 0.60/0.78      inference('sup-', [status(thm)], ['41', '58'])).
% 0.60/0.78  thf('60', plain, ((l1_pre_topc @ sk_D)),
% 0.60/0.78      inference('demod', [status(thm)], ['49', '50'])).
% 0.60/0.78  thf(dt_l1_pre_topc, axiom,
% 0.60/0.78    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.60/0.78  thf('61', plain,
% 0.60/0.78      (![X13 : $i]: ((l1_struct_0 @ X13) | ~ (l1_pre_topc @ X13))),
% 0.60/0.78      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.60/0.78  thf('62', plain, ((l1_struct_0 @ sk_D)),
% 0.60/0.78      inference('sup-', [status(thm)], ['60', '61'])).
% 0.60/0.78  thf('63', plain,
% 0.60/0.78      ((~ (v3_pre_topc @ (k2_struct_0 @ sk_D) @ sk_D)
% 0.60/0.78        | (v2_struct_0 @ sk_D)
% 0.60/0.78        | (m1_connsp_2 @ (u1_struct_0 @ sk_D) @ sk_D @ sk_F)
% 0.60/0.78        | ~ (r2_hidden @ sk_F @ (u1_struct_0 @ sk_D)))),
% 0.60/0.78      inference('demod', [status(thm)], ['59', '62'])).
% 0.60/0.78  thf('64', plain,
% 0.60/0.78      ((~ (v2_pre_topc @ sk_D)
% 0.60/0.78        | ~ (l1_pre_topc @ sk_D)
% 0.60/0.78        | ~ (r2_hidden @ sk_F @ (u1_struct_0 @ sk_D))
% 0.60/0.78        | (m1_connsp_2 @ (u1_struct_0 @ sk_D) @ sk_D @ sk_F)
% 0.60/0.78        | (v2_struct_0 @ sk_D))),
% 0.60/0.78      inference('sup-', [status(thm)], ['40', '63'])).
% 0.60/0.78  thf('65', plain, ((v2_pre_topc @ sk_D)),
% 0.60/0.78      inference('demod', [status(thm)], ['54', '55', '56'])).
% 0.60/0.78  thf('66', plain, ((l1_pre_topc @ sk_D)),
% 0.60/0.78      inference('demod', [status(thm)], ['49', '50'])).
% 0.60/0.78  thf('67', plain,
% 0.60/0.78      ((~ (r2_hidden @ sk_F @ (u1_struct_0 @ sk_D))
% 0.60/0.78        | (m1_connsp_2 @ (u1_struct_0 @ sk_D) @ sk_D @ sk_F)
% 0.60/0.78        | (v2_struct_0 @ sk_D))),
% 0.60/0.78      inference('demod', [status(thm)], ['64', '65', '66'])).
% 0.60/0.78  thf('68', plain, (~ (v2_struct_0 @ sk_D)),
% 0.60/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.78  thf('69', plain,
% 0.60/0.78      (((m1_connsp_2 @ (u1_struct_0 @ sk_D) @ sk_D @ sk_F)
% 0.60/0.78        | ~ (r2_hidden @ sk_F @ (u1_struct_0 @ sk_D)))),
% 0.60/0.78      inference('clc', [status(thm)], ['67', '68'])).
% 0.60/0.78  thf('70', plain,
% 0.60/0.78      ((~ (r2_hidden @ sk_F @ (k2_struct_0 @ sk_D))
% 0.60/0.78        | ~ (l1_struct_0 @ sk_D)
% 0.60/0.78        | (m1_connsp_2 @ (u1_struct_0 @ sk_D) @ sk_D @ sk_F))),
% 0.60/0.78      inference('sup-', [status(thm)], ['39', '69'])).
% 0.60/0.78  thf('71', plain,
% 0.60/0.78      (![X12 : $i]:
% 0.60/0.78         (((k2_struct_0 @ X12) = (u1_struct_0 @ X12)) | ~ (l1_struct_0 @ X12))),
% 0.60/0.78      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.60/0.78  thf('72', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_D))),
% 0.60/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.78  thf(t2_subset, axiom,
% 0.60/0.78    (![A:$i,B:$i]:
% 0.60/0.78     ( ( m1_subset_1 @ A @ B ) =>
% 0.60/0.78       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.60/0.78  thf('73', plain,
% 0.60/0.78      (![X2 : $i, X3 : $i]:
% 0.60/0.78         ((r2_hidden @ X2 @ X3)
% 0.60/0.78          | (v1_xboole_0 @ X3)
% 0.60/0.78          | ~ (m1_subset_1 @ X2 @ X3))),
% 0.60/0.78      inference('cnf', [status(esa)], [t2_subset])).
% 0.60/0.78  thf('74', plain,
% 0.60/0.78      (((v1_xboole_0 @ (u1_struct_0 @ sk_D))
% 0.60/0.78        | (r2_hidden @ sk_F @ (u1_struct_0 @ sk_D)))),
% 0.60/0.78      inference('sup-', [status(thm)], ['72', '73'])).
% 0.60/0.78  thf('75', plain,
% 0.60/0.78      (((r2_hidden @ sk_F @ (k2_struct_0 @ sk_D))
% 0.60/0.78        | ~ (l1_struct_0 @ sk_D)
% 0.60/0.78        | (v1_xboole_0 @ (u1_struct_0 @ sk_D)))),
% 0.60/0.78      inference('sup+', [status(thm)], ['71', '74'])).
% 0.60/0.78  thf('76', plain, ((l1_struct_0 @ sk_D)),
% 0.60/0.78      inference('sup-', [status(thm)], ['60', '61'])).
% 0.60/0.78  thf('77', plain,
% 0.60/0.78      (((r2_hidden @ sk_F @ (k2_struct_0 @ sk_D))
% 0.60/0.78        | (v1_xboole_0 @ (u1_struct_0 @ sk_D)))),
% 0.60/0.78      inference('demod', [status(thm)], ['75', '76'])).
% 0.60/0.78  thf(fc2_struct_0, axiom,
% 0.60/0.78    (![A:$i]:
% 0.60/0.78     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.60/0.78       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.60/0.78  thf('78', plain,
% 0.60/0.78      (![X16 : $i]:
% 0.60/0.78         (~ (v1_xboole_0 @ (u1_struct_0 @ X16))
% 0.60/0.78          | ~ (l1_struct_0 @ X16)
% 0.60/0.78          | (v2_struct_0 @ X16))),
% 0.60/0.78      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.60/0.78  thf('79', plain,
% 0.60/0.78      (((r2_hidden @ sk_F @ (k2_struct_0 @ sk_D))
% 0.60/0.78        | (v2_struct_0 @ sk_D)
% 0.60/0.78        | ~ (l1_struct_0 @ sk_D))),
% 0.60/0.78      inference('sup-', [status(thm)], ['77', '78'])).
% 0.60/0.78  thf('80', plain, ((l1_struct_0 @ sk_D)),
% 0.60/0.78      inference('sup-', [status(thm)], ['60', '61'])).
% 0.60/0.78  thf('81', plain,
% 0.60/0.78      (((r2_hidden @ sk_F @ (k2_struct_0 @ sk_D)) | (v2_struct_0 @ sk_D))),
% 0.60/0.78      inference('demod', [status(thm)], ['79', '80'])).
% 0.60/0.78  thf('82', plain, (~ (v2_struct_0 @ sk_D)),
% 0.60/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.78  thf('83', plain, ((r2_hidden @ sk_F @ (k2_struct_0 @ sk_D))),
% 0.60/0.78      inference('clc', [status(thm)], ['81', '82'])).
% 0.60/0.78  thf('84', plain, ((l1_struct_0 @ sk_D)),
% 0.60/0.78      inference('sup-', [status(thm)], ['60', '61'])).
% 0.60/0.78  thf('85', plain, ((m1_connsp_2 @ (u1_struct_0 @ sk_D) @ sk_D @ sk_F)),
% 0.60/0.78      inference('demod', [status(thm)], ['70', '83', '84'])).
% 0.60/0.78  thf('86', plain,
% 0.60/0.78      (![X27 : $i]: ((m1_pre_topc @ X27 @ X27) | ~ (l1_pre_topc @ X27))),
% 0.60/0.78      inference('cnf', [status(esa)], [t2_tsep_1])).
% 0.60/0.78  thf('87', plain,
% 0.60/0.78      (((g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) = (sk_D))),
% 0.60/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.78  thf(t59_pre_topc, axiom,
% 0.60/0.78    (![A:$i]:
% 0.60/0.78     ( ( l1_pre_topc @ A ) =>
% 0.60/0.78       ( ![B:$i]:
% 0.60/0.78         ( ( m1_pre_topc @
% 0.60/0.78             B @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) =>
% 0.60/0.78           ( m1_pre_topc @ B @ A ) ) ) ))).
% 0.60/0.78  thf('88', plain,
% 0.60/0.78      (![X17 : $i, X18 : $i]:
% 0.60/0.78         (~ (m1_pre_topc @ X17 @ 
% 0.60/0.78             (g1_pre_topc @ (u1_struct_0 @ X18) @ (u1_pre_topc @ X18)))
% 0.60/0.78          | (m1_pre_topc @ X17 @ X18)
% 0.60/0.78          | ~ (l1_pre_topc @ X18))),
% 0.60/0.78      inference('cnf', [status(esa)], [t59_pre_topc])).
% 0.60/0.78  thf('89', plain,
% 0.60/0.78      (![X0 : $i]:
% 0.60/0.78         (~ (m1_pre_topc @ X0 @ sk_D)
% 0.60/0.78          | ~ (l1_pre_topc @ sk_C)
% 0.60/0.78          | (m1_pre_topc @ X0 @ sk_C))),
% 0.60/0.78      inference('sup-', [status(thm)], ['87', '88'])).
% 0.60/0.78  thf('90', plain, ((l1_pre_topc @ sk_C)),
% 0.60/0.78      inference('demod', [status(thm)], ['32', '33'])).
% 0.60/0.78  thf('91', plain,
% 0.60/0.78      (![X0 : $i]: (~ (m1_pre_topc @ X0 @ sk_D) | (m1_pre_topc @ X0 @ sk_C))),
% 0.60/0.78      inference('demod', [status(thm)], ['89', '90'])).
% 0.60/0.78  thf('92', plain, ((~ (l1_pre_topc @ sk_D) | (m1_pre_topc @ sk_D @ sk_C))),
% 0.60/0.78      inference('sup-', [status(thm)], ['86', '91'])).
% 0.60/0.78  thf('93', plain, ((l1_pre_topc @ sk_D)),
% 0.60/0.78      inference('demod', [status(thm)], ['49', '50'])).
% 0.60/0.78  thf('94', plain, ((m1_pre_topc @ sk_D @ sk_C)),
% 0.60/0.78      inference('demod', [status(thm)], ['92', '93'])).
% 0.60/0.78  thf(t1_tsep_1, axiom,
% 0.60/0.78    (![A:$i]:
% 0.60/0.78     ( ( l1_pre_topc @ A ) =>
% 0.60/0.78       ( ![B:$i]:
% 0.60/0.78         ( ( m1_pre_topc @ B @ A ) =>
% 0.60/0.78           ( m1_subset_1 @
% 0.60/0.78             ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.60/0.78  thf('95', plain,
% 0.60/0.78      (![X25 : $i, X26 : $i]:
% 0.60/0.78         (~ (m1_pre_topc @ X25 @ X26)
% 0.60/0.78          | (m1_subset_1 @ (u1_struct_0 @ X25) @ 
% 0.60/0.78             (k1_zfmisc_1 @ (u1_struct_0 @ X26)))
% 0.60/0.78          | ~ (l1_pre_topc @ X26))),
% 0.60/0.78      inference('cnf', [status(esa)], [t1_tsep_1])).
% 0.60/0.78  thf('96', plain,
% 0.60/0.78      ((~ (l1_pre_topc @ sk_C)
% 0.60/0.78        | (m1_subset_1 @ (u1_struct_0 @ sk_D) @ 
% 0.60/0.78           (k1_zfmisc_1 @ (u1_struct_0 @ sk_C))))),
% 0.60/0.78      inference('sup-', [status(thm)], ['94', '95'])).
% 0.60/0.78  thf('97', plain, ((l1_pre_topc @ sk_C)),
% 0.60/0.78      inference('demod', [status(thm)], ['32', '33'])).
% 0.60/0.78  thf('98', plain,
% 0.60/0.78      ((m1_subset_1 @ (u1_struct_0 @ sk_D) @ 
% 0.60/0.78        (k1_zfmisc_1 @ (u1_struct_0 @ sk_C)))),
% 0.60/0.78      inference('demod', [status(thm)], ['96', '97'])).
% 0.60/0.78  thf(t3_subset, axiom,
% 0.60/0.78    (![A:$i,B:$i]:
% 0.60/0.78     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.60/0.78  thf('99', plain,
% 0.60/0.78      (![X4 : $i, X5 : $i]:
% 0.60/0.78         ((r1_tarski @ X4 @ X5) | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5)))),
% 0.60/0.78      inference('cnf', [status(esa)], [t3_subset])).
% 0.60/0.78  thf('100', plain,
% 0.60/0.78      ((r1_tarski @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_C))),
% 0.60/0.78      inference('sup-', [status(thm)], ['98', '99'])).
% 0.60/0.78  thf('101', plain,
% 0.60/0.78      (((v2_struct_0 @ sk_B)
% 0.60/0.78        | (v2_struct_0 @ sk_D)
% 0.60/0.78        | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)
% 0.60/0.78        | (v2_struct_0 @ sk_C)
% 0.60/0.78        | (v2_struct_0 @ sk_A))),
% 0.60/0.78      inference('demod', [status(thm)], ['38', '85', '100'])).
% 0.60/0.78  thf('102', plain, (~ (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)),
% 0.60/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.78  thf('103', plain,
% 0.60/0.78      (((v2_struct_0 @ sk_A)
% 0.60/0.78        | (v2_struct_0 @ sk_C)
% 0.60/0.78        | (v2_struct_0 @ sk_D)
% 0.60/0.78        | (v2_struct_0 @ sk_B))),
% 0.60/0.78      inference('sup-', [status(thm)], ['101', '102'])).
% 0.60/0.78  thf('104', plain, (~ (v2_struct_0 @ sk_D)),
% 0.60/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.78  thf('105', plain,
% 0.60/0.78      (((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_A))),
% 0.60/0.78      inference('sup-', [status(thm)], ['103', '104'])).
% 0.60/0.78  thf('106', plain, (~ (v2_struct_0 @ sk_B)),
% 0.60/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.78  thf('107', plain, (((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_C))),
% 0.60/0.78      inference('clc', [status(thm)], ['105', '106'])).
% 0.60/0.78  thf('108', plain, (~ (v2_struct_0 @ sk_A)),
% 0.60/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.78  thf('109', plain, ((v2_struct_0 @ sk_C)),
% 0.60/0.78      inference('clc', [status(thm)], ['107', '108'])).
% 0.60/0.78  thf('110', plain, ($false), inference('demod', [status(thm)], ['0', '109'])).
% 0.60/0.78  
% 0.60/0.78  % SZS output end Refutation
% 0.60/0.78  
% 0.60/0.78  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
