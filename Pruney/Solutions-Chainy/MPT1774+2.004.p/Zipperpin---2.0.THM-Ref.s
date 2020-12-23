%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.fciIitQOKQ

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:10:17 EST 2020

% Result     : Theorem 0.68s
% Output     : Refutation 0.68s
% Verified   : 
% Statistics : Number of formulae       :  215 ( 832 expanded)
%              Number of leaves         :   38 ( 248 expanded)
%              Depth                    :   26
%              Number of atoms          : 2532 (34813 expanded)
%              Number of equality atoms :   34 ( 446 expanded)
%              Maximal formula depth    :   28 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(k3_tmap_1_type,type,(
    k3_tmap_1: $i > $i > $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_G_type,type,(
    sk_G: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(m1_connsp_2_type,type,(
    m1_connsp_2: $i > $i > $i > $o )).

thf(r1_tmap_1_type,type,(
    r1_tmap_1: $i > $i > $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k2_tmap_1_type,type,(
    k2_tmap_1: $i > $i > $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_H_type,type,(
    sk_H: $i )).

thf(k2_partfun1_type,type,(
    k2_partfun1: $i > $i > $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(t85_tmap_1,conjecture,(
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
                                        <=> ( r1_tmap_1 @ C @ A @ ( k3_tmap_1 @ B @ A @ D @ C @ E ) @ H ) ) ) ) ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t85_tmap_1])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_pre_topc @ sk_C @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('3',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['2'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('4',plain,(
    ! [X3: $i,X5: $i] :
      ( ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X5 ) )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('5',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(t39_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) )
             => ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) )).

thf('6',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_pre_topc @ X13 @ X14 )
      | ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ~ ( l1_pre_topc @ X14 ) ) ),
    inference(cnf,[status(esa)],[t39_pre_topc])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X1 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,
    ( ( m1_subset_1 @ ( u1_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D_1 ) ) )
    | ~ ( l1_pre_topc @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['1','7'])).

thf('9',plain,(
    m1_pre_topc @ sk_D_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('10',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_pre_topc @ X11 @ X12 )
      | ( l1_pre_topc @ X11 )
      | ~ ( l1_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('11',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( l1_pre_topc @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    l1_pre_topc @ sk_D_1 ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['8','13'])).

thf('15',plain,
    ( ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D_1 @ sk_C @ sk_E ) @ sk_H )
    | ( r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_G ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D_1 @ sk_C @ sk_E ) @ sk_H )
   <= ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D_1 @ sk_C @ sk_E ) @ sk_H ) ),
    inference(split,[status(esa)],['15'])).

thf('17',plain,(
    m1_pre_topc @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    m1_pre_topc @ sk_D_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D_1 ) @ ( u1_struct_0 @ sk_A ) ) ) ),
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

thf('20',plain,(
    ! [X34: $i,X35: $i,X36: $i,X37: $i,X38: $i] :
      ( ( v2_struct_0 @ X34 )
      | ~ ( v2_pre_topc @ X34 )
      | ~ ( l1_pre_topc @ X34 )
      | ~ ( m1_pre_topc @ X35 @ X36 )
      | ~ ( m1_pre_topc @ X35 @ X37 )
      | ( ( k3_tmap_1 @ X36 @ X34 @ X37 @ X35 @ X38 )
        = ( k2_partfun1 @ ( u1_struct_0 @ X37 ) @ ( u1_struct_0 @ X34 ) @ X38 @ ( u1_struct_0 @ X35 ) ) )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X37 ) @ ( u1_struct_0 @ X34 ) ) ) )
      | ~ ( v1_funct_2 @ X38 @ ( u1_struct_0 @ X37 ) @ ( u1_struct_0 @ X34 ) )
      | ~ ( v1_funct_1 @ X38 )
      | ~ ( m1_pre_topc @ X37 @ X36 )
      | ~ ( l1_pre_topc @ X36 )
      | ~ ( v2_pre_topc @ X36 )
      | ( v2_struct_0 @ X36 ) ) ),
    inference(cnf,[status(esa)],[d5_tmap_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ sk_D_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D_1 ) @ ( u1_struct_0 @ sk_A ) )
      | ( ( k3_tmap_1 @ X0 @ sk_A @ sk_D_1 @ X1 @ sk_E )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D_1 ) @ ( u1_struct_0 @ sk_A ) @ sk_E @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( m1_pre_topc @ X1 @ sk_D_1 )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ sk_D_1 @ X0 )
      | ( ( k3_tmap_1 @ X0 @ sk_A @ sk_D_1 @ X1 @ sk_E )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D_1 ) @ ( u1_struct_0 @ sk_A ) @ sk_E @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( m1_pre_topc @ X1 @ sk_D_1 )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['21','22','23','24','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ~ ( m1_pre_topc @ X0 @ sk_D_1 )
      | ( ( k3_tmap_1 @ sk_B @ sk_A @ sk_D_1 @ X0 @ sk_E )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D_1 ) @ ( u1_struct_0 @ sk_A ) @ sk_E @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['18','26'])).

thf('28',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ~ ( m1_pre_topc @ X0 @ sk_D_1 )
      | ( ( k3_tmap_1 @ sk_B @ sk_A @ sk_D_1 @ X0 @ sk_E )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D_1 ) @ ( u1_struct_0 @ sk_A ) @ sk_E @ ( u1_struct_0 @ X0 ) ) )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['27','28','29'])).

thf('31',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k3_tmap_1 @ sk_B @ sk_A @ sk_D_1 @ sk_C @ sk_E )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_D_1 ) @ ( u1_struct_0 @ sk_A ) @ sk_E @ ( u1_struct_0 @ sk_C ) ) )
    | ~ ( m1_pre_topc @ sk_C @ sk_D_1 )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['17','30'])).

thf('32',plain,(
    m1_pre_topc @ sk_C @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D_1 ) @ ( u1_struct_0 @ sk_A ) ) ) ),
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

thf('34',plain,(
    ! [X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ( v2_struct_0 @ X30 )
      | ~ ( v2_pre_topc @ X30 )
      | ~ ( l1_pre_topc @ X30 )
      | ~ ( m1_pre_topc @ X31 @ X32 )
      | ( ( k2_tmap_1 @ X32 @ X30 @ X33 @ X31 )
        = ( k2_partfun1 @ ( u1_struct_0 @ X32 ) @ ( u1_struct_0 @ X30 ) @ X33 @ ( u1_struct_0 @ X31 ) ) )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X32 ) @ ( u1_struct_0 @ X30 ) ) ) )
      | ~ ( v1_funct_2 @ X33 @ ( u1_struct_0 @ X32 ) @ ( u1_struct_0 @ X30 ) )
      | ~ ( v1_funct_1 @ X33 )
      | ~ ( l1_pre_topc @ X32 )
      | ~ ( v2_pre_topc @ X32 )
      | ( v2_struct_0 @ X32 ) ) ),
    inference(cnf,[status(esa)],[d4_tmap_1])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_D_1 )
      | ~ ( v2_pre_topc @ sk_D_1 )
      | ~ ( l1_pre_topc @ sk_D_1 )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D_1 ) @ ( u1_struct_0 @ sk_A ) )
      | ( ( k2_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ X0 )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D_1 ) @ ( u1_struct_0 @ sk_A ) @ sk_E @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_D_1 )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    m1_pre_topc @ sk_D_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( v2_pre_topc @ B ) ) ) )).

thf('37',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( m1_pre_topc @ X9 @ X10 )
      | ( v2_pre_topc @ X9 )
      | ~ ( l1_pre_topc @ X10 )
      | ~ ( v2_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[cc1_pre_topc])).

thf('38',plain,
    ( ~ ( v2_pre_topc @ sk_B )
    | ~ ( l1_pre_topc @ sk_B )
    | ( v2_pre_topc @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    v2_pre_topc @ sk_D_1 ),
    inference(demod,[status(thm)],['38','39','40'])).

thf('42',plain,(
    l1_pre_topc @ sk_D_1 ),
    inference(demod,[status(thm)],['11','12'])).

thf('43',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_D_1 )
      | ( ( k2_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ X0 )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D_1 ) @ ( u1_struct_0 @ sk_A ) @ sk_E @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_D_1 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['35','41','42','43','44','45','46'])).

thf('48',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k2_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_C )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_D_1 ) @ ( u1_struct_0 @ sk_A ) @ sk_E @ ( u1_struct_0 @ sk_C ) ) )
    | ( v2_struct_0 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['32','47'])).

thf('49',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,
    ( ( v2_struct_0 @ sk_D_1 )
    | ( ( k2_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_C )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_D_1 ) @ ( u1_struct_0 @ sk_A ) @ sk_E @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference(clc,[status(thm)],['48','49'])).

thf('51',plain,(
    ~ ( v2_struct_0 @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,
    ( ( k2_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_C )
    = ( k2_partfun1 @ ( u1_struct_0 @ sk_D_1 ) @ ( u1_struct_0 @ sk_A ) @ sk_E @ ( u1_struct_0 @ sk_C ) ) ),
    inference(clc,[status(thm)],['50','51'])).

thf('53',plain,(
    m1_pre_topc @ sk_C @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k3_tmap_1 @ sk_B @ sk_A @ sk_D_1 @ sk_C @ sk_E )
      = ( k2_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_C ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['31','52','53'])).

thf('55',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k3_tmap_1 @ sk_B @ sk_A @ sk_D_1 @ sk_C @ sk_E )
      = ( k2_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_C ) ) ),
    inference(clc,[status(thm)],['54','55'])).

thf('57',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,
    ( ( k3_tmap_1 @ sk_B @ sk_A @ sk_D_1 @ sk_C @ sk_E )
    = ( k2_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_C ) ),
    inference(clc,[status(thm)],['56','57'])).

thf('59',plain,
    ( ( r1_tmap_1 @ sk_C @ sk_A @ ( k2_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_C ) @ sk_H )
   <= ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D_1 @ sk_C @ sk_E ) @ sk_H ) ),
    inference(demod,[status(thm)],['16','58'])).

thf('60',plain,
    ( ~ ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D_1 @ sk_C @ sk_E ) @ sk_H )
    | ~ ( r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_G ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    sk_G = sk_H ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,
    ( ~ ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D_1 @ sk_C @ sk_E ) @ sk_H )
    | ~ ( r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_H ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,
    ( ~ ( r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_H )
    | ~ ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D_1 @ sk_C @ sk_E ) @ sk_H ) ),
    inference(split,[status(esa)],['62'])).

thf('64',plain,
    ( ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D_1 @ sk_C @ sk_E ) @ sk_H )
    | ( r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_G ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    sk_G = sk_H ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,
    ( ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D_1 @ sk_C @ sk_E ) @ sk_H )
    | ( r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_H ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,
    ( ( r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_H )
   <= ( r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_H ) ),
    inference(split,[status(esa)],['66'])).

thf('68',plain,
    ( ~ ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D_1 @ sk_C @ sk_E ) @ sk_H )
    | ~ ( r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_G ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,
    ( ~ ( r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_G )
   <= ~ ( r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_G ) ),
    inference(split,[status(esa)],['68'])).

thf('70',plain,(
    sk_G = sk_H ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,
    ( ~ ( r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_H )
   <= ~ ( r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_G ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('72',plain,
    ( ~ ( r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_H )
    | ( r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_G ) ),
    inference('sup-',[status(thm)],['67','71'])).

thf('73',plain,(
    m1_subset_1 @ sk_H @ ( u1_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,
    ( ( r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_G )
   <= ( r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_G ) ),
    inference(split,[status(esa)],['15'])).

thf('75',plain,(
    sk_G = sk_H ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,
    ( ( r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_H )
   <= ( r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_G ) ),
    inference(demod,[status(thm)],['74','75'])).

thf('77',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D_1 ) @ ( u1_struct_0 @ sk_A ) ) ) ),
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

thf('78',plain,(
    ! [X39: $i,X40: $i,X41: $i,X42: $i,X43: $i,X44: $i] :
      ( ( v2_struct_0 @ X39 )
      | ~ ( v2_pre_topc @ X39 )
      | ~ ( l1_pre_topc @ X39 )
      | ( v2_struct_0 @ X40 )
      | ~ ( m1_pre_topc @ X40 @ X39 )
      | ~ ( m1_subset_1 @ X41 @ ( u1_struct_0 @ X40 ) )
      | ( r1_tmap_1 @ X40 @ X42 @ ( k2_tmap_1 @ X39 @ X42 @ X43 @ X40 ) @ X41 )
      | ( X44 != X41 )
      | ~ ( r1_tmap_1 @ X39 @ X42 @ X43 @ X44 )
      | ~ ( m1_subset_1 @ X44 @ ( u1_struct_0 @ X39 ) )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X39 ) @ ( u1_struct_0 @ X42 ) ) ) )
      | ~ ( v1_funct_2 @ X43 @ ( u1_struct_0 @ X39 ) @ ( u1_struct_0 @ X42 ) )
      | ~ ( v1_funct_1 @ X43 )
      | ~ ( l1_pre_topc @ X42 )
      | ~ ( v2_pre_topc @ X42 )
      | ( v2_struct_0 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t64_tmap_1])).

thf('79',plain,(
    ! [X39: $i,X40: $i,X41: $i,X42: $i,X43: $i] :
      ( ( v2_struct_0 @ X42 )
      | ~ ( v2_pre_topc @ X42 )
      | ~ ( l1_pre_topc @ X42 )
      | ~ ( v1_funct_1 @ X43 )
      | ~ ( v1_funct_2 @ X43 @ ( u1_struct_0 @ X39 ) @ ( u1_struct_0 @ X42 ) )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X39 ) @ ( u1_struct_0 @ X42 ) ) ) )
      | ~ ( m1_subset_1 @ X41 @ ( u1_struct_0 @ X39 ) )
      | ~ ( r1_tmap_1 @ X39 @ X42 @ X43 @ X41 )
      | ( r1_tmap_1 @ X40 @ X42 @ ( k2_tmap_1 @ X39 @ X42 @ X43 @ X40 ) @ X41 )
      | ~ ( m1_subset_1 @ X41 @ ( u1_struct_0 @ X40 ) )
      | ~ ( m1_pre_topc @ X40 @ X39 )
      | ( v2_struct_0 @ X40 )
      | ~ ( l1_pre_topc @ X39 )
      | ~ ( v2_pre_topc @ X39 )
      | ( v2_struct_0 @ X39 ) ) ),
    inference(simplify,[status(thm)],['78'])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_D_1 )
      | ~ ( v2_pre_topc @ sk_D_1 )
      | ~ ( l1_pre_topc @ sk_D_1 )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_D_1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ( r1_tmap_1 @ X0 @ sk_A @ ( k2_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ X0 ) @ X1 )
      | ~ ( r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_D_1 ) )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D_1 ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['77','79'])).

thf('81',plain,(
    v2_pre_topc @ sk_D_1 ),
    inference(demod,[status(thm)],['38','39','40'])).

thf('82',plain,(
    l1_pre_topc @ sk_D_1 ),
    inference(demod,[status(thm)],['11','12'])).

thf('83',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_D_1 )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_D_1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ( r1_tmap_1 @ X0 @ sk_A @ ( k2_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ X0 ) @ X1 )
      | ~ ( r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_D_1 ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['80','81','82','83','84','85','86'])).

thf('88',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ~ ( m1_subset_1 @ sk_H @ ( u1_struct_0 @ sk_D_1 ) )
        | ( r1_tmap_1 @ X0 @ sk_A @ ( k2_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ X0 ) @ sk_H )
        | ~ ( m1_subset_1 @ sk_H @ ( u1_struct_0 @ X0 ) )
        | ~ ( m1_pre_topc @ X0 @ sk_D_1 )
        | ( v2_struct_0 @ X0 )
        | ( v2_struct_0 @ sk_D_1 ) )
   <= ( r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_G ) ),
    inference('sup-',[status(thm)],['76','87'])).

thf('89',plain,(
    m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    sk_G = sk_H ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    m1_subset_1 @ sk_H @ ( u1_struct_0 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['89','90'])).

thf('92',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( r1_tmap_1 @ X0 @ sk_A @ ( k2_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ X0 ) @ sk_H )
        | ~ ( m1_subset_1 @ sk_H @ ( u1_struct_0 @ X0 ) )
        | ~ ( m1_pre_topc @ X0 @ sk_D_1 )
        | ( v2_struct_0 @ X0 )
        | ( v2_struct_0 @ sk_D_1 ) )
   <= ( r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_G ) ),
    inference(demod,[status(thm)],['88','91'])).

thf('93',plain,
    ( ( ( v2_struct_0 @ sk_D_1 )
      | ( v2_struct_0 @ sk_C )
      | ~ ( m1_pre_topc @ sk_C @ sk_D_1 )
      | ( r1_tmap_1 @ sk_C @ sk_A @ ( k2_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_C ) @ sk_H )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_G ) ),
    inference('sup-',[status(thm)],['73','92'])).

thf('94',plain,(
    m1_pre_topc @ sk_C @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,
    ( ( ( v2_struct_0 @ sk_D_1 )
      | ( v2_struct_0 @ sk_C )
      | ( r1_tmap_1 @ sk_C @ sk_A @ ( k2_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_C ) @ sk_H )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_G ) ),
    inference(demod,[status(thm)],['93','94'])).

thf('96',plain,
    ( ( k3_tmap_1 @ sk_B @ sk_A @ sk_D_1 @ sk_C @ sk_E )
    = ( k2_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_C ) ),
    inference(clc,[status(thm)],['56','57'])).

thf('97',plain,
    ( ~ ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D_1 @ sk_C @ sk_E ) @ sk_H )
   <= ~ ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D_1 @ sk_C @ sk_E ) @ sk_H ) ),
    inference(split,[status(esa)],['68'])).

thf('98',plain,
    ( ~ ( r1_tmap_1 @ sk_C @ sk_A @ ( k2_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_C ) @ sk_H )
   <= ~ ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D_1 @ sk_C @ sk_E ) @ sk_H ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_D_1 ) )
   <= ( ~ ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D_1 @ sk_C @ sk_E ) @ sk_H )
      & ( r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_G ) ) ),
    inference('sup-',[status(thm)],['95','98'])).

thf('100',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,
    ( ( ( v2_struct_0 @ sk_D_1 )
      | ( v2_struct_0 @ sk_C ) )
   <= ( ~ ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D_1 @ sk_C @ sk_E ) @ sk_H )
      & ( r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_G ) ) ),
    inference(clc,[status(thm)],['99','100'])).

thf('102',plain,(
    ~ ( v2_struct_0 @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,
    ( ( v2_struct_0 @ sk_C )
   <= ( ~ ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D_1 @ sk_C @ sk_E ) @ sk_H )
      & ( r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_G ) ) ),
    inference(clc,[status(thm)],['101','102'])).

thf('104',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,
    ( ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D_1 @ sk_C @ sk_E ) @ sk_H )
    | ~ ( r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_G ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,
    ( ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D_1 @ sk_C @ sk_E ) @ sk_H )
    | ( r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_H ) ),
    inference(split,[status(esa)],['66'])).

thf('107',plain,(
    r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D_1 @ sk_C @ sk_E ) @ sk_H ),
    inference('sat_resolution*',[status(thm)],['63','72','105','106'])).

thf('108',plain,(
    r1_tmap_1 @ sk_C @ sk_A @ ( k2_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_C ) @ sk_H ),
    inference(simpl_trail,[status(thm)],['59','107'])).

thf('109',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D_1 ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t65_tmap_1,axiom,(
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
                      ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) )
                     => ! [F: $i] :
                          ( ( m1_subset_1 @ F @ ( u1_struct_0 @ B ) )
                         => ! [G: $i] :
                              ( ( m1_subset_1 @ G @ ( u1_struct_0 @ D ) )
                             => ( ( ( r1_tarski @ E @ ( u1_struct_0 @ D ) )
                                  & ( m1_connsp_2 @ E @ B @ F )
                                  & ( F = G ) )
                               => ( ( r1_tmap_1 @ B @ A @ C @ F )
                                <=> ( r1_tmap_1 @ D @ A @ ( k2_tmap_1 @ B @ A @ C @ D ) @ G ) ) ) ) ) ) ) ) ) ) )).

thf('110',plain,(
    ! [X45: $i,X46: $i,X47: $i,X48: $i,X49: $i,X50: $i,X51: $i] :
      ( ( v2_struct_0 @ X45 )
      | ~ ( v2_pre_topc @ X45 )
      | ~ ( l1_pre_topc @ X45 )
      | ( v2_struct_0 @ X46 )
      | ~ ( m1_pre_topc @ X46 @ X45 )
      | ~ ( m1_subset_1 @ X47 @ ( u1_struct_0 @ X45 ) )
      | ~ ( r1_tarski @ X48 @ ( u1_struct_0 @ X46 ) )
      | ~ ( m1_connsp_2 @ X48 @ X45 @ X47 )
      | ( X47 != X49 )
      | ~ ( r1_tmap_1 @ X46 @ X50 @ ( k2_tmap_1 @ X45 @ X50 @ X51 @ X46 ) @ X49 )
      | ( r1_tmap_1 @ X45 @ X50 @ X51 @ X47 )
      | ~ ( m1_subset_1 @ X49 @ ( u1_struct_0 @ X46 ) )
      | ~ ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X45 ) ) )
      | ~ ( m1_subset_1 @ X51 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X45 ) @ ( u1_struct_0 @ X50 ) ) ) )
      | ~ ( v1_funct_2 @ X51 @ ( u1_struct_0 @ X45 ) @ ( u1_struct_0 @ X50 ) )
      | ~ ( v1_funct_1 @ X51 )
      | ~ ( l1_pre_topc @ X50 )
      | ~ ( v2_pre_topc @ X50 )
      | ( v2_struct_0 @ X50 ) ) ),
    inference(cnf,[status(esa)],[t65_tmap_1])).

thf('111',plain,(
    ! [X45: $i,X46: $i,X48: $i,X49: $i,X50: $i,X51: $i] :
      ( ( v2_struct_0 @ X50 )
      | ~ ( v2_pre_topc @ X50 )
      | ~ ( l1_pre_topc @ X50 )
      | ~ ( v1_funct_1 @ X51 )
      | ~ ( v1_funct_2 @ X51 @ ( u1_struct_0 @ X45 ) @ ( u1_struct_0 @ X50 ) )
      | ~ ( m1_subset_1 @ X51 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X45 ) @ ( u1_struct_0 @ X50 ) ) ) )
      | ~ ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X45 ) ) )
      | ~ ( m1_subset_1 @ X49 @ ( u1_struct_0 @ X46 ) )
      | ( r1_tmap_1 @ X45 @ X50 @ X51 @ X49 )
      | ~ ( r1_tmap_1 @ X46 @ X50 @ ( k2_tmap_1 @ X45 @ X50 @ X51 @ X46 ) @ X49 )
      | ~ ( m1_connsp_2 @ X48 @ X45 @ X49 )
      | ~ ( r1_tarski @ X48 @ ( u1_struct_0 @ X46 ) )
      | ~ ( m1_subset_1 @ X49 @ ( u1_struct_0 @ X45 ) )
      | ~ ( m1_pre_topc @ X46 @ X45 )
      | ( v2_struct_0 @ X46 )
      | ~ ( l1_pre_topc @ X45 )
      | ~ ( v2_pre_topc @ X45 )
      | ( v2_struct_0 @ X45 ) ) ),
    inference(simplify,[status(thm)],['110'])).

thf('112',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ sk_D_1 )
      | ~ ( v2_pre_topc @ sk_D_1 )
      | ~ ( l1_pre_topc @ sk_D_1 )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_D_1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_D_1 ) )
      | ~ ( r1_tarski @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_connsp_2 @ X2 @ sk_D_1 @ X1 )
      | ~ ( r1_tmap_1 @ X0 @ sk_A @ ( k2_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ X0 ) @ X1 )
      | ( r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D_1 ) ) )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D_1 ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['109','111'])).

thf('113',plain,(
    v2_pre_topc @ sk_D_1 ),
    inference(demod,[status(thm)],['38','39','40'])).

thf('114',plain,(
    l1_pre_topc @ sk_D_1 ),
    inference(demod,[status(thm)],['11','12'])).

thf('115',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ sk_D_1 )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_D_1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_D_1 ) )
      | ~ ( r1_tarski @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_connsp_2 @ X2 @ sk_D_1 @ X1 )
      | ~ ( r1_tmap_1 @ X0 @ sk_A @ ( k2_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ X0 ) @ X1 )
      | ( r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D_1 ) ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['112','113','114','115','116','117','118'])).

thf('120',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D_1 ) ) )
      | ~ ( m1_subset_1 @ sk_H @ ( u1_struct_0 @ sk_C ) )
      | ( r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_H )
      | ~ ( m1_connsp_2 @ X0 @ sk_D_1 @ sk_H )
      | ~ ( r1_tarski @ X0 @ ( u1_struct_0 @ sk_C ) )
      | ~ ( m1_subset_1 @ sk_H @ ( u1_struct_0 @ sk_D_1 ) )
      | ~ ( m1_pre_topc @ sk_C @ sk_D_1 )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['108','119'])).

thf('121',plain,(
    m1_subset_1 @ sk_H @ ( u1_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,(
    m1_subset_1 @ sk_H @ ( u1_struct_0 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['89','90'])).

thf('123',plain,(
    m1_pre_topc @ sk_C @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D_1 ) ) )
      | ( r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_H )
      | ~ ( m1_connsp_2 @ X0 @ sk_D_1 @ sk_H )
      | ~ ( r1_tarski @ X0 @ ( u1_struct_0 @ sk_C ) )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['120','121','122','123'])).

thf('125',plain,
    ( ( v2_struct_0 @ sk_D_1 )
    | ( v2_struct_0 @ sk_C )
    | ~ ( r1_tarski @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_C ) )
    | ~ ( m1_connsp_2 @ ( u1_struct_0 @ sk_C ) @ sk_D_1 @ sk_H )
    | ( r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_H )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['14','124'])).

thf('126',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['2'])).

thf('127',plain,(
    m1_subset_1 @ sk_H @ ( u1_struct_0 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['89','90'])).

thf('128',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['8','13'])).

thf('129',plain,(
    m1_pre_topc @ sk_C @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('130',plain,(
    r1_tarski @ sk_F @ ( u1_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('131',plain,(
    ! [X3: $i,X5: $i] :
      ( ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X5 ) )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('132',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['130','131'])).

thf('133',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_pre_topc @ X13 @ X14 )
      | ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ~ ( l1_pre_topc @ X14 ) ) ),
    inference(cnf,[status(esa)],[t39_pre_topc])).

thf('134',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['132','133'])).

thf('135',plain,
    ( ( m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D_1 ) ) )
    | ~ ( l1_pre_topc @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['129','134'])).

thf('136',plain,(
    l1_pre_topc @ sk_D_1 ),
    inference(demod,[status(thm)],['11','12'])).

thf('137',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['135','136'])).

thf(t8_connsp_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( m1_connsp_2 @ C @ A @ B )
              <=> ? [D: $i] :
                    ( ( r2_hidden @ B @ D )
                    & ( r1_tarski @ D @ C )
                    & ( v3_pre_topc @ D @ A )
                    & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ) )).

thf('138',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( u1_struct_0 @ X27 ) )
      | ~ ( r2_hidden @ X26 @ X29 )
      | ~ ( r1_tarski @ X29 @ X28 )
      | ~ ( v3_pre_topc @ X29 @ X27 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
      | ( m1_connsp_2 @ X28 @ X27 @ X26 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
      | ~ ( l1_pre_topc @ X27 )
      | ~ ( v2_pre_topc @ X27 )
      | ( v2_struct_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t8_connsp_2])).

thf('139',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_D_1 )
      | ~ ( v2_pre_topc @ sk_D_1 )
      | ~ ( l1_pre_topc @ sk_D_1 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D_1 ) ) )
      | ( m1_connsp_2 @ X0 @ sk_D_1 @ X1 )
      | ~ ( v3_pre_topc @ sk_F @ sk_D_1 )
      | ~ ( r1_tarski @ sk_F @ X0 )
      | ~ ( r2_hidden @ X1 @ sk_F )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_D_1 ) ) ) ),
    inference('sup-',[status(thm)],['137','138'])).

thf('140',plain,(
    v2_pre_topc @ sk_D_1 ),
    inference(demod,[status(thm)],['38','39','40'])).

thf('141',plain,(
    l1_pre_topc @ sk_D_1 ),
    inference(demod,[status(thm)],['11','12'])).

thf('142',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('143',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['135','136'])).

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

thf('144',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ~ ( v3_pre_topc @ X19 @ X20 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ( v3_pre_topc @ X21 @ X22 )
      | ( X21 != X19 )
      | ~ ( m1_pre_topc @ X22 @ X20 )
      | ~ ( l1_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[t33_tops_2])).

thf('145',plain,(
    ! [X19: $i,X20: $i,X22: $i] :
      ( ~ ( l1_pre_topc @ X20 )
      | ~ ( m1_pre_topc @ X22 @ X20 )
      | ( v3_pre_topc @ X19 @ X22 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ~ ( v3_pre_topc @ X19 @ X20 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) ) ) ),
    inference(simplify,[status(thm)],['144'])).

thf('146',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( v3_pre_topc @ sk_F @ X0 )
      | ( v3_pre_topc @ sk_F @ sk_D_1 )
      | ~ ( m1_pre_topc @ sk_D_1 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['143','145'])).

thf('147',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ~ ( m1_pre_topc @ sk_D_1 @ sk_B )
    | ( v3_pre_topc @ sk_F @ sk_D_1 )
    | ~ ( v3_pre_topc @ sk_F @ sk_B ) ),
    inference('sup-',[status(thm)],['142','146'])).

thf('148',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('149',plain,(
    m1_pre_topc @ sk_D_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('150',plain,(
    v3_pre_topc @ sk_F @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('151',plain,(
    v3_pre_topc @ sk_F @ sk_D_1 ),
    inference(demod,[status(thm)],['147','148','149','150'])).

thf('152',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_D_1 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D_1 ) ) )
      | ( m1_connsp_2 @ X0 @ sk_D_1 @ X1 )
      | ~ ( r1_tarski @ sk_F @ X0 )
      | ~ ( r2_hidden @ X1 @ sk_F )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_D_1 ) ) ) ),
    inference(demod,[status(thm)],['139','140','141','151'])).

thf('153',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_D_1 ) )
      | ~ ( r2_hidden @ X0 @ sk_F )
      | ~ ( r1_tarski @ sk_F @ ( u1_struct_0 @ sk_C ) )
      | ( m1_connsp_2 @ ( u1_struct_0 @ sk_C ) @ sk_D_1 @ X0 )
      | ( v2_struct_0 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['128','152'])).

thf('154',plain,(
    r1_tarski @ sk_F @ ( u1_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('155',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_D_1 ) )
      | ~ ( r2_hidden @ X0 @ sk_F )
      | ( m1_connsp_2 @ ( u1_struct_0 @ sk_C ) @ sk_D_1 @ X0 )
      | ( v2_struct_0 @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['153','154'])).

thf('156',plain,
    ( ( v2_struct_0 @ sk_D_1 )
    | ( m1_connsp_2 @ ( u1_struct_0 @ sk_C ) @ sk_D_1 @ sk_H )
    | ~ ( r2_hidden @ sk_H @ sk_F ) ),
    inference('sup-',[status(thm)],['127','155'])).

thf('157',plain,(
    r2_hidden @ sk_G @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('158',plain,(
    sk_G = sk_H ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('159',plain,(
    r2_hidden @ sk_H @ sk_F ),
    inference(demod,[status(thm)],['157','158'])).

thf('160',plain,
    ( ( v2_struct_0 @ sk_D_1 )
    | ( m1_connsp_2 @ ( u1_struct_0 @ sk_C ) @ sk_D_1 @ sk_H ) ),
    inference(demod,[status(thm)],['156','159'])).

thf('161',plain,(
    ~ ( v2_struct_0 @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('162',plain,(
    m1_connsp_2 @ ( u1_struct_0 @ sk_C ) @ sk_D_1 @ sk_H ),
    inference(clc,[status(thm)],['160','161'])).

thf('163',plain,
    ( ( v2_struct_0 @ sk_D_1 )
    | ( v2_struct_0 @ sk_C )
    | ( r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_H )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['125','126','162'])).

thf('164',plain,
    ( ~ ( r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_H )
   <= ~ ( r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_G ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('165',plain,
    ( ( r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_H )
   <= ( r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_G ) ),
    inference(demod,[status(thm)],['74','75'])).

thf('166',plain,
    ( ~ ( r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_H )
   <= ~ ( r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_H ) ),
    inference(split,[status(esa)],['62'])).

thf('167',plain,
    ( ~ ( r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_G )
    | ( r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_H ) ),
    inference('sup-',[status(thm)],['165','166'])).

thf('168',plain,(
    ~ ( r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_G ) ),
    inference('sat_resolution*',[status(thm)],['63','72','105','167'])).

thf('169',plain,(
    ~ ( r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_H ) ),
    inference(simpl_trail,[status(thm)],['164','168'])).

thf('170',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['163','169'])).

thf('171',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('172',plain,
    ( ( v2_struct_0 @ sk_D_1 )
    | ( v2_struct_0 @ sk_C ) ),
    inference(clc,[status(thm)],['170','171'])).

thf('173',plain,(
    ~ ( v2_struct_0 @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('174',plain,(
    v2_struct_0 @ sk_C ),
    inference(clc,[status(thm)],['172','173'])).

thf('175',plain,(
    $false ),
    inference(demod,[status(thm)],['0','174'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.fciIitQOKQ
% 0.15/0.37  % Computer   : n023.cluster.edu
% 0.15/0.37  % Model      : x86_64 x86_64
% 0.15/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.37  % Memory     : 8042.1875MB
% 0.15/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.37  % CPULimit   : 60
% 0.15/0.37  % DateTime   : Tue Dec  1 11:30:51 EST 2020
% 0.15/0.37  % CPUTime    : 
% 0.15/0.37  % Running portfolio for 600 s
% 0.15/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.37  % Number of cores: 8
% 0.15/0.38  % Python version: Python 3.6.8
% 0.15/0.38  % Running in FO mode
% 0.68/0.86  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.68/0.86  % Solved by: fo/fo7.sh
% 0.68/0.86  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.68/0.86  % done 795 iterations in 0.371s
% 0.68/0.86  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.68/0.86  % SZS output start Refutation
% 0.68/0.86  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.68/0.86  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.68/0.86  thf(sk_C_type, type, sk_C: $i).
% 0.68/0.86  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.68/0.86  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.68/0.86  thf(sk_B_type, type, sk_B: $i).
% 0.68/0.86  thf(sk_F_type, type, sk_F: $i).
% 0.68/0.86  thf(k3_tmap_1_type, type, k3_tmap_1: $i > $i > $i > $i > $i > $i).
% 0.68/0.86  thf(sk_A_type, type, sk_A: $i).
% 0.68/0.86  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.68/0.86  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.68/0.86  thf(sk_G_type, type, sk_G: $i).
% 0.68/0.86  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.68/0.86  thf(m1_connsp_2_type, type, m1_connsp_2: $i > $i > $i > $o).
% 0.68/0.86  thf(r1_tmap_1_type, type, r1_tmap_1: $i > $i > $i > $i > $o).
% 0.68/0.86  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.68/0.86  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.68/0.86  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.68/0.86  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.68/0.86  thf(k2_tmap_1_type, type, k2_tmap_1: $i > $i > $i > $i > $i).
% 0.68/0.86  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.68/0.86  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.68/0.86  thf(sk_H_type, type, sk_H: $i).
% 0.68/0.86  thf(k2_partfun1_type, type, k2_partfun1: $i > $i > $i > $i > $i).
% 0.68/0.86  thf(sk_E_type, type, sk_E: $i).
% 0.68/0.86  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.68/0.86  thf(t85_tmap_1, conjecture,
% 0.68/0.86    (![A:$i]:
% 0.68/0.86     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.68/0.86       ( ![B:$i]:
% 0.68/0.86         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.68/0.86             ( l1_pre_topc @ B ) ) =>
% 0.68/0.86           ( ![C:$i]:
% 0.68/0.86             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ B ) ) =>
% 0.68/0.86               ( ![D:$i]:
% 0.68/0.86                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ B ) ) =>
% 0.68/0.86                   ( ![E:$i]:
% 0.68/0.86                     ( ( ( v1_funct_1 @ E ) & 
% 0.68/0.86                         ( v1_funct_2 @
% 0.68/0.86                           E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ A ) ) & 
% 0.68/0.86                         ( m1_subset_1 @
% 0.68/0.86                           E @ 
% 0.68/0.86                           ( k1_zfmisc_1 @
% 0.68/0.86                             ( k2_zfmisc_1 @
% 0.68/0.86                               ( u1_struct_0 @ D ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.68/0.86                       ( ( m1_pre_topc @ C @ D ) =>
% 0.68/0.86                         ( ![F:$i]:
% 0.68/0.86                           ( ( m1_subset_1 @
% 0.68/0.86                               F @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.68/0.86                             ( ![G:$i]:
% 0.68/0.86                               ( ( m1_subset_1 @ G @ ( u1_struct_0 @ D ) ) =>
% 0.68/0.86                                 ( ![H:$i]:
% 0.68/0.86                                   ( ( m1_subset_1 @ H @ ( u1_struct_0 @ C ) ) =>
% 0.68/0.86                                     ( ( ( v3_pre_topc @ F @ B ) & 
% 0.68/0.86                                         ( r2_hidden @ G @ F ) & 
% 0.68/0.86                                         ( r1_tarski @ F @ ( u1_struct_0 @ C ) ) & 
% 0.68/0.86                                         ( ( G ) = ( H ) ) ) =>
% 0.68/0.86                                       ( ( r1_tmap_1 @ D @ A @ E @ G ) <=>
% 0.68/0.86                                         ( r1_tmap_1 @
% 0.68/0.86                                           C @ A @ 
% 0.68/0.86                                           ( k3_tmap_1 @ B @ A @ D @ C @ E ) @ 
% 0.68/0.86                                           H ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.68/0.86  thf(zf_stmt_0, negated_conjecture,
% 0.68/0.86    (~( ![A:$i]:
% 0.68/0.86        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.68/0.86            ( l1_pre_topc @ A ) ) =>
% 0.68/0.86          ( ![B:$i]:
% 0.68/0.86            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.68/0.86                ( l1_pre_topc @ B ) ) =>
% 0.68/0.86              ( ![C:$i]:
% 0.68/0.86                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ B ) ) =>
% 0.68/0.86                  ( ![D:$i]:
% 0.68/0.86                    ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ B ) ) =>
% 0.68/0.86                      ( ![E:$i]:
% 0.68/0.86                        ( ( ( v1_funct_1 @ E ) & 
% 0.68/0.86                            ( v1_funct_2 @
% 0.68/0.86                              E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ A ) ) & 
% 0.68/0.86                            ( m1_subset_1 @
% 0.68/0.86                              E @ 
% 0.68/0.86                              ( k1_zfmisc_1 @
% 0.68/0.86                                ( k2_zfmisc_1 @
% 0.68/0.86                                  ( u1_struct_0 @ D ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.68/0.86                          ( ( m1_pre_topc @ C @ D ) =>
% 0.68/0.86                            ( ![F:$i]:
% 0.68/0.86                              ( ( m1_subset_1 @
% 0.68/0.86                                  F @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.68/0.86                                ( ![G:$i]:
% 0.68/0.86                                  ( ( m1_subset_1 @ G @ ( u1_struct_0 @ D ) ) =>
% 0.68/0.86                                    ( ![H:$i]:
% 0.68/0.86                                      ( ( m1_subset_1 @ H @ ( u1_struct_0 @ C ) ) =>
% 0.68/0.86                                        ( ( ( v3_pre_topc @ F @ B ) & 
% 0.68/0.86                                            ( r2_hidden @ G @ F ) & 
% 0.68/0.86                                            ( r1_tarski @
% 0.68/0.86                                              F @ ( u1_struct_0 @ C ) ) & 
% 0.68/0.86                                            ( ( G ) = ( H ) ) ) =>
% 0.68/0.86                                          ( ( r1_tmap_1 @ D @ A @ E @ G ) <=>
% 0.68/0.86                                            ( r1_tmap_1 @
% 0.68/0.86                                              C @ A @ 
% 0.68/0.86                                              ( k3_tmap_1 @ B @ A @ D @ C @ E ) @ 
% 0.68/0.86                                              H ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.68/0.86    inference('cnf.neg', [status(esa)], [t85_tmap_1])).
% 0.68/0.86  thf('0', plain, (~ (v2_struct_0 @ sk_C)),
% 0.68/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.86  thf('1', plain, ((m1_pre_topc @ sk_C @ sk_D_1)),
% 0.68/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.86  thf(d10_xboole_0, axiom,
% 0.68/0.86    (![A:$i,B:$i]:
% 0.68/0.86     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.68/0.86  thf('2', plain,
% 0.68/0.86      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.68/0.86      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.68/0.86  thf('3', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.68/0.86      inference('simplify', [status(thm)], ['2'])).
% 0.68/0.86  thf(t3_subset, axiom,
% 0.68/0.86    (![A:$i,B:$i]:
% 0.68/0.86     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.68/0.86  thf('4', plain,
% 0.68/0.86      (![X3 : $i, X5 : $i]:
% 0.68/0.86         ((m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X5)) | ~ (r1_tarski @ X3 @ X5))),
% 0.68/0.86      inference('cnf', [status(esa)], [t3_subset])).
% 0.68/0.86  thf('5', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.68/0.86      inference('sup-', [status(thm)], ['3', '4'])).
% 0.68/0.86  thf(t39_pre_topc, axiom,
% 0.68/0.86    (![A:$i]:
% 0.68/0.86     ( ( l1_pre_topc @ A ) =>
% 0.68/0.86       ( ![B:$i]:
% 0.68/0.86         ( ( m1_pre_topc @ B @ A ) =>
% 0.68/0.86           ( ![C:$i]:
% 0.68/0.86             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.68/0.86               ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ))).
% 0.68/0.86  thf('6', plain,
% 0.68/0.86      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.68/0.86         (~ (m1_pre_topc @ X13 @ X14)
% 0.68/0.86          | (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.68/0.86          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.68/0.86          | ~ (l1_pre_topc @ X14))),
% 0.68/0.86      inference('cnf', [status(esa)], [t39_pre_topc])).
% 0.68/0.86  thf('7', plain,
% 0.68/0.86      (![X0 : $i, X1 : $i]:
% 0.68/0.86         (~ (l1_pre_topc @ X1)
% 0.68/0.86          | (m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 0.68/0.86             (k1_zfmisc_1 @ (u1_struct_0 @ X1)))
% 0.68/0.86          | ~ (m1_pre_topc @ X0 @ X1))),
% 0.68/0.86      inference('sup-', [status(thm)], ['5', '6'])).
% 0.68/0.86  thf('8', plain,
% 0.68/0.86      (((m1_subset_1 @ (u1_struct_0 @ sk_C) @ 
% 0.68/0.86         (k1_zfmisc_1 @ (u1_struct_0 @ sk_D_1)))
% 0.68/0.86        | ~ (l1_pre_topc @ sk_D_1))),
% 0.68/0.86      inference('sup-', [status(thm)], ['1', '7'])).
% 0.68/0.86  thf('9', plain, ((m1_pre_topc @ sk_D_1 @ sk_B)),
% 0.68/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.86  thf(dt_m1_pre_topc, axiom,
% 0.68/0.86    (![A:$i]:
% 0.68/0.86     ( ( l1_pre_topc @ A ) =>
% 0.68/0.86       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.68/0.86  thf('10', plain,
% 0.68/0.86      (![X11 : $i, X12 : $i]:
% 0.68/0.86         (~ (m1_pre_topc @ X11 @ X12)
% 0.68/0.86          | (l1_pre_topc @ X11)
% 0.68/0.86          | ~ (l1_pre_topc @ X12))),
% 0.68/0.86      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.68/0.86  thf('11', plain, ((~ (l1_pre_topc @ sk_B) | (l1_pre_topc @ sk_D_1))),
% 0.68/0.86      inference('sup-', [status(thm)], ['9', '10'])).
% 0.68/0.86  thf('12', plain, ((l1_pre_topc @ sk_B)),
% 0.68/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.86  thf('13', plain, ((l1_pre_topc @ sk_D_1)),
% 0.68/0.86      inference('demod', [status(thm)], ['11', '12'])).
% 0.68/0.86  thf('14', plain,
% 0.68/0.86      ((m1_subset_1 @ (u1_struct_0 @ sk_C) @ 
% 0.68/0.86        (k1_zfmisc_1 @ (u1_struct_0 @ sk_D_1)))),
% 0.68/0.86      inference('demod', [status(thm)], ['8', '13'])).
% 0.68/0.86  thf('15', plain,
% 0.68/0.86      (((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.68/0.86         (k3_tmap_1 @ sk_B @ sk_A @ sk_D_1 @ sk_C @ sk_E) @ sk_H)
% 0.68/0.86        | (r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_G))),
% 0.68/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.86  thf('16', plain,
% 0.68/0.86      (((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.68/0.86         (k3_tmap_1 @ sk_B @ sk_A @ sk_D_1 @ sk_C @ sk_E) @ sk_H))
% 0.68/0.86         <= (((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.68/0.86               (k3_tmap_1 @ sk_B @ sk_A @ sk_D_1 @ sk_C @ sk_E) @ sk_H)))),
% 0.68/0.86      inference('split', [status(esa)], ['15'])).
% 0.68/0.86  thf('17', plain, ((m1_pre_topc @ sk_C @ sk_B)),
% 0.68/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.86  thf('18', plain, ((m1_pre_topc @ sk_D_1 @ sk_B)),
% 0.68/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.86  thf('19', plain,
% 0.68/0.86      ((m1_subset_1 @ sk_E @ 
% 0.68/0.86        (k1_zfmisc_1 @ 
% 0.68/0.86         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D_1) @ (u1_struct_0 @ sk_A))))),
% 0.68/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.86  thf(d5_tmap_1, axiom,
% 0.68/0.86    (![A:$i]:
% 0.68/0.86     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.68/0.86       ( ![B:$i]:
% 0.68/0.86         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.68/0.86             ( l1_pre_topc @ B ) ) =>
% 0.68/0.86           ( ![C:$i]:
% 0.68/0.86             ( ( m1_pre_topc @ C @ A ) =>
% 0.68/0.86               ( ![D:$i]:
% 0.68/0.86                 ( ( m1_pre_topc @ D @ A ) =>
% 0.68/0.86                   ( ![E:$i]:
% 0.68/0.86                     ( ( ( v1_funct_1 @ E ) & 
% 0.68/0.86                         ( v1_funct_2 @
% 0.68/0.86                           E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 0.68/0.86                         ( m1_subset_1 @
% 0.68/0.86                           E @ 
% 0.68/0.86                           ( k1_zfmisc_1 @
% 0.68/0.86                             ( k2_zfmisc_1 @
% 0.68/0.86                               ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.68/0.86                       ( ( m1_pre_topc @ D @ C ) =>
% 0.68/0.86                         ( ( k3_tmap_1 @ A @ B @ C @ D @ E ) =
% 0.68/0.86                           ( k2_partfun1 @
% 0.68/0.86                             ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ E @ 
% 0.68/0.86                             ( u1_struct_0 @ D ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.68/0.86  thf('20', plain,
% 0.68/0.86      (![X34 : $i, X35 : $i, X36 : $i, X37 : $i, X38 : $i]:
% 0.68/0.86         ((v2_struct_0 @ X34)
% 0.68/0.86          | ~ (v2_pre_topc @ X34)
% 0.68/0.86          | ~ (l1_pre_topc @ X34)
% 0.68/0.86          | ~ (m1_pre_topc @ X35 @ X36)
% 0.68/0.86          | ~ (m1_pre_topc @ X35 @ X37)
% 0.68/0.86          | ((k3_tmap_1 @ X36 @ X34 @ X37 @ X35 @ X38)
% 0.68/0.86              = (k2_partfun1 @ (u1_struct_0 @ X37) @ (u1_struct_0 @ X34) @ 
% 0.68/0.86                 X38 @ (u1_struct_0 @ X35)))
% 0.68/0.86          | ~ (m1_subset_1 @ X38 @ 
% 0.68/0.86               (k1_zfmisc_1 @ 
% 0.68/0.86                (k2_zfmisc_1 @ (u1_struct_0 @ X37) @ (u1_struct_0 @ X34))))
% 0.68/0.86          | ~ (v1_funct_2 @ X38 @ (u1_struct_0 @ X37) @ (u1_struct_0 @ X34))
% 0.68/0.86          | ~ (v1_funct_1 @ X38)
% 0.68/0.86          | ~ (m1_pre_topc @ X37 @ X36)
% 0.68/0.86          | ~ (l1_pre_topc @ X36)
% 0.68/0.86          | ~ (v2_pre_topc @ X36)
% 0.68/0.86          | (v2_struct_0 @ X36))),
% 0.68/0.86      inference('cnf', [status(esa)], [d5_tmap_1])).
% 0.68/0.86  thf('21', plain,
% 0.68/0.86      (![X0 : $i, X1 : $i]:
% 0.68/0.86         ((v2_struct_0 @ X0)
% 0.68/0.86          | ~ (v2_pre_topc @ X0)
% 0.68/0.86          | ~ (l1_pre_topc @ X0)
% 0.68/0.86          | ~ (m1_pre_topc @ sk_D_1 @ X0)
% 0.68/0.86          | ~ (v1_funct_1 @ sk_E)
% 0.68/0.86          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D_1) @ 
% 0.68/0.86               (u1_struct_0 @ sk_A))
% 0.68/0.86          | ((k3_tmap_1 @ X0 @ sk_A @ sk_D_1 @ X1 @ sk_E)
% 0.68/0.86              = (k2_partfun1 @ (u1_struct_0 @ sk_D_1) @ (u1_struct_0 @ sk_A) @ 
% 0.68/0.86                 sk_E @ (u1_struct_0 @ X1)))
% 0.68/0.86          | ~ (m1_pre_topc @ X1 @ sk_D_1)
% 0.68/0.86          | ~ (m1_pre_topc @ X1 @ X0)
% 0.68/0.86          | ~ (l1_pre_topc @ sk_A)
% 0.68/0.86          | ~ (v2_pre_topc @ sk_A)
% 0.68/0.86          | (v2_struct_0 @ sk_A))),
% 0.68/0.86      inference('sup-', [status(thm)], ['19', '20'])).
% 0.68/0.86  thf('22', plain, ((v1_funct_1 @ sk_E)),
% 0.68/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.86  thf('23', plain,
% 0.68/0.86      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D_1) @ (u1_struct_0 @ sk_A))),
% 0.68/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.86  thf('24', plain, ((l1_pre_topc @ sk_A)),
% 0.68/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.86  thf('25', plain, ((v2_pre_topc @ sk_A)),
% 0.68/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.86  thf('26', plain,
% 0.68/0.86      (![X0 : $i, X1 : $i]:
% 0.68/0.86         ((v2_struct_0 @ X0)
% 0.68/0.86          | ~ (v2_pre_topc @ X0)
% 0.68/0.86          | ~ (l1_pre_topc @ X0)
% 0.68/0.86          | ~ (m1_pre_topc @ sk_D_1 @ X0)
% 0.68/0.86          | ((k3_tmap_1 @ X0 @ sk_A @ sk_D_1 @ X1 @ sk_E)
% 0.68/0.86              = (k2_partfun1 @ (u1_struct_0 @ sk_D_1) @ (u1_struct_0 @ sk_A) @ 
% 0.68/0.86                 sk_E @ (u1_struct_0 @ X1)))
% 0.68/0.86          | ~ (m1_pre_topc @ X1 @ sk_D_1)
% 0.68/0.86          | ~ (m1_pre_topc @ X1 @ X0)
% 0.68/0.86          | (v2_struct_0 @ sk_A))),
% 0.68/0.86      inference('demod', [status(thm)], ['21', '22', '23', '24', '25'])).
% 0.68/0.86  thf('27', plain,
% 0.68/0.86      (![X0 : $i]:
% 0.68/0.86         ((v2_struct_0 @ sk_A)
% 0.68/0.86          | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.68/0.86          | ~ (m1_pre_topc @ X0 @ sk_D_1)
% 0.68/0.86          | ((k3_tmap_1 @ sk_B @ sk_A @ sk_D_1 @ X0 @ sk_E)
% 0.68/0.86              = (k2_partfun1 @ (u1_struct_0 @ sk_D_1) @ (u1_struct_0 @ sk_A) @ 
% 0.68/0.86                 sk_E @ (u1_struct_0 @ X0)))
% 0.68/0.86          | ~ (l1_pre_topc @ sk_B)
% 0.68/0.86          | ~ (v2_pre_topc @ sk_B)
% 0.68/0.86          | (v2_struct_0 @ sk_B))),
% 0.68/0.86      inference('sup-', [status(thm)], ['18', '26'])).
% 0.68/0.86  thf('28', plain, ((l1_pre_topc @ sk_B)),
% 0.68/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.86  thf('29', plain, ((v2_pre_topc @ sk_B)),
% 0.68/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.86  thf('30', plain,
% 0.68/0.86      (![X0 : $i]:
% 0.68/0.86         ((v2_struct_0 @ sk_A)
% 0.68/0.86          | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.68/0.86          | ~ (m1_pre_topc @ X0 @ sk_D_1)
% 0.68/0.86          | ((k3_tmap_1 @ sk_B @ sk_A @ sk_D_1 @ X0 @ sk_E)
% 0.68/0.86              = (k2_partfun1 @ (u1_struct_0 @ sk_D_1) @ (u1_struct_0 @ sk_A) @ 
% 0.68/0.86                 sk_E @ (u1_struct_0 @ X0)))
% 0.68/0.86          | (v2_struct_0 @ sk_B))),
% 0.68/0.86      inference('demod', [status(thm)], ['27', '28', '29'])).
% 0.68/0.86  thf('31', plain,
% 0.68/0.86      (((v2_struct_0 @ sk_B)
% 0.68/0.86        | ((k3_tmap_1 @ sk_B @ sk_A @ sk_D_1 @ sk_C @ sk_E)
% 0.68/0.86            = (k2_partfun1 @ (u1_struct_0 @ sk_D_1) @ (u1_struct_0 @ sk_A) @ 
% 0.68/0.86               sk_E @ (u1_struct_0 @ sk_C)))
% 0.68/0.86        | ~ (m1_pre_topc @ sk_C @ sk_D_1)
% 0.68/0.86        | (v2_struct_0 @ sk_A))),
% 0.68/0.86      inference('sup-', [status(thm)], ['17', '30'])).
% 0.68/0.86  thf('32', plain, ((m1_pre_topc @ sk_C @ sk_D_1)),
% 0.68/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.86  thf('33', plain,
% 0.68/0.86      ((m1_subset_1 @ sk_E @ 
% 0.68/0.86        (k1_zfmisc_1 @ 
% 0.68/0.86         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D_1) @ (u1_struct_0 @ sk_A))))),
% 0.68/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.86  thf(d4_tmap_1, axiom,
% 0.68/0.86    (![A:$i]:
% 0.68/0.86     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.68/0.86       ( ![B:$i]:
% 0.68/0.86         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.68/0.86             ( l1_pre_topc @ B ) ) =>
% 0.68/0.86           ( ![C:$i]:
% 0.68/0.86             ( ( ( v1_funct_1 @ C ) & 
% 0.68/0.86                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.68/0.86                 ( m1_subset_1 @
% 0.68/0.86                   C @ 
% 0.68/0.86                   ( k1_zfmisc_1 @
% 0.68/0.86                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.68/0.86               ( ![D:$i]:
% 0.68/0.86                 ( ( m1_pre_topc @ D @ A ) =>
% 0.68/0.86                   ( ( k2_tmap_1 @ A @ B @ C @ D ) =
% 0.68/0.86                     ( k2_partfun1 @
% 0.68/0.86                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ 
% 0.68/0.86                       ( u1_struct_0 @ D ) ) ) ) ) ) ) ) ) ))).
% 0.68/0.86  thf('34', plain,
% 0.68/0.86      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 0.68/0.86         ((v2_struct_0 @ X30)
% 0.68/0.86          | ~ (v2_pre_topc @ X30)
% 0.68/0.86          | ~ (l1_pre_topc @ X30)
% 0.68/0.86          | ~ (m1_pre_topc @ X31 @ X32)
% 0.68/0.86          | ((k2_tmap_1 @ X32 @ X30 @ X33 @ X31)
% 0.68/0.86              = (k2_partfun1 @ (u1_struct_0 @ X32) @ (u1_struct_0 @ X30) @ 
% 0.68/0.86                 X33 @ (u1_struct_0 @ X31)))
% 0.68/0.86          | ~ (m1_subset_1 @ X33 @ 
% 0.68/0.86               (k1_zfmisc_1 @ 
% 0.68/0.86                (k2_zfmisc_1 @ (u1_struct_0 @ X32) @ (u1_struct_0 @ X30))))
% 0.68/0.86          | ~ (v1_funct_2 @ X33 @ (u1_struct_0 @ X32) @ (u1_struct_0 @ X30))
% 0.68/0.86          | ~ (v1_funct_1 @ X33)
% 0.68/0.86          | ~ (l1_pre_topc @ X32)
% 0.68/0.86          | ~ (v2_pre_topc @ X32)
% 0.68/0.86          | (v2_struct_0 @ X32))),
% 0.68/0.86      inference('cnf', [status(esa)], [d4_tmap_1])).
% 0.68/0.86  thf('35', plain,
% 0.68/0.86      (![X0 : $i]:
% 0.68/0.86         ((v2_struct_0 @ sk_D_1)
% 0.68/0.86          | ~ (v2_pre_topc @ sk_D_1)
% 0.68/0.86          | ~ (l1_pre_topc @ sk_D_1)
% 0.68/0.86          | ~ (v1_funct_1 @ sk_E)
% 0.68/0.86          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D_1) @ 
% 0.68/0.86               (u1_struct_0 @ sk_A))
% 0.68/0.86          | ((k2_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ X0)
% 0.68/0.86              = (k2_partfun1 @ (u1_struct_0 @ sk_D_1) @ (u1_struct_0 @ sk_A) @ 
% 0.68/0.86                 sk_E @ (u1_struct_0 @ X0)))
% 0.68/0.86          | ~ (m1_pre_topc @ X0 @ sk_D_1)
% 0.68/0.86          | ~ (l1_pre_topc @ sk_A)
% 0.68/0.86          | ~ (v2_pre_topc @ sk_A)
% 0.68/0.86          | (v2_struct_0 @ sk_A))),
% 0.68/0.86      inference('sup-', [status(thm)], ['33', '34'])).
% 0.68/0.86  thf('36', plain, ((m1_pre_topc @ sk_D_1 @ sk_B)),
% 0.68/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.86  thf(cc1_pre_topc, axiom,
% 0.68/0.86    (![A:$i]:
% 0.68/0.86     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.68/0.86       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( v2_pre_topc @ B ) ) ) ))).
% 0.68/0.86  thf('37', plain,
% 0.68/0.86      (![X9 : $i, X10 : $i]:
% 0.68/0.86         (~ (m1_pre_topc @ X9 @ X10)
% 0.68/0.86          | (v2_pre_topc @ X9)
% 0.68/0.86          | ~ (l1_pre_topc @ X10)
% 0.68/0.86          | ~ (v2_pre_topc @ X10))),
% 0.68/0.86      inference('cnf', [status(esa)], [cc1_pre_topc])).
% 0.68/0.86  thf('38', plain,
% 0.68/0.86      ((~ (v2_pre_topc @ sk_B)
% 0.68/0.86        | ~ (l1_pre_topc @ sk_B)
% 0.68/0.86        | (v2_pre_topc @ sk_D_1))),
% 0.68/0.86      inference('sup-', [status(thm)], ['36', '37'])).
% 0.68/0.86  thf('39', plain, ((v2_pre_topc @ sk_B)),
% 0.68/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.86  thf('40', plain, ((l1_pre_topc @ sk_B)),
% 0.68/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.86  thf('41', plain, ((v2_pre_topc @ sk_D_1)),
% 0.68/0.86      inference('demod', [status(thm)], ['38', '39', '40'])).
% 0.68/0.86  thf('42', plain, ((l1_pre_topc @ sk_D_1)),
% 0.68/0.86      inference('demod', [status(thm)], ['11', '12'])).
% 0.68/0.86  thf('43', plain, ((v1_funct_1 @ sk_E)),
% 0.68/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.86  thf('44', plain,
% 0.68/0.86      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D_1) @ (u1_struct_0 @ sk_A))),
% 0.68/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.86  thf('45', plain, ((l1_pre_topc @ sk_A)),
% 0.68/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.86  thf('46', plain, ((v2_pre_topc @ sk_A)),
% 0.68/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.86  thf('47', plain,
% 0.68/0.86      (![X0 : $i]:
% 0.68/0.86         ((v2_struct_0 @ sk_D_1)
% 0.68/0.86          | ((k2_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ X0)
% 0.68/0.86              = (k2_partfun1 @ (u1_struct_0 @ sk_D_1) @ (u1_struct_0 @ sk_A) @ 
% 0.68/0.86                 sk_E @ (u1_struct_0 @ X0)))
% 0.68/0.86          | ~ (m1_pre_topc @ X0 @ sk_D_1)
% 0.68/0.86          | (v2_struct_0 @ sk_A))),
% 0.68/0.86      inference('demod', [status(thm)],
% 0.68/0.86                ['35', '41', '42', '43', '44', '45', '46'])).
% 0.68/0.86  thf('48', plain,
% 0.68/0.86      (((v2_struct_0 @ sk_A)
% 0.68/0.86        | ((k2_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_C)
% 0.68/0.86            = (k2_partfun1 @ (u1_struct_0 @ sk_D_1) @ (u1_struct_0 @ sk_A) @ 
% 0.68/0.86               sk_E @ (u1_struct_0 @ sk_C)))
% 0.68/0.86        | (v2_struct_0 @ sk_D_1))),
% 0.68/0.86      inference('sup-', [status(thm)], ['32', '47'])).
% 0.68/0.86  thf('49', plain, (~ (v2_struct_0 @ sk_A)),
% 0.68/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.86  thf('50', plain,
% 0.68/0.86      (((v2_struct_0 @ sk_D_1)
% 0.68/0.86        | ((k2_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_C)
% 0.68/0.86            = (k2_partfun1 @ (u1_struct_0 @ sk_D_1) @ (u1_struct_0 @ sk_A) @ 
% 0.68/0.86               sk_E @ (u1_struct_0 @ sk_C))))),
% 0.68/0.86      inference('clc', [status(thm)], ['48', '49'])).
% 0.68/0.86  thf('51', plain, (~ (v2_struct_0 @ sk_D_1)),
% 0.68/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.86  thf('52', plain,
% 0.68/0.86      (((k2_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_C)
% 0.68/0.86         = (k2_partfun1 @ (u1_struct_0 @ sk_D_1) @ (u1_struct_0 @ sk_A) @ 
% 0.68/0.86            sk_E @ (u1_struct_0 @ sk_C)))),
% 0.68/0.86      inference('clc', [status(thm)], ['50', '51'])).
% 0.68/0.86  thf('53', plain, ((m1_pre_topc @ sk_C @ sk_D_1)),
% 0.68/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.86  thf('54', plain,
% 0.68/0.86      (((v2_struct_0 @ sk_B)
% 0.68/0.86        | ((k3_tmap_1 @ sk_B @ sk_A @ sk_D_1 @ sk_C @ sk_E)
% 0.68/0.86            = (k2_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_C))
% 0.68/0.86        | (v2_struct_0 @ sk_A))),
% 0.68/0.86      inference('demod', [status(thm)], ['31', '52', '53'])).
% 0.68/0.86  thf('55', plain, (~ (v2_struct_0 @ sk_B)),
% 0.68/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.86  thf('56', plain,
% 0.68/0.86      (((v2_struct_0 @ sk_A)
% 0.68/0.86        | ((k3_tmap_1 @ sk_B @ sk_A @ sk_D_1 @ sk_C @ sk_E)
% 0.68/0.86            = (k2_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_C)))),
% 0.68/0.86      inference('clc', [status(thm)], ['54', '55'])).
% 0.68/0.86  thf('57', plain, (~ (v2_struct_0 @ sk_A)),
% 0.68/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.86  thf('58', plain,
% 0.68/0.86      (((k3_tmap_1 @ sk_B @ sk_A @ sk_D_1 @ sk_C @ sk_E)
% 0.68/0.86         = (k2_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_C))),
% 0.68/0.86      inference('clc', [status(thm)], ['56', '57'])).
% 0.68/0.86  thf('59', plain,
% 0.68/0.86      (((r1_tmap_1 @ sk_C @ sk_A @ (k2_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_C) @ 
% 0.68/0.86         sk_H))
% 0.68/0.86         <= (((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.68/0.86               (k3_tmap_1 @ sk_B @ sk_A @ sk_D_1 @ sk_C @ sk_E) @ sk_H)))),
% 0.68/0.86      inference('demod', [status(thm)], ['16', '58'])).
% 0.68/0.86  thf('60', plain,
% 0.68/0.86      ((~ (r1_tmap_1 @ sk_C @ sk_A @ 
% 0.68/0.86           (k3_tmap_1 @ sk_B @ sk_A @ sk_D_1 @ sk_C @ sk_E) @ sk_H)
% 0.68/0.86        | ~ (r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_G))),
% 0.68/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.86  thf('61', plain, (((sk_G) = (sk_H))),
% 0.68/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.86  thf('62', plain,
% 0.68/0.86      ((~ (r1_tmap_1 @ sk_C @ sk_A @ 
% 0.68/0.86           (k3_tmap_1 @ sk_B @ sk_A @ sk_D_1 @ sk_C @ sk_E) @ sk_H)
% 0.68/0.86        | ~ (r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_H))),
% 0.68/0.86      inference('demod', [status(thm)], ['60', '61'])).
% 0.68/0.86  thf('63', plain,
% 0.68/0.86      (~ ((r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_H)) | 
% 0.68/0.86       ~
% 0.68/0.86       ((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.68/0.86         (k3_tmap_1 @ sk_B @ sk_A @ sk_D_1 @ sk_C @ sk_E) @ sk_H))),
% 0.68/0.86      inference('split', [status(esa)], ['62'])).
% 0.68/0.86  thf('64', plain,
% 0.68/0.86      (((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.68/0.86         (k3_tmap_1 @ sk_B @ sk_A @ sk_D_1 @ sk_C @ sk_E) @ sk_H)
% 0.68/0.86        | (r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_G))),
% 0.68/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.86  thf('65', plain, (((sk_G) = (sk_H))),
% 0.68/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.86  thf('66', plain,
% 0.68/0.86      (((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.68/0.86         (k3_tmap_1 @ sk_B @ sk_A @ sk_D_1 @ sk_C @ sk_E) @ sk_H)
% 0.68/0.86        | (r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_H))),
% 0.68/0.86      inference('demod', [status(thm)], ['64', '65'])).
% 0.68/0.86  thf('67', plain,
% 0.68/0.86      (((r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_H))
% 0.68/0.86         <= (((r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_H)))),
% 0.68/0.86      inference('split', [status(esa)], ['66'])).
% 0.68/0.86  thf('68', plain,
% 0.68/0.86      ((~ (r1_tmap_1 @ sk_C @ sk_A @ 
% 0.68/0.86           (k3_tmap_1 @ sk_B @ sk_A @ sk_D_1 @ sk_C @ sk_E) @ sk_H)
% 0.68/0.87        | ~ (r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_G))),
% 0.68/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.87  thf('69', plain,
% 0.68/0.87      ((~ (r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_G))
% 0.68/0.87         <= (~ ((r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_G)))),
% 0.68/0.87      inference('split', [status(esa)], ['68'])).
% 0.68/0.87  thf('70', plain, (((sk_G) = (sk_H))),
% 0.68/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.87  thf('71', plain,
% 0.68/0.87      ((~ (r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_H))
% 0.68/0.87         <= (~ ((r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_G)))),
% 0.68/0.87      inference('demod', [status(thm)], ['69', '70'])).
% 0.68/0.87  thf('72', plain,
% 0.68/0.87      (~ ((r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_H)) | 
% 0.68/0.87       ((r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_G))),
% 0.68/0.87      inference('sup-', [status(thm)], ['67', '71'])).
% 0.68/0.87  thf('73', plain, ((m1_subset_1 @ sk_H @ (u1_struct_0 @ sk_C))),
% 0.68/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.87  thf('74', plain,
% 0.68/0.87      (((r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_G))
% 0.68/0.87         <= (((r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_G)))),
% 0.68/0.87      inference('split', [status(esa)], ['15'])).
% 0.68/0.87  thf('75', plain, (((sk_G) = (sk_H))),
% 0.68/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.87  thf('76', plain,
% 0.68/0.87      (((r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_H))
% 0.68/0.87         <= (((r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_G)))),
% 0.68/0.87      inference('demod', [status(thm)], ['74', '75'])).
% 0.68/0.87  thf('77', plain,
% 0.68/0.87      ((m1_subset_1 @ sk_E @ 
% 0.68/0.87        (k1_zfmisc_1 @ 
% 0.68/0.87         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D_1) @ (u1_struct_0 @ sk_A))))),
% 0.68/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.87  thf(t64_tmap_1, axiom,
% 0.68/0.87    (![A:$i]:
% 0.68/0.87     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.68/0.87       ( ![B:$i]:
% 0.68/0.87         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.68/0.87             ( l1_pre_topc @ B ) ) =>
% 0.68/0.87           ( ![C:$i]:
% 0.68/0.87             ( ( ( v1_funct_1 @ C ) & 
% 0.68/0.87                 ( v1_funct_2 @ C @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 0.68/0.87                 ( m1_subset_1 @
% 0.68/0.87                   C @ 
% 0.68/0.87                   ( k1_zfmisc_1 @
% 0.68/0.87                     ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.68/0.87               ( ![D:$i]:
% 0.68/0.87                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ B ) ) =>
% 0.68/0.87                   ( ![E:$i]:
% 0.68/0.87                     ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) =>
% 0.68/0.87                       ( ![F:$i]:
% 0.68/0.87                         ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 0.68/0.87                           ( ( ( ( E ) = ( F ) ) & 
% 0.68/0.87                               ( r1_tmap_1 @ B @ A @ C @ E ) ) =>
% 0.68/0.87                             ( r1_tmap_1 @
% 0.68/0.87                               D @ A @ ( k2_tmap_1 @ B @ A @ C @ D ) @ F ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.68/0.87  thf('78', plain,
% 0.68/0.87      (![X39 : $i, X40 : $i, X41 : $i, X42 : $i, X43 : $i, X44 : $i]:
% 0.68/0.87         ((v2_struct_0 @ X39)
% 0.68/0.87          | ~ (v2_pre_topc @ X39)
% 0.68/0.87          | ~ (l1_pre_topc @ X39)
% 0.68/0.87          | (v2_struct_0 @ X40)
% 0.68/0.87          | ~ (m1_pre_topc @ X40 @ X39)
% 0.68/0.87          | ~ (m1_subset_1 @ X41 @ (u1_struct_0 @ X40))
% 0.68/0.87          | (r1_tmap_1 @ X40 @ X42 @ (k2_tmap_1 @ X39 @ X42 @ X43 @ X40) @ X41)
% 0.68/0.87          | ((X44) != (X41))
% 0.68/0.87          | ~ (r1_tmap_1 @ X39 @ X42 @ X43 @ X44)
% 0.68/0.87          | ~ (m1_subset_1 @ X44 @ (u1_struct_0 @ X39))
% 0.68/0.87          | ~ (m1_subset_1 @ X43 @ 
% 0.68/0.87               (k1_zfmisc_1 @ 
% 0.68/0.87                (k2_zfmisc_1 @ (u1_struct_0 @ X39) @ (u1_struct_0 @ X42))))
% 0.68/0.87          | ~ (v1_funct_2 @ X43 @ (u1_struct_0 @ X39) @ (u1_struct_0 @ X42))
% 0.68/0.87          | ~ (v1_funct_1 @ X43)
% 0.68/0.87          | ~ (l1_pre_topc @ X42)
% 0.68/0.87          | ~ (v2_pre_topc @ X42)
% 0.68/0.87          | (v2_struct_0 @ X42))),
% 0.68/0.87      inference('cnf', [status(esa)], [t64_tmap_1])).
% 0.68/0.87  thf('79', plain,
% 0.68/0.87      (![X39 : $i, X40 : $i, X41 : $i, X42 : $i, X43 : $i]:
% 0.68/0.87         ((v2_struct_0 @ X42)
% 0.68/0.87          | ~ (v2_pre_topc @ X42)
% 0.68/0.87          | ~ (l1_pre_topc @ X42)
% 0.68/0.87          | ~ (v1_funct_1 @ X43)
% 0.68/0.87          | ~ (v1_funct_2 @ X43 @ (u1_struct_0 @ X39) @ (u1_struct_0 @ X42))
% 0.68/0.87          | ~ (m1_subset_1 @ X43 @ 
% 0.68/0.87               (k1_zfmisc_1 @ 
% 0.68/0.87                (k2_zfmisc_1 @ (u1_struct_0 @ X39) @ (u1_struct_0 @ X42))))
% 0.68/0.87          | ~ (m1_subset_1 @ X41 @ (u1_struct_0 @ X39))
% 0.68/0.87          | ~ (r1_tmap_1 @ X39 @ X42 @ X43 @ X41)
% 0.68/0.87          | (r1_tmap_1 @ X40 @ X42 @ (k2_tmap_1 @ X39 @ X42 @ X43 @ X40) @ X41)
% 0.68/0.87          | ~ (m1_subset_1 @ X41 @ (u1_struct_0 @ X40))
% 0.68/0.87          | ~ (m1_pre_topc @ X40 @ X39)
% 0.68/0.87          | (v2_struct_0 @ X40)
% 0.68/0.87          | ~ (l1_pre_topc @ X39)
% 0.68/0.87          | ~ (v2_pre_topc @ X39)
% 0.68/0.87          | (v2_struct_0 @ X39))),
% 0.68/0.87      inference('simplify', [status(thm)], ['78'])).
% 0.68/0.87  thf('80', plain,
% 0.68/0.87      (![X0 : $i, X1 : $i]:
% 0.68/0.87         ((v2_struct_0 @ sk_D_1)
% 0.68/0.87          | ~ (v2_pre_topc @ sk_D_1)
% 0.68/0.87          | ~ (l1_pre_topc @ sk_D_1)
% 0.68/0.87          | (v2_struct_0 @ X0)
% 0.68/0.87          | ~ (m1_pre_topc @ X0 @ sk_D_1)
% 0.68/0.87          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.68/0.87          | (r1_tmap_1 @ X0 @ sk_A @ (k2_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ X0) @ 
% 0.68/0.87             X1)
% 0.68/0.87          | ~ (r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ X1)
% 0.68/0.87          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_D_1))
% 0.68/0.87          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D_1) @ 
% 0.68/0.87               (u1_struct_0 @ sk_A))
% 0.68/0.87          | ~ (v1_funct_1 @ sk_E)
% 0.68/0.87          | ~ (l1_pre_topc @ sk_A)
% 0.68/0.87          | ~ (v2_pre_topc @ sk_A)
% 0.68/0.87          | (v2_struct_0 @ sk_A))),
% 0.68/0.87      inference('sup-', [status(thm)], ['77', '79'])).
% 0.68/0.87  thf('81', plain, ((v2_pre_topc @ sk_D_1)),
% 0.68/0.87      inference('demod', [status(thm)], ['38', '39', '40'])).
% 0.68/0.87  thf('82', plain, ((l1_pre_topc @ sk_D_1)),
% 0.68/0.87      inference('demod', [status(thm)], ['11', '12'])).
% 0.68/0.87  thf('83', plain,
% 0.68/0.87      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D_1) @ (u1_struct_0 @ sk_A))),
% 0.68/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.87  thf('84', plain, ((v1_funct_1 @ sk_E)),
% 0.68/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.87  thf('85', plain, ((l1_pre_topc @ sk_A)),
% 0.68/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.87  thf('86', plain, ((v2_pre_topc @ sk_A)),
% 0.68/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.87  thf('87', plain,
% 0.68/0.87      (![X0 : $i, X1 : $i]:
% 0.68/0.87         ((v2_struct_0 @ sk_D_1)
% 0.68/0.87          | (v2_struct_0 @ X0)
% 0.68/0.87          | ~ (m1_pre_topc @ X0 @ sk_D_1)
% 0.68/0.87          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.68/0.87          | (r1_tmap_1 @ X0 @ sk_A @ (k2_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ X0) @ 
% 0.68/0.87             X1)
% 0.68/0.87          | ~ (r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ X1)
% 0.68/0.87          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_D_1))
% 0.68/0.87          | (v2_struct_0 @ sk_A))),
% 0.68/0.87      inference('demod', [status(thm)],
% 0.68/0.87                ['80', '81', '82', '83', '84', '85', '86'])).
% 0.68/0.87  thf('88', plain,
% 0.68/0.87      ((![X0 : $i]:
% 0.68/0.87          ((v2_struct_0 @ sk_A)
% 0.68/0.87           | ~ (m1_subset_1 @ sk_H @ (u1_struct_0 @ sk_D_1))
% 0.68/0.87           | (r1_tmap_1 @ X0 @ sk_A @ 
% 0.68/0.87              (k2_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ X0) @ sk_H)
% 0.68/0.87           | ~ (m1_subset_1 @ sk_H @ (u1_struct_0 @ X0))
% 0.68/0.87           | ~ (m1_pre_topc @ X0 @ sk_D_1)
% 0.68/0.87           | (v2_struct_0 @ X0)
% 0.68/0.87           | (v2_struct_0 @ sk_D_1)))
% 0.68/0.87         <= (((r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_G)))),
% 0.68/0.87      inference('sup-', [status(thm)], ['76', '87'])).
% 0.68/0.87  thf('89', plain, ((m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_D_1))),
% 0.68/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.87  thf('90', plain, (((sk_G) = (sk_H))),
% 0.68/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.87  thf('91', plain, ((m1_subset_1 @ sk_H @ (u1_struct_0 @ sk_D_1))),
% 0.68/0.87      inference('demod', [status(thm)], ['89', '90'])).
% 0.68/0.87  thf('92', plain,
% 0.68/0.87      ((![X0 : $i]:
% 0.68/0.87          ((v2_struct_0 @ sk_A)
% 0.68/0.87           | (r1_tmap_1 @ X0 @ sk_A @ 
% 0.68/0.87              (k2_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ X0) @ sk_H)
% 0.68/0.87           | ~ (m1_subset_1 @ sk_H @ (u1_struct_0 @ X0))
% 0.68/0.87           | ~ (m1_pre_topc @ X0 @ sk_D_1)
% 0.68/0.87           | (v2_struct_0 @ X0)
% 0.68/0.87           | (v2_struct_0 @ sk_D_1)))
% 0.68/0.87         <= (((r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_G)))),
% 0.68/0.87      inference('demod', [status(thm)], ['88', '91'])).
% 0.68/0.87  thf('93', plain,
% 0.68/0.87      ((((v2_struct_0 @ sk_D_1)
% 0.68/0.87         | (v2_struct_0 @ sk_C)
% 0.68/0.87         | ~ (m1_pre_topc @ sk_C @ sk_D_1)
% 0.68/0.87         | (r1_tmap_1 @ sk_C @ sk_A @ 
% 0.68/0.87            (k2_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_C) @ sk_H)
% 0.68/0.87         | (v2_struct_0 @ sk_A)))
% 0.68/0.87         <= (((r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_G)))),
% 0.68/0.87      inference('sup-', [status(thm)], ['73', '92'])).
% 0.68/0.87  thf('94', plain, ((m1_pre_topc @ sk_C @ sk_D_1)),
% 0.68/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.87  thf('95', plain,
% 0.68/0.87      ((((v2_struct_0 @ sk_D_1)
% 0.68/0.87         | (v2_struct_0 @ sk_C)
% 0.68/0.87         | (r1_tmap_1 @ sk_C @ sk_A @ 
% 0.68/0.87            (k2_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_C) @ sk_H)
% 0.68/0.87         | (v2_struct_0 @ sk_A)))
% 0.68/0.87         <= (((r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_G)))),
% 0.68/0.87      inference('demod', [status(thm)], ['93', '94'])).
% 0.68/0.87  thf('96', plain,
% 0.68/0.87      (((k3_tmap_1 @ sk_B @ sk_A @ sk_D_1 @ sk_C @ sk_E)
% 0.68/0.87         = (k2_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_C))),
% 0.68/0.87      inference('clc', [status(thm)], ['56', '57'])).
% 0.68/0.87  thf('97', plain,
% 0.68/0.87      ((~ (r1_tmap_1 @ sk_C @ sk_A @ 
% 0.68/0.87           (k3_tmap_1 @ sk_B @ sk_A @ sk_D_1 @ sk_C @ sk_E) @ sk_H))
% 0.68/0.87         <= (~
% 0.68/0.87             ((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.68/0.87               (k3_tmap_1 @ sk_B @ sk_A @ sk_D_1 @ sk_C @ sk_E) @ sk_H)))),
% 0.68/0.87      inference('split', [status(esa)], ['68'])).
% 0.68/0.87  thf('98', plain,
% 0.68/0.87      ((~ (r1_tmap_1 @ sk_C @ sk_A @ 
% 0.68/0.87           (k2_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_C) @ sk_H))
% 0.68/0.87         <= (~
% 0.68/0.87             ((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.68/0.87               (k3_tmap_1 @ sk_B @ sk_A @ sk_D_1 @ sk_C @ sk_E) @ sk_H)))),
% 0.68/0.87      inference('sup-', [status(thm)], ['96', '97'])).
% 0.68/0.87  thf('99', plain,
% 0.68/0.87      ((((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_D_1)))
% 0.68/0.87         <= (~
% 0.68/0.87             ((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.68/0.87               (k3_tmap_1 @ sk_B @ sk_A @ sk_D_1 @ sk_C @ sk_E) @ sk_H)) & 
% 0.68/0.87             ((r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_G)))),
% 0.68/0.87      inference('sup-', [status(thm)], ['95', '98'])).
% 0.68/0.87  thf('100', plain, (~ (v2_struct_0 @ sk_A)),
% 0.68/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.87  thf('101', plain,
% 0.68/0.87      ((((v2_struct_0 @ sk_D_1) | (v2_struct_0 @ sk_C)))
% 0.68/0.87         <= (~
% 0.68/0.87             ((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.68/0.87               (k3_tmap_1 @ sk_B @ sk_A @ sk_D_1 @ sk_C @ sk_E) @ sk_H)) & 
% 0.68/0.87             ((r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_G)))),
% 0.68/0.87      inference('clc', [status(thm)], ['99', '100'])).
% 0.68/0.87  thf('102', plain, (~ (v2_struct_0 @ sk_D_1)),
% 0.68/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.87  thf('103', plain,
% 0.68/0.87      (((v2_struct_0 @ sk_C))
% 0.68/0.87         <= (~
% 0.68/0.87             ((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.68/0.87               (k3_tmap_1 @ sk_B @ sk_A @ sk_D_1 @ sk_C @ sk_E) @ sk_H)) & 
% 0.68/0.87             ((r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_G)))),
% 0.68/0.87      inference('clc', [status(thm)], ['101', '102'])).
% 0.68/0.87  thf('104', plain, (~ (v2_struct_0 @ sk_C)),
% 0.68/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.87  thf('105', plain,
% 0.68/0.87      (((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.68/0.87         (k3_tmap_1 @ sk_B @ sk_A @ sk_D_1 @ sk_C @ sk_E) @ sk_H)) | 
% 0.68/0.87       ~ ((r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_G))),
% 0.68/0.87      inference('sup-', [status(thm)], ['103', '104'])).
% 0.68/0.87  thf('106', plain,
% 0.68/0.87      (((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.68/0.87         (k3_tmap_1 @ sk_B @ sk_A @ sk_D_1 @ sk_C @ sk_E) @ sk_H)) | 
% 0.68/0.87       ((r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_H))),
% 0.68/0.87      inference('split', [status(esa)], ['66'])).
% 0.68/0.87  thf('107', plain,
% 0.68/0.87      (((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.68/0.87         (k3_tmap_1 @ sk_B @ sk_A @ sk_D_1 @ sk_C @ sk_E) @ sk_H))),
% 0.68/0.87      inference('sat_resolution*', [status(thm)], ['63', '72', '105', '106'])).
% 0.68/0.87  thf('108', plain,
% 0.68/0.87      ((r1_tmap_1 @ sk_C @ sk_A @ (k2_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_C) @ 
% 0.68/0.87        sk_H)),
% 0.68/0.87      inference('simpl_trail', [status(thm)], ['59', '107'])).
% 0.68/0.87  thf('109', plain,
% 0.68/0.87      ((m1_subset_1 @ sk_E @ 
% 0.68/0.87        (k1_zfmisc_1 @ 
% 0.68/0.87         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D_1) @ (u1_struct_0 @ sk_A))))),
% 0.68/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.87  thf(t65_tmap_1, axiom,
% 0.68/0.87    (![A:$i]:
% 0.68/0.87     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.68/0.87       ( ![B:$i]:
% 0.68/0.87         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.68/0.87             ( l1_pre_topc @ B ) ) =>
% 0.68/0.87           ( ![C:$i]:
% 0.68/0.87             ( ( ( v1_funct_1 @ C ) & 
% 0.68/0.87                 ( v1_funct_2 @ C @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 0.68/0.87                 ( m1_subset_1 @
% 0.68/0.87                   C @ 
% 0.68/0.87                   ( k1_zfmisc_1 @
% 0.68/0.87                     ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.68/0.87               ( ![D:$i]:
% 0.68/0.87                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ B ) ) =>
% 0.68/0.87                   ( ![E:$i]:
% 0.68/0.87                     ( ( m1_subset_1 @
% 0.68/0.87                         E @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.68/0.87                       ( ![F:$i]:
% 0.68/0.87                         ( ( m1_subset_1 @ F @ ( u1_struct_0 @ B ) ) =>
% 0.68/0.87                           ( ![G:$i]:
% 0.68/0.87                             ( ( m1_subset_1 @ G @ ( u1_struct_0 @ D ) ) =>
% 0.68/0.87                               ( ( ( r1_tarski @ E @ ( u1_struct_0 @ D ) ) & 
% 0.68/0.87                                   ( m1_connsp_2 @ E @ B @ F ) & 
% 0.68/0.87                                   ( ( F ) = ( G ) ) ) =>
% 0.68/0.87                                 ( ( r1_tmap_1 @ B @ A @ C @ F ) <=>
% 0.68/0.87                                   ( r1_tmap_1 @
% 0.68/0.87                                     D @ A @ ( k2_tmap_1 @ B @ A @ C @ D ) @ G ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.68/0.87  thf('110', plain,
% 0.68/0.87      (![X45 : $i, X46 : $i, X47 : $i, X48 : $i, X49 : $i, X50 : $i, X51 : $i]:
% 0.68/0.87         ((v2_struct_0 @ X45)
% 0.68/0.87          | ~ (v2_pre_topc @ X45)
% 0.68/0.87          | ~ (l1_pre_topc @ X45)
% 0.68/0.87          | (v2_struct_0 @ X46)
% 0.68/0.87          | ~ (m1_pre_topc @ X46 @ X45)
% 0.68/0.87          | ~ (m1_subset_1 @ X47 @ (u1_struct_0 @ X45))
% 0.68/0.87          | ~ (r1_tarski @ X48 @ (u1_struct_0 @ X46))
% 0.68/0.87          | ~ (m1_connsp_2 @ X48 @ X45 @ X47)
% 0.68/0.87          | ((X47) != (X49))
% 0.68/0.87          | ~ (r1_tmap_1 @ X46 @ X50 @ (k2_tmap_1 @ X45 @ X50 @ X51 @ X46) @ 
% 0.68/0.87               X49)
% 0.68/0.87          | (r1_tmap_1 @ X45 @ X50 @ X51 @ X47)
% 0.68/0.87          | ~ (m1_subset_1 @ X49 @ (u1_struct_0 @ X46))
% 0.68/0.87          | ~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ (u1_struct_0 @ X45)))
% 0.68/0.87          | ~ (m1_subset_1 @ X51 @ 
% 0.68/0.87               (k1_zfmisc_1 @ 
% 0.68/0.87                (k2_zfmisc_1 @ (u1_struct_0 @ X45) @ (u1_struct_0 @ X50))))
% 0.68/0.87          | ~ (v1_funct_2 @ X51 @ (u1_struct_0 @ X45) @ (u1_struct_0 @ X50))
% 0.68/0.87          | ~ (v1_funct_1 @ X51)
% 0.68/0.87          | ~ (l1_pre_topc @ X50)
% 0.68/0.87          | ~ (v2_pre_topc @ X50)
% 0.68/0.87          | (v2_struct_0 @ X50))),
% 0.68/0.87      inference('cnf', [status(esa)], [t65_tmap_1])).
% 0.68/0.87  thf('111', plain,
% 0.68/0.87      (![X45 : $i, X46 : $i, X48 : $i, X49 : $i, X50 : $i, X51 : $i]:
% 0.68/0.87         ((v2_struct_0 @ X50)
% 0.68/0.87          | ~ (v2_pre_topc @ X50)
% 0.68/0.87          | ~ (l1_pre_topc @ X50)
% 0.68/0.87          | ~ (v1_funct_1 @ X51)
% 0.68/0.87          | ~ (v1_funct_2 @ X51 @ (u1_struct_0 @ X45) @ (u1_struct_0 @ X50))
% 0.68/0.87          | ~ (m1_subset_1 @ X51 @ 
% 0.68/0.87               (k1_zfmisc_1 @ 
% 0.68/0.87                (k2_zfmisc_1 @ (u1_struct_0 @ X45) @ (u1_struct_0 @ X50))))
% 0.68/0.87          | ~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ (u1_struct_0 @ X45)))
% 0.68/0.87          | ~ (m1_subset_1 @ X49 @ (u1_struct_0 @ X46))
% 0.68/0.87          | (r1_tmap_1 @ X45 @ X50 @ X51 @ X49)
% 0.68/0.87          | ~ (r1_tmap_1 @ X46 @ X50 @ (k2_tmap_1 @ X45 @ X50 @ X51 @ X46) @ 
% 0.68/0.87               X49)
% 0.68/0.87          | ~ (m1_connsp_2 @ X48 @ X45 @ X49)
% 0.68/0.87          | ~ (r1_tarski @ X48 @ (u1_struct_0 @ X46))
% 0.68/0.87          | ~ (m1_subset_1 @ X49 @ (u1_struct_0 @ X45))
% 0.68/0.87          | ~ (m1_pre_topc @ X46 @ X45)
% 0.68/0.87          | (v2_struct_0 @ X46)
% 0.68/0.87          | ~ (l1_pre_topc @ X45)
% 0.68/0.87          | ~ (v2_pre_topc @ X45)
% 0.68/0.87          | (v2_struct_0 @ X45))),
% 0.68/0.87      inference('simplify', [status(thm)], ['110'])).
% 0.68/0.87  thf('112', plain,
% 0.68/0.87      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.68/0.87         ((v2_struct_0 @ sk_D_1)
% 0.68/0.87          | ~ (v2_pre_topc @ sk_D_1)
% 0.68/0.87          | ~ (l1_pre_topc @ sk_D_1)
% 0.68/0.87          | (v2_struct_0 @ X0)
% 0.68/0.87          | ~ (m1_pre_topc @ X0 @ sk_D_1)
% 0.68/0.87          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_D_1))
% 0.68/0.87          | ~ (r1_tarski @ X2 @ (u1_struct_0 @ X0))
% 0.68/0.87          | ~ (m1_connsp_2 @ X2 @ sk_D_1 @ X1)
% 0.68/0.87          | ~ (r1_tmap_1 @ X0 @ sk_A @ 
% 0.68/0.87               (k2_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ X0) @ X1)
% 0.68/0.87          | (r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ X1)
% 0.68/0.87          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.68/0.87          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D_1)))
% 0.68/0.87          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D_1) @ 
% 0.68/0.87               (u1_struct_0 @ sk_A))
% 0.68/0.87          | ~ (v1_funct_1 @ sk_E)
% 0.68/0.87          | ~ (l1_pre_topc @ sk_A)
% 0.68/0.87          | ~ (v2_pre_topc @ sk_A)
% 0.68/0.87          | (v2_struct_0 @ sk_A))),
% 0.68/0.87      inference('sup-', [status(thm)], ['109', '111'])).
% 0.68/0.87  thf('113', plain, ((v2_pre_topc @ sk_D_1)),
% 0.68/0.87      inference('demod', [status(thm)], ['38', '39', '40'])).
% 0.68/0.87  thf('114', plain, ((l1_pre_topc @ sk_D_1)),
% 0.68/0.87      inference('demod', [status(thm)], ['11', '12'])).
% 0.68/0.87  thf('115', plain,
% 0.68/0.87      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D_1) @ (u1_struct_0 @ sk_A))),
% 0.68/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.87  thf('116', plain, ((v1_funct_1 @ sk_E)),
% 0.68/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.87  thf('117', plain, ((l1_pre_topc @ sk_A)),
% 0.68/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.87  thf('118', plain, ((v2_pre_topc @ sk_A)),
% 0.68/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.87  thf('119', plain,
% 0.68/0.87      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.68/0.87         ((v2_struct_0 @ sk_D_1)
% 0.68/0.87          | (v2_struct_0 @ X0)
% 0.68/0.87          | ~ (m1_pre_topc @ X0 @ sk_D_1)
% 0.68/0.87          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_D_1))
% 0.68/0.87          | ~ (r1_tarski @ X2 @ (u1_struct_0 @ X0))
% 0.68/0.87          | ~ (m1_connsp_2 @ X2 @ sk_D_1 @ X1)
% 0.68/0.87          | ~ (r1_tmap_1 @ X0 @ sk_A @ 
% 0.68/0.87               (k2_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ X0) @ X1)
% 0.68/0.87          | (r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ X1)
% 0.68/0.87          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.68/0.87          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D_1)))
% 0.68/0.87          | (v2_struct_0 @ sk_A))),
% 0.68/0.87      inference('demod', [status(thm)],
% 0.68/0.87                ['112', '113', '114', '115', '116', '117', '118'])).
% 0.68/0.87  thf('120', plain,
% 0.68/0.87      (![X0 : $i]:
% 0.68/0.87         ((v2_struct_0 @ sk_A)
% 0.68/0.87          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D_1)))
% 0.68/0.87          | ~ (m1_subset_1 @ sk_H @ (u1_struct_0 @ sk_C))
% 0.68/0.87          | (r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_H)
% 0.68/0.87          | ~ (m1_connsp_2 @ X0 @ sk_D_1 @ sk_H)
% 0.68/0.87          | ~ (r1_tarski @ X0 @ (u1_struct_0 @ sk_C))
% 0.68/0.87          | ~ (m1_subset_1 @ sk_H @ (u1_struct_0 @ sk_D_1))
% 0.68/0.87          | ~ (m1_pre_topc @ sk_C @ sk_D_1)
% 0.68/0.87          | (v2_struct_0 @ sk_C)
% 0.68/0.87          | (v2_struct_0 @ sk_D_1))),
% 0.68/0.87      inference('sup-', [status(thm)], ['108', '119'])).
% 0.68/0.87  thf('121', plain, ((m1_subset_1 @ sk_H @ (u1_struct_0 @ sk_C))),
% 0.68/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.87  thf('122', plain, ((m1_subset_1 @ sk_H @ (u1_struct_0 @ sk_D_1))),
% 0.68/0.87      inference('demod', [status(thm)], ['89', '90'])).
% 0.68/0.87  thf('123', plain, ((m1_pre_topc @ sk_C @ sk_D_1)),
% 0.68/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.87  thf('124', plain,
% 0.68/0.87      (![X0 : $i]:
% 0.68/0.87         ((v2_struct_0 @ sk_A)
% 0.68/0.87          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D_1)))
% 0.68/0.87          | (r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_H)
% 0.68/0.87          | ~ (m1_connsp_2 @ X0 @ sk_D_1 @ sk_H)
% 0.68/0.87          | ~ (r1_tarski @ X0 @ (u1_struct_0 @ sk_C))
% 0.68/0.87          | (v2_struct_0 @ sk_C)
% 0.68/0.87          | (v2_struct_0 @ sk_D_1))),
% 0.68/0.87      inference('demod', [status(thm)], ['120', '121', '122', '123'])).
% 0.68/0.87  thf('125', plain,
% 0.68/0.87      (((v2_struct_0 @ sk_D_1)
% 0.68/0.87        | (v2_struct_0 @ sk_C)
% 0.68/0.87        | ~ (r1_tarski @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_C))
% 0.68/0.87        | ~ (m1_connsp_2 @ (u1_struct_0 @ sk_C) @ sk_D_1 @ sk_H)
% 0.68/0.87        | (r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_H)
% 0.68/0.87        | (v2_struct_0 @ sk_A))),
% 0.68/0.87      inference('sup-', [status(thm)], ['14', '124'])).
% 0.68/0.87  thf('126', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.68/0.87      inference('simplify', [status(thm)], ['2'])).
% 0.68/0.87  thf('127', plain, ((m1_subset_1 @ sk_H @ (u1_struct_0 @ sk_D_1))),
% 0.68/0.87      inference('demod', [status(thm)], ['89', '90'])).
% 0.68/0.87  thf('128', plain,
% 0.68/0.87      ((m1_subset_1 @ (u1_struct_0 @ sk_C) @ 
% 0.68/0.87        (k1_zfmisc_1 @ (u1_struct_0 @ sk_D_1)))),
% 0.68/0.87      inference('demod', [status(thm)], ['8', '13'])).
% 0.68/0.87  thf('129', plain, ((m1_pre_topc @ sk_C @ sk_D_1)),
% 0.68/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.87  thf('130', plain, ((r1_tarski @ sk_F @ (u1_struct_0 @ sk_C))),
% 0.68/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.87  thf('131', plain,
% 0.68/0.87      (![X3 : $i, X5 : $i]:
% 0.68/0.87         ((m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X5)) | ~ (r1_tarski @ X3 @ X5))),
% 0.68/0.87      inference('cnf', [status(esa)], [t3_subset])).
% 0.68/0.87  thf('132', plain,
% 0.68/0.87      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_C)))),
% 0.68/0.87      inference('sup-', [status(thm)], ['130', '131'])).
% 0.68/0.87  thf('133', plain,
% 0.68/0.87      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.68/0.87         (~ (m1_pre_topc @ X13 @ X14)
% 0.68/0.87          | (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.68/0.87          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.68/0.87          | ~ (l1_pre_topc @ X14))),
% 0.68/0.87      inference('cnf', [status(esa)], [t39_pre_topc])).
% 0.68/0.87  thf('134', plain,
% 0.68/0.87      (![X0 : $i]:
% 0.68/0.87         (~ (l1_pre_topc @ X0)
% 0.68/0.87          | (m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.68/0.87          | ~ (m1_pre_topc @ sk_C @ X0))),
% 0.68/0.87      inference('sup-', [status(thm)], ['132', '133'])).
% 0.68/0.87  thf('135', plain,
% 0.68/0.87      (((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D_1)))
% 0.68/0.87        | ~ (l1_pre_topc @ sk_D_1))),
% 0.68/0.87      inference('sup-', [status(thm)], ['129', '134'])).
% 0.68/0.87  thf('136', plain, ((l1_pre_topc @ sk_D_1)),
% 0.68/0.87      inference('demod', [status(thm)], ['11', '12'])).
% 0.68/0.87  thf('137', plain,
% 0.68/0.87      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D_1)))),
% 0.68/0.87      inference('demod', [status(thm)], ['135', '136'])).
% 0.68/0.87  thf(t8_connsp_2, axiom,
% 0.68/0.87    (![A:$i]:
% 0.68/0.87     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.68/0.87       ( ![B:$i]:
% 0.68/0.87         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.68/0.87           ( ![C:$i]:
% 0.68/0.87             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.68/0.87               ( ( m1_connsp_2 @ C @ A @ B ) <=>
% 0.68/0.87                 ( ?[D:$i]:
% 0.68/0.87                   ( ( r2_hidden @ B @ D ) & ( r1_tarski @ D @ C ) & 
% 0.68/0.87                     ( v3_pre_topc @ D @ A ) & 
% 0.68/0.87                     ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ) ) ) ))).
% 0.68/0.87  thf('138', plain,
% 0.68/0.87      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 0.68/0.87         (~ (m1_subset_1 @ X26 @ (u1_struct_0 @ X27))
% 0.68/0.87          | ~ (r2_hidden @ X26 @ X29)
% 0.68/0.87          | ~ (r1_tarski @ X29 @ X28)
% 0.68/0.87          | ~ (v3_pre_topc @ X29 @ X27)
% 0.68/0.87          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 0.68/0.87          | (m1_connsp_2 @ X28 @ X27 @ X26)
% 0.68/0.87          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 0.68/0.87          | ~ (l1_pre_topc @ X27)
% 0.68/0.87          | ~ (v2_pre_topc @ X27)
% 0.68/0.87          | (v2_struct_0 @ X27))),
% 0.68/0.87      inference('cnf', [status(esa)], [t8_connsp_2])).
% 0.68/0.87  thf('139', plain,
% 0.68/0.87      (![X0 : $i, X1 : $i]:
% 0.68/0.87         ((v2_struct_0 @ sk_D_1)
% 0.68/0.87          | ~ (v2_pre_topc @ sk_D_1)
% 0.68/0.87          | ~ (l1_pre_topc @ sk_D_1)
% 0.68/0.87          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D_1)))
% 0.68/0.87          | (m1_connsp_2 @ X0 @ sk_D_1 @ X1)
% 0.68/0.87          | ~ (v3_pre_topc @ sk_F @ sk_D_1)
% 0.68/0.87          | ~ (r1_tarski @ sk_F @ X0)
% 0.68/0.87          | ~ (r2_hidden @ X1 @ sk_F)
% 0.68/0.87          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_D_1)))),
% 0.68/0.87      inference('sup-', [status(thm)], ['137', '138'])).
% 0.68/0.87  thf('140', plain, ((v2_pre_topc @ sk_D_1)),
% 0.68/0.87      inference('demod', [status(thm)], ['38', '39', '40'])).
% 0.68/0.87  thf('141', plain, ((l1_pre_topc @ sk_D_1)),
% 0.68/0.87      inference('demod', [status(thm)], ['11', '12'])).
% 0.68/0.87  thf('142', plain,
% 0.68/0.87      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.68/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.87  thf('143', plain,
% 0.68/0.87      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D_1)))),
% 0.68/0.87      inference('demod', [status(thm)], ['135', '136'])).
% 0.68/0.87  thf(t33_tops_2, axiom,
% 0.68/0.87    (![A:$i]:
% 0.68/0.87     ( ( l1_pre_topc @ A ) =>
% 0.68/0.87       ( ![B:$i]:
% 0.68/0.87         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.68/0.87           ( ![C:$i]:
% 0.68/0.87             ( ( m1_pre_topc @ C @ A ) =>
% 0.68/0.87               ( ( v3_pre_topc @ B @ A ) =>
% 0.68/0.87                 ( ![D:$i]:
% 0.68/0.87                   ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ C ) ) ) =>
% 0.68/0.87                     ( ( ( D ) = ( B ) ) => ( v3_pre_topc @ D @ C ) ) ) ) ) ) ) ) ) ))).
% 0.68/0.87  thf('144', plain,
% 0.68/0.87      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 0.68/0.87         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.68/0.87          | ~ (v3_pre_topc @ X19 @ X20)
% 0.68/0.87          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 0.68/0.87          | (v3_pre_topc @ X21 @ X22)
% 0.68/0.87          | ((X21) != (X19))
% 0.68/0.87          | ~ (m1_pre_topc @ X22 @ X20)
% 0.68/0.87          | ~ (l1_pre_topc @ X20))),
% 0.68/0.87      inference('cnf', [status(esa)], [t33_tops_2])).
% 0.68/0.87  thf('145', plain,
% 0.68/0.87      (![X19 : $i, X20 : $i, X22 : $i]:
% 0.68/0.87         (~ (l1_pre_topc @ X20)
% 0.68/0.87          | ~ (m1_pre_topc @ X22 @ X20)
% 0.68/0.87          | (v3_pre_topc @ X19 @ X22)
% 0.68/0.87          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 0.68/0.87          | ~ (v3_pre_topc @ X19 @ X20)
% 0.68/0.87          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20))))),
% 0.68/0.87      inference('simplify', [status(thm)], ['144'])).
% 0.68/0.87  thf('146', plain,
% 0.68/0.87      (![X0 : $i]:
% 0.68/0.87         (~ (m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.68/0.87          | ~ (v3_pre_topc @ sk_F @ X0)
% 0.68/0.87          | (v3_pre_topc @ sk_F @ sk_D_1)
% 0.68/0.87          | ~ (m1_pre_topc @ sk_D_1 @ X0)
% 0.68/0.87          | ~ (l1_pre_topc @ X0))),
% 0.68/0.87      inference('sup-', [status(thm)], ['143', '145'])).
% 0.68/0.87  thf('147', plain,
% 0.68/0.87      ((~ (l1_pre_topc @ sk_B)
% 0.68/0.87        | ~ (m1_pre_topc @ sk_D_1 @ sk_B)
% 0.68/0.87        | (v3_pre_topc @ sk_F @ sk_D_1)
% 0.68/0.87        | ~ (v3_pre_topc @ sk_F @ sk_B))),
% 0.68/0.87      inference('sup-', [status(thm)], ['142', '146'])).
% 0.68/0.87  thf('148', plain, ((l1_pre_topc @ sk_B)),
% 0.68/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.87  thf('149', plain, ((m1_pre_topc @ sk_D_1 @ sk_B)),
% 0.68/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.87  thf('150', plain, ((v3_pre_topc @ sk_F @ sk_B)),
% 0.68/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.87  thf('151', plain, ((v3_pre_topc @ sk_F @ sk_D_1)),
% 0.68/0.87      inference('demod', [status(thm)], ['147', '148', '149', '150'])).
% 0.68/0.87  thf('152', plain,
% 0.68/0.87      (![X0 : $i, X1 : $i]:
% 0.68/0.87         ((v2_struct_0 @ sk_D_1)
% 0.68/0.87          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D_1)))
% 0.68/0.87          | (m1_connsp_2 @ X0 @ sk_D_1 @ X1)
% 0.68/0.87          | ~ (r1_tarski @ sk_F @ X0)
% 0.68/0.87          | ~ (r2_hidden @ X1 @ sk_F)
% 0.68/0.87          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_D_1)))),
% 0.68/0.87      inference('demod', [status(thm)], ['139', '140', '141', '151'])).
% 0.68/0.87  thf('153', plain,
% 0.68/0.87      (![X0 : $i]:
% 0.68/0.87         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_D_1))
% 0.68/0.87          | ~ (r2_hidden @ X0 @ sk_F)
% 0.68/0.87          | ~ (r1_tarski @ sk_F @ (u1_struct_0 @ sk_C))
% 0.68/0.87          | (m1_connsp_2 @ (u1_struct_0 @ sk_C) @ sk_D_1 @ X0)
% 0.68/0.87          | (v2_struct_0 @ sk_D_1))),
% 0.68/0.87      inference('sup-', [status(thm)], ['128', '152'])).
% 0.68/0.87  thf('154', plain, ((r1_tarski @ sk_F @ (u1_struct_0 @ sk_C))),
% 0.68/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.87  thf('155', plain,
% 0.68/0.87      (![X0 : $i]:
% 0.68/0.87         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_D_1))
% 0.68/0.87          | ~ (r2_hidden @ X0 @ sk_F)
% 0.68/0.87          | (m1_connsp_2 @ (u1_struct_0 @ sk_C) @ sk_D_1 @ X0)
% 0.68/0.87          | (v2_struct_0 @ sk_D_1))),
% 0.68/0.87      inference('demod', [status(thm)], ['153', '154'])).
% 0.68/0.87  thf('156', plain,
% 0.68/0.87      (((v2_struct_0 @ sk_D_1)
% 0.68/0.87        | (m1_connsp_2 @ (u1_struct_0 @ sk_C) @ sk_D_1 @ sk_H)
% 0.68/0.87        | ~ (r2_hidden @ sk_H @ sk_F))),
% 0.68/0.87      inference('sup-', [status(thm)], ['127', '155'])).
% 0.68/0.87  thf('157', plain, ((r2_hidden @ sk_G @ sk_F)),
% 0.68/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.87  thf('158', plain, (((sk_G) = (sk_H))),
% 0.68/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.87  thf('159', plain, ((r2_hidden @ sk_H @ sk_F)),
% 0.68/0.87      inference('demod', [status(thm)], ['157', '158'])).
% 0.68/0.87  thf('160', plain,
% 0.68/0.87      (((v2_struct_0 @ sk_D_1)
% 0.68/0.87        | (m1_connsp_2 @ (u1_struct_0 @ sk_C) @ sk_D_1 @ sk_H))),
% 0.68/0.87      inference('demod', [status(thm)], ['156', '159'])).
% 0.68/0.87  thf('161', plain, (~ (v2_struct_0 @ sk_D_1)),
% 0.68/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.87  thf('162', plain, ((m1_connsp_2 @ (u1_struct_0 @ sk_C) @ sk_D_1 @ sk_H)),
% 0.68/0.87      inference('clc', [status(thm)], ['160', '161'])).
% 0.68/0.87  thf('163', plain,
% 0.68/0.87      (((v2_struct_0 @ sk_D_1)
% 0.68/0.87        | (v2_struct_0 @ sk_C)
% 0.68/0.87        | (r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_H)
% 0.68/0.87        | (v2_struct_0 @ sk_A))),
% 0.68/0.87      inference('demod', [status(thm)], ['125', '126', '162'])).
% 0.68/0.87  thf('164', plain,
% 0.68/0.87      ((~ (r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_H))
% 0.68/0.87         <= (~ ((r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_G)))),
% 0.68/0.87      inference('demod', [status(thm)], ['69', '70'])).
% 0.68/0.87  thf('165', plain,
% 0.68/0.87      (((r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_H))
% 0.68/0.87         <= (((r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_G)))),
% 0.68/0.87      inference('demod', [status(thm)], ['74', '75'])).
% 0.68/0.87  thf('166', plain,
% 0.68/0.87      ((~ (r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_H))
% 0.68/0.87         <= (~ ((r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_H)))),
% 0.68/0.87      inference('split', [status(esa)], ['62'])).
% 0.68/0.87  thf('167', plain,
% 0.68/0.87      (~ ((r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_G)) | 
% 0.68/0.87       ((r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_H))),
% 0.68/0.87      inference('sup-', [status(thm)], ['165', '166'])).
% 0.68/0.87  thf('168', plain, (~ ((r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_G))),
% 0.68/0.87      inference('sat_resolution*', [status(thm)], ['63', '72', '105', '167'])).
% 0.68/0.87  thf('169', plain, (~ (r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_H)),
% 0.68/0.87      inference('simpl_trail', [status(thm)], ['164', '168'])).
% 0.68/0.87  thf('170', plain,
% 0.68/0.87      (((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_D_1))),
% 0.68/0.87      inference('sup-', [status(thm)], ['163', '169'])).
% 0.68/0.87  thf('171', plain, (~ (v2_struct_0 @ sk_A)),
% 0.68/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.87  thf('172', plain, (((v2_struct_0 @ sk_D_1) | (v2_struct_0 @ sk_C))),
% 0.68/0.87      inference('clc', [status(thm)], ['170', '171'])).
% 0.68/0.87  thf('173', plain, (~ (v2_struct_0 @ sk_D_1)),
% 0.68/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.87  thf('174', plain, ((v2_struct_0 @ sk_C)),
% 0.68/0.87      inference('clc', [status(thm)], ['172', '173'])).
% 0.68/0.87  thf('175', plain, ($false), inference('demod', [status(thm)], ['0', '174'])).
% 0.68/0.87  
% 0.68/0.87  % SZS output end Refutation
% 0.68/0.87  
% 0.68/0.87  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
