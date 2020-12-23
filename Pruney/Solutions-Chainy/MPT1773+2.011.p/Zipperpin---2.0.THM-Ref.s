%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ZuIAsymDj5

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:10:16 EST 2020

% Result     : Theorem 0.39s
% Output     : Refutation 0.39s
% Verified   : 
% Statistics : Number of formulae       :  167 ( 420 expanded)
%              Number of leaves         :   33 ( 129 expanded)
%              Depth                    :   26
%              Number of atoms          : 2081 (17831 expanded)
%              Number of equality atoms :   12 ( 201 expanded)
%              Maximal formula depth    :   32 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_connsp_2_type,type,(
    m1_connsp_2: $i > $i > $i > $o )).

thf(sk_H_type,type,(
    sk_H: $i )).

thf(k3_tmap_1_type,type,(
    k3_tmap_1: $i > $i > $i > $i > $i > $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_G_type,type,(
    sk_G: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(r1_tmap_1_type,type,(
    r1_tmap_1: $i > $i > $i > $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(t84_tmap_1,conjecture,(
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
                                        <=> ( r1_tmap_1 @ C @ B @ ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ H ) ) ) ) ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t84_tmap_1])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( m1_pre_topc @ A @ A ) ) )).

thf('1',plain,(
    ! [X13: $i] :
      ( ( m1_pre_topc @ X13 @ X13 )
      | ~ ( l1_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf(t1_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( m1_subset_1 @ ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('2',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_pre_topc @ X11 @ X12 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X11 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ~ ( l1_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('6',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( r1_tarski @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    m1_pre_topc @ sk_C @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_pre_topc @ X11 @ X12 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X11 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ~ ( l1_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('9',plain,
    ( ~ ( l1_pre_topc @ sk_D_1 )
    | ( m1_subset_1 @ ( u1_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D_1 ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    m1_pre_topc @ sk_D_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('11',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( m1_pre_topc @ X5 @ X6 )
      | ( l1_pre_topc @ X5 )
      | ~ ( l1_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('12',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    l1_pre_topc @ sk_D_1 ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['9','14'])).

thf('16',plain,
    ( ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C @ sk_E ) @ sk_H )
    | ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_G ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C @ sk_E ) @ sk_H )
   <= ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C @ sk_E ) @ sk_H ) ),
    inference(split,[status(esa)],['16'])).

thf('18',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D_1 ) @ ( u1_struct_0 @ sk_B ) ) ) ),
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

thf('19',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i,X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ( v2_struct_0 @ X24 )
      | ~ ( v2_pre_topc @ X24 )
      | ~ ( l1_pre_topc @ X24 )
      | ( v2_struct_0 @ X25 )
      | ~ ( m1_pre_topc @ X25 @ X26 )
      | ~ ( m1_pre_topc @ X27 @ X25 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) )
      | ~ ( m1_subset_1 @ X29 @ ( u1_struct_0 @ X27 ) )
      | ~ ( r1_tmap_1 @ X27 @ X24 @ ( k3_tmap_1 @ X26 @ X24 @ X25 @ X27 @ X30 ) @ X29 )
      | ( r1_tmap_1 @ X25 @ X24 @ X30 @ X31 )
      | ( X31 != X29 )
      | ~ ( m1_connsp_2 @ X28 @ X25 @ X31 )
      | ~ ( r1_tarski @ X28 @ ( u1_struct_0 @ X27 ) )
      | ~ ( m1_subset_1 @ X31 @ ( u1_struct_0 @ X25 ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X25 ) @ ( u1_struct_0 @ X24 ) ) ) )
      | ~ ( v1_funct_2 @ X30 @ ( u1_struct_0 @ X25 ) @ ( u1_struct_0 @ X24 ) )
      | ~ ( v1_funct_1 @ X30 )
      | ~ ( m1_pre_topc @ X27 @ X26 )
      | ( v2_struct_0 @ X27 )
      | ~ ( l1_pre_topc @ X26 )
      | ~ ( v2_pre_topc @ X26 )
      | ( v2_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t83_tmap_1])).

thf('20',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ( v2_struct_0 @ X26 )
      | ~ ( v2_pre_topc @ X26 )
      | ~ ( l1_pre_topc @ X26 )
      | ( v2_struct_0 @ X27 )
      | ~ ( m1_pre_topc @ X27 @ X26 )
      | ~ ( v1_funct_1 @ X30 )
      | ~ ( v1_funct_2 @ X30 @ ( u1_struct_0 @ X25 ) @ ( u1_struct_0 @ X24 ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X25 ) @ ( u1_struct_0 @ X24 ) ) ) )
      | ~ ( m1_subset_1 @ X29 @ ( u1_struct_0 @ X25 ) )
      | ~ ( r1_tarski @ X28 @ ( u1_struct_0 @ X27 ) )
      | ~ ( m1_connsp_2 @ X28 @ X25 @ X29 )
      | ( r1_tmap_1 @ X25 @ X24 @ X30 @ X29 )
      | ~ ( r1_tmap_1 @ X27 @ X24 @ ( k3_tmap_1 @ X26 @ X24 @ X25 @ X27 @ X30 ) @ X29 )
      | ~ ( m1_subset_1 @ X29 @ ( u1_struct_0 @ X27 ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) )
      | ~ ( m1_pre_topc @ X27 @ X25 )
      | ~ ( m1_pre_topc @ X25 @ X26 )
      | ( v2_struct_0 @ X25 )
      | ~ ( l1_pre_topc @ X24 )
      | ~ ( v2_pre_topc @ X24 )
      | ( v2_struct_0 @ X24 ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ( v2_struct_0 @ sk_D_1 )
      | ~ ( m1_pre_topc @ sk_D_1 @ X0 )
      | ~ ( m1_pre_topc @ X1 @ sk_D_1 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D_1 ) ) )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X1 ) )
      | ~ ( r1_tmap_1 @ X1 @ sk_B @ ( k3_tmap_1 @ X0 @ sk_B @ sk_D_1 @ X1 @ sk_E ) @ X3 )
      | ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ X3 )
      | ~ ( m1_connsp_2 @ X2 @ sk_D_1 @ X3 )
      | ~ ( r1_tarski @ X2 @ ( u1_struct_0 @ X1 ) )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ sk_D_1 ) )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D_1 ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ( v2_struct_0 @ X1 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','20'])).

thf('22',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D_1 ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D_1 )
      | ~ ( m1_pre_topc @ sk_D_1 @ X0 )
      | ~ ( m1_pre_topc @ X1 @ sk_D_1 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D_1 ) ) )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X1 ) )
      | ~ ( r1_tmap_1 @ X1 @ sk_B @ ( k3_tmap_1 @ X0 @ sk_B @ sk_D_1 @ X1 @ sk_E ) @ X3 )
      | ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ X3 )
      | ~ ( m1_connsp_2 @ X2 @ sk_D_1 @ X3 )
      | ~ ( r1_tarski @ X2 @ ( u1_struct_0 @ X1 ) )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ sk_D_1 ) )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ( v2_struct_0 @ X1 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['21','22','23','24','25'])).

thf('27',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ~ ( v2_pre_topc @ sk_A )
        | ~ ( l1_pre_topc @ sk_A )
        | ( v2_struct_0 @ sk_C )
        | ~ ( m1_pre_topc @ sk_C @ sk_A )
        | ~ ( m1_subset_1 @ sk_H @ ( u1_struct_0 @ sk_D_1 ) )
        | ~ ( r1_tarski @ X0 @ ( u1_struct_0 @ sk_C ) )
        | ~ ( m1_connsp_2 @ X0 @ sk_D_1 @ sk_H )
        | ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_H )
        | ~ ( m1_subset_1 @ sk_H @ ( u1_struct_0 @ sk_C ) )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D_1 ) ) )
        | ~ ( m1_pre_topc @ sk_C @ sk_D_1 )
        | ~ ( m1_pre_topc @ sk_D_1 @ sk_A )
        | ( v2_struct_0 @ sk_D_1 )
        | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C @ sk_E ) @ sk_H ) ),
    inference('sup-',[status(thm)],['17','26'])).

thf('28',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    sk_G = sk_H ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    m1_subset_1 @ sk_H @ ( u1_struct_0 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,(
    m1_subset_1 @ sk_H @ ( u1_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    m1_pre_topc @ sk_C @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    m1_pre_topc @ sk_D_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ sk_C )
        | ~ ( r1_tarski @ X0 @ ( u1_struct_0 @ sk_C ) )
        | ~ ( m1_connsp_2 @ X0 @ sk_D_1 @ sk_H )
        | ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_H )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D_1 ) ) )
        | ( v2_struct_0 @ sk_D_1 )
        | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C @ sk_E ) @ sk_H ) ),
    inference(demod,[status(thm)],['27','28','29','30','33','34','35','36'])).

thf('38',plain,
    ( ~ ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C @ sk_E ) @ sk_H )
    | ~ ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_G ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    sk_G = sk_H ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,
    ( ~ ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C @ sk_E ) @ sk_H )
    | ~ ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_H ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,
    ( ~ ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_H )
    | ~ ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C @ sk_E ) @ sk_H ) ),
    inference(split,[status(esa)],['40'])).

thf('42',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    m1_subset_1 @ sk_H @ ( u1_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,
    ( ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C @ sk_E ) @ sk_H )
    | ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_G ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    sk_G = sk_H ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C @ sk_E ) @ sk_H )
    | ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_H ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,
    ( ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_H )
   <= ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_H ) ),
    inference(split,[status(esa)],['46'])).

thf('48',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D_1 ) @ ( u1_struct_0 @ sk_B ) ) ) ),
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

thf('49',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ( v2_struct_0 @ X17 )
      | ~ ( v2_pre_topc @ X17 )
      | ~ ( l1_pre_topc @ X17 )
      | ( v2_struct_0 @ X18 )
      | ~ ( m1_pre_topc @ X18 @ X19 )
      | ~ ( m1_subset_1 @ X20 @ ( u1_struct_0 @ X21 ) )
      | ~ ( m1_pre_topc @ X18 @ X21 )
      | ~ ( r1_tmap_1 @ X21 @ X17 @ X22 @ X20 )
      | ( X20 != X23 )
      | ( r1_tmap_1 @ X18 @ X17 @ ( k3_tmap_1 @ X19 @ X17 @ X21 @ X18 @ X22 ) @ X23 )
      | ~ ( m1_subset_1 @ X23 @ ( u1_struct_0 @ X18 ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X21 ) @ ( u1_struct_0 @ X17 ) ) ) )
      | ~ ( v1_funct_2 @ X22 @ ( u1_struct_0 @ X21 ) @ ( u1_struct_0 @ X17 ) )
      | ~ ( v1_funct_1 @ X22 )
      | ~ ( m1_pre_topc @ X21 @ X19 )
      | ( v2_struct_0 @ X21 )
      | ~ ( l1_pre_topc @ X19 )
      | ~ ( v2_pre_topc @ X19 )
      | ( v2_struct_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t81_tmap_1])).

thf('50',plain,(
    ! [X17: $i,X18: $i,X19: $i,X21: $i,X22: $i,X23: $i] :
      ( ( v2_struct_0 @ X19 )
      | ~ ( v2_pre_topc @ X19 )
      | ~ ( l1_pre_topc @ X19 )
      | ( v2_struct_0 @ X21 )
      | ~ ( m1_pre_topc @ X21 @ X19 )
      | ~ ( v1_funct_1 @ X22 )
      | ~ ( v1_funct_2 @ X22 @ ( u1_struct_0 @ X21 ) @ ( u1_struct_0 @ X17 ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X21 ) @ ( u1_struct_0 @ X17 ) ) ) )
      | ~ ( m1_subset_1 @ X23 @ ( u1_struct_0 @ X18 ) )
      | ( r1_tmap_1 @ X18 @ X17 @ ( k3_tmap_1 @ X19 @ X17 @ X21 @ X18 @ X22 ) @ X23 )
      | ~ ( r1_tmap_1 @ X21 @ X17 @ X22 @ X23 )
      | ~ ( m1_pre_topc @ X18 @ X21 )
      | ~ ( m1_subset_1 @ X23 @ ( u1_struct_0 @ X21 ) )
      | ~ ( m1_pre_topc @ X18 @ X19 )
      | ( v2_struct_0 @ X18 )
      | ~ ( l1_pre_topc @ X17 )
      | ~ ( v2_pre_topc @ X17 )
      | ( v2_struct_0 @ X17 ) ) ),
    inference(simplify,[status(thm)],['49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X1 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ sk_D_1 ) )
      | ~ ( m1_pre_topc @ X0 @ sk_D_1 )
      | ~ ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ X2 )
      | ( r1_tmap_1 @ X0 @ sk_B @ ( k3_tmap_1 @ X1 @ sk_B @ sk_D_1 @ X0 @ sk_E ) @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D_1 ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( m1_pre_topc @ sk_D_1 @ X1 )
      | ( v2_struct_0 @ sk_D_1 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['48','50'])).

thf('52',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D_1 ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X1 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ sk_D_1 ) )
      | ~ ( m1_pre_topc @ X0 @ sk_D_1 )
      | ~ ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ X2 )
      | ( r1_tmap_1 @ X0 @ sk_B @ ( k3_tmap_1 @ X1 @ sk_B @ sk_D_1 @ X0 @ sk_E ) @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ sk_D_1 @ X1 )
      | ( v2_struct_0 @ sk_D_1 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(demod,[status(thm)],['51','52','53','54','55'])).

thf('57',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( v2_struct_0 @ X0 )
        | ~ ( v2_pre_topc @ X0 )
        | ~ ( l1_pre_topc @ X0 )
        | ( v2_struct_0 @ sk_D_1 )
        | ~ ( m1_pre_topc @ sk_D_1 @ X0 )
        | ~ ( m1_subset_1 @ sk_H @ ( u1_struct_0 @ X1 ) )
        | ( r1_tmap_1 @ X1 @ sk_B @ ( k3_tmap_1 @ X0 @ sk_B @ sk_D_1 @ X1 @ sk_E ) @ sk_H )
        | ~ ( m1_pre_topc @ X1 @ sk_D_1 )
        | ~ ( m1_subset_1 @ sk_H @ ( u1_struct_0 @ sk_D_1 ) )
        | ~ ( m1_pre_topc @ X1 @ X0 )
        | ( v2_struct_0 @ X1 )
        | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_H ) ),
    inference('sup-',[status(thm)],['47','56'])).

thf('58',plain,(
    m1_subset_1 @ sk_H @ ( u1_struct_0 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('59',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( v2_struct_0 @ X0 )
        | ~ ( v2_pre_topc @ X0 )
        | ~ ( l1_pre_topc @ X0 )
        | ( v2_struct_0 @ sk_D_1 )
        | ~ ( m1_pre_topc @ sk_D_1 @ X0 )
        | ~ ( m1_subset_1 @ sk_H @ ( u1_struct_0 @ X1 ) )
        | ( r1_tmap_1 @ X1 @ sk_B @ ( k3_tmap_1 @ X0 @ sk_B @ sk_D_1 @ X1 @ sk_E ) @ sk_H )
        | ~ ( m1_pre_topc @ X1 @ sk_D_1 )
        | ~ ( m1_pre_topc @ X1 @ X0 )
        | ( v2_struct_0 @ X1 )
        | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_H ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_B )
        | ( v2_struct_0 @ sk_C )
        | ~ ( m1_pre_topc @ sk_C @ X0 )
        | ~ ( m1_pre_topc @ sk_C @ sk_D_1 )
        | ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ X0 @ sk_B @ sk_D_1 @ sk_C @ sk_E ) @ sk_H )
        | ~ ( m1_pre_topc @ sk_D_1 @ X0 )
        | ( v2_struct_0 @ sk_D_1 )
        | ~ ( l1_pre_topc @ X0 )
        | ~ ( v2_pre_topc @ X0 )
        | ( v2_struct_0 @ X0 ) )
   <= ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_H ) ),
    inference('sup-',[status(thm)],['43','59'])).

thf('61',plain,(
    m1_pre_topc @ sk_C @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_B )
        | ( v2_struct_0 @ sk_C )
        | ~ ( m1_pre_topc @ sk_C @ X0 )
        | ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ X0 @ sk_B @ sk_D_1 @ sk_C @ sk_E ) @ sk_H )
        | ~ ( m1_pre_topc @ sk_D_1 @ X0 )
        | ( v2_struct_0 @ sk_D_1 )
        | ~ ( l1_pre_topc @ X0 )
        | ~ ( v2_pre_topc @ X0 )
        | ( v2_struct_0 @ X0 ) )
   <= ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_H ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_D_1 )
      | ~ ( m1_pre_topc @ sk_D_1 @ sk_A )
      | ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C @ sk_E ) @ sk_H )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_H ) ),
    inference('sup-',[status(thm)],['42','62'])).

thf('64',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    m1_pre_topc @ sk_D_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D_1 )
      | ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C @ sk_E ) @ sk_H )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_H ) ),
    inference(demod,[status(thm)],['63','64','65','66'])).

thf('68',plain,
    ( ~ ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C @ sk_E ) @ sk_H )
    | ~ ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_G ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,
    ( ~ ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C @ sk_E ) @ sk_H )
   <= ~ ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C @ sk_E ) @ sk_H ) ),
    inference(split,[status(esa)],['68'])).

thf('70',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_D_1 )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ~ ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C @ sk_E ) @ sk_H )
      & ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_H ) ) ),
    inference('sup-',[status(thm)],['67','69'])).

thf('71',plain,(
    ~ ( v2_struct_0 @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ~ ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C @ sk_E ) @ sk_H )
      & ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_H ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_C ) )
   <= ( ~ ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C @ sk_E ) @ sk_H )
      & ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_H ) ) ),
    inference(clc,[status(thm)],['72','73'])).

thf('75',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,
    ( ( v2_struct_0 @ sk_C )
   <= ( ~ ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C @ sk_E ) @ sk_H )
      & ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_H ) ) ),
    inference(clc,[status(thm)],['74','75'])).

thf('77',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,
    ( ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C @ sk_E ) @ sk_H )
    | ~ ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_H ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,
    ( ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C @ sk_E ) @ sk_H )
    | ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_H ) ),
    inference(split,[status(esa)],['46'])).

thf('80',plain,(
    r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C @ sk_E ) @ sk_H ),
    inference('sat_resolution*',[status(thm)],['41','78','79'])).

thf('81',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ~ ( r1_tarski @ X0 @ ( u1_struct_0 @ sk_C ) )
      | ~ ( m1_connsp_2 @ X0 @ sk_D_1 @ sk_H )
      | ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_H )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D_1 ) ) )
      | ( v2_struct_0 @ sk_D_1 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(simpl_trail,[status(thm)],['37','80'])).

thf('82',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D_1 )
    | ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_H )
    | ~ ( m1_connsp_2 @ ( u1_struct_0 @ sk_C ) @ sk_D_1 @ sk_H )
    | ~ ( r1_tarski @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_C ) )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['15','81'])).

thf('83',plain,(
    m1_subset_1 @ sk_H @ ( u1_struct_0 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('84',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['9','14'])).

thf('85',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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

thf('86',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( u1_struct_0 @ X8 ) )
      | ~ ( r2_hidden @ X7 @ X10 )
      | ~ ( r1_tarski @ X10 @ X9 )
      | ~ ( v3_pre_topc @ X10 @ X8 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ( m1_connsp_2 @ X9 @ X8 @ X7 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ~ ( l1_pre_topc @ X8 )
      | ~ ( v2_pre_topc @ X8 )
      | ( v2_struct_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t8_connsp_2])).

thf('87',plain,(
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
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,(
    m1_pre_topc @ sk_D_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( v2_pre_topc @ B ) ) ) )).

thf('89',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_pre_topc @ X3 @ X4 )
      | ( v2_pre_topc @ X3 )
      | ~ ( l1_pre_topc @ X4 )
      | ~ ( v2_pre_topc @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc1_pre_topc])).

thf('90',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_pre_topc @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    v2_pre_topc @ sk_D_1 ),
    inference(demod,[status(thm)],['90','91','92'])).

thf('94',plain,(
    l1_pre_topc @ sk_D_1 ),
    inference(demod,[status(thm)],['12','13'])).

thf('95',plain,(
    v3_pre_topc @ sk_F @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_D_1 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D_1 ) ) )
      | ( m1_connsp_2 @ X0 @ sk_D_1 @ X1 )
      | ~ ( r1_tarski @ sk_F @ X0 )
      | ~ ( r2_hidden @ X1 @ sk_F )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_D_1 ) ) ) ),
    inference(demod,[status(thm)],['87','93','94','95'])).

thf('97',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_D_1 ) )
      | ~ ( r2_hidden @ X0 @ sk_F )
      | ~ ( r1_tarski @ sk_F @ ( u1_struct_0 @ sk_C ) )
      | ( m1_connsp_2 @ ( u1_struct_0 @ sk_C ) @ sk_D_1 @ X0 )
      | ( v2_struct_0 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['84','96'])).

thf('98',plain,(
    r1_tarski @ sk_F @ ( u1_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_D_1 ) )
      | ~ ( r2_hidden @ X0 @ sk_F )
      | ( m1_connsp_2 @ ( u1_struct_0 @ sk_C ) @ sk_D_1 @ X0 )
      | ( v2_struct_0 @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['97','98'])).

thf('100',plain,
    ( ( v2_struct_0 @ sk_D_1 )
    | ( m1_connsp_2 @ ( u1_struct_0 @ sk_C ) @ sk_D_1 @ sk_H )
    | ~ ( r2_hidden @ sk_H @ sk_F ) ),
    inference('sup-',[status(thm)],['83','99'])).

thf('101',plain,(
    r2_hidden @ sk_G @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    sk_G = sk_H ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,(
    r2_hidden @ sk_H @ sk_F ),
    inference(demod,[status(thm)],['101','102'])).

thf('104',plain,
    ( ( v2_struct_0 @ sk_D_1 )
    | ( m1_connsp_2 @ ( u1_struct_0 @ sk_C ) @ sk_D_1 @ sk_H ) ),
    inference(demod,[status(thm)],['100','103'])).

thf('105',plain,(
    ~ ( v2_struct_0 @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,(
    m1_connsp_2 @ ( u1_struct_0 @ sk_C ) @ sk_D_1 @ sk_H ),
    inference(clc,[status(thm)],['104','105'])).

thf('107',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D_1 )
    | ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_H )
    | ~ ( r1_tarski @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_C ) )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['82','106'])).

thf('108',plain,
    ( ~ ( l1_pre_topc @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_H )
    | ( v2_struct_0 @ sk_D_1 )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['6','107'])).

thf('109',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( m1_pre_topc @ X5 @ X6 )
      | ( l1_pre_topc @ X5 )
      | ~ ( l1_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('111',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_C ) ),
    inference('sup-',[status(thm)],['109','110'])).

thf('112',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['111','112'])).

thf('114',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_H )
    | ( v2_struct_0 @ sk_D_1 )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['108','113'])).

thf('115',plain,
    ( ~ ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_G )
   <= ~ ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_G ) ),
    inference(split,[status(esa)],['68'])).

thf('116',plain,(
    sk_G = sk_H ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,
    ( ~ ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_H )
   <= ~ ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_G ) ),
    inference(demod,[status(thm)],['115','116'])).

thf('118',plain,
    ( ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_G )
   <= ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_G ) ),
    inference(split,[status(esa)],['16'])).

thf('119',plain,(
    sk_G = sk_H ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,
    ( ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_H )
   <= ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_G ) ),
    inference(demod,[status(thm)],['118','119'])).

thf('121',plain,
    ( ~ ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_H )
   <= ~ ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_H ) ),
    inference(split,[status(esa)],['40'])).

thf('122',plain,
    ( ~ ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_G )
    | ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_H ) ),
    inference('sup-',[status(thm)],['120','121'])).

thf('123',plain,(
    ~ ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_G ) ),
    inference('sat_resolution*',[status(thm)],['41','78','122'])).

thf('124',plain,(
    ~ ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_H ) ),
    inference(simpl_trail,[status(thm)],['117','123'])).

thf('125',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D_1 )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['114','124'])).

thf('126',plain,(
    ~ ( v2_struct_0 @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['125','126'])).

thf('128',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('129',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C ) ),
    inference(clc,[status(thm)],['127','128'])).

thf('130',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('131',plain,(
    v2_struct_0 @ sk_C ),
    inference(clc,[status(thm)],['129','130'])).

thf('132',plain,(
    $false ),
    inference(demod,[status(thm)],['0','131'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ZuIAsymDj5
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 10:35:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.39/0.56  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.39/0.56  % Solved by: fo/fo7.sh
% 0.39/0.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.39/0.56  % done 195 iterations in 0.095s
% 0.39/0.56  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.39/0.56  % SZS output start Refutation
% 0.39/0.56  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.39/0.56  thf(m1_connsp_2_type, type, m1_connsp_2: $i > $i > $i > $o).
% 0.39/0.56  thf(sk_H_type, type, sk_H: $i).
% 0.39/0.56  thf(k3_tmap_1_type, type, k3_tmap_1: $i > $i > $i > $i > $i > $i).
% 0.39/0.56  thf(sk_F_type, type, sk_F: $i).
% 0.39/0.56  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.39/0.56  thf(sk_G_type, type, sk_G: $i).
% 0.39/0.56  thf(sk_B_type, type, sk_B: $i).
% 0.39/0.56  thf(sk_A_type, type, sk_A: $i).
% 0.39/0.56  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.39/0.56  thf(r1_tmap_1_type, type, r1_tmap_1: $i > $i > $i > $i > $o).
% 0.39/0.56  thf(sk_E_type, type, sk_E: $i).
% 0.39/0.56  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.39/0.56  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.39/0.56  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.39/0.56  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.39/0.56  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.39/0.56  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.39/0.56  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.39/0.56  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.39/0.56  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.39/0.56  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.39/0.56  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.39/0.56  thf(sk_C_type, type, sk_C: $i).
% 0.39/0.56  thf(t84_tmap_1, conjecture,
% 0.39/0.56    (![A:$i]:
% 0.39/0.56     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.39/0.56       ( ![B:$i]:
% 0.39/0.56         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.39/0.56             ( l1_pre_topc @ B ) ) =>
% 0.39/0.56           ( ![C:$i]:
% 0.39/0.56             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.39/0.56               ( ![D:$i]:
% 0.39/0.56                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.39/0.56                   ( ![E:$i]:
% 0.39/0.56                     ( ( ( v1_funct_1 @ E ) & 
% 0.39/0.56                         ( v1_funct_2 @
% 0.39/0.56                           E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 0.39/0.56                         ( m1_subset_1 @
% 0.39/0.56                           E @ 
% 0.39/0.56                           ( k1_zfmisc_1 @
% 0.39/0.56                             ( k2_zfmisc_1 @
% 0.39/0.56                               ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.39/0.56                       ( ( m1_pre_topc @ C @ D ) =>
% 0.39/0.56                         ( ![F:$i]:
% 0.39/0.56                           ( ( m1_subset_1 @
% 0.39/0.56                               F @ ( k1_zfmisc_1 @ ( u1_struct_0 @ D ) ) ) =>
% 0.39/0.56                             ( ![G:$i]:
% 0.39/0.56                               ( ( m1_subset_1 @ G @ ( u1_struct_0 @ D ) ) =>
% 0.39/0.56                                 ( ![H:$i]:
% 0.39/0.56                                   ( ( m1_subset_1 @ H @ ( u1_struct_0 @ C ) ) =>
% 0.39/0.56                                     ( ( ( v3_pre_topc @ F @ D ) & 
% 0.39/0.56                                         ( r2_hidden @ G @ F ) & 
% 0.39/0.56                                         ( r1_tarski @ F @ ( u1_struct_0 @ C ) ) & 
% 0.39/0.56                                         ( ( G ) = ( H ) ) ) =>
% 0.39/0.56                                       ( ( r1_tmap_1 @ D @ B @ E @ G ) <=>
% 0.39/0.56                                         ( r1_tmap_1 @
% 0.39/0.56                                           C @ B @ 
% 0.39/0.56                                           ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ 
% 0.39/0.56                                           H ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.39/0.56  thf(zf_stmt_0, negated_conjecture,
% 0.39/0.56    (~( ![A:$i]:
% 0.39/0.56        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.39/0.56            ( l1_pre_topc @ A ) ) =>
% 0.39/0.56          ( ![B:$i]:
% 0.39/0.56            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.39/0.56                ( l1_pre_topc @ B ) ) =>
% 0.39/0.56              ( ![C:$i]:
% 0.39/0.56                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.39/0.56                  ( ![D:$i]:
% 0.39/0.56                    ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.39/0.56                      ( ![E:$i]:
% 0.39/0.56                        ( ( ( v1_funct_1 @ E ) & 
% 0.39/0.56                            ( v1_funct_2 @
% 0.39/0.56                              E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 0.39/0.56                            ( m1_subset_1 @
% 0.39/0.56                              E @ 
% 0.39/0.56                              ( k1_zfmisc_1 @
% 0.39/0.56                                ( k2_zfmisc_1 @
% 0.39/0.56                                  ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.39/0.56                          ( ( m1_pre_topc @ C @ D ) =>
% 0.39/0.56                            ( ![F:$i]:
% 0.39/0.56                              ( ( m1_subset_1 @
% 0.39/0.56                                  F @ ( k1_zfmisc_1 @ ( u1_struct_0 @ D ) ) ) =>
% 0.39/0.56                                ( ![G:$i]:
% 0.39/0.56                                  ( ( m1_subset_1 @ G @ ( u1_struct_0 @ D ) ) =>
% 0.39/0.56                                    ( ![H:$i]:
% 0.39/0.56                                      ( ( m1_subset_1 @ H @ ( u1_struct_0 @ C ) ) =>
% 0.39/0.56                                        ( ( ( v3_pre_topc @ F @ D ) & 
% 0.39/0.56                                            ( r2_hidden @ G @ F ) & 
% 0.39/0.56                                            ( r1_tarski @
% 0.39/0.56                                              F @ ( u1_struct_0 @ C ) ) & 
% 0.39/0.56                                            ( ( G ) = ( H ) ) ) =>
% 0.39/0.56                                          ( ( r1_tmap_1 @ D @ B @ E @ G ) <=>
% 0.39/0.56                                            ( r1_tmap_1 @
% 0.39/0.56                                              C @ B @ 
% 0.39/0.56                                              ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ 
% 0.39/0.56                                              H ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.39/0.56    inference('cnf.neg', [status(esa)], [t84_tmap_1])).
% 0.39/0.56  thf('0', plain, (~ (v2_struct_0 @ sk_C)),
% 0.39/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.56  thf(t2_tsep_1, axiom,
% 0.39/0.56    (![A:$i]: ( ( l1_pre_topc @ A ) => ( m1_pre_topc @ A @ A ) ))).
% 0.39/0.56  thf('1', plain,
% 0.39/0.56      (![X13 : $i]: ((m1_pre_topc @ X13 @ X13) | ~ (l1_pre_topc @ X13))),
% 0.39/0.56      inference('cnf', [status(esa)], [t2_tsep_1])).
% 0.39/0.56  thf(t1_tsep_1, axiom,
% 0.39/0.56    (![A:$i]:
% 0.39/0.56     ( ( l1_pre_topc @ A ) =>
% 0.39/0.56       ( ![B:$i]:
% 0.39/0.56         ( ( m1_pre_topc @ B @ A ) =>
% 0.39/0.56           ( m1_subset_1 @
% 0.39/0.56             ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.39/0.56  thf('2', plain,
% 0.39/0.56      (![X11 : $i, X12 : $i]:
% 0.39/0.56         (~ (m1_pre_topc @ X11 @ X12)
% 0.39/0.56          | (m1_subset_1 @ (u1_struct_0 @ X11) @ 
% 0.39/0.56             (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.39/0.56          | ~ (l1_pre_topc @ X12))),
% 0.39/0.56      inference('cnf', [status(esa)], [t1_tsep_1])).
% 0.39/0.56  thf('3', plain,
% 0.39/0.56      (![X0 : $i]:
% 0.39/0.56         (~ (l1_pre_topc @ X0)
% 0.39/0.56          | ~ (l1_pre_topc @ X0)
% 0.39/0.56          | (m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 0.39/0.56             (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.39/0.56      inference('sup-', [status(thm)], ['1', '2'])).
% 0.39/0.56  thf('4', plain,
% 0.39/0.56      (![X0 : $i]:
% 0.39/0.56         ((m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 0.39/0.56           (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.39/0.56          | ~ (l1_pre_topc @ X0))),
% 0.39/0.56      inference('simplify', [status(thm)], ['3'])).
% 0.39/0.56  thf(t3_subset, axiom,
% 0.39/0.56    (![A:$i,B:$i]:
% 0.39/0.56     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.39/0.56  thf('5', plain,
% 0.39/0.56      (![X0 : $i, X1 : $i]:
% 0.39/0.56         ((r1_tarski @ X0 @ X1) | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1)))),
% 0.39/0.56      inference('cnf', [status(esa)], [t3_subset])).
% 0.39/0.56  thf('6', plain,
% 0.39/0.56      (![X0 : $i]:
% 0.39/0.56         (~ (l1_pre_topc @ X0)
% 0.39/0.56          | (r1_tarski @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0)))),
% 0.39/0.56      inference('sup-', [status(thm)], ['4', '5'])).
% 0.39/0.56  thf('7', plain, ((m1_pre_topc @ sk_C @ sk_D_1)),
% 0.39/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.56  thf('8', plain,
% 0.39/0.56      (![X11 : $i, X12 : $i]:
% 0.39/0.56         (~ (m1_pre_topc @ X11 @ X12)
% 0.39/0.56          | (m1_subset_1 @ (u1_struct_0 @ X11) @ 
% 0.39/0.56             (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.39/0.56          | ~ (l1_pre_topc @ X12))),
% 0.39/0.56      inference('cnf', [status(esa)], [t1_tsep_1])).
% 0.39/0.56  thf('9', plain,
% 0.39/0.56      ((~ (l1_pre_topc @ sk_D_1)
% 0.39/0.56        | (m1_subset_1 @ (u1_struct_0 @ sk_C) @ 
% 0.39/0.56           (k1_zfmisc_1 @ (u1_struct_0 @ sk_D_1))))),
% 0.39/0.56      inference('sup-', [status(thm)], ['7', '8'])).
% 0.39/0.56  thf('10', plain, ((m1_pre_topc @ sk_D_1 @ sk_A)),
% 0.39/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.56  thf(dt_m1_pre_topc, axiom,
% 0.39/0.56    (![A:$i]:
% 0.39/0.56     ( ( l1_pre_topc @ A ) =>
% 0.39/0.56       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.39/0.56  thf('11', plain,
% 0.39/0.56      (![X5 : $i, X6 : $i]:
% 0.39/0.56         (~ (m1_pre_topc @ X5 @ X6) | (l1_pre_topc @ X5) | ~ (l1_pre_topc @ X6))),
% 0.39/0.56      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.39/0.56  thf('12', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_D_1))),
% 0.39/0.56      inference('sup-', [status(thm)], ['10', '11'])).
% 0.39/0.56  thf('13', plain, ((l1_pre_topc @ sk_A)),
% 0.39/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.56  thf('14', plain, ((l1_pre_topc @ sk_D_1)),
% 0.39/0.56      inference('demod', [status(thm)], ['12', '13'])).
% 0.39/0.56  thf('15', plain,
% 0.39/0.56      ((m1_subset_1 @ (u1_struct_0 @ sk_C) @ 
% 0.39/0.56        (k1_zfmisc_1 @ (u1_struct_0 @ sk_D_1)))),
% 0.39/0.56      inference('demod', [status(thm)], ['9', '14'])).
% 0.39/0.56  thf('16', plain,
% 0.39/0.56      (((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.39/0.56         (k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C @ sk_E) @ sk_H)
% 0.39/0.56        | (r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_G))),
% 0.39/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.56  thf('17', plain,
% 0.39/0.56      (((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.39/0.56         (k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C @ sk_E) @ sk_H))
% 0.39/0.56         <= (((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.39/0.56               (k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C @ sk_E) @ sk_H)))),
% 0.39/0.56      inference('split', [status(esa)], ['16'])).
% 0.39/0.56  thf('18', plain,
% 0.39/0.56      ((m1_subset_1 @ sk_E @ 
% 0.39/0.56        (k1_zfmisc_1 @ 
% 0.39/0.56         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D_1) @ (u1_struct_0 @ sk_B))))),
% 0.39/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.56  thf(t83_tmap_1, axiom,
% 0.39/0.56    (![A:$i]:
% 0.39/0.56     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.39/0.56       ( ![B:$i]:
% 0.39/0.56         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.39/0.56             ( l1_pre_topc @ B ) ) =>
% 0.39/0.56           ( ![C:$i]:
% 0.39/0.56             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.39/0.56               ( ![D:$i]:
% 0.39/0.56                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.39/0.56                   ( ![E:$i]:
% 0.39/0.56                     ( ( ( v1_funct_1 @ E ) & 
% 0.39/0.56                         ( v1_funct_2 @
% 0.39/0.56                           E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 0.39/0.56                         ( m1_subset_1 @
% 0.39/0.56                           E @ 
% 0.39/0.56                           ( k1_zfmisc_1 @
% 0.39/0.56                             ( k2_zfmisc_1 @
% 0.39/0.56                               ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.39/0.56                       ( ( m1_pre_topc @ C @ D ) =>
% 0.39/0.56                         ( ![F:$i]:
% 0.39/0.56                           ( ( m1_subset_1 @
% 0.39/0.56                               F @ ( k1_zfmisc_1 @ ( u1_struct_0 @ D ) ) ) =>
% 0.39/0.56                             ( ![G:$i]:
% 0.39/0.56                               ( ( m1_subset_1 @ G @ ( u1_struct_0 @ D ) ) =>
% 0.39/0.56                                 ( ![H:$i]:
% 0.39/0.56                                   ( ( m1_subset_1 @ H @ ( u1_struct_0 @ C ) ) =>
% 0.39/0.56                                     ( ( ( r1_tarski @ F @ ( u1_struct_0 @ C ) ) & 
% 0.39/0.56                                         ( m1_connsp_2 @ F @ D @ G ) & 
% 0.39/0.56                                         ( ( G ) = ( H ) ) ) =>
% 0.39/0.56                                       ( ( r1_tmap_1 @ D @ B @ E @ G ) <=>
% 0.39/0.56                                         ( r1_tmap_1 @
% 0.39/0.56                                           C @ B @ 
% 0.39/0.56                                           ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ 
% 0.39/0.56                                           H ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.39/0.56  thf('19', plain,
% 0.39/0.56      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i, X30 : $i, 
% 0.39/0.56         X31 : $i]:
% 0.39/0.56         ((v2_struct_0 @ X24)
% 0.39/0.56          | ~ (v2_pre_topc @ X24)
% 0.39/0.56          | ~ (l1_pre_topc @ X24)
% 0.39/0.56          | (v2_struct_0 @ X25)
% 0.39/0.56          | ~ (m1_pre_topc @ X25 @ X26)
% 0.39/0.56          | ~ (m1_pre_topc @ X27 @ X25)
% 0.39/0.56          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 0.39/0.56          | ~ (m1_subset_1 @ X29 @ (u1_struct_0 @ X27))
% 0.39/0.56          | ~ (r1_tmap_1 @ X27 @ X24 @ 
% 0.39/0.56               (k3_tmap_1 @ X26 @ X24 @ X25 @ X27 @ X30) @ X29)
% 0.39/0.56          | (r1_tmap_1 @ X25 @ X24 @ X30 @ X31)
% 0.39/0.56          | ((X31) != (X29))
% 0.39/0.56          | ~ (m1_connsp_2 @ X28 @ X25 @ X31)
% 0.39/0.56          | ~ (r1_tarski @ X28 @ (u1_struct_0 @ X27))
% 0.39/0.56          | ~ (m1_subset_1 @ X31 @ (u1_struct_0 @ X25))
% 0.39/0.56          | ~ (m1_subset_1 @ X30 @ 
% 0.39/0.56               (k1_zfmisc_1 @ 
% 0.39/0.56                (k2_zfmisc_1 @ (u1_struct_0 @ X25) @ (u1_struct_0 @ X24))))
% 0.39/0.56          | ~ (v1_funct_2 @ X30 @ (u1_struct_0 @ X25) @ (u1_struct_0 @ X24))
% 0.39/0.56          | ~ (v1_funct_1 @ X30)
% 0.39/0.56          | ~ (m1_pre_topc @ X27 @ X26)
% 0.39/0.56          | (v2_struct_0 @ X27)
% 0.39/0.56          | ~ (l1_pre_topc @ X26)
% 0.39/0.56          | ~ (v2_pre_topc @ X26)
% 0.39/0.56          | (v2_struct_0 @ X26))),
% 0.39/0.56      inference('cnf', [status(esa)], [t83_tmap_1])).
% 0.39/0.56  thf('20', plain,
% 0.39/0.56      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 0.39/0.56         ((v2_struct_0 @ X26)
% 0.39/0.56          | ~ (v2_pre_topc @ X26)
% 0.39/0.56          | ~ (l1_pre_topc @ X26)
% 0.39/0.56          | (v2_struct_0 @ X27)
% 0.39/0.56          | ~ (m1_pre_topc @ X27 @ X26)
% 0.39/0.56          | ~ (v1_funct_1 @ X30)
% 0.39/0.56          | ~ (v1_funct_2 @ X30 @ (u1_struct_0 @ X25) @ (u1_struct_0 @ X24))
% 0.39/0.56          | ~ (m1_subset_1 @ X30 @ 
% 0.39/0.56               (k1_zfmisc_1 @ 
% 0.39/0.56                (k2_zfmisc_1 @ (u1_struct_0 @ X25) @ (u1_struct_0 @ X24))))
% 0.39/0.56          | ~ (m1_subset_1 @ X29 @ (u1_struct_0 @ X25))
% 0.39/0.56          | ~ (r1_tarski @ X28 @ (u1_struct_0 @ X27))
% 0.39/0.56          | ~ (m1_connsp_2 @ X28 @ X25 @ X29)
% 0.39/0.56          | (r1_tmap_1 @ X25 @ X24 @ X30 @ X29)
% 0.39/0.56          | ~ (r1_tmap_1 @ X27 @ X24 @ 
% 0.39/0.56               (k3_tmap_1 @ X26 @ X24 @ X25 @ X27 @ X30) @ X29)
% 0.39/0.56          | ~ (m1_subset_1 @ X29 @ (u1_struct_0 @ X27))
% 0.39/0.56          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 0.39/0.56          | ~ (m1_pre_topc @ X27 @ X25)
% 0.39/0.56          | ~ (m1_pre_topc @ X25 @ X26)
% 0.39/0.56          | (v2_struct_0 @ X25)
% 0.39/0.56          | ~ (l1_pre_topc @ X24)
% 0.39/0.56          | ~ (v2_pre_topc @ X24)
% 0.39/0.56          | (v2_struct_0 @ X24))),
% 0.39/0.56      inference('simplify', [status(thm)], ['19'])).
% 0.39/0.56  thf('21', plain,
% 0.39/0.56      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.39/0.56         ((v2_struct_0 @ sk_B)
% 0.39/0.56          | ~ (v2_pre_topc @ sk_B)
% 0.39/0.56          | ~ (l1_pre_topc @ sk_B)
% 0.39/0.56          | (v2_struct_0 @ sk_D_1)
% 0.39/0.56          | ~ (m1_pre_topc @ sk_D_1 @ X0)
% 0.39/0.56          | ~ (m1_pre_topc @ X1 @ sk_D_1)
% 0.39/0.56          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D_1)))
% 0.39/0.56          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X1))
% 0.39/0.56          | ~ (r1_tmap_1 @ X1 @ sk_B @ 
% 0.39/0.56               (k3_tmap_1 @ X0 @ sk_B @ sk_D_1 @ X1 @ sk_E) @ X3)
% 0.39/0.56          | (r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ X3)
% 0.39/0.56          | ~ (m1_connsp_2 @ X2 @ sk_D_1 @ X3)
% 0.39/0.56          | ~ (r1_tarski @ X2 @ (u1_struct_0 @ X1))
% 0.39/0.56          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ sk_D_1))
% 0.39/0.56          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D_1) @ 
% 0.39/0.56               (u1_struct_0 @ sk_B))
% 0.39/0.56          | ~ (v1_funct_1 @ sk_E)
% 0.39/0.56          | ~ (m1_pre_topc @ X1 @ X0)
% 0.39/0.56          | (v2_struct_0 @ X1)
% 0.39/0.56          | ~ (l1_pre_topc @ X0)
% 0.39/0.56          | ~ (v2_pre_topc @ X0)
% 0.39/0.56          | (v2_struct_0 @ X0))),
% 0.39/0.56      inference('sup-', [status(thm)], ['18', '20'])).
% 0.39/0.56  thf('22', plain, ((v2_pre_topc @ sk_B)),
% 0.39/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.56  thf('23', plain, ((l1_pre_topc @ sk_B)),
% 0.39/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.56  thf('24', plain,
% 0.39/0.56      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D_1) @ (u1_struct_0 @ sk_B))),
% 0.39/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.56  thf('25', plain, ((v1_funct_1 @ sk_E)),
% 0.39/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.56  thf('26', plain,
% 0.39/0.56      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.39/0.56         ((v2_struct_0 @ sk_B)
% 0.39/0.56          | (v2_struct_0 @ sk_D_1)
% 0.39/0.56          | ~ (m1_pre_topc @ sk_D_1 @ X0)
% 0.39/0.56          | ~ (m1_pre_topc @ X1 @ sk_D_1)
% 0.39/0.56          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D_1)))
% 0.39/0.56          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X1))
% 0.39/0.56          | ~ (r1_tmap_1 @ X1 @ sk_B @ 
% 0.39/0.56               (k3_tmap_1 @ X0 @ sk_B @ sk_D_1 @ X1 @ sk_E) @ X3)
% 0.39/0.56          | (r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ X3)
% 0.39/0.56          | ~ (m1_connsp_2 @ X2 @ sk_D_1 @ X3)
% 0.39/0.56          | ~ (r1_tarski @ X2 @ (u1_struct_0 @ X1))
% 0.39/0.56          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ sk_D_1))
% 0.39/0.56          | ~ (m1_pre_topc @ X1 @ X0)
% 0.39/0.56          | (v2_struct_0 @ X1)
% 0.39/0.56          | ~ (l1_pre_topc @ X0)
% 0.39/0.56          | ~ (v2_pre_topc @ X0)
% 0.39/0.56          | (v2_struct_0 @ X0))),
% 0.39/0.56      inference('demod', [status(thm)], ['21', '22', '23', '24', '25'])).
% 0.39/0.56  thf('27', plain,
% 0.39/0.56      ((![X0 : $i]:
% 0.39/0.56          ((v2_struct_0 @ sk_A)
% 0.39/0.56           | ~ (v2_pre_topc @ sk_A)
% 0.39/0.56           | ~ (l1_pre_topc @ sk_A)
% 0.39/0.56           | (v2_struct_0 @ sk_C)
% 0.39/0.56           | ~ (m1_pre_topc @ sk_C @ sk_A)
% 0.39/0.56           | ~ (m1_subset_1 @ sk_H @ (u1_struct_0 @ sk_D_1))
% 0.39/0.56           | ~ (r1_tarski @ X0 @ (u1_struct_0 @ sk_C))
% 0.39/0.56           | ~ (m1_connsp_2 @ X0 @ sk_D_1 @ sk_H)
% 0.39/0.56           | (r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_H)
% 0.39/0.56           | ~ (m1_subset_1 @ sk_H @ (u1_struct_0 @ sk_C))
% 0.39/0.56           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D_1)))
% 0.39/0.56           | ~ (m1_pre_topc @ sk_C @ sk_D_1)
% 0.39/0.56           | ~ (m1_pre_topc @ sk_D_1 @ sk_A)
% 0.39/0.56           | (v2_struct_0 @ sk_D_1)
% 0.39/0.56           | (v2_struct_0 @ sk_B)))
% 0.39/0.56         <= (((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.39/0.56               (k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C @ sk_E) @ sk_H)))),
% 0.39/0.56      inference('sup-', [status(thm)], ['17', '26'])).
% 0.39/0.56  thf('28', plain, ((v2_pre_topc @ sk_A)),
% 0.39/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.56  thf('29', plain, ((l1_pre_topc @ sk_A)),
% 0.39/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.56  thf('30', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.39/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.56  thf('31', plain, ((m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_D_1))),
% 0.39/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.56  thf('32', plain, (((sk_G) = (sk_H))),
% 0.39/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.56  thf('33', plain, ((m1_subset_1 @ sk_H @ (u1_struct_0 @ sk_D_1))),
% 0.39/0.56      inference('demod', [status(thm)], ['31', '32'])).
% 0.39/0.56  thf('34', plain, ((m1_subset_1 @ sk_H @ (u1_struct_0 @ sk_C))),
% 0.39/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.56  thf('35', plain, ((m1_pre_topc @ sk_C @ sk_D_1)),
% 0.39/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.56  thf('36', plain, ((m1_pre_topc @ sk_D_1 @ sk_A)),
% 0.39/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.56  thf('37', plain,
% 0.39/0.56      ((![X0 : $i]:
% 0.39/0.56          ((v2_struct_0 @ sk_A)
% 0.39/0.56           | (v2_struct_0 @ sk_C)
% 0.39/0.56           | ~ (r1_tarski @ X0 @ (u1_struct_0 @ sk_C))
% 0.39/0.56           | ~ (m1_connsp_2 @ X0 @ sk_D_1 @ sk_H)
% 0.39/0.56           | (r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_H)
% 0.39/0.56           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D_1)))
% 0.39/0.56           | (v2_struct_0 @ sk_D_1)
% 0.39/0.56           | (v2_struct_0 @ sk_B)))
% 0.39/0.56         <= (((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.39/0.56               (k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C @ sk_E) @ sk_H)))),
% 0.39/0.56      inference('demod', [status(thm)],
% 0.39/0.56                ['27', '28', '29', '30', '33', '34', '35', '36'])).
% 0.39/0.56  thf('38', plain,
% 0.39/0.56      ((~ (r1_tmap_1 @ sk_C @ sk_B @ 
% 0.39/0.56           (k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C @ sk_E) @ sk_H)
% 0.39/0.56        | ~ (r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_G))),
% 0.39/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.56  thf('39', plain, (((sk_G) = (sk_H))),
% 0.39/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.56  thf('40', plain,
% 0.39/0.56      ((~ (r1_tmap_1 @ sk_C @ sk_B @ 
% 0.39/0.56           (k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C @ sk_E) @ sk_H)
% 0.39/0.56        | ~ (r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_H))),
% 0.39/0.56      inference('demod', [status(thm)], ['38', '39'])).
% 0.39/0.56  thf('41', plain,
% 0.39/0.56      (~ ((r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_H)) | 
% 0.39/0.56       ~
% 0.39/0.56       ((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.39/0.56         (k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C @ sk_E) @ sk_H))),
% 0.39/0.56      inference('split', [status(esa)], ['40'])).
% 0.39/0.56  thf('42', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.39/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.56  thf('43', plain, ((m1_subset_1 @ sk_H @ (u1_struct_0 @ sk_C))),
% 0.39/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.56  thf('44', plain,
% 0.39/0.56      (((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.39/0.56         (k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C @ sk_E) @ sk_H)
% 0.39/0.56        | (r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_G))),
% 0.39/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.56  thf('45', plain, (((sk_G) = (sk_H))),
% 0.39/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.56  thf('46', plain,
% 0.39/0.56      (((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.39/0.56         (k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C @ sk_E) @ sk_H)
% 0.39/0.56        | (r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_H))),
% 0.39/0.56      inference('demod', [status(thm)], ['44', '45'])).
% 0.39/0.56  thf('47', plain,
% 0.39/0.56      (((r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_H))
% 0.39/0.56         <= (((r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_H)))),
% 0.39/0.56      inference('split', [status(esa)], ['46'])).
% 0.39/0.56  thf('48', plain,
% 0.39/0.56      ((m1_subset_1 @ sk_E @ 
% 0.39/0.56        (k1_zfmisc_1 @ 
% 0.39/0.56         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D_1) @ (u1_struct_0 @ sk_B))))),
% 0.39/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.56  thf(t81_tmap_1, axiom,
% 0.39/0.56    (![A:$i]:
% 0.39/0.56     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.39/0.56       ( ![B:$i]:
% 0.39/0.56         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.39/0.56             ( l1_pre_topc @ B ) ) =>
% 0.39/0.56           ( ![C:$i]:
% 0.39/0.56             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.39/0.56               ( ![D:$i]:
% 0.39/0.56                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.39/0.56                   ( ![E:$i]:
% 0.39/0.56                     ( ( ( v1_funct_1 @ E ) & 
% 0.39/0.56                         ( v1_funct_2 @
% 0.39/0.56                           E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 0.39/0.56                         ( m1_subset_1 @
% 0.39/0.56                           E @ 
% 0.39/0.56                           ( k1_zfmisc_1 @
% 0.39/0.56                             ( k2_zfmisc_1 @
% 0.39/0.56                               ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.39/0.56                       ( ![F:$i]:
% 0.39/0.56                         ( ( m1_subset_1 @ F @ ( u1_struct_0 @ C ) ) =>
% 0.39/0.56                           ( ![G:$i]:
% 0.39/0.56                             ( ( m1_subset_1 @ G @ ( u1_struct_0 @ D ) ) =>
% 0.39/0.56                               ( ( ( ( F ) = ( G ) ) & 
% 0.39/0.56                                   ( m1_pre_topc @ D @ C ) & 
% 0.39/0.56                                   ( r1_tmap_1 @ C @ B @ E @ F ) ) =>
% 0.39/0.56                                 ( r1_tmap_1 @
% 0.39/0.56                                   D @ B @ ( k3_tmap_1 @ A @ B @ C @ D @ E ) @ 
% 0.39/0.56                                   G ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.39/0.56  thf('49', plain,
% 0.39/0.56      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 0.39/0.56         ((v2_struct_0 @ X17)
% 0.39/0.56          | ~ (v2_pre_topc @ X17)
% 0.39/0.56          | ~ (l1_pre_topc @ X17)
% 0.39/0.56          | (v2_struct_0 @ X18)
% 0.39/0.56          | ~ (m1_pre_topc @ X18 @ X19)
% 0.39/0.56          | ~ (m1_subset_1 @ X20 @ (u1_struct_0 @ X21))
% 0.39/0.56          | ~ (m1_pre_topc @ X18 @ X21)
% 0.39/0.56          | ~ (r1_tmap_1 @ X21 @ X17 @ X22 @ X20)
% 0.39/0.56          | ((X20) != (X23))
% 0.39/0.56          | (r1_tmap_1 @ X18 @ X17 @ 
% 0.39/0.56             (k3_tmap_1 @ X19 @ X17 @ X21 @ X18 @ X22) @ X23)
% 0.39/0.56          | ~ (m1_subset_1 @ X23 @ (u1_struct_0 @ X18))
% 0.39/0.56          | ~ (m1_subset_1 @ X22 @ 
% 0.39/0.56               (k1_zfmisc_1 @ 
% 0.39/0.56                (k2_zfmisc_1 @ (u1_struct_0 @ X21) @ (u1_struct_0 @ X17))))
% 0.39/0.56          | ~ (v1_funct_2 @ X22 @ (u1_struct_0 @ X21) @ (u1_struct_0 @ X17))
% 0.39/0.56          | ~ (v1_funct_1 @ X22)
% 0.39/0.56          | ~ (m1_pre_topc @ X21 @ X19)
% 0.39/0.56          | (v2_struct_0 @ X21)
% 0.39/0.56          | ~ (l1_pre_topc @ X19)
% 0.39/0.56          | ~ (v2_pre_topc @ X19)
% 0.39/0.56          | (v2_struct_0 @ X19))),
% 0.39/0.56      inference('cnf', [status(esa)], [t81_tmap_1])).
% 0.39/0.56  thf('50', plain,
% 0.39/0.56      (![X17 : $i, X18 : $i, X19 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 0.39/0.56         ((v2_struct_0 @ X19)
% 0.39/0.56          | ~ (v2_pre_topc @ X19)
% 0.39/0.56          | ~ (l1_pre_topc @ X19)
% 0.39/0.56          | (v2_struct_0 @ X21)
% 0.39/0.56          | ~ (m1_pre_topc @ X21 @ X19)
% 0.39/0.56          | ~ (v1_funct_1 @ X22)
% 0.39/0.56          | ~ (v1_funct_2 @ X22 @ (u1_struct_0 @ X21) @ (u1_struct_0 @ X17))
% 0.39/0.56          | ~ (m1_subset_1 @ X22 @ 
% 0.39/0.56               (k1_zfmisc_1 @ 
% 0.39/0.56                (k2_zfmisc_1 @ (u1_struct_0 @ X21) @ (u1_struct_0 @ X17))))
% 0.39/0.56          | ~ (m1_subset_1 @ X23 @ (u1_struct_0 @ X18))
% 0.39/0.56          | (r1_tmap_1 @ X18 @ X17 @ 
% 0.39/0.56             (k3_tmap_1 @ X19 @ X17 @ X21 @ X18 @ X22) @ X23)
% 0.39/0.56          | ~ (r1_tmap_1 @ X21 @ X17 @ X22 @ X23)
% 0.39/0.56          | ~ (m1_pre_topc @ X18 @ X21)
% 0.39/0.56          | ~ (m1_subset_1 @ X23 @ (u1_struct_0 @ X21))
% 0.39/0.56          | ~ (m1_pre_topc @ X18 @ X19)
% 0.39/0.56          | (v2_struct_0 @ X18)
% 0.39/0.56          | ~ (l1_pre_topc @ X17)
% 0.39/0.56          | ~ (v2_pre_topc @ X17)
% 0.39/0.56          | (v2_struct_0 @ X17))),
% 0.39/0.56      inference('simplify', [status(thm)], ['49'])).
% 0.39/0.56  thf('51', plain,
% 0.39/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.39/0.56         ((v2_struct_0 @ sk_B)
% 0.39/0.56          | ~ (v2_pre_topc @ sk_B)
% 0.39/0.56          | ~ (l1_pre_topc @ sk_B)
% 0.39/0.56          | (v2_struct_0 @ X0)
% 0.39/0.56          | ~ (m1_pre_topc @ X0 @ X1)
% 0.39/0.56          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ sk_D_1))
% 0.39/0.56          | ~ (m1_pre_topc @ X0 @ sk_D_1)
% 0.39/0.56          | ~ (r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ X2)
% 0.39/0.56          | (r1_tmap_1 @ X0 @ sk_B @ 
% 0.39/0.56             (k3_tmap_1 @ X1 @ sk_B @ sk_D_1 @ X0 @ sk_E) @ X2)
% 0.39/0.56          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.39/0.56          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D_1) @ 
% 0.39/0.56               (u1_struct_0 @ sk_B))
% 0.39/0.56          | ~ (v1_funct_1 @ sk_E)
% 0.39/0.56          | ~ (m1_pre_topc @ sk_D_1 @ X1)
% 0.39/0.56          | (v2_struct_0 @ sk_D_1)
% 0.39/0.56          | ~ (l1_pre_topc @ X1)
% 0.39/0.56          | ~ (v2_pre_topc @ X1)
% 0.39/0.56          | (v2_struct_0 @ X1))),
% 0.39/0.56      inference('sup-', [status(thm)], ['48', '50'])).
% 0.39/0.56  thf('52', plain, ((v2_pre_topc @ sk_B)),
% 0.39/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.56  thf('53', plain, ((l1_pre_topc @ sk_B)),
% 0.39/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.56  thf('54', plain,
% 0.39/0.56      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D_1) @ (u1_struct_0 @ sk_B))),
% 0.39/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.56  thf('55', plain, ((v1_funct_1 @ sk_E)),
% 0.39/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.56  thf('56', plain,
% 0.39/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.39/0.56         ((v2_struct_0 @ sk_B)
% 0.39/0.56          | (v2_struct_0 @ X0)
% 0.39/0.56          | ~ (m1_pre_topc @ X0 @ X1)
% 0.39/0.56          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ sk_D_1))
% 0.39/0.56          | ~ (m1_pre_topc @ X0 @ sk_D_1)
% 0.39/0.56          | ~ (r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ X2)
% 0.39/0.56          | (r1_tmap_1 @ X0 @ sk_B @ 
% 0.39/0.56             (k3_tmap_1 @ X1 @ sk_B @ sk_D_1 @ X0 @ sk_E) @ X2)
% 0.39/0.56          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.39/0.56          | ~ (m1_pre_topc @ sk_D_1 @ X1)
% 0.39/0.56          | (v2_struct_0 @ sk_D_1)
% 0.39/0.56          | ~ (l1_pre_topc @ X1)
% 0.39/0.56          | ~ (v2_pre_topc @ X1)
% 0.39/0.56          | (v2_struct_0 @ X1))),
% 0.39/0.56      inference('demod', [status(thm)], ['51', '52', '53', '54', '55'])).
% 0.39/0.56  thf('57', plain,
% 0.39/0.56      ((![X0 : $i, X1 : $i]:
% 0.39/0.56          ((v2_struct_0 @ X0)
% 0.39/0.56           | ~ (v2_pre_topc @ X0)
% 0.39/0.56           | ~ (l1_pre_topc @ X0)
% 0.39/0.56           | (v2_struct_0 @ sk_D_1)
% 0.39/0.56           | ~ (m1_pre_topc @ sk_D_1 @ X0)
% 0.39/0.56           | ~ (m1_subset_1 @ sk_H @ (u1_struct_0 @ X1))
% 0.39/0.56           | (r1_tmap_1 @ X1 @ sk_B @ 
% 0.39/0.56              (k3_tmap_1 @ X0 @ sk_B @ sk_D_1 @ X1 @ sk_E) @ sk_H)
% 0.39/0.56           | ~ (m1_pre_topc @ X1 @ sk_D_1)
% 0.39/0.56           | ~ (m1_subset_1 @ sk_H @ (u1_struct_0 @ sk_D_1))
% 0.39/0.56           | ~ (m1_pre_topc @ X1 @ X0)
% 0.39/0.56           | (v2_struct_0 @ X1)
% 0.39/0.56           | (v2_struct_0 @ sk_B)))
% 0.39/0.56         <= (((r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_H)))),
% 0.39/0.56      inference('sup-', [status(thm)], ['47', '56'])).
% 0.39/0.56  thf('58', plain, ((m1_subset_1 @ sk_H @ (u1_struct_0 @ sk_D_1))),
% 0.39/0.56      inference('demod', [status(thm)], ['31', '32'])).
% 0.39/0.56  thf('59', plain,
% 0.39/0.56      ((![X0 : $i, X1 : $i]:
% 0.39/0.56          ((v2_struct_0 @ X0)
% 0.39/0.56           | ~ (v2_pre_topc @ X0)
% 0.39/0.56           | ~ (l1_pre_topc @ X0)
% 0.39/0.56           | (v2_struct_0 @ sk_D_1)
% 0.39/0.56           | ~ (m1_pre_topc @ sk_D_1 @ X0)
% 0.39/0.56           | ~ (m1_subset_1 @ sk_H @ (u1_struct_0 @ X1))
% 0.39/0.56           | (r1_tmap_1 @ X1 @ sk_B @ 
% 0.39/0.56              (k3_tmap_1 @ X0 @ sk_B @ sk_D_1 @ X1 @ sk_E) @ sk_H)
% 0.39/0.56           | ~ (m1_pre_topc @ X1 @ sk_D_1)
% 0.39/0.56           | ~ (m1_pre_topc @ X1 @ X0)
% 0.39/0.56           | (v2_struct_0 @ X1)
% 0.39/0.56           | (v2_struct_0 @ sk_B)))
% 0.39/0.56         <= (((r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_H)))),
% 0.39/0.56      inference('demod', [status(thm)], ['57', '58'])).
% 0.39/0.56  thf('60', plain,
% 0.39/0.56      ((![X0 : $i]:
% 0.39/0.56          ((v2_struct_0 @ sk_B)
% 0.39/0.56           | (v2_struct_0 @ sk_C)
% 0.39/0.56           | ~ (m1_pre_topc @ sk_C @ X0)
% 0.39/0.56           | ~ (m1_pre_topc @ sk_C @ sk_D_1)
% 0.39/0.56           | (r1_tmap_1 @ sk_C @ sk_B @ 
% 0.39/0.56              (k3_tmap_1 @ X0 @ sk_B @ sk_D_1 @ sk_C @ sk_E) @ sk_H)
% 0.39/0.56           | ~ (m1_pre_topc @ sk_D_1 @ X0)
% 0.39/0.56           | (v2_struct_0 @ sk_D_1)
% 0.39/0.56           | ~ (l1_pre_topc @ X0)
% 0.39/0.56           | ~ (v2_pre_topc @ X0)
% 0.39/0.56           | (v2_struct_0 @ X0)))
% 0.39/0.56         <= (((r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_H)))),
% 0.39/0.56      inference('sup-', [status(thm)], ['43', '59'])).
% 0.39/0.56  thf('61', plain, ((m1_pre_topc @ sk_C @ sk_D_1)),
% 0.39/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.56  thf('62', plain,
% 0.39/0.56      ((![X0 : $i]:
% 0.39/0.56          ((v2_struct_0 @ sk_B)
% 0.39/0.56           | (v2_struct_0 @ sk_C)
% 0.39/0.56           | ~ (m1_pre_topc @ sk_C @ X0)
% 0.39/0.56           | (r1_tmap_1 @ sk_C @ sk_B @ 
% 0.39/0.56              (k3_tmap_1 @ X0 @ sk_B @ sk_D_1 @ sk_C @ sk_E) @ sk_H)
% 0.39/0.56           | ~ (m1_pre_topc @ sk_D_1 @ X0)
% 0.39/0.56           | (v2_struct_0 @ sk_D_1)
% 0.39/0.56           | ~ (l1_pre_topc @ X0)
% 0.39/0.56           | ~ (v2_pre_topc @ X0)
% 0.39/0.56           | (v2_struct_0 @ X0)))
% 0.39/0.56         <= (((r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_H)))),
% 0.39/0.56      inference('demod', [status(thm)], ['60', '61'])).
% 0.39/0.56  thf('63', plain,
% 0.39/0.56      ((((v2_struct_0 @ sk_A)
% 0.39/0.56         | ~ (v2_pre_topc @ sk_A)
% 0.39/0.56         | ~ (l1_pre_topc @ sk_A)
% 0.39/0.56         | (v2_struct_0 @ sk_D_1)
% 0.39/0.56         | ~ (m1_pre_topc @ sk_D_1 @ sk_A)
% 0.39/0.56         | (r1_tmap_1 @ sk_C @ sk_B @ 
% 0.39/0.56            (k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C @ sk_E) @ sk_H)
% 0.39/0.56         | (v2_struct_0 @ sk_C)
% 0.39/0.56         | (v2_struct_0 @ sk_B)))
% 0.39/0.56         <= (((r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_H)))),
% 0.39/0.56      inference('sup-', [status(thm)], ['42', '62'])).
% 0.39/0.56  thf('64', plain, ((v2_pre_topc @ sk_A)),
% 0.39/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.56  thf('65', plain, ((l1_pre_topc @ sk_A)),
% 0.39/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.56  thf('66', plain, ((m1_pre_topc @ sk_D_1 @ sk_A)),
% 0.39/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.56  thf('67', plain,
% 0.39/0.56      ((((v2_struct_0 @ sk_A)
% 0.39/0.56         | (v2_struct_0 @ sk_D_1)
% 0.39/0.56         | (r1_tmap_1 @ sk_C @ sk_B @ 
% 0.39/0.56            (k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C @ sk_E) @ sk_H)
% 0.39/0.56         | (v2_struct_0 @ sk_C)
% 0.39/0.56         | (v2_struct_0 @ sk_B)))
% 0.39/0.56         <= (((r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_H)))),
% 0.39/0.56      inference('demod', [status(thm)], ['63', '64', '65', '66'])).
% 0.39/0.56  thf('68', plain,
% 0.39/0.56      ((~ (r1_tmap_1 @ sk_C @ sk_B @ 
% 0.39/0.56           (k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C @ sk_E) @ sk_H)
% 0.39/0.56        | ~ (r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_G))),
% 0.39/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.56  thf('69', plain,
% 0.39/0.56      ((~ (r1_tmap_1 @ sk_C @ sk_B @ 
% 0.39/0.56           (k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C @ sk_E) @ sk_H))
% 0.39/0.56         <= (~
% 0.39/0.56             ((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.39/0.56               (k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C @ sk_E) @ sk_H)))),
% 0.39/0.56      inference('split', [status(esa)], ['68'])).
% 0.39/0.56  thf('70', plain,
% 0.39/0.56      ((((v2_struct_0 @ sk_B)
% 0.39/0.56         | (v2_struct_0 @ sk_C)
% 0.39/0.56         | (v2_struct_0 @ sk_D_1)
% 0.39/0.56         | (v2_struct_0 @ sk_A)))
% 0.39/0.56         <= (~
% 0.39/0.56             ((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.39/0.56               (k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C @ sk_E) @ sk_H)) & 
% 0.39/0.56             ((r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_H)))),
% 0.39/0.56      inference('sup-', [status(thm)], ['67', '69'])).
% 0.39/0.56  thf('71', plain, (~ (v2_struct_0 @ sk_D_1)),
% 0.39/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.56  thf('72', plain,
% 0.39/0.56      ((((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_B)))
% 0.39/0.56         <= (~
% 0.39/0.56             ((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.39/0.56               (k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C @ sk_E) @ sk_H)) & 
% 0.39/0.56             ((r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_H)))),
% 0.39/0.56      inference('sup-', [status(thm)], ['70', '71'])).
% 0.39/0.56  thf('73', plain, (~ (v2_struct_0 @ sk_A)),
% 0.39/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.56  thf('74', plain,
% 0.39/0.56      ((((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_C)))
% 0.39/0.56         <= (~
% 0.39/0.56             ((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.39/0.56               (k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C @ sk_E) @ sk_H)) & 
% 0.39/0.56             ((r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_H)))),
% 0.39/0.56      inference('clc', [status(thm)], ['72', '73'])).
% 0.39/0.56  thf('75', plain, (~ (v2_struct_0 @ sk_B)),
% 0.39/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.56  thf('76', plain,
% 0.39/0.56      (((v2_struct_0 @ sk_C))
% 0.39/0.56         <= (~
% 0.39/0.56             ((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.39/0.56               (k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C @ sk_E) @ sk_H)) & 
% 0.39/0.56             ((r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_H)))),
% 0.39/0.56      inference('clc', [status(thm)], ['74', '75'])).
% 0.39/0.56  thf('77', plain, (~ (v2_struct_0 @ sk_C)),
% 0.39/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.56  thf('78', plain,
% 0.39/0.56      (((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.39/0.56         (k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C @ sk_E) @ sk_H)) | 
% 0.39/0.56       ~ ((r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_H))),
% 0.39/0.56      inference('sup-', [status(thm)], ['76', '77'])).
% 0.39/0.56  thf('79', plain,
% 0.39/0.56      (((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.39/0.56         (k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C @ sk_E) @ sk_H)) | 
% 0.39/0.56       ((r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_H))),
% 0.39/0.56      inference('split', [status(esa)], ['46'])).
% 0.39/0.56  thf('80', plain,
% 0.39/0.56      (((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.39/0.56         (k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C @ sk_E) @ sk_H))),
% 0.39/0.56      inference('sat_resolution*', [status(thm)], ['41', '78', '79'])).
% 0.39/0.56  thf('81', plain,
% 0.39/0.56      (![X0 : $i]:
% 0.39/0.56         ((v2_struct_0 @ sk_A)
% 0.39/0.56          | (v2_struct_0 @ sk_C)
% 0.39/0.56          | ~ (r1_tarski @ X0 @ (u1_struct_0 @ sk_C))
% 0.39/0.56          | ~ (m1_connsp_2 @ X0 @ sk_D_1 @ sk_H)
% 0.39/0.56          | (r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_H)
% 0.39/0.56          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D_1)))
% 0.39/0.56          | (v2_struct_0 @ sk_D_1)
% 0.39/0.56          | (v2_struct_0 @ sk_B))),
% 0.39/0.56      inference('simpl_trail', [status(thm)], ['37', '80'])).
% 0.39/0.56  thf('82', plain,
% 0.39/0.56      (((v2_struct_0 @ sk_B)
% 0.39/0.56        | (v2_struct_0 @ sk_D_1)
% 0.39/0.56        | (r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_H)
% 0.39/0.56        | ~ (m1_connsp_2 @ (u1_struct_0 @ sk_C) @ sk_D_1 @ sk_H)
% 0.39/0.56        | ~ (r1_tarski @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_C))
% 0.39/0.56        | (v2_struct_0 @ sk_C)
% 0.39/0.56        | (v2_struct_0 @ sk_A))),
% 0.39/0.56      inference('sup-', [status(thm)], ['15', '81'])).
% 0.39/0.56  thf('83', plain, ((m1_subset_1 @ sk_H @ (u1_struct_0 @ sk_D_1))),
% 0.39/0.56      inference('demod', [status(thm)], ['31', '32'])).
% 0.39/0.56  thf('84', plain,
% 0.39/0.56      ((m1_subset_1 @ (u1_struct_0 @ sk_C) @ 
% 0.39/0.56        (k1_zfmisc_1 @ (u1_struct_0 @ sk_D_1)))),
% 0.39/0.56      inference('demod', [status(thm)], ['9', '14'])).
% 0.39/0.56  thf('85', plain,
% 0.39/0.56      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D_1)))),
% 0.39/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.56  thf(t8_connsp_2, axiom,
% 0.39/0.56    (![A:$i]:
% 0.39/0.56     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.39/0.56       ( ![B:$i]:
% 0.39/0.56         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.39/0.56           ( ![C:$i]:
% 0.39/0.56             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.39/0.56               ( ( m1_connsp_2 @ C @ A @ B ) <=>
% 0.39/0.56                 ( ?[D:$i]:
% 0.39/0.56                   ( ( r2_hidden @ B @ D ) & ( r1_tarski @ D @ C ) & 
% 0.39/0.56                     ( v3_pre_topc @ D @ A ) & 
% 0.39/0.56                     ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ) ) ) ))).
% 0.39/0.56  thf('86', plain,
% 0.39/0.56      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.39/0.56         (~ (m1_subset_1 @ X7 @ (u1_struct_0 @ X8))
% 0.39/0.56          | ~ (r2_hidden @ X7 @ X10)
% 0.39/0.56          | ~ (r1_tarski @ X10 @ X9)
% 0.39/0.56          | ~ (v3_pre_topc @ X10 @ X8)
% 0.39/0.56          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 0.39/0.56          | (m1_connsp_2 @ X9 @ X8 @ X7)
% 0.39/0.56          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 0.39/0.56          | ~ (l1_pre_topc @ X8)
% 0.39/0.56          | ~ (v2_pre_topc @ X8)
% 0.39/0.56          | (v2_struct_0 @ X8))),
% 0.39/0.56      inference('cnf', [status(esa)], [t8_connsp_2])).
% 0.39/0.56  thf('87', plain,
% 0.39/0.56      (![X0 : $i, X1 : $i]:
% 0.39/0.56         ((v2_struct_0 @ sk_D_1)
% 0.39/0.56          | ~ (v2_pre_topc @ sk_D_1)
% 0.39/0.56          | ~ (l1_pre_topc @ sk_D_1)
% 0.39/0.56          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D_1)))
% 0.39/0.56          | (m1_connsp_2 @ X0 @ sk_D_1 @ X1)
% 0.39/0.56          | ~ (v3_pre_topc @ sk_F @ sk_D_1)
% 0.39/0.56          | ~ (r1_tarski @ sk_F @ X0)
% 0.39/0.56          | ~ (r2_hidden @ X1 @ sk_F)
% 0.39/0.56          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_D_1)))),
% 0.39/0.56      inference('sup-', [status(thm)], ['85', '86'])).
% 0.39/0.56  thf('88', plain, ((m1_pre_topc @ sk_D_1 @ sk_A)),
% 0.39/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.56  thf(cc1_pre_topc, axiom,
% 0.39/0.56    (![A:$i]:
% 0.39/0.56     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.39/0.56       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( v2_pre_topc @ B ) ) ) ))).
% 0.39/0.56  thf('89', plain,
% 0.39/0.56      (![X3 : $i, X4 : $i]:
% 0.39/0.56         (~ (m1_pre_topc @ X3 @ X4)
% 0.39/0.56          | (v2_pre_topc @ X3)
% 0.39/0.56          | ~ (l1_pre_topc @ X4)
% 0.39/0.56          | ~ (v2_pre_topc @ X4))),
% 0.39/0.56      inference('cnf', [status(esa)], [cc1_pre_topc])).
% 0.39/0.56  thf('90', plain,
% 0.39/0.56      ((~ (v2_pre_topc @ sk_A)
% 0.39/0.56        | ~ (l1_pre_topc @ sk_A)
% 0.39/0.56        | (v2_pre_topc @ sk_D_1))),
% 0.39/0.56      inference('sup-', [status(thm)], ['88', '89'])).
% 0.39/0.56  thf('91', plain, ((v2_pre_topc @ sk_A)),
% 0.39/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.56  thf('92', plain, ((l1_pre_topc @ sk_A)),
% 0.39/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.56  thf('93', plain, ((v2_pre_topc @ sk_D_1)),
% 0.39/0.56      inference('demod', [status(thm)], ['90', '91', '92'])).
% 0.39/0.56  thf('94', plain, ((l1_pre_topc @ sk_D_1)),
% 0.39/0.56      inference('demod', [status(thm)], ['12', '13'])).
% 0.39/0.56  thf('95', plain, ((v3_pre_topc @ sk_F @ sk_D_1)),
% 0.39/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.56  thf('96', plain,
% 0.39/0.56      (![X0 : $i, X1 : $i]:
% 0.39/0.56         ((v2_struct_0 @ sk_D_1)
% 0.39/0.56          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D_1)))
% 0.39/0.56          | (m1_connsp_2 @ X0 @ sk_D_1 @ X1)
% 0.39/0.56          | ~ (r1_tarski @ sk_F @ X0)
% 0.39/0.56          | ~ (r2_hidden @ X1 @ sk_F)
% 0.39/0.56          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_D_1)))),
% 0.39/0.56      inference('demod', [status(thm)], ['87', '93', '94', '95'])).
% 0.39/0.56  thf('97', plain,
% 0.39/0.56      (![X0 : $i]:
% 0.39/0.56         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_D_1))
% 0.39/0.56          | ~ (r2_hidden @ X0 @ sk_F)
% 0.39/0.56          | ~ (r1_tarski @ sk_F @ (u1_struct_0 @ sk_C))
% 0.39/0.56          | (m1_connsp_2 @ (u1_struct_0 @ sk_C) @ sk_D_1 @ X0)
% 0.39/0.56          | (v2_struct_0 @ sk_D_1))),
% 0.39/0.56      inference('sup-', [status(thm)], ['84', '96'])).
% 0.39/0.56  thf('98', plain, ((r1_tarski @ sk_F @ (u1_struct_0 @ sk_C))),
% 0.39/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.56  thf('99', plain,
% 0.39/0.56      (![X0 : $i]:
% 0.39/0.56         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_D_1))
% 0.39/0.56          | ~ (r2_hidden @ X0 @ sk_F)
% 0.39/0.56          | (m1_connsp_2 @ (u1_struct_0 @ sk_C) @ sk_D_1 @ X0)
% 0.39/0.56          | (v2_struct_0 @ sk_D_1))),
% 0.39/0.56      inference('demod', [status(thm)], ['97', '98'])).
% 0.39/0.56  thf('100', plain,
% 0.39/0.56      (((v2_struct_0 @ sk_D_1)
% 0.39/0.56        | (m1_connsp_2 @ (u1_struct_0 @ sk_C) @ sk_D_1 @ sk_H)
% 0.39/0.56        | ~ (r2_hidden @ sk_H @ sk_F))),
% 0.39/0.56      inference('sup-', [status(thm)], ['83', '99'])).
% 0.39/0.56  thf('101', plain, ((r2_hidden @ sk_G @ sk_F)),
% 0.39/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.56  thf('102', plain, (((sk_G) = (sk_H))),
% 0.39/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.56  thf('103', plain, ((r2_hidden @ sk_H @ sk_F)),
% 0.39/0.56      inference('demod', [status(thm)], ['101', '102'])).
% 0.39/0.56  thf('104', plain,
% 0.39/0.56      (((v2_struct_0 @ sk_D_1)
% 0.39/0.56        | (m1_connsp_2 @ (u1_struct_0 @ sk_C) @ sk_D_1 @ sk_H))),
% 0.39/0.56      inference('demod', [status(thm)], ['100', '103'])).
% 0.39/0.56  thf('105', plain, (~ (v2_struct_0 @ sk_D_1)),
% 0.39/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.56  thf('106', plain, ((m1_connsp_2 @ (u1_struct_0 @ sk_C) @ sk_D_1 @ sk_H)),
% 0.39/0.56      inference('clc', [status(thm)], ['104', '105'])).
% 0.39/0.56  thf('107', plain,
% 0.39/0.56      (((v2_struct_0 @ sk_B)
% 0.39/0.56        | (v2_struct_0 @ sk_D_1)
% 0.39/0.56        | (r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_H)
% 0.39/0.56        | ~ (r1_tarski @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_C))
% 0.39/0.56        | (v2_struct_0 @ sk_C)
% 0.39/0.56        | (v2_struct_0 @ sk_A))),
% 0.39/0.56      inference('demod', [status(thm)], ['82', '106'])).
% 0.39/0.56  thf('108', plain,
% 0.39/0.56      ((~ (l1_pre_topc @ sk_C)
% 0.39/0.56        | (v2_struct_0 @ sk_A)
% 0.39/0.56        | (v2_struct_0 @ sk_C)
% 0.39/0.56        | (r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_H)
% 0.39/0.56        | (v2_struct_0 @ sk_D_1)
% 0.39/0.56        | (v2_struct_0 @ sk_B))),
% 0.39/0.56      inference('sup-', [status(thm)], ['6', '107'])).
% 0.39/0.56  thf('109', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.39/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.56  thf('110', plain,
% 0.39/0.56      (![X5 : $i, X6 : $i]:
% 0.39/0.56         (~ (m1_pre_topc @ X5 @ X6) | (l1_pre_topc @ X5) | ~ (l1_pre_topc @ X6))),
% 0.39/0.56      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.39/0.56  thf('111', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_C))),
% 0.39/0.56      inference('sup-', [status(thm)], ['109', '110'])).
% 0.39/0.56  thf('112', plain, ((l1_pre_topc @ sk_A)),
% 0.39/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.56  thf('113', plain, ((l1_pre_topc @ sk_C)),
% 0.39/0.56      inference('demod', [status(thm)], ['111', '112'])).
% 0.39/0.56  thf('114', plain,
% 0.39/0.56      (((v2_struct_0 @ sk_A)
% 0.39/0.56        | (v2_struct_0 @ sk_C)
% 0.39/0.56        | (r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_H)
% 0.39/0.56        | (v2_struct_0 @ sk_D_1)
% 0.39/0.56        | (v2_struct_0 @ sk_B))),
% 0.39/0.56      inference('demod', [status(thm)], ['108', '113'])).
% 0.39/0.56  thf('115', plain,
% 0.39/0.56      ((~ (r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_G))
% 0.39/0.56         <= (~ ((r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_G)))),
% 0.39/0.56      inference('split', [status(esa)], ['68'])).
% 0.39/0.56  thf('116', plain, (((sk_G) = (sk_H))),
% 0.39/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.56  thf('117', plain,
% 0.39/0.56      ((~ (r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_H))
% 0.39/0.56         <= (~ ((r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_G)))),
% 0.39/0.56      inference('demod', [status(thm)], ['115', '116'])).
% 0.39/0.56  thf('118', plain,
% 0.39/0.56      (((r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_G))
% 0.39/0.56         <= (((r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_G)))),
% 0.39/0.56      inference('split', [status(esa)], ['16'])).
% 0.39/0.56  thf('119', plain, (((sk_G) = (sk_H))),
% 0.39/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.56  thf('120', plain,
% 0.39/0.56      (((r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_H))
% 0.39/0.56         <= (((r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_G)))),
% 0.39/0.56      inference('demod', [status(thm)], ['118', '119'])).
% 0.39/0.56  thf('121', plain,
% 0.39/0.56      ((~ (r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_H))
% 0.39/0.56         <= (~ ((r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_H)))),
% 0.39/0.56      inference('split', [status(esa)], ['40'])).
% 0.39/0.56  thf('122', plain,
% 0.39/0.56      (~ ((r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_G)) | 
% 0.39/0.56       ((r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_H))),
% 0.39/0.56      inference('sup-', [status(thm)], ['120', '121'])).
% 0.39/0.56  thf('123', plain, (~ ((r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_G))),
% 0.39/0.56      inference('sat_resolution*', [status(thm)], ['41', '78', '122'])).
% 0.39/0.56  thf('124', plain, (~ (r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_H)),
% 0.39/0.56      inference('simpl_trail', [status(thm)], ['117', '123'])).
% 0.39/0.56  thf('125', plain,
% 0.39/0.56      (((v2_struct_0 @ sk_B)
% 0.39/0.56        | (v2_struct_0 @ sk_D_1)
% 0.39/0.56        | (v2_struct_0 @ sk_C)
% 0.39/0.56        | (v2_struct_0 @ sk_A))),
% 0.39/0.56      inference('sup-', [status(thm)], ['114', '124'])).
% 0.39/0.56  thf('126', plain, (~ (v2_struct_0 @ sk_D_1)),
% 0.39/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.56  thf('127', plain,
% 0.39/0.56      (((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_B))),
% 0.39/0.56      inference('sup-', [status(thm)], ['125', '126'])).
% 0.39/0.56  thf('128', plain, (~ (v2_struct_0 @ sk_A)),
% 0.39/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.56  thf('129', plain, (((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_C))),
% 0.39/0.56      inference('clc', [status(thm)], ['127', '128'])).
% 0.39/0.56  thf('130', plain, (~ (v2_struct_0 @ sk_B)),
% 0.39/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.56  thf('131', plain, ((v2_struct_0 @ sk_C)),
% 0.39/0.56      inference('clc', [status(thm)], ['129', '130'])).
% 0.39/0.56  thf('132', plain, ($false), inference('demod', [status(thm)], ['0', '131'])).
% 0.39/0.56  
% 0.39/0.56  % SZS output end Refutation
% 0.39/0.56  
% 0.39/0.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
