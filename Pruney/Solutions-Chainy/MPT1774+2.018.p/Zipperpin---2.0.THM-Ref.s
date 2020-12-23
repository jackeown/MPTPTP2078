%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.NAqiuFETSQ

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:10:20 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  156 ( 417 expanded)
%              Number of leaves         :   31 ( 129 expanded)
%              Depth                    :   26
%              Number of atoms          : 1976 (17540 expanded)
%              Number of equality atoms :   14 ( 198 expanded)
%              Maximal formula depth    :   33 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_G_type,type,(
    sk_G: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_H_type,type,(
    sk_H: $i )).

thf(r1_tmap_1_type,type,(
    r1_tmap_1: $i > $i > $i > $i > $o )).

thf(k3_tmap_1_type,type,(
    k3_tmap_1: $i > $i > $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

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
    ~ ( v2_struct_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('1',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('2',plain,(
    r1_tarski @ sk_F @ ( u1_struct_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_C_1 ) )
      | ~ ( r2_hidden @ X0 @ sk_F ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_F @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_F ) @ ( u1_struct_0 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf('6',plain,(
    m1_pre_topc @ sk_D @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    m1_pre_topc @ sk_C_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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

thf('8',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( m1_pre_topc @ X11 @ X12 )
      | ~ ( m1_pre_topc @ X11 @ X13 )
      | ( r1_tarski @ ( u1_struct_0 @ X11 ) @ ( u1_struct_0 @ X13 ) )
      | ~ ( m1_pre_topc @ X13 @ X12 )
      | ~ ( l1_pre_topc @ X12 )
      | ~ ( v2_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[t4_tsep_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ( r1_tarski @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ sk_C_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_B )
      | ( r1_tarski @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ sk_C_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['9','10','11'])).

thf('13',plain,
    ( ~ ( m1_pre_topc @ sk_C_1 @ sk_D )
    | ( r1_tarski @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['6','12'])).

thf('14',plain,(
    m1_pre_topc @ sk_C_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_D ) )
      | ~ ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_F @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_F ) @ ( u1_struct_0 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['5','17'])).

thf('19',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('20',plain,
    ( ( r1_tarski @ sk_F @ ( u1_struct_0 @ sk_D ) )
    | ( r1_tarski @ sk_F @ ( u1_struct_0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    r1_tarski @ sk_F @ ( u1_struct_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['20'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('22',plain,(
    ! [X4: $i,X6: $i] :
      ( ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X6 ) )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('23',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,
    ( ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E ) @ sk_H )
    | ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E ) @ sk_H )
   <= ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E ) @ sk_H ) ),
    inference(split,[status(esa)],['24'])).

thf('26',plain,
    ( ~ ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E ) @ sk_H )
    | ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    sk_G = sk_H ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( ~ ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E ) @ sk_H )
    | ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,
    ( ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H )
    | ~ ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E ) @ sk_H ) ),
    inference(split,[status(esa)],['28'])).

thf('30',plain,(
    m1_pre_topc @ sk_C_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    m1_subset_1 @ sk_H @ ( u1_struct_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E ) @ sk_H )
    | ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    sk_G = sk_H ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E ) @ sk_H )
    | ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,
    ( ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H )
   <= ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H ) ),
    inference(split,[status(esa)],['34'])).

thf('36',plain,(
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

thf('37',plain,(
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

thf('38',plain,(
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
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,(
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
    inference('sup-',[status(thm)],['36','38'])).

thf('40',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
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
    inference(demod,[status(thm)],['39','40','41','42','43'])).

thf('45',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( v2_struct_0 @ X0 )
        | ~ ( v2_pre_topc @ X0 )
        | ~ ( l1_pre_topc @ X0 )
        | ( v2_struct_0 @ sk_D )
        | ~ ( m1_pre_topc @ sk_D @ X0 )
        | ~ ( m1_subset_1 @ sk_H @ ( u1_struct_0 @ X1 ) )
        | ( r1_tmap_1 @ X1 @ sk_A @ ( k3_tmap_1 @ X0 @ sk_A @ sk_D @ X1 @ sk_E ) @ sk_H )
        | ~ ( m1_pre_topc @ X1 @ sk_D )
        | ~ ( m1_subset_1 @ sk_H @ ( u1_struct_0 @ sk_D ) )
        | ~ ( m1_pre_topc @ X1 @ X0 )
        | ( v2_struct_0 @ X1 )
        | ( v2_struct_0 @ sk_A ) )
   <= ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H ) ),
    inference('sup-',[status(thm)],['35','44'])).

thf('46',plain,(
    m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    sk_G = sk_H ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    m1_subset_1 @ sk_H @ ( u1_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( v2_struct_0 @ X0 )
        | ~ ( v2_pre_topc @ X0 )
        | ~ ( l1_pre_topc @ X0 )
        | ( v2_struct_0 @ sk_D )
        | ~ ( m1_pre_topc @ sk_D @ X0 )
        | ~ ( m1_subset_1 @ sk_H @ ( u1_struct_0 @ X1 ) )
        | ( r1_tmap_1 @ X1 @ sk_A @ ( k3_tmap_1 @ X0 @ sk_A @ sk_D @ X1 @ sk_E ) @ sk_H )
        | ~ ( m1_pre_topc @ X1 @ sk_D )
        | ~ ( m1_pre_topc @ X1 @ X0 )
        | ( v2_struct_0 @ X1 )
        | ( v2_struct_0 @ sk_A ) )
   <= ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H ) ),
    inference(demod,[status(thm)],['45','48'])).

thf('50',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ sk_C_1 )
        | ~ ( m1_pre_topc @ sk_C_1 @ X0 )
        | ~ ( m1_pre_topc @ sk_C_1 @ sk_D )
        | ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ X0 @ sk_A @ sk_D @ sk_C_1 @ sk_E ) @ sk_H )
        | ~ ( m1_pre_topc @ sk_D @ X0 )
        | ( v2_struct_0 @ sk_D )
        | ~ ( l1_pre_topc @ X0 )
        | ~ ( v2_pre_topc @ X0 )
        | ( v2_struct_0 @ X0 ) )
   <= ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H ) ),
    inference('sup-',[status(thm)],['31','49'])).

thf('51',plain,(
    m1_pre_topc @ sk_C_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ sk_C_1 )
        | ~ ( m1_pre_topc @ sk_C_1 @ X0 )
        | ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ X0 @ sk_A @ sk_D @ sk_C_1 @ sk_E ) @ sk_H )
        | ~ ( m1_pre_topc @ sk_D @ X0 )
        | ( v2_struct_0 @ sk_D )
        | ~ ( l1_pre_topc @ X0 )
        | ~ ( v2_pre_topc @ X0 )
        | ( v2_struct_0 @ X0 ) )
   <= ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ~ ( m1_pre_topc @ sk_D @ sk_B )
      | ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E ) @ sk_H )
      | ( v2_struct_0 @ sk_C_1 )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H ) ),
    inference('sup-',[status(thm)],['30','52'])).

thf('54',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    m1_pre_topc @ sk_D @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E ) @ sk_H )
      | ( v2_struct_0 @ sk_C_1 )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H ) ),
    inference(demod,[status(thm)],['53','54','55','56'])).

thf('58',plain,
    ( ~ ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E ) @ sk_H )
    | ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,
    ( ~ ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E ) @ sk_H )
   <= ~ ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E ) @ sk_H ) ),
    inference(split,[status(esa)],['58'])).

thf('60',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C_1 )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ~ ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E ) @ sk_H )
      & ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H ) ) ),
    inference('sup-',[status(thm)],['57','59'])).

thf('61',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_C_1 ) )
   <= ( ~ ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E ) @ sk_H )
      & ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,
    ( ( ( v2_struct_0 @ sk_C_1 )
      | ( v2_struct_0 @ sk_D ) )
   <= ( ~ ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E ) @ sk_H )
      & ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H ) ) ),
    inference(clc,[status(thm)],['62','63'])).

thf('65',plain,(
    ~ ( v2_struct_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,
    ( ( v2_struct_0 @ sk_D )
   <= ( ~ ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E ) @ sk_H )
      & ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H ) ) ),
    inference(clc,[status(thm)],['64','65'])).

thf('67',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,
    ( ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E ) @ sk_H )
    | ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,
    ( ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E ) @ sk_H )
    | ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H ) ),
    inference(split,[status(esa)],['34'])).

thf('70',plain,(
    r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E ) @ sk_H ),
    inference('sat_resolution*',[status(thm)],['29','68','69'])).

thf('71',plain,(
    r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E ) @ sk_H ),
    inference(simpl_trail,[status(thm)],['25','70'])).

thf('72',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) ) ) ),
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

thf('73',plain,(
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
      | ~ ( r1_tarski @ X28 @ ( u1_struct_0 @ X27 ) )
      | ~ ( r2_hidden @ X31 @ X28 )
      | ~ ( v3_pre_topc @ X28 @ X25 )
      | ~ ( m1_subset_1 @ X31 @ ( u1_struct_0 @ X25 ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X25 ) @ ( u1_struct_0 @ X24 ) ) ) )
      | ~ ( v1_funct_2 @ X30 @ ( u1_struct_0 @ X25 ) @ ( u1_struct_0 @ X24 ) )
      | ~ ( v1_funct_1 @ X30 )
      | ~ ( m1_pre_topc @ X27 @ X26 )
      | ( v2_struct_0 @ X27 )
      | ~ ( l1_pre_topc @ X26 )
      | ~ ( v2_pre_topc @ X26 )
      | ( v2_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t84_tmap_1])).

thf('74',plain,(
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
      | ~ ( v3_pre_topc @ X28 @ X25 )
      | ~ ( r2_hidden @ X29 @ X28 )
      | ~ ( r1_tarski @ X28 @ ( u1_struct_0 @ X27 ) )
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
    inference(simplify,[status(thm)],['73'])).

thf('75',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ~ ( m1_pre_topc @ X1 @ sk_D )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X1 ) )
      | ~ ( r1_tmap_1 @ X1 @ sk_A @ ( k3_tmap_1 @ X0 @ sk_A @ sk_D @ X1 @ sk_E ) @ X3 )
      | ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ X3 )
      | ~ ( r1_tarski @ X2 @ ( u1_struct_0 @ X1 ) )
      | ~ ( r2_hidden @ X3 @ X2 )
      | ~ ( v3_pre_topc @ X2 @ sk_D )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ sk_D ) )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ( v2_struct_0 @ X1 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['72','74'])).

thf('76',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ~ ( m1_pre_topc @ X1 @ sk_D )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X1 ) )
      | ~ ( r1_tmap_1 @ X1 @ sk_A @ ( k3_tmap_1 @ X0 @ sk_A @ sk_D @ X1 @ sk_E ) @ X3 )
      | ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ X3 )
      | ~ ( r1_tarski @ X2 @ ( u1_struct_0 @ X1 ) )
      | ~ ( r2_hidden @ X3 @ X2 )
      | ~ ( v3_pre_topc @ X2 @ sk_D )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ sk_D ) )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ( v2_struct_0 @ X1 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['75','76','77','78','79'])).

thf('81',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ( v2_struct_0 @ sk_C_1 )
      | ~ ( m1_pre_topc @ sk_C_1 @ sk_B )
      | ~ ( m1_subset_1 @ sk_H @ ( u1_struct_0 @ sk_D ) )
      | ~ ( v3_pre_topc @ X0 @ sk_D )
      | ~ ( r2_hidden @ sk_H @ X0 )
      | ~ ( r1_tarski @ X0 @ ( u1_struct_0 @ sk_C_1 ) )
      | ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H )
      | ~ ( m1_subset_1 @ sk_H @ ( u1_struct_0 @ sk_C_1 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) )
      | ~ ( m1_pre_topc @ sk_C_1 @ sk_D )
      | ~ ( m1_pre_topc @ sk_D @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['71','80'])).

thf('82',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    m1_pre_topc @ sk_C_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    m1_subset_1 @ sk_H @ ( u1_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('86',plain,(
    m1_subset_1 @ sk_H @ ( u1_struct_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    m1_pre_topc @ sk_C_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    m1_pre_topc @ sk_D @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_C_1 )
      | ~ ( v3_pre_topc @ X0 @ sk_D )
      | ~ ( r2_hidden @ sk_H @ X0 )
      | ~ ( r1_tarski @ X0 @ ( u1_struct_0 @ sk_C_1 ) )
      | ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['81','82','83','84','85','86','87','88'])).

thf('90',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D )
    | ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H )
    | ~ ( r1_tarski @ sk_F @ ( u1_struct_0 @ sk_C_1 ) )
    | ~ ( r2_hidden @ sk_H @ sk_F )
    | ~ ( v3_pre_topc @ sk_F @ sk_D )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['23','89'])).

thf('91',plain,(
    r1_tarski @ sk_F @ ( u1_struct_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    r2_hidden @ sk_G @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    sk_G = sk_H ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    r2_hidden @ sk_H @ sk_F ),
    inference(demod,[status(thm)],['92','93'])).

thf('95',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

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

thf('97',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ~ ( v3_pre_topc @ X7 @ X8 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ( v3_pre_topc @ X9 @ X10 )
      | ( X9 != X7 )
      | ~ ( m1_pre_topc @ X10 @ X8 )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[t33_tops_2])).

thf('98',plain,(
    ! [X7: $i,X8: $i,X10: $i] :
      ( ~ ( l1_pre_topc @ X8 )
      | ~ ( m1_pre_topc @ X10 @ X8 )
      | ( v3_pre_topc @ X7 @ X10 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ~ ( v3_pre_topc @ X7 @ X8 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) ) ) ),
    inference(simplify,[status(thm)],['97'])).

thf('99',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( v3_pre_topc @ sk_F @ X0 )
      | ( v3_pre_topc @ sk_F @ sk_D )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['96','98'])).

thf('100',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ~ ( m1_pre_topc @ sk_D @ sk_B )
    | ( v3_pre_topc @ sk_F @ sk_D )
    | ~ ( v3_pre_topc @ sk_F @ sk_B ) ),
    inference('sup-',[status(thm)],['95','99'])).

thf('101',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    m1_pre_topc @ sk_D @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,(
    v3_pre_topc @ sk_F @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,(
    v3_pre_topc @ sk_F @ sk_D ),
    inference(demod,[status(thm)],['100','101','102','103'])).

thf('105',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D )
    | ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['90','91','94','104'])).

thf('106',plain,
    ( ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G )
   <= ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G ) ),
    inference(split,[status(esa)],['58'])).

thf('107',plain,(
    sk_G = sk_H ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,
    ( ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H )
   <= ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G ) ),
    inference(demod,[status(thm)],['106','107'])).

thf('109',plain,
    ( ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G )
   <= ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G ) ),
    inference(split,[status(esa)],['24'])).

thf('110',plain,(
    sk_G = sk_H ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,
    ( ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H )
   <= ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G ) ),
    inference(demod,[status(thm)],['109','110'])).

thf('112',plain,
    ( ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H )
   <= ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H ) ),
    inference(split,[status(esa)],['28'])).

thf('113',plain,
    ( ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G )
    | ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H ) ),
    inference('sup-',[status(thm)],['111','112'])).

thf('114',plain,(
    ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G ) ),
    inference('sat_resolution*',[status(thm)],['29','68','113'])).

thf('115',plain,(
    ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H ) ),
    inference(simpl_trail,[status(thm)],['108','114'])).

thf('116',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['105','115'])).

thf('117',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['116','117'])).

thf('119',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C_1 ) ),
    inference(clc,[status(thm)],['118','119'])).

thf('121',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,(
    v2_struct_0 @ sk_C_1 ),
    inference(clc,[status(thm)],['120','121'])).

thf('123',plain,(
    $false ),
    inference(demod,[status(thm)],['0','122'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.NAqiuFETSQ
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:34:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.59  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.59  % Solved by: fo/fo7.sh
% 0.20/0.59  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.59  % done 132 iterations in 0.113s
% 0.20/0.59  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.59  % SZS output start Refutation
% 0.20/0.59  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.59  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.59  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.59  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.20/0.59  thf(sk_G_type, type, sk_G: $i).
% 0.20/0.59  thf(sk_D_type, type, sk_D: $i).
% 0.20/0.59  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.59  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.20/0.59  thf(sk_H_type, type, sk_H: $i).
% 0.20/0.59  thf(r1_tmap_1_type, type, r1_tmap_1: $i > $i > $i > $i > $o).
% 0.20/0.59  thf(k3_tmap_1_type, type, k3_tmap_1: $i > $i > $i > $i > $i > $i).
% 0.20/0.59  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.59  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.59  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.20/0.59  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.59  thf(sk_E_type, type, sk_E: $i).
% 0.20/0.59  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.20/0.59  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.20/0.59  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.59  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.20/0.59  thf(sk_F_type, type, sk_F: $i).
% 0.20/0.59  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.20/0.59  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.20/0.59  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.20/0.59  thf(t85_tmap_1, conjecture,
% 0.20/0.59    (![A:$i]:
% 0.20/0.59     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.59       ( ![B:$i]:
% 0.20/0.59         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.20/0.59             ( l1_pre_topc @ B ) ) =>
% 0.20/0.59           ( ![C:$i]:
% 0.20/0.59             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ B ) ) =>
% 0.20/0.59               ( ![D:$i]:
% 0.20/0.59                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ B ) ) =>
% 0.20/0.59                   ( ![E:$i]:
% 0.20/0.59                     ( ( ( v1_funct_1 @ E ) & 
% 0.20/0.59                         ( v1_funct_2 @
% 0.20/0.59                           E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ A ) ) & 
% 0.20/0.59                         ( m1_subset_1 @
% 0.20/0.59                           E @ 
% 0.20/0.59                           ( k1_zfmisc_1 @
% 0.20/0.59                             ( k2_zfmisc_1 @
% 0.20/0.59                               ( u1_struct_0 @ D ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.20/0.59                       ( ( m1_pre_topc @ C @ D ) =>
% 0.20/0.59                         ( ![F:$i]:
% 0.20/0.59                           ( ( m1_subset_1 @
% 0.20/0.59                               F @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.20/0.59                             ( ![G:$i]:
% 0.20/0.59                               ( ( m1_subset_1 @ G @ ( u1_struct_0 @ D ) ) =>
% 0.20/0.59                                 ( ![H:$i]:
% 0.20/0.59                                   ( ( m1_subset_1 @ H @ ( u1_struct_0 @ C ) ) =>
% 0.20/0.59                                     ( ( ( v3_pre_topc @ F @ B ) & 
% 0.20/0.59                                         ( r2_hidden @ G @ F ) & 
% 0.20/0.59                                         ( r1_tarski @ F @ ( u1_struct_0 @ C ) ) & 
% 0.20/0.59                                         ( ( G ) = ( H ) ) ) =>
% 0.20/0.59                                       ( ( r1_tmap_1 @ D @ A @ E @ G ) <=>
% 0.20/0.59                                         ( r1_tmap_1 @
% 0.20/0.59                                           C @ A @ 
% 0.20/0.59                                           ( k3_tmap_1 @ B @ A @ D @ C @ E ) @ 
% 0.20/0.59                                           H ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.59  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.59    (~( ![A:$i]:
% 0.20/0.59        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.20/0.59            ( l1_pre_topc @ A ) ) =>
% 0.20/0.59          ( ![B:$i]:
% 0.20/0.59            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.20/0.59                ( l1_pre_topc @ B ) ) =>
% 0.20/0.59              ( ![C:$i]:
% 0.20/0.59                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ B ) ) =>
% 0.20/0.59                  ( ![D:$i]:
% 0.20/0.59                    ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ B ) ) =>
% 0.20/0.59                      ( ![E:$i]:
% 0.20/0.59                        ( ( ( v1_funct_1 @ E ) & 
% 0.20/0.59                            ( v1_funct_2 @
% 0.20/0.59                              E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ A ) ) & 
% 0.20/0.59                            ( m1_subset_1 @
% 0.20/0.59                              E @ 
% 0.20/0.59                              ( k1_zfmisc_1 @
% 0.20/0.59                                ( k2_zfmisc_1 @
% 0.20/0.59                                  ( u1_struct_0 @ D ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.20/0.59                          ( ( m1_pre_topc @ C @ D ) =>
% 0.20/0.59                            ( ![F:$i]:
% 0.20/0.59                              ( ( m1_subset_1 @
% 0.20/0.59                                  F @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.20/0.59                                ( ![G:$i]:
% 0.20/0.59                                  ( ( m1_subset_1 @ G @ ( u1_struct_0 @ D ) ) =>
% 0.20/0.59                                    ( ![H:$i]:
% 0.20/0.59                                      ( ( m1_subset_1 @ H @ ( u1_struct_0 @ C ) ) =>
% 0.20/0.59                                        ( ( ( v3_pre_topc @ F @ B ) & 
% 0.20/0.59                                            ( r2_hidden @ G @ F ) & 
% 0.20/0.59                                            ( r1_tarski @
% 0.20/0.59                                              F @ ( u1_struct_0 @ C ) ) & 
% 0.20/0.59                                            ( ( G ) = ( H ) ) ) =>
% 0.20/0.59                                          ( ( r1_tmap_1 @ D @ A @ E @ G ) <=>
% 0.20/0.59                                            ( r1_tmap_1 @
% 0.20/0.59                                              C @ A @ 
% 0.20/0.59                                              ( k3_tmap_1 @ B @ A @ D @ C @ E ) @ 
% 0.20/0.59                                              H ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.20/0.59    inference('cnf.neg', [status(esa)], [t85_tmap_1])).
% 0.20/0.59  thf('0', plain, (~ (v2_struct_0 @ sk_C_1)),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf(d3_tarski, axiom,
% 0.20/0.59    (![A:$i,B:$i]:
% 0.20/0.59     ( ( r1_tarski @ A @ B ) <=>
% 0.20/0.59       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.20/0.59  thf('1', plain,
% 0.20/0.59      (![X1 : $i, X3 : $i]:
% 0.20/0.59         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.20/0.59      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.59  thf('2', plain, ((r1_tarski @ sk_F @ (u1_struct_0 @ sk_C_1))),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('3', plain,
% 0.20/0.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.59         (~ (r2_hidden @ X0 @ X1)
% 0.20/0.59          | (r2_hidden @ X0 @ X2)
% 0.20/0.59          | ~ (r1_tarski @ X1 @ X2))),
% 0.20/0.59      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.59  thf('4', plain,
% 0.20/0.59      (![X0 : $i]:
% 0.20/0.59         ((r2_hidden @ X0 @ (u1_struct_0 @ sk_C_1)) | ~ (r2_hidden @ X0 @ sk_F))),
% 0.20/0.59      inference('sup-', [status(thm)], ['2', '3'])).
% 0.20/0.59  thf('5', plain,
% 0.20/0.59      (![X0 : $i]:
% 0.20/0.59         ((r1_tarski @ sk_F @ X0)
% 0.20/0.59          | (r2_hidden @ (sk_C @ X0 @ sk_F) @ (u1_struct_0 @ sk_C_1)))),
% 0.20/0.59      inference('sup-', [status(thm)], ['1', '4'])).
% 0.20/0.59  thf('6', plain, ((m1_pre_topc @ sk_D @ sk_B)),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('7', plain, ((m1_pre_topc @ sk_C_1 @ sk_B)),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf(t4_tsep_1, axiom,
% 0.20/0.59    (![A:$i]:
% 0.20/0.59     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.59       ( ![B:$i]:
% 0.20/0.59         ( ( m1_pre_topc @ B @ A ) =>
% 0.20/0.59           ( ![C:$i]:
% 0.20/0.59             ( ( m1_pre_topc @ C @ A ) =>
% 0.20/0.59               ( ( r1_tarski @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ C ) ) <=>
% 0.20/0.59                 ( m1_pre_topc @ B @ C ) ) ) ) ) ) ))).
% 0.20/0.59  thf('8', plain,
% 0.20/0.59      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.20/0.59         (~ (m1_pre_topc @ X11 @ X12)
% 0.20/0.59          | ~ (m1_pre_topc @ X11 @ X13)
% 0.20/0.59          | (r1_tarski @ (u1_struct_0 @ X11) @ (u1_struct_0 @ X13))
% 0.20/0.59          | ~ (m1_pre_topc @ X13 @ X12)
% 0.20/0.59          | ~ (l1_pre_topc @ X12)
% 0.20/0.59          | ~ (v2_pre_topc @ X12))),
% 0.20/0.59      inference('cnf', [status(esa)], [t4_tsep_1])).
% 0.20/0.59  thf('9', plain,
% 0.20/0.59      (![X0 : $i]:
% 0.20/0.59         (~ (v2_pre_topc @ sk_B)
% 0.20/0.59          | ~ (l1_pre_topc @ sk_B)
% 0.20/0.59          | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.20/0.59          | (r1_tarski @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ X0))
% 0.20/0.59          | ~ (m1_pre_topc @ sk_C_1 @ X0))),
% 0.20/0.59      inference('sup-', [status(thm)], ['7', '8'])).
% 0.20/0.59  thf('10', plain, ((v2_pre_topc @ sk_B)),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('11', plain, ((l1_pre_topc @ sk_B)),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('12', plain,
% 0.20/0.59      (![X0 : $i]:
% 0.20/0.59         (~ (m1_pre_topc @ X0 @ sk_B)
% 0.20/0.59          | (r1_tarski @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ X0))
% 0.20/0.59          | ~ (m1_pre_topc @ sk_C_1 @ X0))),
% 0.20/0.59      inference('demod', [status(thm)], ['9', '10', '11'])).
% 0.20/0.59  thf('13', plain,
% 0.20/0.59      ((~ (m1_pre_topc @ sk_C_1 @ sk_D)
% 0.20/0.59        | (r1_tarski @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_D)))),
% 0.20/0.59      inference('sup-', [status(thm)], ['6', '12'])).
% 0.20/0.59  thf('14', plain, ((m1_pre_topc @ sk_C_1 @ sk_D)),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('15', plain,
% 0.20/0.59      ((r1_tarski @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_D))),
% 0.20/0.59      inference('demod', [status(thm)], ['13', '14'])).
% 0.20/0.59  thf('16', plain,
% 0.20/0.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.59         (~ (r2_hidden @ X0 @ X1)
% 0.20/0.59          | (r2_hidden @ X0 @ X2)
% 0.20/0.59          | ~ (r1_tarski @ X1 @ X2))),
% 0.20/0.59      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.59  thf('17', plain,
% 0.20/0.59      (![X0 : $i]:
% 0.20/0.59         ((r2_hidden @ X0 @ (u1_struct_0 @ sk_D))
% 0.20/0.59          | ~ (r2_hidden @ X0 @ (u1_struct_0 @ sk_C_1)))),
% 0.20/0.59      inference('sup-', [status(thm)], ['15', '16'])).
% 0.20/0.59  thf('18', plain,
% 0.20/0.59      (![X0 : $i]:
% 0.20/0.59         ((r1_tarski @ sk_F @ X0)
% 0.20/0.59          | (r2_hidden @ (sk_C @ X0 @ sk_F) @ (u1_struct_0 @ sk_D)))),
% 0.20/0.59      inference('sup-', [status(thm)], ['5', '17'])).
% 0.20/0.59  thf('19', plain,
% 0.20/0.59      (![X1 : $i, X3 : $i]:
% 0.20/0.59         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.20/0.59      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.59  thf('20', plain,
% 0.20/0.59      (((r1_tarski @ sk_F @ (u1_struct_0 @ sk_D))
% 0.20/0.59        | (r1_tarski @ sk_F @ (u1_struct_0 @ sk_D)))),
% 0.20/0.59      inference('sup-', [status(thm)], ['18', '19'])).
% 0.20/0.59  thf('21', plain, ((r1_tarski @ sk_F @ (u1_struct_0 @ sk_D))),
% 0.20/0.59      inference('simplify', [status(thm)], ['20'])).
% 0.20/0.59  thf(t3_subset, axiom,
% 0.20/0.59    (![A:$i,B:$i]:
% 0.20/0.59     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.20/0.59  thf('22', plain,
% 0.20/0.59      (![X4 : $i, X6 : $i]:
% 0.20/0.59         ((m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X6)) | ~ (r1_tarski @ X4 @ X6))),
% 0.20/0.59      inference('cnf', [status(esa)], [t3_subset])).
% 0.20/0.59  thf('23', plain,
% 0.20/0.59      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))),
% 0.20/0.59      inference('sup-', [status(thm)], ['21', '22'])).
% 0.20/0.59  thf('24', plain,
% 0.20/0.59      (((r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.20/0.59         (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_H)
% 0.20/0.59        | (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G))),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('25', plain,
% 0.20/0.59      (((r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.20/0.59         (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_H))
% 0.20/0.59         <= (((r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.20/0.59               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_H)))),
% 0.20/0.59      inference('split', [status(esa)], ['24'])).
% 0.20/0.59  thf('26', plain,
% 0.20/0.59      ((~ (r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.20/0.59           (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_H)
% 0.20/0.59        | ~ (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G))),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('27', plain, (((sk_G) = (sk_H))),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('28', plain,
% 0.20/0.59      ((~ (r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.20/0.59           (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_H)
% 0.20/0.59        | ~ (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H))),
% 0.20/0.59      inference('demod', [status(thm)], ['26', '27'])).
% 0.20/0.59  thf('29', plain,
% 0.20/0.59      (~ ((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H)) | 
% 0.20/0.59       ~
% 0.20/0.59       ((r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.20/0.59         (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_H))),
% 0.20/0.59      inference('split', [status(esa)], ['28'])).
% 0.20/0.59  thf('30', plain, ((m1_pre_topc @ sk_C_1 @ sk_B)),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('31', plain, ((m1_subset_1 @ sk_H @ (u1_struct_0 @ sk_C_1))),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('32', plain,
% 0.20/0.59      (((r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.20/0.59         (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_H)
% 0.20/0.59        | (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G))),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('33', plain, (((sk_G) = (sk_H))),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('34', plain,
% 0.20/0.59      (((r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.20/0.59         (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_H)
% 0.20/0.59        | (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H))),
% 0.20/0.59      inference('demod', [status(thm)], ['32', '33'])).
% 0.20/0.59  thf('35', plain,
% 0.20/0.59      (((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H))
% 0.20/0.59         <= (((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H)))),
% 0.20/0.59      inference('split', [status(esa)], ['34'])).
% 0.20/0.59  thf('36', plain,
% 0.20/0.59      ((m1_subset_1 @ sk_E @ 
% 0.20/0.59        (k1_zfmisc_1 @ 
% 0.20/0.59         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A))))),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf(t81_tmap_1, axiom,
% 0.20/0.59    (![A:$i]:
% 0.20/0.59     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.59       ( ![B:$i]:
% 0.20/0.59         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.20/0.59             ( l1_pre_topc @ B ) ) =>
% 0.20/0.59           ( ![C:$i]:
% 0.20/0.59             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.20/0.59               ( ![D:$i]:
% 0.20/0.59                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.20/0.59                   ( ![E:$i]:
% 0.20/0.59                     ( ( ( v1_funct_1 @ E ) & 
% 0.20/0.59                         ( v1_funct_2 @
% 0.20/0.59                           E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 0.20/0.59                         ( m1_subset_1 @
% 0.20/0.59                           E @ 
% 0.20/0.59                           ( k1_zfmisc_1 @
% 0.20/0.59                             ( k2_zfmisc_1 @
% 0.20/0.59                               ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.20/0.59                       ( ![F:$i]:
% 0.20/0.59                         ( ( m1_subset_1 @ F @ ( u1_struct_0 @ C ) ) =>
% 0.20/0.59                           ( ![G:$i]:
% 0.20/0.59                             ( ( m1_subset_1 @ G @ ( u1_struct_0 @ D ) ) =>
% 0.20/0.59                               ( ( ( ( F ) = ( G ) ) & 
% 0.20/0.59                                   ( m1_pre_topc @ D @ C ) & 
% 0.20/0.59                                   ( r1_tmap_1 @ C @ B @ E @ F ) ) =>
% 0.20/0.59                                 ( r1_tmap_1 @
% 0.20/0.59                                   D @ B @ ( k3_tmap_1 @ A @ B @ C @ D @ E ) @ 
% 0.20/0.59                                   G ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.59  thf('37', plain,
% 0.20/0.59      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 0.20/0.59         ((v2_struct_0 @ X17)
% 0.20/0.59          | ~ (v2_pre_topc @ X17)
% 0.20/0.59          | ~ (l1_pre_topc @ X17)
% 0.20/0.59          | (v2_struct_0 @ X18)
% 0.20/0.59          | ~ (m1_pre_topc @ X18 @ X19)
% 0.20/0.59          | ~ (m1_subset_1 @ X20 @ (u1_struct_0 @ X21))
% 0.20/0.59          | ~ (m1_pre_topc @ X18 @ X21)
% 0.20/0.59          | ~ (r1_tmap_1 @ X21 @ X17 @ X22 @ X20)
% 0.20/0.59          | ((X20) != (X23))
% 0.20/0.59          | (r1_tmap_1 @ X18 @ X17 @ 
% 0.20/0.59             (k3_tmap_1 @ X19 @ X17 @ X21 @ X18 @ X22) @ X23)
% 0.20/0.59          | ~ (m1_subset_1 @ X23 @ (u1_struct_0 @ X18))
% 0.20/0.59          | ~ (m1_subset_1 @ X22 @ 
% 0.20/0.59               (k1_zfmisc_1 @ 
% 0.20/0.59                (k2_zfmisc_1 @ (u1_struct_0 @ X21) @ (u1_struct_0 @ X17))))
% 0.20/0.59          | ~ (v1_funct_2 @ X22 @ (u1_struct_0 @ X21) @ (u1_struct_0 @ X17))
% 0.20/0.59          | ~ (v1_funct_1 @ X22)
% 0.20/0.59          | ~ (m1_pre_topc @ X21 @ X19)
% 0.20/0.59          | (v2_struct_0 @ X21)
% 0.20/0.59          | ~ (l1_pre_topc @ X19)
% 0.20/0.59          | ~ (v2_pre_topc @ X19)
% 0.20/0.59          | (v2_struct_0 @ X19))),
% 0.20/0.59      inference('cnf', [status(esa)], [t81_tmap_1])).
% 0.20/0.59  thf('38', plain,
% 0.20/0.59      (![X17 : $i, X18 : $i, X19 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 0.20/0.59         ((v2_struct_0 @ X19)
% 0.20/0.59          | ~ (v2_pre_topc @ X19)
% 0.20/0.59          | ~ (l1_pre_topc @ X19)
% 0.20/0.59          | (v2_struct_0 @ X21)
% 0.20/0.59          | ~ (m1_pre_topc @ X21 @ X19)
% 0.20/0.59          | ~ (v1_funct_1 @ X22)
% 0.20/0.59          | ~ (v1_funct_2 @ X22 @ (u1_struct_0 @ X21) @ (u1_struct_0 @ X17))
% 0.20/0.59          | ~ (m1_subset_1 @ X22 @ 
% 0.20/0.59               (k1_zfmisc_1 @ 
% 0.20/0.59                (k2_zfmisc_1 @ (u1_struct_0 @ X21) @ (u1_struct_0 @ X17))))
% 0.20/0.59          | ~ (m1_subset_1 @ X23 @ (u1_struct_0 @ X18))
% 0.20/0.59          | (r1_tmap_1 @ X18 @ X17 @ 
% 0.20/0.59             (k3_tmap_1 @ X19 @ X17 @ X21 @ X18 @ X22) @ X23)
% 0.20/0.59          | ~ (r1_tmap_1 @ X21 @ X17 @ X22 @ X23)
% 0.20/0.59          | ~ (m1_pre_topc @ X18 @ X21)
% 0.20/0.59          | ~ (m1_subset_1 @ X23 @ (u1_struct_0 @ X21))
% 0.20/0.59          | ~ (m1_pre_topc @ X18 @ X19)
% 0.20/0.59          | (v2_struct_0 @ X18)
% 0.20/0.59          | ~ (l1_pre_topc @ X17)
% 0.20/0.59          | ~ (v2_pre_topc @ X17)
% 0.20/0.59          | (v2_struct_0 @ X17))),
% 0.20/0.59      inference('simplify', [status(thm)], ['37'])).
% 0.20/0.59  thf('39', plain,
% 0.20/0.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.59         ((v2_struct_0 @ sk_A)
% 0.20/0.59          | ~ (v2_pre_topc @ sk_A)
% 0.20/0.59          | ~ (l1_pre_topc @ sk_A)
% 0.20/0.59          | (v2_struct_0 @ X0)
% 0.20/0.59          | ~ (m1_pre_topc @ X0 @ X1)
% 0.20/0.59          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ sk_D))
% 0.20/0.59          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.20/0.59          | ~ (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ X2)
% 0.20/0.59          | (r1_tmap_1 @ X0 @ sk_A @ 
% 0.20/0.59             (k3_tmap_1 @ X1 @ sk_A @ sk_D @ X0 @ sk_E) @ X2)
% 0.20/0.59          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.20/0.59          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A))
% 0.20/0.59          | ~ (v1_funct_1 @ sk_E)
% 0.20/0.59          | ~ (m1_pre_topc @ sk_D @ X1)
% 0.20/0.59          | (v2_struct_0 @ sk_D)
% 0.20/0.59          | ~ (l1_pre_topc @ X1)
% 0.20/0.59          | ~ (v2_pre_topc @ X1)
% 0.20/0.59          | (v2_struct_0 @ X1))),
% 0.20/0.59      inference('sup-', [status(thm)], ['36', '38'])).
% 0.20/0.59  thf('40', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('41', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('42', plain,
% 0.20/0.59      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A))),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('43', plain, ((v1_funct_1 @ sk_E)),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('44', plain,
% 0.20/0.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.59         ((v2_struct_0 @ sk_A)
% 0.20/0.59          | (v2_struct_0 @ X0)
% 0.20/0.59          | ~ (m1_pre_topc @ X0 @ X1)
% 0.20/0.59          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ sk_D))
% 0.20/0.59          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.20/0.59          | ~ (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ X2)
% 0.20/0.59          | (r1_tmap_1 @ X0 @ sk_A @ 
% 0.20/0.59             (k3_tmap_1 @ X1 @ sk_A @ sk_D @ X0 @ sk_E) @ X2)
% 0.20/0.59          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.20/0.59          | ~ (m1_pre_topc @ sk_D @ X1)
% 0.20/0.59          | (v2_struct_0 @ sk_D)
% 0.20/0.59          | ~ (l1_pre_topc @ X1)
% 0.20/0.59          | ~ (v2_pre_topc @ X1)
% 0.20/0.59          | (v2_struct_0 @ X1))),
% 0.20/0.59      inference('demod', [status(thm)], ['39', '40', '41', '42', '43'])).
% 0.20/0.59  thf('45', plain,
% 0.20/0.59      ((![X0 : $i, X1 : $i]:
% 0.20/0.59          ((v2_struct_0 @ X0)
% 0.20/0.59           | ~ (v2_pre_topc @ X0)
% 0.20/0.59           | ~ (l1_pre_topc @ X0)
% 0.20/0.59           | (v2_struct_0 @ sk_D)
% 0.20/0.59           | ~ (m1_pre_topc @ sk_D @ X0)
% 0.20/0.59           | ~ (m1_subset_1 @ sk_H @ (u1_struct_0 @ X1))
% 0.20/0.59           | (r1_tmap_1 @ X1 @ sk_A @ 
% 0.20/0.59              (k3_tmap_1 @ X0 @ sk_A @ sk_D @ X1 @ sk_E) @ sk_H)
% 0.20/0.59           | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.20/0.59           | ~ (m1_subset_1 @ sk_H @ (u1_struct_0 @ sk_D))
% 0.20/0.59           | ~ (m1_pre_topc @ X1 @ X0)
% 0.20/0.59           | (v2_struct_0 @ X1)
% 0.20/0.59           | (v2_struct_0 @ sk_A)))
% 0.20/0.59         <= (((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H)))),
% 0.20/0.59      inference('sup-', [status(thm)], ['35', '44'])).
% 0.20/0.59  thf('46', plain, ((m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_D))),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('47', plain, (((sk_G) = (sk_H))),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('48', plain, ((m1_subset_1 @ sk_H @ (u1_struct_0 @ sk_D))),
% 0.20/0.59      inference('demod', [status(thm)], ['46', '47'])).
% 0.20/0.59  thf('49', plain,
% 0.20/0.59      ((![X0 : $i, X1 : $i]:
% 0.20/0.59          ((v2_struct_0 @ X0)
% 0.20/0.59           | ~ (v2_pre_topc @ X0)
% 0.20/0.59           | ~ (l1_pre_topc @ X0)
% 0.20/0.59           | (v2_struct_0 @ sk_D)
% 0.20/0.59           | ~ (m1_pre_topc @ sk_D @ X0)
% 0.20/0.59           | ~ (m1_subset_1 @ sk_H @ (u1_struct_0 @ X1))
% 0.20/0.59           | (r1_tmap_1 @ X1 @ sk_A @ 
% 0.20/0.59              (k3_tmap_1 @ X0 @ sk_A @ sk_D @ X1 @ sk_E) @ sk_H)
% 0.20/0.59           | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.20/0.59           | ~ (m1_pre_topc @ X1 @ X0)
% 0.20/0.59           | (v2_struct_0 @ X1)
% 0.20/0.59           | (v2_struct_0 @ sk_A)))
% 0.20/0.59         <= (((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H)))),
% 0.20/0.59      inference('demod', [status(thm)], ['45', '48'])).
% 0.20/0.59  thf('50', plain,
% 0.20/0.59      ((![X0 : $i]:
% 0.20/0.59          ((v2_struct_0 @ sk_A)
% 0.20/0.59           | (v2_struct_0 @ sk_C_1)
% 0.20/0.59           | ~ (m1_pre_topc @ sk_C_1 @ X0)
% 0.20/0.59           | ~ (m1_pre_topc @ sk_C_1 @ sk_D)
% 0.20/0.59           | (r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.20/0.59              (k3_tmap_1 @ X0 @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_H)
% 0.20/0.59           | ~ (m1_pre_topc @ sk_D @ X0)
% 0.20/0.59           | (v2_struct_0 @ sk_D)
% 0.20/0.59           | ~ (l1_pre_topc @ X0)
% 0.20/0.59           | ~ (v2_pre_topc @ X0)
% 0.20/0.59           | (v2_struct_0 @ X0)))
% 0.20/0.59         <= (((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H)))),
% 0.20/0.59      inference('sup-', [status(thm)], ['31', '49'])).
% 0.20/0.59  thf('51', plain, ((m1_pre_topc @ sk_C_1 @ sk_D)),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('52', plain,
% 0.20/0.59      ((![X0 : $i]:
% 0.20/0.59          ((v2_struct_0 @ sk_A)
% 0.20/0.59           | (v2_struct_0 @ sk_C_1)
% 0.20/0.59           | ~ (m1_pre_topc @ sk_C_1 @ X0)
% 0.20/0.59           | (r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.20/0.59              (k3_tmap_1 @ X0 @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_H)
% 0.20/0.59           | ~ (m1_pre_topc @ sk_D @ X0)
% 0.20/0.59           | (v2_struct_0 @ sk_D)
% 0.20/0.59           | ~ (l1_pre_topc @ X0)
% 0.20/0.59           | ~ (v2_pre_topc @ X0)
% 0.20/0.59           | (v2_struct_0 @ X0)))
% 0.20/0.59         <= (((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H)))),
% 0.20/0.59      inference('demod', [status(thm)], ['50', '51'])).
% 0.20/0.59  thf('53', plain,
% 0.20/0.59      ((((v2_struct_0 @ sk_B)
% 0.20/0.59         | ~ (v2_pre_topc @ sk_B)
% 0.20/0.59         | ~ (l1_pre_topc @ sk_B)
% 0.20/0.59         | (v2_struct_0 @ sk_D)
% 0.20/0.59         | ~ (m1_pre_topc @ sk_D @ sk_B)
% 0.20/0.59         | (r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.20/0.59            (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_H)
% 0.20/0.59         | (v2_struct_0 @ sk_C_1)
% 0.20/0.59         | (v2_struct_0 @ sk_A)))
% 0.20/0.59         <= (((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H)))),
% 0.20/0.59      inference('sup-', [status(thm)], ['30', '52'])).
% 0.20/0.59  thf('54', plain, ((v2_pre_topc @ sk_B)),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('55', plain, ((l1_pre_topc @ sk_B)),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('56', plain, ((m1_pre_topc @ sk_D @ sk_B)),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('57', plain,
% 0.20/0.59      ((((v2_struct_0 @ sk_B)
% 0.20/0.59         | (v2_struct_0 @ sk_D)
% 0.20/0.59         | (r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.20/0.59            (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_H)
% 0.20/0.59         | (v2_struct_0 @ sk_C_1)
% 0.20/0.59         | (v2_struct_0 @ sk_A)))
% 0.20/0.59         <= (((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H)))),
% 0.20/0.59      inference('demod', [status(thm)], ['53', '54', '55', '56'])).
% 0.20/0.59  thf('58', plain,
% 0.20/0.59      ((~ (r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.20/0.59           (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_H)
% 0.20/0.59        | ~ (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G))),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('59', plain,
% 0.20/0.59      ((~ (r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.20/0.59           (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_H))
% 0.20/0.59         <= (~
% 0.20/0.59             ((r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.20/0.59               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_H)))),
% 0.20/0.59      inference('split', [status(esa)], ['58'])).
% 0.20/0.59  thf('60', plain,
% 0.20/0.59      ((((v2_struct_0 @ sk_A)
% 0.20/0.59         | (v2_struct_0 @ sk_C_1)
% 0.20/0.59         | (v2_struct_0 @ sk_D)
% 0.20/0.59         | (v2_struct_0 @ sk_B)))
% 0.20/0.59         <= (~
% 0.20/0.59             ((r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.20/0.59               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_H)) & 
% 0.20/0.59             ((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H)))),
% 0.20/0.59      inference('sup-', [status(thm)], ['57', '59'])).
% 0.20/0.59  thf('61', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('62', plain,
% 0.20/0.59      ((((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_C_1)))
% 0.20/0.59         <= (~
% 0.20/0.59             ((r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.20/0.59               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_H)) & 
% 0.20/0.59             ((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H)))),
% 0.20/0.59      inference('sup-', [status(thm)], ['60', '61'])).
% 0.20/0.59  thf('63', plain, (~ (v2_struct_0 @ sk_B)),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('64', plain,
% 0.20/0.59      ((((v2_struct_0 @ sk_C_1) | (v2_struct_0 @ sk_D)))
% 0.20/0.59         <= (~
% 0.20/0.59             ((r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.20/0.59               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_H)) & 
% 0.20/0.59             ((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H)))),
% 0.20/0.59      inference('clc', [status(thm)], ['62', '63'])).
% 0.20/0.59  thf('65', plain, (~ (v2_struct_0 @ sk_C_1)),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('66', plain,
% 0.20/0.59      (((v2_struct_0 @ sk_D))
% 0.20/0.59         <= (~
% 0.20/0.59             ((r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.20/0.59               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_H)) & 
% 0.20/0.59             ((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H)))),
% 0.20/0.59      inference('clc', [status(thm)], ['64', '65'])).
% 0.20/0.59  thf('67', plain, (~ (v2_struct_0 @ sk_D)),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('68', plain,
% 0.20/0.59      (((r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.20/0.59         (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_H)) | 
% 0.20/0.59       ~ ((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H))),
% 0.20/0.59      inference('sup-', [status(thm)], ['66', '67'])).
% 0.20/0.59  thf('69', plain,
% 0.20/0.59      (((r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.20/0.59         (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_H)) | 
% 0.20/0.59       ((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H))),
% 0.20/0.59      inference('split', [status(esa)], ['34'])).
% 0.20/0.59  thf('70', plain,
% 0.20/0.59      (((r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.20/0.59         (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_H))),
% 0.20/0.59      inference('sat_resolution*', [status(thm)], ['29', '68', '69'])).
% 0.20/0.59  thf('71', plain,
% 0.20/0.59      ((r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.20/0.59        (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_H)),
% 0.20/0.59      inference('simpl_trail', [status(thm)], ['25', '70'])).
% 0.20/0.59  thf('72', plain,
% 0.20/0.59      ((m1_subset_1 @ sk_E @ 
% 0.20/0.59        (k1_zfmisc_1 @ 
% 0.20/0.59         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A))))),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf(t84_tmap_1, axiom,
% 0.20/0.59    (![A:$i]:
% 0.20/0.59     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.59       ( ![B:$i]:
% 0.20/0.59         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.20/0.59             ( l1_pre_topc @ B ) ) =>
% 0.20/0.59           ( ![C:$i]:
% 0.20/0.59             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.20/0.59               ( ![D:$i]:
% 0.20/0.59                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.20/0.59                   ( ![E:$i]:
% 0.20/0.59                     ( ( ( v1_funct_1 @ E ) & 
% 0.20/0.59                         ( v1_funct_2 @
% 0.20/0.59                           E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 0.20/0.59                         ( m1_subset_1 @
% 0.20/0.59                           E @ 
% 0.20/0.59                           ( k1_zfmisc_1 @
% 0.20/0.59                             ( k2_zfmisc_1 @
% 0.20/0.59                               ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.20/0.59                       ( ( m1_pre_topc @ C @ D ) =>
% 0.20/0.59                         ( ![F:$i]:
% 0.20/0.59                           ( ( m1_subset_1 @
% 0.20/0.59                               F @ ( k1_zfmisc_1 @ ( u1_struct_0 @ D ) ) ) =>
% 0.20/0.59                             ( ![G:$i]:
% 0.20/0.59                               ( ( m1_subset_1 @ G @ ( u1_struct_0 @ D ) ) =>
% 0.20/0.59                                 ( ![H:$i]:
% 0.20/0.59                                   ( ( m1_subset_1 @ H @ ( u1_struct_0 @ C ) ) =>
% 0.20/0.59                                     ( ( ( v3_pre_topc @ F @ D ) & 
% 0.20/0.59                                         ( r2_hidden @ G @ F ) & 
% 0.20/0.59                                         ( r1_tarski @ F @ ( u1_struct_0 @ C ) ) & 
% 0.20/0.59                                         ( ( G ) = ( H ) ) ) =>
% 0.20/0.59                                       ( ( r1_tmap_1 @ D @ B @ E @ G ) <=>
% 0.20/0.59                                         ( r1_tmap_1 @
% 0.20/0.59                                           C @ B @ 
% 0.20/0.59                                           ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ 
% 0.20/0.59                                           H ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.59  thf('73', plain,
% 0.20/0.59      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i, X30 : $i, 
% 0.20/0.59         X31 : $i]:
% 0.20/0.59         ((v2_struct_0 @ X24)
% 0.20/0.59          | ~ (v2_pre_topc @ X24)
% 0.20/0.59          | ~ (l1_pre_topc @ X24)
% 0.20/0.59          | (v2_struct_0 @ X25)
% 0.20/0.59          | ~ (m1_pre_topc @ X25 @ X26)
% 0.20/0.59          | ~ (m1_pre_topc @ X27 @ X25)
% 0.20/0.59          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 0.20/0.59          | ~ (m1_subset_1 @ X29 @ (u1_struct_0 @ X27))
% 0.20/0.59          | ~ (r1_tmap_1 @ X27 @ X24 @ 
% 0.20/0.59               (k3_tmap_1 @ X26 @ X24 @ X25 @ X27 @ X30) @ X29)
% 0.20/0.59          | (r1_tmap_1 @ X25 @ X24 @ X30 @ X31)
% 0.20/0.59          | ((X31) != (X29))
% 0.20/0.59          | ~ (r1_tarski @ X28 @ (u1_struct_0 @ X27))
% 0.20/0.59          | ~ (r2_hidden @ X31 @ X28)
% 0.20/0.59          | ~ (v3_pre_topc @ X28 @ X25)
% 0.20/0.59          | ~ (m1_subset_1 @ X31 @ (u1_struct_0 @ X25))
% 0.20/0.59          | ~ (m1_subset_1 @ X30 @ 
% 0.20/0.59               (k1_zfmisc_1 @ 
% 0.20/0.59                (k2_zfmisc_1 @ (u1_struct_0 @ X25) @ (u1_struct_0 @ X24))))
% 0.20/0.59          | ~ (v1_funct_2 @ X30 @ (u1_struct_0 @ X25) @ (u1_struct_0 @ X24))
% 0.20/0.59          | ~ (v1_funct_1 @ X30)
% 0.20/0.59          | ~ (m1_pre_topc @ X27 @ X26)
% 0.20/0.59          | (v2_struct_0 @ X27)
% 0.20/0.59          | ~ (l1_pre_topc @ X26)
% 0.20/0.59          | ~ (v2_pre_topc @ X26)
% 0.20/0.59          | (v2_struct_0 @ X26))),
% 0.20/0.59      inference('cnf', [status(esa)], [t84_tmap_1])).
% 0.20/0.59  thf('74', plain,
% 0.20/0.59      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 0.20/0.59         ((v2_struct_0 @ X26)
% 0.20/0.59          | ~ (v2_pre_topc @ X26)
% 0.20/0.59          | ~ (l1_pre_topc @ X26)
% 0.20/0.59          | (v2_struct_0 @ X27)
% 0.20/0.59          | ~ (m1_pre_topc @ X27 @ X26)
% 0.20/0.59          | ~ (v1_funct_1 @ X30)
% 0.20/0.59          | ~ (v1_funct_2 @ X30 @ (u1_struct_0 @ X25) @ (u1_struct_0 @ X24))
% 0.20/0.59          | ~ (m1_subset_1 @ X30 @ 
% 0.20/0.59               (k1_zfmisc_1 @ 
% 0.20/0.59                (k2_zfmisc_1 @ (u1_struct_0 @ X25) @ (u1_struct_0 @ X24))))
% 0.20/0.59          | ~ (m1_subset_1 @ X29 @ (u1_struct_0 @ X25))
% 0.20/0.59          | ~ (v3_pre_topc @ X28 @ X25)
% 0.20/0.59          | ~ (r2_hidden @ X29 @ X28)
% 0.20/0.59          | ~ (r1_tarski @ X28 @ (u1_struct_0 @ X27))
% 0.20/0.59          | (r1_tmap_1 @ X25 @ X24 @ X30 @ X29)
% 0.20/0.59          | ~ (r1_tmap_1 @ X27 @ X24 @ 
% 0.20/0.59               (k3_tmap_1 @ X26 @ X24 @ X25 @ X27 @ X30) @ X29)
% 0.20/0.59          | ~ (m1_subset_1 @ X29 @ (u1_struct_0 @ X27))
% 0.20/0.59          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 0.20/0.59          | ~ (m1_pre_topc @ X27 @ X25)
% 0.20/0.59          | ~ (m1_pre_topc @ X25 @ X26)
% 0.20/0.59          | (v2_struct_0 @ X25)
% 0.20/0.59          | ~ (l1_pre_topc @ X24)
% 0.20/0.59          | ~ (v2_pre_topc @ X24)
% 0.20/0.59          | (v2_struct_0 @ X24))),
% 0.20/0.59      inference('simplify', [status(thm)], ['73'])).
% 0.20/0.59  thf('75', plain,
% 0.20/0.59      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.59         ((v2_struct_0 @ sk_A)
% 0.20/0.59          | ~ (v2_pre_topc @ sk_A)
% 0.20/0.59          | ~ (l1_pre_topc @ sk_A)
% 0.20/0.59          | (v2_struct_0 @ sk_D)
% 0.20/0.59          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.20/0.59          | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.20/0.59          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))
% 0.20/0.59          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X1))
% 0.20/0.59          | ~ (r1_tmap_1 @ X1 @ sk_A @ 
% 0.20/0.59               (k3_tmap_1 @ X0 @ sk_A @ sk_D @ X1 @ sk_E) @ X3)
% 0.20/0.59          | (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ X3)
% 0.20/0.59          | ~ (r1_tarski @ X2 @ (u1_struct_0 @ X1))
% 0.20/0.59          | ~ (r2_hidden @ X3 @ X2)
% 0.20/0.59          | ~ (v3_pre_topc @ X2 @ sk_D)
% 0.20/0.59          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ sk_D))
% 0.20/0.59          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A))
% 0.20/0.59          | ~ (v1_funct_1 @ sk_E)
% 0.20/0.59          | ~ (m1_pre_topc @ X1 @ X0)
% 0.20/0.59          | (v2_struct_0 @ X1)
% 0.20/0.59          | ~ (l1_pre_topc @ X0)
% 0.20/0.59          | ~ (v2_pre_topc @ X0)
% 0.20/0.59          | (v2_struct_0 @ X0))),
% 0.20/0.59      inference('sup-', [status(thm)], ['72', '74'])).
% 0.20/0.59  thf('76', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('77', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('78', plain,
% 0.20/0.59      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A))),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('79', plain, ((v1_funct_1 @ sk_E)),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('80', plain,
% 0.20/0.59      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.59         ((v2_struct_0 @ sk_A)
% 0.20/0.59          | (v2_struct_0 @ sk_D)
% 0.20/0.59          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.20/0.59          | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.20/0.59          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))
% 0.20/0.59          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X1))
% 0.20/0.59          | ~ (r1_tmap_1 @ X1 @ sk_A @ 
% 0.20/0.59               (k3_tmap_1 @ X0 @ sk_A @ sk_D @ X1 @ sk_E) @ X3)
% 0.20/0.59          | (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ X3)
% 0.20/0.59          | ~ (r1_tarski @ X2 @ (u1_struct_0 @ X1))
% 0.20/0.59          | ~ (r2_hidden @ X3 @ X2)
% 0.20/0.59          | ~ (v3_pre_topc @ X2 @ sk_D)
% 0.20/0.59          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ sk_D))
% 0.20/0.59          | ~ (m1_pre_topc @ X1 @ X0)
% 0.20/0.59          | (v2_struct_0 @ X1)
% 0.20/0.59          | ~ (l1_pre_topc @ X0)
% 0.20/0.59          | ~ (v2_pre_topc @ X0)
% 0.20/0.59          | (v2_struct_0 @ X0))),
% 0.20/0.59      inference('demod', [status(thm)], ['75', '76', '77', '78', '79'])).
% 0.20/0.59  thf('81', plain,
% 0.20/0.59      (![X0 : $i]:
% 0.20/0.59         ((v2_struct_0 @ sk_B)
% 0.20/0.59          | ~ (v2_pre_topc @ sk_B)
% 0.20/0.59          | ~ (l1_pre_topc @ sk_B)
% 0.20/0.59          | (v2_struct_0 @ sk_C_1)
% 0.20/0.59          | ~ (m1_pre_topc @ sk_C_1 @ sk_B)
% 0.20/0.59          | ~ (m1_subset_1 @ sk_H @ (u1_struct_0 @ sk_D))
% 0.20/0.59          | ~ (v3_pre_topc @ X0 @ sk_D)
% 0.20/0.59          | ~ (r2_hidden @ sk_H @ X0)
% 0.20/0.59          | ~ (r1_tarski @ X0 @ (u1_struct_0 @ sk_C_1))
% 0.20/0.59          | (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H)
% 0.20/0.59          | ~ (m1_subset_1 @ sk_H @ (u1_struct_0 @ sk_C_1))
% 0.20/0.59          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))
% 0.20/0.59          | ~ (m1_pre_topc @ sk_C_1 @ sk_D)
% 0.20/0.59          | ~ (m1_pre_topc @ sk_D @ sk_B)
% 0.20/0.59          | (v2_struct_0 @ sk_D)
% 0.20/0.59          | (v2_struct_0 @ sk_A))),
% 0.20/0.59      inference('sup-', [status(thm)], ['71', '80'])).
% 0.20/0.59  thf('82', plain, ((v2_pre_topc @ sk_B)),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('83', plain, ((l1_pre_topc @ sk_B)),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('84', plain, ((m1_pre_topc @ sk_C_1 @ sk_B)),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('85', plain, ((m1_subset_1 @ sk_H @ (u1_struct_0 @ sk_D))),
% 0.20/0.59      inference('demod', [status(thm)], ['46', '47'])).
% 0.20/0.59  thf('86', plain, ((m1_subset_1 @ sk_H @ (u1_struct_0 @ sk_C_1))),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('87', plain, ((m1_pre_topc @ sk_C_1 @ sk_D)),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('88', plain, ((m1_pre_topc @ sk_D @ sk_B)),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('89', plain,
% 0.20/0.59      (![X0 : $i]:
% 0.20/0.59         ((v2_struct_0 @ sk_B)
% 0.20/0.59          | (v2_struct_0 @ sk_C_1)
% 0.20/0.59          | ~ (v3_pre_topc @ X0 @ sk_D)
% 0.20/0.59          | ~ (r2_hidden @ sk_H @ X0)
% 0.20/0.59          | ~ (r1_tarski @ X0 @ (u1_struct_0 @ sk_C_1))
% 0.20/0.59          | (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H)
% 0.20/0.59          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))
% 0.20/0.59          | (v2_struct_0 @ sk_D)
% 0.20/0.59          | (v2_struct_0 @ sk_A))),
% 0.20/0.59      inference('demod', [status(thm)],
% 0.20/0.59                ['81', '82', '83', '84', '85', '86', '87', '88'])).
% 0.20/0.59  thf('90', plain,
% 0.20/0.59      (((v2_struct_0 @ sk_A)
% 0.20/0.59        | (v2_struct_0 @ sk_D)
% 0.20/0.59        | (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H)
% 0.20/0.59        | ~ (r1_tarski @ sk_F @ (u1_struct_0 @ sk_C_1))
% 0.20/0.59        | ~ (r2_hidden @ sk_H @ sk_F)
% 0.20/0.59        | ~ (v3_pre_topc @ sk_F @ sk_D)
% 0.20/0.59        | (v2_struct_0 @ sk_C_1)
% 0.20/0.59        | (v2_struct_0 @ sk_B))),
% 0.20/0.59      inference('sup-', [status(thm)], ['23', '89'])).
% 0.20/0.59  thf('91', plain, ((r1_tarski @ sk_F @ (u1_struct_0 @ sk_C_1))),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('92', plain, ((r2_hidden @ sk_G @ sk_F)),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('93', plain, (((sk_G) = (sk_H))),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('94', plain, ((r2_hidden @ sk_H @ sk_F)),
% 0.20/0.59      inference('demod', [status(thm)], ['92', '93'])).
% 0.20/0.59  thf('95', plain,
% 0.20/0.59      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('96', plain,
% 0.20/0.59      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))),
% 0.20/0.59      inference('sup-', [status(thm)], ['21', '22'])).
% 0.20/0.59  thf(t33_tops_2, axiom,
% 0.20/0.59    (![A:$i]:
% 0.20/0.59     ( ( l1_pre_topc @ A ) =>
% 0.20/0.59       ( ![B:$i]:
% 0.20/0.59         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.59           ( ![C:$i]:
% 0.20/0.59             ( ( m1_pre_topc @ C @ A ) =>
% 0.20/0.59               ( ( v3_pre_topc @ B @ A ) =>
% 0.20/0.59                 ( ![D:$i]:
% 0.20/0.59                   ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ C ) ) ) =>
% 0.20/0.59                     ( ( ( D ) = ( B ) ) => ( v3_pre_topc @ D @ C ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.59  thf('97', plain,
% 0.20/0.59      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.20/0.59         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 0.20/0.59          | ~ (v3_pre_topc @ X7 @ X8)
% 0.20/0.59          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 0.20/0.59          | (v3_pre_topc @ X9 @ X10)
% 0.20/0.59          | ((X9) != (X7))
% 0.20/0.59          | ~ (m1_pre_topc @ X10 @ X8)
% 0.20/0.59          | ~ (l1_pre_topc @ X8))),
% 0.20/0.59      inference('cnf', [status(esa)], [t33_tops_2])).
% 0.20/0.59  thf('98', plain,
% 0.20/0.59      (![X7 : $i, X8 : $i, X10 : $i]:
% 0.20/0.59         (~ (l1_pre_topc @ X8)
% 0.20/0.59          | ~ (m1_pre_topc @ X10 @ X8)
% 0.20/0.59          | (v3_pre_topc @ X7 @ X10)
% 0.20/0.59          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 0.20/0.59          | ~ (v3_pre_topc @ X7 @ X8)
% 0.20/0.59          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (u1_struct_0 @ X8))))),
% 0.20/0.59      inference('simplify', [status(thm)], ['97'])).
% 0.20/0.59  thf('99', plain,
% 0.20/0.59      (![X0 : $i]:
% 0.20/0.59         (~ (m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.20/0.59          | ~ (v3_pre_topc @ sk_F @ X0)
% 0.20/0.59          | (v3_pre_topc @ sk_F @ sk_D)
% 0.20/0.59          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.20/0.59          | ~ (l1_pre_topc @ X0))),
% 0.20/0.59      inference('sup-', [status(thm)], ['96', '98'])).
% 0.20/0.59  thf('100', plain,
% 0.20/0.59      ((~ (l1_pre_topc @ sk_B)
% 0.20/0.59        | ~ (m1_pre_topc @ sk_D @ sk_B)
% 0.20/0.59        | (v3_pre_topc @ sk_F @ sk_D)
% 0.20/0.59        | ~ (v3_pre_topc @ sk_F @ sk_B))),
% 0.20/0.59      inference('sup-', [status(thm)], ['95', '99'])).
% 0.20/0.59  thf('101', plain, ((l1_pre_topc @ sk_B)),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('102', plain, ((m1_pre_topc @ sk_D @ sk_B)),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('103', plain, ((v3_pre_topc @ sk_F @ sk_B)),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('104', plain, ((v3_pre_topc @ sk_F @ sk_D)),
% 0.20/0.59      inference('demod', [status(thm)], ['100', '101', '102', '103'])).
% 0.20/0.59  thf('105', plain,
% 0.20/0.59      (((v2_struct_0 @ sk_A)
% 0.20/0.59        | (v2_struct_0 @ sk_D)
% 0.20/0.59        | (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H)
% 0.20/0.59        | (v2_struct_0 @ sk_C_1)
% 0.20/0.59        | (v2_struct_0 @ sk_B))),
% 0.20/0.59      inference('demod', [status(thm)], ['90', '91', '94', '104'])).
% 0.20/0.59  thf('106', plain,
% 0.20/0.59      ((~ (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G))
% 0.20/0.59         <= (~ ((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G)))),
% 0.20/0.59      inference('split', [status(esa)], ['58'])).
% 0.20/0.59  thf('107', plain, (((sk_G) = (sk_H))),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('108', plain,
% 0.20/0.59      ((~ (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H))
% 0.20/0.59         <= (~ ((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G)))),
% 0.20/0.59      inference('demod', [status(thm)], ['106', '107'])).
% 0.20/0.59  thf('109', plain,
% 0.20/0.59      (((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G))
% 0.20/0.59         <= (((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G)))),
% 0.20/0.59      inference('split', [status(esa)], ['24'])).
% 0.20/0.59  thf('110', plain, (((sk_G) = (sk_H))),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('111', plain,
% 0.20/0.59      (((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H))
% 0.20/0.59         <= (((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G)))),
% 0.20/0.59      inference('demod', [status(thm)], ['109', '110'])).
% 0.20/0.59  thf('112', plain,
% 0.20/0.59      ((~ (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H))
% 0.20/0.59         <= (~ ((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H)))),
% 0.20/0.59      inference('split', [status(esa)], ['28'])).
% 0.20/0.59  thf('113', plain,
% 0.20/0.59      (~ ((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G)) | 
% 0.20/0.59       ((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H))),
% 0.20/0.59      inference('sup-', [status(thm)], ['111', '112'])).
% 0.20/0.59  thf('114', plain, (~ ((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G))),
% 0.20/0.59      inference('sat_resolution*', [status(thm)], ['29', '68', '113'])).
% 0.20/0.59  thf('115', plain, (~ (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H)),
% 0.20/0.59      inference('simpl_trail', [status(thm)], ['108', '114'])).
% 0.20/0.59  thf('116', plain,
% 0.20/0.59      (((v2_struct_0 @ sk_B)
% 0.20/0.59        | (v2_struct_0 @ sk_C_1)
% 0.20/0.59        | (v2_struct_0 @ sk_D)
% 0.20/0.59        | (v2_struct_0 @ sk_A))),
% 0.20/0.59      inference('sup-', [status(thm)], ['105', '115'])).
% 0.20/0.59  thf('117', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('118', plain,
% 0.20/0.59      (((v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_C_1) | (v2_struct_0 @ sk_B))),
% 0.20/0.59      inference('sup-', [status(thm)], ['116', '117'])).
% 0.20/0.59  thf('119', plain, (~ (v2_struct_0 @ sk_D)),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('120', plain, (((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_C_1))),
% 0.20/0.59      inference('clc', [status(thm)], ['118', '119'])).
% 0.20/0.59  thf('121', plain, (~ (v2_struct_0 @ sk_B)),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('122', plain, ((v2_struct_0 @ sk_C_1)),
% 0.20/0.59      inference('clc', [status(thm)], ['120', '121'])).
% 0.20/0.59  thf('123', plain, ($false), inference('demod', [status(thm)], ['0', '122'])).
% 0.20/0.59  
% 0.20/0.59  % SZS output end Refutation
% 0.20/0.59  
% 0.20/0.60  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
