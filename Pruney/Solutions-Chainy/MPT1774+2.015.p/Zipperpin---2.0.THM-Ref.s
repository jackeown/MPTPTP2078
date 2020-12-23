%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.wLSyM22ByT

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:10:19 EST 2020

% Result     : Theorem 0.25s
% Output     : Refutation 0.25s
% Verified   : 
% Statistics : Number of formulae       :  166 ( 470 expanded)
%              Number of leaves         :   32 ( 144 expanded)
%              Depth                    :   26
%              Number of atoms          : 2137 (19380 expanded)
%              Number of equality atoms :   16 ( 218 expanded)
%              Maximal formula depth    :   33 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_H_type,type,(
    sk_H: $i )).

thf(r1_tmap_1_type,type,(
    r1_tmap_1: $i > $i > $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k3_tmap_1_type,type,(
    k3_tmap_1: $i > $i > $i > $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(sk_G_type,type,(
    sk_G: $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

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
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( m1_pre_topc @ X10 @ X11 )
      | ~ ( m1_pre_topc @ X10 @ X12 )
      | ( r1_tarski @ ( u1_struct_0 @ X10 ) @ ( u1_struct_0 @ X12 ) )
      | ~ ( m1_pre_topc @ X12 @ X11 )
      | ~ ( l1_pre_topc @ X11 )
      | ~ ( v2_pre_topc @ X11 ) ) ),
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
    ! [X7: $i,X9: $i] :
      ( ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X9 ) )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
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
    ! [X16: $i,X17: $i,X18: $i,X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ( v2_struct_0 @ X16 )
      | ~ ( v2_pre_topc @ X16 )
      | ~ ( l1_pre_topc @ X16 )
      | ( v2_struct_0 @ X17 )
      | ~ ( m1_pre_topc @ X17 @ X18 )
      | ~ ( m1_subset_1 @ X19 @ ( u1_struct_0 @ X20 ) )
      | ~ ( m1_pre_topc @ X17 @ X20 )
      | ~ ( r1_tmap_1 @ X20 @ X16 @ X21 @ X19 )
      | ( X19 != X22 )
      | ( r1_tmap_1 @ X17 @ X16 @ ( k3_tmap_1 @ X18 @ X16 @ X20 @ X17 @ X21 ) @ X22 )
      | ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ X17 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X20 ) @ ( u1_struct_0 @ X16 ) ) ) )
      | ~ ( v1_funct_2 @ X21 @ ( u1_struct_0 @ X20 ) @ ( u1_struct_0 @ X16 ) )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( m1_pre_topc @ X20 @ X18 )
      | ( v2_struct_0 @ X20 )
      | ~ ( l1_pre_topc @ X18 )
      | ~ ( v2_pre_topc @ X18 )
      | ( v2_struct_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t81_tmap_1])).

thf('38',plain,(
    ! [X16: $i,X17: $i,X18: $i,X20: $i,X21: $i,X22: $i] :
      ( ( v2_struct_0 @ X18 )
      | ~ ( v2_pre_topc @ X18 )
      | ~ ( l1_pre_topc @ X18 )
      | ( v2_struct_0 @ X20 )
      | ~ ( m1_pre_topc @ X20 @ X18 )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_funct_2 @ X21 @ ( u1_struct_0 @ X20 ) @ ( u1_struct_0 @ X16 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X20 ) @ ( u1_struct_0 @ X16 ) ) ) )
      | ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ X17 ) )
      | ( r1_tmap_1 @ X17 @ X16 @ ( k3_tmap_1 @ X18 @ X16 @ X20 @ X17 @ X21 ) @ X22 )
      | ~ ( r1_tmap_1 @ X20 @ X16 @ X21 @ X22 )
      | ~ ( m1_pre_topc @ X17 @ X20 )
      | ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ X20 ) )
      | ~ ( m1_pre_topc @ X17 @ X18 )
      | ( v2_struct_0 @ X17 )
      | ~ ( l1_pre_topc @ X16 )
      | ~ ( v2_pre_topc @ X16 )
      | ( v2_struct_0 @ X16 ) ) ),
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
    ! [X23: $i,X24: $i,X25: $i,X26: $i,X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ( v2_struct_0 @ X23 )
      | ~ ( v2_pre_topc @ X23 )
      | ~ ( l1_pre_topc @ X23 )
      | ( v2_struct_0 @ X24 )
      | ~ ( m1_pre_topc @ X24 @ X25 )
      | ~ ( m1_pre_topc @ X26 @ X24 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ~ ( m1_subset_1 @ X28 @ ( u1_struct_0 @ X26 ) )
      | ~ ( r1_tmap_1 @ X26 @ X23 @ ( k3_tmap_1 @ X25 @ X23 @ X24 @ X26 @ X29 ) @ X28 )
      | ( r1_tmap_1 @ X24 @ X23 @ X29 @ X30 )
      | ( X30 != X28 )
      | ~ ( r1_tarski @ X27 @ ( u1_struct_0 @ X26 ) )
      | ~ ( r2_hidden @ X30 @ X27 )
      | ~ ( v3_pre_topc @ X27 @ X24 )
      | ~ ( m1_subset_1 @ X30 @ ( u1_struct_0 @ X24 ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X24 ) @ ( u1_struct_0 @ X23 ) ) ) )
      | ~ ( v1_funct_2 @ X29 @ ( u1_struct_0 @ X24 ) @ ( u1_struct_0 @ X23 ) )
      | ~ ( v1_funct_1 @ X29 )
      | ~ ( m1_pre_topc @ X26 @ X25 )
      | ( v2_struct_0 @ X26 )
      | ~ ( l1_pre_topc @ X25 )
      | ~ ( v2_pre_topc @ X25 )
      | ( v2_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t84_tmap_1])).

thf('74',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ( v2_struct_0 @ X25 )
      | ~ ( v2_pre_topc @ X25 )
      | ~ ( l1_pre_topc @ X25 )
      | ( v2_struct_0 @ X26 )
      | ~ ( m1_pre_topc @ X26 @ X25 )
      | ~ ( v1_funct_1 @ X29 )
      | ~ ( v1_funct_2 @ X29 @ ( u1_struct_0 @ X24 ) @ ( u1_struct_0 @ X23 ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X24 ) @ ( u1_struct_0 @ X23 ) ) ) )
      | ~ ( m1_subset_1 @ X28 @ ( u1_struct_0 @ X24 ) )
      | ~ ( v3_pre_topc @ X27 @ X24 )
      | ~ ( r2_hidden @ X28 @ X27 )
      | ~ ( r1_tarski @ X27 @ ( u1_struct_0 @ X26 ) )
      | ( r1_tmap_1 @ X24 @ X23 @ X29 @ X28 )
      | ~ ( r1_tmap_1 @ X26 @ X23 @ ( k3_tmap_1 @ X25 @ X23 @ X24 @ X26 @ X29 ) @ X28 )
      | ~ ( m1_subset_1 @ X28 @ ( u1_struct_0 @ X26 ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ~ ( m1_pre_topc @ X26 @ X24 )
      | ~ ( m1_pre_topc @ X24 @ X25 )
      | ( v2_struct_0 @ X24 )
      | ~ ( l1_pre_topc @ X23 )
      | ~ ( v2_pre_topc @ X23 )
      | ( v2_struct_0 @ X23 ) ) ),
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
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('96',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t9_tsep_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ! [D: $i] :
                  ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                 => ! [E: $i] :
                      ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) )
                     => ( ( ( v3_pre_topc @ C @ A )
                          & ( r1_tarski @ C @ ( u1_struct_0 @ B ) )
                          & ( r1_tarski @ D @ C )
                          & ( D = E ) )
                       => ( ( v3_pre_topc @ E @ B )
                        <=> ( v3_pre_topc @ D @ A ) ) ) ) ) ) ) ) )).

thf('98',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ~ ( m1_pre_topc @ X31 @ X32 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X32 ) ) )
      | ~ ( v3_pre_topc @ X34 @ X32 )
      | ~ ( r1_tarski @ X34 @ ( u1_struct_0 @ X31 ) )
      | ~ ( r1_tarski @ X33 @ X34 )
      | ( X33 != X35 )
      | ~ ( v3_pre_topc @ X33 @ X32 )
      | ( v3_pre_topc @ X35 @ X31 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X31 ) ) )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X32 ) ) )
      | ~ ( l1_pre_topc @ X32 )
      | ~ ( v2_pre_topc @ X32 ) ) ),
    inference(cnf,[status(esa)],[t9_tsep_1])).

thf('99',plain,(
    ! [X31: $i,X32: $i,X34: $i,X35: $i] :
      ( ~ ( v2_pre_topc @ X32 )
      | ~ ( l1_pre_topc @ X32 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X32 ) ) )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X31 ) ) )
      | ( v3_pre_topc @ X35 @ X31 )
      | ~ ( v3_pre_topc @ X35 @ X32 )
      | ~ ( r1_tarski @ X35 @ X34 )
      | ~ ( r1_tarski @ X34 @ ( u1_struct_0 @ X31 ) )
      | ~ ( v3_pre_topc @ X34 @ X32 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X32 ) ) )
      | ~ ( m1_pre_topc @ X31 @ X32 ) ) ),
    inference(simplify,[status(thm)],['98'])).

thf('100',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_B )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ~ ( v3_pre_topc @ sk_F @ sk_B )
      | ~ ( r1_tarski @ sk_F @ ( u1_struct_0 @ X0 ) )
      | ~ ( r1_tarski @ X1 @ sk_F )
      | ~ ( v3_pre_topc @ X1 @ sk_B )
      | ( v3_pre_topc @ X1 @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v2_pre_topc @ sk_B ) ) ),
    inference('sup-',[status(thm)],['97','99'])).

thf('101',plain,(
    v3_pre_topc @ sk_F @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_B )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ~ ( r1_tarski @ sk_F @ ( u1_struct_0 @ X0 ) )
      | ~ ( r1_tarski @ X1 @ sk_F )
      | ~ ( v3_pre_topc @ X1 @ sk_B )
      | ( v3_pre_topc @ X1 @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['100','101','102','103'])).

thf('105',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( v3_pre_topc @ sk_F @ X0 )
      | ~ ( v3_pre_topc @ sk_F @ sk_B )
      | ~ ( r1_tarski @ sk_F @ sk_F )
      | ~ ( r1_tarski @ sk_F @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['96','104'])).

thf('106',plain,(
    v3_pre_topc @ sk_F @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('107',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ( X4 != X5 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('108',plain,(
    ! [X5: $i] :
      ( r1_tarski @ X5 @ X5 ) ),
    inference(simplify,[status(thm)],['107'])).

thf('109',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( v3_pre_topc @ sk_F @ X0 )
      | ~ ( r1_tarski @ sk_F @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ X0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['105','106','108'])).

thf('110',plain,
    ( ~ ( m1_pre_topc @ sk_D @ sk_B )
    | ~ ( r1_tarski @ sk_F @ ( u1_struct_0 @ sk_D ) )
    | ( v3_pre_topc @ sk_F @ sk_D ) ),
    inference('sup-',[status(thm)],['95','109'])).

thf('111',plain,(
    m1_pre_topc @ sk_D @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,(
    r1_tarski @ sk_F @ ( u1_struct_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['20'])).

thf('113',plain,(
    v3_pre_topc @ sk_F @ sk_D ),
    inference(demod,[status(thm)],['110','111','112'])).

thf('114',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D )
    | ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['90','91','94','113'])).

thf('115',plain,
    ( ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G )
   <= ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G ) ),
    inference(split,[status(esa)],['58'])).

thf('116',plain,(
    sk_G = sk_H ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,
    ( ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H )
   <= ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G ) ),
    inference(demod,[status(thm)],['115','116'])).

thf('118',plain,
    ( ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G )
   <= ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G ) ),
    inference(split,[status(esa)],['24'])).

thf('119',plain,(
    sk_G = sk_H ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,
    ( ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H )
   <= ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G ) ),
    inference(demod,[status(thm)],['118','119'])).

thf('121',plain,
    ( ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H )
   <= ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H ) ),
    inference(split,[status(esa)],['28'])).

thf('122',plain,
    ( ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G )
    | ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H ) ),
    inference('sup-',[status(thm)],['120','121'])).

thf('123',plain,(
    ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G ) ),
    inference('sat_resolution*',[status(thm)],['29','68','122'])).

thf('124',plain,(
    ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H ) ),
    inference(simpl_trail,[status(thm)],['117','123'])).

thf('125',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['114','124'])).

thf('126',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['125','126'])).

thf('128',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('129',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C_1 ) ),
    inference(clc,[status(thm)],['127','128'])).

thf('130',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('131',plain,(
    v2_struct_0 @ sk_C_1 ),
    inference(clc,[status(thm)],['129','130'])).

thf('132',plain,(
    $false ),
    inference(demod,[status(thm)],['0','131'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.wLSyM22ByT
% 0.15/0.39  % Computer   : n024.cluster.edu
% 0.15/0.39  % Model      : x86_64 x86_64
% 0.15/0.39  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.39  % Memory     : 8042.1875MB
% 0.15/0.39  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.39  % CPULimit   : 60
% 0.15/0.39  % DateTime   : Tue Dec  1 14:06:06 EST 2020
% 0.15/0.39  % CPUTime    : 
% 0.15/0.39  % Running portfolio for 600 s
% 0.15/0.39  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.39  % Number of cores: 8
% 0.15/0.39  % Python version: Python 3.6.8
% 0.15/0.39  % Running in FO mode
% 0.25/0.57  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.25/0.57  % Solved by: fo/fo7.sh
% 0.25/0.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.25/0.57  % done 156 iterations in 0.097s
% 0.25/0.57  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.25/0.57  % SZS output start Refutation
% 0.25/0.57  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.25/0.57  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.25/0.57  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.25/0.57  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.25/0.57  thf(sk_H_type, type, sk_H: $i).
% 0.25/0.57  thf(r1_tmap_1_type, type, r1_tmap_1: $i > $i > $i > $i > $o).
% 0.25/0.57  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.25/0.57  thf(k3_tmap_1_type, type, k3_tmap_1: $i > $i > $i > $i > $i > $i).
% 0.25/0.57  thf(sk_E_type, type, sk_E: $i).
% 0.25/0.57  thf(sk_G_type, type, sk_G: $i).
% 0.25/0.57  thf(sk_F_type, type, sk_F: $i).
% 0.25/0.57  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.25/0.57  thf(sk_D_type, type, sk_D: $i).
% 0.25/0.57  thf(sk_B_type, type, sk_B: $i).
% 0.25/0.57  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.25/0.57  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.25/0.57  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.25/0.57  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.25/0.57  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.25/0.57  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.25/0.57  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.25/0.57  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.25/0.57  thf(sk_A_type, type, sk_A: $i).
% 0.25/0.57  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.25/0.57  thf(t85_tmap_1, conjecture,
% 0.25/0.57    (![A:$i]:
% 0.25/0.57     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.25/0.57       ( ![B:$i]:
% 0.25/0.57         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.25/0.57             ( l1_pre_topc @ B ) ) =>
% 0.25/0.57           ( ![C:$i]:
% 0.25/0.57             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ B ) ) =>
% 0.25/0.57               ( ![D:$i]:
% 0.25/0.57                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ B ) ) =>
% 0.25/0.57                   ( ![E:$i]:
% 0.25/0.57                     ( ( ( v1_funct_1 @ E ) & 
% 0.25/0.57                         ( v1_funct_2 @
% 0.25/0.57                           E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ A ) ) & 
% 0.25/0.57                         ( m1_subset_1 @
% 0.25/0.57                           E @ 
% 0.25/0.57                           ( k1_zfmisc_1 @
% 0.25/0.57                             ( k2_zfmisc_1 @
% 0.25/0.57                               ( u1_struct_0 @ D ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.25/0.57                       ( ( m1_pre_topc @ C @ D ) =>
% 0.25/0.57                         ( ![F:$i]:
% 0.25/0.57                           ( ( m1_subset_1 @
% 0.25/0.57                               F @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.25/0.57                             ( ![G:$i]:
% 0.25/0.57                               ( ( m1_subset_1 @ G @ ( u1_struct_0 @ D ) ) =>
% 0.25/0.57                                 ( ![H:$i]:
% 0.25/0.57                                   ( ( m1_subset_1 @ H @ ( u1_struct_0 @ C ) ) =>
% 0.25/0.57                                     ( ( ( v3_pre_topc @ F @ B ) & 
% 0.25/0.57                                         ( r2_hidden @ G @ F ) & 
% 0.25/0.57                                         ( r1_tarski @ F @ ( u1_struct_0 @ C ) ) & 
% 0.25/0.57                                         ( ( G ) = ( H ) ) ) =>
% 0.25/0.57                                       ( ( r1_tmap_1 @ D @ A @ E @ G ) <=>
% 0.25/0.57                                         ( r1_tmap_1 @
% 0.25/0.57                                           C @ A @ 
% 0.25/0.57                                           ( k3_tmap_1 @ B @ A @ D @ C @ E ) @ 
% 0.25/0.57                                           H ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.25/0.57  thf(zf_stmt_0, negated_conjecture,
% 0.25/0.57    (~( ![A:$i]:
% 0.25/0.57        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.25/0.57            ( l1_pre_topc @ A ) ) =>
% 0.25/0.57          ( ![B:$i]:
% 0.25/0.57            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.25/0.57                ( l1_pre_topc @ B ) ) =>
% 0.25/0.57              ( ![C:$i]:
% 0.25/0.57                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ B ) ) =>
% 0.25/0.57                  ( ![D:$i]:
% 0.25/0.57                    ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ B ) ) =>
% 0.25/0.57                      ( ![E:$i]:
% 0.25/0.57                        ( ( ( v1_funct_1 @ E ) & 
% 0.25/0.57                            ( v1_funct_2 @
% 0.25/0.57                              E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ A ) ) & 
% 0.25/0.57                            ( m1_subset_1 @
% 0.25/0.57                              E @ 
% 0.25/0.57                              ( k1_zfmisc_1 @
% 0.25/0.57                                ( k2_zfmisc_1 @
% 0.25/0.57                                  ( u1_struct_0 @ D ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.25/0.57                          ( ( m1_pre_topc @ C @ D ) =>
% 0.25/0.57                            ( ![F:$i]:
% 0.25/0.57                              ( ( m1_subset_1 @
% 0.25/0.57                                  F @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.25/0.57                                ( ![G:$i]:
% 0.25/0.57                                  ( ( m1_subset_1 @ G @ ( u1_struct_0 @ D ) ) =>
% 0.25/0.57                                    ( ![H:$i]:
% 0.25/0.57                                      ( ( m1_subset_1 @ H @ ( u1_struct_0 @ C ) ) =>
% 0.25/0.57                                        ( ( ( v3_pre_topc @ F @ B ) & 
% 0.25/0.57                                            ( r2_hidden @ G @ F ) & 
% 0.25/0.57                                            ( r1_tarski @
% 0.25/0.57                                              F @ ( u1_struct_0 @ C ) ) & 
% 0.25/0.57                                            ( ( G ) = ( H ) ) ) =>
% 0.25/0.57                                          ( ( r1_tmap_1 @ D @ A @ E @ G ) <=>
% 0.25/0.57                                            ( r1_tmap_1 @
% 0.25/0.57                                              C @ A @ 
% 0.25/0.57                                              ( k3_tmap_1 @ B @ A @ D @ C @ E ) @ 
% 0.25/0.57                                              H ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.25/0.57    inference('cnf.neg', [status(esa)], [t85_tmap_1])).
% 0.25/0.57  thf('0', plain, (~ (v2_struct_0 @ sk_C_1)),
% 0.25/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.57  thf(d3_tarski, axiom,
% 0.25/0.57    (![A:$i,B:$i]:
% 0.25/0.57     ( ( r1_tarski @ A @ B ) <=>
% 0.25/0.57       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.25/0.57  thf('1', plain,
% 0.25/0.57      (![X1 : $i, X3 : $i]:
% 0.25/0.57         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.25/0.57      inference('cnf', [status(esa)], [d3_tarski])).
% 0.25/0.57  thf('2', plain, ((r1_tarski @ sk_F @ (u1_struct_0 @ sk_C_1))),
% 0.25/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.57  thf('3', plain,
% 0.25/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.25/0.57         (~ (r2_hidden @ X0 @ X1)
% 0.25/0.57          | (r2_hidden @ X0 @ X2)
% 0.25/0.57          | ~ (r1_tarski @ X1 @ X2))),
% 0.25/0.57      inference('cnf', [status(esa)], [d3_tarski])).
% 0.25/0.57  thf('4', plain,
% 0.25/0.57      (![X0 : $i]:
% 0.25/0.57         ((r2_hidden @ X0 @ (u1_struct_0 @ sk_C_1)) | ~ (r2_hidden @ X0 @ sk_F))),
% 0.25/0.57      inference('sup-', [status(thm)], ['2', '3'])).
% 0.25/0.57  thf('5', plain,
% 0.25/0.57      (![X0 : $i]:
% 0.25/0.57         ((r1_tarski @ sk_F @ X0)
% 0.25/0.57          | (r2_hidden @ (sk_C @ X0 @ sk_F) @ (u1_struct_0 @ sk_C_1)))),
% 0.25/0.57      inference('sup-', [status(thm)], ['1', '4'])).
% 0.25/0.57  thf('6', plain, ((m1_pre_topc @ sk_D @ sk_B)),
% 0.25/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.57  thf('7', plain, ((m1_pre_topc @ sk_C_1 @ sk_B)),
% 0.25/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.57  thf(t4_tsep_1, axiom,
% 0.25/0.57    (![A:$i]:
% 0.25/0.57     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.25/0.57       ( ![B:$i]:
% 0.25/0.57         ( ( m1_pre_topc @ B @ A ) =>
% 0.25/0.57           ( ![C:$i]:
% 0.25/0.57             ( ( m1_pre_topc @ C @ A ) =>
% 0.25/0.57               ( ( r1_tarski @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ C ) ) <=>
% 0.25/0.57                 ( m1_pre_topc @ B @ C ) ) ) ) ) ) ))).
% 0.25/0.57  thf('8', plain,
% 0.25/0.57      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.25/0.57         (~ (m1_pre_topc @ X10 @ X11)
% 0.25/0.57          | ~ (m1_pre_topc @ X10 @ X12)
% 0.25/0.57          | (r1_tarski @ (u1_struct_0 @ X10) @ (u1_struct_0 @ X12))
% 0.25/0.57          | ~ (m1_pre_topc @ X12 @ X11)
% 0.25/0.57          | ~ (l1_pre_topc @ X11)
% 0.25/0.57          | ~ (v2_pre_topc @ X11))),
% 0.25/0.57      inference('cnf', [status(esa)], [t4_tsep_1])).
% 0.25/0.57  thf('9', plain,
% 0.25/0.57      (![X0 : $i]:
% 0.25/0.57         (~ (v2_pre_topc @ sk_B)
% 0.25/0.57          | ~ (l1_pre_topc @ sk_B)
% 0.25/0.57          | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.25/0.57          | (r1_tarski @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ X0))
% 0.25/0.57          | ~ (m1_pre_topc @ sk_C_1 @ X0))),
% 0.25/0.57      inference('sup-', [status(thm)], ['7', '8'])).
% 0.25/0.57  thf('10', plain, ((v2_pre_topc @ sk_B)),
% 0.25/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.57  thf('11', plain, ((l1_pre_topc @ sk_B)),
% 0.25/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.57  thf('12', plain,
% 0.25/0.57      (![X0 : $i]:
% 0.25/0.57         (~ (m1_pre_topc @ X0 @ sk_B)
% 0.25/0.57          | (r1_tarski @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ X0))
% 0.25/0.57          | ~ (m1_pre_topc @ sk_C_1 @ X0))),
% 0.25/0.57      inference('demod', [status(thm)], ['9', '10', '11'])).
% 0.25/0.57  thf('13', plain,
% 0.25/0.57      ((~ (m1_pre_topc @ sk_C_1 @ sk_D)
% 0.25/0.57        | (r1_tarski @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_D)))),
% 0.25/0.57      inference('sup-', [status(thm)], ['6', '12'])).
% 0.25/0.57  thf('14', plain, ((m1_pre_topc @ sk_C_1 @ sk_D)),
% 0.25/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.57  thf('15', plain,
% 0.25/0.57      ((r1_tarski @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_D))),
% 0.25/0.57      inference('demod', [status(thm)], ['13', '14'])).
% 0.25/0.57  thf('16', plain,
% 0.25/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.25/0.57         (~ (r2_hidden @ X0 @ X1)
% 0.25/0.57          | (r2_hidden @ X0 @ X2)
% 0.25/0.57          | ~ (r1_tarski @ X1 @ X2))),
% 0.25/0.57      inference('cnf', [status(esa)], [d3_tarski])).
% 0.25/0.57  thf('17', plain,
% 0.25/0.57      (![X0 : $i]:
% 0.25/0.57         ((r2_hidden @ X0 @ (u1_struct_0 @ sk_D))
% 0.25/0.57          | ~ (r2_hidden @ X0 @ (u1_struct_0 @ sk_C_1)))),
% 0.25/0.57      inference('sup-', [status(thm)], ['15', '16'])).
% 0.25/0.57  thf('18', plain,
% 0.25/0.57      (![X0 : $i]:
% 0.25/0.57         ((r1_tarski @ sk_F @ X0)
% 0.25/0.57          | (r2_hidden @ (sk_C @ X0 @ sk_F) @ (u1_struct_0 @ sk_D)))),
% 0.25/0.57      inference('sup-', [status(thm)], ['5', '17'])).
% 0.25/0.57  thf('19', plain,
% 0.25/0.57      (![X1 : $i, X3 : $i]:
% 0.25/0.57         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.25/0.57      inference('cnf', [status(esa)], [d3_tarski])).
% 0.25/0.57  thf('20', plain,
% 0.25/0.57      (((r1_tarski @ sk_F @ (u1_struct_0 @ sk_D))
% 0.25/0.57        | (r1_tarski @ sk_F @ (u1_struct_0 @ sk_D)))),
% 0.25/0.57      inference('sup-', [status(thm)], ['18', '19'])).
% 0.25/0.57  thf('21', plain, ((r1_tarski @ sk_F @ (u1_struct_0 @ sk_D))),
% 0.25/0.57      inference('simplify', [status(thm)], ['20'])).
% 0.25/0.57  thf(t3_subset, axiom,
% 0.25/0.57    (![A:$i,B:$i]:
% 0.25/0.57     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.25/0.57  thf('22', plain,
% 0.25/0.57      (![X7 : $i, X9 : $i]:
% 0.25/0.57         ((m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X9)) | ~ (r1_tarski @ X7 @ X9))),
% 0.25/0.57      inference('cnf', [status(esa)], [t3_subset])).
% 0.25/0.57  thf('23', plain,
% 0.25/0.57      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))),
% 0.25/0.57      inference('sup-', [status(thm)], ['21', '22'])).
% 0.25/0.57  thf('24', plain,
% 0.25/0.57      (((r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.25/0.57         (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_H)
% 0.25/0.57        | (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G))),
% 0.25/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.57  thf('25', plain,
% 0.25/0.57      (((r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.25/0.57         (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_H))
% 0.25/0.57         <= (((r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.25/0.57               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_H)))),
% 0.25/0.57      inference('split', [status(esa)], ['24'])).
% 0.25/0.57  thf('26', plain,
% 0.25/0.57      ((~ (r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.25/0.57           (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_H)
% 0.25/0.57        | ~ (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G))),
% 0.25/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.57  thf('27', plain, (((sk_G) = (sk_H))),
% 0.25/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.57  thf('28', plain,
% 0.25/0.57      ((~ (r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.25/0.57           (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_H)
% 0.25/0.57        | ~ (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H))),
% 0.25/0.57      inference('demod', [status(thm)], ['26', '27'])).
% 0.25/0.57  thf('29', plain,
% 0.25/0.57      (~ ((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H)) | 
% 0.25/0.57       ~
% 0.25/0.57       ((r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.25/0.57         (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_H))),
% 0.25/0.57      inference('split', [status(esa)], ['28'])).
% 0.25/0.57  thf('30', plain, ((m1_pre_topc @ sk_C_1 @ sk_B)),
% 0.25/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.57  thf('31', plain, ((m1_subset_1 @ sk_H @ (u1_struct_0 @ sk_C_1))),
% 0.25/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.57  thf('32', plain,
% 0.25/0.57      (((r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.25/0.57         (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_H)
% 0.25/0.57        | (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G))),
% 0.25/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.57  thf('33', plain, (((sk_G) = (sk_H))),
% 0.25/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.57  thf('34', plain,
% 0.25/0.57      (((r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.25/0.57         (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_H)
% 0.25/0.57        | (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H))),
% 0.25/0.57      inference('demod', [status(thm)], ['32', '33'])).
% 0.25/0.57  thf('35', plain,
% 0.25/0.57      (((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H))
% 0.25/0.57         <= (((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H)))),
% 0.25/0.57      inference('split', [status(esa)], ['34'])).
% 0.25/0.57  thf('36', plain,
% 0.25/0.57      ((m1_subset_1 @ sk_E @ 
% 0.25/0.57        (k1_zfmisc_1 @ 
% 0.25/0.57         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A))))),
% 0.25/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.57  thf(t81_tmap_1, axiom,
% 0.25/0.57    (![A:$i]:
% 0.25/0.57     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.25/0.57       ( ![B:$i]:
% 0.25/0.57         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.25/0.57             ( l1_pre_topc @ B ) ) =>
% 0.25/0.57           ( ![C:$i]:
% 0.25/0.57             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.25/0.57               ( ![D:$i]:
% 0.25/0.57                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.25/0.57                   ( ![E:$i]:
% 0.25/0.57                     ( ( ( v1_funct_1 @ E ) & 
% 0.25/0.57                         ( v1_funct_2 @
% 0.25/0.57                           E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 0.25/0.57                         ( m1_subset_1 @
% 0.25/0.57                           E @ 
% 0.25/0.57                           ( k1_zfmisc_1 @
% 0.25/0.57                             ( k2_zfmisc_1 @
% 0.25/0.57                               ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.25/0.57                       ( ![F:$i]:
% 0.25/0.57                         ( ( m1_subset_1 @ F @ ( u1_struct_0 @ C ) ) =>
% 0.25/0.57                           ( ![G:$i]:
% 0.25/0.57                             ( ( m1_subset_1 @ G @ ( u1_struct_0 @ D ) ) =>
% 0.25/0.57                               ( ( ( ( F ) = ( G ) ) & 
% 0.25/0.57                                   ( m1_pre_topc @ D @ C ) & 
% 0.25/0.57                                   ( r1_tmap_1 @ C @ B @ E @ F ) ) =>
% 0.25/0.57                                 ( r1_tmap_1 @
% 0.25/0.57                                   D @ B @ ( k3_tmap_1 @ A @ B @ C @ D @ E ) @ 
% 0.25/0.57                                   G ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.25/0.57  thf('37', plain,
% 0.25/0.57      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 0.25/0.57         ((v2_struct_0 @ X16)
% 0.25/0.57          | ~ (v2_pre_topc @ X16)
% 0.25/0.57          | ~ (l1_pre_topc @ X16)
% 0.25/0.57          | (v2_struct_0 @ X17)
% 0.25/0.57          | ~ (m1_pre_topc @ X17 @ X18)
% 0.25/0.57          | ~ (m1_subset_1 @ X19 @ (u1_struct_0 @ X20))
% 0.25/0.57          | ~ (m1_pre_topc @ X17 @ X20)
% 0.25/0.57          | ~ (r1_tmap_1 @ X20 @ X16 @ X21 @ X19)
% 0.25/0.57          | ((X19) != (X22))
% 0.25/0.57          | (r1_tmap_1 @ X17 @ X16 @ 
% 0.25/0.57             (k3_tmap_1 @ X18 @ X16 @ X20 @ X17 @ X21) @ X22)
% 0.25/0.57          | ~ (m1_subset_1 @ X22 @ (u1_struct_0 @ X17))
% 0.25/0.57          | ~ (m1_subset_1 @ X21 @ 
% 0.25/0.57               (k1_zfmisc_1 @ 
% 0.25/0.57                (k2_zfmisc_1 @ (u1_struct_0 @ X20) @ (u1_struct_0 @ X16))))
% 0.25/0.57          | ~ (v1_funct_2 @ X21 @ (u1_struct_0 @ X20) @ (u1_struct_0 @ X16))
% 0.25/0.57          | ~ (v1_funct_1 @ X21)
% 0.25/0.57          | ~ (m1_pre_topc @ X20 @ X18)
% 0.25/0.57          | (v2_struct_0 @ X20)
% 0.25/0.57          | ~ (l1_pre_topc @ X18)
% 0.25/0.57          | ~ (v2_pre_topc @ X18)
% 0.25/0.57          | (v2_struct_0 @ X18))),
% 0.25/0.57      inference('cnf', [status(esa)], [t81_tmap_1])).
% 0.25/0.57  thf('38', plain,
% 0.25/0.57      (![X16 : $i, X17 : $i, X18 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 0.25/0.57         ((v2_struct_0 @ X18)
% 0.25/0.57          | ~ (v2_pre_topc @ X18)
% 0.25/0.57          | ~ (l1_pre_topc @ X18)
% 0.25/0.57          | (v2_struct_0 @ X20)
% 0.25/0.57          | ~ (m1_pre_topc @ X20 @ X18)
% 0.25/0.57          | ~ (v1_funct_1 @ X21)
% 0.25/0.57          | ~ (v1_funct_2 @ X21 @ (u1_struct_0 @ X20) @ (u1_struct_0 @ X16))
% 0.25/0.57          | ~ (m1_subset_1 @ X21 @ 
% 0.25/0.57               (k1_zfmisc_1 @ 
% 0.25/0.57                (k2_zfmisc_1 @ (u1_struct_0 @ X20) @ (u1_struct_0 @ X16))))
% 0.25/0.57          | ~ (m1_subset_1 @ X22 @ (u1_struct_0 @ X17))
% 0.25/0.57          | (r1_tmap_1 @ X17 @ X16 @ 
% 0.25/0.57             (k3_tmap_1 @ X18 @ X16 @ X20 @ X17 @ X21) @ X22)
% 0.25/0.57          | ~ (r1_tmap_1 @ X20 @ X16 @ X21 @ X22)
% 0.25/0.57          | ~ (m1_pre_topc @ X17 @ X20)
% 0.25/0.57          | ~ (m1_subset_1 @ X22 @ (u1_struct_0 @ X20))
% 0.25/0.57          | ~ (m1_pre_topc @ X17 @ X18)
% 0.25/0.57          | (v2_struct_0 @ X17)
% 0.25/0.57          | ~ (l1_pre_topc @ X16)
% 0.25/0.57          | ~ (v2_pre_topc @ X16)
% 0.25/0.57          | (v2_struct_0 @ X16))),
% 0.25/0.57      inference('simplify', [status(thm)], ['37'])).
% 0.25/0.57  thf('39', plain,
% 0.25/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.25/0.57         ((v2_struct_0 @ sk_A)
% 0.25/0.57          | ~ (v2_pre_topc @ sk_A)
% 0.25/0.57          | ~ (l1_pre_topc @ sk_A)
% 0.25/0.57          | (v2_struct_0 @ X0)
% 0.25/0.57          | ~ (m1_pre_topc @ X0 @ X1)
% 0.25/0.57          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ sk_D))
% 0.25/0.57          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.25/0.57          | ~ (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ X2)
% 0.25/0.57          | (r1_tmap_1 @ X0 @ sk_A @ 
% 0.25/0.57             (k3_tmap_1 @ X1 @ sk_A @ sk_D @ X0 @ sk_E) @ X2)
% 0.25/0.57          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.25/0.57          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A))
% 0.25/0.57          | ~ (v1_funct_1 @ sk_E)
% 0.25/0.57          | ~ (m1_pre_topc @ sk_D @ X1)
% 0.25/0.57          | (v2_struct_0 @ sk_D)
% 0.25/0.57          | ~ (l1_pre_topc @ X1)
% 0.25/0.57          | ~ (v2_pre_topc @ X1)
% 0.25/0.57          | (v2_struct_0 @ X1))),
% 0.25/0.57      inference('sup-', [status(thm)], ['36', '38'])).
% 0.25/0.57  thf('40', plain, ((v2_pre_topc @ sk_A)),
% 0.25/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.57  thf('41', plain, ((l1_pre_topc @ sk_A)),
% 0.25/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.57  thf('42', plain,
% 0.25/0.57      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A))),
% 0.25/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.57  thf('43', plain, ((v1_funct_1 @ sk_E)),
% 0.25/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.57  thf('44', plain,
% 0.25/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.25/0.57         ((v2_struct_0 @ sk_A)
% 0.25/0.57          | (v2_struct_0 @ X0)
% 0.25/0.57          | ~ (m1_pre_topc @ X0 @ X1)
% 0.25/0.57          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ sk_D))
% 0.25/0.57          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.25/0.57          | ~ (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ X2)
% 0.25/0.57          | (r1_tmap_1 @ X0 @ sk_A @ 
% 0.25/0.57             (k3_tmap_1 @ X1 @ sk_A @ sk_D @ X0 @ sk_E) @ X2)
% 0.25/0.57          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.25/0.57          | ~ (m1_pre_topc @ sk_D @ X1)
% 0.25/0.57          | (v2_struct_0 @ sk_D)
% 0.25/0.57          | ~ (l1_pre_topc @ X1)
% 0.25/0.57          | ~ (v2_pre_topc @ X1)
% 0.25/0.57          | (v2_struct_0 @ X1))),
% 0.25/0.57      inference('demod', [status(thm)], ['39', '40', '41', '42', '43'])).
% 0.25/0.57  thf('45', plain,
% 0.25/0.57      ((![X0 : $i, X1 : $i]:
% 0.25/0.57          ((v2_struct_0 @ X0)
% 0.25/0.57           | ~ (v2_pre_topc @ X0)
% 0.25/0.57           | ~ (l1_pre_topc @ X0)
% 0.25/0.57           | (v2_struct_0 @ sk_D)
% 0.25/0.57           | ~ (m1_pre_topc @ sk_D @ X0)
% 0.25/0.57           | ~ (m1_subset_1 @ sk_H @ (u1_struct_0 @ X1))
% 0.25/0.57           | (r1_tmap_1 @ X1 @ sk_A @ 
% 0.25/0.57              (k3_tmap_1 @ X0 @ sk_A @ sk_D @ X1 @ sk_E) @ sk_H)
% 0.25/0.57           | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.25/0.57           | ~ (m1_subset_1 @ sk_H @ (u1_struct_0 @ sk_D))
% 0.25/0.57           | ~ (m1_pre_topc @ X1 @ X0)
% 0.25/0.57           | (v2_struct_0 @ X1)
% 0.25/0.57           | (v2_struct_0 @ sk_A)))
% 0.25/0.57         <= (((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H)))),
% 0.25/0.57      inference('sup-', [status(thm)], ['35', '44'])).
% 0.25/0.57  thf('46', plain, ((m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_D))),
% 0.25/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.57  thf('47', plain, (((sk_G) = (sk_H))),
% 0.25/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.57  thf('48', plain, ((m1_subset_1 @ sk_H @ (u1_struct_0 @ sk_D))),
% 0.25/0.57      inference('demod', [status(thm)], ['46', '47'])).
% 0.25/0.57  thf('49', plain,
% 0.25/0.57      ((![X0 : $i, X1 : $i]:
% 0.25/0.57          ((v2_struct_0 @ X0)
% 0.25/0.57           | ~ (v2_pre_topc @ X0)
% 0.25/0.57           | ~ (l1_pre_topc @ X0)
% 0.25/0.57           | (v2_struct_0 @ sk_D)
% 0.25/0.57           | ~ (m1_pre_topc @ sk_D @ X0)
% 0.25/0.57           | ~ (m1_subset_1 @ sk_H @ (u1_struct_0 @ X1))
% 0.25/0.57           | (r1_tmap_1 @ X1 @ sk_A @ 
% 0.25/0.57              (k3_tmap_1 @ X0 @ sk_A @ sk_D @ X1 @ sk_E) @ sk_H)
% 0.25/0.57           | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.25/0.57           | ~ (m1_pre_topc @ X1 @ X0)
% 0.25/0.57           | (v2_struct_0 @ X1)
% 0.25/0.57           | (v2_struct_0 @ sk_A)))
% 0.25/0.57         <= (((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H)))),
% 0.25/0.57      inference('demod', [status(thm)], ['45', '48'])).
% 0.25/0.57  thf('50', plain,
% 0.25/0.57      ((![X0 : $i]:
% 0.25/0.57          ((v2_struct_0 @ sk_A)
% 0.25/0.57           | (v2_struct_0 @ sk_C_1)
% 0.25/0.57           | ~ (m1_pre_topc @ sk_C_1 @ X0)
% 0.25/0.57           | ~ (m1_pre_topc @ sk_C_1 @ sk_D)
% 0.25/0.57           | (r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.25/0.57              (k3_tmap_1 @ X0 @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_H)
% 0.25/0.57           | ~ (m1_pre_topc @ sk_D @ X0)
% 0.25/0.57           | (v2_struct_0 @ sk_D)
% 0.25/0.57           | ~ (l1_pre_topc @ X0)
% 0.25/0.57           | ~ (v2_pre_topc @ X0)
% 0.25/0.57           | (v2_struct_0 @ X0)))
% 0.25/0.57         <= (((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H)))),
% 0.25/0.57      inference('sup-', [status(thm)], ['31', '49'])).
% 0.25/0.57  thf('51', plain, ((m1_pre_topc @ sk_C_1 @ sk_D)),
% 0.25/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.57  thf('52', plain,
% 0.25/0.57      ((![X0 : $i]:
% 0.25/0.57          ((v2_struct_0 @ sk_A)
% 0.25/0.57           | (v2_struct_0 @ sk_C_1)
% 0.25/0.57           | ~ (m1_pre_topc @ sk_C_1 @ X0)
% 0.25/0.57           | (r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.25/0.57              (k3_tmap_1 @ X0 @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_H)
% 0.25/0.57           | ~ (m1_pre_topc @ sk_D @ X0)
% 0.25/0.57           | (v2_struct_0 @ sk_D)
% 0.25/0.57           | ~ (l1_pre_topc @ X0)
% 0.25/0.57           | ~ (v2_pre_topc @ X0)
% 0.25/0.57           | (v2_struct_0 @ X0)))
% 0.25/0.57         <= (((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H)))),
% 0.25/0.57      inference('demod', [status(thm)], ['50', '51'])).
% 0.25/0.57  thf('53', plain,
% 0.25/0.57      ((((v2_struct_0 @ sk_B)
% 0.25/0.57         | ~ (v2_pre_topc @ sk_B)
% 0.25/0.57         | ~ (l1_pre_topc @ sk_B)
% 0.25/0.57         | (v2_struct_0 @ sk_D)
% 0.25/0.57         | ~ (m1_pre_topc @ sk_D @ sk_B)
% 0.25/0.57         | (r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.25/0.57            (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_H)
% 0.25/0.57         | (v2_struct_0 @ sk_C_1)
% 0.25/0.57         | (v2_struct_0 @ sk_A)))
% 0.25/0.57         <= (((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H)))),
% 0.25/0.57      inference('sup-', [status(thm)], ['30', '52'])).
% 0.25/0.57  thf('54', plain, ((v2_pre_topc @ sk_B)),
% 0.25/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.57  thf('55', plain, ((l1_pre_topc @ sk_B)),
% 0.25/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.57  thf('56', plain, ((m1_pre_topc @ sk_D @ sk_B)),
% 0.25/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.57  thf('57', plain,
% 0.25/0.57      ((((v2_struct_0 @ sk_B)
% 0.25/0.57         | (v2_struct_0 @ sk_D)
% 0.25/0.57         | (r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.25/0.57            (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_H)
% 0.25/0.57         | (v2_struct_0 @ sk_C_1)
% 0.25/0.57         | (v2_struct_0 @ sk_A)))
% 0.25/0.57         <= (((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H)))),
% 0.25/0.57      inference('demod', [status(thm)], ['53', '54', '55', '56'])).
% 0.25/0.57  thf('58', plain,
% 0.25/0.57      ((~ (r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.25/0.57           (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_H)
% 0.25/0.57        | ~ (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G))),
% 0.25/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.57  thf('59', plain,
% 0.25/0.57      ((~ (r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.25/0.57           (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_H))
% 0.25/0.57         <= (~
% 0.25/0.57             ((r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.25/0.57               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_H)))),
% 0.25/0.57      inference('split', [status(esa)], ['58'])).
% 0.25/0.57  thf('60', plain,
% 0.25/0.57      ((((v2_struct_0 @ sk_A)
% 0.25/0.57         | (v2_struct_0 @ sk_C_1)
% 0.25/0.57         | (v2_struct_0 @ sk_D)
% 0.25/0.57         | (v2_struct_0 @ sk_B)))
% 0.25/0.57         <= (~
% 0.25/0.57             ((r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.25/0.57               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_H)) & 
% 0.25/0.57             ((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H)))),
% 0.25/0.57      inference('sup-', [status(thm)], ['57', '59'])).
% 0.25/0.57  thf('61', plain, (~ (v2_struct_0 @ sk_A)),
% 0.25/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.57  thf('62', plain,
% 0.25/0.57      ((((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_C_1)))
% 0.25/0.57         <= (~
% 0.25/0.57             ((r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.25/0.57               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_H)) & 
% 0.25/0.57             ((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H)))),
% 0.25/0.57      inference('sup-', [status(thm)], ['60', '61'])).
% 0.25/0.57  thf('63', plain, (~ (v2_struct_0 @ sk_B)),
% 0.25/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.57  thf('64', plain,
% 0.25/0.57      ((((v2_struct_0 @ sk_C_1) | (v2_struct_0 @ sk_D)))
% 0.25/0.57         <= (~
% 0.25/0.57             ((r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.25/0.57               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_H)) & 
% 0.25/0.57             ((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H)))),
% 0.25/0.57      inference('clc', [status(thm)], ['62', '63'])).
% 0.25/0.57  thf('65', plain, (~ (v2_struct_0 @ sk_C_1)),
% 0.25/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.57  thf('66', plain,
% 0.25/0.57      (((v2_struct_0 @ sk_D))
% 0.25/0.57         <= (~
% 0.25/0.57             ((r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.25/0.57               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_H)) & 
% 0.25/0.57             ((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H)))),
% 0.25/0.57      inference('clc', [status(thm)], ['64', '65'])).
% 0.25/0.57  thf('67', plain, (~ (v2_struct_0 @ sk_D)),
% 0.25/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.57  thf('68', plain,
% 0.25/0.57      (((r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.25/0.57         (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_H)) | 
% 0.25/0.57       ~ ((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H))),
% 0.25/0.57      inference('sup-', [status(thm)], ['66', '67'])).
% 0.25/0.57  thf('69', plain,
% 0.25/0.57      (((r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.25/0.57         (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_H)) | 
% 0.25/0.57       ((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H))),
% 0.25/0.57      inference('split', [status(esa)], ['34'])).
% 0.25/0.57  thf('70', plain,
% 0.25/0.57      (((r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.25/0.57         (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_H))),
% 0.25/0.57      inference('sat_resolution*', [status(thm)], ['29', '68', '69'])).
% 0.25/0.57  thf('71', plain,
% 0.25/0.57      ((r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.25/0.57        (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_H)),
% 0.25/0.57      inference('simpl_trail', [status(thm)], ['25', '70'])).
% 0.25/0.57  thf('72', plain,
% 0.25/0.57      ((m1_subset_1 @ sk_E @ 
% 0.25/0.57        (k1_zfmisc_1 @ 
% 0.25/0.57         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A))))),
% 0.25/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.57  thf(t84_tmap_1, axiom,
% 0.25/0.57    (![A:$i]:
% 0.25/0.57     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.25/0.57       ( ![B:$i]:
% 0.25/0.57         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.25/0.57             ( l1_pre_topc @ B ) ) =>
% 0.25/0.57           ( ![C:$i]:
% 0.25/0.57             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.25/0.57               ( ![D:$i]:
% 0.25/0.57                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.25/0.57                   ( ![E:$i]:
% 0.25/0.57                     ( ( ( v1_funct_1 @ E ) & 
% 0.25/0.57                         ( v1_funct_2 @
% 0.25/0.57                           E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 0.25/0.57                         ( m1_subset_1 @
% 0.25/0.57                           E @ 
% 0.25/0.57                           ( k1_zfmisc_1 @
% 0.25/0.57                             ( k2_zfmisc_1 @
% 0.25/0.57                               ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.25/0.57                       ( ( m1_pre_topc @ C @ D ) =>
% 0.25/0.57                         ( ![F:$i]:
% 0.25/0.57                           ( ( m1_subset_1 @
% 0.25/0.57                               F @ ( k1_zfmisc_1 @ ( u1_struct_0 @ D ) ) ) =>
% 0.25/0.57                             ( ![G:$i]:
% 0.25/0.57                               ( ( m1_subset_1 @ G @ ( u1_struct_0 @ D ) ) =>
% 0.25/0.57                                 ( ![H:$i]:
% 0.25/0.57                                   ( ( m1_subset_1 @ H @ ( u1_struct_0 @ C ) ) =>
% 0.25/0.57                                     ( ( ( v3_pre_topc @ F @ D ) & 
% 0.25/0.57                                         ( r2_hidden @ G @ F ) & 
% 0.25/0.57                                         ( r1_tarski @ F @ ( u1_struct_0 @ C ) ) & 
% 0.25/0.57                                         ( ( G ) = ( H ) ) ) =>
% 0.25/0.57                                       ( ( r1_tmap_1 @ D @ B @ E @ G ) <=>
% 0.25/0.57                                         ( r1_tmap_1 @
% 0.25/0.57                                           C @ B @ 
% 0.25/0.57                                           ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ 
% 0.25/0.57                                           H ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.25/0.57  thf('73', plain,
% 0.25/0.57      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i, 
% 0.25/0.57         X30 : $i]:
% 0.25/0.57         ((v2_struct_0 @ X23)
% 0.25/0.57          | ~ (v2_pre_topc @ X23)
% 0.25/0.57          | ~ (l1_pre_topc @ X23)
% 0.25/0.57          | (v2_struct_0 @ X24)
% 0.25/0.57          | ~ (m1_pre_topc @ X24 @ X25)
% 0.25/0.57          | ~ (m1_pre_topc @ X26 @ X24)
% 0.25/0.57          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 0.25/0.57          | ~ (m1_subset_1 @ X28 @ (u1_struct_0 @ X26))
% 0.25/0.57          | ~ (r1_tmap_1 @ X26 @ X23 @ 
% 0.25/0.57               (k3_tmap_1 @ X25 @ X23 @ X24 @ X26 @ X29) @ X28)
% 0.25/0.57          | (r1_tmap_1 @ X24 @ X23 @ X29 @ X30)
% 0.25/0.57          | ((X30) != (X28))
% 0.25/0.57          | ~ (r1_tarski @ X27 @ (u1_struct_0 @ X26))
% 0.25/0.57          | ~ (r2_hidden @ X30 @ X27)
% 0.25/0.57          | ~ (v3_pre_topc @ X27 @ X24)
% 0.25/0.57          | ~ (m1_subset_1 @ X30 @ (u1_struct_0 @ X24))
% 0.25/0.57          | ~ (m1_subset_1 @ X29 @ 
% 0.25/0.57               (k1_zfmisc_1 @ 
% 0.25/0.57                (k2_zfmisc_1 @ (u1_struct_0 @ X24) @ (u1_struct_0 @ X23))))
% 0.25/0.57          | ~ (v1_funct_2 @ X29 @ (u1_struct_0 @ X24) @ (u1_struct_0 @ X23))
% 0.25/0.57          | ~ (v1_funct_1 @ X29)
% 0.25/0.57          | ~ (m1_pre_topc @ X26 @ X25)
% 0.25/0.57          | (v2_struct_0 @ X26)
% 0.25/0.57          | ~ (l1_pre_topc @ X25)
% 0.25/0.57          | ~ (v2_pre_topc @ X25)
% 0.25/0.57          | (v2_struct_0 @ X25))),
% 0.25/0.57      inference('cnf', [status(esa)], [t84_tmap_1])).
% 0.25/0.57  thf('74', plain,
% 0.25/0.57      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 0.25/0.57         ((v2_struct_0 @ X25)
% 0.25/0.57          | ~ (v2_pre_topc @ X25)
% 0.25/0.57          | ~ (l1_pre_topc @ X25)
% 0.25/0.57          | (v2_struct_0 @ X26)
% 0.25/0.57          | ~ (m1_pre_topc @ X26 @ X25)
% 0.25/0.57          | ~ (v1_funct_1 @ X29)
% 0.25/0.57          | ~ (v1_funct_2 @ X29 @ (u1_struct_0 @ X24) @ (u1_struct_0 @ X23))
% 0.25/0.57          | ~ (m1_subset_1 @ X29 @ 
% 0.25/0.57               (k1_zfmisc_1 @ 
% 0.25/0.57                (k2_zfmisc_1 @ (u1_struct_0 @ X24) @ (u1_struct_0 @ X23))))
% 0.25/0.57          | ~ (m1_subset_1 @ X28 @ (u1_struct_0 @ X24))
% 0.25/0.57          | ~ (v3_pre_topc @ X27 @ X24)
% 0.25/0.57          | ~ (r2_hidden @ X28 @ X27)
% 0.25/0.57          | ~ (r1_tarski @ X27 @ (u1_struct_0 @ X26))
% 0.25/0.57          | (r1_tmap_1 @ X24 @ X23 @ X29 @ X28)
% 0.25/0.57          | ~ (r1_tmap_1 @ X26 @ X23 @ 
% 0.25/0.57               (k3_tmap_1 @ X25 @ X23 @ X24 @ X26 @ X29) @ X28)
% 0.25/0.57          | ~ (m1_subset_1 @ X28 @ (u1_struct_0 @ X26))
% 0.25/0.57          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 0.25/0.57          | ~ (m1_pre_topc @ X26 @ X24)
% 0.25/0.57          | ~ (m1_pre_topc @ X24 @ X25)
% 0.25/0.57          | (v2_struct_0 @ X24)
% 0.25/0.57          | ~ (l1_pre_topc @ X23)
% 0.25/0.57          | ~ (v2_pre_topc @ X23)
% 0.25/0.57          | (v2_struct_0 @ X23))),
% 0.25/0.57      inference('simplify', [status(thm)], ['73'])).
% 0.25/0.57  thf('75', plain,
% 0.25/0.57      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.25/0.57         ((v2_struct_0 @ sk_A)
% 0.25/0.57          | ~ (v2_pre_topc @ sk_A)
% 0.25/0.57          | ~ (l1_pre_topc @ sk_A)
% 0.25/0.57          | (v2_struct_0 @ sk_D)
% 0.25/0.57          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.25/0.57          | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.25/0.57          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))
% 0.25/0.57          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X1))
% 0.25/0.57          | ~ (r1_tmap_1 @ X1 @ sk_A @ 
% 0.25/0.57               (k3_tmap_1 @ X0 @ sk_A @ sk_D @ X1 @ sk_E) @ X3)
% 0.25/0.57          | (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ X3)
% 0.25/0.57          | ~ (r1_tarski @ X2 @ (u1_struct_0 @ X1))
% 0.25/0.57          | ~ (r2_hidden @ X3 @ X2)
% 0.25/0.57          | ~ (v3_pre_topc @ X2 @ sk_D)
% 0.25/0.57          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ sk_D))
% 0.25/0.57          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A))
% 0.25/0.57          | ~ (v1_funct_1 @ sk_E)
% 0.25/0.57          | ~ (m1_pre_topc @ X1 @ X0)
% 0.25/0.57          | (v2_struct_0 @ X1)
% 0.25/0.57          | ~ (l1_pre_topc @ X0)
% 0.25/0.57          | ~ (v2_pre_topc @ X0)
% 0.25/0.57          | (v2_struct_0 @ X0))),
% 0.25/0.57      inference('sup-', [status(thm)], ['72', '74'])).
% 0.25/0.57  thf('76', plain, ((v2_pre_topc @ sk_A)),
% 0.25/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.57  thf('77', plain, ((l1_pre_topc @ sk_A)),
% 0.25/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.57  thf('78', plain,
% 0.25/0.57      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A))),
% 0.25/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.57  thf('79', plain, ((v1_funct_1 @ sk_E)),
% 0.25/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.57  thf('80', plain,
% 0.25/0.57      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.25/0.57         ((v2_struct_0 @ sk_A)
% 0.25/0.57          | (v2_struct_0 @ sk_D)
% 0.25/0.57          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.25/0.57          | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.25/0.57          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))
% 0.25/0.57          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X1))
% 0.25/0.57          | ~ (r1_tmap_1 @ X1 @ sk_A @ 
% 0.25/0.57               (k3_tmap_1 @ X0 @ sk_A @ sk_D @ X1 @ sk_E) @ X3)
% 0.25/0.57          | (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ X3)
% 0.25/0.57          | ~ (r1_tarski @ X2 @ (u1_struct_0 @ X1))
% 0.25/0.57          | ~ (r2_hidden @ X3 @ X2)
% 0.25/0.57          | ~ (v3_pre_topc @ X2 @ sk_D)
% 0.25/0.57          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ sk_D))
% 0.25/0.57          | ~ (m1_pre_topc @ X1 @ X0)
% 0.25/0.57          | (v2_struct_0 @ X1)
% 0.25/0.57          | ~ (l1_pre_topc @ X0)
% 0.25/0.57          | ~ (v2_pre_topc @ X0)
% 0.25/0.57          | (v2_struct_0 @ X0))),
% 0.25/0.57      inference('demod', [status(thm)], ['75', '76', '77', '78', '79'])).
% 0.25/0.57  thf('81', plain,
% 0.25/0.57      (![X0 : $i]:
% 0.25/0.57         ((v2_struct_0 @ sk_B)
% 0.25/0.57          | ~ (v2_pre_topc @ sk_B)
% 0.25/0.57          | ~ (l1_pre_topc @ sk_B)
% 0.25/0.57          | (v2_struct_0 @ sk_C_1)
% 0.25/0.57          | ~ (m1_pre_topc @ sk_C_1 @ sk_B)
% 0.25/0.57          | ~ (m1_subset_1 @ sk_H @ (u1_struct_0 @ sk_D))
% 0.25/0.57          | ~ (v3_pre_topc @ X0 @ sk_D)
% 0.25/0.57          | ~ (r2_hidden @ sk_H @ X0)
% 0.25/0.57          | ~ (r1_tarski @ X0 @ (u1_struct_0 @ sk_C_1))
% 0.25/0.57          | (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H)
% 0.25/0.57          | ~ (m1_subset_1 @ sk_H @ (u1_struct_0 @ sk_C_1))
% 0.25/0.57          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))
% 0.25/0.57          | ~ (m1_pre_topc @ sk_C_1 @ sk_D)
% 0.25/0.57          | ~ (m1_pre_topc @ sk_D @ sk_B)
% 0.25/0.57          | (v2_struct_0 @ sk_D)
% 0.25/0.57          | (v2_struct_0 @ sk_A))),
% 0.25/0.57      inference('sup-', [status(thm)], ['71', '80'])).
% 0.25/0.57  thf('82', plain, ((v2_pre_topc @ sk_B)),
% 0.25/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.57  thf('83', plain, ((l1_pre_topc @ sk_B)),
% 0.25/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.57  thf('84', plain, ((m1_pre_topc @ sk_C_1 @ sk_B)),
% 0.25/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.57  thf('85', plain, ((m1_subset_1 @ sk_H @ (u1_struct_0 @ sk_D))),
% 0.25/0.57      inference('demod', [status(thm)], ['46', '47'])).
% 0.25/0.57  thf('86', plain, ((m1_subset_1 @ sk_H @ (u1_struct_0 @ sk_C_1))),
% 0.25/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.57  thf('87', plain, ((m1_pre_topc @ sk_C_1 @ sk_D)),
% 0.25/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.57  thf('88', plain, ((m1_pre_topc @ sk_D @ sk_B)),
% 0.25/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.57  thf('89', plain,
% 0.25/0.57      (![X0 : $i]:
% 0.25/0.57         ((v2_struct_0 @ sk_B)
% 0.25/0.57          | (v2_struct_0 @ sk_C_1)
% 0.25/0.57          | ~ (v3_pre_topc @ X0 @ sk_D)
% 0.25/0.57          | ~ (r2_hidden @ sk_H @ X0)
% 0.25/0.57          | ~ (r1_tarski @ X0 @ (u1_struct_0 @ sk_C_1))
% 0.25/0.57          | (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H)
% 0.25/0.57          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))
% 0.25/0.57          | (v2_struct_0 @ sk_D)
% 0.25/0.57          | (v2_struct_0 @ sk_A))),
% 0.25/0.57      inference('demod', [status(thm)],
% 0.25/0.57                ['81', '82', '83', '84', '85', '86', '87', '88'])).
% 0.25/0.57  thf('90', plain,
% 0.25/0.57      (((v2_struct_0 @ sk_A)
% 0.25/0.57        | (v2_struct_0 @ sk_D)
% 0.25/0.57        | (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H)
% 0.25/0.57        | ~ (r1_tarski @ sk_F @ (u1_struct_0 @ sk_C_1))
% 0.25/0.57        | ~ (r2_hidden @ sk_H @ sk_F)
% 0.25/0.57        | ~ (v3_pre_topc @ sk_F @ sk_D)
% 0.25/0.57        | (v2_struct_0 @ sk_C_1)
% 0.25/0.57        | (v2_struct_0 @ sk_B))),
% 0.25/0.57      inference('sup-', [status(thm)], ['23', '89'])).
% 0.25/0.57  thf('91', plain, ((r1_tarski @ sk_F @ (u1_struct_0 @ sk_C_1))),
% 0.25/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.57  thf('92', plain, ((r2_hidden @ sk_G @ sk_F)),
% 0.25/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.57  thf('93', plain, (((sk_G) = (sk_H))),
% 0.25/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.57  thf('94', plain, ((r2_hidden @ sk_H @ sk_F)),
% 0.25/0.57      inference('demod', [status(thm)], ['92', '93'])).
% 0.25/0.57  thf('95', plain,
% 0.25/0.57      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))),
% 0.25/0.57      inference('sup-', [status(thm)], ['21', '22'])).
% 0.25/0.57  thf('96', plain,
% 0.25/0.57      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.25/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.57  thf('97', plain,
% 0.25/0.57      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.25/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.57  thf(t9_tsep_1, axiom,
% 0.25/0.57    (![A:$i]:
% 0.25/0.57     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.25/0.57       ( ![B:$i]:
% 0.25/0.57         ( ( m1_pre_topc @ B @ A ) =>
% 0.25/0.57           ( ![C:$i]:
% 0.25/0.57             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.25/0.57               ( ![D:$i]:
% 0.25/0.57                 ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.25/0.57                   ( ![E:$i]:
% 0.25/0.57                     ( ( m1_subset_1 @
% 0.25/0.57                         E @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.25/0.57                       ( ( ( v3_pre_topc @ C @ A ) & 
% 0.25/0.57                           ( r1_tarski @ C @ ( u1_struct_0 @ B ) ) & 
% 0.25/0.57                           ( r1_tarski @ D @ C ) & ( ( D ) = ( E ) ) ) =>
% 0.25/0.57                         ( ( v3_pre_topc @ E @ B ) <=> ( v3_pre_topc @ D @ A ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.25/0.57  thf('98', plain,
% 0.25/0.57      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 0.25/0.57         (~ (m1_pre_topc @ X31 @ X32)
% 0.25/0.57          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (u1_struct_0 @ X32)))
% 0.25/0.57          | ~ (v3_pre_topc @ X34 @ X32)
% 0.25/0.57          | ~ (r1_tarski @ X34 @ (u1_struct_0 @ X31))
% 0.25/0.57          | ~ (r1_tarski @ X33 @ X34)
% 0.25/0.57          | ((X33) != (X35))
% 0.25/0.57          | ~ (v3_pre_topc @ X33 @ X32)
% 0.25/0.57          | (v3_pre_topc @ X35 @ X31)
% 0.25/0.57          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (u1_struct_0 @ X31)))
% 0.25/0.57          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (u1_struct_0 @ X32)))
% 0.25/0.57          | ~ (l1_pre_topc @ X32)
% 0.25/0.57          | ~ (v2_pre_topc @ X32))),
% 0.25/0.57      inference('cnf', [status(esa)], [t9_tsep_1])).
% 0.25/0.57  thf('99', plain,
% 0.25/0.57      (![X31 : $i, X32 : $i, X34 : $i, X35 : $i]:
% 0.25/0.57         (~ (v2_pre_topc @ X32)
% 0.25/0.57          | ~ (l1_pre_topc @ X32)
% 0.25/0.57          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (u1_struct_0 @ X32)))
% 0.25/0.57          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (u1_struct_0 @ X31)))
% 0.25/0.57          | (v3_pre_topc @ X35 @ X31)
% 0.25/0.57          | ~ (v3_pre_topc @ X35 @ X32)
% 0.25/0.57          | ~ (r1_tarski @ X35 @ X34)
% 0.25/0.57          | ~ (r1_tarski @ X34 @ (u1_struct_0 @ X31))
% 0.25/0.57          | ~ (v3_pre_topc @ X34 @ X32)
% 0.25/0.57          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (u1_struct_0 @ X32)))
% 0.25/0.57          | ~ (m1_pre_topc @ X31 @ X32))),
% 0.25/0.57      inference('simplify', [status(thm)], ['98'])).
% 0.25/0.57  thf('100', plain,
% 0.25/0.57      (![X0 : $i, X1 : $i]:
% 0.25/0.57         (~ (m1_pre_topc @ X0 @ sk_B)
% 0.25/0.57          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.25/0.57          | ~ (v3_pre_topc @ sk_F @ sk_B)
% 0.25/0.57          | ~ (r1_tarski @ sk_F @ (u1_struct_0 @ X0))
% 0.25/0.57          | ~ (r1_tarski @ X1 @ sk_F)
% 0.25/0.57          | ~ (v3_pre_topc @ X1 @ sk_B)
% 0.25/0.57          | (v3_pre_topc @ X1 @ X0)
% 0.25/0.57          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.25/0.57          | ~ (l1_pre_topc @ sk_B)
% 0.25/0.57          | ~ (v2_pre_topc @ sk_B))),
% 0.25/0.57      inference('sup-', [status(thm)], ['97', '99'])).
% 0.25/0.57  thf('101', plain, ((v3_pre_topc @ sk_F @ sk_B)),
% 0.25/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.57  thf('102', plain, ((l1_pre_topc @ sk_B)),
% 0.25/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.57  thf('103', plain, ((v2_pre_topc @ sk_B)),
% 0.25/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.57  thf('104', plain,
% 0.25/0.57      (![X0 : $i, X1 : $i]:
% 0.25/0.57         (~ (m1_pre_topc @ X0 @ sk_B)
% 0.25/0.57          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.25/0.57          | ~ (r1_tarski @ sk_F @ (u1_struct_0 @ X0))
% 0.25/0.57          | ~ (r1_tarski @ X1 @ sk_F)
% 0.25/0.57          | ~ (v3_pre_topc @ X1 @ sk_B)
% 0.25/0.57          | (v3_pre_topc @ X1 @ X0)
% 0.25/0.57          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.25/0.57      inference('demod', [status(thm)], ['100', '101', '102', '103'])).
% 0.25/0.57  thf('105', plain,
% 0.25/0.57      (![X0 : $i]:
% 0.25/0.57         (~ (m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.25/0.57          | (v3_pre_topc @ sk_F @ X0)
% 0.25/0.57          | ~ (v3_pre_topc @ sk_F @ sk_B)
% 0.25/0.57          | ~ (r1_tarski @ sk_F @ sk_F)
% 0.25/0.57          | ~ (r1_tarski @ sk_F @ (u1_struct_0 @ X0))
% 0.25/0.57          | ~ (m1_pre_topc @ X0 @ sk_B))),
% 0.25/0.57      inference('sup-', [status(thm)], ['96', '104'])).
% 0.25/0.57  thf('106', plain, ((v3_pre_topc @ sk_F @ sk_B)),
% 0.25/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.57  thf(d10_xboole_0, axiom,
% 0.25/0.57    (![A:$i,B:$i]:
% 0.25/0.57     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.25/0.57  thf('107', plain,
% 0.25/0.57      (![X4 : $i, X5 : $i]: ((r1_tarski @ X4 @ X5) | ((X4) != (X5)))),
% 0.25/0.57      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.25/0.57  thf('108', plain, (![X5 : $i]: (r1_tarski @ X5 @ X5)),
% 0.25/0.57      inference('simplify', [status(thm)], ['107'])).
% 0.25/0.57  thf('109', plain,
% 0.25/0.57      (![X0 : $i]:
% 0.25/0.57         (~ (m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.25/0.57          | (v3_pre_topc @ sk_F @ X0)
% 0.25/0.57          | ~ (r1_tarski @ sk_F @ (u1_struct_0 @ X0))
% 0.25/0.57          | ~ (m1_pre_topc @ X0 @ sk_B))),
% 0.25/0.57      inference('demod', [status(thm)], ['105', '106', '108'])).
% 0.25/0.57  thf('110', plain,
% 0.25/0.57      ((~ (m1_pre_topc @ sk_D @ sk_B)
% 0.25/0.57        | ~ (r1_tarski @ sk_F @ (u1_struct_0 @ sk_D))
% 0.25/0.57        | (v3_pre_topc @ sk_F @ sk_D))),
% 0.25/0.57      inference('sup-', [status(thm)], ['95', '109'])).
% 0.25/0.57  thf('111', plain, ((m1_pre_topc @ sk_D @ sk_B)),
% 0.25/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.57  thf('112', plain, ((r1_tarski @ sk_F @ (u1_struct_0 @ sk_D))),
% 0.25/0.57      inference('simplify', [status(thm)], ['20'])).
% 0.25/0.57  thf('113', plain, ((v3_pre_topc @ sk_F @ sk_D)),
% 0.25/0.57      inference('demod', [status(thm)], ['110', '111', '112'])).
% 0.25/0.57  thf('114', plain,
% 0.25/0.57      (((v2_struct_0 @ sk_A)
% 0.25/0.57        | (v2_struct_0 @ sk_D)
% 0.25/0.57        | (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H)
% 0.25/0.57        | (v2_struct_0 @ sk_C_1)
% 0.25/0.57        | (v2_struct_0 @ sk_B))),
% 0.25/0.57      inference('demod', [status(thm)], ['90', '91', '94', '113'])).
% 0.25/0.57  thf('115', plain,
% 0.25/0.57      ((~ (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G))
% 0.25/0.57         <= (~ ((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G)))),
% 0.25/0.57      inference('split', [status(esa)], ['58'])).
% 0.25/0.57  thf('116', plain, (((sk_G) = (sk_H))),
% 0.25/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.57  thf('117', plain,
% 0.25/0.57      ((~ (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H))
% 0.25/0.57         <= (~ ((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G)))),
% 0.25/0.57      inference('demod', [status(thm)], ['115', '116'])).
% 0.25/0.57  thf('118', plain,
% 0.25/0.57      (((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G))
% 0.25/0.57         <= (((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G)))),
% 0.25/0.57      inference('split', [status(esa)], ['24'])).
% 0.25/0.57  thf('119', plain, (((sk_G) = (sk_H))),
% 0.25/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.57  thf('120', plain,
% 0.25/0.57      (((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H))
% 0.25/0.57         <= (((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G)))),
% 0.25/0.57      inference('demod', [status(thm)], ['118', '119'])).
% 0.25/0.57  thf('121', plain,
% 0.25/0.57      ((~ (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H))
% 0.25/0.57         <= (~ ((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H)))),
% 0.25/0.57      inference('split', [status(esa)], ['28'])).
% 0.25/0.57  thf('122', plain,
% 0.25/0.57      (~ ((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G)) | 
% 0.25/0.57       ((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H))),
% 0.25/0.57      inference('sup-', [status(thm)], ['120', '121'])).
% 0.25/0.57  thf('123', plain, (~ ((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G))),
% 0.25/0.57      inference('sat_resolution*', [status(thm)], ['29', '68', '122'])).
% 0.25/0.57  thf('124', plain, (~ (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H)),
% 0.25/0.57      inference('simpl_trail', [status(thm)], ['117', '123'])).
% 0.25/0.57  thf('125', plain,
% 0.25/0.57      (((v2_struct_0 @ sk_B)
% 0.25/0.57        | (v2_struct_0 @ sk_C_1)
% 0.25/0.57        | (v2_struct_0 @ sk_D)
% 0.25/0.57        | (v2_struct_0 @ sk_A))),
% 0.25/0.57      inference('sup-', [status(thm)], ['114', '124'])).
% 0.25/0.57  thf('126', plain, (~ (v2_struct_0 @ sk_A)),
% 0.25/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.57  thf('127', plain,
% 0.25/0.57      (((v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_C_1) | (v2_struct_0 @ sk_B))),
% 0.25/0.57      inference('sup-', [status(thm)], ['125', '126'])).
% 0.25/0.57  thf('128', plain, (~ (v2_struct_0 @ sk_D)),
% 0.25/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.57  thf('129', plain, (((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_C_1))),
% 0.25/0.57      inference('clc', [status(thm)], ['127', '128'])).
% 0.25/0.57  thf('130', plain, (~ (v2_struct_0 @ sk_B)),
% 0.25/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.57  thf('131', plain, ((v2_struct_0 @ sk_C_1)),
% 0.25/0.57      inference('clc', [status(thm)], ['129', '130'])).
% 0.25/0.57  thf('132', plain, ($false), inference('demod', [status(thm)], ['0', '131'])).
% 0.25/0.57  
% 0.25/0.57  % SZS output end Refutation
% 0.25/0.57  
% 0.41/0.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
