%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.6Kza8KDcg8

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:10:19 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  168 ( 467 expanded)
%              Number of leaves         :   33 ( 144 expanded)
%              Depth                    :   24
%              Number of atoms          : 2163 (18419 expanded)
%              Number of equality atoms :   16 ( 206 expanded)
%              Maximal formula depth    :   33 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_tmap_1_type,type,(
    r1_tmap_1: $i > $i > $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_H_type,type,(
    sk_H: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_G_type,type,(
    sk_G: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k3_tmap_1_type,type,(
    k3_tmap_1: $i > $i > $i > $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

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
    m1_pre_topc @ sk_C_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t1_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( m1_subset_1 @ ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('7',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( m1_pre_topc @ X12 @ X13 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X12 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ~ ( l1_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('8',plain,
    ( ~ ( l1_pre_topc @ sk_D )
    | ( m1_subset_1 @ ( u1_struct_0 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    m1_pre_topc @ sk_D @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('10',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( m1_pre_topc @ X10 @ X11 )
      | ( l1_pre_topc @ X10 )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('11',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( l1_pre_topc @ sk_D ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['8','13'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('15',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_tarski @ X7 @ X8 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('16',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_D ) )
      | ~ ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_F @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_F ) @ ( u1_struct_0 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['5','18'])).

thf('20',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('21',plain,
    ( ( r1_tarski @ sk_F @ ( u1_struct_0 @ sk_D ) )
    | ( r1_tarski @ sk_F @ ( u1_struct_0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    r1_tarski @ sk_F @ ( u1_struct_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    ! [X7: $i,X9: $i] :
      ( ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X9 ) )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('24',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,
    ( ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E ) @ sk_H )
    | ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E ) @ sk_H )
   <= ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E ) @ sk_H ) ),
    inference(split,[status(esa)],['25'])).

thf('27',plain,(
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

thf('28',plain,(
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

thf('29',plain,(
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
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,(
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
    inference('sup-',[status(thm)],['27','29'])).

thf('31',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
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
    inference(demod,[status(thm)],['30','31','32','33','34'])).

thf('36',plain,
    ( ! [X0: $i] :
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
        | ( v2_struct_0 @ sk_A ) )
   <= ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E ) @ sk_H ) ),
    inference('sup-',[status(thm)],['26','35'])).

thf('37',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    m1_pre_topc @ sk_C_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    sk_G = sk_H ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    m1_subset_1 @ sk_H @ ( u1_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,(
    m1_subset_1 @ sk_H @ ( u1_struct_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    m1_pre_topc @ sk_C_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    m1_pre_topc @ sk_D @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_B )
        | ( v2_struct_0 @ sk_C_1 )
        | ~ ( v3_pre_topc @ X0 @ sk_D )
        | ~ ( r2_hidden @ sk_H @ X0 )
        | ~ ( r1_tarski @ X0 @ ( u1_struct_0 @ sk_C_1 ) )
        | ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) )
        | ( v2_struct_0 @ sk_D )
        | ( v2_struct_0 @ sk_A ) )
   <= ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E ) @ sk_H ) ),
    inference(demod,[status(thm)],['36','37','38','39','42','43','44','45'])).

thf('47',plain,
    ( ~ ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E ) @ sk_H )
    | ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    sk_G = sk_H ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( ~ ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E ) @ sk_H )
    | ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,
    ( ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H )
    | ~ ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E ) @ sk_H ) ),
    inference(split,[status(esa)],['49'])).

thf('51',plain,(
    m1_pre_topc @ sk_C_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    m1_subset_1 @ sk_H @ ( u1_struct_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,
    ( ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E ) @ sk_H )
    | ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    sk_G = sk_H ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E ) @ sk_H )
    | ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,
    ( ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H )
   <= ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H ) ),
    inference(split,[status(esa)],['55'])).

thf('57',plain,(
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

thf('58',plain,(
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

thf('59',plain,(
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
    inference(simplify,[status(thm)],['58'])).

thf('60',plain,(
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
    inference('sup-',[status(thm)],['57','59'])).

thf('61',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
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
    inference(demod,[status(thm)],['60','61','62','63','64'])).

thf('66',plain,
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
    inference('sup-',[status(thm)],['56','65'])).

thf('67',plain,(
    m1_subset_1 @ sk_H @ ( u1_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('68',plain,
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
    inference(demod,[status(thm)],['66','67'])).

thf('69',plain,
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
    inference('sup-',[status(thm)],['52','68'])).

thf('70',plain,(
    m1_pre_topc @ sk_C_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,
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
    inference(demod,[status(thm)],['69','70'])).

thf('72',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ~ ( m1_pre_topc @ sk_D @ sk_B )
      | ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E ) @ sk_H )
      | ( v2_struct_0 @ sk_C_1 )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H ) ),
    inference('sup-',[status(thm)],['51','71'])).

thf('73',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    m1_pre_topc @ sk_D @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E ) @ sk_H )
      | ( v2_struct_0 @ sk_C_1 )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H ) ),
    inference(demod,[status(thm)],['72','73','74','75'])).

thf('77',plain,
    ( ~ ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E ) @ sk_H )
    | ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,
    ( ~ ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E ) @ sk_H )
   <= ~ ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E ) @ sk_H ) ),
    inference(split,[status(esa)],['77'])).

thf('79',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C_1 )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ~ ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E ) @ sk_H )
      & ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H ) ) ),
    inference('sup-',[status(thm)],['76','78'])).

thf('80',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_C_1 ) )
   <= ( ~ ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E ) @ sk_H )
      & ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H ) ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,
    ( ( ( v2_struct_0 @ sk_C_1 )
      | ( v2_struct_0 @ sk_D ) )
   <= ( ~ ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E ) @ sk_H )
      & ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H ) ) ),
    inference(clc,[status(thm)],['81','82'])).

thf('84',plain,(
    ~ ( v2_struct_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,
    ( ( v2_struct_0 @ sk_D )
   <= ( ~ ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E ) @ sk_H )
      & ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H ) ) ),
    inference(clc,[status(thm)],['83','84'])).

thf('86',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,
    ( ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E ) @ sk_H )
    | ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,
    ( ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E ) @ sk_H )
    | ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H ) ),
    inference(split,[status(esa)],['55'])).

thf('89',plain,(
    r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E ) @ sk_H ),
    inference('sat_resolution*',[status(thm)],['50','87','88'])).

thf('90',plain,(
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
    inference(simpl_trail,[status(thm)],['46','89'])).

thf('91',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D )
    | ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H )
    | ~ ( r1_tarski @ sk_F @ ( u1_struct_0 @ sk_C_1 ) )
    | ~ ( r2_hidden @ sk_H @ sk_F )
    | ~ ( v3_pre_topc @ sk_F @ sk_D )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['24','90'])).

thf('92',plain,(
    r1_tarski @ sk_F @ ( u1_struct_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    r2_hidden @ sk_G @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    sk_G = sk_H ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    r2_hidden @ sk_H @ sk_F ),
    inference(demod,[status(thm)],['93','94'])).

thf('96',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('97',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
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

thf('99',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i,X36: $i] :
      ( ~ ( m1_pre_topc @ X32 @ X33 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X33 ) ) )
      | ~ ( v3_pre_topc @ X35 @ X33 )
      | ~ ( r1_tarski @ X35 @ ( u1_struct_0 @ X32 ) )
      | ~ ( r1_tarski @ X34 @ X35 )
      | ( X34 != X36 )
      | ~ ( v3_pre_topc @ X34 @ X33 )
      | ( v3_pre_topc @ X36 @ X32 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X32 ) ) )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X33 ) ) )
      | ~ ( l1_pre_topc @ X33 )
      | ~ ( v2_pre_topc @ X33 ) ) ),
    inference(cnf,[status(esa)],[t9_tsep_1])).

thf('100',plain,(
    ! [X32: $i,X33: $i,X35: $i,X36: $i] :
      ( ~ ( v2_pre_topc @ X33 )
      | ~ ( l1_pre_topc @ X33 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X33 ) ) )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X32 ) ) )
      | ( v3_pre_topc @ X36 @ X32 )
      | ~ ( v3_pre_topc @ X36 @ X33 )
      | ~ ( r1_tarski @ X36 @ X35 )
      | ~ ( r1_tarski @ X35 @ ( u1_struct_0 @ X32 ) )
      | ~ ( v3_pre_topc @ X35 @ X33 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X33 ) ) )
      | ~ ( m1_pre_topc @ X32 @ X33 ) ) ),
    inference(simplify,[status(thm)],['99'])).

thf('101',plain,(
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
    inference('sup-',[status(thm)],['98','100'])).

thf('102',plain,(
    v3_pre_topc @ sk_F @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_B )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ~ ( r1_tarski @ sk_F @ ( u1_struct_0 @ X0 ) )
      | ~ ( r1_tarski @ X1 @ sk_F )
      | ~ ( v3_pre_topc @ X1 @ sk_B )
      | ( v3_pre_topc @ X1 @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['101','102','103','104'])).

thf('106',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( v3_pre_topc @ sk_F @ X0 )
      | ~ ( v3_pre_topc @ sk_F @ sk_B )
      | ~ ( r1_tarski @ sk_F @ sk_F )
      | ~ ( r1_tarski @ sk_F @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['97','105'])).

thf('107',plain,(
    v3_pre_topc @ sk_F @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('108',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ( X4 != X5 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('109',plain,(
    ! [X5: $i] :
      ( r1_tarski @ X5 @ X5 ) ),
    inference(simplify,[status(thm)],['108'])).

thf('110',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( v3_pre_topc @ sk_F @ X0 )
      | ~ ( r1_tarski @ sk_F @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ X0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['106','107','109'])).

thf('111',plain,
    ( ~ ( m1_pre_topc @ sk_D @ sk_B )
    | ~ ( r1_tarski @ sk_F @ ( u1_struct_0 @ sk_D ) )
    | ( v3_pre_topc @ sk_F @ sk_D ) ),
    inference('sup-',[status(thm)],['96','110'])).

thf('112',plain,(
    m1_pre_topc @ sk_D @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,(
    r1_tarski @ sk_F @ ( u1_struct_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['21'])).

thf('114',plain,(
    v3_pre_topc @ sk_F @ sk_D ),
    inference(demod,[status(thm)],['111','112','113'])).

thf('115',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D )
    | ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['91','92','95','114'])).

thf('116',plain,
    ( ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G )
   <= ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G ) ),
    inference(split,[status(esa)],['77'])).

thf('117',plain,(
    sk_G = sk_H ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,
    ( ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H )
   <= ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G ) ),
    inference(demod,[status(thm)],['116','117'])).

thf('119',plain,
    ( ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G )
   <= ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G ) ),
    inference(split,[status(esa)],['25'])).

thf('120',plain,(
    sk_G = sk_H ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('121',plain,
    ( ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H )
   <= ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G ) ),
    inference(demod,[status(thm)],['119','120'])).

thf('122',plain,
    ( ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H )
   <= ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H ) ),
    inference(split,[status(esa)],['49'])).

thf('123',plain,
    ( ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G )
    | ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H ) ),
    inference('sup-',[status(thm)],['121','122'])).

thf('124',plain,(
    ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G ) ),
    inference('sat_resolution*',[status(thm)],['50','87','123'])).

thf('125',plain,(
    ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H ) ),
    inference(simpl_trail,[status(thm)],['118','124'])).

thf('126',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['115','125'])).

thf('127',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('128',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['126','127'])).

thf('129',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('130',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C_1 ) ),
    inference(clc,[status(thm)],['128','129'])).

thf('131',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('132',plain,(
    v2_struct_0 @ sk_C_1 ),
    inference(clc,[status(thm)],['130','131'])).

thf('133',plain,(
    $false ),
    inference(demod,[status(thm)],['0','132'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.6Kza8KDcg8
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:37:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.52  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.52  % Solved by: fo/fo7.sh
% 0.20/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.52  % done 174 iterations in 0.065s
% 0.20/0.52  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.52  % SZS output start Refutation
% 0.20/0.52  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.52  thf(r1_tmap_1_type, type, r1_tmap_1: $i > $i > $i > $i > $o).
% 0.20/0.52  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.20/0.52  thf(sk_F_type, type, sk_F: $i).
% 0.20/0.52  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.20/0.52  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.20/0.52  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.52  thf(sk_E_type, type, sk_E: $i).
% 0.20/0.52  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.52  thf(sk_D_type, type, sk_D: $i).
% 0.20/0.52  thf(sk_H_type, type, sk_H: $i).
% 0.20/0.52  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.20/0.52  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.52  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.52  thf(sk_G_type, type, sk_G: $i).
% 0.20/0.52  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.20/0.52  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.20/0.52  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.52  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.20/0.52  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.52  thf(k3_tmap_1_type, type, k3_tmap_1: $i > $i > $i > $i > $i > $i).
% 0.20/0.52  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.20/0.52  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.20/0.52  thf(t85_tmap_1, conjecture,
% 0.20/0.52    (![A:$i]:
% 0.20/0.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.52       ( ![B:$i]:
% 0.20/0.52         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.20/0.52             ( l1_pre_topc @ B ) ) =>
% 0.20/0.52           ( ![C:$i]:
% 0.20/0.52             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ B ) ) =>
% 0.20/0.52               ( ![D:$i]:
% 0.20/0.52                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ B ) ) =>
% 0.20/0.52                   ( ![E:$i]:
% 0.20/0.52                     ( ( ( v1_funct_1 @ E ) & 
% 0.20/0.52                         ( v1_funct_2 @
% 0.20/0.52                           E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ A ) ) & 
% 0.20/0.52                         ( m1_subset_1 @
% 0.20/0.52                           E @ 
% 0.20/0.52                           ( k1_zfmisc_1 @
% 0.20/0.52                             ( k2_zfmisc_1 @
% 0.20/0.52                               ( u1_struct_0 @ D ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.20/0.52                       ( ( m1_pre_topc @ C @ D ) =>
% 0.20/0.52                         ( ![F:$i]:
% 0.20/0.52                           ( ( m1_subset_1 @
% 0.20/0.52                               F @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.20/0.52                             ( ![G:$i]:
% 0.20/0.52                               ( ( m1_subset_1 @ G @ ( u1_struct_0 @ D ) ) =>
% 0.20/0.52                                 ( ![H:$i]:
% 0.20/0.52                                   ( ( m1_subset_1 @ H @ ( u1_struct_0 @ C ) ) =>
% 0.20/0.52                                     ( ( ( v3_pre_topc @ F @ B ) & 
% 0.20/0.52                                         ( r2_hidden @ G @ F ) & 
% 0.20/0.52                                         ( r1_tarski @ F @ ( u1_struct_0 @ C ) ) & 
% 0.20/0.52                                         ( ( G ) = ( H ) ) ) =>
% 0.20/0.52                                       ( ( r1_tmap_1 @ D @ A @ E @ G ) <=>
% 0.20/0.52                                         ( r1_tmap_1 @
% 0.20/0.52                                           C @ A @ 
% 0.20/0.52                                           ( k3_tmap_1 @ B @ A @ D @ C @ E ) @ 
% 0.20/0.52                                           H ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.52    (~( ![A:$i]:
% 0.20/0.52        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.20/0.52            ( l1_pre_topc @ A ) ) =>
% 0.20/0.52          ( ![B:$i]:
% 0.20/0.52            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.20/0.52                ( l1_pre_topc @ B ) ) =>
% 0.20/0.52              ( ![C:$i]:
% 0.20/0.52                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ B ) ) =>
% 0.20/0.52                  ( ![D:$i]:
% 0.20/0.52                    ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ B ) ) =>
% 0.20/0.52                      ( ![E:$i]:
% 0.20/0.52                        ( ( ( v1_funct_1 @ E ) & 
% 0.20/0.52                            ( v1_funct_2 @
% 0.20/0.52                              E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ A ) ) & 
% 0.20/0.52                            ( m1_subset_1 @
% 0.20/0.52                              E @ 
% 0.20/0.52                              ( k1_zfmisc_1 @
% 0.20/0.52                                ( k2_zfmisc_1 @
% 0.20/0.52                                  ( u1_struct_0 @ D ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.20/0.52                          ( ( m1_pre_topc @ C @ D ) =>
% 0.20/0.52                            ( ![F:$i]:
% 0.20/0.52                              ( ( m1_subset_1 @
% 0.20/0.52                                  F @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.20/0.52                                ( ![G:$i]:
% 0.20/0.52                                  ( ( m1_subset_1 @ G @ ( u1_struct_0 @ D ) ) =>
% 0.20/0.52                                    ( ![H:$i]:
% 0.20/0.52                                      ( ( m1_subset_1 @ H @ ( u1_struct_0 @ C ) ) =>
% 0.20/0.52                                        ( ( ( v3_pre_topc @ F @ B ) & 
% 0.20/0.52                                            ( r2_hidden @ G @ F ) & 
% 0.20/0.52                                            ( r1_tarski @
% 0.20/0.52                                              F @ ( u1_struct_0 @ C ) ) & 
% 0.20/0.52                                            ( ( G ) = ( H ) ) ) =>
% 0.20/0.52                                          ( ( r1_tmap_1 @ D @ A @ E @ G ) <=>
% 0.20/0.52                                            ( r1_tmap_1 @
% 0.20/0.52                                              C @ A @ 
% 0.20/0.52                                              ( k3_tmap_1 @ B @ A @ D @ C @ E ) @ 
% 0.20/0.52                                              H ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.20/0.52    inference('cnf.neg', [status(esa)], [t85_tmap_1])).
% 0.20/0.52  thf('0', plain, (~ (v2_struct_0 @ sk_C_1)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf(d3_tarski, axiom,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( r1_tarski @ A @ B ) <=>
% 0.20/0.52       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.20/0.52  thf('1', plain,
% 0.20/0.52      (![X1 : $i, X3 : $i]:
% 0.20/0.52         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.20/0.52      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.52  thf('2', plain, ((r1_tarski @ sk_F @ (u1_struct_0 @ sk_C_1))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('3', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.52         (~ (r2_hidden @ X0 @ X1)
% 0.20/0.52          | (r2_hidden @ X0 @ X2)
% 0.20/0.52          | ~ (r1_tarski @ X1 @ X2))),
% 0.20/0.52      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.52  thf('4', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         ((r2_hidden @ X0 @ (u1_struct_0 @ sk_C_1)) | ~ (r2_hidden @ X0 @ sk_F))),
% 0.20/0.52      inference('sup-', [status(thm)], ['2', '3'])).
% 0.20/0.52  thf('5', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         ((r1_tarski @ sk_F @ X0)
% 0.20/0.52          | (r2_hidden @ (sk_C @ X0 @ sk_F) @ (u1_struct_0 @ sk_C_1)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['1', '4'])).
% 0.20/0.52  thf('6', plain, ((m1_pre_topc @ sk_C_1 @ sk_D)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf(t1_tsep_1, axiom,
% 0.20/0.52    (![A:$i]:
% 0.20/0.52     ( ( l1_pre_topc @ A ) =>
% 0.20/0.52       ( ![B:$i]:
% 0.20/0.52         ( ( m1_pre_topc @ B @ A ) =>
% 0.20/0.52           ( m1_subset_1 @
% 0.20/0.52             ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.20/0.52  thf('7', plain,
% 0.20/0.52      (![X12 : $i, X13 : $i]:
% 0.20/0.52         (~ (m1_pre_topc @ X12 @ X13)
% 0.20/0.52          | (m1_subset_1 @ (u1_struct_0 @ X12) @ 
% 0.20/0.52             (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.20/0.52          | ~ (l1_pre_topc @ X13))),
% 0.20/0.52      inference('cnf', [status(esa)], [t1_tsep_1])).
% 0.20/0.52  thf('8', plain,
% 0.20/0.52      ((~ (l1_pre_topc @ sk_D)
% 0.20/0.52        | (m1_subset_1 @ (u1_struct_0 @ sk_C_1) @ 
% 0.20/0.52           (k1_zfmisc_1 @ (u1_struct_0 @ sk_D))))),
% 0.20/0.52      inference('sup-', [status(thm)], ['6', '7'])).
% 0.20/0.52  thf('9', plain, ((m1_pre_topc @ sk_D @ sk_B)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf(dt_m1_pre_topc, axiom,
% 0.20/0.52    (![A:$i]:
% 0.20/0.52     ( ( l1_pre_topc @ A ) =>
% 0.20/0.52       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.20/0.52  thf('10', plain,
% 0.20/0.52      (![X10 : $i, X11 : $i]:
% 0.20/0.52         (~ (m1_pre_topc @ X10 @ X11)
% 0.20/0.52          | (l1_pre_topc @ X10)
% 0.20/0.52          | ~ (l1_pre_topc @ X11))),
% 0.20/0.52      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.20/0.52  thf('11', plain, ((~ (l1_pre_topc @ sk_B) | (l1_pre_topc @ sk_D))),
% 0.20/0.52      inference('sup-', [status(thm)], ['9', '10'])).
% 0.20/0.52  thf('12', plain, ((l1_pre_topc @ sk_B)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('13', plain, ((l1_pre_topc @ sk_D)),
% 0.20/0.52      inference('demod', [status(thm)], ['11', '12'])).
% 0.20/0.52  thf('14', plain,
% 0.20/0.52      ((m1_subset_1 @ (u1_struct_0 @ sk_C_1) @ 
% 0.20/0.52        (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))),
% 0.20/0.52      inference('demod', [status(thm)], ['8', '13'])).
% 0.20/0.52  thf(t3_subset, axiom,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.20/0.52  thf('15', plain,
% 0.20/0.52      (![X7 : $i, X8 : $i]:
% 0.20/0.52         ((r1_tarski @ X7 @ X8) | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8)))),
% 0.20/0.52      inference('cnf', [status(esa)], [t3_subset])).
% 0.20/0.52  thf('16', plain,
% 0.20/0.52      ((r1_tarski @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_D))),
% 0.20/0.52      inference('sup-', [status(thm)], ['14', '15'])).
% 0.20/0.52  thf('17', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.52         (~ (r2_hidden @ X0 @ X1)
% 0.20/0.52          | (r2_hidden @ X0 @ X2)
% 0.20/0.52          | ~ (r1_tarski @ X1 @ X2))),
% 0.20/0.52      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.52  thf('18', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         ((r2_hidden @ X0 @ (u1_struct_0 @ sk_D))
% 0.20/0.52          | ~ (r2_hidden @ X0 @ (u1_struct_0 @ sk_C_1)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['16', '17'])).
% 0.20/0.52  thf('19', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         ((r1_tarski @ sk_F @ X0)
% 0.20/0.52          | (r2_hidden @ (sk_C @ X0 @ sk_F) @ (u1_struct_0 @ sk_D)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['5', '18'])).
% 0.20/0.52  thf('20', plain,
% 0.20/0.52      (![X1 : $i, X3 : $i]:
% 0.20/0.52         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.20/0.52      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.52  thf('21', plain,
% 0.20/0.52      (((r1_tarski @ sk_F @ (u1_struct_0 @ sk_D))
% 0.20/0.52        | (r1_tarski @ sk_F @ (u1_struct_0 @ sk_D)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['19', '20'])).
% 0.20/0.52  thf('22', plain, ((r1_tarski @ sk_F @ (u1_struct_0 @ sk_D))),
% 0.20/0.52      inference('simplify', [status(thm)], ['21'])).
% 0.20/0.52  thf('23', plain,
% 0.20/0.52      (![X7 : $i, X9 : $i]:
% 0.20/0.52         ((m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X9)) | ~ (r1_tarski @ X7 @ X9))),
% 0.20/0.52      inference('cnf', [status(esa)], [t3_subset])).
% 0.20/0.52  thf('24', plain,
% 0.20/0.52      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['22', '23'])).
% 0.20/0.52  thf('25', plain,
% 0.20/0.52      (((r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.20/0.52         (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_H)
% 0.20/0.52        | (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('26', plain,
% 0.20/0.52      (((r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.20/0.52         (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_H))
% 0.20/0.52         <= (((r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.20/0.52               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_H)))),
% 0.20/0.52      inference('split', [status(esa)], ['25'])).
% 0.20/0.52  thf('27', plain,
% 0.20/0.52      ((m1_subset_1 @ sk_E @ 
% 0.20/0.52        (k1_zfmisc_1 @ 
% 0.20/0.52         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A))))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf(t84_tmap_1, axiom,
% 0.20/0.52    (![A:$i]:
% 0.20/0.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.52       ( ![B:$i]:
% 0.20/0.52         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.20/0.52             ( l1_pre_topc @ B ) ) =>
% 0.20/0.52           ( ![C:$i]:
% 0.20/0.52             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.20/0.52               ( ![D:$i]:
% 0.20/0.52                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.20/0.52                   ( ![E:$i]:
% 0.20/0.52                     ( ( ( v1_funct_1 @ E ) & 
% 0.20/0.52                         ( v1_funct_2 @
% 0.20/0.52                           E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 0.20/0.53                         ( m1_subset_1 @
% 0.20/0.53                           E @ 
% 0.20/0.53                           ( k1_zfmisc_1 @
% 0.20/0.53                             ( k2_zfmisc_1 @
% 0.20/0.53                               ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.20/0.53                       ( ( m1_pre_topc @ C @ D ) =>
% 0.20/0.53                         ( ![F:$i]:
% 0.20/0.53                           ( ( m1_subset_1 @
% 0.20/0.53                               F @ ( k1_zfmisc_1 @ ( u1_struct_0 @ D ) ) ) =>
% 0.20/0.53                             ( ![G:$i]:
% 0.20/0.53                               ( ( m1_subset_1 @ G @ ( u1_struct_0 @ D ) ) =>
% 0.20/0.53                                 ( ![H:$i]:
% 0.20/0.53                                   ( ( m1_subset_1 @ H @ ( u1_struct_0 @ C ) ) =>
% 0.20/0.53                                     ( ( ( v3_pre_topc @ F @ D ) & 
% 0.20/0.53                                         ( r2_hidden @ G @ F ) & 
% 0.20/0.53                                         ( r1_tarski @ F @ ( u1_struct_0 @ C ) ) & 
% 0.20/0.53                                         ( ( G ) = ( H ) ) ) =>
% 0.20/0.53                                       ( ( r1_tmap_1 @ D @ B @ E @ G ) <=>
% 0.20/0.53                                         ( r1_tmap_1 @
% 0.20/0.53                                           C @ B @ 
% 0.20/0.53                                           ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ 
% 0.20/0.53                                           H ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.53  thf('28', plain,
% 0.20/0.53      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i, X30 : $i, 
% 0.20/0.53         X31 : $i]:
% 0.20/0.53         ((v2_struct_0 @ X24)
% 0.20/0.53          | ~ (v2_pre_topc @ X24)
% 0.20/0.53          | ~ (l1_pre_topc @ X24)
% 0.20/0.53          | (v2_struct_0 @ X25)
% 0.20/0.53          | ~ (m1_pre_topc @ X25 @ X26)
% 0.20/0.53          | ~ (m1_pre_topc @ X27 @ X25)
% 0.20/0.53          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 0.20/0.53          | ~ (m1_subset_1 @ X29 @ (u1_struct_0 @ X27))
% 0.20/0.53          | ~ (r1_tmap_1 @ X27 @ X24 @ 
% 0.20/0.53               (k3_tmap_1 @ X26 @ X24 @ X25 @ X27 @ X30) @ X29)
% 0.20/0.53          | (r1_tmap_1 @ X25 @ X24 @ X30 @ X31)
% 0.20/0.53          | ((X31) != (X29))
% 0.20/0.53          | ~ (r1_tarski @ X28 @ (u1_struct_0 @ X27))
% 0.20/0.53          | ~ (r2_hidden @ X31 @ X28)
% 0.20/0.53          | ~ (v3_pre_topc @ X28 @ X25)
% 0.20/0.53          | ~ (m1_subset_1 @ X31 @ (u1_struct_0 @ X25))
% 0.20/0.53          | ~ (m1_subset_1 @ X30 @ 
% 0.20/0.53               (k1_zfmisc_1 @ 
% 0.20/0.53                (k2_zfmisc_1 @ (u1_struct_0 @ X25) @ (u1_struct_0 @ X24))))
% 0.20/0.53          | ~ (v1_funct_2 @ X30 @ (u1_struct_0 @ X25) @ (u1_struct_0 @ X24))
% 0.20/0.53          | ~ (v1_funct_1 @ X30)
% 0.20/0.53          | ~ (m1_pre_topc @ X27 @ X26)
% 0.20/0.53          | (v2_struct_0 @ X27)
% 0.20/0.53          | ~ (l1_pre_topc @ X26)
% 0.20/0.53          | ~ (v2_pre_topc @ X26)
% 0.20/0.53          | (v2_struct_0 @ X26))),
% 0.20/0.53      inference('cnf', [status(esa)], [t84_tmap_1])).
% 0.20/0.53  thf('29', plain,
% 0.20/0.53      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 0.20/0.53         ((v2_struct_0 @ X26)
% 0.20/0.53          | ~ (v2_pre_topc @ X26)
% 0.20/0.53          | ~ (l1_pre_topc @ X26)
% 0.20/0.53          | (v2_struct_0 @ X27)
% 0.20/0.53          | ~ (m1_pre_topc @ X27 @ X26)
% 0.20/0.53          | ~ (v1_funct_1 @ X30)
% 0.20/0.53          | ~ (v1_funct_2 @ X30 @ (u1_struct_0 @ X25) @ (u1_struct_0 @ X24))
% 0.20/0.53          | ~ (m1_subset_1 @ X30 @ 
% 0.20/0.53               (k1_zfmisc_1 @ 
% 0.20/0.53                (k2_zfmisc_1 @ (u1_struct_0 @ X25) @ (u1_struct_0 @ X24))))
% 0.20/0.53          | ~ (m1_subset_1 @ X29 @ (u1_struct_0 @ X25))
% 0.20/0.53          | ~ (v3_pre_topc @ X28 @ X25)
% 0.20/0.53          | ~ (r2_hidden @ X29 @ X28)
% 0.20/0.53          | ~ (r1_tarski @ X28 @ (u1_struct_0 @ X27))
% 0.20/0.53          | (r1_tmap_1 @ X25 @ X24 @ X30 @ X29)
% 0.20/0.53          | ~ (r1_tmap_1 @ X27 @ X24 @ 
% 0.20/0.53               (k3_tmap_1 @ X26 @ X24 @ X25 @ X27 @ X30) @ X29)
% 0.20/0.53          | ~ (m1_subset_1 @ X29 @ (u1_struct_0 @ X27))
% 0.20/0.53          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 0.20/0.53          | ~ (m1_pre_topc @ X27 @ X25)
% 0.20/0.53          | ~ (m1_pre_topc @ X25 @ X26)
% 0.20/0.53          | (v2_struct_0 @ X25)
% 0.20/0.53          | ~ (l1_pre_topc @ X24)
% 0.20/0.53          | ~ (v2_pre_topc @ X24)
% 0.20/0.53          | (v2_struct_0 @ X24))),
% 0.20/0.53      inference('simplify', [status(thm)], ['28'])).
% 0.20/0.53  thf('30', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.53         ((v2_struct_0 @ sk_A)
% 0.20/0.53          | ~ (v2_pre_topc @ sk_A)
% 0.20/0.53          | ~ (l1_pre_topc @ sk_A)
% 0.20/0.53          | (v2_struct_0 @ sk_D)
% 0.20/0.53          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.20/0.53          | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.20/0.53          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))
% 0.20/0.53          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X1))
% 0.20/0.53          | ~ (r1_tmap_1 @ X1 @ sk_A @ 
% 0.20/0.53               (k3_tmap_1 @ X0 @ sk_A @ sk_D @ X1 @ sk_E) @ X3)
% 0.20/0.53          | (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ X3)
% 0.20/0.53          | ~ (r1_tarski @ X2 @ (u1_struct_0 @ X1))
% 0.20/0.53          | ~ (r2_hidden @ X3 @ X2)
% 0.20/0.53          | ~ (v3_pre_topc @ X2 @ sk_D)
% 0.20/0.53          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ sk_D))
% 0.20/0.53          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A))
% 0.20/0.53          | ~ (v1_funct_1 @ sk_E)
% 0.20/0.53          | ~ (m1_pre_topc @ X1 @ X0)
% 0.20/0.53          | (v2_struct_0 @ X1)
% 0.20/0.53          | ~ (l1_pre_topc @ X0)
% 0.20/0.53          | ~ (v2_pre_topc @ X0)
% 0.20/0.53          | (v2_struct_0 @ X0))),
% 0.20/0.53      inference('sup-', [status(thm)], ['27', '29'])).
% 0.20/0.53  thf('31', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('32', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('33', plain,
% 0.20/0.53      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('34', plain, ((v1_funct_1 @ sk_E)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('35', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.53         ((v2_struct_0 @ sk_A)
% 0.20/0.53          | (v2_struct_0 @ sk_D)
% 0.20/0.53          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.20/0.53          | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.20/0.53          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))
% 0.20/0.53          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X1))
% 0.20/0.53          | ~ (r1_tmap_1 @ X1 @ sk_A @ 
% 0.20/0.53               (k3_tmap_1 @ X0 @ sk_A @ sk_D @ X1 @ sk_E) @ X3)
% 0.20/0.53          | (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ X3)
% 0.20/0.53          | ~ (r1_tarski @ X2 @ (u1_struct_0 @ X1))
% 0.20/0.53          | ~ (r2_hidden @ X3 @ X2)
% 0.20/0.53          | ~ (v3_pre_topc @ X2 @ sk_D)
% 0.20/0.53          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ sk_D))
% 0.20/0.53          | ~ (m1_pre_topc @ X1 @ X0)
% 0.20/0.53          | (v2_struct_0 @ X1)
% 0.20/0.53          | ~ (l1_pre_topc @ X0)
% 0.20/0.53          | ~ (v2_pre_topc @ X0)
% 0.20/0.53          | (v2_struct_0 @ X0))),
% 0.20/0.53      inference('demod', [status(thm)], ['30', '31', '32', '33', '34'])).
% 0.20/0.53  thf('36', plain,
% 0.20/0.53      ((![X0 : $i]:
% 0.20/0.53          ((v2_struct_0 @ sk_B)
% 0.20/0.53           | ~ (v2_pre_topc @ sk_B)
% 0.20/0.53           | ~ (l1_pre_topc @ sk_B)
% 0.20/0.53           | (v2_struct_0 @ sk_C_1)
% 0.20/0.53           | ~ (m1_pre_topc @ sk_C_1 @ sk_B)
% 0.20/0.53           | ~ (m1_subset_1 @ sk_H @ (u1_struct_0 @ sk_D))
% 0.20/0.53           | ~ (v3_pre_topc @ X0 @ sk_D)
% 0.20/0.53           | ~ (r2_hidden @ sk_H @ X0)
% 0.20/0.53           | ~ (r1_tarski @ X0 @ (u1_struct_0 @ sk_C_1))
% 0.20/0.53           | (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H)
% 0.20/0.53           | ~ (m1_subset_1 @ sk_H @ (u1_struct_0 @ sk_C_1))
% 0.20/0.53           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))
% 0.20/0.53           | ~ (m1_pre_topc @ sk_C_1 @ sk_D)
% 0.20/0.53           | ~ (m1_pre_topc @ sk_D @ sk_B)
% 0.20/0.53           | (v2_struct_0 @ sk_D)
% 0.20/0.53           | (v2_struct_0 @ sk_A)))
% 0.20/0.53         <= (((r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.20/0.53               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_H)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['26', '35'])).
% 0.20/0.53  thf('37', plain, ((v2_pre_topc @ sk_B)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('38', plain, ((l1_pre_topc @ sk_B)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('39', plain, ((m1_pre_topc @ sk_C_1 @ sk_B)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('40', plain, ((m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_D))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('41', plain, (((sk_G) = (sk_H))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('42', plain, ((m1_subset_1 @ sk_H @ (u1_struct_0 @ sk_D))),
% 0.20/0.53      inference('demod', [status(thm)], ['40', '41'])).
% 0.20/0.53  thf('43', plain, ((m1_subset_1 @ sk_H @ (u1_struct_0 @ sk_C_1))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('44', plain, ((m1_pre_topc @ sk_C_1 @ sk_D)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('45', plain, ((m1_pre_topc @ sk_D @ sk_B)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('46', plain,
% 0.20/0.53      ((![X0 : $i]:
% 0.20/0.53          ((v2_struct_0 @ sk_B)
% 0.20/0.53           | (v2_struct_0 @ sk_C_1)
% 0.20/0.53           | ~ (v3_pre_topc @ X0 @ sk_D)
% 0.20/0.53           | ~ (r2_hidden @ sk_H @ X0)
% 0.20/0.53           | ~ (r1_tarski @ X0 @ (u1_struct_0 @ sk_C_1))
% 0.20/0.53           | (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H)
% 0.20/0.53           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))
% 0.20/0.53           | (v2_struct_0 @ sk_D)
% 0.20/0.53           | (v2_struct_0 @ sk_A)))
% 0.20/0.53         <= (((r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.20/0.53               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_H)))),
% 0.20/0.53      inference('demod', [status(thm)],
% 0.20/0.53                ['36', '37', '38', '39', '42', '43', '44', '45'])).
% 0.20/0.53  thf('47', plain,
% 0.20/0.53      ((~ (r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.20/0.53           (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_H)
% 0.20/0.53        | ~ (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('48', plain, (((sk_G) = (sk_H))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('49', plain,
% 0.20/0.53      ((~ (r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.20/0.53           (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_H)
% 0.20/0.53        | ~ (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H))),
% 0.20/0.53      inference('demod', [status(thm)], ['47', '48'])).
% 0.20/0.53  thf('50', plain,
% 0.20/0.53      (~ ((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H)) | 
% 0.20/0.53       ~
% 0.20/0.53       ((r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.20/0.53         (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_H))),
% 0.20/0.53      inference('split', [status(esa)], ['49'])).
% 0.20/0.53  thf('51', plain, ((m1_pre_topc @ sk_C_1 @ sk_B)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('52', plain, ((m1_subset_1 @ sk_H @ (u1_struct_0 @ sk_C_1))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('53', plain,
% 0.20/0.53      (((r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.20/0.53         (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_H)
% 0.20/0.53        | (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('54', plain, (((sk_G) = (sk_H))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('55', plain,
% 0.20/0.53      (((r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.20/0.53         (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_H)
% 0.20/0.53        | (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H))),
% 0.20/0.53      inference('demod', [status(thm)], ['53', '54'])).
% 0.20/0.53  thf('56', plain,
% 0.20/0.53      (((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H))
% 0.20/0.53         <= (((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H)))),
% 0.20/0.53      inference('split', [status(esa)], ['55'])).
% 0.20/0.53  thf('57', plain,
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
% 0.20/0.53  thf('58', plain,
% 0.20/0.53      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 0.20/0.53         ((v2_struct_0 @ X17)
% 0.20/0.53          | ~ (v2_pre_topc @ X17)
% 0.20/0.53          | ~ (l1_pre_topc @ X17)
% 0.20/0.53          | (v2_struct_0 @ X18)
% 0.20/0.53          | ~ (m1_pre_topc @ X18 @ X19)
% 0.20/0.53          | ~ (m1_subset_1 @ X20 @ (u1_struct_0 @ X21))
% 0.20/0.53          | ~ (m1_pre_topc @ X18 @ X21)
% 0.20/0.53          | ~ (r1_tmap_1 @ X21 @ X17 @ X22 @ X20)
% 0.20/0.53          | ((X20) != (X23))
% 0.20/0.53          | (r1_tmap_1 @ X18 @ X17 @ 
% 0.20/0.53             (k3_tmap_1 @ X19 @ X17 @ X21 @ X18 @ X22) @ X23)
% 0.20/0.53          | ~ (m1_subset_1 @ X23 @ (u1_struct_0 @ X18))
% 0.20/0.53          | ~ (m1_subset_1 @ X22 @ 
% 0.20/0.53               (k1_zfmisc_1 @ 
% 0.20/0.53                (k2_zfmisc_1 @ (u1_struct_0 @ X21) @ (u1_struct_0 @ X17))))
% 0.20/0.53          | ~ (v1_funct_2 @ X22 @ (u1_struct_0 @ X21) @ (u1_struct_0 @ X17))
% 0.20/0.53          | ~ (v1_funct_1 @ X22)
% 0.20/0.53          | ~ (m1_pre_topc @ X21 @ X19)
% 0.20/0.53          | (v2_struct_0 @ X21)
% 0.20/0.53          | ~ (l1_pre_topc @ X19)
% 0.20/0.53          | ~ (v2_pre_topc @ X19)
% 0.20/0.53          | (v2_struct_0 @ X19))),
% 0.20/0.53      inference('cnf', [status(esa)], [t81_tmap_1])).
% 0.20/0.53  thf('59', plain,
% 0.20/0.53      (![X17 : $i, X18 : $i, X19 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 0.20/0.53         ((v2_struct_0 @ X19)
% 0.20/0.53          | ~ (v2_pre_topc @ X19)
% 0.20/0.53          | ~ (l1_pre_topc @ X19)
% 0.20/0.53          | (v2_struct_0 @ X21)
% 0.20/0.53          | ~ (m1_pre_topc @ X21 @ X19)
% 0.20/0.53          | ~ (v1_funct_1 @ X22)
% 0.20/0.53          | ~ (v1_funct_2 @ X22 @ (u1_struct_0 @ X21) @ (u1_struct_0 @ X17))
% 0.20/0.53          | ~ (m1_subset_1 @ X22 @ 
% 0.20/0.53               (k1_zfmisc_1 @ 
% 0.20/0.53                (k2_zfmisc_1 @ (u1_struct_0 @ X21) @ (u1_struct_0 @ X17))))
% 0.20/0.53          | ~ (m1_subset_1 @ X23 @ (u1_struct_0 @ X18))
% 0.20/0.53          | (r1_tmap_1 @ X18 @ X17 @ 
% 0.20/0.53             (k3_tmap_1 @ X19 @ X17 @ X21 @ X18 @ X22) @ X23)
% 0.20/0.53          | ~ (r1_tmap_1 @ X21 @ X17 @ X22 @ X23)
% 0.20/0.53          | ~ (m1_pre_topc @ X18 @ X21)
% 0.20/0.53          | ~ (m1_subset_1 @ X23 @ (u1_struct_0 @ X21))
% 0.20/0.53          | ~ (m1_pre_topc @ X18 @ X19)
% 0.20/0.53          | (v2_struct_0 @ X18)
% 0.20/0.53          | ~ (l1_pre_topc @ X17)
% 0.20/0.53          | ~ (v2_pre_topc @ X17)
% 0.20/0.53          | (v2_struct_0 @ X17))),
% 0.20/0.53      inference('simplify', [status(thm)], ['58'])).
% 0.20/0.53  thf('60', plain,
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
% 0.20/0.53      inference('sup-', [status(thm)], ['57', '59'])).
% 0.20/0.53  thf('61', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('62', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('63', plain,
% 0.20/0.53      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('64', plain, ((v1_funct_1 @ sk_E)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('65', plain,
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
% 0.20/0.53      inference('demod', [status(thm)], ['60', '61', '62', '63', '64'])).
% 0.20/0.53  thf('66', plain,
% 0.20/0.53      ((![X0 : $i, X1 : $i]:
% 0.20/0.53          ((v2_struct_0 @ X0)
% 0.20/0.53           | ~ (v2_pre_topc @ X0)
% 0.20/0.53           | ~ (l1_pre_topc @ X0)
% 0.20/0.53           | (v2_struct_0 @ sk_D)
% 0.20/0.53           | ~ (m1_pre_topc @ sk_D @ X0)
% 0.20/0.53           | ~ (m1_subset_1 @ sk_H @ (u1_struct_0 @ X1))
% 0.20/0.53           | (r1_tmap_1 @ X1 @ sk_A @ 
% 0.20/0.53              (k3_tmap_1 @ X0 @ sk_A @ sk_D @ X1 @ sk_E) @ sk_H)
% 0.20/0.53           | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.20/0.53           | ~ (m1_subset_1 @ sk_H @ (u1_struct_0 @ sk_D))
% 0.20/0.53           | ~ (m1_pre_topc @ X1 @ X0)
% 0.20/0.53           | (v2_struct_0 @ X1)
% 0.20/0.53           | (v2_struct_0 @ sk_A)))
% 0.20/0.53         <= (((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['56', '65'])).
% 0.20/0.53  thf('67', plain, ((m1_subset_1 @ sk_H @ (u1_struct_0 @ sk_D))),
% 0.20/0.53      inference('demod', [status(thm)], ['40', '41'])).
% 0.20/0.53  thf('68', plain,
% 0.20/0.53      ((![X0 : $i, X1 : $i]:
% 0.20/0.53          ((v2_struct_0 @ X0)
% 0.20/0.53           | ~ (v2_pre_topc @ X0)
% 0.20/0.53           | ~ (l1_pre_topc @ X0)
% 0.20/0.53           | (v2_struct_0 @ sk_D)
% 0.20/0.53           | ~ (m1_pre_topc @ sk_D @ X0)
% 0.20/0.53           | ~ (m1_subset_1 @ sk_H @ (u1_struct_0 @ X1))
% 0.20/0.53           | (r1_tmap_1 @ X1 @ sk_A @ 
% 0.20/0.53              (k3_tmap_1 @ X0 @ sk_A @ sk_D @ X1 @ sk_E) @ sk_H)
% 0.20/0.53           | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.20/0.53           | ~ (m1_pre_topc @ X1 @ X0)
% 0.20/0.53           | (v2_struct_0 @ X1)
% 0.20/0.53           | (v2_struct_0 @ sk_A)))
% 0.20/0.53         <= (((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H)))),
% 0.20/0.53      inference('demod', [status(thm)], ['66', '67'])).
% 0.20/0.53  thf('69', plain,
% 0.20/0.53      ((![X0 : $i]:
% 0.20/0.53          ((v2_struct_0 @ sk_A)
% 0.20/0.53           | (v2_struct_0 @ sk_C_1)
% 0.20/0.53           | ~ (m1_pre_topc @ sk_C_1 @ X0)
% 0.20/0.53           | ~ (m1_pre_topc @ sk_C_1 @ sk_D)
% 0.20/0.53           | (r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.20/0.53              (k3_tmap_1 @ X0 @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_H)
% 0.20/0.53           | ~ (m1_pre_topc @ sk_D @ X0)
% 0.20/0.53           | (v2_struct_0 @ sk_D)
% 0.20/0.53           | ~ (l1_pre_topc @ X0)
% 0.20/0.53           | ~ (v2_pre_topc @ X0)
% 0.20/0.53           | (v2_struct_0 @ X0)))
% 0.20/0.53         <= (((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['52', '68'])).
% 0.20/0.53  thf('70', plain, ((m1_pre_topc @ sk_C_1 @ sk_D)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('71', plain,
% 0.20/0.53      ((![X0 : $i]:
% 0.20/0.53          ((v2_struct_0 @ sk_A)
% 0.20/0.53           | (v2_struct_0 @ sk_C_1)
% 0.20/0.53           | ~ (m1_pre_topc @ sk_C_1 @ X0)
% 0.20/0.53           | (r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.20/0.53              (k3_tmap_1 @ X0 @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_H)
% 0.20/0.53           | ~ (m1_pre_topc @ sk_D @ X0)
% 0.20/0.53           | (v2_struct_0 @ sk_D)
% 0.20/0.53           | ~ (l1_pre_topc @ X0)
% 0.20/0.53           | ~ (v2_pre_topc @ X0)
% 0.20/0.53           | (v2_struct_0 @ X0)))
% 0.20/0.53         <= (((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H)))),
% 0.20/0.53      inference('demod', [status(thm)], ['69', '70'])).
% 0.20/0.53  thf('72', plain,
% 0.20/0.53      ((((v2_struct_0 @ sk_B)
% 0.20/0.53         | ~ (v2_pre_topc @ sk_B)
% 0.20/0.53         | ~ (l1_pre_topc @ sk_B)
% 0.20/0.53         | (v2_struct_0 @ sk_D)
% 0.20/0.53         | ~ (m1_pre_topc @ sk_D @ sk_B)
% 0.20/0.53         | (r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.20/0.53            (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_H)
% 0.20/0.53         | (v2_struct_0 @ sk_C_1)
% 0.20/0.53         | (v2_struct_0 @ sk_A)))
% 0.20/0.53         <= (((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['51', '71'])).
% 0.20/0.53  thf('73', plain, ((v2_pre_topc @ sk_B)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('74', plain, ((l1_pre_topc @ sk_B)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('75', plain, ((m1_pre_topc @ sk_D @ sk_B)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('76', plain,
% 0.20/0.53      ((((v2_struct_0 @ sk_B)
% 0.20/0.53         | (v2_struct_0 @ sk_D)
% 0.20/0.53         | (r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.20/0.53            (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_H)
% 0.20/0.53         | (v2_struct_0 @ sk_C_1)
% 0.20/0.53         | (v2_struct_0 @ sk_A)))
% 0.20/0.53         <= (((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H)))),
% 0.20/0.53      inference('demod', [status(thm)], ['72', '73', '74', '75'])).
% 0.20/0.53  thf('77', plain,
% 0.20/0.53      ((~ (r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.20/0.53           (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_H)
% 0.20/0.53        | ~ (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('78', plain,
% 0.20/0.53      ((~ (r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.20/0.53           (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_H))
% 0.20/0.53         <= (~
% 0.20/0.53             ((r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.20/0.53               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_H)))),
% 0.20/0.53      inference('split', [status(esa)], ['77'])).
% 0.20/0.53  thf('79', plain,
% 0.20/0.53      ((((v2_struct_0 @ sk_A)
% 0.20/0.53         | (v2_struct_0 @ sk_C_1)
% 0.20/0.53         | (v2_struct_0 @ sk_D)
% 0.20/0.53         | (v2_struct_0 @ sk_B)))
% 0.20/0.53         <= (~
% 0.20/0.53             ((r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.20/0.53               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_H)) & 
% 0.20/0.53             ((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['76', '78'])).
% 0.20/0.53  thf('80', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('81', plain,
% 0.20/0.53      ((((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_C_1)))
% 0.20/0.53         <= (~
% 0.20/0.53             ((r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.20/0.53               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_H)) & 
% 0.20/0.53             ((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['79', '80'])).
% 0.20/0.53  thf('82', plain, (~ (v2_struct_0 @ sk_B)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('83', plain,
% 0.20/0.53      ((((v2_struct_0 @ sk_C_1) | (v2_struct_0 @ sk_D)))
% 0.20/0.53         <= (~
% 0.20/0.53             ((r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.20/0.53               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_H)) & 
% 0.20/0.53             ((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H)))),
% 0.20/0.53      inference('clc', [status(thm)], ['81', '82'])).
% 0.20/0.53  thf('84', plain, (~ (v2_struct_0 @ sk_C_1)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('85', plain,
% 0.20/0.53      (((v2_struct_0 @ sk_D))
% 0.20/0.53         <= (~
% 0.20/0.53             ((r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.20/0.53               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_H)) & 
% 0.20/0.53             ((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H)))),
% 0.20/0.53      inference('clc', [status(thm)], ['83', '84'])).
% 0.20/0.53  thf('86', plain, (~ (v2_struct_0 @ sk_D)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('87', plain,
% 0.20/0.53      (((r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.20/0.53         (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_H)) | 
% 0.20/0.53       ~ ((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H))),
% 0.20/0.53      inference('sup-', [status(thm)], ['85', '86'])).
% 0.20/0.53  thf('88', plain,
% 0.20/0.53      (((r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.20/0.53         (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_H)) | 
% 0.20/0.53       ((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H))),
% 0.20/0.53      inference('split', [status(esa)], ['55'])).
% 0.20/0.53  thf('89', plain,
% 0.20/0.53      (((r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.20/0.53         (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_H))),
% 0.20/0.53      inference('sat_resolution*', [status(thm)], ['50', '87', '88'])).
% 0.20/0.53  thf('90', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         ((v2_struct_0 @ sk_B)
% 0.20/0.53          | (v2_struct_0 @ sk_C_1)
% 0.20/0.53          | ~ (v3_pre_topc @ X0 @ sk_D)
% 0.20/0.53          | ~ (r2_hidden @ sk_H @ X0)
% 0.20/0.53          | ~ (r1_tarski @ X0 @ (u1_struct_0 @ sk_C_1))
% 0.20/0.53          | (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H)
% 0.20/0.53          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))
% 0.20/0.53          | (v2_struct_0 @ sk_D)
% 0.20/0.53          | (v2_struct_0 @ sk_A))),
% 0.20/0.53      inference('simpl_trail', [status(thm)], ['46', '89'])).
% 0.20/0.53  thf('91', plain,
% 0.20/0.53      (((v2_struct_0 @ sk_A)
% 0.20/0.53        | (v2_struct_0 @ sk_D)
% 0.20/0.53        | (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H)
% 0.20/0.53        | ~ (r1_tarski @ sk_F @ (u1_struct_0 @ sk_C_1))
% 0.20/0.53        | ~ (r2_hidden @ sk_H @ sk_F)
% 0.20/0.53        | ~ (v3_pre_topc @ sk_F @ sk_D)
% 0.20/0.53        | (v2_struct_0 @ sk_C_1)
% 0.20/0.53        | (v2_struct_0 @ sk_B))),
% 0.20/0.53      inference('sup-', [status(thm)], ['24', '90'])).
% 0.20/0.53  thf('92', plain, ((r1_tarski @ sk_F @ (u1_struct_0 @ sk_C_1))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('93', plain, ((r2_hidden @ sk_G @ sk_F)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('94', plain, (((sk_G) = (sk_H))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('95', plain, ((r2_hidden @ sk_H @ sk_F)),
% 0.20/0.53      inference('demod', [status(thm)], ['93', '94'])).
% 0.20/0.53  thf('96', plain,
% 0.20/0.53      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['22', '23'])).
% 0.20/0.53  thf('97', plain,
% 0.20/0.53      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('98', plain,
% 0.20/0.53      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf(t9_tsep_1, axiom,
% 0.20/0.53    (![A:$i]:
% 0.20/0.53     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.53       ( ![B:$i]:
% 0.20/0.53         ( ( m1_pre_topc @ B @ A ) =>
% 0.20/0.53           ( ![C:$i]:
% 0.20/0.53             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.53               ( ![D:$i]:
% 0.20/0.53                 ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.53                   ( ![E:$i]:
% 0.20/0.53                     ( ( m1_subset_1 @
% 0.20/0.53                         E @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.20/0.53                       ( ( ( v3_pre_topc @ C @ A ) & 
% 0.20/0.53                           ( r1_tarski @ C @ ( u1_struct_0 @ B ) ) & 
% 0.20/0.53                           ( r1_tarski @ D @ C ) & ( ( D ) = ( E ) ) ) =>
% 0.20/0.53                         ( ( v3_pre_topc @ E @ B ) <=> ( v3_pre_topc @ D @ A ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.53  thf('99', plain,
% 0.20/0.53      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 0.20/0.53         (~ (m1_pre_topc @ X32 @ X33)
% 0.20/0.53          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (u1_struct_0 @ X33)))
% 0.20/0.53          | ~ (v3_pre_topc @ X35 @ X33)
% 0.20/0.53          | ~ (r1_tarski @ X35 @ (u1_struct_0 @ X32))
% 0.20/0.53          | ~ (r1_tarski @ X34 @ X35)
% 0.20/0.53          | ((X34) != (X36))
% 0.20/0.53          | ~ (v3_pre_topc @ X34 @ X33)
% 0.20/0.53          | (v3_pre_topc @ X36 @ X32)
% 0.20/0.53          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (u1_struct_0 @ X32)))
% 0.20/0.53          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (u1_struct_0 @ X33)))
% 0.20/0.53          | ~ (l1_pre_topc @ X33)
% 0.20/0.53          | ~ (v2_pre_topc @ X33))),
% 0.20/0.53      inference('cnf', [status(esa)], [t9_tsep_1])).
% 0.20/0.53  thf('100', plain,
% 0.20/0.53      (![X32 : $i, X33 : $i, X35 : $i, X36 : $i]:
% 0.20/0.53         (~ (v2_pre_topc @ X33)
% 0.20/0.53          | ~ (l1_pre_topc @ X33)
% 0.20/0.53          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (u1_struct_0 @ X33)))
% 0.20/0.53          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (u1_struct_0 @ X32)))
% 0.20/0.53          | (v3_pre_topc @ X36 @ X32)
% 0.20/0.53          | ~ (v3_pre_topc @ X36 @ X33)
% 0.20/0.53          | ~ (r1_tarski @ X36 @ X35)
% 0.20/0.53          | ~ (r1_tarski @ X35 @ (u1_struct_0 @ X32))
% 0.20/0.53          | ~ (v3_pre_topc @ X35 @ X33)
% 0.20/0.53          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (u1_struct_0 @ X33)))
% 0.20/0.53          | ~ (m1_pre_topc @ X32 @ X33))),
% 0.20/0.53      inference('simplify', [status(thm)], ['99'])).
% 0.20/0.53  thf('101', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]:
% 0.20/0.53         (~ (m1_pre_topc @ X0 @ sk_B)
% 0.20/0.53          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.20/0.53          | ~ (v3_pre_topc @ sk_F @ sk_B)
% 0.20/0.53          | ~ (r1_tarski @ sk_F @ (u1_struct_0 @ X0))
% 0.20/0.53          | ~ (r1_tarski @ X1 @ sk_F)
% 0.20/0.53          | ~ (v3_pre_topc @ X1 @ sk_B)
% 0.20/0.53          | (v3_pre_topc @ X1 @ X0)
% 0.20/0.53          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.20/0.53          | ~ (l1_pre_topc @ sk_B)
% 0.20/0.53          | ~ (v2_pre_topc @ sk_B))),
% 0.20/0.53      inference('sup-', [status(thm)], ['98', '100'])).
% 0.20/0.53  thf('102', plain, ((v3_pre_topc @ sk_F @ sk_B)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('103', plain, ((l1_pre_topc @ sk_B)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('104', plain, ((v2_pre_topc @ sk_B)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('105', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]:
% 0.20/0.53         (~ (m1_pre_topc @ X0 @ sk_B)
% 0.20/0.53          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.20/0.53          | ~ (r1_tarski @ sk_F @ (u1_struct_0 @ X0))
% 0.20/0.53          | ~ (r1_tarski @ X1 @ sk_F)
% 0.20/0.53          | ~ (v3_pre_topc @ X1 @ sk_B)
% 0.20/0.53          | (v3_pre_topc @ X1 @ X0)
% 0.20/0.53          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.20/0.53      inference('demod', [status(thm)], ['101', '102', '103', '104'])).
% 0.20/0.53  thf('106', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         (~ (m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.20/0.53          | (v3_pre_topc @ sk_F @ X0)
% 0.20/0.53          | ~ (v3_pre_topc @ sk_F @ sk_B)
% 0.20/0.53          | ~ (r1_tarski @ sk_F @ sk_F)
% 0.20/0.53          | ~ (r1_tarski @ sk_F @ (u1_struct_0 @ X0))
% 0.20/0.53          | ~ (m1_pre_topc @ X0 @ sk_B))),
% 0.20/0.53      inference('sup-', [status(thm)], ['97', '105'])).
% 0.20/0.53  thf('107', plain, ((v3_pre_topc @ sk_F @ sk_B)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf(d10_xboole_0, axiom,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.20/0.53  thf('108', plain,
% 0.20/0.53      (![X4 : $i, X5 : $i]: ((r1_tarski @ X4 @ X5) | ((X4) != (X5)))),
% 0.20/0.53      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.20/0.53  thf('109', plain, (![X5 : $i]: (r1_tarski @ X5 @ X5)),
% 0.20/0.53      inference('simplify', [status(thm)], ['108'])).
% 0.20/0.53  thf('110', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         (~ (m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.20/0.53          | (v3_pre_topc @ sk_F @ X0)
% 0.20/0.53          | ~ (r1_tarski @ sk_F @ (u1_struct_0 @ X0))
% 0.20/0.53          | ~ (m1_pre_topc @ X0 @ sk_B))),
% 0.20/0.53      inference('demod', [status(thm)], ['106', '107', '109'])).
% 0.20/0.53  thf('111', plain,
% 0.20/0.53      ((~ (m1_pre_topc @ sk_D @ sk_B)
% 0.20/0.53        | ~ (r1_tarski @ sk_F @ (u1_struct_0 @ sk_D))
% 0.20/0.53        | (v3_pre_topc @ sk_F @ sk_D))),
% 0.20/0.53      inference('sup-', [status(thm)], ['96', '110'])).
% 0.20/0.53  thf('112', plain, ((m1_pre_topc @ sk_D @ sk_B)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('113', plain, ((r1_tarski @ sk_F @ (u1_struct_0 @ sk_D))),
% 0.20/0.53      inference('simplify', [status(thm)], ['21'])).
% 0.20/0.53  thf('114', plain, ((v3_pre_topc @ sk_F @ sk_D)),
% 0.20/0.53      inference('demod', [status(thm)], ['111', '112', '113'])).
% 0.20/0.53  thf('115', plain,
% 0.20/0.53      (((v2_struct_0 @ sk_A)
% 0.20/0.53        | (v2_struct_0 @ sk_D)
% 0.20/0.53        | (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H)
% 0.20/0.53        | (v2_struct_0 @ sk_C_1)
% 0.20/0.53        | (v2_struct_0 @ sk_B))),
% 0.20/0.53      inference('demod', [status(thm)], ['91', '92', '95', '114'])).
% 0.20/0.53  thf('116', plain,
% 0.20/0.53      ((~ (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G))
% 0.20/0.53         <= (~ ((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G)))),
% 0.20/0.53      inference('split', [status(esa)], ['77'])).
% 0.20/0.53  thf('117', plain, (((sk_G) = (sk_H))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('118', plain,
% 0.20/0.53      ((~ (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H))
% 0.20/0.53         <= (~ ((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G)))),
% 0.20/0.53      inference('demod', [status(thm)], ['116', '117'])).
% 0.20/0.53  thf('119', plain,
% 0.20/0.53      (((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G))
% 0.20/0.53         <= (((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G)))),
% 0.20/0.53      inference('split', [status(esa)], ['25'])).
% 0.20/0.53  thf('120', plain, (((sk_G) = (sk_H))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('121', plain,
% 0.20/0.53      (((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H))
% 0.20/0.53         <= (((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G)))),
% 0.20/0.53      inference('demod', [status(thm)], ['119', '120'])).
% 0.20/0.53  thf('122', plain,
% 0.20/0.53      ((~ (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H))
% 0.20/0.53         <= (~ ((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H)))),
% 0.20/0.53      inference('split', [status(esa)], ['49'])).
% 0.20/0.53  thf('123', plain,
% 0.20/0.53      (~ ((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G)) | 
% 0.20/0.53       ((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H))),
% 0.20/0.53      inference('sup-', [status(thm)], ['121', '122'])).
% 0.20/0.53  thf('124', plain, (~ ((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G))),
% 0.20/0.53      inference('sat_resolution*', [status(thm)], ['50', '87', '123'])).
% 0.20/0.53  thf('125', plain, (~ (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H)),
% 0.20/0.53      inference('simpl_trail', [status(thm)], ['118', '124'])).
% 0.20/0.53  thf('126', plain,
% 0.20/0.53      (((v2_struct_0 @ sk_B)
% 0.20/0.53        | (v2_struct_0 @ sk_C_1)
% 0.20/0.53        | (v2_struct_0 @ sk_D)
% 0.20/0.53        | (v2_struct_0 @ sk_A))),
% 0.20/0.53      inference('sup-', [status(thm)], ['115', '125'])).
% 0.20/0.53  thf('127', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('128', plain,
% 0.20/0.53      (((v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_C_1) | (v2_struct_0 @ sk_B))),
% 0.20/0.53      inference('sup-', [status(thm)], ['126', '127'])).
% 0.20/0.53  thf('129', plain, (~ (v2_struct_0 @ sk_D)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('130', plain, (((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_C_1))),
% 0.20/0.53      inference('clc', [status(thm)], ['128', '129'])).
% 0.20/0.53  thf('131', plain, (~ (v2_struct_0 @ sk_B)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('132', plain, ((v2_struct_0 @ sk_C_1)),
% 0.20/0.53      inference('clc', [status(thm)], ['130', '131'])).
% 0.20/0.53  thf('133', plain, ($false), inference('demod', [status(thm)], ['0', '132'])).
% 0.20/0.53  
% 0.20/0.53  % SZS output end Refutation
% 0.20/0.53  
% 0.20/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
