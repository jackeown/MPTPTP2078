%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.QlSo28f1OG

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:10:01 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  177 ( 806 expanded)
%              Number of leaves         :   37 ( 249 expanded)
%              Depth                    :   32
%              Number of atoms          : 2296 (35729 expanded)
%              Number of equality atoms :   57 ( 473 expanded)
%              Maximal formula depth    :   25 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_F_type,type,(
    sk_F: $i > $i > $i > $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k3_tmap_1_type,type,(
    k3_tmap_1: $i > $i > $i > $i > $i > $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k3_funct_2_type,type,(
    k3_funct_2: $i > $i > $i > $i > $i )).

thf(k2_partfun1_type,type,(
    k2_partfun1: $i > $i > $i > $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(r2_funct_2_type,type,(
    r2_funct_2: $i > $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_F_1_type,type,(
    sk_F_1: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(t73_tmap_1,conjecture,(
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
                            ( ( ( v1_funct_1 @ F )
                              & ( v1_funct_2 @ F @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) )
                              & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) )
                           => ( ! [G: $i] :
                                  ( ( m1_subset_1 @ G @ ( u1_struct_0 @ D ) )
                                 => ( ( r2_hidden @ G @ ( u1_struct_0 @ C ) )
                                   => ( ( k3_funct_2 @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) @ E @ G )
                                      = ( k1_funct_1 @ F @ G ) ) ) )
                             => ( r2_funct_2 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ F ) ) ) ) ) ) ) ) ) )).

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
                              ( ( ( v1_funct_1 @ F )
                                & ( v1_funct_2 @ F @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) )
                                & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) )
                             => ( ! [G: $i] :
                                    ( ( m1_subset_1 @ G @ ( u1_struct_0 @ D ) )
                                   => ( ( r2_hidden @ G @ ( u1_struct_0 @ C ) )
                                     => ( ( k3_funct_2 @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) @ E @ G )
                                        = ( k1_funct_1 @ F @ G ) ) ) )
                               => ( r2_funct_2 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ F ) ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t73_tmap_1])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_subset_1 @ sk_F_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t173_funct_2,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ~ ( v1_xboole_0 @ B )
         => ! [C: $i] :
              ( ( ( v1_funct_1 @ C )
                & ( v1_funct_2 @ C @ A @ B )
                & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
             => ! [D: $i] :
                  ( ( ~ ( v1_xboole_0 @ D )
                    & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) )
                 => ! [E: $i] :
                      ( ( ( v1_funct_1 @ E )
                        & ( v1_funct_2 @ E @ D @ B )
                        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ D @ B ) ) ) )
                     => ( ! [F: $i] :
                            ( ( m1_subset_1 @ F @ A )
                           => ( ( r2_hidden @ F @ D )
                             => ( ( k3_funct_2 @ A @ B @ C @ F )
                                = ( k1_funct_1 @ E @ F ) ) ) )
                       => ( ( k2_partfun1 @ A @ B @ C @ D )
                          = E ) ) ) ) ) ) ) )).

thf('3',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ( v1_xboole_0 @ X7 )
      | ( v1_xboole_0 @ X8 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) )
      | ( m1_subset_1 @ ( sk_F @ X10 @ X8 @ X11 @ X7 @ X9 ) @ X9 )
      | ( ( k2_partfun1 @ X9 @ X7 @ X11 @ X8 )
        = X10 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X7 ) ) )
      | ~ ( v1_funct_2 @ X10 @ X8 @ X7 )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X7 ) ) )
      | ~ ( v1_funct_2 @ X11 @ X9 @ X7 )
      | ~ ( v1_funct_1 @ X11 )
      | ( v1_xboole_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t173_funct_2])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ X0 @ ( u1_struct_0 @ sk_B ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_1 @ sk_F_1 )
      | ~ ( v1_funct_2 @ sk_F_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
      | ( ( k2_partfun1 @ X0 @ ( u1_struct_0 @ sk_B ) @ X1 @ ( u1_struct_0 @ sk_C ) )
        = sk_F_1 )
      | ( m1_subset_1 @ ( sk_F @ sk_F_1 @ ( u1_struct_0 @ sk_C ) @ X1 @ ( u1_struct_0 @ sk_B ) @ X0 ) @ X0 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ X0 ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    v1_funct_1 @ sk_F_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    v1_funct_2 @ sk_F_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ X0 @ ( u1_struct_0 @ sk_B ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ ( u1_struct_0 @ sk_B ) ) ) )
      | ( ( k2_partfun1 @ X0 @ ( u1_struct_0 @ sk_B ) @ X1 @ ( u1_struct_0 @ sk_C ) )
        = sk_F_1 )
      | ( m1_subset_1 @ ( sk_F @ sk_F_1 @ ( u1_struct_0 @ sk_C ) @ X1 @ ( u1_struct_0 @ sk_B ) @ X0 ) @ X0 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ X0 ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['4','5','6'])).

thf('8',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) )
    | ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) )
    | ( m1_subset_1 @ ( sk_F @ sk_F_1 @ ( u1_struct_0 @ sk_C ) @ sk_E @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D ) ) @ ( u1_struct_0 @ sk_D ) )
    | ( ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ sk_C ) )
      = sk_F_1 )
    | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ sk_E )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['1','7'])).

thf('9',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
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

thf('11',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( m1_pre_topc @ X24 @ X25 )
      | ~ ( m1_pre_topc @ X24 @ X26 )
      | ( r1_tarski @ ( u1_struct_0 @ X24 ) @ ( u1_struct_0 @ X26 ) )
      | ~ ( m1_pre_topc @ X26 @ X25 )
      | ~ ( l1_pre_topc @ X25 )
      | ~ ( v2_pre_topc @ X25 ) ) ),
    inference(cnf,[status(esa)],[t4_tsep_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( r1_tarski @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( r1_tarski @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ sk_C @ X0 ) ) ),
    inference(demod,[status(thm)],['12','13','14'])).

thf('16',plain,
    ( ~ ( m1_pre_topc @ sk_C @ sk_D )
    | ( r1_tarski @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['9','15'])).

thf('17',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['16','17'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('19',plain,(
    ! [X0: $i,X2: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X2 ) )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('20',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) )
    | ( m1_subset_1 @ ( sk_F @ sk_F_1 @ ( u1_struct_0 @ sk_C ) @ sk_E @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D ) ) @ ( u1_struct_0 @ sk_D ) )
    | ( ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ sk_C ) )
      = sk_F_1 )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['8','20','21','22'])).

thf('24',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( m1_pre_topc @ A @ A ) ) )).

thf('25',plain,(
    ! [X23: $i] :
      ( ( m1_pre_topc @ X23 @ X23 )
      | ~ ( l1_pre_topc @ X23 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('26',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
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

thf('27',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ( v2_struct_0 @ X18 )
      | ~ ( v2_pre_topc @ X18 )
      | ~ ( l1_pre_topc @ X18 )
      | ~ ( m1_pre_topc @ X19 @ X20 )
      | ~ ( m1_pre_topc @ X19 @ X21 )
      | ( ( k3_tmap_1 @ X20 @ X18 @ X21 @ X19 @ X22 )
        = ( k2_partfun1 @ ( u1_struct_0 @ X21 ) @ ( u1_struct_0 @ X18 ) @ X22 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X21 ) @ ( u1_struct_0 @ X18 ) ) ) )
      | ~ ( v1_funct_2 @ X22 @ ( u1_struct_0 @ X21 ) @ ( u1_struct_0 @ X18 ) )
      | ~ ( v1_funct_1 @ X22 )
      | ~ ( m1_pre_topc @ X21 @ X20 )
      | ~ ( l1_pre_topc @ X20 )
      | ~ ( v2_pre_topc @ X20 )
      | ( v2_struct_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[d5_tmap_1])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      | ( ( k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( m1_pre_topc @ X1 @ sk_D )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ( ( k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( m1_pre_topc @ X1 @ sk_D )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['28','29','30','31','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_D )
      | ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ X0 @ sk_E )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ sk_D )
      | ~ ( v2_pre_topc @ sk_D )
      | ( v2_struct_0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['25','33'])).

thf('35',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('36',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( m1_pre_topc @ X15 @ X16 )
      | ( l1_pre_topc @ X15 )
      | ~ ( l1_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('37',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_D ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['37','38'])).

thf('41',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( v2_pre_topc @ B ) ) ) )).

thf('42',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( m1_pre_topc @ X12 @ X13 )
      | ( v2_pre_topc @ X12 )
      | ~ ( l1_pre_topc @ X13 )
      | ~ ( v2_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[cc1_pre_topc])).

thf('43',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_pre_topc @ sk_D ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    v2_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['43','44','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ X0 @ sk_E )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ X0 ) ) )
      | ( v2_struct_0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['34','39','40','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_D )
      | ( ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ X0 @ sk_E )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ sk_C ) ) )
    | ( v2_struct_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['24','48'])).

thf('50',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference(clc,[status(thm)],['49','50'])).

thf('52',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,
    ( ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E )
    = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ sk_C ) ) ),
    inference(clc,[status(thm)],['51','52'])).

thf('54',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) )
    | ( m1_subset_1 @ ( sk_F @ sk_F_1 @ ( u1_struct_0 @ sk_C ) @ sk_E @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D ) ) @ ( u1_struct_0 @ sk_D ) )
    | ( ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E )
      = sk_F_1 )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['23','53'])).

thf('55',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ( ( k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( m1_pre_topc @ X1 @ sk_D )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['28','29','30','31','32'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ X0 @ sk_E )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ X0 @ sk_E )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ X0 ) ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['58','59','60'])).

thf('62',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ sk_C ) ) )
    | ~ ( m1_pre_topc @ sk_C @ sk_D )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['55','61'])).

thf('63',plain,
    ( ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E )
    = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ sk_C ) ) ),
    inference(clc,[status(thm)],['51','52'])).

thf('64',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E )
      = ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['62','63','64'])).

thf('66',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E )
      = ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E ) ) ),
    inference(clc,[status(thm)],['65','66'])).

thf('68',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,
    ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E )
    = ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E ) ),
    inference(clc,[status(thm)],['67','68'])).

thf('70',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) )
    | ( m1_subset_1 @ ( sk_F @ sk_F_1 @ ( u1_struct_0 @ sk_C ) @ sk_E @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D ) ) @ ( u1_struct_0 @ sk_D ) )
    | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E )
      = sk_F_1 )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['54','69'])).

thf('71',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    m1_subset_1 @ sk_F_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ( v1_xboole_0 @ X7 )
      | ( v1_xboole_0 @ X8 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) )
      | ( r2_hidden @ ( sk_F @ X10 @ X8 @ X11 @ X7 @ X9 ) @ X8 )
      | ( ( k2_partfun1 @ X9 @ X7 @ X11 @ X8 )
        = X10 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X7 ) ) )
      | ~ ( v1_funct_2 @ X10 @ X8 @ X7 )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X7 ) ) )
      | ~ ( v1_funct_2 @ X11 @ X9 @ X7 )
      | ~ ( v1_funct_1 @ X11 )
      | ( v1_xboole_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t173_funct_2])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ X0 @ ( u1_struct_0 @ sk_B ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_1 @ sk_F_1 )
      | ~ ( v1_funct_2 @ sk_F_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
      | ( ( k2_partfun1 @ X0 @ ( u1_struct_0 @ sk_B ) @ X1 @ ( u1_struct_0 @ sk_C ) )
        = sk_F_1 )
      | ( r2_hidden @ ( sk_F @ sk_F_1 @ ( u1_struct_0 @ sk_C ) @ X1 @ ( u1_struct_0 @ sk_B ) @ X0 ) @ ( u1_struct_0 @ sk_C ) )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ X0 ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    v1_funct_1 @ sk_F_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    v1_funct_2 @ sk_F_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ X0 @ ( u1_struct_0 @ sk_B ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ ( u1_struct_0 @ sk_B ) ) ) )
      | ( ( k2_partfun1 @ X0 @ ( u1_struct_0 @ sk_B ) @ X1 @ ( u1_struct_0 @ sk_C ) )
        = sk_F_1 )
      | ( r2_hidden @ ( sk_F @ sk_F_1 @ ( u1_struct_0 @ sk_C ) @ X1 @ ( u1_struct_0 @ sk_B ) @ X0 ) @ ( u1_struct_0 @ sk_C ) )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ X0 ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['74','75','76'])).

thf('78',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) )
    | ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) )
    | ( r2_hidden @ ( sk_F @ sk_F_1 @ ( u1_struct_0 @ sk_C ) @ sk_E @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D ) ) @ ( u1_struct_0 @ sk_C ) )
    | ( ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ sk_C ) )
      = sk_F_1 )
    | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ sk_E )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['71','77'])).

thf('79',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('80',plain,
    ( ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E )
    = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ sk_C ) ) ),
    inference(clc,[status(thm)],['51','52'])).

thf('81',plain,
    ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E )
    = ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E ) ),
    inference(clc,[status(thm)],['67','68'])).

thf('82',plain,
    ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E )
    = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['80','81'])).

thf('83',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) )
    | ( r2_hidden @ ( sk_F @ sk_F_1 @ ( u1_struct_0 @ sk_C ) @ sk_E @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D ) ) @ ( u1_struct_0 @ sk_C ) )
    | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E )
      = sk_F_1 )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['78','79','82','83','84'])).

thf('86',plain,(
    ! [X27: $i] :
      ( ~ ( r2_hidden @ X27 @ ( u1_struct_0 @ sk_C ) )
      | ( ( k3_funct_2 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ X27 )
        = ( k1_funct_1 @ sk_F_1 @ X27 ) )
      | ~ ( m1_subset_1 @ X27 @ ( u1_struct_0 @ sk_D ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_D ) )
    | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E )
      = sk_F_1 )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ~ ( m1_subset_1 @ ( sk_F @ sk_F_1 @ ( u1_struct_0 @ sk_C ) @ sk_E @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D ) ) @ ( u1_struct_0 @ sk_D ) )
    | ( ( k3_funct_2 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( sk_F @ sk_F_1 @ ( u1_struct_0 @ sk_C ) @ sk_E @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D ) ) )
      = ( k1_funct_1 @ sk_F_1 @ ( sk_F @ sk_F_1 @ ( u1_struct_0 @ sk_C ) @ sk_E @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D ) ) ) ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_D ) )
    | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E )
      = sk_F_1 )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( ( k3_funct_2 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( sk_F @ sk_F_1 @ ( u1_struct_0 @ sk_C ) @ sk_E @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D ) ) )
      = ( k1_funct_1 @ sk_F_1 @ ( sk_F @ sk_F_1 @ ( u1_struct_0 @ sk_C ) @ sk_E @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D ) ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) )
    | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E )
      = sk_F_1 )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['70','87'])).

thf('89',plain,
    ( ( ( k3_funct_2 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( sk_F @ sk_F_1 @ ( u1_struct_0 @ sk_C ) @ sk_E @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D ) ) )
      = ( k1_funct_1 @ sk_F_1 @ ( sk_F @ sk_F_1 @ ( u1_struct_0 @ sk_C ) @ sk_E @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D ) ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) )
    | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E )
      = sk_F_1 )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_D ) ) ),
    inference(simplify,[status(thm)],['88'])).

thf('90',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ( v1_xboole_0 @ X7 )
      | ( v1_xboole_0 @ X8 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) )
      | ( ( k3_funct_2 @ X9 @ X7 @ X11 @ ( sk_F @ X10 @ X8 @ X11 @ X7 @ X9 ) )
       != ( k1_funct_1 @ X10 @ ( sk_F @ X10 @ X8 @ X11 @ X7 @ X9 ) ) )
      | ( ( k2_partfun1 @ X9 @ X7 @ X11 @ X8 )
        = X10 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X7 ) ) )
      | ~ ( v1_funct_2 @ X10 @ X8 @ X7 )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X7 ) ) )
      | ~ ( v1_funct_2 @ X11 @ X9 @ X7 )
      | ~ ( v1_funct_1 @ X11 )
      | ( v1_xboole_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t173_funct_2])).

thf('91',plain,
    ( ( ( k1_funct_1 @ sk_F_1 @ ( sk_F @ sk_F_1 @ ( u1_struct_0 @ sk_C ) @ sk_E @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D ) ) )
     != ( k1_funct_1 @ sk_F_1 @ ( sk_F @ sk_F_1 @ ( u1_struct_0 @ sk_C ) @ sk_E @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D ) ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_D ) )
    | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E )
      = sk_F_1 )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_D ) )
    | ~ ( v1_funct_1 @ sk_E )
    | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( v1_funct_1 @ sk_F_1 )
    | ~ ( v1_funct_2 @ sk_F_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( m1_subset_1 @ sk_F_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ( ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ sk_C ) )
      = sk_F_1 )
    | ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    v1_funct_1 @ sk_F_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    v1_funct_2 @ sk_F_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    m1_subset_1 @ sk_F_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,
    ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E )
    = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['80','81'])).

thf('99',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('100',plain,
    ( ( ( k1_funct_1 @ sk_F_1 @ ( sk_F @ sk_F_1 @ ( u1_struct_0 @ sk_C ) @ sk_E @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D ) ) )
     != ( k1_funct_1 @ sk_F_1 @ ( sk_F @ sk_F_1 @ ( u1_struct_0 @ sk_C ) @ sk_E @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D ) ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_D ) )
    | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E )
      = sk_F_1 )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_D ) )
    | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E )
      = sk_F_1 )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['91','92','93','94','95','96','97','98','99'])).

thf('101',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) )
    | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E )
      = sk_F_1 )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_D ) ) ),
    inference(simplify,[status(thm)],['100'])).

thf('102',plain,(
    ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_F_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,
    ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_F_1 @ sk_F_1 )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_D ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,(
    m1_subset_1 @ sk_F_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_r2_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_funct_2 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('105',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X4 @ X5 ) ) )
      | ~ ( v1_funct_2 @ X3 @ X4 @ X5 )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_funct_2 @ X6 @ X4 @ X5 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X4 @ X5 ) ) )
      | ( r2_funct_2 @ X4 @ X5 @ X3 @ X6 )
      | ( X3 != X6 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_funct_2])).

thf('106',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( r2_funct_2 @ X4 @ X5 @ X6 @ X6 )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_funct_2 @ X6 @ X4 @ X5 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X4 @ X5 ) ) ) ) ),
    inference(simplify,[status(thm)],['105'])).

thf('107',plain,
    ( ~ ( v1_funct_2 @ sk_F_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ sk_F_1 )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_F_1 @ sk_F_1 ) ),
    inference('sup-',[status(thm)],['104','106'])).

thf('108',plain,(
    v1_funct_2 @ sk_F_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,(
    v1_funct_1 @ sk_F_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,(
    r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_F_1 @ sk_F_1 ),
    inference(demod,[status(thm)],['107','108','109'])).

thf('111',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_D ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['103','110'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('112',plain,(
    ! [X17: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X17 ) )
      | ~ ( l1_struct_0 @ X17 )
      | ( v2_struct_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('113',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_D ) )
    | ( v2_struct_0 @ sk_B )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['111','112'])).

thf('114',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('115',plain,(
    ! [X14: $i] :
      ( ( l1_struct_0 @ X14 )
      | ~ ( l1_pre_topc @ X14 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('116',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['114','115'])).

thf('117',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_D ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['113','116'])).

thf('118',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_D ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) ) ),
    inference(clc,[status(thm)],['117','118'])).

thf('120',plain,(
    ! [X17: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X17 ) )
      | ~ ( l1_struct_0 @ X17 )
      | ( v2_struct_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('121',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) )
    | ( v2_struct_0 @ sk_D )
    | ~ ( l1_struct_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['119','120'])).

thf('122',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['37','38'])).

thf('123',plain,(
    ! [X14: $i] :
      ( ( l1_struct_0 @ X14 )
      | ~ ( l1_pre_topc @ X14 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('124',plain,(
    l1_struct_0 @ sk_D ),
    inference('sup-',[status(thm)],['122','123'])).

thf('125',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) )
    | ( v2_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['121','124'])).

thf('126',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_C ) ),
    inference(clc,[status(thm)],['125','126'])).

thf('128',plain,(
    ! [X17: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X17 ) )
      | ~ ( l1_struct_0 @ X17 )
      | ( v2_struct_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('129',plain,
    ( ( v2_struct_0 @ sk_C )
    | ~ ( l1_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['127','128'])).

thf('130',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('131',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( m1_pre_topc @ X15 @ X16 )
      | ( l1_pre_topc @ X15 )
      | ~ ( l1_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('132',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_C ) ),
    inference('sup-',[status(thm)],['130','131'])).

thf('133',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('134',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['132','133'])).

thf('135',plain,(
    ! [X14: $i] :
      ( ( l1_struct_0 @ X14 )
      | ~ ( l1_pre_topc @ X14 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('136',plain,(
    l1_struct_0 @ sk_C ),
    inference('sup-',[status(thm)],['134','135'])).

thf('137',plain,(
    v2_struct_0 @ sk_C ),
    inference(demod,[status(thm)],['129','136'])).

thf('138',plain,(
    $false ),
    inference(demod,[status(thm)],['0','137'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.QlSo28f1OG
% 0.13/0.35  % Computer   : n008.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 19:43:45 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.53  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.53  % Solved by: fo/fo7.sh
% 0.20/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.53  % done 141 iterations in 0.066s
% 0.20/0.53  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.53  % SZS output start Refutation
% 0.20/0.53  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.20/0.53  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.53  thf(sk_F_type, type, sk_F: $i > $i > $i > $i > $i > $i).
% 0.20/0.53  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.20/0.53  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.53  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.53  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.53  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.20/0.53  thf(sk_D_type, type, sk_D: $i).
% 0.20/0.53  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.53  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.20/0.53  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.20/0.53  thf(k3_tmap_1_type, type, k3_tmap_1: $i > $i > $i > $i > $i > $i).
% 0.20/0.53  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.20/0.53  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.53  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.20/0.53  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.53  thf(k3_funct_2_type, type, k3_funct_2: $i > $i > $i > $i > $i).
% 0.20/0.53  thf(k2_partfun1_type, type, k2_partfun1: $i > $i > $i > $i > $i).
% 0.20/0.53  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.20/0.53  thf(r2_funct_2_type, type, r2_funct_2: $i > $i > $i > $i > $o).
% 0.20/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.53  thf(sk_F_1_type, type, sk_F_1: $i).
% 0.20/0.53  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.53  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.53  thf(sk_E_type, type, sk_E: $i).
% 0.20/0.53  thf(t73_tmap_1, conjecture,
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
% 0.20/0.53                           E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 0.20/0.53                         ( m1_subset_1 @
% 0.20/0.53                           E @ 
% 0.20/0.53                           ( k1_zfmisc_1 @
% 0.20/0.53                             ( k2_zfmisc_1 @
% 0.20/0.53                               ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.20/0.53                       ( ( m1_pre_topc @ C @ D ) =>
% 0.20/0.53                         ( ![F:$i]:
% 0.20/0.53                           ( ( ( v1_funct_1 @ F ) & 
% 0.20/0.53                               ( v1_funct_2 @
% 0.20/0.53                                 F @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 0.20/0.53                               ( m1_subset_1 @
% 0.20/0.53                                 F @ 
% 0.20/0.53                                 ( k1_zfmisc_1 @
% 0.20/0.53                                   ( k2_zfmisc_1 @
% 0.20/0.53                                     ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.20/0.53                             ( ( ![G:$i]:
% 0.20/0.53                                 ( ( m1_subset_1 @ G @ ( u1_struct_0 @ D ) ) =>
% 0.20/0.53                                   ( ( r2_hidden @ G @ ( u1_struct_0 @ C ) ) =>
% 0.20/0.53                                     ( ( k3_funct_2 @
% 0.20/0.53                                         ( u1_struct_0 @ D ) @ 
% 0.20/0.53                                         ( u1_struct_0 @ B ) @ E @ G ) =
% 0.20/0.53                                       ( k1_funct_1 @ F @ G ) ) ) ) ) =>
% 0.20/0.53                               ( r2_funct_2 @
% 0.20/0.53                                 ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ 
% 0.20/0.53                                 ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ F ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.53    (~( ![A:$i]:
% 0.20/0.53        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.20/0.53            ( l1_pre_topc @ A ) ) =>
% 0.20/0.53          ( ![B:$i]:
% 0.20/0.53            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.20/0.53                ( l1_pre_topc @ B ) ) =>
% 0.20/0.53              ( ![C:$i]:
% 0.20/0.53                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.20/0.53                  ( ![D:$i]:
% 0.20/0.53                    ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.20/0.53                      ( ![E:$i]:
% 0.20/0.53                        ( ( ( v1_funct_1 @ E ) & 
% 0.20/0.53                            ( v1_funct_2 @
% 0.20/0.53                              E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 0.20/0.53                            ( m1_subset_1 @
% 0.20/0.53                              E @ 
% 0.20/0.53                              ( k1_zfmisc_1 @
% 0.20/0.53                                ( k2_zfmisc_1 @
% 0.20/0.53                                  ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.20/0.53                          ( ( m1_pre_topc @ C @ D ) =>
% 0.20/0.53                            ( ![F:$i]:
% 0.20/0.53                              ( ( ( v1_funct_1 @ F ) & 
% 0.20/0.53                                  ( v1_funct_2 @
% 0.20/0.53                                    F @ ( u1_struct_0 @ C ) @ 
% 0.20/0.53                                    ( u1_struct_0 @ B ) ) & 
% 0.20/0.53                                  ( m1_subset_1 @
% 0.20/0.53                                    F @ 
% 0.20/0.53                                    ( k1_zfmisc_1 @
% 0.20/0.53                                      ( k2_zfmisc_1 @
% 0.20/0.53                                        ( u1_struct_0 @ C ) @ 
% 0.20/0.53                                        ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.20/0.53                                ( ( ![G:$i]:
% 0.20/0.53                                    ( ( m1_subset_1 @ G @ ( u1_struct_0 @ D ) ) =>
% 0.20/0.53                                      ( ( r2_hidden @ G @ ( u1_struct_0 @ C ) ) =>
% 0.20/0.53                                        ( ( k3_funct_2 @
% 0.20/0.53                                            ( u1_struct_0 @ D ) @ 
% 0.20/0.53                                            ( u1_struct_0 @ B ) @ E @ G ) =
% 0.20/0.53                                          ( k1_funct_1 @ F @ G ) ) ) ) ) =>
% 0.20/0.53                                  ( r2_funct_2 @
% 0.20/0.53                                    ( u1_struct_0 @ C ) @ 
% 0.20/0.53                                    ( u1_struct_0 @ B ) @ 
% 0.20/0.53                                    ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ F ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.20/0.53    inference('cnf.neg', [status(esa)], [t73_tmap_1])).
% 0.20/0.53  thf('0', plain, (~ (v2_struct_0 @ sk_C)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('1', plain,
% 0.20/0.53      ((m1_subset_1 @ sk_E @ 
% 0.20/0.53        (k1_zfmisc_1 @ 
% 0.20/0.53         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('2', plain,
% 0.20/0.53      ((m1_subset_1 @ sk_F_1 @ 
% 0.20/0.53        (k1_zfmisc_1 @ 
% 0.20/0.53         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf(t173_funct_2, axiom,
% 0.20/0.53    (![A:$i]:
% 0.20/0.53     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.20/0.53       ( ![B:$i]:
% 0.20/0.53         ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.20/0.53           ( ![C:$i]:
% 0.20/0.53             ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.20/0.53                 ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.20/0.53               ( ![D:$i]:
% 0.20/0.53                 ( ( ( ~( v1_xboole_0 @ D ) ) & 
% 0.20/0.53                     ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.20/0.53                   ( ![E:$i]:
% 0.20/0.53                     ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ D @ B ) & 
% 0.20/0.53                         ( m1_subset_1 @
% 0.20/0.53                           E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ D @ B ) ) ) ) =>
% 0.20/0.53                       ( ( ![F:$i]:
% 0.20/0.53                           ( ( m1_subset_1 @ F @ A ) =>
% 0.20/0.53                             ( ( r2_hidden @ F @ D ) =>
% 0.20/0.53                               ( ( k3_funct_2 @ A @ B @ C @ F ) =
% 0.20/0.53                                 ( k1_funct_1 @ E @ F ) ) ) ) ) =>
% 0.20/0.53                         ( ( k2_partfun1 @ A @ B @ C @ D ) = ( E ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.53  thf('3', plain,
% 0.20/0.53      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.20/0.53         ((v1_xboole_0 @ X7)
% 0.20/0.53          | (v1_xboole_0 @ X8)
% 0.20/0.53          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9))
% 0.20/0.53          | (m1_subset_1 @ (sk_F @ X10 @ X8 @ X11 @ X7 @ X9) @ X9)
% 0.20/0.53          | ((k2_partfun1 @ X9 @ X7 @ X11 @ X8) = (X10))
% 0.20/0.53          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X7)))
% 0.20/0.53          | ~ (v1_funct_2 @ X10 @ X8 @ X7)
% 0.20/0.53          | ~ (v1_funct_1 @ X10)
% 0.20/0.53          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X7)))
% 0.20/0.53          | ~ (v1_funct_2 @ X11 @ X9 @ X7)
% 0.20/0.53          | ~ (v1_funct_1 @ X11)
% 0.20/0.53          | (v1_xboole_0 @ X9))),
% 0.20/0.53      inference('cnf', [status(esa)], [t173_funct_2])).
% 0.20/0.53  thf('4', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]:
% 0.20/0.53         ((v1_xboole_0 @ X0)
% 0.20/0.53          | ~ (v1_funct_1 @ X1)
% 0.20/0.53          | ~ (v1_funct_2 @ X1 @ X0 @ (u1_struct_0 @ sk_B))
% 0.20/0.53          | ~ (m1_subset_1 @ X1 @ 
% 0.20/0.53               (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ (u1_struct_0 @ sk_B))))
% 0.20/0.53          | ~ (v1_funct_1 @ sk_F_1)
% 0.20/0.53          | ~ (v1_funct_2 @ sk_F_1 @ (u1_struct_0 @ sk_C) @ 
% 0.20/0.53               (u1_struct_0 @ sk_B))
% 0.20/0.53          | ((k2_partfun1 @ X0 @ (u1_struct_0 @ sk_B) @ X1 @ 
% 0.20/0.53              (u1_struct_0 @ sk_C)) = (sk_F_1))
% 0.20/0.53          | (m1_subset_1 @ 
% 0.20/0.53             (sk_F @ sk_F_1 @ (u1_struct_0 @ sk_C) @ X1 @ 
% 0.20/0.53              (u1_struct_0 @ sk_B) @ X0) @ 
% 0.20/0.53             X0)
% 0.20/0.53          | ~ (m1_subset_1 @ (u1_struct_0 @ sk_C) @ (k1_zfmisc_1 @ X0))
% 0.20/0.53          | (v1_xboole_0 @ (u1_struct_0 @ sk_C))
% 0.20/0.53          | (v1_xboole_0 @ (u1_struct_0 @ sk_B)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['2', '3'])).
% 0.20/0.53  thf('5', plain, ((v1_funct_1 @ sk_F_1)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('6', plain,
% 0.20/0.53      ((v1_funct_2 @ sk_F_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('7', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]:
% 0.20/0.53         ((v1_xboole_0 @ X0)
% 0.20/0.53          | ~ (v1_funct_1 @ X1)
% 0.20/0.53          | ~ (v1_funct_2 @ X1 @ X0 @ (u1_struct_0 @ sk_B))
% 0.20/0.53          | ~ (m1_subset_1 @ X1 @ 
% 0.20/0.53               (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ (u1_struct_0 @ sk_B))))
% 0.20/0.53          | ((k2_partfun1 @ X0 @ (u1_struct_0 @ sk_B) @ X1 @ 
% 0.20/0.53              (u1_struct_0 @ sk_C)) = (sk_F_1))
% 0.20/0.53          | (m1_subset_1 @ 
% 0.20/0.53             (sk_F @ sk_F_1 @ (u1_struct_0 @ sk_C) @ X1 @ 
% 0.20/0.53              (u1_struct_0 @ sk_B) @ X0) @ 
% 0.20/0.53             X0)
% 0.20/0.53          | ~ (m1_subset_1 @ (u1_struct_0 @ sk_C) @ (k1_zfmisc_1 @ X0))
% 0.20/0.53          | (v1_xboole_0 @ (u1_struct_0 @ sk_C))
% 0.20/0.53          | (v1_xboole_0 @ (u1_struct_0 @ sk_B)))),
% 0.20/0.53      inference('demod', [status(thm)], ['4', '5', '6'])).
% 0.20/0.53  thf('8', plain,
% 0.20/0.53      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.20/0.53        | (v1_xboole_0 @ (u1_struct_0 @ sk_C))
% 0.20/0.53        | ~ (m1_subset_1 @ (u1_struct_0 @ sk_C) @ 
% 0.20/0.53             (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))
% 0.20/0.53        | (m1_subset_1 @ 
% 0.20/0.53           (sk_F @ sk_F_1 @ (u1_struct_0 @ sk_C) @ sk_E @ 
% 0.20/0.53            (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D)) @ 
% 0.20/0.53           (u1_struct_0 @ sk_D))
% 0.20/0.53        | ((k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ sk_E @ 
% 0.20/0.53            (u1_struct_0 @ sk_C)) = (sk_F_1))
% 0.20/0.53        | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.20/0.53        | ~ (v1_funct_1 @ sk_E)
% 0.20/0.53        | (v1_xboole_0 @ (u1_struct_0 @ sk_D)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['1', '7'])).
% 0.20/0.53  thf('9', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('10', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf(t4_tsep_1, axiom,
% 0.20/0.53    (![A:$i]:
% 0.20/0.53     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.53       ( ![B:$i]:
% 0.20/0.53         ( ( m1_pre_topc @ B @ A ) =>
% 0.20/0.53           ( ![C:$i]:
% 0.20/0.53             ( ( m1_pre_topc @ C @ A ) =>
% 0.20/0.53               ( ( r1_tarski @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ C ) ) <=>
% 0.20/0.53                 ( m1_pre_topc @ B @ C ) ) ) ) ) ) ))).
% 0.20/0.53  thf('11', plain,
% 0.20/0.53      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.20/0.53         (~ (m1_pre_topc @ X24 @ X25)
% 0.20/0.53          | ~ (m1_pre_topc @ X24 @ X26)
% 0.20/0.53          | (r1_tarski @ (u1_struct_0 @ X24) @ (u1_struct_0 @ X26))
% 0.20/0.53          | ~ (m1_pre_topc @ X26 @ X25)
% 0.20/0.53          | ~ (l1_pre_topc @ X25)
% 0.20/0.53          | ~ (v2_pre_topc @ X25))),
% 0.20/0.53      inference('cnf', [status(esa)], [t4_tsep_1])).
% 0.20/0.53  thf('12', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         (~ (v2_pre_topc @ sk_A)
% 0.20/0.53          | ~ (l1_pre_topc @ sk_A)
% 0.20/0.53          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.20/0.53          | (r1_tarski @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ X0))
% 0.20/0.53          | ~ (m1_pre_topc @ sk_C @ X0))),
% 0.20/0.53      inference('sup-', [status(thm)], ['10', '11'])).
% 0.20/0.53  thf('13', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('14', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('15', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         (~ (m1_pre_topc @ X0 @ sk_A)
% 0.20/0.53          | (r1_tarski @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ X0))
% 0.20/0.53          | ~ (m1_pre_topc @ sk_C @ X0))),
% 0.20/0.53      inference('demod', [status(thm)], ['12', '13', '14'])).
% 0.20/0.53  thf('16', plain,
% 0.20/0.53      ((~ (m1_pre_topc @ sk_C @ sk_D)
% 0.20/0.53        | (r1_tarski @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['9', '15'])).
% 0.20/0.53  thf('17', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('18', plain, ((r1_tarski @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D))),
% 0.20/0.53      inference('demod', [status(thm)], ['16', '17'])).
% 0.20/0.53  thf(t3_subset, axiom,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.20/0.53  thf('19', plain,
% 0.20/0.53      (![X0 : $i, X2 : $i]:
% 0.20/0.53         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X2)) | ~ (r1_tarski @ X0 @ X2))),
% 0.20/0.53      inference('cnf', [status(esa)], [t3_subset])).
% 0.20/0.53  thf('20', plain,
% 0.20/0.53      ((m1_subset_1 @ (u1_struct_0 @ sk_C) @ 
% 0.20/0.53        (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['18', '19'])).
% 0.20/0.53  thf('21', plain,
% 0.20/0.53      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('22', plain, ((v1_funct_1 @ sk_E)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('23', plain,
% 0.20/0.53      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.20/0.53        | (v1_xboole_0 @ (u1_struct_0 @ sk_C))
% 0.20/0.53        | (m1_subset_1 @ 
% 0.20/0.53           (sk_F @ sk_F_1 @ (u1_struct_0 @ sk_C) @ sk_E @ 
% 0.20/0.53            (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D)) @ 
% 0.20/0.53           (u1_struct_0 @ sk_D))
% 0.20/0.53        | ((k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ sk_E @ 
% 0.20/0.53            (u1_struct_0 @ sk_C)) = (sk_F_1))
% 0.20/0.53        | (v1_xboole_0 @ (u1_struct_0 @ sk_D)))),
% 0.20/0.53      inference('demod', [status(thm)], ['8', '20', '21', '22'])).
% 0.20/0.53  thf('24', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf(t2_tsep_1, axiom,
% 0.20/0.53    (![A:$i]: ( ( l1_pre_topc @ A ) => ( m1_pre_topc @ A @ A ) ))).
% 0.20/0.53  thf('25', plain,
% 0.20/0.53      (![X23 : $i]: ((m1_pre_topc @ X23 @ X23) | ~ (l1_pre_topc @ X23))),
% 0.20/0.53      inference('cnf', [status(esa)], [t2_tsep_1])).
% 0.20/0.53  thf('26', plain,
% 0.20/0.53      ((m1_subset_1 @ sk_E @ 
% 0.20/0.53        (k1_zfmisc_1 @ 
% 0.20/0.53         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf(d5_tmap_1, axiom,
% 0.20/0.53    (![A:$i]:
% 0.20/0.53     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.53       ( ![B:$i]:
% 0.20/0.53         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.20/0.53             ( l1_pre_topc @ B ) ) =>
% 0.20/0.53           ( ![C:$i]:
% 0.20/0.53             ( ( m1_pre_topc @ C @ A ) =>
% 0.20/0.53               ( ![D:$i]:
% 0.20/0.53                 ( ( m1_pre_topc @ D @ A ) =>
% 0.20/0.53                   ( ![E:$i]:
% 0.20/0.53                     ( ( ( v1_funct_1 @ E ) & 
% 0.20/0.53                         ( v1_funct_2 @
% 0.20/0.53                           E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 0.20/0.53                         ( m1_subset_1 @
% 0.20/0.53                           E @ 
% 0.20/0.53                           ( k1_zfmisc_1 @
% 0.20/0.53                             ( k2_zfmisc_1 @
% 0.20/0.53                               ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.20/0.53                       ( ( m1_pre_topc @ D @ C ) =>
% 0.20/0.53                         ( ( k3_tmap_1 @ A @ B @ C @ D @ E ) =
% 0.20/0.53                           ( k2_partfun1 @
% 0.20/0.53                             ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ E @ 
% 0.20/0.53                             ( u1_struct_0 @ D ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.53  thf('27', plain,
% 0.20/0.53      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 0.20/0.53         ((v2_struct_0 @ X18)
% 0.20/0.53          | ~ (v2_pre_topc @ X18)
% 0.20/0.53          | ~ (l1_pre_topc @ X18)
% 0.20/0.53          | ~ (m1_pre_topc @ X19 @ X20)
% 0.20/0.53          | ~ (m1_pre_topc @ X19 @ X21)
% 0.20/0.53          | ((k3_tmap_1 @ X20 @ X18 @ X21 @ X19 @ X22)
% 0.20/0.53              = (k2_partfun1 @ (u1_struct_0 @ X21) @ (u1_struct_0 @ X18) @ 
% 0.20/0.53                 X22 @ (u1_struct_0 @ X19)))
% 0.20/0.53          | ~ (m1_subset_1 @ X22 @ 
% 0.20/0.53               (k1_zfmisc_1 @ 
% 0.20/0.53                (k2_zfmisc_1 @ (u1_struct_0 @ X21) @ (u1_struct_0 @ X18))))
% 0.20/0.53          | ~ (v1_funct_2 @ X22 @ (u1_struct_0 @ X21) @ (u1_struct_0 @ X18))
% 0.20/0.53          | ~ (v1_funct_1 @ X22)
% 0.20/0.53          | ~ (m1_pre_topc @ X21 @ X20)
% 0.20/0.53          | ~ (l1_pre_topc @ X20)
% 0.20/0.53          | ~ (v2_pre_topc @ X20)
% 0.20/0.53          | (v2_struct_0 @ X20))),
% 0.20/0.53      inference('cnf', [status(esa)], [d5_tmap_1])).
% 0.20/0.53  thf('28', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]:
% 0.20/0.53         ((v2_struct_0 @ X0)
% 0.20/0.53          | ~ (v2_pre_topc @ X0)
% 0.20/0.53          | ~ (l1_pre_topc @ X0)
% 0.20/0.53          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.20/0.53          | ~ (v1_funct_1 @ sk_E)
% 0.20/0.53          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.20/0.53          | ((k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E)
% 0.20/0.53              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.53                 sk_E @ (u1_struct_0 @ X1)))
% 0.20/0.53          | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.20/0.53          | ~ (m1_pre_topc @ X1 @ X0)
% 0.20/0.53          | ~ (l1_pre_topc @ sk_B)
% 0.20/0.53          | ~ (v2_pre_topc @ sk_B)
% 0.20/0.53          | (v2_struct_0 @ sk_B))),
% 0.20/0.53      inference('sup-', [status(thm)], ['26', '27'])).
% 0.20/0.53  thf('29', plain, ((v1_funct_1 @ sk_E)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('30', plain,
% 0.20/0.53      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('31', plain, ((l1_pre_topc @ sk_B)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('32', plain, ((v2_pre_topc @ sk_B)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('33', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]:
% 0.20/0.53         ((v2_struct_0 @ X0)
% 0.20/0.53          | ~ (v2_pre_topc @ X0)
% 0.20/0.53          | ~ (l1_pre_topc @ X0)
% 0.20/0.53          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.20/0.53          | ((k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E)
% 0.20/0.53              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.53                 sk_E @ (u1_struct_0 @ X1)))
% 0.20/0.53          | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.20/0.53          | ~ (m1_pre_topc @ X1 @ X0)
% 0.20/0.53          | (v2_struct_0 @ sk_B))),
% 0.20/0.53      inference('demod', [status(thm)], ['28', '29', '30', '31', '32'])).
% 0.20/0.53  thf('34', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         (~ (l1_pre_topc @ sk_D)
% 0.20/0.53          | (v2_struct_0 @ sk_B)
% 0.20/0.53          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.20/0.53          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.20/0.53          | ((k3_tmap_1 @ sk_D @ sk_B @ sk_D @ X0 @ sk_E)
% 0.20/0.53              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.53                 sk_E @ (u1_struct_0 @ X0)))
% 0.20/0.53          | ~ (l1_pre_topc @ sk_D)
% 0.20/0.53          | ~ (v2_pre_topc @ sk_D)
% 0.20/0.53          | (v2_struct_0 @ sk_D))),
% 0.20/0.53      inference('sup-', [status(thm)], ['25', '33'])).
% 0.20/0.53  thf('35', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf(dt_m1_pre_topc, axiom,
% 0.20/0.53    (![A:$i]:
% 0.20/0.53     ( ( l1_pre_topc @ A ) =>
% 0.20/0.53       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.20/0.53  thf('36', plain,
% 0.20/0.53      (![X15 : $i, X16 : $i]:
% 0.20/0.53         (~ (m1_pre_topc @ X15 @ X16)
% 0.20/0.53          | (l1_pre_topc @ X15)
% 0.20/0.53          | ~ (l1_pre_topc @ X16))),
% 0.20/0.53      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.20/0.53  thf('37', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_D))),
% 0.20/0.53      inference('sup-', [status(thm)], ['35', '36'])).
% 0.20/0.53  thf('38', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('39', plain, ((l1_pre_topc @ sk_D)),
% 0.20/0.53      inference('demod', [status(thm)], ['37', '38'])).
% 0.20/0.53  thf('40', plain, ((l1_pre_topc @ sk_D)),
% 0.20/0.53      inference('demod', [status(thm)], ['37', '38'])).
% 0.20/0.53  thf('41', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf(cc1_pre_topc, axiom,
% 0.20/0.53    (![A:$i]:
% 0.20/0.53     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.53       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( v2_pre_topc @ B ) ) ) ))).
% 0.20/0.53  thf('42', plain,
% 0.20/0.53      (![X12 : $i, X13 : $i]:
% 0.20/0.53         (~ (m1_pre_topc @ X12 @ X13)
% 0.20/0.53          | (v2_pre_topc @ X12)
% 0.20/0.53          | ~ (l1_pre_topc @ X13)
% 0.20/0.53          | ~ (v2_pre_topc @ X13))),
% 0.20/0.53      inference('cnf', [status(esa)], [cc1_pre_topc])).
% 0.20/0.53  thf('43', plain,
% 0.20/0.53      ((~ (v2_pre_topc @ sk_A) | ~ (l1_pre_topc @ sk_A) | (v2_pre_topc @ sk_D))),
% 0.20/0.53      inference('sup-', [status(thm)], ['41', '42'])).
% 0.20/0.53  thf('44', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('45', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('46', plain, ((v2_pre_topc @ sk_D)),
% 0.20/0.53      inference('demod', [status(thm)], ['43', '44', '45'])).
% 0.20/0.53  thf('47', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         ((v2_struct_0 @ sk_B)
% 0.20/0.53          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.20/0.53          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.20/0.53          | ((k3_tmap_1 @ sk_D @ sk_B @ sk_D @ X0 @ sk_E)
% 0.20/0.53              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.53                 sk_E @ (u1_struct_0 @ X0)))
% 0.20/0.53          | (v2_struct_0 @ sk_D))),
% 0.20/0.53      inference('demod', [status(thm)], ['34', '39', '40', '46'])).
% 0.20/0.53  thf('48', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         ((v2_struct_0 @ sk_D)
% 0.20/0.53          | ((k3_tmap_1 @ sk_D @ sk_B @ sk_D @ X0 @ sk_E)
% 0.20/0.53              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.53                 sk_E @ (u1_struct_0 @ X0)))
% 0.20/0.53          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.20/0.53          | (v2_struct_0 @ sk_B))),
% 0.20/0.53      inference('simplify', [status(thm)], ['47'])).
% 0.20/0.53  thf('49', plain,
% 0.20/0.53      (((v2_struct_0 @ sk_B)
% 0.20/0.53        | ((k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E)
% 0.20/0.53            = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.53               sk_E @ (u1_struct_0 @ sk_C)))
% 0.20/0.53        | (v2_struct_0 @ sk_D))),
% 0.20/0.53      inference('sup-', [status(thm)], ['24', '48'])).
% 0.20/0.53  thf('50', plain, (~ (v2_struct_0 @ sk_B)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('51', plain,
% 0.20/0.53      (((v2_struct_0 @ sk_D)
% 0.20/0.53        | ((k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E)
% 0.20/0.53            = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.53               sk_E @ (u1_struct_0 @ sk_C))))),
% 0.20/0.53      inference('clc', [status(thm)], ['49', '50'])).
% 0.20/0.53  thf('52', plain, (~ (v2_struct_0 @ sk_D)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('53', plain,
% 0.20/0.53      (((k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E)
% 0.20/0.53         = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ sk_E @ 
% 0.20/0.53            (u1_struct_0 @ sk_C)))),
% 0.20/0.53      inference('clc', [status(thm)], ['51', '52'])).
% 0.20/0.53  thf('54', plain,
% 0.20/0.53      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.20/0.53        | (v1_xboole_0 @ (u1_struct_0 @ sk_C))
% 0.20/0.53        | (m1_subset_1 @ 
% 0.20/0.53           (sk_F @ sk_F_1 @ (u1_struct_0 @ sk_C) @ sk_E @ 
% 0.20/0.53            (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D)) @ 
% 0.20/0.53           (u1_struct_0 @ sk_D))
% 0.20/0.53        | ((k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E) = (sk_F_1))
% 0.20/0.53        | (v1_xboole_0 @ (u1_struct_0 @ sk_D)))),
% 0.20/0.53      inference('demod', [status(thm)], ['23', '53'])).
% 0.20/0.53  thf('55', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('56', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('57', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]:
% 0.20/0.53         ((v2_struct_0 @ X0)
% 0.20/0.53          | ~ (v2_pre_topc @ X0)
% 0.20/0.53          | ~ (l1_pre_topc @ X0)
% 0.20/0.53          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.20/0.53          | ((k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E)
% 0.20/0.53              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.53                 sk_E @ (u1_struct_0 @ X1)))
% 0.20/0.53          | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.20/0.53          | ~ (m1_pre_topc @ X1 @ X0)
% 0.20/0.53          | (v2_struct_0 @ sk_B))),
% 0.20/0.53      inference('demod', [status(thm)], ['28', '29', '30', '31', '32'])).
% 0.20/0.53  thf('58', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         ((v2_struct_0 @ sk_B)
% 0.20/0.53          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.20/0.53          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.20/0.53          | ((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ X0 @ sk_E)
% 0.20/0.53              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.53                 sk_E @ (u1_struct_0 @ X0)))
% 0.20/0.53          | ~ (l1_pre_topc @ sk_A)
% 0.20/0.53          | ~ (v2_pre_topc @ sk_A)
% 0.20/0.53          | (v2_struct_0 @ sk_A))),
% 0.20/0.53      inference('sup-', [status(thm)], ['56', '57'])).
% 0.20/0.53  thf('59', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('60', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('61', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         ((v2_struct_0 @ sk_B)
% 0.20/0.53          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.20/0.53          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.20/0.53          | ((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ X0 @ sk_E)
% 0.20/0.53              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.53                 sk_E @ (u1_struct_0 @ X0)))
% 0.20/0.53          | (v2_struct_0 @ sk_A))),
% 0.20/0.53      inference('demod', [status(thm)], ['58', '59', '60'])).
% 0.20/0.53  thf('62', plain,
% 0.20/0.53      (((v2_struct_0 @ sk_A)
% 0.20/0.53        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E)
% 0.20/0.53            = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.53               sk_E @ (u1_struct_0 @ sk_C)))
% 0.20/0.53        | ~ (m1_pre_topc @ sk_C @ sk_D)
% 0.20/0.53        | (v2_struct_0 @ sk_B))),
% 0.20/0.53      inference('sup-', [status(thm)], ['55', '61'])).
% 0.20/0.53  thf('63', plain,
% 0.20/0.53      (((k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E)
% 0.20/0.53         = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ sk_E @ 
% 0.20/0.53            (u1_struct_0 @ sk_C)))),
% 0.20/0.53      inference('clc', [status(thm)], ['51', '52'])).
% 0.20/0.53  thf('64', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('65', plain,
% 0.20/0.53      (((v2_struct_0 @ sk_A)
% 0.20/0.53        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E)
% 0.20/0.53            = (k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E))
% 0.20/0.53        | (v2_struct_0 @ sk_B))),
% 0.20/0.53      inference('demod', [status(thm)], ['62', '63', '64'])).
% 0.20/0.53  thf('66', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('67', plain,
% 0.20/0.53      (((v2_struct_0 @ sk_B)
% 0.20/0.53        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E)
% 0.20/0.53            = (k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E)))),
% 0.20/0.53      inference('clc', [status(thm)], ['65', '66'])).
% 0.20/0.53  thf('68', plain, (~ (v2_struct_0 @ sk_B)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('69', plain,
% 0.20/0.53      (((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E)
% 0.20/0.53         = (k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E))),
% 0.20/0.53      inference('clc', [status(thm)], ['67', '68'])).
% 0.20/0.53  thf('70', plain,
% 0.20/0.53      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.20/0.53        | (v1_xboole_0 @ (u1_struct_0 @ sk_C))
% 0.20/0.53        | (m1_subset_1 @ 
% 0.20/0.53           (sk_F @ sk_F_1 @ (u1_struct_0 @ sk_C) @ sk_E @ 
% 0.20/0.53            (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D)) @ 
% 0.20/0.53           (u1_struct_0 @ sk_D))
% 0.20/0.53        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) = (sk_F_1))
% 0.20/0.53        | (v1_xboole_0 @ (u1_struct_0 @ sk_D)))),
% 0.20/0.53      inference('demod', [status(thm)], ['54', '69'])).
% 0.20/0.53  thf('71', plain,
% 0.20/0.53      ((m1_subset_1 @ sk_E @ 
% 0.20/0.53        (k1_zfmisc_1 @ 
% 0.20/0.53         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('72', plain,
% 0.20/0.53      ((m1_subset_1 @ sk_F_1 @ 
% 0.20/0.53        (k1_zfmisc_1 @ 
% 0.20/0.53         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('73', plain,
% 0.20/0.53      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.20/0.53         ((v1_xboole_0 @ X7)
% 0.20/0.53          | (v1_xboole_0 @ X8)
% 0.20/0.53          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9))
% 0.20/0.53          | (r2_hidden @ (sk_F @ X10 @ X8 @ X11 @ X7 @ X9) @ X8)
% 0.20/0.53          | ((k2_partfun1 @ X9 @ X7 @ X11 @ X8) = (X10))
% 0.20/0.53          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X7)))
% 0.20/0.53          | ~ (v1_funct_2 @ X10 @ X8 @ X7)
% 0.20/0.53          | ~ (v1_funct_1 @ X10)
% 0.20/0.53          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X7)))
% 0.20/0.53          | ~ (v1_funct_2 @ X11 @ X9 @ X7)
% 0.20/0.53          | ~ (v1_funct_1 @ X11)
% 0.20/0.53          | (v1_xboole_0 @ X9))),
% 0.20/0.53      inference('cnf', [status(esa)], [t173_funct_2])).
% 0.20/0.53  thf('74', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]:
% 0.20/0.53         ((v1_xboole_0 @ X0)
% 0.20/0.53          | ~ (v1_funct_1 @ X1)
% 0.20/0.53          | ~ (v1_funct_2 @ X1 @ X0 @ (u1_struct_0 @ sk_B))
% 0.20/0.53          | ~ (m1_subset_1 @ X1 @ 
% 0.20/0.53               (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ (u1_struct_0 @ sk_B))))
% 0.20/0.53          | ~ (v1_funct_1 @ sk_F_1)
% 0.20/0.53          | ~ (v1_funct_2 @ sk_F_1 @ (u1_struct_0 @ sk_C) @ 
% 0.20/0.53               (u1_struct_0 @ sk_B))
% 0.20/0.53          | ((k2_partfun1 @ X0 @ (u1_struct_0 @ sk_B) @ X1 @ 
% 0.20/0.53              (u1_struct_0 @ sk_C)) = (sk_F_1))
% 0.20/0.53          | (r2_hidden @ 
% 0.20/0.53             (sk_F @ sk_F_1 @ (u1_struct_0 @ sk_C) @ X1 @ 
% 0.20/0.53              (u1_struct_0 @ sk_B) @ X0) @ 
% 0.20/0.53             (u1_struct_0 @ sk_C))
% 0.20/0.53          | ~ (m1_subset_1 @ (u1_struct_0 @ sk_C) @ (k1_zfmisc_1 @ X0))
% 0.20/0.53          | (v1_xboole_0 @ (u1_struct_0 @ sk_C))
% 0.20/0.53          | (v1_xboole_0 @ (u1_struct_0 @ sk_B)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['72', '73'])).
% 0.20/0.53  thf('75', plain, ((v1_funct_1 @ sk_F_1)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('76', plain,
% 0.20/0.53      ((v1_funct_2 @ sk_F_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('77', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]:
% 0.20/0.53         ((v1_xboole_0 @ X0)
% 0.20/0.53          | ~ (v1_funct_1 @ X1)
% 0.20/0.53          | ~ (v1_funct_2 @ X1 @ X0 @ (u1_struct_0 @ sk_B))
% 0.20/0.53          | ~ (m1_subset_1 @ X1 @ 
% 0.20/0.53               (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ (u1_struct_0 @ sk_B))))
% 0.20/0.53          | ((k2_partfun1 @ X0 @ (u1_struct_0 @ sk_B) @ X1 @ 
% 0.20/0.53              (u1_struct_0 @ sk_C)) = (sk_F_1))
% 0.20/0.53          | (r2_hidden @ 
% 0.20/0.53             (sk_F @ sk_F_1 @ (u1_struct_0 @ sk_C) @ X1 @ 
% 0.20/0.53              (u1_struct_0 @ sk_B) @ X0) @ 
% 0.20/0.53             (u1_struct_0 @ sk_C))
% 0.20/0.53          | ~ (m1_subset_1 @ (u1_struct_0 @ sk_C) @ (k1_zfmisc_1 @ X0))
% 0.20/0.53          | (v1_xboole_0 @ (u1_struct_0 @ sk_C))
% 0.20/0.53          | (v1_xboole_0 @ (u1_struct_0 @ sk_B)))),
% 0.20/0.53      inference('demod', [status(thm)], ['74', '75', '76'])).
% 0.20/0.53  thf('78', plain,
% 0.20/0.53      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.20/0.53        | (v1_xboole_0 @ (u1_struct_0 @ sk_C))
% 0.20/0.53        | ~ (m1_subset_1 @ (u1_struct_0 @ sk_C) @ 
% 0.20/0.53             (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))
% 0.20/0.53        | (r2_hidden @ 
% 0.20/0.53           (sk_F @ sk_F_1 @ (u1_struct_0 @ sk_C) @ sk_E @ 
% 0.20/0.53            (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D)) @ 
% 0.20/0.53           (u1_struct_0 @ sk_C))
% 0.20/0.53        | ((k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ sk_E @ 
% 0.20/0.53            (u1_struct_0 @ sk_C)) = (sk_F_1))
% 0.20/0.53        | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.20/0.53        | ~ (v1_funct_1 @ sk_E)
% 0.20/0.53        | (v1_xboole_0 @ (u1_struct_0 @ sk_D)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['71', '77'])).
% 0.20/0.53  thf('79', plain,
% 0.20/0.53      ((m1_subset_1 @ (u1_struct_0 @ sk_C) @ 
% 0.20/0.53        (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['18', '19'])).
% 0.20/0.53  thf('80', plain,
% 0.20/0.53      (((k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E)
% 0.20/0.53         = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ sk_E @ 
% 0.20/0.53            (u1_struct_0 @ sk_C)))),
% 0.20/0.53      inference('clc', [status(thm)], ['51', '52'])).
% 0.20/0.53  thf('81', plain,
% 0.20/0.53      (((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E)
% 0.20/0.53         = (k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E))),
% 0.20/0.53      inference('clc', [status(thm)], ['67', '68'])).
% 0.20/0.53  thf('82', plain,
% 0.20/0.53      (((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E)
% 0.20/0.53         = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ sk_E @ 
% 0.20/0.53            (u1_struct_0 @ sk_C)))),
% 0.20/0.53      inference('demod', [status(thm)], ['80', '81'])).
% 0.20/0.53  thf('83', plain,
% 0.20/0.53      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('84', plain, ((v1_funct_1 @ sk_E)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('85', plain,
% 0.20/0.53      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.20/0.53        | (v1_xboole_0 @ (u1_struct_0 @ sk_C))
% 0.20/0.53        | (r2_hidden @ 
% 0.20/0.53           (sk_F @ sk_F_1 @ (u1_struct_0 @ sk_C) @ sk_E @ 
% 0.20/0.53            (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D)) @ 
% 0.20/0.53           (u1_struct_0 @ sk_C))
% 0.20/0.53        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) = (sk_F_1))
% 0.20/0.53        | (v1_xboole_0 @ (u1_struct_0 @ sk_D)))),
% 0.20/0.53      inference('demod', [status(thm)], ['78', '79', '82', '83', '84'])).
% 0.20/0.53  thf('86', plain,
% 0.20/0.53      (![X27 : $i]:
% 0.20/0.53         (~ (r2_hidden @ X27 @ (u1_struct_0 @ sk_C))
% 0.20/0.53          | ((k3_funct_2 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.53              sk_E @ X27) = (k1_funct_1 @ sk_F_1 @ X27))
% 0.20/0.53          | ~ (m1_subset_1 @ X27 @ (u1_struct_0 @ sk_D)))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('87', plain,
% 0.20/0.53      (((v1_xboole_0 @ (u1_struct_0 @ sk_D))
% 0.20/0.53        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) = (sk_F_1))
% 0.20/0.53        | (v1_xboole_0 @ (u1_struct_0 @ sk_C))
% 0.20/0.53        | (v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.20/0.53        | ~ (m1_subset_1 @ 
% 0.20/0.53             (sk_F @ sk_F_1 @ (u1_struct_0 @ sk_C) @ sk_E @ 
% 0.20/0.53              (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D)) @ 
% 0.20/0.53             (u1_struct_0 @ sk_D))
% 0.20/0.53        | ((k3_funct_2 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ sk_E @ 
% 0.20/0.53            (sk_F @ sk_F_1 @ (u1_struct_0 @ sk_C) @ sk_E @ 
% 0.20/0.53             (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D)))
% 0.20/0.53            = (k1_funct_1 @ sk_F_1 @ 
% 0.20/0.53               (sk_F @ sk_F_1 @ (u1_struct_0 @ sk_C) @ sk_E @ 
% 0.20/0.53                (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D)))))),
% 0.20/0.53      inference('sup-', [status(thm)], ['85', '86'])).
% 0.20/0.53  thf('88', plain,
% 0.20/0.53      (((v1_xboole_0 @ (u1_struct_0 @ sk_D))
% 0.20/0.53        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) = (sk_F_1))
% 0.20/0.53        | (v1_xboole_0 @ (u1_struct_0 @ sk_C))
% 0.20/0.53        | (v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.20/0.53        | ((k3_funct_2 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ sk_E @ 
% 0.20/0.53            (sk_F @ sk_F_1 @ (u1_struct_0 @ sk_C) @ sk_E @ 
% 0.20/0.53             (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D)))
% 0.20/0.53            = (k1_funct_1 @ sk_F_1 @ 
% 0.20/0.53               (sk_F @ sk_F_1 @ (u1_struct_0 @ sk_C) @ sk_E @ 
% 0.20/0.53                (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D))))
% 0.20/0.53        | (v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.20/0.53        | (v1_xboole_0 @ (u1_struct_0 @ sk_C))
% 0.20/0.53        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) = (sk_F_1))
% 0.20/0.53        | (v1_xboole_0 @ (u1_struct_0 @ sk_D)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['70', '87'])).
% 0.20/0.53  thf('89', plain,
% 0.20/0.53      ((((k3_funct_2 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ sk_E @ 
% 0.20/0.53          (sk_F @ sk_F_1 @ (u1_struct_0 @ sk_C) @ sk_E @ 
% 0.20/0.53           (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D)))
% 0.20/0.53          = (k1_funct_1 @ sk_F_1 @ 
% 0.20/0.53             (sk_F @ sk_F_1 @ (u1_struct_0 @ sk_C) @ sk_E @ 
% 0.20/0.53              (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D))))
% 0.20/0.53        | (v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.20/0.53        | (v1_xboole_0 @ (u1_struct_0 @ sk_C))
% 0.20/0.53        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) = (sk_F_1))
% 0.20/0.53        | (v1_xboole_0 @ (u1_struct_0 @ sk_D)))),
% 0.20/0.53      inference('simplify', [status(thm)], ['88'])).
% 0.20/0.53  thf('90', plain,
% 0.20/0.53      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.20/0.53         ((v1_xboole_0 @ X7)
% 0.20/0.53          | (v1_xboole_0 @ X8)
% 0.20/0.53          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9))
% 0.20/0.53          | ((k3_funct_2 @ X9 @ X7 @ X11 @ (sk_F @ X10 @ X8 @ X11 @ X7 @ X9))
% 0.20/0.53              != (k1_funct_1 @ X10 @ (sk_F @ X10 @ X8 @ X11 @ X7 @ X9)))
% 0.20/0.53          | ((k2_partfun1 @ X9 @ X7 @ X11 @ X8) = (X10))
% 0.20/0.53          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X7)))
% 0.20/0.53          | ~ (v1_funct_2 @ X10 @ X8 @ X7)
% 0.20/0.53          | ~ (v1_funct_1 @ X10)
% 0.20/0.53          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X7)))
% 0.20/0.53          | ~ (v1_funct_2 @ X11 @ X9 @ X7)
% 0.20/0.53          | ~ (v1_funct_1 @ X11)
% 0.20/0.53          | (v1_xboole_0 @ X9))),
% 0.20/0.53      inference('cnf', [status(esa)], [t173_funct_2])).
% 0.20/0.53  thf('91', plain,
% 0.20/0.53      ((((k1_funct_1 @ sk_F_1 @ 
% 0.20/0.53          (sk_F @ sk_F_1 @ (u1_struct_0 @ sk_C) @ sk_E @ 
% 0.20/0.53           (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D)))
% 0.20/0.53          != (k1_funct_1 @ sk_F_1 @ 
% 0.20/0.53              (sk_F @ sk_F_1 @ (u1_struct_0 @ sk_C) @ sk_E @ 
% 0.20/0.53               (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D))))
% 0.20/0.53        | (v1_xboole_0 @ (u1_struct_0 @ sk_D))
% 0.20/0.53        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) = (sk_F_1))
% 0.20/0.53        | (v1_xboole_0 @ (u1_struct_0 @ sk_C))
% 0.20/0.53        | (v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.20/0.53        | (v1_xboole_0 @ (u1_struct_0 @ sk_D))
% 0.20/0.53        | ~ (v1_funct_1 @ sk_E)
% 0.20/0.53        | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.20/0.53        | ~ (m1_subset_1 @ sk_E @ 
% 0.20/0.53             (k1_zfmisc_1 @ 
% 0.20/0.53              (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))
% 0.20/0.53        | ~ (v1_funct_1 @ sk_F_1)
% 0.20/0.53        | ~ (v1_funct_2 @ sk_F_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))
% 0.20/0.53        | ~ (m1_subset_1 @ sk_F_1 @ 
% 0.20/0.53             (k1_zfmisc_1 @ 
% 0.20/0.53              (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))
% 0.20/0.53        | ((k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ sk_E @ 
% 0.20/0.53            (u1_struct_0 @ sk_C)) = (sk_F_1))
% 0.20/0.53        | ~ (m1_subset_1 @ (u1_struct_0 @ sk_C) @ 
% 0.20/0.53             (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))
% 0.20/0.53        | (v1_xboole_0 @ (u1_struct_0 @ sk_C))
% 0.20/0.53        | (v1_xboole_0 @ (u1_struct_0 @ sk_B)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['89', '90'])).
% 0.20/0.53  thf('92', plain, ((v1_funct_1 @ sk_E)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('93', plain,
% 0.20/0.53      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('94', plain,
% 0.20/0.53      ((m1_subset_1 @ sk_E @ 
% 0.20/0.53        (k1_zfmisc_1 @ 
% 0.20/0.53         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('95', plain, ((v1_funct_1 @ sk_F_1)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('96', plain,
% 0.20/0.53      ((v1_funct_2 @ sk_F_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('97', plain,
% 0.20/0.53      ((m1_subset_1 @ sk_F_1 @ 
% 0.20/0.53        (k1_zfmisc_1 @ 
% 0.20/0.53         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('98', plain,
% 0.20/0.53      (((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E)
% 0.20/0.53         = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ sk_E @ 
% 0.20/0.53            (u1_struct_0 @ sk_C)))),
% 0.20/0.53      inference('demod', [status(thm)], ['80', '81'])).
% 0.20/0.53  thf('99', plain,
% 0.20/0.53      ((m1_subset_1 @ (u1_struct_0 @ sk_C) @ 
% 0.20/0.53        (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['18', '19'])).
% 0.20/0.53  thf('100', plain,
% 0.20/0.53      ((((k1_funct_1 @ sk_F_1 @ 
% 0.20/0.53          (sk_F @ sk_F_1 @ (u1_struct_0 @ sk_C) @ sk_E @ 
% 0.20/0.53           (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D)))
% 0.20/0.53          != (k1_funct_1 @ sk_F_1 @ 
% 0.20/0.53              (sk_F @ sk_F_1 @ (u1_struct_0 @ sk_C) @ sk_E @ 
% 0.20/0.53               (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D))))
% 0.20/0.53        | (v1_xboole_0 @ (u1_struct_0 @ sk_D))
% 0.20/0.53        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) = (sk_F_1))
% 0.20/0.53        | (v1_xboole_0 @ (u1_struct_0 @ sk_C))
% 0.20/0.53        | (v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.20/0.53        | (v1_xboole_0 @ (u1_struct_0 @ sk_D))
% 0.20/0.53        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) = (sk_F_1))
% 0.20/0.53        | (v1_xboole_0 @ (u1_struct_0 @ sk_C))
% 0.20/0.53        | (v1_xboole_0 @ (u1_struct_0 @ sk_B)))),
% 0.20/0.53      inference('demod', [status(thm)],
% 0.20/0.53                ['91', '92', '93', '94', '95', '96', '97', '98', '99'])).
% 0.20/0.53  thf('101', plain,
% 0.20/0.53      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.20/0.53        | (v1_xboole_0 @ (u1_struct_0 @ sk_C))
% 0.20/0.53        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) = (sk_F_1))
% 0.20/0.53        | (v1_xboole_0 @ (u1_struct_0 @ sk_D)))),
% 0.20/0.53      inference('simplify', [status(thm)], ['100'])).
% 0.20/0.53  thf('102', plain,
% 0.20/0.53      (~ (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.53          (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_F_1)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('103', plain,
% 0.20/0.53      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_F_1 @ 
% 0.20/0.53           sk_F_1)
% 0.20/0.53        | (v1_xboole_0 @ (u1_struct_0 @ sk_D))
% 0.20/0.53        | (v1_xboole_0 @ (u1_struct_0 @ sk_C))
% 0.20/0.53        | (v1_xboole_0 @ (u1_struct_0 @ sk_B)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['101', '102'])).
% 0.20/0.53  thf('104', plain,
% 0.20/0.53      ((m1_subset_1 @ sk_F_1 @ 
% 0.20/0.53        (k1_zfmisc_1 @ 
% 0.20/0.53         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf(redefinition_r2_funct_2, axiom,
% 0.20/0.53    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.53     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.20/0.53         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.20/0.53         ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.20/0.53         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.20/0.53       ( ( r2_funct_2 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 0.20/0.53  thf('105', plain,
% 0.20/0.53      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.20/0.53         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X4 @ X5)))
% 0.20/0.53          | ~ (v1_funct_2 @ X3 @ X4 @ X5)
% 0.20/0.53          | ~ (v1_funct_1 @ X3)
% 0.20/0.53          | ~ (v1_funct_1 @ X6)
% 0.20/0.53          | ~ (v1_funct_2 @ X6 @ X4 @ X5)
% 0.20/0.53          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X4 @ X5)))
% 0.20/0.53          | (r2_funct_2 @ X4 @ X5 @ X3 @ X6)
% 0.20/0.53          | ((X3) != (X6)))),
% 0.20/0.53      inference('cnf', [status(esa)], [redefinition_r2_funct_2])).
% 0.20/0.53  thf('106', plain,
% 0.20/0.53      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.20/0.53         ((r2_funct_2 @ X4 @ X5 @ X6 @ X6)
% 0.20/0.53          | ~ (v1_funct_1 @ X6)
% 0.20/0.53          | ~ (v1_funct_2 @ X6 @ X4 @ X5)
% 0.20/0.53          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X4 @ X5))))),
% 0.20/0.53      inference('simplify', [status(thm)], ['105'])).
% 0.20/0.53  thf('107', plain,
% 0.20/0.53      ((~ (v1_funct_2 @ sk_F_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))
% 0.20/0.53        | ~ (v1_funct_1 @ sk_F_1)
% 0.20/0.53        | (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_F_1 @ 
% 0.20/0.53           sk_F_1))),
% 0.20/0.53      inference('sup-', [status(thm)], ['104', '106'])).
% 0.20/0.53  thf('108', plain,
% 0.20/0.53      ((v1_funct_2 @ sk_F_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('109', plain, ((v1_funct_1 @ sk_F_1)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('110', plain,
% 0.20/0.53      ((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_F_1 @ 
% 0.20/0.53        sk_F_1)),
% 0.20/0.53      inference('demod', [status(thm)], ['107', '108', '109'])).
% 0.20/0.53  thf('111', plain,
% 0.20/0.53      (((v1_xboole_0 @ (u1_struct_0 @ sk_D))
% 0.20/0.53        | (v1_xboole_0 @ (u1_struct_0 @ sk_C))
% 0.20/0.53        | (v1_xboole_0 @ (u1_struct_0 @ sk_B)))),
% 0.20/0.53      inference('demod', [status(thm)], ['103', '110'])).
% 0.20/0.53  thf(fc2_struct_0, axiom,
% 0.20/0.53    (![A:$i]:
% 0.20/0.53     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.20/0.53       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.20/0.53  thf('112', plain,
% 0.20/0.53      (![X17 : $i]:
% 0.20/0.53         (~ (v1_xboole_0 @ (u1_struct_0 @ X17))
% 0.20/0.53          | ~ (l1_struct_0 @ X17)
% 0.20/0.53          | (v2_struct_0 @ X17))),
% 0.20/0.53      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.20/0.53  thf('113', plain,
% 0.20/0.53      (((v1_xboole_0 @ (u1_struct_0 @ sk_C))
% 0.20/0.53        | (v1_xboole_0 @ (u1_struct_0 @ sk_D))
% 0.20/0.53        | (v2_struct_0 @ sk_B)
% 0.20/0.53        | ~ (l1_struct_0 @ sk_B))),
% 0.20/0.53      inference('sup-', [status(thm)], ['111', '112'])).
% 0.20/0.53  thf('114', plain, ((l1_pre_topc @ sk_B)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf(dt_l1_pre_topc, axiom,
% 0.20/0.53    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.20/0.53  thf('115', plain,
% 0.20/0.53      (![X14 : $i]: ((l1_struct_0 @ X14) | ~ (l1_pre_topc @ X14))),
% 0.20/0.53      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.20/0.53  thf('116', plain, ((l1_struct_0 @ sk_B)),
% 0.20/0.53      inference('sup-', [status(thm)], ['114', '115'])).
% 0.20/0.53  thf('117', plain,
% 0.20/0.53      (((v1_xboole_0 @ (u1_struct_0 @ sk_C))
% 0.20/0.53        | (v1_xboole_0 @ (u1_struct_0 @ sk_D))
% 0.20/0.53        | (v2_struct_0 @ sk_B))),
% 0.20/0.53      inference('demod', [status(thm)], ['113', '116'])).
% 0.20/0.53  thf('118', plain, (~ (v2_struct_0 @ sk_B)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('119', plain,
% 0.20/0.53      (((v1_xboole_0 @ (u1_struct_0 @ sk_D))
% 0.20/0.53        | (v1_xboole_0 @ (u1_struct_0 @ sk_C)))),
% 0.20/0.53      inference('clc', [status(thm)], ['117', '118'])).
% 0.20/0.53  thf('120', plain,
% 0.20/0.53      (![X17 : $i]:
% 0.20/0.53         (~ (v1_xboole_0 @ (u1_struct_0 @ X17))
% 0.20/0.53          | ~ (l1_struct_0 @ X17)
% 0.20/0.53          | (v2_struct_0 @ X17))),
% 0.20/0.53      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.20/0.53  thf('121', plain,
% 0.20/0.53      (((v1_xboole_0 @ (u1_struct_0 @ sk_C))
% 0.20/0.53        | (v2_struct_0 @ sk_D)
% 0.20/0.53        | ~ (l1_struct_0 @ sk_D))),
% 0.20/0.53      inference('sup-', [status(thm)], ['119', '120'])).
% 0.20/0.53  thf('122', plain, ((l1_pre_topc @ sk_D)),
% 0.20/0.53      inference('demod', [status(thm)], ['37', '38'])).
% 0.20/0.53  thf('123', plain,
% 0.20/0.53      (![X14 : $i]: ((l1_struct_0 @ X14) | ~ (l1_pre_topc @ X14))),
% 0.20/0.53      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.20/0.53  thf('124', plain, ((l1_struct_0 @ sk_D)),
% 0.20/0.53      inference('sup-', [status(thm)], ['122', '123'])).
% 0.20/0.53  thf('125', plain,
% 0.20/0.53      (((v1_xboole_0 @ (u1_struct_0 @ sk_C)) | (v2_struct_0 @ sk_D))),
% 0.20/0.53      inference('demod', [status(thm)], ['121', '124'])).
% 0.20/0.53  thf('126', plain, (~ (v2_struct_0 @ sk_D)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('127', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_C))),
% 0.20/0.53      inference('clc', [status(thm)], ['125', '126'])).
% 0.20/0.53  thf('128', plain,
% 0.20/0.53      (![X17 : $i]:
% 0.20/0.53         (~ (v1_xboole_0 @ (u1_struct_0 @ X17))
% 0.20/0.53          | ~ (l1_struct_0 @ X17)
% 0.20/0.53          | (v2_struct_0 @ X17))),
% 0.20/0.53      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.20/0.53  thf('129', plain, (((v2_struct_0 @ sk_C) | ~ (l1_struct_0 @ sk_C))),
% 0.20/0.53      inference('sup-', [status(thm)], ['127', '128'])).
% 0.20/0.53  thf('130', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('131', plain,
% 0.20/0.53      (![X15 : $i, X16 : $i]:
% 0.20/0.53         (~ (m1_pre_topc @ X15 @ X16)
% 0.20/0.53          | (l1_pre_topc @ X15)
% 0.20/0.53          | ~ (l1_pre_topc @ X16))),
% 0.20/0.53      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.20/0.53  thf('132', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_C))),
% 0.20/0.53      inference('sup-', [status(thm)], ['130', '131'])).
% 0.20/0.53  thf('133', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('134', plain, ((l1_pre_topc @ sk_C)),
% 0.20/0.53      inference('demod', [status(thm)], ['132', '133'])).
% 0.20/0.53  thf('135', plain,
% 0.20/0.53      (![X14 : $i]: ((l1_struct_0 @ X14) | ~ (l1_pre_topc @ X14))),
% 0.20/0.53      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.20/0.53  thf('136', plain, ((l1_struct_0 @ sk_C)),
% 0.20/0.53      inference('sup-', [status(thm)], ['134', '135'])).
% 0.20/0.53  thf('137', plain, ((v2_struct_0 @ sk_C)),
% 0.20/0.53      inference('demod', [status(thm)], ['129', '136'])).
% 0.20/0.53  thf('138', plain, ($false), inference('demod', [status(thm)], ['0', '137'])).
% 0.20/0.53  
% 0.20/0.53  % SZS output end Refutation
% 0.20/0.53  
% 0.20/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
