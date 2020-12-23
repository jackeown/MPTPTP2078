%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.pdU1hUlflI

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:10:41 EST 2020

% Result     : Theorem 1.24s
% Output     : Refutation 1.29s
% Verified   : 
% Statistics : Number of formulae       :  340 (2114 expanded)
%              Number of leaves         :   39 ( 601 expanded)
%              Depth                    :   34
%              Number of atoms          : 5759 (57923 expanded)
%              Number of equality atoms :   60 ( 923 expanded)
%              Maximal formula depth    :   25 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_F_type,type,(
    sk_F: $i > $i > $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(r2_funct_2_type,type,(
    r2_funct_2: $i > $i > $i > $i > $o )).

thf(k2_tmap_1_type,type,(
    k2_tmap_1: $i > $i > $i > $i > $i )).

thf(k3_funct_2_type,type,(
    k3_funct_2: $i > $i > $i > $i > $i )).

thf(k2_partfun1_type,type,(
    k2_partfun1: $i > $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k4_tmap_1_type,type,(
    k4_tmap_1: $i > $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k3_tmap_1_type,type,(
    k3_tmap_1: $i > $i > $i > $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(t96_tmap_1,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( m1_pre_topc @ B @ A ) )
         => ! [C: $i] :
              ( ( ( v1_funct_1 @ C )
                & ( v1_funct_2 @ C @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) )
                & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) )
             => ( ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                   => ( ( r2_hidden @ D @ ( u1_struct_0 @ B ) )
                     => ( D
                        = ( k1_funct_1 @ C @ D ) ) ) )
               => ( r2_funct_2 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ ( k4_tmap_1 @ A @ B ) @ C ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( ~ ( v2_struct_0 @ B )
              & ( m1_pre_topc @ B @ A ) )
           => ! [C: $i] :
                ( ( ( v1_funct_1 @ C )
                  & ( v1_funct_2 @ C @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) )
                  & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) )
               => ( ! [D: $i] :
                      ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                     => ( ( r2_hidden @ D @ ( u1_struct_0 @ B ) )
                       => ( D
                          = ( k1_funct_1 @ C @ D ) ) ) )
                 => ( r2_funct_2 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ ( k4_tmap_1 @ A @ B ) @ C ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t96_tmap_1])).

thf('0',plain,(
    ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( m1_pre_topc @ A @ A ) ) )).

thf('1',plain,(
    ! [X39: $i] :
      ( ( m1_pre_topc @ X39 @ X39 )
      | ~ ( l1_pre_topc @ X39 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf(dt_k4_tmap_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_pre_topc @ B @ A ) )
     => ( ( v1_funct_1 @ ( k4_tmap_1 @ A @ B ) )
        & ( v1_funct_2 @ ( k4_tmap_1 @ A @ B ) @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) )
        & ( m1_subset_1 @ ( k4_tmap_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) ) )).

thf('2',plain,(
    ! [X35: $i,X36: $i] :
      ( ~ ( l1_pre_topc @ X35 )
      | ~ ( v2_pre_topc @ X35 )
      | ( v2_struct_0 @ X35 )
      | ~ ( m1_pre_topc @ X36 @ X35 )
      | ( v1_funct_1 @ ( k4_tmap_1 @ X35 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k4_tmap_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v1_funct_1 @ ( k4_tmap_1 @ X0 @ X0 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( v1_funct_1 @ ( k4_tmap_1 @ X0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('5',plain,(
    ! [X39: $i] :
      ( ( m1_pre_topc @ X39 @ X39 )
      | ~ ( l1_pre_topc @ X39 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('6',plain,(
    ! [X35: $i,X36: $i] :
      ( ~ ( l1_pre_topc @ X35 )
      | ~ ( v2_pre_topc @ X35 )
      | ( v2_struct_0 @ X35 )
      | ~ ( m1_pre_topc @ X36 @ X35 )
      | ( v1_funct_2 @ ( k4_tmap_1 @ X35 @ X36 ) @ ( u1_struct_0 @ X36 ) @ ( u1_struct_0 @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k4_tmap_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v1_funct_2 @ ( k4_tmap_1 @ X0 @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( v1_funct_2 @ ( k4_tmap_1 @ X0 @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    ! [X35: $i,X36: $i] :
      ( ~ ( l1_pre_topc @ X35 )
      | ~ ( v2_pre_topc @ X35 )
      | ( v2_struct_0 @ X35 )
      | ~ ( m1_pre_topc @ X36 @ X35 )
      | ( m1_subset_1 @ ( k4_tmap_1 @ X35 @ X36 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X36 ) @ ( u1_struct_0 @ X35 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k4_tmap_1])).

thf('11',plain,
    ( ( m1_subset_1 @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ( m1_subset_1 @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['11','12','13'])).

thf('15',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    m1_subset_1 @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X39: $i] :
      ( ( m1_pre_topc @ X39 @ X39 )
      | ~ ( l1_pre_topc @ X39 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('18',plain,(
    ! [X35: $i,X36: $i] :
      ( ~ ( l1_pre_topc @ X35 )
      | ~ ( v2_pre_topc @ X35 )
      | ( v2_struct_0 @ X35 )
      | ~ ( m1_pre_topc @ X36 @ X35 )
      | ( m1_subset_1 @ ( k4_tmap_1 @ X35 @ X36 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X36 ) @ ( u1_struct_0 @ X35 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k4_tmap_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( m1_subset_1 @ ( k4_tmap_1 @ X0 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( m1_subset_1 @ ( k4_tmap_1 @ X0 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf(t59_tmap_1,axiom,(
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
                  ( ( ( v1_funct_1 @ D )
                    & ( v1_funct_2 @ D @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) )
                    & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) )
                 => ! [E: $i] :
                      ( ( ( v1_funct_1 @ E )
                        & ( v1_funct_2 @ E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ A ) )
                        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ A ) ) ) ) )
                     => ( ! [F: $i] :
                            ( ( m1_subset_1 @ F @ ( u1_struct_0 @ B ) )
                           => ( ( r2_hidden @ F @ ( u1_struct_0 @ C ) )
                             => ( ( k3_funct_2 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ D @ F )
                                = ( k1_funct_1 @ E @ F ) ) ) )
                       => ( r2_funct_2 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ A ) @ ( k2_tmap_1 @ B @ A @ D @ C ) @ E ) ) ) ) ) ) ) )).

thf('21',plain,(
    ! [X40: $i,X41: $i,X42: $i,X43: $i,X44: $i] :
      ( ( v2_struct_0 @ X40 )
      | ~ ( v2_pre_topc @ X40 )
      | ~ ( l1_pre_topc @ X40 )
      | ~ ( v1_funct_1 @ X41 )
      | ~ ( v1_funct_2 @ X41 @ ( u1_struct_0 @ X40 ) @ ( u1_struct_0 @ X42 ) )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X40 ) @ ( u1_struct_0 @ X42 ) ) ) )
      | ( r2_hidden @ ( sk_F @ X43 @ X41 @ X44 @ X40 @ X42 ) @ ( u1_struct_0 @ X44 ) )
      | ( r2_funct_2 @ ( u1_struct_0 @ X44 ) @ ( u1_struct_0 @ X42 ) @ ( k2_tmap_1 @ X40 @ X42 @ X41 @ X44 ) @ X43 )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X44 ) @ ( u1_struct_0 @ X42 ) ) ) )
      | ~ ( v1_funct_2 @ X43 @ ( u1_struct_0 @ X44 ) @ ( u1_struct_0 @ X42 ) )
      | ~ ( v1_funct_1 @ X43 )
      | ~ ( m1_pre_topc @ X44 @ X40 )
      | ( v2_struct_0 @ X44 )
      | ~ ( l1_pre_topc @ X42 )
      | ~ ( v2_pre_topc @ X42 )
      | ( v2_struct_0 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t59_tmap_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X1 )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_funct_2 @ X2 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ( r2_funct_2 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ X0 ) @ ( k2_tmap_1 @ X0 @ X0 @ ( k4_tmap_1 @ X0 @ X0 ) @ X1 ) @ X2 )
      | ( r2_hidden @ ( sk_F @ X2 @ ( k4_tmap_1 @ X0 @ X0 ) @ X1 @ X0 @ X0 ) @ ( u1_struct_0 @ X1 ) )
      | ~ ( v1_funct_2 @ ( k4_tmap_1 @ X0 @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k4_tmap_1 @ X0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_funct_1 @ ( k4_tmap_1 @ X0 @ X0 ) )
      | ~ ( v1_funct_2 @ ( k4_tmap_1 @ X0 @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ( r2_hidden @ ( sk_F @ X2 @ ( k4_tmap_1 @ X0 @ X0 ) @ X1 @ X0 @ X0 ) @ ( u1_struct_0 @ X1 ) )
      | ( r2_funct_2 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ X0 ) @ ( k2_tmap_1 @ X0 @ X0 @ ( k4_tmap_1 @ X0 @ X0 ) @ X1 ) @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( v1_funct_2 @ X2 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ~ ( m1_pre_topc @ sk_B @ sk_A )
    | ~ ( v1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( v1_funct_2 @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tmap_1 @ sk_A @ sk_A @ ( k4_tmap_1 @ sk_A @ sk_A ) @ sk_B ) @ ( k4_tmap_1 @ sk_A @ sk_B ) )
    | ( r2_hidden @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( k4_tmap_1 @ sk_A @ sk_A ) @ sk_B @ sk_A @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_2 @ ( k4_tmap_1 @ sk_A @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_A ) ) ),
    inference('sup-',[status(thm)],['16','23'])).

thf('25',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    ! [X35: $i,X36: $i] :
      ( ~ ( l1_pre_topc @ X35 )
      | ~ ( v2_pre_topc @ X35 )
      | ( v2_struct_0 @ X35 )
      | ~ ( m1_pre_topc @ X36 @ X35 )
      | ( v1_funct_1 @ ( k4_tmap_1 @ X35 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k4_tmap_1])).

thf('30',plain,
    ( ( v1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ( v1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['30','31','32'])).

thf('34',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    v1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['33','34'])).

thf('36',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    ! [X35: $i,X36: $i] :
      ( ~ ( l1_pre_topc @ X35 )
      | ~ ( v2_pre_topc @ X35 )
      | ( v2_struct_0 @ X35 )
      | ~ ( m1_pre_topc @ X36 @ X35 )
      | ( v1_funct_2 @ ( k4_tmap_1 @ X35 @ X36 ) @ ( u1_struct_0 @ X36 ) @ ( u1_struct_0 @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k4_tmap_1])).

thf('38',plain,
    ( ( v1_funct_2 @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,
    ( ( v1_funct_2 @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['38','39','40'])).

thf('42',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    v1_funct_2 @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['41','42'])).

thf('44',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tmap_1 @ sk_A @ sk_A @ ( k4_tmap_1 @ sk_A @ sk_A ) @ sk_B ) @ ( k4_tmap_1 @ sk_A @ sk_B ) )
    | ( r2_hidden @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( k4_tmap_1 @ sk_A @ sk_A ) @ sk_B @ sk_A @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_2 @ ( k4_tmap_1 @ sk_A @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['24','25','26','27','35','43'])).

thf('45',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( v1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_A ) )
    | ( r2_hidden @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( k4_tmap_1 @ sk_A @ sk_A ) @ sk_B @ sk_A @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tmap_1 @ sk_A @ sk_A @ ( k4_tmap_1 @ sk_A @ sk_A ) @ sk_B ) @ ( k4_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['8','44'])).

thf('46',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_A ) )
    | ( r2_hidden @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( k4_tmap_1 @ sk_A @ sk_A ) @ sk_B @ sk_A @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tmap_1 @ sk_A @ sk_A @ ( k4_tmap_1 @ sk_A @ sk_A ) @ sk_B ) @ ( k4_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['45','46','47'])).

thf('49',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tmap_1 @ sk_A @ sk_A @ ( k4_tmap_1 @ sk_A @ sk_A ) @ sk_B ) @ ( k4_tmap_1 @ sk_A @ sk_B ) )
    | ( r2_hidden @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( k4_tmap_1 @ sk_A @ sk_A ) @ sk_B @ sk_A @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( k4_tmap_1 @ sk_A @ sk_A ) @ sk_B @ sk_A @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tmap_1 @ sk_A @ sk_A @ ( k4_tmap_1 @ sk_A @ sk_A ) @ sk_B ) @ ( k4_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['4','49'])).

thf('51',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( k4_tmap_1 @ sk_A @ sk_A ) @ sk_B @ sk_A @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tmap_1 @ sk_A @ sk_A @ ( k4_tmap_1 @ sk_A @ sk_A ) @ sk_B ) @ ( k4_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['50','51','52'])).

thf('54',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tmap_1 @ sk_A @ sk_A @ ( k4_tmap_1 @ sk_A @ sk_A ) @ sk_B ) @ ( k4_tmap_1 @ sk_A @ sk_B ) )
    | ( r2_hidden @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( k4_tmap_1 @ sk_A @ sk_A ) @ sk_B @ sk_A @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['53'])).

thf('55',plain,(
    ! [X39: $i] :
      ( ( m1_pre_topc @ X39 @ X39 )
      | ~ ( l1_pre_topc @ X39 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('56',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( v1_funct_1 @ ( k4_tmap_1 @ X0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( v1_funct_2 @ ( k4_tmap_1 @ X0 @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( m1_subset_1 @ ( k4_tmap_1 @ X0 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf(dt_k3_tmap_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ~ ( v2_struct_0 @ B )
        & ( v2_pre_topc @ B )
        & ( l1_pre_topc @ B )
        & ( m1_pre_topc @ C @ A )
        & ( m1_pre_topc @ D @ A )
        & ( v1_funct_1 @ E )
        & ( v1_funct_2 @ E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) )
     => ( ( v1_funct_1 @ ( k3_tmap_1 @ A @ B @ C @ D @ E ) )
        & ( v1_funct_2 @ ( k3_tmap_1 @ A @ B @ C @ D @ E ) @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) )
        & ( m1_subset_1 @ ( k3_tmap_1 @ A @ B @ C @ D @ E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) ) )).

thf('60',plain,(
    ! [X30: $i,X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( m1_pre_topc @ X30 @ X31 )
      | ~ ( m1_pre_topc @ X32 @ X31 )
      | ~ ( l1_pre_topc @ X33 )
      | ~ ( v2_pre_topc @ X33 )
      | ( v2_struct_0 @ X33 )
      | ~ ( l1_pre_topc @ X31 )
      | ~ ( v2_pre_topc @ X31 )
      | ( v2_struct_0 @ X31 )
      | ~ ( v1_funct_1 @ X34 )
      | ~ ( v1_funct_2 @ X34 @ ( u1_struct_0 @ X32 ) @ ( u1_struct_0 @ X33 ) )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X32 ) @ ( u1_struct_0 @ X33 ) ) ) )
      | ( m1_subset_1 @ ( k3_tmap_1 @ X31 @ X33 @ X32 @ X30 @ X34 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X30 ) @ ( u1_struct_0 @ X33 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_tmap_1])).

thf('61',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( m1_subset_1 @ ( k3_tmap_1 @ X2 @ X0 @ X0 @ X1 @ ( k4_tmap_1 @ X0 @ X0 ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( v1_funct_2 @ ( k4_tmap_1 @ X0 @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k4_tmap_1 @ X0 @ X0 ) )
      | ( v2_struct_0 @ X2 )
      | ~ ( v2_pre_topc @ X2 )
      | ~ ( l1_pre_topc @ X2 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X2 )
      | ~ ( m1_pre_topc @ X1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_pre_topc @ X1 @ X2 )
      | ~ ( m1_pre_topc @ X0 @ X2 )
      | ~ ( l1_pre_topc @ X2 )
      | ~ ( v2_pre_topc @ X2 )
      | ( v2_struct_0 @ X2 )
      | ~ ( v1_funct_1 @ ( k4_tmap_1 @ X0 @ X0 ) )
      | ~ ( v1_funct_2 @ ( k4_tmap_1 @ X0 @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ( m1_subset_1 @ ( k3_tmap_1 @ X2 @ X0 @ X0 @ X1 @ ( k4_tmap_1 @ X0 @ X0 ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['61'])).

thf('63',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( m1_subset_1 @ ( k3_tmap_1 @ X2 @ X0 @ X0 @ X1 @ ( k4_tmap_1 @ X0 @ X0 ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( v1_funct_1 @ ( k4_tmap_1 @ X0 @ X0 ) )
      | ( v2_struct_0 @ X2 )
      | ~ ( v2_pre_topc @ X2 )
      | ~ ( l1_pre_topc @ X2 )
      | ~ ( m1_pre_topc @ X0 @ X2 )
      | ~ ( m1_pre_topc @ X1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['58','62'])).

thf('64',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_pre_topc @ X1 @ X2 )
      | ~ ( m1_pre_topc @ X0 @ X2 )
      | ~ ( l1_pre_topc @ X2 )
      | ~ ( v2_pre_topc @ X2 )
      | ( v2_struct_0 @ X2 )
      | ~ ( v1_funct_1 @ ( k4_tmap_1 @ X0 @ X0 ) )
      | ( m1_subset_1 @ ( k3_tmap_1 @ X2 @ X0 @ X0 @ X1 @ ( k4_tmap_1 @ X0 @ X0 ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['63'])).

thf('65',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( m1_subset_1 @ ( k3_tmap_1 @ X2 @ X0 @ X0 @ X1 @ ( k4_tmap_1 @ X0 @ X0 ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ( v2_struct_0 @ X2 )
      | ~ ( v2_pre_topc @ X2 )
      | ~ ( l1_pre_topc @ X2 )
      | ~ ( m1_pre_topc @ X0 @ X2 )
      | ~ ( m1_pre_topc @ X1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['57','64'])).

thf('66',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_pre_topc @ X1 @ X2 )
      | ~ ( m1_pre_topc @ X0 @ X2 )
      | ~ ( l1_pre_topc @ X2 )
      | ~ ( v2_pre_topc @ X2 )
      | ( v2_struct_0 @ X2 )
      | ( m1_subset_1 @ ( k3_tmap_1 @ X2 @ X0 @ X0 @ X1 @ ( k4_tmap_1 @ X0 @ X0 ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ X0 @ X0 @ sk_B @ ( k4_tmap_1 @ X0 @ X0 ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['56','66'])).

thf('68',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ X0 @ X0 @ sk_B @ ( k4_tmap_1 @ X0 @ X0 ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['67','68','69'])).

thf('71',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_A @ sk_A @ sk_B @ ( k4_tmap_1 @ sk_A @ sk_A ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ~ ( v2_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['55','70'])).

thf('72',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_A @ sk_A @ sk_B @ ( k4_tmap_1 @ sk_A @ sk_A ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['71','72','73','74'])).

thf('76',plain,
    ( ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_A @ sk_A @ sk_B @ ( k4_tmap_1 @ sk_A @ sk_A ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['75'])).

thf('77',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_A @ sk_A @ sk_B @ ( k4_tmap_1 @ sk_A @ sk_A ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X39: $i] :
      ( ( m1_pre_topc @ X39 @ X39 )
      | ~ ( l1_pre_topc @ X39 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('80',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( v1_funct_1 @ ( k4_tmap_1 @ X0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('82',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( v1_funct_2 @ ( k4_tmap_1 @ X0 @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('83',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( m1_subset_1 @ ( k4_tmap_1 @ X0 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['19'])).

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

thf('84',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ( v2_struct_0 @ X25 )
      | ~ ( v2_pre_topc @ X25 )
      | ~ ( l1_pre_topc @ X25 )
      | ~ ( m1_pre_topc @ X26 @ X27 )
      | ~ ( m1_pre_topc @ X26 @ X28 )
      | ( ( k3_tmap_1 @ X27 @ X25 @ X28 @ X26 @ X29 )
        = ( k2_partfun1 @ ( u1_struct_0 @ X28 ) @ ( u1_struct_0 @ X25 ) @ X29 @ ( u1_struct_0 @ X26 ) ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X28 ) @ ( u1_struct_0 @ X25 ) ) ) )
      | ~ ( v1_funct_2 @ X29 @ ( u1_struct_0 @ X28 ) @ ( u1_struct_0 @ X25 ) )
      | ~ ( v1_funct_1 @ X29 )
      | ~ ( m1_pre_topc @ X28 @ X27 )
      | ~ ( l1_pre_topc @ X27 )
      | ~ ( v2_pre_topc @ X27 )
      | ( v2_struct_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[d5_tmap_1])).

thf('85',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 )
      | ~ ( v1_funct_1 @ ( k4_tmap_1 @ X0 @ X0 ) )
      | ~ ( v1_funct_2 @ ( k4_tmap_1 @ X0 @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ( ( k3_tmap_1 @ X1 @ X0 @ X0 @ X2 @ ( k4_tmap_1 @ X0 @ X0 ) )
        = ( k2_partfun1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( k4_tmap_1 @ X0 @ X0 ) @ ( u1_struct_0 @ X2 ) ) )
      | ~ ( m1_pre_topc @ X2 @ X0 )
      | ~ ( m1_pre_topc @ X2 @ X1 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_pre_topc @ X2 @ X1 )
      | ~ ( m1_pre_topc @ X2 @ X0 )
      | ( ( k3_tmap_1 @ X1 @ X0 @ X0 @ X2 @ ( k4_tmap_1 @ X0 @ X0 ) )
        = ( k2_partfun1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( k4_tmap_1 @ X0 @ X0 ) @ ( u1_struct_0 @ X2 ) ) )
      | ~ ( v1_funct_2 @ ( k4_tmap_1 @ X0 @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k4_tmap_1 @ X0 @ X0 ) )
      | ~ ( m1_pre_topc @ X0 @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['85'])).

thf('87',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 )
      | ~ ( v1_funct_1 @ ( k4_tmap_1 @ X0 @ X0 ) )
      | ( ( k3_tmap_1 @ X1 @ X0 @ X0 @ X2 @ ( k4_tmap_1 @ X0 @ X0 ) )
        = ( k2_partfun1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( k4_tmap_1 @ X0 @ X0 ) @ ( u1_struct_0 @ X2 ) ) )
      | ~ ( m1_pre_topc @ X2 @ X0 )
      | ~ ( m1_pre_topc @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['82','86'])).

thf('88',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_pre_topc @ X2 @ X1 )
      | ~ ( m1_pre_topc @ X2 @ X0 )
      | ( ( k3_tmap_1 @ X1 @ X0 @ X0 @ X2 @ ( k4_tmap_1 @ X0 @ X0 ) )
        = ( k2_partfun1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( k4_tmap_1 @ X0 @ X0 ) @ ( u1_struct_0 @ X2 ) ) )
      | ~ ( v1_funct_1 @ ( k4_tmap_1 @ X0 @ X0 ) )
      | ~ ( m1_pre_topc @ X0 @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['87'])).

thf('89',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 )
      | ( ( k3_tmap_1 @ X1 @ X0 @ X0 @ X2 @ ( k4_tmap_1 @ X0 @ X0 ) )
        = ( k2_partfun1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( k4_tmap_1 @ X0 @ X0 ) @ ( u1_struct_0 @ X2 ) ) )
      | ~ ( m1_pre_topc @ X2 @ X0 )
      | ~ ( m1_pre_topc @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['81','88'])).

thf('90',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_pre_topc @ X2 @ X1 )
      | ~ ( m1_pre_topc @ X2 @ X0 )
      | ( ( k3_tmap_1 @ X1 @ X0 @ X0 @ X2 @ ( k4_tmap_1 @ X0 @ X0 ) )
        = ( k2_partfun1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( k4_tmap_1 @ X0 @ X0 ) @ ( u1_struct_0 @ X2 ) ) )
      | ~ ( m1_pre_topc @ X0 @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['89'])).

thf('91',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( ( k3_tmap_1 @ sk_A @ X0 @ X0 @ sk_B @ ( k4_tmap_1 @ X0 @ X0 ) )
        = ( k2_partfun1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( k4_tmap_1 @ X0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) )
      | ~ ( m1_pre_topc @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['80','90'])).

thf('92',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( ( k3_tmap_1 @ sk_A @ X0 @ X0 @ sk_B @ ( k4_tmap_1 @ X0 @ X0 ) )
        = ( k2_partfun1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( k4_tmap_1 @ X0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) )
      | ~ ( m1_pre_topc @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['91','92','93'])).

thf('95',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( m1_pre_topc @ sk_B @ sk_A )
    | ( ( k3_tmap_1 @ sk_A @ sk_A @ sk_A @ sk_B @ ( k4_tmap_1 @ sk_A @ sk_A ) )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['79','94'])).

thf('96',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( v1_funct_1 @ ( k4_tmap_1 @ X0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('100',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( v1_funct_2 @ ( k4_tmap_1 @ X0 @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('101',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( m1_subset_1 @ ( k4_tmap_1 @ X0 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['19'])).

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

thf('102',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ( v2_struct_0 @ X21 )
      | ~ ( v2_pre_topc @ X21 )
      | ~ ( l1_pre_topc @ X21 )
      | ~ ( m1_pre_topc @ X22 @ X23 )
      | ( ( k2_tmap_1 @ X23 @ X21 @ X24 @ X22 )
        = ( k2_partfun1 @ ( u1_struct_0 @ X23 ) @ ( u1_struct_0 @ X21 ) @ X24 @ ( u1_struct_0 @ X22 ) ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X23 ) @ ( u1_struct_0 @ X21 ) ) ) )
      | ~ ( v1_funct_2 @ X24 @ ( u1_struct_0 @ X23 ) @ ( u1_struct_0 @ X21 ) )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( l1_pre_topc @ X23 )
      | ~ ( v2_pre_topc @ X23 )
      | ( v2_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[d4_tmap_1])).

thf('103',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_funct_1 @ ( k4_tmap_1 @ X0 @ X0 ) )
      | ~ ( v1_funct_2 @ ( k4_tmap_1 @ X0 @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ( ( k2_tmap_1 @ X0 @ X0 @ ( k4_tmap_1 @ X0 @ X0 ) @ X1 )
        = ( k2_partfun1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( k4_tmap_1 @ X0 @ X0 ) @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_pre_topc @ X1 @ X0 )
      | ( ( k2_tmap_1 @ X0 @ X0 @ ( k4_tmap_1 @ X0 @ X0 ) @ X1 )
        = ( k2_partfun1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( k4_tmap_1 @ X0 @ X0 ) @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( v1_funct_2 @ ( k4_tmap_1 @ X0 @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k4_tmap_1 @ X0 @ X0 ) )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['103'])).

thf('105',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( v1_funct_1 @ ( k4_tmap_1 @ X0 @ X0 ) )
      | ( ( k2_tmap_1 @ X0 @ X0 @ ( k4_tmap_1 @ X0 @ X0 ) @ X1 )
        = ( k2_partfun1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( k4_tmap_1 @ X0 @ X0 ) @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( m1_pre_topc @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['100','104'])).

thf('106',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_pre_topc @ X1 @ X0 )
      | ( ( k2_tmap_1 @ X0 @ X0 @ ( k4_tmap_1 @ X0 @ X0 ) @ X1 )
        = ( k2_partfun1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( k4_tmap_1 @ X0 @ X0 ) @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( v1_funct_1 @ ( k4_tmap_1 @ X0 @ X0 ) )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['105'])).

thf('107',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( ( k2_tmap_1 @ X0 @ X0 @ ( k4_tmap_1 @ X0 @ X0 ) @ X1 )
        = ( k2_partfun1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( k4_tmap_1 @ X0 @ X0 ) @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( m1_pre_topc @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['99','106'])).

thf('108',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_pre_topc @ X1 @ X0 )
      | ( ( k2_tmap_1 @ X0 @ X0 @ ( k4_tmap_1 @ X0 @ X0 ) @ X1 )
        = ( k2_partfun1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( k4_tmap_1 @ X0 @ X0 ) @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['107'])).

thf('109',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ( ( k2_tmap_1 @ sk_A @ sk_A @ ( k4_tmap_1 @ sk_A @ sk_A ) @ sk_B )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['98','108'])).

thf('110',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k2_tmap_1 @ sk_A @ sk_A @ ( k4_tmap_1 @ sk_A @ sk_A ) @ sk_B )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['109','110','111'])).

thf('113',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_A @ ( k4_tmap_1 @ sk_A @ sk_A ) @ sk_B )
    = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['112','113'])).

thf('115',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,
    ( ( ( k3_tmap_1 @ sk_A @ sk_A @ sk_A @ sk_B @ ( k4_tmap_1 @ sk_A @ sk_A ) )
      = ( k2_tmap_1 @ sk_A @ sk_A @ ( k4_tmap_1 @ sk_A @ sk_A ) @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['95','96','97','114','115','116'])).

thf('118',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k3_tmap_1 @ sk_A @ sk_A @ sk_A @ sk_B @ ( k4_tmap_1 @ sk_A @ sk_A ) )
      = ( k2_tmap_1 @ sk_A @ sk_A @ ( k4_tmap_1 @ sk_A @ sk_A ) @ sk_B ) ) ),
    inference(simplify,[status(thm)],['117'])).

thf('119',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,
    ( ( k3_tmap_1 @ sk_A @ sk_A @ sk_A @ sk_B @ ( k4_tmap_1 @ sk_A @ sk_A ) )
    = ( k2_tmap_1 @ sk_A @ sk_A @ ( k4_tmap_1 @ sk_A @ sk_A ) @ sk_B ) ),
    inference(clc,[status(thm)],['118','119'])).

thf('121',plain,(
    m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_A @ ( k4_tmap_1 @ sk_A @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['78','120'])).

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

thf('122',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) )
      | ~ ( v1_funct_2 @ X10 @ X11 @ X12 )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_funct_2 @ X13 @ X11 @ X12 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) )
      | ( X10 = X13 )
      | ~ ( r2_funct_2 @ X11 @ X12 @ X10 @ X13 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_funct_2])).

thf('123',plain,(
    ! [X0: $i] :
      ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tmap_1 @ sk_A @ sk_A @ ( k4_tmap_1 @ sk_A @ sk_A ) @ sk_B ) @ X0 )
      | ( ( k2_tmap_1 @ sk_A @ sk_A @ ( k4_tmap_1 @ sk_A @ sk_A ) @ sk_B )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) )
      | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_A @ ( k4_tmap_1 @ sk_A @ sk_A ) @ sk_B ) )
      | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_A @ ( k4_tmap_1 @ sk_A @ sk_A ) @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['121','122'])).

thf('124',plain,(
    ! [X39: $i] :
      ( ( m1_pre_topc @ X39 @ X39 )
      | ~ ( l1_pre_topc @ X39 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('125',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( v1_funct_1 @ ( k4_tmap_1 @ X0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('127',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( v1_funct_2 @ ( k4_tmap_1 @ X0 @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('128',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( m1_subset_1 @ ( k4_tmap_1 @ X0 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('129',plain,(
    ! [X30: $i,X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( m1_pre_topc @ X30 @ X31 )
      | ~ ( m1_pre_topc @ X32 @ X31 )
      | ~ ( l1_pre_topc @ X33 )
      | ~ ( v2_pre_topc @ X33 )
      | ( v2_struct_0 @ X33 )
      | ~ ( l1_pre_topc @ X31 )
      | ~ ( v2_pre_topc @ X31 )
      | ( v2_struct_0 @ X31 )
      | ~ ( v1_funct_1 @ X34 )
      | ~ ( v1_funct_2 @ X34 @ ( u1_struct_0 @ X32 ) @ ( u1_struct_0 @ X33 ) )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X32 ) @ ( u1_struct_0 @ X33 ) ) ) )
      | ( v1_funct_1 @ ( k3_tmap_1 @ X31 @ X33 @ X32 @ X30 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_tmap_1])).

thf('130',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v1_funct_1 @ ( k3_tmap_1 @ X2 @ X0 @ X0 @ X1 @ ( k4_tmap_1 @ X0 @ X0 ) ) )
      | ~ ( v1_funct_2 @ ( k4_tmap_1 @ X0 @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k4_tmap_1 @ X0 @ X0 ) )
      | ( v2_struct_0 @ X2 )
      | ~ ( v2_pre_topc @ X2 )
      | ~ ( l1_pre_topc @ X2 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X2 )
      | ~ ( m1_pre_topc @ X1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['128','129'])).

thf('131',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_pre_topc @ X1 @ X2 )
      | ~ ( m1_pre_topc @ X0 @ X2 )
      | ~ ( l1_pre_topc @ X2 )
      | ~ ( v2_pre_topc @ X2 )
      | ( v2_struct_0 @ X2 )
      | ~ ( v1_funct_1 @ ( k4_tmap_1 @ X0 @ X0 ) )
      | ~ ( v1_funct_2 @ ( k4_tmap_1 @ X0 @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ( v1_funct_1 @ ( k3_tmap_1 @ X2 @ X0 @ X0 @ X1 @ ( k4_tmap_1 @ X0 @ X0 ) ) )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['130'])).

thf('132',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v1_funct_1 @ ( k3_tmap_1 @ X2 @ X0 @ X0 @ X1 @ ( k4_tmap_1 @ X0 @ X0 ) ) )
      | ~ ( v1_funct_1 @ ( k4_tmap_1 @ X0 @ X0 ) )
      | ( v2_struct_0 @ X2 )
      | ~ ( v2_pre_topc @ X2 )
      | ~ ( l1_pre_topc @ X2 )
      | ~ ( m1_pre_topc @ X0 @ X2 )
      | ~ ( m1_pre_topc @ X1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['127','131'])).

thf('133',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_pre_topc @ X1 @ X2 )
      | ~ ( m1_pre_topc @ X0 @ X2 )
      | ~ ( l1_pre_topc @ X2 )
      | ~ ( v2_pre_topc @ X2 )
      | ( v2_struct_0 @ X2 )
      | ~ ( v1_funct_1 @ ( k4_tmap_1 @ X0 @ X0 ) )
      | ( v1_funct_1 @ ( k3_tmap_1 @ X2 @ X0 @ X0 @ X1 @ ( k4_tmap_1 @ X0 @ X0 ) ) )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['132'])).

thf('134',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v1_funct_1 @ ( k3_tmap_1 @ X2 @ X0 @ X0 @ X1 @ ( k4_tmap_1 @ X0 @ X0 ) ) )
      | ( v2_struct_0 @ X2 )
      | ~ ( v2_pre_topc @ X2 )
      | ~ ( l1_pre_topc @ X2 )
      | ~ ( m1_pre_topc @ X0 @ X2 )
      | ~ ( m1_pre_topc @ X1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['126','133'])).

thf('135',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_pre_topc @ X1 @ X2 )
      | ~ ( m1_pre_topc @ X0 @ X2 )
      | ~ ( l1_pre_topc @ X2 )
      | ~ ( v2_pre_topc @ X2 )
      | ( v2_struct_0 @ X2 )
      | ( v1_funct_1 @ ( k3_tmap_1 @ X2 @ X0 @ X0 @ X1 @ ( k4_tmap_1 @ X0 @ X0 ) ) )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['134'])).

thf('136',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ X0 @ X0 @ sk_B @ ( k4_tmap_1 @ X0 @ X0 ) ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['125','135'])).

thf('137',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('138',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('139',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ X0 @ X0 @ sk_B @ ( k4_tmap_1 @ X0 @ X0 ) ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['136','137','138'])).

thf('140',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_A @ sk_A @ sk_B @ ( k4_tmap_1 @ sk_A @ sk_A ) ) )
    | ~ ( v2_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['124','139'])).

thf('141',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('142',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('143',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('144',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_A @ sk_A @ sk_B @ ( k4_tmap_1 @ sk_A @ sk_A ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['140','141','142','143'])).

thf('145',plain,
    ( ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_A @ sk_A @ sk_B @ ( k4_tmap_1 @ sk_A @ sk_A ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['144'])).

thf('146',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('147',plain,(
    v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_A @ sk_A @ sk_B @ ( k4_tmap_1 @ sk_A @ sk_A ) ) ),
    inference(clc,[status(thm)],['145','146'])).

thf('148',plain,
    ( ( k3_tmap_1 @ sk_A @ sk_A @ sk_A @ sk_B @ ( k4_tmap_1 @ sk_A @ sk_A ) )
    = ( k2_tmap_1 @ sk_A @ sk_A @ ( k4_tmap_1 @ sk_A @ sk_A ) @ sk_B ) ),
    inference(clc,[status(thm)],['118','119'])).

thf('149',plain,(
    v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_A @ ( k4_tmap_1 @ sk_A @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['147','148'])).

thf('150',plain,(
    ! [X39: $i] :
      ( ( m1_pre_topc @ X39 @ X39 )
      | ~ ( l1_pre_topc @ X39 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('151',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('152',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( v1_funct_1 @ ( k4_tmap_1 @ X0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('153',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( v1_funct_2 @ ( k4_tmap_1 @ X0 @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('154',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( m1_subset_1 @ ( k4_tmap_1 @ X0 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('155',plain,(
    ! [X30: $i,X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( m1_pre_topc @ X30 @ X31 )
      | ~ ( m1_pre_topc @ X32 @ X31 )
      | ~ ( l1_pre_topc @ X33 )
      | ~ ( v2_pre_topc @ X33 )
      | ( v2_struct_0 @ X33 )
      | ~ ( l1_pre_topc @ X31 )
      | ~ ( v2_pre_topc @ X31 )
      | ( v2_struct_0 @ X31 )
      | ~ ( v1_funct_1 @ X34 )
      | ~ ( v1_funct_2 @ X34 @ ( u1_struct_0 @ X32 ) @ ( u1_struct_0 @ X33 ) )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X32 ) @ ( u1_struct_0 @ X33 ) ) ) )
      | ( v1_funct_2 @ ( k3_tmap_1 @ X31 @ X33 @ X32 @ X30 @ X34 ) @ ( u1_struct_0 @ X30 ) @ ( u1_struct_0 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_tmap_1])).

thf('156',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v1_funct_2 @ ( k3_tmap_1 @ X2 @ X0 @ X0 @ X1 @ ( k4_tmap_1 @ X0 @ X0 ) ) @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v1_funct_2 @ ( k4_tmap_1 @ X0 @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k4_tmap_1 @ X0 @ X0 ) )
      | ( v2_struct_0 @ X2 )
      | ~ ( v2_pre_topc @ X2 )
      | ~ ( l1_pre_topc @ X2 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X2 )
      | ~ ( m1_pre_topc @ X1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['154','155'])).

thf('157',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_pre_topc @ X1 @ X2 )
      | ~ ( m1_pre_topc @ X0 @ X2 )
      | ~ ( l1_pre_topc @ X2 )
      | ~ ( v2_pre_topc @ X2 )
      | ( v2_struct_0 @ X2 )
      | ~ ( v1_funct_1 @ ( k4_tmap_1 @ X0 @ X0 ) )
      | ~ ( v1_funct_2 @ ( k4_tmap_1 @ X0 @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ( v1_funct_2 @ ( k3_tmap_1 @ X2 @ X0 @ X0 @ X1 @ ( k4_tmap_1 @ X0 @ X0 ) ) @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['156'])).

thf('158',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v1_funct_2 @ ( k3_tmap_1 @ X2 @ X0 @ X0 @ X1 @ ( k4_tmap_1 @ X0 @ X0 ) ) @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k4_tmap_1 @ X0 @ X0 ) )
      | ( v2_struct_0 @ X2 )
      | ~ ( v2_pre_topc @ X2 )
      | ~ ( l1_pre_topc @ X2 )
      | ~ ( m1_pre_topc @ X0 @ X2 )
      | ~ ( m1_pre_topc @ X1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['153','157'])).

thf('159',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_pre_topc @ X1 @ X2 )
      | ~ ( m1_pre_topc @ X0 @ X2 )
      | ~ ( l1_pre_topc @ X2 )
      | ~ ( v2_pre_topc @ X2 )
      | ( v2_struct_0 @ X2 )
      | ~ ( v1_funct_1 @ ( k4_tmap_1 @ X0 @ X0 ) )
      | ( v1_funct_2 @ ( k3_tmap_1 @ X2 @ X0 @ X0 @ X1 @ ( k4_tmap_1 @ X0 @ X0 ) ) @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['158'])).

thf('160',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v1_funct_2 @ ( k3_tmap_1 @ X2 @ X0 @ X0 @ X1 @ ( k4_tmap_1 @ X0 @ X0 ) ) @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ X0 ) )
      | ( v2_struct_0 @ X2 )
      | ~ ( v2_pre_topc @ X2 )
      | ~ ( l1_pre_topc @ X2 )
      | ~ ( m1_pre_topc @ X0 @ X2 )
      | ~ ( m1_pre_topc @ X1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['152','159'])).

thf('161',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_pre_topc @ X1 @ X2 )
      | ~ ( m1_pre_topc @ X0 @ X2 )
      | ~ ( l1_pre_topc @ X2 )
      | ~ ( v2_pre_topc @ X2 )
      | ( v2_struct_0 @ X2 )
      | ( v1_funct_2 @ ( k3_tmap_1 @ X2 @ X0 @ X0 @ X1 @ ( k4_tmap_1 @ X0 @ X0 ) ) @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['160'])).

thf('162',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ X0 @ X0 @ sk_B @ ( k4_tmap_1 @ X0 @ X0 ) ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X0 ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['151','161'])).

thf('163',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('164',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('165',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ X0 @ X0 @ sk_B @ ( k4_tmap_1 @ X0 @ X0 ) ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X0 ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['162','163','164'])).

thf('166',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_A @ sk_A @ sk_B @ ( k4_tmap_1 @ sk_A @ sk_A ) ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v2_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['150','165'])).

thf('167',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('168',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('169',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('170',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_A @ sk_A @ sk_B @ ( k4_tmap_1 @ sk_A @ sk_A ) ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['166','167','168','169'])).

thf('171',plain,
    ( ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_A @ sk_A @ sk_B @ ( k4_tmap_1 @ sk_A @ sk_A ) ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['170'])).

thf('172',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('173',plain,(
    v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_A @ sk_A @ sk_B @ ( k4_tmap_1 @ sk_A @ sk_A ) ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['171','172'])).

thf('174',plain,
    ( ( k3_tmap_1 @ sk_A @ sk_A @ sk_A @ sk_B @ ( k4_tmap_1 @ sk_A @ sk_A ) )
    = ( k2_tmap_1 @ sk_A @ sk_A @ ( k4_tmap_1 @ sk_A @ sk_A ) @ sk_B ) ),
    inference(clc,[status(thm)],['118','119'])).

thf('175',plain,(
    v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_A @ ( k4_tmap_1 @ sk_A @ sk_A ) @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['173','174'])).

thf('176',plain,(
    ! [X0: $i] :
      ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tmap_1 @ sk_A @ sk_A @ ( k4_tmap_1 @ sk_A @ sk_A ) @ sk_B ) @ X0 )
      | ( ( k2_tmap_1 @ sk_A @ sk_A @ ( k4_tmap_1 @ sk_A @ sk_A ) @ sk_B )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) )
      | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['123','149','175'])).

thf('177',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( k4_tmap_1 @ sk_A @ sk_A ) @ sk_B @ sk_A @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ~ ( v1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( v1_funct_2 @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( m1_subset_1 @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ( ( k2_tmap_1 @ sk_A @ sk_A @ ( k4_tmap_1 @ sk_A @ sk_A ) @ sk_B )
      = ( k4_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['54','176'])).

thf('178',plain,(
    v1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['33','34'])).

thf('179',plain,(
    v1_funct_2 @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['41','42'])).

thf('180',plain,(
    m1_subset_1 @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['14','15'])).

thf('181',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( k4_tmap_1 @ sk_A @ sk_A ) @ sk_B @ sk_A @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( ( k2_tmap_1 @ sk_A @ sk_A @ ( k4_tmap_1 @ sk_A @ sk_A ) @ sk_B )
      = ( k4_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['177','178','179','180'])).

thf('182',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( v1_funct_1 @ ( k4_tmap_1 @ X0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('183',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( v1_funct_2 @ ( k4_tmap_1 @ X0 @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('184',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('185',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_funct_1 @ ( k4_tmap_1 @ X0 @ X0 ) )
      | ~ ( v1_funct_2 @ ( k4_tmap_1 @ X0 @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ( r2_hidden @ ( sk_F @ X2 @ ( k4_tmap_1 @ X0 @ X0 ) @ X1 @ X0 @ X0 ) @ ( u1_struct_0 @ X1 ) )
      | ( r2_funct_2 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ X0 ) @ ( k2_tmap_1 @ X0 @ X0 @ ( k4_tmap_1 @ X0 @ X0 ) @ X1 ) @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( v1_funct_2 @ X2 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('186',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ~ ( m1_pre_topc @ sk_B @ sk_A )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tmap_1 @ sk_A @ sk_A @ ( k4_tmap_1 @ sk_A @ sk_A ) @ sk_B ) @ sk_C )
    | ( r2_hidden @ ( sk_F @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_A ) @ sk_B @ sk_A @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_2 @ ( k4_tmap_1 @ sk_A @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_A ) ) ),
    inference('sup-',[status(thm)],['184','185'])).

thf('187',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('188',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('189',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('190',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('191',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('192',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tmap_1 @ sk_A @ sk_A @ ( k4_tmap_1 @ sk_A @ sk_A ) @ sk_B ) @ sk_C )
    | ( r2_hidden @ ( sk_F @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_A ) @ sk_B @ sk_A @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_2 @ ( k4_tmap_1 @ sk_A @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['186','187','188','189','190','191'])).

thf('193',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( v1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_A ) )
    | ( r2_hidden @ ( sk_F @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_A ) @ sk_B @ sk_A @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tmap_1 @ sk_A @ sk_A @ ( k4_tmap_1 @ sk_A @ sk_A ) @ sk_B ) @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['183','192'])).

thf('194',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('195',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('196',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_A ) )
    | ( r2_hidden @ ( sk_F @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_A ) @ sk_B @ sk_A @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tmap_1 @ sk_A @ sk_A @ ( k4_tmap_1 @ sk_A @ sk_A ) @ sk_B ) @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['193','194','195'])).

thf('197',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tmap_1 @ sk_A @ sk_A @ ( k4_tmap_1 @ sk_A @ sk_A ) @ sk_B ) @ sk_C )
    | ( r2_hidden @ ( sk_F @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_A ) @ sk_B @ sk_A @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['196'])).

thf('198',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ ( sk_F @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_A ) @ sk_B @ sk_A @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tmap_1 @ sk_A @ sk_A @ ( k4_tmap_1 @ sk_A @ sk_A ) @ sk_B ) @ sk_C )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['182','197'])).

thf('199',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('200',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('201',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ ( sk_F @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_A ) @ sk_B @ sk_A @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tmap_1 @ sk_A @ sk_A @ ( k4_tmap_1 @ sk_A @ sk_A ) @ sk_B ) @ sk_C )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['198','199','200'])).

thf('202',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tmap_1 @ sk_A @ sk_A @ ( k4_tmap_1 @ sk_A @ sk_A ) @ sk_B ) @ sk_C )
    | ( r2_hidden @ ( sk_F @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_A ) @ sk_B @ sk_A @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['201'])).

thf('203',plain,(
    ! [X0: $i] :
      ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tmap_1 @ sk_A @ sk_A @ ( k4_tmap_1 @ sk_A @ sk_A ) @ sk_B ) @ X0 )
      | ( ( k2_tmap_1 @ sk_A @ sk_A @ ( k4_tmap_1 @ sk_A @ sk_A ) @ sk_B )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) )
      | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['123','149','175'])).

thf('204',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ ( sk_F @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_A ) @ sk_B @ sk_A @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ( ( k2_tmap_1 @ sk_A @ sk_A @ ( k4_tmap_1 @ sk_A @ sk_A ) @ sk_B )
      = sk_C ) ),
    inference('sup-',[status(thm)],['202','203'])).

thf('205',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('206',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('207',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('208',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ ( sk_F @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_A ) @ sk_B @ sk_A @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( ( k2_tmap_1 @ sk_A @ sk_A @ ( k4_tmap_1 @ sk_A @ sk_A ) @ sk_B )
      = sk_C ) ),
    inference(demod,[status(thm)],['204','205','206','207'])).

thf('209',plain,(
    m1_subset_1 @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['14','15'])).

thf('210',plain,(
    m1_subset_1 @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['14','15'])).

thf('211',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d9_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [D: $i] :
          ( ( ( v1_funct_1 @ D )
            & ( v1_funct_2 @ D @ A @ B )
            & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
         => ( ( r2_funct_2 @ A @ B @ C @ D )
          <=> ! [E: $i] :
                ( ( m1_subset_1 @ E @ A )
               => ( ( k1_funct_1 @ C @ E )
                  = ( k1_funct_1 @ D @ E ) ) ) ) ) ) )).

thf('212',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_funct_2 @ X5 @ X6 @ X7 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) ) )
      | ( m1_subset_1 @ ( sk_E @ X5 @ X8 @ X6 ) @ X6 )
      | ( r2_funct_2 @ X6 @ X7 @ X8 @ X5 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) ) )
      | ~ ( v1_funct_2 @ X8 @ X6 @ X7 )
      | ~ ( v1_funct_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_2])).

thf('213',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) )
      | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_C )
      | ( m1_subset_1 @ ( sk_E @ sk_C @ X0 @ ( u1_struct_0 @ sk_B ) ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['211','212'])).

thf('214',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('215',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('216',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) )
      | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_C )
      | ( m1_subset_1 @ ( sk_E @ sk_C @ X0 @ ( u1_struct_0 @ sk_B ) ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['213','214','215'])).

thf('217',plain,
    ( ( m1_subset_1 @ ( sk_E @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_B ) ) @ ( u1_struct_0 @ sk_B ) )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C )
    | ~ ( v1_funct_2 @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['210','216'])).

thf('218',plain,(
    v1_funct_2 @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['41','42'])).

thf('219',plain,(
    v1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['33','34'])).

thf('220',plain,
    ( ( m1_subset_1 @ ( sk_E @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_B ) ) @ ( u1_struct_0 @ sk_B ) )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C ) ),
    inference(demod,[status(thm)],['217','218','219'])).

thf('221',plain,(
    ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('222',plain,(
    m1_subset_1 @ ( sk_E @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_B ) ) @ ( u1_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['220','221'])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('223',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( v1_xboole_0 @ X1 )
      | ~ ( m1_subset_1 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('224',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( r2_hidden @ ( sk_E @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_B ) ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['222','223'])).

thf('225',plain,(
    ! [X55: $i] :
      ( ~ ( r2_hidden @ X55 @ ( u1_struct_0 @ sk_B ) )
      | ( X55
        = ( k1_funct_1 @ sk_C @ X55 ) )
      | ~ ( m1_subset_1 @ X55 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('226',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ~ ( m1_subset_1 @ ( sk_E @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_B ) ) @ ( u1_struct_0 @ sk_A ) )
    | ( ( sk_E @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_B ) )
      = ( k1_funct_1 @ sk_C @ ( sk_E @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['224','225'])).

thf('227',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('228',plain,(
    m1_subset_1 @ ( sk_E @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_B ) ) @ ( u1_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['220','221'])).

thf(t55_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( m1_pre_topc @ B @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ B ) )
             => ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('229',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( v2_struct_0 @ X18 )
      | ~ ( m1_pre_topc @ X18 @ X19 )
      | ( m1_subset_1 @ X20 @ ( u1_struct_0 @ X19 ) )
      | ~ ( m1_subset_1 @ X20 @ ( u1_struct_0 @ X18 ) )
      | ~ ( l1_pre_topc @ X19 )
      | ( v2_struct_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t55_pre_topc])).

thf('230',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_subset_1 @ ( sk_E @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_B ) ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['228','229'])).

thf('231',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( m1_subset_1 @ ( sk_E @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_B ) ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['227','230'])).

thf('232',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('233',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( m1_subset_1 @ ( sk_E @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_B ) ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['231','232'])).

thf('234',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('235',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( sk_E @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_B ) ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['233','234'])).

thf('236',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('237',plain,(
    m1_subset_1 @ ( sk_E @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_B ) ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['235','236'])).

thf('238',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( ( sk_E @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_B ) )
      = ( k1_funct_1 @ sk_C @ ( sk_E @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['226','237'])).

thf('239',plain,(
    m1_subset_1 @ ( sk_E @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_B ) ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['235','236'])).

thf('240',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( r2_hidden @ ( sk_E @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_B ) ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['222','223'])).

thf(t95_tmap_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( m1_pre_topc @ B @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ( ( r2_hidden @ C @ ( u1_struct_0 @ B ) )
               => ( ( k1_funct_1 @ ( k4_tmap_1 @ A @ B ) @ C )
                  = C ) ) ) ) ) )).

thf('241',plain,(
    ! [X52: $i,X53: $i,X54: $i] :
      ( ( v2_struct_0 @ X52 )
      | ~ ( m1_pre_topc @ X52 @ X53 )
      | ~ ( r2_hidden @ X54 @ ( u1_struct_0 @ X52 ) )
      | ( ( k1_funct_1 @ ( k4_tmap_1 @ X53 @ X52 ) @ X54 )
        = X54 )
      | ~ ( m1_subset_1 @ X54 @ ( u1_struct_0 @ X53 ) )
      | ~ ( l1_pre_topc @ X53 )
      | ~ ( v2_pre_topc @ X53 )
      | ( v2_struct_0 @ X53 ) ) ),
    inference(cnf,[status(esa)],[t95_tmap_1])).

thf('242',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_subset_1 @ ( sk_E @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_B ) ) @ ( u1_struct_0 @ X0 ) )
      | ( ( k1_funct_1 @ ( k4_tmap_1 @ X0 @ sk_B ) @ ( sk_E @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_B ) ) )
        = ( sk_E @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_B ) ) )
      | ~ ( m1_pre_topc @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['240','241'])).

thf('243',plain,
    ( ( v2_struct_0 @ sk_B )
    | ~ ( m1_pre_topc @ sk_B @ sk_A )
    | ( ( k1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( sk_E @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_B ) ) )
      = ( sk_E @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_B ) ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['239','242'])).

thf('244',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('245',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('246',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('247',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( sk_E @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_B ) ) )
      = ( sk_E @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_B ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['243','244','245','246'])).

thf('248',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_funct_2 @ X5 @ X6 @ X7 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) ) )
      | ( ( k1_funct_1 @ X8 @ ( sk_E @ X5 @ X8 @ X6 ) )
       != ( k1_funct_1 @ X5 @ ( sk_E @ X5 @ X8 @ X6 ) ) )
      | ( r2_funct_2 @ X6 @ X7 @ X8 @ X5 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) ) )
      | ~ ( v1_funct_2 @ X8 @ X6 @ X7 )
      | ~ ( v1_funct_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_2])).

thf('249',plain,(
    ! [X0: $i] :
      ( ( ( sk_E @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_B ) )
       != ( k1_funct_1 @ sk_C @ ( sk_E @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ~ ( v1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_B ) )
      | ~ ( v1_funct_2 @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ X0 )
      | ~ ( m1_subset_1 @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ X0 ) ) )
      | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ X0 @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C )
      | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ X0 ) ) )
      | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B ) @ X0 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['247','248'])).

thf('250',plain,(
    v1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['33','34'])).

thf('251',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('252',plain,(
    ! [X0: $i] :
      ( ( ( sk_E @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_B ) )
       != ( k1_funct_1 @ sk_C @ ( sk_E @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ~ ( v1_funct_2 @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ X0 )
      | ~ ( m1_subset_1 @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ X0 ) ) )
      | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ X0 @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C )
      | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ X0 ) ) )
      | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B ) @ X0 ) ) ),
    inference(demod,[status(thm)],['249','250','251'])).

thf('253',plain,(
    ! [X0: $i] :
      ( ( ( sk_E @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_B ) )
       != ( sk_E @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_B ) ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B ) @ X0 )
      | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ X0 ) ) )
      | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ X0 @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C )
      | ~ ( m1_subset_1 @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ X0 ) ) )
      | ~ ( v1_funct_2 @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['238','252'])).

thf('254',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ~ ( v1_funct_2 @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ X0 )
      | ~ ( m1_subset_1 @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ X0 ) ) )
      | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ X0 @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C )
      | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ X0 ) ) )
      | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B ) @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['253'])).

thf('255',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C )
    | ~ ( v1_funct_2 @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['209','254'])).

thf('256',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('257',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('258',plain,(
    v1_funct_2 @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['41','42'])).

thf('259',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['255','256','257','258'])).

thf('260',plain,(
    ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('261',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['259','260'])).

thf('262',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('263',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['261','262'])).

thf('264',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('265',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['263','264'])).

thf('266',plain,(
    ! [X39: $i] :
      ( ( m1_pre_topc @ X39 @ X39 )
      | ~ ( l1_pre_topc @ X39 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf(t1_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( m1_subset_1 @ ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('267',plain,(
    ! [X37: $i,X38: $i] :
      ( ~ ( m1_pre_topc @ X37 @ X38 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X37 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X38 ) ) )
      | ~ ( l1_pre_topc @ X38 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('268',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['266','267'])).

thf('269',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['268'])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('270',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( v1_xboole_0 @ X4 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('271',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['269','270'])).

thf('272',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_B ) )
      | ~ ( l1_pre_topc @ sk_B ) ) ),
    inference('sup-',[status(thm)],['265','271'])).

thf('273',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('274',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( m1_pre_topc @ X16 @ X17 )
      | ( l1_pre_topc @ X16 )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('275',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['273','274'])).

thf('276',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('277',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['275','276'])).

thf('278',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['272','277'])).

thf('279',plain,
    ( ( ( k2_tmap_1 @ sk_A @ sk_A @ ( k4_tmap_1 @ sk_A @ sk_A ) @ sk_B )
      = sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['208','278'])).

thf('280',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('281',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k2_tmap_1 @ sk_A @ sk_A @ ( k4_tmap_1 @ sk_A @ sk_A ) @ sk_B )
      = sk_C ) ),
    inference(clc,[status(thm)],['279','280'])).

thf('282',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('283',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_A @ ( k4_tmap_1 @ sk_A @ sk_A ) @ sk_B )
    = sk_C ),
    inference(clc,[status(thm)],['281','282'])).

thf('284',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( k4_tmap_1 @ sk_A @ sk_A ) @ sk_B @ sk_A @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( sk_C
      = ( k4_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['181','283'])).

thf('285',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['272','277'])).

thf('286',plain,
    ( ( sk_C
      = ( k4_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['284','285'])).

thf('287',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('288',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( sk_C
      = ( k4_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['286','287'])).

thf('289',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('290',plain,
    ( sk_C
    = ( k4_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['288','289'])).

thf('291',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('292',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_funct_2 @ X5 @ X6 @ X7 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) ) )
      | ( ( k1_funct_1 @ X8 @ ( sk_E @ X5 @ X8 @ X6 ) )
       != ( k1_funct_1 @ X5 @ ( sk_E @ X5 @ X8 @ X6 ) ) )
      | ( r2_funct_2 @ X6 @ X7 @ X8 @ X5 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) ) )
      | ~ ( v1_funct_2 @ X8 @ X6 @ X7 )
      | ~ ( v1_funct_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_2])).

thf('293',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X2 @ X1 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ( r2_funct_2 @ X2 @ X1 @ X0 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_2 @ X0 @ X2 @ X1 )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(eq_res,[status(thm)],['292'])).

thf('294',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_funct_2 @ X2 @ X1 @ X0 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_2 @ X0 @ X2 @ X1 )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['293'])).

thf('295',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ sk_C ) ),
    inference('sup-',[status(thm)],['291','294'])).

thf('296',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('297',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('298',plain,(
    r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ sk_C ),
    inference(demod,[status(thm)],['295','296','297'])).

thf('299',plain,(
    $false ),
    inference(demod,[status(thm)],['0','290','298'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.pdU1hUlflI
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:13:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.24/1.46  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.24/1.46  % Solved by: fo/fo7.sh
% 1.24/1.46  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.24/1.46  % done 1606 iterations in 1.027s
% 1.24/1.46  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.24/1.46  % SZS output start Refutation
% 1.24/1.46  thf(sk_F_type, type, sk_F: $i > $i > $i > $i > $i > $i).
% 1.24/1.46  thf(sk_C_type, type, sk_C: $i).
% 1.24/1.46  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.24/1.46  thf(r2_funct_2_type, type, r2_funct_2: $i > $i > $i > $i > $o).
% 1.24/1.46  thf(k2_tmap_1_type, type, k2_tmap_1: $i > $i > $i > $i > $i).
% 1.24/1.46  thf(k3_funct_2_type, type, k3_funct_2: $i > $i > $i > $i > $i).
% 1.24/1.46  thf(k2_partfun1_type, type, k2_partfun1: $i > $i > $i > $i > $i).
% 1.24/1.46  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.24/1.46  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.24/1.46  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 1.24/1.46  thf(k4_tmap_1_type, type, k4_tmap_1: $i > $i > $i).
% 1.24/1.46  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 1.24/1.46  thf(k3_tmap_1_type, type, k3_tmap_1: $i > $i > $i > $i > $i > $i).
% 1.24/1.46  thf(sk_E_type, type, sk_E: $i > $i > $i > $i).
% 1.24/1.46  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.24/1.46  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 1.24/1.46  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 1.24/1.46  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 1.24/1.46  thf(sk_A_type, type, sk_A: $i).
% 1.24/1.46  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 1.24/1.46  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.24/1.46  thf(sk_B_type, type, sk_B: $i).
% 1.24/1.46  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.24/1.46  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.24/1.46  thf(t96_tmap_1, conjecture,
% 1.24/1.46    (![A:$i]:
% 1.24/1.46     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.24/1.46       ( ![B:$i]:
% 1.24/1.46         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 1.24/1.46           ( ![C:$i]:
% 1.24/1.46             ( ( ( v1_funct_1 @ C ) & 
% 1.24/1.46                 ( v1_funct_2 @ C @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 1.24/1.46                 ( m1_subset_1 @
% 1.24/1.46                   C @ 
% 1.24/1.46                   ( k1_zfmisc_1 @
% 1.24/1.46                     ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 1.24/1.46               ( ( ![D:$i]:
% 1.24/1.46                   ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 1.24/1.46                     ( ( r2_hidden @ D @ ( u1_struct_0 @ B ) ) =>
% 1.24/1.46                       ( ( D ) = ( k1_funct_1 @ C @ D ) ) ) ) ) =>
% 1.24/1.46                 ( r2_funct_2 @
% 1.24/1.46                   ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 1.24/1.46                   ( k4_tmap_1 @ A @ B ) @ C ) ) ) ) ) ) ))).
% 1.24/1.46  thf(zf_stmt_0, negated_conjecture,
% 1.24/1.46    (~( ![A:$i]:
% 1.24/1.46        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 1.24/1.46            ( l1_pre_topc @ A ) ) =>
% 1.24/1.46          ( ![B:$i]:
% 1.24/1.46            ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 1.24/1.46              ( ![C:$i]:
% 1.24/1.46                ( ( ( v1_funct_1 @ C ) & 
% 1.24/1.46                    ( v1_funct_2 @
% 1.24/1.46                      C @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 1.24/1.46                    ( m1_subset_1 @
% 1.24/1.46                      C @ 
% 1.24/1.46                      ( k1_zfmisc_1 @
% 1.24/1.46                        ( k2_zfmisc_1 @
% 1.24/1.46                          ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 1.24/1.46                  ( ( ![D:$i]:
% 1.24/1.46                      ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 1.24/1.46                        ( ( r2_hidden @ D @ ( u1_struct_0 @ B ) ) =>
% 1.24/1.46                          ( ( D ) = ( k1_funct_1 @ C @ D ) ) ) ) ) =>
% 1.24/1.46                    ( r2_funct_2 @
% 1.24/1.46                      ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 1.24/1.46                      ( k4_tmap_1 @ A @ B ) @ C ) ) ) ) ) ) ) )),
% 1.24/1.46    inference('cnf.neg', [status(esa)], [t96_tmap_1])).
% 1.24/1.46  thf('0', plain,
% 1.24/1.46      (~ (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.24/1.46          (k4_tmap_1 @ sk_A @ sk_B) @ sk_C)),
% 1.24/1.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.24/1.46  thf(t2_tsep_1, axiom,
% 1.24/1.46    (![A:$i]: ( ( l1_pre_topc @ A ) => ( m1_pre_topc @ A @ A ) ))).
% 1.24/1.46  thf('1', plain,
% 1.24/1.46      (![X39 : $i]: ((m1_pre_topc @ X39 @ X39) | ~ (l1_pre_topc @ X39))),
% 1.24/1.46      inference('cnf', [status(esa)], [t2_tsep_1])).
% 1.24/1.46  thf(dt_k4_tmap_1, axiom,
% 1.24/1.46    (![A:$i,B:$i]:
% 1.24/1.46     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 1.24/1.46         ( l1_pre_topc @ A ) & ( m1_pre_topc @ B @ A ) ) =>
% 1.24/1.46       ( ( v1_funct_1 @ ( k4_tmap_1 @ A @ B ) ) & 
% 1.24/1.46         ( v1_funct_2 @
% 1.24/1.46           ( k4_tmap_1 @ A @ B ) @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 1.24/1.46         ( m1_subset_1 @
% 1.24/1.46           ( k4_tmap_1 @ A @ B ) @ 
% 1.24/1.46           ( k1_zfmisc_1 @
% 1.24/1.46             ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 1.24/1.46  thf('2', plain,
% 1.24/1.46      (![X35 : $i, X36 : $i]:
% 1.24/1.46         (~ (l1_pre_topc @ X35)
% 1.24/1.46          | ~ (v2_pre_topc @ X35)
% 1.24/1.46          | (v2_struct_0 @ X35)
% 1.24/1.46          | ~ (m1_pre_topc @ X36 @ X35)
% 1.24/1.46          | (v1_funct_1 @ (k4_tmap_1 @ X35 @ X36)))),
% 1.24/1.46      inference('cnf', [status(esa)], [dt_k4_tmap_1])).
% 1.24/1.46  thf('3', plain,
% 1.24/1.46      (![X0 : $i]:
% 1.24/1.46         (~ (l1_pre_topc @ X0)
% 1.24/1.46          | (v1_funct_1 @ (k4_tmap_1 @ X0 @ X0))
% 1.24/1.46          | (v2_struct_0 @ X0)
% 1.24/1.46          | ~ (v2_pre_topc @ X0)
% 1.24/1.46          | ~ (l1_pre_topc @ X0))),
% 1.24/1.46      inference('sup-', [status(thm)], ['1', '2'])).
% 1.24/1.46  thf('4', plain,
% 1.24/1.46      (![X0 : $i]:
% 1.24/1.46         (~ (v2_pre_topc @ X0)
% 1.24/1.46          | (v2_struct_0 @ X0)
% 1.24/1.46          | (v1_funct_1 @ (k4_tmap_1 @ X0 @ X0))
% 1.24/1.46          | ~ (l1_pre_topc @ X0))),
% 1.24/1.46      inference('simplify', [status(thm)], ['3'])).
% 1.24/1.46  thf('5', plain,
% 1.24/1.46      (![X39 : $i]: ((m1_pre_topc @ X39 @ X39) | ~ (l1_pre_topc @ X39))),
% 1.24/1.46      inference('cnf', [status(esa)], [t2_tsep_1])).
% 1.24/1.46  thf('6', plain,
% 1.24/1.46      (![X35 : $i, X36 : $i]:
% 1.24/1.46         (~ (l1_pre_topc @ X35)
% 1.24/1.46          | ~ (v2_pre_topc @ X35)
% 1.24/1.46          | (v2_struct_0 @ X35)
% 1.24/1.46          | ~ (m1_pre_topc @ X36 @ X35)
% 1.24/1.46          | (v1_funct_2 @ (k4_tmap_1 @ X35 @ X36) @ (u1_struct_0 @ X36) @ 
% 1.24/1.46             (u1_struct_0 @ X35)))),
% 1.24/1.46      inference('cnf', [status(esa)], [dt_k4_tmap_1])).
% 1.24/1.46  thf('7', plain,
% 1.24/1.46      (![X0 : $i]:
% 1.24/1.46         (~ (l1_pre_topc @ X0)
% 1.24/1.46          | (v1_funct_2 @ (k4_tmap_1 @ X0 @ X0) @ (u1_struct_0 @ X0) @ 
% 1.24/1.46             (u1_struct_0 @ X0))
% 1.24/1.46          | (v2_struct_0 @ X0)
% 1.24/1.46          | ~ (v2_pre_topc @ X0)
% 1.24/1.46          | ~ (l1_pre_topc @ X0))),
% 1.24/1.46      inference('sup-', [status(thm)], ['5', '6'])).
% 1.24/1.46  thf('8', plain,
% 1.24/1.46      (![X0 : $i]:
% 1.24/1.46         (~ (v2_pre_topc @ X0)
% 1.24/1.46          | (v2_struct_0 @ X0)
% 1.24/1.46          | (v1_funct_2 @ (k4_tmap_1 @ X0 @ X0) @ (u1_struct_0 @ X0) @ 
% 1.24/1.46             (u1_struct_0 @ X0))
% 1.24/1.46          | ~ (l1_pre_topc @ X0))),
% 1.24/1.46      inference('simplify', [status(thm)], ['7'])).
% 1.24/1.46  thf('9', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 1.24/1.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.24/1.46  thf('10', plain,
% 1.24/1.46      (![X35 : $i, X36 : $i]:
% 1.24/1.46         (~ (l1_pre_topc @ X35)
% 1.24/1.46          | ~ (v2_pre_topc @ X35)
% 1.24/1.46          | (v2_struct_0 @ X35)
% 1.24/1.46          | ~ (m1_pre_topc @ X36 @ X35)
% 1.24/1.46          | (m1_subset_1 @ (k4_tmap_1 @ X35 @ X36) @ 
% 1.24/1.46             (k1_zfmisc_1 @ 
% 1.24/1.46              (k2_zfmisc_1 @ (u1_struct_0 @ X36) @ (u1_struct_0 @ X35)))))),
% 1.24/1.46      inference('cnf', [status(esa)], [dt_k4_tmap_1])).
% 1.24/1.46  thf('11', plain,
% 1.24/1.46      (((m1_subset_1 @ (k4_tmap_1 @ sk_A @ sk_B) @ 
% 1.24/1.46         (k1_zfmisc_1 @ 
% 1.24/1.46          (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))
% 1.24/1.46        | (v2_struct_0 @ sk_A)
% 1.24/1.46        | ~ (v2_pre_topc @ sk_A)
% 1.24/1.46        | ~ (l1_pre_topc @ sk_A))),
% 1.24/1.46      inference('sup-', [status(thm)], ['9', '10'])).
% 1.24/1.46  thf('12', plain, ((v2_pre_topc @ sk_A)),
% 1.24/1.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.24/1.46  thf('13', plain, ((l1_pre_topc @ sk_A)),
% 1.24/1.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.24/1.46  thf('14', plain,
% 1.24/1.46      (((m1_subset_1 @ (k4_tmap_1 @ sk_A @ sk_B) @ 
% 1.24/1.46         (k1_zfmisc_1 @ 
% 1.24/1.46          (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))
% 1.24/1.46        | (v2_struct_0 @ sk_A))),
% 1.24/1.46      inference('demod', [status(thm)], ['11', '12', '13'])).
% 1.24/1.46  thf('15', plain, (~ (v2_struct_0 @ sk_A)),
% 1.24/1.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.24/1.46  thf('16', plain,
% 1.24/1.46      ((m1_subset_1 @ (k4_tmap_1 @ sk_A @ sk_B) @ 
% 1.24/1.46        (k1_zfmisc_1 @ 
% 1.24/1.46         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 1.24/1.46      inference('clc', [status(thm)], ['14', '15'])).
% 1.24/1.46  thf('17', plain,
% 1.24/1.46      (![X39 : $i]: ((m1_pre_topc @ X39 @ X39) | ~ (l1_pre_topc @ X39))),
% 1.24/1.46      inference('cnf', [status(esa)], [t2_tsep_1])).
% 1.24/1.46  thf('18', plain,
% 1.24/1.46      (![X35 : $i, X36 : $i]:
% 1.24/1.46         (~ (l1_pre_topc @ X35)
% 1.24/1.46          | ~ (v2_pre_topc @ X35)
% 1.24/1.46          | (v2_struct_0 @ X35)
% 1.24/1.46          | ~ (m1_pre_topc @ X36 @ X35)
% 1.24/1.46          | (m1_subset_1 @ (k4_tmap_1 @ X35 @ X36) @ 
% 1.24/1.46             (k1_zfmisc_1 @ 
% 1.24/1.46              (k2_zfmisc_1 @ (u1_struct_0 @ X36) @ (u1_struct_0 @ X35)))))),
% 1.24/1.46      inference('cnf', [status(esa)], [dt_k4_tmap_1])).
% 1.24/1.46  thf('19', plain,
% 1.24/1.46      (![X0 : $i]:
% 1.24/1.46         (~ (l1_pre_topc @ X0)
% 1.24/1.46          | (m1_subset_1 @ (k4_tmap_1 @ X0 @ X0) @ 
% 1.24/1.46             (k1_zfmisc_1 @ 
% 1.24/1.46              (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0))))
% 1.24/1.46          | (v2_struct_0 @ X0)
% 1.24/1.46          | ~ (v2_pre_topc @ X0)
% 1.24/1.46          | ~ (l1_pre_topc @ X0))),
% 1.24/1.46      inference('sup-', [status(thm)], ['17', '18'])).
% 1.24/1.46  thf('20', plain,
% 1.24/1.46      (![X0 : $i]:
% 1.24/1.46         (~ (v2_pre_topc @ X0)
% 1.24/1.46          | (v2_struct_0 @ X0)
% 1.24/1.46          | (m1_subset_1 @ (k4_tmap_1 @ X0 @ X0) @ 
% 1.24/1.46             (k1_zfmisc_1 @ 
% 1.24/1.46              (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0))))
% 1.24/1.46          | ~ (l1_pre_topc @ X0))),
% 1.24/1.46      inference('simplify', [status(thm)], ['19'])).
% 1.24/1.46  thf(t59_tmap_1, axiom,
% 1.24/1.46    (![A:$i]:
% 1.24/1.46     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.24/1.46       ( ![B:$i]:
% 1.24/1.46         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 1.24/1.46             ( l1_pre_topc @ B ) ) =>
% 1.24/1.46           ( ![C:$i]:
% 1.24/1.46             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ B ) ) =>
% 1.24/1.46               ( ![D:$i]:
% 1.24/1.46                 ( ( ( v1_funct_1 @ D ) & 
% 1.24/1.46                     ( v1_funct_2 @
% 1.24/1.46                       D @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 1.24/1.46                     ( m1_subset_1 @
% 1.24/1.46                       D @ 
% 1.24/1.46                       ( k1_zfmisc_1 @
% 1.24/1.46                         ( k2_zfmisc_1 @
% 1.24/1.46                           ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 1.24/1.46                   ( ![E:$i]:
% 1.24/1.46                     ( ( ( v1_funct_1 @ E ) & 
% 1.24/1.46                         ( v1_funct_2 @
% 1.24/1.46                           E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ A ) ) & 
% 1.24/1.46                         ( m1_subset_1 @
% 1.24/1.46                           E @ 
% 1.24/1.46                           ( k1_zfmisc_1 @
% 1.24/1.46                             ( k2_zfmisc_1 @
% 1.24/1.46                               ( u1_struct_0 @ C ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 1.24/1.46                       ( ( ![F:$i]:
% 1.24/1.46                           ( ( m1_subset_1 @ F @ ( u1_struct_0 @ B ) ) =>
% 1.24/1.46                             ( ( r2_hidden @ F @ ( u1_struct_0 @ C ) ) =>
% 1.24/1.46                               ( ( k3_funct_2 @
% 1.24/1.46                                   ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 1.24/1.46                                   D @ F ) =
% 1.24/1.46                                 ( k1_funct_1 @ E @ F ) ) ) ) ) =>
% 1.24/1.46                         ( r2_funct_2 @
% 1.24/1.46                           ( u1_struct_0 @ C ) @ ( u1_struct_0 @ A ) @ 
% 1.24/1.46                           ( k2_tmap_1 @ B @ A @ D @ C ) @ E ) ) ) ) ) ) ) ) ) ) ))).
% 1.24/1.46  thf('21', plain,
% 1.24/1.46      (![X40 : $i, X41 : $i, X42 : $i, X43 : $i, X44 : $i]:
% 1.24/1.46         ((v2_struct_0 @ X40)
% 1.24/1.46          | ~ (v2_pre_topc @ X40)
% 1.24/1.46          | ~ (l1_pre_topc @ X40)
% 1.24/1.46          | ~ (v1_funct_1 @ X41)
% 1.24/1.46          | ~ (v1_funct_2 @ X41 @ (u1_struct_0 @ X40) @ (u1_struct_0 @ X42))
% 1.24/1.46          | ~ (m1_subset_1 @ X41 @ 
% 1.24/1.46               (k1_zfmisc_1 @ 
% 1.24/1.46                (k2_zfmisc_1 @ (u1_struct_0 @ X40) @ (u1_struct_0 @ X42))))
% 1.24/1.46          | (r2_hidden @ (sk_F @ X43 @ X41 @ X44 @ X40 @ X42) @ 
% 1.24/1.46             (u1_struct_0 @ X44))
% 1.24/1.46          | (r2_funct_2 @ (u1_struct_0 @ X44) @ (u1_struct_0 @ X42) @ 
% 1.24/1.46             (k2_tmap_1 @ X40 @ X42 @ X41 @ X44) @ X43)
% 1.24/1.46          | ~ (m1_subset_1 @ X43 @ 
% 1.24/1.46               (k1_zfmisc_1 @ 
% 1.24/1.46                (k2_zfmisc_1 @ (u1_struct_0 @ X44) @ (u1_struct_0 @ X42))))
% 1.24/1.46          | ~ (v1_funct_2 @ X43 @ (u1_struct_0 @ X44) @ (u1_struct_0 @ X42))
% 1.24/1.46          | ~ (v1_funct_1 @ X43)
% 1.24/1.46          | ~ (m1_pre_topc @ X44 @ X40)
% 1.24/1.46          | (v2_struct_0 @ X44)
% 1.24/1.46          | ~ (l1_pre_topc @ X42)
% 1.24/1.46          | ~ (v2_pre_topc @ X42)
% 1.24/1.46          | (v2_struct_0 @ X42))),
% 1.24/1.46      inference('cnf', [status(esa)], [t59_tmap_1])).
% 1.24/1.46  thf('22', plain,
% 1.24/1.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.24/1.46         (~ (l1_pre_topc @ X0)
% 1.24/1.46          | (v2_struct_0 @ X0)
% 1.24/1.46          | ~ (v2_pre_topc @ X0)
% 1.24/1.46          | (v2_struct_0 @ X0)
% 1.24/1.46          | ~ (v2_pre_topc @ X0)
% 1.24/1.46          | ~ (l1_pre_topc @ X0)
% 1.24/1.46          | (v2_struct_0 @ X1)
% 1.24/1.46          | ~ (m1_pre_topc @ X1 @ X0)
% 1.24/1.46          | ~ (v1_funct_1 @ X2)
% 1.24/1.46          | ~ (v1_funct_2 @ X2 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ X0))
% 1.24/1.46          | ~ (m1_subset_1 @ X2 @ 
% 1.24/1.46               (k1_zfmisc_1 @ 
% 1.24/1.46                (k2_zfmisc_1 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ X0))))
% 1.24/1.46          | (r2_funct_2 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ X0) @ 
% 1.24/1.46             (k2_tmap_1 @ X0 @ X0 @ (k4_tmap_1 @ X0 @ X0) @ X1) @ X2)
% 1.24/1.46          | (r2_hidden @ (sk_F @ X2 @ (k4_tmap_1 @ X0 @ X0) @ X1 @ X0 @ X0) @ 
% 1.24/1.46             (u1_struct_0 @ X1))
% 1.24/1.46          | ~ (v1_funct_2 @ (k4_tmap_1 @ X0 @ X0) @ (u1_struct_0 @ X0) @ 
% 1.24/1.46               (u1_struct_0 @ X0))
% 1.24/1.46          | ~ (v1_funct_1 @ (k4_tmap_1 @ X0 @ X0))
% 1.24/1.46          | ~ (l1_pre_topc @ X0)
% 1.24/1.46          | ~ (v2_pre_topc @ X0)
% 1.24/1.46          | (v2_struct_0 @ X0))),
% 1.24/1.46      inference('sup-', [status(thm)], ['20', '21'])).
% 1.24/1.46  thf('23', plain,
% 1.24/1.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.24/1.46         (~ (v1_funct_1 @ (k4_tmap_1 @ X0 @ X0))
% 1.24/1.46          | ~ (v1_funct_2 @ (k4_tmap_1 @ X0 @ X0) @ (u1_struct_0 @ X0) @ 
% 1.24/1.46               (u1_struct_0 @ X0))
% 1.24/1.46          | (r2_hidden @ (sk_F @ X2 @ (k4_tmap_1 @ X0 @ X0) @ X1 @ X0 @ X0) @ 
% 1.24/1.46             (u1_struct_0 @ X1))
% 1.24/1.46          | (r2_funct_2 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ X0) @ 
% 1.24/1.46             (k2_tmap_1 @ X0 @ X0 @ (k4_tmap_1 @ X0 @ X0) @ X1) @ X2)
% 1.24/1.46          | ~ (m1_subset_1 @ X2 @ 
% 1.24/1.46               (k1_zfmisc_1 @ 
% 1.24/1.46                (k2_zfmisc_1 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ X0))))
% 1.24/1.46          | ~ (v1_funct_2 @ X2 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ X0))
% 1.24/1.46          | ~ (v1_funct_1 @ X2)
% 1.24/1.46          | ~ (m1_pre_topc @ X1 @ X0)
% 1.24/1.46          | (v2_struct_0 @ X1)
% 1.24/1.46          | ~ (v2_pre_topc @ X0)
% 1.24/1.46          | (v2_struct_0 @ X0)
% 1.24/1.46          | ~ (l1_pre_topc @ X0))),
% 1.24/1.46      inference('simplify', [status(thm)], ['22'])).
% 1.24/1.46  thf('24', plain,
% 1.24/1.46      ((~ (l1_pre_topc @ sk_A)
% 1.24/1.46        | (v2_struct_0 @ sk_A)
% 1.24/1.46        | ~ (v2_pre_topc @ sk_A)
% 1.24/1.46        | (v2_struct_0 @ sk_B)
% 1.24/1.46        | ~ (m1_pre_topc @ sk_B @ sk_A)
% 1.24/1.46        | ~ (v1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_B))
% 1.24/1.46        | ~ (v1_funct_2 @ (k4_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_B) @ 
% 1.24/1.46             (u1_struct_0 @ sk_A))
% 1.24/1.46        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.24/1.46           (k2_tmap_1 @ sk_A @ sk_A @ (k4_tmap_1 @ sk_A @ sk_A) @ sk_B) @ 
% 1.24/1.46           (k4_tmap_1 @ sk_A @ sk_B))
% 1.24/1.46        | (r2_hidden @ 
% 1.24/1.46           (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ (k4_tmap_1 @ sk_A @ sk_A) @ 
% 1.24/1.46            sk_B @ sk_A @ sk_A) @ 
% 1.24/1.46           (u1_struct_0 @ sk_B))
% 1.24/1.46        | ~ (v1_funct_2 @ (k4_tmap_1 @ sk_A @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 1.24/1.46             (u1_struct_0 @ sk_A))
% 1.24/1.46        | ~ (v1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_A)))),
% 1.24/1.46      inference('sup-', [status(thm)], ['16', '23'])).
% 1.24/1.46  thf('25', plain, ((l1_pre_topc @ sk_A)),
% 1.24/1.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.24/1.46  thf('26', plain, ((v2_pre_topc @ sk_A)),
% 1.24/1.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.24/1.46  thf('27', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 1.24/1.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.24/1.46  thf('28', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 1.24/1.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.24/1.46  thf('29', plain,
% 1.24/1.46      (![X35 : $i, X36 : $i]:
% 1.24/1.46         (~ (l1_pre_topc @ X35)
% 1.24/1.46          | ~ (v2_pre_topc @ X35)
% 1.24/1.46          | (v2_struct_0 @ X35)
% 1.24/1.46          | ~ (m1_pre_topc @ X36 @ X35)
% 1.24/1.46          | (v1_funct_1 @ (k4_tmap_1 @ X35 @ X36)))),
% 1.24/1.46      inference('cnf', [status(esa)], [dt_k4_tmap_1])).
% 1.24/1.46  thf('30', plain,
% 1.24/1.46      (((v1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_B))
% 1.24/1.46        | (v2_struct_0 @ sk_A)
% 1.24/1.46        | ~ (v2_pre_topc @ sk_A)
% 1.24/1.46        | ~ (l1_pre_topc @ sk_A))),
% 1.24/1.46      inference('sup-', [status(thm)], ['28', '29'])).
% 1.24/1.46  thf('31', plain, ((v2_pre_topc @ sk_A)),
% 1.24/1.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.24/1.46  thf('32', plain, ((l1_pre_topc @ sk_A)),
% 1.24/1.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.24/1.46  thf('33', plain,
% 1.24/1.46      (((v1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_B)) | (v2_struct_0 @ sk_A))),
% 1.24/1.46      inference('demod', [status(thm)], ['30', '31', '32'])).
% 1.24/1.46  thf('34', plain, (~ (v2_struct_0 @ sk_A)),
% 1.24/1.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.24/1.46  thf('35', plain, ((v1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_B))),
% 1.24/1.46      inference('clc', [status(thm)], ['33', '34'])).
% 1.24/1.46  thf('36', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 1.24/1.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.24/1.46  thf('37', plain,
% 1.24/1.46      (![X35 : $i, X36 : $i]:
% 1.24/1.46         (~ (l1_pre_topc @ X35)
% 1.24/1.46          | ~ (v2_pre_topc @ X35)
% 1.24/1.46          | (v2_struct_0 @ X35)
% 1.24/1.46          | ~ (m1_pre_topc @ X36 @ X35)
% 1.24/1.46          | (v1_funct_2 @ (k4_tmap_1 @ X35 @ X36) @ (u1_struct_0 @ X36) @ 
% 1.24/1.46             (u1_struct_0 @ X35)))),
% 1.24/1.46      inference('cnf', [status(esa)], [dt_k4_tmap_1])).
% 1.24/1.46  thf('38', plain,
% 1.24/1.46      (((v1_funct_2 @ (k4_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_B) @ 
% 1.24/1.46         (u1_struct_0 @ sk_A))
% 1.24/1.46        | (v2_struct_0 @ sk_A)
% 1.24/1.46        | ~ (v2_pre_topc @ sk_A)
% 1.24/1.46        | ~ (l1_pre_topc @ sk_A))),
% 1.24/1.46      inference('sup-', [status(thm)], ['36', '37'])).
% 1.24/1.46  thf('39', plain, ((v2_pre_topc @ sk_A)),
% 1.24/1.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.24/1.46  thf('40', plain, ((l1_pre_topc @ sk_A)),
% 1.24/1.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.24/1.46  thf('41', plain,
% 1.24/1.46      (((v1_funct_2 @ (k4_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_B) @ 
% 1.24/1.46         (u1_struct_0 @ sk_A))
% 1.24/1.46        | (v2_struct_0 @ sk_A))),
% 1.24/1.46      inference('demod', [status(thm)], ['38', '39', '40'])).
% 1.24/1.46  thf('42', plain, (~ (v2_struct_0 @ sk_A)),
% 1.24/1.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.24/1.46  thf('43', plain,
% 1.24/1.46      ((v1_funct_2 @ (k4_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_B) @ 
% 1.24/1.46        (u1_struct_0 @ sk_A))),
% 1.24/1.46      inference('clc', [status(thm)], ['41', '42'])).
% 1.24/1.46  thf('44', plain,
% 1.24/1.46      (((v2_struct_0 @ sk_A)
% 1.24/1.46        | (v2_struct_0 @ sk_B)
% 1.24/1.46        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.24/1.46           (k2_tmap_1 @ sk_A @ sk_A @ (k4_tmap_1 @ sk_A @ sk_A) @ sk_B) @ 
% 1.24/1.46           (k4_tmap_1 @ sk_A @ sk_B))
% 1.24/1.46        | (r2_hidden @ 
% 1.24/1.46           (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ (k4_tmap_1 @ sk_A @ sk_A) @ 
% 1.24/1.46            sk_B @ sk_A @ sk_A) @ 
% 1.24/1.46           (u1_struct_0 @ sk_B))
% 1.24/1.46        | ~ (v1_funct_2 @ (k4_tmap_1 @ sk_A @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 1.24/1.46             (u1_struct_0 @ sk_A))
% 1.24/1.46        | ~ (v1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_A)))),
% 1.24/1.46      inference('demod', [status(thm)], ['24', '25', '26', '27', '35', '43'])).
% 1.24/1.46  thf('45', plain,
% 1.24/1.46      ((~ (l1_pre_topc @ sk_A)
% 1.24/1.46        | (v2_struct_0 @ sk_A)
% 1.24/1.46        | ~ (v2_pre_topc @ sk_A)
% 1.24/1.46        | ~ (v1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_A))
% 1.24/1.46        | (r2_hidden @ 
% 1.24/1.46           (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ (k4_tmap_1 @ sk_A @ sk_A) @ 
% 1.24/1.46            sk_B @ sk_A @ sk_A) @ 
% 1.24/1.46           (u1_struct_0 @ sk_B))
% 1.24/1.46        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.24/1.46           (k2_tmap_1 @ sk_A @ sk_A @ (k4_tmap_1 @ sk_A @ sk_A) @ sk_B) @ 
% 1.24/1.46           (k4_tmap_1 @ sk_A @ sk_B))
% 1.24/1.46        | (v2_struct_0 @ sk_B)
% 1.24/1.46        | (v2_struct_0 @ sk_A))),
% 1.24/1.46      inference('sup-', [status(thm)], ['8', '44'])).
% 1.24/1.46  thf('46', plain, ((l1_pre_topc @ sk_A)),
% 1.24/1.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.24/1.46  thf('47', plain, ((v2_pre_topc @ sk_A)),
% 1.24/1.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.24/1.46  thf('48', plain,
% 1.24/1.46      (((v2_struct_0 @ sk_A)
% 1.24/1.46        | ~ (v1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_A))
% 1.24/1.46        | (r2_hidden @ 
% 1.24/1.46           (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ (k4_tmap_1 @ sk_A @ sk_A) @ 
% 1.24/1.46            sk_B @ sk_A @ sk_A) @ 
% 1.24/1.46           (u1_struct_0 @ sk_B))
% 1.24/1.46        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.24/1.46           (k2_tmap_1 @ sk_A @ sk_A @ (k4_tmap_1 @ sk_A @ sk_A) @ sk_B) @ 
% 1.24/1.46           (k4_tmap_1 @ sk_A @ sk_B))
% 1.24/1.46        | (v2_struct_0 @ sk_B)
% 1.24/1.46        | (v2_struct_0 @ sk_A))),
% 1.24/1.46      inference('demod', [status(thm)], ['45', '46', '47'])).
% 1.24/1.46  thf('49', plain,
% 1.24/1.46      (((v2_struct_0 @ sk_B)
% 1.24/1.46        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.24/1.46           (k2_tmap_1 @ sk_A @ sk_A @ (k4_tmap_1 @ sk_A @ sk_A) @ sk_B) @ 
% 1.24/1.46           (k4_tmap_1 @ sk_A @ sk_B))
% 1.24/1.46        | (r2_hidden @ 
% 1.24/1.46           (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ (k4_tmap_1 @ sk_A @ sk_A) @ 
% 1.24/1.46            sk_B @ sk_A @ sk_A) @ 
% 1.24/1.46           (u1_struct_0 @ sk_B))
% 1.24/1.46        | ~ (v1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_A))
% 1.24/1.46        | (v2_struct_0 @ sk_A))),
% 1.24/1.46      inference('simplify', [status(thm)], ['48'])).
% 1.24/1.46  thf('50', plain,
% 1.24/1.46      ((~ (l1_pre_topc @ sk_A)
% 1.24/1.46        | (v2_struct_0 @ sk_A)
% 1.24/1.46        | ~ (v2_pre_topc @ sk_A)
% 1.24/1.46        | (v2_struct_0 @ sk_A)
% 1.24/1.46        | (r2_hidden @ 
% 1.24/1.46           (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ (k4_tmap_1 @ sk_A @ sk_A) @ 
% 1.24/1.46            sk_B @ sk_A @ sk_A) @ 
% 1.24/1.46           (u1_struct_0 @ sk_B))
% 1.24/1.46        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.24/1.46           (k2_tmap_1 @ sk_A @ sk_A @ (k4_tmap_1 @ sk_A @ sk_A) @ sk_B) @ 
% 1.24/1.46           (k4_tmap_1 @ sk_A @ sk_B))
% 1.24/1.46        | (v2_struct_0 @ sk_B))),
% 1.24/1.46      inference('sup-', [status(thm)], ['4', '49'])).
% 1.24/1.46  thf('51', plain, ((l1_pre_topc @ sk_A)),
% 1.24/1.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.24/1.46  thf('52', plain, ((v2_pre_topc @ sk_A)),
% 1.24/1.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.24/1.46  thf('53', plain,
% 1.24/1.46      (((v2_struct_0 @ sk_A)
% 1.24/1.46        | (v2_struct_0 @ sk_A)
% 1.24/1.46        | (r2_hidden @ 
% 1.24/1.46           (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ (k4_tmap_1 @ sk_A @ sk_A) @ 
% 1.24/1.46            sk_B @ sk_A @ sk_A) @ 
% 1.24/1.46           (u1_struct_0 @ sk_B))
% 1.24/1.46        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.24/1.46           (k2_tmap_1 @ sk_A @ sk_A @ (k4_tmap_1 @ sk_A @ sk_A) @ sk_B) @ 
% 1.24/1.46           (k4_tmap_1 @ sk_A @ sk_B))
% 1.24/1.46        | (v2_struct_0 @ sk_B))),
% 1.24/1.46      inference('demod', [status(thm)], ['50', '51', '52'])).
% 1.24/1.46  thf('54', plain,
% 1.24/1.46      (((v2_struct_0 @ sk_B)
% 1.24/1.46        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.24/1.46           (k2_tmap_1 @ sk_A @ sk_A @ (k4_tmap_1 @ sk_A @ sk_A) @ sk_B) @ 
% 1.24/1.46           (k4_tmap_1 @ sk_A @ sk_B))
% 1.24/1.46        | (r2_hidden @ 
% 1.24/1.46           (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ (k4_tmap_1 @ sk_A @ sk_A) @ 
% 1.24/1.46            sk_B @ sk_A @ sk_A) @ 
% 1.24/1.46           (u1_struct_0 @ sk_B))
% 1.24/1.46        | (v2_struct_0 @ sk_A))),
% 1.24/1.46      inference('simplify', [status(thm)], ['53'])).
% 1.24/1.46  thf('55', plain,
% 1.24/1.46      (![X39 : $i]: ((m1_pre_topc @ X39 @ X39) | ~ (l1_pre_topc @ X39))),
% 1.24/1.46      inference('cnf', [status(esa)], [t2_tsep_1])).
% 1.24/1.46  thf('56', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 1.24/1.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.24/1.46  thf('57', plain,
% 1.24/1.46      (![X0 : $i]:
% 1.24/1.46         (~ (v2_pre_topc @ X0)
% 1.24/1.46          | (v2_struct_0 @ X0)
% 1.24/1.46          | (v1_funct_1 @ (k4_tmap_1 @ X0 @ X0))
% 1.24/1.46          | ~ (l1_pre_topc @ X0))),
% 1.24/1.46      inference('simplify', [status(thm)], ['3'])).
% 1.24/1.46  thf('58', plain,
% 1.24/1.46      (![X0 : $i]:
% 1.24/1.46         (~ (v2_pre_topc @ X0)
% 1.24/1.46          | (v2_struct_0 @ X0)
% 1.24/1.46          | (v1_funct_2 @ (k4_tmap_1 @ X0 @ X0) @ (u1_struct_0 @ X0) @ 
% 1.24/1.46             (u1_struct_0 @ X0))
% 1.24/1.46          | ~ (l1_pre_topc @ X0))),
% 1.24/1.46      inference('simplify', [status(thm)], ['7'])).
% 1.24/1.46  thf('59', plain,
% 1.24/1.46      (![X0 : $i]:
% 1.24/1.46         (~ (v2_pre_topc @ X0)
% 1.24/1.46          | (v2_struct_0 @ X0)
% 1.24/1.46          | (m1_subset_1 @ (k4_tmap_1 @ X0 @ X0) @ 
% 1.24/1.46             (k1_zfmisc_1 @ 
% 1.24/1.46              (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0))))
% 1.24/1.46          | ~ (l1_pre_topc @ X0))),
% 1.24/1.46      inference('simplify', [status(thm)], ['19'])).
% 1.24/1.46  thf(dt_k3_tmap_1, axiom,
% 1.24/1.46    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 1.24/1.46     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 1.24/1.46         ( l1_pre_topc @ A ) & ( ~( v2_struct_0 @ B ) ) & 
% 1.24/1.46         ( v2_pre_topc @ B ) & ( l1_pre_topc @ B ) & ( m1_pre_topc @ C @ A ) & 
% 1.24/1.46         ( m1_pre_topc @ D @ A ) & ( v1_funct_1 @ E ) & 
% 1.24/1.46         ( v1_funct_2 @ E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 1.24/1.46         ( m1_subset_1 @
% 1.24/1.46           E @ 
% 1.24/1.46           ( k1_zfmisc_1 @
% 1.24/1.46             ( k2_zfmisc_1 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 1.24/1.46       ( ( v1_funct_1 @ ( k3_tmap_1 @ A @ B @ C @ D @ E ) ) & 
% 1.24/1.46         ( v1_funct_2 @
% 1.24/1.46           ( k3_tmap_1 @ A @ B @ C @ D @ E ) @ ( u1_struct_0 @ D ) @ 
% 1.24/1.46           ( u1_struct_0 @ B ) ) & 
% 1.24/1.46         ( m1_subset_1 @
% 1.24/1.46           ( k3_tmap_1 @ A @ B @ C @ D @ E ) @ 
% 1.24/1.46           ( k1_zfmisc_1 @
% 1.24/1.46             ( k2_zfmisc_1 @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) ))).
% 1.29/1.46  thf('60', plain,
% 1.29/1.46      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 1.29/1.46         (~ (m1_pre_topc @ X30 @ X31)
% 1.29/1.46          | ~ (m1_pre_topc @ X32 @ X31)
% 1.29/1.46          | ~ (l1_pre_topc @ X33)
% 1.29/1.46          | ~ (v2_pre_topc @ X33)
% 1.29/1.46          | (v2_struct_0 @ X33)
% 1.29/1.46          | ~ (l1_pre_topc @ X31)
% 1.29/1.46          | ~ (v2_pre_topc @ X31)
% 1.29/1.46          | (v2_struct_0 @ X31)
% 1.29/1.46          | ~ (v1_funct_1 @ X34)
% 1.29/1.46          | ~ (v1_funct_2 @ X34 @ (u1_struct_0 @ X32) @ (u1_struct_0 @ X33))
% 1.29/1.46          | ~ (m1_subset_1 @ X34 @ 
% 1.29/1.46               (k1_zfmisc_1 @ 
% 1.29/1.46                (k2_zfmisc_1 @ (u1_struct_0 @ X32) @ (u1_struct_0 @ X33))))
% 1.29/1.46          | (m1_subset_1 @ (k3_tmap_1 @ X31 @ X33 @ X32 @ X30 @ X34) @ 
% 1.29/1.46             (k1_zfmisc_1 @ 
% 1.29/1.46              (k2_zfmisc_1 @ (u1_struct_0 @ X30) @ (u1_struct_0 @ X33)))))),
% 1.29/1.46      inference('cnf', [status(esa)], [dt_k3_tmap_1])).
% 1.29/1.46  thf('61', plain,
% 1.29/1.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.29/1.46         (~ (l1_pre_topc @ X0)
% 1.29/1.46          | (v2_struct_0 @ X0)
% 1.29/1.46          | ~ (v2_pre_topc @ X0)
% 1.29/1.46          | (m1_subset_1 @ 
% 1.29/1.46             (k3_tmap_1 @ X2 @ X0 @ X0 @ X1 @ (k4_tmap_1 @ X0 @ X0)) @ 
% 1.29/1.46             (k1_zfmisc_1 @ 
% 1.29/1.46              (k2_zfmisc_1 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ X0))))
% 1.29/1.46          | ~ (v1_funct_2 @ (k4_tmap_1 @ X0 @ X0) @ (u1_struct_0 @ X0) @ 
% 1.29/1.46               (u1_struct_0 @ X0))
% 1.29/1.46          | ~ (v1_funct_1 @ (k4_tmap_1 @ X0 @ X0))
% 1.29/1.46          | (v2_struct_0 @ X2)
% 1.29/1.46          | ~ (v2_pre_topc @ X2)
% 1.29/1.46          | ~ (l1_pre_topc @ X2)
% 1.29/1.46          | (v2_struct_0 @ X0)
% 1.29/1.46          | ~ (v2_pre_topc @ X0)
% 1.29/1.46          | ~ (l1_pre_topc @ X0)
% 1.29/1.46          | ~ (m1_pre_topc @ X0 @ X2)
% 1.29/1.46          | ~ (m1_pre_topc @ X1 @ X2))),
% 1.29/1.46      inference('sup-', [status(thm)], ['59', '60'])).
% 1.29/1.46  thf('62', plain,
% 1.29/1.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.29/1.46         (~ (m1_pre_topc @ X1 @ X2)
% 1.29/1.46          | ~ (m1_pre_topc @ X0 @ X2)
% 1.29/1.46          | ~ (l1_pre_topc @ X2)
% 1.29/1.46          | ~ (v2_pre_topc @ X2)
% 1.29/1.46          | (v2_struct_0 @ X2)
% 1.29/1.46          | ~ (v1_funct_1 @ (k4_tmap_1 @ X0 @ X0))
% 1.29/1.46          | ~ (v1_funct_2 @ (k4_tmap_1 @ X0 @ X0) @ (u1_struct_0 @ X0) @ 
% 1.29/1.46               (u1_struct_0 @ X0))
% 1.29/1.46          | (m1_subset_1 @ 
% 1.29/1.46             (k3_tmap_1 @ X2 @ X0 @ X0 @ X1 @ (k4_tmap_1 @ X0 @ X0)) @ 
% 1.29/1.46             (k1_zfmisc_1 @ 
% 1.29/1.46              (k2_zfmisc_1 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ X0))))
% 1.29/1.46          | ~ (v2_pre_topc @ X0)
% 1.29/1.46          | (v2_struct_0 @ X0)
% 1.29/1.46          | ~ (l1_pre_topc @ X0))),
% 1.29/1.46      inference('simplify', [status(thm)], ['61'])).
% 1.29/1.46  thf('63', plain,
% 1.29/1.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.29/1.46         (~ (l1_pre_topc @ X0)
% 1.29/1.46          | (v2_struct_0 @ X0)
% 1.29/1.46          | ~ (v2_pre_topc @ X0)
% 1.29/1.46          | ~ (l1_pre_topc @ X0)
% 1.29/1.46          | (v2_struct_0 @ X0)
% 1.29/1.46          | ~ (v2_pre_topc @ X0)
% 1.29/1.46          | (m1_subset_1 @ 
% 1.29/1.46             (k3_tmap_1 @ X2 @ X0 @ X0 @ X1 @ (k4_tmap_1 @ X0 @ X0)) @ 
% 1.29/1.46             (k1_zfmisc_1 @ 
% 1.29/1.46              (k2_zfmisc_1 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ X0))))
% 1.29/1.46          | ~ (v1_funct_1 @ (k4_tmap_1 @ X0 @ X0))
% 1.29/1.46          | (v2_struct_0 @ X2)
% 1.29/1.46          | ~ (v2_pre_topc @ X2)
% 1.29/1.46          | ~ (l1_pre_topc @ X2)
% 1.29/1.46          | ~ (m1_pre_topc @ X0 @ X2)
% 1.29/1.46          | ~ (m1_pre_topc @ X1 @ X2))),
% 1.29/1.46      inference('sup-', [status(thm)], ['58', '62'])).
% 1.29/1.46  thf('64', plain,
% 1.29/1.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.29/1.46         (~ (m1_pre_topc @ X1 @ X2)
% 1.29/1.46          | ~ (m1_pre_topc @ X0 @ X2)
% 1.29/1.46          | ~ (l1_pre_topc @ X2)
% 1.29/1.46          | ~ (v2_pre_topc @ X2)
% 1.29/1.46          | (v2_struct_0 @ X2)
% 1.29/1.46          | ~ (v1_funct_1 @ (k4_tmap_1 @ X0 @ X0))
% 1.29/1.46          | (m1_subset_1 @ 
% 1.29/1.46             (k3_tmap_1 @ X2 @ X0 @ X0 @ X1 @ (k4_tmap_1 @ X0 @ X0)) @ 
% 1.29/1.46             (k1_zfmisc_1 @ 
% 1.29/1.46              (k2_zfmisc_1 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ X0))))
% 1.29/1.46          | ~ (v2_pre_topc @ X0)
% 1.29/1.46          | (v2_struct_0 @ X0)
% 1.29/1.46          | ~ (l1_pre_topc @ X0))),
% 1.29/1.46      inference('simplify', [status(thm)], ['63'])).
% 1.29/1.46  thf('65', plain,
% 1.29/1.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.29/1.46         (~ (l1_pre_topc @ X0)
% 1.29/1.46          | (v2_struct_0 @ X0)
% 1.29/1.46          | ~ (v2_pre_topc @ X0)
% 1.29/1.46          | ~ (l1_pre_topc @ X0)
% 1.29/1.46          | (v2_struct_0 @ X0)
% 1.29/1.46          | ~ (v2_pre_topc @ X0)
% 1.29/1.46          | (m1_subset_1 @ 
% 1.29/1.46             (k3_tmap_1 @ X2 @ X0 @ X0 @ X1 @ (k4_tmap_1 @ X0 @ X0)) @ 
% 1.29/1.46             (k1_zfmisc_1 @ 
% 1.29/1.46              (k2_zfmisc_1 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ X0))))
% 1.29/1.46          | (v2_struct_0 @ X2)
% 1.29/1.46          | ~ (v2_pre_topc @ X2)
% 1.29/1.46          | ~ (l1_pre_topc @ X2)
% 1.29/1.46          | ~ (m1_pre_topc @ X0 @ X2)
% 1.29/1.46          | ~ (m1_pre_topc @ X1 @ X2))),
% 1.29/1.46      inference('sup-', [status(thm)], ['57', '64'])).
% 1.29/1.46  thf('66', plain,
% 1.29/1.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.29/1.46         (~ (m1_pre_topc @ X1 @ X2)
% 1.29/1.46          | ~ (m1_pre_topc @ X0 @ X2)
% 1.29/1.46          | ~ (l1_pre_topc @ X2)
% 1.29/1.46          | ~ (v2_pre_topc @ X2)
% 1.29/1.46          | (v2_struct_0 @ X2)
% 1.29/1.46          | (m1_subset_1 @ 
% 1.29/1.46             (k3_tmap_1 @ X2 @ X0 @ X0 @ X1 @ (k4_tmap_1 @ X0 @ X0)) @ 
% 1.29/1.46             (k1_zfmisc_1 @ 
% 1.29/1.46              (k2_zfmisc_1 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ X0))))
% 1.29/1.46          | ~ (v2_pre_topc @ X0)
% 1.29/1.46          | (v2_struct_0 @ X0)
% 1.29/1.46          | ~ (l1_pre_topc @ X0))),
% 1.29/1.46      inference('simplify', [status(thm)], ['65'])).
% 1.29/1.46  thf('67', plain,
% 1.29/1.46      (![X0 : $i]:
% 1.29/1.46         (~ (l1_pre_topc @ X0)
% 1.29/1.46          | (v2_struct_0 @ X0)
% 1.29/1.46          | ~ (v2_pre_topc @ X0)
% 1.29/1.46          | (m1_subset_1 @ 
% 1.29/1.46             (k3_tmap_1 @ sk_A @ X0 @ X0 @ sk_B @ (k4_tmap_1 @ X0 @ X0)) @ 
% 1.29/1.46             (k1_zfmisc_1 @ 
% 1.29/1.46              (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ X0))))
% 1.29/1.46          | (v2_struct_0 @ sk_A)
% 1.29/1.46          | ~ (v2_pre_topc @ sk_A)
% 1.29/1.46          | ~ (l1_pre_topc @ sk_A)
% 1.29/1.46          | ~ (m1_pre_topc @ X0 @ sk_A))),
% 1.29/1.46      inference('sup-', [status(thm)], ['56', '66'])).
% 1.29/1.46  thf('68', plain, ((v2_pre_topc @ sk_A)),
% 1.29/1.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.46  thf('69', plain, ((l1_pre_topc @ sk_A)),
% 1.29/1.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.46  thf('70', plain,
% 1.29/1.46      (![X0 : $i]:
% 1.29/1.46         (~ (l1_pre_topc @ X0)
% 1.29/1.46          | (v2_struct_0 @ X0)
% 1.29/1.46          | ~ (v2_pre_topc @ X0)
% 1.29/1.46          | (m1_subset_1 @ 
% 1.29/1.46             (k3_tmap_1 @ sk_A @ X0 @ X0 @ sk_B @ (k4_tmap_1 @ X0 @ X0)) @ 
% 1.29/1.46             (k1_zfmisc_1 @ 
% 1.29/1.46              (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ X0))))
% 1.29/1.46          | (v2_struct_0 @ sk_A)
% 1.29/1.46          | ~ (m1_pre_topc @ X0 @ sk_A))),
% 1.29/1.46      inference('demod', [status(thm)], ['67', '68', '69'])).
% 1.29/1.46  thf('71', plain,
% 1.29/1.46      ((~ (l1_pre_topc @ sk_A)
% 1.29/1.46        | (v2_struct_0 @ sk_A)
% 1.29/1.46        | (m1_subset_1 @ 
% 1.29/1.46           (k3_tmap_1 @ sk_A @ sk_A @ sk_A @ sk_B @ (k4_tmap_1 @ sk_A @ sk_A)) @ 
% 1.29/1.46           (k1_zfmisc_1 @ 
% 1.29/1.46            (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))
% 1.29/1.46        | ~ (v2_pre_topc @ sk_A)
% 1.29/1.46        | (v2_struct_0 @ sk_A)
% 1.29/1.46        | ~ (l1_pre_topc @ sk_A))),
% 1.29/1.46      inference('sup-', [status(thm)], ['55', '70'])).
% 1.29/1.46  thf('72', plain, ((l1_pre_topc @ sk_A)),
% 1.29/1.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.46  thf('73', plain, ((v2_pre_topc @ sk_A)),
% 1.29/1.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.46  thf('74', plain, ((l1_pre_topc @ sk_A)),
% 1.29/1.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.46  thf('75', plain,
% 1.29/1.46      (((v2_struct_0 @ sk_A)
% 1.29/1.46        | (m1_subset_1 @ 
% 1.29/1.46           (k3_tmap_1 @ sk_A @ sk_A @ sk_A @ sk_B @ (k4_tmap_1 @ sk_A @ sk_A)) @ 
% 1.29/1.46           (k1_zfmisc_1 @ 
% 1.29/1.46            (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))
% 1.29/1.46        | (v2_struct_0 @ sk_A))),
% 1.29/1.46      inference('demod', [status(thm)], ['71', '72', '73', '74'])).
% 1.29/1.46  thf('76', plain,
% 1.29/1.46      (((m1_subset_1 @ 
% 1.29/1.46         (k3_tmap_1 @ sk_A @ sk_A @ sk_A @ sk_B @ (k4_tmap_1 @ sk_A @ sk_A)) @ 
% 1.29/1.46         (k1_zfmisc_1 @ 
% 1.29/1.46          (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))
% 1.29/1.46        | (v2_struct_0 @ sk_A))),
% 1.29/1.46      inference('simplify', [status(thm)], ['75'])).
% 1.29/1.46  thf('77', plain, (~ (v2_struct_0 @ sk_A)),
% 1.29/1.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.46  thf('78', plain,
% 1.29/1.46      ((m1_subset_1 @ 
% 1.29/1.46        (k3_tmap_1 @ sk_A @ sk_A @ sk_A @ sk_B @ (k4_tmap_1 @ sk_A @ sk_A)) @ 
% 1.29/1.46        (k1_zfmisc_1 @ 
% 1.29/1.46         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 1.29/1.46      inference('clc', [status(thm)], ['76', '77'])).
% 1.29/1.46  thf('79', plain,
% 1.29/1.46      (![X39 : $i]: ((m1_pre_topc @ X39 @ X39) | ~ (l1_pre_topc @ X39))),
% 1.29/1.46      inference('cnf', [status(esa)], [t2_tsep_1])).
% 1.29/1.46  thf('80', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 1.29/1.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.46  thf('81', plain,
% 1.29/1.46      (![X0 : $i]:
% 1.29/1.46         (~ (v2_pre_topc @ X0)
% 1.29/1.46          | (v2_struct_0 @ X0)
% 1.29/1.46          | (v1_funct_1 @ (k4_tmap_1 @ X0 @ X0))
% 1.29/1.46          | ~ (l1_pre_topc @ X0))),
% 1.29/1.46      inference('simplify', [status(thm)], ['3'])).
% 1.29/1.46  thf('82', plain,
% 1.29/1.46      (![X0 : $i]:
% 1.29/1.46         (~ (v2_pre_topc @ X0)
% 1.29/1.46          | (v2_struct_0 @ X0)
% 1.29/1.46          | (v1_funct_2 @ (k4_tmap_1 @ X0 @ X0) @ (u1_struct_0 @ X0) @ 
% 1.29/1.46             (u1_struct_0 @ X0))
% 1.29/1.46          | ~ (l1_pre_topc @ X0))),
% 1.29/1.46      inference('simplify', [status(thm)], ['7'])).
% 1.29/1.46  thf('83', plain,
% 1.29/1.46      (![X0 : $i]:
% 1.29/1.46         (~ (v2_pre_topc @ X0)
% 1.29/1.46          | (v2_struct_0 @ X0)
% 1.29/1.46          | (m1_subset_1 @ (k4_tmap_1 @ X0 @ X0) @ 
% 1.29/1.46             (k1_zfmisc_1 @ 
% 1.29/1.46              (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0))))
% 1.29/1.46          | ~ (l1_pre_topc @ X0))),
% 1.29/1.46      inference('simplify', [status(thm)], ['19'])).
% 1.29/1.46  thf(d5_tmap_1, axiom,
% 1.29/1.46    (![A:$i]:
% 1.29/1.46     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.29/1.46       ( ![B:$i]:
% 1.29/1.46         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 1.29/1.46             ( l1_pre_topc @ B ) ) =>
% 1.29/1.46           ( ![C:$i]:
% 1.29/1.46             ( ( m1_pre_topc @ C @ A ) =>
% 1.29/1.46               ( ![D:$i]:
% 1.29/1.46                 ( ( m1_pre_topc @ D @ A ) =>
% 1.29/1.46                   ( ![E:$i]:
% 1.29/1.46                     ( ( ( v1_funct_1 @ E ) & 
% 1.29/1.46                         ( v1_funct_2 @
% 1.29/1.46                           E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 1.29/1.46                         ( m1_subset_1 @
% 1.29/1.46                           E @ 
% 1.29/1.46                           ( k1_zfmisc_1 @
% 1.29/1.46                             ( k2_zfmisc_1 @
% 1.29/1.46                               ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 1.29/1.46                       ( ( m1_pre_topc @ D @ C ) =>
% 1.29/1.46                         ( ( k3_tmap_1 @ A @ B @ C @ D @ E ) =
% 1.29/1.46                           ( k2_partfun1 @
% 1.29/1.46                             ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ E @ 
% 1.29/1.46                             ( u1_struct_0 @ D ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 1.29/1.46  thf('84', plain,
% 1.29/1.46      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 1.29/1.46         ((v2_struct_0 @ X25)
% 1.29/1.46          | ~ (v2_pre_topc @ X25)
% 1.29/1.46          | ~ (l1_pre_topc @ X25)
% 1.29/1.46          | ~ (m1_pre_topc @ X26 @ X27)
% 1.29/1.46          | ~ (m1_pre_topc @ X26 @ X28)
% 1.29/1.46          | ((k3_tmap_1 @ X27 @ X25 @ X28 @ X26 @ X29)
% 1.29/1.46              = (k2_partfun1 @ (u1_struct_0 @ X28) @ (u1_struct_0 @ X25) @ 
% 1.29/1.46                 X29 @ (u1_struct_0 @ X26)))
% 1.29/1.46          | ~ (m1_subset_1 @ X29 @ 
% 1.29/1.46               (k1_zfmisc_1 @ 
% 1.29/1.46                (k2_zfmisc_1 @ (u1_struct_0 @ X28) @ (u1_struct_0 @ X25))))
% 1.29/1.46          | ~ (v1_funct_2 @ X29 @ (u1_struct_0 @ X28) @ (u1_struct_0 @ X25))
% 1.29/1.46          | ~ (v1_funct_1 @ X29)
% 1.29/1.46          | ~ (m1_pre_topc @ X28 @ X27)
% 1.29/1.46          | ~ (l1_pre_topc @ X27)
% 1.29/1.46          | ~ (v2_pre_topc @ X27)
% 1.29/1.46          | (v2_struct_0 @ X27))),
% 1.29/1.46      inference('cnf', [status(esa)], [d5_tmap_1])).
% 1.29/1.46  thf('85', plain,
% 1.29/1.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.29/1.46         (~ (l1_pre_topc @ X0)
% 1.29/1.46          | (v2_struct_0 @ X0)
% 1.29/1.46          | ~ (v2_pre_topc @ X0)
% 1.29/1.46          | (v2_struct_0 @ X1)
% 1.29/1.46          | ~ (v2_pre_topc @ X1)
% 1.29/1.46          | ~ (l1_pre_topc @ X1)
% 1.29/1.46          | ~ (m1_pre_topc @ X0 @ X1)
% 1.29/1.46          | ~ (v1_funct_1 @ (k4_tmap_1 @ X0 @ X0))
% 1.29/1.46          | ~ (v1_funct_2 @ (k4_tmap_1 @ X0 @ X0) @ (u1_struct_0 @ X0) @ 
% 1.29/1.46               (u1_struct_0 @ X0))
% 1.29/1.46          | ((k3_tmap_1 @ X1 @ X0 @ X0 @ X2 @ (k4_tmap_1 @ X0 @ X0))
% 1.29/1.46              = (k2_partfun1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0) @ 
% 1.29/1.46                 (k4_tmap_1 @ X0 @ X0) @ (u1_struct_0 @ X2)))
% 1.29/1.46          | ~ (m1_pre_topc @ X2 @ X0)
% 1.29/1.46          | ~ (m1_pre_topc @ X2 @ X1)
% 1.29/1.46          | ~ (l1_pre_topc @ X0)
% 1.29/1.46          | ~ (v2_pre_topc @ X0)
% 1.29/1.46          | (v2_struct_0 @ X0))),
% 1.29/1.46      inference('sup-', [status(thm)], ['83', '84'])).
% 1.29/1.46  thf('86', plain,
% 1.29/1.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.29/1.46         (~ (m1_pre_topc @ X2 @ X1)
% 1.29/1.46          | ~ (m1_pre_topc @ X2 @ X0)
% 1.29/1.46          | ((k3_tmap_1 @ X1 @ X0 @ X0 @ X2 @ (k4_tmap_1 @ X0 @ X0))
% 1.29/1.46              = (k2_partfun1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0) @ 
% 1.29/1.46                 (k4_tmap_1 @ X0 @ X0) @ (u1_struct_0 @ X2)))
% 1.29/1.46          | ~ (v1_funct_2 @ (k4_tmap_1 @ X0 @ X0) @ (u1_struct_0 @ X0) @ 
% 1.29/1.46               (u1_struct_0 @ X0))
% 1.29/1.46          | ~ (v1_funct_1 @ (k4_tmap_1 @ X0 @ X0))
% 1.29/1.46          | ~ (m1_pre_topc @ X0 @ X1)
% 1.29/1.46          | ~ (l1_pre_topc @ X1)
% 1.29/1.46          | ~ (v2_pre_topc @ X1)
% 1.29/1.46          | (v2_struct_0 @ X1)
% 1.29/1.46          | ~ (v2_pre_topc @ X0)
% 1.29/1.46          | (v2_struct_0 @ X0)
% 1.29/1.46          | ~ (l1_pre_topc @ X0))),
% 1.29/1.46      inference('simplify', [status(thm)], ['85'])).
% 1.29/1.46  thf('87', plain,
% 1.29/1.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.29/1.46         (~ (l1_pre_topc @ X0)
% 1.29/1.46          | (v2_struct_0 @ X0)
% 1.29/1.46          | ~ (v2_pre_topc @ X0)
% 1.29/1.46          | ~ (l1_pre_topc @ X0)
% 1.29/1.46          | (v2_struct_0 @ X0)
% 1.29/1.46          | ~ (v2_pre_topc @ X0)
% 1.29/1.46          | (v2_struct_0 @ X1)
% 1.29/1.46          | ~ (v2_pre_topc @ X1)
% 1.29/1.46          | ~ (l1_pre_topc @ X1)
% 1.29/1.46          | ~ (m1_pre_topc @ X0 @ X1)
% 1.29/1.46          | ~ (v1_funct_1 @ (k4_tmap_1 @ X0 @ X0))
% 1.29/1.46          | ((k3_tmap_1 @ X1 @ X0 @ X0 @ X2 @ (k4_tmap_1 @ X0 @ X0))
% 1.29/1.46              = (k2_partfun1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0) @ 
% 1.29/1.46                 (k4_tmap_1 @ X0 @ X0) @ (u1_struct_0 @ X2)))
% 1.29/1.46          | ~ (m1_pre_topc @ X2 @ X0)
% 1.29/1.46          | ~ (m1_pre_topc @ X2 @ X1))),
% 1.29/1.46      inference('sup-', [status(thm)], ['82', '86'])).
% 1.29/1.46  thf('88', plain,
% 1.29/1.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.29/1.46         (~ (m1_pre_topc @ X2 @ X1)
% 1.29/1.46          | ~ (m1_pre_topc @ X2 @ X0)
% 1.29/1.46          | ((k3_tmap_1 @ X1 @ X0 @ X0 @ X2 @ (k4_tmap_1 @ X0 @ X0))
% 1.29/1.46              = (k2_partfun1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0) @ 
% 1.29/1.46                 (k4_tmap_1 @ X0 @ X0) @ (u1_struct_0 @ X2)))
% 1.29/1.46          | ~ (v1_funct_1 @ (k4_tmap_1 @ X0 @ X0))
% 1.29/1.46          | ~ (m1_pre_topc @ X0 @ X1)
% 1.29/1.46          | ~ (l1_pre_topc @ X1)
% 1.29/1.46          | ~ (v2_pre_topc @ X1)
% 1.29/1.46          | (v2_struct_0 @ X1)
% 1.29/1.46          | ~ (v2_pre_topc @ X0)
% 1.29/1.46          | (v2_struct_0 @ X0)
% 1.29/1.46          | ~ (l1_pre_topc @ X0))),
% 1.29/1.46      inference('simplify', [status(thm)], ['87'])).
% 1.29/1.46  thf('89', plain,
% 1.29/1.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.29/1.46         (~ (l1_pre_topc @ X0)
% 1.29/1.46          | (v2_struct_0 @ X0)
% 1.29/1.46          | ~ (v2_pre_topc @ X0)
% 1.29/1.46          | ~ (l1_pre_topc @ X0)
% 1.29/1.46          | (v2_struct_0 @ X0)
% 1.29/1.46          | ~ (v2_pre_topc @ X0)
% 1.29/1.46          | (v2_struct_0 @ X1)
% 1.29/1.46          | ~ (v2_pre_topc @ X1)
% 1.29/1.46          | ~ (l1_pre_topc @ X1)
% 1.29/1.46          | ~ (m1_pre_topc @ X0 @ X1)
% 1.29/1.46          | ((k3_tmap_1 @ X1 @ X0 @ X0 @ X2 @ (k4_tmap_1 @ X0 @ X0))
% 1.29/1.46              = (k2_partfun1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0) @ 
% 1.29/1.46                 (k4_tmap_1 @ X0 @ X0) @ (u1_struct_0 @ X2)))
% 1.29/1.46          | ~ (m1_pre_topc @ X2 @ X0)
% 1.29/1.46          | ~ (m1_pre_topc @ X2 @ X1))),
% 1.29/1.46      inference('sup-', [status(thm)], ['81', '88'])).
% 1.29/1.46  thf('90', plain,
% 1.29/1.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.29/1.46         (~ (m1_pre_topc @ X2 @ X1)
% 1.29/1.46          | ~ (m1_pre_topc @ X2 @ X0)
% 1.29/1.46          | ((k3_tmap_1 @ X1 @ X0 @ X0 @ X2 @ (k4_tmap_1 @ X0 @ X0))
% 1.29/1.46              = (k2_partfun1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0) @ 
% 1.29/1.46                 (k4_tmap_1 @ X0 @ X0) @ (u1_struct_0 @ X2)))
% 1.29/1.46          | ~ (m1_pre_topc @ X0 @ X1)
% 1.29/1.46          | ~ (l1_pre_topc @ X1)
% 1.29/1.46          | ~ (v2_pre_topc @ X1)
% 1.29/1.46          | (v2_struct_0 @ X1)
% 1.29/1.46          | ~ (v2_pre_topc @ X0)
% 1.29/1.46          | (v2_struct_0 @ X0)
% 1.29/1.46          | ~ (l1_pre_topc @ X0))),
% 1.29/1.46      inference('simplify', [status(thm)], ['89'])).
% 1.29/1.46  thf('91', plain,
% 1.29/1.46      (![X0 : $i]:
% 1.29/1.46         (~ (l1_pre_topc @ X0)
% 1.29/1.46          | (v2_struct_0 @ X0)
% 1.29/1.46          | ~ (v2_pre_topc @ X0)
% 1.29/1.46          | (v2_struct_0 @ sk_A)
% 1.29/1.46          | ~ (v2_pre_topc @ sk_A)
% 1.29/1.46          | ~ (l1_pre_topc @ sk_A)
% 1.29/1.46          | ~ (m1_pre_topc @ X0 @ sk_A)
% 1.29/1.46          | ((k3_tmap_1 @ sk_A @ X0 @ X0 @ sk_B @ (k4_tmap_1 @ X0 @ X0))
% 1.29/1.46              = (k2_partfun1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0) @ 
% 1.29/1.46                 (k4_tmap_1 @ X0 @ X0) @ (u1_struct_0 @ sk_B)))
% 1.29/1.46          | ~ (m1_pre_topc @ sk_B @ X0))),
% 1.29/1.46      inference('sup-', [status(thm)], ['80', '90'])).
% 1.29/1.46  thf('92', plain, ((v2_pre_topc @ sk_A)),
% 1.29/1.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.46  thf('93', plain, ((l1_pre_topc @ sk_A)),
% 1.29/1.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.46  thf('94', plain,
% 1.29/1.46      (![X0 : $i]:
% 1.29/1.46         (~ (l1_pre_topc @ X0)
% 1.29/1.46          | (v2_struct_0 @ X0)
% 1.29/1.46          | ~ (v2_pre_topc @ X0)
% 1.29/1.46          | (v2_struct_0 @ sk_A)
% 1.29/1.46          | ~ (m1_pre_topc @ X0 @ sk_A)
% 1.29/1.46          | ((k3_tmap_1 @ sk_A @ X0 @ X0 @ sk_B @ (k4_tmap_1 @ X0 @ X0))
% 1.29/1.46              = (k2_partfun1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0) @ 
% 1.29/1.46                 (k4_tmap_1 @ X0 @ X0) @ (u1_struct_0 @ sk_B)))
% 1.29/1.46          | ~ (m1_pre_topc @ sk_B @ X0))),
% 1.29/1.46      inference('demod', [status(thm)], ['91', '92', '93'])).
% 1.29/1.46  thf('95', plain,
% 1.29/1.46      ((~ (l1_pre_topc @ sk_A)
% 1.29/1.46        | ~ (m1_pre_topc @ sk_B @ sk_A)
% 1.29/1.46        | ((k3_tmap_1 @ sk_A @ sk_A @ sk_A @ sk_B @ (k4_tmap_1 @ sk_A @ sk_A))
% 1.29/1.46            = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 1.29/1.46               (k4_tmap_1 @ sk_A @ sk_A) @ (u1_struct_0 @ sk_B)))
% 1.29/1.46        | (v2_struct_0 @ sk_A)
% 1.29/1.46        | ~ (v2_pre_topc @ sk_A)
% 1.29/1.46        | (v2_struct_0 @ sk_A)
% 1.29/1.46        | ~ (l1_pre_topc @ sk_A))),
% 1.29/1.46      inference('sup-', [status(thm)], ['79', '94'])).
% 1.29/1.46  thf('96', plain, ((l1_pre_topc @ sk_A)),
% 1.29/1.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.46  thf('97', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 1.29/1.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.46  thf('98', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 1.29/1.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.46  thf('99', plain,
% 1.29/1.46      (![X0 : $i]:
% 1.29/1.46         (~ (v2_pre_topc @ X0)
% 1.29/1.46          | (v2_struct_0 @ X0)
% 1.29/1.46          | (v1_funct_1 @ (k4_tmap_1 @ X0 @ X0))
% 1.29/1.46          | ~ (l1_pre_topc @ X0))),
% 1.29/1.46      inference('simplify', [status(thm)], ['3'])).
% 1.29/1.46  thf('100', plain,
% 1.29/1.46      (![X0 : $i]:
% 1.29/1.46         (~ (v2_pre_topc @ X0)
% 1.29/1.46          | (v2_struct_0 @ X0)
% 1.29/1.46          | (v1_funct_2 @ (k4_tmap_1 @ X0 @ X0) @ (u1_struct_0 @ X0) @ 
% 1.29/1.46             (u1_struct_0 @ X0))
% 1.29/1.46          | ~ (l1_pre_topc @ X0))),
% 1.29/1.46      inference('simplify', [status(thm)], ['7'])).
% 1.29/1.46  thf('101', plain,
% 1.29/1.46      (![X0 : $i]:
% 1.29/1.46         (~ (v2_pre_topc @ X0)
% 1.29/1.46          | (v2_struct_0 @ X0)
% 1.29/1.46          | (m1_subset_1 @ (k4_tmap_1 @ X0 @ X0) @ 
% 1.29/1.46             (k1_zfmisc_1 @ 
% 1.29/1.46              (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0))))
% 1.29/1.46          | ~ (l1_pre_topc @ X0))),
% 1.29/1.46      inference('simplify', [status(thm)], ['19'])).
% 1.29/1.46  thf(d4_tmap_1, axiom,
% 1.29/1.46    (![A:$i]:
% 1.29/1.46     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.29/1.46       ( ![B:$i]:
% 1.29/1.46         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 1.29/1.46             ( l1_pre_topc @ B ) ) =>
% 1.29/1.46           ( ![C:$i]:
% 1.29/1.46             ( ( ( v1_funct_1 @ C ) & 
% 1.29/1.46                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 1.29/1.46                 ( m1_subset_1 @
% 1.29/1.46                   C @ 
% 1.29/1.46                   ( k1_zfmisc_1 @
% 1.29/1.46                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 1.29/1.46               ( ![D:$i]:
% 1.29/1.46                 ( ( m1_pre_topc @ D @ A ) =>
% 1.29/1.46                   ( ( k2_tmap_1 @ A @ B @ C @ D ) =
% 1.29/1.46                     ( k2_partfun1 @
% 1.29/1.46                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ 
% 1.29/1.46                       ( u1_struct_0 @ D ) ) ) ) ) ) ) ) ) ))).
% 1.29/1.46  thf('102', plain,
% 1.29/1.46      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 1.29/1.46         ((v2_struct_0 @ X21)
% 1.29/1.46          | ~ (v2_pre_topc @ X21)
% 1.29/1.46          | ~ (l1_pre_topc @ X21)
% 1.29/1.46          | ~ (m1_pre_topc @ X22 @ X23)
% 1.29/1.46          | ((k2_tmap_1 @ X23 @ X21 @ X24 @ X22)
% 1.29/1.46              = (k2_partfun1 @ (u1_struct_0 @ X23) @ (u1_struct_0 @ X21) @ 
% 1.29/1.46                 X24 @ (u1_struct_0 @ X22)))
% 1.29/1.46          | ~ (m1_subset_1 @ X24 @ 
% 1.29/1.46               (k1_zfmisc_1 @ 
% 1.29/1.46                (k2_zfmisc_1 @ (u1_struct_0 @ X23) @ (u1_struct_0 @ X21))))
% 1.29/1.46          | ~ (v1_funct_2 @ X24 @ (u1_struct_0 @ X23) @ (u1_struct_0 @ X21))
% 1.29/1.46          | ~ (v1_funct_1 @ X24)
% 1.29/1.46          | ~ (l1_pre_topc @ X23)
% 1.29/1.46          | ~ (v2_pre_topc @ X23)
% 1.29/1.46          | (v2_struct_0 @ X23))),
% 1.29/1.46      inference('cnf', [status(esa)], [d4_tmap_1])).
% 1.29/1.46  thf('103', plain,
% 1.29/1.46      (![X0 : $i, X1 : $i]:
% 1.29/1.46         (~ (l1_pre_topc @ X0)
% 1.29/1.46          | (v2_struct_0 @ X0)
% 1.29/1.46          | ~ (v2_pre_topc @ X0)
% 1.29/1.46          | (v2_struct_0 @ X0)
% 1.29/1.46          | ~ (v2_pre_topc @ X0)
% 1.29/1.46          | ~ (l1_pre_topc @ X0)
% 1.29/1.46          | ~ (v1_funct_1 @ (k4_tmap_1 @ X0 @ X0))
% 1.29/1.46          | ~ (v1_funct_2 @ (k4_tmap_1 @ X0 @ X0) @ (u1_struct_0 @ X0) @ 
% 1.29/1.46               (u1_struct_0 @ X0))
% 1.29/1.46          | ((k2_tmap_1 @ X0 @ X0 @ (k4_tmap_1 @ X0 @ X0) @ X1)
% 1.29/1.46              = (k2_partfun1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0) @ 
% 1.29/1.46                 (k4_tmap_1 @ X0 @ X0) @ (u1_struct_0 @ X1)))
% 1.29/1.46          | ~ (m1_pre_topc @ X1 @ X0)
% 1.29/1.46          | ~ (l1_pre_topc @ X0)
% 1.29/1.46          | ~ (v2_pre_topc @ X0)
% 1.29/1.46          | (v2_struct_0 @ X0))),
% 1.29/1.46      inference('sup-', [status(thm)], ['101', '102'])).
% 1.29/1.46  thf('104', plain,
% 1.29/1.46      (![X0 : $i, X1 : $i]:
% 1.29/1.46         (~ (m1_pre_topc @ X1 @ X0)
% 1.29/1.46          | ((k2_tmap_1 @ X0 @ X0 @ (k4_tmap_1 @ X0 @ X0) @ X1)
% 1.29/1.46              = (k2_partfun1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0) @ 
% 1.29/1.46                 (k4_tmap_1 @ X0 @ X0) @ (u1_struct_0 @ X1)))
% 1.29/1.46          | ~ (v1_funct_2 @ (k4_tmap_1 @ X0 @ X0) @ (u1_struct_0 @ X0) @ 
% 1.29/1.46               (u1_struct_0 @ X0))
% 1.29/1.46          | ~ (v1_funct_1 @ (k4_tmap_1 @ X0 @ X0))
% 1.29/1.46          | ~ (v2_pre_topc @ X0)
% 1.29/1.46          | (v2_struct_0 @ X0)
% 1.29/1.46          | ~ (l1_pre_topc @ X0))),
% 1.29/1.46      inference('simplify', [status(thm)], ['103'])).
% 1.29/1.46  thf('105', plain,
% 1.29/1.46      (![X0 : $i, X1 : $i]:
% 1.29/1.46         (~ (l1_pre_topc @ X0)
% 1.29/1.46          | (v2_struct_0 @ X0)
% 1.29/1.46          | ~ (v2_pre_topc @ X0)
% 1.29/1.46          | ~ (l1_pre_topc @ X0)
% 1.29/1.46          | (v2_struct_0 @ X0)
% 1.29/1.46          | ~ (v2_pre_topc @ X0)
% 1.29/1.46          | ~ (v1_funct_1 @ (k4_tmap_1 @ X0 @ X0))
% 1.29/1.46          | ((k2_tmap_1 @ X0 @ X0 @ (k4_tmap_1 @ X0 @ X0) @ X1)
% 1.29/1.46              = (k2_partfun1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0) @ 
% 1.29/1.46                 (k4_tmap_1 @ X0 @ X0) @ (u1_struct_0 @ X1)))
% 1.29/1.46          | ~ (m1_pre_topc @ X1 @ X0))),
% 1.29/1.46      inference('sup-', [status(thm)], ['100', '104'])).
% 1.29/1.46  thf('106', plain,
% 1.29/1.46      (![X0 : $i, X1 : $i]:
% 1.29/1.46         (~ (m1_pre_topc @ X1 @ X0)
% 1.29/1.46          | ((k2_tmap_1 @ X0 @ X0 @ (k4_tmap_1 @ X0 @ X0) @ X1)
% 1.29/1.46              = (k2_partfun1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0) @ 
% 1.29/1.46                 (k4_tmap_1 @ X0 @ X0) @ (u1_struct_0 @ X1)))
% 1.29/1.46          | ~ (v1_funct_1 @ (k4_tmap_1 @ X0 @ X0))
% 1.29/1.46          | ~ (v2_pre_topc @ X0)
% 1.29/1.46          | (v2_struct_0 @ X0)
% 1.29/1.46          | ~ (l1_pre_topc @ X0))),
% 1.29/1.46      inference('simplify', [status(thm)], ['105'])).
% 1.29/1.46  thf('107', plain,
% 1.29/1.46      (![X0 : $i, X1 : $i]:
% 1.29/1.46         (~ (l1_pre_topc @ X0)
% 1.29/1.46          | (v2_struct_0 @ X0)
% 1.29/1.46          | ~ (v2_pre_topc @ X0)
% 1.29/1.46          | ~ (l1_pre_topc @ X0)
% 1.29/1.46          | (v2_struct_0 @ X0)
% 1.29/1.46          | ~ (v2_pre_topc @ X0)
% 1.29/1.46          | ((k2_tmap_1 @ X0 @ X0 @ (k4_tmap_1 @ X0 @ X0) @ X1)
% 1.29/1.46              = (k2_partfun1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0) @ 
% 1.29/1.46                 (k4_tmap_1 @ X0 @ X0) @ (u1_struct_0 @ X1)))
% 1.29/1.46          | ~ (m1_pre_topc @ X1 @ X0))),
% 1.29/1.46      inference('sup-', [status(thm)], ['99', '106'])).
% 1.29/1.46  thf('108', plain,
% 1.29/1.46      (![X0 : $i, X1 : $i]:
% 1.29/1.46         (~ (m1_pre_topc @ X1 @ X0)
% 1.29/1.46          | ((k2_tmap_1 @ X0 @ X0 @ (k4_tmap_1 @ X0 @ X0) @ X1)
% 1.29/1.46              = (k2_partfun1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0) @ 
% 1.29/1.46                 (k4_tmap_1 @ X0 @ X0) @ (u1_struct_0 @ X1)))
% 1.29/1.46          | ~ (v2_pre_topc @ X0)
% 1.29/1.46          | (v2_struct_0 @ X0)
% 1.29/1.46          | ~ (l1_pre_topc @ X0))),
% 1.29/1.46      inference('simplify', [status(thm)], ['107'])).
% 1.29/1.46  thf('109', plain,
% 1.29/1.46      ((~ (l1_pre_topc @ sk_A)
% 1.29/1.46        | (v2_struct_0 @ sk_A)
% 1.29/1.46        | ~ (v2_pre_topc @ sk_A)
% 1.29/1.46        | ((k2_tmap_1 @ sk_A @ sk_A @ (k4_tmap_1 @ sk_A @ sk_A) @ sk_B)
% 1.29/1.46            = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 1.29/1.46               (k4_tmap_1 @ sk_A @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 1.29/1.46      inference('sup-', [status(thm)], ['98', '108'])).
% 1.29/1.46  thf('110', plain, ((l1_pre_topc @ sk_A)),
% 1.29/1.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.46  thf('111', plain, ((v2_pre_topc @ sk_A)),
% 1.29/1.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.46  thf('112', plain,
% 1.29/1.46      (((v2_struct_0 @ sk_A)
% 1.29/1.46        | ((k2_tmap_1 @ sk_A @ sk_A @ (k4_tmap_1 @ sk_A @ sk_A) @ sk_B)
% 1.29/1.46            = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 1.29/1.46               (k4_tmap_1 @ sk_A @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 1.29/1.46      inference('demod', [status(thm)], ['109', '110', '111'])).
% 1.29/1.46  thf('113', plain, (~ (v2_struct_0 @ sk_A)),
% 1.29/1.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.46  thf('114', plain,
% 1.29/1.46      (((k2_tmap_1 @ sk_A @ sk_A @ (k4_tmap_1 @ sk_A @ sk_A) @ sk_B)
% 1.29/1.46         = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 1.29/1.46            (k4_tmap_1 @ sk_A @ sk_A) @ (u1_struct_0 @ sk_B)))),
% 1.29/1.46      inference('clc', [status(thm)], ['112', '113'])).
% 1.29/1.46  thf('115', plain, ((v2_pre_topc @ sk_A)),
% 1.29/1.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.46  thf('116', plain, ((l1_pre_topc @ sk_A)),
% 1.29/1.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.46  thf('117', plain,
% 1.29/1.46      ((((k3_tmap_1 @ sk_A @ sk_A @ sk_A @ sk_B @ (k4_tmap_1 @ sk_A @ sk_A))
% 1.29/1.46          = (k2_tmap_1 @ sk_A @ sk_A @ (k4_tmap_1 @ sk_A @ sk_A) @ sk_B))
% 1.29/1.46        | (v2_struct_0 @ sk_A)
% 1.29/1.46        | (v2_struct_0 @ sk_A))),
% 1.29/1.46      inference('demod', [status(thm)], ['95', '96', '97', '114', '115', '116'])).
% 1.29/1.46  thf('118', plain,
% 1.29/1.46      (((v2_struct_0 @ sk_A)
% 1.29/1.46        | ((k3_tmap_1 @ sk_A @ sk_A @ sk_A @ sk_B @ (k4_tmap_1 @ sk_A @ sk_A))
% 1.29/1.46            = (k2_tmap_1 @ sk_A @ sk_A @ (k4_tmap_1 @ sk_A @ sk_A) @ sk_B)))),
% 1.29/1.46      inference('simplify', [status(thm)], ['117'])).
% 1.29/1.46  thf('119', plain, (~ (v2_struct_0 @ sk_A)),
% 1.29/1.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.46  thf('120', plain,
% 1.29/1.46      (((k3_tmap_1 @ sk_A @ sk_A @ sk_A @ sk_B @ (k4_tmap_1 @ sk_A @ sk_A))
% 1.29/1.46         = (k2_tmap_1 @ sk_A @ sk_A @ (k4_tmap_1 @ sk_A @ sk_A) @ sk_B))),
% 1.29/1.46      inference('clc', [status(thm)], ['118', '119'])).
% 1.29/1.46  thf('121', plain,
% 1.29/1.46      ((m1_subset_1 @ 
% 1.29/1.46        (k2_tmap_1 @ sk_A @ sk_A @ (k4_tmap_1 @ sk_A @ sk_A) @ sk_B) @ 
% 1.29/1.46        (k1_zfmisc_1 @ 
% 1.29/1.46         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 1.29/1.46      inference('demod', [status(thm)], ['78', '120'])).
% 1.29/1.46  thf(redefinition_r2_funct_2, axiom,
% 1.29/1.46    (![A:$i,B:$i,C:$i,D:$i]:
% 1.29/1.46     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.29/1.46         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.29/1.46         ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 1.29/1.46         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.29/1.46       ( ( r2_funct_2 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 1.29/1.46  thf('122', plain,
% 1.29/1.46      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 1.29/1.46         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12)))
% 1.29/1.46          | ~ (v1_funct_2 @ X10 @ X11 @ X12)
% 1.29/1.46          | ~ (v1_funct_1 @ X10)
% 1.29/1.46          | ~ (v1_funct_1 @ X13)
% 1.29/1.46          | ~ (v1_funct_2 @ X13 @ X11 @ X12)
% 1.29/1.46          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12)))
% 1.29/1.46          | ((X10) = (X13))
% 1.29/1.46          | ~ (r2_funct_2 @ X11 @ X12 @ X10 @ X13))),
% 1.29/1.46      inference('cnf', [status(esa)], [redefinition_r2_funct_2])).
% 1.29/1.46  thf('123', plain,
% 1.29/1.46      (![X0 : $i]:
% 1.29/1.46         (~ (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.29/1.46             (k2_tmap_1 @ sk_A @ sk_A @ (k4_tmap_1 @ sk_A @ sk_A) @ sk_B) @ X0)
% 1.29/1.46          | ((k2_tmap_1 @ sk_A @ sk_A @ (k4_tmap_1 @ sk_A @ sk_A) @ sk_B)
% 1.29/1.46              = (X0))
% 1.29/1.46          | ~ (m1_subset_1 @ X0 @ 
% 1.29/1.46               (k1_zfmisc_1 @ 
% 1.29/1.46                (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))
% 1.29/1.46          | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 1.29/1.46          | ~ (v1_funct_1 @ X0)
% 1.29/1.46          | ~ (v1_funct_1 @ 
% 1.29/1.46               (k2_tmap_1 @ sk_A @ sk_A @ (k4_tmap_1 @ sk_A @ sk_A) @ sk_B))
% 1.29/1.46          | ~ (v1_funct_2 @ 
% 1.29/1.46               (k2_tmap_1 @ sk_A @ sk_A @ (k4_tmap_1 @ sk_A @ sk_A) @ sk_B) @ 
% 1.29/1.46               (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 1.29/1.46      inference('sup-', [status(thm)], ['121', '122'])).
% 1.29/1.46  thf('124', plain,
% 1.29/1.46      (![X39 : $i]: ((m1_pre_topc @ X39 @ X39) | ~ (l1_pre_topc @ X39))),
% 1.29/1.46      inference('cnf', [status(esa)], [t2_tsep_1])).
% 1.29/1.46  thf('125', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 1.29/1.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.46  thf('126', plain,
% 1.29/1.46      (![X0 : $i]:
% 1.29/1.46         (~ (v2_pre_topc @ X0)
% 1.29/1.46          | (v2_struct_0 @ X0)
% 1.29/1.46          | (v1_funct_1 @ (k4_tmap_1 @ X0 @ X0))
% 1.29/1.46          | ~ (l1_pre_topc @ X0))),
% 1.29/1.46      inference('simplify', [status(thm)], ['3'])).
% 1.29/1.46  thf('127', plain,
% 1.29/1.46      (![X0 : $i]:
% 1.29/1.46         (~ (v2_pre_topc @ X0)
% 1.29/1.46          | (v2_struct_0 @ X0)
% 1.29/1.46          | (v1_funct_2 @ (k4_tmap_1 @ X0 @ X0) @ (u1_struct_0 @ X0) @ 
% 1.29/1.46             (u1_struct_0 @ X0))
% 1.29/1.46          | ~ (l1_pre_topc @ X0))),
% 1.29/1.46      inference('simplify', [status(thm)], ['7'])).
% 1.29/1.46  thf('128', plain,
% 1.29/1.46      (![X0 : $i]:
% 1.29/1.46         (~ (v2_pre_topc @ X0)
% 1.29/1.46          | (v2_struct_0 @ X0)
% 1.29/1.46          | (m1_subset_1 @ (k4_tmap_1 @ X0 @ X0) @ 
% 1.29/1.46             (k1_zfmisc_1 @ 
% 1.29/1.46              (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0))))
% 1.29/1.46          | ~ (l1_pre_topc @ X0))),
% 1.29/1.46      inference('simplify', [status(thm)], ['19'])).
% 1.29/1.46  thf('129', plain,
% 1.29/1.46      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 1.29/1.46         (~ (m1_pre_topc @ X30 @ X31)
% 1.29/1.46          | ~ (m1_pre_topc @ X32 @ X31)
% 1.29/1.46          | ~ (l1_pre_topc @ X33)
% 1.29/1.46          | ~ (v2_pre_topc @ X33)
% 1.29/1.46          | (v2_struct_0 @ X33)
% 1.29/1.46          | ~ (l1_pre_topc @ X31)
% 1.29/1.46          | ~ (v2_pre_topc @ X31)
% 1.29/1.46          | (v2_struct_0 @ X31)
% 1.29/1.46          | ~ (v1_funct_1 @ X34)
% 1.29/1.46          | ~ (v1_funct_2 @ X34 @ (u1_struct_0 @ X32) @ (u1_struct_0 @ X33))
% 1.29/1.46          | ~ (m1_subset_1 @ X34 @ 
% 1.29/1.46               (k1_zfmisc_1 @ 
% 1.29/1.46                (k2_zfmisc_1 @ (u1_struct_0 @ X32) @ (u1_struct_0 @ X33))))
% 1.29/1.46          | (v1_funct_1 @ (k3_tmap_1 @ X31 @ X33 @ X32 @ X30 @ X34)))),
% 1.29/1.46      inference('cnf', [status(esa)], [dt_k3_tmap_1])).
% 1.29/1.46  thf('130', plain,
% 1.29/1.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.29/1.46         (~ (l1_pre_topc @ X0)
% 1.29/1.46          | (v2_struct_0 @ X0)
% 1.29/1.46          | ~ (v2_pre_topc @ X0)
% 1.29/1.46          | (v1_funct_1 @ 
% 1.29/1.46             (k3_tmap_1 @ X2 @ X0 @ X0 @ X1 @ (k4_tmap_1 @ X0 @ X0)))
% 1.29/1.46          | ~ (v1_funct_2 @ (k4_tmap_1 @ X0 @ X0) @ (u1_struct_0 @ X0) @ 
% 1.29/1.46               (u1_struct_0 @ X0))
% 1.29/1.46          | ~ (v1_funct_1 @ (k4_tmap_1 @ X0 @ X0))
% 1.29/1.46          | (v2_struct_0 @ X2)
% 1.29/1.46          | ~ (v2_pre_topc @ X2)
% 1.29/1.46          | ~ (l1_pre_topc @ X2)
% 1.29/1.46          | (v2_struct_0 @ X0)
% 1.29/1.46          | ~ (v2_pre_topc @ X0)
% 1.29/1.46          | ~ (l1_pre_topc @ X0)
% 1.29/1.46          | ~ (m1_pre_topc @ X0 @ X2)
% 1.29/1.46          | ~ (m1_pre_topc @ X1 @ X2))),
% 1.29/1.46      inference('sup-', [status(thm)], ['128', '129'])).
% 1.29/1.46  thf('131', plain,
% 1.29/1.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.29/1.46         (~ (m1_pre_topc @ X1 @ X2)
% 1.29/1.46          | ~ (m1_pre_topc @ X0 @ X2)
% 1.29/1.46          | ~ (l1_pre_topc @ X2)
% 1.29/1.46          | ~ (v2_pre_topc @ X2)
% 1.29/1.46          | (v2_struct_0 @ X2)
% 1.29/1.46          | ~ (v1_funct_1 @ (k4_tmap_1 @ X0 @ X0))
% 1.29/1.46          | ~ (v1_funct_2 @ (k4_tmap_1 @ X0 @ X0) @ (u1_struct_0 @ X0) @ 
% 1.29/1.46               (u1_struct_0 @ X0))
% 1.29/1.46          | (v1_funct_1 @ 
% 1.29/1.46             (k3_tmap_1 @ X2 @ X0 @ X0 @ X1 @ (k4_tmap_1 @ X0 @ X0)))
% 1.29/1.46          | ~ (v2_pre_topc @ X0)
% 1.29/1.46          | (v2_struct_0 @ X0)
% 1.29/1.46          | ~ (l1_pre_topc @ X0))),
% 1.29/1.46      inference('simplify', [status(thm)], ['130'])).
% 1.29/1.46  thf('132', plain,
% 1.29/1.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.29/1.46         (~ (l1_pre_topc @ X0)
% 1.29/1.46          | (v2_struct_0 @ X0)
% 1.29/1.46          | ~ (v2_pre_topc @ X0)
% 1.29/1.46          | ~ (l1_pre_topc @ X0)
% 1.29/1.46          | (v2_struct_0 @ X0)
% 1.29/1.46          | ~ (v2_pre_topc @ X0)
% 1.29/1.46          | (v1_funct_1 @ 
% 1.29/1.46             (k3_tmap_1 @ X2 @ X0 @ X0 @ X1 @ (k4_tmap_1 @ X0 @ X0)))
% 1.29/1.46          | ~ (v1_funct_1 @ (k4_tmap_1 @ X0 @ X0))
% 1.29/1.46          | (v2_struct_0 @ X2)
% 1.29/1.46          | ~ (v2_pre_topc @ X2)
% 1.29/1.46          | ~ (l1_pre_topc @ X2)
% 1.29/1.46          | ~ (m1_pre_topc @ X0 @ X2)
% 1.29/1.46          | ~ (m1_pre_topc @ X1 @ X2))),
% 1.29/1.46      inference('sup-', [status(thm)], ['127', '131'])).
% 1.29/1.46  thf('133', plain,
% 1.29/1.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.29/1.46         (~ (m1_pre_topc @ X1 @ X2)
% 1.29/1.46          | ~ (m1_pre_topc @ X0 @ X2)
% 1.29/1.46          | ~ (l1_pre_topc @ X2)
% 1.29/1.46          | ~ (v2_pre_topc @ X2)
% 1.29/1.46          | (v2_struct_0 @ X2)
% 1.29/1.46          | ~ (v1_funct_1 @ (k4_tmap_1 @ X0 @ X0))
% 1.29/1.46          | (v1_funct_1 @ 
% 1.29/1.46             (k3_tmap_1 @ X2 @ X0 @ X0 @ X1 @ (k4_tmap_1 @ X0 @ X0)))
% 1.29/1.46          | ~ (v2_pre_topc @ X0)
% 1.29/1.46          | (v2_struct_0 @ X0)
% 1.29/1.46          | ~ (l1_pre_topc @ X0))),
% 1.29/1.46      inference('simplify', [status(thm)], ['132'])).
% 1.29/1.46  thf('134', plain,
% 1.29/1.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.29/1.46         (~ (l1_pre_topc @ X0)
% 1.29/1.46          | (v2_struct_0 @ X0)
% 1.29/1.46          | ~ (v2_pre_topc @ X0)
% 1.29/1.46          | ~ (l1_pre_topc @ X0)
% 1.29/1.46          | (v2_struct_0 @ X0)
% 1.29/1.46          | ~ (v2_pre_topc @ X0)
% 1.29/1.46          | (v1_funct_1 @ 
% 1.29/1.46             (k3_tmap_1 @ X2 @ X0 @ X0 @ X1 @ (k4_tmap_1 @ X0 @ X0)))
% 1.29/1.46          | (v2_struct_0 @ X2)
% 1.29/1.46          | ~ (v2_pre_topc @ X2)
% 1.29/1.46          | ~ (l1_pre_topc @ X2)
% 1.29/1.46          | ~ (m1_pre_topc @ X0 @ X2)
% 1.29/1.46          | ~ (m1_pre_topc @ X1 @ X2))),
% 1.29/1.46      inference('sup-', [status(thm)], ['126', '133'])).
% 1.29/1.46  thf('135', plain,
% 1.29/1.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.29/1.46         (~ (m1_pre_topc @ X1 @ X2)
% 1.29/1.46          | ~ (m1_pre_topc @ X0 @ X2)
% 1.29/1.46          | ~ (l1_pre_topc @ X2)
% 1.29/1.46          | ~ (v2_pre_topc @ X2)
% 1.29/1.46          | (v2_struct_0 @ X2)
% 1.29/1.46          | (v1_funct_1 @ 
% 1.29/1.46             (k3_tmap_1 @ X2 @ X0 @ X0 @ X1 @ (k4_tmap_1 @ X0 @ X0)))
% 1.29/1.46          | ~ (v2_pre_topc @ X0)
% 1.29/1.46          | (v2_struct_0 @ X0)
% 1.29/1.46          | ~ (l1_pre_topc @ X0))),
% 1.29/1.46      inference('simplify', [status(thm)], ['134'])).
% 1.29/1.46  thf('136', plain,
% 1.29/1.46      (![X0 : $i]:
% 1.29/1.46         (~ (l1_pre_topc @ X0)
% 1.29/1.46          | (v2_struct_0 @ X0)
% 1.29/1.46          | ~ (v2_pre_topc @ X0)
% 1.29/1.46          | (v1_funct_1 @ 
% 1.29/1.46             (k3_tmap_1 @ sk_A @ X0 @ X0 @ sk_B @ (k4_tmap_1 @ X0 @ X0)))
% 1.29/1.46          | (v2_struct_0 @ sk_A)
% 1.29/1.46          | ~ (v2_pre_topc @ sk_A)
% 1.29/1.46          | ~ (l1_pre_topc @ sk_A)
% 1.29/1.46          | ~ (m1_pre_topc @ X0 @ sk_A))),
% 1.29/1.46      inference('sup-', [status(thm)], ['125', '135'])).
% 1.29/1.46  thf('137', plain, ((v2_pre_topc @ sk_A)),
% 1.29/1.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.46  thf('138', plain, ((l1_pre_topc @ sk_A)),
% 1.29/1.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.46  thf('139', plain,
% 1.29/1.46      (![X0 : $i]:
% 1.29/1.46         (~ (l1_pre_topc @ X0)
% 1.29/1.46          | (v2_struct_0 @ X0)
% 1.29/1.46          | ~ (v2_pre_topc @ X0)
% 1.29/1.46          | (v1_funct_1 @ 
% 1.29/1.46             (k3_tmap_1 @ sk_A @ X0 @ X0 @ sk_B @ (k4_tmap_1 @ X0 @ X0)))
% 1.29/1.46          | (v2_struct_0 @ sk_A)
% 1.29/1.46          | ~ (m1_pre_topc @ X0 @ sk_A))),
% 1.29/1.46      inference('demod', [status(thm)], ['136', '137', '138'])).
% 1.29/1.46  thf('140', plain,
% 1.29/1.46      ((~ (l1_pre_topc @ sk_A)
% 1.29/1.46        | (v2_struct_0 @ sk_A)
% 1.29/1.46        | (v1_funct_1 @ 
% 1.29/1.46           (k3_tmap_1 @ sk_A @ sk_A @ sk_A @ sk_B @ (k4_tmap_1 @ sk_A @ sk_A)))
% 1.29/1.46        | ~ (v2_pre_topc @ sk_A)
% 1.29/1.46        | (v2_struct_0 @ sk_A)
% 1.29/1.46        | ~ (l1_pre_topc @ sk_A))),
% 1.29/1.46      inference('sup-', [status(thm)], ['124', '139'])).
% 1.29/1.46  thf('141', plain, ((l1_pre_topc @ sk_A)),
% 1.29/1.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.46  thf('142', plain, ((v2_pre_topc @ sk_A)),
% 1.29/1.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.46  thf('143', plain, ((l1_pre_topc @ sk_A)),
% 1.29/1.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.46  thf('144', plain,
% 1.29/1.46      (((v2_struct_0 @ sk_A)
% 1.29/1.46        | (v1_funct_1 @ 
% 1.29/1.46           (k3_tmap_1 @ sk_A @ sk_A @ sk_A @ sk_B @ (k4_tmap_1 @ sk_A @ sk_A)))
% 1.29/1.46        | (v2_struct_0 @ sk_A))),
% 1.29/1.46      inference('demod', [status(thm)], ['140', '141', '142', '143'])).
% 1.29/1.46  thf('145', plain,
% 1.29/1.46      (((v1_funct_1 @ 
% 1.29/1.46         (k3_tmap_1 @ sk_A @ sk_A @ sk_A @ sk_B @ (k4_tmap_1 @ sk_A @ sk_A)))
% 1.29/1.46        | (v2_struct_0 @ sk_A))),
% 1.29/1.46      inference('simplify', [status(thm)], ['144'])).
% 1.29/1.46  thf('146', plain, (~ (v2_struct_0 @ sk_A)),
% 1.29/1.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.46  thf('147', plain,
% 1.29/1.46      ((v1_funct_1 @ 
% 1.29/1.46        (k3_tmap_1 @ sk_A @ sk_A @ sk_A @ sk_B @ (k4_tmap_1 @ sk_A @ sk_A)))),
% 1.29/1.46      inference('clc', [status(thm)], ['145', '146'])).
% 1.29/1.46  thf('148', plain,
% 1.29/1.46      (((k3_tmap_1 @ sk_A @ sk_A @ sk_A @ sk_B @ (k4_tmap_1 @ sk_A @ sk_A))
% 1.29/1.46         = (k2_tmap_1 @ sk_A @ sk_A @ (k4_tmap_1 @ sk_A @ sk_A) @ sk_B))),
% 1.29/1.46      inference('clc', [status(thm)], ['118', '119'])).
% 1.29/1.46  thf('149', plain,
% 1.29/1.46      ((v1_funct_1 @ 
% 1.29/1.46        (k2_tmap_1 @ sk_A @ sk_A @ (k4_tmap_1 @ sk_A @ sk_A) @ sk_B))),
% 1.29/1.46      inference('demod', [status(thm)], ['147', '148'])).
% 1.29/1.46  thf('150', plain,
% 1.29/1.46      (![X39 : $i]: ((m1_pre_topc @ X39 @ X39) | ~ (l1_pre_topc @ X39))),
% 1.29/1.46      inference('cnf', [status(esa)], [t2_tsep_1])).
% 1.29/1.46  thf('151', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 1.29/1.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.46  thf('152', plain,
% 1.29/1.46      (![X0 : $i]:
% 1.29/1.46         (~ (v2_pre_topc @ X0)
% 1.29/1.46          | (v2_struct_0 @ X0)
% 1.29/1.46          | (v1_funct_1 @ (k4_tmap_1 @ X0 @ X0))
% 1.29/1.46          | ~ (l1_pre_topc @ X0))),
% 1.29/1.46      inference('simplify', [status(thm)], ['3'])).
% 1.29/1.46  thf('153', plain,
% 1.29/1.46      (![X0 : $i]:
% 1.29/1.46         (~ (v2_pre_topc @ X0)
% 1.29/1.46          | (v2_struct_0 @ X0)
% 1.29/1.46          | (v1_funct_2 @ (k4_tmap_1 @ X0 @ X0) @ (u1_struct_0 @ X0) @ 
% 1.29/1.46             (u1_struct_0 @ X0))
% 1.29/1.46          | ~ (l1_pre_topc @ X0))),
% 1.29/1.46      inference('simplify', [status(thm)], ['7'])).
% 1.29/1.46  thf('154', plain,
% 1.29/1.46      (![X0 : $i]:
% 1.29/1.46         (~ (v2_pre_topc @ X0)
% 1.29/1.46          | (v2_struct_0 @ X0)
% 1.29/1.46          | (m1_subset_1 @ (k4_tmap_1 @ X0 @ X0) @ 
% 1.29/1.46             (k1_zfmisc_1 @ 
% 1.29/1.46              (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0))))
% 1.29/1.46          | ~ (l1_pre_topc @ X0))),
% 1.29/1.46      inference('simplify', [status(thm)], ['19'])).
% 1.29/1.46  thf('155', plain,
% 1.29/1.46      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 1.29/1.46         (~ (m1_pre_topc @ X30 @ X31)
% 1.29/1.46          | ~ (m1_pre_topc @ X32 @ X31)
% 1.29/1.46          | ~ (l1_pre_topc @ X33)
% 1.29/1.46          | ~ (v2_pre_topc @ X33)
% 1.29/1.46          | (v2_struct_0 @ X33)
% 1.29/1.46          | ~ (l1_pre_topc @ X31)
% 1.29/1.46          | ~ (v2_pre_topc @ X31)
% 1.29/1.46          | (v2_struct_0 @ X31)
% 1.29/1.46          | ~ (v1_funct_1 @ X34)
% 1.29/1.46          | ~ (v1_funct_2 @ X34 @ (u1_struct_0 @ X32) @ (u1_struct_0 @ X33))
% 1.29/1.46          | ~ (m1_subset_1 @ X34 @ 
% 1.29/1.46               (k1_zfmisc_1 @ 
% 1.29/1.46                (k2_zfmisc_1 @ (u1_struct_0 @ X32) @ (u1_struct_0 @ X33))))
% 1.29/1.46          | (v1_funct_2 @ (k3_tmap_1 @ X31 @ X33 @ X32 @ X30 @ X34) @ 
% 1.29/1.46             (u1_struct_0 @ X30) @ (u1_struct_0 @ X33)))),
% 1.29/1.46      inference('cnf', [status(esa)], [dt_k3_tmap_1])).
% 1.29/1.46  thf('156', plain,
% 1.29/1.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.29/1.46         (~ (l1_pre_topc @ X0)
% 1.29/1.46          | (v2_struct_0 @ X0)
% 1.29/1.46          | ~ (v2_pre_topc @ X0)
% 1.29/1.46          | (v1_funct_2 @ 
% 1.29/1.46             (k3_tmap_1 @ X2 @ X0 @ X0 @ X1 @ (k4_tmap_1 @ X0 @ X0)) @ 
% 1.29/1.46             (u1_struct_0 @ X1) @ (u1_struct_0 @ X0))
% 1.29/1.46          | ~ (v1_funct_2 @ (k4_tmap_1 @ X0 @ X0) @ (u1_struct_0 @ X0) @ 
% 1.29/1.46               (u1_struct_0 @ X0))
% 1.29/1.46          | ~ (v1_funct_1 @ (k4_tmap_1 @ X0 @ X0))
% 1.29/1.46          | (v2_struct_0 @ X2)
% 1.29/1.46          | ~ (v2_pre_topc @ X2)
% 1.29/1.46          | ~ (l1_pre_topc @ X2)
% 1.29/1.46          | (v2_struct_0 @ X0)
% 1.29/1.46          | ~ (v2_pre_topc @ X0)
% 1.29/1.46          | ~ (l1_pre_topc @ X0)
% 1.29/1.46          | ~ (m1_pre_topc @ X0 @ X2)
% 1.29/1.46          | ~ (m1_pre_topc @ X1 @ X2))),
% 1.29/1.46      inference('sup-', [status(thm)], ['154', '155'])).
% 1.29/1.46  thf('157', plain,
% 1.29/1.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.29/1.46         (~ (m1_pre_topc @ X1 @ X2)
% 1.29/1.46          | ~ (m1_pre_topc @ X0 @ X2)
% 1.29/1.46          | ~ (l1_pre_topc @ X2)
% 1.29/1.46          | ~ (v2_pre_topc @ X2)
% 1.29/1.46          | (v2_struct_0 @ X2)
% 1.29/1.46          | ~ (v1_funct_1 @ (k4_tmap_1 @ X0 @ X0))
% 1.29/1.46          | ~ (v1_funct_2 @ (k4_tmap_1 @ X0 @ X0) @ (u1_struct_0 @ X0) @ 
% 1.29/1.46               (u1_struct_0 @ X0))
% 1.29/1.46          | (v1_funct_2 @ 
% 1.29/1.46             (k3_tmap_1 @ X2 @ X0 @ X0 @ X1 @ (k4_tmap_1 @ X0 @ X0)) @ 
% 1.29/1.46             (u1_struct_0 @ X1) @ (u1_struct_0 @ X0))
% 1.29/1.46          | ~ (v2_pre_topc @ X0)
% 1.29/1.46          | (v2_struct_0 @ X0)
% 1.29/1.46          | ~ (l1_pre_topc @ X0))),
% 1.29/1.47      inference('simplify', [status(thm)], ['156'])).
% 1.29/1.47  thf('158', plain,
% 1.29/1.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.29/1.47         (~ (l1_pre_topc @ X0)
% 1.29/1.47          | (v2_struct_0 @ X0)
% 1.29/1.47          | ~ (v2_pre_topc @ X0)
% 1.29/1.47          | ~ (l1_pre_topc @ X0)
% 1.29/1.47          | (v2_struct_0 @ X0)
% 1.29/1.47          | ~ (v2_pre_topc @ X0)
% 1.29/1.47          | (v1_funct_2 @ 
% 1.29/1.47             (k3_tmap_1 @ X2 @ X0 @ X0 @ X1 @ (k4_tmap_1 @ X0 @ X0)) @ 
% 1.29/1.47             (u1_struct_0 @ X1) @ (u1_struct_0 @ X0))
% 1.29/1.47          | ~ (v1_funct_1 @ (k4_tmap_1 @ X0 @ X0))
% 1.29/1.47          | (v2_struct_0 @ X2)
% 1.29/1.47          | ~ (v2_pre_topc @ X2)
% 1.29/1.47          | ~ (l1_pre_topc @ X2)
% 1.29/1.47          | ~ (m1_pre_topc @ X0 @ X2)
% 1.29/1.47          | ~ (m1_pre_topc @ X1 @ X2))),
% 1.29/1.47      inference('sup-', [status(thm)], ['153', '157'])).
% 1.29/1.47  thf('159', plain,
% 1.29/1.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.29/1.47         (~ (m1_pre_topc @ X1 @ X2)
% 1.29/1.47          | ~ (m1_pre_topc @ X0 @ X2)
% 1.29/1.47          | ~ (l1_pre_topc @ X2)
% 1.29/1.47          | ~ (v2_pre_topc @ X2)
% 1.29/1.47          | (v2_struct_0 @ X2)
% 1.29/1.47          | ~ (v1_funct_1 @ (k4_tmap_1 @ X0 @ X0))
% 1.29/1.47          | (v1_funct_2 @ 
% 1.29/1.47             (k3_tmap_1 @ X2 @ X0 @ X0 @ X1 @ (k4_tmap_1 @ X0 @ X0)) @ 
% 1.29/1.47             (u1_struct_0 @ X1) @ (u1_struct_0 @ X0))
% 1.29/1.47          | ~ (v2_pre_topc @ X0)
% 1.29/1.47          | (v2_struct_0 @ X0)
% 1.29/1.47          | ~ (l1_pre_topc @ X0))),
% 1.29/1.47      inference('simplify', [status(thm)], ['158'])).
% 1.29/1.47  thf('160', plain,
% 1.29/1.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.29/1.47         (~ (l1_pre_topc @ X0)
% 1.29/1.47          | (v2_struct_0 @ X0)
% 1.29/1.47          | ~ (v2_pre_topc @ X0)
% 1.29/1.47          | ~ (l1_pre_topc @ X0)
% 1.29/1.47          | (v2_struct_0 @ X0)
% 1.29/1.47          | ~ (v2_pre_topc @ X0)
% 1.29/1.47          | (v1_funct_2 @ 
% 1.29/1.47             (k3_tmap_1 @ X2 @ X0 @ X0 @ X1 @ (k4_tmap_1 @ X0 @ X0)) @ 
% 1.29/1.47             (u1_struct_0 @ X1) @ (u1_struct_0 @ X0))
% 1.29/1.47          | (v2_struct_0 @ X2)
% 1.29/1.47          | ~ (v2_pre_topc @ X2)
% 1.29/1.47          | ~ (l1_pre_topc @ X2)
% 1.29/1.47          | ~ (m1_pre_topc @ X0 @ X2)
% 1.29/1.47          | ~ (m1_pre_topc @ X1 @ X2))),
% 1.29/1.47      inference('sup-', [status(thm)], ['152', '159'])).
% 1.29/1.47  thf('161', plain,
% 1.29/1.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.29/1.47         (~ (m1_pre_topc @ X1 @ X2)
% 1.29/1.47          | ~ (m1_pre_topc @ X0 @ X2)
% 1.29/1.47          | ~ (l1_pre_topc @ X2)
% 1.29/1.47          | ~ (v2_pre_topc @ X2)
% 1.29/1.47          | (v2_struct_0 @ X2)
% 1.29/1.47          | (v1_funct_2 @ 
% 1.29/1.47             (k3_tmap_1 @ X2 @ X0 @ X0 @ X1 @ (k4_tmap_1 @ X0 @ X0)) @ 
% 1.29/1.47             (u1_struct_0 @ X1) @ (u1_struct_0 @ X0))
% 1.29/1.47          | ~ (v2_pre_topc @ X0)
% 1.29/1.47          | (v2_struct_0 @ X0)
% 1.29/1.47          | ~ (l1_pre_topc @ X0))),
% 1.29/1.47      inference('simplify', [status(thm)], ['160'])).
% 1.29/1.47  thf('162', plain,
% 1.29/1.47      (![X0 : $i]:
% 1.29/1.47         (~ (l1_pre_topc @ X0)
% 1.29/1.47          | (v2_struct_0 @ X0)
% 1.29/1.47          | ~ (v2_pre_topc @ X0)
% 1.29/1.47          | (v1_funct_2 @ 
% 1.29/1.47             (k3_tmap_1 @ sk_A @ X0 @ X0 @ sk_B @ (k4_tmap_1 @ X0 @ X0)) @ 
% 1.29/1.47             (u1_struct_0 @ sk_B) @ (u1_struct_0 @ X0))
% 1.29/1.47          | (v2_struct_0 @ sk_A)
% 1.29/1.47          | ~ (v2_pre_topc @ sk_A)
% 1.29/1.47          | ~ (l1_pre_topc @ sk_A)
% 1.29/1.47          | ~ (m1_pre_topc @ X0 @ sk_A))),
% 1.29/1.47      inference('sup-', [status(thm)], ['151', '161'])).
% 1.29/1.47  thf('163', plain, ((v2_pre_topc @ sk_A)),
% 1.29/1.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.47  thf('164', plain, ((l1_pre_topc @ sk_A)),
% 1.29/1.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.47  thf('165', plain,
% 1.29/1.47      (![X0 : $i]:
% 1.29/1.47         (~ (l1_pre_topc @ X0)
% 1.29/1.47          | (v2_struct_0 @ X0)
% 1.29/1.47          | ~ (v2_pre_topc @ X0)
% 1.29/1.47          | (v1_funct_2 @ 
% 1.29/1.47             (k3_tmap_1 @ sk_A @ X0 @ X0 @ sk_B @ (k4_tmap_1 @ X0 @ X0)) @ 
% 1.29/1.47             (u1_struct_0 @ sk_B) @ (u1_struct_0 @ X0))
% 1.29/1.47          | (v2_struct_0 @ sk_A)
% 1.29/1.47          | ~ (m1_pre_topc @ X0 @ sk_A))),
% 1.29/1.47      inference('demod', [status(thm)], ['162', '163', '164'])).
% 1.29/1.47  thf('166', plain,
% 1.29/1.47      ((~ (l1_pre_topc @ sk_A)
% 1.29/1.47        | (v2_struct_0 @ sk_A)
% 1.29/1.47        | (v1_funct_2 @ 
% 1.29/1.47           (k3_tmap_1 @ sk_A @ sk_A @ sk_A @ sk_B @ (k4_tmap_1 @ sk_A @ sk_A)) @ 
% 1.29/1.47           (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 1.29/1.47        | ~ (v2_pre_topc @ sk_A)
% 1.29/1.47        | (v2_struct_0 @ sk_A)
% 1.29/1.47        | ~ (l1_pre_topc @ sk_A))),
% 1.29/1.47      inference('sup-', [status(thm)], ['150', '165'])).
% 1.29/1.47  thf('167', plain, ((l1_pre_topc @ sk_A)),
% 1.29/1.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.47  thf('168', plain, ((v2_pre_topc @ sk_A)),
% 1.29/1.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.47  thf('169', plain, ((l1_pre_topc @ sk_A)),
% 1.29/1.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.47  thf('170', plain,
% 1.29/1.47      (((v2_struct_0 @ sk_A)
% 1.29/1.47        | (v1_funct_2 @ 
% 1.29/1.47           (k3_tmap_1 @ sk_A @ sk_A @ sk_A @ sk_B @ (k4_tmap_1 @ sk_A @ sk_A)) @ 
% 1.29/1.47           (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 1.29/1.47        | (v2_struct_0 @ sk_A))),
% 1.29/1.47      inference('demod', [status(thm)], ['166', '167', '168', '169'])).
% 1.29/1.47  thf('171', plain,
% 1.29/1.47      (((v1_funct_2 @ 
% 1.29/1.47         (k3_tmap_1 @ sk_A @ sk_A @ sk_A @ sk_B @ (k4_tmap_1 @ sk_A @ sk_A)) @ 
% 1.29/1.47         (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 1.29/1.47        | (v2_struct_0 @ sk_A))),
% 1.29/1.47      inference('simplify', [status(thm)], ['170'])).
% 1.29/1.47  thf('172', plain, (~ (v2_struct_0 @ sk_A)),
% 1.29/1.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.47  thf('173', plain,
% 1.29/1.47      ((v1_funct_2 @ 
% 1.29/1.47        (k3_tmap_1 @ sk_A @ sk_A @ sk_A @ sk_B @ (k4_tmap_1 @ sk_A @ sk_A)) @ 
% 1.29/1.47        (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 1.29/1.47      inference('clc', [status(thm)], ['171', '172'])).
% 1.29/1.47  thf('174', plain,
% 1.29/1.47      (((k3_tmap_1 @ sk_A @ sk_A @ sk_A @ sk_B @ (k4_tmap_1 @ sk_A @ sk_A))
% 1.29/1.47         = (k2_tmap_1 @ sk_A @ sk_A @ (k4_tmap_1 @ sk_A @ sk_A) @ sk_B))),
% 1.29/1.47      inference('clc', [status(thm)], ['118', '119'])).
% 1.29/1.47  thf('175', plain,
% 1.29/1.47      ((v1_funct_2 @ 
% 1.29/1.47        (k2_tmap_1 @ sk_A @ sk_A @ (k4_tmap_1 @ sk_A @ sk_A) @ sk_B) @ 
% 1.29/1.47        (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 1.29/1.47      inference('demod', [status(thm)], ['173', '174'])).
% 1.29/1.47  thf('176', plain,
% 1.29/1.47      (![X0 : $i]:
% 1.29/1.47         (~ (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.29/1.47             (k2_tmap_1 @ sk_A @ sk_A @ (k4_tmap_1 @ sk_A @ sk_A) @ sk_B) @ X0)
% 1.29/1.47          | ((k2_tmap_1 @ sk_A @ sk_A @ (k4_tmap_1 @ sk_A @ sk_A) @ sk_B)
% 1.29/1.47              = (X0))
% 1.29/1.47          | ~ (m1_subset_1 @ X0 @ 
% 1.29/1.47               (k1_zfmisc_1 @ 
% 1.29/1.47                (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))
% 1.29/1.47          | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 1.29/1.47          | ~ (v1_funct_1 @ X0))),
% 1.29/1.47      inference('demod', [status(thm)], ['123', '149', '175'])).
% 1.29/1.47  thf('177', plain,
% 1.29/1.47      (((v2_struct_0 @ sk_A)
% 1.29/1.47        | (r2_hidden @ 
% 1.29/1.47           (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ (k4_tmap_1 @ sk_A @ sk_A) @ 
% 1.29/1.47            sk_B @ sk_A @ sk_A) @ 
% 1.29/1.47           (u1_struct_0 @ sk_B))
% 1.29/1.47        | (v2_struct_0 @ sk_B)
% 1.29/1.47        | ~ (v1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_B))
% 1.29/1.47        | ~ (v1_funct_2 @ (k4_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_B) @ 
% 1.29/1.47             (u1_struct_0 @ sk_A))
% 1.29/1.47        | ~ (m1_subset_1 @ (k4_tmap_1 @ sk_A @ sk_B) @ 
% 1.29/1.47             (k1_zfmisc_1 @ 
% 1.29/1.47              (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))
% 1.29/1.47        | ((k2_tmap_1 @ sk_A @ sk_A @ (k4_tmap_1 @ sk_A @ sk_A) @ sk_B)
% 1.29/1.47            = (k4_tmap_1 @ sk_A @ sk_B)))),
% 1.29/1.47      inference('sup-', [status(thm)], ['54', '176'])).
% 1.29/1.47  thf('178', plain, ((v1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_B))),
% 1.29/1.47      inference('clc', [status(thm)], ['33', '34'])).
% 1.29/1.47  thf('179', plain,
% 1.29/1.47      ((v1_funct_2 @ (k4_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_B) @ 
% 1.29/1.47        (u1_struct_0 @ sk_A))),
% 1.29/1.47      inference('clc', [status(thm)], ['41', '42'])).
% 1.29/1.47  thf('180', plain,
% 1.29/1.47      ((m1_subset_1 @ (k4_tmap_1 @ sk_A @ sk_B) @ 
% 1.29/1.47        (k1_zfmisc_1 @ 
% 1.29/1.47         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 1.29/1.47      inference('clc', [status(thm)], ['14', '15'])).
% 1.29/1.47  thf('181', plain,
% 1.29/1.47      (((v2_struct_0 @ sk_A)
% 1.29/1.47        | (r2_hidden @ 
% 1.29/1.47           (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ (k4_tmap_1 @ sk_A @ sk_A) @ 
% 1.29/1.47            sk_B @ sk_A @ sk_A) @ 
% 1.29/1.47           (u1_struct_0 @ sk_B))
% 1.29/1.47        | (v2_struct_0 @ sk_B)
% 1.29/1.47        | ((k2_tmap_1 @ sk_A @ sk_A @ (k4_tmap_1 @ sk_A @ sk_A) @ sk_B)
% 1.29/1.47            = (k4_tmap_1 @ sk_A @ sk_B)))),
% 1.29/1.47      inference('demod', [status(thm)], ['177', '178', '179', '180'])).
% 1.29/1.47  thf('182', plain,
% 1.29/1.47      (![X0 : $i]:
% 1.29/1.47         (~ (v2_pre_topc @ X0)
% 1.29/1.47          | (v2_struct_0 @ X0)
% 1.29/1.47          | (v1_funct_1 @ (k4_tmap_1 @ X0 @ X0))
% 1.29/1.47          | ~ (l1_pre_topc @ X0))),
% 1.29/1.47      inference('simplify', [status(thm)], ['3'])).
% 1.29/1.47  thf('183', plain,
% 1.29/1.47      (![X0 : $i]:
% 1.29/1.47         (~ (v2_pre_topc @ X0)
% 1.29/1.47          | (v2_struct_0 @ X0)
% 1.29/1.47          | (v1_funct_2 @ (k4_tmap_1 @ X0 @ X0) @ (u1_struct_0 @ X0) @ 
% 1.29/1.47             (u1_struct_0 @ X0))
% 1.29/1.47          | ~ (l1_pre_topc @ X0))),
% 1.29/1.47      inference('simplify', [status(thm)], ['7'])).
% 1.29/1.47  thf('184', plain,
% 1.29/1.47      ((m1_subset_1 @ sk_C @ 
% 1.29/1.47        (k1_zfmisc_1 @ 
% 1.29/1.47         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 1.29/1.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.47  thf('185', plain,
% 1.29/1.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.29/1.47         (~ (v1_funct_1 @ (k4_tmap_1 @ X0 @ X0))
% 1.29/1.47          | ~ (v1_funct_2 @ (k4_tmap_1 @ X0 @ X0) @ (u1_struct_0 @ X0) @ 
% 1.29/1.47               (u1_struct_0 @ X0))
% 1.29/1.47          | (r2_hidden @ (sk_F @ X2 @ (k4_tmap_1 @ X0 @ X0) @ X1 @ X0 @ X0) @ 
% 1.29/1.47             (u1_struct_0 @ X1))
% 1.29/1.47          | (r2_funct_2 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ X0) @ 
% 1.29/1.47             (k2_tmap_1 @ X0 @ X0 @ (k4_tmap_1 @ X0 @ X0) @ X1) @ X2)
% 1.29/1.47          | ~ (m1_subset_1 @ X2 @ 
% 1.29/1.47               (k1_zfmisc_1 @ 
% 1.29/1.47                (k2_zfmisc_1 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ X0))))
% 1.29/1.47          | ~ (v1_funct_2 @ X2 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ X0))
% 1.29/1.47          | ~ (v1_funct_1 @ X2)
% 1.29/1.47          | ~ (m1_pre_topc @ X1 @ X0)
% 1.29/1.47          | (v2_struct_0 @ X1)
% 1.29/1.47          | ~ (v2_pre_topc @ X0)
% 1.29/1.47          | (v2_struct_0 @ X0)
% 1.29/1.47          | ~ (l1_pre_topc @ X0))),
% 1.29/1.47      inference('simplify', [status(thm)], ['22'])).
% 1.29/1.47  thf('186', plain,
% 1.29/1.47      ((~ (l1_pre_topc @ sk_A)
% 1.29/1.47        | (v2_struct_0 @ sk_A)
% 1.29/1.47        | ~ (v2_pre_topc @ sk_A)
% 1.29/1.47        | (v2_struct_0 @ sk_B)
% 1.29/1.47        | ~ (m1_pre_topc @ sk_B @ sk_A)
% 1.29/1.47        | ~ (v1_funct_1 @ sk_C)
% 1.29/1.47        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 1.29/1.47        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.29/1.47           (k2_tmap_1 @ sk_A @ sk_A @ (k4_tmap_1 @ sk_A @ sk_A) @ sk_B) @ sk_C)
% 1.29/1.47        | (r2_hidden @ 
% 1.29/1.47           (sk_F @ sk_C @ (k4_tmap_1 @ sk_A @ sk_A) @ sk_B @ sk_A @ sk_A) @ 
% 1.29/1.47           (u1_struct_0 @ sk_B))
% 1.29/1.47        | ~ (v1_funct_2 @ (k4_tmap_1 @ sk_A @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 1.29/1.47             (u1_struct_0 @ sk_A))
% 1.29/1.47        | ~ (v1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_A)))),
% 1.29/1.47      inference('sup-', [status(thm)], ['184', '185'])).
% 1.29/1.47  thf('187', plain, ((l1_pre_topc @ sk_A)),
% 1.29/1.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.47  thf('188', plain, ((v2_pre_topc @ sk_A)),
% 1.29/1.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.47  thf('189', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 1.29/1.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.47  thf('190', plain, ((v1_funct_1 @ sk_C)),
% 1.29/1.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.47  thf('191', plain,
% 1.29/1.47      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 1.29/1.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.47  thf('192', plain,
% 1.29/1.47      (((v2_struct_0 @ sk_A)
% 1.29/1.47        | (v2_struct_0 @ sk_B)
% 1.29/1.47        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.29/1.47           (k2_tmap_1 @ sk_A @ sk_A @ (k4_tmap_1 @ sk_A @ sk_A) @ sk_B) @ sk_C)
% 1.29/1.47        | (r2_hidden @ 
% 1.29/1.47           (sk_F @ sk_C @ (k4_tmap_1 @ sk_A @ sk_A) @ sk_B @ sk_A @ sk_A) @ 
% 1.29/1.47           (u1_struct_0 @ sk_B))
% 1.29/1.47        | ~ (v1_funct_2 @ (k4_tmap_1 @ sk_A @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 1.29/1.47             (u1_struct_0 @ sk_A))
% 1.29/1.47        | ~ (v1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_A)))),
% 1.29/1.47      inference('demod', [status(thm)],
% 1.29/1.47                ['186', '187', '188', '189', '190', '191'])).
% 1.29/1.47  thf('193', plain,
% 1.29/1.47      ((~ (l1_pre_topc @ sk_A)
% 1.29/1.47        | (v2_struct_0 @ sk_A)
% 1.29/1.47        | ~ (v2_pre_topc @ sk_A)
% 1.29/1.47        | ~ (v1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_A))
% 1.29/1.47        | (r2_hidden @ 
% 1.29/1.47           (sk_F @ sk_C @ (k4_tmap_1 @ sk_A @ sk_A) @ sk_B @ sk_A @ sk_A) @ 
% 1.29/1.47           (u1_struct_0 @ sk_B))
% 1.29/1.47        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.29/1.47           (k2_tmap_1 @ sk_A @ sk_A @ (k4_tmap_1 @ sk_A @ sk_A) @ sk_B) @ sk_C)
% 1.29/1.47        | (v2_struct_0 @ sk_B)
% 1.29/1.47        | (v2_struct_0 @ sk_A))),
% 1.29/1.47      inference('sup-', [status(thm)], ['183', '192'])).
% 1.29/1.47  thf('194', plain, ((l1_pre_topc @ sk_A)),
% 1.29/1.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.47  thf('195', plain, ((v2_pre_topc @ sk_A)),
% 1.29/1.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.47  thf('196', plain,
% 1.29/1.47      (((v2_struct_0 @ sk_A)
% 1.29/1.47        | ~ (v1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_A))
% 1.29/1.47        | (r2_hidden @ 
% 1.29/1.47           (sk_F @ sk_C @ (k4_tmap_1 @ sk_A @ sk_A) @ sk_B @ sk_A @ sk_A) @ 
% 1.29/1.47           (u1_struct_0 @ sk_B))
% 1.29/1.47        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.29/1.47           (k2_tmap_1 @ sk_A @ sk_A @ (k4_tmap_1 @ sk_A @ sk_A) @ sk_B) @ sk_C)
% 1.29/1.47        | (v2_struct_0 @ sk_B)
% 1.29/1.47        | (v2_struct_0 @ sk_A))),
% 1.29/1.47      inference('demod', [status(thm)], ['193', '194', '195'])).
% 1.29/1.47  thf('197', plain,
% 1.29/1.47      (((v2_struct_0 @ sk_B)
% 1.29/1.47        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.29/1.47           (k2_tmap_1 @ sk_A @ sk_A @ (k4_tmap_1 @ sk_A @ sk_A) @ sk_B) @ sk_C)
% 1.29/1.47        | (r2_hidden @ 
% 1.29/1.47           (sk_F @ sk_C @ (k4_tmap_1 @ sk_A @ sk_A) @ sk_B @ sk_A @ sk_A) @ 
% 1.29/1.47           (u1_struct_0 @ sk_B))
% 1.29/1.47        | ~ (v1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_A))
% 1.29/1.47        | (v2_struct_0 @ sk_A))),
% 1.29/1.47      inference('simplify', [status(thm)], ['196'])).
% 1.29/1.47  thf('198', plain,
% 1.29/1.47      ((~ (l1_pre_topc @ sk_A)
% 1.29/1.47        | (v2_struct_0 @ sk_A)
% 1.29/1.47        | ~ (v2_pre_topc @ sk_A)
% 1.29/1.47        | (v2_struct_0 @ sk_A)
% 1.29/1.47        | (r2_hidden @ 
% 1.29/1.47           (sk_F @ sk_C @ (k4_tmap_1 @ sk_A @ sk_A) @ sk_B @ sk_A @ sk_A) @ 
% 1.29/1.47           (u1_struct_0 @ sk_B))
% 1.29/1.47        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.29/1.47           (k2_tmap_1 @ sk_A @ sk_A @ (k4_tmap_1 @ sk_A @ sk_A) @ sk_B) @ sk_C)
% 1.29/1.47        | (v2_struct_0 @ sk_B))),
% 1.29/1.47      inference('sup-', [status(thm)], ['182', '197'])).
% 1.29/1.47  thf('199', plain, ((l1_pre_topc @ sk_A)),
% 1.29/1.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.47  thf('200', plain, ((v2_pre_topc @ sk_A)),
% 1.29/1.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.47  thf('201', plain,
% 1.29/1.47      (((v2_struct_0 @ sk_A)
% 1.29/1.47        | (v2_struct_0 @ sk_A)
% 1.29/1.47        | (r2_hidden @ 
% 1.29/1.47           (sk_F @ sk_C @ (k4_tmap_1 @ sk_A @ sk_A) @ sk_B @ sk_A @ sk_A) @ 
% 1.29/1.47           (u1_struct_0 @ sk_B))
% 1.29/1.47        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.29/1.47           (k2_tmap_1 @ sk_A @ sk_A @ (k4_tmap_1 @ sk_A @ sk_A) @ sk_B) @ sk_C)
% 1.29/1.47        | (v2_struct_0 @ sk_B))),
% 1.29/1.47      inference('demod', [status(thm)], ['198', '199', '200'])).
% 1.29/1.47  thf('202', plain,
% 1.29/1.47      (((v2_struct_0 @ sk_B)
% 1.29/1.47        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.29/1.47           (k2_tmap_1 @ sk_A @ sk_A @ (k4_tmap_1 @ sk_A @ sk_A) @ sk_B) @ sk_C)
% 1.29/1.47        | (r2_hidden @ 
% 1.29/1.47           (sk_F @ sk_C @ (k4_tmap_1 @ sk_A @ sk_A) @ sk_B @ sk_A @ sk_A) @ 
% 1.29/1.47           (u1_struct_0 @ sk_B))
% 1.29/1.47        | (v2_struct_0 @ sk_A))),
% 1.29/1.47      inference('simplify', [status(thm)], ['201'])).
% 1.29/1.47  thf('203', plain,
% 1.29/1.47      (![X0 : $i]:
% 1.29/1.47         (~ (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.29/1.47             (k2_tmap_1 @ sk_A @ sk_A @ (k4_tmap_1 @ sk_A @ sk_A) @ sk_B) @ X0)
% 1.29/1.47          | ((k2_tmap_1 @ sk_A @ sk_A @ (k4_tmap_1 @ sk_A @ sk_A) @ sk_B)
% 1.29/1.47              = (X0))
% 1.29/1.47          | ~ (m1_subset_1 @ X0 @ 
% 1.29/1.47               (k1_zfmisc_1 @ 
% 1.29/1.47                (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))
% 1.29/1.47          | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 1.29/1.47          | ~ (v1_funct_1 @ X0))),
% 1.29/1.47      inference('demod', [status(thm)], ['123', '149', '175'])).
% 1.29/1.47  thf('204', plain,
% 1.29/1.47      (((v2_struct_0 @ sk_A)
% 1.29/1.47        | (r2_hidden @ 
% 1.29/1.47           (sk_F @ sk_C @ (k4_tmap_1 @ sk_A @ sk_A) @ sk_B @ sk_A @ sk_A) @ 
% 1.29/1.47           (u1_struct_0 @ sk_B))
% 1.29/1.47        | (v2_struct_0 @ sk_B)
% 1.29/1.47        | ~ (v1_funct_1 @ sk_C)
% 1.29/1.47        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 1.29/1.47        | ~ (m1_subset_1 @ sk_C @ 
% 1.29/1.47             (k1_zfmisc_1 @ 
% 1.29/1.47              (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))
% 1.29/1.47        | ((k2_tmap_1 @ sk_A @ sk_A @ (k4_tmap_1 @ sk_A @ sk_A) @ sk_B)
% 1.29/1.47            = (sk_C)))),
% 1.29/1.47      inference('sup-', [status(thm)], ['202', '203'])).
% 1.29/1.47  thf('205', plain, ((v1_funct_1 @ sk_C)),
% 1.29/1.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.47  thf('206', plain,
% 1.29/1.47      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 1.29/1.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.47  thf('207', plain,
% 1.29/1.47      ((m1_subset_1 @ sk_C @ 
% 1.29/1.47        (k1_zfmisc_1 @ 
% 1.29/1.47         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 1.29/1.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.47  thf('208', plain,
% 1.29/1.47      (((v2_struct_0 @ sk_A)
% 1.29/1.47        | (r2_hidden @ 
% 1.29/1.47           (sk_F @ sk_C @ (k4_tmap_1 @ sk_A @ sk_A) @ sk_B @ sk_A @ sk_A) @ 
% 1.29/1.47           (u1_struct_0 @ sk_B))
% 1.29/1.47        | (v2_struct_0 @ sk_B)
% 1.29/1.47        | ((k2_tmap_1 @ sk_A @ sk_A @ (k4_tmap_1 @ sk_A @ sk_A) @ sk_B)
% 1.29/1.47            = (sk_C)))),
% 1.29/1.47      inference('demod', [status(thm)], ['204', '205', '206', '207'])).
% 1.29/1.47  thf('209', plain,
% 1.29/1.47      ((m1_subset_1 @ (k4_tmap_1 @ sk_A @ sk_B) @ 
% 1.29/1.47        (k1_zfmisc_1 @ 
% 1.29/1.47         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 1.29/1.47      inference('clc', [status(thm)], ['14', '15'])).
% 1.29/1.47  thf('210', plain,
% 1.29/1.47      ((m1_subset_1 @ (k4_tmap_1 @ sk_A @ sk_B) @ 
% 1.29/1.47        (k1_zfmisc_1 @ 
% 1.29/1.47         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 1.29/1.47      inference('clc', [status(thm)], ['14', '15'])).
% 1.29/1.47  thf('211', plain,
% 1.29/1.47      ((m1_subset_1 @ sk_C @ 
% 1.29/1.47        (k1_zfmisc_1 @ 
% 1.29/1.47         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 1.29/1.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.47  thf(d9_funct_2, axiom,
% 1.29/1.47    (![A:$i,B:$i,C:$i]:
% 1.29/1.47     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.29/1.47         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.29/1.47       ( ![D:$i]:
% 1.29/1.47         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 1.29/1.47             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.29/1.47           ( ( r2_funct_2 @ A @ B @ C @ D ) <=>
% 1.29/1.47             ( ![E:$i]:
% 1.29/1.47               ( ( m1_subset_1 @ E @ A ) =>
% 1.29/1.47                 ( ( k1_funct_1 @ C @ E ) = ( k1_funct_1 @ D @ E ) ) ) ) ) ) ) ))).
% 1.29/1.47  thf('212', plain,
% 1.29/1.47      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 1.29/1.47         (~ (v1_funct_1 @ X5)
% 1.29/1.47          | ~ (v1_funct_2 @ X5 @ X6 @ X7)
% 1.29/1.47          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X7)))
% 1.29/1.47          | (m1_subset_1 @ (sk_E @ X5 @ X8 @ X6) @ X6)
% 1.29/1.47          | (r2_funct_2 @ X6 @ X7 @ X8 @ X5)
% 1.29/1.47          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X7)))
% 1.29/1.47          | ~ (v1_funct_2 @ X8 @ X6 @ X7)
% 1.29/1.47          | ~ (v1_funct_1 @ X8))),
% 1.29/1.47      inference('cnf', [status(esa)], [d9_funct_2])).
% 1.29/1.47  thf('213', plain,
% 1.29/1.47      (![X0 : $i]:
% 1.29/1.47         (~ (v1_funct_1 @ X0)
% 1.29/1.47          | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 1.29/1.47          | ~ (m1_subset_1 @ X0 @ 
% 1.29/1.47               (k1_zfmisc_1 @ 
% 1.29/1.47                (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))
% 1.29/1.47          | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ X0 @ 
% 1.29/1.47             sk_C)
% 1.29/1.47          | (m1_subset_1 @ (sk_E @ sk_C @ X0 @ (u1_struct_0 @ sk_B)) @ 
% 1.29/1.47             (u1_struct_0 @ sk_B))
% 1.29/1.47          | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 1.29/1.47          | ~ (v1_funct_1 @ sk_C))),
% 1.29/1.47      inference('sup-', [status(thm)], ['211', '212'])).
% 1.29/1.47  thf('214', plain,
% 1.29/1.47      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 1.29/1.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.47  thf('215', plain, ((v1_funct_1 @ sk_C)),
% 1.29/1.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.47  thf('216', plain,
% 1.29/1.47      (![X0 : $i]:
% 1.29/1.47         (~ (v1_funct_1 @ X0)
% 1.29/1.47          | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 1.29/1.47          | ~ (m1_subset_1 @ X0 @ 
% 1.29/1.47               (k1_zfmisc_1 @ 
% 1.29/1.47                (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))
% 1.29/1.47          | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ X0 @ 
% 1.29/1.47             sk_C)
% 1.29/1.47          | (m1_subset_1 @ (sk_E @ sk_C @ X0 @ (u1_struct_0 @ sk_B)) @ 
% 1.29/1.47             (u1_struct_0 @ sk_B)))),
% 1.29/1.47      inference('demod', [status(thm)], ['213', '214', '215'])).
% 1.29/1.47  thf('217', plain,
% 1.29/1.47      (((m1_subset_1 @ 
% 1.29/1.47         (sk_E @ sk_C @ (k4_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_B)) @ 
% 1.29/1.47         (u1_struct_0 @ sk_B))
% 1.29/1.47        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.29/1.47           (k4_tmap_1 @ sk_A @ sk_B) @ sk_C)
% 1.29/1.47        | ~ (v1_funct_2 @ (k4_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_B) @ 
% 1.29/1.47             (u1_struct_0 @ sk_A))
% 1.29/1.47        | ~ (v1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_B)))),
% 1.29/1.47      inference('sup-', [status(thm)], ['210', '216'])).
% 1.29/1.47  thf('218', plain,
% 1.29/1.47      ((v1_funct_2 @ (k4_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_B) @ 
% 1.29/1.47        (u1_struct_0 @ sk_A))),
% 1.29/1.47      inference('clc', [status(thm)], ['41', '42'])).
% 1.29/1.47  thf('219', plain, ((v1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_B))),
% 1.29/1.47      inference('clc', [status(thm)], ['33', '34'])).
% 1.29/1.47  thf('220', plain,
% 1.29/1.47      (((m1_subset_1 @ 
% 1.29/1.47         (sk_E @ sk_C @ (k4_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_B)) @ 
% 1.29/1.47         (u1_struct_0 @ sk_B))
% 1.29/1.47        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.29/1.47           (k4_tmap_1 @ sk_A @ sk_B) @ sk_C))),
% 1.29/1.47      inference('demod', [status(thm)], ['217', '218', '219'])).
% 1.29/1.47  thf('221', plain,
% 1.29/1.47      (~ (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.29/1.47          (k4_tmap_1 @ sk_A @ sk_B) @ sk_C)),
% 1.29/1.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.47  thf('222', plain,
% 1.29/1.47      ((m1_subset_1 @ 
% 1.29/1.47        (sk_E @ sk_C @ (k4_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_B)) @ 
% 1.29/1.47        (u1_struct_0 @ sk_B))),
% 1.29/1.47      inference('clc', [status(thm)], ['220', '221'])).
% 1.29/1.47  thf(t2_subset, axiom,
% 1.29/1.47    (![A:$i,B:$i]:
% 1.29/1.47     ( ( m1_subset_1 @ A @ B ) =>
% 1.29/1.47       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 1.29/1.47  thf('223', plain,
% 1.29/1.47      (![X0 : $i, X1 : $i]:
% 1.29/1.47         ((r2_hidden @ X0 @ X1)
% 1.29/1.47          | (v1_xboole_0 @ X1)
% 1.29/1.47          | ~ (m1_subset_1 @ X0 @ X1))),
% 1.29/1.47      inference('cnf', [status(esa)], [t2_subset])).
% 1.29/1.47  thf('224', plain,
% 1.29/1.47      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 1.29/1.47        | (r2_hidden @ 
% 1.29/1.47           (sk_E @ sk_C @ (k4_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_B)) @ 
% 1.29/1.47           (u1_struct_0 @ sk_B)))),
% 1.29/1.47      inference('sup-', [status(thm)], ['222', '223'])).
% 1.29/1.47  thf('225', plain,
% 1.29/1.47      (![X55 : $i]:
% 1.29/1.47         (~ (r2_hidden @ X55 @ (u1_struct_0 @ sk_B))
% 1.29/1.47          | ((X55) = (k1_funct_1 @ sk_C @ X55))
% 1.29/1.47          | ~ (m1_subset_1 @ X55 @ (u1_struct_0 @ sk_A)))),
% 1.29/1.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.47  thf('226', plain,
% 1.29/1.47      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 1.29/1.47        | ~ (m1_subset_1 @ 
% 1.29/1.47             (sk_E @ sk_C @ (k4_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_B)) @ 
% 1.29/1.47             (u1_struct_0 @ sk_A))
% 1.29/1.47        | ((sk_E @ sk_C @ (k4_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_B))
% 1.29/1.47            = (k1_funct_1 @ sk_C @ 
% 1.29/1.47               (sk_E @ sk_C @ (k4_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_B)))))),
% 1.29/1.47      inference('sup-', [status(thm)], ['224', '225'])).
% 1.29/1.47  thf('227', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 1.29/1.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.47  thf('228', plain,
% 1.29/1.47      ((m1_subset_1 @ 
% 1.29/1.47        (sk_E @ sk_C @ (k4_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_B)) @ 
% 1.29/1.47        (u1_struct_0 @ sk_B))),
% 1.29/1.47      inference('clc', [status(thm)], ['220', '221'])).
% 1.29/1.47  thf(t55_pre_topc, axiom,
% 1.29/1.47    (![A:$i]:
% 1.29/1.47     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 1.29/1.47       ( ![B:$i]:
% 1.29/1.47         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 1.29/1.47           ( ![C:$i]:
% 1.29/1.47             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ B ) ) =>
% 1.29/1.47               ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) ) ) ) ))).
% 1.29/1.47  thf('229', plain,
% 1.29/1.47      (![X18 : $i, X19 : $i, X20 : $i]:
% 1.29/1.47         ((v2_struct_0 @ X18)
% 1.29/1.47          | ~ (m1_pre_topc @ X18 @ X19)
% 1.29/1.47          | (m1_subset_1 @ X20 @ (u1_struct_0 @ X19))
% 1.29/1.47          | ~ (m1_subset_1 @ X20 @ (u1_struct_0 @ X18))
% 1.29/1.47          | ~ (l1_pre_topc @ X19)
% 1.29/1.47          | (v2_struct_0 @ X19))),
% 1.29/1.47      inference('cnf', [status(esa)], [t55_pre_topc])).
% 1.29/1.47  thf('230', plain,
% 1.29/1.47      (![X0 : $i]:
% 1.29/1.47         ((v2_struct_0 @ X0)
% 1.29/1.47          | ~ (l1_pre_topc @ X0)
% 1.29/1.47          | (m1_subset_1 @ 
% 1.29/1.47             (sk_E @ sk_C @ (k4_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_B)) @ 
% 1.29/1.47             (u1_struct_0 @ X0))
% 1.29/1.47          | ~ (m1_pre_topc @ sk_B @ X0)
% 1.29/1.47          | (v2_struct_0 @ sk_B))),
% 1.29/1.47      inference('sup-', [status(thm)], ['228', '229'])).
% 1.29/1.47  thf('231', plain,
% 1.29/1.47      (((v2_struct_0 @ sk_B)
% 1.29/1.47        | (m1_subset_1 @ 
% 1.29/1.47           (sk_E @ sk_C @ (k4_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_B)) @ 
% 1.29/1.47           (u1_struct_0 @ sk_A))
% 1.29/1.47        | ~ (l1_pre_topc @ sk_A)
% 1.29/1.47        | (v2_struct_0 @ sk_A))),
% 1.29/1.47      inference('sup-', [status(thm)], ['227', '230'])).
% 1.29/1.47  thf('232', plain, ((l1_pre_topc @ sk_A)),
% 1.29/1.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.47  thf('233', plain,
% 1.29/1.47      (((v2_struct_0 @ sk_B)
% 1.29/1.47        | (m1_subset_1 @ 
% 1.29/1.47           (sk_E @ sk_C @ (k4_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_B)) @ 
% 1.29/1.47           (u1_struct_0 @ sk_A))
% 1.29/1.47        | (v2_struct_0 @ sk_A))),
% 1.29/1.47      inference('demod', [status(thm)], ['231', '232'])).
% 1.29/1.47  thf('234', plain, (~ (v2_struct_0 @ sk_B)),
% 1.29/1.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.47  thf('235', plain,
% 1.29/1.47      (((v2_struct_0 @ sk_A)
% 1.29/1.47        | (m1_subset_1 @ 
% 1.29/1.47           (sk_E @ sk_C @ (k4_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_B)) @ 
% 1.29/1.47           (u1_struct_0 @ sk_A)))),
% 1.29/1.47      inference('clc', [status(thm)], ['233', '234'])).
% 1.29/1.47  thf('236', plain, (~ (v2_struct_0 @ sk_A)),
% 1.29/1.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.47  thf('237', plain,
% 1.29/1.47      ((m1_subset_1 @ 
% 1.29/1.47        (sk_E @ sk_C @ (k4_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_B)) @ 
% 1.29/1.47        (u1_struct_0 @ sk_A))),
% 1.29/1.47      inference('clc', [status(thm)], ['235', '236'])).
% 1.29/1.47  thf('238', plain,
% 1.29/1.47      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 1.29/1.47        | ((sk_E @ sk_C @ (k4_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_B))
% 1.29/1.47            = (k1_funct_1 @ sk_C @ 
% 1.29/1.47               (sk_E @ sk_C @ (k4_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_B)))))),
% 1.29/1.47      inference('demod', [status(thm)], ['226', '237'])).
% 1.29/1.47  thf('239', plain,
% 1.29/1.47      ((m1_subset_1 @ 
% 1.29/1.47        (sk_E @ sk_C @ (k4_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_B)) @ 
% 1.29/1.47        (u1_struct_0 @ sk_A))),
% 1.29/1.47      inference('clc', [status(thm)], ['235', '236'])).
% 1.29/1.47  thf('240', plain,
% 1.29/1.47      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 1.29/1.47        | (r2_hidden @ 
% 1.29/1.47           (sk_E @ sk_C @ (k4_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_B)) @ 
% 1.29/1.47           (u1_struct_0 @ sk_B)))),
% 1.29/1.47      inference('sup-', [status(thm)], ['222', '223'])).
% 1.29/1.47  thf(t95_tmap_1, axiom,
% 1.29/1.47    (![A:$i]:
% 1.29/1.47     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.29/1.47       ( ![B:$i]:
% 1.29/1.47         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 1.29/1.47           ( ![C:$i]:
% 1.29/1.47             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 1.29/1.47               ( ( r2_hidden @ C @ ( u1_struct_0 @ B ) ) =>
% 1.29/1.47                 ( ( k1_funct_1 @ ( k4_tmap_1 @ A @ B ) @ C ) = ( C ) ) ) ) ) ) ) ))).
% 1.29/1.47  thf('241', plain,
% 1.29/1.47      (![X52 : $i, X53 : $i, X54 : $i]:
% 1.29/1.47         ((v2_struct_0 @ X52)
% 1.29/1.47          | ~ (m1_pre_topc @ X52 @ X53)
% 1.29/1.47          | ~ (r2_hidden @ X54 @ (u1_struct_0 @ X52))
% 1.29/1.47          | ((k1_funct_1 @ (k4_tmap_1 @ X53 @ X52) @ X54) = (X54))
% 1.29/1.47          | ~ (m1_subset_1 @ X54 @ (u1_struct_0 @ X53))
% 1.29/1.47          | ~ (l1_pre_topc @ X53)
% 1.29/1.47          | ~ (v2_pre_topc @ X53)
% 1.29/1.47          | (v2_struct_0 @ X53))),
% 1.29/1.47      inference('cnf', [status(esa)], [t95_tmap_1])).
% 1.29/1.47  thf('242', plain,
% 1.29/1.47      (![X0 : $i]:
% 1.29/1.47         ((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 1.29/1.47          | (v2_struct_0 @ X0)
% 1.29/1.47          | ~ (v2_pre_topc @ X0)
% 1.29/1.47          | ~ (l1_pre_topc @ X0)
% 1.29/1.47          | ~ (m1_subset_1 @ 
% 1.29/1.47               (sk_E @ sk_C @ (k4_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_B)) @ 
% 1.29/1.47               (u1_struct_0 @ X0))
% 1.29/1.47          | ((k1_funct_1 @ (k4_tmap_1 @ X0 @ sk_B) @ 
% 1.29/1.47              (sk_E @ sk_C @ (k4_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_B)))
% 1.29/1.47              = (sk_E @ sk_C @ (k4_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_B)))
% 1.29/1.47          | ~ (m1_pre_topc @ sk_B @ X0)
% 1.29/1.47          | (v2_struct_0 @ sk_B))),
% 1.29/1.47      inference('sup-', [status(thm)], ['240', '241'])).
% 1.29/1.47  thf('243', plain,
% 1.29/1.47      (((v2_struct_0 @ sk_B)
% 1.29/1.47        | ~ (m1_pre_topc @ sk_B @ sk_A)
% 1.29/1.47        | ((k1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_B) @ 
% 1.29/1.47            (sk_E @ sk_C @ (k4_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_B)))
% 1.29/1.47            = (sk_E @ sk_C @ (k4_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_B)))
% 1.29/1.47        | ~ (l1_pre_topc @ sk_A)
% 1.29/1.47        | ~ (v2_pre_topc @ sk_A)
% 1.29/1.47        | (v2_struct_0 @ sk_A)
% 1.29/1.47        | (v1_xboole_0 @ (u1_struct_0 @ sk_B)))),
% 1.29/1.47      inference('sup-', [status(thm)], ['239', '242'])).
% 1.29/1.47  thf('244', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 1.29/1.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.47  thf('245', plain, ((l1_pre_topc @ sk_A)),
% 1.29/1.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.47  thf('246', plain, ((v2_pre_topc @ sk_A)),
% 1.29/1.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.47  thf('247', plain,
% 1.29/1.47      (((v2_struct_0 @ sk_B)
% 1.29/1.47        | ((k1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_B) @ 
% 1.29/1.47            (sk_E @ sk_C @ (k4_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_B)))
% 1.29/1.47            = (sk_E @ sk_C @ (k4_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_B)))
% 1.29/1.47        | (v2_struct_0 @ sk_A)
% 1.29/1.47        | (v1_xboole_0 @ (u1_struct_0 @ sk_B)))),
% 1.29/1.47      inference('demod', [status(thm)], ['243', '244', '245', '246'])).
% 1.29/1.47  thf('248', plain,
% 1.29/1.47      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 1.29/1.47         (~ (v1_funct_1 @ X5)
% 1.29/1.47          | ~ (v1_funct_2 @ X5 @ X6 @ X7)
% 1.29/1.47          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X7)))
% 1.29/1.47          | ((k1_funct_1 @ X8 @ (sk_E @ X5 @ X8 @ X6))
% 1.29/1.47              != (k1_funct_1 @ X5 @ (sk_E @ X5 @ X8 @ X6)))
% 1.29/1.47          | (r2_funct_2 @ X6 @ X7 @ X8 @ X5)
% 1.29/1.47          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X7)))
% 1.29/1.47          | ~ (v1_funct_2 @ X8 @ X6 @ X7)
% 1.29/1.47          | ~ (v1_funct_1 @ X8))),
% 1.29/1.47      inference('cnf', [status(esa)], [d9_funct_2])).
% 1.29/1.47  thf('249', plain,
% 1.29/1.47      (![X0 : $i]:
% 1.29/1.47         (((sk_E @ sk_C @ (k4_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_B))
% 1.29/1.47            != (k1_funct_1 @ sk_C @ 
% 1.29/1.47                (sk_E @ sk_C @ (k4_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_B))))
% 1.29/1.47          | (v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 1.29/1.47          | (v2_struct_0 @ sk_A)
% 1.29/1.47          | (v2_struct_0 @ sk_B)
% 1.29/1.47          | ~ (v1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_B))
% 1.29/1.47          | ~ (v1_funct_2 @ (k4_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_B) @ 
% 1.29/1.47               X0)
% 1.29/1.47          | ~ (m1_subset_1 @ (k4_tmap_1 @ sk_A @ sk_B) @ 
% 1.29/1.47               (k1_zfmisc_1 @ (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ X0)))
% 1.29/1.47          | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ X0 @ 
% 1.29/1.47             (k4_tmap_1 @ sk_A @ sk_B) @ sk_C)
% 1.29/1.47          | ~ (m1_subset_1 @ sk_C @ 
% 1.29/1.47               (k1_zfmisc_1 @ (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ X0)))
% 1.29/1.47          | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B) @ X0)
% 1.29/1.47          | ~ (v1_funct_1 @ sk_C))),
% 1.29/1.47      inference('sup-', [status(thm)], ['247', '248'])).
% 1.29/1.47  thf('250', plain, ((v1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_B))),
% 1.29/1.47      inference('clc', [status(thm)], ['33', '34'])).
% 1.29/1.47  thf('251', plain, ((v1_funct_1 @ sk_C)),
% 1.29/1.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.47  thf('252', plain,
% 1.29/1.47      (![X0 : $i]:
% 1.29/1.47         (((sk_E @ sk_C @ (k4_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_B))
% 1.29/1.47            != (k1_funct_1 @ sk_C @ 
% 1.29/1.47                (sk_E @ sk_C @ (k4_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_B))))
% 1.29/1.47          | (v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 1.29/1.47          | (v2_struct_0 @ sk_A)
% 1.29/1.47          | (v2_struct_0 @ sk_B)
% 1.29/1.47          | ~ (v1_funct_2 @ (k4_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_B) @ 
% 1.29/1.47               X0)
% 1.29/1.47          | ~ (m1_subset_1 @ (k4_tmap_1 @ sk_A @ sk_B) @ 
% 1.29/1.47               (k1_zfmisc_1 @ (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ X0)))
% 1.29/1.47          | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ X0 @ 
% 1.29/1.47             (k4_tmap_1 @ sk_A @ sk_B) @ sk_C)
% 1.29/1.47          | ~ (m1_subset_1 @ sk_C @ 
% 1.29/1.47               (k1_zfmisc_1 @ (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ X0)))
% 1.29/1.47          | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B) @ X0))),
% 1.29/1.47      inference('demod', [status(thm)], ['249', '250', '251'])).
% 1.29/1.47  thf('253', plain,
% 1.29/1.47      (![X0 : $i]:
% 1.29/1.47         (((sk_E @ sk_C @ (k4_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_B))
% 1.29/1.47            != (sk_E @ sk_C @ (k4_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_B)))
% 1.29/1.47          | (v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 1.29/1.47          | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B) @ X0)
% 1.29/1.47          | ~ (m1_subset_1 @ sk_C @ 
% 1.29/1.47               (k1_zfmisc_1 @ (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ X0)))
% 1.29/1.47          | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ X0 @ 
% 1.29/1.47             (k4_tmap_1 @ sk_A @ sk_B) @ sk_C)
% 1.29/1.47          | ~ (m1_subset_1 @ (k4_tmap_1 @ sk_A @ sk_B) @ 
% 1.29/1.47               (k1_zfmisc_1 @ (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ X0)))
% 1.29/1.47          | ~ (v1_funct_2 @ (k4_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_B) @ 
% 1.29/1.47               X0)
% 1.29/1.47          | (v2_struct_0 @ sk_B)
% 1.29/1.47          | (v2_struct_0 @ sk_A)
% 1.29/1.47          | (v1_xboole_0 @ (u1_struct_0 @ sk_B)))),
% 1.29/1.47      inference('sup-', [status(thm)], ['238', '252'])).
% 1.29/1.47  thf('254', plain,
% 1.29/1.47      (![X0 : $i]:
% 1.29/1.47         ((v2_struct_0 @ sk_A)
% 1.29/1.47          | (v2_struct_0 @ sk_B)
% 1.29/1.47          | ~ (v1_funct_2 @ (k4_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_B) @ 
% 1.29/1.47               X0)
% 1.29/1.47          | ~ (m1_subset_1 @ (k4_tmap_1 @ sk_A @ sk_B) @ 
% 1.29/1.47               (k1_zfmisc_1 @ (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ X0)))
% 1.29/1.47          | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ X0 @ 
% 1.29/1.47             (k4_tmap_1 @ sk_A @ sk_B) @ sk_C)
% 1.29/1.47          | ~ (m1_subset_1 @ sk_C @ 
% 1.29/1.47               (k1_zfmisc_1 @ (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ X0)))
% 1.29/1.47          | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B) @ X0)
% 1.29/1.47          | (v1_xboole_0 @ (u1_struct_0 @ sk_B)))),
% 1.29/1.47      inference('simplify', [status(thm)], ['253'])).
% 1.29/1.47  thf('255', plain,
% 1.29/1.47      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 1.29/1.47        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 1.29/1.47        | ~ (m1_subset_1 @ sk_C @ 
% 1.29/1.47             (k1_zfmisc_1 @ 
% 1.29/1.47              (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))
% 1.29/1.47        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.29/1.47           (k4_tmap_1 @ sk_A @ sk_B) @ sk_C)
% 1.29/1.47        | ~ (v1_funct_2 @ (k4_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_B) @ 
% 1.29/1.47             (u1_struct_0 @ sk_A))
% 1.29/1.47        | (v2_struct_0 @ sk_B)
% 1.29/1.47        | (v2_struct_0 @ sk_A))),
% 1.29/1.47      inference('sup-', [status(thm)], ['209', '254'])).
% 1.29/1.47  thf('256', plain,
% 1.29/1.47      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 1.29/1.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.47  thf('257', plain,
% 1.29/1.47      ((m1_subset_1 @ sk_C @ 
% 1.29/1.47        (k1_zfmisc_1 @ 
% 1.29/1.47         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 1.29/1.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.47  thf('258', plain,
% 1.29/1.47      ((v1_funct_2 @ (k4_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_B) @ 
% 1.29/1.47        (u1_struct_0 @ sk_A))),
% 1.29/1.47      inference('clc', [status(thm)], ['41', '42'])).
% 1.29/1.47  thf('259', plain,
% 1.29/1.47      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 1.29/1.47        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.29/1.47           (k4_tmap_1 @ sk_A @ sk_B) @ sk_C)
% 1.29/1.47        | (v2_struct_0 @ sk_B)
% 1.29/1.47        | (v2_struct_0 @ sk_A))),
% 1.29/1.47      inference('demod', [status(thm)], ['255', '256', '257', '258'])).
% 1.29/1.47  thf('260', plain,
% 1.29/1.47      (~ (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.29/1.47          (k4_tmap_1 @ sk_A @ sk_B) @ sk_C)),
% 1.29/1.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.47  thf('261', plain,
% 1.29/1.47      (((v2_struct_0 @ sk_A)
% 1.29/1.47        | (v2_struct_0 @ sk_B)
% 1.29/1.47        | (v1_xboole_0 @ (u1_struct_0 @ sk_B)))),
% 1.29/1.47      inference('sup-', [status(thm)], ['259', '260'])).
% 1.29/1.47  thf('262', plain, (~ (v2_struct_0 @ sk_A)),
% 1.29/1.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.47  thf('263', plain,
% 1.29/1.47      (((v1_xboole_0 @ (u1_struct_0 @ sk_B)) | (v2_struct_0 @ sk_B))),
% 1.29/1.47      inference('clc', [status(thm)], ['261', '262'])).
% 1.29/1.47  thf('264', plain, (~ (v2_struct_0 @ sk_B)),
% 1.29/1.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.47  thf('265', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_B))),
% 1.29/1.47      inference('clc', [status(thm)], ['263', '264'])).
% 1.29/1.47  thf('266', plain,
% 1.29/1.47      (![X39 : $i]: ((m1_pre_topc @ X39 @ X39) | ~ (l1_pre_topc @ X39))),
% 1.29/1.47      inference('cnf', [status(esa)], [t2_tsep_1])).
% 1.29/1.47  thf(t1_tsep_1, axiom,
% 1.29/1.47    (![A:$i]:
% 1.29/1.47     ( ( l1_pre_topc @ A ) =>
% 1.29/1.47       ( ![B:$i]:
% 1.29/1.47         ( ( m1_pre_topc @ B @ A ) =>
% 1.29/1.47           ( m1_subset_1 @
% 1.29/1.47             ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 1.29/1.47  thf('267', plain,
% 1.29/1.47      (![X37 : $i, X38 : $i]:
% 1.29/1.47         (~ (m1_pre_topc @ X37 @ X38)
% 1.29/1.47          | (m1_subset_1 @ (u1_struct_0 @ X37) @ 
% 1.29/1.47             (k1_zfmisc_1 @ (u1_struct_0 @ X38)))
% 1.29/1.47          | ~ (l1_pre_topc @ X38))),
% 1.29/1.47      inference('cnf', [status(esa)], [t1_tsep_1])).
% 1.29/1.47  thf('268', plain,
% 1.29/1.47      (![X0 : $i]:
% 1.29/1.47         (~ (l1_pre_topc @ X0)
% 1.29/1.47          | ~ (l1_pre_topc @ X0)
% 1.29/1.47          | (m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 1.29/1.47             (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 1.29/1.47      inference('sup-', [status(thm)], ['266', '267'])).
% 1.29/1.47  thf('269', plain,
% 1.29/1.47      (![X0 : $i]:
% 1.29/1.47         ((m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 1.29/1.47           (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 1.29/1.47          | ~ (l1_pre_topc @ X0))),
% 1.29/1.47      inference('simplify', [status(thm)], ['268'])).
% 1.29/1.47  thf(t5_subset, axiom,
% 1.29/1.47    (![A:$i,B:$i,C:$i]:
% 1.29/1.47     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 1.29/1.47          ( v1_xboole_0 @ C ) ) ))).
% 1.29/1.47  thf('270', plain,
% 1.29/1.47      (![X2 : $i, X3 : $i, X4 : $i]:
% 1.29/1.47         (~ (r2_hidden @ X2 @ X3)
% 1.29/1.47          | ~ (v1_xboole_0 @ X4)
% 1.29/1.47          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4)))),
% 1.29/1.47      inference('cnf', [status(esa)], [t5_subset])).
% 1.29/1.47  thf('271', plain,
% 1.29/1.47      (![X0 : $i, X1 : $i]:
% 1.29/1.47         (~ (l1_pre_topc @ X0)
% 1.29/1.47          | ~ (v1_xboole_0 @ (u1_struct_0 @ X0))
% 1.29/1.47          | ~ (r2_hidden @ X1 @ (u1_struct_0 @ X0)))),
% 1.29/1.47      inference('sup-', [status(thm)], ['269', '270'])).
% 1.29/1.47  thf('272', plain,
% 1.29/1.47      (![X0 : $i]:
% 1.29/1.47         (~ (r2_hidden @ X0 @ (u1_struct_0 @ sk_B)) | ~ (l1_pre_topc @ sk_B))),
% 1.29/1.47      inference('sup-', [status(thm)], ['265', '271'])).
% 1.29/1.47  thf('273', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 1.29/1.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.47  thf(dt_m1_pre_topc, axiom,
% 1.29/1.47    (![A:$i]:
% 1.29/1.47     ( ( l1_pre_topc @ A ) =>
% 1.29/1.47       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 1.29/1.47  thf('274', plain,
% 1.29/1.47      (![X16 : $i, X17 : $i]:
% 1.29/1.47         (~ (m1_pre_topc @ X16 @ X17)
% 1.29/1.47          | (l1_pre_topc @ X16)
% 1.29/1.47          | ~ (l1_pre_topc @ X17))),
% 1.29/1.47      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 1.29/1.47  thf('275', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_B))),
% 1.29/1.47      inference('sup-', [status(thm)], ['273', '274'])).
% 1.29/1.47  thf('276', plain, ((l1_pre_topc @ sk_A)),
% 1.29/1.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.47  thf('277', plain, ((l1_pre_topc @ sk_B)),
% 1.29/1.47      inference('demod', [status(thm)], ['275', '276'])).
% 1.29/1.47  thf('278', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ (u1_struct_0 @ sk_B))),
% 1.29/1.47      inference('demod', [status(thm)], ['272', '277'])).
% 1.29/1.47  thf('279', plain,
% 1.29/1.47      ((((k2_tmap_1 @ sk_A @ sk_A @ (k4_tmap_1 @ sk_A @ sk_A) @ sk_B) = (sk_C))
% 1.29/1.47        | (v2_struct_0 @ sk_B)
% 1.29/1.47        | (v2_struct_0 @ sk_A))),
% 1.29/1.47      inference('sup-', [status(thm)], ['208', '278'])).
% 1.29/1.47  thf('280', plain, (~ (v2_struct_0 @ sk_B)),
% 1.29/1.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.47  thf('281', plain,
% 1.29/1.47      (((v2_struct_0 @ sk_A)
% 1.29/1.47        | ((k2_tmap_1 @ sk_A @ sk_A @ (k4_tmap_1 @ sk_A @ sk_A) @ sk_B)
% 1.29/1.47            = (sk_C)))),
% 1.29/1.47      inference('clc', [status(thm)], ['279', '280'])).
% 1.29/1.47  thf('282', plain, (~ (v2_struct_0 @ sk_A)),
% 1.29/1.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.47  thf('283', plain,
% 1.29/1.47      (((k2_tmap_1 @ sk_A @ sk_A @ (k4_tmap_1 @ sk_A @ sk_A) @ sk_B) = (sk_C))),
% 1.29/1.47      inference('clc', [status(thm)], ['281', '282'])).
% 1.29/1.47  thf('284', plain,
% 1.29/1.47      (((v2_struct_0 @ sk_A)
% 1.29/1.47        | (r2_hidden @ 
% 1.29/1.47           (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ (k4_tmap_1 @ sk_A @ sk_A) @ 
% 1.29/1.47            sk_B @ sk_A @ sk_A) @ 
% 1.29/1.47           (u1_struct_0 @ sk_B))
% 1.29/1.47        | (v2_struct_0 @ sk_B)
% 1.29/1.47        | ((sk_C) = (k4_tmap_1 @ sk_A @ sk_B)))),
% 1.29/1.47      inference('demod', [status(thm)], ['181', '283'])).
% 1.29/1.47  thf('285', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ (u1_struct_0 @ sk_B))),
% 1.29/1.47      inference('demod', [status(thm)], ['272', '277'])).
% 1.29/1.47  thf('286', plain,
% 1.29/1.47      ((((sk_C) = (k4_tmap_1 @ sk_A @ sk_B))
% 1.29/1.47        | (v2_struct_0 @ sk_B)
% 1.29/1.47        | (v2_struct_0 @ sk_A))),
% 1.29/1.47      inference('sup-', [status(thm)], ['284', '285'])).
% 1.29/1.47  thf('287', plain, (~ (v2_struct_0 @ sk_B)),
% 1.29/1.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.47  thf('288', plain,
% 1.29/1.47      (((v2_struct_0 @ sk_A) | ((sk_C) = (k4_tmap_1 @ sk_A @ sk_B)))),
% 1.29/1.47      inference('clc', [status(thm)], ['286', '287'])).
% 1.29/1.47  thf('289', plain, (~ (v2_struct_0 @ sk_A)),
% 1.29/1.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.47  thf('290', plain, (((sk_C) = (k4_tmap_1 @ sk_A @ sk_B))),
% 1.29/1.47      inference('clc', [status(thm)], ['288', '289'])).
% 1.29/1.47  thf('291', plain,
% 1.29/1.47      ((m1_subset_1 @ sk_C @ 
% 1.29/1.47        (k1_zfmisc_1 @ 
% 1.29/1.47         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 1.29/1.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.47  thf('292', plain,
% 1.29/1.47      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 1.29/1.47         (~ (v1_funct_1 @ X5)
% 1.29/1.47          | ~ (v1_funct_2 @ X5 @ X6 @ X7)
% 1.29/1.47          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X7)))
% 1.29/1.47          | ((k1_funct_1 @ X8 @ (sk_E @ X5 @ X8 @ X6))
% 1.29/1.47              != (k1_funct_1 @ X5 @ (sk_E @ X5 @ X8 @ X6)))
% 1.29/1.47          | (r2_funct_2 @ X6 @ X7 @ X8 @ X5)
% 1.29/1.47          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X7)))
% 1.29/1.47          | ~ (v1_funct_2 @ X8 @ X6 @ X7)
% 1.29/1.47          | ~ (v1_funct_1 @ X8))),
% 1.29/1.47      inference('cnf', [status(esa)], [d9_funct_2])).
% 1.29/1.47  thf('293', plain,
% 1.29/1.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.29/1.47         (~ (v1_funct_1 @ X0)
% 1.29/1.47          | ~ (v1_funct_2 @ X0 @ X2 @ X1)
% 1.29/1.47          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 1.29/1.47          | (r2_funct_2 @ X2 @ X1 @ X0 @ X0)
% 1.29/1.47          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 1.29/1.47          | ~ (v1_funct_2 @ X0 @ X2 @ X1)
% 1.29/1.47          | ~ (v1_funct_1 @ X0))),
% 1.29/1.47      inference('eq_res', [status(thm)], ['292'])).
% 1.29/1.47  thf('294', plain,
% 1.29/1.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.29/1.47         ((r2_funct_2 @ X2 @ X1 @ X0 @ X0)
% 1.29/1.47          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 1.29/1.47          | ~ (v1_funct_2 @ X0 @ X2 @ X1)
% 1.29/1.47          | ~ (v1_funct_1 @ X0))),
% 1.29/1.47      inference('simplify', [status(thm)], ['293'])).
% 1.29/1.47  thf('295', plain,
% 1.29/1.47      ((~ (v1_funct_1 @ sk_C)
% 1.29/1.47        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 1.29/1.47        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 1.29/1.47           sk_C))),
% 1.29/1.47      inference('sup-', [status(thm)], ['291', '294'])).
% 1.29/1.47  thf('296', plain, ((v1_funct_1 @ sk_C)),
% 1.29/1.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.47  thf('297', plain,
% 1.29/1.47      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 1.29/1.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.47  thf('298', plain,
% 1.29/1.47      ((r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ sk_C)),
% 1.29/1.47      inference('demod', [status(thm)], ['295', '296', '297'])).
% 1.29/1.47  thf('299', plain, ($false),
% 1.29/1.47      inference('demod', [status(thm)], ['0', '290', '298'])).
% 1.29/1.47  
% 1.29/1.47  % SZS output end Refutation
% 1.29/1.47  
% 1.29/1.47  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
