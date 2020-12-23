%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.HsaP56n8x0

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:10:42 EST 2020

% Result     : Theorem 2.05s
% Output     : Refutation 2.05s
% Verified   : 
% Statistics : Number of formulae       :  374 (10663 expanded)
%              Number of leaves         :   40 (3123 expanded)
%              Depth                    :   43
%              Number of atoms          : 5293 (281844 expanded)
%              Number of equality atoms :   75 (5406 expanded)
%              Maximal formula depth    :   25 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k3_funct_2_type,type,(
    k3_funct_2: $i > $i > $i > $i > $i )).

thf(k2_partfun1_type,type,(
    k2_partfun1: $i > $i > $i > $i > $i )).

thf(k3_tmap_1_type,type,(
    k3_tmap_1: $i > $i > $i > $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k2_tmap_1_type,type,(
    k2_tmap_1: $i > $i > $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_F_type,type,(
    sk_F: $i > $i > $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k4_tmap_1_type,type,(
    k4_tmap_1: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(r2_funct_2_type,type,(
    r2_funct_2: $i > $i > $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

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
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( m1_pre_topc @ A @ A ) ) )).

thf('1',plain,(
    ! [X35: $i] :
      ( ( m1_pre_topc @ X35 @ X35 )
      | ~ ( l1_pre_topc @ X35 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('2',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,(
    ! [X35: $i] :
      ( ( m1_pre_topc @ X35 @ X35 )
      | ~ ( l1_pre_topc @ X35 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('4',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k4_tmap_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_pre_topc @ B @ A ) )
     => ( ( v1_funct_1 @ ( k4_tmap_1 @ A @ B ) )
        & ( v1_funct_2 @ ( k4_tmap_1 @ A @ B ) @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) )
        & ( m1_subset_1 @ ( k4_tmap_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) ) )).

thf('5',plain,(
    ! [X33: $i,X34: $i] :
      ( ~ ( l1_pre_topc @ X33 )
      | ~ ( v2_pre_topc @ X33 )
      | ( v2_struct_0 @ X33 )
      | ~ ( m1_pre_topc @ X34 @ X33 )
      | ( m1_subset_1 @ ( k4_tmap_1 @ X33 @ X34 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X34 ) @ ( u1_struct_0 @ X33 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k4_tmap_1])).

thf('6',plain,
    ( ( m1_subset_1 @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( m1_subset_1 @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['6','7','8'])).

thf('10',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    m1_subset_1 @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['9','10'])).

thf('12',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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

thf('13',plain,(
    ! [X36: $i,X37: $i,X38: $i,X39: $i,X40: $i] :
      ( ( v2_struct_0 @ X36 )
      | ~ ( v2_pre_topc @ X36 )
      | ~ ( l1_pre_topc @ X36 )
      | ~ ( v1_funct_1 @ X37 )
      | ~ ( v1_funct_2 @ X37 @ ( u1_struct_0 @ X36 ) @ ( u1_struct_0 @ X38 ) )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X36 ) @ ( u1_struct_0 @ X38 ) ) ) )
      | ( m1_subset_1 @ ( sk_F @ X39 @ X37 @ X40 @ X36 @ X38 ) @ ( u1_struct_0 @ X36 ) )
      | ( r2_funct_2 @ ( u1_struct_0 @ X40 ) @ ( u1_struct_0 @ X38 ) @ ( k2_tmap_1 @ X36 @ X38 @ X37 @ X40 ) @ X39 )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X40 ) @ ( u1_struct_0 @ X38 ) ) ) )
      | ~ ( v1_funct_2 @ X39 @ ( u1_struct_0 @ X40 ) @ ( u1_struct_0 @ X38 ) )
      | ~ ( v1_funct_1 @ X39 )
      | ~ ( m1_pre_topc @ X40 @ X36 )
      | ( v2_struct_0 @ X40 )
      | ~ ( l1_pre_topc @ X38 )
      | ~ ( v2_pre_topc @ X38 )
      | ( v2_struct_0 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t59_tmap_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ) )
      | ( r2_funct_2 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ X0 ) @ X1 )
      | ( m1_subset_1 @ ( sk_F @ X1 @ sk_C @ X0 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('20',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( m1_pre_topc @ X13 @ X14 )
      | ( l1_pre_topc @ X13 )
      | ~ ( l1_pre_topc @ X14 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('21',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( v2_pre_topc @ B ) ) ) )).

thf('25',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( m1_pre_topc @ X10 @ X11 )
      | ( v2_pre_topc @ X10 )
      | ~ ( l1_pre_topc @ X11 )
      | ~ ( v2_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[cc1_pre_topc])).

thf('26',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    v2_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['26','27','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ) )
      | ( r2_funct_2 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ X0 ) @ X1 )
      | ( m1_subset_1 @ ( sk_F @ X1 @ sk_C @ X0 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['14','15','16','17','18','23','29'])).

thf('31',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( m1_subset_1 @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B ) @ ( k4_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( v1_funct_2 @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( m1_pre_topc @ sk_B @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['11','30'])).

thf('32',plain,(
    ! [X35: $i] :
      ( ( m1_pre_topc @ X35 @ X35 )
      | ~ ( l1_pre_topc @ X35 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('33',plain,(
    ! [X35: $i] :
      ( ( m1_pre_topc @ X35 @ X35 )
      | ~ ( l1_pre_topc @ X35 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('34',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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

thf('35',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ~ ( m1_pre_topc @ X28 @ X29 )
      | ~ ( m1_pre_topc @ X30 @ X29 )
      | ~ ( l1_pre_topc @ X31 )
      | ~ ( v2_pre_topc @ X31 )
      | ( v2_struct_0 @ X31 )
      | ~ ( l1_pre_topc @ X29 )
      | ~ ( v2_pre_topc @ X29 )
      | ( v2_struct_0 @ X29 )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( v1_funct_2 @ X32 @ ( u1_struct_0 @ X30 ) @ ( u1_struct_0 @ X31 ) )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X30 ) @ ( u1_struct_0 @ X31 ) ) ) )
      | ( m1_subset_1 @ ( k3_tmap_1 @ X29 @ X31 @ X30 @ X28 @ X32 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X28 ) @ ( u1_struct_0 @ X31 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_tmap_1])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( k3_tmap_1 @ X1 @ sk_A @ sk_B @ X0 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ) )
      | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_1 @ sk_C )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_pre_topc @ sk_B @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( k3_tmap_1 @ X1 @ sk_A @ sk_B @ X0 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( m1_pre_topc @ sk_B @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['36','37','38','39','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_B )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ( v2_struct_0 @ sk_B )
      | ( m1_subset_1 @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_B @ X0 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['33','41'])).

thf('43',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['21','22'])).

thf('44',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['21','22'])).

thf('45',plain,(
    v2_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['26','27','28'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( m1_subset_1 @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_B @ X0 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['42','43','44','45'])).

thf('47',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( m1_subset_1 @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_B @ sk_B @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['32','46'])).

thf('48',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['21','22'])).

thf('49',plain,
    ( ( m1_subset_1 @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_B @ sk_B @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_B @ sk_B @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(clc,[status(thm)],['49','50'])).

thf('52',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    m1_subset_1 @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_B @ sk_B @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['51','52'])).

thf('54',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
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

thf('55',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) )
      | ~ ( v1_funct_2 @ X6 @ X7 @ X8 )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_funct_2 @ X9 @ X7 @ X8 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) )
      | ( X6 = X9 )
      | ~ ( r2_funct_2 @ X7 @ X8 @ X6 @ X9 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_funct_2])).

thf('56',plain,(
    ! [X0: $i] :
      ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ X0 )
      | ( sk_C = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) )
      | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    ! [X0: $i] :
      ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ X0 )
      | ( sk_C = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) )
      | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['56','57','58'])).

thf('60',plain,
    ( ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_B @ sk_B @ sk_C ) )
    | ~ ( v1_funct_2 @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_B @ sk_B @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( sk_C
      = ( k3_tmap_1 @ sk_B @ sk_A @ sk_B @ sk_B @ sk_C ) )
    | ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_B @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['53','59'])).

thf('61',plain,(
    ! [X35: $i] :
      ( ( m1_pre_topc @ X35 @ X35 )
      | ~ ( l1_pre_topc @ X35 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('62',plain,(
    ! [X35: $i] :
      ( ( m1_pre_topc @ X35 @ X35 )
      | ~ ( l1_pre_topc @ X35 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('63',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ~ ( m1_pre_topc @ X28 @ X29 )
      | ~ ( m1_pre_topc @ X30 @ X29 )
      | ~ ( l1_pre_topc @ X31 )
      | ~ ( v2_pre_topc @ X31 )
      | ( v2_struct_0 @ X31 )
      | ~ ( l1_pre_topc @ X29 )
      | ~ ( v2_pre_topc @ X29 )
      | ( v2_struct_0 @ X29 )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( v1_funct_2 @ X32 @ ( u1_struct_0 @ X30 ) @ ( u1_struct_0 @ X31 ) )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X30 ) @ ( u1_struct_0 @ X31 ) ) ) )
      | ( v1_funct_1 @ ( k3_tmap_1 @ X29 @ X31 @ X30 @ X28 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_tmap_1])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_1 @ ( k3_tmap_1 @ X1 @ sk_A @ sk_B @ X0 @ sk_C ) )
      | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_1 @ sk_C )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_pre_topc @ sk_B @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_1 @ ( k3_tmap_1 @ X1 @ sk_A @ sk_B @ X0 @ sk_C ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( m1_pre_topc @ sk_B @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['65','66','67','68','69'])).

thf('71',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_B )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ( v2_struct_0 @ sk_B )
      | ( v1_funct_1 @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_B @ X0 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['62','70'])).

thf('72',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['21','22'])).

thf('73',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['21','22'])).

thf('74',plain,(
    v2_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['26','27','28'])).

thf('75',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( v1_funct_1 @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_B @ X0 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['71','72','73','74'])).

thf('76',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( v1_funct_1 @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_B @ sk_B @ sk_C ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['61','75'])).

thf('77',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['21','22'])).

thf('78',plain,
    ( ( v1_funct_1 @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_B @ sk_B @ sk_C ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('79',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v1_funct_1 @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_B @ sk_B @ sk_C ) ) ),
    inference(clc,[status(thm)],['78','79'])).

thf('81',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    v1_funct_1 @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_B @ sk_B @ sk_C ) ),
    inference(clc,[status(thm)],['80','81'])).

thf('83',plain,
    ( ~ ( v1_funct_2 @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_B @ sk_B @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( sk_C
      = ( k3_tmap_1 @ sk_B @ sk_A @ sk_B @ sk_B @ sk_C ) )
    | ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_B @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['60','82'])).

thf('84',plain,(
    ! [X35: $i] :
      ( ( m1_pre_topc @ X35 @ X35 )
      | ~ ( l1_pre_topc @ X35 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('85',plain,(
    ! [X35: $i] :
      ( ( m1_pre_topc @ X35 @ X35 )
      | ~ ( l1_pre_topc @ X35 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('86',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ~ ( m1_pre_topc @ X28 @ X29 )
      | ~ ( m1_pre_topc @ X30 @ X29 )
      | ~ ( l1_pre_topc @ X31 )
      | ~ ( v2_pre_topc @ X31 )
      | ( v2_struct_0 @ X31 )
      | ~ ( l1_pre_topc @ X29 )
      | ~ ( v2_pre_topc @ X29 )
      | ( v2_struct_0 @ X29 )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( v1_funct_2 @ X32 @ ( u1_struct_0 @ X30 ) @ ( u1_struct_0 @ X31 ) )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X30 ) @ ( u1_struct_0 @ X31 ) ) ) )
      | ( v1_funct_2 @ ( k3_tmap_1 @ X29 @ X31 @ X30 @ X28 @ X32 ) @ ( u1_struct_0 @ X28 ) @ ( u1_struct_0 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_tmap_1])).

thf('88',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_2 @ ( k3_tmap_1 @ X1 @ sk_A @ sk_B @ X0 @ sk_C ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_1 @ sk_C )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_pre_topc @ sk_B @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_2 @ ( k3_tmap_1 @ X1 @ sk_A @ sk_B @ X0 @ sk_C ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( m1_pre_topc @ sk_B @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['88','89','90','91','92'])).

thf('94',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_B )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ( v2_struct_0 @ sk_B )
      | ( v1_funct_2 @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_B @ X0 @ sk_C ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['85','93'])).

thf('95',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['21','22'])).

thf('96',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['21','22'])).

thf('97',plain,(
    v2_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['26','27','28'])).

thf('98',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( v1_funct_2 @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_B @ X0 @ sk_C ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['94','95','96','97'])).

thf('99',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( v1_funct_2 @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_B @ sk_B @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['84','98'])).

thf('100',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['21','22'])).

thf('101',plain,
    ( ( v1_funct_2 @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_B @ sk_B @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['99','100'])).

thf('102',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v1_funct_2 @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_B @ sk_B @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['101','102'])).

thf('104',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,(
    v1_funct_2 @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_B @ sk_B @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['103','104'])).

thf('106',plain,
    ( ( sk_C
      = ( k3_tmap_1 @ sk_B @ sk_A @ sk_B @ sk_B @ sk_C ) )
    | ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_B @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['83','105'])).

thf('107',plain,(
    ! [X35: $i] :
      ( ( m1_pre_topc @ X35 @ X35 )
      | ~ ( l1_pre_topc @ X35 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('108',plain,(
    ! [X35: $i] :
      ( ( m1_pre_topc @ X35 @ X35 )
      | ~ ( l1_pre_topc @ X35 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('109',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
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

thf('110',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ( v2_struct_0 @ X23 )
      | ~ ( v2_pre_topc @ X23 )
      | ~ ( l1_pre_topc @ X23 )
      | ~ ( m1_pre_topc @ X24 @ X25 )
      | ~ ( m1_pre_topc @ X24 @ X26 )
      | ( ( k3_tmap_1 @ X25 @ X23 @ X26 @ X24 @ X27 )
        = ( k2_partfun1 @ ( u1_struct_0 @ X26 ) @ ( u1_struct_0 @ X23 ) @ X27 @ ( u1_struct_0 @ X24 ) ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X26 ) @ ( u1_struct_0 @ X23 ) ) ) )
      | ~ ( v1_funct_2 @ X27 @ ( u1_struct_0 @ X26 ) @ ( u1_struct_0 @ X23 ) )
      | ~ ( v1_funct_1 @ X27 )
      | ~ ( m1_pre_topc @ X26 @ X25 )
      | ~ ( l1_pre_topc @ X25 )
      | ~ ( v2_pre_topc @ X25 )
      | ( v2_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d5_tmap_1])).

thf('111',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ sk_B @ X0 )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
      | ( ( k3_tmap_1 @ X0 @ sk_A @ sk_B @ X1 @ sk_C )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( m1_pre_topc @ X1 @ sk_B )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['109','110'])).

thf('112',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ sk_B @ X0 )
      | ( ( k3_tmap_1 @ X0 @ sk_A @ sk_B @ X1 @ sk_C )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( m1_pre_topc @ X1 @ sk_B )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['111','112','113','114','115'])).

thf('117',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ( ( k3_tmap_1 @ sk_B @ sk_A @ sk_B @ X0 @ sk_C )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['108','116'])).

thf('118',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['21','22'])).

thf('119',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['21','22'])).

thf('120',plain,(
    v2_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['26','27','28'])).

thf('121',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ( ( k3_tmap_1 @ sk_B @ sk_A @ sk_B @ X0 @ sk_C )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( u1_struct_0 @ X0 ) ) )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['117','118','119','120'])).

thf('122',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( ( k3_tmap_1 @ sk_B @ sk_A @ sk_B @ X0 @ sk_C )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['121'])).

thf('123',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( ( k3_tmap_1 @ sk_B @ sk_A @ sk_B @ sk_B @ sk_C )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( u1_struct_0 @ sk_B ) ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['107','122'])).

thf('124',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['21','22'])).

thf('125',plain,(
    ! [X35: $i] :
      ( ( m1_pre_topc @ X35 @ X35 )
      | ~ ( l1_pre_topc @ X35 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('126',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
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

thf('127',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ( v2_struct_0 @ X19 )
      | ~ ( v2_pre_topc @ X19 )
      | ~ ( l1_pre_topc @ X19 )
      | ~ ( m1_pre_topc @ X20 @ X21 )
      | ( ( k2_tmap_1 @ X21 @ X19 @ X22 @ X20 )
        = ( k2_partfun1 @ ( u1_struct_0 @ X21 ) @ ( u1_struct_0 @ X19 ) @ X22 @ ( u1_struct_0 @ X20 ) ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X21 ) @ ( u1_struct_0 @ X19 ) ) ) )
      | ~ ( v1_funct_2 @ X22 @ ( u1_struct_0 @ X21 ) @ ( u1_struct_0 @ X19 ) )
      | ~ ( v1_funct_1 @ X22 )
      | ~ ( l1_pre_topc @ X21 )
      | ~ ( v2_pre_topc @ X21 )
      | ( v2_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d4_tmap_1])).

thf('128',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
      | ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ X0 )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['126','127'])).

thf('129',plain,(
    v2_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['26','27','28'])).

thf('130',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['21','22'])).

thf('131',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('132',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('133',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('134',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('135',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ X0 )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['128','129','130','131','132','133','134'])).

thf('136',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( u1_struct_0 @ sk_B ) ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['125','135'])).

thf('137',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['21','22'])).

thf('138',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( u1_struct_0 @ sk_B ) ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['136','137'])).

thf('139',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('140',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['138','139'])).

thf('141',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('142',plain,
    ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B )
    = ( k2_partfun1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['140','141'])).

thf('143',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k3_tmap_1 @ sk_B @ sk_A @ sk_B @ sk_B @ sk_C )
      = ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['123','124','142'])).

thf('144',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('145',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k3_tmap_1 @ sk_B @ sk_A @ sk_B @ sk_B @ sk_C )
      = ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B ) ) ),
    inference(clc,[status(thm)],['143','144'])).

thf('146',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('147',plain,
    ( ( k3_tmap_1 @ sk_B @ sk_A @ sk_B @ sk_B @ sk_C )
    = ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B ) ),
    inference(clc,[status(thm)],['145','146'])).

thf('148',plain,
    ( ( k3_tmap_1 @ sk_B @ sk_A @ sk_B @ sk_B @ sk_C )
    = ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B ) ),
    inference(clc,[status(thm)],['145','146'])).

thf('149',plain,
    ( ( sk_C
      = ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B ) )
    | ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B ) ) ),
    inference(demod,[status(thm)],['106','147','148'])).

thf('150',plain,(
    ! [X35: $i] :
      ( ( m1_pre_topc @ X35 @ X35 )
      | ~ ( l1_pre_topc @ X35 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('151',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t74_tmap_1,axiom,(
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
                  ( ( ( v1_funct_1 @ D )
                    & ( v1_funct_2 @ D @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) )
                    & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) )
                 => ( r2_funct_2 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ D @ ( k3_tmap_1 @ A @ B @ C @ C @ D ) ) ) ) ) ) )).

thf('152',plain,(
    ! [X41: $i,X42: $i,X43: $i,X44: $i] :
      ( ( v2_struct_0 @ X41 )
      | ~ ( v2_pre_topc @ X41 )
      | ~ ( l1_pre_topc @ X41 )
      | ~ ( v1_funct_1 @ X42 )
      | ~ ( v1_funct_2 @ X42 @ ( u1_struct_0 @ X43 ) @ ( u1_struct_0 @ X41 ) )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X43 ) @ ( u1_struct_0 @ X41 ) ) ) )
      | ( r2_funct_2 @ ( u1_struct_0 @ X43 ) @ ( u1_struct_0 @ X41 ) @ X42 @ ( k3_tmap_1 @ X44 @ X41 @ X43 @ X43 @ X42 ) )
      | ~ ( m1_pre_topc @ X43 @ X44 )
      | ( v2_struct_0 @ X43 )
      | ~ ( l1_pre_topc @ X44 )
      | ~ ( v2_pre_topc @ X44 )
      | ( v2_struct_0 @ X44 ) ) ),
    inference(cnf,[status(esa)],[t74_tmap_1])).

thf('153',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ sk_B @ X0 )
      | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k3_tmap_1 @ X0 @ sk_A @ sk_B @ sk_B @ sk_C ) )
      | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['151','152'])).

thf('154',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('155',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('156',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('157',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('158',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ sk_B @ X0 )
      | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k3_tmap_1 @ X0 @ sk_A @ sk_B @ sk_B @ sk_C ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['153','154','155','156','157'])).

thf('159',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_B @ sk_B @ sk_C ) )
    | ( v2_struct_0 @ sk_B )
    | ~ ( l1_pre_topc @ sk_B )
    | ~ ( v2_pre_topc @ sk_B )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['150','158'])).

thf('160',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['21','22'])).

thf('161',plain,
    ( ( k3_tmap_1 @ sk_B @ sk_A @ sk_B @ sk_B @ sk_C )
    = ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B ) ),
    inference(clc,[status(thm)],['145','146'])).

thf('162',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['21','22'])).

thf('163',plain,(
    v2_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['26','27','28'])).

thf('164',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['159','160','161','162','163'])).

thf('165',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['164'])).

thf('166',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('167',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B ) ) ),
    inference(clc,[status(thm)],['165','166'])).

thf('168',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('169',plain,(
    r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B ) ),
    inference(clc,[status(thm)],['167','168'])).

thf('170',plain,
    ( sk_C
    = ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['149','169'])).

thf('171',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('172',plain,(
    ! [X33: $i,X34: $i] :
      ( ~ ( l1_pre_topc @ X33 )
      | ~ ( v2_pre_topc @ X33 )
      | ( v2_struct_0 @ X33 )
      | ~ ( m1_pre_topc @ X34 @ X33 )
      | ( v1_funct_2 @ ( k4_tmap_1 @ X33 @ X34 ) @ ( u1_struct_0 @ X34 ) @ ( u1_struct_0 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k4_tmap_1])).

thf('173',plain,
    ( ( v1_funct_2 @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['171','172'])).

thf('174',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('175',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('176',plain,
    ( ( v1_funct_2 @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['173','174','175'])).

thf('177',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('178',plain,(
    v1_funct_2 @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['176','177'])).

thf('179',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('180',plain,(
    ! [X33: $i,X34: $i] :
      ( ~ ( l1_pre_topc @ X33 )
      | ~ ( v2_pre_topc @ X33 )
      | ( v2_struct_0 @ X33 )
      | ~ ( m1_pre_topc @ X34 @ X33 )
      | ( v1_funct_1 @ ( k4_tmap_1 @ X33 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k4_tmap_1])).

thf('181',plain,
    ( ( v1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['179','180'])).

thf('182',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('183',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('184',plain,
    ( ( v1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['181','182','183'])).

thf('185',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('186',plain,(
    v1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['184','185'])).

thf('187',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( m1_subset_1 @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( m1_pre_topc @ sk_B @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['31','170','178','186'])).

thf('188',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( m1_pre_topc @ sk_B @ sk_B )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) )
    | ( m1_subset_1 @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(simplify,[status(thm)],['187'])).

thf('189',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( m1_subset_1 @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['3','188'])).

thf('190',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['21','22'])).

thf('191',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( m1_subset_1 @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['189','190'])).

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

thf('192',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( v2_struct_0 @ X16 )
      | ~ ( m1_pre_topc @ X16 @ X17 )
      | ( m1_subset_1 @ X18 @ ( u1_struct_0 @ X17 ) )
      | ~ ( m1_subset_1 @ X18 @ ( u1_struct_0 @ X16 ) )
      | ~ ( l1_pre_topc @ X17 )
      | ( v2_struct_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t55_pre_topc])).

thf('193',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_subset_1 @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['191','192'])).

thf('194',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ sk_B @ X0 )
      | ( m1_subset_1 @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['193'])).

thf('195',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( m1_subset_1 @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['2','194'])).

thf('196',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('197',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['195','196'])).

thf('198',plain,
    ( ( m1_subset_1 @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['197'])).

thf('199',plain,(
    ! [X35: $i] :
      ( ( m1_pre_topc @ X35 @ X35 )
      | ~ ( l1_pre_topc @ X35 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('200',plain,(
    m1_subset_1 @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['9','10'])).

thf('201',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('202',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('203',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( k3_tmap_1 @ X1 @ sk_A @ sk_B @ X0 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( m1_pre_topc @ sk_B @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['36','37','38','39','40'])).

thf('204',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_A @ sk_B @ X0 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['202','203'])).

thf('205',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('206',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('207',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_A @ sk_B @ X0 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['204','205','206'])).

thf('208',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_A @ sk_B @ X0 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['207'])).

thf('209',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('210',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_A @ sk_B @ X0 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ) ) ) ),
    inference(clc,[status(thm)],['208','209'])).

thf('211',plain,(
    m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_A @ sk_B @ sk_B @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['201','210'])).

thf('212',plain,(
    ! [X36: $i,X37: $i,X38: $i,X39: $i,X40: $i] :
      ( ( v2_struct_0 @ X36 )
      | ~ ( v2_pre_topc @ X36 )
      | ~ ( l1_pre_topc @ X36 )
      | ~ ( v1_funct_1 @ X37 )
      | ~ ( v1_funct_2 @ X37 @ ( u1_struct_0 @ X36 ) @ ( u1_struct_0 @ X38 ) )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X36 ) @ ( u1_struct_0 @ X38 ) ) ) )
      | ( r2_hidden @ ( sk_F @ X39 @ X37 @ X40 @ X36 @ X38 ) @ ( u1_struct_0 @ X40 ) )
      | ( r2_funct_2 @ ( u1_struct_0 @ X40 ) @ ( u1_struct_0 @ X38 ) @ ( k2_tmap_1 @ X36 @ X38 @ X37 @ X40 ) @ X39 )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X40 ) @ ( u1_struct_0 @ X38 ) ) ) )
      | ~ ( v1_funct_2 @ X39 @ ( u1_struct_0 @ X40 ) @ ( u1_struct_0 @ X38 ) )
      | ~ ( v1_funct_1 @ X39 )
      | ~ ( m1_pre_topc @ X40 @ X36 )
      | ( v2_struct_0 @ X40 )
      | ~ ( l1_pre_topc @ X38 )
      | ~ ( v2_pre_topc @ X38 )
      | ( v2_struct_0 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t59_tmap_1])).

thf('213',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ) )
      | ( r2_funct_2 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tmap_1 @ sk_B @ sk_A @ ( k3_tmap_1 @ sk_A @ sk_A @ sk_B @ sk_B @ sk_C ) @ X0 ) @ X1 )
      | ( r2_hidden @ ( sk_F @ X1 @ ( k3_tmap_1 @ sk_A @ sk_A @ sk_B @ sk_B @ sk_C ) @ X0 @ sk_B @ sk_A ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_A @ sk_B @ sk_B @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_A @ sk_B @ sk_B @ sk_C ) )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['211','212'])).

thf('214',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('215',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('216',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('217',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('218',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_1 @ ( k3_tmap_1 @ X1 @ sk_A @ sk_B @ X0 @ sk_C ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( m1_pre_topc @ sk_B @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['65','66','67','68','69'])).

thf('219',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_A @ sk_B @ X0 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['217','218'])).

thf('220',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('221',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('222',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_A @ sk_B @ X0 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['219','220','221'])).

thf('223',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_A @ sk_B @ X0 @ sk_C ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['222'])).

thf('224',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('225',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_A @ sk_B @ X0 @ sk_C ) ) ) ),
    inference(clc,[status(thm)],['223','224'])).

thf('226',plain,(
    v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_A @ sk_B @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['216','225'])).

thf('227',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['21','22'])).

thf('228',plain,(
    v2_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['26','27','28'])).

thf('229',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ) )
      | ( r2_funct_2 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tmap_1 @ sk_B @ sk_A @ ( k3_tmap_1 @ sk_A @ sk_A @ sk_B @ sk_B @ sk_C ) @ X0 ) @ X1 )
      | ( r2_hidden @ ( sk_F @ X1 @ ( k3_tmap_1 @ sk_A @ sk_A @ sk_B @ sk_B @ sk_C ) @ X0 @ sk_B @ sk_A ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_A @ sk_B @ sk_B @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['213','214','215','226','227','228'])).

thf('230',plain,(
    ! [X35: $i] :
      ( ( m1_pre_topc @ X35 @ X35 )
      | ~ ( l1_pre_topc @ X35 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('231',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('232',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ sk_B @ X0 )
      | ( ( k3_tmap_1 @ X0 @ sk_A @ sk_B @ X1 @ sk_C )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( m1_pre_topc @ X1 @ sk_B )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['111','112','113','114','115'])).

thf('233',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ( ( k3_tmap_1 @ sk_A @ sk_A @ sk_B @ X0 @ sk_C )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['231','232'])).

thf('234',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('235',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('236',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ( ( k3_tmap_1 @ sk_A @ sk_A @ sk_B @ X0 @ sk_C )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( u1_struct_0 @ X0 ) ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['233','234','235'])).

thf('237',plain,(
    ! [X0: $i] :
      ( ( ( k3_tmap_1 @ sk_A @ sk_A @ sk_B @ X0 @ sk_C )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['236'])).

thf('238',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ~ ( m1_pre_topc @ sk_B @ sk_A )
    | ( ( k3_tmap_1 @ sk_A @ sk_A @ sk_B @ sk_B @ sk_C )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['230','237'])).

thf('239',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['21','22'])).

thf('240',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('241',plain,
    ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B )
    = ( k2_partfun1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['140','141'])).

thf('242',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k3_tmap_1 @ sk_A @ sk_A @ sk_B @ sk_B @ sk_C )
      = ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B ) ) ),
    inference(demod,[status(thm)],['238','239','240','241'])).

thf('243',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('244',plain,
    ( ( k3_tmap_1 @ sk_A @ sk_A @ sk_B @ sk_B @ sk_C )
    = ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B ) ),
    inference(clc,[status(thm)],['242','243'])).

thf('245',plain,
    ( sk_C
    = ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['149','169'])).

thf('246',plain,
    ( ( k3_tmap_1 @ sk_A @ sk_A @ sk_B @ sk_B @ sk_C )
    = sk_C ),
    inference(demod,[status(thm)],['244','245'])).

thf('247',plain,
    ( ( k3_tmap_1 @ sk_A @ sk_A @ sk_B @ sk_B @ sk_C )
    = sk_C ),
    inference(demod,[status(thm)],['244','245'])).

thf('248',plain,
    ( ( k3_tmap_1 @ sk_A @ sk_A @ sk_B @ sk_B @ sk_C )
    = sk_C ),
    inference(demod,[status(thm)],['244','245'])).

thf('249',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('250',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ) )
      | ( r2_funct_2 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ X0 ) @ X1 )
      | ( r2_hidden @ ( sk_F @ X1 @ sk_C @ X0 @ sk_B @ sk_A ) @ ( u1_struct_0 @ X0 ) )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['229','246','247','248','249'])).

thf('251',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( r2_hidden @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B ) @ ( k4_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( v1_funct_2 @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( m1_pre_topc @ sk_B @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['200','250'])).

thf('252',plain,
    ( sk_C
    = ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['149','169'])).

thf('253',plain,(
    v1_funct_2 @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['176','177'])).

thf('254',plain,(
    v1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['184','185'])).

thf('255',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( r2_hidden @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( m1_pre_topc @ sk_B @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['251','252','253','254'])).

thf('256',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( m1_pre_topc @ sk_B @ sk_B )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) )
    | ( r2_hidden @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(simplify,[status(thm)],['255'])).

thf('257',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( r2_hidden @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['199','256'])).

thf('258',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['21','22'])).

thf('259',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( r2_hidden @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['257','258'])).

thf('260',plain,(
    ! [X51: $i] :
      ( ~ ( r2_hidden @ X51 @ ( u1_struct_0 @ sk_B ) )
      | ( X51
        = ( k1_funct_1 @ sk_C @ X51 ) )
      | ~ ( m1_subset_1 @ X51 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('261',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ~ ( m1_subset_1 @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A )
      = ( k1_funct_1 @ sk_C @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['259','260'])).

thf('262',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A )
      = ( k1_funct_1 @ sk_C @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A ) ) )
    | ( v2_struct_0 @ sk_B )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['198','261'])).

thf('263',plain,
    ( ( ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A )
      = ( k1_funct_1 @ sk_C @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A ) ) )
    | ( v2_struct_0 @ sk_B )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['262'])).

thf('264',plain,
    ( ( m1_subset_1 @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['197'])).

thf('265',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( r2_hidden @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['257','258'])).

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

thf('266',plain,(
    ! [X48: $i,X49: $i,X50: $i] :
      ( ( v2_struct_0 @ X48 )
      | ~ ( m1_pre_topc @ X48 @ X49 )
      | ~ ( r2_hidden @ X50 @ ( u1_struct_0 @ X48 ) )
      | ( ( k1_funct_1 @ ( k4_tmap_1 @ X49 @ X48 ) @ X50 )
        = X50 )
      | ~ ( m1_subset_1 @ X50 @ ( u1_struct_0 @ X49 ) )
      | ~ ( l1_pre_topc @ X49 )
      | ~ ( v2_pre_topc @ X49 )
      | ( v2_struct_0 @ X49 ) ) ),
    inference(cnf,[status(esa)],[t95_tmap_1])).

thf('267',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_subset_1 @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A ) @ ( u1_struct_0 @ X0 ) )
      | ( ( k1_funct_1 @ ( k4_tmap_1 @ X0 @ sk_B ) @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A ) )
        = ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A ) )
      | ~ ( m1_pre_topc @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['265','266'])).

thf('268',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ sk_B @ X0 )
      | ( ( k1_funct_1 @ ( k4_tmap_1 @ X0 @ sk_B ) @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A ) )
        = ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A ) )
      | ~ ( m1_subset_1 @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['267'])).

thf('269',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A ) )
      = ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A ) )
    | ~ ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['264','268'])).

thf('270',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('271',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('272',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('273',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( ( k1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A ) )
      = ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['269','270','271','272'])).

thf('274',plain,
    ( ( ( k1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A ) )
      = ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['273'])).

thf('275',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( m1_subset_1 @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['189','190'])).

thf('276',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k3_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ A ) )
     => ( ( k3_funct_2 @ A @ B @ C @ D )
        = ( k1_funct_1 @ C @ D ) ) ) )).

thf('277',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) ) )
      | ~ ( v1_funct_2 @ X2 @ X3 @ X4 )
      | ~ ( v1_funct_1 @ X2 )
      | ( v1_xboole_0 @ X3 )
      | ~ ( m1_subset_1 @ X5 @ X3 )
      | ( ( k3_funct_2 @ X3 @ X4 @ X2 @ X5 )
        = ( k1_funct_1 @ X2 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k3_funct_2])).

thf('278',plain,(
    ! [X0: $i] :
      ( ( ( k3_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ X0 )
        = ( k1_funct_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['276','277'])).

thf('279',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('280',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('281',plain,(
    ! [X0: $i] :
      ( ( ( k3_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ X0 )
        = ( k1_funct_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['278','279','280'])).

thf('282',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( ( k3_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A ) )
      = ( k1_funct_1 @ sk_C @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['275','281'])).

thf('283',plain,(
    ! [X36: $i,X37: $i,X38: $i,X39: $i,X40: $i] :
      ( ( v2_struct_0 @ X36 )
      | ~ ( v2_pre_topc @ X36 )
      | ~ ( l1_pre_topc @ X36 )
      | ~ ( v1_funct_1 @ X37 )
      | ~ ( v1_funct_2 @ X37 @ ( u1_struct_0 @ X36 ) @ ( u1_struct_0 @ X38 ) )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X36 ) @ ( u1_struct_0 @ X38 ) ) ) )
      | ( ( k3_funct_2 @ ( u1_struct_0 @ X36 ) @ ( u1_struct_0 @ X38 ) @ X37 @ ( sk_F @ X39 @ X37 @ X40 @ X36 @ X38 ) )
       != ( k1_funct_1 @ X39 @ ( sk_F @ X39 @ X37 @ X40 @ X36 @ X38 ) ) )
      | ( r2_funct_2 @ ( u1_struct_0 @ X40 ) @ ( u1_struct_0 @ X38 ) @ ( k2_tmap_1 @ X36 @ X38 @ X37 @ X40 ) @ X39 )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X40 ) @ ( u1_struct_0 @ X38 ) ) ) )
      | ~ ( v1_funct_2 @ X39 @ ( u1_struct_0 @ X40 ) @ ( u1_struct_0 @ X38 ) )
      | ~ ( v1_funct_1 @ X39 )
      | ~ ( m1_pre_topc @ X40 @ X36 )
      | ( v2_struct_0 @ X40 )
      | ~ ( l1_pre_topc @ X38 )
      | ~ ( v2_pre_topc @ X38 )
      | ( v2_struct_0 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t59_tmap_1])).

thf('284',plain,
    ( ( ( k1_funct_1 @ sk_C @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A ) )
     != ( k1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ~ ( m1_pre_topc @ sk_B @ sk_B )
    | ~ ( v1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( v1_funct_2 @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( m1_subset_1 @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B ) @ ( k4_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( l1_pre_topc @ sk_B )
    | ~ ( v2_pre_topc @ sk_B )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['282','283'])).

thf('285',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('286',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('287',plain,(
    v1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['184','185'])).

thf('288',plain,(
    v1_funct_2 @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['176','177'])).

thf('289',plain,(
    m1_subset_1 @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['9','10'])).

thf('290',plain,
    ( sk_C
    = ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['149','169'])).

thf('291',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('292',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('293',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('294',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['21','22'])).

thf('295',plain,(
    v2_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['26','27','28'])).

thf('296',plain,
    ( ( ( k1_funct_1 @ sk_C @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A ) )
     != ( k1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ~ ( m1_pre_topc @ sk_B @ sk_B )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['284','285','286','287','288','289','290','291','292','293','294','295'])).

thf('297',plain,
    ( ~ ( m1_pre_topc @ sk_B @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( ( k1_funct_1 @ sk_C @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A ) )
     != ( k1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['296'])).

thf('298',plain,
    ( ( ( k1_funct_1 @ sk_C @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A ) )
     != ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( m1_pre_topc @ sk_B @ sk_B ) ),
    inference('sup-',[status(thm)],['274','297'])).

thf('299',plain,
    ( ~ ( m1_pre_topc @ sk_B @ sk_B )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( ( k1_funct_1 @ sk_C @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A ) )
     != ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A ) ) ),
    inference(simplify,[status(thm)],['298'])).

thf('300',plain,
    ( ( ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A )
     != ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ~ ( m1_pre_topc @ sk_B @ sk_B ) ),
    inference('sup-',[status(thm)],['263','299'])).

thf('301',plain,
    ( ~ ( m1_pre_topc @ sk_B @ sk_B )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['300'])).

thf('302',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['1','301'])).

thf('303',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['21','22'])).

thf('304',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['302','303'])).

thf('305',plain,(
    m1_subset_1 @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['9','10'])).

thf('306',plain,(
    ! [X0: $i] :
      ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ X0 )
      | ( sk_C = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) )
      | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['56','57','58'])).

thf('307',plain,
    ( ~ ( v1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( v1_funct_2 @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( sk_C
      = ( k4_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['305','306'])).

thf('308',plain,(
    v1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['184','185'])).

thf('309',plain,(
    v1_funct_2 @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['176','177'])).

thf('310',plain,
    ( ( sk_C
      = ( k4_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['307','308','309'])).

thf('311',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( sk_C
      = ( k4_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['304','310'])).

thf('312',plain,(
    ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('313',plain,
    ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['311','312'])).

thf('314',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('315',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) )
      | ~ ( v1_funct_2 @ X6 @ X7 @ X8 )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_funct_2 @ X9 @ X7 @ X8 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) )
      | ( r2_funct_2 @ X7 @ X8 @ X6 @ X9 )
      | ( X6 != X9 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_funct_2])).

thf('316',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( r2_funct_2 @ X7 @ X8 @ X9 @ X9 )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_funct_2 @ X9 @ X7 @ X8 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ) ) ),
    inference(simplify,[status(thm)],['315'])).

thf('317',plain,
    ( ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ sk_C ) ),
    inference('sup-',[status(thm)],['314','316'])).

thf('318',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('319',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('320',plain,(
    r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ sk_C ),
    inference(demod,[status(thm)],['317','318','319'])).

thf('321',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['313','320'])).

thf('322',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('323',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['321','322'])).

thf('324',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('325',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['323','324'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('326',plain,(
    ! [X15: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X15 ) )
      | ~ ( l1_struct_0 @ X15 )
      | ( v2_struct_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('327',plain,
    ( ( v2_struct_0 @ sk_B )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['325','326'])).

thf('328',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['21','22'])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('329',plain,(
    ! [X12: $i] :
      ( ( l1_struct_0 @ X12 )
      | ~ ( l1_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('330',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['328','329'])).

thf('331',plain,(
    v2_struct_0 @ sk_B ),
    inference(demod,[status(thm)],['327','330'])).

thf('332',plain,(
    $false ),
    inference(demod,[status(thm)],['0','331'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.HsaP56n8x0
% 0.14/0.34  % Computer   : n006.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:28:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 2.05/2.28  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 2.05/2.28  % Solved by: fo/fo7.sh
% 2.05/2.28  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.05/2.28  % done 2608 iterations in 1.839s
% 2.05/2.28  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 2.05/2.28  % SZS output start Refutation
% 2.05/2.28  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 2.05/2.28  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 2.05/2.28  thf(k3_funct_2_type, type, k3_funct_2: $i > $i > $i > $i > $i).
% 2.05/2.28  thf(k2_partfun1_type, type, k2_partfun1: $i > $i > $i > $i > $i).
% 2.05/2.28  thf(k3_tmap_1_type, type, k3_tmap_1: $i > $i > $i > $i > $i > $i).
% 2.05/2.28  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 2.05/2.28  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 2.05/2.28  thf(k2_tmap_1_type, type, k2_tmap_1: $i > $i > $i > $i > $i).
% 2.05/2.28  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 2.05/2.28  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 2.05/2.28  thf(sk_F_type, type, sk_F: $i > $i > $i > $i > $i > $i).
% 2.05/2.28  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 2.05/2.28  thf(sk_B_type, type, sk_B: $i).
% 2.05/2.28  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 2.05/2.28  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 2.05/2.28  thf(k4_tmap_1_type, type, k4_tmap_1: $i > $i > $i).
% 2.05/2.28  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 2.05/2.28  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 2.05/2.28  thf(r2_funct_2_type, type, r2_funct_2: $i > $i > $i > $i > $o).
% 2.05/2.28  thf(sk_C_type, type, sk_C: $i).
% 2.05/2.28  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 2.05/2.28  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 2.05/2.28  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 2.05/2.28  thf(sk_A_type, type, sk_A: $i).
% 2.05/2.28  thf(t96_tmap_1, conjecture,
% 2.05/2.28    (![A:$i]:
% 2.05/2.28     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 2.05/2.28       ( ![B:$i]:
% 2.05/2.28         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 2.05/2.28           ( ![C:$i]:
% 2.05/2.28             ( ( ( v1_funct_1 @ C ) & 
% 2.05/2.28                 ( v1_funct_2 @ C @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 2.05/2.28                 ( m1_subset_1 @
% 2.05/2.28                   C @ 
% 2.05/2.28                   ( k1_zfmisc_1 @
% 2.05/2.28                     ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 2.05/2.28               ( ( ![D:$i]:
% 2.05/2.28                   ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 2.05/2.28                     ( ( r2_hidden @ D @ ( u1_struct_0 @ B ) ) =>
% 2.05/2.28                       ( ( D ) = ( k1_funct_1 @ C @ D ) ) ) ) ) =>
% 2.05/2.28                 ( r2_funct_2 @
% 2.05/2.28                   ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 2.05/2.28                   ( k4_tmap_1 @ A @ B ) @ C ) ) ) ) ) ) ))).
% 2.05/2.28  thf(zf_stmt_0, negated_conjecture,
% 2.05/2.28    (~( ![A:$i]:
% 2.05/2.28        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 2.05/2.28            ( l1_pre_topc @ A ) ) =>
% 2.05/2.28          ( ![B:$i]:
% 2.05/2.28            ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 2.05/2.28              ( ![C:$i]:
% 2.05/2.28                ( ( ( v1_funct_1 @ C ) & 
% 2.05/2.28                    ( v1_funct_2 @
% 2.05/2.28                      C @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 2.05/2.28                    ( m1_subset_1 @
% 2.05/2.28                      C @ 
% 2.05/2.28                      ( k1_zfmisc_1 @
% 2.05/2.28                        ( k2_zfmisc_1 @
% 2.05/2.28                          ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 2.05/2.28                  ( ( ![D:$i]:
% 2.05/2.28                      ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 2.05/2.28                        ( ( r2_hidden @ D @ ( u1_struct_0 @ B ) ) =>
% 2.05/2.28                          ( ( D ) = ( k1_funct_1 @ C @ D ) ) ) ) ) =>
% 2.05/2.28                    ( r2_funct_2 @
% 2.05/2.28                      ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 2.05/2.28                      ( k4_tmap_1 @ A @ B ) @ C ) ) ) ) ) ) ) )),
% 2.05/2.28    inference('cnf.neg', [status(esa)], [t96_tmap_1])).
% 2.05/2.28  thf('0', plain, (~ (v2_struct_0 @ sk_B)),
% 2.05/2.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.05/2.28  thf(t2_tsep_1, axiom,
% 2.05/2.28    (![A:$i]: ( ( l1_pre_topc @ A ) => ( m1_pre_topc @ A @ A ) ))).
% 2.05/2.28  thf('1', plain,
% 2.05/2.28      (![X35 : $i]: ((m1_pre_topc @ X35 @ X35) | ~ (l1_pre_topc @ X35))),
% 2.05/2.28      inference('cnf', [status(esa)], [t2_tsep_1])).
% 2.05/2.28  thf('2', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 2.05/2.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.05/2.28  thf('3', plain,
% 2.05/2.28      (![X35 : $i]: ((m1_pre_topc @ X35 @ X35) | ~ (l1_pre_topc @ X35))),
% 2.05/2.28      inference('cnf', [status(esa)], [t2_tsep_1])).
% 2.05/2.28  thf('4', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 2.05/2.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.05/2.28  thf(dt_k4_tmap_1, axiom,
% 2.05/2.28    (![A:$i,B:$i]:
% 2.05/2.28     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 2.05/2.28         ( l1_pre_topc @ A ) & ( m1_pre_topc @ B @ A ) ) =>
% 2.05/2.28       ( ( v1_funct_1 @ ( k4_tmap_1 @ A @ B ) ) & 
% 2.05/2.28         ( v1_funct_2 @
% 2.05/2.28           ( k4_tmap_1 @ A @ B ) @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 2.05/2.28         ( m1_subset_1 @
% 2.05/2.28           ( k4_tmap_1 @ A @ B ) @ 
% 2.05/2.28           ( k1_zfmisc_1 @
% 2.05/2.28             ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 2.05/2.28  thf('5', plain,
% 2.05/2.28      (![X33 : $i, X34 : $i]:
% 2.05/2.28         (~ (l1_pre_topc @ X33)
% 2.05/2.28          | ~ (v2_pre_topc @ X33)
% 2.05/2.28          | (v2_struct_0 @ X33)
% 2.05/2.28          | ~ (m1_pre_topc @ X34 @ X33)
% 2.05/2.28          | (m1_subset_1 @ (k4_tmap_1 @ X33 @ X34) @ 
% 2.05/2.28             (k1_zfmisc_1 @ 
% 2.05/2.28              (k2_zfmisc_1 @ (u1_struct_0 @ X34) @ (u1_struct_0 @ X33)))))),
% 2.05/2.28      inference('cnf', [status(esa)], [dt_k4_tmap_1])).
% 2.05/2.28  thf('6', plain,
% 2.05/2.28      (((m1_subset_1 @ (k4_tmap_1 @ sk_A @ sk_B) @ 
% 2.05/2.28         (k1_zfmisc_1 @ 
% 2.05/2.28          (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))
% 2.05/2.28        | (v2_struct_0 @ sk_A)
% 2.05/2.28        | ~ (v2_pre_topc @ sk_A)
% 2.05/2.28        | ~ (l1_pre_topc @ sk_A))),
% 2.05/2.28      inference('sup-', [status(thm)], ['4', '5'])).
% 2.05/2.28  thf('7', plain, ((v2_pre_topc @ sk_A)),
% 2.05/2.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.05/2.28  thf('8', plain, ((l1_pre_topc @ sk_A)),
% 2.05/2.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.05/2.28  thf('9', plain,
% 2.05/2.28      (((m1_subset_1 @ (k4_tmap_1 @ sk_A @ sk_B) @ 
% 2.05/2.28         (k1_zfmisc_1 @ 
% 2.05/2.28          (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))
% 2.05/2.28        | (v2_struct_0 @ sk_A))),
% 2.05/2.28      inference('demod', [status(thm)], ['6', '7', '8'])).
% 2.05/2.28  thf('10', plain, (~ (v2_struct_0 @ sk_A)),
% 2.05/2.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.05/2.28  thf('11', plain,
% 2.05/2.28      ((m1_subset_1 @ (k4_tmap_1 @ sk_A @ sk_B) @ 
% 2.05/2.28        (k1_zfmisc_1 @ 
% 2.05/2.28         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 2.05/2.28      inference('clc', [status(thm)], ['9', '10'])).
% 2.05/2.28  thf('12', plain,
% 2.05/2.28      ((m1_subset_1 @ sk_C @ 
% 2.05/2.28        (k1_zfmisc_1 @ 
% 2.05/2.28         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 2.05/2.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.05/2.28  thf(t59_tmap_1, axiom,
% 2.05/2.28    (![A:$i]:
% 2.05/2.28     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 2.05/2.28       ( ![B:$i]:
% 2.05/2.28         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 2.05/2.28             ( l1_pre_topc @ B ) ) =>
% 2.05/2.28           ( ![C:$i]:
% 2.05/2.28             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ B ) ) =>
% 2.05/2.28               ( ![D:$i]:
% 2.05/2.28                 ( ( ( v1_funct_1 @ D ) & 
% 2.05/2.28                     ( v1_funct_2 @
% 2.05/2.28                       D @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 2.05/2.28                     ( m1_subset_1 @
% 2.05/2.28                       D @ 
% 2.05/2.28                       ( k1_zfmisc_1 @
% 2.05/2.28                         ( k2_zfmisc_1 @
% 2.05/2.28                           ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 2.05/2.28                   ( ![E:$i]:
% 2.05/2.28                     ( ( ( v1_funct_1 @ E ) & 
% 2.05/2.28                         ( v1_funct_2 @
% 2.05/2.28                           E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ A ) ) & 
% 2.05/2.28                         ( m1_subset_1 @
% 2.05/2.28                           E @ 
% 2.05/2.28                           ( k1_zfmisc_1 @
% 2.05/2.28                             ( k2_zfmisc_1 @
% 2.05/2.28                               ( u1_struct_0 @ C ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 2.05/2.28                       ( ( ![F:$i]:
% 2.05/2.28                           ( ( m1_subset_1 @ F @ ( u1_struct_0 @ B ) ) =>
% 2.05/2.28                             ( ( r2_hidden @ F @ ( u1_struct_0 @ C ) ) =>
% 2.05/2.28                               ( ( k3_funct_2 @
% 2.05/2.28                                   ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 2.05/2.28                                   D @ F ) =
% 2.05/2.28                                 ( k1_funct_1 @ E @ F ) ) ) ) ) =>
% 2.05/2.28                         ( r2_funct_2 @
% 2.05/2.28                           ( u1_struct_0 @ C ) @ ( u1_struct_0 @ A ) @ 
% 2.05/2.28                           ( k2_tmap_1 @ B @ A @ D @ C ) @ E ) ) ) ) ) ) ) ) ) ) ))).
% 2.05/2.28  thf('13', plain,
% 2.05/2.28      (![X36 : $i, X37 : $i, X38 : $i, X39 : $i, X40 : $i]:
% 2.05/2.28         ((v2_struct_0 @ X36)
% 2.05/2.28          | ~ (v2_pre_topc @ X36)
% 2.05/2.28          | ~ (l1_pre_topc @ X36)
% 2.05/2.28          | ~ (v1_funct_1 @ X37)
% 2.05/2.28          | ~ (v1_funct_2 @ X37 @ (u1_struct_0 @ X36) @ (u1_struct_0 @ X38))
% 2.05/2.28          | ~ (m1_subset_1 @ X37 @ 
% 2.05/2.28               (k1_zfmisc_1 @ 
% 2.05/2.28                (k2_zfmisc_1 @ (u1_struct_0 @ X36) @ (u1_struct_0 @ X38))))
% 2.05/2.28          | (m1_subset_1 @ (sk_F @ X39 @ X37 @ X40 @ X36 @ X38) @ 
% 2.05/2.28             (u1_struct_0 @ X36))
% 2.05/2.28          | (r2_funct_2 @ (u1_struct_0 @ X40) @ (u1_struct_0 @ X38) @ 
% 2.05/2.28             (k2_tmap_1 @ X36 @ X38 @ X37 @ X40) @ X39)
% 2.05/2.28          | ~ (m1_subset_1 @ X39 @ 
% 2.05/2.28               (k1_zfmisc_1 @ 
% 2.05/2.28                (k2_zfmisc_1 @ (u1_struct_0 @ X40) @ (u1_struct_0 @ X38))))
% 2.05/2.28          | ~ (v1_funct_2 @ X39 @ (u1_struct_0 @ X40) @ (u1_struct_0 @ X38))
% 2.05/2.28          | ~ (v1_funct_1 @ X39)
% 2.05/2.28          | ~ (m1_pre_topc @ X40 @ X36)
% 2.05/2.28          | (v2_struct_0 @ X40)
% 2.05/2.28          | ~ (l1_pre_topc @ X38)
% 2.05/2.28          | ~ (v2_pre_topc @ X38)
% 2.05/2.28          | (v2_struct_0 @ X38))),
% 2.05/2.28      inference('cnf', [status(esa)], [t59_tmap_1])).
% 2.05/2.28  thf('14', plain,
% 2.05/2.28      (![X0 : $i, X1 : $i]:
% 2.05/2.28         ((v2_struct_0 @ sk_A)
% 2.05/2.28          | ~ (v2_pre_topc @ sk_A)
% 2.05/2.28          | ~ (l1_pre_topc @ sk_A)
% 2.05/2.28          | (v2_struct_0 @ X0)
% 2.05/2.28          | ~ (m1_pre_topc @ X0 @ sk_B)
% 2.05/2.28          | ~ (v1_funct_1 @ X1)
% 2.05/2.28          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A))
% 2.05/2.28          | ~ (m1_subset_1 @ X1 @ 
% 2.05/2.28               (k1_zfmisc_1 @ 
% 2.05/2.28                (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A))))
% 2.05/2.28          | (r2_funct_2 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A) @ 
% 2.05/2.28             (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ X0) @ X1)
% 2.05/2.28          | (m1_subset_1 @ (sk_F @ X1 @ sk_C @ X0 @ sk_B @ sk_A) @ 
% 2.05/2.28             (u1_struct_0 @ sk_B))
% 2.05/2.28          | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 2.05/2.28          | ~ (v1_funct_1 @ sk_C)
% 2.05/2.28          | ~ (l1_pre_topc @ sk_B)
% 2.05/2.28          | ~ (v2_pre_topc @ sk_B)
% 2.05/2.28          | (v2_struct_0 @ sk_B))),
% 2.05/2.28      inference('sup-', [status(thm)], ['12', '13'])).
% 2.05/2.28  thf('15', plain, ((v2_pre_topc @ sk_A)),
% 2.05/2.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.05/2.28  thf('16', plain, ((l1_pre_topc @ sk_A)),
% 2.05/2.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.05/2.28  thf('17', plain,
% 2.05/2.28      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 2.05/2.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.05/2.28  thf('18', plain, ((v1_funct_1 @ sk_C)),
% 2.05/2.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.05/2.28  thf('19', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 2.05/2.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.05/2.28  thf(dt_m1_pre_topc, axiom,
% 2.05/2.28    (![A:$i]:
% 2.05/2.28     ( ( l1_pre_topc @ A ) =>
% 2.05/2.28       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 2.05/2.28  thf('20', plain,
% 2.05/2.28      (![X13 : $i, X14 : $i]:
% 2.05/2.28         (~ (m1_pre_topc @ X13 @ X14)
% 2.05/2.28          | (l1_pre_topc @ X13)
% 2.05/2.28          | ~ (l1_pre_topc @ X14))),
% 2.05/2.28      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 2.05/2.28  thf('21', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_B))),
% 2.05/2.28      inference('sup-', [status(thm)], ['19', '20'])).
% 2.05/2.28  thf('22', plain, ((l1_pre_topc @ sk_A)),
% 2.05/2.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.05/2.28  thf('23', plain, ((l1_pre_topc @ sk_B)),
% 2.05/2.28      inference('demod', [status(thm)], ['21', '22'])).
% 2.05/2.28  thf('24', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 2.05/2.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.05/2.28  thf(cc1_pre_topc, axiom,
% 2.05/2.28    (![A:$i]:
% 2.05/2.28     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 2.05/2.28       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( v2_pre_topc @ B ) ) ) ))).
% 2.05/2.28  thf('25', plain,
% 2.05/2.28      (![X10 : $i, X11 : $i]:
% 2.05/2.28         (~ (m1_pre_topc @ X10 @ X11)
% 2.05/2.28          | (v2_pre_topc @ X10)
% 2.05/2.28          | ~ (l1_pre_topc @ X11)
% 2.05/2.28          | ~ (v2_pre_topc @ X11))),
% 2.05/2.28      inference('cnf', [status(esa)], [cc1_pre_topc])).
% 2.05/2.28  thf('26', plain,
% 2.05/2.28      ((~ (v2_pre_topc @ sk_A) | ~ (l1_pre_topc @ sk_A) | (v2_pre_topc @ sk_B))),
% 2.05/2.28      inference('sup-', [status(thm)], ['24', '25'])).
% 2.05/2.28  thf('27', plain, ((v2_pre_topc @ sk_A)),
% 2.05/2.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.05/2.28  thf('28', plain, ((l1_pre_topc @ sk_A)),
% 2.05/2.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.05/2.28  thf('29', plain, ((v2_pre_topc @ sk_B)),
% 2.05/2.28      inference('demod', [status(thm)], ['26', '27', '28'])).
% 2.05/2.28  thf('30', plain,
% 2.05/2.28      (![X0 : $i, X1 : $i]:
% 2.05/2.28         ((v2_struct_0 @ sk_A)
% 2.05/2.28          | (v2_struct_0 @ X0)
% 2.05/2.28          | ~ (m1_pre_topc @ X0 @ sk_B)
% 2.05/2.28          | ~ (v1_funct_1 @ X1)
% 2.05/2.28          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A))
% 2.05/2.28          | ~ (m1_subset_1 @ X1 @ 
% 2.05/2.28               (k1_zfmisc_1 @ 
% 2.05/2.28                (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A))))
% 2.05/2.28          | (r2_funct_2 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A) @ 
% 2.05/2.28             (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ X0) @ X1)
% 2.05/2.28          | (m1_subset_1 @ (sk_F @ X1 @ sk_C @ X0 @ sk_B @ sk_A) @ 
% 2.05/2.28             (u1_struct_0 @ sk_B))
% 2.05/2.28          | (v2_struct_0 @ sk_B))),
% 2.05/2.28      inference('demod', [status(thm)],
% 2.05/2.28                ['14', '15', '16', '17', '18', '23', '29'])).
% 2.05/2.28  thf('31', plain,
% 2.05/2.28      (((v2_struct_0 @ sk_B)
% 2.05/2.28        | (m1_subset_1 @ 
% 2.05/2.28           (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A) @ 
% 2.05/2.28           (u1_struct_0 @ sk_B))
% 2.05/2.28        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 2.05/2.28           (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B) @ (k4_tmap_1 @ sk_A @ sk_B))
% 2.05/2.28        | ~ (v1_funct_2 @ (k4_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_B) @ 
% 2.05/2.28             (u1_struct_0 @ sk_A))
% 2.05/2.28        | ~ (v1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_B))
% 2.05/2.28        | ~ (m1_pre_topc @ sk_B @ sk_B)
% 2.05/2.28        | (v2_struct_0 @ sk_B)
% 2.05/2.28        | (v2_struct_0 @ sk_A))),
% 2.05/2.28      inference('sup-', [status(thm)], ['11', '30'])).
% 2.05/2.28  thf('32', plain,
% 2.05/2.28      (![X35 : $i]: ((m1_pre_topc @ X35 @ X35) | ~ (l1_pre_topc @ X35))),
% 2.05/2.28      inference('cnf', [status(esa)], [t2_tsep_1])).
% 2.05/2.28  thf('33', plain,
% 2.05/2.28      (![X35 : $i]: ((m1_pre_topc @ X35 @ X35) | ~ (l1_pre_topc @ X35))),
% 2.05/2.28      inference('cnf', [status(esa)], [t2_tsep_1])).
% 2.05/2.28  thf('34', plain,
% 2.05/2.28      ((m1_subset_1 @ sk_C @ 
% 2.05/2.28        (k1_zfmisc_1 @ 
% 2.05/2.28         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 2.05/2.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.05/2.28  thf(dt_k3_tmap_1, axiom,
% 2.05/2.28    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 2.05/2.28     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 2.05/2.28         ( l1_pre_topc @ A ) & ( ~( v2_struct_0 @ B ) ) & 
% 2.05/2.28         ( v2_pre_topc @ B ) & ( l1_pre_topc @ B ) & ( m1_pre_topc @ C @ A ) & 
% 2.05/2.28         ( m1_pre_topc @ D @ A ) & ( v1_funct_1 @ E ) & 
% 2.05/2.28         ( v1_funct_2 @ E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 2.05/2.28         ( m1_subset_1 @
% 2.05/2.28           E @ 
% 2.05/2.28           ( k1_zfmisc_1 @
% 2.05/2.28             ( k2_zfmisc_1 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 2.05/2.28       ( ( v1_funct_1 @ ( k3_tmap_1 @ A @ B @ C @ D @ E ) ) & 
% 2.05/2.28         ( v1_funct_2 @
% 2.05/2.28           ( k3_tmap_1 @ A @ B @ C @ D @ E ) @ ( u1_struct_0 @ D ) @ 
% 2.05/2.28           ( u1_struct_0 @ B ) ) & 
% 2.05/2.28         ( m1_subset_1 @
% 2.05/2.28           ( k3_tmap_1 @ A @ B @ C @ D @ E ) @ 
% 2.05/2.28           ( k1_zfmisc_1 @
% 2.05/2.28             ( k2_zfmisc_1 @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) ))).
% 2.05/2.28  thf('35', plain,
% 2.05/2.28      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 2.05/2.28         (~ (m1_pre_topc @ X28 @ X29)
% 2.05/2.28          | ~ (m1_pre_topc @ X30 @ X29)
% 2.05/2.28          | ~ (l1_pre_topc @ X31)
% 2.05/2.28          | ~ (v2_pre_topc @ X31)
% 2.05/2.28          | (v2_struct_0 @ X31)
% 2.05/2.28          | ~ (l1_pre_topc @ X29)
% 2.05/2.28          | ~ (v2_pre_topc @ X29)
% 2.05/2.28          | (v2_struct_0 @ X29)
% 2.05/2.28          | ~ (v1_funct_1 @ X32)
% 2.05/2.28          | ~ (v1_funct_2 @ X32 @ (u1_struct_0 @ X30) @ (u1_struct_0 @ X31))
% 2.05/2.28          | ~ (m1_subset_1 @ X32 @ 
% 2.05/2.28               (k1_zfmisc_1 @ 
% 2.05/2.28                (k2_zfmisc_1 @ (u1_struct_0 @ X30) @ (u1_struct_0 @ X31))))
% 2.05/2.28          | (m1_subset_1 @ (k3_tmap_1 @ X29 @ X31 @ X30 @ X28 @ X32) @ 
% 2.05/2.28             (k1_zfmisc_1 @ 
% 2.05/2.28              (k2_zfmisc_1 @ (u1_struct_0 @ X28) @ (u1_struct_0 @ X31)))))),
% 2.05/2.28      inference('cnf', [status(esa)], [dt_k3_tmap_1])).
% 2.05/2.28  thf('36', plain,
% 2.05/2.28      (![X0 : $i, X1 : $i]:
% 2.05/2.28         ((m1_subset_1 @ (k3_tmap_1 @ X1 @ sk_A @ sk_B @ X0 @ sk_C) @ 
% 2.05/2.28           (k1_zfmisc_1 @ 
% 2.05/2.28            (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A))))
% 2.05/2.28          | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 2.05/2.28          | ~ (v1_funct_1 @ sk_C)
% 2.05/2.28          | (v2_struct_0 @ X1)
% 2.05/2.28          | ~ (v2_pre_topc @ X1)
% 2.05/2.28          | ~ (l1_pre_topc @ X1)
% 2.05/2.28          | (v2_struct_0 @ sk_A)
% 2.05/2.28          | ~ (v2_pre_topc @ sk_A)
% 2.05/2.28          | ~ (l1_pre_topc @ sk_A)
% 2.05/2.28          | ~ (m1_pre_topc @ sk_B @ X1)
% 2.05/2.28          | ~ (m1_pre_topc @ X0 @ X1))),
% 2.05/2.28      inference('sup-', [status(thm)], ['34', '35'])).
% 2.05/2.28  thf('37', plain,
% 2.05/2.28      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 2.05/2.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.05/2.28  thf('38', plain, ((v1_funct_1 @ sk_C)),
% 2.05/2.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.05/2.28  thf('39', plain, ((v2_pre_topc @ sk_A)),
% 2.05/2.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.05/2.28  thf('40', plain, ((l1_pre_topc @ sk_A)),
% 2.05/2.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.05/2.28  thf('41', plain,
% 2.05/2.28      (![X0 : $i, X1 : $i]:
% 2.05/2.28         ((m1_subset_1 @ (k3_tmap_1 @ X1 @ sk_A @ sk_B @ X0 @ sk_C) @ 
% 2.05/2.28           (k1_zfmisc_1 @ 
% 2.05/2.28            (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A))))
% 2.05/2.28          | (v2_struct_0 @ X1)
% 2.05/2.28          | ~ (v2_pre_topc @ X1)
% 2.05/2.28          | ~ (l1_pre_topc @ X1)
% 2.05/2.28          | (v2_struct_0 @ sk_A)
% 2.05/2.28          | ~ (m1_pre_topc @ sk_B @ X1)
% 2.05/2.28          | ~ (m1_pre_topc @ X0 @ X1))),
% 2.05/2.28      inference('demod', [status(thm)], ['36', '37', '38', '39', '40'])).
% 2.05/2.28  thf('42', plain,
% 2.05/2.28      (![X0 : $i]:
% 2.05/2.28         (~ (l1_pre_topc @ sk_B)
% 2.05/2.28          | ~ (m1_pre_topc @ X0 @ sk_B)
% 2.05/2.28          | (v2_struct_0 @ sk_A)
% 2.05/2.28          | ~ (l1_pre_topc @ sk_B)
% 2.05/2.28          | ~ (v2_pre_topc @ sk_B)
% 2.05/2.28          | (v2_struct_0 @ sk_B)
% 2.05/2.28          | (m1_subset_1 @ (k3_tmap_1 @ sk_B @ sk_A @ sk_B @ X0 @ sk_C) @ 
% 2.05/2.28             (k1_zfmisc_1 @ 
% 2.05/2.28              (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A)))))),
% 2.05/2.28      inference('sup-', [status(thm)], ['33', '41'])).
% 2.05/2.28  thf('43', plain, ((l1_pre_topc @ sk_B)),
% 2.05/2.28      inference('demod', [status(thm)], ['21', '22'])).
% 2.05/2.28  thf('44', plain, ((l1_pre_topc @ sk_B)),
% 2.05/2.28      inference('demod', [status(thm)], ['21', '22'])).
% 2.05/2.28  thf('45', plain, ((v2_pre_topc @ sk_B)),
% 2.05/2.28      inference('demod', [status(thm)], ['26', '27', '28'])).
% 2.05/2.28  thf('46', plain,
% 2.05/2.28      (![X0 : $i]:
% 2.05/2.28         (~ (m1_pre_topc @ X0 @ sk_B)
% 2.05/2.28          | (v2_struct_0 @ sk_A)
% 2.05/2.28          | (v2_struct_0 @ sk_B)
% 2.05/2.28          | (m1_subset_1 @ (k3_tmap_1 @ sk_B @ sk_A @ sk_B @ X0 @ sk_C) @ 
% 2.05/2.28             (k1_zfmisc_1 @ 
% 2.05/2.28              (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A)))))),
% 2.05/2.28      inference('demod', [status(thm)], ['42', '43', '44', '45'])).
% 2.05/2.28  thf('47', plain,
% 2.05/2.28      ((~ (l1_pre_topc @ sk_B)
% 2.05/2.28        | (m1_subset_1 @ (k3_tmap_1 @ sk_B @ sk_A @ sk_B @ sk_B @ sk_C) @ 
% 2.05/2.28           (k1_zfmisc_1 @ 
% 2.05/2.28            (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))
% 2.05/2.28        | (v2_struct_0 @ sk_B)
% 2.05/2.28        | (v2_struct_0 @ sk_A))),
% 2.05/2.28      inference('sup-', [status(thm)], ['32', '46'])).
% 2.05/2.28  thf('48', plain, ((l1_pre_topc @ sk_B)),
% 2.05/2.28      inference('demod', [status(thm)], ['21', '22'])).
% 2.05/2.28  thf('49', plain,
% 2.05/2.28      (((m1_subset_1 @ (k3_tmap_1 @ sk_B @ sk_A @ sk_B @ sk_B @ sk_C) @ 
% 2.05/2.28         (k1_zfmisc_1 @ 
% 2.05/2.28          (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))
% 2.05/2.28        | (v2_struct_0 @ sk_B)
% 2.05/2.28        | (v2_struct_0 @ sk_A))),
% 2.05/2.28      inference('demod', [status(thm)], ['47', '48'])).
% 2.05/2.28  thf('50', plain, (~ (v2_struct_0 @ sk_B)),
% 2.05/2.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.05/2.28  thf('51', plain,
% 2.05/2.28      (((v2_struct_0 @ sk_A)
% 2.05/2.28        | (m1_subset_1 @ (k3_tmap_1 @ sk_B @ sk_A @ sk_B @ sk_B @ sk_C) @ 
% 2.05/2.28           (k1_zfmisc_1 @ 
% 2.05/2.28            (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A)))))),
% 2.05/2.28      inference('clc', [status(thm)], ['49', '50'])).
% 2.05/2.28  thf('52', plain, (~ (v2_struct_0 @ sk_A)),
% 2.05/2.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.05/2.28  thf('53', plain,
% 2.05/2.28      ((m1_subset_1 @ (k3_tmap_1 @ sk_B @ sk_A @ sk_B @ sk_B @ sk_C) @ 
% 2.05/2.28        (k1_zfmisc_1 @ 
% 2.05/2.28         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 2.05/2.28      inference('clc', [status(thm)], ['51', '52'])).
% 2.05/2.28  thf('54', plain,
% 2.05/2.28      ((m1_subset_1 @ sk_C @ 
% 2.05/2.28        (k1_zfmisc_1 @ 
% 2.05/2.28         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 2.05/2.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.05/2.28  thf(redefinition_r2_funct_2, axiom,
% 2.05/2.28    (![A:$i,B:$i,C:$i,D:$i]:
% 2.05/2.28     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 2.05/2.28         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 2.05/2.28         ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 2.05/2.28         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.05/2.28       ( ( r2_funct_2 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 2.05/2.28  thf('55', plain,
% 2.05/2.28      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 2.05/2.28         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8)))
% 2.05/2.28          | ~ (v1_funct_2 @ X6 @ X7 @ X8)
% 2.05/2.28          | ~ (v1_funct_1 @ X6)
% 2.05/2.28          | ~ (v1_funct_1 @ X9)
% 2.05/2.28          | ~ (v1_funct_2 @ X9 @ X7 @ X8)
% 2.05/2.28          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8)))
% 2.05/2.28          | ((X6) = (X9))
% 2.05/2.28          | ~ (r2_funct_2 @ X7 @ X8 @ X6 @ X9))),
% 2.05/2.28      inference('cnf', [status(esa)], [redefinition_r2_funct_2])).
% 2.05/2.28  thf('56', plain,
% 2.05/2.28      (![X0 : $i]:
% 2.05/2.28         (~ (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 2.05/2.28             X0)
% 2.05/2.28          | ((sk_C) = (X0))
% 2.05/2.28          | ~ (m1_subset_1 @ X0 @ 
% 2.05/2.28               (k1_zfmisc_1 @ 
% 2.05/2.28                (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))
% 2.05/2.28          | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 2.05/2.28          | ~ (v1_funct_1 @ X0)
% 2.05/2.28          | ~ (v1_funct_1 @ sk_C)
% 2.05/2.28          | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 2.05/2.28      inference('sup-', [status(thm)], ['54', '55'])).
% 2.05/2.28  thf('57', plain, ((v1_funct_1 @ sk_C)),
% 2.05/2.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.05/2.28  thf('58', plain,
% 2.05/2.28      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 2.05/2.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.05/2.28  thf('59', plain,
% 2.05/2.28      (![X0 : $i]:
% 2.05/2.28         (~ (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 2.05/2.28             X0)
% 2.05/2.28          | ((sk_C) = (X0))
% 2.05/2.28          | ~ (m1_subset_1 @ X0 @ 
% 2.05/2.28               (k1_zfmisc_1 @ 
% 2.05/2.28                (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))
% 2.05/2.28          | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 2.05/2.28          | ~ (v1_funct_1 @ X0))),
% 2.05/2.28      inference('demod', [status(thm)], ['56', '57', '58'])).
% 2.05/2.28  thf('60', plain,
% 2.05/2.28      ((~ (v1_funct_1 @ (k3_tmap_1 @ sk_B @ sk_A @ sk_B @ sk_B @ sk_C))
% 2.05/2.28        | ~ (v1_funct_2 @ (k3_tmap_1 @ sk_B @ sk_A @ sk_B @ sk_B @ sk_C) @ 
% 2.05/2.28             (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 2.05/2.28        | ((sk_C) = (k3_tmap_1 @ sk_B @ sk_A @ sk_B @ sk_B @ sk_C))
% 2.05/2.28        | ~ (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 2.05/2.28             (k3_tmap_1 @ sk_B @ sk_A @ sk_B @ sk_B @ sk_C)))),
% 2.05/2.28      inference('sup-', [status(thm)], ['53', '59'])).
% 2.05/2.28  thf('61', plain,
% 2.05/2.28      (![X35 : $i]: ((m1_pre_topc @ X35 @ X35) | ~ (l1_pre_topc @ X35))),
% 2.05/2.28      inference('cnf', [status(esa)], [t2_tsep_1])).
% 2.05/2.28  thf('62', plain,
% 2.05/2.28      (![X35 : $i]: ((m1_pre_topc @ X35 @ X35) | ~ (l1_pre_topc @ X35))),
% 2.05/2.28      inference('cnf', [status(esa)], [t2_tsep_1])).
% 2.05/2.28  thf('63', plain,
% 2.05/2.28      ((m1_subset_1 @ sk_C @ 
% 2.05/2.28        (k1_zfmisc_1 @ 
% 2.05/2.28         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 2.05/2.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.05/2.28  thf('64', plain,
% 2.05/2.28      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 2.05/2.28         (~ (m1_pre_topc @ X28 @ X29)
% 2.05/2.28          | ~ (m1_pre_topc @ X30 @ X29)
% 2.05/2.28          | ~ (l1_pre_topc @ X31)
% 2.05/2.28          | ~ (v2_pre_topc @ X31)
% 2.05/2.28          | (v2_struct_0 @ X31)
% 2.05/2.28          | ~ (l1_pre_topc @ X29)
% 2.05/2.28          | ~ (v2_pre_topc @ X29)
% 2.05/2.28          | (v2_struct_0 @ X29)
% 2.05/2.28          | ~ (v1_funct_1 @ X32)
% 2.05/2.28          | ~ (v1_funct_2 @ X32 @ (u1_struct_0 @ X30) @ (u1_struct_0 @ X31))
% 2.05/2.28          | ~ (m1_subset_1 @ X32 @ 
% 2.05/2.28               (k1_zfmisc_1 @ 
% 2.05/2.28                (k2_zfmisc_1 @ (u1_struct_0 @ X30) @ (u1_struct_0 @ X31))))
% 2.05/2.28          | (v1_funct_1 @ (k3_tmap_1 @ X29 @ X31 @ X30 @ X28 @ X32)))),
% 2.05/2.28      inference('cnf', [status(esa)], [dt_k3_tmap_1])).
% 2.05/2.28  thf('65', plain,
% 2.05/2.28      (![X0 : $i, X1 : $i]:
% 2.05/2.28         ((v1_funct_1 @ (k3_tmap_1 @ X1 @ sk_A @ sk_B @ X0 @ sk_C))
% 2.05/2.28          | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 2.05/2.28          | ~ (v1_funct_1 @ sk_C)
% 2.05/2.28          | (v2_struct_0 @ X1)
% 2.05/2.28          | ~ (v2_pre_topc @ X1)
% 2.05/2.28          | ~ (l1_pre_topc @ X1)
% 2.05/2.28          | (v2_struct_0 @ sk_A)
% 2.05/2.28          | ~ (v2_pre_topc @ sk_A)
% 2.05/2.28          | ~ (l1_pre_topc @ sk_A)
% 2.05/2.28          | ~ (m1_pre_topc @ sk_B @ X1)
% 2.05/2.28          | ~ (m1_pre_topc @ X0 @ X1))),
% 2.05/2.28      inference('sup-', [status(thm)], ['63', '64'])).
% 2.05/2.28  thf('66', plain,
% 2.05/2.28      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 2.05/2.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.05/2.28  thf('67', plain, ((v1_funct_1 @ sk_C)),
% 2.05/2.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.05/2.28  thf('68', plain, ((v2_pre_topc @ sk_A)),
% 2.05/2.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.05/2.28  thf('69', plain, ((l1_pre_topc @ sk_A)),
% 2.05/2.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.05/2.28  thf('70', plain,
% 2.05/2.28      (![X0 : $i, X1 : $i]:
% 2.05/2.28         ((v1_funct_1 @ (k3_tmap_1 @ X1 @ sk_A @ sk_B @ X0 @ sk_C))
% 2.05/2.28          | (v2_struct_0 @ X1)
% 2.05/2.28          | ~ (v2_pre_topc @ X1)
% 2.05/2.28          | ~ (l1_pre_topc @ X1)
% 2.05/2.28          | (v2_struct_0 @ sk_A)
% 2.05/2.28          | ~ (m1_pre_topc @ sk_B @ X1)
% 2.05/2.28          | ~ (m1_pre_topc @ X0 @ X1))),
% 2.05/2.28      inference('demod', [status(thm)], ['65', '66', '67', '68', '69'])).
% 2.05/2.28  thf('71', plain,
% 2.05/2.28      (![X0 : $i]:
% 2.05/2.28         (~ (l1_pre_topc @ sk_B)
% 2.05/2.28          | ~ (m1_pre_topc @ X0 @ sk_B)
% 2.05/2.28          | (v2_struct_0 @ sk_A)
% 2.05/2.28          | ~ (l1_pre_topc @ sk_B)
% 2.05/2.28          | ~ (v2_pre_topc @ sk_B)
% 2.05/2.28          | (v2_struct_0 @ sk_B)
% 2.05/2.28          | (v1_funct_1 @ (k3_tmap_1 @ sk_B @ sk_A @ sk_B @ X0 @ sk_C)))),
% 2.05/2.28      inference('sup-', [status(thm)], ['62', '70'])).
% 2.05/2.28  thf('72', plain, ((l1_pre_topc @ sk_B)),
% 2.05/2.28      inference('demod', [status(thm)], ['21', '22'])).
% 2.05/2.28  thf('73', plain, ((l1_pre_topc @ sk_B)),
% 2.05/2.28      inference('demod', [status(thm)], ['21', '22'])).
% 2.05/2.28  thf('74', plain, ((v2_pre_topc @ sk_B)),
% 2.05/2.28      inference('demod', [status(thm)], ['26', '27', '28'])).
% 2.05/2.28  thf('75', plain,
% 2.05/2.28      (![X0 : $i]:
% 2.05/2.28         (~ (m1_pre_topc @ X0 @ sk_B)
% 2.05/2.28          | (v2_struct_0 @ sk_A)
% 2.05/2.28          | (v2_struct_0 @ sk_B)
% 2.05/2.28          | (v1_funct_1 @ (k3_tmap_1 @ sk_B @ sk_A @ sk_B @ X0 @ sk_C)))),
% 2.05/2.28      inference('demod', [status(thm)], ['71', '72', '73', '74'])).
% 2.05/2.28  thf('76', plain,
% 2.05/2.28      ((~ (l1_pre_topc @ sk_B)
% 2.05/2.28        | (v1_funct_1 @ (k3_tmap_1 @ sk_B @ sk_A @ sk_B @ sk_B @ sk_C))
% 2.05/2.28        | (v2_struct_0 @ sk_B)
% 2.05/2.28        | (v2_struct_0 @ sk_A))),
% 2.05/2.28      inference('sup-', [status(thm)], ['61', '75'])).
% 2.05/2.28  thf('77', plain, ((l1_pre_topc @ sk_B)),
% 2.05/2.28      inference('demod', [status(thm)], ['21', '22'])).
% 2.05/2.28  thf('78', plain,
% 2.05/2.28      (((v1_funct_1 @ (k3_tmap_1 @ sk_B @ sk_A @ sk_B @ sk_B @ sk_C))
% 2.05/2.28        | (v2_struct_0 @ sk_B)
% 2.05/2.28        | (v2_struct_0 @ sk_A))),
% 2.05/2.28      inference('demod', [status(thm)], ['76', '77'])).
% 2.05/2.28  thf('79', plain, (~ (v2_struct_0 @ sk_B)),
% 2.05/2.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.05/2.28  thf('80', plain,
% 2.05/2.28      (((v2_struct_0 @ sk_A)
% 2.05/2.28        | (v1_funct_1 @ (k3_tmap_1 @ sk_B @ sk_A @ sk_B @ sk_B @ sk_C)))),
% 2.05/2.28      inference('clc', [status(thm)], ['78', '79'])).
% 2.05/2.28  thf('81', plain, (~ (v2_struct_0 @ sk_A)),
% 2.05/2.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.05/2.28  thf('82', plain,
% 2.05/2.28      ((v1_funct_1 @ (k3_tmap_1 @ sk_B @ sk_A @ sk_B @ sk_B @ sk_C))),
% 2.05/2.28      inference('clc', [status(thm)], ['80', '81'])).
% 2.05/2.28  thf('83', plain,
% 2.05/2.28      ((~ (v1_funct_2 @ (k3_tmap_1 @ sk_B @ sk_A @ sk_B @ sk_B @ sk_C) @ 
% 2.05/2.28           (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 2.05/2.28        | ((sk_C) = (k3_tmap_1 @ sk_B @ sk_A @ sk_B @ sk_B @ sk_C))
% 2.05/2.28        | ~ (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 2.05/2.28             (k3_tmap_1 @ sk_B @ sk_A @ sk_B @ sk_B @ sk_C)))),
% 2.05/2.28      inference('demod', [status(thm)], ['60', '82'])).
% 2.05/2.28  thf('84', plain,
% 2.05/2.28      (![X35 : $i]: ((m1_pre_topc @ X35 @ X35) | ~ (l1_pre_topc @ X35))),
% 2.05/2.28      inference('cnf', [status(esa)], [t2_tsep_1])).
% 2.05/2.28  thf('85', plain,
% 2.05/2.28      (![X35 : $i]: ((m1_pre_topc @ X35 @ X35) | ~ (l1_pre_topc @ X35))),
% 2.05/2.28      inference('cnf', [status(esa)], [t2_tsep_1])).
% 2.05/2.28  thf('86', plain,
% 2.05/2.28      ((m1_subset_1 @ sk_C @ 
% 2.05/2.28        (k1_zfmisc_1 @ 
% 2.05/2.28         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 2.05/2.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.05/2.28  thf('87', plain,
% 2.05/2.28      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 2.05/2.28         (~ (m1_pre_topc @ X28 @ X29)
% 2.05/2.28          | ~ (m1_pre_topc @ X30 @ X29)
% 2.05/2.28          | ~ (l1_pre_topc @ X31)
% 2.05/2.28          | ~ (v2_pre_topc @ X31)
% 2.05/2.28          | (v2_struct_0 @ X31)
% 2.05/2.28          | ~ (l1_pre_topc @ X29)
% 2.05/2.28          | ~ (v2_pre_topc @ X29)
% 2.05/2.28          | (v2_struct_0 @ X29)
% 2.05/2.28          | ~ (v1_funct_1 @ X32)
% 2.05/2.28          | ~ (v1_funct_2 @ X32 @ (u1_struct_0 @ X30) @ (u1_struct_0 @ X31))
% 2.05/2.28          | ~ (m1_subset_1 @ X32 @ 
% 2.05/2.28               (k1_zfmisc_1 @ 
% 2.05/2.28                (k2_zfmisc_1 @ (u1_struct_0 @ X30) @ (u1_struct_0 @ X31))))
% 2.05/2.28          | (v1_funct_2 @ (k3_tmap_1 @ X29 @ X31 @ X30 @ X28 @ X32) @ 
% 2.05/2.28             (u1_struct_0 @ X28) @ (u1_struct_0 @ X31)))),
% 2.05/2.28      inference('cnf', [status(esa)], [dt_k3_tmap_1])).
% 2.05/2.28  thf('88', plain,
% 2.05/2.28      (![X0 : $i, X1 : $i]:
% 2.05/2.28         ((v1_funct_2 @ (k3_tmap_1 @ X1 @ sk_A @ sk_B @ X0 @ sk_C) @ 
% 2.05/2.28           (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A))
% 2.05/2.28          | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 2.05/2.28          | ~ (v1_funct_1 @ sk_C)
% 2.05/2.28          | (v2_struct_0 @ X1)
% 2.05/2.28          | ~ (v2_pre_topc @ X1)
% 2.05/2.28          | ~ (l1_pre_topc @ X1)
% 2.05/2.28          | (v2_struct_0 @ sk_A)
% 2.05/2.28          | ~ (v2_pre_topc @ sk_A)
% 2.05/2.28          | ~ (l1_pre_topc @ sk_A)
% 2.05/2.28          | ~ (m1_pre_topc @ sk_B @ X1)
% 2.05/2.28          | ~ (m1_pre_topc @ X0 @ X1))),
% 2.05/2.28      inference('sup-', [status(thm)], ['86', '87'])).
% 2.05/2.28  thf('89', plain,
% 2.05/2.28      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 2.05/2.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.05/2.28  thf('90', plain, ((v1_funct_1 @ sk_C)),
% 2.05/2.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.05/2.28  thf('91', plain, ((v2_pre_topc @ sk_A)),
% 2.05/2.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.05/2.28  thf('92', plain, ((l1_pre_topc @ sk_A)),
% 2.05/2.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.05/2.28  thf('93', plain,
% 2.05/2.28      (![X0 : $i, X1 : $i]:
% 2.05/2.28         ((v1_funct_2 @ (k3_tmap_1 @ X1 @ sk_A @ sk_B @ X0 @ sk_C) @ 
% 2.05/2.28           (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A))
% 2.05/2.28          | (v2_struct_0 @ X1)
% 2.05/2.28          | ~ (v2_pre_topc @ X1)
% 2.05/2.28          | ~ (l1_pre_topc @ X1)
% 2.05/2.28          | (v2_struct_0 @ sk_A)
% 2.05/2.28          | ~ (m1_pre_topc @ sk_B @ X1)
% 2.05/2.28          | ~ (m1_pre_topc @ X0 @ X1))),
% 2.05/2.28      inference('demod', [status(thm)], ['88', '89', '90', '91', '92'])).
% 2.05/2.28  thf('94', plain,
% 2.05/2.28      (![X0 : $i]:
% 2.05/2.28         (~ (l1_pre_topc @ sk_B)
% 2.05/2.28          | ~ (m1_pre_topc @ X0 @ sk_B)
% 2.05/2.28          | (v2_struct_0 @ sk_A)
% 2.05/2.28          | ~ (l1_pre_topc @ sk_B)
% 2.05/2.28          | ~ (v2_pre_topc @ sk_B)
% 2.05/2.28          | (v2_struct_0 @ sk_B)
% 2.05/2.28          | (v1_funct_2 @ (k3_tmap_1 @ sk_B @ sk_A @ sk_B @ X0 @ sk_C) @ 
% 2.05/2.28             (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A)))),
% 2.05/2.28      inference('sup-', [status(thm)], ['85', '93'])).
% 2.05/2.28  thf('95', plain, ((l1_pre_topc @ sk_B)),
% 2.05/2.28      inference('demod', [status(thm)], ['21', '22'])).
% 2.05/2.28  thf('96', plain, ((l1_pre_topc @ sk_B)),
% 2.05/2.28      inference('demod', [status(thm)], ['21', '22'])).
% 2.05/2.28  thf('97', plain, ((v2_pre_topc @ sk_B)),
% 2.05/2.28      inference('demod', [status(thm)], ['26', '27', '28'])).
% 2.05/2.28  thf('98', plain,
% 2.05/2.28      (![X0 : $i]:
% 2.05/2.28         (~ (m1_pre_topc @ X0 @ sk_B)
% 2.05/2.28          | (v2_struct_0 @ sk_A)
% 2.05/2.28          | (v2_struct_0 @ sk_B)
% 2.05/2.28          | (v1_funct_2 @ (k3_tmap_1 @ sk_B @ sk_A @ sk_B @ X0 @ sk_C) @ 
% 2.05/2.28             (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A)))),
% 2.05/2.28      inference('demod', [status(thm)], ['94', '95', '96', '97'])).
% 2.05/2.28  thf('99', plain,
% 2.05/2.28      ((~ (l1_pre_topc @ sk_B)
% 2.05/2.28        | (v1_funct_2 @ (k3_tmap_1 @ sk_B @ sk_A @ sk_B @ sk_B @ sk_C) @ 
% 2.05/2.28           (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 2.05/2.28        | (v2_struct_0 @ sk_B)
% 2.05/2.28        | (v2_struct_0 @ sk_A))),
% 2.05/2.28      inference('sup-', [status(thm)], ['84', '98'])).
% 2.05/2.28  thf('100', plain, ((l1_pre_topc @ sk_B)),
% 2.05/2.28      inference('demod', [status(thm)], ['21', '22'])).
% 2.05/2.28  thf('101', plain,
% 2.05/2.28      (((v1_funct_2 @ (k3_tmap_1 @ sk_B @ sk_A @ sk_B @ sk_B @ sk_C) @ 
% 2.05/2.28         (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 2.05/2.28        | (v2_struct_0 @ sk_B)
% 2.05/2.28        | (v2_struct_0 @ sk_A))),
% 2.05/2.28      inference('demod', [status(thm)], ['99', '100'])).
% 2.05/2.28  thf('102', plain, (~ (v2_struct_0 @ sk_B)),
% 2.05/2.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.05/2.28  thf('103', plain,
% 2.05/2.28      (((v2_struct_0 @ sk_A)
% 2.05/2.28        | (v1_funct_2 @ (k3_tmap_1 @ sk_B @ sk_A @ sk_B @ sk_B @ sk_C) @ 
% 2.05/2.28           (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 2.05/2.28      inference('clc', [status(thm)], ['101', '102'])).
% 2.05/2.28  thf('104', plain, (~ (v2_struct_0 @ sk_A)),
% 2.05/2.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.05/2.28  thf('105', plain,
% 2.05/2.28      ((v1_funct_2 @ (k3_tmap_1 @ sk_B @ sk_A @ sk_B @ sk_B @ sk_C) @ 
% 2.05/2.28        (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 2.05/2.28      inference('clc', [status(thm)], ['103', '104'])).
% 2.05/2.28  thf('106', plain,
% 2.05/2.28      ((((sk_C) = (k3_tmap_1 @ sk_B @ sk_A @ sk_B @ sk_B @ sk_C))
% 2.05/2.28        | ~ (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 2.05/2.28             (k3_tmap_1 @ sk_B @ sk_A @ sk_B @ sk_B @ sk_C)))),
% 2.05/2.28      inference('demod', [status(thm)], ['83', '105'])).
% 2.05/2.28  thf('107', plain,
% 2.05/2.28      (![X35 : $i]: ((m1_pre_topc @ X35 @ X35) | ~ (l1_pre_topc @ X35))),
% 2.05/2.28      inference('cnf', [status(esa)], [t2_tsep_1])).
% 2.05/2.28  thf('108', plain,
% 2.05/2.28      (![X35 : $i]: ((m1_pre_topc @ X35 @ X35) | ~ (l1_pre_topc @ X35))),
% 2.05/2.28      inference('cnf', [status(esa)], [t2_tsep_1])).
% 2.05/2.28  thf('109', plain,
% 2.05/2.28      ((m1_subset_1 @ sk_C @ 
% 2.05/2.28        (k1_zfmisc_1 @ 
% 2.05/2.28         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 2.05/2.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.05/2.28  thf(d5_tmap_1, axiom,
% 2.05/2.28    (![A:$i]:
% 2.05/2.28     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 2.05/2.28       ( ![B:$i]:
% 2.05/2.28         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 2.05/2.28             ( l1_pre_topc @ B ) ) =>
% 2.05/2.28           ( ![C:$i]:
% 2.05/2.28             ( ( m1_pre_topc @ C @ A ) =>
% 2.05/2.28               ( ![D:$i]:
% 2.05/2.28                 ( ( m1_pre_topc @ D @ A ) =>
% 2.05/2.28                   ( ![E:$i]:
% 2.05/2.28                     ( ( ( v1_funct_1 @ E ) & 
% 2.05/2.28                         ( v1_funct_2 @
% 2.05/2.28                           E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 2.05/2.28                         ( m1_subset_1 @
% 2.05/2.28                           E @ 
% 2.05/2.28                           ( k1_zfmisc_1 @
% 2.05/2.28                             ( k2_zfmisc_1 @
% 2.05/2.28                               ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 2.05/2.28                       ( ( m1_pre_topc @ D @ C ) =>
% 2.05/2.28                         ( ( k3_tmap_1 @ A @ B @ C @ D @ E ) =
% 2.05/2.28                           ( k2_partfun1 @
% 2.05/2.28                             ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ E @ 
% 2.05/2.28                             ( u1_struct_0 @ D ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 2.05/2.28  thf('110', plain,
% 2.05/2.28      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 2.05/2.28         ((v2_struct_0 @ X23)
% 2.05/2.28          | ~ (v2_pre_topc @ X23)
% 2.05/2.28          | ~ (l1_pre_topc @ X23)
% 2.05/2.28          | ~ (m1_pre_topc @ X24 @ X25)
% 2.05/2.28          | ~ (m1_pre_topc @ X24 @ X26)
% 2.05/2.28          | ((k3_tmap_1 @ X25 @ X23 @ X26 @ X24 @ X27)
% 2.05/2.28              = (k2_partfun1 @ (u1_struct_0 @ X26) @ (u1_struct_0 @ X23) @ 
% 2.05/2.28                 X27 @ (u1_struct_0 @ X24)))
% 2.05/2.28          | ~ (m1_subset_1 @ X27 @ 
% 2.05/2.28               (k1_zfmisc_1 @ 
% 2.05/2.28                (k2_zfmisc_1 @ (u1_struct_0 @ X26) @ (u1_struct_0 @ X23))))
% 2.05/2.28          | ~ (v1_funct_2 @ X27 @ (u1_struct_0 @ X26) @ (u1_struct_0 @ X23))
% 2.05/2.28          | ~ (v1_funct_1 @ X27)
% 2.05/2.28          | ~ (m1_pre_topc @ X26 @ X25)
% 2.05/2.28          | ~ (l1_pre_topc @ X25)
% 2.05/2.28          | ~ (v2_pre_topc @ X25)
% 2.05/2.28          | (v2_struct_0 @ X25))),
% 2.05/2.28      inference('cnf', [status(esa)], [d5_tmap_1])).
% 2.05/2.28  thf('111', plain,
% 2.05/2.28      (![X0 : $i, X1 : $i]:
% 2.05/2.28         ((v2_struct_0 @ X0)
% 2.05/2.28          | ~ (v2_pre_topc @ X0)
% 2.05/2.28          | ~ (l1_pre_topc @ X0)
% 2.05/2.28          | ~ (m1_pre_topc @ sk_B @ X0)
% 2.05/2.28          | ~ (v1_funct_1 @ sk_C)
% 2.05/2.28          | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 2.05/2.28          | ((k3_tmap_1 @ X0 @ sk_A @ sk_B @ X1 @ sk_C)
% 2.05/2.28              = (k2_partfun1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 2.05/2.28                 sk_C @ (u1_struct_0 @ X1)))
% 2.05/2.28          | ~ (m1_pre_topc @ X1 @ sk_B)
% 2.05/2.28          | ~ (m1_pre_topc @ X1 @ X0)
% 2.05/2.28          | ~ (l1_pre_topc @ sk_A)
% 2.05/2.28          | ~ (v2_pre_topc @ sk_A)
% 2.05/2.28          | (v2_struct_0 @ sk_A))),
% 2.05/2.28      inference('sup-', [status(thm)], ['109', '110'])).
% 2.05/2.28  thf('112', plain, ((v1_funct_1 @ sk_C)),
% 2.05/2.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.05/2.28  thf('113', plain,
% 2.05/2.28      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 2.05/2.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.05/2.28  thf('114', plain, ((l1_pre_topc @ sk_A)),
% 2.05/2.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.05/2.28  thf('115', plain, ((v2_pre_topc @ sk_A)),
% 2.05/2.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.05/2.28  thf('116', plain,
% 2.05/2.28      (![X0 : $i, X1 : $i]:
% 2.05/2.28         ((v2_struct_0 @ X0)
% 2.05/2.28          | ~ (v2_pre_topc @ X0)
% 2.05/2.28          | ~ (l1_pre_topc @ X0)
% 2.05/2.28          | ~ (m1_pre_topc @ sk_B @ X0)
% 2.05/2.28          | ((k3_tmap_1 @ X0 @ sk_A @ sk_B @ X1 @ sk_C)
% 2.05/2.28              = (k2_partfun1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 2.05/2.28                 sk_C @ (u1_struct_0 @ X1)))
% 2.05/2.28          | ~ (m1_pre_topc @ X1 @ sk_B)
% 2.05/2.28          | ~ (m1_pre_topc @ X1 @ X0)
% 2.05/2.28          | (v2_struct_0 @ sk_A))),
% 2.05/2.28      inference('demod', [status(thm)], ['111', '112', '113', '114', '115'])).
% 2.05/2.28  thf('117', plain,
% 2.05/2.28      (![X0 : $i]:
% 2.05/2.28         (~ (l1_pre_topc @ sk_B)
% 2.05/2.28          | (v2_struct_0 @ sk_A)
% 2.05/2.28          | ~ (m1_pre_topc @ X0 @ sk_B)
% 2.05/2.28          | ~ (m1_pre_topc @ X0 @ sk_B)
% 2.05/2.28          | ((k3_tmap_1 @ sk_B @ sk_A @ sk_B @ X0 @ sk_C)
% 2.05/2.28              = (k2_partfun1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 2.05/2.28                 sk_C @ (u1_struct_0 @ X0)))
% 2.05/2.28          | ~ (l1_pre_topc @ sk_B)
% 2.05/2.28          | ~ (v2_pre_topc @ sk_B)
% 2.05/2.28          | (v2_struct_0 @ sk_B))),
% 2.05/2.28      inference('sup-', [status(thm)], ['108', '116'])).
% 2.05/2.28  thf('118', plain, ((l1_pre_topc @ sk_B)),
% 2.05/2.28      inference('demod', [status(thm)], ['21', '22'])).
% 2.05/2.28  thf('119', plain, ((l1_pre_topc @ sk_B)),
% 2.05/2.28      inference('demod', [status(thm)], ['21', '22'])).
% 2.05/2.28  thf('120', plain, ((v2_pre_topc @ sk_B)),
% 2.05/2.28      inference('demod', [status(thm)], ['26', '27', '28'])).
% 2.05/2.28  thf('121', plain,
% 2.05/2.28      (![X0 : $i]:
% 2.05/2.28         ((v2_struct_0 @ sk_A)
% 2.05/2.28          | ~ (m1_pre_topc @ X0 @ sk_B)
% 2.05/2.28          | ~ (m1_pre_topc @ X0 @ sk_B)
% 2.05/2.28          | ((k3_tmap_1 @ sk_B @ sk_A @ sk_B @ X0 @ sk_C)
% 2.05/2.28              = (k2_partfun1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 2.05/2.28                 sk_C @ (u1_struct_0 @ X0)))
% 2.05/2.28          | (v2_struct_0 @ sk_B))),
% 2.05/2.28      inference('demod', [status(thm)], ['117', '118', '119', '120'])).
% 2.05/2.28  thf('122', plain,
% 2.05/2.28      (![X0 : $i]:
% 2.05/2.28         ((v2_struct_0 @ sk_B)
% 2.05/2.28          | ((k3_tmap_1 @ sk_B @ sk_A @ sk_B @ X0 @ sk_C)
% 2.05/2.28              = (k2_partfun1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 2.05/2.28                 sk_C @ (u1_struct_0 @ X0)))
% 2.05/2.28          | ~ (m1_pre_topc @ X0 @ sk_B)
% 2.05/2.28          | (v2_struct_0 @ sk_A))),
% 2.05/2.28      inference('simplify', [status(thm)], ['121'])).
% 2.05/2.28  thf('123', plain,
% 2.05/2.28      ((~ (l1_pre_topc @ sk_B)
% 2.05/2.28        | (v2_struct_0 @ sk_A)
% 2.05/2.28        | ((k3_tmap_1 @ sk_B @ sk_A @ sk_B @ sk_B @ sk_C)
% 2.05/2.28            = (k2_partfun1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 2.05/2.28               sk_C @ (u1_struct_0 @ sk_B)))
% 2.05/2.28        | (v2_struct_0 @ sk_B))),
% 2.05/2.28      inference('sup-', [status(thm)], ['107', '122'])).
% 2.05/2.28  thf('124', plain, ((l1_pre_topc @ sk_B)),
% 2.05/2.28      inference('demod', [status(thm)], ['21', '22'])).
% 2.05/2.28  thf('125', plain,
% 2.05/2.28      (![X35 : $i]: ((m1_pre_topc @ X35 @ X35) | ~ (l1_pre_topc @ X35))),
% 2.05/2.28      inference('cnf', [status(esa)], [t2_tsep_1])).
% 2.05/2.28  thf('126', plain,
% 2.05/2.28      ((m1_subset_1 @ sk_C @ 
% 2.05/2.28        (k1_zfmisc_1 @ 
% 2.05/2.28         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 2.05/2.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.05/2.28  thf(d4_tmap_1, axiom,
% 2.05/2.28    (![A:$i]:
% 2.05/2.28     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 2.05/2.28       ( ![B:$i]:
% 2.05/2.28         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 2.05/2.28             ( l1_pre_topc @ B ) ) =>
% 2.05/2.28           ( ![C:$i]:
% 2.05/2.28             ( ( ( v1_funct_1 @ C ) & 
% 2.05/2.28                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 2.05/2.28                 ( m1_subset_1 @
% 2.05/2.28                   C @ 
% 2.05/2.28                   ( k1_zfmisc_1 @
% 2.05/2.28                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 2.05/2.28               ( ![D:$i]:
% 2.05/2.28                 ( ( m1_pre_topc @ D @ A ) =>
% 2.05/2.28                   ( ( k2_tmap_1 @ A @ B @ C @ D ) =
% 2.05/2.28                     ( k2_partfun1 @
% 2.05/2.28                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ 
% 2.05/2.28                       ( u1_struct_0 @ D ) ) ) ) ) ) ) ) ) ))).
% 2.05/2.28  thf('127', plain,
% 2.05/2.28      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 2.05/2.28         ((v2_struct_0 @ X19)
% 2.05/2.28          | ~ (v2_pre_topc @ X19)
% 2.05/2.28          | ~ (l1_pre_topc @ X19)
% 2.05/2.28          | ~ (m1_pre_topc @ X20 @ X21)
% 2.05/2.28          | ((k2_tmap_1 @ X21 @ X19 @ X22 @ X20)
% 2.05/2.28              = (k2_partfun1 @ (u1_struct_0 @ X21) @ (u1_struct_0 @ X19) @ 
% 2.05/2.28                 X22 @ (u1_struct_0 @ X20)))
% 2.05/2.28          | ~ (m1_subset_1 @ X22 @ 
% 2.05/2.28               (k1_zfmisc_1 @ 
% 2.05/2.28                (k2_zfmisc_1 @ (u1_struct_0 @ X21) @ (u1_struct_0 @ X19))))
% 2.05/2.28          | ~ (v1_funct_2 @ X22 @ (u1_struct_0 @ X21) @ (u1_struct_0 @ X19))
% 2.05/2.28          | ~ (v1_funct_1 @ X22)
% 2.05/2.28          | ~ (l1_pre_topc @ X21)
% 2.05/2.28          | ~ (v2_pre_topc @ X21)
% 2.05/2.28          | (v2_struct_0 @ X21))),
% 2.05/2.28      inference('cnf', [status(esa)], [d4_tmap_1])).
% 2.05/2.28  thf('128', plain,
% 2.05/2.28      (![X0 : $i]:
% 2.05/2.28         ((v2_struct_0 @ sk_B)
% 2.05/2.28          | ~ (v2_pre_topc @ sk_B)
% 2.05/2.28          | ~ (l1_pre_topc @ sk_B)
% 2.05/2.28          | ~ (v1_funct_1 @ sk_C)
% 2.05/2.28          | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 2.05/2.28          | ((k2_tmap_1 @ sk_B @ sk_A @ sk_C @ X0)
% 2.05/2.28              = (k2_partfun1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 2.05/2.28                 sk_C @ (u1_struct_0 @ X0)))
% 2.05/2.28          | ~ (m1_pre_topc @ X0 @ sk_B)
% 2.05/2.28          | ~ (l1_pre_topc @ sk_A)
% 2.05/2.28          | ~ (v2_pre_topc @ sk_A)
% 2.05/2.28          | (v2_struct_0 @ sk_A))),
% 2.05/2.28      inference('sup-', [status(thm)], ['126', '127'])).
% 2.05/2.28  thf('129', plain, ((v2_pre_topc @ sk_B)),
% 2.05/2.28      inference('demod', [status(thm)], ['26', '27', '28'])).
% 2.05/2.28  thf('130', plain, ((l1_pre_topc @ sk_B)),
% 2.05/2.28      inference('demod', [status(thm)], ['21', '22'])).
% 2.05/2.28  thf('131', plain, ((v1_funct_1 @ sk_C)),
% 2.05/2.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.05/2.28  thf('132', plain,
% 2.05/2.28      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 2.05/2.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.05/2.28  thf('133', plain, ((l1_pre_topc @ sk_A)),
% 2.05/2.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.05/2.28  thf('134', plain, ((v2_pre_topc @ sk_A)),
% 2.05/2.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.05/2.28  thf('135', plain,
% 2.05/2.28      (![X0 : $i]:
% 2.05/2.28         ((v2_struct_0 @ sk_B)
% 2.05/2.28          | ((k2_tmap_1 @ sk_B @ sk_A @ sk_C @ X0)
% 2.05/2.28              = (k2_partfun1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 2.05/2.28                 sk_C @ (u1_struct_0 @ X0)))
% 2.05/2.28          | ~ (m1_pre_topc @ X0 @ sk_B)
% 2.05/2.28          | (v2_struct_0 @ sk_A))),
% 2.05/2.28      inference('demod', [status(thm)],
% 2.05/2.28                ['128', '129', '130', '131', '132', '133', '134'])).
% 2.05/2.28  thf('136', plain,
% 2.05/2.28      ((~ (l1_pre_topc @ sk_B)
% 2.05/2.28        | (v2_struct_0 @ sk_A)
% 2.05/2.28        | ((k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B)
% 2.05/2.28            = (k2_partfun1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 2.05/2.28               sk_C @ (u1_struct_0 @ sk_B)))
% 2.05/2.28        | (v2_struct_0 @ sk_B))),
% 2.05/2.28      inference('sup-', [status(thm)], ['125', '135'])).
% 2.05/2.28  thf('137', plain, ((l1_pre_topc @ sk_B)),
% 2.05/2.28      inference('demod', [status(thm)], ['21', '22'])).
% 2.05/2.28  thf('138', plain,
% 2.05/2.28      (((v2_struct_0 @ sk_A)
% 2.05/2.28        | ((k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B)
% 2.05/2.28            = (k2_partfun1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 2.05/2.28               sk_C @ (u1_struct_0 @ sk_B)))
% 2.05/2.28        | (v2_struct_0 @ sk_B))),
% 2.05/2.28      inference('demod', [status(thm)], ['136', '137'])).
% 2.05/2.28  thf('139', plain, (~ (v2_struct_0 @ sk_A)),
% 2.05/2.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.05/2.28  thf('140', plain,
% 2.05/2.28      (((v2_struct_0 @ sk_B)
% 2.05/2.28        | ((k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B)
% 2.05/2.28            = (k2_partfun1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 2.05/2.28               sk_C @ (u1_struct_0 @ sk_B))))),
% 2.05/2.28      inference('clc', [status(thm)], ['138', '139'])).
% 2.05/2.28  thf('141', plain, (~ (v2_struct_0 @ sk_B)),
% 2.05/2.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.05/2.28  thf('142', plain,
% 2.05/2.28      (((k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B)
% 2.05/2.28         = (k2_partfun1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 2.05/2.28            (u1_struct_0 @ sk_B)))),
% 2.05/2.28      inference('clc', [status(thm)], ['140', '141'])).
% 2.05/2.28  thf('143', plain,
% 2.05/2.28      (((v2_struct_0 @ sk_A)
% 2.05/2.28        | ((k3_tmap_1 @ sk_B @ sk_A @ sk_B @ sk_B @ sk_C)
% 2.05/2.28            = (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B))
% 2.05/2.28        | (v2_struct_0 @ sk_B))),
% 2.05/2.28      inference('demod', [status(thm)], ['123', '124', '142'])).
% 2.05/2.28  thf('144', plain, (~ (v2_struct_0 @ sk_A)),
% 2.05/2.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.05/2.28  thf('145', plain,
% 2.05/2.28      (((v2_struct_0 @ sk_B)
% 2.05/2.28        | ((k3_tmap_1 @ sk_B @ sk_A @ sk_B @ sk_B @ sk_C)
% 2.05/2.28            = (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B)))),
% 2.05/2.28      inference('clc', [status(thm)], ['143', '144'])).
% 2.05/2.28  thf('146', plain, (~ (v2_struct_0 @ sk_B)),
% 2.05/2.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.05/2.28  thf('147', plain,
% 2.05/2.28      (((k3_tmap_1 @ sk_B @ sk_A @ sk_B @ sk_B @ sk_C)
% 2.05/2.28         = (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B))),
% 2.05/2.28      inference('clc', [status(thm)], ['145', '146'])).
% 2.05/2.28  thf('148', plain,
% 2.05/2.28      (((k3_tmap_1 @ sk_B @ sk_A @ sk_B @ sk_B @ sk_C)
% 2.05/2.28         = (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B))),
% 2.05/2.28      inference('clc', [status(thm)], ['145', '146'])).
% 2.05/2.28  thf('149', plain,
% 2.05/2.28      ((((sk_C) = (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B))
% 2.05/2.28        | ~ (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 2.05/2.28             (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B)))),
% 2.05/2.28      inference('demod', [status(thm)], ['106', '147', '148'])).
% 2.05/2.28  thf('150', plain,
% 2.05/2.28      (![X35 : $i]: ((m1_pre_topc @ X35 @ X35) | ~ (l1_pre_topc @ X35))),
% 2.05/2.28      inference('cnf', [status(esa)], [t2_tsep_1])).
% 2.05/2.28  thf('151', plain,
% 2.05/2.28      ((m1_subset_1 @ sk_C @ 
% 2.05/2.28        (k1_zfmisc_1 @ 
% 2.05/2.28         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 2.05/2.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.05/2.28  thf(t74_tmap_1, axiom,
% 2.05/2.28    (![A:$i]:
% 2.05/2.28     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 2.05/2.28       ( ![B:$i]:
% 2.05/2.28         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 2.05/2.28             ( l1_pre_topc @ B ) ) =>
% 2.05/2.28           ( ![C:$i]:
% 2.05/2.28             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 2.05/2.28               ( ![D:$i]:
% 2.05/2.28                 ( ( ( v1_funct_1 @ D ) & 
% 2.05/2.28                     ( v1_funct_2 @
% 2.05/2.28                       D @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 2.05/2.28                     ( m1_subset_1 @
% 2.05/2.28                       D @ 
% 2.05/2.28                       ( k1_zfmisc_1 @
% 2.05/2.28                         ( k2_zfmisc_1 @
% 2.05/2.28                           ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 2.05/2.28                   ( r2_funct_2 @
% 2.05/2.28                     ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ D @ 
% 2.05/2.28                     ( k3_tmap_1 @ A @ B @ C @ C @ D ) ) ) ) ) ) ) ) ))).
% 2.05/2.28  thf('152', plain,
% 2.05/2.28      (![X41 : $i, X42 : $i, X43 : $i, X44 : $i]:
% 2.05/2.28         ((v2_struct_0 @ X41)
% 2.05/2.28          | ~ (v2_pre_topc @ X41)
% 2.05/2.28          | ~ (l1_pre_topc @ X41)
% 2.05/2.28          | ~ (v1_funct_1 @ X42)
% 2.05/2.28          | ~ (v1_funct_2 @ X42 @ (u1_struct_0 @ X43) @ (u1_struct_0 @ X41))
% 2.05/2.28          | ~ (m1_subset_1 @ X42 @ 
% 2.05/2.28               (k1_zfmisc_1 @ 
% 2.05/2.28                (k2_zfmisc_1 @ (u1_struct_0 @ X43) @ (u1_struct_0 @ X41))))
% 2.05/2.28          | (r2_funct_2 @ (u1_struct_0 @ X43) @ (u1_struct_0 @ X41) @ X42 @ 
% 2.05/2.28             (k3_tmap_1 @ X44 @ X41 @ X43 @ X43 @ X42))
% 2.05/2.28          | ~ (m1_pre_topc @ X43 @ X44)
% 2.05/2.28          | (v2_struct_0 @ X43)
% 2.05/2.28          | ~ (l1_pre_topc @ X44)
% 2.05/2.28          | ~ (v2_pre_topc @ X44)
% 2.05/2.28          | (v2_struct_0 @ X44))),
% 2.05/2.28      inference('cnf', [status(esa)], [t74_tmap_1])).
% 2.05/2.28  thf('153', plain,
% 2.05/2.28      (![X0 : $i]:
% 2.05/2.28         ((v2_struct_0 @ X0)
% 2.05/2.28          | ~ (v2_pre_topc @ X0)
% 2.05/2.28          | ~ (l1_pre_topc @ X0)
% 2.05/2.28          | (v2_struct_0 @ sk_B)
% 2.05/2.28          | ~ (m1_pre_topc @ sk_B @ X0)
% 2.05/2.28          | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 2.05/2.28             (k3_tmap_1 @ X0 @ sk_A @ sk_B @ sk_B @ sk_C))
% 2.05/2.28          | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 2.05/2.28          | ~ (v1_funct_1 @ sk_C)
% 2.05/2.28          | ~ (l1_pre_topc @ sk_A)
% 2.05/2.28          | ~ (v2_pre_topc @ sk_A)
% 2.05/2.28          | (v2_struct_0 @ sk_A))),
% 2.05/2.28      inference('sup-', [status(thm)], ['151', '152'])).
% 2.05/2.28  thf('154', plain,
% 2.05/2.28      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 2.05/2.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.05/2.28  thf('155', plain, ((v1_funct_1 @ sk_C)),
% 2.05/2.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.05/2.28  thf('156', plain, ((l1_pre_topc @ sk_A)),
% 2.05/2.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.05/2.28  thf('157', plain, ((v2_pre_topc @ sk_A)),
% 2.05/2.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.05/2.28  thf('158', plain,
% 2.05/2.28      (![X0 : $i]:
% 2.05/2.28         ((v2_struct_0 @ X0)
% 2.05/2.28          | ~ (v2_pre_topc @ X0)
% 2.05/2.28          | ~ (l1_pre_topc @ X0)
% 2.05/2.28          | (v2_struct_0 @ sk_B)
% 2.05/2.28          | ~ (m1_pre_topc @ sk_B @ X0)
% 2.05/2.28          | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 2.05/2.28             (k3_tmap_1 @ X0 @ sk_A @ sk_B @ sk_B @ sk_C))
% 2.05/2.28          | (v2_struct_0 @ sk_A))),
% 2.05/2.28      inference('demod', [status(thm)], ['153', '154', '155', '156', '157'])).
% 2.05/2.28  thf('159', plain,
% 2.05/2.28      ((~ (l1_pre_topc @ sk_B)
% 2.05/2.28        | (v2_struct_0 @ sk_A)
% 2.05/2.28        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 2.05/2.28           (k3_tmap_1 @ sk_B @ sk_A @ sk_B @ sk_B @ sk_C))
% 2.05/2.28        | (v2_struct_0 @ sk_B)
% 2.05/2.28        | ~ (l1_pre_topc @ sk_B)
% 2.05/2.28        | ~ (v2_pre_topc @ sk_B)
% 2.05/2.28        | (v2_struct_0 @ sk_B))),
% 2.05/2.28      inference('sup-', [status(thm)], ['150', '158'])).
% 2.05/2.28  thf('160', plain, ((l1_pre_topc @ sk_B)),
% 2.05/2.28      inference('demod', [status(thm)], ['21', '22'])).
% 2.05/2.28  thf('161', plain,
% 2.05/2.28      (((k3_tmap_1 @ sk_B @ sk_A @ sk_B @ sk_B @ sk_C)
% 2.05/2.28         = (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B))),
% 2.05/2.28      inference('clc', [status(thm)], ['145', '146'])).
% 2.05/2.28  thf('162', plain, ((l1_pre_topc @ sk_B)),
% 2.05/2.28      inference('demod', [status(thm)], ['21', '22'])).
% 2.05/2.28  thf('163', plain, ((v2_pre_topc @ sk_B)),
% 2.05/2.28      inference('demod', [status(thm)], ['26', '27', '28'])).
% 2.05/2.28  thf('164', plain,
% 2.05/2.28      (((v2_struct_0 @ sk_A)
% 2.05/2.28        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 2.05/2.28           (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B))
% 2.05/2.28        | (v2_struct_0 @ sk_B)
% 2.05/2.28        | (v2_struct_0 @ sk_B))),
% 2.05/2.28      inference('demod', [status(thm)], ['159', '160', '161', '162', '163'])).
% 2.05/2.28  thf('165', plain,
% 2.05/2.28      (((v2_struct_0 @ sk_B)
% 2.05/2.28        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 2.05/2.28           (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B))
% 2.05/2.28        | (v2_struct_0 @ sk_A))),
% 2.05/2.28      inference('simplify', [status(thm)], ['164'])).
% 2.05/2.28  thf('166', plain, (~ (v2_struct_0 @ sk_B)),
% 2.05/2.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.05/2.28  thf('167', plain,
% 2.05/2.28      (((v2_struct_0 @ sk_A)
% 2.05/2.28        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 2.05/2.28           (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B)))),
% 2.05/2.28      inference('clc', [status(thm)], ['165', '166'])).
% 2.05/2.28  thf('168', plain, (~ (v2_struct_0 @ sk_A)),
% 2.05/2.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.05/2.28  thf('169', plain,
% 2.05/2.28      ((r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 2.05/2.28        (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B))),
% 2.05/2.28      inference('clc', [status(thm)], ['167', '168'])).
% 2.05/2.28  thf('170', plain, (((sk_C) = (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B))),
% 2.05/2.28      inference('demod', [status(thm)], ['149', '169'])).
% 2.05/2.28  thf('171', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 2.05/2.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.05/2.28  thf('172', plain,
% 2.05/2.28      (![X33 : $i, X34 : $i]:
% 2.05/2.28         (~ (l1_pre_topc @ X33)
% 2.05/2.28          | ~ (v2_pre_topc @ X33)
% 2.05/2.28          | (v2_struct_0 @ X33)
% 2.05/2.28          | ~ (m1_pre_topc @ X34 @ X33)
% 2.05/2.28          | (v1_funct_2 @ (k4_tmap_1 @ X33 @ X34) @ (u1_struct_0 @ X34) @ 
% 2.05/2.28             (u1_struct_0 @ X33)))),
% 2.05/2.28      inference('cnf', [status(esa)], [dt_k4_tmap_1])).
% 2.05/2.28  thf('173', plain,
% 2.05/2.28      (((v1_funct_2 @ (k4_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_B) @ 
% 2.05/2.28         (u1_struct_0 @ sk_A))
% 2.05/2.28        | (v2_struct_0 @ sk_A)
% 2.05/2.28        | ~ (v2_pre_topc @ sk_A)
% 2.05/2.28        | ~ (l1_pre_topc @ sk_A))),
% 2.05/2.28      inference('sup-', [status(thm)], ['171', '172'])).
% 2.05/2.28  thf('174', plain, ((v2_pre_topc @ sk_A)),
% 2.05/2.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.05/2.28  thf('175', plain, ((l1_pre_topc @ sk_A)),
% 2.05/2.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.05/2.28  thf('176', plain,
% 2.05/2.28      (((v1_funct_2 @ (k4_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_B) @ 
% 2.05/2.28         (u1_struct_0 @ sk_A))
% 2.05/2.28        | (v2_struct_0 @ sk_A))),
% 2.05/2.28      inference('demod', [status(thm)], ['173', '174', '175'])).
% 2.05/2.28  thf('177', plain, (~ (v2_struct_0 @ sk_A)),
% 2.05/2.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.05/2.28  thf('178', plain,
% 2.05/2.28      ((v1_funct_2 @ (k4_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_B) @ 
% 2.05/2.28        (u1_struct_0 @ sk_A))),
% 2.05/2.28      inference('clc', [status(thm)], ['176', '177'])).
% 2.05/2.28  thf('179', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 2.05/2.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.05/2.28  thf('180', plain,
% 2.05/2.28      (![X33 : $i, X34 : $i]:
% 2.05/2.28         (~ (l1_pre_topc @ X33)
% 2.05/2.28          | ~ (v2_pre_topc @ X33)
% 2.05/2.28          | (v2_struct_0 @ X33)
% 2.05/2.28          | ~ (m1_pre_topc @ X34 @ X33)
% 2.05/2.28          | (v1_funct_1 @ (k4_tmap_1 @ X33 @ X34)))),
% 2.05/2.28      inference('cnf', [status(esa)], [dt_k4_tmap_1])).
% 2.05/2.28  thf('181', plain,
% 2.05/2.28      (((v1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_B))
% 2.05/2.28        | (v2_struct_0 @ sk_A)
% 2.05/2.28        | ~ (v2_pre_topc @ sk_A)
% 2.05/2.28        | ~ (l1_pre_topc @ sk_A))),
% 2.05/2.28      inference('sup-', [status(thm)], ['179', '180'])).
% 2.05/2.28  thf('182', plain, ((v2_pre_topc @ sk_A)),
% 2.05/2.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.05/2.28  thf('183', plain, ((l1_pre_topc @ sk_A)),
% 2.05/2.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.05/2.28  thf('184', plain,
% 2.05/2.28      (((v1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_B)) | (v2_struct_0 @ sk_A))),
% 2.05/2.28      inference('demod', [status(thm)], ['181', '182', '183'])).
% 2.05/2.28  thf('185', plain, (~ (v2_struct_0 @ sk_A)),
% 2.05/2.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.05/2.28  thf('186', plain, ((v1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_B))),
% 2.05/2.28      inference('clc', [status(thm)], ['184', '185'])).
% 2.05/2.28  thf('187', plain,
% 2.05/2.28      (((v2_struct_0 @ sk_B)
% 2.05/2.28        | (m1_subset_1 @ 
% 2.05/2.28           (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A) @ 
% 2.05/2.28           (u1_struct_0 @ sk_B))
% 2.05/2.28        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 2.05/2.28           (k4_tmap_1 @ sk_A @ sk_B))
% 2.05/2.28        | ~ (m1_pre_topc @ sk_B @ sk_B)
% 2.05/2.28        | (v2_struct_0 @ sk_B)
% 2.05/2.28        | (v2_struct_0 @ sk_A))),
% 2.05/2.28      inference('demod', [status(thm)], ['31', '170', '178', '186'])).
% 2.05/2.28  thf('188', plain,
% 2.05/2.28      (((v2_struct_0 @ sk_A)
% 2.05/2.28        | ~ (m1_pre_topc @ sk_B @ sk_B)
% 2.05/2.28        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 2.05/2.28           (k4_tmap_1 @ sk_A @ sk_B))
% 2.05/2.28        | (m1_subset_1 @ 
% 2.05/2.28           (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A) @ 
% 2.05/2.28           (u1_struct_0 @ sk_B))
% 2.05/2.28        | (v2_struct_0 @ sk_B))),
% 2.05/2.28      inference('simplify', [status(thm)], ['187'])).
% 2.05/2.28  thf('189', plain,
% 2.05/2.28      ((~ (l1_pre_topc @ sk_B)
% 2.05/2.28        | (v2_struct_0 @ sk_B)
% 2.05/2.28        | (m1_subset_1 @ 
% 2.05/2.28           (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A) @ 
% 2.05/2.28           (u1_struct_0 @ sk_B))
% 2.05/2.28        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 2.05/2.28           (k4_tmap_1 @ sk_A @ sk_B))
% 2.05/2.28        | (v2_struct_0 @ sk_A))),
% 2.05/2.28      inference('sup-', [status(thm)], ['3', '188'])).
% 2.05/2.28  thf('190', plain, ((l1_pre_topc @ sk_B)),
% 2.05/2.28      inference('demod', [status(thm)], ['21', '22'])).
% 2.05/2.28  thf('191', plain,
% 2.05/2.28      (((v2_struct_0 @ sk_B)
% 2.05/2.28        | (m1_subset_1 @ 
% 2.05/2.28           (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A) @ 
% 2.05/2.28           (u1_struct_0 @ sk_B))
% 2.05/2.28        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 2.05/2.28           (k4_tmap_1 @ sk_A @ sk_B))
% 2.05/2.28        | (v2_struct_0 @ sk_A))),
% 2.05/2.28      inference('demod', [status(thm)], ['189', '190'])).
% 2.05/2.28  thf(t55_pre_topc, axiom,
% 2.05/2.28    (![A:$i]:
% 2.05/2.28     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 2.05/2.28       ( ![B:$i]:
% 2.05/2.28         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 2.05/2.28           ( ![C:$i]:
% 2.05/2.28             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ B ) ) =>
% 2.05/2.28               ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) ) ) ) ))).
% 2.05/2.28  thf('192', plain,
% 2.05/2.28      (![X16 : $i, X17 : $i, X18 : $i]:
% 2.05/2.28         ((v2_struct_0 @ X16)
% 2.05/2.28          | ~ (m1_pre_topc @ X16 @ X17)
% 2.05/2.28          | (m1_subset_1 @ X18 @ (u1_struct_0 @ X17))
% 2.05/2.28          | ~ (m1_subset_1 @ X18 @ (u1_struct_0 @ X16))
% 2.05/2.28          | ~ (l1_pre_topc @ X17)
% 2.05/2.28          | (v2_struct_0 @ X17))),
% 2.05/2.28      inference('cnf', [status(esa)], [t55_pre_topc])).
% 2.05/2.28  thf('193', plain,
% 2.05/2.28      (![X0 : $i]:
% 2.05/2.28         ((v2_struct_0 @ sk_A)
% 2.05/2.28          | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 2.05/2.28             (k4_tmap_1 @ sk_A @ sk_B))
% 2.05/2.28          | (v2_struct_0 @ sk_B)
% 2.05/2.28          | (v2_struct_0 @ X0)
% 2.05/2.28          | ~ (l1_pre_topc @ X0)
% 2.05/2.28          | (m1_subset_1 @ 
% 2.05/2.28             (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A) @ 
% 2.05/2.28             (u1_struct_0 @ X0))
% 2.05/2.28          | ~ (m1_pre_topc @ sk_B @ X0)
% 2.05/2.28          | (v2_struct_0 @ sk_B))),
% 2.05/2.28      inference('sup-', [status(thm)], ['191', '192'])).
% 2.05/2.28  thf('194', plain,
% 2.05/2.28      (![X0 : $i]:
% 2.05/2.28         (~ (m1_pre_topc @ sk_B @ X0)
% 2.05/2.28          | (m1_subset_1 @ 
% 2.05/2.28             (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A) @ 
% 2.05/2.28             (u1_struct_0 @ X0))
% 2.05/2.28          | ~ (l1_pre_topc @ X0)
% 2.05/2.28          | (v2_struct_0 @ X0)
% 2.05/2.28          | (v2_struct_0 @ sk_B)
% 2.05/2.28          | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 2.05/2.28             (k4_tmap_1 @ sk_A @ sk_B))
% 2.05/2.28          | (v2_struct_0 @ sk_A))),
% 2.05/2.28      inference('simplify', [status(thm)], ['193'])).
% 2.05/2.28  thf('195', plain,
% 2.05/2.28      (((v2_struct_0 @ sk_A)
% 2.05/2.28        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 2.05/2.28           (k4_tmap_1 @ sk_A @ sk_B))
% 2.05/2.28        | (v2_struct_0 @ sk_B)
% 2.05/2.28        | (v2_struct_0 @ sk_A)
% 2.05/2.28        | ~ (l1_pre_topc @ sk_A)
% 2.05/2.28        | (m1_subset_1 @ 
% 2.05/2.28           (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A) @ 
% 2.05/2.28           (u1_struct_0 @ sk_A)))),
% 2.05/2.28      inference('sup-', [status(thm)], ['2', '194'])).
% 2.05/2.28  thf('196', plain, ((l1_pre_topc @ sk_A)),
% 2.05/2.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.05/2.28  thf('197', plain,
% 2.05/2.28      (((v2_struct_0 @ sk_A)
% 2.05/2.28        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 2.05/2.28           (k4_tmap_1 @ sk_A @ sk_B))
% 2.05/2.28        | (v2_struct_0 @ sk_B)
% 2.05/2.28        | (v2_struct_0 @ sk_A)
% 2.05/2.28        | (m1_subset_1 @ 
% 2.05/2.28           (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A) @ 
% 2.05/2.28           (u1_struct_0 @ sk_A)))),
% 2.05/2.28      inference('demod', [status(thm)], ['195', '196'])).
% 2.05/2.28  thf('198', plain,
% 2.05/2.28      (((m1_subset_1 @ 
% 2.05/2.28         (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A) @ 
% 2.05/2.28         (u1_struct_0 @ sk_A))
% 2.05/2.28        | (v2_struct_0 @ sk_B)
% 2.05/2.28        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 2.05/2.28           (k4_tmap_1 @ sk_A @ sk_B))
% 2.05/2.28        | (v2_struct_0 @ sk_A))),
% 2.05/2.28      inference('simplify', [status(thm)], ['197'])).
% 2.05/2.28  thf('199', plain,
% 2.05/2.28      (![X35 : $i]: ((m1_pre_topc @ X35 @ X35) | ~ (l1_pre_topc @ X35))),
% 2.05/2.28      inference('cnf', [status(esa)], [t2_tsep_1])).
% 2.05/2.28  thf('200', plain,
% 2.05/2.28      ((m1_subset_1 @ (k4_tmap_1 @ sk_A @ sk_B) @ 
% 2.05/2.28        (k1_zfmisc_1 @ 
% 2.05/2.28         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 2.05/2.28      inference('clc', [status(thm)], ['9', '10'])).
% 2.05/2.28  thf('201', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 2.05/2.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.05/2.28  thf('202', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 2.05/2.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.05/2.28  thf('203', plain,
% 2.05/2.28      (![X0 : $i, X1 : $i]:
% 2.05/2.28         ((m1_subset_1 @ (k3_tmap_1 @ X1 @ sk_A @ sk_B @ X0 @ sk_C) @ 
% 2.05/2.28           (k1_zfmisc_1 @ 
% 2.05/2.28            (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A))))
% 2.05/2.28          | (v2_struct_0 @ X1)
% 2.05/2.28          | ~ (v2_pre_topc @ X1)
% 2.05/2.28          | ~ (l1_pre_topc @ X1)
% 2.05/2.28          | (v2_struct_0 @ sk_A)
% 2.05/2.28          | ~ (m1_pre_topc @ sk_B @ X1)
% 2.05/2.28          | ~ (m1_pre_topc @ X0 @ X1))),
% 2.05/2.28      inference('demod', [status(thm)], ['36', '37', '38', '39', '40'])).
% 2.05/2.28  thf('204', plain,
% 2.05/2.28      (![X0 : $i]:
% 2.05/2.28         (~ (m1_pre_topc @ X0 @ sk_A)
% 2.05/2.28          | (v2_struct_0 @ sk_A)
% 2.05/2.28          | ~ (l1_pre_topc @ sk_A)
% 2.05/2.28          | ~ (v2_pre_topc @ sk_A)
% 2.05/2.28          | (v2_struct_0 @ sk_A)
% 2.05/2.28          | (m1_subset_1 @ (k3_tmap_1 @ sk_A @ sk_A @ sk_B @ X0 @ sk_C) @ 
% 2.05/2.28             (k1_zfmisc_1 @ 
% 2.05/2.28              (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A)))))),
% 2.05/2.28      inference('sup-', [status(thm)], ['202', '203'])).
% 2.05/2.28  thf('205', plain, ((l1_pre_topc @ sk_A)),
% 2.05/2.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.05/2.28  thf('206', plain, ((v2_pre_topc @ sk_A)),
% 2.05/2.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.05/2.28  thf('207', plain,
% 2.05/2.28      (![X0 : $i]:
% 2.05/2.28         (~ (m1_pre_topc @ X0 @ sk_A)
% 2.05/2.28          | (v2_struct_0 @ sk_A)
% 2.05/2.28          | (v2_struct_0 @ sk_A)
% 2.05/2.28          | (m1_subset_1 @ (k3_tmap_1 @ sk_A @ sk_A @ sk_B @ X0 @ sk_C) @ 
% 2.05/2.28             (k1_zfmisc_1 @ 
% 2.05/2.28              (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A)))))),
% 2.05/2.28      inference('demod', [status(thm)], ['204', '205', '206'])).
% 2.05/2.28  thf('208', plain,
% 2.05/2.28      (![X0 : $i]:
% 2.05/2.28         ((m1_subset_1 @ (k3_tmap_1 @ sk_A @ sk_A @ sk_B @ X0 @ sk_C) @ 
% 2.05/2.28           (k1_zfmisc_1 @ 
% 2.05/2.28            (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A))))
% 2.05/2.28          | (v2_struct_0 @ sk_A)
% 2.05/2.28          | ~ (m1_pre_topc @ X0 @ sk_A))),
% 2.05/2.28      inference('simplify', [status(thm)], ['207'])).
% 2.05/2.28  thf('209', plain, (~ (v2_struct_0 @ sk_A)),
% 2.05/2.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.05/2.28  thf('210', plain,
% 2.05/2.28      (![X0 : $i]:
% 2.05/2.28         (~ (m1_pre_topc @ X0 @ sk_A)
% 2.05/2.28          | (m1_subset_1 @ (k3_tmap_1 @ sk_A @ sk_A @ sk_B @ X0 @ sk_C) @ 
% 2.05/2.28             (k1_zfmisc_1 @ 
% 2.05/2.28              (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A)))))),
% 2.05/2.28      inference('clc', [status(thm)], ['208', '209'])).
% 2.05/2.28  thf('211', plain,
% 2.05/2.28      ((m1_subset_1 @ (k3_tmap_1 @ sk_A @ sk_A @ sk_B @ sk_B @ sk_C) @ 
% 2.05/2.28        (k1_zfmisc_1 @ 
% 2.05/2.28         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 2.05/2.28      inference('sup-', [status(thm)], ['201', '210'])).
% 2.05/2.28  thf('212', plain,
% 2.05/2.28      (![X36 : $i, X37 : $i, X38 : $i, X39 : $i, X40 : $i]:
% 2.05/2.28         ((v2_struct_0 @ X36)
% 2.05/2.28          | ~ (v2_pre_topc @ X36)
% 2.05/2.28          | ~ (l1_pre_topc @ X36)
% 2.05/2.28          | ~ (v1_funct_1 @ X37)
% 2.05/2.28          | ~ (v1_funct_2 @ X37 @ (u1_struct_0 @ X36) @ (u1_struct_0 @ X38))
% 2.05/2.28          | ~ (m1_subset_1 @ X37 @ 
% 2.05/2.28               (k1_zfmisc_1 @ 
% 2.05/2.28                (k2_zfmisc_1 @ (u1_struct_0 @ X36) @ (u1_struct_0 @ X38))))
% 2.05/2.28          | (r2_hidden @ (sk_F @ X39 @ X37 @ X40 @ X36 @ X38) @ 
% 2.05/2.28             (u1_struct_0 @ X40))
% 2.05/2.28          | (r2_funct_2 @ (u1_struct_0 @ X40) @ (u1_struct_0 @ X38) @ 
% 2.05/2.28             (k2_tmap_1 @ X36 @ X38 @ X37 @ X40) @ X39)
% 2.05/2.28          | ~ (m1_subset_1 @ X39 @ 
% 2.05/2.28               (k1_zfmisc_1 @ 
% 2.05/2.28                (k2_zfmisc_1 @ (u1_struct_0 @ X40) @ (u1_struct_0 @ X38))))
% 2.05/2.28          | ~ (v1_funct_2 @ X39 @ (u1_struct_0 @ X40) @ (u1_struct_0 @ X38))
% 2.05/2.28          | ~ (v1_funct_1 @ X39)
% 2.05/2.28          | ~ (m1_pre_topc @ X40 @ X36)
% 2.05/2.28          | (v2_struct_0 @ X40)
% 2.05/2.28          | ~ (l1_pre_topc @ X38)
% 2.05/2.28          | ~ (v2_pre_topc @ X38)
% 2.05/2.28          | (v2_struct_0 @ X38))),
% 2.05/2.28      inference('cnf', [status(esa)], [t59_tmap_1])).
% 2.05/2.28  thf('213', plain,
% 2.05/2.28      (![X0 : $i, X1 : $i]:
% 2.05/2.28         ((v2_struct_0 @ sk_A)
% 2.05/2.28          | ~ (v2_pre_topc @ sk_A)
% 2.05/2.28          | ~ (l1_pre_topc @ sk_A)
% 2.05/2.28          | (v2_struct_0 @ X0)
% 2.05/2.28          | ~ (m1_pre_topc @ X0 @ sk_B)
% 2.05/2.28          | ~ (v1_funct_1 @ X1)
% 2.05/2.28          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A))
% 2.05/2.28          | ~ (m1_subset_1 @ X1 @ 
% 2.05/2.28               (k1_zfmisc_1 @ 
% 2.05/2.28                (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A))))
% 2.05/2.28          | (r2_funct_2 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A) @ 
% 2.05/2.28             (k2_tmap_1 @ sk_B @ sk_A @ 
% 2.05/2.28              (k3_tmap_1 @ sk_A @ sk_A @ sk_B @ sk_B @ sk_C) @ X0) @ 
% 2.05/2.28             X1)
% 2.05/2.28          | (r2_hidden @ 
% 2.05/2.28             (sk_F @ X1 @ (k3_tmap_1 @ sk_A @ sk_A @ sk_B @ sk_B @ sk_C) @ 
% 2.05/2.28              X0 @ sk_B @ sk_A) @ 
% 2.05/2.28             (u1_struct_0 @ X0))
% 2.05/2.28          | ~ (v1_funct_2 @ (k3_tmap_1 @ sk_A @ sk_A @ sk_B @ sk_B @ sk_C) @ 
% 2.05/2.28               (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 2.05/2.28          | ~ (v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_A @ sk_B @ sk_B @ sk_C))
% 2.05/2.28          | ~ (l1_pre_topc @ sk_B)
% 2.05/2.28          | ~ (v2_pre_topc @ sk_B)
% 2.05/2.28          | (v2_struct_0 @ sk_B))),
% 2.05/2.28      inference('sup-', [status(thm)], ['211', '212'])).
% 2.05/2.28  thf('214', plain, ((v2_pre_topc @ sk_A)),
% 2.05/2.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.05/2.28  thf('215', plain, ((l1_pre_topc @ sk_A)),
% 2.05/2.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.05/2.28  thf('216', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 2.05/2.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.05/2.28  thf('217', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 2.05/2.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.05/2.28  thf('218', plain,
% 2.05/2.28      (![X0 : $i, X1 : $i]:
% 2.05/2.28         ((v1_funct_1 @ (k3_tmap_1 @ X1 @ sk_A @ sk_B @ X0 @ sk_C))
% 2.05/2.28          | (v2_struct_0 @ X1)
% 2.05/2.28          | ~ (v2_pre_topc @ X1)
% 2.05/2.28          | ~ (l1_pre_topc @ X1)
% 2.05/2.28          | (v2_struct_0 @ sk_A)
% 2.05/2.28          | ~ (m1_pre_topc @ sk_B @ X1)
% 2.05/2.28          | ~ (m1_pre_topc @ X0 @ X1))),
% 2.05/2.28      inference('demod', [status(thm)], ['65', '66', '67', '68', '69'])).
% 2.05/2.28  thf('219', plain,
% 2.05/2.28      (![X0 : $i]:
% 2.05/2.28         (~ (m1_pre_topc @ X0 @ sk_A)
% 2.05/2.28          | (v2_struct_0 @ sk_A)
% 2.05/2.28          | ~ (l1_pre_topc @ sk_A)
% 2.05/2.28          | ~ (v2_pre_topc @ sk_A)
% 2.05/2.28          | (v2_struct_0 @ sk_A)
% 2.05/2.28          | (v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_A @ sk_B @ X0 @ sk_C)))),
% 2.05/2.28      inference('sup-', [status(thm)], ['217', '218'])).
% 2.05/2.28  thf('220', plain, ((l1_pre_topc @ sk_A)),
% 2.05/2.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.05/2.28  thf('221', plain, ((v2_pre_topc @ sk_A)),
% 2.05/2.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.05/2.28  thf('222', plain,
% 2.05/2.28      (![X0 : $i]:
% 2.05/2.28         (~ (m1_pre_topc @ X0 @ sk_A)
% 2.05/2.28          | (v2_struct_0 @ sk_A)
% 2.05/2.28          | (v2_struct_0 @ sk_A)
% 2.05/2.28          | (v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_A @ sk_B @ X0 @ sk_C)))),
% 2.05/2.28      inference('demod', [status(thm)], ['219', '220', '221'])).
% 2.05/2.28  thf('223', plain,
% 2.05/2.28      (![X0 : $i]:
% 2.05/2.28         ((v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_A @ sk_B @ X0 @ sk_C))
% 2.05/2.28          | (v2_struct_0 @ sk_A)
% 2.05/2.28          | ~ (m1_pre_topc @ X0 @ sk_A))),
% 2.05/2.28      inference('simplify', [status(thm)], ['222'])).
% 2.05/2.28  thf('224', plain, (~ (v2_struct_0 @ sk_A)),
% 2.05/2.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.05/2.28  thf('225', plain,
% 2.05/2.28      (![X0 : $i]:
% 2.05/2.28         (~ (m1_pre_topc @ X0 @ sk_A)
% 2.05/2.28          | (v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_A @ sk_B @ X0 @ sk_C)))),
% 2.05/2.28      inference('clc', [status(thm)], ['223', '224'])).
% 2.05/2.28  thf('226', plain,
% 2.05/2.28      ((v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_A @ sk_B @ sk_B @ sk_C))),
% 2.05/2.28      inference('sup-', [status(thm)], ['216', '225'])).
% 2.05/2.28  thf('227', plain, ((l1_pre_topc @ sk_B)),
% 2.05/2.28      inference('demod', [status(thm)], ['21', '22'])).
% 2.05/2.28  thf('228', plain, ((v2_pre_topc @ sk_B)),
% 2.05/2.28      inference('demod', [status(thm)], ['26', '27', '28'])).
% 2.05/2.28  thf('229', plain,
% 2.05/2.28      (![X0 : $i, X1 : $i]:
% 2.05/2.28         ((v2_struct_0 @ sk_A)
% 2.05/2.28          | (v2_struct_0 @ X0)
% 2.05/2.28          | ~ (m1_pre_topc @ X0 @ sk_B)
% 2.05/2.28          | ~ (v1_funct_1 @ X1)
% 2.05/2.28          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A))
% 2.05/2.28          | ~ (m1_subset_1 @ X1 @ 
% 2.05/2.28               (k1_zfmisc_1 @ 
% 2.05/2.28                (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A))))
% 2.05/2.28          | (r2_funct_2 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A) @ 
% 2.05/2.28             (k2_tmap_1 @ sk_B @ sk_A @ 
% 2.05/2.28              (k3_tmap_1 @ sk_A @ sk_A @ sk_B @ sk_B @ sk_C) @ X0) @ 
% 2.05/2.28             X1)
% 2.05/2.28          | (r2_hidden @ 
% 2.05/2.28             (sk_F @ X1 @ (k3_tmap_1 @ sk_A @ sk_A @ sk_B @ sk_B @ sk_C) @ 
% 2.05/2.28              X0 @ sk_B @ sk_A) @ 
% 2.05/2.28             (u1_struct_0 @ X0))
% 2.05/2.28          | ~ (v1_funct_2 @ (k3_tmap_1 @ sk_A @ sk_A @ sk_B @ sk_B @ sk_C) @ 
% 2.05/2.28               (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 2.05/2.28          | (v2_struct_0 @ sk_B))),
% 2.05/2.28      inference('demod', [status(thm)],
% 2.05/2.28                ['213', '214', '215', '226', '227', '228'])).
% 2.05/2.28  thf('230', plain,
% 2.05/2.28      (![X35 : $i]: ((m1_pre_topc @ X35 @ X35) | ~ (l1_pre_topc @ X35))),
% 2.05/2.28      inference('cnf', [status(esa)], [t2_tsep_1])).
% 2.05/2.28  thf('231', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 2.05/2.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.05/2.28  thf('232', plain,
% 2.05/2.28      (![X0 : $i, X1 : $i]:
% 2.05/2.28         ((v2_struct_0 @ X0)
% 2.05/2.28          | ~ (v2_pre_topc @ X0)
% 2.05/2.28          | ~ (l1_pre_topc @ X0)
% 2.05/2.28          | ~ (m1_pre_topc @ sk_B @ X0)
% 2.05/2.28          | ((k3_tmap_1 @ X0 @ sk_A @ sk_B @ X1 @ sk_C)
% 2.05/2.28              = (k2_partfun1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 2.05/2.28                 sk_C @ (u1_struct_0 @ X1)))
% 2.05/2.28          | ~ (m1_pre_topc @ X1 @ sk_B)
% 2.05/2.28          | ~ (m1_pre_topc @ X1 @ X0)
% 2.05/2.28          | (v2_struct_0 @ sk_A))),
% 2.05/2.28      inference('demod', [status(thm)], ['111', '112', '113', '114', '115'])).
% 2.05/2.28  thf('233', plain,
% 2.05/2.28      (![X0 : $i]:
% 2.05/2.28         ((v2_struct_0 @ sk_A)
% 2.05/2.28          | ~ (m1_pre_topc @ X0 @ sk_A)
% 2.05/2.28          | ~ (m1_pre_topc @ X0 @ sk_B)
% 2.05/2.28          | ((k3_tmap_1 @ sk_A @ sk_A @ sk_B @ X0 @ sk_C)
% 2.05/2.28              = (k2_partfun1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 2.05/2.28                 sk_C @ (u1_struct_0 @ X0)))
% 2.05/2.28          | ~ (l1_pre_topc @ sk_A)
% 2.05/2.28          | ~ (v2_pre_topc @ sk_A)
% 2.05/2.28          | (v2_struct_0 @ sk_A))),
% 2.05/2.28      inference('sup-', [status(thm)], ['231', '232'])).
% 2.05/2.28  thf('234', plain, ((l1_pre_topc @ sk_A)),
% 2.05/2.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.05/2.28  thf('235', plain, ((v2_pre_topc @ sk_A)),
% 2.05/2.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.05/2.28  thf('236', plain,
% 2.05/2.28      (![X0 : $i]:
% 2.05/2.28         ((v2_struct_0 @ sk_A)
% 2.05/2.28          | ~ (m1_pre_topc @ X0 @ sk_A)
% 2.05/2.28          | ~ (m1_pre_topc @ X0 @ sk_B)
% 2.05/2.28          | ((k3_tmap_1 @ sk_A @ sk_A @ sk_B @ X0 @ sk_C)
% 2.05/2.28              = (k2_partfun1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 2.05/2.28                 sk_C @ (u1_struct_0 @ X0)))
% 2.05/2.28          | (v2_struct_0 @ sk_A))),
% 2.05/2.28      inference('demod', [status(thm)], ['233', '234', '235'])).
% 2.05/2.28  thf('237', plain,
% 2.05/2.28      (![X0 : $i]:
% 2.05/2.28         (((k3_tmap_1 @ sk_A @ sk_A @ sk_B @ X0 @ sk_C)
% 2.05/2.28            = (k2_partfun1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 2.05/2.28               sk_C @ (u1_struct_0 @ X0)))
% 2.05/2.28          | ~ (m1_pre_topc @ X0 @ sk_B)
% 2.05/2.28          | ~ (m1_pre_topc @ X0 @ sk_A)
% 2.05/2.28          | (v2_struct_0 @ sk_A))),
% 2.05/2.28      inference('simplify', [status(thm)], ['236'])).
% 2.05/2.28  thf('238', plain,
% 2.05/2.28      ((~ (l1_pre_topc @ sk_B)
% 2.05/2.28        | (v2_struct_0 @ sk_A)
% 2.05/2.28        | ~ (m1_pre_topc @ sk_B @ sk_A)
% 2.05/2.28        | ((k3_tmap_1 @ sk_A @ sk_A @ sk_B @ sk_B @ sk_C)
% 2.05/2.28            = (k2_partfun1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 2.05/2.28               sk_C @ (u1_struct_0 @ sk_B))))),
% 2.05/2.28      inference('sup-', [status(thm)], ['230', '237'])).
% 2.05/2.28  thf('239', plain, ((l1_pre_topc @ sk_B)),
% 2.05/2.28      inference('demod', [status(thm)], ['21', '22'])).
% 2.05/2.28  thf('240', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 2.05/2.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.05/2.28  thf('241', plain,
% 2.05/2.28      (((k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B)
% 2.05/2.28         = (k2_partfun1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 2.05/2.28            (u1_struct_0 @ sk_B)))),
% 2.05/2.28      inference('clc', [status(thm)], ['140', '141'])).
% 2.05/2.28  thf('242', plain,
% 2.05/2.28      (((v2_struct_0 @ sk_A)
% 2.05/2.28        | ((k3_tmap_1 @ sk_A @ sk_A @ sk_B @ sk_B @ sk_C)
% 2.05/2.28            = (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B)))),
% 2.05/2.28      inference('demod', [status(thm)], ['238', '239', '240', '241'])).
% 2.05/2.28  thf('243', plain, (~ (v2_struct_0 @ sk_A)),
% 2.05/2.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.05/2.28  thf('244', plain,
% 2.05/2.28      (((k3_tmap_1 @ sk_A @ sk_A @ sk_B @ sk_B @ sk_C)
% 2.05/2.28         = (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B))),
% 2.05/2.28      inference('clc', [status(thm)], ['242', '243'])).
% 2.05/2.28  thf('245', plain, (((sk_C) = (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B))),
% 2.05/2.28      inference('demod', [status(thm)], ['149', '169'])).
% 2.05/2.28  thf('246', plain,
% 2.05/2.28      (((k3_tmap_1 @ sk_A @ sk_A @ sk_B @ sk_B @ sk_C) = (sk_C))),
% 2.05/2.28      inference('demod', [status(thm)], ['244', '245'])).
% 2.05/2.28  thf('247', plain,
% 2.05/2.28      (((k3_tmap_1 @ sk_A @ sk_A @ sk_B @ sk_B @ sk_C) = (sk_C))),
% 2.05/2.28      inference('demod', [status(thm)], ['244', '245'])).
% 2.05/2.28  thf('248', plain,
% 2.05/2.28      (((k3_tmap_1 @ sk_A @ sk_A @ sk_B @ sk_B @ sk_C) = (sk_C))),
% 2.05/2.28      inference('demod', [status(thm)], ['244', '245'])).
% 2.05/2.28  thf('249', plain,
% 2.05/2.28      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 2.05/2.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.05/2.28  thf('250', plain,
% 2.05/2.28      (![X0 : $i, X1 : $i]:
% 2.05/2.28         ((v2_struct_0 @ sk_A)
% 2.05/2.28          | (v2_struct_0 @ X0)
% 2.05/2.28          | ~ (m1_pre_topc @ X0 @ sk_B)
% 2.05/2.28          | ~ (v1_funct_1 @ X1)
% 2.05/2.28          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A))
% 2.05/2.28          | ~ (m1_subset_1 @ X1 @ 
% 2.05/2.28               (k1_zfmisc_1 @ 
% 2.05/2.28                (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A))))
% 2.05/2.28          | (r2_funct_2 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A) @ 
% 2.05/2.28             (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ X0) @ X1)
% 2.05/2.28          | (r2_hidden @ (sk_F @ X1 @ sk_C @ X0 @ sk_B @ sk_A) @ 
% 2.05/2.28             (u1_struct_0 @ X0))
% 2.05/2.28          | (v2_struct_0 @ sk_B))),
% 2.05/2.28      inference('demod', [status(thm)], ['229', '246', '247', '248', '249'])).
% 2.05/2.28  thf('251', plain,
% 2.05/2.28      (((v2_struct_0 @ sk_B)
% 2.05/2.28        | (r2_hidden @ 
% 2.05/2.28           (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A) @ 
% 2.05/2.28           (u1_struct_0 @ sk_B))
% 2.05/2.28        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 2.05/2.28           (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B) @ (k4_tmap_1 @ sk_A @ sk_B))
% 2.05/2.28        | ~ (v1_funct_2 @ (k4_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_B) @ 
% 2.05/2.28             (u1_struct_0 @ sk_A))
% 2.05/2.28        | ~ (v1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_B))
% 2.05/2.28        | ~ (m1_pre_topc @ sk_B @ sk_B)
% 2.05/2.28        | (v2_struct_0 @ sk_B)
% 2.05/2.28        | (v2_struct_0 @ sk_A))),
% 2.05/2.28      inference('sup-', [status(thm)], ['200', '250'])).
% 2.05/2.28  thf('252', plain, (((sk_C) = (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B))),
% 2.05/2.28      inference('demod', [status(thm)], ['149', '169'])).
% 2.05/2.28  thf('253', plain,
% 2.05/2.28      ((v1_funct_2 @ (k4_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_B) @ 
% 2.05/2.28        (u1_struct_0 @ sk_A))),
% 2.05/2.28      inference('clc', [status(thm)], ['176', '177'])).
% 2.05/2.28  thf('254', plain, ((v1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_B))),
% 2.05/2.28      inference('clc', [status(thm)], ['184', '185'])).
% 2.05/2.28  thf('255', plain,
% 2.05/2.28      (((v2_struct_0 @ sk_B)
% 2.05/2.28        | (r2_hidden @ 
% 2.05/2.28           (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A) @ 
% 2.05/2.28           (u1_struct_0 @ sk_B))
% 2.05/2.28        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 2.05/2.28           (k4_tmap_1 @ sk_A @ sk_B))
% 2.05/2.28        | ~ (m1_pre_topc @ sk_B @ sk_B)
% 2.05/2.28        | (v2_struct_0 @ sk_B)
% 2.05/2.28        | (v2_struct_0 @ sk_A))),
% 2.05/2.28      inference('demod', [status(thm)], ['251', '252', '253', '254'])).
% 2.05/2.28  thf('256', plain,
% 2.05/2.28      (((v2_struct_0 @ sk_A)
% 2.05/2.28        | ~ (m1_pre_topc @ sk_B @ sk_B)
% 2.05/2.28        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 2.05/2.28           (k4_tmap_1 @ sk_A @ sk_B))
% 2.05/2.28        | (r2_hidden @ 
% 2.05/2.28           (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A) @ 
% 2.05/2.28           (u1_struct_0 @ sk_B))
% 2.05/2.28        | (v2_struct_0 @ sk_B))),
% 2.05/2.28      inference('simplify', [status(thm)], ['255'])).
% 2.05/2.28  thf('257', plain,
% 2.05/2.28      ((~ (l1_pre_topc @ sk_B)
% 2.05/2.28        | (v2_struct_0 @ sk_B)
% 2.05/2.28        | (r2_hidden @ 
% 2.05/2.28           (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A) @ 
% 2.05/2.28           (u1_struct_0 @ sk_B))
% 2.05/2.28        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 2.05/2.28           (k4_tmap_1 @ sk_A @ sk_B))
% 2.05/2.28        | (v2_struct_0 @ sk_A))),
% 2.05/2.28      inference('sup-', [status(thm)], ['199', '256'])).
% 2.05/2.28  thf('258', plain, ((l1_pre_topc @ sk_B)),
% 2.05/2.28      inference('demod', [status(thm)], ['21', '22'])).
% 2.05/2.28  thf('259', plain,
% 2.05/2.28      (((v2_struct_0 @ sk_B)
% 2.05/2.28        | (r2_hidden @ 
% 2.05/2.28           (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A) @ 
% 2.05/2.28           (u1_struct_0 @ sk_B))
% 2.05/2.28        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 2.05/2.28           (k4_tmap_1 @ sk_A @ sk_B))
% 2.05/2.28        | (v2_struct_0 @ sk_A))),
% 2.05/2.28      inference('demod', [status(thm)], ['257', '258'])).
% 2.05/2.28  thf('260', plain,
% 2.05/2.28      (![X51 : $i]:
% 2.05/2.28         (~ (r2_hidden @ X51 @ (u1_struct_0 @ sk_B))
% 2.05/2.28          | ((X51) = (k1_funct_1 @ sk_C @ X51))
% 2.05/2.28          | ~ (m1_subset_1 @ X51 @ (u1_struct_0 @ sk_A)))),
% 2.05/2.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.05/2.28  thf('261', plain,
% 2.05/2.28      (((v2_struct_0 @ sk_A)
% 2.05/2.28        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 2.05/2.28           (k4_tmap_1 @ sk_A @ sk_B))
% 2.05/2.28        | (v2_struct_0 @ sk_B)
% 2.05/2.28        | ~ (m1_subset_1 @ 
% 2.05/2.28             (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A) @ 
% 2.05/2.28             (u1_struct_0 @ sk_A))
% 2.05/2.28        | ((sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A)
% 2.05/2.28            = (k1_funct_1 @ sk_C @ 
% 2.05/2.28               (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A))))),
% 2.05/2.28      inference('sup-', [status(thm)], ['259', '260'])).
% 2.05/2.28  thf('262', plain,
% 2.05/2.28      (((v2_struct_0 @ sk_A)
% 2.05/2.28        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 2.05/2.28           (k4_tmap_1 @ sk_A @ sk_B))
% 2.05/2.28        | (v2_struct_0 @ sk_B)
% 2.05/2.28        | ((sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A)
% 2.05/2.28            = (k1_funct_1 @ sk_C @ 
% 2.05/2.28               (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A)))
% 2.05/2.28        | (v2_struct_0 @ sk_B)
% 2.05/2.28        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 2.05/2.28           (k4_tmap_1 @ sk_A @ sk_B))
% 2.05/2.28        | (v2_struct_0 @ sk_A))),
% 2.05/2.28      inference('sup-', [status(thm)], ['198', '261'])).
% 2.05/2.28  thf('263', plain,
% 2.05/2.28      ((((sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A)
% 2.05/2.28          = (k1_funct_1 @ sk_C @ 
% 2.05/2.28             (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A)))
% 2.05/2.28        | (v2_struct_0 @ sk_B)
% 2.05/2.28        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 2.05/2.28           (k4_tmap_1 @ sk_A @ sk_B))
% 2.05/2.28        | (v2_struct_0 @ sk_A))),
% 2.05/2.28      inference('simplify', [status(thm)], ['262'])).
% 2.05/2.28  thf('264', plain,
% 2.05/2.28      (((m1_subset_1 @ 
% 2.05/2.28         (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A) @ 
% 2.05/2.28         (u1_struct_0 @ sk_A))
% 2.05/2.28        | (v2_struct_0 @ sk_B)
% 2.05/2.28        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 2.05/2.28           (k4_tmap_1 @ sk_A @ sk_B))
% 2.05/2.28        | (v2_struct_0 @ sk_A))),
% 2.05/2.28      inference('simplify', [status(thm)], ['197'])).
% 2.05/2.28  thf('265', plain,
% 2.05/2.28      (((v2_struct_0 @ sk_B)
% 2.05/2.28        | (r2_hidden @ 
% 2.05/2.28           (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A) @ 
% 2.05/2.28           (u1_struct_0 @ sk_B))
% 2.05/2.28        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 2.05/2.28           (k4_tmap_1 @ sk_A @ sk_B))
% 2.05/2.28        | (v2_struct_0 @ sk_A))),
% 2.05/2.28      inference('demod', [status(thm)], ['257', '258'])).
% 2.05/2.28  thf(t95_tmap_1, axiom,
% 2.05/2.28    (![A:$i]:
% 2.05/2.28     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 2.05/2.28       ( ![B:$i]:
% 2.05/2.28         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 2.05/2.28           ( ![C:$i]:
% 2.05/2.28             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 2.05/2.28               ( ( r2_hidden @ C @ ( u1_struct_0 @ B ) ) =>
% 2.05/2.28                 ( ( k1_funct_1 @ ( k4_tmap_1 @ A @ B ) @ C ) = ( C ) ) ) ) ) ) ) ))).
% 2.05/2.28  thf('266', plain,
% 2.05/2.28      (![X48 : $i, X49 : $i, X50 : $i]:
% 2.05/2.28         ((v2_struct_0 @ X48)
% 2.05/2.28          | ~ (m1_pre_topc @ X48 @ X49)
% 2.05/2.28          | ~ (r2_hidden @ X50 @ (u1_struct_0 @ X48))
% 2.05/2.28          | ((k1_funct_1 @ (k4_tmap_1 @ X49 @ X48) @ X50) = (X50))
% 2.05/2.28          | ~ (m1_subset_1 @ X50 @ (u1_struct_0 @ X49))
% 2.05/2.28          | ~ (l1_pre_topc @ X49)
% 2.05/2.28          | ~ (v2_pre_topc @ X49)
% 2.05/2.28          | (v2_struct_0 @ X49))),
% 2.05/2.28      inference('cnf', [status(esa)], [t95_tmap_1])).
% 2.05/2.28  thf('267', plain,
% 2.05/2.28      (![X0 : $i]:
% 2.05/2.28         ((v2_struct_0 @ sk_A)
% 2.05/2.28          | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 2.05/2.28             (k4_tmap_1 @ sk_A @ sk_B))
% 2.05/2.28          | (v2_struct_0 @ sk_B)
% 2.05/2.28          | (v2_struct_0 @ X0)
% 2.05/2.28          | ~ (v2_pre_topc @ X0)
% 2.05/2.28          | ~ (l1_pre_topc @ X0)
% 2.05/2.28          | ~ (m1_subset_1 @ 
% 2.05/2.28               (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A) @ 
% 2.05/2.28               (u1_struct_0 @ X0))
% 2.05/2.28          | ((k1_funct_1 @ (k4_tmap_1 @ X0 @ sk_B) @ 
% 2.05/2.28              (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A))
% 2.05/2.28              = (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A))
% 2.05/2.28          | ~ (m1_pre_topc @ sk_B @ X0)
% 2.05/2.28          | (v2_struct_0 @ sk_B))),
% 2.05/2.28      inference('sup-', [status(thm)], ['265', '266'])).
% 2.05/2.28  thf('268', plain,
% 2.05/2.28      (![X0 : $i]:
% 2.05/2.28         (~ (m1_pre_topc @ sk_B @ X0)
% 2.05/2.28          | ((k1_funct_1 @ (k4_tmap_1 @ X0 @ sk_B) @ 
% 2.05/2.28              (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A))
% 2.05/2.28              = (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A))
% 2.05/2.28          | ~ (m1_subset_1 @ 
% 2.05/2.28               (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A) @ 
% 2.05/2.28               (u1_struct_0 @ X0))
% 2.05/2.28          | ~ (l1_pre_topc @ X0)
% 2.05/2.28          | ~ (v2_pre_topc @ X0)
% 2.05/2.28          | (v2_struct_0 @ X0)
% 2.05/2.28          | (v2_struct_0 @ sk_B)
% 2.05/2.28          | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 2.05/2.28             (k4_tmap_1 @ sk_A @ sk_B))
% 2.05/2.28          | (v2_struct_0 @ sk_A))),
% 2.05/2.28      inference('simplify', [status(thm)], ['267'])).
% 2.05/2.28  thf('269', plain,
% 2.05/2.28      (((v2_struct_0 @ sk_A)
% 2.05/2.28        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 2.05/2.28           (k4_tmap_1 @ sk_A @ sk_B))
% 2.05/2.28        | (v2_struct_0 @ sk_B)
% 2.05/2.28        | (v2_struct_0 @ sk_A)
% 2.05/2.28        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 2.05/2.28           (k4_tmap_1 @ sk_A @ sk_B))
% 2.05/2.28        | (v2_struct_0 @ sk_B)
% 2.05/2.28        | (v2_struct_0 @ sk_A)
% 2.05/2.28        | ~ (v2_pre_topc @ sk_A)
% 2.05/2.28        | ~ (l1_pre_topc @ sk_A)
% 2.05/2.28        | ((k1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_B) @ 
% 2.05/2.28            (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A))
% 2.05/2.28            = (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A))
% 2.05/2.28        | ~ (m1_pre_topc @ sk_B @ sk_A))),
% 2.05/2.28      inference('sup-', [status(thm)], ['264', '268'])).
% 2.05/2.28  thf('270', plain, ((v2_pre_topc @ sk_A)),
% 2.05/2.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.05/2.28  thf('271', plain, ((l1_pre_topc @ sk_A)),
% 2.05/2.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.05/2.28  thf('272', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 2.05/2.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.05/2.28  thf('273', plain,
% 2.05/2.28      (((v2_struct_0 @ sk_A)
% 2.05/2.28        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 2.05/2.28           (k4_tmap_1 @ sk_A @ sk_B))
% 2.05/2.28        | (v2_struct_0 @ sk_B)
% 2.05/2.28        | (v2_struct_0 @ sk_A)
% 2.05/2.28        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 2.05/2.28           (k4_tmap_1 @ sk_A @ sk_B))
% 2.05/2.28        | (v2_struct_0 @ sk_B)
% 2.05/2.28        | (v2_struct_0 @ sk_A)
% 2.05/2.28        | ((k1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_B) @ 
% 2.05/2.28            (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A))
% 2.05/2.28            = (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A)))),
% 2.05/2.28      inference('demod', [status(thm)], ['269', '270', '271', '272'])).
% 2.05/2.28  thf('274', plain,
% 2.05/2.28      ((((k1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_B) @ 
% 2.05/2.28          (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A))
% 2.05/2.28          = (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A))
% 2.05/2.28        | (v2_struct_0 @ sk_B)
% 2.05/2.28        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 2.05/2.28           (k4_tmap_1 @ sk_A @ sk_B))
% 2.05/2.28        | (v2_struct_0 @ sk_A))),
% 2.05/2.28      inference('simplify', [status(thm)], ['273'])).
% 2.05/2.28  thf('275', plain,
% 2.05/2.28      (((v2_struct_0 @ sk_B)
% 2.05/2.28        | (m1_subset_1 @ 
% 2.05/2.28           (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A) @ 
% 2.05/2.28           (u1_struct_0 @ sk_B))
% 2.05/2.28        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 2.05/2.28           (k4_tmap_1 @ sk_A @ sk_B))
% 2.05/2.28        | (v2_struct_0 @ sk_A))),
% 2.05/2.28      inference('demod', [status(thm)], ['189', '190'])).
% 2.05/2.28  thf('276', plain,
% 2.05/2.28      ((m1_subset_1 @ sk_C @ 
% 2.05/2.28        (k1_zfmisc_1 @ 
% 2.05/2.28         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 2.05/2.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.05/2.28  thf(redefinition_k3_funct_2, axiom,
% 2.05/2.28    (![A:$i,B:$i,C:$i,D:$i]:
% 2.05/2.28     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_funct_1 @ C ) & 
% 2.05/2.28         ( v1_funct_2 @ C @ A @ B ) & 
% 2.05/2.28         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 2.05/2.28         ( m1_subset_1 @ D @ A ) ) =>
% 2.05/2.28       ( ( k3_funct_2 @ A @ B @ C @ D ) = ( k1_funct_1 @ C @ D ) ) ))).
% 2.05/2.28  thf('277', plain,
% 2.05/2.28      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 2.05/2.28         (~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X4)))
% 2.05/2.28          | ~ (v1_funct_2 @ X2 @ X3 @ X4)
% 2.05/2.28          | ~ (v1_funct_1 @ X2)
% 2.05/2.28          | (v1_xboole_0 @ X3)
% 2.05/2.28          | ~ (m1_subset_1 @ X5 @ X3)
% 2.05/2.28          | ((k3_funct_2 @ X3 @ X4 @ X2 @ X5) = (k1_funct_1 @ X2 @ X5)))),
% 2.05/2.28      inference('cnf', [status(esa)], [redefinition_k3_funct_2])).
% 2.05/2.28  thf('278', plain,
% 2.05/2.28      (![X0 : $i]:
% 2.05/2.28         (((k3_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 2.05/2.28            X0) = (k1_funct_1 @ sk_C @ X0))
% 2.05/2.28          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B))
% 2.05/2.28          | (v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 2.05/2.28          | ~ (v1_funct_1 @ sk_C)
% 2.05/2.28          | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 2.05/2.28      inference('sup-', [status(thm)], ['276', '277'])).
% 2.05/2.28  thf('279', plain, ((v1_funct_1 @ sk_C)),
% 2.05/2.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.05/2.28  thf('280', plain,
% 2.05/2.28      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 2.05/2.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.05/2.28  thf('281', plain,
% 2.05/2.28      (![X0 : $i]:
% 2.05/2.28         (((k3_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 2.05/2.28            X0) = (k1_funct_1 @ sk_C @ X0))
% 2.05/2.28          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B))
% 2.05/2.28          | (v1_xboole_0 @ (u1_struct_0 @ sk_B)))),
% 2.05/2.28      inference('demod', [status(thm)], ['278', '279', '280'])).
% 2.05/2.28  thf('282', plain,
% 2.05/2.28      (((v2_struct_0 @ sk_A)
% 2.05/2.28        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 2.05/2.28           (k4_tmap_1 @ sk_A @ sk_B))
% 2.05/2.28        | (v2_struct_0 @ sk_B)
% 2.05/2.28        | (v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 2.05/2.28        | ((k3_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 2.05/2.28            (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A))
% 2.05/2.28            = (k1_funct_1 @ sk_C @ 
% 2.05/2.28               (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A))))),
% 2.05/2.28      inference('sup-', [status(thm)], ['275', '281'])).
% 2.05/2.28  thf('283', plain,
% 2.05/2.28      (![X36 : $i, X37 : $i, X38 : $i, X39 : $i, X40 : $i]:
% 2.05/2.28         ((v2_struct_0 @ X36)
% 2.05/2.28          | ~ (v2_pre_topc @ X36)
% 2.05/2.28          | ~ (l1_pre_topc @ X36)
% 2.05/2.28          | ~ (v1_funct_1 @ X37)
% 2.05/2.28          | ~ (v1_funct_2 @ X37 @ (u1_struct_0 @ X36) @ (u1_struct_0 @ X38))
% 2.05/2.28          | ~ (m1_subset_1 @ X37 @ 
% 2.05/2.28               (k1_zfmisc_1 @ 
% 2.05/2.28                (k2_zfmisc_1 @ (u1_struct_0 @ X36) @ (u1_struct_0 @ X38))))
% 2.05/2.28          | ((k3_funct_2 @ (u1_struct_0 @ X36) @ (u1_struct_0 @ X38) @ X37 @ 
% 2.05/2.28              (sk_F @ X39 @ X37 @ X40 @ X36 @ X38))
% 2.05/2.28              != (k1_funct_1 @ X39 @ (sk_F @ X39 @ X37 @ X40 @ X36 @ X38)))
% 2.05/2.28          | (r2_funct_2 @ (u1_struct_0 @ X40) @ (u1_struct_0 @ X38) @ 
% 2.05/2.28             (k2_tmap_1 @ X36 @ X38 @ X37 @ X40) @ X39)
% 2.05/2.28          | ~ (m1_subset_1 @ X39 @ 
% 2.05/2.28               (k1_zfmisc_1 @ 
% 2.05/2.28                (k2_zfmisc_1 @ (u1_struct_0 @ X40) @ (u1_struct_0 @ X38))))
% 2.05/2.28          | ~ (v1_funct_2 @ X39 @ (u1_struct_0 @ X40) @ (u1_struct_0 @ X38))
% 2.05/2.28          | ~ (v1_funct_1 @ X39)
% 2.05/2.28          | ~ (m1_pre_topc @ X40 @ X36)
% 2.05/2.28          | (v2_struct_0 @ X40)
% 2.05/2.28          | ~ (l1_pre_topc @ X38)
% 2.05/2.28          | ~ (v2_pre_topc @ X38)
% 2.05/2.28          | (v2_struct_0 @ X38))),
% 2.05/2.28      inference('cnf', [status(esa)], [t59_tmap_1])).
% 2.05/2.28  thf('284', plain,
% 2.05/2.28      ((((k1_funct_1 @ sk_C @ 
% 2.05/2.28          (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A))
% 2.05/2.28          != (k1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_B) @ 
% 2.05/2.28              (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A)))
% 2.05/2.28        | (v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 2.05/2.28        | (v2_struct_0 @ sk_B)
% 2.05/2.28        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 2.05/2.28           (k4_tmap_1 @ sk_A @ sk_B))
% 2.05/2.28        | (v2_struct_0 @ sk_A)
% 2.05/2.28        | (v2_struct_0 @ sk_A)
% 2.05/2.28        | ~ (v2_pre_topc @ sk_A)
% 2.05/2.28        | ~ (l1_pre_topc @ sk_A)
% 2.05/2.28        | (v2_struct_0 @ sk_B)
% 2.05/2.28        | ~ (m1_pre_topc @ sk_B @ sk_B)
% 2.05/2.28        | ~ (v1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_B))
% 2.05/2.28        | ~ (v1_funct_2 @ (k4_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_B) @ 
% 2.05/2.28             (u1_struct_0 @ sk_A))
% 2.05/2.28        | ~ (m1_subset_1 @ (k4_tmap_1 @ sk_A @ sk_B) @ 
% 2.05/2.28             (k1_zfmisc_1 @ 
% 2.05/2.28              (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))
% 2.05/2.28        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 2.05/2.28           (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B) @ (k4_tmap_1 @ sk_A @ sk_B))
% 2.05/2.28        | ~ (m1_subset_1 @ sk_C @ 
% 2.05/2.28             (k1_zfmisc_1 @ 
% 2.05/2.28              (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))
% 2.05/2.28        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 2.05/2.28        | ~ (v1_funct_1 @ sk_C)
% 2.05/2.28        | ~ (l1_pre_topc @ sk_B)
% 2.05/2.28        | ~ (v2_pre_topc @ sk_B)
% 2.05/2.28        | (v2_struct_0 @ sk_B))),
% 2.05/2.28      inference('sup-', [status(thm)], ['282', '283'])).
% 2.05/2.28  thf('285', plain, ((v2_pre_topc @ sk_A)),
% 2.05/2.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.05/2.28  thf('286', plain, ((l1_pre_topc @ sk_A)),
% 2.05/2.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.05/2.28  thf('287', plain, ((v1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_B))),
% 2.05/2.28      inference('clc', [status(thm)], ['184', '185'])).
% 2.05/2.28  thf('288', plain,
% 2.05/2.28      ((v1_funct_2 @ (k4_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_B) @ 
% 2.05/2.28        (u1_struct_0 @ sk_A))),
% 2.05/2.28      inference('clc', [status(thm)], ['176', '177'])).
% 2.05/2.28  thf('289', plain,
% 2.05/2.28      ((m1_subset_1 @ (k4_tmap_1 @ sk_A @ sk_B) @ 
% 2.05/2.28        (k1_zfmisc_1 @ 
% 2.05/2.28         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 2.05/2.28      inference('clc', [status(thm)], ['9', '10'])).
% 2.05/2.28  thf('290', plain, (((sk_C) = (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B))),
% 2.05/2.28      inference('demod', [status(thm)], ['149', '169'])).
% 2.05/2.28  thf('291', plain,
% 2.05/2.28      ((m1_subset_1 @ sk_C @ 
% 2.05/2.28        (k1_zfmisc_1 @ 
% 2.05/2.28         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 2.05/2.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.05/2.28  thf('292', plain,
% 2.05/2.28      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 2.05/2.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.05/2.28  thf('293', plain, ((v1_funct_1 @ sk_C)),
% 2.05/2.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.05/2.28  thf('294', plain, ((l1_pre_topc @ sk_B)),
% 2.05/2.28      inference('demod', [status(thm)], ['21', '22'])).
% 2.05/2.28  thf('295', plain, ((v2_pre_topc @ sk_B)),
% 2.05/2.28      inference('demod', [status(thm)], ['26', '27', '28'])).
% 2.05/2.28  thf('296', plain,
% 2.05/2.28      ((((k1_funct_1 @ sk_C @ 
% 2.05/2.28          (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A))
% 2.05/2.28          != (k1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_B) @ 
% 2.05/2.28              (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A)))
% 2.05/2.28        | (v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 2.05/2.28        | (v2_struct_0 @ sk_B)
% 2.05/2.28        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 2.05/2.28           (k4_tmap_1 @ sk_A @ sk_B))
% 2.05/2.28        | (v2_struct_0 @ sk_A)
% 2.05/2.28        | (v2_struct_0 @ sk_A)
% 2.05/2.28        | (v2_struct_0 @ sk_B)
% 2.05/2.28        | ~ (m1_pre_topc @ sk_B @ sk_B)
% 2.05/2.28        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 2.05/2.28           (k4_tmap_1 @ sk_A @ sk_B))
% 2.05/2.28        | (v2_struct_0 @ sk_B))),
% 2.05/2.28      inference('demod', [status(thm)],
% 2.05/2.28                ['284', '285', '286', '287', '288', '289', '290', '291', 
% 2.05/2.28                 '292', '293', '294', '295'])).
% 2.05/2.28  thf('297', plain,
% 2.05/2.28      ((~ (m1_pre_topc @ sk_B @ sk_B)
% 2.05/2.28        | (v2_struct_0 @ sk_A)
% 2.05/2.28        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 2.05/2.28           (k4_tmap_1 @ sk_A @ sk_B))
% 2.05/2.28        | (v2_struct_0 @ sk_B)
% 2.05/2.28        | (v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 2.05/2.28        | ((k1_funct_1 @ sk_C @ 
% 2.05/2.28            (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A))
% 2.05/2.28            != (k1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_B) @ 
% 2.05/2.28                (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A))))),
% 2.05/2.28      inference('simplify', [status(thm)], ['296'])).
% 2.05/2.28  thf('298', plain,
% 2.05/2.28      ((((k1_funct_1 @ sk_C @ 
% 2.05/2.28          (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A))
% 2.05/2.28          != (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A))
% 2.05/2.28        | (v2_struct_0 @ sk_A)
% 2.05/2.28        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 2.05/2.28           (k4_tmap_1 @ sk_A @ sk_B))
% 2.05/2.28        | (v2_struct_0 @ sk_B)
% 2.05/2.28        | (v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 2.05/2.28        | (v2_struct_0 @ sk_B)
% 2.05/2.28        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 2.05/2.28           (k4_tmap_1 @ sk_A @ sk_B))
% 2.05/2.28        | (v2_struct_0 @ sk_A)
% 2.05/2.28        | ~ (m1_pre_topc @ sk_B @ sk_B))),
% 2.05/2.28      inference('sup-', [status(thm)], ['274', '297'])).
% 2.05/2.28  thf('299', plain,
% 2.05/2.28      ((~ (m1_pre_topc @ sk_B @ sk_B)
% 2.05/2.28        | (v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 2.05/2.28        | (v2_struct_0 @ sk_B)
% 2.05/2.28        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 2.05/2.28           (k4_tmap_1 @ sk_A @ sk_B))
% 2.05/2.28        | (v2_struct_0 @ sk_A)
% 2.05/2.28        | ((k1_funct_1 @ sk_C @ 
% 2.05/2.28            (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A))
% 2.05/2.28            != (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A)))),
% 2.05/2.28      inference('simplify', [status(thm)], ['298'])).
% 2.05/2.28  thf('300', plain,
% 2.05/2.28      ((((sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A)
% 2.05/2.28          != (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A))
% 2.05/2.28        | (v2_struct_0 @ sk_A)
% 2.05/2.28        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 2.05/2.28           (k4_tmap_1 @ sk_A @ sk_B))
% 2.05/2.28        | (v2_struct_0 @ sk_B)
% 2.05/2.28        | (v2_struct_0 @ sk_A)
% 2.05/2.28        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 2.05/2.28           (k4_tmap_1 @ sk_A @ sk_B))
% 2.05/2.28        | (v2_struct_0 @ sk_B)
% 2.05/2.28        | (v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 2.05/2.28        | ~ (m1_pre_topc @ sk_B @ sk_B))),
% 2.05/2.28      inference('sup-', [status(thm)], ['263', '299'])).
% 2.05/2.28  thf('301', plain,
% 2.05/2.28      ((~ (m1_pre_topc @ sk_B @ sk_B)
% 2.05/2.28        | (v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 2.05/2.28        | (v2_struct_0 @ sk_B)
% 2.05/2.28        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 2.05/2.28           (k4_tmap_1 @ sk_A @ sk_B))
% 2.05/2.28        | (v2_struct_0 @ sk_A))),
% 2.05/2.28      inference('simplify', [status(thm)], ['300'])).
% 2.05/2.28  thf('302', plain,
% 2.05/2.28      ((~ (l1_pre_topc @ sk_B)
% 2.05/2.28        | (v2_struct_0 @ sk_A)
% 2.05/2.28        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 2.05/2.28           (k4_tmap_1 @ sk_A @ sk_B))
% 2.05/2.28        | (v2_struct_0 @ sk_B)
% 2.05/2.28        | (v1_xboole_0 @ (u1_struct_0 @ sk_B)))),
% 2.05/2.28      inference('sup-', [status(thm)], ['1', '301'])).
% 2.05/2.28  thf('303', plain, ((l1_pre_topc @ sk_B)),
% 2.05/2.28      inference('demod', [status(thm)], ['21', '22'])).
% 2.05/2.28  thf('304', plain,
% 2.05/2.28      (((v2_struct_0 @ sk_A)
% 2.05/2.28        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 2.05/2.28           (k4_tmap_1 @ sk_A @ sk_B))
% 2.05/2.28        | (v2_struct_0 @ sk_B)
% 2.05/2.28        | (v1_xboole_0 @ (u1_struct_0 @ sk_B)))),
% 2.05/2.28      inference('demod', [status(thm)], ['302', '303'])).
% 2.05/2.28  thf('305', plain,
% 2.05/2.28      ((m1_subset_1 @ (k4_tmap_1 @ sk_A @ sk_B) @ 
% 2.05/2.28        (k1_zfmisc_1 @ 
% 2.05/2.28         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 2.05/2.28      inference('clc', [status(thm)], ['9', '10'])).
% 2.05/2.28  thf('306', plain,
% 2.05/2.28      (![X0 : $i]:
% 2.05/2.28         (~ (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 2.05/2.28             X0)
% 2.05/2.28          | ((sk_C) = (X0))
% 2.05/2.28          | ~ (m1_subset_1 @ X0 @ 
% 2.05/2.28               (k1_zfmisc_1 @ 
% 2.05/2.28                (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))
% 2.05/2.28          | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 2.05/2.28          | ~ (v1_funct_1 @ X0))),
% 2.05/2.28      inference('demod', [status(thm)], ['56', '57', '58'])).
% 2.05/2.28  thf('307', plain,
% 2.05/2.28      ((~ (v1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_B))
% 2.05/2.28        | ~ (v1_funct_2 @ (k4_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_B) @ 
% 2.05/2.28             (u1_struct_0 @ sk_A))
% 2.05/2.28        | ((sk_C) = (k4_tmap_1 @ sk_A @ sk_B))
% 2.05/2.28        | ~ (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 2.05/2.28             (k4_tmap_1 @ sk_A @ sk_B)))),
% 2.05/2.28      inference('sup-', [status(thm)], ['305', '306'])).
% 2.05/2.28  thf('308', plain, ((v1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_B))),
% 2.05/2.28      inference('clc', [status(thm)], ['184', '185'])).
% 2.05/2.28  thf('309', plain,
% 2.05/2.28      ((v1_funct_2 @ (k4_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_B) @ 
% 2.05/2.28        (u1_struct_0 @ sk_A))),
% 2.05/2.28      inference('clc', [status(thm)], ['176', '177'])).
% 2.05/2.28  thf('310', plain,
% 2.05/2.28      ((((sk_C) = (k4_tmap_1 @ sk_A @ sk_B))
% 2.05/2.28        | ~ (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 2.05/2.28             (k4_tmap_1 @ sk_A @ sk_B)))),
% 2.05/2.28      inference('demod', [status(thm)], ['307', '308', '309'])).
% 2.05/2.28  thf('311', plain,
% 2.05/2.28      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 2.05/2.28        | (v2_struct_0 @ sk_B)
% 2.05/2.28        | (v2_struct_0 @ sk_A)
% 2.05/2.28        | ((sk_C) = (k4_tmap_1 @ sk_A @ sk_B)))),
% 2.05/2.28      inference('sup-', [status(thm)], ['304', '310'])).
% 2.05/2.28  thf('312', plain,
% 2.05/2.28      (~ (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 2.05/2.28          (k4_tmap_1 @ sk_A @ sk_B) @ sk_C)),
% 2.05/2.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.05/2.28  thf('313', plain,
% 2.05/2.28      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 2.05/2.28           sk_C)
% 2.05/2.28        | (v2_struct_0 @ sk_A)
% 2.05/2.28        | (v2_struct_0 @ sk_B)
% 2.05/2.28        | (v1_xboole_0 @ (u1_struct_0 @ sk_B)))),
% 2.05/2.28      inference('sup-', [status(thm)], ['311', '312'])).
% 2.05/2.28  thf('314', plain,
% 2.05/2.28      ((m1_subset_1 @ sk_C @ 
% 2.05/2.28        (k1_zfmisc_1 @ 
% 2.05/2.28         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 2.05/2.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.05/2.28  thf('315', plain,
% 2.05/2.28      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 2.05/2.28         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8)))
% 2.05/2.28          | ~ (v1_funct_2 @ X6 @ X7 @ X8)
% 2.05/2.28          | ~ (v1_funct_1 @ X6)
% 2.05/2.28          | ~ (v1_funct_1 @ X9)
% 2.05/2.28          | ~ (v1_funct_2 @ X9 @ X7 @ X8)
% 2.05/2.28          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8)))
% 2.05/2.28          | (r2_funct_2 @ X7 @ X8 @ X6 @ X9)
% 2.05/2.28          | ((X6) != (X9)))),
% 2.05/2.28      inference('cnf', [status(esa)], [redefinition_r2_funct_2])).
% 2.05/2.28  thf('316', plain,
% 2.05/2.28      (![X7 : $i, X8 : $i, X9 : $i]:
% 2.05/2.28         ((r2_funct_2 @ X7 @ X8 @ X9 @ X9)
% 2.05/2.28          | ~ (v1_funct_1 @ X9)
% 2.05/2.28          | ~ (v1_funct_2 @ X9 @ X7 @ X8)
% 2.05/2.28          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8))))),
% 2.05/2.28      inference('simplify', [status(thm)], ['315'])).
% 2.05/2.28  thf('317', plain,
% 2.05/2.28      ((~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 2.05/2.28        | ~ (v1_funct_1 @ sk_C)
% 2.05/2.28        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 2.05/2.28           sk_C))),
% 2.05/2.28      inference('sup-', [status(thm)], ['314', '316'])).
% 2.05/2.28  thf('318', plain,
% 2.05/2.28      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 2.05/2.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.05/2.28  thf('319', plain, ((v1_funct_1 @ sk_C)),
% 2.05/2.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.05/2.28  thf('320', plain,
% 2.05/2.28      ((r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ sk_C)),
% 2.05/2.28      inference('demod', [status(thm)], ['317', '318', '319'])).
% 2.05/2.28  thf('321', plain,
% 2.05/2.28      (((v2_struct_0 @ sk_A)
% 2.05/2.28        | (v2_struct_0 @ sk_B)
% 2.05/2.28        | (v1_xboole_0 @ (u1_struct_0 @ sk_B)))),
% 2.05/2.28      inference('demod', [status(thm)], ['313', '320'])).
% 2.05/2.28  thf('322', plain, (~ (v2_struct_0 @ sk_A)),
% 2.05/2.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.05/2.28  thf('323', plain,
% 2.05/2.28      (((v1_xboole_0 @ (u1_struct_0 @ sk_B)) | (v2_struct_0 @ sk_B))),
% 2.05/2.28      inference('clc', [status(thm)], ['321', '322'])).
% 2.05/2.28  thf('324', plain, (~ (v2_struct_0 @ sk_B)),
% 2.05/2.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.05/2.28  thf('325', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_B))),
% 2.05/2.28      inference('clc', [status(thm)], ['323', '324'])).
% 2.05/2.28  thf(fc2_struct_0, axiom,
% 2.05/2.28    (![A:$i]:
% 2.05/2.28     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 2.05/2.28       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 2.05/2.28  thf('326', plain,
% 2.05/2.28      (![X15 : $i]:
% 2.05/2.28         (~ (v1_xboole_0 @ (u1_struct_0 @ X15))
% 2.05/2.28          | ~ (l1_struct_0 @ X15)
% 2.05/2.28          | (v2_struct_0 @ X15))),
% 2.05/2.28      inference('cnf', [status(esa)], [fc2_struct_0])).
% 2.05/2.28  thf('327', plain, (((v2_struct_0 @ sk_B) | ~ (l1_struct_0 @ sk_B))),
% 2.05/2.28      inference('sup-', [status(thm)], ['325', '326'])).
% 2.05/2.28  thf('328', plain, ((l1_pre_topc @ sk_B)),
% 2.05/2.28      inference('demod', [status(thm)], ['21', '22'])).
% 2.05/2.28  thf(dt_l1_pre_topc, axiom,
% 2.05/2.28    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 2.05/2.28  thf('329', plain,
% 2.05/2.28      (![X12 : $i]: ((l1_struct_0 @ X12) | ~ (l1_pre_topc @ X12))),
% 2.05/2.28      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 2.05/2.28  thf('330', plain, ((l1_struct_0 @ sk_B)),
% 2.05/2.28      inference('sup-', [status(thm)], ['328', '329'])).
% 2.05/2.28  thf('331', plain, ((v2_struct_0 @ sk_B)),
% 2.05/2.28      inference('demod', [status(thm)], ['327', '330'])).
% 2.05/2.28  thf('332', plain, ($false), inference('demod', [status(thm)], ['0', '331'])).
% 2.05/2.28  
% 2.05/2.28  % SZS output end Refutation
% 2.05/2.28  
% 2.05/2.29  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
