%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.BM48RHGemt

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:10:42 EST 2020

% Result     : Theorem 4.66s
% Output     : Refutation 4.66s
% Verified   : 
% Statistics : Number of formulae       :  316 (8664 expanded)
%              Number of leaves         :   41 (2516 expanded)
%              Depth                    :   42
%              Number of atoms          : 4621 (237382 expanded)
%              Number of equality atoms :   62 (4237 expanded)
%              Maximal formula depth    :   25 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_partfun1_type,type,(
    k2_partfun1: $i > $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k3_funct_2_type,type,(
    k3_funct_2: $i > $i > $i > $i > $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k3_tmap_1_type,type,(
    k3_tmap_1: $i > $i > $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k2_tmap_1_type,type,(
    k2_tmap_1: $i > $i > $i > $i > $i )).

thf(r2_funct_2_type,type,(
    r2_funct_2: $i > $i > $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k4_tmap_1_type,type,(
    k4_tmap_1: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_F_type,type,(
    sk_F: $i > $i > $i > $i > $i > $i )).

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
    ! [X37: $i] :
      ( ( m1_pre_topc @ X37 @ X37 )
      | ~ ( l1_pre_topc @ X37 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('2',plain,(
    ! [X37: $i] :
      ( ( m1_pre_topc @ X37 @ X37 )
      | ~ ( l1_pre_topc @ X37 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('3',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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

thf('12',plain,(
    ! [X38: $i,X39: $i,X40: $i,X41: $i,X42: $i] :
      ( ( v2_struct_0 @ X38 )
      | ~ ( v2_pre_topc @ X38 )
      | ~ ( l1_pre_topc @ X38 )
      | ~ ( v1_funct_1 @ X39 )
      | ~ ( v1_funct_2 @ X39 @ ( u1_struct_0 @ X38 ) @ ( u1_struct_0 @ X40 ) )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X38 ) @ ( u1_struct_0 @ X40 ) ) ) )
      | ( r2_hidden @ ( sk_F @ X41 @ X39 @ X42 @ X38 @ X40 ) @ ( u1_struct_0 @ X42 ) )
      | ( r2_funct_2 @ ( u1_struct_0 @ X42 ) @ ( u1_struct_0 @ X40 ) @ ( k2_tmap_1 @ X38 @ X40 @ X39 @ X42 ) @ X41 )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X42 ) @ ( u1_struct_0 @ X40 ) ) ) )
      | ~ ( v1_funct_2 @ X41 @ ( u1_struct_0 @ X42 ) @ ( u1_struct_0 @ X40 ) )
      | ~ ( v1_funct_1 @ X41 )
      | ~ ( m1_pre_topc @ X42 @ X38 )
      | ( v2_struct_0 @ X42 )
      | ~ ( l1_pre_topc @ X40 )
      | ~ ( v2_pre_topc @ X40 )
      | ( v2_struct_0 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t59_tmap_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ) )
      | ( r2_funct_2 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tmap_1 @ sk_B @ sk_A @ ( k4_tmap_1 @ sk_A @ sk_B ) @ X0 ) @ X1 )
      | ( r2_hidden @ ( sk_F @ X1 @ ( k4_tmap_1 @ sk_A @ sk_B ) @ X0 @ sk_B @ sk_A ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v1_funct_2 @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_B ) )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    ! [X33: $i,X34: $i] :
      ( ~ ( l1_pre_topc @ X33 )
      | ~ ( v2_pre_topc @ X33 )
      | ( v2_struct_0 @ X33 )
      | ~ ( m1_pre_topc @ X34 @ X33 )
      | ( v1_funct_2 @ ( k4_tmap_1 @ X33 @ X34 ) @ ( u1_struct_0 @ X34 ) @ ( u1_struct_0 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k4_tmap_1])).

thf('18',plain,
    ( ( v1_funct_2 @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ( v1_funct_2 @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['18','19','20'])).

thf('22',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    v1_funct_2 @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['21','22'])).

thf('24',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    ! [X33: $i,X34: $i] :
      ( ~ ( l1_pre_topc @ X33 )
      | ~ ( v2_pre_topc @ X33 )
      | ( v2_struct_0 @ X33 )
      | ~ ( m1_pre_topc @ X34 @ X33 )
      | ( v1_funct_1 @ ( k4_tmap_1 @ X33 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k4_tmap_1])).

thf('26',plain,
    ( ( v1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ( v1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['26','27','28'])).

thf('30',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    v1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['29','30'])).

thf('32',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('33',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( m1_pre_topc @ X16 @ X17 )
      | ( l1_pre_topc @ X16 )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('34',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( v2_pre_topc @ B ) ) ) )).

thf('38',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( m1_pre_topc @ X13 @ X14 )
      | ( v2_pre_topc @ X13 )
      | ~ ( l1_pre_topc @ X14 )
      | ~ ( v2_pre_topc @ X14 ) ) ),
    inference(cnf,[status(esa)],[cc1_pre_topc])).

thf('39',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    v2_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['39','40','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ) )
      | ( r2_funct_2 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tmap_1 @ sk_B @ sk_A @ ( k4_tmap_1 @ sk_A @ sk_B ) @ X0 ) @ X1 )
      | ( r2_hidden @ ( sk_F @ X1 @ ( k4_tmap_1 @ sk_A @ sk_B ) @ X0 @ sk_B @ sk_A ) @ ( u1_struct_0 @ X0 ) )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['13','14','15','23','31','36','42'])).

thf('44',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( r2_hidden @ ( sk_F @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_B @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tmap_1 @ sk_B @ sk_A @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_B ) @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( m1_pre_topc @ sk_B @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['3','43'])).

thf('45',plain,(
    ! [X37: $i] :
      ( ( m1_pre_topc @ X37 @ X37 )
      | ~ ( l1_pre_topc @ X37 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('46',plain,(
    m1_subset_1 @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['9','10'])).

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

thf('47',plain,(
    ! [X43: $i,X44: $i,X45: $i,X46: $i] :
      ( ( v2_struct_0 @ X43 )
      | ~ ( v2_pre_topc @ X43 )
      | ~ ( l1_pre_topc @ X43 )
      | ~ ( v1_funct_1 @ X44 )
      | ~ ( v1_funct_2 @ X44 @ ( u1_struct_0 @ X45 ) @ ( u1_struct_0 @ X43 ) )
      | ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X45 ) @ ( u1_struct_0 @ X43 ) ) ) )
      | ( r2_funct_2 @ ( u1_struct_0 @ X45 ) @ ( u1_struct_0 @ X43 ) @ X44 @ ( k3_tmap_1 @ X46 @ X43 @ X45 @ X45 @ X44 ) )
      | ~ ( m1_pre_topc @ X45 @ X46 )
      | ( v2_struct_0 @ X45 )
      | ~ ( l1_pre_topc @ X46 )
      | ~ ( v2_pre_topc @ X46 )
      | ( v2_struct_0 @ X46 ) ) ),
    inference(cnf,[status(esa)],[t74_tmap_1])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ sk_B @ X0 )
      | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( k3_tmap_1 @ X0 @ sk_A @ sk_B @ sk_B @ ( k4_tmap_1 @ sk_A @ sk_B ) ) )
      | ~ ( v1_funct_2 @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_B ) )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    v1_funct_2 @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['21','22'])).

thf('50',plain,(
    v1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['29','30'])).

thf('51',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ sk_B @ X0 )
      | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( k3_tmap_1 @ X0 @ sk_A @ sk_B @ sk_B @ ( k4_tmap_1 @ sk_A @ sk_B ) ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['48','49','50','51','52'])).

thf('54',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_B @ sk_B @ ( k4_tmap_1 @ sk_A @ sk_B ) ) )
    | ( v2_struct_0 @ sk_B )
    | ~ ( l1_pre_topc @ sk_B )
    | ~ ( v2_pre_topc @ sk_B )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['45','53'])).

thf('55',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['34','35'])).

thf('56',plain,(
    ! [X37: $i] :
      ( ( m1_pre_topc @ X37 @ X37 )
      | ~ ( l1_pre_topc @ X37 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('57',plain,(
    ! [X37: $i] :
      ( ( m1_pre_topc @ X37 @ X37 )
      | ~ ( l1_pre_topc @ X37 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('58',plain,(
    m1_subset_1 @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['9','10'])).

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

thf('59',plain,(
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

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ sk_B @ X0 )
      | ~ ( v1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_B ) )
      | ~ ( v1_funct_2 @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
      | ( ( k3_tmap_1 @ X0 @ sk_A @ sk_B @ X1 @ ( k4_tmap_1 @ sk_A @ sk_B ) )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( m1_pre_topc @ X1 @ sk_B )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    v1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['29','30'])).

thf('62',plain,(
    v1_funct_2 @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['21','22'])).

thf('63',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ sk_B @ X0 )
      | ( ( k3_tmap_1 @ X0 @ sk_A @ sk_B @ X1 @ ( k4_tmap_1 @ sk_A @ sk_B ) )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( m1_pre_topc @ X1 @ sk_B )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['60','61','62','63','64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ( ( k3_tmap_1 @ sk_B @ sk_A @ sk_B @ X0 @ ( k4_tmap_1 @ sk_A @ sk_B ) )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['57','65'])).

thf('67',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['34','35'])).

thf('68',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['34','35'])).

thf('69',plain,(
    v2_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['39','40','41'])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ( ( k3_tmap_1 @ sk_B @ sk_A @ sk_B @ X0 @ ( k4_tmap_1 @ sk_A @ sk_B ) )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ X0 ) ) )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['66','67','68','69'])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( ( k3_tmap_1 @ sk_B @ sk_A @ sk_B @ X0 @ ( k4_tmap_1 @ sk_A @ sk_B ) )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['70'])).

thf('72',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( ( k3_tmap_1 @ sk_B @ sk_A @ sk_B @ sk_B @ ( k4_tmap_1 @ sk_A @ sk_B ) )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_B ) ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['56','71'])).

thf('73',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['34','35'])).

thf('74',plain,(
    ! [X37: $i] :
      ( ( m1_pre_topc @ X37 @ X37 )
      | ~ ( l1_pre_topc @ X37 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('75',plain,(
    m1_subset_1 @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['9','10'])).

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

thf('76',plain,(
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

thf('77',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_B ) )
      | ~ ( v1_funct_2 @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
      | ( ( k2_tmap_1 @ sk_B @ sk_A @ ( k4_tmap_1 @ sk_A @ sk_B ) @ X0 )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    v2_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['39','40','41'])).

thf('79',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['34','35'])).

thf('80',plain,(
    v1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['29','30'])).

thf('81',plain,(
    v1_funct_2 @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['21','22'])).

thf('82',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( ( k2_tmap_1 @ sk_B @ sk_A @ ( k4_tmap_1 @ sk_A @ sk_B ) @ X0 )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['77','78','79','80','81','82','83'])).

thf('85',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( ( k2_tmap_1 @ sk_B @ sk_A @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_B )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_B ) ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['74','84'])).

thf('86',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['34','35'])).

thf('87',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k2_tmap_1 @ sk_B @ sk_A @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_B )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_B ) ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['85','86'])).

thf('88',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k2_tmap_1 @ sk_B @ sk_A @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_B )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['87','88'])).

thf('90',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,
    ( ( k2_tmap_1 @ sk_B @ sk_A @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_B )
    = ( k2_partfun1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['89','90'])).

thf('92',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k3_tmap_1 @ sk_B @ sk_A @ sk_B @ sk_B @ ( k4_tmap_1 @ sk_A @ sk_B ) )
      = ( k2_tmap_1 @ sk_B @ sk_A @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_B ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['72','73','91'])).

thf('93',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k3_tmap_1 @ sk_B @ sk_A @ sk_B @ sk_B @ ( k4_tmap_1 @ sk_A @ sk_B ) )
      = ( k2_tmap_1 @ sk_B @ sk_A @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference(clc,[status(thm)],['92','93'])).

thf('95',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,
    ( ( k3_tmap_1 @ sk_B @ sk_A @ sk_B @ sk_B @ ( k4_tmap_1 @ sk_A @ sk_B ) )
    = ( k2_tmap_1 @ sk_B @ sk_A @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(clc,[status(thm)],['94','95'])).

thf('97',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['34','35'])).

thf('98',plain,(
    v2_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['39','40','41'])).

thf('99',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( k2_tmap_1 @ sk_B @ sk_A @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['54','55','96','97','98'])).

thf('100',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( k2_tmap_1 @ sk_B @ sk_A @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['99'])).

thf('101',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( k2_tmap_1 @ sk_B @ sk_A @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference(clc,[status(thm)],['100','101'])).

thf('103',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,(
    r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( k2_tmap_1 @ sk_B @ sk_A @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(clc,[status(thm)],['102','103'])).

thf('105',plain,(
    m1_subset_1 @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['9','10'])).

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

thf('106',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) )
      | ~ ( v1_funct_2 @ X9 @ X10 @ X11 )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_funct_2 @ X12 @ X10 @ X11 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) )
      | ( X9 = X12 )
      | ~ ( r2_funct_2 @ X10 @ X11 @ X9 @ X12 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_funct_2])).

thf('107',plain,(
    ! [X0: $i] :
      ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B ) @ X0 )
      | ( ( k4_tmap_1 @ sk_A @ sk_B )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) )
      | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_B ) )
      | ~ ( v1_funct_2 @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['105','106'])).

thf('108',plain,(
    v1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['29','30'])).

thf('109',plain,(
    v1_funct_2 @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['21','22'])).

thf('110',plain,(
    ! [X0: $i] :
      ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B ) @ X0 )
      | ( ( k4_tmap_1 @ sk_A @ sk_B )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) )
      | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['107','108','109'])).

thf('111',plain,
    ( ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_B @ sk_A @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_B ) )
    | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_B @ sk_A @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_B @ sk_A @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ( ( k4_tmap_1 @ sk_A @ sk_B )
      = ( k2_tmap_1 @ sk_B @ sk_A @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['104','110'])).

thf('112',plain,(
    ! [X37: $i] :
      ( ( m1_pre_topc @ X37 @ X37 )
      | ~ ( l1_pre_topc @ X37 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('113',plain,(
    ! [X37: $i] :
      ( ( m1_pre_topc @ X37 @ X37 )
      | ~ ( l1_pre_topc @ X37 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('114',plain,(
    m1_subset_1 @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['9','10'])).

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

thf('115',plain,(
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

thf('116',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_1 @ ( k3_tmap_1 @ X1 @ sk_A @ sk_B @ X0 @ ( k4_tmap_1 @ sk_A @ sk_B ) ) )
      | ~ ( v1_funct_2 @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_B ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_pre_topc @ sk_B @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['114','115'])).

thf('117',plain,(
    v1_funct_2 @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['21','22'])).

thf('118',plain,(
    v1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['29','30'])).

thf('119',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('121',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_1 @ ( k3_tmap_1 @ X1 @ sk_A @ sk_B @ X0 @ ( k4_tmap_1 @ sk_A @ sk_B ) ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( m1_pre_topc @ sk_B @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['116','117','118','119','120'])).

thf('122',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_B )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ( v2_struct_0 @ sk_B )
      | ( v1_funct_1 @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_B @ X0 @ ( k4_tmap_1 @ sk_A @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['113','121'])).

thf('123',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['34','35'])).

thf('124',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['34','35'])).

thf('125',plain,(
    v2_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['39','40','41'])).

thf('126',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( v1_funct_1 @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_B @ X0 @ ( k4_tmap_1 @ sk_A @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['122','123','124','125'])).

thf('127',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( v1_funct_1 @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_B @ sk_B @ ( k4_tmap_1 @ sk_A @ sk_B ) ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['112','126'])).

thf('128',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['34','35'])).

thf('129',plain,
    ( ( v1_funct_1 @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_B @ sk_B @ ( k4_tmap_1 @ sk_A @ sk_B ) ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['127','128'])).

thf('130',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('131',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v1_funct_1 @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_B @ sk_B @ ( k4_tmap_1 @ sk_A @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['129','130'])).

thf('132',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('133',plain,(
    v1_funct_1 @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_B @ sk_B @ ( k4_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['131','132'])).

thf('134',plain,
    ( ( k3_tmap_1 @ sk_B @ sk_A @ sk_B @ sk_B @ ( k4_tmap_1 @ sk_A @ sk_B ) )
    = ( k2_tmap_1 @ sk_B @ sk_A @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(clc,[status(thm)],['94','95'])).

thf('135',plain,(
    v1_funct_1 @ ( k2_tmap_1 @ sk_B @ sk_A @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(demod,[status(thm)],['133','134'])).

thf('136',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('137',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('138',plain,(
    m1_subset_1 @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['9','10'])).

thf('139',plain,(
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

thf('140',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_2 @ ( k3_tmap_1 @ X1 @ sk_A @ sk_B @ X0 @ ( k4_tmap_1 @ sk_A @ sk_B ) ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_2 @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_B ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_pre_topc @ sk_B @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['138','139'])).

thf('141',plain,(
    v1_funct_2 @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['21','22'])).

thf('142',plain,(
    v1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['29','30'])).

thf('143',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('144',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('145',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_2 @ ( k3_tmap_1 @ X1 @ sk_A @ sk_B @ X0 @ ( k4_tmap_1 @ sk_A @ sk_B ) ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( m1_pre_topc @ sk_B @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['140','141','142','143','144'])).

thf('146',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_A @ sk_B @ X0 @ ( k4_tmap_1 @ sk_A @ sk_B ) ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['137','145'])).

thf('147',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('148',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('149',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_A @ sk_B @ X0 @ ( k4_tmap_1 @ sk_A @ sk_B ) ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['146','147','148'])).

thf('150',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_A @ sk_B @ X0 @ ( k4_tmap_1 @ sk_A @ sk_B ) ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['149'])).

thf('151',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('152',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_A @ sk_B @ X0 @ ( k4_tmap_1 @ sk_A @ sk_B ) ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['150','151'])).

thf('153',plain,(
    v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_A @ sk_B @ sk_B @ ( k4_tmap_1 @ sk_A @ sk_B ) ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['136','152'])).

thf('154',plain,(
    ! [X37: $i] :
      ( ( m1_pre_topc @ X37 @ X37 )
      | ~ ( l1_pre_topc @ X37 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('155',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('156',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ sk_B @ X0 )
      | ( ( k3_tmap_1 @ X0 @ sk_A @ sk_B @ X1 @ ( k4_tmap_1 @ sk_A @ sk_B ) )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( m1_pre_topc @ X1 @ sk_B )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['60','61','62','63','64'])).

thf('157',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ( ( k3_tmap_1 @ sk_A @ sk_A @ sk_B @ X0 @ ( k4_tmap_1 @ sk_A @ sk_B ) )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['155','156'])).

thf('158',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('159',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('160',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ( ( k3_tmap_1 @ sk_A @ sk_A @ sk_B @ X0 @ ( k4_tmap_1 @ sk_A @ sk_B ) )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ X0 ) ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['157','158','159'])).

thf('161',plain,(
    ! [X0: $i] :
      ( ( ( k3_tmap_1 @ sk_A @ sk_A @ sk_B @ X0 @ ( k4_tmap_1 @ sk_A @ sk_B ) )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['160'])).

thf('162',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ~ ( m1_pre_topc @ sk_B @ sk_A )
    | ( ( k3_tmap_1 @ sk_A @ sk_A @ sk_B @ sk_B @ ( k4_tmap_1 @ sk_A @ sk_B ) )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['154','161'])).

thf('163',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['34','35'])).

thf('164',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('165',plain,
    ( ( k2_tmap_1 @ sk_B @ sk_A @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_B )
    = ( k2_partfun1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['89','90'])).

thf('166',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k3_tmap_1 @ sk_A @ sk_A @ sk_B @ sk_B @ ( k4_tmap_1 @ sk_A @ sk_B ) )
      = ( k2_tmap_1 @ sk_B @ sk_A @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['162','163','164','165'])).

thf('167',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('168',plain,
    ( ( k3_tmap_1 @ sk_A @ sk_A @ sk_B @ sk_B @ ( k4_tmap_1 @ sk_A @ sk_B ) )
    = ( k2_tmap_1 @ sk_B @ sk_A @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(clc,[status(thm)],['166','167'])).

thf('169',plain,(
    v1_funct_2 @ ( k2_tmap_1 @ sk_B @ sk_A @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['153','168'])).

thf('170',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('171',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('172',plain,(
    m1_subset_1 @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['9','10'])).

thf('173',plain,(
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

thf('174',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( k3_tmap_1 @ X1 @ sk_A @ sk_B @ X0 @ ( k4_tmap_1 @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ) )
      | ~ ( v1_funct_2 @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_B ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_pre_topc @ sk_B @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['172','173'])).

thf('175',plain,(
    v1_funct_2 @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['21','22'])).

thf('176',plain,(
    v1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['29','30'])).

thf('177',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('178',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('179',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( k3_tmap_1 @ X1 @ sk_A @ sk_B @ X0 @ ( k4_tmap_1 @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( m1_pre_topc @ sk_B @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['174','175','176','177','178'])).

thf('180',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_A @ sk_B @ X0 @ ( k4_tmap_1 @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['171','179'])).

thf('181',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('182',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('183',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_A @ sk_B @ X0 @ ( k4_tmap_1 @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['180','181','182'])).

thf('184',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_A @ sk_B @ X0 @ ( k4_tmap_1 @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['183'])).

thf('185',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('186',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_A @ sk_B @ X0 @ ( k4_tmap_1 @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ) ) ) ),
    inference(clc,[status(thm)],['184','185'])).

thf('187',plain,(
    m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_A @ sk_B @ sk_B @ ( k4_tmap_1 @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['170','186'])).

thf('188',plain,
    ( ( k3_tmap_1 @ sk_A @ sk_A @ sk_B @ sk_B @ ( k4_tmap_1 @ sk_A @ sk_B ) )
    = ( k2_tmap_1 @ sk_B @ sk_A @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(clc,[status(thm)],['166','167'])).

thf('189',plain,(
    m1_subset_1 @ ( k2_tmap_1 @ sk_B @ sk_A @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['187','188'])).

thf('190',plain,
    ( ( k4_tmap_1 @ sk_A @ sk_B )
    = ( k2_tmap_1 @ sk_B @ sk_A @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(demod,[status(thm)],['111','135','169','189'])).

thf('191',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('192',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('193',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( r2_hidden @ ( sk_F @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_B @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C )
    | ~ ( m1_pre_topc @ sk_B @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['44','190','191','192'])).

thf('194',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( m1_pre_topc @ sk_B @ sk_B )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C )
    | ( r2_hidden @ ( sk_F @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_B @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(simplify,[status(thm)],['193'])).

thf('195',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( r2_hidden @ ( sk_F @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_B @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['2','194'])).

thf('196',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['34','35'])).

thf('197',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( r2_hidden @ ( sk_F @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_B @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['195','196'])).

thf('198',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t1_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( m1_subset_1 @ ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('199',plain,(
    ! [X35: $i,X36: $i] :
      ( ~ ( m1_pre_topc @ X35 @ X36 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X35 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X36 ) ) )
      | ~ ( l1_pre_topc @ X36 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('200',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['198','199'])).

thf('201',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('202',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['200','201'])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('203',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( m1_subset_1 @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('204',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['202','203'])).

thf('205',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( m1_subset_1 @ ( sk_F @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_B @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['197','204'])).

thf('206',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( r2_hidden @ ( sk_F @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_B @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['195','196'])).

thf('207',plain,(
    ! [X53: $i] :
      ( ~ ( r2_hidden @ X53 @ ( u1_struct_0 @ sk_B ) )
      | ( X53
        = ( k1_funct_1 @ sk_C @ X53 ) )
      | ~ ( m1_subset_1 @ X53 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('208',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ~ ( m1_subset_1 @ ( sk_F @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_B @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( ( sk_F @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_B @ sk_B @ sk_A )
      = ( k1_funct_1 @ sk_C @ ( sk_F @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_B @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['206','207'])).

thf('209',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( ( sk_F @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_B @ sk_B @ sk_A )
      = ( k1_funct_1 @ sk_C @ ( sk_F @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_B @ sk_B @ sk_A ) ) )
    | ( v2_struct_0 @ sk_B )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['205','208'])).

thf('210',plain,
    ( ( ( sk_F @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_B @ sk_B @ sk_A )
      = ( k1_funct_1 @ sk_C @ ( sk_F @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_B @ sk_B @ sk_A ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C )
    | ( v2_struct_0 @ sk_B ) ),
    inference(simplify,[status(thm)],['209'])).

thf('211',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( m1_subset_1 @ ( sk_F @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_B @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['197','204'])).

thf('212',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( r2_hidden @ ( sk_F @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_B @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['195','196'])).

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

thf('213',plain,(
    ! [X50: $i,X51: $i,X52: $i] :
      ( ( v2_struct_0 @ X50 )
      | ~ ( m1_pre_topc @ X50 @ X51 )
      | ~ ( r2_hidden @ X52 @ ( u1_struct_0 @ X50 ) )
      | ( ( k1_funct_1 @ ( k4_tmap_1 @ X51 @ X50 ) @ X52 )
        = X52 )
      | ~ ( m1_subset_1 @ X52 @ ( u1_struct_0 @ X51 ) )
      | ~ ( l1_pre_topc @ X51 )
      | ~ ( v2_pre_topc @ X51 )
      | ( v2_struct_0 @ X51 ) ) ),
    inference(cnf,[status(esa)],[t95_tmap_1])).

thf('214',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_subset_1 @ ( sk_F @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_B @ sk_B @ sk_A ) @ ( u1_struct_0 @ X0 ) )
      | ( ( k1_funct_1 @ ( k4_tmap_1 @ X0 @ sk_B ) @ ( sk_F @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_B @ sk_B @ sk_A ) )
        = ( sk_F @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_B @ sk_B @ sk_A ) )
      | ~ ( m1_pre_topc @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['212','213'])).

thf('215',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ sk_B @ X0 )
      | ( ( k1_funct_1 @ ( k4_tmap_1 @ X0 @ sk_B ) @ ( sk_F @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_B @ sk_B @ sk_A ) )
        = ( sk_F @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_B @ sk_B @ sk_A ) )
      | ~ ( m1_subset_1 @ ( sk_F @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_B @ sk_B @ sk_A ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['214'])).

thf('216',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( sk_F @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_B @ sk_B @ sk_A ) )
      = ( sk_F @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_B @ sk_B @ sk_A ) )
    | ~ ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['211','215'])).

thf('217',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('218',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('219',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('220',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( ( k1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( sk_F @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_B @ sk_B @ sk_A ) )
      = ( sk_F @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_B @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['216','217','218','219'])).

thf('221',plain,
    ( ( ( k1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( sk_F @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_B @ sk_B @ sk_A ) )
      = ( sk_F @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_B @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C )
    | ( v2_struct_0 @ sk_B ) ),
    inference(simplify,[status(thm)],['220'])).

thf('222',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( r2_hidden @ ( sk_F @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_B @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['195','196'])).

thf('223',plain,(
    ! [X37: $i] :
      ( ( m1_pre_topc @ X37 @ X37 )
      | ~ ( l1_pre_topc @ X37 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('224',plain,(
    ! [X35: $i,X36: $i] :
      ( ~ ( m1_pre_topc @ X35 @ X36 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X35 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X36 ) ) )
      | ~ ( l1_pre_topc @ X36 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('225',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['223','224'])).

thf('226',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['225'])).

thf('227',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( m1_subset_1 @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('228',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['226','227'])).

thf('229',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( m1_subset_1 @ ( sk_F @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_B @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['222','228'])).

thf('230',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['34','35'])).

thf('231',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( m1_subset_1 @ ( sk_F @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_B @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['229','230'])).

thf('232',plain,(
    m1_subset_1 @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['9','10'])).

thf(redefinition_k3_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ A ) )
     => ( ( k3_funct_2 @ A @ B @ C @ D )
        = ( k1_funct_1 @ C @ D ) ) ) )).

thf('233',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) ) )
      | ~ ( v1_funct_2 @ X5 @ X6 @ X7 )
      | ~ ( v1_funct_1 @ X5 )
      | ( v1_xboole_0 @ X6 )
      | ~ ( m1_subset_1 @ X8 @ X6 )
      | ( ( k3_funct_2 @ X6 @ X7 @ X5 @ X8 )
        = ( k1_funct_1 @ X5 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k3_funct_2])).

thf('234',plain,(
    ! [X0: $i] :
      ( ( ( k3_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B ) @ X0 )
        = ( k1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_B ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_B ) )
      | ~ ( v1_funct_2 @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['232','233'])).

thf('235',plain,(
    v1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['29','30'])).

thf('236',plain,(
    v1_funct_2 @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['21','22'])).

thf('237',plain,(
    ! [X0: $i] :
      ( ( ( k3_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B ) @ X0 )
        = ( k1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_B ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['234','235','236'])).

thf('238',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( ( k3_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( sk_F @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_B @ sk_B @ sk_A ) )
      = ( k1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( sk_F @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_B @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['231','237'])).

thf('239',plain,(
    ! [X38: $i,X39: $i,X40: $i,X41: $i,X42: $i] :
      ( ( v2_struct_0 @ X38 )
      | ~ ( v2_pre_topc @ X38 )
      | ~ ( l1_pre_topc @ X38 )
      | ~ ( v1_funct_1 @ X39 )
      | ~ ( v1_funct_2 @ X39 @ ( u1_struct_0 @ X38 ) @ ( u1_struct_0 @ X40 ) )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X38 ) @ ( u1_struct_0 @ X40 ) ) ) )
      | ( ( k3_funct_2 @ ( u1_struct_0 @ X38 ) @ ( u1_struct_0 @ X40 ) @ X39 @ ( sk_F @ X41 @ X39 @ X42 @ X38 @ X40 ) )
       != ( k1_funct_1 @ X41 @ ( sk_F @ X41 @ X39 @ X42 @ X38 @ X40 ) ) )
      | ( r2_funct_2 @ ( u1_struct_0 @ X42 ) @ ( u1_struct_0 @ X40 ) @ ( k2_tmap_1 @ X38 @ X40 @ X39 @ X42 ) @ X41 )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X42 ) @ ( u1_struct_0 @ X40 ) ) ) )
      | ~ ( v1_funct_2 @ X41 @ ( u1_struct_0 @ X42 ) @ ( u1_struct_0 @ X40 ) )
      | ~ ( v1_funct_1 @ X41 )
      | ~ ( m1_pre_topc @ X42 @ X38 )
      | ( v2_struct_0 @ X42 )
      | ~ ( l1_pre_topc @ X40 )
      | ~ ( v2_pre_topc @ X40 )
      | ( v2_struct_0 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t59_tmap_1])).

thf('240',plain,
    ( ( ( k1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( sk_F @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_B @ sk_B @ sk_A ) )
     != ( k1_funct_1 @ sk_C @ ( sk_F @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_B @ sk_B @ sk_A ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ~ ( m1_pre_topc @ sk_B @ sk_B )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tmap_1 @ sk_B @ sk_A @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_B ) @ sk_C )
    | ~ ( m1_subset_1 @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ~ ( v1_funct_2 @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( l1_pre_topc @ sk_B )
    | ~ ( v2_pre_topc @ sk_B )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['238','239'])).

thf('241',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('242',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('243',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('244',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('245',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('246',plain,
    ( ( k4_tmap_1 @ sk_A @ sk_B )
    = ( k2_tmap_1 @ sk_B @ sk_A @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(demod,[status(thm)],['111','135','169','189'])).

thf('247',plain,(
    m1_subset_1 @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['9','10'])).

thf('248',plain,(
    v1_funct_2 @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['21','22'])).

thf('249',plain,(
    v1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['29','30'])).

thf('250',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['34','35'])).

thf('251',plain,(
    v2_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['39','40','41'])).

thf('252',plain,
    ( ( ( k1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( sk_F @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_B @ sk_B @ sk_A ) )
     != ( k1_funct_1 @ sk_C @ ( sk_F @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_B @ sk_B @ sk_A ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ~ ( m1_pre_topc @ sk_B @ sk_B )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['240','241','242','243','244','245','246','247','248','249','250','251'])).

thf('253',plain,
    ( ~ ( m1_pre_topc @ sk_B @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( ( k1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( sk_F @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_B @ sk_B @ sk_A ) )
     != ( k1_funct_1 @ sk_C @ ( sk_F @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_B @ sk_B @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['252'])).

thf('254',plain,
    ( ( ( sk_F @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_B @ sk_B @ sk_A )
     != ( k1_funct_1 @ sk_C @ ( sk_F @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_B @ sk_B @ sk_A ) ) )
    | ( v2_struct_0 @ sk_B )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ~ ( m1_pre_topc @ sk_B @ sk_B ) ),
    inference('sup-',[status(thm)],['221','253'])).

thf('255',plain,
    ( ~ ( m1_pre_topc @ sk_B @ sk_B )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( ( sk_F @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_B @ sk_B @ sk_A )
     != ( k1_funct_1 @ sk_C @ ( sk_F @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_B @ sk_B @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['254'])).

thf('256',plain,
    ( ( ( sk_F @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_B @ sk_B @ sk_A )
     != ( sk_F @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_B @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ~ ( m1_pre_topc @ sk_B @ sk_B ) ),
    inference('sup-',[status(thm)],['210','255'])).

thf('257',plain,
    ( ~ ( m1_pre_topc @ sk_B @ sk_B )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C )
    | ( v2_struct_0 @ sk_B ) ),
    inference(simplify,[status(thm)],['256'])).

thf('258',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['1','257'])).

thf('259',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['34','35'])).

thf('260',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['258','259'])).

thf('261',plain,(
    ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('262',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['260','261'])).

thf('263',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('264',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['262','263'])).

thf('265',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('266',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['264','265'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('267',plain,(
    ! [X18: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X18 ) )
      | ~ ( l1_struct_0 @ X18 )
      | ( v2_struct_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('268',plain,
    ( ( v2_struct_0 @ sk_B )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['266','267'])).

thf('269',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['34','35'])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('270',plain,(
    ! [X15: $i] :
      ( ( l1_struct_0 @ X15 )
      | ~ ( l1_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('271',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['269','270'])).

thf('272',plain,(
    v2_struct_0 @ sk_B ),
    inference(demod,[status(thm)],['268','271'])).

thf('273',plain,(
    $false ),
    inference(demod,[status(thm)],['0','272'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.13/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.BM48RHGemt
% 0.14/0.35  % Computer   : n016.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 13:29:49 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 4.66/4.86  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 4.66/4.86  % Solved by: fo/fo7.sh
% 4.66/4.86  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 4.66/4.86  % done 2779 iterations in 4.356s
% 4.66/4.86  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 4.66/4.86  % SZS output start Refutation
% 4.66/4.86  thf(sk_C_type, type, sk_C: $i).
% 4.66/4.86  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 4.66/4.86  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 4.66/4.86  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 4.66/4.86  thf(k2_partfun1_type, type, k2_partfun1: $i > $i > $i > $i > $i).
% 4.66/4.86  thf(sk_B_type, type, sk_B: $i).
% 4.66/4.86  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 4.66/4.86  thf(k3_funct_2_type, type, k3_funct_2: $i > $i > $i > $i > $i).
% 4.66/4.86  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 4.66/4.86  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 4.66/4.86  thf(k3_tmap_1_type, type, k3_tmap_1: $i > $i > $i > $i > $i > $i).
% 4.66/4.86  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 4.66/4.86  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 4.66/4.86  thf(k2_tmap_1_type, type, k2_tmap_1: $i > $i > $i > $i > $i).
% 4.66/4.86  thf(r2_funct_2_type, type, r2_funct_2: $i > $i > $i > $i > $o).
% 4.66/4.86  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 4.66/4.86  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 4.66/4.86  thf(k4_tmap_1_type, type, k4_tmap_1: $i > $i > $i).
% 4.66/4.86  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 4.66/4.86  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 4.66/4.86  thf(sk_A_type, type, sk_A: $i).
% 4.66/4.86  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 4.66/4.86  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 4.66/4.86  thf(sk_F_type, type, sk_F: $i > $i > $i > $i > $i > $i).
% 4.66/4.86  thf(t96_tmap_1, conjecture,
% 4.66/4.86    (![A:$i]:
% 4.66/4.86     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 4.66/4.86       ( ![B:$i]:
% 4.66/4.86         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 4.66/4.86           ( ![C:$i]:
% 4.66/4.86             ( ( ( v1_funct_1 @ C ) & 
% 4.66/4.86                 ( v1_funct_2 @ C @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 4.66/4.86                 ( m1_subset_1 @
% 4.66/4.86                   C @ 
% 4.66/4.86                   ( k1_zfmisc_1 @
% 4.66/4.86                     ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 4.66/4.86               ( ( ![D:$i]:
% 4.66/4.86                   ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 4.66/4.86                     ( ( r2_hidden @ D @ ( u1_struct_0 @ B ) ) =>
% 4.66/4.86                       ( ( D ) = ( k1_funct_1 @ C @ D ) ) ) ) ) =>
% 4.66/4.86                 ( r2_funct_2 @
% 4.66/4.86                   ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 4.66/4.86                   ( k4_tmap_1 @ A @ B ) @ C ) ) ) ) ) ) ))).
% 4.66/4.86  thf(zf_stmt_0, negated_conjecture,
% 4.66/4.86    (~( ![A:$i]:
% 4.66/4.86        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 4.66/4.86            ( l1_pre_topc @ A ) ) =>
% 4.66/4.86          ( ![B:$i]:
% 4.66/4.86            ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 4.66/4.86              ( ![C:$i]:
% 4.66/4.86                ( ( ( v1_funct_1 @ C ) & 
% 4.66/4.86                    ( v1_funct_2 @
% 4.66/4.86                      C @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 4.66/4.86                    ( m1_subset_1 @
% 4.66/4.86                      C @ 
% 4.66/4.86                      ( k1_zfmisc_1 @
% 4.66/4.86                        ( k2_zfmisc_1 @
% 4.66/4.86                          ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 4.66/4.86                  ( ( ![D:$i]:
% 4.66/4.86                      ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 4.66/4.86                        ( ( r2_hidden @ D @ ( u1_struct_0 @ B ) ) =>
% 4.66/4.86                          ( ( D ) = ( k1_funct_1 @ C @ D ) ) ) ) ) =>
% 4.66/4.86                    ( r2_funct_2 @
% 4.66/4.86                      ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 4.66/4.86                      ( k4_tmap_1 @ A @ B ) @ C ) ) ) ) ) ) ) )),
% 4.66/4.86    inference('cnf.neg', [status(esa)], [t96_tmap_1])).
% 4.66/4.86  thf('0', plain, (~ (v2_struct_0 @ sk_B)),
% 4.66/4.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.66/4.86  thf(t2_tsep_1, axiom,
% 4.66/4.86    (![A:$i]: ( ( l1_pre_topc @ A ) => ( m1_pre_topc @ A @ A ) ))).
% 4.66/4.86  thf('1', plain,
% 4.66/4.86      (![X37 : $i]: ((m1_pre_topc @ X37 @ X37) | ~ (l1_pre_topc @ X37))),
% 4.66/4.86      inference('cnf', [status(esa)], [t2_tsep_1])).
% 4.66/4.86  thf('2', plain,
% 4.66/4.86      (![X37 : $i]: ((m1_pre_topc @ X37 @ X37) | ~ (l1_pre_topc @ X37))),
% 4.66/4.86      inference('cnf', [status(esa)], [t2_tsep_1])).
% 4.66/4.86  thf('3', plain,
% 4.66/4.86      ((m1_subset_1 @ sk_C @ 
% 4.66/4.86        (k1_zfmisc_1 @ 
% 4.66/4.86         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 4.66/4.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.66/4.86  thf('4', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 4.66/4.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.66/4.86  thf(dt_k4_tmap_1, axiom,
% 4.66/4.86    (![A:$i,B:$i]:
% 4.66/4.86     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 4.66/4.86         ( l1_pre_topc @ A ) & ( m1_pre_topc @ B @ A ) ) =>
% 4.66/4.86       ( ( v1_funct_1 @ ( k4_tmap_1 @ A @ B ) ) & 
% 4.66/4.86         ( v1_funct_2 @
% 4.66/4.86           ( k4_tmap_1 @ A @ B ) @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 4.66/4.86         ( m1_subset_1 @
% 4.66/4.86           ( k4_tmap_1 @ A @ B ) @ 
% 4.66/4.86           ( k1_zfmisc_1 @
% 4.66/4.86             ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 4.66/4.86  thf('5', plain,
% 4.66/4.86      (![X33 : $i, X34 : $i]:
% 4.66/4.86         (~ (l1_pre_topc @ X33)
% 4.66/4.86          | ~ (v2_pre_topc @ X33)
% 4.66/4.86          | (v2_struct_0 @ X33)
% 4.66/4.86          | ~ (m1_pre_topc @ X34 @ X33)
% 4.66/4.86          | (m1_subset_1 @ (k4_tmap_1 @ X33 @ X34) @ 
% 4.66/4.86             (k1_zfmisc_1 @ 
% 4.66/4.86              (k2_zfmisc_1 @ (u1_struct_0 @ X34) @ (u1_struct_0 @ X33)))))),
% 4.66/4.86      inference('cnf', [status(esa)], [dt_k4_tmap_1])).
% 4.66/4.86  thf('6', plain,
% 4.66/4.86      (((m1_subset_1 @ (k4_tmap_1 @ sk_A @ sk_B) @ 
% 4.66/4.86         (k1_zfmisc_1 @ 
% 4.66/4.86          (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))
% 4.66/4.86        | (v2_struct_0 @ sk_A)
% 4.66/4.86        | ~ (v2_pre_topc @ sk_A)
% 4.66/4.86        | ~ (l1_pre_topc @ sk_A))),
% 4.66/4.86      inference('sup-', [status(thm)], ['4', '5'])).
% 4.66/4.86  thf('7', plain, ((v2_pre_topc @ sk_A)),
% 4.66/4.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.66/4.86  thf('8', plain, ((l1_pre_topc @ sk_A)),
% 4.66/4.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.66/4.86  thf('9', plain,
% 4.66/4.86      (((m1_subset_1 @ (k4_tmap_1 @ sk_A @ sk_B) @ 
% 4.66/4.86         (k1_zfmisc_1 @ 
% 4.66/4.86          (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))
% 4.66/4.86        | (v2_struct_0 @ sk_A))),
% 4.66/4.86      inference('demod', [status(thm)], ['6', '7', '8'])).
% 4.66/4.86  thf('10', plain, (~ (v2_struct_0 @ sk_A)),
% 4.66/4.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.66/4.86  thf('11', plain,
% 4.66/4.86      ((m1_subset_1 @ (k4_tmap_1 @ sk_A @ sk_B) @ 
% 4.66/4.86        (k1_zfmisc_1 @ 
% 4.66/4.86         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 4.66/4.86      inference('clc', [status(thm)], ['9', '10'])).
% 4.66/4.86  thf(t59_tmap_1, axiom,
% 4.66/4.86    (![A:$i]:
% 4.66/4.86     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 4.66/4.86       ( ![B:$i]:
% 4.66/4.86         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 4.66/4.86             ( l1_pre_topc @ B ) ) =>
% 4.66/4.86           ( ![C:$i]:
% 4.66/4.86             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ B ) ) =>
% 4.66/4.86               ( ![D:$i]:
% 4.66/4.86                 ( ( ( v1_funct_1 @ D ) & 
% 4.66/4.86                     ( v1_funct_2 @
% 4.66/4.86                       D @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 4.66/4.86                     ( m1_subset_1 @
% 4.66/4.86                       D @ 
% 4.66/4.86                       ( k1_zfmisc_1 @
% 4.66/4.86                         ( k2_zfmisc_1 @
% 4.66/4.86                           ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 4.66/4.86                   ( ![E:$i]:
% 4.66/4.86                     ( ( ( v1_funct_1 @ E ) & 
% 4.66/4.86                         ( v1_funct_2 @
% 4.66/4.86                           E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ A ) ) & 
% 4.66/4.86                         ( m1_subset_1 @
% 4.66/4.86                           E @ 
% 4.66/4.86                           ( k1_zfmisc_1 @
% 4.66/4.86                             ( k2_zfmisc_1 @
% 4.66/4.86                               ( u1_struct_0 @ C ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 4.66/4.86                       ( ( ![F:$i]:
% 4.66/4.86                           ( ( m1_subset_1 @ F @ ( u1_struct_0 @ B ) ) =>
% 4.66/4.86                             ( ( r2_hidden @ F @ ( u1_struct_0 @ C ) ) =>
% 4.66/4.86                               ( ( k3_funct_2 @
% 4.66/4.86                                   ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 4.66/4.86                                   D @ F ) =
% 4.66/4.86                                 ( k1_funct_1 @ E @ F ) ) ) ) ) =>
% 4.66/4.86                         ( r2_funct_2 @
% 4.66/4.86                           ( u1_struct_0 @ C ) @ ( u1_struct_0 @ A ) @ 
% 4.66/4.86                           ( k2_tmap_1 @ B @ A @ D @ C ) @ E ) ) ) ) ) ) ) ) ) ) ))).
% 4.66/4.86  thf('12', plain,
% 4.66/4.86      (![X38 : $i, X39 : $i, X40 : $i, X41 : $i, X42 : $i]:
% 4.66/4.86         ((v2_struct_0 @ X38)
% 4.66/4.86          | ~ (v2_pre_topc @ X38)
% 4.66/4.86          | ~ (l1_pre_topc @ X38)
% 4.66/4.86          | ~ (v1_funct_1 @ X39)
% 4.66/4.86          | ~ (v1_funct_2 @ X39 @ (u1_struct_0 @ X38) @ (u1_struct_0 @ X40))
% 4.66/4.86          | ~ (m1_subset_1 @ X39 @ 
% 4.66/4.86               (k1_zfmisc_1 @ 
% 4.66/4.86                (k2_zfmisc_1 @ (u1_struct_0 @ X38) @ (u1_struct_0 @ X40))))
% 4.66/4.86          | (r2_hidden @ (sk_F @ X41 @ X39 @ X42 @ X38 @ X40) @ 
% 4.66/4.86             (u1_struct_0 @ X42))
% 4.66/4.86          | (r2_funct_2 @ (u1_struct_0 @ X42) @ (u1_struct_0 @ X40) @ 
% 4.66/4.86             (k2_tmap_1 @ X38 @ X40 @ X39 @ X42) @ X41)
% 4.66/4.86          | ~ (m1_subset_1 @ X41 @ 
% 4.66/4.86               (k1_zfmisc_1 @ 
% 4.66/4.86                (k2_zfmisc_1 @ (u1_struct_0 @ X42) @ (u1_struct_0 @ X40))))
% 4.66/4.86          | ~ (v1_funct_2 @ X41 @ (u1_struct_0 @ X42) @ (u1_struct_0 @ X40))
% 4.66/4.86          | ~ (v1_funct_1 @ X41)
% 4.66/4.86          | ~ (m1_pre_topc @ X42 @ X38)
% 4.66/4.86          | (v2_struct_0 @ X42)
% 4.66/4.86          | ~ (l1_pre_topc @ X40)
% 4.66/4.86          | ~ (v2_pre_topc @ X40)
% 4.66/4.86          | (v2_struct_0 @ X40))),
% 4.66/4.86      inference('cnf', [status(esa)], [t59_tmap_1])).
% 4.66/4.86  thf('13', plain,
% 4.66/4.86      (![X0 : $i, X1 : $i]:
% 4.66/4.86         ((v2_struct_0 @ sk_A)
% 4.66/4.86          | ~ (v2_pre_topc @ sk_A)
% 4.66/4.86          | ~ (l1_pre_topc @ sk_A)
% 4.66/4.86          | (v2_struct_0 @ X0)
% 4.66/4.86          | ~ (m1_pre_topc @ X0 @ sk_B)
% 4.66/4.86          | ~ (v1_funct_1 @ X1)
% 4.66/4.86          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A))
% 4.66/4.86          | ~ (m1_subset_1 @ X1 @ 
% 4.66/4.86               (k1_zfmisc_1 @ 
% 4.66/4.86                (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A))))
% 4.66/4.86          | (r2_funct_2 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A) @ 
% 4.66/4.86             (k2_tmap_1 @ sk_B @ sk_A @ (k4_tmap_1 @ sk_A @ sk_B) @ X0) @ X1)
% 4.66/4.86          | (r2_hidden @ 
% 4.66/4.86             (sk_F @ X1 @ (k4_tmap_1 @ sk_A @ sk_B) @ X0 @ sk_B @ sk_A) @ 
% 4.66/4.86             (u1_struct_0 @ X0))
% 4.66/4.86          | ~ (v1_funct_2 @ (k4_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_B) @ 
% 4.66/4.86               (u1_struct_0 @ sk_A))
% 4.66/4.86          | ~ (v1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_B))
% 4.66/4.86          | ~ (l1_pre_topc @ sk_B)
% 4.66/4.86          | ~ (v2_pre_topc @ sk_B)
% 4.66/4.86          | (v2_struct_0 @ sk_B))),
% 4.66/4.86      inference('sup-', [status(thm)], ['11', '12'])).
% 4.66/4.86  thf('14', plain, ((v2_pre_topc @ sk_A)),
% 4.66/4.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.66/4.86  thf('15', plain, ((l1_pre_topc @ sk_A)),
% 4.66/4.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.66/4.86  thf('16', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 4.66/4.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.66/4.86  thf('17', plain,
% 4.66/4.86      (![X33 : $i, X34 : $i]:
% 4.66/4.86         (~ (l1_pre_topc @ X33)
% 4.66/4.86          | ~ (v2_pre_topc @ X33)
% 4.66/4.86          | (v2_struct_0 @ X33)
% 4.66/4.86          | ~ (m1_pre_topc @ X34 @ X33)
% 4.66/4.86          | (v1_funct_2 @ (k4_tmap_1 @ X33 @ X34) @ (u1_struct_0 @ X34) @ 
% 4.66/4.86             (u1_struct_0 @ X33)))),
% 4.66/4.86      inference('cnf', [status(esa)], [dt_k4_tmap_1])).
% 4.66/4.86  thf('18', plain,
% 4.66/4.86      (((v1_funct_2 @ (k4_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_B) @ 
% 4.66/4.86         (u1_struct_0 @ sk_A))
% 4.66/4.86        | (v2_struct_0 @ sk_A)
% 4.66/4.86        | ~ (v2_pre_topc @ sk_A)
% 4.66/4.86        | ~ (l1_pre_topc @ sk_A))),
% 4.66/4.86      inference('sup-', [status(thm)], ['16', '17'])).
% 4.66/4.86  thf('19', plain, ((v2_pre_topc @ sk_A)),
% 4.66/4.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.66/4.86  thf('20', plain, ((l1_pre_topc @ sk_A)),
% 4.66/4.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.66/4.86  thf('21', plain,
% 4.66/4.86      (((v1_funct_2 @ (k4_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_B) @ 
% 4.66/4.86         (u1_struct_0 @ sk_A))
% 4.66/4.86        | (v2_struct_0 @ sk_A))),
% 4.66/4.86      inference('demod', [status(thm)], ['18', '19', '20'])).
% 4.66/4.86  thf('22', plain, (~ (v2_struct_0 @ sk_A)),
% 4.66/4.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.66/4.86  thf('23', plain,
% 4.66/4.86      ((v1_funct_2 @ (k4_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_B) @ 
% 4.66/4.86        (u1_struct_0 @ sk_A))),
% 4.66/4.86      inference('clc', [status(thm)], ['21', '22'])).
% 4.66/4.86  thf('24', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 4.66/4.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.66/4.86  thf('25', plain,
% 4.66/4.86      (![X33 : $i, X34 : $i]:
% 4.66/4.86         (~ (l1_pre_topc @ X33)
% 4.66/4.86          | ~ (v2_pre_topc @ X33)
% 4.66/4.86          | (v2_struct_0 @ X33)
% 4.66/4.86          | ~ (m1_pre_topc @ X34 @ X33)
% 4.66/4.86          | (v1_funct_1 @ (k4_tmap_1 @ X33 @ X34)))),
% 4.66/4.86      inference('cnf', [status(esa)], [dt_k4_tmap_1])).
% 4.66/4.86  thf('26', plain,
% 4.66/4.86      (((v1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_B))
% 4.66/4.86        | (v2_struct_0 @ sk_A)
% 4.66/4.86        | ~ (v2_pre_topc @ sk_A)
% 4.66/4.86        | ~ (l1_pre_topc @ sk_A))),
% 4.66/4.86      inference('sup-', [status(thm)], ['24', '25'])).
% 4.66/4.86  thf('27', plain, ((v2_pre_topc @ sk_A)),
% 4.66/4.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.66/4.86  thf('28', plain, ((l1_pre_topc @ sk_A)),
% 4.66/4.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.66/4.86  thf('29', plain,
% 4.66/4.86      (((v1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_B)) | (v2_struct_0 @ sk_A))),
% 4.66/4.86      inference('demod', [status(thm)], ['26', '27', '28'])).
% 4.66/4.86  thf('30', plain, (~ (v2_struct_0 @ sk_A)),
% 4.66/4.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.66/4.86  thf('31', plain, ((v1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_B))),
% 4.66/4.86      inference('clc', [status(thm)], ['29', '30'])).
% 4.66/4.86  thf('32', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 4.66/4.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.66/4.86  thf(dt_m1_pre_topc, axiom,
% 4.66/4.86    (![A:$i]:
% 4.66/4.86     ( ( l1_pre_topc @ A ) =>
% 4.66/4.86       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 4.66/4.86  thf('33', plain,
% 4.66/4.86      (![X16 : $i, X17 : $i]:
% 4.66/4.86         (~ (m1_pre_topc @ X16 @ X17)
% 4.66/4.86          | (l1_pre_topc @ X16)
% 4.66/4.86          | ~ (l1_pre_topc @ X17))),
% 4.66/4.86      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 4.66/4.86  thf('34', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_B))),
% 4.66/4.86      inference('sup-', [status(thm)], ['32', '33'])).
% 4.66/4.86  thf('35', plain, ((l1_pre_topc @ sk_A)),
% 4.66/4.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.66/4.86  thf('36', plain, ((l1_pre_topc @ sk_B)),
% 4.66/4.86      inference('demod', [status(thm)], ['34', '35'])).
% 4.66/4.86  thf('37', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 4.66/4.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.66/4.86  thf(cc1_pre_topc, axiom,
% 4.66/4.86    (![A:$i]:
% 4.66/4.86     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 4.66/4.86       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( v2_pre_topc @ B ) ) ) ))).
% 4.66/4.86  thf('38', plain,
% 4.66/4.86      (![X13 : $i, X14 : $i]:
% 4.66/4.86         (~ (m1_pre_topc @ X13 @ X14)
% 4.66/4.86          | (v2_pre_topc @ X13)
% 4.66/4.86          | ~ (l1_pre_topc @ X14)
% 4.66/4.86          | ~ (v2_pre_topc @ X14))),
% 4.66/4.86      inference('cnf', [status(esa)], [cc1_pre_topc])).
% 4.66/4.86  thf('39', plain,
% 4.66/4.86      ((~ (v2_pre_topc @ sk_A) | ~ (l1_pre_topc @ sk_A) | (v2_pre_topc @ sk_B))),
% 4.66/4.86      inference('sup-', [status(thm)], ['37', '38'])).
% 4.66/4.86  thf('40', plain, ((v2_pre_topc @ sk_A)),
% 4.66/4.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.66/4.86  thf('41', plain, ((l1_pre_topc @ sk_A)),
% 4.66/4.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.66/4.86  thf('42', plain, ((v2_pre_topc @ sk_B)),
% 4.66/4.86      inference('demod', [status(thm)], ['39', '40', '41'])).
% 4.66/4.86  thf('43', plain,
% 4.66/4.86      (![X0 : $i, X1 : $i]:
% 4.66/4.86         ((v2_struct_0 @ sk_A)
% 4.66/4.86          | (v2_struct_0 @ X0)
% 4.66/4.86          | ~ (m1_pre_topc @ X0 @ sk_B)
% 4.66/4.86          | ~ (v1_funct_1 @ X1)
% 4.66/4.86          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A))
% 4.66/4.86          | ~ (m1_subset_1 @ X1 @ 
% 4.66/4.86               (k1_zfmisc_1 @ 
% 4.66/4.86                (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A))))
% 4.66/4.86          | (r2_funct_2 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A) @ 
% 4.66/4.86             (k2_tmap_1 @ sk_B @ sk_A @ (k4_tmap_1 @ sk_A @ sk_B) @ X0) @ X1)
% 4.66/4.86          | (r2_hidden @ 
% 4.66/4.86             (sk_F @ X1 @ (k4_tmap_1 @ sk_A @ sk_B) @ X0 @ sk_B @ sk_A) @ 
% 4.66/4.86             (u1_struct_0 @ X0))
% 4.66/4.86          | (v2_struct_0 @ sk_B))),
% 4.66/4.86      inference('demod', [status(thm)],
% 4.66/4.86                ['13', '14', '15', '23', '31', '36', '42'])).
% 4.66/4.86  thf('44', plain,
% 4.66/4.86      (((v2_struct_0 @ sk_B)
% 4.66/4.86        | (r2_hidden @ 
% 4.66/4.86           (sk_F @ sk_C @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_B @ sk_B @ sk_A) @ 
% 4.66/4.86           (u1_struct_0 @ sk_B))
% 4.66/4.86        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 4.66/4.86           (k2_tmap_1 @ sk_B @ sk_A @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_B) @ sk_C)
% 4.66/4.86        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 4.66/4.86        | ~ (v1_funct_1 @ sk_C)
% 4.66/4.86        | ~ (m1_pre_topc @ sk_B @ sk_B)
% 4.66/4.86        | (v2_struct_0 @ sk_B)
% 4.66/4.86        | (v2_struct_0 @ sk_A))),
% 4.66/4.86      inference('sup-', [status(thm)], ['3', '43'])).
% 4.66/4.86  thf('45', plain,
% 4.66/4.86      (![X37 : $i]: ((m1_pre_topc @ X37 @ X37) | ~ (l1_pre_topc @ X37))),
% 4.66/4.86      inference('cnf', [status(esa)], [t2_tsep_1])).
% 4.66/4.86  thf('46', plain,
% 4.66/4.86      ((m1_subset_1 @ (k4_tmap_1 @ sk_A @ sk_B) @ 
% 4.66/4.86        (k1_zfmisc_1 @ 
% 4.66/4.86         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 4.66/4.86      inference('clc', [status(thm)], ['9', '10'])).
% 4.66/4.86  thf(t74_tmap_1, axiom,
% 4.66/4.86    (![A:$i]:
% 4.66/4.86     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 4.66/4.86       ( ![B:$i]:
% 4.66/4.86         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 4.66/4.86             ( l1_pre_topc @ B ) ) =>
% 4.66/4.86           ( ![C:$i]:
% 4.66/4.86             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 4.66/4.86               ( ![D:$i]:
% 4.66/4.86                 ( ( ( v1_funct_1 @ D ) & 
% 4.66/4.86                     ( v1_funct_2 @
% 4.66/4.86                       D @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 4.66/4.86                     ( m1_subset_1 @
% 4.66/4.86                       D @ 
% 4.66/4.86                       ( k1_zfmisc_1 @
% 4.66/4.86                         ( k2_zfmisc_1 @
% 4.66/4.86                           ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 4.66/4.86                   ( r2_funct_2 @
% 4.66/4.86                     ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ D @ 
% 4.66/4.86                     ( k3_tmap_1 @ A @ B @ C @ C @ D ) ) ) ) ) ) ) ) ))).
% 4.66/4.86  thf('47', plain,
% 4.66/4.86      (![X43 : $i, X44 : $i, X45 : $i, X46 : $i]:
% 4.66/4.86         ((v2_struct_0 @ X43)
% 4.66/4.86          | ~ (v2_pre_topc @ X43)
% 4.66/4.86          | ~ (l1_pre_topc @ X43)
% 4.66/4.86          | ~ (v1_funct_1 @ X44)
% 4.66/4.86          | ~ (v1_funct_2 @ X44 @ (u1_struct_0 @ X45) @ (u1_struct_0 @ X43))
% 4.66/4.86          | ~ (m1_subset_1 @ X44 @ 
% 4.66/4.86               (k1_zfmisc_1 @ 
% 4.66/4.86                (k2_zfmisc_1 @ (u1_struct_0 @ X45) @ (u1_struct_0 @ X43))))
% 4.66/4.86          | (r2_funct_2 @ (u1_struct_0 @ X45) @ (u1_struct_0 @ X43) @ X44 @ 
% 4.66/4.86             (k3_tmap_1 @ X46 @ X43 @ X45 @ X45 @ X44))
% 4.66/4.86          | ~ (m1_pre_topc @ X45 @ X46)
% 4.66/4.86          | (v2_struct_0 @ X45)
% 4.66/4.86          | ~ (l1_pre_topc @ X46)
% 4.66/4.86          | ~ (v2_pre_topc @ X46)
% 4.66/4.86          | (v2_struct_0 @ X46))),
% 4.66/4.86      inference('cnf', [status(esa)], [t74_tmap_1])).
% 4.66/4.86  thf('48', plain,
% 4.66/4.86      (![X0 : $i]:
% 4.66/4.86         ((v2_struct_0 @ X0)
% 4.66/4.86          | ~ (v2_pre_topc @ X0)
% 4.66/4.86          | ~ (l1_pre_topc @ X0)
% 4.66/4.86          | (v2_struct_0 @ sk_B)
% 4.66/4.86          | ~ (m1_pre_topc @ sk_B @ X0)
% 4.66/4.86          | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 4.66/4.86             (k4_tmap_1 @ sk_A @ sk_B) @ 
% 4.66/4.86             (k3_tmap_1 @ X0 @ sk_A @ sk_B @ sk_B @ (k4_tmap_1 @ sk_A @ sk_B)))
% 4.66/4.86          | ~ (v1_funct_2 @ (k4_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_B) @ 
% 4.66/4.86               (u1_struct_0 @ sk_A))
% 4.66/4.86          | ~ (v1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_B))
% 4.66/4.86          | ~ (l1_pre_topc @ sk_A)
% 4.66/4.86          | ~ (v2_pre_topc @ sk_A)
% 4.66/4.86          | (v2_struct_0 @ sk_A))),
% 4.66/4.86      inference('sup-', [status(thm)], ['46', '47'])).
% 4.66/4.86  thf('49', plain,
% 4.66/4.86      ((v1_funct_2 @ (k4_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_B) @ 
% 4.66/4.86        (u1_struct_0 @ sk_A))),
% 4.66/4.86      inference('clc', [status(thm)], ['21', '22'])).
% 4.66/4.86  thf('50', plain, ((v1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_B))),
% 4.66/4.86      inference('clc', [status(thm)], ['29', '30'])).
% 4.66/4.86  thf('51', plain, ((l1_pre_topc @ sk_A)),
% 4.66/4.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.66/4.86  thf('52', plain, ((v2_pre_topc @ sk_A)),
% 4.66/4.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.66/4.86  thf('53', plain,
% 4.66/4.86      (![X0 : $i]:
% 4.66/4.86         ((v2_struct_0 @ X0)
% 4.66/4.86          | ~ (v2_pre_topc @ X0)
% 4.66/4.86          | ~ (l1_pre_topc @ X0)
% 4.66/4.86          | (v2_struct_0 @ sk_B)
% 4.66/4.86          | ~ (m1_pre_topc @ sk_B @ X0)
% 4.66/4.86          | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 4.66/4.86             (k4_tmap_1 @ sk_A @ sk_B) @ 
% 4.66/4.86             (k3_tmap_1 @ X0 @ sk_A @ sk_B @ sk_B @ (k4_tmap_1 @ sk_A @ sk_B)))
% 4.66/4.86          | (v2_struct_0 @ sk_A))),
% 4.66/4.86      inference('demod', [status(thm)], ['48', '49', '50', '51', '52'])).
% 4.66/4.86  thf('54', plain,
% 4.66/4.86      ((~ (l1_pre_topc @ sk_B)
% 4.66/4.86        | (v2_struct_0 @ sk_A)
% 4.66/4.86        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 4.66/4.86           (k4_tmap_1 @ sk_A @ sk_B) @ 
% 4.66/4.86           (k3_tmap_1 @ sk_B @ sk_A @ sk_B @ sk_B @ (k4_tmap_1 @ sk_A @ sk_B)))
% 4.66/4.86        | (v2_struct_0 @ sk_B)
% 4.66/4.86        | ~ (l1_pre_topc @ sk_B)
% 4.66/4.86        | ~ (v2_pre_topc @ sk_B)
% 4.66/4.86        | (v2_struct_0 @ sk_B))),
% 4.66/4.86      inference('sup-', [status(thm)], ['45', '53'])).
% 4.66/4.86  thf('55', plain, ((l1_pre_topc @ sk_B)),
% 4.66/4.86      inference('demod', [status(thm)], ['34', '35'])).
% 4.66/4.86  thf('56', plain,
% 4.66/4.86      (![X37 : $i]: ((m1_pre_topc @ X37 @ X37) | ~ (l1_pre_topc @ X37))),
% 4.66/4.86      inference('cnf', [status(esa)], [t2_tsep_1])).
% 4.66/4.86  thf('57', plain,
% 4.66/4.86      (![X37 : $i]: ((m1_pre_topc @ X37 @ X37) | ~ (l1_pre_topc @ X37))),
% 4.66/4.86      inference('cnf', [status(esa)], [t2_tsep_1])).
% 4.66/4.86  thf('58', plain,
% 4.66/4.86      ((m1_subset_1 @ (k4_tmap_1 @ sk_A @ sk_B) @ 
% 4.66/4.86        (k1_zfmisc_1 @ 
% 4.66/4.86         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 4.66/4.86      inference('clc', [status(thm)], ['9', '10'])).
% 4.66/4.86  thf(d5_tmap_1, axiom,
% 4.66/4.86    (![A:$i]:
% 4.66/4.86     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 4.66/4.86       ( ![B:$i]:
% 4.66/4.86         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 4.66/4.86             ( l1_pre_topc @ B ) ) =>
% 4.66/4.86           ( ![C:$i]:
% 4.66/4.86             ( ( m1_pre_topc @ C @ A ) =>
% 4.66/4.86               ( ![D:$i]:
% 4.66/4.86                 ( ( m1_pre_topc @ D @ A ) =>
% 4.66/4.86                   ( ![E:$i]:
% 4.66/4.86                     ( ( ( v1_funct_1 @ E ) & 
% 4.66/4.86                         ( v1_funct_2 @
% 4.66/4.86                           E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 4.66/4.86                         ( m1_subset_1 @
% 4.66/4.86                           E @ 
% 4.66/4.86                           ( k1_zfmisc_1 @
% 4.66/4.86                             ( k2_zfmisc_1 @
% 4.66/4.86                               ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 4.66/4.86                       ( ( m1_pre_topc @ D @ C ) =>
% 4.66/4.86                         ( ( k3_tmap_1 @ A @ B @ C @ D @ E ) =
% 4.66/4.86                           ( k2_partfun1 @
% 4.66/4.86                             ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ E @ 
% 4.66/4.86                             ( u1_struct_0 @ D ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 4.66/4.86  thf('59', plain,
% 4.66/4.86      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 4.66/4.86         ((v2_struct_0 @ X23)
% 4.66/4.86          | ~ (v2_pre_topc @ X23)
% 4.66/4.86          | ~ (l1_pre_topc @ X23)
% 4.66/4.86          | ~ (m1_pre_topc @ X24 @ X25)
% 4.66/4.86          | ~ (m1_pre_topc @ X24 @ X26)
% 4.66/4.86          | ((k3_tmap_1 @ X25 @ X23 @ X26 @ X24 @ X27)
% 4.66/4.86              = (k2_partfun1 @ (u1_struct_0 @ X26) @ (u1_struct_0 @ X23) @ 
% 4.66/4.86                 X27 @ (u1_struct_0 @ X24)))
% 4.66/4.86          | ~ (m1_subset_1 @ X27 @ 
% 4.66/4.86               (k1_zfmisc_1 @ 
% 4.66/4.86                (k2_zfmisc_1 @ (u1_struct_0 @ X26) @ (u1_struct_0 @ X23))))
% 4.66/4.86          | ~ (v1_funct_2 @ X27 @ (u1_struct_0 @ X26) @ (u1_struct_0 @ X23))
% 4.66/4.86          | ~ (v1_funct_1 @ X27)
% 4.66/4.86          | ~ (m1_pre_topc @ X26 @ X25)
% 4.66/4.86          | ~ (l1_pre_topc @ X25)
% 4.66/4.86          | ~ (v2_pre_topc @ X25)
% 4.66/4.86          | (v2_struct_0 @ X25))),
% 4.66/4.86      inference('cnf', [status(esa)], [d5_tmap_1])).
% 4.66/4.86  thf('60', plain,
% 4.66/4.86      (![X0 : $i, X1 : $i]:
% 4.66/4.86         ((v2_struct_0 @ X0)
% 4.66/4.86          | ~ (v2_pre_topc @ X0)
% 4.66/4.86          | ~ (l1_pre_topc @ X0)
% 4.66/4.86          | ~ (m1_pre_topc @ sk_B @ X0)
% 4.66/4.86          | ~ (v1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_B))
% 4.66/4.86          | ~ (v1_funct_2 @ (k4_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_B) @ 
% 4.66/4.86               (u1_struct_0 @ sk_A))
% 4.66/4.86          | ((k3_tmap_1 @ X0 @ sk_A @ sk_B @ X1 @ (k4_tmap_1 @ sk_A @ sk_B))
% 4.66/4.86              = (k2_partfun1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 4.66/4.86                 (k4_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ X1)))
% 4.66/4.86          | ~ (m1_pre_topc @ X1 @ sk_B)
% 4.66/4.86          | ~ (m1_pre_topc @ X1 @ X0)
% 4.66/4.86          | ~ (l1_pre_topc @ sk_A)
% 4.66/4.86          | ~ (v2_pre_topc @ sk_A)
% 4.66/4.86          | (v2_struct_0 @ sk_A))),
% 4.66/4.86      inference('sup-', [status(thm)], ['58', '59'])).
% 4.66/4.86  thf('61', plain, ((v1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_B))),
% 4.66/4.86      inference('clc', [status(thm)], ['29', '30'])).
% 4.66/4.86  thf('62', plain,
% 4.66/4.86      ((v1_funct_2 @ (k4_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_B) @ 
% 4.66/4.86        (u1_struct_0 @ sk_A))),
% 4.66/4.86      inference('clc', [status(thm)], ['21', '22'])).
% 4.66/4.86  thf('63', plain, ((l1_pre_topc @ sk_A)),
% 4.66/4.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.66/4.86  thf('64', plain, ((v2_pre_topc @ sk_A)),
% 4.66/4.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.66/4.86  thf('65', plain,
% 4.66/4.86      (![X0 : $i, X1 : $i]:
% 4.66/4.86         ((v2_struct_0 @ X0)
% 4.66/4.86          | ~ (v2_pre_topc @ X0)
% 4.66/4.86          | ~ (l1_pre_topc @ X0)
% 4.66/4.86          | ~ (m1_pre_topc @ sk_B @ X0)
% 4.66/4.86          | ((k3_tmap_1 @ X0 @ sk_A @ sk_B @ X1 @ (k4_tmap_1 @ sk_A @ sk_B))
% 4.66/4.86              = (k2_partfun1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 4.66/4.86                 (k4_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ X1)))
% 4.66/4.86          | ~ (m1_pre_topc @ X1 @ sk_B)
% 4.66/4.86          | ~ (m1_pre_topc @ X1 @ X0)
% 4.66/4.86          | (v2_struct_0 @ sk_A))),
% 4.66/4.86      inference('demod', [status(thm)], ['60', '61', '62', '63', '64'])).
% 4.66/4.86  thf('66', plain,
% 4.66/4.86      (![X0 : $i]:
% 4.66/4.86         (~ (l1_pre_topc @ sk_B)
% 4.66/4.86          | (v2_struct_0 @ sk_A)
% 4.66/4.86          | ~ (m1_pre_topc @ X0 @ sk_B)
% 4.66/4.86          | ~ (m1_pre_topc @ X0 @ sk_B)
% 4.66/4.86          | ((k3_tmap_1 @ sk_B @ sk_A @ sk_B @ X0 @ (k4_tmap_1 @ sk_A @ sk_B))
% 4.66/4.86              = (k2_partfun1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 4.66/4.86                 (k4_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ X0)))
% 4.66/4.86          | ~ (l1_pre_topc @ sk_B)
% 4.66/4.86          | ~ (v2_pre_topc @ sk_B)
% 4.66/4.86          | (v2_struct_0 @ sk_B))),
% 4.66/4.86      inference('sup-', [status(thm)], ['57', '65'])).
% 4.66/4.86  thf('67', plain, ((l1_pre_topc @ sk_B)),
% 4.66/4.86      inference('demod', [status(thm)], ['34', '35'])).
% 4.66/4.86  thf('68', plain, ((l1_pre_topc @ sk_B)),
% 4.66/4.86      inference('demod', [status(thm)], ['34', '35'])).
% 4.66/4.86  thf('69', plain, ((v2_pre_topc @ sk_B)),
% 4.66/4.86      inference('demod', [status(thm)], ['39', '40', '41'])).
% 4.66/4.86  thf('70', plain,
% 4.66/4.86      (![X0 : $i]:
% 4.66/4.86         ((v2_struct_0 @ sk_A)
% 4.66/4.86          | ~ (m1_pre_topc @ X0 @ sk_B)
% 4.66/4.86          | ~ (m1_pre_topc @ X0 @ sk_B)
% 4.66/4.86          | ((k3_tmap_1 @ sk_B @ sk_A @ sk_B @ X0 @ (k4_tmap_1 @ sk_A @ sk_B))
% 4.66/4.86              = (k2_partfun1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 4.66/4.86                 (k4_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ X0)))
% 4.66/4.86          | (v2_struct_0 @ sk_B))),
% 4.66/4.86      inference('demod', [status(thm)], ['66', '67', '68', '69'])).
% 4.66/4.86  thf('71', plain,
% 4.66/4.86      (![X0 : $i]:
% 4.66/4.86         ((v2_struct_0 @ sk_B)
% 4.66/4.86          | ((k3_tmap_1 @ sk_B @ sk_A @ sk_B @ X0 @ (k4_tmap_1 @ sk_A @ sk_B))
% 4.66/4.86              = (k2_partfun1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 4.66/4.86                 (k4_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ X0)))
% 4.66/4.86          | ~ (m1_pre_topc @ X0 @ sk_B)
% 4.66/4.86          | (v2_struct_0 @ sk_A))),
% 4.66/4.86      inference('simplify', [status(thm)], ['70'])).
% 4.66/4.86  thf('72', plain,
% 4.66/4.86      ((~ (l1_pre_topc @ sk_B)
% 4.66/4.86        | (v2_struct_0 @ sk_A)
% 4.66/4.86        | ((k3_tmap_1 @ sk_B @ sk_A @ sk_B @ sk_B @ (k4_tmap_1 @ sk_A @ sk_B))
% 4.66/4.86            = (k2_partfun1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 4.66/4.86               (k4_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_B)))
% 4.66/4.86        | (v2_struct_0 @ sk_B))),
% 4.66/4.86      inference('sup-', [status(thm)], ['56', '71'])).
% 4.66/4.86  thf('73', plain, ((l1_pre_topc @ sk_B)),
% 4.66/4.86      inference('demod', [status(thm)], ['34', '35'])).
% 4.66/4.86  thf('74', plain,
% 4.66/4.86      (![X37 : $i]: ((m1_pre_topc @ X37 @ X37) | ~ (l1_pre_topc @ X37))),
% 4.66/4.86      inference('cnf', [status(esa)], [t2_tsep_1])).
% 4.66/4.86  thf('75', plain,
% 4.66/4.86      ((m1_subset_1 @ (k4_tmap_1 @ sk_A @ sk_B) @ 
% 4.66/4.86        (k1_zfmisc_1 @ 
% 4.66/4.86         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 4.66/4.86      inference('clc', [status(thm)], ['9', '10'])).
% 4.66/4.86  thf(d4_tmap_1, axiom,
% 4.66/4.86    (![A:$i]:
% 4.66/4.86     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 4.66/4.86       ( ![B:$i]:
% 4.66/4.86         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 4.66/4.86             ( l1_pre_topc @ B ) ) =>
% 4.66/4.86           ( ![C:$i]:
% 4.66/4.86             ( ( ( v1_funct_1 @ C ) & 
% 4.66/4.86                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 4.66/4.86                 ( m1_subset_1 @
% 4.66/4.86                   C @ 
% 4.66/4.86                   ( k1_zfmisc_1 @
% 4.66/4.86                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 4.66/4.86               ( ![D:$i]:
% 4.66/4.86                 ( ( m1_pre_topc @ D @ A ) =>
% 4.66/4.86                   ( ( k2_tmap_1 @ A @ B @ C @ D ) =
% 4.66/4.86                     ( k2_partfun1 @
% 4.66/4.86                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ 
% 4.66/4.86                       ( u1_struct_0 @ D ) ) ) ) ) ) ) ) ) ))).
% 4.66/4.86  thf('76', plain,
% 4.66/4.86      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 4.66/4.86         ((v2_struct_0 @ X19)
% 4.66/4.86          | ~ (v2_pre_topc @ X19)
% 4.66/4.86          | ~ (l1_pre_topc @ X19)
% 4.66/4.86          | ~ (m1_pre_topc @ X20 @ X21)
% 4.66/4.86          | ((k2_tmap_1 @ X21 @ X19 @ X22 @ X20)
% 4.66/4.86              = (k2_partfun1 @ (u1_struct_0 @ X21) @ (u1_struct_0 @ X19) @ 
% 4.66/4.86                 X22 @ (u1_struct_0 @ X20)))
% 4.66/4.86          | ~ (m1_subset_1 @ X22 @ 
% 4.66/4.86               (k1_zfmisc_1 @ 
% 4.66/4.86                (k2_zfmisc_1 @ (u1_struct_0 @ X21) @ (u1_struct_0 @ X19))))
% 4.66/4.86          | ~ (v1_funct_2 @ X22 @ (u1_struct_0 @ X21) @ (u1_struct_0 @ X19))
% 4.66/4.86          | ~ (v1_funct_1 @ X22)
% 4.66/4.86          | ~ (l1_pre_topc @ X21)
% 4.66/4.86          | ~ (v2_pre_topc @ X21)
% 4.66/4.86          | (v2_struct_0 @ X21))),
% 4.66/4.86      inference('cnf', [status(esa)], [d4_tmap_1])).
% 4.66/4.86  thf('77', plain,
% 4.66/4.86      (![X0 : $i]:
% 4.66/4.86         ((v2_struct_0 @ sk_B)
% 4.66/4.86          | ~ (v2_pre_topc @ sk_B)
% 4.66/4.86          | ~ (l1_pre_topc @ sk_B)
% 4.66/4.86          | ~ (v1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_B))
% 4.66/4.86          | ~ (v1_funct_2 @ (k4_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_B) @ 
% 4.66/4.86               (u1_struct_0 @ sk_A))
% 4.66/4.86          | ((k2_tmap_1 @ sk_B @ sk_A @ (k4_tmap_1 @ sk_A @ sk_B) @ X0)
% 4.66/4.86              = (k2_partfun1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 4.66/4.86                 (k4_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ X0)))
% 4.66/4.86          | ~ (m1_pre_topc @ X0 @ sk_B)
% 4.66/4.86          | ~ (l1_pre_topc @ sk_A)
% 4.66/4.86          | ~ (v2_pre_topc @ sk_A)
% 4.66/4.86          | (v2_struct_0 @ sk_A))),
% 4.66/4.86      inference('sup-', [status(thm)], ['75', '76'])).
% 4.66/4.86  thf('78', plain, ((v2_pre_topc @ sk_B)),
% 4.66/4.86      inference('demod', [status(thm)], ['39', '40', '41'])).
% 4.66/4.86  thf('79', plain, ((l1_pre_topc @ sk_B)),
% 4.66/4.86      inference('demod', [status(thm)], ['34', '35'])).
% 4.66/4.86  thf('80', plain, ((v1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_B))),
% 4.66/4.86      inference('clc', [status(thm)], ['29', '30'])).
% 4.66/4.86  thf('81', plain,
% 4.66/4.86      ((v1_funct_2 @ (k4_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_B) @ 
% 4.66/4.86        (u1_struct_0 @ sk_A))),
% 4.66/4.86      inference('clc', [status(thm)], ['21', '22'])).
% 4.66/4.86  thf('82', plain, ((l1_pre_topc @ sk_A)),
% 4.66/4.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.66/4.86  thf('83', plain, ((v2_pre_topc @ sk_A)),
% 4.66/4.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.66/4.86  thf('84', plain,
% 4.66/4.86      (![X0 : $i]:
% 4.66/4.86         ((v2_struct_0 @ sk_B)
% 4.66/4.86          | ((k2_tmap_1 @ sk_B @ sk_A @ (k4_tmap_1 @ sk_A @ sk_B) @ X0)
% 4.66/4.86              = (k2_partfun1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 4.66/4.86                 (k4_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ X0)))
% 4.66/4.86          | ~ (m1_pre_topc @ X0 @ sk_B)
% 4.66/4.86          | (v2_struct_0 @ sk_A))),
% 4.66/4.86      inference('demod', [status(thm)],
% 4.66/4.86                ['77', '78', '79', '80', '81', '82', '83'])).
% 4.66/4.86  thf('85', plain,
% 4.66/4.86      ((~ (l1_pre_topc @ sk_B)
% 4.66/4.86        | (v2_struct_0 @ sk_A)
% 4.66/4.86        | ((k2_tmap_1 @ sk_B @ sk_A @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_B)
% 4.66/4.86            = (k2_partfun1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 4.66/4.86               (k4_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_B)))
% 4.66/4.86        | (v2_struct_0 @ sk_B))),
% 4.66/4.86      inference('sup-', [status(thm)], ['74', '84'])).
% 4.66/4.86  thf('86', plain, ((l1_pre_topc @ sk_B)),
% 4.66/4.86      inference('demod', [status(thm)], ['34', '35'])).
% 4.66/4.86  thf('87', plain,
% 4.66/4.86      (((v2_struct_0 @ sk_A)
% 4.66/4.86        | ((k2_tmap_1 @ sk_B @ sk_A @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_B)
% 4.66/4.86            = (k2_partfun1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 4.66/4.86               (k4_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_B)))
% 4.66/4.86        | (v2_struct_0 @ sk_B))),
% 4.66/4.86      inference('demod', [status(thm)], ['85', '86'])).
% 4.66/4.86  thf('88', plain, (~ (v2_struct_0 @ sk_A)),
% 4.66/4.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.66/4.86  thf('89', plain,
% 4.66/4.86      (((v2_struct_0 @ sk_B)
% 4.66/4.86        | ((k2_tmap_1 @ sk_B @ sk_A @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_B)
% 4.66/4.86            = (k2_partfun1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 4.66/4.86               (k4_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_B))))),
% 4.66/4.86      inference('clc', [status(thm)], ['87', '88'])).
% 4.66/4.86  thf('90', plain, (~ (v2_struct_0 @ sk_B)),
% 4.66/4.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.66/4.86  thf('91', plain,
% 4.66/4.86      (((k2_tmap_1 @ sk_B @ sk_A @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_B)
% 4.66/4.86         = (k2_partfun1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 4.66/4.86            (k4_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_B)))),
% 4.66/4.86      inference('clc', [status(thm)], ['89', '90'])).
% 4.66/4.86  thf('92', plain,
% 4.66/4.86      (((v2_struct_0 @ sk_A)
% 4.66/4.86        | ((k3_tmap_1 @ sk_B @ sk_A @ sk_B @ sk_B @ (k4_tmap_1 @ sk_A @ sk_B))
% 4.66/4.86            = (k2_tmap_1 @ sk_B @ sk_A @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_B))
% 4.66/4.86        | (v2_struct_0 @ sk_B))),
% 4.66/4.86      inference('demod', [status(thm)], ['72', '73', '91'])).
% 4.66/4.86  thf('93', plain, (~ (v2_struct_0 @ sk_A)),
% 4.66/4.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.66/4.86  thf('94', plain,
% 4.66/4.86      (((v2_struct_0 @ sk_B)
% 4.66/4.86        | ((k3_tmap_1 @ sk_B @ sk_A @ sk_B @ sk_B @ (k4_tmap_1 @ sk_A @ sk_B))
% 4.66/4.86            = (k2_tmap_1 @ sk_B @ sk_A @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_B)))),
% 4.66/4.86      inference('clc', [status(thm)], ['92', '93'])).
% 4.66/4.86  thf('95', plain, (~ (v2_struct_0 @ sk_B)),
% 4.66/4.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.66/4.86  thf('96', plain,
% 4.66/4.86      (((k3_tmap_1 @ sk_B @ sk_A @ sk_B @ sk_B @ (k4_tmap_1 @ sk_A @ sk_B))
% 4.66/4.86         = (k2_tmap_1 @ sk_B @ sk_A @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_B))),
% 4.66/4.86      inference('clc', [status(thm)], ['94', '95'])).
% 4.66/4.86  thf('97', plain, ((l1_pre_topc @ sk_B)),
% 4.66/4.86      inference('demod', [status(thm)], ['34', '35'])).
% 4.66/4.86  thf('98', plain, ((v2_pre_topc @ sk_B)),
% 4.66/4.86      inference('demod', [status(thm)], ['39', '40', '41'])).
% 4.66/4.86  thf('99', plain,
% 4.66/4.86      (((v2_struct_0 @ sk_A)
% 4.66/4.86        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 4.66/4.86           (k4_tmap_1 @ sk_A @ sk_B) @ 
% 4.66/4.86           (k2_tmap_1 @ sk_B @ sk_A @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_B))
% 4.66/4.86        | (v2_struct_0 @ sk_B)
% 4.66/4.86        | (v2_struct_0 @ sk_B))),
% 4.66/4.86      inference('demod', [status(thm)], ['54', '55', '96', '97', '98'])).
% 4.66/4.86  thf('100', plain,
% 4.66/4.86      (((v2_struct_0 @ sk_B)
% 4.66/4.86        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 4.66/4.86           (k4_tmap_1 @ sk_A @ sk_B) @ 
% 4.66/4.86           (k2_tmap_1 @ sk_B @ sk_A @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_B))
% 4.66/4.86        | (v2_struct_0 @ sk_A))),
% 4.66/4.86      inference('simplify', [status(thm)], ['99'])).
% 4.66/4.86  thf('101', plain, (~ (v2_struct_0 @ sk_B)),
% 4.66/4.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.66/4.86  thf('102', plain,
% 4.66/4.86      (((v2_struct_0 @ sk_A)
% 4.66/4.86        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 4.66/4.86           (k4_tmap_1 @ sk_A @ sk_B) @ 
% 4.66/4.86           (k2_tmap_1 @ sk_B @ sk_A @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_B)))),
% 4.66/4.86      inference('clc', [status(thm)], ['100', '101'])).
% 4.66/4.86  thf('103', plain, (~ (v2_struct_0 @ sk_A)),
% 4.66/4.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.66/4.86  thf('104', plain,
% 4.66/4.86      ((r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 4.66/4.86        (k4_tmap_1 @ sk_A @ sk_B) @ 
% 4.66/4.86        (k2_tmap_1 @ sk_B @ sk_A @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_B))),
% 4.66/4.86      inference('clc', [status(thm)], ['102', '103'])).
% 4.66/4.86  thf('105', plain,
% 4.66/4.86      ((m1_subset_1 @ (k4_tmap_1 @ sk_A @ sk_B) @ 
% 4.66/4.86        (k1_zfmisc_1 @ 
% 4.66/4.86         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 4.66/4.86      inference('clc', [status(thm)], ['9', '10'])).
% 4.66/4.86  thf(redefinition_r2_funct_2, axiom,
% 4.66/4.86    (![A:$i,B:$i,C:$i,D:$i]:
% 4.66/4.86     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 4.66/4.86         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 4.66/4.86         ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 4.66/4.86         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 4.66/4.86       ( ( r2_funct_2 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 4.66/4.86  thf('106', plain,
% 4.66/4.86      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 4.66/4.86         (~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11)))
% 4.66/4.86          | ~ (v1_funct_2 @ X9 @ X10 @ X11)
% 4.66/4.86          | ~ (v1_funct_1 @ X9)
% 4.66/4.86          | ~ (v1_funct_1 @ X12)
% 4.66/4.86          | ~ (v1_funct_2 @ X12 @ X10 @ X11)
% 4.66/4.86          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11)))
% 4.66/4.86          | ((X9) = (X12))
% 4.66/4.86          | ~ (r2_funct_2 @ X10 @ X11 @ X9 @ X12))),
% 4.66/4.86      inference('cnf', [status(esa)], [redefinition_r2_funct_2])).
% 4.66/4.86  thf('107', plain,
% 4.66/4.86      (![X0 : $i]:
% 4.66/4.86         (~ (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 4.66/4.86             (k4_tmap_1 @ sk_A @ sk_B) @ X0)
% 4.66/4.86          | ((k4_tmap_1 @ sk_A @ sk_B) = (X0))
% 4.66/4.86          | ~ (m1_subset_1 @ X0 @ 
% 4.66/4.86               (k1_zfmisc_1 @ 
% 4.66/4.86                (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))
% 4.66/4.86          | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 4.66/4.86          | ~ (v1_funct_1 @ X0)
% 4.66/4.86          | ~ (v1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_B))
% 4.66/4.86          | ~ (v1_funct_2 @ (k4_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_B) @ 
% 4.66/4.86               (u1_struct_0 @ sk_A)))),
% 4.66/4.86      inference('sup-', [status(thm)], ['105', '106'])).
% 4.66/4.86  thf('108', plain, ((v1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_B))),
% 4.66/4.86      inference('clc', [status(thm)], ['29', '30'])).
% 4.66/4.86  thf('109', plain,
% 4.66/4.86      ((v1_funct_2 @ (k4_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_B) @ 
% 4.66/4.86        (u1_struct_0 @ sk_A))),
% 4.66/4.86      inference('clc', [status(thm)], ['21', '22'])).
% 4.66/4.86  thf('110', plain,
% 4.66/4.86      (![X0 : $i]:
% 4.66/4.86         (~ (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 4.66/4.86             (k4_tmap_1 @ sk_A @ sk_B) @ X0)
% 4.66/4.86          | ((k4_tmap_1 @ sk_A @ sk_B) = (X0))
% 4.66/4.86          | ~ (m1_subset_1 @ X0 @ 
% 4.66/4.86               (k1_zfmisc_1 @ 
% 4.66/4.86                (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))
% 4.66/4.86          | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 4.66/4.86          | ~ (v1_funct_1 @ X0))),
% 4.66/4.86      inference('demod', [status(thm)], ['107', '108', '109'])).
% 4.66/4.86  thf('111', plain,
% 4.66/4.86      ((~ (v1_funct_1 @ 
% 4.66/4.86           (k2_tmap_1 @ sk_B @ sk_A @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_B))
% 4.66/4.86        | ~ (v1_funct_2 @ 
% 4.66/4.86             (k2_tmap_1 @ sk_B @ sk_A @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_B) @ 
% 4.66/4.86             (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 4.66/4.86        | ~ (m1_subset_1 @ 
% 4.66/4.86             (k2_tmap_1 @ sk_B @ sk_A @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_B) @ 
% 4.66/4.86             (k1_zfmisc_1 @ 
% 4.66/4.86              (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))
% 4.66/4.86        | ((k4_tmap_1 @ sk_A @ sk_B)
% 4.66/4.86            = (k2_tmap_1 @ sk_B @ sk_A @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_B)))),
% 4.66/4.86      inference('sup-', [status(thm)], ['104', '110'])).
% 4.66/4.86  thf('112', plain,
% 4.66/4.86      (![X37 : $i]: ((m1_pre_topc @ X37 @ X37) | ~ (l1_pre_topc @ X37))),
% 4.66/4.86      inference('cnf', [status(esa)], [t2_tsep_1])).
% 4.66/4.86  thf('113', plain,
% 4.66/4.86      (![X37 : $i]: ((m1_pre_topc @ X37 @ X37) | ~ (l1_pre_topc @ X37))),
% 4.66/4.86      inference('cnf', [status(esa)], [t2_tsep_1])).
% 4.66/4.86  thf('114', plain,
% 4.66/4.86      ((m1_subset_1 @ (k4_tmap_1 @ sk_A @ sk_B) @ 
% 4.66/4.86        (k1_zfmisc_1 @ 
% 4.66/4.86         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 4.66/4.86      inference('clc', [status(thm)], ['9', '10'])).
% 4.66/4.86  thf(dt_k3_tmap_1, axiom,
% 4.66/4.86    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 4.66/4.86     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 4.66/4.86         ( l1_pre_topc @ A ) & ( ~( v2_struct_0 @ B ) ) & 
% 4.66/4.86         ( v2_pre_topc @ B ) & ( l1_pre_topc @ B ) & ( m1_pre_topc @ C @ A ) & 
% 4.66/4.86         ( m1_pre_topc @ D @ A ) & ( v1_funct_1 @ E ) & 
% 4.66/4.86         ( v1_funct_2 @ E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 4.66/4.86         ( m1_subset_1 @
% 4.66/4.86           E @ 
% 4.66/4.86           ( k1_zfmisc_1 @
% 4.66/4.86             ( k2_zfmisc_1 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 4.66/4.86       ( ( v1_funct_1 @ ( k3_tmap_1 @ A @ B @ C @ D @ E ) ) & 
% 4.66/4.86         ( v1_funct_2 @
% 4.66/4.86           ( k3_tmap_1 @ A @ B @ C @ D @ E ) @ ( u1_struct_0 @ D ) @ 
% 4.66/4.86           ( u1_struct_0 @ B ) ) & 
% 4.66/4.86         ( m1_subset_1 @
% 4.66/4.86           ( k3_tmap_1 @ A @ B @ C @ D @ E ) @ 
% 4.66/4.86           ( k1_zfmisc_1 @
% 4.66/4.86             ( k2_zfmisc_1 @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) ))).
% 4.66/4.86  thf('115', plain,
% 4.66/4.86      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 4.66/4.86         (~ (m1_pre_topc @ X28 @ X29)
% 4.66/4.86          | ~ (m1_pre_topc @ X30 @ X29)
% 4.66/4.86          | ~ (l1_pre_topc @ X31)
% 4.66/4.86          | ~ (v2_pre_topc @ X31)
% 4.66/4.86          | (v2_struct_0 @ X31)
% 4.66/4.86          | ~ (l1_pre_topc @ X29)
% 4.66/4.86          | ~ (v2_pre_topc @ X29)
% 4.66/4.86          | (v2_struct_0 @ X29)
% 4.66/4.86          | ~ (v1_funct_1 @ X32)
% 4.66/4.86          | ~ (v1_funct_2 @ X32 @ (u1_struct_0 @ X30) @ (u1_struct_0 @ X31))
% 4.66/4.86          | ~ (m1_subset_1 @ X32 @ 
% 4.66/4.86               (k1_zfmisc_1 @ 
% 4.66/4.86                (k2_zfmisc_1 @ (u1_struct_0 @ X30) @ (u1_struct_0 @ X31))))
% 4.66/4.86          | (v1_funct_1 @ (k3_tmap_1 @ X29 @ X31 @ X30 @ X28 @ X32)))),
% 4.66/4.86      inference('cnf', [status(esa)], [dt_k3_tmap_1])).
% 4.66/4.86  thf('116', plain,
% 4.66/4.86      (![X0 : $i, X1 : $i]:
% 4.66/4.86         ((v1_funct_1 @ 
% 4.66/4.86           (k3_tmap_1 @ X1 @ sk_A @ sk_B @ X0 @ (k4_tmap_1 @ sk_A @ sk_B)))
% 4.66/4.86          | ~ (v1_funct_2 @ (k4_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_B) @ 
% 4.66/4.86               (u1_struct_0 @ sk_A))
% 4.66/4.86          | ~ (v1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_B))
% 4.66/4.86          | (v2_struct_0 @ X1)
% 4.66/4.86          | ~ (v2_pre_topc @ X1)
% 4.66/4.86          | ~ (l1_pre_topc @ X1)
% 4.66/4.86          | (v2_struct_0 @ sk_A)
% 4.66/4.86          | ~ (v2_pre_topc @ sk_A)
% 4.66/4.86          | ~ (l1_pre_topc @ sk_A)
% 4.66/4.86          | ~ (m1_pre_topc @ sk_B @ X1)
% 4.66/4.86          | ~ (m1_pre_topc @ X0 @ X1))),
% 4.66/4.86      inference('sup-', [status(thm)], ['114', '115'])).
% 4.66/4.86  thf('117', plain,
% 4.66/4.86      ((v1_funct_2 @ (k4_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_B) @ 
% 4.66/4.86        (u1_struct_0 @ sk_A))),
% 4.66/4.86      inference('clc', [status(thm)], ['21', '22'])).
% 4.66/4.86  thf('118', plain, ((v1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_B))),
% 4.66/4.86      inference('clc', [status(thm)], ['29', '30'])).
% 4.66/4.86  thf('119', plain, ((v2_pre_topc @ sk_A)),
% 4.66/4.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.66/4.86  thf('120', plain, ((l1_pre_topc @ sk_A)),
% 4.66/4.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.66/4.86  thf('121', plain,
% 4.66/4.86      (![X0 : $i, X1 : $i]:
% 4.66/4.86         ((v1_funct_1 @ 
% 4.66/4.86           (k3_tmap_1 @ X1 @ sk_A @ sk_B @ X0 @ (k4_tmap_1 @ sk_A @ sk_B)))
% 4.66/4.86          | (v2_struct_0 @ X1)
% 4.66/4.86          | ~ (v2_pre_topc @ X1)
% 4.66/4.86          | ~ (l1_pre_topc @ X1)
% 4.66/4.86          | (v2_struct_0 @ sk_A)
% 4.66/4.86          | ~ (m1_pre_topc @ sk_B @ X1)
% 4.66/4.86          | ~ (m1_pre_topc @ X0 @ X1))),
% 4.66/4.86      inference('demod', [status(thm)], ['116', '117', '118', '119', '120'])).
% 4.66/4.86  thf('122', plain,
% 4.66/4.86      (![X0 : $i]:
% 4.66/4.86         (~ (l1_pre_topc @ sk_B)
% 4.66/4.86          | ~ (m1_pre_topc @ X0 @ sk_B)
% 4.66/4.86          | (v2_struct_0 @ sk_A)
% 4.66/4.86          | ~ (l1_pre_topc @ sk_B)
% 4.66/4.86          | ~ (v2_pre_topc @ sk_B)
% 4.66/4.86          | (v2_struct_0 @ sk_B)
% 4.66/4.86          | (v1_funct_1 @ 
% 4.66/4.86             (k3_tmap_1 @ sk_B @ sk_A @ sk_B @ X0 @ (k4_tmap_1 @ sk_A @ sk_B))))),
% 4.66/4.86      inference('sup-', [status(thm)], ['113', '121'])).
% 4.66/4.86  thf('123', plain, ((l1_pre_topc @ sk_B)),
% 4.66/4.86      inference('demod', [status(thm)], ['34', '35'])).
% 4.66/4.86  thf('124', plain, ((l1_pre_topc @ sk_B)),
% 4.66/4.86      inference('demod', [status(thm)], ['34', '35'])).
% 4.66/4.86  thf('125', plain, ((v2_pre_topc @ sk_B)),
% 4.66/4.86      inference('demod', [status(thm)], ['39', '40', '41'])).
% 4.66/4.86  thf('126', plain,
% 4.66/4.86      (![X0 : $i]:
% 4.66/4.86         (~ (m1_pre_topc @ X0 @ sk_B)
% 4.66/4.86          | (v2_struct_0 @ sk_A)
% 4.66/4.86          | (v2_struct_0 @ sk_B)
% 4.66/4.86          | (v1_funct_1 @ 
% 4.66/4.86             (k3_tmap_1 @ sk_B @ sk_A @ sk_B @ X0 @ (k4_tmap_1 @ sk_A @ sk_B))))),
% 4.66/4.86      inference('demod', [status(thm)], ['122', '123', '124', '125'])).
% 4.66/4.86  thf('127', plain,
% 4.66/4.86      ((~ (l1_pre_topc @ sk_B)
% 4.66/4.86        | (v1_funct_1 @ 
% 4.66/4.86           (k3_tmap_1 @ sk_B @ sk_A @ sk_B @ sk_B @ (k4_tmap_1 @ sk_A @ sk_B)))
% 4.66/4.86        | (v2_struct_0 @ sk_B)
% 4.66/4.86        | (v2_struct_0 @ sk_A))),
% 4.66/4.86      inference('sup-', [status(thm)], ['112', '126'])).
% 4.66/4.86  thf('128', plain, ((l1_pre_topc @ sk_B)),
% 4.66/4.86      inference('demod', [status(thm)], ['34', '35'])).
% 4.66/4.86  thf('129', plain,
% 4.66/4.86      (((v1_funct_1 @ 
% 4.66/4.86         (k3_tmap_1 @ sk_B @ sk_A @ sk_B @ sk_B @ (k4_tmap_1 @ sk_A @ sk_B)))
% 4.66/4.86        | (v2_struct_0 @ sk_B)
% 4.66/4.86        | (v2_struct_0 @ sk_A))),
% 4.66/4.86      inference('demod', [status(thm)], ['127', '128'])).
% 4.66/4.86  thf('130', plain, (~ (v2_struct_0 @ sk_B)),
% 4.66/4.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.66/4.86  thf('131', plain,
% 4.66/4.86      (((v2_struct_0 @ sk_A)
% 4.66/4.86        | (v1_funct_1 @ 
% 4.66/4.86           (k3_tmap_1 @ sk_B @ sk_A @ sk_B @ sk_B @ (k4_tmap_1 @ sk_A @ sk_B))))),
% 4.66/4.86      inference('clc', [status(thm)], ['129', '130'])).
% 4.66/4.86  thf('132', plain, (~ (v2_struct_0 @ sk_A)),
% 4.66/4.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.66/4.86  thf('133', plain,
% 4.66/4.86      ((v1_funct_1 @ 
% 4.66/4.86        (k3_tmap_1 @ sk_B @ sk_A @ sk_B @ sk_B @ (k4_tmap_1 @ sk_A @ sk_B)))),
% 4.66/4.86      inference('clc', [status(thm)], ['131', '132'])).
% 4.66/4.86  thf('134', plain,
% 4.66/4.86      (((k3_tmap_1 @ sk_B @ sk_A @ sk_B @ sk_B @ (k4_tmap_1 @ sk_A @ sk_B))
% 4.66/4.86         = (k2_tmap_1 @ sk_B @ sk_A @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_B))),
% 4.66/4.86      inference('clc', [status(thm)], ['94', '95'])).
% 4.66/4.86  thf('135', plain,
% 4.66/4.86      ((v1_funct_1 @ 
% 4.66/4.86        (k2_tmap_1 @ sk_B @ sk_A @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_B))),
% 4.66/4.86      inference('demod', [status(thm)], ['133', '134'])).
% 4.66/4.86  thf('136', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 4.66/4.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.66/4.86  thf('137', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 4.66/4.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.66/4.86  thf('138', plain,
% 4.66/4.86      ((m1_subset_1 @ (k4_tmap_1 @ sk_A @ sk_B) @ 
% 4.66/4.86        (k1_zfmisc_1 @ 
% 4.66/4.86         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 4.66/4.86      inference('clc', [status(thm)], ['9', '10'])).
% 4.66/4.86  thf('139', plain,
% 4.66/4.86      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 4.66/4.86         (~ (m1_pre_topc @ X28 @ X29)
% 4.66/4.86          | ~ (m1_pre_topc @ X30 @ X29)
% 4.66/4.86          | ~ (l1_pre_topc @ X31)
% 4.66/4.86          | ~ (v2_pre_topc @ X31)
% 4.66/4.86          | (v2_struct_0 @ X31)
% 4.66/4.86          | ~ (l1_pre_topc @ X29)
% 4.66/4.86          | ~ (v2_pre_topc @ X29)
% 4.66/4.86          | (v2_struct_0 @ X29)
% 4.66/4.86          | ~ (v1_funct_1 @ X32)
% 4.66/4.86          | ~ (v1_funct_2 @ X32 @ (u1_struct_0 @ X30) @ (u1_struct_0 @ X31))
% 4.66/4.86          | ~ (m1_subset_1 @ X32 @ 
% 4.66/4.86               (k1_zfmisc_1 @ 
% 4.66/4.86                (k2_zfmisc_1 @ (u1_struct_0 @ X30) @ (u1_struct_0 @ X31))))
% 4.66/4.86          | (v1_funct_2 @ (k3_tmap_1 @ X29 @ X31 @ X30 @ X28 @ X32) @ 
% 4.66/4.86             (u1_struct_0 @ X28) @ (u1_struct_0 @ X31)))),
% 4.66/4.86      inference('cnf', [status(esa)], [dt_k3_tmap_1])).
% 4.66/4.86  thf('140', plain,
% 4.66/4.86      (![X0 : $i, X1 : $i]:
% 4.66/4.86         ((v1_funct_2 @ 
% 4.66/4.86           (k3_tmap_1 @ X1 @ sk_A @ sk_B @ X0 @ (k4_tmap_1 @ sk_A @ sk_B)) @ 
% 4.66/4.86           (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A))
% 4.66/4.86          | ~ (v1_funct_2 @ (k4_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_B) @ 
% 4.66/4.86               (u1_struct_0 @ sk_A))
% 4.66/4.86          | ~ (v1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_B))
% 4.66/4.86          | (v2_struct_0 @ X1)
% 4.66/4.86          | ~ (v2_pre_topc @ X1)
% 4.66/4.86          | ~ (l1_pre_topc @ X1)
% 4.66/4.86          | (v2_struct_0 @ sk_A)
% 4.66/4.86          | ~ (v2_pre_topc @ sk_A)
% 4.66/4.86          | ~ (l1_pre_topc @ sk_A)
% 4.66/4.86          | ~ (m1_pre_topc @ sk_B @ X1)
% 4.66/4.86          | ~ (m1_pre_topc @ X0 @ X1))),
% 4.66/4.86      inference('sup-', [status(thm)], ['138', '139'])).
% 4.66/4.86  thf('141', plain,
% 4.66/4.86      ((v1_funct_2 @ (k4_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_B) @ 
% 4.66/4.86        (u1_struct_0 @ sk_A))),
% 4.66/4.86      inference('clc', [status(thm)], ['21', '22'])).
% 4.66/4.86  thf('142', plain, ((v1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_B))),
% 4.66/4.86      inference('clc', [status(thm)], ['29', '30'])).
% 4.66/4.86  thf('143', plain, ((v2_pre_topc @ sk_A)),
% 4.66/4.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.66/4.86  thf('144', plain, ((l1_pre_topc @ sk_A)),
% 4.66/4.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.66/4.86  thf('145', plain,
% 4.66/4.86      (![X0 : $i, X1 : $i]:
% 4.66/4.86         ((v1_funct_2 @ 
% 4.66/4.86           (k3_tmap_1 @ X1 @ sk_A @ sk_B @ X0 @ (k4_tmap_1 @ sk_A @ sk_B)) @ 
% 4.66/4.86           (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A))
% 4.66/4.86          | (v2_struct_0 @ X1)
% 4.66/4.86          | ~ (v2_pre_topc @ X1)
% 4.66/4.86          | ~ (l1_pre_topc @ X1)
% 4.66/4.86          | (v2_struct_0 @ sk_A)
% 4.66/4.86          | ~ (m1_pre_topc @ sk_B @ X1)
% 4.66/4.86          | ~ (m1_pre_topc @ X0 @ X1))),
% 4.66/4.86      inference('demod', [status(thm)], ['140', '141', '142', '143', '144'])).
% 4.66/4.86  thf('146', plain,
% 4.66/4.86      (![X0 : $i]:
% 4.66/4.86         (~ (m1_pre_topc @ X0 @ sk_A)
% 4.66/4.86          | (v2_struct_0 @ sk_A)
% 4.66/4.86          | ~ (l1_pre_topc @ sk_A)
% 4.66/4.86          | ~ (v2_pre_topc @ sk_A)
% 4.66/4.86          | (v2_struct_0 @ sk_A)
% 4.66/4.86          | (v1_funct_2 @ 
% 4.66/4.86             (k3_tmap_1 @ sk_A @ sk_A @ sk_B @ X0 @ (k4_tmap_1 @ sk_A @ sk_B)) @ 
% 4.66/4.86             (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A)))),
% 4.66/4.86      inference('sup-', [status(thm)], ['137', '145'])).
% 4.66/4.86  thf('147', plain, ((l1_pre_topc @ sk_A)),
% 4.66/4.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.66/4.86  thf('148', plain, ((v2_pre_topc @ sk_A)),
% 4.66/4.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.66/4.86  thf('149', plain,
% 4.66/4.86      (![X0 : $i]:
% 4.66/4.86         (~ (m1_pre_topc @ X0 @ sk_A)
% 4.66/4.86          | (v2_struct_0 @ sk_A)
% 4.66/4.86          | (v2_struct_0 @ sk_A)
% 4.66/4.86          | (v1_funct_2 @ 
% 4.66/4.86             (k3_tmap_1 @ sk_A @ sk_A @ sk_B @ X0 @ (k4_tmap_1 @ sk_A @ sk_B)) @ 
% 4.66/4.86             (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A)))),
% 4.66/4.86      inference('demod', [status(thm)], ['146', '147', '148'])).
% 4.66/4.86  thf('150', plain,
% 4.66/4.86      (![X0 : $i]:
% 4.66/4.86         ((v1_funct_2 @ 
% 4.66/4.86           (k3_tmap_1 @ sk_A @ sk_A @ sk_B @ X0 @ (k4_tmap_1 @ sk_A @ sk_B)) @ 
% 4.66/4.86           (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A))
% 4.66/4.86          | (v2_struct_0 @ sk_A)
% 4.66/4.86          | ~ (m1_pre_topc @ X0 @ sk_A))),
% 4.66/4.86      inference('simplify', [status(thm)], ['149'])).
% 4.66/4.86  thf('151', plain, (~ (v2_struct_0 @ sk_A)),
% 4.66/4.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.66/4.86  thf('152', plain,
% 4.66/4.86      (![X0 : $i]:
% 4.66/4.86         (~ (m1_pre_topc @ X0 @ sk_A)
% 4.66/4.86          | (v1_funct_2 @ 
% 4.66/4.86             (k3_tmap_1 @ sk_A @ sk_A @ sk_B @ X0 @ (k4_tmap_1 @ sk_A @ sk_B)) @ 
% 4.66/4.86             (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A)))),
% 4.66/4.86      inference('clc', [status(thm)], ['150', '151'])).
% 4.66/4.86  thf('153', plain,
% 4.66/4.86      ((v1_funct_2 @ 
% 4.66/4.86        (k3_tmap_1 @ sk_A @ sk_A @ sk_B @ sk_B @ (k4_tmap_1 @ sk_A @ sk_B)) @ 
% 4.66/4.86        (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 4.66/4.86      inference('sup-', [status(thm)], ['136', '152'])).
% 4.66/4.86  thf('154', plain,
% 4.66/4.86      (![X37 : $i]: ((m1_pre_topc @ X37 @ X37) | ~ (l1_pre_topc @ X37))),
% 4.66/4.86      inference('cnf', [status(esa)], [t2_tsep_1])).
% 4.66/4.86  thf('155', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 4.66/4.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.66/4.86  thf('156', plain,
% 4.66/4.86      (![X0 : $i, X1 : $i]:
% 4.66/4.86         ((v2_struct_0 @ X0)
% 4.66/4.86          | ~ (v2_pre_topc @ X0)
% 4.66/4.86          | ~ (l1_pre_topc @ X0)
% 4.66/4.86          | ~ (m1_pre_topc @ sk_B @ X0)
% 4.66/4.86          | ((k3_tmap_1 @ X0 @ sk_A @ sk_B @ X1 @ (k4_tmap_1 @ sk_A @ sk_B))
% 4.66/4.86              = (k2_partfun1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 4.66/4.86                 (k4_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ X1)))
% 4.66/4.86          | ~ (m1_pre_topc @ X1 @ sk_B)
% 4.66/4.86          | ~ (m1_pre_topc @ X1 @ X0)
% 4.66/4.86          | (v2_struct_0 @ sk_A))),
% 4.66/4.86      inference('demod', [status(thm)], ['60', '61', '62', '63', '64'])).
% 4.66/4.86  thf('157', plain,
% 4.66/4.86      (![X0 : $i]:
% 4.66/4.86         ((v2_struct_0 @ sk_A)
% 4.66/4.86          | ~ (m1_pre_topc @ X0 @ sk_A)
% 4.66/4.86          | ~ (m1_pre_topc @ X0 @ sk_B)
% 4.66/4.86          | ((k3_tmap_1 @ sk_A @ sk_A @ sk_B @ X0 @ (k4_tmap_1 @ sk_A @ sk_B))
% 4.66/4.86              = (k2_partfun1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 4.66/4.86                 (k4_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ X0)))
% 4.66/4.86          | ~ (l1_pre_topc @ sk_A)
% 4.66/4.86          | ~ (v2_pre_topc @ sk_A)
% 4.66/4.86          | (v2_struct_0 @ sk_A))),
% 4.66/4.86      inference('sup-', [status(thm)], ['155', '156'])).
% 4.66/4.86  thf('158', plain, ((l1_pre_topc @ sk_A)),
% 4.66/4.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.66/4.86  thf('159', plain, ((v2_pre_topc @ sk_A)),
% 4.66/4.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.66/4.86  thf('160', plain,
% 4.66/4.86      (![X0 : $i]:
% 4.66/4.86         ((v2_struct_0 @ sk_A)
% 4.66/4.86          | ~ (m1_pre_topc @ X0 @ sk_A)
% 4.66/4.86          | ~ (m1_pre_topc @ X0 @ sk_B)
% 4.66/4.86          | ((k3_tmap_1 @ sk_A @ sk_A @ sk_B @ X0 @ (k4_tmap_1 @ sk_A @ sk_B))
% 4.66/4.86              = (k2_partfun1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 4.66/4.86                 (k4_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ X0)))
% 4.66/4.86          | (v2_struct_0 @ sk_A))),
% 4.66/4.86      inference('demod', [status(thm)], ['157', '158', '159'])).
% 4.66/4.86  thf('161', plain,
% 4.66/4.86      (![X0 : $i]:
% 4.66/4.86         (((k3_tmap_1 @ sk_A @ sk_A @ sk_B @ X0 @ (k4_tmap_1 @ sk_A @ sk_B))
% 4.66/4.86            = (k2_partfun1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 4.66/4.86               (k4_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ X0)))
% 4.66/4.86          | ~ (m1_pre_topc @ X0 @ sk_B)
% 4.66/4.86          | ~ (m1_pre_topc @ X0 @ sk_A)
% 4.66/4.86          | (v2_struct_0 @ sk_A))),
% 4.66/4.86      inference('simplify', [status(thm)], ['160'])).
% 4.66/4.86  thf('162', plain,
% 4.66/4.86      ((~ (l1_pre_topc @ sk_B)
% 4.66/4.86        | (v2_struct_0 @ sk_A)
% 4.66/4.86        | ~ (m1_pre_topc @ sk_B @ sk_A)
% 4.66/4.86        | ((k3_tmap_1 @ sk_A @ sk_A @ sk_B @ sk_B @ (k4_tmap_1 @ sk_A @ sk_B))
% 4.66/4.86            = (k2_partfun1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 4.66/4.86               (k4_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_B))))),
% 4.66/4.86      inference('sup-', [status(thm)], ['154', '161'])).
% 4.66/4.86  thf('163', plain, ((l1_pre_topc @ sk_B)),
% 4.66/4.86      inference('demod', [status(thm)], ['34', '35'])).
% 4.66/4.86  thf('164', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 4.66/4.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.66/4.86  thf('165', plain,
% 4.66/4.86      (((k2_tmap_1 @ sk_B @ sk_A @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_B)
% 4.66/4.86         = (k2_partfun1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 4.66/4.86            (k4_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_B)))),
% 4.66/4.86      inference('clc', [status(thm)], ['89', '90'])).
% 4.66/4.86  thf('166', plain,
% 4.66/4.86      (((v2_struct_0 @ sk_A)
% 4.66/4.86        | ((k3_tmap_1 @ sk_A @ sk_A @ sk_B @ sk_B @ (k4_tmap_1 @ sk_A @ sk_B))
% 4.66/4.86            = (k2_tmap_1 @ sk_B @ sk_A @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_B)))),
% 4.66/4.86      inference('demod', [status(thm)], ['162', '163', '164', '165'])).
% 4.66/4.86  thf('167', plain, (~ (v2_struct_0 @ sk_A)),
% 4.66/4.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.66/4.86  thf('168', plain,
% 4.66/4.86      (((k3_tmap_1 @ sk_A @ sk_A @ sk_B @ sk_B @ (k4_tmap_1 @ sk_A @ sk_B))
% 4.66/4.86         = (k2_tmap_1 @ sk_B @ sk_A @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_B))),
% 4.66/4.86      inference('clc', [status(thm)], ['166', '167'])).
% 4.66/4.86  thf('169', plain,
% 4.66/4.86      ((v1_funct_2 @ 
% 4.66/4.86        (k2_tmap_1 @ sk_B @ sk_A @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_B) @ 
% 4.66/4.86        (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 4.66/4.86      inference('demod', [status(thm)], ['153', '168'])).
% 4.66/4.86  thf('170', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 4.66/4.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.66/4.86  thf('171', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 4.66/4.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.66/4.86  thf('172', plain,
% 4.66/4.86      ((m1_subset_1 @ (k4_tmap_1 @ sk_A @ sk_B) @ 
% 4.66/4.86        (k1_zfmisc_1 @ 
% 4.66/4.86         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 4.66/4.86      inference('clc', [status(thm)], ['9', '10'])).
% 4.66/4.86  thf('173', plain,
% 4.66/4.86      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 4.66/4.86         (~ (m1_pre_topc @ X28 @ X29)
% 4.66/4.86          | ~ (m1_pre_topc @ X30 @ X29)
% 4.66/4.86          | ~ (l1_pre_topc @ X31)
% 4.66/4.86          | ~ (v2_pre_topc @ X31)
% 4.66/4.86          | (v2_struct_0 @ X31)
% 4.66/4.86          | ~ (l1_pre_topc @ X29)
% 4.66/4.86          | ~ (v2_pre_topc @ X29)
% 4.66/4.86          | (v2_struct_0 @ X29)
% 4.66/4.86          | ~ (v1_funct_1 @ X32)
% 4.66/4.86          | ~ (v1_funct_2 @ X32 @ (u1_struct_0 @ X30) @ (u1_struct_0 @ X31))
% 4.66/4.86          | ~ (m1_subset_1 @ X32 @ 
% 4.66/4.86               (k1_zfmisc_1 @ 
% 4.66/4.86                (k2_zfmisc_1 @ (u1_struct_0 @ X30) @ (u1_struct_0 @ X31))))
% 4.66/4.86          | (m1_subset_1 @ (k3_tmap_1 @ X29 @ X31 @ X30 @ X28 @ X32) @ 
% 4.66/4.86             (k1_zfmisc_1 @ 
% 4.66/4.86              (k2_zfmisc_1 @ (u1_struct_0 @ X28) @ (u1_struct_0 @ X31)))))),
% 4.66/4.86      inference('cnf', [status(esa)], [dt_k3_tmap_1])).
% 4.66/4.86  thf('174', plain,
% 4.66/4.86      (![X0 : $i, X1 : $i]:
% 4.66/4.86         ((m1_subset_1 @ 
% 4.66/4.86           (k3_tmap_1 @ X1 @ sk_A @ sk_B @ X0 @ (k4_tmap_1 @ sk_A @ sk_B)) @ 
% 4.66/4.86           (k1_zfmisc_1 @ 
% 4.66/4.86            (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A))))
% 4.66/4.86          | ~ (v1_funct_2 @ (k4_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_B) @ 
% 4.66/4.86               (u1_struct_0 @ sk_A))
% 4.66/4.86          | ~ (v1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_B))
% 4.66/4.86          | (v2_struct_0 @ X1)
% 4.66/4.86          | ~ (v2_pre_topc @ X1)
% 4.66/4.86          | ~ (l1_pre_topc @ X1)
% 4.66/4.86          | (v2_struct_0 @ sk_A)
% 4.66/4.86          | ~ (v2_pre_topc @ sk_A)
% 4.66/4.86          | ~ (l1_pre_topc @ sk_A)
% 4.66/4.86          | ~ (m1_pre_topc @ sk_B @ X1)
% 4.66/4.86          | ~ (m1_pre_topc @ X0 @ X1))),
% 4.66/4.86      inference('sup-', [status(thm)], ['172', '173'])).
% 4.66/4.86  thf('175', plain,
% 4.66/4.86      ((v1_funct_2 @ (k4_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_B) @ 
% 4.66/4.86        (u1_struct_0 @ sk_A))),
% 4.66/4.86      inference('clc', [status(thm)], ['21', '22'])).
% 4.66/4.86  thf('176', plain, ((v1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_B))),
% 4.66/4.86      inference('clc', [status(thm)], ['29', '30'])).
% 4.66/4.86  thf('177', plain, ((v2_pre_topc @ sk_A)),
% 4.66/4.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.66/4.86  thf('178', plain, ((l1_pre_topc @ sk_A)),
% 4.66/4.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.66/4.86  thf('179', plain,
% 4.66/4.86      (![X0 : $i, X1 : $i]:
% 4.66/4.86         ((m1_subset_1 @ 
% 4.66/4.86           (k3_tmap_1 @ X1 @ sk_A @ sk_B @ X0 @ (k4_tmap_1 @ sk_A @ sk_B)) @ 
% 4.66/4.86           (k1_zfmisc_1 @ 
% 4.66/4.86            (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A))))
% 4.66/4.86          | (v2_struct_0 @ X1)
% 4.66/4.86          | ~ (v2_pre_topc @ X1)
% 4.66/4.86          | ~ (l1_pre_topc @ X1)
% 4.66/4.86          | (v2_struct_0 @ sk_A)
% 4.66/4.86          | ~ (m1_pre_topc @ sk_B @ X1)
% 4.66/4.86          | ~ (m1_pre_topc @ X0 @ X1))),
% 4.66/4.86      inference('demod', [status(thm)], ['174', '175', '176', '177', '178'])).
% 4.66/4.86  thf('180', plain,
% 4.66/4.86      (![X0 : $i]:
% 4.66/4.86         (~ (m1_pre_topc @ X0 @ sk_A)
% 4.66/4.86          | (v2_struct_0 @ sk_A)
% 4.66/4.86          | ~ (l1_pre_topc @ sk_A)
% 4.66/4.86          | ~ (v2_pre_topc @ sk_A)
% 4.66/4.86          | (v2_struct_0 @ sk_A)
% 4.66/4.86          | (m1_subset_1 @ 
% 4.66/4.86             (k3_tmap_1 @ sk_A @ sk_A @ sk_B @ X0 @ (k4_tmap_1 @ sk_A @ sk_B)) @ 
% 4.66/4.86             (k1_zfmisc_1 @ 
% 4.66/4.86              (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A)))))),
% 4.66/4.86      inference('sup-', [status(thm)], ['171', '179'])).
% 4.66/4.86  thf('181', plain, ((l1_pre_topc @ sk_A)),
% 4.66/4.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.66/4.86  thf('182', plain, ((v2_pre_topc @ sk_A)),
% 4.66/4.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.66/4.86  thf('183', plain,
% 4.66/4.86      (![X0 : $i]:
% 4.66/4.86         (~ (m1_pre_topc @ X0 @ sk_A)
% 4.66/4.86          | (v2_struct_0 @ sk_A)
% 4.66/4.86          | (v2_struct_0 @ sk_A)
% 4.66/4.86          | (m1_subset_1 @ 
% 4.66/4.86             (k3_tmap_1 @ sk_A @ sk_A @ sk_B @ X0 @ (k4_tmap_1 @ sk_A @ sk_B)) @ 
% 4.66/4.86             (k1_zfmisc_1 @ 
% 4.66/4.86              (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A)))))),
% 4.66/4.86      inference('demod', [status(thm)], ['180', '181', '182'])).
% 4.66/4.86  thf('184', plain,
% 4.66/4.86      (![X0 : $i]:
% 4.66/4.86         ((m1_subset_1 @ 
% 4.66/4.86           (k3_tmap_1 @ sk_A @ sk_A @ sk_B @ X0 @ (k4_tmap_1 @ sk_A @ sk_B)) @ 
% 4.66/4.86           (k1_zfmisc_1 @ 
% 4.66/4.86            (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A))))
% 4.66/4.86          | (v2_struct_0 @ sk_A)
% 4.66/4.86          | ~ (m1_pre_topc @ X0 @ sk_A))),
% 4.66/4.86      inference('simplify', [status(thm)], ['183'])).
% 4.66/4.86  thf('185', plain, (~ (v2_struct_0 @ sk_A)),
% 4.66/4.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.66/4.86  thf('186', plain,
% 4.66/4.86      (![X0 : $i]:
% 4.66/4.86         (~ (m1_pre_topc @ X0 @ sk_A)
% 4.66/4.86          | (m1_subset_1 @ 
% 4.66/4.86             (k3_tmap_1 @ sk_A @ sk_A @ sk_B @ X0 @ (k4_tmap_1 @ sk_A @ sk_B)) @ 
% 4.66/4.86             (k1_zfmisc_1 @ 
% 4.66/4.86              (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A)))))),
% 4.66/4.86      inference('clc', [status(thm)], ['184', '185'])).
% 4.66/4.86  thf('187', plain,
% 4.66/4.86      ((m1_subset_1 @ 
% 4.66/4.86        (k3_tmap_1 @ sk_A @ sk_A @ sk_B @ sk_B @ (k4_tmap_1 @ sk_A @ sk_B)) @ 
% 4.66/4.86        (k1_zfmisc_1 @ 
% 4.66/4.86         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 4.66/4.86      inference('sup-', [status(thm)], ['170', '186'])).
% 4.66/4.86  thf('188', plain,
% 4.66/4.86      (((k3_tmap_1 @ sk_A @ sk_A @ sk_B @ sk_B @ (k4_tmap_1 @ sk_A @ sk_B))
% 4.66/4.86         = (k2_tmap_1 @ sk_B @ sk_A @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_B))),
% 4.66/4.86      inference('clc', [status(thm)], ['166', '167'])).
% 4.66/4.86  thf('189', plain,
% 4.66/4.86      ((m1_subset_1 @ 
% 4.66/4.86        (k2_tmap_1 @ sk_B @ sk_A @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_B) @ 
% 4.66/4.86        (k1_zfmisc_1 @ 
% 4.66/4.86         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 4.66/4.86      inference('demod', [status(thm)], ['187', '188'])).
% 4.66/4.86  thf('190', plain,
% 4.66/4.86      (((k4_tmap_1 @ sk_A @ sk_B)
% 4.66/4.86         = (k2_tmap_1 @ sk_B @ sk_A @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_B))),
% 4.66/4.86      inference('demod', [status(thm)], ['111', '135', '169', '189'])).
% 4.66/4.86  thf('191', plain,
% 4.66/4.86      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 4.66/4.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.66/4.86  thf('192', plain, ((v1_funct_1 @ sk_C)),
% 4.66/4.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.66/4.86  thf('193', plain,
% 4.66/4.86      (((v2_struct_0 @ sk_B)
% 4.66/4.86        | (r2_hidden @ 
% 4.66/4.86           (sk_F @ sk_C @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_B @ sk_B @ sk_A) @ 
% 4.66/4.86           (u1_struct_0 @ sk_B))
% 4.66/4.86        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 4.66/4.86           (k4_tmap_1 @ sk_A @ sk_B) @ sk_C)
% 4.66/4.86        | ~ (m1_pre_topc @ sk_B @ sk_B)
% 4.66/4.86        | (v2_struct_0 @ sk_B)
% 4.66/4.86        | (v2_struct_0 @ sk_A))),
% 4.66/4.86      inference('demod', [status(thm)], ['44', '190', '191', '192'])).
% 4.66/4.86  thf('194', plain,
% 4.66/4.86      (((v2_struct_0 @ sk_A)
% 4.66/4.86        | ~ (m1_pre_topc @ sk_B @ sk_B)
% 4.66/4.86        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 4.66/4.86           (k4_tmap_1 @ sk_A @ sk_B) @ sk_C)
% 4.66/4.86        | (r2_hidden @ 
% 4.66/4.86           (sk_F @ sk_C @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_B @ sk_B @ sk_A) @ 
% 4.66/4.86           (u1_struct_0 @ sk_B))
% 4.66/4.86        | (v2_struct_0 @ sk_B))),
% 4.66/4.86      inference('simplify', [status(thm)], ['193'])).
% 4.66/4.86  thf('195', plain,
% 4.66/4.86      ((~ (l1_pre_topc @ sk_B)
% 4.66/4.86        | (v2_struct_0 @ sk_B)
% 4.66/4.86        | (r2_hidden @ 
% 4.66/4.86           (sk_F @ sk_C @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_B @ sk_B @ sk_A) @ 
% 4.66/4.86           (u1_struct_0 @ sk_B))
% 4.66/4.86        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 4.66/4.86           (k4_tmap_1 @ sk_A @ sk_B) @ sk_C)
% 4.66/4.86        | (v2_struct_0 @ sk_A))),
% 4.66/4.86      inference('sup-', [status(thm)], ['2', '194'])).
% 4.66/4.86  thf('196', plain, ((l1_pre_topc @ sk_B)),
% 4.66/4.86      inference('demod', [status(thm)], ['34', '35'])).
% 4.66/4.86  thf('197', plain,
% 4.66/4.86      (((v2_struct_0 @ sk_B)
% 4.66/4.86        | (r2_hidden @ 
% 4.66/4.86           (sk_F @ sk_C @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_B @ sk_B @ sk_A) @ 
% 4.66/4.86           (u1_struct_0 @ sk_B))
% 4.66/4.86        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 4.66/4.86           (k4_tmap_1 @ sk_A @ sk_B) @ sk_C)
% 4.66/4.86        | (v2_struct_0 @ sk_A))),
% 4.66/4.86      inference('demod', [status(thm)], ['195', '196'])).
% 4.66/4.86  thf('198', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 4.66/4.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.66/4.86  thf(t1_tsep_1, axiom,
% 4.66/4.86    (![A:$i]:
% 4.66/4.86     ( ( l1_pre_topc @ A ) =>
% 4.66/4.86       ( ![B:$i]:
% 4.66/4.86         ( ( m1_pre_topc @ B @ A ) =>
% 4.66/4.86           ( m1_subset_1 @
% 4.66/4.86             ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 4.66/4.86  thf('199', plain,
% 4.66/4.86      (![X35 : $i, X36 : $i]:
% 4.66/4.86         (~ (m1_pre_topc @ X35 @ X36)
% 4.66/4.86          | (m1_subset_1 @ (u1_struct_0 @ X35) @ 
% 4.66/4.86             (k1_zfmisc_1 @ (u1_struct_0 @ X36)))
% 4.66/4.86          | ~ (l1_pre_topc @ X36))),
% 4.66/4.86      inference('cnf', [status(esa)], [t1_tsep_1])).
% 4.66/4.86  thf('200', plain,
% 4.66/4.86      ((~ (l1_pre_topc @ sk_A)
% 4.66/4.86        | (m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 4.66/4.86           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 4.66/4.86      inference('sup-', [status(thm)], ['198', '199'])).
% 4.66/4.86  thf('201', plain, ((l1_pre_topc @ sk_A)),
% 4.66/4.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.66/4.86  thf('202', plain,
% 4.66/4.86      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 4.66/4.86        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 4.66/4.86      inference('demod', [status(thm)], ['200', '201'])).
% 4.66/4.86  thf(t4_subset, axiom,
% 4.66/4.86    (![A:$i,B:$i,C:$i]:
% 4.66/4.86     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 4.66/4.86       ( m1_subset_1 @ A @ C ) ))).
% 4.66/4.86  thf('203', plain,
% 4.66/4.86      (![X2 : $i, X3 : $i, X4 : $i]:
% 4.66/4.86         (~ (r2_hidden @ X2 @ X3)
% 4.66/4.86          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 4.66/4.86          | (m1_subset_1 @ X2 @ X4))),
% 4.66/4.86      inference('cnf', [status(esa)], [t4_subset])).
% 4.66/4.86  thf('204', plain,
% 4.66/4.86      (![X0 : $i]:
% 4.66/4.86         ((m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 4.66/4.86          | ~ (r2_hidden @ X0 @ (u1_struct_0 @ sk_B)))),
% 4.66/4.86      inference('sup-', [status(thm)], ['202', '203'])).
% 4.66/4.86  thf('205', plain,
% 4.66/4.86      (((v2_struct_0 @ sk_A)
% 4.66/4.86        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 4.66/4.86           (k4_tmap_1 @ sk_A @ sk_B) @ sk_C)
% 4.66/4.86        | (v2_struct_0 @ sk_B)
% 4.66/4.86        | (m1_subset_1 @ 
% 4.66/4.86           (sk_F @ sk_C @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_B @ sk_B @ sk_A) @ 
% 4.66/4.86           (u1_struct_0 @ sk_A)))),
% 4.66/4.86      inference('sup-', [status(thm)], ['197', '204'])).
% 4.66/4.86  thf('206', plain,
% 4.66/4.86      (((v2_struct_0 @ sk_B)
% 4.66/4.86        | (r2_hidden @ 
% 4.66/4.86           (sk_F @ sk_C @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_B @ sk_B @ sk_A) @ 
% 4.66/4.86           (u1_struct_0 @ sk_B))
% 4.66/4.86        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 4.66/4.86           (k4_tmap_1 @ sk_A @ sk_B) @ sk_C)
% 4.66/4.86        | (v2_struct_0 @ sk_A))),
% 4.66/4.86      inference('demod', [status(thm)], ['195', '196'])).
% 4.66/4.86  thf('207', plain,
% 4.66/4.86      (![X53 : $i]:
% 4.66/4.86         (~ (r2_hidden @ X53 @ (u1_struct_0 @ sk_B))
% 4.66/4.86          | ((X53) = (k1_funct_1 @ sk_C @ X53))
% 4.66/4.86          | ~ (m1_subset_1 @ X53 @ (u1_struct_0 @ sk_A)))),
% 4.66/4.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.66/4.86  thf('208', plain,
% 4.66/4.86      (((v2_struct_0 @ sk_A)
% 4.66/4.86        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 4.66/4.86           (k4_tmap_1 @ sk_A @ sk_B) @ sk_C)
% 4.66/4.86        | (v2_struct_0 @ sk_B)
% 4.66/4.86        | ~ (m1_subset_1 @ 
% 4.66/4.86             (sk_F @ sk_C @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_B @ sk_B @ sk_A) @ 
% 4.66/4.86             (u1_struct_0 @ sk_A))
% 4.66/4.86        | ((sk_F @ sk_C @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_B @ sk_B @ sk_A)
% 4.66/4.86            = (k1_funct_1 @ sk_C @ 
% 4.66/4.86               (sk_F @ sk_C @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_B @ sk_B @ sk_A))))),
% 4.66/4.86      inference('sup-', [status(thm)], ['206', '207'])).
% 4.66/4.86  thf('209', plain,
% 4.66/4.86      (((v2_struct_0 @ sk_B)
% 4.66/4.86        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 4.66/4.86           (k4_tmap_1 @ sk_A @ sk_B) @ sk_C)
% 4.66/4.86        | (v2_struct_0 @ sk_A)
% 4.66/4.86        | ((sk_F @ sk_C @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_B @ sk_B @ sk_A)
% 4.66/4.86            = (k1_funct_1 @ sk_C @ 
% 4.66/4.86               (sk_F @ sk_C @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_B @ sk_B @ sk_A)))
% 4.66/4.86        | (v2_struct_0 @ sk_B)
% 4.66/4.86        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 4.66/4.86           (k4_tmap_1 @ sk_A @ sk_B) @ sk_C)
% 4.66/4.86        | (v2_struct_0 @ sk_A))),
% 4.66/4.86      inference('sup-', [status(thm)], ['205', '208'])).
% 4.66/4.86  thf('210', plain,
% 4.66/4.86      ((((sk_F @ sk_C @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_B @ sk_B @ sk_A)
% 4.66/4.86          = (k1_funct_1 @ sk_C @ 
% 4.66/4.86             (sk_F @ sk_C @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_B @ sk_B @ sk_A)))
% 4.66/4.86        | (v2_struct_0 @ sk_A)
% 4.66/4.86        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 4.66/4.86           (k4_tmap_1 @ sk_A @ sk_B) @ sk_C)
% 4.66/4.86        | (v2_struct_0 @ sk_B))),
% 4.66/4.86      inference('simplify', [status(thm)], ['209'])).
% 4.66/4.86  thf('211', plain,
% 4.66/4.86      (((v2_struct_0 @ sk_A)
% 4.66/4.86        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 4.66/4.86           (k4_tmap_1 @ sk_A @ sk_B) @ sk_C)
% 4.66/4.86        | (v2_struct_0 @ sk_B)
% 4.66/4.86        | (m1_subset_1 @ 
% 4.66/4.86           (sk_F @ sk_C @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_B @ sk_B @ sk_A) @ 
% 4.66/4.86           (u1_struct_0 @ sk_A)))),
% 4.66/4.86      inference('sup-', [status(thm)], ['197', '204'])).
% 4.66/4.86  thf('212', plain,
% 4.66/4.86      (((v2_struct_0 @ sk_B)
% 4.66/4.86        | (r2_hidden @ 
% 4.66/4.86           (sk_F @ sk_C @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_B @ sk_B @ sk_A) @ 
% 4.66/4.86           (u1_struct_0 @ sk_B))
% 4.66/4.86        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 4.66/4.86           (k4_tmap_1 @ sk_A @ sk_B) @ sk_C)
% 4.66/4.86        | (v2_struct_0 @ sk_A))),
% 4.66/4.86      inference('demod', [status(thm)], ['195', '196'])).
% 4.66/4.86  thf(t95_tmap_1, axiom,
% 4.66/4.86    (![A:$i]:
% 4.66/4.86     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 4.66/4.86       ( ![B:$i]:
% 4.66/4.86         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 4.66/4.86           ( ![C:$i]:
% 4.66/4.86             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 4.66/4.86               ( ( r2_hidden @ C @ ( u1_struct_0 @ B ) ) =>
% 4.66/4.86                 ( ( k1_funct_1 @ ( k4_tmap_1 @ A @ B ) @ C ) = ( C ) ) ) ) ) ) ) ))).
% 4.66/4.86  thf('213', plain,
% 4.66/4.86      (![X50 : $i, X51 : $i, X52 : $i]:
% 4.66/4.86         ((v2_struct_0 @ X50)
% 4.66/4.86          | ~ (m1_pre_topc @ X50 @ X51)
% 4.66/4.86          | ~ (r2_hidden @ X52 @ (u1_struct_0 @ X50))
% 4.66/4.86          | ((k1_funct_1 @ (k4_tmap_1 @ X51 @ X50) @ X52) = (X52))
% 4.66/4.86          | ~ (m1_subset_1 @ X52 @ (u1_struct_0 @ X51))
% 4.66/4.86          | ~ (l1_pre_topc @ X51)
% 4.66/4.86          | ~ (v2_pre_topc @ X51)
% 4.66/4.86          | (v2_struct_0 @ X51))),
% 4.66/4.86      inference('cnf', [status(esa)], [t95_tmap_1])).
% 4.66/4.86  thf('214', plain,
% 4.66/4.86      (![X0 : $i]:
% 4.66/4.86         ((v2_struct_0 @ sk_A)
% 4.66/4.86          | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 4.66/4.86             (k4_tmap_1 @ sk_A @ sk_B) @ sk_C)
% 4.66/4.86          | (v2_struct_0 @ sk_B)
% 4.66/4.86          | (v2_struct_0 @ X0)
% 4.66/4.86          | ~ (v2_pre_topc @ X0)
% 4.66/4.86          | ~ (l1_pre_topc @ X0)
% 4.66/4.86          | ~ (m1_subset_1 @ 
% 4.66/4.86               (sk_F @ sk_C @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_B @ sk_B @ sk_A) @ 
% 4.66/4.86               (u1_struct_0 @ X0))
% 4.66/4.86          | ((k1_funct_1 @ (k4_tmap_1 @ X0 @ sk_B) @ 
% 4.66/4.86              (sk_F @ sk_C @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_B @ sk_B @ sk_A))
% 4.66/4.86              = (sk_F @ sk_C @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_B @ sk_B @ sk_A))
% 4.66/4.86          | ~ (m1_pre_topc @ sk_B @ X0)
% 4.66/4.86          | (v2_struct_0 @ sk_B))),
% 4.66/4.86      inference('sup-', [status(thm)], ['212', '213'])).
% 4.66/4.86  thf('215', plain,
% 4.66/4.86      (![X0 : $i]:
% 4.66/4.86         (~ (m1_pre_topc @ sk_B @ X0)
% 4.66/4.86          | ((k1_funct_1 @ (k4_tmap_1 @ X0 @ sk_B) @ 
% 4.66/4.86              (sk_F @ sk_C @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_B @ sk_B @ sk_A))
% 4.66/4.86              = (sk_F @ sk_C @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_B @ sk_B @ sk_A))
% 4.66/4.86          | ~ (m1_subset_1 @ 
% 4.66/4.86               (sk_F @ sk_C @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_B @ sk_B @ sk_A) @ 
% 4.66/4.86               (u1_struct_0 @ X0))
% 4.66/4.86          | ~ (l1_pre_topc @ X0)
% 4.66/4.86          | ~ (v2_pre_topc @ X0)
% 4.66/4.86          | (v2_struct_0 @ X0)
% 4.66/4.86          | (v2_struct_0 @ sk_B)
% 4.66/4.86          | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 4.66/4.86             (k4_tmap_1 @ sk_A @ sk_B) @ sk_C)
% 4.66/4.86          | (v2_struct_0 @ sk_A))),
% 4.66/4.86      inference('simplify', [status(thm)], ['214'])).
% 4.66/4.86  thf('216', plain,
% 4.66/4.86      (((v2_struct_0 @ sk_B)
% 4.66/4.86        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 4.66/4.86           (k4_tmap_1 @ sk_A @ sk_B) @ sk_C)
% 4.66/4.86        | (v2_struct_0 @ sk_A)
% 4.66/4.86        | (v2_struct_0 @ sk_A)
% 4.66/4.86        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 4.66/4.86           (k4_tmap_1 @ sk_A @ sk_B) @ sk_C)
% 4.66/4.86        | (v2_struct_0 @ sk_B)
% 4.66/4.86        | (v2_struct_0 @ sk_A)
% 4.66/4.86        | ~ (v2_pre_topc @ sk_A)
% 4.66/4.86        | ~ (l1_pre_topc @ sk_A)
% 4.66/4.86        | ((k1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_B) @ 
% 4.66/4.86            (sk_F @ sk_C @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_B @ sk_B @ sk_A))
% 4.66/4.86            = (sk_F @ sk_C @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_B @ sk_B @ sk_A))
% 4.66/4.86        | ~ (m1_pre_topc @ sk_B @ sk_A))),
% 4.66/4.86      inference('sup-', [status(thm)], ['211', '215'])).
% 4.66/4.86  thf('217', plain, ((v2_pre_topc @ sk_A)),
% 4.66/4.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.66/4.86  thf('218', plain, ((l1_pre_topc @ sk_A)),
% 4.66/4.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.66/4.86  thf('219', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 4.66/4.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.66/4.86  thf('220', plain,
% 4.66/4.86      (((v2_struct_0 @ sk_B)
% 4.66/4.86        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 4.66/4.86           (k4_tmap_1 @ sk_A @ sk_B) @ sk_C)
% 4.66/4.86        | (v2_struct_0 @ sk_A)
% 4.66/4.86        | (v2_struct_0 @ sk_A)
% 4.66/4.86        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 4.66/4.86           (k4_tmap_1 @ sk_A @ sk_B) @ sk_C)
% 4.66/4.86        | (v2_struct_0 @ sk_B)
% 4.66/4.86        | (v2_struct_0 @ sk_A)
% 4.66/4.86        | ((k1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_B) @ 
% 4.66/4.86            (sk_F @ sk_C @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_B @ sk_B @ sk_A))
% 4.66/4.86            = (sk_F @ sk_C @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_B @ sk_B @ sk_A)))),
% 4.66/4.86      inference('demod', [status(thm)], ['216', '217', '218', '219'])).
% 4.66/4.86  thf('221', plain,
% 4.66/4.86      ((((k1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_B) @ 
% 4.66/4.86          (sk_F @ sk_C @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_B @ sk_B @ sk_A))
% 4.66/4.86          = (sk_F @ sk_C @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_B @ sk_B @ sk_A))
% 4.66/4.86        | (v2_struct_0 @ sk_A)
% 4.66/4.86        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 4.66/4.86           (k4_tmap_1 @ sk_A @ sk_B) @ sk_C)
% 4.66/4.86        | (v2_struct_0 @ sk_B))),
% 4.66/4.86      inference('simplify', [status(thm)], ['220'])).
% 4.66/4.86  thf('222', plain,
% 4.66/4.86      (((v2_struct_0 @ sk_B)
% 4.66/4.86        | (r2_hidden @ 
% 4.66/4.86           (sk_F @ sk_C @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_B @ sk_B @ sk_A) @ 
% 4.66/4.86           (u1_struct_0 @ sk_B))
% 4.66/4.86        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 4.66/4.86           (k4_tmap_1 @ sk_A @ sk_B) @ sk_C)
% 4.66/4.86        | (v2_struct_0 @ sk_A))),
% 4.66/4.86      inference('demod', [status(thm)], ['195', '196'])).
% 4.66/4.86  thf('223', plain,
% 4.66/4.86      (![X37 : $i]: ((m1_pre_topc @ X37 @ X37) | ~ (l1_pre_topc @ X37))),
% 4.66/4.86      inference('cnf', [status(esa)], [t2_tsep_1])).
% 4.66/4.86  thf('224', plain,
% 4.66/4.86      (![X35 : $i, X36 : $i]:
% 4.66/4.86         (~ (m1_pre_topc @ X35 @ X36)
% 4.66/4.86          | (m1_subset_1 @ (u1_struct_0 @ X35) @ 
% 4.66/4.86             (k1_zfmisc_1 @ (u1_struct_0 @ X36)))
% 4.66/4.86          | ~ (l1_pre_topc @ X36))),
% 4.66/4.86      inference('cnf', [status(esa)], [t1_tsep_1])).
% 4.66/4.86  thf('225', plain,
% 4.66/4.86      (![X0 : $i]:
% 4.66/4.86         (~ (l1_pre_topc @ X0)
% 4.66/4.86          | ~ (l1_pre_topc @ X0)
% 4.66/4.86          | (m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 4.66/4.86             (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 4.66/4.86      inference('sup-', [status(thm)], ['223', '224'])).
% 4.66/4.86  thf('226', plain,
% 4.66/4.86      (![X0 : $i]:
% 4.66/4.86         ((m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 4.66/4.86           (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 4.66/4.86          | ~ (l1_pre_topc @ X0))),
% 4.66/4.86      inference('simplify', [status(thm)], ['225'])).
% 4.66/4.86  thf('227', plain,
% 4.66/4.86      (![X2 : $i, X3 : $i, X4 : $i]:
% 4.66/4.86         (~ (r2_hidden @ X2 @ X3)
% 4.66/4.86          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 4.66/4.86          | (m1_subset_1 @ X2 @ X4))),
% 4.66/4.86      inference('cnf', [status(esa)], [t4_subset])).
% 4.66/4.86  thf('228', plain,
% 4.66/4.86      (![X0 : $i, X1 : $i]:
% 4.66/4.86         (~ (l1_pre_topc @ X0)
% 4.66/4.86          | (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 4.66/4.86          | ~ (r2_hidden @ X1 @ (u1_struct_0 @ X0)))),
% 4.66/4.86      inference('sup-', [status(thm)], ['226', '227'])).
% 4.66/4.86  thf('229', plain,
% 4.66/4.86      (((v2_struct_0 @ sk_A)
% 4.66/4.86        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 4.66/4.86           (k4_tmap_1 @ sk_A @ sk_B) @ sk_C)
% 4.66/4.86        | (v2_struct_0 @ sk_B)
% 4.66/4.86        | (m1_subset_1 @ 
% 4.66/4.86           (sk_F @ sk_C @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_B @ sk_B @ sk_A) @ 
% 4.66/4.86           (u1_struct_0 @ sk_B))
% 4.66/4.86        | ~ (l1_pre_topc @ sk_B))),
% 4.66/4.86      inference('sup-', [status(thm)], ['222', '228'])).
% 4.66/4.86  thf('230', plain, ((l1_pre_topc @ sk_B)),
% 4.66/4.86      inference('demod', [status(thm)], ['34', '35'])).
% 4.66/4.86  thf('231', plain,
% 4.66/4.86      (((v2_struct_0 @ sk_A)
% 4.66/4.86        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 4.66/4.86           (k4_tmap_1 @ sk_A @ sk_B) @ sk_C)
% 4.66/4.86        | (v2_struct_0 @ sk_B)
% 4.66/4.86        | (m1_subset_1 @ 
% 4.66/4.86           (sk_F @ sk_C @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_B @ sk_B @ sk_A) @ 
% 4.66/4.86           (u1_struct_0 @ sk_B)))),
% 4.66/4.86      inference('demod', [status(thm)], ['229', '230'])).
% 4.66/4.86  thf('232', plain,
% 4.66/4.86      ((m1_subset_1 @ (k4_tmap_1 @ sk_A @ sk_B) @ 
% 4.66/4.86        (k1_zfmisc_1 @ 
% 4.66/4.86         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 4.66/4.86      inference('clc', [status(thm)], ['9', '10'])).
% 4.66/4.86  thf(redefinition_k3_funct_2, axiom,
% 4.66/4.86    (![A:$i,B:$i,C:$i,D:$i]:
% 4.66/4.86     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_funct_1 @ C ) & 
% 4.66/4.86         ( v1_funct_2 @ C @ A @ B ) & 
% 4.66/4.86         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 4.66/4.86         ( m1_subset_1 @ D @ A ) ) =>
% 4.66/4.86       ( ( k3_funct_2 @ A @ B @ C @ D ) = ( k1_funct_1 @ C @ D ) ) ))).
% 4.66/4.86  thf('233', plain,
% 4.66/4.86      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 4.66/4.86         (~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X7)))
% 4.66/4.86          | ~ (v1_funct_2 @ X5 @ X6 @ X7)
% 4.66/4.86          | ~ (v1_funct_1 @ X5)
% 4.66/4.86          | (v1_xboole_0 @ X6)
% 4.66/4.86          | ~ (m1_subset_1 @ X8 @ X6)
% 4.66/4.86          | ((k3_funct_2 @ X6 @ X7 @ X5 @ X8) = (k1_funct_1 @ X5 @ X8)))),
% 4.66/4.86      inference('cnf', [status(esa)], [redefinition_k3_funct_2])).
% 4.66/4.86  thf('234', plain,
% 4.66/4.86      (![X0 : $i]:
% 4.66/4.86         (((k3_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 4.66/4.86            (k4_tmap_1 @ sk_A @ sk_B) @ X0)
% 4.66/4.86            = (k1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_B) @ X0))
% 4.66/4.86          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B))
% 4.66/4.86          | (v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 4.66/4.86          | ~ (v1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_B))
% 4.66/4.86          | ~ (v1_funct_2 @ (k4_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_B) @ 
% 4.66/4.86               (u1_struct_0 @ sk_A)))),
% 4.66/4.86      inference('sup-', [status(thm)], ['232', '233'])).
% 4.66/4.86  thf('235', plain, ((v1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_B))),
% 4.66/4.86      inference('clc', [status(thm)], ['29', '30'])).
% 4.66/4.86  thf('236', plain,
% 4.66/4.86      ((v1_funct_2 @ (k4_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_B) @ 
% 4.66/4.86        (u1_struct_0 @ sk_A))),
% 4.66/4.86      inference('clc', [status(thm)], ['21', '22'])).
% 4.66/4.86  thf('237', plain,
% 4.66/4.86      (![X0 : $i]:
% 4.66/4.86         (((k3_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 4.66/4.86            (k4_tmap_1 @ sk_A @ sk_B) @ X0)
% 4.66/4.86            = (k1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_B) @ X0))
% 4.66/4.86          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B))
% 4.66/4.86          | (v1_xboole_0 @ (u1_struct_0 @ sk_B)))),
% 4.66/4.86      inference('demod', [status(thm)], ['234', '235', '236'])).
% 4.66/4.86  thf('238', plain,
% 4.66/4.86      (((v2_struct_0 @ sk_B)
% 4.66/4.86        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 4.66/4.86           (k4_tmap_1 @ sk_A @ sk_B) @ sk_C)
% 4.66/4.86        | (v2_struct_0 @ sk_A)
% 4.66/4.86        | (v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 4.66/4.86        | ((k3_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 4.66/4.86            (k4_tmap_1 @ sk_A @ sk_B) @ 
% 4.66/4.86            (sk_F @ sk_C @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_B @ sk_B @ sk_A))
% 4.66/4.86            = (k1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_B) @ 
% 4.66/4.86               (sk_F @ sk_C @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_B @ sk_B @ sk_A))))),
% 4.66/4.86      inference('sup-', [status(thm)], ['231', '237'])).
% 4.66/4.86  thf('239', plain,
% 4.66/4.86      (![X38 : $i, X39 : $i, X40 : $i, X41 : $i, X42 : $i]:
% 4.66/4.86         ((v2_struct_0 @ X38)
% 4.66/4.86          | ~ (v2_pre_topc @ X38)
% 4.66/4.86          | ~ (l1_pre_topc @ X38)
% 4.66/4.86          | ~ (v1_funct_1 @ X39)
% 4.66/4.86          | ~ (v1_funct_2 @ X39 @ (u1_struct_0 @ X38) @ (u1_struct_0 @ X40))
% 4.66/4.86          | ~ (m1_subset_1 @ X39 @ 
% 4.66/4.86               (k1_zfmisc_1 @ 
% 4.66/4.86                (k2_zfmisc_1 @ (u1_struct_0 @ X38) @ (u1_struct_0 @ X40))))
% 4.66/4.86          | ((k3_funct_2 @ (u1_struct_0 @ X38) @ (u1_struct_0 @ X40) @ X39 @ 
% 4.66/4.86              (sk_F @ X41 @ X39 @ X42 @ X38 @ X40))
% 4.66/4.86              != (k1_funct_1 @ X41 @ (sk_F @ X41 @ X39 @ X42 @ X38 @ X40)))
% 4.66/4.86          | (r2_funct_2 @ (u1_struct_0 @ X42) @ (u1_struct_0 @ X40) @ 
% 4.66/4.86             (k2_tmap_1 @ X38 @ X40 @ X39 @ X42) @ X41)
% 4.66/4.86          | ~ (m1_subset_1 @ X41 @ 
% 4.66/4.86               (k1_zfmisc_1 @ 
% 4.66/4.86                (k2_zfmisc_1 @ (u1_struct_0 @ X42) @ (u1_struct_0 @ X40))))
% 4.66/4.86          | ~ (v1_funct_2 @ X41 @ (u1_struct_0 @ X42) @ (u1_struct_0 @ X40))
% 4.66/4.86          | ~ (v1_funct_1 @ X41)
% 4.66/4.86          | ~ (m1_pre_topc @ X42 @ X38)
% 4.66/4.86          | (v2_struct_0 @ X42)
% 4.66/4.86          | ~ (l1_pre_topc @ X40)
% 4.66/4.86          | ~ (v2_pre_topc @ X40)
% 4.66/4.86          | (v2_struct_0 @ X40))),
% 4.66/4.86      inference('cnf', [status(esa)], [t59_tmap_1])).
% 4.66/4.86  thf('240', plain,
% 4.66/4.86      ((((k1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_B) @ 
% 4.66/4.86          (sk_F @ sk_C @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_B @ sk_B @ sk_A))
% 4.66/4.86          != (k1_funct_1 @ sk_C @ 
% 4.66/4.86              (sk_F @ sk_C @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_B @ sk_B @ sk_A)))
% 4.66/4.86        | (v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 4.66/4.86        | (v2_struct_0 @ sk_A)
% 4.66/4.86        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 4.66/4.86           (k4_tmap_1 @ sk_A @ sk_B) @ sk_C)
% 4.66/4.86        | (v2_struct_0 @ sk_B)
% 4.66/4.86        | (v2_struct_0 @ sk_A)
% 4.66/4.86        | ~ (v2_pre_topc @ sk_A)
% 4.66/4.86        | ~ (l1_pre_topc @ sk_A)
% 4.66/4.86        | (v2_struct_0 @ sk_B)
% 4.66/4.86        | ~ (m1_pre_topc @ sk_B @ sk_B)
% 4.66/4.86        | ~ (v1_funct_1 @ sk_C)
% 4.66/4.86        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 4.66/4.86        | ~ (m1_subset_1 @ sk_C @ 
% 4.66/4.86             (k1_zfmisc_1 @ 
% 4.66/4.86              (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))
% 4.66/4.86        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 4.66/4.86           (k2_tmap_1 @ sk_B @ sk_A @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_B) @ sk_C)
% 4.66/4.86        | ~ (m1_subset_1 @ (k4_tmap_1 @ sk_A @ sk_B) @ 
% 4.66/4.86             (k1_zfmisc_1 @ 
% 4.66/4.86              (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))
% 4.66/4.86        | ~ (v1_funct_2 @ (k4_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_B) @ 
% 4.66/4.86             (u1_struct_0 @ sk_A))
% 4.66/4.86        | ~ (v1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_B))
% 4.66/4.86        | ~ (l1_pre_topc @ sk_B)
% 4.66/4.86        | ~ (v2_pre_topc @ sk_B)
% 4.66/4.86        | (v2_struct_0 @ sk_B))),
% 4.66/4.86      inference('sup-', [status(thm)], ['238', '239'])).
% 4.66/4.86  thf('241', plain, ((v2_pre_topc @ sk_A)),
% 4.66/4.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.66/4.86  thf('242', plain, ((l1_pre_topc @ sk_A)),
% 4.66/4.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.66/4.86  thf('243', plain, ((v1_funct_1 @ sk_C)),
% 4.66/4.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.66/4.86  thf('244', plain,
% 4.66/4.86      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 4.66/4.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.66/4.86  thf('245', plain,
% 4.66/4.86      ((m1_subset_1 @ sk_C @ 
% 4.66/4.86        (k1_zfmisc_1 @ 
% 4.66/4.86         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 4.66/4.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.66/4.86  thf('246', plain,
% 4.66/4.86      (((k4_tmap_1 @ sk_A @ sk_B)
% 4.66/4.86         = (k2_tmap_1 @ sk_B @ sk_A @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_B))),
% 4.66/4.86      inference('demod', [status(thm)], ['111', '135', '169', '189'])).
% 4.66/4.86  thf('247', plain,
% 4.66/4.86      ((m1_subset_1 @ (k4_tmap_1 @ sk_A @ sk_B) @ 
% 4.66/4.86        (k1_zfmisc_1 @ 
% 4.66/4.86         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 4.66/4.86      inference('clc', [status(thm)], ['9', '10'])).
% 4.66/4.86  thf('248', plain,
% 4.66/4.86      ((v1_funct_2 @ (k4_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_B) @ 
% 4.66/4.86        (u1_struct_0 @ sk_A))),
% 4.66/4.86      inference('clc', [status(thm)], ['21', '22'])).
% 4.66/4.86  thf('249', plain, ((v1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_B))),
% 4.66/4.86      inference('clc', [status(thm)], ['29', '30'])).
% 4.66/4.86  thf('250', plain, ((l1_pre_topc @ sk_B)),
% 4.66/4.86      inference('demod', [status(thm)], ['34', '35'])).
% 4.66/4.86  thf('251', plain, ((v2_pre_topc @ sk_B)),
% 4.66/4.86      inference('demod', [status(thm)], ['39', '40', '41'])).
% 4.66/4.86  thf('252', plain,
% 4.66/4.86      ((((k1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_B) @ 
% 4.66/4.86          (sk_F @ sk_C @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_B @ sk_B @ sk_A))
% 4.66/4.86          != (k1_funct_1 @ sk_C @ 
% 4.66/4.86              (sk_F @ sk_C @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_B @ sk_B @ sk_A)))
% 4.66/4.86        | (v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 4.66/4.86        | (v2_struct_0 @ sk_A)
% 4.66/4.86        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 4.66/4.86           (k4_tmap_1 @ sk_A @ sk_B) @ sk_C)
% 4.66/4.86        | (v2_struct_0 @ sk_B)
% 4.66/4.86        | (v2_struct_0 @ sk_A)
% 4.66/4.86        | (v2_struct_0 @ sk_B)
% 4.66/4.86        | ~ (m1_pre_topc @ sk_B @ sk_B)
% 4.66/4.86        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 4.66/4.86           (k4_tmap_1 @ sk_A @ sk_B) @ sk_C)
% 4.66/4.86        | (v2_struct_0 @ sk_B))),
% 4.66/4.86      inference('demod', [status(thm)],
% 4.66/4.86                ['240', '241', '242', '243', '244', '245', '246', '247', 
% 4.66/4.86                 '248', '249', '250', '251'])).
% 4.66/4.86  thf('253', plain,
% 4.66/4.86      ((~ (m1_pre_topc @ sk_B @ sk_B)
% 4.66/4.86        | (v2_struct_0 @ sk_B)
% 4.66/4.86        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 4.66/4.86           (k4_tmap_1 @ sk_A @ sk_B) @ sk_C)
% 4.66/4.86        | (v2_struct_0 @ sk_A)
% 4.66/4.86        | (v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 4.66/4.86        | ((k1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_B) @ 
% 4.66/4.86            (sk_F @ sk_C @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_B @ sk_B @ sk_A))
% 4.66/4.86            != (k1_funct_1 @ sk_C @ 
% 4.66/4.86                (sk_F @ sk_C @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_B @ sk_B @ sk_A))))),
% 4.66/4.86      inference('simplify', [status(thm)], ['252'])).
% 4.66/4.86  thf('254', plain,
% 4.66/4.86      ((((sk_F @ sk_C @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_B @ sk_B @ sk_A)
% 4.66/4.86          != (k1_funct_1 @ sk_C @ 
% 4.66/4.86              (sk_F @ sk_C @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_B @ sk_B @ sk_A)))
% 4.66/4.86        | (v2_struct_0 @ sk_B)
% 4.66/4.86        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 4.66/4.86           (k4_tmap_1 @ sk_A @ sk_B) @ sk_C)
% 4.66/4.86        | (v2_struct_0 @ sk_A)
% 4.66/4.86        | (v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 4.66/4.86        | (v2_struct_0 @ sk_A)
% 4.66/4.86        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 4.66/4.86           (k4_tmap_1 @ sk_A @ sk_B) @ sk_C)
% 4.66/4.86        | (v2_struct_0 @ sk_B)
% 4.66/4.86        | ~ (m1_pre_topc @ sk_B @ sk_B))),
% 4.66/4.86      inference('sup-', [status(thm)], ['221', '253'])).
% 4.66/4.86  thf('255', plain,
% 4.66/4.86      ((~ (m1_pre_topc @ sk_B @ sk_B)
% 4.66/4.86        | (v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 4.66/4.86        | (v2_struct_0 @ sk_A)
% 4.66/4.86        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 4.66/4.86           (k4_tmap_1 @ sk_A @ sk_B) @ sk_C)
% 4.66/4.86        | (v2_struct_0 @ sk_B)
% 4.66/4.86        | ((sk_F @ sk_C @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_B @ sk_B @ sk_A)
% 4.66/4.86            != (k1_funct_1 @ sk_C @ 
% 4.66/4.86                (sk_F @ sk_C @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_B @ sk_B @ sk_A))))),
% 4.66/4.86      inference('simplify', [status(thm)], ['254'])).
% 4.66/4.86  thf('256', plain,
% 4.66/4.86      ((((sk_F @ sk_C @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_B @ sk_B @ sk_A)
% 4.66/4.86          != (sk_F @ sk_C @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_B @ sk_B @ sk_A))
% 4.66/4.86        | (v2_struct_0 @ sk_B)
% 4.66/4.86        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 4.66/4.86           (k4_tmap_1 @ sk_A @ sk_B) @ sk_C)
% 4.66/4.86        | (v2_struct_0 @ sk_A)
% 4.66/4.86        | (v2_struct_0 @ sk_B)
% 4.66/4.86        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 4.66/4.86           (k4_tmap_1 @ sk_A @ sk_B) @ sk_C)
% 4.66/4.86        | (v2_struct_0 @ sk_A)
% 4.66/4.86        | (v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 4.66/4.86        | ~ (m1_pre_topc @ sk_B @ sk_B))),
% 4.66/4.86      inference('sup-', [status(thm)], ['210', '255'])).
% 4.66/4.86  thf('257', plain,
% 4.66/4.86      ((~ (m1_pre_topc @ sk_B @ sk_B)
% 4.66/4.86        | (v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 4.66/4.86        | (v2_struct_0 @ sk_A)
% 4.66/4.86        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 4.66/4.86           (k4_tmap_1 @ sk_A @ sk_B) @ sk_C)
% 4.66/4.86        | (v2_struct_0 @ sk_B))),
% 4.66/4.86      inference('simplify', [status(thm)], ['256'])).
% 4.66/4.86  thf('258', plain,
% 4.66/4.86      ((~ (l1_pre_topc @ sk_B)
% 4.66/4.86        | (v2_struct_0 @ sk_B)
% 4.66/4.86        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 4.66/4.86           (k4_tmap_1 @ sk_A @ sk_B) @ sk_C)
% 4.66/4.86        | (v2_struct_0 @ sk_A)
% 4.66/4.86        | (v1_xboole_0 @ (u1_struct_0 @ sk_B)))),
% 4.66/4.86      inference('sup-', [status(thm)], ['1', '257'])).
% 4.66/4.86  thf('259', plain, ((l1_pre_topc @ sk_B)),
% 4.66/4.86      inference('demod', [status(thm)], ['34', '35'])).
% 4.66/4.86  thf('260', plain,
% 4.66/4.86      (((v2_struct_0 @ sk_B)
% 4.66/4.86        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 4.66/4.86           (k4_tmap_1 @ sk_A @ sk_B) @ sk_C)
% 4.66/4.86        | (v2_struct_0 @ sk_A)
% 4.66/4.86        | (v1_xboole_0 @ (u1_struct_0 @ sk_B)))),
% 4.66/4.86      inference('demod', [status(thm)], ['258', '259'])).
% 4.66/4.86  thf('261', plain,
% 4.66/4.86      (~ (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 4.66/4.86          (k4_tmap_1 @ sk_A @ sk_B) @ sk_C)),
% 4.66/4.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.66/4.86  thf('262', plain,
% 4.66/4.86      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 4.66/4.86        | (v2_struct_0 @ sk_A)
% 4.66/4.86        | (v2_struct_0 @ sk_B))),
% 4.66/4.86      inference('sup-', [status(thm)], ['260', '261'])).
% 4.66/4.86  thf('263', plain, (~ (v2_struct_0 @ sk_A)),
% 4.66/4.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.66/4.86  thf('264', plain,
% 4.66/4.86      (((v2_struct_0 @ sk_B) | (v1_xboole_0 @ (u1_struct_0 @ sk_B)))),
% 4.66/4.86      inference('clc', [status(thm)], ['262', '263'])).
% 4.66/4.86  thf('265', plain, (~ (v2_struct_0 @ sk_B)),
% 4.66/4.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.66/4.86  thf('266', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_B))),
% 4.66/4.86      inference('clc', [status(thm)], ['264', '265'])).
% 4.66/4.86  thf(fc2_struct_0, axiom,
% 4.66/4.86    (![A:$i]:
% 4.66/4.86     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 4.66/4.86       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 4.66/4.86  thf('267', plain,
% 4.66/4.86      (![X18 : $i]:
% 4.66/4.86         (~ (v1_xboole_0 @ (u1_struct_0 @ X18))
% 4.66/4.86          | ~ (l1_struct_0 @ X18)
% 4.66/4.86          | (v2_struct_0 @ X18))),
% 4.66/4.86      inference('cnf', [status(esa)], [fc2_struct_0])).
% 4.66/4.86  thf('268', plain, (((v2_struct_0 @ sk_B) | ~ (l1_struct_0 @ sk_B))),
% 4.66/4.86      inference('sup-', [status(thm)], ['266', '267'])).
% 4.66/4.86  thf('269', plain, ((l1_pre_topc @ sk_B)),
% 4.66/4.86      inference('demod', [status(thm)], ['34', '35'])).
% 4.66/4.86  thf(dt_l1_pre_topc, axiom,
% 4.66/4.86    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 4.66/4.86  thf('270', plain,
% 4.66/4.86      (![X15 : $i]: ((l1_struct_0 @ X15) | ~ (l1_pre_topc @ X15))),
% 4.66/4.86      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 4.66/4.86  thf('271', plain, ((l1_struct_0 @ sk_B)),
% 4.66/4.86      inference('sup-', [status(thm)], ['269', '270'])).
% 4.66/4.86  thf('272', plain, ((v2_struct_0 @ sk_B)),
% 4.66/4.86      inference('demod', [status(thm)], ['268', '271'])).
% 4.66/4.86  thf('273', plain, ($false), inference('demod', [status(thm)], ['0', '272'])).
% 4.66/4.86  
% 4.66/4.86  % SZS output end Refutation
% 4.66/4.86  
% 4.68/4.87  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
