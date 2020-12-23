%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.HFXoK4c9Wp

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:10:41 EST 2020

% Result     : Theorem 2.25s
% Output     : Refutation 2.25s
% Verified   : 
% Statistics : Number of formulae       :  319 (10965 expanded)
%              Number of leaves         :   38 (3193 expanded)
%              Depth                    :   45
%              Number of atoms          : 4876 (293122 expanded)
%              Number of equality atoms :   56 (5220 expanded)
%              Maximal formula depth    :   25 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_F_type,type,(
    sk_F: $i > $i > $i > $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k3_funct_2_type,type,(
    k3_funct_2: $i > $i > $i > $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(r2_funct_2_type,type,(
    r2_funct_2: $i > $i > $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k2_partfun1_type,type,(
    k2_partfun1: $i > $i > $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k3_tmap_1_type,type,(
    k3_tmap_1: $i > $i > $i > $i > $i > $i )).

thf(k2_tmap_1_type,type,(
    k2_tmap_1: $i > $i > $i > $i > $i )).

thf(k4_tmap_1_type,type,(
    k4_tmap_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

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
    ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( m1_pre_topc @ A @ A ) ) )).

thf('1',plain,(
    ! [X36: $i] :
      ( ( m1_pre_topc @ X36 @ X36 )
      | ~ ( l1_pre_topc @ X36 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('2',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,(
    m1_pre_topc @ sk_B_1 @ sk_A ),
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

thf('4',plain,(
    ! [X34: $i,X35: $i] :
      ( ~ ( l1_pre_topc @ X34 )
      | ~ ( v2_pre_topc @ X34 )
      | ( v2_struct_0 @ X34 )
      | ~ ( m1_pre_topc @ X35 @ X34 )
      | ( m1_subset_1 @ ( k4_tmap_1 @ X34 @ X35 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X35 ) @ ( u1_struct_0 @ X34 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k4_tmap_1])).

thf('5',plain,
    ( ( m1_subset_1 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ( m1_subset_1 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['5','6','7'])).

thf('9',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    m1_subset_1 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['8','9'])).

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

thf('11',plain,(
    ! [X37: $i,X38: $i,X39: $i,X40: $i,X41: $i] :
      ( ( v2_struct_0 @ X37 )
      | ~ ( v2_pre_topc @ X37 )
      | ~ ( l1_pre_topc @ X37 )
      | ~ ( v1_funct_1 @ X38 )
      | ~ ( v1_funct_2 @ X38 @ ( u1_struct_0 @ X37 ) @ ( u1_struct_0 @ X39 ) )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X37 ) @ ( u1_struct_0 @ X39 ) ) ) )
      | ( r2_hidden @ ( sk_F @ X40 @ X38 @ X41 @ X37 @ X39 ) @ ( u1_struct_0 @ X41 ) )
      | ( r2_funct_2 @ ( u1_struct_0 @ X41 ) @ ( u1_struct_0 @ X39 ) @ ( k2_tmap_1 @ X37 @ X39 @ X38 @ X41 ) @ X40 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X41 ) @ ( u1_struct_0 @ X39 ) ) ) )
      | ~ ( v1_funct_2 @ X40 @ ( u1_struct_0 @ X41 ) @ ( u1_struct_0 @ X39 ) )
      | ~ ( v1_funct_1 @ X40 )
      | ~ ( m1_pre_topc @ X41 @ X37 )
      | ( v2_struct_0 @ X41 )
      | ~ ( l1_pre_topc @ X39 )
      | ~ ( v2_pre_topc @ X39 )
      | ( v2_struct_0 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t59_tmap_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_B_1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ) )
      | ( r2_funct_2 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tmap_1 @ sk_B_1 @ sk_A @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ X0 ) @ X1 )
      | ( r2_hidden @ ( sk_F @ X1 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ X0 @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v1_funct_2 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) )
      | ~ ( l1_pre_topc @ sk_B_1 )
      | ~ ( v2_pre_topc @ sk_B_1 )
      | ( v2_struct_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    m1_pre_topc @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ! [X34: $i,X35: $i] :
      ( ~ ( l1_pre_topc @ X34 )
      | ~ ( v2_pre_topc @ X34 )
      | ( v2_struct_0 @ X34 )
      | ~ ( m1_pre_topc @ X35 @ X34 )
      | ( v1_funct_2 @ ( k4_tmap_1 @ X34 @ X35 ) @ ( u1_struct_0 @ X35 ) @ ( u1_struct_0 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k4_tmap_1])).

thf('17',plain,
    ( ( v1_funct_2 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ( v1_funct_2 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['17','18','19'])).

thf('21',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    v1_funct_2 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['20','21'])).

thf('23',plain,(
    m1_pre_topc @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ! [X34: $i,X35: $i] :
      ( ~ ( l1_pre_topc @ X34 )
      | ~ ( v2_pre_topc @ X34 )
      | ( v2_struct_0 @ X34 )
      | ~ ( m1_pre_topc @ X35 @ X34 )
      | ( v1_funct_1 @ ( k4_tmap_1 @ X34 @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k4_tmap_1])).

thf('25',plain,
    ( ( v1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( ( v1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['25','26','27'])).

thf('29',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    v1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) ),
    inference(clc,[status(thm)],['28','29'])).

thf('31',plain,(
    m1_pre_topc @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('32',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( m1_pre_topc @ X15 @ X16 )
      | ( l1_pre_topc @ X15 )
      | ~ ( l1_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('33',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,(
    m1_pre_topc @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( v2_pre_topc @ B ) ) ) )).

thf('37',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( m1_pre_topc @ X13 @ X14 )
      | ( v2_pre_topc @ X13 )
      | ~ ( l1_pre_topc @ X14 )
      | ~ ( v2_pre_topc @ X14 ) ) ),
    inference(cnf,[status(esa)],[cc1_pre_topc])).

thf('38',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_pre_topc @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    v2_pre_topc @ sk_B_1 ),
    inference(demod,[status(thm)],['38','39','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_B_1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ) )
      | ( r2_funct_2 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tmap_1 @ sk_B_1 @ sk_A @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ X0 ) @ X1 )
      | ( r2_hidden @ ( sk_F @ X1 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ X0 @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ X0 ) )
      | ( v2_struct_0 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['12','13','14','22','30','35','41'])).

thf('43',plain,
    ( ( v2_struct_0 @ sk_B_1 )
    | ( r2_hidden @ ( sk_F @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_B_1 @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tmap_1 @ sk_B_1 @ sk_A @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_B_1 ) @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( m1_pre_topc @ sk_B_1 @ sk_B_1 )
    | ( v2_struct_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['2','42'])).

thf('44',plain,(
    ! [X36: $i] :
      ( ( m1_pre_topc @ X36 @ X36 )
      | ~ ( l1_pre_topc @ X36 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('45',plain,(
    m1_subset_1 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['8','9'])).

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

thf('46',plain,(
    ! [X42: $i,X43: $i,X44: $i,X45: $i] :
      ( ( v2_struct_0 @ X42 )
      | ~ ( v2_pre_topc @ X42 )
      | ~ ( l1_pre_topc @ X42 )
      | ~ ( v1_funct_1 @ X43 )
      | ~ ( v1_funct_2 @ X43 @ ( u1_struct_0 @ X44 ) @ ( u1_struct_0 @ X42 ) )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X44 ) @ ( u1_struct_0 @ X42 ) ) ) )
      | ( r2_funct_2 @ ( u1_struct_0 @ X44 ) @ ( u1_struct_0 @ X42 ) @ X43 @ ( k3_tmap_1 @ X45 @ X42 @ X44 @ X44 @ X43 ) )
      | ~ ( m1_pre_topc @ X44 @ X45 )
      | ( v2_struct_0 @ X44 )
      | ~ ( l1_pre_topc @ X45 )
      | ~ ( v2_pre_topc @ X45 )
      | ( v2_struct_0 @ X45 ) ) ),
    inference(cnf,[status(esa)],[t74_tmap_1])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ sk_B_1 )
      | ~ ( m1_pre_topc @ sk_B_1 @ X0 )
      | ( r2_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ ( k3_tmap_1 @ X0 @ sk_A @ sk_B_1 @ sk_B_1 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) ) )
      | ~ ( v1_funct_2 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    v1_funct_2 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['20','21'])).

thf('49',plain,(
    v1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) ),
    inference(clc,[status(thm)],['28','29'])).

thf('50',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ sk_B_1 )
      | ~ ( m1_pre_topc @ sk_B_1 @ X0 )
      | ( r2_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ ( k3_tmap_1 @ X0 @ sk_A @ sk_B_1 @ sk_B_1 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['47','48','49','50','51'])).

thf('53',plain,
    ( ~ ( l1_pre_topc @ sk_B_1 )
    | ( v2_struct_0 @ sk_A )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ ( k3_tmap_1 @ sk_B_1 @ sk_A @ sk_B_1 @ sk_B_1 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) ) )
    | ( v2_struct_0 @ sk_B_1 )
    | ~ ( l1_pre_topc @ sk_B_1 )
    | ~ ( v2_pre_topc @ sk_B_1 )
    | ( v2_struct_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['44','52'])).

thf('54',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(demod,[status(thm)],['33','34'])).

thf('55',plain,(
    ! [X36: $i] :
      ( ( m1_pre_topc @ X36 @ X36 )
      | ~ ( l1_pre_topc @ X36 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('56',plain,(
    ! [X36: $i] :
      ( ( m1_pre_topc @ X36 @ X36 )
      | ~ ( l1_pre_topc @ X36 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('57',plain,(
    m1_subset_1 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['8','9'])).

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

thf('58',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ( v2_struct_0 @ X24 )
      | ~ ( v2_pre_topc @ X24 )
      | ~ ( l1_pre_topc @ X24 )
      | ~ ( m1_pre_topc @ X25 @ X26 )
      | ~ ( m1_pre_topc @ X25 @ X27 )
      | ( ( k3_tmap_1 @ X26 @ X24 @ X27 @ X25 @ X28 )
        = ( k2_partfun1 @ ( u1_struct_0 @ X27 ) @ ( u1_struct_0 @ X24 ) @ X28 @ ( u1_struct_0 @ X25 ) ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X27 ) @ ( u1_struct_0 @ X24 ) ) ) )
      | ~ ( v1_funct_2 @ X28 @ ( u1_struct_0 @ X27 ) @ ( u1_struct_0 @ X24 ) )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( m1_pre_topc @ X27 @ X26 )
      | ~ ( l1_pre_topc @ X26 )
      | ~ ( v2_pre_topc @ X26 )
      | ( v2_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d5_tmap_1])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ sk_B_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) )
      | ~ ( v1_funct_2 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
      | ( ( k3_tmap_1 @ X0 @ sk_A @ sk_B_1 @ X1 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( m1_pre_topc @ X1 @ sk_B_1 )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    v1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) ),
    inference(clc,[status(thm)],['28','29'])).

thf('61',plain,(
    v1_funct_2 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['20','21'])).

thf('62',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ sk_B_1 @ X0 )
      | ( ( k3_tmap_1 @ X0 @ sk_A @ sk_B_1 @ X1 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( m1_pre_topc @ X1 @ sk_B_1 )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['59','60','61','62','63'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_B_1 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_B_1 )
      | ~ ( m1_pre_topc @ X0 @ sk_B_1 )
      | ( ( k3_tmap_1 @ sk_B_1 @ sk_A @ sk_B_1 @ X0 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ sk_B_1 )
      | ~ ( v2_pre_topc @ sk_B_1 )
      | ( v2_struct_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['56','64'])).

thf('66',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(demod,[status(thm)],['33','34'])).

thf('67',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(demod,[status(thm)],['33','34'])).

thf('68',plain,(
    v2_pre_topc @ sk_B_1 ),
    inference(demod,[status(thm)],['38','39','40'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_B_1 )
      | ~ ( m1_pre_topc @ X0 @ sk_B_1 )
      | ( ( k3_tmap_1 @ sk_B_1 @ sk_A @ sk_B_1 @ X0 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ ( u1_struct_0 @ X0 ) ) )
      | ( v2_struct_0 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['65','66','67','68'])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B_1 )
      | ( ( k3_tmap_1 @ sk_B_1 @ sk_A @ sk_B_1 @ X0 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['69'])).

thf('71',plain,
    ( ~ ( l1_pre_topc @ sk_B_1 )
    | ( v2_struct_0 @ sk_A )
    | ( ( k3_tmap_1 @ sk_B_1 @ sk_A @ sk_B_1 @ sk_B_1 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ ( u1_struct_0 @ sk_B_1 ) ) )
    | ( v2_struct_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['55','70'])).

thf('72',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(demod,[status(thm)],['33','34'])).

thf('73',plain,(
    ! [X36: $i] :
      ( ( m1_pre_topc @ X36 @ X36 )
      | ~ ( l1_pre_topc @ X36 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('74',plain,(
    m1_subset_1 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['8','9'])).

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

thf('75',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ( v2_struct_0 @ X20 )
      | ~ ( v2_pre_topc @ X20 )
      | ~ ( l1_pre_topc @ X20 )
      | ~ ( m1_pre_topc @ X21 @ X22 )
      | ( ( k2_tmap_1 @ X22 @ X20 @ X23 @ X21 )
        = ( k2_partfun1 @ ( u1_struct_0 @ X22 ) @ ( u1_struct_0 @ X20 ) @ X23 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X22 ) @ ( u1_struct_0 @ X20 ) ) ) )
      | ~ ( v1_funct_2 @ X23 @ ( u1_struct_0 @ X22 ) @ ( u1_struct_0 @ X20 ) )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( l1_pre_topc @ X22 )
      | ~ ( v2_pre_topc @ X22 )
      | ( v2_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d4_tmap_1])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B_1 )
      | ~ ( v2_pre_topc @ sk_B_1 )
      | ~ ( l1_pre_topc @ sk_B_1 )
      | ~ ( v1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) )
      | ~ ( v1_funct_2 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
      | ( ( k2_tmap_1 @ sk_B_1 @ sk_A @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ X0 )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_B_1 )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    v2_pre_topc @ sk_B_1 ),
    inference(demod,[status(thm)],['38','39','40'])).

thf('78',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(demod,[status(thm)],['33','34'])).

thf('79',plain,(
    v1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) ),
    inference(clc,[status(thm)],['28','29'])).

thf('80',plain,(
    v1_funct_2 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['20','21'])).

thf('81',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B_1 )
      | ( ( k2_tmap_1 @ sk_B_1 @ sk_A @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ X0 )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['76','77','78','79','80','81','82'])).

thf('84',plain,
    ( ~ ( l1_pre_topc @ sk_B_1 )
    | ( v2_struct_0 @ sk_A )
    | ( ( k2_tmap_1 @ sk_B_1 @ sk_A @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_B_1 )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ ( u1_struct_0 @ sk_B_1 ) ) )
    | ( v2_struct_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['73','83'])).

thf('85',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(demod,[status(thm)],['33','34'])).

thf('86',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k2_tmap_1 @ sk_B_1 @ sk_A @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_B_1 )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ ( u1_struct_0 @ sk_B_1 ) ) )
    | ( v2_struct_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('87',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,
    ( ( v2_struct_0 @ sk_B_1 )
    | ( ( k2_tmap_1 @ sk_B_1 @ sk_A @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_B_1 )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference(clc,[status(thm)],['86','87'])).

thf('89',plain,(
    ~ ( v2_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,
    ( ( k2_tmap_1 @ sk_B_1 @ sk_A @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_B_1 )
    = ( k2_partfun1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['88','89'])).

thf('91',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k3_tmap_1 @ sk_B_1 @ sk_A @ sk_B_1 @ sk_B_1 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) )
      = ( k2_tmap_1 @ sk_B_1 @ sk_A @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['71','72','90'])).

thf('92',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,
    ( ( v2_struct_0 @ sk_B_1 )
    | ( ( k3_tmap_1 @ sk_B_1 @ sk_A @ sk_B_1 @ sk_B_1 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) )
      = ( k2_tmap_1 @ sk_B_1 @ sk_A @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['91','92'])).

thf('94',plain,(
    ~ ( v2_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,
    ( ( k3_tmap_1 @ sk_B_1 @ sk_A @ sk_B_1 @ sk_B_1 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) )
    = ( k2_tmap_1 @ sk_B_1 @ sk_A @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_B_1 ) ),
    inference(clc,[status(thm)],['93','94'])).

thf('96',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(demod,[status(thm)],['33','34'])).

thf('97',plain,(
    v2_pre_topc @ sk_B_1 ),
    inference(demod,[status(thm)],['38','39','40'])).

thf('98',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ ( k2_tmap_1 @ sk_B_1 @ sk_A @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['53','54','95','96','97'])).

thf('99',plain,
    ( ( v2_struct_0 @ sk_B_1 )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ ( k2_tmap_1 @ sk_B_1 @ sk_A @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['98'])).

thf('100',plain,(
    ~ ( v2_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ ( k2_tmap_1 @ sk_B_1 @ sk_A @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['99','100'])).

thf('102',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,(
    r2_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ ( k2_tmap_1 @ sk_B_1 @ sk_A @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_B_1 ) ),
    inference(clc,[status(thm)],['101','102'])).

thf('104',plain,(
    m1_subset_1 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['8','9'])).

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

thf('106',plain,(
    ! [X0: $i] :
      ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ X0 )
      | ( ( k4_tmap_1 @ sk_A @ sk_B_1 )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ) )
      | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) )
      | ~ ( v1_funct_2 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['104','105'])).

thf('107',plain,(
    v1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) ),
    inference(clc,[status(thm)],['28','29'])).

thf('108',plain,(
    v1_funct_2 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['20','21'])).

thf('109',plain,(
    ! [X0: $i] :
      ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ X0 )
      | ( ( k4_tmap_1 @ sk_A @ sk_B_1 )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ) )
      | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['106','107','108'])).

thf('110',plain,
    ( ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_B_1 @ sk_A @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
    | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_B_1 @ sk_A @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_B_1 @ sk_A @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ( ( k4_tmap_1 @ sk_A @ sk_B_1 )
      = ( k2_tmap_1 @ sk_B_1 @ sk_A @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['103','109'])).

thf('111',plain,(
    ! [X36: $i] :
      ( ( m1_pre_topc @ X36 @ X36 )
      | ~ ( l1_pre_topc @ X36 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('112',plain,(
    ! [X36: $i] :
      ( ( m1_pre_topc @ X36 @ X36 )
      | ~ ( l1_pre_topc @ X36 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('113',plain,(
    m1_subset_1 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['8','9'])).

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

thf('114',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ~ ( m1_pre_topc @ X29 @ X30 )
      | ~ ( m1_pre_topc @ X31 @ X30 )
      | ~ ( l1_pre_topc @ X32 )
      | ~ ( v2_pre_topc @ X32 )
      | ( v2_struct_0 @ X32 )
      | ~ ( l1_pre_topc @ X30 )
      | ~ ( v2_pre_topc @ X30 )
      | ( v2_struct_0 @ X30 )
      | ~ ( v1_funct_1 @ X33 )
      | ~ ( v1_funct_2 @ X33 @ ( u1_struct_0 @ X31 ) @ ( u1_struct_0 @ X32 ) )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X31 ) @ ( u1_struct_0 @ X32 ) ) ) )
      | ( v1_funct_1 @ ( k3_tmap_1 @ X30 @ X32 @ X31 @ X29 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_tmap_1])).

thf('115',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_1 @ ( k3_tmap_1 @ X1 @ sk_A @ sk_B_1 @ X0 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) ) )
      | ~ ( v1_funct_2 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_pre_topc @ sk_B_1 @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['113','114'])).

thf('116',plain,(
    v1_funct_2 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['20','21'])).

thf('117',plain,(
    v1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) ),
    inference(clc,[status(thm)],['28','29'])).

thf('118',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_1 @ ( k3_tmap_1 @ X1 @ sk_A @ sk_B_1 @ X0 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( m1_pre_topc @ sk_B_1 @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['115','116','117','118','119'])).

thf('121',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_B_1 )
      | ~ ( m1_pre_topc @ X0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_pre_topc @ sk_B_1 )
      | ~ ( v2_pre_topc @ sk_B_1 )
      | ( v2_struct_0 @ sk_B_1 )
      | ( v1_funct_1 @ ( k3_tmap_1 @ sk_B_1 @ sk_A @ sk_B_1 @ X0 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['112','120'])).

thf('122',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(demod,[status(thm)],['33','34'])).

thf('123',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(demod,[status(thm)],['33','34'])).

thf('124',plain,(
    v2_pre_topc @ sk_B_1 ),
    inference(demod,[status(thm)],['38','39','40'])).

thf('125',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B_1 )
      | ( v1_funct_1 @ ( k3_tmap_1 @ sk_B_1 @ sk_A @ sk_B_1 @ X0 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) ) ) ) ),
    inference(demod,[status(thm)],['121','122','123','124'])).

thf('126',plain,
    ( ~ ( l1_pre_topc @ sk_B_1 )
    | ( v1_funct_1 @ ( k3_tmap_1 @ sk_B_1 @ sk_A @ sk_B_1 @ sk_B_1 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) ) )
    | ( v2_struct_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['111','125'])).

thf('127',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(demod,[status(thm)],['33','34'])).

thf('128',plain,
    ( ( v1_funct_1 @ ( k3_tmap_1 @ sk_B_1 @ sk_A @ sk_B_1 @ sk_B_1 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) ) )
    | ( v2_struct_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['126','127'])).

thf('129',plain,(
    ~ ( v2_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('130',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v1_funct_1 @ ( k3_tmap_1 @ sk_B_1 @ sk_A @ sk_B_1 @ sk_B_1 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) ) ) ),
    inference(clc,[status(thm)],['128','129'])).

thf('131',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('132',plain,(
    v1_funct_1 @ ( k3_tmap_1 @ sk_B_1 @ sk_A @ sk_B_1 @ sk_B_1 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['130','131'])).

thf('133',plain,
    ( ( k3_tmap_1 @ sk_B_1 @ sk_A @ sk_B_1 @ sk_B_1 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) )
    = ( k2_tmap_1 @ sk_B_1 @ sk_A @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_B_1 ) ),
    inference(clc,[status(thm)],['93','94'])).

thf('134',plain,(
    v1_funct_1 @ ( k2_tmap_1 @ sk_B_1 @ sk_A @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_B_1 ) ),
    inference(demod,[status(thm)],['132','133'])).

thf('135',plain,(
    ! [X36: $i] :
      ( ( m1_pre_topc @ X36 @ X36 )
      | ~ ( l1_pre_topc @ X36 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('136',plain,(
    ! [X36: $i] :
      ( ( m1_pre_topc @ X36 @ X36 )
      | ~ ( l1_pre_topc @ X36 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('137',plain,(
    m1_subset_1 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['8','9'])).

thf('138',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ~ ( m1_pre_topc @ X29 @ X30 )
      | ~ ( m1_pre_topc @ X31 @ X30 )
      | ~ ( l1_pre_topc @ X32 )
      | ~ ( v2_pre_topc @ X32 )
      | ( v2_struct_0 @ X32 )
      | ~ ( l1_pre_topc @ X30 )
      | ~ ( v2_pre_topc @ X30 )
      | ( v2_struct_0 @ X30 )
      | ~ ( v1_funct_1 @ X33 )
      | ~ ( v1_funct_2 @ X33 @ ( u1_struct_0 @ X31 ) @ ( u1_struct_0 @ X32 ) )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X31 ) @ ( u1_struct_0 @ X32 ) ) ) )
      | ( v1_funct_2 @ ( k3_tmap_1 @ X30 @ X32 @ X31 @ X29 @ X33 ) @ ( u1_struct_0 @ X29 ) @ ( u1_struct_0 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_tmap_1])).

thf('139',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_2 @ ( k3_tmap_1 @ X1 @ sk_A @ sk_B_1 @ X0 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_2 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_pre_topc @ sk_B_1 @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['137','138'])).

thf('140',plain,(
    v1_funct_2 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['20','21'])).

thf('141',plain,(
    v1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) ),
    inference(clc,[status(thm)],['28','29'])).

thf('142',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('143',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('144',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_2 @ ( k3_tmap_1 @ X1 @ sk_A @ sk_B_1 @ X0 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( m1_pre_topc @ sk_B_1 @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['139','140','141','142','143'])).

thf('145',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_B_1 )
      | ~ ( m1_pre_topc @ X0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_pre_topc @ sk_B_1 )
      | ~ ( v2_pre_topc @ sk_B_1 )
      | ( v2_struct_0 @ sk_B_1 )
      | ( v1_funct_2 @ ( k3_tmap_1 @ sk_B_1 @ sk_A @ sk_B_1 @ X0 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['136','144'])).

thf('146',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(demod,[status(thm)],['33','34'])).

thf('147',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(demod,[status(thm)],['33','34'])).

thf('148',plain,(
    v2_pre_topc @ sk_B_1 ),
    inference(demod,[status(thm)],['38','39','40'])).

thf('149',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B_1 )
      | ( v1_funct_2 @ ( k3_tmap_1 @ sk_B_1 @ sk_A @ sk_B_1 @ X0 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['145','146','147','148'])).

thf('150',plain,
    ( ~ ( l1_pre_topc @ sk_B_1 )
    | ( v1_funct_2 @ ( k3_tmap_1 @ sk_B_1 @ sk_A @ sk_B_1 @ sk_B_1 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) ) @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['135','149'])).

thf('151',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(demod,[status(thm)],['33','34'])).

thf('152',plain,
    ( ( v1_funct_2 @ ( k3_tmap_1 @ sk_B_1 @ sk_A @ sk_B_1 @ sk_B_1 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) ) @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['150','151'])).

thf('153',plain,(
    ~ ( v2_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('154',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v1_funct_2 @ ( k3_tmap_1 @ sk_B_1 @ sk_A @ sk_B_1 @ sk_B_1 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) ) @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['152','153'])).

thf('155',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('156',plain,(
    v1_funct_2 @ ( k3_tmap_1 @ sk_B_1 @ sk_A @ sk_B_1 @ sk_B_1 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) ) @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['154','155'])).

thf('157',plain,
    ( ( k3_tmap_1 @ sk_B_1 @ sk_A @ sk_B_1 @ sk_B_1 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) )
    = ( k2_tmap_1 @ sk_B_1 @ sk_A @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_B_1 ) ),
    inference(clc,[status(thm)],['93','94'])).

thf('158',plain,(
    v1_funct_2 @ ( k2_tmap_1 @ sk_B_1 @ sk_A @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['156','157'])).

thf('159',plain,(
    ! [X36: $i] :
      ( ( m1_pre_topc @ X36 @ X36 )
      | ~ ( l1_pre_topc @ X36 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('160',plain,(
    ! [X36: $i] :
      ( ( m1_pre_topc @ X36 @ X36 )
      | ~ ( l1_pre_topc @ X36 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('161',plain,(
    m1_subset_1 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['8','9'])).

thf('162',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ~ ( m1_pre_topc @ X29 @ X30 )
      | ~ ( m1_pre_topc @ X31 @ X30 )
      | ~ ( l1_pre_topc @ X32 )
      | ~ ( v2_pre_topc @ X32 )
      | ( v2_struct_0 @ X32 )
      | ~ ( l1_pre_topc @ X30 )
      | ~ ( v2_pre_topc @ X30 )
      | ( v2_struct_0 @ X30 )
      | ~ ( v1_funct_1 @ X33 )
      | ~ ( v1_funct_2 @ X33 @ ( u1_struct_0 @ X31 ) @ ( u1_struct_0 @ X32 ) )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X31 ) @ ( u1_struct_0 @ X32 ) ) ) )
      | ( m1_subset_1 @ ( k3_tmap_1 @ X30 @ X32 @ X31 @ X29 @ X33 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X29 ) @ ( u1_struct_0 @ X32 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_tmap_1])).

thf('163',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( k3_tmap_1 @ X1 @ sk_A @ sk_B_1 @ X0 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ) )
      | ~ ( v1_funct_2 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_pre_topc @ sk_B_1 @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['161','162'])).

thf('164',plain,(
    v1_funct_2 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['20','21'])).

thf('165',plain,(
    v1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) ),
    inference(clc,[status(thm)],['28','29'])).

thf('166',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('167',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('168',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( k3_tmap_1 @ X1 @ sk_A @ sk_B_1 @ X0 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( m1_pre_topc @ sk_B_1 @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['163','164','165','166','167'])).

thf('169',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_B_1 )
      | ~ ( m1_pre_topc @ X0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_pre_topc @ sk_B_1 )
      | ~ ( v2_pre_topc @ sk_B_1 )
      | ( v2_struct_0 @ sk_B_1 )
      | ( m1_subset_1 @ ( k3_tmap_1 @ sk_B_1 @ sk_A @ sk_B_1 @ X0 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['160','168'])).

thf('170',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(demod,[status(thm)],['33','34'])).

thf('171',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(demod,[status(thm)],['33','34'])).

thf('172',plain,(
    v2_pre_topc @ sk_B_1 ),
    inference(demod,[status(thm)],['38','39','40'])).

thf('173',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B_1 )
      | ( m1_subset_1 @ ( k3_tmap_1 @ sk_B_1 @ sk_A @ sk_B_1 @ X0 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['169','170','171','172'])).

thf('174',plain,
    ( ~ ( l1_pre_topc @ sk_B_1 )
    | ( m1_subset_1 @ ( k3_tmap_1 @ sk_B_1 @ sk_A @ sk_B_1 @ sk_B_1 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ( v2_struct_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['159','173'])).

thf('175',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(demod,[status(thm)],['33','34'])).

thf('176',plain,
    ( ( k3_tmap_1 @ sk_B_1 @ sk_A @ sk_B_1 @ sk_B_1 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) )
    = ( k2_tmap_1 @ sk_B_1 @ sk_A @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_B_1 ) ),
    inference(clc,[status(thm)],['93','94'])).

thf('177',plain,
    ( ( m1_subset_1 @ ( k2_tmap_1 @ sk_B_1 @ sk_A @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ( v2_struct_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['174','175','176'])).

thf('178',plain,(
    ~ ( v2_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('179',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( k2_tmap_1 @ sk_B_1 @ sk_A @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(clc,[status(thm)],['177','178'])).

thf('180',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('181',plain,(
    m1_subset_1 @ ( k2_tmap_1 @ sk_B_1 @ sk_A @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['179','180'])).

thf('182',plain,
    ( ( k4_tmap_1 @ sk_A @ sk_B_1 )
    = ( k2_tmap_1 @ sk_B_1 @ sk_A @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_B_1 ) ),
    inference(demod,[status(thm)],['110','134','158','181'])).

thf('183',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('184',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('185',plain,
    ( ( v2_struct_0 @ sk_B_1 )
    | ( r2_hidden @ ( sk_F @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_B_1 @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_C )
    | ~ ( m1_pre_topc @ sk_B_1 @ sk_B_1 )
    | ( v2_struct_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['43','182','183','184'])).

thf('186',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( m1_pre_topc @ sk_B_1 @ sk_B_1 )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_C )
    | ( r2_hidden @ ( sk_F @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_B_1 @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_B_1 ) ),
    inference(simplify,[status(thm)],['185'])).

thf('187',plain,
    ( ~ ( l1_pre_topc @ sk_B_1 )
    | ( v2_struct_0 @ sk_B_1 )
    | ( r2_hidden @ ( sk_F @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_B_1 @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['1','186'])).

thf('188',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(demod,[status(thm)],['33','34'])).

thf('189',plain,
    ( ( v2_struct_0 @ sk_B_1 )
    | ( r2_hidden @ ( sk_F @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_B_1 @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['187','188'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('190',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('191',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_C )
    | ( v2_struct_0 @ sk_B_1 )
    | ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['189','190'])).

thf('192',plain,(
    ! [X36: $i] :
      ( ( m1_pre_topc @ X36 @ X36 )
      | ~ ( l1_pre_topc @ X36 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('193',plain,(
    m1_pre_topc @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('194',plain,(
    ! [X36: $i] :
      ( ( m1_pre_topc @ X36 @ X36 )
      | ~ ( l1_pre_topc @ X36 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('195',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('196',plain,(
    m1_subset_1 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['8','9'])).

thf('197',plain,(
    ! [X37: $i,X38: $i,X39: $i,X40: $i,X41: $i] :
      ( ( v2_struct_0 @ X37 )
      | ~ ( v2_pre_topc @ X37 )
      | ~ ( l1_pre_topc @ X37 )
      | ~ ( v1_funct_1 @ X38 )
      | ~ ( v1_funct_2 @ X38 @ ( u1_struct_0 @ X37 ) @ ( u1_struct_0 @ X39 ) )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X37 ) @ ( u1_struct_0 @ X39 ) ) ) )
      | ( m1_subset_1 @ ( sk_F @ X40 @ X38 @ X41 @ X37 @ X39 ) @ ( u1_struct_0 @ X37 ) )
      | ( r2_funct_2 @ ( u1_struct_0 @ X41 ) @ ( u1_struct_0 @ X39 ) @ ( k2_tmap_1 @ X37 @ X39 @ X38 @ X41 ) @ X40 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X41 ) @ ( u1_struct_0 @ X39 ) ) ) )
      | ~ ( v1_funct_2 @ X40 @ ( u1_struct_0 @ X41 ) @ ( u1_struct_0 @ X39 ) )
      | ~ ( v1_funct_1 @ X40 )
      | ~ ( m1_pre_topc @ X41 @ X37 )
      | ( v2_struct_0 @ X41 )
      | ~ ( l1_pre_topc @ X39 )
      | ~ ( v2_pre_topc @ X39 )
      | ( v2_struct_0 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t59_tmap_1])).

thf('198',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_B_1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ) )
      | ( r2_funct_2 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tmap_1 @ sk_B_1 @ sk_A @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ X0 ) @ X1 )
      | ( m1_subset_1 @ ( sk_F @ X1 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ X0 @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) )
      | ~ ( v1_funct_2 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) )
      | ~ ( l1_pre_topc @ sk_B_1 )
      | ~ ( v2_pre_topc @ sk_B_1 )
      | ( v2_struct_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['196','197'])).

thf('199',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('200',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('201',plain,(
    v1_funct_2 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['20','21'])).

thf('202',plain,(
    v1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) ),
    inference(clc,[status(thm)],['28','29'])).

thf('203',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(demod,[status(thm)],['33','34'])).

thf('204',plain,(
    v2_pre_topc @ sk_B_1 ),
    inference(demod,[status(thm)],['38','39','40'])).

thf('205',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_B_1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ) )
      | ( r2_funct_2 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tmap_1 @ sk_B_1 @ sk_A @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ X0 ) @ X1 )
      | ( m1_subset_1 @ ( sk_F @ X1 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ X0 @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) )
      | ( v2_struct_0 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['198','199','200','201','202','203','204'])).

thf('206',plain,
    ( ( v2_struct_0 @ sk_B_1 )
    | ( m1_subset_1 @ ( sk_F @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_B_1 @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tmap_1 @ sk_B_1 @ sk_A @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_B_1 ) @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( m1_pre_topc @ sk_B_1 @ sk_B_1 )
    | ( v2_struct_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['195','205'])).

thf('207',plain,
    ( ( k4_tmap_1 @ sk_A @ sk_B_1 )
    = ( k2_tmap_1 @ sk_B_1 @ sk_A @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_B_1 ) ),
    inference(demod,[status(thm)],['110','134','158','181'])).

thf('208',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('209',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('210',plain,
    ( ( v2_struct_0 @ sk_B_1 )
    | ( m1_subset_1 @ ( sk_F @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_B_1 @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_C )
    | ~ ( m1_pre_topc @ sk_B_1 @ sk_B_1 )
    | ( v2_struct_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['206','207','208','209'])).

thf('211',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( m1_pre_topc @ sk_B_1 @ sk_B_1 )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_C )
    | ( m1_subset_1 @ ( sk_F @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_B_1 @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_B_1 ) ),
    inference(simplify,[status(thm)],['210'])).

thf('212',plain,
    ( ~ ( l1_pre_topc @ sk_B_1 )
    | ( v2_struct_0 @ sk_B_1 )
    | ( m1_subset_1 @ ( sk_F @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_B_1 @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['194','211'])).

thf('213',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(demod,[status(thm)],['33','34'])).

thf('214',plain,
    ( ( v2_struct_0 @ sk_B_1 )
    | ( m1_subset_1 @ ( sk_F @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_B_1 @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['212','213'])).

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

thf('215',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( v2_struct_0 @ X17 )
      | ~ ( m1_pre_topc @ X17 @ X18 )
      | ( m1_subset_1 @ X19 @ ( u1_struct_0 @ X18 ) )
      | ~ ( m1_subset_1 @ X19 @ ( u1_struct_0 @ X17 ) )
      | ~ ( l1_pre_topc @ X18 )
      | ( v2_struct_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t55_pre_topc])).

thf('216',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r2_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_C )
      | ( v2_struct_0 @ sk_B_1 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_subset_1 @ ( sk_F @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_B_1 @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ sk_B_1 @ X0 )
      | ( v2_struct_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['214','215'])).

thf('217',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ sk_B_1 @ X0 )
      | ( m1_subset_1 @ ( sk_F @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_B_1 @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_B_1 )
      | ( r2_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_C )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['216'])).

thf('218',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_C )
    | ( v2_struct_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( m1_subset_1 @ ( sk_F @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_B_1 @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['193','217'])).

thf('219',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('220',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_C )
    | ( v2_struct_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( sk_F @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_B_1 @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['218','219'])).

thf('221',plain,
    ( ( m1_subset_1 @ ( sk_F @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_B_1 @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B_1 )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['220'])).

thf('222',plain,
    ( ( v2_struct_0 @ sk_B_1 )
    | ( r2_hidden @ ( sk_F @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_B_1 @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['187','188'])).

thf('223',plain,(
    ! [X52: $i] :
      ( ~ ( r2_hidden @ X52 @ ( u1_struct_0 @ sk_B_1 ) )
      | ( X52
        = ( k1_funct_1 @ sk_C @ X52 ) )
      | ~ ( m1_subset_1 @ X52 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('224',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_C )
    | ( v2_struct_0 @ sk_B_1 )
    | ~ ( m1_subset_1 @ ( sk_F @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_B_1 @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( ( sk_F @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_B_1 @ sk_B_1 @ sk_A )
      = ( k1_funct_1 @ sk_C @ ( sk_F @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_B_1 @ sk_B_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['222','223'])).

thf('225',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_C )
    | ( v2_struct_0 @ sk_B_1 )
    | ( ( sk_F @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_B_1 @ sk_B_1 @ sk_A )
      = ( k1_funct_1 @ sk_C @ ( sk_F @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_B_1 @ sk_B_1 @ sk_A ) ) )
    | ( v2_struct_0 @ sk_B_1 )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['221','224'])).

thf('226',plain,
    ( ( ( sk_F @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_B_1 @ sk_B_1 @ sk_A )
      = ( k1_funct_1 @ sk_C @ ( sk_F @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_B_1 @ sk_B_1 @ sk_A ) ) )
    | ( v2_struct_0 @ sk_B_1 )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['225'])).

thf('227',plain,
    ( ( m1_subset_1 @ ( sk_F @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_B_1 @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B_1 )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['220'])).

thf('228',plain,
    ( ( v2_struct_0 @ sk_B_1 )
    | ( r2_hidden @ ( sk_F @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_B_1 @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['187','188'])).

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

thf('229',plain,(
    ! [X49: $i,X50: $i,X51: $i] :
      ( ( v2_struct_0 @ X49 )
      | ~ ( m1_pre_topc @ X49 @ X50 )
      | ~ ( r2_hidden @ X51 @ ( u1_struct_0 @ X49 ) )
      | ( ( k1_funct_1 @ ( k4_tmap_1 @ X50 @ X49 ) @ X51 )
        = X51 )
      | ~ ( m1_subset_1 @ X51 @ ( u1_struct_0 @ X50 ) )
      | ~ ( l1_pre_topc @ X50 )
      | ~ ( v2_pre_topc @ X50 )
      | ( v2_struct_0 @ X50 ) ) ),
    inference(cnf,[status(esa)],[t95_tmap_1])).

thf('230',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r2_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_C )
      | ( v2_struct_0 @ sk_B_1 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_subset_1 @ ( sk_F @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_B_1 @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ X0 ) )
      | ( ( k1_funct_1 @ ( k4_tmap_1 @ X0 @ sk_B_1 ) @ ( sk_F @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_B_1 @ sk_B_1 @ sk_A ) )
        = ( sk_F @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_B_1 @ sk_B_1 @ sk_A ) )
      | ~ ( m1_pre_topc @ sk_B_1 @ X0 )
      | ( v2_struct_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['228','229'])).

thf('231',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ sk_B_1 @ X0 )
      | ( ( k1_funct_1 @ ( k4_tmap_1 @ X0 @ sk_B_1 ) @ ( sk_F @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_B_1 @ sk_B_1 @ sk_A ) )
        = ( sk_F @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_B_1 @ sk_B_1 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( sk_F @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_B_1 @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_B_1 )
      | ( r2_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_C )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['230'])).

thf('232',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_C )
    | ( v2_struct_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_C )
    | ( v2_struct_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ ( sk_F @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_B_1 @ sk_B_1 @ sk_A ) )
      = ( sk_F @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_B_1 @ sk_B_1 @ sk_A ) )
    | ~ ( m1_pre_topc @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['227','231'])).

thf('233',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('234',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('235',plain,(
    m1_pre_topc @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('236',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_C )
    | ( v2_struct_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_C )
    | ( v2_struct_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A )
    | ( ( k1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ ( sk_F @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_B_1 @ sk_B_1 @ sk_A ) )
      = ( sk_F @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_B_1 @ sk_B_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['232','233','234','235'])).

thf('237',plain,
    ( ( ( k1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ ( sk_F @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_B_1 @ sk_B_1 @ sk_A ) )
      = ( sk_F @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_B_1 @ sk_B_1 @ sk_A ) )
    | ( v2_struct_0 @ sk_B_1 )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['236'])).

thf('238',plain,
    ( ( v2_struct_0 @ sk_B_1 )
    | ( m1_subset_1 @ ( sk_F @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_B_1 @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['212','213'])).

thf('239',plain,(
    m1_subset_1 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['8','9'])).

thf(redefinition_k3_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ A ) )
     => ( ( k3_funct_2 @ A @ B @ C @ D )
        = ( k1_funct_1 @ C @ D ) ) ) )).

thf('240',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) ) )
      | ~ ( v1_funct_2 @ X5 @ X6 @ X7 )
      | ~ ( v1_funct_1 @ X5 )
      | ( v1_xboole_0 @ X6 )
      | ~ ( m1_subset_1 @ X8 @ X6 )
      | ( ( k3_funct_2 @ X6 @ X7 @ X5 @ X8 )
        = ( k1_funct_1 @ X5 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k3_funct_2])).

thf('241',plain,(
    ! [X0: $i] :
      ( ( ( k3_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ X0 )
        = ( k1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B_1 ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
      | ~ ( v1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) )
      | ~ ( v1_funct_2 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['239','240'])).

thf('242',plain,(
    v1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) ),
    inference(clc,[status(thm)],['28','29'])).

thf('243',plain,(
    v1_funct_2 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['20','21'])).

thf('244',plain,(
    ! [X0: $i] :
      ( ( ( k3_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ X0 )
        = ( k1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B_1 ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['241','242','243'])).

thf('245',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_C )
    | ( v2_struct_0 @ sk_B_1 )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( ( k3_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ ( sk_F @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_B_1 @ sk_B_1 @ sk_A ) )
      = ( k1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ ( sk_F @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_B_1 @ sk_B_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['238','244'])).

thf('246',plain,(
    ! [X37: $i,X38: $i,X39: $i,X40: $i,X41: $i] :
      ( ( v2_struct_0 @ X37 )
      | ~ ( v2_pre_topc @ X37 )
      | ~ ( l1_pre_topc @ X37 )
      | ~ ( v1_funct_1 @ X38 )
      | ~ ( v1_funct_2 @ X38 @ ( u1_struct_0 @ X37 ) @ ( u1_struct_0 @ X39 ) )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X37 ) @ ( u1_struct_0 @ X39 ) ) ) )
      | ( ( k3_funct_2 @ ( u1_struct_0 @ X37 ) @ ( u1_struct_0 @ X39 ) @ X38 @ ( sk_F @ X40 @ X38 @ X41 @ X37 @ X39 ) )
       != ( k1_funct_1 @ X40 @ ( sk_F @ X40 @ X38 @ X41 @ X37 @ X39 ) ) )
      | ( r2_funct_2 @ ( u1_struct_0 @ X41 ) @ ( u1_struct_0 @ X39 ) @ ( k2_tmap_1 @ X37 @ X39 @ X38 @ X41 ) @ X40 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X41 ) @ ( u1_struct_0 @ X39 ) ) ) )
      | ~ ( v1_funct_2 @ X40 @ ( u1_struct_0 @ X41 ) @ ( u1_struct_0 @ X39 ) )
      | ~ ( v1_funct_1 @ X40 )
      | ~ ( m1_pre_topc @ X41 @ X37 )
      | ( v2_struct_0 @ X41 )
      | ~ ( l1_pre_topc @ X39 )
      | ~ ( v2_pre_topc @ X39 )
      | ( v2_struct_0 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t59_tmap_1])).

thf('247',plain,
    ( ( ( k1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ ( sk_F @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_B_1 @ sk_B_1 @ sk_A ) )
     != ( k1_funct_1 @ sk_C @ ( sk_F @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_B_1 @ sk_B_1 @ sk_A ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_B_1 )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_B_1 )
    | ~ ( m1_pre_topc @ sk_B_1 @ sk_B_1 )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tmap_1 @ sk_B_1 @ sk_A @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_B_1 ) @ sk_C )
    | ~ ( m1_subset_1 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ~ ( v1_funct_2 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) )
    | ~ ( l1_pre_topc @ sk_B_1 )
    | ~ ( v2_pre_topc @ sk_B_1 )
    | ( v2_struct_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['245','246'])).

thf('248',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('249',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('250',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('251',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('252',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('253',plain,
    ( ( k4_tmap_1 @ sk_A @ sk_B_1 )
    = ( k2_tmap_1 @ sk_B_1 @ sk_A @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_B_1 ) ),
    inference(demod,[status(thm)],['110','134','158','181'])).

thf('254',plain,(
    m1_subset_1 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['8','9'])).

thf('255',plain,(
    v1_funct_2 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['20','21'])).

thf('256',plain,(
    v1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) ),
    inference(clc,[status(thm)],['28','29'])).

thf('257',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(demod,[status(thm)],['33','34'])).

thf('258',plain,(
    v2_pre_topc @ sk_B_1 ),
    inference(demod,[status(thm)],['38','39','40'])).

thf('259',plain,
    ( ( ( k1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ ( sk_F @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_B_1 @ sk_B_1 @ sk_A ) )
     != ( k1_funct_1 @ sk_C @ ( sk_F @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_B_1 @ sk_B_1 @ sk_A ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_B_1 )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B_1 )
    | ~ ( m1_pre_topc @ sk_B_1 @ sk_B_1 )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_C )
    | ( v2_struct_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['247','248','249','250','251','252','253','254','255','256','257','258'])).

thf('260',plain,
    ( ~ ( m1_pre_topc @ sk_B_1 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_C )
    | ( v2_struct_0 @ sk_B_1 )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( ( k1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ ( sk_F @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_B_1 @ sk_B_1 @ sk_A ) )
     != ( k1_funct_1 @ sk_C @ ( sk_F @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_B_1 @ sk_B_1 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['259'])).

thf('261',plain,
    ( ( ( sk_F @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_B_1 @ sk_B_1 @ sk_A )
     != ( k1_funct_1 @ sk_C @ ( sk_F @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_B_1 @ sk_B_1 @ sk_A ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_C )
    | ( v2_struct_0 @ sk_B_1 )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_B_1 )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ~ ( m1_pre_topc @ sk_B_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['237','260'])).

thf('262',plain,
    ( ~ ( m1_pre_topc @ sk_B_1 @ sk_B_1 )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_B_1 )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( ( sk_F @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_B_1 @ sk_B_1 @ sk_A )
     != ( k1_funct_1 @ sk_C @ ( sk_F @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_B_1 @ sk_B_1 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['261'])).

thf('263',plain,
    ( ( ( sk_F @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_B_1 @ sk_B_1 @ sk_A )
     != ( sk_F @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_B_1 @ sk_B_1 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_C )
    | ( v2_struct_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_C )
    | ( v2_struct_0 @ sk_B_1 )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ~ ( m1_pre_topc @ sk_B_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['226','262'])).

thf('264',plain,
    ( ~ ( m1_pre_topc @ sk_B_1 @ sk_B_1 )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_B_1 )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['263'])).

thf('265',plain,
    ( ~ ( l1_pre_topc @ sk_B_1 )
    | ( v2_struct_0 @ sk_A )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_C )
    | ( v2_struct_0 @ sk_B_1 )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['192','264'])).

thf('266',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(demod,[status(thm)],['33','34'])).

thf('267',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_C )
    | ( v2_struct_0 @ sk_B_1 )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['265','266'])).

thf('268',plain,(
    ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('269',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['267','268'])).

thf('270',plain,(
    ~ ( v2_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('271',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['269','270'])).

thf('272',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('273',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['271','272'])).

thf('274',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_C )
    | ( v2_struct_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['191','273'])).

thf('275',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('276',plain,
    ( ( v2_struct_0 @ sk_B_1 )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_C ) ),
    inference(clc,[status(thm)],['274','275'])).

thf('277',plain,(
    ~ ( v2_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('278',plain,(
    r2_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_C ),
    inference(clc,[status(thm)],['276','277'])).

thf('279',plain,(
    $false ),
    inference(demod,[status(thm)],['0','278'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.HFXoK4c9Wp
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:59:57 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.34  % Running in FO mode
% 2.25/2.44  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 2.25/2.44  % Solved by: fo/fo7.sh
% 2.25/2.44  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.25/2.44  % done 2931 iterations in 1.988s
% 2.25/2.44  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 2.25/2.44  % SZS output start Refutation
% 2.25/2.44  thf(sk_A_type, type, sk_A: $i).
% 2.25/2.44  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 2.25/2.44  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 2.25/2.44  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 2.25/2.44  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 2.25/2.44  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 2.25/2.44  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 2.25/2.44  thf(sk_F_type, type, sk_F: $i > $i > $i > $i > $i > $i).
% 2.25/2.44  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 2.25/2.44  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 2.25/2.44  thf(sk_C_type, type, sk_C: $i).
% 2.25/2.44  thf(k3_funct_2_type, type, k3_funct_2: $i > $i > $i > $i > $i).
% 2.25/2.44  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 2.25/2.44  thf(r2_funct_2_type, type, r2_funct_2: $i > $i > $i > $i > $o).
% 2.25/2.44  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 2.25/2.44  thf(k2_partfun1_type, type, k2_partfun1: $i > $i > $i > $i > $i).
% 2.25/2.44  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 2.25/2.44  thf(k3_tmap_1_type, type, k3_tmap_1: $i > $i > $i > $i > $i > $i).
% 2.25/2.44  thf(k2_tmap_1_type, type, k2_tmap_1: $i > $i > $i > $i > $i).
% 2.25/2.44  thf(k4_tmap_1_type, type, k4_tmap_1: $i > $i > $i).
% 2.25/2.44  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 2.25/2.44  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 2.25/2.44  thf(sk_B_1_type, type, sk_B_1: $i).
% 2.25/2.44  thf(t96_tmap_1, conjecture,
% 2.25/2.44    (![A:$i]:
% 2.25/2.44     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 2.25/2.44       ( ![B:$i]:
% 2.25/2.44         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 2.25/2.44           ( ![C:$i]:
% 2.25/2.44             ( ( ( v1_funct_1 @ C ) & 
% 2.25/2.44                 ( v1_funct_2 @ C @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 2.25/2.44                 ( m1_subset_1 @
% 2.25/2.44                   C @ 
% 2.25/2.44                   ( k1_zfmisc_1 @
% 2.25/2.44                     ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 2.25/2.44               ( ( ![D:$i]:
% 2.25/2.44                   ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 2.25/2.44                     ( ( r2_hidden @ D @ ( u1_struct_0 @ B ) ) =>
% 2.25/2.44                       ( ( D ) = ( k1_funct_1 @ C @ D ) ) ) ) ) =>
% 2.25/2.44                 ( r2_funct_2 @
% 2.25/2.44                   ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 2.25/2.44                   ( k4_tmap_1 @ A @ B ) @ C ) ) ) ) ) ) ))).
% 2.25/2.44  thf(zf_stmt_0, negated_conjecture,
% 2.25/2.44    (~( ![A:$i]:
% 2.25/2.44        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 2.25/2.44            ( l1_pre_topc @ A ) ) =>
% 2.25/2.44          ( ![B:$i]:
% 2.25/2.44            ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 2.25/2.44              ( ![C:$i]:
% 2.25/2.44                ( ( ( v1_funct_1 @ C ) & 
% 2.25/2.44                    ( v1_funct_2 @
% 2.25/2.44                      C @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 2.25/2.44                    ( m1_subset_1 @
% 2.25/2.44                      C @ 
% 2.25/2.44                      ( k1_zfmisc_1 @
% 2.25/2.44                        ( k2_zfmisc_1 @
% 2.25/2.44                          ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 2.25/2.44                  ( ( ![D:$i]:
% 2.25/2.44                      ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 2.25/2.44                        ( ( r2_hidden @ D @ ( u1_struct_0 @ B ) ) =>
% 2.25/2.44                          ( ( D ) = ( k1_funct_1 @ C @ D ) ) ) ) ) =>
% 2.25/2.44                    ( r2_funct_2 @
% 2.25/2.44                      ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 2.25/2.44                      ( k4_tmap_1 @ A @ B ) @ C ) ) ) ) ) ) ) )),
% 2.25/2.44    inference('cnf.neg', [status(esa)], [t96_tmap_1])).
% 2.25/2.44  thf('0', plain,
% 2.25/2.44      (~ (r2_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 2.25/2.44          (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_C)),
% 2.25/2.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.25/2.44  thf(t2_tsep_1, axiom,
% 2.25/2.44    (![A:$i]: ( ( l1_pre_topc @ A ) => ( m1_pre_topc @ A @ A ) ))).
% 2.25/2.44  thf('1', plain,
% 2.25/2.44      (![X36 : $i]: ((m1_pre_topc @ X36 @ X36) | ~ (l1_pre_topc @ X36))),
% 2.25/2.44      inference('cnf', [status(esa)], [t2_tsep_1])).
% 2.25/2.44  thf('2', plain,
% 2.25/2.44      ((m1_subset_1 @ sk_C @ 
% 2.25/2.44        (k1_zfmisc_1 @ 
% 2.25/2.44         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A))))),
% 2.25/2.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.25/2.44  thf('3', plain, ((m1_pre_topc @ sk_B_1 @ sk_A)),
% 2.25/2.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.25/2.44  thf(dt_k4_tmap_1, axiom,
% 2.25/2.44    (![A:$i,B:$i]:
% 2.25/2.44     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 2.25/2.44         ( l1_pre_topc @ A ) & ( m1_pre_topc @ B @ A ) ) =>
% 2.25/2.44       ( ( v1_funct_1 @ ( k4_tmap_1 @ A @ B ) ) & 
% 2.25/2.44         ( v1_funct_2 @
% 2.25/2.44           ( k4_tmap_1 @ A @ B ) @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 2.25/2.44         ( m1_subset_1 @
% 2.25/2.44           ( k4_tmap_1 @ A @ B ) @ 
% 2.25/2.44           ( k1_zfmisc_1 @
% 2.25/2.44             ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 2.25/2.44  thf('4', plain,
% 2.25/2.44      (![X34 : $i, X35 : $i]:
% 2.25/2.44         (~ (l1_pre_topc @ X34)
% 2.25/2.44          | ~ (v2_pre_topc @ X34)
% 2.25/2.44          | (v2_struct_0 @ X34)
% 2.25/2.44          | ~ (m1_pre_topc @ X35 @ X34)
% 2.25/2.44          | (m1_subset_1 @ (k4_tmap_1 @ X34 @ X35) @ 
% 2.25/2.44             (k1_zfmisc_1 @ 
% 2.25/2.44              (k2_zfmisc_1 @ (u1_struct_0 @ X35) @ (u1_struct_0 @ X34)))))),
% 2.25/2.44      inference('cnf', [status(esa)], [dt_k4_tmap_1])).
% 2.25/2.44  thf('5', plain,
% 2.25/2.44      (((m1_subset_1 @ (k4_tmap_1 @ sk_A @ sk_B_1) @ 
% 2.25/2.44         (k1_zfmisc_1 @ 
% 2.25/2.44          (k2_zfmisc_1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A))))
% 2.25/2.44        | (v2_struct_0 @ sk_A)
% 2.25/2.44        | ~ (v2_pre_topc @ sk_A)
% 2.25/2.44        | ~ (l1_pre_topc @ sk_A))),
% 2.25/2.44      inference('sup-', [status(thm)], ['3', '4'])).
% 2.25/2.44  thf('6', plain, ((v2_pre_topc @ sk_A)),
% 2.25/2.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.25/2.44  thf('7', plain, ((l1_pre_topc @ sk_A)),
% 2.25/2.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.25/2.44  thf('8', plain,
% 2.25/2.44      (((m1_subset_1 @ (k4_tmap_1 @ sk_A @ sk_B_1) @ 
% 2.25/2.44         (k1_zfmisc_1 @ 
% 2.25/2.44          (k2_zfmisc_1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A))))
% 2.25/2.44        | (v2_struct_0 @ sk_A))),
% 2.25/2.44      inference('demod', [status(thm)], ['5', '6', '7'])).
% 2.25/2.44  thf('9', plain, (~ (v2_struct_0 @ sk_A)),
% 2.25/2.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.25/2.44  thf('10', plain,
% 2.25/2.44      ((m1_subset_1 @ (k4_tmap_1 @ sk_A @ sk_B_1) @ 
% 2.25/2.44        (k1_zfmisc_1 @ 
% 2.25/2.44         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A))))),
% 2.25/2.44      inference('clc', [status(thm)], ['8', '9'])).
% 2.25/2.44  thf(t59_tmap_1, axiom,
% 2.25/2.44    (![A:$i]:
% 2.25/2.44     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 2.25/2.44       ( ![B:$i]:
% 2.25/2.44         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 2.25/2.44             ( l1_pre_topc @ B ) ) =>
% 2.25/2.44           ( ![C:$i]:
% 2.25/2.44             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ B ) ) =>
% 2.25/2.44               ( ![D:$i]:
% 2.25/2.44                 ( ( ( v1_funct_1 @ D ) & 
% 2.25/2.44                     ( v1_funct_2 @
% 2.25/2.44                       D @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 2.25/2.44                     ( m1_subset_1 @
% 2.25/2.44                       D @ 
% 2.25/2.44                       ( k1_zfmisc_1 @
% 2.25/2.44                         ( k2_zfmisc_1 @
% 2.25/2.44                           ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 2.25/2.44                   ( ![E:$i]:
% 2.25/2.44                     ( ( ( v1_funct_1 @ E ) & 
% 2.25/2.44                         ( v1_funct_2 @
% 2.25/2.44                           E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ A ) ) & 
% 2.25/2.44                         ( m1_subset_1 @
% 2.25/2.44                           E @ 
% 2.25/2.44                           ( k1_zfmisc_1 @
% 2.25/2.44                             ( k2_zfmisc_1 @
% 2.25/2.44                               ( u1_struct_0 @ C ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 2.25/2.44                       ( ( ![F:$i]:
% 2.25/2.44                           ( ( m1_subset_1 @ F @ ( u1_struct_0 @ B ) ) =>
% 2.25/2.44                             ( ( r2_hidden @ F @ ( u1_struct_0 @ C ) ) =>
% 2.25/2.44                               ( ( k3_funct_2 @
% 2.25/2.44                                   ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 2.25/2.44                                   D @ F ) =
% 2.25/2.44                                 ( k1_funct_1 @ E @ F ) ) ) ) ) =>
% 2.25/2.44                         ( r2_funct_2 @
% 2.25/2.44                           ( u1_struct_0 @ C ) @ ( u1_struct_0 @ A ) @ 
% 2.25/2.44                           ( k2_tmap_1 @ B @ A @ D @ C ) @ E ) ) ) ) ) ) ) ) ) ) ))).
% 2.25/2.44  thf('11', plain,
% 2.25/2.44      (![X37 : $i, X38 : $i, X39 : $i, X40 : $i, X41 : $i]:
% 2.25/2.44         ((v2_struct_0 @ X37)
% 2.25/2.44          | ~ (v2_pre_topc @ X37)
% 2.25/2.44          | ~ (l1_pre_topc @ X37)
% 2.25/2.44          | ~ (v1_funct_1 @ X38)
% 2.25/2.44          | ~ (v1_funct_2 @ X38 @ (u1_struct_0 @ X37) @ (u1_struct_0 @ X39))
% 2.25/2.44          | ~ (m1_subset_1 @ X38 @ 
% 2.25/2.44               (k1_zfmisc_1 @ 
% 2.25/2.44                (k2_zfmisc_1 @ (u1_struct_0 @ X37) @ (u1_struct_0 @ X39))))
% 2.25/2.44          | (r2_hidden @ (sk_F @ X40 @ X38 @ X41 @ X37 @ X39) @ 
% 2.25/2.44             (u1_struct_0 @ X41))
% 2.25/2.44          | (r2_funct_2 @ (u1_struct_0 @ X41) @ (u1_struct_0 @ X39) @ 
% 2.25/2.44             (k2_tmap_1 @ X37 @ X39 @ X38 @ X41) @ X40)
% 2.25/2.44          | ~ (m1_subset_1 @ X40 @ 
% 2.25/2.44               (k1_zfmisc_1 @ 
% 2.25/2.44                (k2_zfmisc_1 @ (u1_struct_0 @ X41) @ (u1_struct_0 @ X39))))
% 2.25/2.44          | ~ (v1_funct_2 @ X40 @ (u1_struct_0 @ X41) @ (u1_struct_0 @ X39))
% 2.25/2.44          | ~ (v1_funct_1 @ X40)
% 2.25/2.44          | ~ (m1_pre_topc @ X41 @ X37)
% 2.25/2.44          | (v2_struct_0 @ X41)
% 2.25/2.44          | ~ (l1_pre_topc @ X39)
% 2.25/2.44          | ~ (v2_pre_topc @ X39)
% 2.25/2.44          | (v2_struct_0 @ X39))),
% 2.25/2.44      inference('cnf', [status(esa)], [t59_tmap_1])).
% 2.25/2.44  thf('12', plain,
% 2.25/2.44      (![X0 : $i, X1 : $i]:
% 2.25/2.44         ((v2_struct_0 @ sk_A)
% 2.25/2.44          | ~ (v2_pre_topc @ sk_A)
% 2.25/2.44          | ~ (l1_pre_topc @ sk_A)
% 2.25/2.44          | (v2_struct_0 @ X0)
% 2.25/2.44          | ~ (m1_pre_topc @ X0 @ sk_B_1)
% 2.25/2.44          | ~ (v1_funct_1 @ X1)
% 2.25/2.44          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A))
% 2.25/2.44          | ~ (m1_subset_1 @ X1 @ 
% 2.25/2.44               (k1_zfmisc_1 @ 
% 2.25/2.44                (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A))))
% 2.25/2.44          | (r2_funct_2 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A) @ 
% 2.25/2.44             (k2_tmap_1 @ sk_B_1 @ sk_A @ (k4_tmap_1 @ sk_A @ sk_B_1) @ X0) @ 
% 2.25/2.44             X1)
% 2.25/2.44          | (r2_hidden @ 
% 2.25/2.44             (sk_F @ X1 @ (k4_tmap_1 @ sk_A @ sk_B_1) @ X0 @ sk_B_1 @ sk_A) @ 
% 2.25/2.44             (u1_struct_0 @ X0))
% 2.25/2.44          | ~ (v1_funct_2 @ (k4_tmap_1 @ sk_A @ sk_B_1) @ 
% 2.25/2.44               (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A))
% 2.25/2.44          | ~ (v1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_B_1))
% 2.25/2.44          | ~ (l1_pre_topc @ sk_B_1)
% 2.25/2.44          | ~ (v2_pre_topc @ sk_B_1)
% 2.25/2.44          | (v2_struct_0 @ sk_B_1))),
% 2.25/2.44      inference('sup-', [status(thm)], ['10', '11'])).
% 2.25/2.44  thf('13', plain, ((v2_pre_topc @ sk_A)),
% 2.25/2.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.25/2.44  thf('14', plain, ((l1_pre_topc @ sk_A)),
% 2.25/2.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.25/2.44  thf('15', plain, ((m1_pre_topc @ sk_B_1 @ sk_A)),
% 2.25/2.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.25/2.44  thf('16', plain,
% 2.25/2.44      (![X34 : $i, X35 : $i]:
% 2.25/2.44         (~ (l1_pre_topc @ X34)
% 2.25/2.44          | ~ (v2_pre_topc @ X34)
% 2.25/2.44          | (v2_struct_0 @ X34)
% 2.25/2.44          | ~ (m1_pre_topc @ X35 @ X34)
% 2.25/2.44          | (v1_funct_2 @ (k4_tmap_1 @ X34 @ X35) @ (u1_struct_0 @ X35) @ 
% 2.25/2.44             (u1_struct_0 @ X34)))),
% 2.25/2.44      inference('cnf', [status(esa)], [dt_k4_tmap_1])).
% 2.25/2.44  thf('17', plain,
% 2.25/2.44      (((v1_funct_2 @ (k4_tmap_1 @ sk_A @ sk_B_1) @ (u1_struct_0 @ sk_B_1) @ 
% 2.25/2.44         (u1_struct_0 @ sk_A))
% 2.25/2.44        | (v2_struct_0 @ sk_A)
% 2.25/2.44        | ~ (v2_pre_topc @ sk_A)
% 2.25/2.44        | ~ (l1_pre_topc @ sk_A))),
% 2.25/2.44      inference('sup-', [status(thm)], ['15', '16'])).
% 2.25/2.44  thf('18', plain, ((v2_pre_topc @ sk_A)),
% 2.25/2.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.25/2.44  thf('19', plain, ((l1_pre_topc @ sk_A)),
% 2.25/2.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.25/2.44  thf('20', plain,
% 2.25/2.44      (((v1_funct_2 @ (k4_tmap_1 @ sk_A @ sk_B_1) @ (u1_struct_0 @ sk_B_1) @ 
% 2.25/2.44         (u1_struct_0 @ sk_A))
% 2.25/2.44        | (v2_struct_0 @ sk_A))),
% 2.25/2.44      inference('demod', [status(thm)], ['17', '18', '19'])).
% 2.25/2.44  thf('21', plain, (~ (v2_struct_0 @ sk_A)),
% 2.25/2.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.25/2.44  thf('22', plain,
% 2.25/2.44      ((v1_funct_2 @ (k4_tmap_1 @ sk_A @ sk_B_1) @ (u1_struct_0 @ sk_B_1) @ 
% 2.25/2.44        (u1_struct_0 @ sk_A))),
% 2.25/2.44      inference('clc', [status(thm)], ['20', '21'])).
% 2.25/2.44  thf('23', plain, ((m1_pre_topc @ sk_B_1 @ sk_A)),
% 2.25/2.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.25/2.44  thf('24', plain,
% 2.25/2.44      (![X34 : $i, X35 : $i]:
% 2.25/2.44         (~ (l1_pre_topc @ X34)
% 2.25/2.44          | ~ (v2_pre_topc @ X34)
% 2.25/2.44          | (v2_struct_0 @ X34)
% 2.25/2.44          | ~ (m1_pre_topc @ X35 @ X34)
% 2.25/2.44          | (v1_funct_1 @ (k4_tmap_1 @ X34 @ X35)))),
% 2.25/2.44      inference('cnf', [status(esa)], [dt_k4_tmap_1])).
% 2.25/2.44  thf('25', plain,
% 2.25/2.44      (((v1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_B_1))
% 2.25/2.44        | (v2_struct_0 @ sk_A)
% 2.25/2.44        | ~ (v2_pre_topc @ sk_A)
% 2.25/2.44        | ~ (l1_pre_topc @ sk_A))),
% 2.25/2.44      inference('sup-', [status(thm)], ['23', '24'])).
% 2.25/2.44  thf('26', plain, ((v2_pre_topc @ sk_A)),
% 2.25/2.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.25/2.44  thf('27', plain, ((l1_pre_topc @ sk_A)),
% 2.25/2.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.25/2.44  thf('28', plain,
% 2.25/2.44      (((v1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_B_1)) | (v2_struct_0 @ sk_A))),
% 2.25/2.44      inference('demod', [status(thm)], ['25', '26', '27'])).
% 2.25/2.44  thf('29', plain, (~ (v2_struct_0 @ sk_A)),
% 2.25/2.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.25/2.44  thf('30', plain, ((v1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_B_1))),
% 2.25/2.44      inference('clc', [status(thm)], ['28', '29'])).
% 2.25/2.44  thf('31', plain, ((m1_pre_topc @ sk_B_1 @ sk_A)),
% 2.25/2.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.25/2.44  thf(dt_m1_pre_topc, axiom,
% 2.25/2.44    (![A:$i]:
% 2.25/2.44     ( ( l1_pre_topc @ A ) =>
% 2.25/2.44       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 2.25/2.44  thf('32', plain,
% 2.25/2.44      (![X15 : $i, X16 : $i]:
% 2.25/2.44         (~ (m1_pre_topc @ X15 @ X16)
% 2.25/2.44          | (l1_pre_topc @ X15)
% 2.25/2.44          | ~ (l1_pre_topc @ X16))),
% 2.25/2.44      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 2.25/2.44  thf('33', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_B_1))),
% 2.25/2.44      inference('sup-', [status(thm)], ['31', '32'])).
% 2.25/2.44  thf('34', plain, ((l1_pre_topc @ sk_A)),
% 2.25/2.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.25/2.44  thf('35', plain, ((l1_pre_topc @ sk_B_1)),
% 2.25/2.44      inference('demod', [status(thm)], ['33', '34'])).
% 2.25/2.44  thf('36', plain, ((m1_pre_topc @ sk_B_1 @ sk_A)),
% 2.25/2.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.25/2.44  thf(cc1_pre_topc, axiom,
% 2.25/2.44    (![A:$i]:
% 2.25/2.44     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 2.25/2.44       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( v2_pre_topc @ B ) ) ) ))).
% 2.25/2.44  thf('37', plain,
% 2.25/2.44      (![X13 : $i, X14 : $i]:
% 2.25/2.44         (~ (m1_pre_topc @ X13 @ X14)
% 2.25/2.44          | (v2_pre_topc @ X13)
% 2.25/2.44          | ~ (l1_pre_topc @ X14)
% 2.25/2.44          | ~ (v2_pre_topc @ X14))),
% 2.25/2.44      inference('cnf', [status(esa)], [cc1_pre_topc])).
% 2.25/2.44  thf('38', plain,
% 2.25/2.44      ((~ (v2_pre_topc @ sk_A)
% 2.25/2.44        | ~ (l1_pre_topc @ sk_A)
% 2.25/2.44        | (v2_pre_topc @ sk_B_1))),
% 2.25/2.44      inference('sup-', [status(thm)], ['36', '37'])).
% 2.25/2.44  thf('39', plain, ((v2_pre_topc @ sk_A)),
% 2.25/2.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.25/2.44  thf('40', plain, ((l1_pre_topc @ sk_A)),
% 2.25/2.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.25/2.44  thf('41', plain, ((v2_pre_topc @ sk_B_1)),
% 2.25/2.44      inference('demod', [status(thm)], ['38', '39', '40'])).
% 2.25/2.44  thf('42', plain,
% 2.25/2.44      (![X0 : $i, X1 : $i]:
% 2.25/2.44         ((v2_struct_0 @ sk_A)
% 2.25/2.44          | (v2_struct_0 @ X0)
% 2.25/2.44          | ~ (m1_pre_topc @ X0 @ sk_B_1)
% 2.25/2.44          | ~ (v1_funct_1 @ X1)
% 2.25/2.44          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A))
% 2.25/2.44          | ~ (m1_subset_1 @ X1 @ 
% 2.25/2.44               (k1_zfmisc_1 @ 
% 2.25/2.44                (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A))))
% 2.25/2.44          | (r2_funct_2 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A) @ 
% 2.25/2.44             (k2_tmap_1 @ sk_B_1 @ sk_A @ (k4_tmap_1 @ sk_A @ sk_B_1) @ X0) @ 
% 2.25/2.44             X1)
% 2.25/2.44          | (r2_hidden @ 
% 2.25/2.44             (sk_F @ X1 @ (k4_tmap_1 @ sk_A @ sk_B_1) @ X0 @ sk_B_1 @ sk_A) @ 
% 2.25/2.44             (u1_struct_0 @ X0))
% 2.25/2.44          | (v2_struct_0 @ sk_B_1))),
% 2.25/2.44      inference('demod', [status(thm)],
% 2.25/2.44                ['12', '13', '14', '22', '30', '35', '41'])).
% 2.25/2.44  thf('43', plain,
% 2.25/2.44      (((v2_struct_0 @ sk_B_1)
% 2.25/2.44        | (r2_hidden @ 
% 2.25/2.44           (sk_F @ sk_C @ (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_B_1 @ sk_B_1 @ sk_A) @ 
% 2.25/2.44           (u1_struct_0 @ sk_B_1))
% 2.25/2.44        | (r2_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 2.25/2.44           (k2_tmap_1 @ sk_B_1 @ sk_A @ (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_B_1) @ 
% 2.25/2.44           sk_C)
% 2.25/2.44        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A))
% 2.25/2.44        | ~ (v1_funct_1 @ sk_C)
% 2.25/2.44        | ~ (m1_pre_topc @ sk_B_1 @ sk_B_1)
% 2.25/2.44        | (v2_struct_0 @ sk_B_1)
% 2.25/2.44        | (v2_struct_0 @ sk_A))),
% 2.25/2.44      inference('sup-', [status(thm)], ['2', '42'])).
% 2.25/2.44  thf('44', plain,
% 2.25/2.44      (![X36 : $i]: ((m1_pre_topc @ X36 @ X36) | ~ (l1_pre_topc @ X36))),
% 2.25/2.44      inference('cnf', [status(esa)], [t2_tsep_1])).
% 2.25/2.44  thf('45', plain,
% 2.25/2.44      ((m1_subset_1 @ (k4_tmap_1 @ sk_A @ sk_B_1) @ 
% 2.25/2.44        (k1_zfmisc_1 @ 
% 2.25/2.44         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A))))),
% 2.25/2.44      inference('clc', [status(thm)], ['8', '9'])).
% 2.25/2.44  thf(t74_tmap_1, axiom,
% 2.25/2.44    (![A:$i]:
% 2.25/2.44     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 2.25/2.44       ( ![B:$i]:
% 2.25/2.44         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 2.25/2.44             ( l1_pre_topc @ B ) ) =>
% 2.25/2.44           ( ![C:$i]:
% 2.25/2.44             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 2.25/2.44               ( ![D:$i]:
% 2.25/2.44                 ( ( ( v1_funct_1 @ D ) & 
% 2.25/2.44                     ( v1_funct_2 @
% 2.25/2.44                       D @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 2.25/2.44                     ( m1_subset_1 @
% 2.25/2.44                       D @ 
% 2.25/2.44                       ( k1_zfmisc_1 @
% 2.25/2.44                         ( k2_zfmisc_1 @
% 2.25/2.44                           ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 2.25/2.44                   ( r2_funct_2 @
% 2.25/2.44                     ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ D @ 
% 2.25/2.44                     ( k3_tmap_1 @ A @ B @ C @ C @ D ) ) ) ) ) ) ) ) ))).
% 2.25/2.44  thf('46', plain,
% 2.25/2.44      (![X42 : $i, X43 : $i, X44 : $i, X45 : $i]:
% 2.25/2.44         ((v2_struct_0 @ X42)
% 2.25/2.44          | ~ (v2_pre_topc @ X42)
% 2.25/2.44          | ~ (l1_pre_topc @ X42)
% 2.25/2.44          | ~ (v1_funct_1 @ X43)
% 2.25/2.44          | ~ (v1_funct_2 @ X43 @ (u1_struct_0 @ X44) @ (u1_struct_0 @ X42))
% 2.25/2.44          | ~ (m1_subset_1 @ X43 @ 
% 2.25/2.44               (k1_zfmisc_1 @ 
% 2.25/2.44                (k2_zfmisc_1 @ (u1_struct_0 @ X44) @ (u1_struct_0 @ X42))))
% 2.25/2.44          | (r2_funct_2 @ (u1_struct_0 @ X44) @ (u1_struct_0 @ X42) @ X43 @ 
% 2.25/2.44             (k3_tmap_1 @ X45 @ X42 @ X44 @ X44 @ X43))
% 2.25/2.44          | ~ (m1_pre_topc @ X44 @ X45)
% 2.25/2.44          | (v2_struct_0 @ X44)
% 2.25/2.44          | ~ (l1_pre_topc @ X45)
% 2.25/2.44          | ~ (v2_pre_topc @ X45)
% 2.25/2.44          | (v2_struct_0 @ X45))),
% 2.25/2.44      inference('cnf', [status(esa)], [t74_tmap_1])).
% 2.25/2.44  thf('47', plain,
% 2.25/2.44      (![X0 : $i]:
% 2.25/2.44         ((v2_struct_0 @ X0)
% 2.25/2.44          | ~ (v2_pre_topc @ X0)
% 2.25/2.44          | ~ (l1_pre_topc @ X0)
% 2.25/2.44          | (v2_struct_0 @ sk_B_1)
% 2.25/2.44          | ~ (m1_pre_topc @ sk_B_1 @ X0)
% 2.25/2.44          | (r2_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 2.25/2.44             (k4_tmap_1 @ sk_A @ sk_B_1) @ 
% 2.25/2.44             (k3_tmap_1 @ X0 @ sk_A @ sk_B_1 @ sk_B_1 @ 
% 2.25/2.44              (k4_tmap_1 @ sk_A @ sk_B_1)))
% 2.25/2.44          | ~ (v1_funct_2 @ (k4_tmap_1 @ sk_A @ sk_B_1) @ 
% 2.25/2.44               (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A))
% 2.25/2.44          | ~ (v1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_B_1))
% 2.25/2.44          | ~ (l1_pre_topc @ sk_A)
% 2.25/2.44          | ~ (v2_pre_topc @ sk_A)
% 2.25/2.44          | (v2_struct_0 @ sk_A))),
% 2.25/2.44      inference('sup-', [status(thm)], ['45', '46'])).
% 2.25/2.44  thf('48', plain,
% 2.25/2.44      ((v1_funct_2 @ (k4_tmap_1 @ sk_A @ sk_B_1) @ (u1_struct_0 @ sk_B_1) @ 
% 2.25/2.44        (u1_struct_0 @ sk_A))),
% 2.25/2.44      inference('clc', [status(thm)], ['20', '21'])).
% 2.25/2.44  thf('49', plain, ((v1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_B_1))),
% 2.25/2.44      inference('clc', [status(thm)], ['28', '29'])).
% 2.25/2.44  thf('50', plain, ((l1_pre_topc @ sk_A)),
% 2.25/2.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.25/2.44  thf('51', plain, ((v2_pre_topc @ sk_A)),
% 2.25/2.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.25/2.44  thf('52', plain,
% 2.25/2.44      (![X0 : $i]:
% 2.25/2.44         ((v2_struct_0 @ X0)
% 2.25/2.44          | ~ (v2_pre_topc @ X0)
% 2.25/2.44          | ~ (l1_pre_topc @ X0)
% 2.25/2.44          | (v2_struct_0 @ sk_B_1)
% 2.25/2.44          | ~ (m1_pre_topc @ sk_B_1 @ X0)
% 2.25/2.44          | (r2_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 2.25/2.44             (k4_tmap_1 @ sk_A @ sk_B_1) @ 
% 2.25/2.44             (k3_tmap_1 @ X0 @ sk_A @ sk_B_1 @ sk_B_1 @ 
% 2.25/2.44              (k4_tmap_1 @ sk_A @ sk_B_1)))
% 2.25/2.44          | (v2_struct_0 @ sk_A))),
% 2.25/2.44      inference('demod', [status(thm)], ['47', '48', '49', '50', '51'])).
% 2.25/2.44  thf('53', plain,
% 2.25/2.44      ((~ (l1_pre_topc @ sk_B_1)
% 2.25/2.44        | (v2_struct_0 @ sk_A)
% 2.25/2.44        | (r2_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 2.25/2.44           (k4_tmap_1 @ sk_A @ sk_B_1) @ 
% 2.25/2.44           (k3_tmap_1 @ sk_B_1 @ sk_A @ sk_B_1 @ sk_B_1 @ 
% 2.25/2.44            (k4_tmap_1 @ sk_A @ sk_B_1)))
% 2.25/2.44        | (v2_struct_0 @ sk_B_1)
% 2.25/2.44        | ~ (l1_pre_topc @ sk_B_1)
% 2.25/2.44        | ~ (v2_pre_topc @ sk_B_1)
% 2.25/2.44        | (v2_struct_0 @ sk_B_1))),
% 2.25/2.44      inference('sup-', [status(thm)], ['44', '52'])).
% 2.25/2.44  thf('54', plain, ((l1_pre_topc @ sk_B_1)),
% 2.25/2.44      inference('demod', [status(thm)], ['33', '34'])).
% 2.25/2.44  thf('55', plain,
% 2.25/2.44      (![X36 : $i]: ((m1_pre_topc @ X36 @ X36) | ~ (l1_pre_topc @ X36))),
% 2.25/2.44      inference('cnf', [status(esa)], [t2_tsep_1])).
% 2.25/2.44  thf('56', plain,
% 2.25/2.44      (![X36 : $i]: ((m1_pre_topc @ X36 @ X36) | ~ (l1_pre_topc @ X36))),
% 2.25/2.44      inference('cnf', [status(esa)], [t2_tsep_1])).
% 2.25/2.44  thf('57', plain,
% 2.25/2.44      ((m1_subset_1 @ (k4_tmap_1 @ sk_A @ sk_B_1) @ 
% 2.25/2.44        (k1_zfmisc_1 @ 
% 2.25/2.44         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A))))),
% 2.25/2.44      inference('clc', [status(thm)], ['8', '9'])).
% 2.25/2.44  thf(d5_tmap_1, axiom,
% 2.25/2.44    (![A:$i]:
% 2.25/2.44     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 2.25/2.44       ( ![B:$i]:
% 2.25/2.44         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 2.25/2.44             ( l1_pre_topc @ B ) ) =>
% 2.25/2.44           ( ![C:$i]:
% 2.25/2.44             ( ( m1_pre_topc @ C @ A ) =>
% 2.25/2.44               ( ![D:$i]:
% 2.25/2.44                 ( ( m1_pre_topc @ D @ A ) =>
% 2.25/2.44                   ( ![E:$i]:
% 2.25/2.44                     ( ( ( v1_funct_1 @ E ) & 
% 2.25/2.44                         ( v1_funct_2 @
% 2.25/2.44                           E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 2.25/2.44                         ( m1_subset_1 @
% 2.25/2.44                           E @ 
% 2.25/2.44                           ( k1_zfmisc_1 @
% 2.25/2.44                             ( k2_zfmisc_1 @
% 2.25/2.44                               ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 2.25/2.44                       ( ( m1_pre_topc @ D @ C ) =>
% 2.25/2.44                         ( ( k3_tmap_1 @ A @ B @ C @ D @ E ) =
% 2.25/2.44                           ( k2_partfun1 @
% 2.25/2.44                             ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ E @ 
% 2.25/2.44                             ( u1_struct_0 @ D ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 2.25/2.44  thf('58', plain,
% 2.25/2.44      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 2.25/2.44         ((v2_struct_0 @ X24)
% 2.25/2.44          | ~ (v2_pre_topc @ X24)
% 2.25/2.44          | ~ (l1_pre_topc @ X24)
% 2.25/2.44          | ~ (m1_pre_topc @ X25 @ X26)
% 2.25/2.44          | ~ (m1_pre_topc @ X25 @ X27)
% 2.25/2.44          | ((k3_tmap_1 @ X26 @ X24 @ X27 @ X25 @ X28)
% 2.25/2.44              = (k2_partfun1 @ (u1_struct_0 @ X27) @ (u1_struct_0 @ X24) @ 
% 2.25/2.44                 X28 @ (u1_struct_0 @ X25)))
% 2.25/2.44          | ~ (m1_subset_1 @ X28 @ 
% 2.25/2.44               (k1_zfmisc_1 @ 
% 2.25/2.44                (k2_zfmisc_1 @ (u1_struct_0 @ X27) @ (u1_struct_0 @ X24))))
% 2.25/2.44          | ~ (v1_funct_2 @ X28 @ (u1_struct_0 @ X27) @ (u1_struct_0 @ X24))
% 2.25/2.44          | ~ (v1_funct_1 @ X28)
% 2.25/2.44          | ~ (m1_pre_topc @ X27 @ X26)
% 2.25/2.44          | ~ (l1_pre_topc @ X26)
% 2.25/2.44          | ~ (v2_pre_topc @ X26)
% 2.25/2.44          | (v2_struct_0 @ X26))),
% 2.25/2.44      inference('cnf', [status(esa)], [d5_tmap_1])).
% 2.25/2.44  thf('59', plain,
% 2.25/2.44      (![X0 : $i, X1 : $i]:
% 2.25/2.44         ((v2_struct_0 @ X0)
% 2.25/2.44          | ~ (v2_pre_topc @ X0)
% 2.25/2.44          | ~ (l1_pre_topc @ X0)
% 2.25/2.44          | ~ (m1_pre_topc @ sk_B_1 @ X0)
% 2.25/2.44          | ~ (v1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_B_1))
% 2.25/2.44          | ~ (v1_funct_2 @ (k4_tmap_1 @ sk_A @ sk_B_1) @ 
% 2.25/2.44               (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A))
% 2.25/2.44          | ((k3_tmap_1 @ X0 @ sk_A @ sk_B_1 @ X1 @ (k4_tmap_1 @ sk_A @ sk_B_1))
% 2.25/2.44              = (k2_partfun1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 2.25/2.44                 (k4_tmap_1 @ sk_A @ sk_B_1) @ (u1_struct_0 @ X1)))
% 2.25/2.44          | ~ (m1_pre_topc @ X1 @ sk_B_1)
% 2.25/2.44          | ~ (m1_pre_topc @ X1 @ X0)
% 2.25/2.44          | ~ (l1_pre_topc @ sk_A)
% 2.25/2.44          | ~ (v2_pre_topc @ sk_A)
% 2.25/2.44          | (v2_struct_0 @ sk_A))),
% 2.25/2.44      inference('sup-', [status(thm)], ['57', '58'])).
% 2.25/2.44  thf('60', plain, ((v1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_B_1))),
% 2.25/2.44      inference('clc', [status(thm)], ['28', '29'])).
% 2.25/2.44  thf('61', plain,
% 2.25/2.44      ((v1_funct_2 @ (k4_tmap_1 @ sk_A @ sk_B_1) @ (u1_struct_0 @ sk_B_1) @ 
% 2.25/2.44        (u1_struct_0 @ sk_A))),
% 2.25/2.44      inference('clc', [status(thm)], ['20', '21'])).
% 2.25/2.44  thf('62', plain, ((l1_pre_topc @ sk_A)),
% 2.25/2.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.25/2.44  thf('63', plain, ((v2_pre_topc @ sk_A)),
% 2.25/2.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.25/2.44  thf('64', plain,
% 2.25/2.44      (![X0 : $i, X1 : $i]:
% 2.25/2.44         ((v2_struct_0 @ X0)
% 2.25/2.44          | ~ (v2_pre_topc @ X0)
% 2.25/2.44          | ~ (l1_pre_topc @ X0)
% 2.25/2.44          | ~ (m1_pre_topc @ sk_B_1 @ X0)
% 2.25/2.44          | ((k3_tmap_1 @ X0 @ sk_A @ sk_B_1 @ X1 @ (k4_tmap_1 @ sk_A @ sk_B_1))
% 2.25/2.44              = (k2_partfun1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 2.25/2.44                 (k4_tmap_1 @ sk_A @ sk_B_1) @ (u1_struct_0 @ X1)))
% 2.25/2.44          | ~ (m1_pre_topc @ X1 @ sk_B_1)
% 2.25/2.44          | ~ (m1_pre_topc @ X1 @ X0)
% 2.25/2.44          | (v2_struct_0 @ sk_A))),
% 2.25/2.44      inference('demod', [status(thm)], ['59', '60', '61', '62', '63'])).
% 2.25/2.44  thf('65', plain,
% 2.25/2.44      (![X0 : $i]:
% 2.25/2.44         (~ (l1_pre_topc @ sk_B_1)
% 2.25/2.44          | (v2_struct_0 @ sk_A)
% 2.25/2.44          | ~ (m1_pre_topc @ X0 @ sk_B_1)
% 2.25/2.44          | ~ (m1_pre_topc @ X0 @ sk_B_1)
% 2.25/2.44          | ((k3_tmap_1 @ sk_B_1 @ sk_A @ sk_B_1 @ X0 @ 
% 2.25/2.44              (k4_tmap_1 @ sk_A @ sk_B_1))
% 2.25/2.44              = (k2_partfun1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 2.25/2.44                 (k4_tmap_1 @ sk_A @ sk_B_1) @ (u1_struct_0 @ X0)))
% 2.25/2.44          | ~ (l1_pre_topc @ sk_B_1)
% 2.25/2.44          | ~ (v2_pre_topc @ sk_B_1)
% 2.25/2.44          | (v2_struct_0 @ sk_B_1))),
% 2.25/2.44      inference('sup-', [status(thm)], ['56', '64'])).
% 2.25/2.44  thf('66', plain, ((l1_pre_topc @ sk_B_1)),
% 2.25/2.44      inference('demod', [status(thm)], ['33', '34'])).
% 2.25/2.44  thf('67', plain, ((l1_pre_topc @ sk_B_1)),
% 2.25/2.44      inference('demod', [status(thm)], ['33', '34'])).
% 2.25/2.44  thf('68', plain, ((v2_pre_topc @ sk_B_1)),
% 2.25/2.44      inference('demod', [status(thm)], ['38', '39', '40'])).
% 2.25/2.44  thf('69', plain,
% 2.25/2.44      (![X0 : $i]:
% 2.25/2.44         ((v2_struct_0 @ sk_A)
% 2.25/2.44          | ~ (m1_pre_topc @ X0 @ sk_B_1)
% 2.25/2.44          | ~ (m1_pre_topc @ X0 @ sk_B_1)
% 2.25/2.44          | ((k3_tmap_1 @ sk_B_1 @ sk_A @ sk_B_1 @ X0 @ 
% 2.25/2.44              (k4_tmap_1 @ sk_A @ sk_B_1))
% 2.25/2.44              = (k2_partfun1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 2.25/2.44                 (k4_tmap_1 @ sk_A @ sk_B_1) @ (u1_struct_0 @ X0)))
% 2.25/2.44          | (v2_struct_0 @ sk_B_1))),
% 2.25/2.44      inference('demod', [status(thm)], ['65', '66', '67', '68'])).
% 2.25/2.44  thf('70', plain,
% 2.25/2.44      (![X0 : $i]:
% 2.25/2.44         ((v2_struct_0 @ sk_B_1)
% 2.25/2.44          | ((k3_tmap_1 @ sk_B_1 @ sk_A @ sk_B_1 @ X0 @ 
% 2.25/2.44              (k4_tmap_1 @ sk_A @ sk_B_1))
% 2.25/2.44              = (k2_partfun1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 2.25/2.44                 (k4_tmap_1 @ sk_A @ sk_B_1) @ (u1_struct_0 @ X0)))
% 2.25/2.44          | ~ (m1_pre_topc @ X0 @ sk_B_1)
% 2.25/2.44          | (v2_struct_0 @ sk_A))),
% 2.25/2.44      inference('simplify', [status(thm)], ['69'])).
% 2.25/2.44  thf('71', plain,
% 2.25/2.44      ((~ (l1_pre_topc @ sk_B_1)
% 2.25/2.44        | (v2_struct_0 @ sk_A)
% 2.25/2.44        | ((k3_tmap_1 @ sk_B_1 @ sk_A @ sk_B_1 @ sk_B_1 @ 
% 2.25/2.44            (k4_tmap_1 @ sk_A @ sk_B_1))
% 2.25/2.44            = (k2_partfun1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 2.25/2.44               (k4_tmap_1 @ sk_A @ sk_B_1) @ (u1_struct_0 @ sk_B_1)))
% 2.25/2.44        | (v2_struct_0 @ sk_B_1))),
% 2.25/2.44      inference('sup-', [status(thm)], ['55', '70'])).
% 2.25/2.44  thf('72', plain, ((l1_pre_topc @ sk_B_1)),
% 2.25/2.44      inference('demod', [status(thm)], ['33', '34'])).
% 2.25/2.44  thf('73', plain,
% 2.25/2.44      (![X36 : $i]: ((m1_pre_topc @ X36 @ X36) | ~ (l1_pre_topc @ X36))),
% 2.25/2.44      inference('cnf', [status(esa)], [t2_tsep_1])).
% 2.25/2.44  thf('74', plain,
% 2.25/2.44      ((m1_subset_1 @ (k4_tmap_1 @ sk_A @ sk_B_1) @ 
% 2.25/2.44        (k1_zfmisc_1 @ 
% 2.25/2.44         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A))))),
% 2.25/2.44      inference('clc', [status(thm)], ['8', '9'])).
% 2.25/2.44  thf(d4_tmap_1, axiom,
% 2.25/2.44    (![A:$i]:
% 2.25/2.44     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 2.25/2.44       ( ![B:$i]:
% 2.25/2.44         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 2.25/2.44             ( l1_pre_topc @ B ) ) =>
% 2.25/2.44           ( ![C:$i]:
% 2.25/2.44             ( ( ( v1_funct_1 @ C ) & 
% 2.25/2.44                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 2.25/2.44                 ( m1_subset_1 @
% 2.25/2.44                   C @ 
% 2.25/2.44                   ( k1_zfmisc_1 @
% 2.25/2.44                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 2.25/2.44               ( ![D:$i]:
% 2.25/2.44                 ( ( m1_pre_topc @ D @ A ) =>
% 2.25/2.44                   ( ( k2_tmap_1 @ A @ B @ C @ D ) =
% 2.25/2.44                     ( k2_partfun1 @
% 2.25/2.44                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ 
% 2.25/2.44                       ( u1_struct_0 @ D ) ) ) ) ) ) ) ) ) ))).
% 2.25/2.44  thf('75', plain,
% 2.25/2.44      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 2.25/2.44         ((v2_struct_0 @ X20)
% 2.25/2.44          | ~ (v2_pre_topc @ X20)
% 2.25/2.44          | ~ (l1_pre_topc @ X20)
% 2.25/2.44          | ~ (m1_pre_topc @ X21 @ X22)
% 2.25/2.44          | ((k2_tmap_1 @ X22 @ X20 @ X23 @ X21)
% 2.25/2.44              = (k2_partfun1 @ (u1_struct_0 @ X22) @ (u1_struct_0 @ X20) @ 
% 2.25/2.44                 X23 @ (u1_struct_0 @ X21)))
% 2.25/2.44          | ~ (m1_subset_1 @ X23 @ 
% 2.25/2.44               (k1_zfmisc_1 @ 
% 2.25/2.44                (k2_zfmisc_1 @ (u1_struct_0 @ X22) @ (u1_struct_0 @ X20))))
% 2.25/2.44          | ~ (v1_funct_2 @ X23 @ (u1_struct_0 @ X22) @ (u1_struct_0 @ X20))
% 2.25/2.44          | ~ (v1_funct_1 @ X23)
% 2.25/2.44          | ~ (l1_pre_topc @ X22)
% 2.25/2.44          | ~ (v2_pre_topc @ X22)
% 2.25/2.44          | (v2_struct_0 @ X22))),
% 2.25/2.44      inference('cnf', [status(esa)], [d4_tmap_1])).
% 2.25/2.44  thf('76', plain,
% 2.25/2.44      (![X0 : $i]:
% 2.25/2.44         ((v2_struct_0 @ sk_B_1)
% 2.25/2.44          | ~ (v2_pre_topc @ sk_B_1)
% 2.25/2.44          | ~ (l1_pre_topc @ sk_B_1)
% 2.25/2.44          | ~ (v1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_B_1))
% 2.25/2.44          | ~ (v1_funct_2 @ (k4_tmap_1 @ sk_A @ sk_B_1) @ 
% 2.25/2.44               (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A))
% 2.25/2.44          | ((k2_tmap_1 @ sk_B_1 @ sk_A @ (k4_tmap_1 @ sk_A @ sk_B_1) @ X0)
% 2.25/2.44              = (k2_partfun1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 2.25/2.44                 (k4_tmap_1 @ sk_A @ sk_B_1) @ (u1_struct_0 @ X0)))
% 2.25/2.44          | ~ (m1_pre_topc @ X0 @ sk_B_1)
% 2.25/2.44          | ~ (l1_pre_topc @ sk_A)
% 2.25/2.44          | ~ (v2_pre_topc @ sk_A)
% 2.25/2.44          | (v2_struct_0 @ sk_A))),
% 2.25/2.44      inference('sup-', [status(thm)], ['74', '75'])).
% 2.25/2.44  thf('77', plain, ((v2_pre_topc @ sk_B_1)),
% 2.25/2.44      inference('demod', [status(thm)], ['38', '39', '40'])).
% 2.25/2.44  thf('78', plain, ((l1_pre_topc @ sk_B_1)),
% 2.25/2.44      inference('demod', [status(thm)], ['33', '34'])).
% 2.25/2.44  thf('79', plain, ((v1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_B_1))),
% 2.25/2.44      inference('clc', [status(thm)], ['28', '29'])).
% 2.25/2.44  thf('80', plain,
% 2.25/2.44      ((v1_funct_2 @ (k4_tmap_1 @ sk_A @ sk_B_1) @ (u1_struct_0 @ sk_B_1) @ 
% 2.25/2.44        (u1_struct_0 @ sk_A))),
% 2.25/2.44      inference('clc', [status(thm)], ['20', '21'])).
% 2.25/2.44  thf('81', plain, ((l1_pre_topc @ sk_A)),
% 2.25/2.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.25/2.44  thf('82', plain, ((v2_pre_topc @ sk_A)),
% 2.25/2.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.25/2.44  thf('83', plain,
% 2.25/2.44      (![X0 : $i]:
% 2.25/2.44         ((v2_struct_0 @ sk_B_1)
% 2.25/2.44          | ((k2_tmap_1 @ sk_B_1 @ sk_A @ (k4_tmap_1 @ sk_A @ sk_B_1) @ X0)
% 2.25/2.44              = (k2_partfun1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 2.25/2.44                 (k4_tmap_1 @ sk_A @ sk_B_1) @ (u1_struct_0 @ X0)))
% 2.25/2.44          | ~ (m1_pre_topc @ X0 @ sk_B_1)
% 2.25/2.44          | (v2_struct_0 @ sk_A))),
% 2.25/2.44      inference('demod', [status(thm)],
% 2.25/2.44                ['76', '77', '78', '79', '80', '81', '82'])).
% 2.25/2.44  thf('84', plain,
% 2.25/2.44      ((~ (l1_pre_topc @ sk_B_1)
% 2.25/2.44        | (v2_struct_0 @ sk_A)
% 2.25/2.44        | ((k2_tmap_1 @ sk_B_1 @ sk_A @ (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_B_1)
% 2.25/2.44            = (k2_partfun1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 2.25/2.44               (k4_tmap_1 @ sk_A @ sk_B_1) @ (u1_struct_0 @ sk_B_1)))
% 2.25/2.44        | (v2_struct_0 @ sk_B_1))),
% 2.25/2.44      inference('sup-', [status(thm)], ['73', '83'])).
% 2.25/2.44  thf('85', plain, ((l1_pre_topc @ sk_B_1)),
% 2.25/2.44      inference('demod', [status(thm)], ['33', '34'])).
% 2.25/2.44  thf('86', plain,
% 2.25/2.44      (((v2_struct_0 @ sk_A)
% 2.25/2.44        | ((k2_tmap_1 @ sk_B_1 @ sk_A @ (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_B_1)
% 2.25/2.44            = (k2_partfun1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 2.25/2.44               (k4_tmap_1 @ sk_A @ sk_B_1) @ (u1_struct_0 @ sk_B_1)))
% 2.25/2.44        | (v2_struct_0 @ sk_B_1))),
% 2.25/2.44      inference('demod', [status(thm)], ['84', '85'])).
% 2.25/2.44  thf('87', plain, (~ (v2_struct_0 @ sk_A)),
% 2.25/2.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.25/2.44  thf('88', plain,
% 2.25/2.44      (((v2_struct_0 @ sk_B_1)
% 2.25/2.44        | ((k2_tmap_1 @ sk_B_1 @ sk_A @ (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_B_1)
% 2.25/2.44            = (k2_partfun1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 2.25/2.44               (k4_tmap_1 @ sk_A @ sk_B_1) @ (u1_struct_0 @ sk_B_1))))),
% 2.25/2.44      inference('clc', [status(thm)], ['86', '87'])).
% 2.25/2.44  thf('89', plain, (~ (v2_struct_0 @ sk_B_1)),
% 2.25/2.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.25/2.44  thf('90', plain,
% 2.25/2.44      (((k2_tmap_1 @ sk_B_1 @ sk_A @ (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_B_1)
% 2.25/2.44         = (k2_partfun1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 2.25/2.44            (k4_tmap_1 @ sk_A @ sk_B_1) @ (u1_struct_0 @ sk_B_1)))),
% 2.25/2.44      inference('clc', [status(thm)], ['88', '89'])).
% 2.25/2.44  thf('91', plain,
% 2.25/2.44      (((v2_struct_0 @ sk_A)
% 2.25/2.44        | ((k3_tmap_1 @ sk_B_1 @ sk_A @ sk_B_1 @ sk_B_1 @ 
% 2.25/2.44            (k4_tmap_1 @ sk_A @ sk_B_1))
% 2.25/2.44            = (k2_tmap_1 @ sk_B_1 @ sk_A @ (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_B_1))
% 2.25/2.44        | (v2_struct_0 @ sk_B_1))),
% 2.25/2.44      inference('demod', [status(thm)], ['71', '72', '90'])).
% 2.25/2.44  thf('92', plain, (~ (v2_struct_0 @ sk_A)),
% 2.25/2.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.25/2.44  thf('93', plain,
% 2.25/2.44      (((v2_struct_0 @ sk_B_1)
% 2.25/2.44        | ((k3_tmap_1 @ sk_B_1 @ sk_A @ sk_B_1 @ sk_B_1 @ 
% 2.25/2.44            (k4_tmap_1 @ sk_A @ sk_B_1))
% 2.25/2.44            = (k2_tmap_1 @ sk_B_1 @ sk_A @ (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_B_1)))),
% 2.25/2.44      inference('clc', [status(thm)], ['91', '92'])).
% 2.25/2.44  thf('94', plain, (~ (v2_struct_0 @ sk_B_1)),
% 2.25/2.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.25/2.44  thf('95', plain,
% 2.25/2.44      (((k3_tmap_1 @ sk_B_1 @ sk_A @ sk_B_1 @ sk_B_1 @ 
% 2.25/2.44         (k4_tmap_1 @ sk_A @ sk_B_1))
% 2.25/2.44         = (k2_tmap_1 @ sk_B_1 @ sk_A @ (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_B_1))),
% 2.25/2.44      inference('clc', [status(thm)], ['93', '94'])).
% 2.25/2.44  thf('96', plain, ((l1_pre_topc @ sk_B_1)),
% 2.25/2.44      inference('demod', [status(thm)], ['33', '34'])).
% 2.25/2.44  thf('97', plain, ((v2_pre_topc @ sk_B_1)),
% 2.25/2.44      inference('demod', [status(thm)], ['38', '39', '40'])).
% 2.25/2.44  thf('98', plain,
% 2.25/2.44      (((v2_struct_0 @ sk_A)
% 2.25/2.44        | (r2_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 2.25/2.44           (k4_tmap_1 @ sk_A @ sk_B_1) @ 
% 2.25/2.44           (k2_tmap_1 @ sk_B_1 @ sk_A @ (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_B_1))
% 2.25/2.44        | (v2_struct_0 @ sk_B_1)
% 2.25/2.44        | (v2_struct_0 @ sk_B_1))),
% 2.25/2.44      inference('demod', [status(thm)], ['53', '54', '95', '96', '97'])).
% 2.25/2.44  thf('99', plain,
% 2.25/2.44      (((v2_struct_0 @ sk_B_1)
% 2.25/2.44        | (r2_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 2.25/2.44           (k4_tmap_1 @ sk_A @ sk_B_1) @ 
% 2.25/2.44           (k2_tmap_1 @ sk_B_1 @ sk_A @ (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_B_1))
% 2.25/2.44        | (v2_struct_0 @ sk_A))),
% 2.25/2.44      inference('simplify', [status(thm)], ['98'])).
% 2.25/2.44  thf('100', plain, (~ (v2_struct_0 @ sk_B_1)),
% 2.25/2.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.25/2.44  thf('101', plain,
% 2.25/2.44      (((v2_struct_0 @ sk_A)
% 2.25/2.44        | (r2_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 2.25/2.44           (k4_tmap_1 @ sk_A @ sk_B_1) @ 
% 2.25/2.44           (k2_tmap_1 @ sk_B_1 @ sk_A @ (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_B_1)))),
% 2.25/2.44      inference('clc', [status(thm)], ['99', '100'])).
% 2.25/2.44  thf('102', plain, (~ (v2_struct_0 @ sk_A)),
% 2.25/2.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.25/2.44  thf('103', plain,
% 2.25/2.44      ((r2_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 2.25/2.44        (k4_tmap_1 @ sk_A @ sk_B_1) @ 
% 2.25/2.44        (k2_tmap_1 @ sk_B_1 @ sk_A @ (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_B_1))),
% 2.25/2.44      inference('clc', [status(thm)], ['101', '102'])).
% 2.25/2.44  thf('104', plain,
% 2.25/2.44      ((m1_subset_1 @ (k4_tmap_1 @ sk_A @ sk_B_1) @ 
% 2.25/2.44        (k1_zfmisc_1 @ 
% 2.25/2.44         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A))))),
% 2.25/2.44      inference('clc', [status(thm)], ['8', '9'])).
% 2.25/2.44  thf(redefinition_r2_funct_2, axiom,
% 2.25/2.44    (![A:$i,B:$i,C:$i,D:$i]:
% 2.25/2.44     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 2.25/2.44         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 2.25/2.44         ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 2.25/2.44         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.25/2.44       ( ( r2_funct_2 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 2.25/2.44  thf('105', plain,
% 2.25/2.44      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 2.25/2.44         (~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11)))
% 2.25/2.44          | ~ (v1_funct_2 @ X9 @ X10 @ X11)
% 2.25/2.44          | ~ (v1_funct_1 @ X9)
% 2.25/2.44          | ~ (v1_funct_1 @ X12)
% 2.25/2.44          | ~ (v1_funct_2 @ X12 @ X10 @ X11)
% 2.25/2.44          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11)))
% 2.25/2.44          | ((X9) = (X12))
% 2.25/2.44          | ~ (r2_funct_2 @ X10 @ X11 @ X9 @ X12))),
% 2.25/2.44      inference('cnf', [status(esa)], [redefinition_r2_funct_2])).
% 2.25/2.44  thf('106', plain,
% 2.25/2.44      (![X0 : $i]:
% 2.25/2.44         (~ (r2_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 2.25/2.44             (k4_tmap_1 @ sk_A @ sk_B_1) @ X0)
% 2.25/2.44          | ((k4_tmap_1 @ sk_A @ sk_B_1) = (X0))
% 2.25/2.44          | ~ (m1_subset_1 @ X0 @ 
% 2.25/2.44               (k1_zfmisc_1 @ 
% 2.25/2.44                (k2_zfmisc_1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A))))
% 2.25/2.44          | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A))
% 2.25/2.44          | ~ (v1_funct_1 @ X0)
% 2.25/2.44          | ~ (v1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_B_1))
% 2.25/2.44          | ~ (v1_funct_2 @ (k4_tmap_1 @ sk_A @ sk_B_1) @ 
% 2.25/2.44               (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A)))),
% 2.25/2.44      inference('sup-', [status(thm)], ['104', '105'])).
% 2.25/2.44  thf('107', plain, ((v1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_B_1))),
% 2.25/2.44      inference('clc', [status(thm)], ['28', '29'])).
% 2.25/2.44  thf('108', plain,
% 2.25/2.44      ((v1_funct_2 @ (k4_tmap_1 @ sk_A @ sk_B_1) @ (u1_struct_0 @ sk_B_1) @ 
% 2.25/2.44        (u1_struct_0 @ sk_A))),
% 2.25/2.44      inference('clc', [status(thm)], ['20', '21'])).
% 2.25/2.44  thf('109', plain,
% 2.25/2.44      (![X0 : $i]:
% 2.25/2.44         (~ (r2_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 2.25/2.44             (k4_tmap_1 @ sk_A @ sk_B_1) @ X0)
% 2.25/2.44          | ((k4_tmap_1 @ sk_A @ sk_B_1) = (X0))
% 2.25/2.44          | ~ (m1_subset_1 @ X0 @ 
% 2.25/2.44               (k1_zfmisc_1 @ 
% 2.25/2.44                (k2_zfmisc_1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A))))
% 2.25/2.44          | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A))
% 2.25/2.44          | ~ (v1_funct_1 @ X0))),
% 2.25/2.44      inference('demod', [status(thm)], ['106', '107', '108'])).
% 2.25/2.44  thf('110', plain,
% 2.25/2.44      ((~ (v1_funct_1 @ 
% 2.25/2.44           (k2_tmap_1 @ sk_B_1 @ sk_A @ (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_B_1))
% 2.25/2.44        | ~ (v1_funct_2 @ 
% 2.25/2.44             (k2_tmap_1 @ sk_B_1 @ sk_A @ (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_B_1) @ 
% 2.25/2.44             (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A))
% 2.25/2.44        | ~ (m1_subset_1 @ 
% 2.25/2.44             (k2_tmap_1 @ sk_B_1 @ sk_A @ (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_B_1) @ 
% 2.25/2.44             (k1_zfmisc_1 @ 
% 2.25/2.44              (k2_zfmisc_1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A))))
% 2.25/2.44        | ((k4_tmap_1 @ sk_A @ sk_B_1)
% 2.25/2.44            = (k2_tmap_1 @ sk_B_1 @ sk_A @ (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_B_1)))),
% 2.25/2.44      inference('sup-', [status(thm)], ['103', '109'])).
% 2.25/2.44  thf('111', plain,
% 2.25/2.44      (![X36 : $i]: ((m1_pre_topc @ X36 @ X36) | ~ (l1_pre_topc @ X36))),
% 2.25/2.44      inference('cnf', [status(esa)], [t2_tsep_1])).
% 2.25/2.44  thf('112', plain,
% 2.25/2.44      (![X36 : $i]: ((m1_pre_topc @ X36 @ X36) | ~ (l1_pre_topc @ X36))),
% 2.25/2.44      inference('cnf', [status(esa)], [t2_tsep_1])).
% 2.25/2.44  thf('113', plain,
% 2.25/2.44      ((m1_subset_1 @ (k4_tmap_1 @ sk_A @ sk_B_1) @ 
% 2.25/2.44        (k1_zfmisc_1 @ 
% 2.25/2.44         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A))))),
% 2.25/2.44      inference('clc', [status(thm)], ['8', '9'])).
% 2.25/2.44  thf(dt_k3_tmap_1, axiom,
% 2.25/2.44    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 2.25/2.44     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 2.25/2.44         ( l1_pre_topc @ A ) & ( ~( v2_struct_0 @ B ) ) & 
% 2.25/2.44         ( v2_pre_topc @ B ) & ( l1_pre_topc @ B ) & ( m1_pre_topc @ C @ A ) & 
% 2.25/2.44         ( m1_pre_topc @ D @ A ) & ( v1_funct_1 @ E ) & 
% 2.25/2.44         ( v1_funct_2 @ E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 2.25/2.44         ( m1_subset_1 @
% 2.25/2.44           E @ 
% 2.25/2.44           ( k1_zfmisc_1 @
% 2.25/2.44             ( k2_zfmisc_1 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 2.25/2.44       ( ( v1_funct_1 @ ( k3_tmap_1 @ A @ B @ C @ D @ E ) ) & 
% 2.25/2.44         ( v1_funct_2 @
% 2.25/2.44           ( k3_tmap_1 @ A @ B @ C @ D @ E ) @ ( u1_struct_0 @ D ) @ 
% 2.25/2.44           ( u1_struct_0 @ B ) ) & 
% 2.25/2.44         ( m1_subset_1 @
% 2.25/2.44           ( k3_tmap_1 @ A @ B @ C @ D @ E ) @ 
% 2.25/2.44           ( k1_zfmisc_1 @
% 2.25/2.44             ( k2_zfmisc_1 @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) ))).
% 2.25/2.44  thf('114', plain,
% 2.25/2.44      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 2.25/2.44         (~ (m1_pre_topc @ X29 @ X30)
% 2.25/2.44          | ~ (m1_pre_topc @ X31 @ X30)
% 2.25/2.44          | ~ (l1_pre_topc @ X32)
% 2.25/2.44          | ~ (v2_pre_topc @ X32)
% 2.25/2.44          | (v2_struct_0 @ X32)
% 2.25/2.44          | ~ (l1_pre_topc @ X30)
% 2.25/2.44          | ~ (v2_pre_topc @ X30)
% 2.25/2.44          | (v2_struct_0 @ X30)
% 2.25/2.44          | ~ (v1_funct_1 @ X33)
% 2.25/2.44          | ~ (v1_funct_2 @ X33 @ (u1_struct_0 @ X31) @ (u1_struct_0 @ X32))
% 2.25/2.44          | ~ (m1_subset_1 @ X33 @ 
% 2.25/2.44               (k1_zfmisc_1 @ 
% 2.25/2.44                (k2_zfmisc_1 @ (u1_struct_0 @ X31) @ (u1_struct_0 @ X32))))
% 2.25/2.44          | (v1_funct_1 @ (k3_tmap_1 @ X30 @ X32 @ X31 @ X29 @ X33)))),
% 2.25/2.44      inference('cnf', [status(esa)], [dt_k3_tmap_1])).
% 2.25/2.44  thf('115', plain,
% 2.25/2.44      (![X0 : $i, X1 : $i]:
% 2.25/2.44         ((v1_funct_1 @ 
% 2.25/2.44           (k3_tmap_1 @ X1 @ sk_A @ sk_B_1 @ X0 @ (k4_tmap_1 @ sk_A @ sk_B_1)))
% 2.25/2.44          | ~ (v1_funct_2 @ (k4_tmap_1 @ sk_A @ sk_B_1) @ 
% 2.25/2.44               (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A))
% 2.25/2.44          | ~ (v1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_B_1))
% 2.25/2.44          | (v2_struct_0 @ X1)
% 2.25/2.44          | ~ (v2_pre_topc @ X1)
% 2.25/2.44          | ~ (l1_pre_topc @ X1)
% 2.25/2.44          | (v2_struct_0 @ sk_A)
% 2.25/2.44          | ~ (v2_pre_topc @ sk_A)
% 2.25/2.44          | ~ (l1_pre_topc @ sk_A)
% 2.25/2.44          | ~ (m1_pre_topc @ sk_B_1 @ X1)
% 2.25/2.44          | ~ (m1_pre_topc @ X0 @ X1))),
% 2.25/2.44      inference('sup-', [status(thm)], ['113', '114'])).
% 2.25/2.44  thf('116', plain,
% 2.25/2.44      ((v1_funct_2 @ (k4_tmap_1 @ sk_A @ sk_B_1) @ (u1_struct_0 @ sk_B_1) @ 
% 2.25/2.44        (u1_struct_0 @ sk_A))),
% 2.25/2.44      inference('clc', [status(thm)], ['20', '21'])).
% 2.25/2.44  thf('117', plain, ((v1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_B_1))),
% 2.25/2.44      inference('clc', [status(thm)], ['28', '29'])).
% 2.25/2.44  thf('118', plain, ((v2_pre_topc @ sk_A)),
% 2.25/2.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.25/2.44  thf('119', plain, ((l1_pre_topc @ sk_A)),
% 2.25/2.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.25/2.44  thf('120', plain,
% 2.25/2.44      (![X0 : $i, X1 : $i]:
% 2.25/2.44         ((v1_funct_1 @ 
% 2.25/2.44           (k3_tmap_1 @ X1 @ sk_A @ sk_B_1 @ X0 @ (k4_tmap_1 @ sk_A @ sk_B_1)))
% 2.25/2.44          | (v2_struct_0 @ X1)
% 2.25/2.44          | ~ (v2_pre_topc @ X1)
% 2.25/2.44          | ~ (l1_pre_topc @ X1)
% 2.25/2.44          | (v2_struct_0 @ sk_A)
% 2.25/2.44          | ~ (m1_pre_topc @ sk_B_1 @ X1)
% 2.25/2.44          | ~ (m1_pre_topc @ X0 @ X1))),
% 2.25/2.44      inference('demod', [status(thm)], ['115', '116', '117', '118', '119'])).
% 2.25/2.44  thf('121', plain,
% 2.25/2.44      (![X0 : $i]:
% 2.25/2.44         (~ (l1_pre_topc @ sk_B_1)
% 2.25/2.44          | ~ (m1_pre_topc @ X0 @ sk_B_1)
% 2.25/2.44          | (v2_struct_0 @ sk_A)
% 2.25/2.44          | ~ (l1_pre_topc @ sk_B_1)
% 2.25/2.44          | ~ (v2_pre_topc @ sk_B_1)
% 2.25/2.44          | (v2_struct_0 @ sk_B_1)
% 2.25/2.44          | (v1_funct_1 @ 
% 2.25/2.44             (k3_tmap_1 @ sk_B_1 @ sk_A @ sk_B_1 @ X0 @ 
% 2.25/2.44              (k4_tmap_1 @ sk_A @ sk_B_1))))),
% 2.25/2.44      inference('sup-', [status(thm)], ['112', '120'])).
% 2.25/2.44  thf('122', plain, ((l1_pre_topc @ sk_B_1)),
% 2.25/2.44      inference('demod', [status(thm)], ['33', '34'])).
% 2.25/2.44  thf('123', plain, ((l1_pre_topc @ sk_B_1)),
% 2.25/2.44      inference('demod', [status(thm)], ['33', '34'])).
% 2.25/2.44  thf('124', plain, ((v2_pre_topc @ sk_B_1)),
% 2.25/2.44      inference('demod', [status(thm)], ['38', '39', '40'])).
% 2.25/2.44  thf('125', plain,
% 2.25/2.44      (![X0 : $i]:
% 2.25/2.44         (~ (m1_pre_topc @ X0 @ sk_B_1)
% 2.25/2.44          | (v2_struct_0 @ sk_A)
% 2.25/2.44          | (v2_struct_0 @ sk_B_1)
% 2.25/2.44          | (v1_funct_1 @ 
% 2.25/2.44             (k3_tmap_1 @ sk_B_1 @ sk_A @ sk_B_1 @ X0 @ 
% 2.25/2.44              (k4_tmap_1 @ sk_A @ sk_B_1))))),
% 2.25/2.44      inference('demod', [status(thm)], ['121', '122', '123', '124'])).
% 2.25/2.44  thf('126', plain,
% 2.25/2.44      ((~ (l1_pre_topc @ sk_B_1)
% 2.25/2.44        | (v1_funct_1 @ 
% 2.25/2.44           (k3_tmap_1 @ sk_B_1 @ sk_A @ sk_B_1 @ sk_B_1 @ 
% 2.25/2.44            (k4_tmap_1 @ sk_A @ sk_B_1)))
% 2.25/2.44        | (v2_struct_0 @ sk_B_1)
% 2.25/2.44        | (v2_struct_0 @ sk_A))),
% 2.25/2.44      inference('sup-', [status(thm)], ['111', '125'])).
% 2.25/2.44  thf('127', plain, ((l1_pre_topc @ sk_B_1)),
% 2.25/2.44      inference('demod', [status(thm)], ['33', '34'])).
% 2.25/2.44  thf('128', plain,
% 2.25/2.44      (((v1_funct_1 @ 
% 2.25/2.44         (k3_tmap_1 @ sk_B_1 @ sk_A @ sk_B_1 @ sk_B_1 @ 
% 2.25/2.45          (k4_tmap_1 @ sk_A @ sk_B_1)))
% 2.25/2.45        | (v2_struct_0 @ sk_B_1)
% 2.25/2.45        | (v2_struct_0 @ sk_A))),
% 2.25/2.45      inference('demod', [status(thm)], ['126', '127'])).
% 2.25/2.45  thf('129', plain, (~ (v2_struct_0 @ sk_B_1)),
% 2.25/2.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.25/2.45  thf('130', plain,
% 2.25/2.45      (((v2_struct_0 @ sk_A)
% 2.25/2.45        | (v1_funct_1 @ 
% 2.25/2.45           (k3_tmap_1 @ sk_B_1 @ sk_A @ sk_B_1 @ sk_B_1 @ 
% 2.25/2.45            (k4_tmap_1 @ sk_A @ sk_B_1))))),
% 2.25/2.45      inference('clc', [status(thm)], ['128', '129'])).
% 2.25/2.45  thf('131', plain, (~ (v2_struct_0 @ sk_A)),
% 2.25/2.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.25/2.45  thf('132', plain,
% 2.25/2.45      ((v1_funct_1 @ 
% 2.25/2.45        (k3_tmap_1 @ sk_B_1 @ sk_A @ sk_B_1 @ sk_B_1 @ 
% 2.25/2.45         (k4_tmap_1 @ sk_A @ sk_B_1)))),
% 2.25/2.45      inference('clc', [status(thm)], ['130', '131'])).
% 2.25/2.45  thf('133', plain,
% 2.25/2.45      (((k3_tmap_1 @ sk_B_1 @ sk_A @ sk_B_1 @ sk_B_1 @ 
% 2.25/2.45         (k4_tmap_1 @ sk_A @ sk_B_1))
% 2.25/2.45         = (k2_tmap_1 @ sk_B_1 @ sk_A @ (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_B_1))),
% 2.25/2.45      inference('clc', [status(thm)], ['93', '94'])).
% 2.25/2.45  thf('134', plain,
% 2.25/2.45      ((v1_funct_1 @ 
% 2.25/2.45        (k2_tmap_1 @ sk_B_1 @ sk_A @ (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_B_1))),
% 2.25/2.45      inference('demod', [status(thm)], ['132', '133'])).
% 2.25/2.45  thf('135', plain,
% 2.25/2.45      (![X36 : $i]: ((m1_pre_topc @ X36 @ X36) | ~ (l1_pre_topc @ X36))),
% 2.25/2.45      inference('cnf', [status(esa)], [t2_tsep_1])).
% 2.25/2.45  thf('136', plain,
% 2.25/2.45      (![X36 : $i]: ((m1_pre_topc @ X36 @ X36) | ~ (l1_pre_topc @ X36))),
% 2.25/2.45      inference('cnf', [status(esa)], [t2_tsep_1])).
% 2.25/2.45  thf('137', plain,
% 2.25/2.45      ((m1_subset_1 @ (k4_tmap_1 @ sk_A @ sk_B_1) @ 
% 2.25/2.45        (k1_zfmisc_1 @ 
% 2.25/2.45         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A))))),
% 2.25/2.45      inference('clc', [status(thm)], ['8', '9'])).
% 2.25/2.45  thf('138', plain,
% 2.25/2.45      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 2.25/2.45         (~ (m1_pre_topc @ X29 @ X30)
% 2.25/2.45          | ~ (m1_pre_topc @ X31 @ X30)
% 2.25/2.45          | ~ (l1_pre_topc @ X32)
% 2.25/2.45          | ~ (v2_pre_topc @ X32)
% 2.25/2.45          | (v2_struct_0 @ X32)
% 2.25/2.45          | ~ (l1_pre_topc @ X30)
% 2.25/2.45          | ~ (v2_pre_topc @ X30)
% 2.25/2.45          | (v2_struct_0 @ X30)
% 2.25/2.45          | ~ (v1_funct_1 @ X33)
% 2.25/2.45          | ~ (v1_funct_2 @ X33 @ (u1_struct_0 @ X31) @ (u1_struct_0 @ X32))
% 2.25/2.45          | ~ (m1_subset_1 @ X33 @ 
% 2.25/2.45               (k1_zfmisc_1 @ 
% 2.25/2.45                (k2_zfmisc_1 @ (u1_struct_0 @ X31) @ (u1_struct_0 @ X32))))
% 2.25/2.45          | (v1_funct_2 @ (k3_tmap_1 @ X30 @ X32 @ X31 @ X29 @ X33) @ 
% 2.25/2.45             (u1_struct_0 @ X29) @ (u1_struct_0 @ X32)))),
% 2.25/2.45      inference('cnf', [status(esa)], [dt_k3_tmap_1])).
% 2.25/2.45  thf('139', plain,
% 2.25/2.45      (![X0 : $i, X1 : $i]:
% 2.25/2.45         ((v1_funct_2 @ 
% 2.25/2.45           (k3_tmap_1 @ X1 @ sk_A @ sk_B_1 @ X0 @ (k4_tmap_1 @ sk_A @ sk_B_1)) @ 
% 2.25/2.45           (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A))
% 2.25/2.45          | ~ (v1_funct_2 @ (k4_tmap_1 @ sk_A @ sk_B_1) @ 
% 2.25/2.45               (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A))
% 2.25/2.45          | ~ (v1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_B_1))
% 2.25/2.45          | (v2_struct_0 @ X1)
% 2.25/2.45          | ~ (v2_pre_topc @ X1)
% 2.25/2.45          | ~ (l1_pre_topc @ X1)
% 2.25/2.45          | (v2_struct_0 @ sk_A)
% 2.25/2.45          | ~ (v2_pre_topc @ sk_A)
% 2.25/2.45          | ~ (l1_pre_topc @ sk_A)
% 2.25/2.45          | ~ (m1_pre_topc @ sk_B_1 @ X1)
% 2.25/2.45          | ~ (m1_pre_topc @ X0 @ X1))),
% 2.25/2.45      inference('sup-', [status(thm)], ['137', '138'])).
% 2.25/2.45  thf('140', plain,
% 2.25/2.45      ((v1_funct_2 @ (k4_tmap_1 @ sk_A @ sk_B_1) @ (u1_struct_0 @ sk_B_1) @ 
% 2.25/2.45        (u1_struct_0 @ sk_A))),
% 2.25/2.45      inference('clc', [status(thm)], ['20', '21'])).
% 2.25/2.45  thf('141', plain, ((v1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_B_1))),
% 2.25/2.45      inference('clc', [status(thm)], ['28', '29'])).
% 2.25/2.45  thf('142', plain, ((v2_pre_topc @ sk_A)),
% 2.25/2.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.25/2.45  thf('143', plain, ((l1_pre_topc @ sk_A)),
% 2.25/2.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.25/2.45  thf('144', plain,
% 2.25/2.45      (![X0 : $i, X1 : $i]:
% 2.25/2.45         ((v1_funct_2 @ 
% 2.25/2.45           (k3_tmap_1 @ X1 @ sk_A @ sk_B_1 @ X0 @ (k4_tmap_1 @ sk_A @ sk_B_1)) @ 
% 2.25/2.45           (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A))
% 2.25/2.45          | (v2_struct_0 @ X1)
% 2.25/2.45          | ~ (v2_pre_topc @ X1)
% 2.25/2.45          | ~ (l1_pre_topc @ X1)
% 2.25/2.45          | (v2_struct_0 @ sk_A)
% 2.25/2.45          | ~ (m1_pre_topc @ sk_B_1 @ X1)
% 2.25/2.45          | ~ (m1_pre_topc @ X0 @ X1))),
% 2.25/2.45      inference('demod', [status(thm)], ['139', '140', '141', '142', '143'])).
% 2.25/2.45  thf('145', plain,
% 2.25/2.45      (![X0 : $i]:
% 2.25/2.45         (~ (l1_pre_topc @ sk_B_1)
% 2.25/2.45          | ~ (m1_pre_topc @ X0 @ sk_B_1)
% 2.25/2.45          | (v2_struct_0 @ sk_A)
% 2.25/2.45          | ~ (l1_pre_topc @ sk_B_1)
% 2.25/2.45          | ~ (v2_pre_topc @ sk_B_1)
% 2.25/2.45          | (v2_struct_0 @ sk_B_1)
% 2.25/2.45          | (v1_funct_2 @ 
% 2.25/2.45             (k3_tmap_1 @ sk_B_1 @ sk_A @ sk_B_1 @ X0 @ 
% 2.25/2.45              (k4_tmap_1 @ sk_A @ sk_B_1)) @ 
% 2.25/2.45             (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A)))),
% 2.25/2.45      inference('sup-', [status(thm)], ['136', '144'])).
% 2.25/2.45  thf('146', plain, ((l1_pre_topc @ sk_B_1)),
% 2.25/2.45      inference('demod', [status(thm)], ['33', '34'])).
% 2.25/2.45  thf('147', plain, ((l1_pre_topc @ sk_B_1)),
% 2.25/2.45      inference('demod', [status(thm)], ['33', '34'])).
% 2.25/2.45  thf('148', plain, ((v2_pre_topc @ sk_B_1)),
% 2.25/2.45      inference('demod', [status(thm)], ['38', '39', '40'])).
% 2.25/2.45  thf('149', plain,
% 2.25/2.45      (![X0 : $i]:
% 2.25/2.45         (~ (m1_pre_topc @ X0 @ sk_B_1)
% 2.25/2.45          | (v2_struct_0 @ sk_A)
% 2.25/2.45          | (v2_struct_0 @ sk_B_1)
% 2.25/2.45          | (v1_funct_2 @ 
% 2.25/2.45             (k3_tmap_1 @ sk_B_1 @ sk_A @ sk_B_1 @ X0 @ 
% 2.25/2.45              (k4_tmap_1 @ sk_A @ sk_B_1)) @ 
% 2.25/2.45             (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A)))),
% 2.25/2.45      inference('demod', [status(thm)], ['145', '146', '147', '148'])).
% 2.25/2.45  thf('150', plain,
% 2.25/2.45      ((~ (l1_pre_topc @ sk_B_1)
% 2.25/2.45        | (v1_funct_2 @ 
% 2.25/2.45           (k3_tmap_1 @ sk_B_1 @ sk_A @ sk_B_1 @ sk_B_1 @ 
% 2.25/2.45            (k4_tmap_1 @ sk_A @ sk_B_1)) @ 
% 2.25/2.45           (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A))
% 2.25/2.45        | (v2_struct_0 @ sk_B_1)
% 2.25/2.45        | (v2_struct_0 @ sk_A))),
% 2.25/2.45      inference('sup-', [status(thm)], ['135', '149'])).
% 2.25/2.45  thf('151', plain, ((l1_pre_topc @ sk_B_1)),
% 2.25/2.45      inference('demod', [status(thm)], ['33', '34'])).
% 2.25/2.45  thf('152', plain,
% 2.25/2.45      (((v1_funct_2 @ 
% 2.25/2.45         (k3_tmap_1 @ sk_B_1 @ sk_A @ sk_B_1 @ sk_B_1 @ 
% 2.25/2.45          (k4_tmap_1 @ sk_A @ sk_B_1)) @ 
% 2.25/2.45         (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A))
% 2.25/2.45        | (v2_struct_0 @ sk_B_1)
% 2.25/2.45        | (v2_struct_0 @ sk_A))),
% 2.25/2.45      inference('demod', [status(thm)], ['150', '151'])).
% 2.25/2.45  thf('153', plain, (~ (v2_struct_0 @ sk_B_1)),
% 2.25/2.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.25/2.45  thf('154', plain,
% 2.25/2.45      (((v2_struct_0 @ sk_A)
% 2.25/2.45        | (v1_funct_2 @ 
% 2.25/2.45           (k3_tmap_1 @ sk_B_1 @ sk_A @ sk_B_1 @ sk_B_1 @ 
% 2.25/2.45            (k4_tmap_1 @ sk_A @ sk_B_1)) @ 
% 2.25/2.45           (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A)))),
% 2.25/2.45      inference('clc', [status(thm)], ['152', '153'])).
% 2.25/2.45  thf('155', plain, (~ (v2_struct_0 @ sk_A)),
% 2.25/2.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.25/2.45  thf('156', plain,
% 2.25/2.45      ((v1_funct_2 @ 
% 2.25/2.45        (k3_tmap_1 @ sk_B_1 @ sk_A @ sk_B_1 @ sk_B_1 @ 
% 2.25/2.45         (k4_tmap_1 @ sk_A @ sk_B_1)) @ 
% 2.25/2.45        (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A))),
% 2.25/2.45      inference('clc', [status(thm)], ['154', '155'])).
% 2.25/2.45  thf('157', plain,
% 2.25/2.45      (((k3_tmap_1 @ sk_B_1 @ sk_A @ sk_B_1 @ sk_B_1 @ 
% 2.25/2.45         (k4_tmap_1 @ sk_A @ sk_B_1))
% 2.25/2.45         = (k2_tmap_1 @ sk_B_1 @ sk_A @ (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_B_1))),
% 2.25/2.45      inference('clc', [status(thm)], ['93', '94'])).
% 2.25/2.45  thf('158', plain,
% 2.25/2.45      ((v1_funct_2 @ 
% 2.25/2.45        (k2_tmap_1 @ sk_B_1 @ sk_A @ (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_B_1) @ 
% 2.25/2.45        (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A))),
% 2.25/2.45      inference('demod', [status(thm)], ['156', '157'])).
% 2.25/2.45  thf('159', plain,
% 2.25/2.45      (![X36 : $i]: ((m1_pre_topc @ X36 @ X36) | ~ (l1_pre_topc @ X36))),
% 2.25/2.45      inference('cnf', [status(esa)], [t2_tsep_1])).
% 2.25/2.45  thf('160', plain,
% 2.25/2.45      (![X36 : $i]: ((m1_pre_topc @ X36 @ X36) | ~ (l1_pre_topc @ X36))),
% 2.25/2.45      inference('cnf', [status(esa)], [t2_tsep_1])).
% 2.25/2.45  thf('161', plain,
% 2.25/2.45      ((m1_subset_1 @ (k4_tmap_1 @ sk_A @ sk_B_1) @ 
% 2.25/2.45        (k1_zfmisc_1 @ 
% 2.25/2.45         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A))))),
% 2.25/2.45      inference('clc', [status(thm)], ['8', '9'])).
% 2.25/2.45  thf('162', plain,
% 2.25/2.45      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 2.25/2.45         (~ (m1_pre_topc @ X29 @ X30)
% 2.25/2.45          | ~ (m1_pre_topc @ X31 @ X30)
% 2.25/2.45          | ~ (l1_pre_topc @ X32)
% 2.25/2.45          | ~ (v2_pre_topc @ X32)
% 2.25/2.45          | (v2_struct_0 @ X32)
% 2.25/2.45          | ~ (l1_pre_topc @ X30)
% 2.25/2.45          | ~ (v2_pre_topc @ X30)
% 2.25/2.45          | (v2_struct_0 @ X30)
% 2.25/2.45          | ~ (v1_funct_1 @ X33)
% 2.25/2.45          | ~ (v1_funct_2 @ X33 @ (u1_struct_0 @ X31) @ (u1_struct_0 @ X32))
% 2.25/2.45          | ~ (m1_subset_1 @ X33 @ 
% 2.25/2.45               (k1_zfmisc_1 @ 
% 2.25/2.45                (k2_zfmisc_1 @ (u1_struct_0 @ X31) @ (u1_struct_0 @ X32))))
% 2.25/2.45          | (m1_subset_1 @ (k3_tmap_1 @ X30 @ X32 @ X31 @ X29 @ X33) @ 
% 2.25/2.45             (k1_zfmisc_1 @ 
% 2.25/2.45              (k2_zfmisc_1 @ (u1_struct_0 @ X29) @ (u1_struct_0 @ X32)))))),
% 2.25/2.45      inference('cnf', [status(esa)], [dt_k3_tmap_1])).
% 2.25/2.45  thf('163', plain,
% 2.25/2.45      (![X0 : $i, X1 : $i]:
% 2.25/2.45         ((m1_subset_1 @ 
% 2.25/2.45           (k3_tmap_1 @ X1 @ sk_A @ sk_B_1 @ X0 @ (k4_tmap_1 @ sk_A @ sk_B_1)) @ 
% 2.25/2.45           (k1_zfmisc_1 @ 
% 2.25/2.45            (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A))))
% 2.25/2.45          | ~ (v1_funct_2 @ (k4_tmap_1 @ sk_A @ sk_B_1) @ 
% 2.25/2.45               (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A))
% 2.25/2.45          | ~ (v1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_B_1))
% 2.25/2.45          | (v2_struct_0 @ X1)
% 2.25/2.45          | ~ (v2_pre_topc @ X1)
% 2.25/2.45          | ~ (l1_pre_topc @ X1)
% 2.25/2.45          | (v2_struct_0 @ sk_A)
% 2.25/2.45          | ~ (v2_pre_topc @ sk_A)
% 2.25/2.45          | ~ (l1_pre_topc @ sk_A)
% 2.25/2.45          | ~ (m1_pre_topc @ sk_B_1 @ X1)
% 2.25/2.45          | ~ (m1_pre_topc @ X0 @ X1))),
% 2.25/2.45      inference('sup-', [status(thm)], ['161', '162'])).
% 2.25/2.45  thf('164', plain,
% 2.25/2.45      ((v1_funct_2 @ (k4_tmap_1 @ sk_A @ sk_B_1) @ (u1_struct_0 @ sk_B_1) @ 
% 2.25/2.45        (u1_struct_0 @ sk_A))),
% 2.25/2.45      inference('clc', [status(thm)], ['20', '21'])).
% 2.25/2.45  thf('165', plain, ((v1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_B_1))),
% 2.25/2.45      inference('clc', [status(thm)], ['28', '29'])).
% 2.25/2.45  thf('166', plain, ((v2_pre_topc @ sk_A)),
% 2.25/2.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.25/2.45  thf('167', plain, ((l1_pre_topc @ sk_A)),
% 2.25/2.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.25/2.45  thf('168', plain,
% 2.25/2.45      (![X0 : $i, X1 : $i]:
% 2.25/2.45         ((m1_subset_1 @ 
% 2.25/2.45           (k3_tmap_1 @ X1 @ sk_A @ sk_B_1 @ X0 @ (k4_tmap_1 @ sk_A @ sk_B_1)) @ 
% 2.25/2.45           (k1_zfmisc_1 @ 
% 2.25/2.45            (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A))))
% 2.25/2.45          | (v2_struct_0 @ X1)
% 2.25/2.45          | ~ (v2_pre_topc @ X1)
% 2.25/2.45          | ~ (l1_pre_topc @ X1)
% 2.25/2.45          | (v2_struct_0 @ sk_A)
% 2.25/2.45          | ~ (m1_pre_topc @ sk_B_1 @ X1)
% 2.25/2.45          | ~ (m1_pre_topc @ X0 @ X1))),
% 2.25/2.45      inference('demod', [status(thm)], ['163', '164', '165', '166', '167'])).
% 2.25/2.45  thf('169', plain,
% 2.25/2.45      (![X0 : $i]:
% 2.25/2.45         (~ (l1_pre_topc @ sk_B_1)
% 2.25/2.45          | ~ (m1_pre_topc @ X0 @ sk_B_1)
% 2.25/2.45          | (v2_struct_0 @ sk_A)
% 2.25/2.45          | ~ (l1_pre_topc @ sk_B_1)
% 2.25/2.45          | ~ (v2_pre_topc @ sk_B_1)
% 2.25/2.45          | (v2_struct_0 @ sk_B_1)
% 2.25/2.45          | (m1_subset_1 @ 
% 2.25/2.45             (k3_tmap_1 @ sk_B_1 @ sk_A @ sk_B_1 @ X0 @ 
% 2.25/2.45              (k4_tmap_1 @ sk_A @ sk_B_1)) @ 
% 2.25/2.45             (k1_zfmisc_1 @ 
% 2.25/2.45              (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A)))))),
% 2.25/2.45      inference('sup-', [status(thm)], ['160', '168'])).
% 2.25/2.45  thf('170', plain, ((l1_pre_topc @ sk_B_1)),
% 2.25/2.45      inference('demod', [status(thm)], ['33', '34'])).
% 2.25/2.45  thf('171', plain, ((l1_pre_topc @ sk_B_1)),
% 2.25/2.45      inference('demod', [status(thm)], ['33', '34'])).
% 2.25/2.45  thf('172', plain, ((v2_pre_topc @ sk_B_1)),
% 2.25/2.45      inference('demod', [status(thm)], ['38', '39', '40'])).
% 2.25/2.45  thf('173', plain,
% 2.25/2.45      (![X0 : $i]:
% 2.25/2.45         (~ (m1_pre_topc @ X0 @ sk_B_1)
% 2.25/2.45          | (v2_struct_0 @ sk_A)
% 2.25/2.45          | (v2_struct_0 @ sk_B_1)
% 2.25/2.45          | (m1_subset_1 @ 
% 2.25/2.45             (k3_tmap_1 @ sk_B_1 @ sk_A @ sk_B_1 @ X0 @ 
% 2.25/2.45              (k4_tmap_1 @ sk_A @ sk_B_1)) @ 
% 2.25/2.45             (k1_zfmisc_1 @ 
% 2.25/2.45              (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A)))))),
% 2.25/2.45      inference('demod', [status(thm)], ['169', '170', '171', '172'])).
% 2.25/2.45  thf('174', plain,
% 2.25/2.45      ((~ (l1_pre_topc @ sk_B_1)
% 2.25/2.45        | (m1_subset_1 @ 
% 2.25/2.45           (k3_tmap_1 @ sk_B_1 @ sk_A @ sk_B_1 @ sk_B_1 @ 
% 2.25/2.45            (k4_tmap_1 @ sk_A @ sk_B_1)) @ 
% 2.25/2.45           (k1_zfmisc_1 @ 
% 2.25/2.45            (k2_zfmisc_1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A))))
% 2.25/2.45        | (v2_struct_0 @ sk_B_1)
% 2.25/2.45        | (v2_struct_0 @ sk_A))),
% 2.25/2.45      inference('sup-', [status(thm)], ['159', '173'])).
% 2.25/2.45  thf('175', plain, ((l1_pre_topc @ sk_B_1)),
% 2.25/2.45      inference('demod', [status(thm)], ['33', '34'])).
% 2.25/2.45  thf('176', plain,
% 2.25/2.45      (((k3_tmap_1 @ sk_B_1 @ sk_A @ sk_B_1 @ sk_B_1 @ 
% 2.25/2.45         (k4_tmap_1 @ sk_A @ sk_B_1))
% 2.25/2.45         = (k2_tmap_1 @ sk_B_1 @ sk_A @ (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_B_1))),
% 2.25/2.45      inference('clc', [status(thm)], ['93', '94'])).
% 2.25/2.45  thf('177', plain,
% 2.25/2.45      (((m1_subset_1 @ 
% 2.25/2.45         (k2_tmap_1 @ sk_B_1 @ sk_A @ (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_B_1) @ 
% 2.25/2.45         (k1_zfmisc_1 @ 
% 2.25/2.45          (k2_zfmisc_1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A))))
% 2.25/2.45        | (v2_struct_0 @ sk_B_1)
% 2.25/2.45        | (v2_struct_0 @ sk_A))),
% 2.25/2.45      inference('demod', [status(thm)], ['174', '175', '176'])).
% 2.25/2.45  thf('178', plain, (~ (v2_struct_0 @ sk_B_1)),
% 2.25/2.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.25/2.45  thf('179', plain,
% 2.25/2.45      (((v2_struct_0 @ sk_A)
% 2.25/2.45        | (m1_subset_1 @ 
% 2.25/2.45           (k2_tmap_1 @ sk_B_1 @ sk_A @ (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_B_1) @ 
% 2.25/2.45           (k1_zfmisc_1 @ 
% 2.25/2.45            (k2_zfmisc_1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A)))))),
% 2.25/2.45      inference('clc', [status(thm)], ['177', '178'])).
% 2.25/2.45  thf('180', plain, (~ (v2_struct_0 @ sk_A)),
% 2.25/2.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.25/2.45  thf('181', plain,
% 2.25/2.45      ((m1_subset_1 @ 
% 2.25/2.45        (k2_tmap_1 @ sk_B_1 @ sk_A @ (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_B_1) @ 
% 2.25/2.45        (k1_zfmisc_1 @ 
% 2.25/2.45         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A))))),
% 2.25/2.45      inference('clc', [status(thm)], ['179', '180'])).
% 2.25/2.45  thf('182', plain,
% 2.25/2.45      (((k4_tmap_1 @ sk_A @ sk_B_1)
% 2.25/2.45         = (k2_tmap_1 @ sk_B_1 @ sk_A @ (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_B_1))),
% 2.25/2.45      inference('demod', [status(thm)], ['110', '134', '158', '181'])).
% 2.25/2.45  thf('183', plain,
% 2.25/2.45      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A))),
% 2.25/2.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.25/2.45  thf('184', plain, ((v1_funct_1 @ sk_C)),
% 2.25/2.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.25/2.45  thf('185', plain,
% 2.25/2.45      (((v2_struct_0 @ sk_B_1)
% 2.25/2.45        | (r2_hidden @ 
% 2.25/2.45           (sk_F @ sk_C @ (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_B_1 @ sk_B_1 @ sk_A) @ 
% 2.25/2.45           (u1_struct_0 @ sk_B_1))
% 2.25/2.45        | (r2_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 2.25/2.45           (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_C)
% 2.25/2.45        | ~ (m1_pre_topc @ sk_B_1 @ sk_B_1)
% 2.25/2.45        | (v2_struct_0 @ sk_B_1)
% 2.25/2.45        | (v2_struct_0 @ sk_A))),
% 2.25/2.45      inference('demod', [status(thm)], ['43', '182', '183', '184'])).
% 2.25/2.45  thf('186', plain,
% 2.25/2.45      (((v2_struct_0 @ sk_A)
% 2.25/2.45        | ~ (m1_pre_topc @ sk_B_1 @ sk_B_1)
% 2.25/2.45        | (r2_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 2.25/2.45           (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_C)
% 2.25/2.45        | (r2_hidden @ 
% 2.25/2.45           (sk_F @ sk_C @ (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_B_1 @ sk_B_1 @ sk_A) @ 
% 2.25/2.45           (u1_struct_0 @ sk_B_1))
% 2.25/2.45        | (v2_struct_0 @ sk_B_1))),
% 2.25/2.45      inference('simplify', [status(thm)], ['185'])).
% 2.25/2.45  thf('187', plain,
% 2.25/2.45      ((~ (l1_pre_topc @ sk_B_1)
% 2.25/2.45        | (v2_struct_0 @ sk_B_1)
% 2.25/2.45        | (r2_hidden @ 
% 2.25/2.45           (sk_F @ sk_C @ (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_B_1 @ sk_B_1 @ sk_A) @ 
% 2.25/2.45           (u1_struct_0 @ sk_B_1))
% 2.25/2.45        | (r2_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 2.25/2.45           (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_C)
% 2.25/2.45        | (v2_struct_0 @ sk_A))),
% 2.25/2.45      inference('sup-', [status(thm)], ['1', '186'])).
% 2.25/2.45  thf('188', plain, ((l1_pre_topc @ sk_B_1)),
% 2.25/2.45      inference('demod', [status(thm)], ['33', '34'])).
% 2.25/2.45  thf('189', plain,
% 2.25/2.45      (((v2_struct_0 @ sk_B_1)
% 2.25/2.45        | (r2_hidden @ 
% 2.25/2.45           (sk_F @ sk_C @ (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_B_1 @ sk_B_1 @ sk_A) @ 
% 2.25/2.45           (u1_struct_0 @ sk_B_1))
% 2.25/2.45        | (r2_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 2.25/2.45           (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_C)
% 2.25/2.45        | (v2_struct_0 @ sk_A))),
% 2.25/2.45      inference('demod', [status(thm)], ['187', '188'])).
% 2.25/2.45  thf(d1_xboole_0, axiom,
% 2.25/2.45    (![A:$i]:
% 2.25/2.45     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 2.25/2.45  thf('190', plain,
% 2.25/2.45      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 2.25/2.45      inference('cnf', [status(esa)], [d1_xboole_0])).
% 2.25/2.45  thf('191', plain,
% 2.25/2.45      (((v2_struct_0 @ sk_A)
% 2.25/2.45        | (r2_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 2.25/2.45           (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_C)
% 2.25/2.45        | (v2_struct_0 @ sk_B_1)
% 2.25/2.45        | ~ (v1_xboole_0 @ (u1_struct_0 @ sk_B_1)))),
% 2.25/2.45      inference('sup-', [status(thm)], ['189', '190'])).
% 2.25/2.45  thf('192', plain,
% 2.25/2.45      (![X36 : $i]: ((m1_pre_topc @ X36 @ X36) | ~ (l1_pre_topc @ X36))),
% 2.25/2.45      inference('cnf', [status(esa)], [t2_tsep_1])).
% 2.25/2.45  thf('193', plain, ((m1_pre_topc @ sk_B_1 @ sk_A)),
% 2.25/2.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.25/2.45  thf('194', plain,
% 2.25/2.45      (![X36 : $i]: ((m1_pre_topc @ X36 @ X36) | ~ (l1_pre_topc @ X36))),
% 2.25/2.45      inference('cnf', [status(esa)], [t2_tsep_1])).
% 2.25/2.45  thf('195', plain,
% 2.25/2.45      ((m1_subset_1 @ sk_C @ 
% 2.25/2.45        (k1_zfmisc_1 @ 
% 2.25/2.45         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A))))),
% 2.25/2.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.25/2.45  thf('196', plain,
% 2.25/2.45      ((m1_subset_1 @ (k4_tmap_1 @ sk_A @ sk_B_1) @ 
% 2.25/2.45        (k1_zfmisc_1 @ 
% 2.25/2.45         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A))))),
% 2.25/2.45      inference('clc', [status(thm)], ['8', '9'])).
% 2.25/2.45  thf('197', plain,
% 2.25/2.45      (![X37 : $i, X38 : $i, X39 : $i, X40 : $i, X41 : $i]:
% 2.25/2.45         ((v2_struct_0 @ X37)
% 2.25/2.45          | ~ (v2_pre_topc @ X37)
% 2.25/2.45          | ~ (l1_pre_topc @ X37)
% 2.25/2.45          | ~ (v1_funct_1 @ X38)
% 2.25/2.45          | ~ (v1_funct_2 @ X38 @ (u1_struct_0 @ X37) @ (u1_struct_0 @ X39))
% 2.25/2.45          | ~ (m1_subset_1 @ X38 @ 
% 2.25/2.45               (k1_zfmisc_1 @ 
% 2.25/2.45                (k2_zfmisc_1 @ (u1_struct_0 @ X37) @ (u1_struct_0 @ X39))))
% 2.25/2.45          | (m1_subset_1 @ (sk_F @ X40 @ X38 @ X41 @ X37 @ X39) @ 
% 2.25/2.45             (u1_struct_0 @ X37))
% 2.25/2.45          | (r2_funct_2 @ (u1_struct_0 @ X41) @ (u1_struct_0 @ X39) @ 
% 2.25/2.45             (k2_tmap_1 @ X37 @ X39 @ X38 @ X41) @ X40)
% 2.25/2.45          | ~ (m1_subset_1 @ X40 @ 
% 2.25/2.45               (k1_zfmisc_1 @ 
% 2.25/2.45                (k2_zfmisc_1 @ (u1_struct_0 @ X41) @ (u1_struct_0 @ X39))))
% 2.25/2.45          | ~ (v1_funct_2 @ X40 @ (u1_struct_0 @ X41) @ (u1_struct_0 @ X39))
% 2.25/2.45          | ~ (v1_funct_1 @ X40)
% 2.25/2.45          | ~ (m1_pre_topc @ X41 @ X37)
% 2.25/2.45          | (v2_struct_0 @ X41)
% 2.25/2.45          | ~ (l1_pre_topc @ X39)
% 2.25/2.45          | ~ (v2_pre_topc @ X39)
% 2.25/2.45          | (v2_struct_0 @ X39))),
% 2.25/2.45      inference('cnf', [status(esa)], [t59_tmap_1])).
% 2.25/2.45  thf('198', plain,
% 2.25/2.45      (![X0 : $i, X1 : $i]:
% 2.25/2.45         ((v2_struct_0 @ sk_A)
% 2.25/2.45          | ~ (v2_pre_topc @ sk_A)
% 2.25/2.45          | ~ (l1_pre_topc @ sk_A)
% 2.25/2.45          | (v2_struct_0 @ X0)
% 2.25/2.45          | ~ (m1_pre_topc @ X0 @ sk_B_1)
% 2.25/2.45          | ~ (v1_funct_1 @ X1)
% 2.25/2.45          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A))
% 2.25/2.45          | ~ (m1_subset_1 @ X1 @ 
% 2.25/2.45               (k1_zfmisc_1 @ 
% 2.25/2.45                (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A))))
% 2.25/2.45          | (r2_funct_2 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A) @ 
% 2.25/2.45             (k2_tmap_1 @ sk_B_1 @ sk_A @ (k4_tmap_1 @ sk_A @ sk_B_1) @ X0) @ 
% 2.25/2.45             X1)
% 2.25/2.45          | (m1_subset_1 @ 
% 2.25/2.45             (sk_F @ X1 @ (k4_tmap_1 @ sk_A @ sk_B_1) @ X0 @ sk_B_1 @ sk_A) @ 
% 2.25/2.45             (u1_struct_0 @ sk_B_1))
% 2.25/2.45          | ~ (v1_funct_2 @ (k4_tmap_1 @ sk_A @ sk_B_1) @ 
% 2.25/2.45               (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A))
% 2.25/2.45          | ~ (v1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_B_1))
% 2.25/2.45          | ~ (l1_pre_topc @ sk_B_1)
% 2.25/2.45          | ~ (v2_pre_topc @ sk_B_1)
% 2.25/2.45          | (v2_struct_0 @ sk_B_1))),
% 2.25/2.45      inference('sup-', [status(thm)], ['196', '197'])).
% 2.25/2.45  thf('199', plain, ((v2_pre_topc @ sk_A)),
% 2.25/2.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.25/2.45  thf('200', plain, ((l1_pre_topc @ sk_A)),
% 2.25/2.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.25/2.45  thf('201', plain,
% 2.25/2.45      ((v1_funct_2 @ (k4_tmap_1 @ sk_A @ sk_B_1) @ (u1_struct_0 @ sk_B_1) @ 
% 2.25/2.45        (u1_struct_0 @ sk_A))),
% 2.25/2.45      inference('clc', [status(thm)], ['20', '21'])).
% 2.25/2.45  thf('202', plain, ((v1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_B_1))),
% 2.25/2.45      inference('clc', [status(thm)], ['28', '29'])).
% 2.25/2.45  thf('203', plain, ((l1_pre_topc @ sk_B_1)),
% 2.25/2.45      inference('demod', [status(thm)], ['33', '34'])).
% 2.25/2.45  thf('204', plain, ((v2_pre_topc @ sk_B_1)),
% 2.25/2.45      inference('demod', [status(thm)], ['38', '39', '40'])).
% 2.25/2.45  thf('205', plain,
% 2.25/2.45      (![X0 : $i, X1 : $i]:
% 2.25/2.45         ((v2_struct_0 @ sk_A)
% 2.25/2.45          | (v2_struct_0 @ X0)
% 2.25/2.45          | ~ (m1_pre_topc @ X0 @ sk_B_1)
% 2.25/2.45          | ~ (v1_funct_1 @ X1)
% 2.25/2.45          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A))
% 2.25/2.45          | ~ (m1_subset_1 @ X1 @ 
% 2.25/2.45               (k1_zfmisc_1 @ 
% 2.25/2.45                (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A))))
% 2.25/2.45          | (r2_funct_2 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A) @ 
% 2.25/2.45             (k2_tmap_1 @ sk_B_1 @ sk_A @ (k4_tmap_1 @ sk_A @ sk_B_1) @ X0) @ 
% 2.25/2.45             X1)
% 2.25/2.45          | (m1_subset_1 @ 
% 2.25/2.45             (sk_F @ X1 @ (k4_tmap_1 @ sk_A @ sk_B_1) @ X0 @ sk_B_1 @ sk_A) @ 
% 2.25/2.45             (u1_struct_0 @ sk_B_1))
% 2.25/2.45          | (v2_struct_0 @ sk_B_1))),
% 2.25/2.45      inference('demod', [status(thm)],
% 2.25/2.45                ['198', '199', '200', '201', '202', '203', '204'])).
% 2.25/2.45  thf('206', plain,
% 2.25/2.45      (((v2_struct_0 @ sk_B_1)
% 2.25/2.45        | (m1_subset_1 @ 
% 2.25/2.45           (sk_F @ sk_C @ (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_B_1 @ sk_B_1 @ sk_A) @ 
% 2.25/2.45           (u1_struct_0 @ sk_B_1))
% 2.25/2.45        | (r2_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 2.25/2.45           (k2_tmap_1 @ sk_B_1 @ sk_A @ (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_B_1) @ 
% 2.25/2.45           sk_C)
% 2.25/2.45        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A))
% 2.25/2.45        | ~ (v1_funct_1 @ sk_C)
% 2.25/2.45        | ~ (m1_pre_topc @ sk_B_1 @ sk_B_1)
% 2.25/2.45        | (v2_struct_0 @ sk_B_1)
% 2.25/2.45        | (v2_struct_0 @ sk_A))),
% 2.25/2.45      inference('sup-', [status(thm)], ['195', '205'])).
% 2.25/2.45  thf('207', plain,
% 2.25/2.45      (((k4_tmap_1 @ sk_A @ sk_B_1)
% 2.25/2.45         = (k2_tmap_1 @ sk_B_1 @ sk_A @ (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_B_1))),
% 2.25/2.45      inference('demod', [status(thm)], ['110', '134', '158', '181'])).
% 2.25/2.45  thf('208', plain,
% 2.25/2.45      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A))),
% 2.25/2.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.25/2.45  thf('209', plain, ((v1_funct_1 @ sk_C)),
% 2.25/2.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.25/2.45  thf('210', plain,
% 2.25/2.45      (((v2_struct_0 @ sk_B_1)
% 2.25/2.45        | (m1_subset_1 @ 
% 2.25/2.45           (sk_F @ sk_C @ (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_B_1 @ sk_B_1 @ sk_A) @ 
% 2.25/2.45           (u1_struct_0 @ sk_B_1))
% 2.25/2.45        | (r2_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 2.25/2.45           (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_C)
% 2.25/2.45        | ~ (m1_pre_topc @ sk_B_1 @ sk_B_1)
% 2.25/2.45        | (v2_struct_0 @ sk_B_1)
% 2.25/2.45        | (v2_struct_0 @ sk_A))),
% 2.25/2.45      inference('demod', [status(thm)], ['206', '207', '208', '209'])).
% 2.25/2.45  thf('211', plain,
% 2.25/2.45      (((v2_struct_0 @ sk_A)
% 2.25/2.45        | ~ (m1_pre_topc @ sk_B_1 @ sk_B_1)
% 2.25/2.45        | (r2_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 2.25/2.45           (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_C)
% 2.25/2.45        | (m1_subset_1 @ 
% 2.25/2.45           (sk_F @ sk_C @ (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_B_1 @ sk_B_1 @ sk_A) @ 
% 2.25/2.45           (u1_struct_0 @ sk_B_1))
% 2.25/2.45        | (v2_struct_0 @ sk_B_1))),
% 2.25/2.45      inference('simplify', [status(thm)], ['210'])).
% 2.25/2.45  thf('212', plain,
% 2.25/2.45      ((~ (l1_pre_topc @ sk_B_1)
% 2.25/2.45        | (v2_struct_0 @ sk_B_1)
% 2.25/2.45        | (m1_subset_1 @ 
% 2.25/2.45           (sk_F @ sk_C @ (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_B_1 @ sk_B_1 @ sk_A) @ 
% 2.25/2.45           (u1_struct_0 @ sk_B_1))
% 2.25/2.45        | (r2_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 2.25/2.45           (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_C)
% 2.25/2.45        | (v2_struct_0 @ sk_A))),
% 2.25/2.45      inference('sup-', [status(thm)], ['194', '211'])).
% 2.25/2.45  thf('213', plain, ((l1_pre_topc @ sk_B_1)),
% 2.25/2.45      inference('demod', [status(thm)], ['33', '34'])).
% 2.25/2.45  thf('214', plain,
% 2.25/2.45      (((v2_struct_0 @ sk_B_1)
% 2.25/2.45        | (m1_subset_1 @ 
% 2.25/2.45           (sk_F @ sk_C @ (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_B_1 @ sk_B_1 @ sk_A) @ 
% 2.25/2.45           (u1_struct_0 @ sk_B_1))
% 2.25/2.45        | (r2_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 2.25/2.45           (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_C)
% 2.25/2.45        | (v2_struct_0 @ sk_A))),
% 2.25/2.45      inference('demod', [status(thm)], ['212', '213'])).
% 2.25/2.45  thf(t55_pre_topc, axiom,
% 2.25/2.45    (![A:$i]:
% 2.25/2.45     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 2.25/2.45       ( ![B:$i]:
% 2.25/2.45         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 2.25/2.45           ( ![C:$i]:
% 2.25/2.45             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ B ) ) =>
% 2.25/2.45               ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) ) ) ) ))).
% 2.25/2.45  thf('215', plain,
% 2.25/2.45      (![X17 : $i, X18 : $i, X19 : $i]:
% 2.25/2.45         ((v2_struct_0 @ X17)
% 2.25/2.45          | ~ (m1_pre_topc @ X17 @ X18)
% 2.25/2.45          | (m1_subset_1 @ X19 @ (u1_struct_0 @ X18))
% 2.25/2.45          | ~ (m1_subset_1 @ X19 @ (u1_struct_0 @ X17))
% 2.25/2.45          | ~ (l1_pre_topc @ X18)
% 2.25/2.45          | (v2_struct_0 @ X18))),
% 2.25/2.45      inference('cnf', [status(esa)], [t55_pre_topc])).
% 2.25/2.45  thf('216', plain,
% 2.25/2.45      (![X0 : $i]:
% 2.25/2.45         ((v2_struct_0 @ sk_A)
% 2.25/2.45          | (r2_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 2.25/2.45             (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_C)
% 2.25/2.45          | (v2_struct_0 @ sk_B_1)
% 2.25/2.45          | (v2_struct_0 @ X0)
% 2.25/2.45          | ~ (l1_pre_topc @ X0)
% 2.25/2.45          | (m1_subset_1 @ 
% 2.25/2.45             (sk_F @ sk_C @ (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_B_1 @ sk_B_1 @ 
% 2.25/2.45              sk_A) @ 
% 2.25/2.45             (u1_struct_0 @ X0))
% 2.25/2.45          | ~ (m1_pre_topc @ sk_B_1 @ X0)
% 2.25/2.45          | (v2_struct_0 @ sk_B_1))),
% 2.25/2.45      inference('sup-', [status(thm)], ['214', '215'])).
% 2.25/2.45  thf('217', plain,
% 2.25/2.45      (![X0 : $i]:
% 2.25/2.45         (~ (m1_pre_topc @ sk_B_1 @ X0)
% 2.25/2.45          | (m1_subset_1 @ 
% 2.25/2.45             (sk_F @ sk_C @ (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_B_1 @ sk_B_1 @ 
% 2.25/2.45              sk_A) @ 
% 2.25/2.45             (u1_struct_0 @ X0))
% 2.25/2.45          | ~ (l1_pre_topc @ X0)
% 2.25/2.45          | (v2_struct_0 @ X0)
% 2.25/2.45          | (v2_struct_0 @ sk_B_1)
% 2.25/2.45          | (r2_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 2.25/2.45             (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_C)
% 2.25/2.45          | (v2_struct_0 @ sk_A))),
% 2.25/2.45      inference('simplify', [status(thm)], ['216'])).
% 2.25/2.45  thf('218', plain,
% 2.25/2.45      (((v2_struct_0 @ sk_A)
% 2.25/2.45        | (r2_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 2.25/2.45           (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_C)
% 2.25/2.45        | (v2_struct_0 @ sk_B_1)
% 2.25/2.45        | (v2_struct_0 @ sk_A)
% 2.25/2.45        | ~ (l1_pre_topc @ sk_A)
% 2.25/2.45        | (m1_subset_1 @ 
% 2.25/2.45           (sk_F @ sk_C @ (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_B_1 @ sk_B_1 @ sk_A) @ 
% 2.25/2.45           (u1_struct_0 @ sk_A)))),
% 2.25/2.45      inference('sup-', [status(thm)], ['193', '217'])).
% 2.25/2.45  thf('219', plain, ((l1_pre_topc @ sk_A)),
% 2.25/2.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.25/2.45  thf('220', plain,
% 2.25/2.45      (((v2_struct_0 @ sk_A)
% 2.25/2.45        | (r2_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 2.25/2.45           (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_C)
% 2.25/2.45        | (v2_struct_0 @ sk_B_1)
% 2.25/2.45        | (v2_struct_0 @ sk_A)
% 2.25/2.45        | (m1_subset_1 @ 
% 2.25/2.45           (sk_F @ sk_C @ (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_B_1 @ sk_B_1 @ sk_A) @ 
% 2.25/2.45           (u1_struct_0 @ sk_A)))),
% 2.25/2.45      inference('demod', [status(thm)], ['218', '219'])).
% 2.25/2.45  thf('221', plain,
% 2.25/2.45      (((m1_subset_1 @ 
% 2.25/2.45         (sk_F @ sk_C @ (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_B_1 @ sk_B_1 @ sk_A) @ 
% 2.25/2.45         (u1_struct_0 @ sk_A))
% 2.25/2.45        | (v2_struct_0 @ sk_B_1)
% 2.25/2.45        | (r2_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 2.25/2.45           (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_C)
% 2.25/2.45        | (v2_struct_0 @ sk_A))),
% 2.25/2.45      inference('simplify', [status(thm)], ['220'])).
% 2.25/2.45  thf('222', plain,
% 2.25/2.45      (((v2_struct_0 @ sk_B_1)
% 2.25/2.45        | (r2_hidden @ 
% 2.25/2.45           (sk_F @ sk_C @ (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_B_1 @ sk_B_1 @ sk_A) @ 
% 2.25/2.45           (u1_struct_0 @ sk_B_1))
% 2.25/2.45        | (r2_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 2.25/2.45           (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_C)
% 2.25/2.45        | (v2_struct_0 @ sk_A))),
% 2.25/2.45      inference('demod', [status(thm)], ['187', '188'])).
% 2.25/2.45  thf('223', plain,
% 2.25/2.45      (![X52 : $i]:
% 2.25/2.45         (~ (r2_hidden @ X52 @ (u1_struct_0 @ sk_B_1))
% 2.25/2.45          | ((X52) = (k1_funct_1 @ sk_C @ X52))
% 2.25/2.45          | ~ (m1_subset_1 @ X52 @ (u1_struct_0 @ sk_A)))),
% 2.25/2.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.25/2.45  thf('224', plain,
% 2.25/2.45      (((v2_struct_0 @ sk_A)
% 2.25/2.45        | (r2_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 2.25/2.45           (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_C)
% 2.25/2.45        | (v2_struct_0 @ sk_B_1)
% 2.25/2.45        | ~ (m1_subset_1 @ 
% 2.25/2.45             (sk_F @ sk_C @ (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_B_1 @ sk_B_1 @ 
% 2.25/2.45              sk_A) @ 
% 2.25/2.45             (u1_struct_0 @ sk_A))
% 2.25/2.45        | ((sk_F @ sk_C @ (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_B_1 @ sk_B_1 @ sk_A)
% 2.25/2.45            = (k1_funct_1 @ sk_C @ 
% 2.25/2.45               (sk_F @ sk_C @ (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_B_1 @ sk_B_1 @ 
% 2.25/2.45                sk_A))))),
% 2.25/2.45      inference('sup-', [status(thm)], ['222', '223'])).
% 2.25/2.45  thf('225', plain,
% 2.25/2.45      (((v2_struct_0 @ sk_A)
% 2.25/2.45        | (r2_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 2.25/2.45           (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_C)
% 2.25/2.45        | (v2_struct_0 @ sk_B_1)
% 2.25/2.45        | ((sk_F @ sk_C @ (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_B_1 @ sk_B_1 @ sk_A)
% 2.25/2.45            = (k1_funct_1 @ sk_C @ 
% 2.25/2.45               (sk_F @ sk_C @ (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_B_1 @ sk_B_1 @ 
% 2.25/2.45                sk_A)))
% 2.25/2.45        | (v2_struct_0 @ sk_B_1)
% 2.25/2.45        | (r2_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 2.25/2.45           (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_C)
% 2.25/2.45        | (v2_struct_0 @ sk_A))),
% 2.25/2.45      inference('sup-', [status(thm)], ['221', '224'])).
% 2.25/2.45  thf('226', plain,
% 2.25/2.45      ((((sk_F @ sk_C @ (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_B_1 @ sk_B_1 @ sk_A)
% 2.25/2.45          = (k1_funct_1 @ sk_C @ 
% 2.25/2.45             (sk_F @ sk_C @ (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_B_1 @ sk_B_1 @ 
% 2.25/2.45              sk_A)))
% 2.25/2.45        | (v2_struct_0 @ sk_B_1)
% 2.25/2.45        | (r2_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 2.25/2.45           (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_C)
% 2.25/2.45        | (v2_struct_0 @ sk_A))),
% 2.25/2.45      inference('simplify', [status(thm)], ['225'])).
% 2.25/2.45  thf('227', plain,
% 2.25/2.45      (((m1_subset_1 @ 
% 2.25/2.45         (sk_F @ sk_C @ (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_B_1 @ sk_B_1 @ sk_A) @ 
% 2.25/2.45         (u1_struct_0 @ sk_A))
% 2.25/2.45        | (v2_struct_0 @ sk_B_1)
% 2.25/2.45        | (r2_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 2.25/2.45           (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_C)
% 2.25/2.45        | (v2_struct_0 @ sk_A))),
% 2.25/2.45      inference('simplify', [status(thm)], ['220'])).
% 2.25/2.45  thf('228', plain,
% 2.25/2.45      (((v2_struct_0 @ sk_B_1)
% 2.25/2.45        | (r2_hidden @ 
% 2.25/2.45           (sk_F @ sk_C @ (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_B_1 @ sk_B_1 @ sk_A) @ 
% 2.25/2.45           (u1_struct_0 @ sk_B_1))
% 2.25/2.45        | (r2_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 2.25/2.45           (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_C)
% 2.25/2.45        | (v2_struct_0 @ sk_A))),
% 2.25/2.45      inference('demod', [status(thm)], ['187', '188'])).
% 2.25/2.45  thf(t95_tmap_1, axiom,
% 2.25/2.45    (![A:$i]:
% 2.25/2.45     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 2.25/2.45       ( ![B:$i]:
% 2.25/2.45         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 2.25/2.45           ( ![C:$i]:
% 2.25/2.45             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 2.25/2.45               ( ( r2_hidden @ C @ ( u1_struct_0 @ B ) ) =>
% 2.25/2.45                 ( ( k1_funct_1 @ ( k4_tmap_1 @ A @ B ) @ C ) = ( C ) ) ) ) ) ) ) ))).
% 2.25/2.45  thf('229', plain,
% 2.25/2.45      (![X49 : $i, X50 : $i, X51 : $i]:
% 2.25/2.45         ((v2_struct_0 @ X49)
% 2.25/2.45          | ~ (m1_pre_topc @ X49 @ X50)
% 2.25/2.45          | ~ (r2_hidden @ X51 @ (u1_struct_0 @ X49))
% 2.25/2.45          | ((k1_funct_1 @ (k4_tmap_1 @ X50 @ X49) @ X51) = (X51))
% 2.25/2.45          | ~ (m1_subset_1 @ X51 @ (u1_struct_0 @ X50))
% 2.25/2.45          | ~ (l1_pre_topc @ X50)
% 2.25/2.45          | ~ (v2_pre_topc @ X50)
% 2.25/2.45          | (v2_struct_0 @ X50))),
% 2.25/2.45      inference('cnf', [status(esa)], [t95_tmap_1])).
% 2.25/2.45  thf('230', plain,
% 2.25/2.45      (![X0 : $i]:
% 2.25/2.45         ((v2_struct_0 @ sk_A)
% 2.25/2.45          | (r2_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 2.25/2.45             (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_C)
% 2.25/2.45          | (v2_struct_0 @ sk_B_1)
% 2.25/2.45          | (v2_struct_0 @ X0)
% 2.25/2.45          | ~ (v2_pre_topc @ X0)
% 2.25/2.45          | ~ (l1_pre_topc @ X0)
% 2.25/2.45          | ~ (m1_subset_1 @ 
% 2.25/2.45               (sk_F @ sk_C @ (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_B_1 @ sk_B_1 @ 
% 2.25/2.45                sk_A) @ 
% 2.25/2.45               (u1_struct_0 @ X0))
% 2.25/2.45          | ((k1_funct_1 @ (k4_tmap_1 @ X0 @ sk_B_1) @ 
% 2.25/2.45              (sk_F @ sk_C @ (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_B_1 @ sk_B_1 @ 
% 2.25/2.45               sk_A))
% 2.25/2.45              = (sk_F @ sk_C @ (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_B_1 @ sk_B_1 @ 
% 2.25/2.45                 sk_A))
% 2.25/2.45          | ~ (m1_pre_topc @ sk_B_1 @ X0)
% 2.25/2.45          | (v2_struct_0 @ sk_B_1))),
% 2.25/2.45      inference('sup-', [status(thm)], ['228', '229'])).
% 2.25/2.45  thf('231', plain,
% 2.25/2.45      (![X0 : $i]:
% 2.25/2.45         (~ (m1_pre_topc @ sk_B_1 @ X0)
% 2.25/2.45          | ((k1_funct_1 @ (k4_tmap_1 @ X0 @ sk_B_1) @ 
% 2.25/2.45              (sk_F @ sk_C @ (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_B_1 @ sk_B_1 @ 
% 2.25/2.45               sk_A))
% 2.25/2.45              = (sk_F @ sk_C @ (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_B_1 @ sk_B_1 @ 
% 2.25/2.45                 sk_A))
% 2.25/2.45          | ~ (m1_subset_1 @ 
% 2.25/2.45               (sk_F @ sk_C @ (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_B_1 @ sk_B_1 @ 
% 2.25/2.45                sk_A) @ 
% 2.25/2.45               (u1_struct_0 @ X0))
% 2.25/2.45          | ~ (l1_pre_topc @ X0)
% 2.25/2.45          | ~ (v2_pre_topc @ X0)
% 2.25/2.45          | (v2_struct_0 @ X0)
% 2.25/2.45          | (v2_struct_0 @ sk_B_1)
% 2.25/2.45          | (r2_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 2.25/2.45             (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_C)
% 2.25/2.45          | (v2_struct_0 @ sk_A))),
% 2.25/2.45      inference('simplify', [status(thm)], ['230'])).
% 2.25/2.45  thf('232', plain,
% 2.25/2.45      (((v2_struct_0 @ sk_A)
% 2.25/2.45        | (r2_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 2.25/2.45           (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_C)
% 2.25/2.45        | (v2_struct_0 @ sk_B_1)
% 2.25/2.45        | (v2_struct_0 @ sk_A)
% 2.25/2.45        | (r2_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 2.25/2.45           (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_C)
% 2.25/2.45        | (v2_struct_0 @ sk_B_1)
% 2.25/2.45        | (v2_struct_0 @ sk_A)
% 2.25/2.45        | ~ (v2_pre_topc @ sk_A)
% 2.25/2.45        | ~ (l1_pre_topc @ sk_A)
% 2.25/2.45        | ((k1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_B_1) @ 
% 2.25/2.45            (sk_F @ sk_C @ (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_B_1 @ sk_B_1 @ sk_A))
% 2.25/2.45            = (sk_F @ sk_C @ (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_B_1 @ sk_B_1 @ 
% 2.25/2.45               sk_A))
% 2.25/2.45        | ~ (m1_pre_topc @ sk_B_1 @ sk_A))),
% 2.25/2.45      inference('sup-', [status(thm)], ['227', '231'])).
% 2.25/2.45  thf('233', plain, ((v2_pre_topc @ sk_A)),
% 2.25/2.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.25/2.45  thf('234', plain, ((l1_pre_topc @ sk_A)),
% 2.25/2.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.25/2.45  thf('235', plain, ((m1_pre_topc @ sk_B_1 @ sk_A)),
% 2.25/2.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.25/2.45  thf('236', plain,
% 2.25/2.45      (((v2_struct_0 @ sk_A)
% 2.25/2.45        | (r2_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 2.25/2.45           (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_C)
% 2.25/2.45        | (v2_struct_0 @ sk_B_1)
% 2.25/2.45        | (v2_struct_0 @ sk_A)
% 2.25/2.45        | (r2_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 2.25/2.45           (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_C)
% 2.25/2.45        | (v2_struct_0 @ sk_B_1)
% 2.25/2.45        | (v2_struct_0 @ sk_A)
% 2.25/2.45        | ((k1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_B_1) @ 
% 2.25/2.45            (sk_F @ sk_C @ (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_B_1 @ sk_B_1 @ sk_A))
% 2.25/2.45            = (sk_F @ sk_C @ (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_B_1 @ sk_B_1 @ 
% 2.25/2.45               sk_A)))),
% 2.25/2.45      inference('demod', [status(thm)], ['232', '233', '234', '235'])).
% 2.25/2.45  thf('237', plain,
% 2.25/2.45      ((((k1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_B_1) @ 
% 2.25/2.45          (sk_F @ sk_C @ (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_B_1 @ sk_B_1 @ sk_A))
% 2.25/2.45          = (sk_F @ sk_C @ (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_B_1 @ sk_B_1 @ sk_A))
% 2.25/2.45        | (v2_struct_0 @ sk_B_1)
% 2.25/2.45        | (r2_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 2.25/2.45           (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_C)
% 2.25/2.45        | (v2_struct_0 @ sk_A))),
% 2.25/2.45      inference('simplify', [status(thm)], ['236'])).
% 2.25/2.45  thf('238', plain,
% 2.25/2.45      (((v2_struct_0 @ sk_B_1)
% 2.25/2.45        | (m1_subset_1 @ 
% 2.25/2.45           (sk_F @ sk_C @ (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_B_1 @ sk_B_1 @ sk_A) @ 
% 2.25/2.45           (u1_struct_0 @ sk_B_1))
% 2.25/2.45        | (r2_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 2.25/2.45           (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_C)
% 2.25/2.45        | (v2_struct_0 @ sk_A))),
% 2.25/2.45      inference('demod', [status(thm)], ['212', '213'])).
% 2.25/2.45  thf('239', plain,
% 2.25/2.45      ((m1_subset_1 @ (k4_tmap_1 @ sk_A @ sk_B_1) @ 
% 2.25/2.45        (k1_zfmisc_1 @ 
% 2.25/2.45         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A))))),
% 2.25/2.45      inference('clc', [status(thm)], ['8', '9'])).
% 2.25/2.45  thf(redefinition_k3_funct_2, axiom,
% 2.25/2.45    (![A:$i,B:$i,C:$i,D:$i]:
% 2.25/2.45     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_funct_1 @ C ) & 
% 2.25/2.45         ( v1_funct_2 @ C @ A @ B ) & 
% 2.25/2.45         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 2.25/2.45         ( m1_subset_1 @ D @ A ) ) =>
% 2.25/2.45       ( ( k3_funct_2 @ A @ B @ C @ D ) = ( k1_funct_1 @ C @ D ) ) ))).
% 2.25/2.45  thf('240', plain,
% 2.25/2.45      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 2.25/2.45         (~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X7)))
% 2.25/2.45          | ~ (v1_funct_2 @ X5 @ X6 @ X7)
% 2.25/2.45          | ~ (v1_funct_1 @ X5)
% 2.25/2.45          | (v1_xboole_0 @ X6)
% 2.25/2.45          | ~ (m1_subset_1 @ X8 @ X6)
% 2.25/2.45          | ((k3_funct_2 @ X6 @ X7 @ X5 @ X8) = (k1_funct_1 @ X5 @ X8)))),
% 2.25/2.45      inference('cnf', [status(esa)], [redefinition_k3_funct_2])).
% 2.25/2.45  thf('241', plain,
% 2.25/2.45      (![X0 : $i]:
% 2.25/2.45         (((k3_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 2.25/2.45            (k4_tmap_1 @ sk_A @ sk_B_1) @ X0)
% 2.25/2.45            = (k1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_B_1) @ X0))
% 2.25/2.45          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B_1))
% 2.25/2.45          | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 2.25/2.45          | ~ (v1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_B_1))
% 2.25/2.45          | ~ (v1_funct_2 @ (k4_tmap_1 @ sk_A @ sk_B_1) @ 
% 2.25/2.45               (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A)))),
% 2.25/2.45      inference('sup-', [status(thm)], ['239', '240'])).
% 2.25/2.45  thf('242', plain, ((v1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_B_1))),
% 2.25/2.45      inference('clc', [status(thm)], ['28', '29'])).
% 2.25/2.45  thf('243', plain,
% 2.25/2.45      ((v1_funct_2 @ (k4_tmap_1 @ sk_A @ sk_B_1) @ (u1_struct_0 @ sk_B_1) @ 
% 2.25/2.45        (u1_struct_0 @ sk_A))),
% 2.25/2.45      inference('clc', [status(thm)], ['20', '21'])).
% 2.25/2.45  thf('244', plain,
% 2.25/2.45      (![X0 : $i]:
% 2.25/2.45         (((k3_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 2.25/2.45            (k4_tmap_1 @ sk_A @ sk_B_1) @ X0)
% 2.25/2.45            = (k1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_B_1) @ X0))
% 2.25/2.45          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B_1))
% 2.25/2.45          | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1)))),
% 2.25/2.45      inference('demod', [status(thm)], ['241', '242', '243'])).
% 2.25/2.45  thf('245', plain,
% 2.25/2.45      (((v2_struct_0 @ sk_A)
% 2.25/2.45        | (r2_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 2.25/2.45           (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_C)
% 2.25/2.45        | (v2_struct_0 @ sk_B_1)
% 2.25/2.45        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 2.25/2.45        | ((k3_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 2.25/2.45            (k4_tmap_1 @ sk_A @ sk_B_1) @ 
% 2.25/2.45            (sk_F @ sk_C @ (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_B_1 @ sk_B_1 @ sk_A))
% 2.25/2.45            = (k1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_B_1) @ 
% 2.25/2.45               (sk_F @ sk_C @ (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_B_1 @ sk_B_1 @ 
% 2.25/2.45                sk_A))))),
% 2.25/2.45      inference('sup-', [status(thm)], ['238', '244'])).
% 2.25/2.45  thf('246', plain,
% 2.25/2.45      (![X37 : $i, X38 : $i, X39 : $i, X40 : $i, X41 : $i]:
% 2.25/2.45         ((v2_struct_0 @ X37)
% 2.25/2.45          | ~ (v2_pre_topc @ X37)
% 2.25/2.45          | ~ (l1_pre_topc @ X37)
% 2.25/2.45          | ~ (v1_funct_1 @ X38)
% 2.25/2.45          | ~ (v1_funct_2 @ X38 @ (u1_struct_0 @ X37) @ (u1_struct_0 @ X39))
% 2.25/2.45          | ~ (m1_subset_1 @ X38 @ 
% 2.25/2.45               (k1_zfmisc_1 @ 
% 2.25/2.45                (k2_zfmisc_1 @ (u1_struct_0 @ X37) @ (u1_struct_0 @ X39))))
% 2.25/2.45          | ((k3_funct_2 @ (u1_struct_0 @ X37) @ (u1_struct_0 @ X39) @ X38 @ 
% 2.25/2.45              (sk_F @ X40 @ X38 @ X41 @ X37 @ X39))
% 2.25/2.45              != (k1_funct_1 @ X40 @ (sk_F @ X40 @ X38 @ X41 @ X37 @ X39)))
% 2.25/2.45          | (r2_funct_2 @ (u1_struct_0 @ X41) @ (u1_struct_0 @ X39) @ 
% 2.25/2.45             (k2_tmap_1 @ X37 @ X39 @ X38 @ X41) @ X40)
% 2.25/2.45          | ~ (m1_subset_1 @ X40 @ 
% 2.25/2.45               (k1_zfmisc_1 @ 
% 2.25/2.45                (k2_zfmisc_1 @ (u1_struct_0 @ X41) @ (u1_struct_0 @ X39))))
% 2.25/2.45          | ~ (v1_funct_2 @ X40 @ (u1_struct_0 @ X41) @ (u1_struct_0 @ X39))
% 2.25/2.45          | ~ (v1_funct_1 @ X40)
% 2.25/2.45          | ~ (m1_pre_topc @ X41 @ X37)
% 2.25/2.45          | (v2_struct_0 @ X41)
% 2.25/2.45          | ~ (l1_pre_topc @ X39)
% 2.25/2.45          | ~ (v2_pre_topc @ X39)
% 2.25/2.45          | (v2_struct_0 @ X39))),
% 2.25/2.45      inference('cnf', [status(esa)], [t59_tmap_1])).
% 2.25/2.45  thf('247', plain,
% 2.25/2.45      ((((k1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_B_1) @ 
% 2.25/2.45          (sk_F @ sk_C @ (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_B_1 @ sk_B_1 @ sk_A))
% 2.25/2.45          != (k1_funct_1 @ sk_C @ 
% 2.25/2.45              (sk_F @ sk_C @ (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_B_1 @ sk_B_1 @ 
% 2.25/2.45               sk_A)))
% 2.25/2.45        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 2.25/2.45        | (v2_struct_0 @ sk_B_1)
% 2.25/2.45        | (r2_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 2.25/2.45           (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_C)
% 2.25/2.45        | (v2_struct_0 @ sk_A)
% 2.25/2.45        | (v2_struct_0 @ sk_A)
% 2.25/2.45        | ~ (v2_pre_topc @ sk_A)
% 2.25/2.45        | ~ (l1_pre_topc @ sk_A)
% 2.25/2.45        | (v2_struct_0 @ sk_B_1)
% 2.25/2.45        | ~ (m1_pre_topc @ sk_B_1 @ sk_B_1)
% 2.25/2.45        | ~ (v1_funct_1 @ sk_C)
% 2.25/2.45        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A))
% 2.25/2.45        | ~ (m1_subset_1 @ sk_C @ 
% 2.25/2.45             (k1_zfmisc_1 @ 
% 2.25/2.45              (k2_zfmisc_1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A))))
% 2.25/2.45        | (r2_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 2.25/2.45           (k2_tmap_1 @ sk_B_1 @ sk_A @ (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_B_1) @ 
% 2.25/2.45           sk_C)
% 2.25/2.45        | ~ (m1_subset_1 @ (k4_tmap_1 @ sk_A @ sk_B_1) @ 
% 2.25/2.45             (k1_zfmisc_1 @ 
% 2.25/2.45              (k2_zfmisc_1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A))))
% 2.25/2.45        | ~ (v1_funct_2 @ (k4_tmap_1 @ sk_A @ sk_B_1) @ 
% 2.25/2.45             (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A))
% 2.25/2.45        | ~ (v1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_B_1))
% 2.25/2.45        | ~ (l1_pre_topc @ sk_B_1)
% 2.25/2.45        | ~ (v2_pre_topc @ sk_B_1)
% 2.25/2.45        | (v2_struct_0 @ sk_B_1))),
% 2.25/2.45      inference('sup-', [status(thm)], ['245', '246'])).
% 2.25/2.45  thf('248', plain, ((v2_pre_topc @ sk_A)),
% 2.25/2.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.25/2.45  thf('249', plain, ((l1_pre_topc @ sk_A)),
% 2.25/2.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.25/2.45  thf('250', plain, ((v1_funct_1 @ sk_C)),
% 2.25/2.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.25/2.45  thf('251', plain,
% 2.25/2.45      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A))),
% 2.25/2.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.25/2.45  thf('252', plain,
% 2.25/2.45      ((m1_subset_1 @ sk_C @ 
% 2.25/2.45        (k1_zfmisc_1 @ 
% 2.25/2.45         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A))))),
% 2.25/2.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.25/2.45  thf('253', plain,
% 2.25/2.45      (((k4_tmap_1 @ sk_A @ sk_B_1)
% 2.25/2.45         = (k2_tmap_1 @ sk_B_1 @ sk_A @ (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_B_1))),
% 2.25/2.45      inference('demod', [status(thm)], ['110', '134', '158', '181'])).
% 2.25/2.45  thf('254', plain,
% 2.25/2.45      ((m1_subset_1 @ (k4_tmap_1 @ sk_A @ sk_B_1) @ 
% 2.25/2.45        (k1_zfmisc_1 @ 
% 2.25/2.45         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A))))),
% 2.25/2.45      inference('clc', [status(thm)], ['8', '9'])).
% 2.25/2.45  thf('255', plain,
% 2.25/2.45      ((v1_funct_2 @ (k4_tmap_1 @ sk_A @ sk_B_1) @ (u1_struct_0 @ sk_B_1) @ 
% 2.25/2.45        (u1_struct_0 @ sk_A))),
% 2.25/2.45      inference('clc', [status(thm)], ['20', '21'])).
% 2.25/2.45  thf('256', plain, ((v1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_B_1))),
% 2.25/2.45      inference('clc', [status(thm)], ['28', '29'])).
% 2.25/2.45  thf('257', plain, ((l1_pre_topc @ sk_B_1)),
% 2.25/2.45      inference('demod', [status(thm)], ['33', '34'])).
% 2.25/2.45  thf('258', plain, ((v2_pre_topc @ sk_B_1)),
% 2.25/2.45      inference('demod', [status(thm)], ['38', '39', '40'])).
% 2.25/2.45  thf('259', plain,
% 2.25/2.45      ((((k1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_B_1) @ 
% 2.25/2.45          (sk_F @ sk_C @ (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_B_1 @ sk_B_1 @ sk_A))
% 2.25/2.45          != (k1_funct_1 @ sk_C @ 
% 2.25/2.45              (sk_F @ sk_C @ (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_B_1 @ sk_B_1 @ 
% 2.25/2.45               sk_A)))
% 2.25/2.45        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 2.25/2.45        | (v2_struct_0 @ sk_B_1)
% 2.25/2.45        | (r2_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 2.25/2.45           (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_C)
% 2.25/2.45        | (v2_struct_0 @ sk_A)
% 2.25/2.45        | (v2_struct_0 @ sk_A)
% 2.25/2.45        | (v2_struct_0 @ sk_B_1)
% 2.25/2.45        | ~ (m1_pre_topc @ sk_B_1 @ sk_B_1)
% 2.25/2.45        | (r2_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 2.25/2.45           (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_C)
% 2.25/2.45        | (v2_struct_0 @ sk_B_1))),
% 2.25/2.45      inference('demod', [status(thm)],
% 2.25/2.45                ['247', '248', '249', '250', '251', '252', '253', '254', 
% 2.25/2.45                 '255', '256', '257', '258'])).
% 2.25/2.45  thf('260', plain,
% 2.25/2.45      ((~ (m1_pre_topc @ sk_B_1 @ sk_B_1)
% 2.25/2.45        | (v2_struct_0 @ sk_A)
% 2.25/2.45        | (r2_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 2.25/2.45           (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_C)
% 2.25/2.45        | (v2_struct_0 @ sk_B_1)
% 2.25/2.45        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 2.25/2.45        | ((k1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_B_1) @ 
% 2.25/2.45            (sk_F @ sk_C @ (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_B_1 @ sk_B_1 @ sk_A))
% 2.25/2.45            != (k1_funct_1 @ sk_C @ 
% 2.25/2.45                (sk_F @ sk_C @ (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_B_1 @ sk_B_1 @ 
% 2.25/2.45                 sk_A))))),
% 2.25/2.45      inference('simplify', [status(thm)], ['259'])).
% 2.25/2.45  thf('261', plain,
% 2.25/2.45      ((((sk_F @ sk_C @ (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_B_1 @ sk_B_1 @ sk_A)
% 2.25/2.45          != (k1_funct_1 @ sk_C @ 
% 2.25/2.45              (sk_F @ sk_C @ (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_B_1 @ sk_B_1 @ 
% 2.25/2.45               sk_A)))
% 2.25/2.45        | (v2_struct_0 @ sk_A)
% 2.25/2.45        | (r2_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 2.25/2.45           (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_C)
% 2.25/2.45        | (v2_struct_0 @ sk_B_1)
% 2.25/2.45        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 2.25/2.45        | (v2_struct_0 @ sk_B_1)
% 2.25/2.45        | (r2_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 2.25/2.45           (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_C)
% 2.25/2.45        | (v2_struct_0 @ sk_A)
% 2.25/2.45        | ~ (m1_pre_topc @ sk_B_1 @ sk_B_1))),
% 2.25/2.45      inference('sup-', [status(thm)], ['237', '260'])).
% 2.25/2.45  thf('262', plain,
% 2.25/2.45      ((~ (m1_pre_topc @ sk_B_1 @ sk_B_1)
% 2.25/2.45        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 2.25/2.45        | (v2_struct_0 @ sk_B_1)
% 2.25/2.45        | (r2_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 2.25/2.45           (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_C)
% 2.25/2.45        | (v2_struct_0 @ sk_A)
% 2.25/2.45        | ((sk_F @ sk_C @ (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_B_1 @ sk_B_1 @ sk_A)
% 2.25/2.45            != (k1_funct_1 @ sk_C @ 
% 2.25/2.45                (sk_F @ sk_C @ (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_B_1 @ sk_B_1 @ 
% 2.25/2.45                 sk_A))))),
% 2.25/2.45      inference('simplify', [status(thm)], ['261'])).
% 2.25/2.45  thf('263', plain,
% 2.25/2.45      ((((sk_F @ sk_C @ (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_B_1 @ sk_B_1 @ sk_A)
% 2.25/2.45          != (sk_F @ sk_C @ (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_B_1 @ sk_B_1 @ 
% 2.25/2.45              sk_A))
% 2.25/2.45        | (v2_struct_0 @ sk_A)
% 2.25/2.45        | (r2_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 2.25/2.45           (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_C)
% 2.25/2.45        | (v2_struct_0 @ sk_B_1)
% 2.25/2.45        | (v2_struct_0 @ sk_A)
% 2.25/2.45        | (r2_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 2.25/2.45           (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_C)
% 2.25/2.45        | (v2_struct_0 @ sk_B_1)
% 2.25/2.45        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 2.25/2.45        | ~ (m1_pre_topc @ sk_B_1 @ sk_B_1))),
% 2.25/2.45      inference('sup-', [status(thm)], ['226', '262'])).
% 2.25/2.45  thf('264', plain,
% 2.25/2.45      ((~ (m1_pre_topc @ sk_B_1 @ sk_B_1)
% 2.25/2.45        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 2.25/2.45        | (v2_struct_0 @ sk_B_1)
% 2.25/2.45        | (r2_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 2.25/2.45           (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_C)
% 2.25/2.45        | (v2_struct_0 @ sk_A))),
% 2.25/2.45      inference('simplify', [status(thm)], ['263'])).
% 2.25/2.45  thf('265', plain,
% 2.25/2.45      ((~ (l1_pre_topc @ sk_B_1)
% 2.25/2.45        | (v2_struct_0 @ sk_A)
% 2.25/2.45        | (r2_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 2.25/2.45           (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_C)
% 2.25/2.45        | (v2_struct_0 @ sk_B_1)
% 2.25/2.45        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1)))),
% 2.25/2.45      inference('sup-', [status(thm)], ['192', '264'])).
% 2.25/2.45  thf('266', plain, ((l1_pre_topc @ sk_B_1)),
% 2.25/2.45      inference('demod', [status(thm)], ['33', '34'])).
% 2.25/2.45  thf('267', plain,
% 2.25/2.45      (((v2_struct_0 @ sk_A)
% 2.25/2.45        | (r2_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 2.25/2.45           (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_C)
% 2.25/2.45        | (v2_struct_0 @ sk_B_1)
% 2.25/2.45        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1)))),
% 2.25/2.45      inference('demod', [status(thm)], ['265', '266'])).
% 2.25/2.45  thf('268', plain,
% 2.25/2.45      (~ (r2_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 2.25/2.45          (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_C)),
% 2.25/2.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.25/2.45  thf('269', plain,
% 2.25/2.45      (((v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 2.25/2.45        | (v2_struct_0 @ sk_B_1)
% 2.25/2.45        | (v2_struct_0 @ sk_A))),
% 2.25/2.45      inference('sup-', [status(thm)], ['267', '268'])).
% 2.25/2.45  thf('270', plain, (~ (v2_struct_0 @ sk_B_1)),
% 2.25/2.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.25/2.45  thf('271', plain,
% 2.25/2.45      (((v2_struct_0 @ sk_A) | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1)))),
% 2.25/2.45      inference('clc', [status(thm)], ['269', '270'])).
% 2.25/2.45  thf('272', plain, (~ (v2_struct_0 @ sk_A)),
% 2.25/2.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.25/2.45  thf('273', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_B_1))),
% 2.25/2.45      inference('clc', [status(thm)], ['271', '272'])).
% 2.25/2.45  thf('274', plain,
% 2.25/2.45      (((v2_struct_0 @ sk_A)
% 2.25/2.45        | (r2_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 2.25/2.45           (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_C)
% 2.25/2.45        | (v2_struct_0 @ sk_B_1))),
% 2.25/2.45      inference('demod', [status(thm)], ['191', '273'])).
% 2.25/2.45  thf('275', plain, (~ (v2_struct_0 @ sk_A)),
% 2.25/2.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.25/2.45  thf('276', plain,
% 2.25/2.45      (((v2_struct_0 @ sk_B_1)
% 2.25/2.45        | (r2_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 2.25/2.45           (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_C))),
% 2.25/2.45      inference('clc', [status(thm)], ['274', '275'])).
% 2.25/2.45  thf('277', plain, (~ (v2_struct_0 @ sk_B_1)),
% 2.25/2.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.25/2.45  thf('278', plain,
% 2.25/2.45      ((r2_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 2.25/2.45        (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_C)),
% 2.25/2.45      inference('clc', [status(thm)], ['276', '277'])).
% 2.25/2.45  thf('279', plain, ($false), inference('demod', [status(thm)], ['0', '278'])).
% 2.25/2.45  
% 2.25/2.45  % SZS output end Refutation
% 2.25/2.45  
% 2.25/2.45  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
