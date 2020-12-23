%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.9E5cplQ58W

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:13:45 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  113 ( 184 expanded)
%              Number of leaves         :   23 (  62 expanded)
%              Depth                    :   34
%              Number of atoms          : 1682 (3756 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   18 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v5_pre_topc_type,type,(
    v5_pre_topc: $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(v1_tdlat_3_type,type,(
    v1_tdlat_3: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(k7_tmap_1_type,type,(
    k7_tmap_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k6_tmap_1_type,type,(
    k6_tmap_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(t69_tex_2,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( ! [B: $i] :
            ( ( ~ ( v2_struct_0 @ B )
              & ( v2_pre_topc @ B )
              & ( l1_pre_topc @ B ) )
           => ! [C: $i] :
                ( ( ( v1_funct_1 @ C )
                  & ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
                  & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) )
               => ( v5_pre_topc @ C @ A @ B ) ) )
       => ( v1_tdlat_3 @ A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ( ! [B: $i] :
              ( ( ~ ( v2_struct_0 @ B )
                & ( v2_pre_topc @ B )
                & ( l1_pre_topc @ B ) )
             => ! [C: $i] :
                  ( ( ( v1_funct_1 @ C )
                    & ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
                    & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) )
                 => ( v5_pre_topc @ C @ A @ B ) ) )
         => ( v1_tdlat_3 @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t69_tex_2])).

thf('0',plain,(
    ~ ( v1_tdlat_3 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t17_tdlat_3,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( ( v1_tdlat_3 @ A )
      <=> ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( v3_pre_topc @ B @ A ) ) ) ) )).

thf('1',plain,(
    ! [X8: $i] :
      ( ( m1_subset_1 @ ( sk_B @ X8 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ( v1_tdlat_3 @ X8 )
      | ~ ( l1_pre_topc @ X8 )
      | ~ ( v2_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[t17_tdlat_3])).

thf(dt_k7_tmap_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( ( v1_funct_1 @ ( k7_tmap_1 @ A @ B ) )
        & ( v1_funct_2 @ ( k7_tmap_1 @ A @ B ) @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ A @ B ) ) )
        & ( m1_subset_1 @ ( k7_tmap_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ A @ B ) ) ) ) ) ) ) )).

thf('2',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( l1_pre_topc @ X2 )
      | ~ ( v2_pre_topc @ X2 )
      | ( v2_struct_0 @ X2 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X2 ) ) )
      | ( v1_funct_1 @ ( k7_tmap_1 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_tmap_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v1_tdlat_3 @ X0 )
      | ( v1_funct_1 @ ( k7_tmap_1 @ X0 @ ( sk_B @ X0 ) ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ( v1_funct_1 @ ( k7_tmap_1 @ X0 @ ( sk_B @ X0 ) ) )
      | ( v1_tdlat_3 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('5',plain,(
    ! [X8: $i] :
      ( ( m1_subset_1 @ ( sk_B @ X8 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ( v1_tdlat_3 @ X8 )
      | ~ ( l1_pre_topc @ X8 )
      | ~ ( v2_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[t17_tdlat_3])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ( v1_funct_1 @ ( k7_tmap_1 @ X0 @ ( sk_B @ X0 ) ) )
      | ( v1_tdlat_3 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('7',plain,(
    ! [X8: $i] :
      ( ( m1_subset_1 @ ( sk_B @ X8 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ( v1_tdlat_3 @ X8 )
      | ~ ( l1_pre_topc @ X8 )
      | ~ ( v2_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[t17_tdlat_3])).

thf(dt_k6_tmap_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( ( v1_pre_topc @ ( k6_tmap_1 @ A @ B ) )
        & ( v2_pre_topc @ ( k6_tmap_1 @ A @ B ) )
        & ( l1_pre_topc @ ( k6_tmap_1 @ A @ B ) ) ) ) )).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( l1_pre_topc @ ( k6_tmap_1 @ X0 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_tmap_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v1_tdlat_3 @ X0 )
      | ( l1_pre_topc @ ( k6_tmap_1 @ X0 @ ( sk_B @ X0 ) ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ( l1_pre_topc @ ( k6_tmap_1 @ X0 @ ( sk_B @ X0 ) ) )
      | ( v1_tdlat_3 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    ! [X8: $i] :
      ( ( m1_subset_1 @ ( sk_B @ X8 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ( v1_tdlat_3 @ X8 )
      | ~ ( l1_pre_topc @ X8 )
      | ~ ( v2_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[t17_tdlat_3])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( v2_pre_topc @ ( k6_tmap_1 @ X0 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_tmap_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v1_tdlat_3 @ X0 )
      | ( v2_pre_topc @ ( k6_tmap_1 @ X0 @ ( sk_B @ X0 ) ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ( v2_pre_topc @ ( k6_tmap_1 @ X0 @ ( sk_B @ X0 ) ) )
      | ( v1_tdlat_3 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    ! [X8: $i] :
      ( ( m1_subset_1 @ ( sk_B @ X8 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ( v1_tdlat_3 @ X8 )
      | ~ ( l1_pre_topc @ X8 )
      | ~ ( v2_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[t17_tdlat_3])).

thf('16',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( l1_pre_topc @ X2 )
      | ~ ( v2_pre_topc @ X2 )
      | ( v2_struct_0 @ X2 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X2 ) ) )
      | ( v1_funct_2 @ ( k7_tmap_1 @ X2 @ X3 ) @ ( u1_struct_0 @ X2 ) @ ( u1_struct_0 @ ( k6_tmap_1 @ X2 @ X3 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_tmap_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v1_tdlat_3 @ X0 )
      | ( v1_funct_2 @ ( k7_tmap_1 @ X0 @ ( sk_B @ X0 ) ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ ( k6_tmap_1 @ X0 @ ( sk_B @ X0 ) ) ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ( v1_funct_2 @ ( k7_tmap_1 @ X0 @ ( sk_B @ X0 ) ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ ( k6_tmap_1 @ X0 @ ( sk_B @ X0 ) ) ) )
      | ( v1_tdlat_3 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    ! [X8: $i] :
      ( ( m1_subset_1 @ ( sk_B @ X8 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ( v1_tdlat_3 @ X8 )
      | ~ ( l1_pre_topc @ X8 )
      | ~ ( v2_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[t17_tdlat_3])).

thf('20',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( l1_pre_topc @ X2 )
      | ~ ( v2_pre_topc @ X2 )
      | ( v2_struct_0 @ X2 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X2 ) ) )
      | ( m1_subset_1 @ ( k7_tmap_1 @ X2 @ X3 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X2 ) @ ( u1_struct_0 @ ( k6_tmap_1 @ X2 @ X3 ) ) ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_tmap_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v1_tdlat_3 @ X0 )
      | ( m1_subset_1 @ ( k7_tmap_1 @ X0 @ ( sk_B @ X0 ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ ( k6_tmap_1 @ X0 @ ( sk_B @ X0 ) ) ) ) ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ( m1_subset_1 @ ( k7_tmap_1 @ X0 @ ( sk_B @ X0 ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ ( k6_tmap_1 @ X0 @ ( sk_B @ X0 ) ) ) ) ) )
      | ( v1_tdlat_3 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_funct_2 @ X10 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X11 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X11 ) ) ) )
      | ( v5_pre_topc @ X10 @ sk_A @ X11 )
      | ~ ( l1_pre_topc @ X11 )
      | ~ ( v2_pre_topc @ X11 )
      | ( v2_struct_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v1_tdlat_3 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ ( k6_tmap_1 @ sk_A @ ( sk_B @ sk_A ) ) )
    | ~ ( v2_pre_topc @ ( k6_tmap_1 @ sk_A @ ( sk_B @ sk_A ) ) )
    | ~ ( l1_pre_topc @ ( k6_tmap_1 @ sk_A @ ( sk_B @ sk_A ) ) )
    | ( v5_pre_topc @ ( k7_tmap_1 @ sk_A @ ( sk_B @ sk_A ) ) @ sk_A @ ( k6_tmap_1 @ sk_A @ ( sk_B @ sk_A ) ) )
    | ~ ( v1_funct_2 @ ( k7_tmap_1 @ sk_A @ ( sk_B @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ ( sk_B @ sk_A ) ) ) )
    | ~ ( v1_funct_1 @ ( k7_tmap_1 @ sk_A @ ( sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,
    ( ( v1_tdlat_3 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ ( k6_tmap_1 @ sk_A @ ( sk_B @ sk_A ) ) )
    | ~ ( v2_pre_topc @ ( k6_tmap_1 @ sk_A @ ( sk_B @ sk_A ) ) )
    | ~ ( l1_pre_topc @ ( k6_tmap_1 @ sk_A @ ( sk_B @ sk_A ) ) )
    | ( v5_pre_topc @ ( k7_tmap_1 @ sk_A @ ( sk_B @ sk_A ) ) @ sk_A @ ( k6_tmap_1 @ sk_A @ ( sk_B @ sk_A ) ) )
    | ~ ( v1_funct_2 @ ( k7_tmap_1 @ sk_A @ ( sk_B @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ ( sk_B @ sk_A ) ) ) )
    | ~ ( v1_funct_1 @ ( k7_tmap_1 @ sk_A @ ( sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['24','25','26'])).

thf('28',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v1_tdlat_3 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v1_funct_1 @ ( k7_tmap_1 @ sk_A @ ( sk_B @ sk_A ) ) )
    | ( v5_pre_topc @ ( k7_tmap_1 @ sk_A @ ( sk_B @ sk_A ) ) @ sk_A @ ( k6_tmap_1 @ sk_A @ ( sk_B @ sk_A ) ) )
    | ~ ( l1_pre_topc @ ( k6_tmap_1 @ sk_A @ ( sk_B @ sk_A ) ) )
    | ~ ( v2_pre_topc @ ( k6_tmap_1 @ sk_A @ ( sk_B @ sk_A ) ) )
    | ( v2_struct_0 @ ( k6_tmap_1 @ sk_A @ ( sk_B @ sk_A ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_tdlat_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['18','27'])).

thf('29',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( v1_tdlat_3 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v1_funct_1 @ ( k7_tmap_1 @ sk_A @ ( sk_B @ sk_A ) ) )
    | ( v5_pre_topc @ ( k7_tmap_1 @ sk_A @ ( sk_B @ sk_A ) ) @ sk_A @ ( k6_tmap_1 @ sk_A @ ( sk_B @ sk_A ) ) )
    | ~ ( l1_pre_topc @ ( k6_tmap_1 @ sk_A @ ( sk_B @ sk_A ) ) )
    | ~ ( v2_pre_topc @ ( k6_tmap_1 @ sk_A @ ( sk_B @ sk_A ) ) )
    | ( v2_struct_0 @ ( k6_tmap_1 @ sk_A @ ( sk_B @ sk_A ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_tdlat_3 @ sk_A ) ),
    inference(demod,[status(thm)],['28','29','30'])).

thf('32',plain,
    ( ( v2_struct_0 @ ( k6_tmap_1 @ sk_A @ ( sk_B @ sk_A ) ) )
    | ~ ( v2_pre_topc @ ( k6_tmap_1 @ sk_A @ ( sk_B @ sk_A ) ) )
    | ~ ( l1_pre_topc @ ( k6_tmap_1 @ sk_A @ ( sk_B @ sk_A ) ) )
    | ( v5_pre_topc @ ( k7_tmap_1 @ sk_A @ ( sk_B @ sk_A ) ) @ sk_A @ ( k6_tmap_1 @ sk_A @ ( sk_B @ sk_A ) ) )
    | ~ ( v1_funct_1 @ ( k7_tmap_1 @ sk_A @ ( sk_B @ sk_A ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_tdlat_3 @ sk_A ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v1_tdlat_3 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v1_tdlat_3 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v1_funct_1 @ ( k7_tmap_1 @ sk_A @ ( sk_B @ sk_A ) ) )
    | ( v5_pre_topc @ ( k7_tmap_1 @ sk_A @ ( sk_B @ sk_A ) ) @ sk_A @ ( k6_tmap_1 @ sk_A @ ( sk_B @ sk_A ) ) )
    | ~ ( l1_pre_topc @ ( k6_tmap_1 @ sk_A @ ( sk_B @ sk_A ) ) )
    | ( v2_struct_0 @ ( k6_tmap_1 @ sk_A @ ( sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['14','32'])).

thf('34',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ( v1_tdlat_3 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v1_tdlat_3 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v1_funct_1 @ ( k7_tmap_1 @ sk_A @ ( sk_B @ sk_A ) ) )
    | ( v5_pre_topc @ ( k7_tmap_1 @ sk_A @ ( sk_B @ sk_A ) ) @ sk_A @ ( k6_tmap_1 @ sk_A @ ( sk_B @ sk_A ) ) )
    | ~ ( l1_pre_topc @ ( k6_tmap_1 @ sk_A @ ( sk_B @ sk_A ) ) )
    | ( v2_struct_0 @ ( k6_tmap_1 @ sk_A @ ( sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['33','34','35'])).

thf('37',plain,
    ( ( v2_struct_0 @ ( k6_tmap_1 @ sk_A @ ( sk_B @ sk_A ) ) )
    | ~ ( l1_pre_topc @ ( k6_tmap_1 @ sk_A @ ( sk_B @ sk_A ) ) )
    | ( v5_pre_topc @ ( k7_tmap_1 @ sk_A @ ( sk_B @ sk_A ) ) @ sk_A @ ( k6_tmap_1 @ sk_A @ ( sk_B @ sk_A ) ) )
    | ~ ( v1_funct_1 @ ( k7_tmap_1 @ sk_A @ ( sk_B @ sk_A ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_tdlat_3 @ sk_A ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v1_tdlat_3 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v1_tdlat_3 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v1_funct_1 @ ( k7_tmap_1 @ sk_A @ ( sk_B @ sk_A ) ) )
    | ( v5_pre_topc @ ( k7_tmap_1 @ sk_A @ ( sk_B @ sk_A ) ) @ sk_A @ ( k6_tmap_1 @ sk_A @ ( sk_B @ sk_A ) ) )
    | ( v2_struct_0 @ ( k6_tmap_1 @ sk_A @ ( sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['10','37'])).

thf('39',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,
    ( ( v1_tdlat_3 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v1_tdlat_3 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v1_funct_1 @ ( k7_tmap_1 @ sk_A @ ( sk_B @ sk_A ) ) )
    | ( v5_pre_topc @ ( k7_tmap_1 @ sk_A @ ( sk_B @ sk_A ) ) @ sk_A @ ( k6_tmap_1 @ sk_A @ ( sk_B @ sk_A ) ) )
    | ( v2_struct_0 @ ( k6_tmap_1 @ sk_A @ ( sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['38','39','40'])).

thf('42',plain,
    ( ( v2_struct_0 @ ( k6_tmap_1 @ sk_A @ ( sk_B @ sk_A ) ) )
    | ( v5_pre_topc @ ( k7_tmap_1 @ sk_A @ ( sk_B @ sk_A ) ) @ sk_A @ ( k6_tmap_1 @ sk_A @ ( sk_B @ sk_A ) ) )
    | ~ ( v1_funct_1 @ ( k7_tmap_1 @ sk_A @ ( sk_B @ sk_A ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_tdlat_3 @ sk_A ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v1_tdlat_3 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v1_tdlat_3 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v5_pre_topc @ ( k7_tmap_1 @ sk_A @ ( sk_B @ sk_A ) ) @ sk_A @ ( k6_tmap_1 @ sk_A @ ( sk_B @ sk_A ) ) )
    | ( v2_struct_0 @ ( k6_tmap_1 @ sk_A @ ( sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['6','42'])).

thf('44',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( ( v1_tdlat_3 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v1_tdlat_3 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v5_pre_topc @ ( k7_tmap_1 @ sk_A @ ( sk_B @ sk_A ) ) @ sk_A @ ( k6_tmap_1 @ sk_A @ ( sk_B @ sk_A ) ) )
    | ( v2_struct_0 @ ( k6_tmap_1 @ sk_A @ ( sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['43','44','45'])).

thf('47',plain,
    ( ( v2_struct_0 @ ( k6_tmap_1 @ sk_A @ ( sk_B @ sk_A ) ) )
    | ( v5_pre_topc @ ( k7_tmap_1 @ sk_A @ ( sk_B @ sk_A ) ) @ sk_A @ ( k6_tmap_1 @ sk_A @ ( sk_B @ sk_A ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_tdlat_3 @ sk_A ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ( v1_funct_2 @ ( k7_tmap_1 @ X0 @ ( sk_B @ X0 ) ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ ( k6_tmap_1 @ X0 @ ( sk_B @ X0 ) ) ) )
      | ( v1_tdlat_3 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ( m1_subset_1 @ ( k7_tmap_1 @ X0 @ ( sk_B @ X0 ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ ( k6_tmap_1 @ X0 @ ( sk_B @ X0 ) ) ) ) ) )
      | ( v1_tdlat_3 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf(t113_tmap_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v3_pre_topc @ B @ A )
          <=> ( ( v1_funct_1 @ ( k7_tmap_1 @ A @ B ) )
              & ( v1_funct_2 @ ( k7_tmap_1 @ A @ B ) @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ A @ B ) ) )
              & ( v5_pre_topc @ ( k7_tmap_1 @ A @ B ) @ A @ ( k6_tmap_1 @ A @ B ) )
              & ( m1_subset_1 @ ( k7_tmap_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ A @ B ) ) ) ) ) ) ) ) ) )).

thf('50',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) )
      | ~ ( v1_funct_1 @ ( k7_tmap_1 @ X7 @ X6 ) )
      | ~ ( v1_funct_2 @ ( k7_tmap_1 @ X7 @ X6 ) @ ( u1_struct_0 @ X7 ) @ ( u1_struct_0 @ ( k6_tmap_1 @ X7 @ X6 ) ) )
      | ~ ( v5_pre_topc @ ( k7_tmap_1 @ X7 @ X6 ) @ X7 @ ( k6_tmap_1 @ X7 @ X6 ) )
      | ~ ( m1_subset_1 @ ( k7_tmap_1 @ X7 @ X6 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X7 ) @ ( u1_struct_0 @ ( k6_tmap_1 @ X7 @ X6 ) ) ) ) )
      | ( v3_pre_topc @ X6 @ X7 )
      | ~ ( l1_pre_topc @ X7 )
      | ~ ( v2_pre_topc @ X7 )
      | ( v2_struct_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t113_tmap_1])).

thf('51',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v1_tdlat_3 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v3_pre_topc @ ( sk_B @ X0 ) @ X0 )
      | ~ ( v5_pre_topc @ ( k7_tmap_1 @ X0 @ ( sk_B @ X0 ) ) @ X0 @ ( k6_tmap_1 @ X0 @ ( sk_B @ X0 ) ) )
      | ~ ( v1_funct_2 @ ( k7_tmap_1 @ X0 @ ( sk_B @ X0 ) ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ ( k6_tmap_1 @ X0 @ ( sk_B @ X0 ) ) ) )
      | ~ ( v1_funct_1 @ ( k7_tmap_1 @ X0 @ ( sk_B @ X0 ) ) )
      | ~ ( m1_subset_1 @ ( sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ ( sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( v1_funct_1 @ ( k7_tmap_1 @ X0 @ ( sk_B @ X0 ) ) )
      | ~ ( v1_funct_2 @ ( k7_tmap_1 @ X0 @ ( sk_B @ X0 ) ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ ( k6_tmap_1 @ X0 @ ( sk_B @ X0 ) ) ) )
      | ~ ( v5_pre_topc @ ( k7_tmap_1 @ X0 @ ( sk_B @ X0 ) ) @ X0 @ ( k6_tmap_1 @ X0 @ ( sk_B @ X0 ) ) )
      | ( v3_pre_topc @ ( sk_B @ X0 ) @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( v1_tdlat_3 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v1_tdlat_3 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v1_tdlat_3 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( v3_pre_topc @ ( sk_B @ X0 ) @ X0 )
      | ~ ( v5_pre_topc @ ( k7_tmap_1 @ X0 @ ( sk_B @ X0 ) ) @ X0 @ ( k6_tmap_1 @ X0 @ ( sk_B @ X0 ) ) )
      | ~ ( v1_funct_1 @ ( k7_tmap_1 @ X0 @ ( sk_B @ X0 ) ) )
      | ~ ( m1_subset_1 @ ( sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['48','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ ( sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( v1_funct_1 @ ( k7_tmap_1 @ X0 @ ( sk_B @ X0 ) ) )
      | ~ ( v5_pre_topc @ ( k7_tmap_1 @ X0 @ ( sk_B @ X0 ) ) @ X0 @ ( k6_tmap_1 @ X0 @ ( sk_B @ X0 ) ) )
      | ( v3_pre_topc @ ( sk_B @ X0 ) @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( v1_tdlat_3 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['53'])).

thf('55',plain,
    ( ( v1_tdlat_3 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ ( k6_tmap_1 @ sk_A @ ( sk_B @ sk_A ) ) )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v1_tdlat_3 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v3_pre_topc @ ( sk_B @ sk_A ) @ sk_A )
    | ~ ( v1_funct_1 @ ( k7_tmap_1 @ sk_A @ ( sk_B @ sk_A ) ) )
    | ~ ( m1_subset_1 @ ( sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['47','54'])).

thf('56',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,
    ( ( v1_tdlat_3 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ ( k6_tmap_1 @ sk_A @ ( sk_B @ sk_A ) ) )
    | ( v1_tdlat_3 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v3_pre_topc @ ( sk_B @ sk_A ) @ sk_A )
    | ~ ( v1_funct_1 @ ( k7_tmap_1 @ sk_A @ ( sk_B @ sk_A ) ) )
    | ~ ( m1_subset_1 @ ( sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['55','56','57'])).

thf('59',plain,
    ( ~ ( m1_subset_1 @ ( sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( v1_funct_1 @ ( k7_tmap_1 @ sk_A @ ( sk_B @ sk_A ) ) )
    | ( v3_pre_topc @ ( sk_B @ sk_A ) @ sk_A )
    | ( v2_struct_0 @ ( k6_tmap_1 @ sk_A @ ( sk_B @ sk_A ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_tdlat_3 @ sk_A ) ),
    inference(simplify,[status(thm)],['58'])).

thf('60',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v1_tdlat_3 @ sk_A )
    | ( v1_tdlat_3 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ ( k6_tmap_1 @ sk_A @ ( sk_B @ sk_A ) ) )
    | ( v3_pre_topc @ ( sk_B @ sk_A ) @ sk_A )
    | ~ ( v1_funct_1 @ ( k7_tmap_1 @ sk_A @ ( sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['5','59'])).

thf('61',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,
    ( ( v1_tdlat_3 @ sk_A )
    | ( v1_tdlat_3 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ ( k6_tmap_1 @ sk_A @ ( sk_B @ sk_A ) ) )
    | ( v3_pre_topc @ ( sk_B @ sk_A ) @ sk_A )
    | ~ ( v1_funct_1 @ ( k7_tmap_1 @ sk_A @ ( sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['60','61','62'])).

thf('64',plain,
    ( ~ ( v1_funct_1 @ ( k7_tmap_1 @ sk_A @ ( sk_B @ sk_A ) ) )
    | ( v3_pre_topc @ ( sk_B @ sk_A ) @ sk_A )
    | ( v2_struct_0 @ ( k6_tmap_1 @ sk_A @ ( sk_B @ sk_A ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_tdlat_3 @ sk_A ) ),
    inference(simplify,[status(thm)],['63'])).

thf('65',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v1_tdlat_3 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v1_tdlat_3 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ ( k6_tmap_1 @ sk_A @ ( sk_B @ sk_A ) ) )
    | ( v3_pre_topc @ ( sk_B @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['4','64'])).

thf('66',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,
    ( ( v1_tdlat_3 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v1_tdlat_3 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ ( k6_tmap_1 @ sk_A @ ( sk_B @ sk_A ) ) )
    | ( v3_pre_topc @ ( sk_B @ sk_A ) @ sk_A ) ),
    inference(demod,[status(thm)],['65','66','67'])).

thf('69',plain,
    ( ( v3_pre_topc @ ( sk_B @ sk_A ) @ sk_A )
    | ( v2_struct_0 @ ( k6_tmap_1 @ sk_A @ ( sk_B @ sk_A ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_tdlat_3 @ sk_A ) ),
    inference(simplify,[status(thm)],['68'])).

thf('70',plain,(
    ! [X8: $i] :
      ( ( m1_subset_1 @ ( sk_B @ X8 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ( v1_tdlat_3 @ X8 )
      | ~ ( l1_pre_topc @ X8 )
      | ~ ( v2_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[t17_tdlat_3])).

thf(fc4_tmap_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( ~ ( v2_struct_0 @ ( k6_tmap_1 @ A @ B ) )
        & ( v1_pre_topc @ ( k6_tmap_1 @ A @ B ) )
        & ( v2_pre_topc @ ( k6_tmap_1 @ A @ B ) ) ) ) )).

thf('71',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( l1_pre_topc @ X4 )
      | ~ ( v2_pre_topc @ X4 )
      | ( v2_struct_0 @ X4 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X4 ) ) )
      | ~ ( v2_struct_0 @ ( k6_tmap_1 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[fc4_tmap_1])).

thf('72',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v1_tdlat_3 @ X0 )
      | ~ ( v2_struct_0 @ ( k6_tmap_1 @ X0 @ ( sk_B @ X0 ) ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_struct_0 @ ( k6_tmap_1 @ X0 @ ( sk_B @ X0 ) ) )
      | ( v1_tdlat_3 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['72'])).

thf('74',plain,
    ( ( v1_tdlat_3 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v3_pre_topc @ ( sk_B @ sk_A ) @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v1_tdlat_3 @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['69','73'])).

thf('75',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,
    ( ( v1_tdlat_3 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v3_pre_topc @ ( sk_B @ sk_A ) @ sk_A )
    | ( v1_tdlat_3 @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['74','75','76'])).

thf('78',plain,
    ( ( v3_pre_topc @ ( sk_B @ sk_A ) @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v1_tdlat_3 @ sk_A ) ),
    inference(simplify,[status(thm)],['77'])).

thf('79',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,
    ( ( v1_tdlat_3 @ sk_A )
    | ( v3_pre_topc @ ( sk_B @ sk_A ) @ sk_A ) ),
    inference(clc,[status(thm)],['78','79'])).

thf('81',plain,(
    ~ ( v1_tdlat_3 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    v3_pre_topc @ ( sk_B @ sk_A ) @ sk_A ),
    inference(clc,[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X8: $i] :
      ( ~ ( v3_pre_topc @ ( sk_B @ X8 ) @ X8 )
      | ( v1_tdlat_3 @ X8 )
      | ~ ( l1_pre_topc @ X8 )
      | ~ ( v2_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[t17_tdlat_3])).

thf('84',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v1_tdlat_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    v1_tdlat_3 @ sk_A ),
    inference(demod,[status(thm)],['84','85','86'])).

thf('88',plain,(
    $false ),
    inference(demod,[status(thm)],['0','87'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.9E5cplQ58W
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 17:56:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.22/0.50  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.22/0.50  % Solved by: fo/fo7.sh
% 0.22/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.50  % done 41 iterations in 0.033s
% 0.22/0.50  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.22/0.50  % SZS output start Refutation
% 0.22/0.50  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 0.22/0.50  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.22/0.50  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.22/0.50  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.22/0.50  thf(v5_pre_topc_type, type, v5_pre_topc: $i > $i > $i > $o).
% 0.22/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.50  thf(sk_B_type, type, sk_B: $i > $i).
% 0.22/0.50  thf(v1_tdlat_3_type, type, v1_tdlat_3: $i > $o).
% 0.22/0.50  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.22/0.50  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.22/0.50  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.22/0.50  thf(k7_tmap_1_type, type, k7_tmap_1: $i > $i > $i).
% 0.22/0.50  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.22/0.50  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.22/0.50  thf(k6_tmap_1_type, type, k6_tmap_1: $i > $i > $i).
% 0.22/0.50  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.22/0.50  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.22/0.50  thf(t69_tex_2, conjecture,
% 0.22/0.50    (![A:$i]:
% 0.22/0.50     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.22/0.50       ( ( ![B:$i]:
% 0.22/0.50           ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.22/0.50               ( l1_pre_topc @ B ) ) =>
% 0.22/0.50             ( ![C:$i]:
% 0.22/0.50               ( ( ( v1_funct_1 @ C ) & 
% 0.22/0.50                   ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.22/0.50                   ( m1_subset_1 @
% 0.22/0.50                     C @ 
% 0.22/0.50                     ( k1_zfmisc_1 @
% 0.22/0.50                       ( k2_zfmisc_1 @
% 0.22/0.50                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.22/0.50                 ( v5_pre_topc @ C @ A @ B ) ) ) ) ) =>
% 0.22/0.50         ( v1_tdlat_3 @ A ) ) ))).
% 0.22/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.50    (~( ![A:$i]:
% 0.22/0.50        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.22/0.50            ( l1_pre_topc @ A ) ) =>
% 0.22/0.50          ( ( ![B:$i]:
% 0.22/0.50              ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.22/0.50                  ( l1_pre_topc @ B ) ) =>
% 0.22/0.50                ( ![C:$i]:
% 0.22/0.50                  ( ( ( v1_funct_1 @ C ) & 
% 0.22/0.50                      ( v1_funct_2 @
% 0.22/0.50                        C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.22/0.50                      ( m1_subset_1 @
% 0.22/0.50                        C @ 
% 0.22/0.50                        ( k1_zfmisc_1 @
% 0.22/0.50                          ( k2_zfmisc_1 @
% 0.22/0.50                            ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.22/0.50                    ( v5_pre_topc @ C @ A @ B ) ) ) ) ) =>
% 0.22/0.50            ( v1_tdlat_3 @ A ) ) ) )),
% 0.22/0.50    inference('cnf.neg', [status(esa)], [t69_tex_2])).
% 0.22/0.50  thf('0', plain, (~ (v1_tdlat_3 @ sk_A)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf(t17_tdlat_3, axiom,
% 0.22/0.50    (![A:$i]:
% 0.22/0.50     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.22/0.50       ( ( v1_tdlat_3 @ A ) <=>
% 0.22/0.50         ( ![B:$i]:
% 0.22/0.50           ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.50             ( v3_pre_topc @ B @ A ) ) ) ) ))).
% 0.22/0.50  thf('1', plain,
% 0.22/0.50      (![X8 : $i]:
% 0.22/0.50         ((m1_subset_1 @ (sk_B @ X8) @ (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 0.22/0.50          | (v1_tdlat_3 @ X8)
% 0.22/0.50          | ~ (l1_pre_topc @ X8)
% 0.22/0.50          | ~ (v2_pre_topc @ X8))),
% 0.22/0.50      inference('cnf', [status(esa)], [t17_tdlat_3])).
% 0.22/0.50  thf(dt_k7_tmap_1, axiom,
% 0.22/0.50    (![A:$i,B:$i]:
% 0.22/0.50     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.22/0.50         ( l1_pre_topc @ A ) & 
% 0.22/0.50         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.22/0.50       ( ( v1_funct_1 @ ( k7_tmap_1 @ A @ B ) ) & 
% 0.22/0.50         ( v1_funct_2 @
% 0.22/0.50           ( k7_tmap_1 @ A @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.22/0.50           ( u1_struct_0 @ ( k6_tmap_1 @ A @ B ) ) ) & 
% 0.22/0.50         ( m1_subset_1 @
% 0.22/0.50           ( k7_tmap_1 @ A @ B ) @ 
% 0.22/0.50           ( k1_zfmisc_1 @
% 0.22/0.50             ( k2_zfmisc_1 @
% 0.22/0.50               ( u1_struct_0 @ A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ A @ B ) ) ) ) ) ) ))).
% 0.22/0.50  thf('2', plain,
% 0.22/0.50      (![X2 : $i, X3 : $i]:
% 0.22/0.50         (~ (l1_pre_topc @ X2)
% 0.22/0.50          | ~ (v2_pre_topc @ X2)
% 0.22/0.50          | (v2_struct_0 @ X2)
% 0.22/0.50          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (u1_struct_0 @ X2)))
% 0.22/0.50          | (v1_funct_1 @ (k7_tmap_1 @ X2 @ X3)))),
% 0.22/0.50      inference('cnf', [status(esa)], [dt_k7_tmap_1])).
% 0.22/0.50  thf('3', plain,
% 0.22/0.50      (![X0 : $i]:
% 0.22/0.50         (~ (v2_pre_topc @ X0)
% 0.22/0.50          | ~ (l1_pre_topc @ X0)
% 0.22/0.50          | (v1_tdlat_3 @ X0)
% 0.22/0.50          | (v1_funct_1 @ (k7_tmap_1 @ X0 @ (sk_B @ X0)))
% 0.22/0.50          | (v2_struct_0 @ X0)
% 0.22/0.50          | ~ (v2_pre_topc @ X0)
% 0.22/0.50          | ~ (l1_pre_topc @ X0))),
% 0.22/0.50      inference('sup-', [status(thm)], ['1', '2'])).
% 0.22/0.50  thf('4', plain,
% 0.22/0.50      (![X0 : $i]:
% 0.22/0.50         ((v2_struct_0 @ X0)
% 0.22/0.50          | (v1_funct_1 @ (k7_tmap_1 @ X0 @ (sk_B @ X0)))
% 0.22/0.50          | (v1_tdlat_3 @ X0)
% 0.22/0.50          | ~ (l1_pre_topc @ X0)
% 0.22/0.50          | ~ (v2_pre_topc @ X0))),
% 0.22/0.50      inference('simplify', [status(thm)], ['3'])).
% 0.22/0.50  thf('5', plain,
% 0.22/0.50      (![X8 : $i]:
% 0.22/0.50         ((m1_subset_1 @ (sk_B @ X8) @ (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 0.22/0.50          | (v1_tdlat_3 @ X8)
% 0.22/0.50          | ~ (l1_pre_topc @ X8)
% 0.22/0.50          | ~ (v2_pre_topc @ X8))),
% 0.22/0.50      inference('cnf', [status(esa)], [t17_tdlat_3])).
% 0.22/0.50  thf('6', plain,
% 0.22/0.50      (![X0 : $i]:
% 0.22/0.50         ((v2_struct_0 @ X0)
% 0.22/0.50          | (v1_funct_1 @ (k7_tmap_1 @ X0 @ (sk_B @ X0)))
% 0.22/0.50          | (v1_tdlat_3 @ X0)
% 0.22/0.50          | ~ (l1_pre_topc @ X0)
% 0.22/0.50          | ~ (v2_pre_topc @ X0))),
% 0.22/0.50      inference('simplify', [status(thm)], ['3'])).
% 0.22/0.50  thf('7', plain,
% 0.22/0.50      (![X8 : $i]:
% 0.22/0.50         ((m1_subset_1 @ (sk_B @ X8) @ (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 0.22/0.50          | (v1_tdlat_3 @ X8)
% 0.22/0.50          | ~ (l1_pre_topc @ X8)
% 0.22/0.50          | ~ (v2_pre_topc @ X8))),
% 0.22/0.50      inference('cnf', [status(esa)], [t17_tdlat_3])).
% 0.22/0.50  thf(dt_k6_tmap_1, axiom,
% 0.22/0.50    (![A:$i,B:$i]:
% 0.22/0.50     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.22/0.50         ( l1_pre_topc @ A ) & 
% 0.22/0.50         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.22/0.50       ( ( v1_pre_topc @ ( k6_tmap_1 @ A @ B ) ) & 
% 0.22/0.50         ( v2_pre_topc @ ( k6_tmap_1 @ A @ B ) ) & 
% 0.22/0.50         ( l1_pre_topc @ ( k6_tmap_1 @ A @ B ) ) ) ))).
% 0.22/0.50  thf('8', plain,
% 0.22/0.50      (![X0 : $i, X1 : $i]:
% 0.22/0.50         (~ (l1_pre_topc @ X0)
% 0.22/0.50          | ~ (v2_pre_topc @ X0)
% 0.22/0.50          | (v2_struct_0 @ X0)
% 0.22/0.50          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.22/0.50          | (l1_pre_topc @ (k6_tmap_1 @ X0 @ X1)))),
% 0.22/0.50      inference('cnf', [status(esa)], [dt_k6_tmap_1])).
% 0.22/0.50  thf('9', plain,
% 0.22/0.50      (![X0 : $i]:
% 0.22/0.50         (~ (v2_pre_topc @ X0)
% 0.22/0.50          | ~ (l1_pre_topc @ X0)
% 0.22/0.50          | (v1_tdlat_3 @ X0)
% 0.22/0.50          | (l1_pre_topc @ (k6_tmap_1 @ X0 @ (sk_B @ X0)))
% 0.22/0.50          | (v2_struct_0 @ X0)
% 0.22/0.50          | ~ (v2_pre_topc @ X0)
% 0.22/0.50          | ~ (l1_pre_topc @ X0))),
% 0.22/0.50      inference('sup-', [status(thm)], ['7', '8'])).
% 0.22/0.50  thf('10', plain,
% 0.22/0.50      (![X0 : $i]:
% 0.22/0.50         ((v2_struct_0 @ X0)
% 0.22/0.50          | (l1_pre_topc @ (k6_tmap_1 @ X0 @ (sk_B @ X0)))
% 0.22/0.50          | (v1_tdlat_3 @ X0)
% 0.22/0.50          | ~ (l1_pre_topc @ X0)
% 0.22/0.50          | ~ (v2_pre_topc @ X0))),
% 0.22/0.50      inference('simplify', [status(thm)], ['9'])).
% 0.22/0.50  thf('11', plain,
% 0.22/0.50      (![X8 : $i]:
% 0.22/0.50         ((m1_subset_1 @ (sk_B @ X8) @ (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 0.22/0.50          | (v1_tdlat_3 @ X8)
% 0.22/0.50          | ~ (l1_pre_topc @ X8)
% 0.22/0.50          | ~ (v2_pre_topc @ X8))),
% 0.22/0.50      inference('cnf', [status(esa)], [t17_tdlat_3])).
% 0.22/0.50  thf('12', plain,
% 0.22/0.50      (![X0 : $i, X1 : $i]:
% 0.22/0.50         (~ (l1_pre_topc @ X0)
% 0.22/0.50          | ~ (v2_pre_topc @ X0)
% 0.22/0.50          | (v2_struct_0 @ X0)
% 0.22/0.50          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.22/0.50          | (v2_pre_topc @ (k6_tmap_1 @ X0 @ X1)))),
% 0.22/0.50      inference('cnf', [status(esa)], [dt_k6_tmap_1])).
% 0.22/0.50  thf('13', plain,
% 0.22/0.50      (![X0 : $i]:
% 0.22/0.50         (~ (v2_pre_topc @ X0)
% 0.22/0.50          | ~ (l1_pre_topc @ X0)
% 0.22/0.50          | (v1_tdlat_3 @ X0)
% 0.22/0.50          | (v2_pre_topc @ (k6_tmap_1 @ X0 @ (sk_B @ X0)))
% 0.22/0.50          | (v2_struct_0 @ X0)
% 0.22/0.50          | ~ (v2_pre_topc @ X0)
% 0.22/0.50          | ~ (l1_pre_topc @ X0))),
% 0.22/0.50      inference('sup-', [status(thm)], ['11', '12'])).
% 0.22/0.50  thf('14', plain,
% 0.22/0.50      (![X0 : $i]:
% 0.22/0.50         ((v2_struct_0 @ X0)
% 0.22/0.50          | (v2_pre_topc @ (k6_tmap_1 @ X0 @ (sk_B @ X0)))
% 0.22/0.50          | (v1_tdlat_3 @ X0)
% 0.22/0.50          | ~ (l1_pre_topc @ X0)
% 0.22/0.50          | ~ (v2_pre_topc @ X0))),
% 0.22/0.50      inference('simplify', [status(thm)], ['13'])).
% 0.22/0.50  thf('15', plain,
% 0.22/0.50      (![X8 : $i]:
% 0.22/0.50         ((m1_subset_1 @ (sk_B @ X8) @ (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 0.22/0.50          | (v1_tdlat_3 @ X8)
% 0.22/0.50          | ~ (l1_pre_topc @ X8)
% 0.22/0.50          | ~ (v2_pre_topc @ X8))),
% 0.22/0.50      inference('cnf', [status(esa)], [t17_tdlat_3])).
% 0.22/0.50  thf('16', plain,
% 0.22/0.50      (![X2 : $i, X3 : $i]:
% 0.22/0.50         (~ (l1_pre_topc @ X2)
% 0.22/0.50          | ~ (v2_pre_topc @ X2)
% 0.22/0.50          | (v2_struct_0 @ X2)
% 0.22/0.50          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (u1_struct_0 @ X2)))
% 0.22/0.50          | (v1_funct_2 @ (k7_tmap_1 @ X2 @ X3) @ (u1_struct_0 @ X2) @ 
% 0.22/0.50             (u1_struct_0 @ (k6_tmap_1 @ X2 @ X3))))),
% 0.22/0.50      inference('cnf', [status(esa)], [dt_k7_tmap_1])).
% 0.22/0.50  thf('17', plain,
% 0.22/0.50      (![X0 : $i]:
% 0.22/0.50         (~ (v2_pre_topc @ X0)
% 0.22/0.50          | ~ (l1_pre_topc @ X0)
% 0.22/0.50          | (v1_tdlat_3 @ X0)
% 0.22/0.50          | (v1_funct_2 @ (k7_tmap_1 @ X0 @ (sk_B @ X0)) @ 
% 0.22/0.50             (u1_struct_0 @ X0) @ 
% 0.22/0.50             (u1_struct_0 @ (k6_tmap_1 @ X0 @ (sk_B @ X0))))
% 0.22/0.50          | (v2_struct_0 @ X0)
% 0.22/0.50          | ~ (v2_pre_topc @ X0)
% 0.22/0.50          | ~ (l1_pre_topc @ X0))),
% 0.22/0.50      inference('sup-', [status(thm)], ['15', '16'])).
% 0.22/0.50  thf('18', plain,
% 0.22/0.50      (![X0 : $i]:
% 0.22/0.50         ((v2_struct_0 @ X0)
% 0.22/0.50          | (v1_funct_2 @ (k7_tmap_1 @ X0 @ (sk_B @ X0)) @ 
% 0.22/0.50             (u1_struct_0 @ X0) @ 
% 0.22/0.50             (u1_struct_0 @ (k6_tmap_1 @ X0 @ (sk_B @ X0))))
% 0.22/0.50          | (v1_tdlat_3 @ X0)
% 0.22/0.50          | ~ (l1_pre_topc @ X0)
% 0.22/0.50          | ~ (v2_pre_topc @ X0))),
% 0.22/0.50      inference('simplify', [status(thm)], ['17'])).
% 0.22/0.50  thf('19', plain,
% 0.22/0.50      (![X8 : $i]:
% 0.22/0.50         ((m1_subset_1 @ (sk_B @ X8) @ (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 0.22/0.50          | (v1_tdlat_3 @ X8)
% 0.22/0.50          | ~ (l1_pre_topc @ X8)
% 0.22/0.50          | ~ (v2_pre_topc @ X8))),
% 0.22/0.50      inference('cnf', [status(esa)], [t17_tdlat_3])).
% 0.22/0.50  thf('20', plain,
% 0.22/0.50      (![X2 : $i, X3 : $i]:
% 0.22/0.50         (~ (l1_pre_topc @ X2)
% 0.22/0.50          | ~ (v2_pre_topc @ X2)
% 0.22/0.50          | (v2_struct_0 @ X2)
% 0.22/0.50          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (u1_struct_0 @ X2)))
% 0.22/0.50          | (m1_subset_1 @ (k7_tmap_1 @ X2 @ X3) @ 
% 0.22/0.50             (k1_zfmisc_1 @ 
% 0.22/0.50              (k2_zfmisc_1 @ (u1_struct_0 @ X2) @ 
% 0.22/0.50               (u1_struct_0 @ (k6_tmap_1 @ X2 @ X3))))))),
% 0.22/0.50      inference('cnf', [status(esa)], [dt_k7_tmap_1])).
% 0.22/0.50  thf('21', plain,
% 0.22/0.50      (![X0 : $i]:
% 0.22/0.50         (~ (v2_pre_topc @ X0)
% 0.22/0.50          | ~ (l1_pre_topc @ X0)
% 0.22/0.50          | (v1_tdlat_3 @ X0)
% 0.22/0.50          | (m1_subset_1 @ (k7_tmap_1 @ X0 @ (sk_B @ X0)) @ 
% 0.22/0.50             (k1_zfmisc_1 @ 
% 0.22/0.50              (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ 
% 0.22/0.50               (u1_struct_0 @ (k6_tmap_1 @ X0 @ (sk_B @ X0))))))
% 0.22/0.50          | (v2_struct_0 @ X0)
% 0.22/0.50          | ~ (v2_pre_topc @ X0)
% 0.22/0.50          | ~ (l1_pre_topc @ X0))),
% 0.22/0.50      inference('sup-', [status(thm)], ['19', '20'])).
% 0.22/0.50  thf('22', plain,
% 0.22/0.50      (![X0 : $i]:
% 0.22/0.50         ((v2_struct_0 @ X0)
% 0.22/0.50          | (m1_subset_1 @ (k7_tmap_1 @ X0 @ (sk_B @ X0)) @ 
% 0.22/0.50             (k1_zfmisc_1 @ 
% 0.22/0.50              (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ 
% 0.22/0.50               (u1_struct_0 @ (k6_tmap_1 @ X0 @ (sk_B @ X0))))))
% 0.22/0.50          | (v1_tdlat_3 @ X0)
% 0.22/0.50          | ~ (l1_pre_topc @ X0)
% 0.22/0.50          | ~ (v2_pre_topc @ X0))),
% 0.22/0.50      inference('simplify', [status(thm)], ['21'])).
% 0.22/0.50  thf('23', plain,
% 0.22/0.50      (![X10 : $i, X11 : $i]:
% 0.22/0.50         (~ (v1_funct_1 @ X10)
% 0.22/0.50          | ~ (v1_funct_2 @ X10 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ X11))
% 0.22/0.50          | ~ (m1_subset_1 @ X10 @ 
% 0.22/0.50               (k1_zfmisc_1 @ 
% 0.22/0.50                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ X11))))
% 0.22/0.50          | (v5_pre_topc @ X10 @ sk_A @ X11)
% 0.22/0.50          | ~ (l1_pre_topc @ X11)
% 0.22/0.50          | ~ (v2_pre_topc @ X11)
% 0.22/0.50          | (v2_struct_0 @ X11))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('24', plain,
% 0.22/0.50      ((~ (v2_pre_topc @ sk_A)
% 0.22/0.50        | ~ (l1_pre_topc @ sk_A)
% 0.22/0.50        | (v1_tdlat_3 @ sk_A)
% 0.22/0.50        | (v2_struct_0 @ sk_A)
% 0.22/0.50        | (v2_struct_0 @ (k6_tmap_1 @ sk_A @ (sk_B @ sk_A)))
% 0.22/0.50        | ~ (v2_pre_topc @ (k6_tmap_1 @ sk_A @ (sk_B @ sk_A)))
% 0.22/0.50        | ~ (l1_pre_topc @ (k6_tmap_1 @ sk_A @ (sk_B @ sk_A)))
% 0.22/0.50        | (v5_pre_topc @ (k7_tmap_1 @ sk_A @ (sk_B @ sk_A)) @ sk_A @ 
% 0.22/0.50           (k6_tmap_1 @ sk_A @ (sk_B @ sk_A)))
% 0.22/0.50        | ~ (v1_funct_2 @ (k7_tmap_1 @ sk_A @ (sk_B @ sk_A)) @ 
% 0.22/0.50             (u1_struct_0 @ sk_A) @ 
% 0.22/0.50             (u1_struct_0 @ (k6_tmap_1 @ sk_A @ (sk_B @ sk_A))))
% 0.22/0.50        | ~ (v1_funct_1 @ (k7_tmap_1 @ sk_A @ (sk_B @ sk_A))))),
% 0.22/0.50      inference('sup-', [status(thm)], ['22', '23'])).
% 0.22/0.50  thf('25', plain, ((v2_pre_topc @ sk_A)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('26', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('27', plain,
% 0.22/0.50      (((v1_tdlat_3 @ sk_A)
% 0.22/0.50        | (v2_struct_0 @ sk_A)
% 0.22/0.50        | (v2_struct_0 @ (k6_tmap_1 @ sk_A @ (sk_B @ sk_A)))
% 0.22/0.50        | ~ (v2_pre_topc @ (k6_tmap_1 @ sk_A @ (sk_B @ sk_A)))
% 0.22/0.50        | ~ (l1_pre_topc @ (k6_tmap_1 @ sk_A @ (sk_B @ sk_A)))
% 0.22/0.50        | (v5_pre_topc @ (k7_tmap_1 @ sk_A @ (sk_B @ sk_A)) @ sk_A @ 
% 0.22/0.50           (k6_tmap_1 @ sk_A @ (sk_B @ sk_A)))
% 0.22/0.50        | ~ (v1_funct_2 @ (k7_tmap_1 @ sk_A @ (sk_B @ sk_A)) @ 
% 0.22/0.50             (u1_struct_0 @ sk_A) @ 
% 0.22/0.50             (u1_struct_0 @ (k6_tmap_1 @ sk_A @ (sk_B @ sk_A))))
% 0.22/0.50        | ~ (v1_funct_1 @ (k7_tmap_1 @ sk_A @ (sk_B @ sk_A))))),
% 0.22/0.50      inference('demod', [status(thm)], ['24', '25', '26'])).
% 0.22/0.50  thf('28', plain,
% 0.22/0.50      ((~ (v2_pre_topc @ sk_A)
% 0.22/0.50        | ~ (l1_pre_topc @ sk_A)
% 0.22/0.50        | (v1_tdlat_3 @ sk_A)
% 0.22/0.50        | (v2_struct_0 @ sk_A)
% 0.22/0.50        | ~ (v1_funct_1 @ (k7_tmap_1 @ sk_A @ (sk_B @ sk_A)))
% 0.22/0.50        | (v5_pre_topc @ (k7_tmap_1 @ sk_A @ (sk_B @ sk_A)) @ sk_A @ 
% 0.22/0.50           (k6_tmap_1 @ sk_A @ (sk_B @ sk_A)))
% 0.22/0.50        | ~ (l1_pre_topc @ (k6_tmap_1 @ sk_A @ (sk_B @ sk_A)))
% 0.22/0.50        | ~ (v2_pre_topc @ (k6_tmap_1 @ sk_A @ (sk_B @ sk_A)))
% 0.22/0.50        | (v2_struct_0 @ (k6_tmap_1 @ sk_A @ (sk_B @ sk_A)))
% 0.22/0.50        | (v2_struct_0 @ sk_A)
% 0.22/0.50        | (v1_tdlat_3 @ sk_A))),
% 0.22/0.50      inference('sup-', [status(thm)], ['18', '27'])).
% 0.22/0.50  thf('29', plain, ((v2_pre_topc @ sk_A)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('30', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('31', plain,
% 0.22/0.50      (((v1_tdlat_3 @ sk_A)
% 0.22/0.50        | (v2_struct_0 @ sk_A)
% 0.22/0.50        | ~ (v1_funct_1 @ (k7_tmap_1 @ sk_A @ (sk_B @ sk_A)))
% 0.22/0.50        | (v5_pre_topc @ (k7_tmap_1 @ sk_A @ (sk_B @ sk_A)) @ sk_A @ 
% 0.22/0.50           (k6_tmap_1 @ sk_A @ (sk_B @ sk_A)))
% 0.22/0.50        | ~ (l1_pre_topc @ (k6_tmap_1 @ sk_A @ (sk_B @ sk_A)))
% 0.22/0.50        | ~ (v2_pre_topc @ (k6_tmap_1 @ sk_A @ (sk_B @ sk_A)))
% 0.22/0.50        | (v2_struct_0 @ (k6_tmap_1 @ sk_A @ (sk_B @ sk_A)))
% 0.22/0.50        | (v2_struct_0 @ sk_A)
% 0.22/0.50        | (v1_tdlat_3 @ sk_A))),
% 0.22/0.50      inference('demod', [status(thm)], ['28', '29', '30'])).
% 0.22/0.50  thf('32', plain,
% 0.22/0.50      (((v2_struct_0 @ (k6_tmap_1 @ sk_A @ (sk_B @ sk_A)))
% 0.22/0.50        | ~ (v2_pre_topc @ (k6_tmap_1 @ sk_A @ (sk_B @ sk_A)))
% 0.22/0.50        | ~ (l1_pre_topc @ (k6_tmap_1 @ sk_A @ (sk_B @ sk_A)))
% 0.22/0.50        | (v5_pre_topc @ (k7_tmap_1 @ sk_A @ (sk_B @ sk_A)) @ sk_A @ 
% 0.22/0.50           (k6_tmap_1 @ sk_A @ (sk_B @ sk_A)))
% 0.22/0.50        | ~ (v1_funct_1 @ (k7_tmap_1 @ sk_A @ (sk_B @ sk_A)))
% 0.22/0.50        | (v2_struct_0 @ sk_A)
% 0.22/0.50        | (v1_tdlat_3 @ sk_A))),
% 0.22/0.50      inference('simplify', [status(thm)], ['31'])).
% 0.22/0.50  thf('33', plain,
% 0.22/0.50      ((~ (v2_pre_topc @ sk_A)
% 0.22/0.50        | ~ (l1_pre_topc @ sk_A)
% 0.22/0.50        | (v1_tdlat_3 @ sk_A)
% 0.22/0.50        | (v2_struct_0 @ sk_A)
% 0.22/0.50        | (v1_tdlat_3 @ sk_A)
% 0.22/0.50        | (v2_struct_0 @ sk_A)
% 0.22/0.50        | ~ (v1_funct_1 @ (k7_tmap_1 @ sk_A @ (sk_B @ sk_A)))
% 0.22/0.50        | (v5_pre_topc @ (k7_tmap_1 @ sk_A @ (sk_B @ sk_A)) @ sk_A @ 
% 0.22/0.50           (k6_tmap_1 @ sk_A @ (sk_B @ sk_A)))
% 0.22/0.50        | ~ (l1_pre_topc @ (k6_tmap_1 @ sk_A @ (sk_B @ sk_A)))
% 0.22/0.50        | (v2_struct_0 @ (k6_tmap_1 @ sk_A @ (sk_B @ sk_A))))),
% 0.22/0.50      inference('sup-', [status(thm)], ['14', '32'])).
% 0.22/0.50  thf('34', plain, ((v2_pre_topc @ sk_A)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('35', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('36', plain,
% 0.22/0.50      (((v1_tdlat_3 @ sk_A)
% 0.22/0.50        | (v2_struct_0 @ sk_A)
% 0.22/0.50        | (v1_tdlat_3 @ sk_A)
% 0.22/0.50        | (v2_struct_0 @ sk_A)
% 0.22/0.50        | ~ (v1_funct_1 @ (k7_tmap_1 @ sk_A @ (sk_B @ sk_A)))
% 0.22/0.50        | (v5_pre_topc @ (k7_tmap_1 @ sk_A @ (sk_B @ sk_A)) @ sk_A @ 
% 0.22/0.50           (k6_tmap_1 @ sk_A @ (sk_B @ sk_A)))
% 0.22/0.50        | ~ (l1_pre_topc @ (k6_tmap_1 @ sk_A @ (sk_B @ sk_A)))
% 0.22/0.50        | (v2_struct_0 @ (k6_tmap_1 @ sk_A @ (sk_B @ sk_A))))),
% 0.22/0.50      inference('demod', [status(thm)], ['33', '34', '35'])).
% 0.22/0.50  thf('37', plain,
% 0.22/0.50      (((v2_struct_0 @ (k6_tmap_1 @ sk_A @ (sk_B @ sk_A)))
% 0.22/0.50        | ~ (l1_pre_topc @ (k6_tmap_1 @ sk_A @ (sk_B @ sk_A)))
% 0.22/0.50        | (v5_pre_topc @ (k7_tmap_1 @ sk_A @ (sk_B @ sk_A)) @ sk_A @ 
% 0.22/0.50           (k6_tmap_1 @ sk_A @ (sk_B @ sk_A)))
% 0.22/0.50        | ~ (v1_funct_1 @ (k7_tmap_1 @ sk_A @ (sk_B @ sk_A)))
% 0.22/0.50        | (v2_struct_0 @ sk_A)
% 0.22/0.50        | (v1_tdlat_3 @ sk_A))),
% 0.22/0.50      inference('simplify', [status(thm)], ['36'])).
% 0.22/0.50  thf('38', plain,
% 0.22/0.50      ((~ (v2_pre_topc @ sk_A)
% 0.22/0.50        | ~ (l1_pre_topc @ sk_A)
% 0.22/0.50        | (v1_tdlat_3 @ sk_A)
% 0.22/0.50        | (v2_struct_0 @ sk_A)
% 0.22/0.50        | (v1_tdlat_3 @ sk_A)
% 0.22/0.50        | (v2_struct_0 @ sk_A)
% 0.22/0.50        | ~ (v1_funct_1 @ (k7_tmap_1 @ sk_A @ (sk_B @ sk_A)))
% 0.22/0.50        | (v5_pre_topc @ (k7_tmap_1 @ sk_A @ (sk_B @ sk_A)) @ sk_A @ 
% 0.22/0.50           (k6_tmap_1 @ sk_A @ (sk_B @ sk_A)))
% 0.22/0.50        | (v2_struct_0 @ (k6_tmap_1 @ sk_A @ (sk_B @ sk_A))))),
% 0.22/0.50      inference('sup-', [status(thm)], ['10', '37'])).
% 0.22/0.50  thf('39', plain, ((v2_pre_topc @ sk_A)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('40', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('41', plain,
% 0.22/0.50      (((v1_tdlat_3 @ sk_A)
% 0.22/0.50        | (v2_struct_0 @ sk_A)
% 0.22/0.50        | (v1_tdlat_3 @ sk_A)
% 0.22/0.50        | (v2_struct_0 @ sk_A)
% 0.22/0.50        | ~ (v1_funct_1 @ (k7_tmap_1 @ sk_A @ (sk_B @ sk_A)))
% 0.22/0.50        | (v5_pre_topc @ (k7_tmap_1 @ sk_A @ (sk_B @ sk_A)) @ sk_A @ 
% 0.22/0.50           (k6_tmap_1 @ sk_A @ (sk_B @ sk_A)))
% 0.22/0.50        | (v2_struct_0 @ (k6_tmap_1 @ sk_A @ (sk_B @ sk_A))))),
% 0.22/0.50      inference('demod', [status(thm)], ['38', '39', '40'])).
% 0.22/0.50  thf('42', plain,
% 0.22/0.50      (((v2_struct_0 @ (k6_tmap_1 @ sk_A @ (sk_B @ sk_A)))
% 0.22/0.50        | (v5_pre_topc @ (k7_tmap_1 @ sk_A @ (sk_B @ sk_A)) @ sk_A @ 
% 0.22/0.50           (k6_tmap_1 @ sk_A @ (sk_B @ sk_A)))
% 0.22/0.50        | ~ (v1_funct_1 @ (k7_tmap_1 @ sk_A @ (sk_B @ sk_A)))
% 0.22/0.50        | (v2_struct_0 @ sk_A)
% 0.22/0.50        | (v1_tdlat_3 @ sk_A))),
% 0.22/0.50      inference('simplify', [status(thm)], ['41'])).
% 0.22/0.50  thf('43', plain,
% 0.22/0.50      ((~ (v2_pre_topc @ sk_A)
% 0.22/0.50        | ~ (l1_pre_topc @ sk_A)
% 0.22/0.50        | (v1_tdlat_3 @ sk_A)
% 0.22/0.50        | (v2_struct_0 @ sk_A)
% 0.22/0.50        | (v1_tdlat_3 @ sk_A)
% 0.22/0.50        | (v2_struct_0 @ sk_A)
% 0.22/0.50        | (v5_pre_topc @ (k7_tmap_1 @ sk_A @ (sk_B @ sk_A)) @ sk_A @ 
% 0.22/0.50           (k6_tmap_1 @ sk_A @ (sk_B @ sk_A)))
% 0.22/0.50        | (v2_struct_0 @ (k6_tmap_1 @ sk_A @ (sk_B @ sk_A))))),
% 0.22/0.50      inference('sup-', [status(thm)], ['6', '42'])).
% 0.22/0.50  thf('44', plain, ((v2_pre_topc @ sk_A)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('45', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('46', plain,
% 0.22/0.50      (((v1_tdlat_3 @ sk_A)
% 0.22/0.50        | (v2_struct_0 @ sk_A)
% 0.22/0.50        | (v1_tdlat_3 @ sk_A)
% 0.22/0.50        | (v2_struct_0 @ sk_A)
% 0.22/0.50        | (v5_pre_topc @ (k7_tmap_1 @ sk_A @ (sk_B @ sk_A)) @ sk_A @ 
% 0.22/0.50           (k6_tmap_1 @ sk_A @ (sk_B @ sk_A)))
% 0.22/0.50        | (v2_struct_0 @ (k6_tmap_1 @ sk_A @ (sk_B @ sk_A))))),
% 0.22/0.50      inference('demod', [status(thm)], ['43', '44', '45'])).
% 0.22/0.50  thf('47', plain,
% 0.22/0.50      (((v2_struct_0 @ (k6_tmap_1 @ sk_A @ (sk_B @ sk_A)))
% 0.22/0.50        | (v5_pre_topc @ (k7_tmap_1 @ sk_A @ (sk_B @ sk_A)) @ sk_A @ 
% 0.22/0.50           (k6_tmap_1 @ sk_A @ (sk_B @ sk_A)))
% 0.22/0.50        | (v2_struct_0 @ sk_A)
% 0.22/0.50        | (v1_tdlat_3 @ sk_A))),
% 0.22/0.50      inference('simplify', [status(thm)], ['46'])).
% 0.22/0.50  thf('48', plain,
% 0.22/0.50      (![X0 : $i]:
% 0.22/0.50         ((v2_struct_0 @ X0)
% 0.22/0.50          | (v1_funct_2 @ (k7_tmap_1 @ X0 @ (sk_B @ X0)) @ 
% 0.22/0.50             (u1_struct_0 @ X0) @ 
% 0.22/0.50             (u1_struct_0 @ (k6_tmap_1 @ X0 @ (sk_B @ X0))))
% 0.22/0.50          | (v1_tdlat_3 @ X0)
% 0.22/0.50          | ~ (l1_pre_topc @ X0)
% 0.22/0.50          | ~ (v2_pre_topc @ X0))),
% 0.22/0.50      inference('simplify', [status(thm)], ['17'])).
% 0.22/0.50  thf('49', plain,
% 0.22/0.50      (![X0 : $i]:
% 0.22/0.50         ((v2_struct_0 @ X0)
% 0.22/0.50          | (m1_subset_1 @ (k7_tmap_1 @ X0 @ (sk_B @ X0)) @ 
% 0.22/0.50             (k1_zfmisc_1 @ 
% 0.22/0.50              (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ 
% 0.22/0.50               (u1_struct_0 @ (k6_tmap_1 @ X0 @ (sk_B @ X0))))))
% 0.22/0.50          | (v1_tdlat_3 @ X0)
% 0.22/0.50          | ~ (l1_pre_topc @ X0)
% 0.22/0.50          | ~ (v2_pre_topc @ X0))),
% 0.22/0.50      inference('simplify', [status(thm)], ['21'])).
% 0.22/0.50  thf(t113_tmap_1, axiom,
% 0.22/0.50    (![A:$i]:
% 0.22/0.50     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.22/0.50       ( ![B:$i]:
% 0.22/0.50         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.50           ( ( v3_pre_topc @ B @ A ) <=>
% 0.22/0.50             ( ( v1_funct_1 @ ( k7_tmap_1 @ A @ B ) ) & 
% 0.22/0.50               ( v1_funct_2 @
% 0.22/0.50                 ( k7_tmap_1 @ A @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.22/0.50                 ( u1_struct_0 @ ( k6_tmap_1 @ A @ B ) ) ) & 
% 0.22/0.50               ( v5_pre_topc @
% 0.22/0.50                 ( k7_tmap_1 @ A @ B ) @ A @ ( k6_tmap_1 @ A @ B ) ) & 
% 0.22/0.50               ( m1_subset_1 @
% 0.22/0.50                 ( k7_tmap_1 @ A @ B ) @ 
% 0.22/0.50                 ( k1_zfmisc_1 @
% 0.22/0.50                   ( k2_zfmisc_1 @
% 0.22/0.50                     ( u1_struct_0 @ A ) @ 
% 0.22/0.50                     ( u1_struct_0 @ ( k6_tmap_1 @ A @ B ) ) ) ) ) ) ) ) ) ))).
% 0.22/0.50  thf('50', plain,
% 0.22/0.50      (![X6 : $i, X7 : $i]:
% 0.22/0.50         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (u1_struct_0 @ X7)))
% 0.22/0.50          | ~ (v1_funct_1 @ (k7_tmap_1 @ X7 @ X6))
% 0.22/0.50          | ~ (v1_funct_2 @ (k7_tmap_1 @ X7 @ X6) @ (u1_struct_0 @ X7) @ 
% 0.22/0.50               (u1_struct_0 @ (k6_tmap_1 @ X7 @ X6)))
% 0.22/0.50          | ~ (v5_pre_topc @ (k7_tmap_1 @ X7 @ X6) @ X7 @ (k6_tmap_1 @ X7 @ X6))
% 0.22/0.50          | ~ (m1_subset_1 @ (k7_tmap_1 @ X7 @ X6) @ 
% 0.22/0.50               (k1_zfmisc_1 @ 
% 0.22/0.50                (k2_zfmisc_1 @ (u1_struct_0 @ X7) @ 
% 0.22/0.50                 (u1_struct_0 @ (k6_tmap_1 @ X7 @ X6)))))
% 0.22/0.50          | (v3_pre_topc @ X6 @ X7)
% 0.22/0.50          | ~ (l1_pre_topc @ X7)
% 0.22/0.50          | ~ (v2_pre_topc @ X7)
% 0.22/0.50          | (v2_struct_0 @ X7))),
% 0.22/0.50      inference('cnf', [status(esa)], [t113_tmap_1])).
% 0.22/0.50  thf('51', plain,
% 0.22/0.50      (![X0 : $i]:
% 0.22/0.50         (~ (v2_pre_topc @ X0)
% 0.22/0.50          | ~ (l1_pre_topc @ X0)
% 0.22/0.50          | (v1_tdlat_3 @ X0)
% 0.22/0.50          | (v2_struct_0 @ X0)
% 0.22/0.50          | (v2_struct_0 @ X0)
% 0.22/0.50          | ~ (v2_pre_topc @ X0)
% 0.22/0.50          | ~ (l1_pre_topc @ X0)
% 0.22/0.50          | (v3_pre_topc @ (sk_B @ X0) @ X0)
% 0.22/0.50          | ~ (v5_pre_topc @ (k7_tmap_1 @ X0 @ (sk_B @ X0)) @ X0 @ 
% 0.22/0.50               (k6_tmap_1 @ X0 @ (sk_B @ X0)))
% 0.22/0.50          | ~ (v1_funct_2 @ (k7_tmap_1 @ X0 @ (sk_B @ X0)) @ 
% 0.22/0.50               (u1_struct_0 @ X0) @ 
% 0.22/0.50               (u1_struct_0 @ (k6_tmap_1 @ X0 @ (sk_B @ X0))))
% 0.22/0.50          | ~ (v1_funct_1 @ (k7_tmap_1 @ X0 @ (sk_B @ X0)))
% 0.22/0.50          | ~ (m1_subset_1 @ (sk_B @ X0) @ (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.22/0.50      inference('sup-', [status(thm)], ['49', '50'])).
% 0.22/0.50  thf('52', plain,
% 0.22/0.50      (![X0 : $i]:
% 0.22/0.50         (~ (m1_subset_1 @ (sk_B @ X0) @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.22/0.50          | ~ (v1_funct_1 @ (k7_tmap_1 @ X0 @ (sk_B @ X0)))
% 0.22/0.50          | ~ (v1_funct_2 @ (k7_tmap_1 @ X0 @ (sk_B @ X0)) @ 
% 0.22/0.50               (u1_struct_0 @ X0) @ 
% 0.22/0.50               (u1_struct_0 @ (k6_tmap_1 @ X0 @ (sk_B @ X0))))
% 0.22/0.50          | ~ (v5_pre_topc @ (k7_tmap_1 @ X0 @ (sk_B @ X0)) @ X0 @ 
% 0.22/0.50               (k6_tmap_1 @ X0 @ (sk_B @ X0)))
% 0.22/0.50          | (v3_pre_topc @ (sk_B @ X0) @ X0)
% 0.22/0.50          | (v2_struct_0 @ X0)
% 0.22/0.50          | (v1_tdlat_3 @ X0)
% 0.22/0.50          | ~ (l1_pre_topc @ X0)
% 0.22/0.50          | ~ (v2_pre_topc @ X0))),
% 0.22/0.50      inference('simplify', [status(thm)], ['51'])).
% 0.22/0.50  thf('53', plain,
% 0.22/0.50      (![X0 : $i]:
% 0.22/0.50         (~ (v2_pre_topc @ X0)
% 0.22/0.50          | ~ (l1_pre_topc @ X0)
% 0.22/0.50          | (v1_tdlat_3 @ X0)
% 0.22/0.50          | (v2_struct_0 @ X0)
% 0.22/0.50          | ~ (v2_pre_topc @ X0)
% 0.22/0.50          | ~ (l1_pre_topc @ X0)
% 0.22/0.50          | (v1_tdlat_3 @ X0)
% 0.22/0.50          | (v2_struct_0 @ X0)
% 0.22/0.50          | (v3_pre_topc @ (sk_B @ X0) @ X0)
% 0.22/0.50          | ~ (v5_pre_topc @ (k7_tmap_1 @ X0 @ (sk_B @ X0)) @ X0 @ 
% 0.22/0.50               (k6_tmap_1 @ X0 @ (sk_B @ X0)))
% 0.22/0.50          | ~ (v1_funct_1 @ (k7_tmap_1 @ X0 @ (sk_B @ X0)))
% 0.22/0.50          | ~ (m1_subset_1 @ (sk_B @ X0) @ (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.22/0.50      inference('sup-', [status(thm)], ['48', '52'])).
% 0.22/0.50  thf('54', plain,
% 0.22/0.50      (![X0 : $i]:
% 0.22/0.50         (~ (m1_subset_1 @ (sk_B @ X0) @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.22/0.50          | ~ (v1_funct_1 @ (k7_tmap_1 @ X0 @ (sk_B @ X0)))
% 0.22/0.50          | ~ (v5_pre_topc @ (k7_tmap_1 @ X0 @ (sk_B @ X0)) @ X0 @ 
% 0.22/0.50               (k6_tmap_1 @ X0 @ (sk_B @ X0)))
% 0.22/0.50          | (v3_pre_topc @ (sk_B @ X0) @ X0)
% 0.22/0.50          | (v2_struct_0 @ X0)
% 0.22/0.50          | (v1_tdlat_3 @ X0)
% 0.22/0.50          | ~ (l1_pre_topc @ X0)
% 0.22/0.50          | ~ (v2_pre_topc @ X0))),
% 0.22/0.50      inference('simplify', [status(thm)], ['53'])).
% 0.22/0.50  thf('55', plain,
% 0.22/0.50      (((v1_tdlat_3 @ sk_A)
% 0.22/0.50        | (v2_struct_0 @ sk_A)
% 0.22/0.50        | (v2_struct_0 @ (k6_tmap_1 @ sk_A @ (sk_B @ sk_A)))
% 0.22/0.50        | ~ (v2_pre_topc @ sk_A)
% 0.22/0.50        | ~ (l1_pre_topc @ sk_A)
% 0.22/0.50        | (v1_tdlat_3 @ sk_A)
% 0.22/0.50        | (v2_struct_0 @ sk_A)
% 0.22/0.50        | (v3_pre_topc @ (sk_B @ sk_A) @ sk_A)
% 0.22/0.50        | ~ (v1_funct_1 @ (k7_tmap_1 @ sk_A @ (sk_B @ sk_A)))
% 0.22/0.50        | ~ (m1_subset_1 @ (sk_B @ sk_A) @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.22/0.50      inference('sup-', [status(thm)], ['47', '54'])).
% 0.22/0.50  thf('56', plain, ((v2_pre_topc @ sk_A)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('57', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('58', plain,
% 0.22/0.50      (((v1_tdlat_3 @ sk_A)
% 0.22/0.50        | (v2_struct_0 @ sk_A)
% 0.22/0.50        | (v2_struct_0 @ (k6_tmap_1 @ sk_A @ (sk_B @ sk_A)))
% 0.22/0.50        | (v1_tdlat_3 @ sk_A)
% 0.22/0.50        | (v2_struct_0 @ sk_A)
% 0.22/0.50        | (v3_pre_topc @ (sk_B @ sk_A) @ sk_A)
% 0.22/0.50        | ~ (v1_funct_1 @ (k7_tmap_1 @ sk_A @ (sk_B @ sk_A)))
% 0.22/0.50        | ~ (m1_subset_1 @ (sk_B @ sk_A) @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.22/0.50      inference('demod', [status(thm)], ['55', '56', '57'])).
% 0.22/0.50  thf('59', plain,
% 0.22/0.50      ((~ (m1_subset_1 @ (sk_B @ sk_A) @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.22/0.50        | ~ (v1_funct_1 @ (k7_tmap_1 @ sk_A @ (sk_B @ sk_A)))
% 0.22/0.50        | (v3_pre_topc @ (sk_B @ sk_A) @ sk_A)
% 0.22/0.50        | (v2_struct_0 @ (k6_tmap_1 @ sk_A @ (sk_B @ sk_A)))
% 0.22/0.50        | (v2_struct_0 @ sk_A)
% 0.22/0.50        | (v1_tdlat_3 @ sk_A))),
% 0.22/0.50      inference('simplify', [status(thm)], ['58'])).
% 0.22/0.50  thf('60', plain,
% 0.22/0.50      ((~ (v2_pre_topc @ sk_A)
% 0.22/0.50        | ~ (l1_pre_topc @ sk_A)
% 0.22/0.50        | (v1_tdlat_3 @ sk_A)
% 0.22/0.50        | (v1_tdlat_3 @ sk_A)
% 0.22/0.50        | (v2_struct_0 @ sk_A)
% 0.22/0.50        | (v2_struct_0 @ (k6_tmap_1 @ sk_A @ (sk_B @ sk_A)))
% 0.22/0.50        | (v3_pre_topc @ (sk_B @ sk_A) @ sk_A)
% 0.22/0.50        | ~ (v1_funct_1 @ (k7_tmap_1 @ sk_A @ (sk_B @ sk_A))))),
% 0.22/0.50      inference('sup-', [status(thm)], ['5', '59'])).
% 0.22/0.50  thf('61', plain, ((v2_pre_topc @ sk_A)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('62', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('63', plain,
% 0.22/0.50      (((v1_tdlat_3 @ sk_A)
% 0.22/0.50        | (v1_tdlat_3 @ sk_A)
% 0.22/0.50        | (v2_struct_0 @ sk_A)
% 0.22/0.50        | (v2_struct_0 @ (k6_tmap_1 @ sk_A @ (sk_B @ sk_A)))
% 0.22/0.50        | (v3_pre_topc @ (sk_B @ sk_A) @ sk_A)
% 0.22/0.50        | ~ (v1_funct_1 @ (k7_tmap_1 @ sk_A @ (sk_B @ sk_A))))),
% 0.22/0.50      inference('demod', [status(thm)], ['60', '61', '62'])).
% 0.22/0.50  thf('64', plain,
% 0.22/0.50      ((~ (v1_funct_1 @ (k7_tmap_1 @ sk_A @ (sk_B @ sk_A)))
% 0.22/0.50        | (v3_pre_topc @ (sk_B @ sk_A) @ sk_A)
% 0.22/0.50        | (v2_struct_0 @ (k6_tmap_1 @ sk_A @ (sk_B @ sk_A)))
% 0.22/0.50        | (v2_struct_0 @ sk_A)
% 0.22/0.50        | (v1_tdlat_3 @ sk_A))),
% 0.22/0.50      inference('simplify', [status(thm)], ['63'])).
% 0.22/0.50  thf('65', plain,
% 0.22/0.50      ((~ (v2_pre_topc @ sk_A)
% 0.22/0.50        | ~ (l1_pre_topc @ sk_A)
% 0.22/0.50        | (v1_tdlat_3 @ sk_A)
% 0.22/0.50        | (v2_struct_0 @ sk_A)
% 0.22/0.50        | (v1_tdlat_3 @ sk_A)
% 0.22/0.50        | (v2_struct_0 @ sk_A)
% 0.22/0.50        | (v2_struct_0 @ (k6_tmap_1 @ sk_A @ (sk_B @ sk_A)))
% 0.22/0.50        | (v3_pre_topc @ (sk_B @ sk_A) @ sk_A))),
% 0.22/0.50      inference('sup-', [status(thm)], ['4', '64'])).
% 0.22/0.50  thf('66', plain, ((v2_pre_topc @ sk_A)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('67', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('68', plain,
% 0.22/0.50      (((v1_tdlat_3 @ sk_A)
% 0.22/0.50        | (v2_struct_0 @ sk_A)
% 0.22/0.50        | (v1_tdlat_3 @ sk_A)
% 0.22/0.50        | (v2_struct_0 @ sk_A)
% 0.22/0.50        | (v2_struct_0 @ (k6_tmap_1 @ sk_A @ (sk_B @ sk_A)))
% 0.22/0.50        | (v3_pre_topc @ (sk_B @ sk_A) @ sk_A))),
% 0.22/0.50      inference('demod', [status(thm)], ['65', '66', '67'])).
% 0.22/0.50  thf('69', plain,
% 0.22/0.50      (((v3_pre_topc @ (sk_B @ sk_A) @ sk_A)
% 0.22/0.50        | (v2_struct_0 @ (k6_tmap_1 @ sk_A @ (sk_B @ sk_A)))
% 0.22/0.50        | (v2_struct_0 @ sk_A)
% 0.22/0.50        | (v1_tdlat_3 @ sk_A))),
% 0.22/0.50      inference('simplify', [status(thm)], ['68'])).
% 0.22/0.50  thf('70', plain,
% 0.22/0.50      (![X8 : $i]:
% 0.22/0.50         ((m1_subset_1 @ (sk_B @ X8) @ (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 0.22/0.50          | (v1_tdlat_3 @ X8)
% 0.22/0.50          | ~ (l1_pre_topc @ X8)
% 0.22/0.50          | ~ (v2_pre_topc @ X8))),
% 0.22/0.50      inference('cnf', [status(esa)], [t17_tdlat_3])).
% 0.22/0.50  thf(fc4_tmap_1, axiom,
% 0.22/0.50    (![A:$i,B:$i]:
% 0.22/0.50     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.22/0.50         ( l1_pre_topc @ A ) & 
% 0.22/0.50         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.22/0.50       ( ( ~( v2_struct_0 @ ( k6_tmap_1 @ A @ B ) ) ) & 
% 0.22/0.50         ( v1_pre_topc @ ( k6_tmap_1 @ A @ B ) ) & 
% 0.22/0.50         ( v2_pre_topc @ ( k6_tmap_1 @ A @ B ) ) ) ))).
% 0.22/0.50  thf('71', plain,
% 0.22/0.50      (![X4 : $i, X5 : $i]:
% 0.22/0.50         (~ (l1_pre_topc @ X4)
% 0.22/0.50          | ~ (v2_pre_topc @ X4)
% 0.22/0.50          | (v2_struct_0 @ X4)
% 0.22/0.50          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (u1_struct_0 @ X4)))
% 0.22/0.50          | ~ (v2_struct_0 @ (k6_tmap_1 @ X4 @ X5)))),
% 0.22/0.50      inference('cnf', [status(esa)], [fc4_tmap_1])).
% 0.22/0.50  thf('72', plain,
% 0.22/0.50      (![X0 : $i]:
% 0.22/0.50         (~ (v2_pre_topc @ X0)
% 0.22/0.50          | ~ (l1_pre_topc @ X0)
% 0.22/0.50          | (v1_tdlat_3 @ X0)
% 0.22/0.50          | ~ (v2_struct_0 @ (k6_tmap_1 @ X0 @ (sk_B @ X0)))
% 0.22/0.50          | (v2_struct_0 @ X0)
% 0.22/0.50          | ~ (v2_pre_topc @ X0)
% 0.22/0.50          | ~ (l1_pre_topc @ X0))),
% 0.22/0.50      inference('sup-', [status(thm)], ['70', '71'])).
% 0.22/0.50  thf('73', plain,
% 0.22/0.50      (![X0 : $i]:
% 0.22/0.50         ((v2_struct_0 @ X0)
% 0.22/0.50          | ~ (v2_struct_0 @ (k6_tmap_1 @ X0 @ (sk_B @ X0)))
% 0.22/0.50          | (v1_tdlat_3 @ X0)
% 0.22/0.50          | ~ (l1_pre_topc @ X0)
% 0.22/0.50          | ~ (v2_pre_topc @ X0))),
% 0.22/0.50      inference('simplify', [status(thm)], ['72'])).
% 0.22/0.50  thf('74', plain,
% 0.22/0.50      (((v1_tdlat_3 @ sk_A)
% 0.22/0.50        | (v2_struct_0 @ sk_A)
% 0.22/0.50        | (v3_pre_topc @ (sk_B @ sk_A) @ sk_A)
% 0.22/0.50        | ~ (v2_pre_topc @ sk_A)
% 0.22/0.50        | ~ (l1_pre_topc @ sk_A)
% 0.22/0.50        | (v1_tdlat_3 @ sk_A)
% 0.22/0.50        | (v2_struct_0 @ sk_A))),
% 0.22/0.50      inference('sup-', [status(thm)], ['69', '73'])).
% 0.22/0.50  thf('75', plain, ((v2_pre_topc @ sk_A)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('76', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('77', plain,
% 0.22/0.50      (((v1_tdlat_3 @ sk_A)
% 0.22/0.50        | (v2_struct_0 @ sk_A)
% 0.22/0.50        | (v3_pre_topc @ (sk_B @ sk_A) @ sk_A)
% 0.22/0.50        | (v1_tdlat_3 @ sk_A)
% 0.22/0.50        | (v2_struct_0 @ sk_A))),
% 0.22/0.50      inference('demod', [status(thm)], ['74', '75', '76'])).
% 0.22/0.50  thf('78', plain,
% 0.22/0.50      (((v3_pre_topc @ (sk_B @ sk_A) @ sk_A)
% 0.22/0.50        | (v2_struct_0 @ sk_A)
% 0.22/0.50        | (v1_tdlat_3 @ sk_A))),
% 0.22/0.50      inference('simplify', [status(thm)], ['77'])).
% 0.22/0.50  thf('79', plain, (~ (v2_struct_0 @ sk_A)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('80', plain,
% 0.22/0.50      (((v1_tdlat_3 @ sk_A) | (v3_pre_topc @ (sk_B @ sk_A) @ sk_A))),
% 0.22/0.50      inference('clc', [status(thm)], ['78', '79'])).
% 0.22/0.50  thf('81', plain, (~ (v1_tdlat_3 @ sk_A)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('82', plain, ((v3_pre_topc @ (sk_B @ sk_A) @ sk_A)),
% 0.22/0.50      inference('clc', [status(thm)], ['80', '81'])).
% 0.22/0.50  thf('83', plain,
% 0.22/0.50      (![X8 : $i]:
% 0.22/0.50         (~ (v3_pre_topc @ (sk_B @ X8) @ X8)
% 0.22/0.50          | (v1_tdlat_3 @ X8)
% 0.22/0.50          | ~ (l1_pre_topc @ X8)
% 0.22/0.50          | ~ (v2_pre_topc @ X8))),
% 0.22/0.50      inference('cnf', [status(esa)], [t17_tdlat_3])).
% 0.22/0.50  thf('84', plain,
% 0.22/0.50      ((~ (v2_pre_topc @ sk_A) | ~ (l1_pre_topc @ sk_A) | (v1_tdlat_3 @ sk_A))),
% 0.22/0.50      inference('sup-', [status(thm)], ['82', '83'])).
% 0.22/0.50  thf('85', plain, ((v2_pre_topc @ sk_A)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('86', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('87', plain, ((v1_tdlat_3 @ sk_A)),
% 0.22/0.50      inference('demod', [status(thm)], ['84', '85', '86'])).
% 0.22/0.50  thf('88', plain, ($false), inference('demod', [status(thm)], ['0', '87'])).
% 0.22/0.50  
% 0.22/0.50  % SZS output end Refutation
% 0.22/0.50  
% 0.22/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
