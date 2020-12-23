%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT1903+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ebARjzVmwn

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:54:32 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  190 ( 437 expanded)
%              Number of leaves         :   44 ( 161 expanded)
%              Depth                    :   36
%              Number of atoms          : 1811 (5684 expanded)
%              Number of equality atoms :   63 ( 202 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v5_pre_topc_type,type,(
    v5_pre_topc: $i > $i > $i > $o )).

thf(k2_tex_1_type,type,(
    k2_tex_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(v2_tdlat_3_type,type,(
    v2_tdlat_3: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(g1_pre_topc_type,type,(
    g1_pre_topc: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k1_tex_1_type,type,(
    k1_tex_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(t71_tex_2,conjecture,(
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
                  & ( v1_funct_2 @ C @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) )
                  & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) )
               => ( v5_pre_topc @ C @ B @ A ) ) )
       => ( v2_tdlat_3 @ A ) ) ) )).

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
                    & ( v1_funct_2 @ C @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) )
                    & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) )
                 => ( v5_pre_topc @ C @ B @ A ) ) )
         => ( v2_tdlat_3 @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t71_tex_2])).

thf('0',plain,(
    ~ ( v2_tdlat_3 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t21_tdlat_3,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( ( v2_tdlat_3 @ A )
      <=> ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ~ ( ( v4_pre_topc @ B @ A )
                & ( B != k1_xboole_0 )
                & ( B
                 != ( u1_struct_0 @ A ) ) ) ) ) ) )).

thf('1',plain,(
    ! [X28: $i] :
      ( ( m1_subset_1 @ ( sk_B @ X28 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ( v2_tdlat_3 @ X28 )
      | ~ ( l1_pre_topc @ X28 )
      | ~ ( v2_pre_topc @ X28 ) ) ),
    inference(cnf,[status(esa)],[t21_tdlat_3])).

thf(t171_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k8_relset_1 @ A @ A @ ( k6_partfun1 @ A ) @ B )
        = B ) ) )).

thf('2',plain,(
    ! [X26: $i,X27: $i] :
      ( ( ( k8_relset_1 @ X27 @ X27 @ ( k6_partfun1 @ X27 ) @ X26 )
        = X26 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[t171_funct_2])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('3',plain,(
    ! [X25: $i] :
      ( ( k6_partfun1 @ X25 )
      = ( k6_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('4',plain,(
    ! [X26: $i,X27: $i] :
      ( ( ( k8_relset_1 @ X27 @ X27 @ ( k6_relat_1 @ X27 ) @ X26 )
        = X26 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ X27 ) ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_tdlat_3 @ X0 )
      | ( ( k8_relset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( k6_relat_1 @ ( u1_struct_0 @ X0 ) ) @ ( sk_B @ X0 ) )
        = ( sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf('6',plain,(
    ! [X28: $i] :
      ( ( m1_subset_1 @ ( sk_B @ X28 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ( v2_tdlat_3 @ X28 )
      | ~ ( l1_pre_topc @ X28 )
      | ~ ( v2_pre_topc @ X28 ) ) ),
    inference(cnf,[status(esa)],[t21_tdlat_3])).

thf(dt_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( m1_subset_1 @ ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
      & ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ) )).

thf('7',plain,(
    ! [X11: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X11 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('8',plain,(
    ! [X25: $i] :
      ( ( k6_partfun1 @ X25 )
      = ( k6_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('9',plain,(
    ! [X11: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X11 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X11 ) ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf(abstractness_v1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( ( v1_pre_topc @ A )
       => ( A
          = ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ) )).

thf('10',plain,(
    ! [X0: $i] :
      ( ~ ( v1_pre_topc @ X0 )
      | ( X0
        = ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(cnf,[status(esa)],[abstractness_v1_pre_topc])).

thf(d3_tex_1,axiom,(
    ! [A: $i] :
      ( ( k2_tex_1 @ A )
      = ( g1_pre_topc @ A @ ( k1_tex_1 @ A ) ) ) )).

thf('11',plain,(
    ! [X8: $i] :
      ( ( k2_tex_1 @ X8 )
      = ( g1_pre_topc @ X8 @ ( k1_tex_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d3_tex_1])).

thf(dt_u1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( m1_subset_1 @ ( u1_pre_topc @ A ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('12',plain,(
    ! [X13: $i] :
      ( ( m1_subset_1 @ ( u1_pre_topc @ X13 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) ) )
      | ~ ( l1_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_pre_topc])).

thf(free_g1_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ! [C: $i,D: $i] :
          ( ( ( g1_pre_topc @ A @ B )
            = ( g1_pre_topc @ C @ D ) )
         => ( ( A = C )
            & ( B = D ) ) ) ) )).

thf('13',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ( ( g1_pre_topc @ X23 @ X24 )
       != ( g1_pre_topc @ X21 @ X22 ) )
      | ( X23 = X21 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[free_g1_pre_topc])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( u1_struct_0 @ X0 )
        = X1 )
      | ( ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) )
       != ( g1_pre_topc @ X1 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( g1_pre_topc @ ( u1_struct_0 @ X1 ) @ ( u1_pre_topc @ X1 ) )
       != ( k2_tex_1 @ X0 ) )
      | ( ( u1_struct_0 @ X1 )
        = X0 )
      | ~ ( l1_pre_topc @ X1 ) ) ),
    inference('sup-',[status(thm)],['11','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
       != ( k2_tex_1 @ X1 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( u1_struct_0 @ X0 )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['10','15'])).

thf('17',plain,(
    ! [X1: $i] :
      ( ( ( u1_struct_0 @ ( k2_tex_1 @ X1 ) )
        = X1 )
      | ~ ( v1_pre_topc @ ( k2_tex_1 @ X1 ) )
      | ~ ( l1_pre_topc @ ( k2_tex_1 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf(dt_k2_tex_1,axiom,(
    ! [A: $i] :
      ( l1_pre_topc @ ( k2_tex_1 @ A ) ) )).

thf('18',plain,(
    ! [X9: $i] :
      ( l1_pre_topc @ ( k2_tex_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tex_1])).

thf(fc2_tex_1,axiom,(
    ! [A: $i] :
      ( ( v2_tdlat_3 @ ( k2_tex_1 @ A ) )
      & ( v2_pre_topc @ ( k2_tex_1 @ A ) )
      & ( v1_pre_topc @ ( k2_tex_1 @ A ) ) ) )).

thf('19',plain,(
    ! [X15: $i] :
      ( v1_pre_topc @ ( k2_tex_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[fc2_tex_1])).

thf('20',plain,(
    ! [X1: $i] :
      ( ( u1_struct_0 @ ( k2_tex_1 @ X1 ) )
      = X1 ) ),
    inference('simplify_reflect+',[status(thm)],['17','18','19'])).

thf('21',plain,(
    ! [X30: $i,X31: $i] :
      ( ~ ( v1_funct_1 @ X30 )
      | ~ ( v1_funct_2 @ X30 @ ( u1_struct_0 @ X31 ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X31 ) @ ( u1_struct_0 @ sk_A ) ) ) )
      | ( v5_pre_topc @ X30 @ X31 @ sk_A )
      | ~ ( l1_pre_topc @ X31 )
      | ~ ( v2_pre_topc @ X31 )
      | ( v2_struct_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) )
      | ( v2_struct_0 @ ( k2_tex_1 @ X0 ) )
      | ~ ( v2_pre_topc @ ( k2_tex_1 @ X0 ) )
      | ~ ( l1_pre_topc @ ( k2_tex_1 @ X0 ) )
      | ( v5_pre_topc @ X1 @ ( k2_tex_1 @ X0 ) @ sk_A )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ ( k2_tex_1 @ X0 ) ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X16: $i] :
      ( v2_pre_topc @ ( k2_tex_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[fc2_tex_1])).

thf('24',plain,(
    ! [X9: $i] :
      ( l1_pre_topc @ ( k2_tex_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tex_1])).

thf('25',plain,(
    ! [X1: $i] :
      ( ( u1_struct_0 @ ( k2_tex_1 @ X1 ) )
      = X1 ) ),
    inference('simplify_reflect+',[status(thm)],['17','18','19'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) )
      | ( v2_struct_0 @ ( k2_tex_1 @ X0 ) )
      | ( v5_pre_topc @ X1 @ ( k2_tex_1 @ X0 ) @ sk_A )
      | ~ ( v1_funct_2 @ X1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['22','23','24','25'])).

thf('27',plain,
    ( ~ ( v1_funct_1 @ ( k6_relat_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( v1_funct_2 @ ( k6_relat_1 @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v5_pre_topc @ ( k6_relat_1 @ ( u1_struct_0 @ sk_A ) ) @ ( k2_tex_1 @ ( u1_struct_0 @ sk_A ) ) @ sk_A )
    | ( v2_struct_0 @ ( k2_tex_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['9','26'])).

thf(fc3_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('28',plain,(
    ! [X19: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('29',plain,(
    ! [X11: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X11 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X11 ) ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf(cc1_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( v1_funct_1 @ C )
          & ( v1_partfun1 @ C @ A ) )
       => ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B ) ) ) ) )).

thf('30',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_partfun1 @ X1 @ X2 )
      | ( v1_funct_2 @ X1 @ X2 @ X3 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_funct_2])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k6_relat_1 @ X0 ) @ X0 @ X0 )
      | ~ ( v1_partfun1 @ ( k6_relat_1 @ X0 ) @ X0 )
      | ~ ( v1_funct_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X10: $i] :
      ( v1_partfun1 @ ( k6_partfun1 @ X10 ) @ X10 ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('33',plain,(
    ! [X25: $i] :
      ( ( k6_partfun1 @ X25 )
      = ( k6_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('34',plain,(
    ! [X10: $i] :
      ( v1_partfun1 @ ( k6_relat_1 @ X10 ) @ X10 ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X19: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('36',plain,(
    ! [X0: $i] :
      ( v1_funct_2 @ ( k6_relat_1 @ X0 ) @ X0 @ X0 ) ),
    inference(demod,[status(thm)],['31','34','35'])).

thf('37',plain,
    ( ( v5_pre_topc @ ( k6_relat_1 @ ( u1_struct_0 @ sk_A ) ) @ ( k2_tex_1 @ ( u1_struct_0 @ sk_A ) ) @ sk_A )
    | ( v2_struct_0 @ ( k2_tex_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['27','28','36'])).

thf('38',plain,(
    ! [X11: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X11 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X11 ) ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('39',plain,(
    ! [X1: $i] :
      ( ( u1_struct_0 @ ( k2_tex_1 @ X1 ) )
      = X1 ) ),
    inference('simplify_reflect+',[status(thm)],['17','18','19'])).

thf(d12_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( l1_pre_topc @ B )
         => ! [C: $i] :
              ( ( ( v1_funct_1 @ C )
                & ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
                & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) )
             => ( ( v5_pre_topc @ C @ A @ B )
              <=> ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) )
                   => ( ( v4_pre_topc @ D @ B )
                     => ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ D ) @ A ) ) ) ) ) ) ) )).

thf('40',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ~ ( l1_pre_topc @ X4 )
      | ~ ( v5_pre_topc @ X5 @ X6 @ X4 )
      | ~ ( v4_pre_topc @ X7 @ X4 )
      | ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ X6 ) @ ( u1_struct_0 @ X4 ) @ X5 @ X7 ) @ X6 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X4 ) ) )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X6 ) @ ( u1_struct_0 @ X4 ) ) ) )
      | ~ ( v1_funct_2 @ X5 @ ( u1_struct_0 @ X6 ) @ ( u1_struct_0 @ X4 ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( l1_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[d12_pre_topc])).

thf('41',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ ( u1_struct_0 @ X1 ) ) ) )
      | ~ ( l1_pre_topc @ ( k2_tex_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_funct_2 @ X2 @ ( u1_struct_0 @ ( k2_tex_1 @ X0 ) ) @ ( u1_struct_0 @ X1 ) )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) )
      | ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ ( k2_tex_1 @ X0 ) ) @ ( u1_struct_0 @ X1 ) @ X2 @ X3 ) @ ( k2_tex_1 @ X0 ) )
      | ~ ( v4_pre_topc @ X3 @ X1 )
      | ~ ( v5_pre_topc @ X2 @ ( k2_tex_1 @ X0 ) @ X1 )
      | ~ ( l1_pre_topc @ X1 ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X9: $i] :
      ( l1_pre_topc @ ( k2_tex_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tex_1])).

thf('43',plain,(
    ! [X1: $i] :
      ( ( u1_struct_0 @ ( k2_tex_1 @ X1 ) )
      = X1 ) ),
    inference('simplify_reflect+',[status(thm)],['17','18','19'])).

thf('44',plain,(
    ! [X1: $i] :
      ( ( u1_struct_0 @ ( k2_tex_1 @ X1 ) )
      = X1 ) ),
    inference('simplify_reflect+',[status(thm)],['17','18','19'])).

thf('45',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ ( u1_struct_0 @ X1 ) ) ) )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_funct_2 @ X2 @ X0 @ ( u1_struct_0 @ X1 ) )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) )
      | ( v4_pre_topc @ ( k8_relset_1 @ X0 @ ( u1_struct_0 @ X1 ) @ X2 @ X3 ) @ ( k2_tex_1 @ X0 ) )
      | ~ ( v4_pre_topc @ X3 @ X1 )
      | ~ ( v5_pre_topc @ X2 @ ( k2_tex_1 @ X0 ) @ X1 )
      | ~ ( l1_pre_topc @ X1 ) ) ),
    inference(demod,[status(thm)],['41','42','43','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v5_pre_topc @ ( k6_relat_1 @ ( u1_struct_0 @ X0 ) ) @ ( k2_tex_1 @ ( u1_struct_0 @ X0 ) ) @ X0 )
      | ~ ( v4_pre_topc @ X1 @ X0 )
      | ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( k6_relat_1 @ ( u1_struct_0 @ X0 ) ) @ X1 ) @ ( k2_tex_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( v1_funct_2 @ ( k6_relat_1 @ ( u1_struct_0 @ X0 ) ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k6_relat_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['38','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( v1_funct_2 @ ( k6_relat_1 @ X0 ) @ X0 @ X0 ) ),
    inference(demod,[status(thm)],['31','34','35'])).

thf('48',plain,(
    ! [X19: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v5_pre_topc @ ( k6_relat_1 @ ( u1_struct_0 @ X0 ) ) @ ( k2_tex_1 @ ( u1_struct_0 @ X0 ) ) @ X0 )
      | ~ ( v4_pre_topc @ X1 @ X0 )
      | ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( k6_relat_1 @ ( u1_struct_0 @ X0 ) ) @ X1 ) @ ( k2_tex_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['46','47','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ ( k2_tex_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k6_relat_1 @ ( u1_struct_0 @ sk_A ) ) @ X0 ) @ ( k2_tex_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v4_pre_topc @ X0 @ sk_A )
      | ~ ( l1_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['37','49'])).

thf('51',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ ( k2_tex_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k6_relat_1 @ ( u1_struct_0 @ sk_A ) ) @ X0 ) @ ( k2_tex_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v4_pre_topc @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_tdlat_3 @ sk_A )
    | ~ ( v4_pre_topc @ ( sk_B @ sk_A ) @ sk_A )
    | ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k6_relat_1 @ ( u1_struct_0 @ sk_A ) ) @ ( sk_B @ sk_A ) ) @ ( k2_tex_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v2_struct_0 @ ( k2_tex_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['6','52'])).

thf('54',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_tdlat_3 @ X0 )
      | ( ( k8_relset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( k6_relat_1 @ ( u1_struct_0 @ X0 ) ) @ ( sk_B @ X0 ) )
        = ( sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf('57',plain,(
    ! [X28: $i] :
      ( ( v4_pre_topc @ ( sk_B @ X28 ) @ X28 )
      | ( v2_tdlat_3 @ X28 )
      | ~ ( l1_pre_topc @ X28 )
      | ~ ( v2_pre_topc @ X28 ) ) ),
    inference(cnf,[status(esa)],[t21_tdlat_3])).

thf('58',plain,(
    ! [X28: $i] :
      ( ( m1_subset_1 @ ( sk_B @ X28 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ( v2_tdlat_3 @ X28 )
      | ~ ( l1_pre_topc @ X28 )
      | ~ ( v2_pre_topc @ X28 ) ) ),
    inference(cnf,[status(esa)],[t21_tdlat_3])).

thf('59',plain,(
    ! [X11: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X11 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X11 ) ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('60',plain,(
    ! [X30: $i,X31: $i] :
      ( ~ ( v1_funct_1 @ X30 )
      | ~ ( v1_funct_2 @ X30 @ ( u1_struct_0 @ X31 ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X31 ) @ ( u1_struct_0 @ sk_A ) ) ) )
      | ( v5_pre_topc @ X30 @ X31 @ sk_A )
      | ~ ( l1_pre_topc @ X31 )
      | ~ ( v2_pre_topc @ X31 )
      | ( v2_struct_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v5_pre_topc @ ( k6_relat_1 @ ( u1_struct_0 @ sk_A ) ) @ sk_A @ sk_A )
    | ~ ( v1_funct_2 @ ( k6_relat_1 @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_funct_1 @ ( k6_relat_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    ! [X0: $i] :
      ( v1_funct_2 @ ( k6_relat_1 @ X0 ) @ X0 @ X0 ) ),
    inference(demod,[status(thm)],['31','34','35'])).

thf('65',plain,(
    ! [X19: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('66',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v5_pre_topc @ ( k6_relat_1 @ ( u1_struct_0 @ sk_A ) ) @ sk_A @ sk_A ) ),
    inference(demod,[status(thm)],['61','62','63','64','65'])).

thf('67',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    v5_pre_topc @ ( k6_relat_1 @ ( u1_struct_0 @ sk_A ) ) @ sk_A @ sk_A ),
    inference(clc,[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X11: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X11 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X11 ) ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('70',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ~ ( l1_pre_topc @ X4 )
      | ~ ( v5_pre_topc @ X5 @ X6 @ X4 )
      | ~ ( v4_pre_topc @ X7 @ X4 )
      | ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ X6 ) @ ( u1_struct_0 @ X4 ) @ X5 @ X7 ) @ X6 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X4 ) ) )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X6 ) @ ( u1_struct_0 @ X4 ) ) ) )
      | ~ ( v1_funct_2 @ X5 @ ( u1_struct_0 @ X6 ) @ ( u1_struct_0 @ X4 ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( l1_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[d12_pre_topc])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_funct_1 @ ( k6_relat_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( v1_funct_2 @ ( k6_relat_1 @ ( u1_struct_0 @ X0 ) ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( k6_relat_1 @ ( u1_struct_0 @ X0 ) ) @ X1 ) @ X0 )
      | ~ ( v4_pre_topc @ X1 @ X0 )
      | ~ ( v5_pre_topc @ ( k6_relat_1 @ ( u1_struct_0 @ X0 ) ) @ X0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X19: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('73',plain,(
    ! [X0: $i] :
      ( v1_funct_2 @ ( k6_relat_1 @ X0 ) @ X0 @ X0 ) ),
    inference(demod,[status(thm)],['31','34','35'])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( k6_relat_1 @ ( u1_struct_0 @ X0 ) ) @ X1 ) @ X0 )
      | ~ ( v4_pre_topc @ X1 @ X0 )
      | ~ ( v5_pre_topc @ ( k6_relat_1 @ ( u1_struct_0 @ X0 ) ) @ X0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(demod,[status(thm)],['71','72','73'])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v5_pre_topc @ ( k6_relat_1 @ ( u1_struct_0 @ X0 ) ) @ X0 @ X0 )
      | ~ ( v4_pre_topc @ X1 @ X0 )
      | ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( k6_relat_1 @ ( u1_struct_0 @ X0 ) ) @ X1 ) @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['74'])).

thf('76',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k6_relat_1 @ ( u1_struct_0 @ sk_A ) ) @ X0 ) @ sk_A )
      | ~ ( v4_pre_topc @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['68','75'])).

thf('77',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k6_relat_1 @ ( u1_struct_0 @ sk_A ) ) @ X0 ) @ sk_A )
      | ~ ( v4_pre_topc @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('79',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_tdlat_3 @ sk_A )
    | ~ ( v4_pre_topc @ ( sk_B @ sk_A ) @ sk_A )
    | ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k6_relat_1 @ ( u1_struct_0 @ sk_A ) ) @ ( sk_B @ sk_A ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['58','78'])).

thf('80',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,
    ( ( v2_tdlat_3 @ sk_A )
    | ~ ( v4_pre_topc @ ( sk_B @ sk_A ) @ sk_A )
    | ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k6_relat_1 @ ( u1_struct_0 @ sk_A ) ) @ ( sk_B @ sk_A ) ) @ sk_A ) ),
    inference(demod,[status(thm)],['79','80','81'])).

thf('83',plain,(
    ~ ( v2_tdlat_3 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,
    ( ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k6_relat_1 @ ( u1_struct_0 @ sk_A ) ) @ ( sk_B @ sk_A ) ) @ sk_A )
    | ~ ( v4_pre_topc @ ( sk_B @ sk_A ) @ sk_A ) ),
    inference(clc,[status(thm)],['82','83'])).

thf('85',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_tdlat_3 @ sk_A )
    | ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k6_relat_1 @ ( u1_struct_0 @ sk_A ) ) @ ( sk_B @ sk_A ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['57','84'])).

thf('86',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,
    ( ( v2_tdlat_3 @ sk_A )
    | ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k6_relat_1 @ ( u1_struct_0 @ sk_A ) ) @ ( sk_B @ sk_A ) ) @ sk_A ) ),
    inference(demod,[status(thm)],['85','86','87'])).

thf('89',plain,(
    ~ ( v2_tdlat_3 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k6_relat_1 @ ( u1_struct_0 @ sk_A ) ) @ ( sk_B @ sk_A ) ) @ sk_A ),
    inference(clc,[status(thm)],['88','89'])).

thf('91',plain,
    ( ( v4_pre_topc @ ( sk_B @ sk_A ) @ sk_A )
    | ( v2_tdlat_3 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A ) ),
    inference('sup+',[status(thm)],['56','90'])).

thf('92',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,
    ( ( v4_pre_topc @ ( sk_B @ sk_A ) @ sk_A )
    | ( v2_tdlat_3 @ sk_A ) ),
    inference(demod,[status(thm)],['91','92','93'])).

thf('95',plain,(
    ~ ( v2_tdlat_3 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    v4_pre_topc @ ( sk_B @ sk_A ) @ sk_A ),
    inference(clc,[status(thm)],['94','95'])).

thf('97',plain,
    ( ( v2_tdlat_3 @ sk_A )
    | ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k6_relat_1 @ ( u1_struct_0 @ sk_A ) ) @ ( sk_B @ sk_A ) ) @ ( k2_tex_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v2_struct_0 @ ( k2_tex_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['53','54','55','96'])).

thf('98',plain,(
    ~ ( v2_tdlat_3 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,
    ( ( v2_struct_0 @ ( k2_tex_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k6_relat_1 @ ( u1_struct_0 @ sk_A ) ) @ ( sk_B @ sk_A ) ) @ ( k2_tex_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['97','98'])).

thf('100',plain,
    ( ( v4_pre_topc @ ( sk_B @ sk_A ) @ ( k2_tex_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v2_tdlat_3 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ( v2_struct_0 @ ( k2_tex_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['5','99'])).

thf('101',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,
    ( ( v4_pre_topc @ ( sk_B @ sk_A ) @ ( k2_tex_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v2_tdlat_3 @ sk_A )
    | ( v2_struct_0 @ ( k2_tex_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['100','101','102'])).

thf('104',plain,(
    ~ ( v2_tdlat_3 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,
    ( ( v2_struct_0 @ ( k2_tex_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v4_pre_topc @ ( sk_B @ sk_A ) @ ( k2_tex_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['103','104'])).

thf('106',plain,(
    ! [X28: $i] :
      ( ( m1_subset_1 @ ( sk_B @ X28 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ( v2_tdlat_3 @ X28 )
      | ~ ( l1_pre_topc @ X28 )
      | ~ ( v2_pre_topc @ X28 ) ) ),
    inference(cnf,[status(esa)],[t21_tdlat_3])).

thf('107',plain,(
    ! [X1: $i] :
      ( ( u1_struct_0 @ ( k2_tex_1 @ X1 ) )
      = X1 ) ),
    inference('simplify_reflect+',[status(thm)],['17','18','19'])).

thf('108',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( v2_tdlat_3 @ X28 )
      | ( X29
        = ( u1_struct_0 @ X28 ) )
      | ( X29 = k1_xboole_0 )
      | ~ ( v4_pre_topc @ X29 @ X28 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ~ ( l1_pre_topc @ X28 )
      | ~ ( v2_pre_topc @ X28 ) ) ),
    inference(cnf,[status(esa)],[t21_tdlat_3])).

thf('109',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) )
      | ~ ( v2_pre_topc @ ( k2_tex_1 @ X0 ) )
      | ~ ( l1_pre_topc @ ( k2_tex_1 @ X0 ) )
      | ~ ( v4_pre_topc @ X1 @ ( k2_tex_1 @ X0 ) )
      | ( X1 = k1_xboole_0 )
      | ( X1
        = ( u1_struct_0 @ ( k2_tex_1 @ X0 ) ) )
      | ~ ( v2_tdlat_3 @ ( k2_tex_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['107','108'])).

thf('110',plain,(
    ! [X16: $i] :
      ( v2_pre_topc @ ( k2_tex_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[fc2_tex_1])).

thf('111',plain,(
    ! [X9: $i] :
      ( l1_pre_topc @ ( k2_tex_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tex_1])).

thf('112',plain,(
    ! [X1: $i] :
      ( ( u1_struct_0 @ ( k2_tex_1 @ X1 ) )
      = X1 ) ),
    inference('simplify_reflect+',[status(thm)],['17','18','19'])).

thf('113',plain,(
    ! [X17: $i] :
      ( v2_tdlat_3 @ ( k2_tex_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[fc2_tex_1])).

thf('114',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) )
      | ~ ( v4_pre_topc @ X1 @ ( k2_tex_1 @ X0 ) )
      | ( X1 = k1_xboole_0 )
      | ( X1 = X0 ) ) ),
    inference(demod,[status(thm)],['109','110','111','112','113'])).

thf('115',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_tdlat_3 @ X0 )
      | ( ( sk_B @ X0 )
        = ( u1_struct_0 @ X0 ) )
      | ( ( sk_B @ X0 )
        = k1_xboole_0 )
      | ~ ( v4_pre_topc @ ( sk_B @ X0 ) @ ( k2_tex_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['106','114'])).

thf('116',plain,
    ( ( v2_struct_0 @ ( k2_tex_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( ( sk_B @ sk_A )
      = k1_xboole_0 )
    | ( ( sk_B @ sk_A )
      = ( u1_struct_0 @ sk_A ) )
    | ( v2_tdlat_3 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['105','115'])).

thf('117',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,
    ( ( v2_struct_0 @ ( k2_tex_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( ( sk_B @ sk_A )
      = k1_xboole_0 )
    | ( ( sk_B @ sk_A )
      = ( u1_struct_0 @ sk_A ) )
    | ( v2_tdlat_3 @ sk_A ) ),
    inference(demod,[status(thm)],['116','117','118'])).

thf(fc3_tex_1,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ~ ( v2_struct_0 @ ( k2_tex_1 @ A ) ) ) )).

thf('120',plain,(
    ! [X20: $i] :
      ( ~ ( v2_struct_0 @ ( k2_tex_1 @ X20 ) )
      | ( v1_xboole_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[fc3_tex_1])).

thf('121',plain,
    ( ( v2_tdlat_3 @ sk_A )
    | ( ( sk_B @ sk_A )
      = ( u1_struct_0 @ sk_A ) )
    | ( ( sk_B @ sk_A )
      = k1_xboole_0 )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['119','120'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('122',plain,(
    ! [X14: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X14 ) )
      | ~ ( l1_struct_0 @ X14 )
      | ( v2_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('123',plain,
    ( ( ( sk_B @ sk_A )
      = k1_xboole_0 )
    | ( ( sk_B @ sk_A )
      = ( u1_struct_0 @ sk_A ) )
    | ( v2_tdlat_3 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['121','122'])).

thf('124',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('125',plain,(
    ! [X12: $i] :
      ( ( l1_struct_0 @ X12 )
      | ~ ( l1_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('126',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['124','125'])).

thf('127',plain,
    ( ( ( sk_B @ sk_A )
      = k1_xboole_0 )
    | ( ( sk_B @ sk_A )
      = ( u1_struct_0 @ sk_A ) )
    | ( v2_tdlat_3 @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['123','126'])).

thf('128',plain,(
    ! [X28: $i] :
      ( ( ( sk_B @ X28 )
       != ( u1_struct_0 @ X28 ) )
      | ( v2_tdlat_3 @ X28 )
      | ~ ( l1_pre_topc @ X28 )
      | ~ ( v2_pre_topc @ X28 ) ) ),
    inference(cnf,[status(esa)],[t21_tdlat_3])).

thf('129',plain,
    ( ( ( sk_B @ sk_A )
     != ( sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_tdlat_3 @ sk_A )
    | ( ( sk_B @ sk_A )
      = k1_xboole_0 )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_tdlat_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['127','128'])).

thf('130',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('131',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('132',plain,
    ( ( ( sk_B @ sk_A )
     != ( sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_tdlat_3 @ sk_A )
    | ( ( sk_B @ sk_A )
      = k1_xboole_0 )
    | ( v2_tdlat_3 @ sk_A ) ),
    inference(demod,[status(thm)],['129','130','131'])).

thf('133',plain,
    ( ( ( sk_B @ sk_A )
      = k1_xboole_0 )
    | ( v2_tdlat_3 @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['132'])).

thf('134',plain,(
    ~ ( v2_tdlat_3 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('135',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( sk_B @ sk_A )
      = k1_xboole_0 ) ),
    inference(clc,[status(thm)],['133','134'])).

thf('136',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('137',plain,
    ( ( sk_B @ sk_A )
    = k1_xboole_0 ),
    inference(clc,[status(thm)],['135','136'])).

thf('138',plain,(
    ! [X28: $i] :
      ( ( ( sk_B @ X28 )
       != k1_xboole_0 )
      | ( v2_tdlat_3 @ X28 )
      | ~ ( l1_pre_topc @ X28 )
      | ~ ( v2_pre_topc @ X28 ) ) ),
    inference(cnf,[status(esa)],[t21_tdlat_3])).

thf('139',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_tdlat_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['137','138'])).

thf('140',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('141',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('142',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( v2_tdlat_3 @ sk_A ) ),
    inference(demod,[status(thm)],['139','140','141'])).

thf('143',plain,(
    v2_tdlat_3 @ sk_A ),
    inference(simplify,[status(thm)],['142'])).

thf('144',plain,(
    $false ),
    inference(demod,[status(thm)],['0','143'])).


%------------------------------------------------------------------------------
