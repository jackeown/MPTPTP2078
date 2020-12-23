%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT1901+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.MjAVr2GY8Z

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:54:32 EST 2020

% Result     : Theorem 0.12s
% Output     : Refutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :  199 (1093 expanded)
%              Number of leaves         :   49 ( 400 expanded)
%              Depth                    :   35
%              Number of atoms          : 1691 (9084 expanded)
%              Number of equality atoms :   73 ( 767 expanded)
%              Maximal formula depth    :   18 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k9_setfam_1_type,type,(
    k9_setfam_1: $i > $i )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(g1_pre_topc_type,type,(
    g1_pre_topc: $i > $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(v1_tdlat_3_type,type,(
    v1_tdlat_3: $i > $o )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(v5_pre_topc_type,type,(
    v5_pre_topc: $i > $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k1_compts_1_type,type,(
    k1_compts_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

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
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t18_tdlat_3,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( ( v1_tdlat_3 @ A )
      <=> ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( v4_pre_topc @ B @ A ) ) ) ) )).

thf('1',plain,(
    ! [X34: $i] :
      ( ( m1_subset_1 @ ( sk_B @ X34 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X34 ) ) )
      | ( v1_tdlat_3 @ X34 )
      | ~ ( l1_pre_topc @ X34 )
      | ~ ( v2_pre_topc @ X34 ) ) ),
    inference(cnf,[status(esa)],[t18_tdlat_3])).

thf(redefinition_k9_setfam_1,axiom,(
    ! [A: $i] :
      ( ( k9_setfam_1 @ A )
      = ( k1_zfmisc_1 @ A ) ) )).

thf('2',plain,(
    ! [X31: $i] :
      ( ( k9_setfam_1 @ X31 )
      = ( k1_zfmisc_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('3',plain,(
    ! [X34: $i] :
      ( ( m1_subset_1 @ ( sk_B @ X34 ) @ ( k9_setfam_1 @ ( u1_struct_0 @ X34 ) ) )
      | ( v1_tdlat_3 @ X34 )
      | ~ ( l1_pre_topc @ X34 )
      | ~ ( v2_pre_topc @ X34 ) ) ),
    inference(demod,[status(thm)],['1','2'])).

thf(t171_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k8_relset_1 @ A @ A @ ( k6_partfun1 @ A ) @ B )
        = B ) ) )).

thf('4',plain,(
    ! [X32: $i,X33: $i] :
      ( ( ( k8_relset_1 @ X33 @ X33 @ ( k6_partfun1 @ X33 ) @ X32 )
        = X32 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[t171_funct_2])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('5',plain,(
    ! [X26: $i] :
      ( ( k6_partfun1 @ X26 )
      = ( k6_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('6',plain,(
    ! [X31: $i] :
      ( ( k9_setfam_1 @ X31 )
      = ( k1_zfmisc_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('7',plain,(
    ! [X32: $i,X33: $i] :
      ( ( ( k8_relset_1 @ X33 @ X33 @ ( k6_relat_1 @ X33 ) @ X32 )
        = X32 )
      | ~ ( m1_subset_1 @ X32 @ ( k9_setfam_1 @ X33 ) ) ) ),
    inference(demod,[status(thm)],['4','5','6'])).

thf(dt_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( m1_subset_1 @ ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
      & ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ) )).

thf('8',plain,(
    ! [X15: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X15 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('9',plain,(
    ! [X26: $i] :
      ( ( k6_partfun1 @ X26 )
      = ( k6_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('10',plain,(
    ! [X31: $i] :
      ( ( k9_setfam_1 @ X31 )
      = ( k1_zfmisc_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('11',plain,(
    ! [X15: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X15 ) @ ( k9_setfam_1 @ ( k2_zfmisc_1 @ X15 @ X15 ) ) ) ),
    inference(demod,[status(thm)],['8','9','10'])).

thf(redefinition_k8_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k8_relset_1 @ A @ B @ C @ D )
        = ( k10_relat_1 @ C @ D ) ) ) )).

thf('12',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) )
      | ( ( k8_relset_1 @ X28 @ X29 @ X27 @ X30 )
        = ( k10_relat_1 @ X27 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k8_relset_1])).

thf('13',plain,(
    ! [X31: $i] :
      ( ( k9_setfam_1 @ X31 )
      = ( k1_zfmisc_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('14',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k9_setfam_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) )
      | ( ( k8_relset_1 @ X28 @ X29 @ X27 @ X30 )
        = ( k10_relat_1 @ X27 @ X30 ) ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relset_1 @ X0 @ X0 @ ( k6_relat_1 @ X0 ) @ X1 )
      = ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['11','14'])).

thf('16',plain,(
    ! [X32: $i,X33: $i] :
      ( ( ( k10_relat_1 @ ( k6_relat_1 @ X33 ) @ X32 )
        = X32 )
      | ~ ( m1_subset_1 @ X32 @ ( k9_setfam_1 @ X33 ) ) ) ),
    inference(demod,[status(thm)],['7','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v1_tdlat_3 @ X0 )
      | ( ( k10_relat_1 @ ( k6_relat_1 @ ( u1_struct_0 @ X0 ) ) @ ( sk_B @ X0 ) )
        = ( sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['3','16'])).

thf('18',plain,(
    ! [X34: $i] :
      ( ( m1_subset_1 @ ( sk_B @ X34 ) @ ( k9_setfam_1 @ ( u1_struct_0 @ X34 ) ) )
      | ( v1_tdlat_3 @ X34 )
      | ~ ( l1_pre_topc @ X34 )
      | ~ ( v2_pre_topc @ X34 ) ) ),
    inference(demod,[status(thm)],['1','2'])).

thf(abstractness_v1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( ( v1_pre_topc @ A )
       => ( A
          = ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ) )).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( v1_pre_topc @ X0 )
      | ( X0
        = ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(cnf,[status(esa)],[abstractness_v1_pre_topc])).

thf('20',plain,(
    ! [X0: $i] :
      ( ~ ( v1_pre_topc @ X0 )
      | ( X0
        = ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(cnf,[status(esa)],[abstractness_v1_pre_topc])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('21',plain,(
    ! [X13: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X13 ) @ ( k1_zfmisc_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf('22',plain,(
    ! [X31: $i] :
      ( ( k9_setfam_1 @ X31 )
      = ( k1_zfmisc_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('23',plain,(
    ! [X13: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X13 ) @ ( k9_setfam_1 @ X13 ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf(free_g1_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ! [C: $i,D: $i] :
          ( ( ( g1_pre_topc @ A @ B )
            = ( g1_pre_topc @ C @ D ) )
         => ( ( A = C )
            & ( B = D ) ) ) ) )).

thf('24',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ( ( g1_pre_topc @ X24 @ X25 )
       != ( g1_pre_topc @ X22 @ X23 ) )
      | ( X25 = X23 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[free_g1_pre_topc])).

thf('25',plain,(
    ! [X31: $i] :
      ( ( k9_setfam_1 @ X31 )
      = ( k1_zfmisc_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('26',plain,(
    ! [X31: $i] :
      ( ( k9_setfam_1 @ X31 )
      = ( k1_zfmisc_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('27',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ( ( g1_pre_topc @ X24 @ X25 )
       != ( g1_pre_topc @ X22 @ X23 ) )
      | ( X25 = X23 )
      | ~ ( m1_subset_1 @ X25 @ ( k9_setfam_1 @ ( k9_setfam_1 @ X24 ) ) ) ) ),
    inference(demod,[status(thm)],['24','25','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_subset_1 @ ( k9_setfam_1 @ X0 ) )
        = X1 )
      | ( ( g1_pre_topc @ X0 @ ( k2_subset_1 @ ( k9_setfam_1 @ X0 ) ) )
       != ( g1_pre_topc @ X2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['23','27'])).

thf(d8_compts_1,axiom,(
    ! [A: $i] :
      ( ( k1_compts_1 @ A )
      = ( g1_pre_topc @ A @ ( k2_subset_1 @ ( k9_setfam_1 @ A ) ) ) ) )).

thf('29',plain,(
    ! [X9: $i] :
      ( ( k1_compts_1 @ X9 )
      = ( g1_pre_topc @ X9 @ ( k2_subset_1 @ ( k9_setfam_1 @ X9 ) ) ) ) ),
    inference(cnf,[status(esa)],[d8_compts_1])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_subset_1 @ ( k9_setfam_1 @ X0 ) )
        = X1 )
      | ( ( k1_compts_1 @ X0 )
       != ( g1_pre_topc @ X2 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_compts_1 @ X1 )
       != X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_pre_topc @ X0 )
      | ( ( k2_subset_1 @ ( k9_setfam_1 @ X1 ) )
        = ( u1_pre_topc @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['20','30'])).

thf('32',plain,(
    ! [X1: $i] :
      ( ( ( k2_subset_1 @ ( k9_setfam_1 @ X1 ) )
        = ( u1_pre_topc @ ( k1_compts_1 @ X1 ) ) )
      | ~ ( v1_pre_topc @ ( k1_compts_1 @ X1 ) )
      | ~ ( l1_pre_topc @ ( k1_compts_1 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf(dt_k1_compts_1,axiom,(
    ! [A: $i] :
      ( l1_pre_topc @ ( k1_compts_1 @ A ) ) )).

thf('33',plain,(
    ! [X12: $i] :
      ( l1_pre_topc @ ( k1_compts_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_compts_1])).

thf('34',plain,(
    ! [X13: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X13 ) @ ( k9_setfam_1 @ X13 ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf(dt_g1_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( v1_pre_topc @ ( g1_pre_topc @ A @ B ) )
        & ( l1_pre_topc @ ( g1_pre_topc @ A @ B ) ) ) ) )).

thf('35',plain,(
    ! [X10: $i,X11: $i] :
      ( ( v1_pre_topc @ ( g1_pre_topc @ X10 @ X11 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X10 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_g1_pre_topc])).

thf('36',plain,(
    ! [X31: $i] :
      ( ( k9_setfam_1 @ X31 )
      = ( k1_zfmisc_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('37',plain,(
    ! [X31: $i] :
      ( ( k9_setfam_1 @ X31 )
      = ( k1_zfmisc_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('38',plain,(
    ! [X10: $i,X11: $i] :
      ( ( v1_pre_topc @ ( g1_pre_topc @ X10 @ X11 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k9_setfam_1 @ ( k9_setfam_1 @ X10 ) ) ) ) ),
    inference(demod,[status(thm)],['35','36','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( v1_pre_topc @ ( g1_pre_topc @ X0 @ ( k2_subset_1 @ ( k9_setfam_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['34','38'])).

thf('40',plain,(
    ! [X9: $i] :
      ( ( k1_compts_1 @ X9 )
      = ( g1_pre_topc @ X9 @ ( k2_subset_1 @ ( k9_setfam_1 @ X9 ) ) ) ) ),
    inference(cnf,[status(esa)],[d8_compts_1])).

thf('41',plain,(
    ! [X0: $i] :
      ( v1_pre_topc @ ( k1_compts_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X1: $i] :
      ( ( k2_subset_1 @ ( k9_setfam_1 @ X1 ) )
      = ( u1_pre_topc @ ( k1_compts_1 @ X1 ) ) ) ),
    inference('simplify_reflect+',[status(thm)],['32','33','41'])).

thf('43',plain,(
    ! [X13: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X13 ) @ ( k9_setfam_1 @ X13 ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('44',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( u1_pre_topc @ ( k1_compts_1 @ X0 ) ) @ ( k9_setfam_1 @ ( k9_setfam_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ( ( g1_pre_topc @ X24 @ X25 )
       != ( g1_pre_topc @ X22 @ X23 ) )
      | ( X24 = X22 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[free_g1_pre_topc])).

thf('46',plain,(
    ! [X31: $i] :
      ( ( k9_setfam_1 @ X31 )
      = ( k1_zfmisc_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('47',plain,(
    ! [X31: $i] :
      ( ( k9_setfam_1 @ X31 )
      = ( k1_zfmisc_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('48',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ( ( g1_pre_topc @ X24 @ X25 )
       != ( g1_pre_topc @ X22 @ X23 ) )
      | ( X24 = X22 )
      | ~ ( m1_subset_1 @ X25 @ ( k9_setfam_1 @ ( k9_setfam_1 @ X24 ) ) ) ) ),
    inference(demod,[status(thm)],['45','46','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0 = X1 )
      | ( ( g1_pre_topc @ X0 @ ( u1_pre_topc @ ( k1_compts_1 @ X0 ) ) )
       != ( g1_pre_topc @ X1 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['44','48'])).

thf('50',plain,(
    ! [X9: $i] :
      ( ( k1_compts_1 @ X9 )
      = ( g1_pre_topc @ X9 @ ( k2_subset_1 @ ( k9_setfam_1 @ X9 ) ) ) ) ),
    inference(cnf,[status(esa)],[d8_compts_1])).

thf('51',plain,(
    ! [X1: $i] :
      ( ( k2_subset_1 @ ( k9_setfam_1 @ X1 ) )
      = ( u1_pre_topc @ ( k1_compts_1 @ X1 ) ) ) ),
    inference('simplify_reflect+',[status(thm)],['32','33','41'])).

thf('52',plain,(
    ! [X9: $i] :
      ( ( k1_compts_1 @ X9 )
      = ( g1_pre_topc @ X9 @ ( u1_pre_topc @ ( k1_compts_1 @ X9 ) ) ) ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0 = X1 )
      | ( ( k1_compts_1 @ X0 )
       != ( g1_pre_topc @ X1 @ X2 ) ) ) ),
    inference(demod,[status(thm)],['49','52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_compts_1 @ X1 )
       != X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_pre_topc @ X0 )
      | ( X1
        = ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['19','53'])).

thf('55',plain,(
    ! [X1: $i] :
      ( ( X1
        = ( u1_struct_0 @ ( k1_compts_1 @ X1 ) ) )
      | ~ ( v1_pre_topc @ ( k1_compts_1 @ X1 ) )
      | ~ ( l1_pre_topc @ ( k1_compts_1 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['54'])).

thf('56',plain,(
    ! [X12: $i] :
      ( l1_pre_topc @ ( k1_compts_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_compts_1])).

thf('57',plain,(
    ! [X0: $i] :
      ( v1_pre_topc @ ( k1_compts_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('58',plain,(
    ! [X1: $i] :
      ( X1
      = ( u1_struct_0 @ ( k1_compts_1 @ X1 ) ) ) ),
    inference('simplify_reflect+',[status(thm)],['55','56','57'])).

thf('59',plain,(
    ! [X34: $i,X35: $i] :
      ( ~ ( v1_tdlat_3 @ X34 )
      | ( v4_pre_topc @ X35 @ X34 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X34 ) ) )
      | ~ ( l1_pre_topc @ X34 )
      | ~ ( v2_pre_topc @ X34 ) ) ),
    inference(cnf,[status(esa)],[t18_tdlat_3])).

thf('60',plain,(
    ! [X31: $i] :
      ( ( k9_setfam_1 @ X31 )
      = ( k1_zfmisc_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('61',plain,(
    ! [X34: $i,X35: $i] :
      ( ~ ( v1_tdlat_3 @ X34 )
      | ( v4_pre_topc @ X35 @ X34 )
      | ~ ( m1_subset_1 @ X35 @ ( k9_setfam_1 @ ( u1_struct_0 @ X34 ) ) )
      | ~ ( l1_pre_topc @ X34 )
      | ~ ( v2_pre_topc @ X34 ) ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k9_setfam_1 @ X0 ) )
      | ~ ( v2_pre_topc @ ( k1_compts_1 @ X0 ) )
      | ~ ( l1_pre_topc @ ( k1_compts_1 @ X0 ) )
      | ( v4_pre_topc @ X1 @ ( k1_compts_1 @ X0 ) )
      | ~ ( v1_tdlat_3 @ ( k1_compts_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['58','61'])).

thf('63',plain,(
    ! [X12: $i] :
      ( l1_pre_topc @ ( k1_compts_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_compts_1])).

thf(cc1_tdlat_3,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( ( v1_tdlat_3 @ A )
       => ( v2_pre_topc @ A ) ) ) )).

thf('64',plain,(
    ! [X4: $i] :
      ( ~ ( v1_tdlat_3 @ X4 )
      | ( v2_pre_topc @ X4 )
      | ~ ( l1_pre_topc @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc1_tdlat_3])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( v2_pre_topc @ ( k1_compts_1 @ X0 ) )
      | ~ ( v1_tdlat_3 @ ( k1_compts_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf(fc4_tex_1,axiom,(
    ! [A: $i] :
      ( v1_tdlat_3 @ ( k1_compts_1 @ A ) ) )).

thf('66',plain,(
    ! [X21: $i] :
      ( v1_tdlat_3 @ ( k1_compts_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[fc4_tex_1])).

thf('67',plain,(
    ! [X0: $i] :
      ( v2_pre_topc @ ( k1_compts_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X12: $i] :
      ( l1_pre_topc @ ( k1_compts_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_compts_1])).

thf('69',plain,(
    ! [X21: $i] :
      ( v1_tdlat_3 @ ( k1_compts_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[fc4_tex_1])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k9_setfam_1 @ X0 ) )
      | ( v4_pre_topc @ X1 @ ( k1_compts_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['62','67','68','69'])).

thf('71',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v1_tdlat_3 @ X0 )
      | ( v4_pre_topc @ ( sk_B @ X0 ) @ ( k1_compts_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['18','70'])).

thf('72',plain,(
    ! [X34: $i] :
      ( ( m1_subset_1 @ ( sk_B @ X34 ) @ ( k9_setfam_1 @ ( u1_struct_0 @ X34 ) ) )
      | ( v1_tdlat_3 @ X34 )
      | ~ ( l1_pre_topc @ X34 )
      | ~ ( v2_pre_topc @ X34 ) ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('73',plain,(
    ! [X15: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X15 ) @ ( k9_setfam_1 @ ( k2_zfmisc_1 @ X15 @ X15 ) ) ) ),
    inference(demod,[status(thm)],['8','9','10'])).

thf('74',plain,(
    ! [X1: $i] :
      ( X1
      = ( u1_struct_0 @ ( k1_compts_1 @ X1 ) ) ) ),
    inference('simplify_reflect+',[status(thm)],['55','56','57'])).

thf('75',plain,(
    ! [X36: $i,X37: $i] :
      ( ~ ( v1_funct_1 @ X36 )
      | ~ ( v1_funct_2 @ X36 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X37 ) )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X37 ) ) ) )
      | ( v5_pre_topc @ X36 @ sk_A @ X37 )
      | ~ ( l1_pre_topc @ X37 )
      | ~ ( v2_pre_topc @ X37 )
      | ( v2_struct_0 @ X37 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    ! [X31: $i] :
      ( ( k9_setfam_1 @ X31 )
      = ( k1_zfmisc_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('77',plain,(
    ! [X36: $i,X37: $i] :
      ( ~ ( v1_funct_1 @ X36 )
      | ~ ( v1_funct_2 @ X36 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X37 ) )
      | ~ ( m1_subset_1 @ X36 @ ( k9_setfam_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X37 ) ) ) )
      | ( v5_pre_topc @ X36 @ sk_A @ X37 )
      | ~ ( l1_pre_topc @ X37 )
      | ~ ( v2_pre_topc @ X37 )
      | ( v2_struct_0 @ X37 ) ) ),
    inference(demod,[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k9_setfam_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ( v2_struct_0 @ ( k1_compts_1 @ X0 ) )
      | ~ ( v2_pre_topc @ ( k1_compts_1 @ X0 ) )
      | ~ ( l1_pre_topc @ ( k1_compts_1 @ X0 ) )
      | ( v5_pre_topc @ X1 @ sk_A @ ( k1_compts_1 @ X0 ) )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k1_compts_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['74','77'])).

thf('79',plain,(
    ! [X0: $i] :
      ( v2_pre_topc @ ( k1_compts_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['65','66'])).

thf('80',plain,(
    ! [X12: $i] :
      ( l1_pre_topc @ ( k1_compts_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_compts_1])).

thf('81',plain,(
    ! [X1: $i] :
      ( X1
      = ( u1_struct_0 @ ( k1_compts_1 @ X1 ) ) ) ),
    inference('simplify_reflect+',[status(thm)],['55','56','57'])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k9_setfam_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ( v2_struct_0 @ ( k1_compts_1 @ X0 ) )
      | ( v5_pre_topc @ X1 @ sk_A @ ( k1_compts_1 @ X0 ) )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ sk_A ) @ X0 )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['78','79','80','81'])).

thf('83',plain,
    ( ~ ( v1_funct_1 @ ( k6_relat_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( v1_funct_2 @ ( k6_relat_1 @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v5_pre_topc @ ( k6_relat_1 @ ( u1_struct_0 @ sk_A ) ) @ sk_A @ ( k1_compts_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v2_struct_0 @ ( k1_compts_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['73','82'])).

thf(fc3_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('84',plain,(
    ! [X20: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('85',plain,(
    ! [X15: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X15 ) @ ( k9_setfam_1 @ ( k2_zfmisc_1 @ X15 @ X15 ) ) ) ),
    inference(demod,[status(thm)],['8','9','10'])).

thf(cc1_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( v1_funct_1 @ C )
          & ( v1_partfun1 @ C @ A ) )
       => ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B ) ) ) ) )).

thf('86',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_partfun1 @ X1 @ X2 )
      | ( v1_funct_2 @ X1 @ X2 @ X3 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_funct_2])).

thf('87',plain,(
    ! [X31: $i] :
      ( ( k9_setfam_1 @ X31 )
      = ( k1_zfmisc_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('88',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_partfun1 @ X1 @ X2 )
      | ( v1_funct_2 @ X1 @ X2 @ X3 )
      | ~ ( m1_subset_1 @ X1 @ ( k9_setfam_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ) ) ),
    inference(demod,[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k6_relat_1 @ X0 ) @ X0 @ X0 )
      | ~ ( v1_partfun1 @ ( k6_relat_1 @ X0 ) @ X0 )
      | ~ ( v1_funct_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['85','88'])).

thf('90',plain,(
    ! [X14: $i] :
      ( v1_partfun1 @ ( k6_partfun1 @ X14 ) @ X14 ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('91',plain,(
    ! [X26: $i] :
      ( ( k6_partfun1 @ X26 )
      = ( k6_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('92',plain,(
    ! [X14: $i] :
      ( v1_partfun1 @ ( k6_relat_1 @ X14 ) @ X14 ) ),
    inference(demod,[status(thm)],['90','91'])).

thf('93',plain,(
    ! [X20: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('94',plain,(
    ! [X0: $i] :
      ( v1_funct_2 @ ( k6_relat_1 @ X0 ) @ X0 @ X0 ) ),
    inference(demod,[status(thm)],['89','92','93'])).

thf('95',plain,
    ( ( v5_pre_topc @ ( k6_relat_1 @ ( u1_struct_0 @ sk_A ) ) @ sk_A @ ( k1_compts_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v2_struct_0 @ ( k1_compts_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['83','84','94'])).

thf('96',plain,(
    ! [X15: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X15 ) @ ( k9_setfam_1 @ ( k2_zfmisc_1 @ X15 @ X15 ) ) ) ),
    inference(demod,[status(thm)],['8','9','10'])).

thf('97',plain,(
    ! [X1: $i] :
      ( X1
      = ( u1_struct_0 @ ( k1_compts_1 @ X1 ) ) ) ),
    inference('simplify_reflect+',[status(thm)],['55','56','57'])).

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

thf('98',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ~ ( l1_pre_topc @ X5 )
      | ~ ( v5_pre_topc @ X6 @ X7 @ X5 )
      | ~ ( v4_pre_topc @ X8 @ X5 )
      | ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ X7 ) @ ( u1_struct_0 @ X5 ) @ X6 @ X8 ) @ X7 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X7 ) @ ( u1_struct_0 @ X5 ) ) ) )
      | ~ ( v1_funct_2 @ X6 @ ( u1_struct_0 @ X7 ) @ ( u1_struct_0 @ X5 ) )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[d12_pre_topc])).

thf('99',plain,(
    ! [X31: $i] :
      ( ( k9_setfam_1 @ X31 )
      = ( k1_zfmisc_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('100',plain,(
    ! [X31: $i] :
      ( ( k9_setfam_1 @ X31 )
      = ( k1_zfmisc_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('101',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ~ ( l1_pre_topc @ X5 )
      | ~ ( v5_pre_topc @ X6 @ X7 @ X5 )
      | ~ ( v4_pre_topc @ X8 @ X5 )
      | ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ X7 ) @ ( u1_struct_0 @ X5 ) @ X6 @ X8 ) @ X7 )
      | ~ ( m1_subset_1 @ X8 @ ( k9_setfam_1 @ ( u1_struct_0 @ X5 ) ) )
      | ~ ( m1_subset_1 @ X6 @ ( k9_setfam_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X7 ) @ ( u1_struct_0 @ X5 ) ) ) )
      | ~ ( v1_funct_2 @ X6 @ ( u1_struct_0 @ X7 ) @ ( u1_struct_0 @ X5 ) )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(demod,[status(thm)],['98','99','100'])).

thf('102',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( k9_setfam_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X1 ) @ X0 ) ) )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_funct_2 @ X2 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ ( k1_compts_1 @ X0 ) ) )
      | ~ ( m1_subset_1 @ X3 @ ( k9_setfam_1 @ ( u1_struct_0 @ ( k1_compts_1 @ X0 ) ) ) )
      | ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ ( k1_compts_1 @ X0 ) ) @ X2 @ X3 ) @ X1 )
      | ~ ( v4_pre_topc @ X3 @ ( k1_compts_1 @ X0 ) )
      | ~ ( v5_pre_topc @ X2 @ X1 @ ( k1_compts_1 @ X0 ) )
      | ~ ( l1_pre_topc @ ( k1_compts_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['97','101'])).

thf('103',plain,(
    ! [X1: $i] :
      ( X1
      = ( u1_struct_0 @ ( k1_compts_1 @ X1 ) ) ) ),
    inference('simplify_reflect+',[status(thm)],['55','56','57'])).

thf('104',plain,(
    ! [X1: $i] :
      ( X1
      = ( u1_struct_0 @ ( k1_compts_1 @ X1 ) ) ) ),
    inference('simplify_reflect+',[status(thm)],['55','56','57'])).

thf('105',plain,(
    ! [X1: $i] :
      ( X1
      = ( u1_struct_0 @ ( k1_compts_1 @ X1 ) ) ) ),
    inference('simplify_reflect+',[status(thm)],['55','56','57'])).

thf('106',plain,(
    ! [X12: $i] :
      ( l1_pre_topc @ ( k1_compts_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_compts_1])).

thf('107',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( k9_setfam_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X1 ) @ X0 ) ) )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_funct_2 @ X2 @ ( u1_struct_0 @ X1 ) @ X0 )
      | ~ ( m1_subset_1 @ X3 @ ( k9_setfam_1 @ X0 ) )
      | ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ X1 ) @ X0 @ X2 @ X3 ) @ X1 )
      | ~ ( v4_pre_topc @ X3 @ ( k1_compts_1 @ X0 ) )
      | ~ ( v5_pre_topc @ X2 @ X1 @ ( k1_compts_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['102','103','104','105','106'])).

thf('108',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v5_pre_topc @ ( k6_relat_1 @ ( u1_struct_0 @ X0 ) ) @ X0 @ ( k1_compts_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( v4_pre_topc @ X1 @ ( k1_compts_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( k6_relat_1 @ ( u1_struct_0 @ X0 ) ) @ X1 ) @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k9_setfam_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( v1_funct_2 @ ( k6_relat_1 @ ( u1_struct_0 @ X0 ) ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k6_relat_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['96','107'])).

thf('109',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relset_1 @ X0 @ X0 @ ( k6_relat_1 @ X0 ) @ X1 )
      = ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['11','14'])).

thf('110',plain,(
    ! [X0: $i] :
      ( v1_funct_2 @ ( k6_relat_1 @ X0 ) @ X0 @ X0 ) ),
    inference(demod,[status(thm)],['89','92','93'])).

thf('111',plain,(
    ! [X20: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('112',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v5_pre_topc @ ( k6_relat_1 @ ( u1_struct_0 @ X0 ) ) @ X0 @ ( k1_compts_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( v4_pre_topc @ X1 @ ( k1_compts_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( v4_pre_topc @ ( k10_relat_1 @ ( k6_relat_1 @ ( u1_struct_0 @ X0 ) ) @ X1 ) @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k9_setfam_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(demod,[status(thm)],['108','109','110','111'])).

thf('113',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ ( k1_compts_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k9_setfam_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v4_pre_topc @ ( k10_relat_1 @ ( k6_relat_1 @ ( u1_struct_0 @ sk_A ) ) @ X0 ) @ sk_A )
      | ~ ( v4_pre_topc @ X0 @ ( k1_compts_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['95','112'])).

thf('114',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ ( k1_compts_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( k9_setfam_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v4_pre_topc @ ( k10_relat_1 @ ( k6_relat_1 @ ( u1_struct_0 @ sk_A ) ) @ X0 ) @ sk_A )
      | ~ ( v4_pre_topc @ X0 @ ( k1_compts_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['113','114'])).

thf('116',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v1_tdlat_3 @ sk_A )
    | ~ ( v4_pre_topc @ ( sk_B @ sk_A ) @ ( k1_compts_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v4_pre_topc @ ( k10_relat_1 @ ( k6_relat_1 @ ( u1_struct_0 @ sk_A ) ) @ ( sk_B @ sk_A ) ) @ sk_A )
    | ( v2_struct_0 @ ( k1_compts_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['72','115'])).

thf('117',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,
    ( ( v1_tdlat_3 @ sk_A )
    | ~ ( v4_pre_topc @ ( sk_B @ sk_A ) @ ( k1_compts_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v4_pre_topc @ ( k10_relat_1 @ ( k6_relat_1 @ ( u1_struct_0 @ sk_A ) ) @ ( sk_B @ sk_A ) ) @ sk_A )
    | ( v2_struct_0 @ ( k1_compts_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['116','117','118'])).

thf('120',plain,
    ( ( v1_tdlat_3 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ( v2_struct_0 @ ( k1_compts_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v4_pre_topc @ ( k10_relat_1 @ ( k6_relat_1 @ ( u1_struct_0 @ sk_A ) ) @ ( sk_B @ sk_A ) ) @ sk_A )
    | ( v1_tdlat_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['71','119'])).

thf('121',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,
    ( ( v1_tdlat_3 @ sk_A )
    | ( v2_struct_0 @ ( k1_compts_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v4_pre_topc @ ( k10_relat_1 @ ( k6_relat_1 @ ( u1_struct_0 @ sk_A ) ) @ ( sk_B @ sk_A ) ) @ sk_A )
    | ( v1_tdlat_3 @ sk_A ) ),
    inference(demod,[status(thm)],['120','121','122'])).

thf('124',plain,
    ( ( v4_pre_topc @ ( k10_relat_1 @ ( k6_relat_1 @ ( u1_struct_0 @ sk_A ) ) @ ( sk_B @ sk_A ) ) @ sk_A )
    | ( v2_struct_0 @ ( k1_compts_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v1_tdlat_3 @ sk_A ) ),
    inference(simplify,[status(thm)],['123'])).

thf('125',plain,(
    ~ ( v1_tdlat_3 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,
    ( ( v2_struct_0 @ ( k1_compts_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v4_pre_topc @ ( k10_relat_1 @ ( k6_relat_1 @ ( u1_struct_0 @ sk_A ) ) @ ( sk_B @ sk_A ) ) @ sk_A ) ),
    inference(clc,[status(thm)],['124','125'])).

thf('127',plain,
    ( ( v4_pre_topc @ ( sk_B @ sk_A ) @ sk_A )
    | ( v1_tdlat_3 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ( v2_struct_0 @ ( k1_compts_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['17','126'])).

thf('128',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('129',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('130',plain,
    ( ( v4_pre_topc @ ( sk_B @ sk_A ) @ sk_A )
    | ( v1_tdlat_3 @ sk_A )
    | ( v2_struct_0 @ ( k1_compts_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['127','128','129'])).

thf('131',plain,(
    ~ ( v1_tdlat_3 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('132',plain,
    ( ( v2_struct_0 @ ( k1_compts_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v4_pre_topc @ ( sk_B @ sk_A ) @ sk_A ) ),
    inference(clc,[status(thm)],['130','131'])).

thf('133',plain,(
    ! [X34: $i] :
      ( ~ ( v4_pre_topc @ ( sk_B @ X34 ) @ X34 )
      | ( v1_tdlat_3 @ X34 )
      | ~ ( l1_pre_topc @ X34 )
      | ~ ( v2_pre_topc @ X34 ) ) ),
    inference(cnf,[status(esa)],[t18_tdlat_3])).

thf('134',plain,
    ( ( v2_struct_0 @ ( k1_compts_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v1_tdlat_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['132','133'])).

thf('135',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('136',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('137',plain,
    ( ( v2_struct_0 @ ( k1_compts_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v1_tdlat_3 @ sk_A ) ),
    inference(demod,[status(thm)],['134','135','136'])).

thf('138',plain,(
    ~ ( v1_tdlat_3 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('139',plain,(
    v2_struct_0 @ ( k1_compts_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['137','138'])).

thf(fc2_compts_1,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ~ ( v2_struct_0 @ ( k1_compts_1 @ A ) ) ) )).

thf('140',plain,(
    ! [X17: $i] :
      ( ~ ( v2_struct_0 @ ( k1_compts_1 @ X17 ) )
      | ( v1_xboole_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[fc2_compts_1])).

thf('141',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['139','140'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('142',plain,(
    ! [X18: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X18 ) )
      | ~ ( l1_struct_0 @ X18 )
      | ( v2_struct_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('143',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['141','142'])).

thf('144',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('145',plain,(
    ! [X16: $i] :
      ( ( l1_struct_0 @ X16 )
      | ~ ( l1_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('146',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['144','145'])).

thf('147',plain,(
    v2_struct_0 @ sk_A ),
    inference(demod,[status(thm)],['143','146'])).

thf('148',plain,(
    $false ),
    inference(demod,[status(thm)],['0','147'])).


%------------------------------------------------------------------------------
