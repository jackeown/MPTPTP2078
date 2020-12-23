%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.leCupJiOo2

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:10:59 EST 2020

% Result     : Theorem 0.69s
% Output     : Refutation 0.69s
% Verified   : 
% Statistics : Number of formulae       :  201 (2288 expanded)
%              Number of leaves         :   39 ( 675 expanded)
%              Depth                    :   25
%              Number of atoms          : 2186 (42202 expanded)
%              Number of equality atoms :   74 ( 404 expanded)
%              Maximal formula depth    :   22 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k9_tmap_1_type,type,(
    k9_tmap_1: $i > $i > $i )).

thf(r1_funct_2_type,type,(
    r1_funct_2: $i > $i > $i > $i > $i > $i > $o )).

thf(r1_tmap_1_type,type,(
    r1_tmap_1: $i > $i > $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k8_tmap_1_type,type,(
    k8_tmap_1: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i > $i )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(k7_tmap_1_type,type,(
    k7_tmap_1: $i > $i > $i )).

thf(k5_tmap_1_type,type,(
    k5_tmap_1: $i > $i > $i )).

thf(k2_tmap_1_type,type,(
    k2_tmap_1: $i > $i > $i > $i > $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k6_tmap_1_type,type,(
    k6_tmap_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(t119_tmap_1,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( m1_pre_topc @ B @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ B ) )
             => ( r1_tmap_1 @ B @ ( k8_tmap_1 @ A @ B ) @ ( k2_tmap_1 @ A @ ( k8_tmap_1 @ A @ B ) @ ( k9_tmap_1 @ A @ B ) @ B ) @ C ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( ~ ( v2_struct_0 @ B )
              & ( m1_pre_topc @ B @ A ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ B ) )
               => ( r1_tmap_1 @ B @ ( k8_tmap_1 @ A @ B ) @ ( k2_tmap_1 @ A @ ( k8_tmap_1 @ A @ B ) @ ( k9_tmap_1 @ A @ B ) @ B ) @ C ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t119_tmap_1])).

thf('0',plain,(
    ~ ( r1_tmap_1 @ sk_B @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_B ) @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t1_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( m1_subset_1 @ ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('2',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( m1_pre_topc @ X29 @ X30 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X29 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X30 ) ) )
      | ~ ( l1_pre_topc @ X30 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('3',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf(dt_k7_tmap_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( ( v1_funct_1 @ ( k7_tmap_1 @ A @ B ) )
        & ( v1_funct_2 @ ( k7_tmap_1 @ A @ B ) @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ A @ B ) ) )
        & ( m1_subset_1 @ ( k7_tmap_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ A @ B ) ) ) ) ) ) ) )).

thf('6',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( l1_pre_topc @ X18 )
      | ~ ( v2_pre_topc @ X18 )
      | ( v2_struct_0 @ X18 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ( m1_subset_1 @ ( k7_tmap_1 @ X18 @ X19 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X18 ) @ ( u1_struct_0 @ ( k6_tmap_1 @ X18 @ X19 ) ) ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_tmap_1])).

thf('7',plain,
    ( ( m1_subset_1 @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ) ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf(d10_tmap_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k7_tmap_1 @ A @ B )
            = ( k6_partfun1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('9',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ( ( k7_tmap_1 @ X9 @ X8 )
        = ( k6_partfun1 @ ( u1_struct_0 @ X9 ) ) )
      | ~ ( l1_pre_topc @ X9 )
      | ~ ( v2_pre_topc @ X9 )
      | ( v2_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d10_tmap_1])).

thf('10',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) )
      = ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) )
      = ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['10','11','12'])).

thf('14',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) )
    = ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['13','14'])).

thf('16',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ( m1_subset_1 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ) ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['7','15','16','17'])).

thf('19',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    m1_subset_1 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ) ) ) ),
    inference(clc,[status(thm)],['18','19'])).

thf('21',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf(d11_tmap_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ! [C: $i] :
              ( ( ( v1_pre_topc @ C )
                & ( v2_pre_topc @ C )
                & ( l1_pre_topc @ C ) )
             => ( ( C
                  = ( k8_tmap_1 @ A @ B ) )
              <=> ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                   => ( ( D
                        = ( u1_struct_0 @ B ) )
                     => ( C
                        = ( k6_tmap_1 @ A @ D ) ) ) ) ) ) ) ) )).

thf('22',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ~ ( m1_pre_topc @ X10 @ X11 )
      | ( X12
       != ( k8_tmap_1 @ X11 @ X10 ) )
      | ( X13
       != ( u1_struct_0 @ X10 ) )
      | ( X12
        = ( k6_tmap_1 @ X11 @ X13 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ~ ( l1_pre_topc @ X12 )
      | ~ ( v2_pre_topc @ X12 )
      | ~ ( v1_pre_topc @ X12 )
      | ~ ( l1_pre_topc @ X11 )
      | ~ ( v2_pre_topc @ X11 )
      | ( v2_struct_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d11_tmap_1])).

thf('23',plain,(
    ! [X10: $i,X11: $i] :
      ( ( v2_struct_0 @ X11 )
      | ~ ( v2_pre_topc @ X11 )
      | ~ ( l1_pre_topc @ X11 )
      | ~ ( v1_pre_topc @ ( k8_tmap_1 @ X11 @ X10 ) )
      | ~ ( v2_pre_topc @ ( k8_tmap_1 @ X11 @ X10 ) )
      | ~ ( l1_pre_topc @ ( k8_tmap_1 @ X11 @ X10 ) )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X10 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ( ( k8_tmap_1 @ X11 @ X10 )
        = ( k6_tmap_1 @ X11 @ ( u1_struct_0 @ X10 ) ) )
      | ~ ( m1_pre_topc @ X10 @ X11 ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,
    ( ~ ( m1_pre_topc @ sk_B @ sk_A )
    | ( ( k8_tmap_1 @ sk_A @ sk_B )
      = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
    | ~ ( l1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( v2_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( v1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['21','23'])).

thf('25',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k8_tmap_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_pre_topc @ B @ A ) )
     => ( ( v1_pre_topc @ ( k8_tmap_1 @ A @ B ) )
        & ( v2_pre_topc @ ( k8_tmap_1 @ A @ B ) )
        & ( l1_pre_topc @ ( k8_tmap_1 @ A @ B ) ) ) ) )).

thf('27',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( l1_pre_topc @ X20 )
      | ~ ( v2_pre_topc @ X20 )
      | ( v2_struct_0 @ X20 )
      | ~ ( m1_pre_topc @ X21 @ X20 )
      | ( l1_pre_topc @ ( k8_tmap_1 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k8_tmap_1])).

thf('28',plain,
    ( ( l1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( l1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['28','29','30'])).

thf('32',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    l1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['31','32'])).

thf('34',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( l1_pre_topc @ X20 )
      | ~ ( v2_pre_topc @ X20 )
      | ( v2_struct_0 @ X20 )
      | ~ ( m1_pre_topc @ X21 @ X20 )
      | ( v2_pre_topc @ ( k8_tmap_1 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k8_tmap_1])).

thf('36',plain,
    ( ( v2_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ( v2_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['36','37','38'])).

thf('40',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    v2_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['39','40'])).

thf('42',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( l1_pre_topc @ X20 )
      | ~ ( v2_pre_topc @ X20 )
      | ( v2_struct_0 @ X20 )
      | ~ ( m1_pre_topc @ X21 @ X20 )
      | ( v1_pre_topc @ ( k8_tmap_1 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k8_tmap_1])).

thf('44',plain,
    ( ( v1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ( v1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['44','45','46'])).

thf('48',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    v1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['47','48'])).

thf('50',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,
    ( ( ( k8_tmap_1 @ sk_A @ sk_B )
      = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['24','25','33','41','49','50','51'])).

thf('53',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,
    ( ( k8_tmap_1 @ sk_A @ sk_B )
    = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['52','53'])).

thf('55',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t114_tmap_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( m1_pre_topc @ B @ A ) )
         => ( ( ( u1_struct_0 @ ( k8_tmap_1 @ A @ B ) )
              = ( u1_struct_0 @ A ) )
            & ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
               => ( ( C
                    = ( u1_struct_0 @ B ) )
                 => ( ( u1_pre_topc @ ( k8_tmap_1 @ A @ B ) )
                    = ( k5_tmap_1 @ A @ C ) ) ) ) ) ) ) )).

thf('56',plain,(
    ! [X26: $i,X27: $i] :
      ( ( v2_struct_0 @ X26 )
      | ~ ( m1_pre_topc @ X26 @ X27 )
      | ( ( u1_struct_0 @ ( k8_tmap_1 @ X27 @ X26 ) )
        = ( u1_struct_0 @ X27 ) )
      | ~ ( l1_pre_topc @ X27 )
      | ~ ( v2_pre_topc @ X27 )
      | ( v2_struct_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t114_tmap_1])).

thf('57',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
      = ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
      = ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['57','58','59'])).

thf('61',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['60','61'])).

thf('63',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,
    ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['62','63'])).

thf('65',plain,(
    m1_subset_1 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['20','54','64'])).

thf('66',plain,(
    m1_subset_1 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['20','54','64'])).

thf(redefinition_r1_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ~ ( v1_xboole_0 @ B )
        & ~ ( v1_xboole_0 @ D )
        & ( v1_funct_1 @ E )
        & ( v1_funct_2 @ E @ A @ B )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ F )
        & ( v1_funct_2 @ F @ C @ D )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( r1_funct_2 @ A @ B @ C @ D @ E @ F )
      <=> ( E = F ) ) ) )).

thf('67',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) ) )
      | ~ ( v1_funct_2 @ X2 @ X3 @ X4 )
      | ~ ( v1_funct_1 @ X2 )
      | ( v1_xboole_0 @ X5 )
      | ( v1_xboole_0 @ X4 )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_funct_2 @ X6 @ X7 @ X5 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X5 ) ) )
      | ( r1_funct_2 @ X3 @ X4 @ X7 @ X5 @ X2 @ X6 )
      | ( X2 != X6 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_funct_2])).

thf('68',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( r1_funct_2 @ X3 @ X4 @ X7 @ X5 @ X6 @ X6 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X5 ) ) )
      | ~ ( v1_funct_2 @ X6 @ X7 @ X5 )
      | ( v1_xboole_0 @ X4 )
      | ( v1_xboole_0 @ X5 )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_funct_2 @ X6 @ X3 @ X4 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) ) ) ) ),
    inference(simplify,[status(thm)],['67'])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) )
      | ~ ( v1_funct_2 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ X1 @ X0 )
      | ~ ( v1_funct_1 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_funct_2 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( r1_funct_2 @ X1 @ X0 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['66','68'])).

thf('70',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('71',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( l1_pre_topc @ X18 )
      | ~ ( v2_pre_topc @ X18 )
      | ( v2_struct_0 @ X18 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ( v1_funct_1 @ ( k7_tmap_1 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_tmap_1])).

thf('72',plain,
    ( ( v1_funct_1 @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,
    ( ( v1_funct_1 @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['72','73','74'])).

thf('76',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    v1_funct_1 @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['75','76'])).

thf('78',plain,
    ( ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) )
    = ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['13','14'])).

thf('79',plain,(
    v1_funct_1 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['77','78'])).

thf('80',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('81',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( l1_pre_topc @ X18 )
      | ~ ( v2_pre_topc @ X18 )
      | ( v2_struct_0 @ X18 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ( v1_funct_2 @ ( k7_tmap_1 @ X18 @ X19 ) @ ( u1_struct_0 @ X18 ) @ ( u1_struct_0 @ ( k6_tmap_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_tmap_1])).

thf('82',plain,
    ( ( v1_funct_2 @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,
    ( ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) )
    = ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['13','14'])).

thf('84',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,
    ( ( v1_funct_2 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['82','83','84','85'])).

thf('87',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    v1_funct_2 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['86','87'])).

thf('89',plain,
    ( ( k8_tmap_1 @ sk_A @ sk_B )
    = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['52','53'])).

thf('90',plain,
    ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['62','63'])).

thf('91',plain,(
    v1_funct_2 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['88','89','90'])).

thf('92',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) )
      | ~ ( v1_funct_2 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ X1 @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ X0 )
      | ( r1_funct_2 @ X1 @ X0 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['69','79','91'])).

thf('93',plain,
    ( ( r1_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_funct_2 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['65','92'])).

thf('94',plain,(
    v1_funct_2 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['88','89','90'])).

thf('95',plain,
    ( ( r1_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['93','94'])).

thf('96',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r1_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['95'])).

thf('97',plain,(
    m1_subset_1 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['20','54','64'])).

thf('98',plain,
    ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['62','63'])).

thf(d12_tmap_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ! [C: $i] :
              ( ( ( v1_funct_1 @ C )
                & ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ A @ B ) ) )
                & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ A @ B ) ) ) ) ) )
             => ( ( C
                  = ( k9_tmap_1 @ A @ B ) )
              <=> ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                   => ( ( D
                        = ( u1_struct_0 @ B ) )
                     => ( r1_funct_2 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ A @ B ) ) @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ A @ D ) ) @ C @ ( k7_tmap_1 @ A @ D ) ) ) ) ) ) ) ) )).

thf('99',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( m1_pre_topc @ X14 @ X15 )
      | ( ( sk_D_1 @ X16 @ X14 @ X15 )
        = ( u1_struct_0 @ X14 ) )
      | ( X16
        = ( k9_tmap_1 @ X15 @ X14 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ ( k8_tmap_1 @ X15 @ X14 ) ) ) ) )
      | ~ ( v1_funct_2 @ X16 @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ ( k8_tmap_1 @ X15 @ X14 ) ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( l1_pre_topc @ X15 )
      | ~ ( v2_pre_topc @ X15 )
      | ( v2_struct_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d12_tmap_1])).

thf('100',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) )
      | ( X0
        = ( k9_tmap_1 @ sk_A @ sk_B ) )
      | ( ( sk_D_1 @ X0 @ sk_B @ sk_A )
        = ( u1_struct_0 @ sk_B ) )
      | ~ ( m1_pre_topc @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,
    ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['62','63'])).

thf('104',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( X0
        = ( k9_tmap_1 @ sk_A @ sk_B ) )
      | ( ( sk_D_1 @ X0 @ sk_B @ sk_A )
        = ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['100','101','102','103','104'])).

thf('106',plain,
    ( ( ( sk_D_1 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B @ sk_A )
      = ( u1_struct_0 @ sk_B ) )
    | ( ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) )
      = ( k9_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( v1_funct_2 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_funct_1 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['97','105'])).

thf('107',plain,(
    v1_funct_2 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['88','89','90'])).

thf('108',plain,(
    v1_funct_1 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['77','78'])).

thf('109',plain,
    ( ( ( sk_D_1 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B @ sk_A )
      = ( u1_struct_0 @ sk_B ) )
    | ( ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) )
      = ( k9_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['106','107','108'])).

thf('110',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,
    ( ( ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) )
      = ( k9_tmap_1 @ sk_A @ sk_B ) )
    | ( ( sk_D_1 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B @ sk_A )
      = ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['109','110'])).

thf('112',plain,
    ( ( ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) )
      = ( k9_tmap_1 @ sk_A @ sk_B ) )
    | ( ( sk_D_1 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B @ sk_A )
      = ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['109','110'])).

thf('113',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( m1_pre_topc @ X14 @ X15 )
      | ~ ( r1_funct_2 @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ ( k8_tmap_1 @ X15 @ X14 ) ) @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ ( k6_tmap_1 @ X15 @ ( sk_D_1 @ X16 @ X14 @ X15 ) ) ) @ X16 @ ( k7_tmap_1 @ X15 @ ( sk_D_1 @ X16 @ X14 @ X15 ) ) )
      | ( X16
        = ( k9_tmap_1 @ X15 @ X14 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ ( k8_tmap_1 @ X15 @ X14 ) ) ) ) )
      | ~ ( v1_funct_2 @ X16 @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ ( k8_tmap_1 @ X15 @ X14 ) ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( l1_pre_topc @ X15 )
      | ~ ( v2_pre_topc @ X15 )
      | ( v2_struct_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d12_tmap_1])).

thf('114',plain,
    ( ~ ( r1_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ) @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( k7_tmap_1 @ sk_A @ ( sk_D_1 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B @ sk_A ) ) )
    | ( ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) )
      = ( k9_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v1_funct_1 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( v1_funct_2 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) )
    | ~ ( m1_subset_1 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ) )
    | ( ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) )
      = ( k9_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['112','113'])).

thf('115',plain,
    ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['62','63'])).

thf('116',plain,
    ( ( k8_tmap_1 @ sk_A @ sk_B )
    = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['52','53'])).

thf('117',plain,
    ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['62','63'])).

thf('118',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,(
    v1_funct_1 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['77','78'])).

thf('121',plain,
    ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['62','63'])).

thf('122',plain,(
    v1_funct_2 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['88','89','90'])).

thf('123',plain,
    ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['62','63'])).

thf('124',plain,(
    m1_subset_1 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['20','54','64'])).

thf('125',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,
    ( ~ ( r1_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( k7_tmap_1 @ sk_A @ ( sk_D_1 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B @ sk_A ) ) )
    | ( ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) )
      = ( k9_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) )
      = ( k9_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['114','115','116','117','118','119','120','121','122','123','124','125'])).

thf('127',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) )
      = ( k9_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( r1_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( k7_tmap_1 @ sk_A @ ( sk_D_1 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['126'])).

thf('128',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('129',plain,
    ( ~ ( r1_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( k7_tmap_1 @ sk_A @ ( sk_D_1 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B @ sk_A ) ) )
    | ( ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) )
      = ( k9_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['127','128'])).

thf('130',plain,
    ( ~ ( r1_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
    | ( ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) )
      = ( k9_tmap_1 @ sk_A @ sk_B ) )
    | ( ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) )
      = ( k9_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['111','129'])).

thf('131',plain,
    ( ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) )
    = ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['13','14'])).

thf('132',plain,
    ( ~ ( r1_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) )
      = ( k9_tmap_1 @ sk_A @ sk_B ) )
    | ( ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) )
      = ( k9_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['130','131'])).

thf('133',plain,
    ( ( ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) )
      = ( k9_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( r1_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['132'])).

thf('134',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) )
      = ( k9_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['96','133'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('135',plain,(
    ! [X1: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X1 ) )
      | ~ ( l1_struct_0 @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('136',plain,
    ( ( ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) )
      = ( k9_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['134','135'])).

thf('137',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('138',plain,(
    ! [X0: $i] :
      ( ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('139',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['137','138'])).

thf('140',plain,
    ( ( ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) )
      = ( k9_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['136','139'])).

thf('141',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('142',plain,
    ( ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) )
    = ( k9_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['140','141'])).

thf('143',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('144',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf(t110_tmap_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( ~ ( v2_struct_0 @ C )
                & ( m1_pre_topc @ C @ A ) )
             => ( ( ( u1_struct_0 @ C )
                  = B )
               => ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( u1_struct_0 @ C ) )
                   => ( r1_tmap_1 @ C @ ( k6_tmap_1 @ A @ B ) @ ( k2_tmap_1 @ A @ ( k6_tmap_1 @ A @ B ) @ ( k7_tmap_1 @ A @ B ) @ C ) @ D ) ) ) ) ) ) )).

thf('145',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ( ( u1_struct_0 @ X24 )
       != X22 )
      | ~ ( m1_subset_1 @ X25 @ ( u1_struct_0 @ X24 ) )
      | ( r1_tmap_1 @ X24 @ ( k6_tmap_1 @ X23 @ X22 ) @ ( k2_tmap_1 @ X23 @ ( k6_tmap_1 @ X23 @ X22 ) @ ( k7_tmap_1 @ X23 @ X22 ) @ X24 ) @ X25 )
      | ~ ( m1_pre_topc @ X24 @ X23 )
      | ( v2_struct_0 @ X24 )
      | ~ ( l1_pre_topc @ X23 )
      | ~ ( v2_pre_topc @ X23 )
      | ( v2_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t110_tmap_1])).

thf('146',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( v2_struct_0 @ X23 )
      | ~ ( v2_pre_topc @ X23 )
      | ~ ( l1_pre_topc @ X23 )
      | ( v2_struct_0 @ X24 )
      | ~ ( m1_pre_topc @ X24 @ X23 )
      | ( r1_tmap_1 @ X24 @ ( k6_tmap_1 @ X23 @ ( u1_struct_0 @ X24 ) ) @ ( k2_tmap_1 @ X23 @ ( k6_tmap_1 @ X23 @ ( u1_struct_0 @ X24 ) ) @ ( k7_tmap_1 @ X23 @ ( u1_struct_0 @ X24 ) ) @ X24 ) @ X25 )
      | ~ ( m1_subset_1 @ X25 @ ( u1_struct_0 @ X24 ) )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X24 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) ) ) ),
    inference(simplify,[status(thm)],['145'])).

thf('147',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B ) )
      | ( r1_tmap_1 @ sk_B @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) @ ( k2_tmap_1 @ sk_A @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) @ sk_B ) @ X0 )
      | ~ ( m1_pre_topc @ sk_B @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['144','146'])).

thf('148',plain,
    ( ( k8_tmap_1 @ sk_A @ sk_B )
    = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['52','53'])).

thf('149',plain,
    ( ( k8_tmap_1 @ sk_A @ sk_B )
    = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['52','53'])).

thf('150',plain,
    ( ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) )
    = ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['13','14'])).

thf('151',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('152',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('153',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('154',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B ) )
      | ( r1_tmap_1 @ sk_B @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B ) @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['147','148','149','150','151','152','153'])).

thf('155',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r1_tmap_1 @ sk_B @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B ) @ sk_C ) ),
    inference('sup-',[status(thm)],['143','154'])).

thf('156',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('157',plain,
    ( ( r1_tmap_1 @ sk_B @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B ) @ sk_C )
    | ( v2_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['155','156'])).

thf('158',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('159',plain,(
    r1_tmap_1 @ sk_B @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B ) @ sk_C ),
    inference(clc,[status(thm)],['157','158'])).

thf('160',plain,(
    $false ),
    inference(demod,[status(thm)],['0','142','159'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.leCupJiOo2
% 0.13/0.36  % Computer   : n003.cluster.edu
% 0.13/0.36  % Model      : x86_64 x86_64
% 0.13/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.36  % Memory     : 8042.1875MB
% 0.13/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.36  % CPULimit   : 60
% 0.13/0.36  % DateTime   : Tue Dec  1 10:17:27 EST 2020
% 0.13/0.36  % CPUTime    : 
% 0.13/0.36  % Running portfolio for 600 s
% 0.13/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.37  % Number of cores: 8
% 0.13/0.37  % Python version: Python 3.6.8
% 0.13/0.37  % Running in FO mode
% 0.69/0.88  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.69/0.88  % Solved by: fo/fo7.sh
% 0.69/0.88  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.69/0.88  % done 180 iterations in 0.406s
% 0.69/0.88  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.69/0.88  % SZS output start Refutation
% 0.69/0.88  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.69/0.88  thf(k9_tmap_1_type, type, k9_tmap_1: $i > $i > $i).
% 0.69/0.88  thf(r1_funct_2_type, type, r1_funct_2: $i > $i > $i > $i > $i > $i > $o).
% 0.69/0.88  thf(r1_tmap_1_type, type, r1_tmap_1: $i > $i > $i > $i > $o).
% 0.69/0.88  thf(sk_C_type, type, sk_C: $i).
% 0.69/0.88  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.69/0.88  thf(k8_tmap_1_type, type, k8_tmap_1: $i > $i > $i).
% 0.69/0.88  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.69/0.88  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.69/0.88  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.69/0.88  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.69/0.88  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i > $i).
% 0.69/0.88  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 0.69/0.88  thf(k7_tmap_1_type, type, k7_tmap_1: $i > $i > $i).
% 0.69/0.88  thf(k5_tmap_1_type, type, k5_tmap_1: $i > $i > $i).
% 0.69/0.88  thf(k2_tmap_1_type, type, k2_tmap_1: $i > $i > $i > $i > $i).
% 0.69/0.88  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.69/0.88  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.69/0.88  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.69/0.88  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 0.69/0.88  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.69/0.88  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.69/0.88  thf(k6_tmap_1_type, type, k6_tmap_1: $i > $i > $i).
% 0.69/0.88  thf(sk_A_type, type, sk_A: $i).
% 0.69/0.88  thf(sk_B_type, type, sk_B: $i).
% 0.69/0.88  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 0.69/0.88  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.69/0.88  thf(t119_tmap_1, conjecture,
% 0.69/0.88    (![A:$i]:
% 0.69/0.88     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.69/0.88       ( ![B:$i]:
% 0.69/0.88         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.69/0.88           ( ![C:$i]:
% 0.69/0.88             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ B ) ) =>
% 0.69/0.88               ( r1_tmap_1 @
% 0.69/0.88                 B @ ( k8_tmap_1 @ A @ B ) @ 
% 0.69/0.88                 ( k2_tmap_1 @
% 0.69/0.88                   A @ ( k8_tmap_1 @ A @ B ) @ ( k9_tmap_1 @ A @ B ) @ B ) @ 
% 0.69/0.88                 C ) ) ) ) ) ))).
% 0.69/0.88  thf(zf_stmt_0, negated_conjecture,
% 0.69/0.88    (~( ![A:$i]:
% 0.69/0.88        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.69/0.88            ( l1_pre_topc @ A ) ) =>
% 0.69/0.88          ( ![B:$i]:
% 0.69/0.88            ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.69/0.88              ( ![C:$i]:
% 0.69/0.88                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ B ) ) =>
% 0.69/0.88                  ( r1_tmap_1 @
% 0.69/0.88                    B @ ( k8_tmap_1 @ A @ B ) @ 
% 0.69/0.88                    ( k2_tmap_1 @
% 0.69/0.88                      A @ ( k8_tmap_1 @ A @ B ) @ ( k9_tmap_1 @ A @ B ) @ B ) @ 
% 0.69/0.88                    C ) ) ) ) ) ) )),
% 0.69/0.88    inference('cnf.neg', [status(esa)], [t119_tmap_1])).
% 0.69/0.88  thf('0', plain,
% 0.69/0.88      (~ (r1_tmap_1 @ sk_B @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.69/0.88          (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.69/0.88           (k9_tmap_1 @ sk_A @ sk_B) @ sk_B) @ 
% 0.69/0.88          sk_C)),
% 0.69/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.88  thf('1', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.69/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.88  thf(t1_tsep_1, axiom,
% 0.69/0.88    (![A:$i]:
% 0.69/0.88     ( ( l1_pre_topc @ A ) =>
% 0.69/0.88       ( ![B:$i]:
% 0.69/0.88         ( ( m1_pre_topc @ B @ A ) =>
% 0.69/0.88           ( m1_subset_1 @
% 0.69/0.88             ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.69/0.88  thf('2', plain,
% 0.69/0.88      (![X29 : $i, X30 : $i]:
% 0.69/0.88         (~ (m1_pre_topc @ X29 @ X30)
% 0.69/0.88          | (m1_subset_1 @ (u1_struct_0 @ X29) @ 
% 0.69/0.88             (k1_zfmisc_1 @ (u1_struct_0 @ X30)))
% 0.69/0.88          | ~ (l1_pre_topc @ X30))),
% 0.69/0.88      inference('cnf', [status(esa)], [t1_tsep_1])).
% 0.69/0.88  thf('3', plain,
% 0.69/0.88      ((~ (l1_pre_topc @ sk_A)
% 0.69/0.88        | (m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.69/0.88           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.69/0.88      inference('sup-', [status(thm)], ['1', '2'])).
% 0.69/0.88  thf('4', plain, ((l1_pre_topc @ sk_A)),
% 0.69/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.88  thf('5', plain,
% 0.69/0.88      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.69/0.88        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.69/0.88      inference('demod', [status(thm)], ['3', '4'])).
% 0.69/0.88  thf(dt_k7_tmap_1, axiom,
% 0.69/0.88    (![A:$i,B:$i]:
% 0.69/0.88     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.69/0.88         ( l1_pre_topc @ A ) & 
% 0.69/0.88         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.69/0.88       ( ( v1_funct_1 @ ( k7_tmap_1 @ A @ B ) ) & 
% 0.69/0.88         ( v1_funct_2 @
% 0.69/0.88           ( k7_tmap_1 @ A @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.69/0.88           ( u1_struct_0 @ ( k6_tmap_1 @ A @ B ) ) ) & 
% 0.69/0.88         ( m1_subset_1 @
% 0.69/0.88           ( k7_tmap_1 @ A @ B ) @ 
% 0.69/0.88           ( k1_zfmisc_1 @
% 0.69/0.88             ( k2_zfmisc_1 @
% 0.69/0.88               ( u1_struct_0 @ A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ A @ B ) ) ) ) ) ) ))).
% 0.69/0.88  thf('6', plain,
% 0.69/0.88      (![X18 : $i, X19 : $i]:
% 0.69/0.88         (~ (l1_pre_topc @ X18)
% 0.69/0.88          | ~ (v2_pre_topc @ X18)
% 0.69/0.88          | (v2_struct_0 @ X18)
% 0.69/0.88          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.69/0.88          | (m1_subset_1 @ (k7_tmap_1 @ X18 @ X19) @ 
% 0.69/0.88             (k1_zfmisc_1 @ 
% 0.69/0.88              (k2_zfmisc_1 @ (u1_struct_0 @ X18) @ 
% 0.69/0.88               (u1_struct_0 @ (k6_tmap_1 @ X18 @ X19))))))),
% 0.69/0.88      inference('cnf', [status(esa)], [dt_k7_tmap_1])).
% 0.69/0.88  thf('7', plain,
% 0.69/0.88      (((m1_subset_1 @ (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)) @ 
% 0.69/0.88         (k1_zfmisc_1 @ 
% 0.69/0.88          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.69/0.88           (u1_struct_0 @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B))))))
% 0.69/0.88        | (v2_struct_0 @ sk_A)
% 0.69/0.88        | ~ (v2_pre_topc @ sk_A)
% 0.69/0.88        | ~ (l1_pre_topc @ sk_A))),
% 0.69/0.88      inference('sup-', [status(thm)], ['5', '6'])).
% 0.69/0.88  thf('8', plain,
% 0.69/0.88      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.69/0.88        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.69/0.88      inference('demod', [status(thm)], ['3', '4'])).
% 0.69/0.88  thf(d10_tmap_1, axiom,
% 0.69/0.88    (![A:$i]:
% 0.69/0.88     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.69/0.88       ( ![B:$i]:
% 0.69/0.88         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.69/0.88           ( ( k7_tmap_1 @ A @ B ) = ( k6_partfun1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.69/0.88  thf('9', plain,
% 0.69/0.88      (![X8 : $i, X9 : $i]:
% 0.69/0.88         (~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.69/0.88          | ((k7_tmap_1 @ X9 @ X8) = (k6_partfun1 @ (u1_struct_0 @ X9)))
% 0.69/0.88          | ~ (l1_pre_topc @ X9)
% 0.69/0.88          | ~ (v2_pre_topc @ X9)
% 0.69/0.88          | (v2_struct_0 @ X9))),
% 0.69/0.89      inference('cnf', [status(esa)], [d10_tmap_1])).
% 0.69/0.89  thf('10', plain,
% 0.69/0.89      (((v2_struct_0 @ sk_A)
% 0.69/0.89        | ~ (v2_pre_topc @ sk_A)
% 0.69/0.89        | ~ (l1_pre_topc @ sk_A)
% 0.69/0.89        | ((k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B))
% 0.69/0.89            = (k6_partfun1 @ (u1_struct_0 @ sk_A))))),
% 0.69/0.89      inference('sup-', [status(thm)], ['8', '9'])).
% 0.69/0.89  thf('11', plain, ((v2_pre_topc @ sk_A)),
% 0.69/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.89  thf('12', plain, ((l1_pre_topc @ sk_A)),
% 0.69/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.89  thf('13', plain,
% 0.69/0.89      (((v2_struct_0 @ sk_A)
% 0.69/0.89        | ((k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B))
% 0.69/0.89            = (k6_partfun1 @ (u1_struct_0 @ sk_A))))),
% 0.69/0.89      inference('demod', [status(thm)], ['10', '11', '12'])).
% 0.69/0.89  thf('14', plain, (~ (v2_struct_0 @ sk_A)),
% 0.69/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.89  thf('15', plain,
% 0.69/0.89      (((k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B))
% 0.69/0.89         = (k6_partfun1 @ (u1_struct_0 @ sk_A)))),
% 0.69/0.89      inference('clc', [status(thm)], ['13', '14'])).
% 0.69/0.89  thf('16', plain, ((v2_pre_topc @ sk_A)),
% 0.69/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.89  thf('17', plain, ((l1_pre_topc @ sk_A)),
% 0.69/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.89  thf('18', plain,
% 0.69/0.89      (((m1_subset_1 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 0.69/0.89         (k1_zfmisc_1 @ 
% 0.69/0.89          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.69/0.89           (u1_struct_0 @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B))))))
% 0.69/0.89        | (v2_struct_0 @ sk_A))),
% 0.69/0.89      inference('demod', [status(thm)], ['7', '15', '16', '17'])).
% 0.69/0.89  thf('19', plain, (~ (v2_struct_0 @ sk_A)),
% 0.69/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.89  thf('20', plain,
% 0.69/0.89      ((m1_subset_1 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 0.69/0.89        (k1_zfmisc_1 @ 
% 0.69/0.89         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.69/0.89          (u1_struct_0 @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B))))))),
% 0.69/0.89      inference('clc', [status(thm)], ['18', '19'])).
% 0.69/0.89  thf('21', plain,
% 0.69/0.89      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.69/0.89        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.69/0.89      inference('demod', [status(thm)], ['3', '4'])).
% 0.69/0.89  thf(d11_tmap_1, axiom,
% 0.69/0.89    (![A:$i]:
% 0.69/0.89     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.69/0.89       ( ![B:$i]:
% 0.69/0.89         ( ( m1_pre_topc @ B @ A ) =>
% 0.69/0.89           ( ![C:$i]:
% 0.69/0.89             ( ( ( v1_pre_topc @ C ) & ( v2_pre_topc @ C ) & 
% 0.69/0.89                 ( l1_pre_topc @ C ) ) =>
% 0.69/0.89               ( ( ( C ) = ( k8_tmap_1 @ A @ B ) ) <=>
% 0.69/0.89                 ( ![D:$i]:
% 0.69/0.89                   ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.69/0.89                     ( ( ( D ) = ( u1_struct_0 @ B ) ) =>
% 0.69/0.89                       ( ( C ) = ( k6_tmap_1 @ A @ D ) ) ) ) ) ) ) ) ) ) ))).
% 0.69/0.89  thf('22', plain,
% 0.69/0.89      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.69/0.89         (~ (m1_pre_topc @ X10 @ X11)
% 0.69/0.89          | ((X12) != (k8_tmap_1 @ X11 @ X10))
% 0.69/0.89          | ((X13) != (u1_struct_0 @ X10))
% 0.69/0.89          | ((X12) = (k6_tmap_1 @ X11 @ X13))
% 0.69/0.89          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.69/0.89          | ~ (l1_pre_topc @ X12)
% 0.69/0.89          | ~ (v2_pre_topc @ X12)
% 0.69/0.89          | ~ (v1_pre_topc @ X12)
% 0.69/0.89          | ~ (l1_pre_topc @ X11)
% 0.69/0.89          | ~ (v2_pre_topc @ X11)
% 0.69/0.89          | (v2_struct_0 @ X11))),
% 0.69/0.89      inference('cnf', [status(esa)], [d11_tmap_1])).
% 0.69/0.89  thf('23', plain,
% 0.69/0.89      (![X10 : $i, X11 : $i]:
% 0.69/0.89         ((v2_struct_0 @ X11)
% 0.69/0.89          | ~ (v2_pre_topc @ X11)
% 0.69/0.89          | ~ (l1_pre_topc @ X11)
% 0.69/0.89          | ~ (v1_pre_topc @ (k8_tmap_1 @ X11 @ X10))
% 0.69/0.89          | ~ (v2_pre_topc @ (k8_tmap_1 @ X11 @ X10))
% 0.69/0.89          | ~ (l1_pre_topc @ (k8_tmap_1 @ X11 @ X10))
% 0.69/0.89          | ~ (m1_subset_1 @ (u1_struct_0 @ X10) @ 
% 0.69/0.89               (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.69/0.89          | ((k8_tmap_1 @ X11 @ X10) = (k6_tmap_1 @ X11 @ (u1_struct_0 @ X10)))
% 0.69/0.89          | ~ (m1_pre_topc @ X10 @ X11))),
% 0.69/0.89      inference('simplify', [status(thm)], ['22'])).
% 0.69/0.89  thf('24', plain,
% 0.69/0.89      ((~ (m1_pre_topc @ sk_B @ sk_A)
% 0.69/0.89        | ((k8_tmap_1 @ sk_A @ sk_B)
% 0.69/0.89            = (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 0.69/0.89        | ~ (l1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.69/0.89        | ~ (v2_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.69/0.89        | ~ (v1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.69/0.89        | ~ (l1_pre_topc @ sk_A)
% 0.69/0.89        | ~ (v2_pre_topc @ sk_A)
% 0.69/0.89        | (v2_struct_0 @ sk_A))),
% 0.69/0.89      inference('sup-', [status(thm)], ['21', '23'])).
% 0.69/0.89  thf('25', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.69/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.89  thf('26', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.69/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.89  thf(dt_k8_tmap_1, axiom,
% 0.69/0.89    (![A:$i,B:$i]:
% 0.69/0.89     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.69/0.89         ( l1_pre_topc @ A ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.69/0.89       ( ( v1_pre_topc @ ( k8_tmap_1 @ A @ B ) ) & 
% 0.69/0.89         ( v2_pre_topc @ ( k8_tmap_1 @ A @ B ) ) & 
% 0.69/0.89         ( l1_pre_topc @ ( k8_tmap_1 @ A @ B ) ) ) ))).
% 0.69/0.89  thf('27', plain,
% 0.69/0.89      (![X20 : $i, X21 : $i]:
% 0.69/0.89         (~ (l1_pre_topc @ X20)
% 0.69/0.89          | ~ (v2_pre_topc @ X20)
% 0.69/0.89          | (v2_struct_0 @ X20)
% 0.69/0.89          | ~ (m1_pre_topc @ X21 @ X20)
% 0.69/0.89          | (l1_pre_topc @ (k8_tmap_1 @ X20 @ X21)))),
% 0.69/0.89      inference('cnf', [status(esa)], [dt_k8_tmap_1])).
% 0.69/0.89  thf('28', plain,
% 0.69/0.89      (((l1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.69/0.89        | (v2_struct_0 @ sk_A)
% 0.69/0.89        | ~ (v2_pre_topc @ sk_A)
% 0.69/0.89        | ~ (l1_pre_topc @ sk_A))),
% 0.69/0.89      inference('sup-', [status(thm)], ['26', '27'])).
% 0.69/0.89  thf('29', plain, ((v2_pre_topc @ sk_A)),
% 0.69/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.89  thf('30', plain, ((l1_pre_topc @ sk_A)),
% 0.69/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.89  thf('31', plain,
% 0.69/0.89      (((l1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B)) | (v2_struct_0 @ sk_A))),
% 0.69/0.89      inference('demod', [status(thm)], ['28', '29', '30'])).
% 0.69/0.89  thf('32', plain, (~ (v2_struct_0 @ sk_A)),
% 0.69/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.89  thf('33', plain, ((l1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))),
% 0.69/0.89      inference('clc', [status(thm)], ['31', '32'])).
% 0.69/0.89  thf('34', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.69/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.89  thf('35', plain,
% 0.69/0.89      (![X20 : $i, X21 : $i]:
% 0.69/0.89         (~ (l1_pre_topc @ X20)
% 0.69/0.89          | ~ (v2_pre_topc @ X20)
% 0.69/0.89          | (v2_struct_0 @ X20)
% 0.69/0.89          | ~ (m1_pre_topc @ X21 @ X20)
% 0.69/0.89          | (v2_pre_topc @ (k8_tmap_1 @ X20 @ X21)))),
% 0.69/0.89      inference('cnf', [status(esa)], [dt_k8_tmap_1])).
% 0.69/0.89  thf('36', plain,
% 0.69/0.89      (((v2_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.69/0.89        | (v2_struct_0 @ sk_A)
% 0.69/0.89        | ~ (v2_pre_topc @ sk_A)
% 0.69/0.89        | ~ (l1_pre_topc @ sk_A))),
% 0.69/0.89      inference('sup-', [status(thm)], ['34', '35'])).
% 0.69/0.89  thf('37', plain, ((v2_pre_topc @ sk_A)),
% 0.69/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.89  thf('38', plain, ((l1_pre_topc @ sk_A)),
% 0.69/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.89  thf('39', plain,
% 0.69/0.89      (((v2_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B)) | (v2_struct_0 @ sk_A))),
% 0.69/0.89      inference('demod', [status(thm)], ['36', '37', '38'])).
% 0.69/0.89  thf('40', plain, (~ (v2_struct_0 @ sk_A)),
% 0.69/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.89  thf('41', plain, ((v2_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))),
% 0.69/0.89      inference('clc', [status(thm)], ['39', '40'])).
% 0.69/0.89  thf('42', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.69/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.89  thf('43', plain,
% 0.69/0.89      (![X20 : $i, X21 : $i]:
% 0.69/0.89         (~ (l1_pre_topc @ X20)
% 0.69/0.89          | ~ (v2_pre_topc @ X20)
% 0.69/0.89          | (v2_struct_0 @ X20)
% 0.69/0.89          | ~ (m1_pre_topc @ X21 @ X20)
% 0.69/0.89          | (v1_pre_topc @ (k8_tmap_1 @ X20 @ X21)))),
% 0.69/0.89      inference('cnf', [status(esa)], [dt_k8_tmap_1])).
% 0.69/0.89  thf('44', plain,
% 0.69/0.89      (((v1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.69/0.89        | (v2_struct_0 @ sk_A)
% 0.69/0.89        | ~ (v2_pre_topc @ sk_A)
% 0.69/0.89        | ~ (l1_pre_topc @ sk_A))),
% 0.69/0.89      inference('sup-', [status(thm)], ['42', '43'])).
% 0.69/0.89  thf('45', plain, ((v2_pre_topc @ sk_A)),
% 0.69/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.89  thf('46', plain, ((l1_pre_topc @ sk_A)),
% 0.69/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.89  thf('47', plain,
% 0.69/0.89      (((v1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B)) | (v2_struct_0 @ sk_A))),
% 0.69/0.89      inference('demod', [status(thm)], ['44', '45', '46'])).
% 0.69/0.89  thf('48', plain, (~ (v2_struct_0 @ sk_A)),
% 0.69/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.89  thf('49', plain, ((v1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))),
% 0.69/0.89      inference('clc', [status(thm)], ['47', '48'])).
% 0.69/0.89  thf('50', plain, ((l1_pre_topc @ sk_A)),
% 0.69/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.89  thf('51', plain, ((v2_pre_topc @ sk_A)),
% 0.69/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.89  thf('52', plain,
% 0.69/0.89      ((((k8_tmap_1 @ sk_A @ sk_B) = (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 0.69/0.89        | (v2_struct_0 @ sk_A))),
% 0.69/0.89      inference('demod', [status(thm)],
% 0.69/0.89                ['24', '25', '33', '41', '49', '50', '51'])).
% 0.69/0.89  thf('53', plain, (~ (v2_struct_0 @ sk_A)),
% 0.69/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.89  thf('54', plain,
% 0.69/0.89      (((k8_tmap_1 @ sk_A @ sk_B) = (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))),
% 0.69/0.89      inference('clc', [status(thm)], ['52', '53'])).
% 0.69/0.89  thf('55', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.69/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.89  thf(t114_tmap_1, axiom,
% 0.69/0.89    (![A:$i]:
% 0.69/0.89     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.69/0.89       ( ![B:$i]:
% 0.69/0.89         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.69/0.89           ( ( ( u1_struct_0 @ ( k8_tmap_1 @ A @ B ) ) = ( u1_struct_0 @ A ) ) & 
% 0.69/0.89             ( ![C:$i]:
% 0.69/0.89               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.69/0.89                 ( ( ( C ) = ( u1_struct_0 @ B ) ) =>
% 0.69/0.89                   ( ( u1_pre_topc @ ( k8_tmap_1 @ A @ B ) ) =
% 0.69/0.89                     ( k5_tmap_1 @ A @ C ) ) ) ) ) ) ) ) ))).
% 0.69/0.89  thf('56', plain,
% 0.69/0.89      (![X26 : $i, X27 : $i]:
% 0.69/0.89         ((v2_struct_0 @ X26)
% 0.69/0.89          | ~ (m1_pre_topc @ X26 @ X27)
% 0.69/0.89          | ((u1_struct_0 @ (k8_tmap_1 @ X27 @ X26)) = (u1_struct_0 @ X27))
% 0.69/0.89          | ~ (l1_pre_topc @ X27)
% 0.69/0.89          | ~ (v2_pre_topc @ X27)
% 0.69/0.89          | (v2_struct_0 @ X27))),
% 0.69/0.89      inference('cnf', [status(esa)], [t114_tmap_1])).
% 0.69/0.89  thf('57', plain,
% 0.69/0.89      (((v2_struct_0 @ sk_A)
% 0.69/0.89        | ~ (v2_pre_topc @ sk_A)
% 0.69/0.89        | ~ (l1_pre_topc @ sk_A)
% 0.69/0.89        | ((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))
% 0.69/0.89        | (v2_struct_0 @ sk_B))),
% 0.69/0.89      inference('sup-', [status(thm)], ['55', '56'])).
% 0.69/0.89  thf('58', plain, ((v2_pre_topc @ sk_A)),
% 0.69/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.89  thf('59', plain, ((l1_pre_topc @ sk_A)),
% 0.69/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.89  thf('60', plain,
% 0.69/0.89      (((v2_struct_0 @ sk_A)
% 0.69/0.89        | ((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))
% 0.69/0.89        | (v2_struct_0 @ sk_B))),
% 0.69/0.89      inference('demod', [status(thm)], ['57', '58', '59'])).
% 0.69/0.89  thf('61', plain, (~ (v2_struct_0 @ sk_A)),
% 0.69/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.89  thf('62', plain,
% 0.69/0.89      (((v2_struct_0 @ sk_B)
% 0.69/0.89        | ((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A)))),
% 0.69/0.89      inference('clc', [status(thm)], ['60', '61'])).
% 0.69/0.89  thf('63', plain, (~ (v2_struct_0 @ sk_B)),
% 0.69/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.89  thf('64', plain,
% 0.69/0.89      (((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 0.69/0.89      inference('clc', [status(thm)], ['62', '63'])).
% 0.69/0.89  thf('65', plain,
% 0.69/0.89      ((m1_subset_1 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 0.69/0.89        (k1_zfmisc_1 @ 
% 0.69/0.89         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))))),
% 0.69/0.89      inference('demod', [status(thm)], ['20', '54', '64'])).
% 0.69/0.89  thf('66', plain,
% 0.69/0.89      ((m1_subset_1 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 0.69/0.89        (k1_zfmisc_1 @ 
% 0.69/0.89         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))))),
% 0.69/0.89      inference('demod', [status(thm)], ['20', '54', '64'])).
% 0.69/0.89  thf(redefinition_r1_funct_2, axiom,
% 0.69/0.89    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.69/0.89     ( ( ( ~( v1_xboole_0 @ B ) ) & ( ~( v1_xboole_0 @ D ) ) & 
% 0.69/0.89         ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ A @ B ) & 
% 0.69/0.89         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.69/0.89         ( v1_funct_1 @ F ) & ( v1_funct_2 @ F @ C @ D ) & 
% 0.69/0.89         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.69/0.89       ( ( r1_funct_2 @ A @ B @ C @ D @ E @ F ) <=> ( ( E ) = ( F ) ) ) ))).
% 0.69/0.89  thf('67', plain,
% 0.69/0.89      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.69/0.89         (~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X4)))
% 0.69/0.89          | ~ (v1_funct_2 @ X2 @ X3 @ X4)
% 0.69/0.89          | ~ (v1_funct_1 @ X2)
% 0.69/0.89          | (v1_xboole_0 @ X5)
% 0.69/0.89          | (v1_xboole_0 @ X4)
% 0.69/0.89          | ~ (v1_funct_1 @ X6)
% 0.69/0.89          | ~ (v1_funct_2 @ X6 @ X7 @ X5)
% 0.69/0.89          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X5)))
% 0.69/0.89          | (r1_funct_2 @ X3 @ X4 @ X7 @ X5 @ X2 @ X6)
% 0.69/0.89          | ((X2) != (X6)))),
% 0.69/0.89      inference('cnf', [status(esa)], [redefinition_r1_funct_2])).
% 0.69/0.89  thf('68', plain,
% 0.69/0.89      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.69/0.89         ((r1_funct_2 @ X3 @ X4 @ X7 @ X5 @ X6 @ X6)
% 0.69/0.89          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X5)))
% 0.69/0.89          | ~ (v1_funct_2 @ X6 @ X7 @ X5)
% 0.69/0.89          | (v1_xboole_0 @ X4)
% 0.69/0.89          | (v1_xboole_0 @ X5)
% 0.69/0.89          | ~ (v1_funct_1 @ X6)
% 0.69/0.89          | ~ (v1_funct_2 @ X6 @ X3 @ X4)
% 0.69/0.89          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X4))))),
% 0.69/0.89      inference('simplify', [status(thm)], ['67'])).
% 0.69/0.89  thf('69', plain,
% 0.69/0.89      (![X0 : $i, X1 : $i]:
% 0.69/0.89         (~ (m1_subset_1 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 0.69/0.89             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ X0)))
% 0.69/0.89          | ~ (v1_funct_2 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ X1 @ X0)
% 0.69/0.89          | ~ (v1_funct_1 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)))
% 0.69/0.89          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.69/0.89          | (v1_xboole_0 @ X0)
% 0.69/0.89          | ~ (v1_funct_2 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 0.69/0.89               (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.69/0.89          | (r1_funct_2 @ X1 @ X0 @ (u1_struct_0 @ sk_A) @ 
% 0.69/0.89             (u1_struct_0 @ sk_A) @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 0.69/0.89             (k6_partfun1 @ (u1_struct_0 @ sk_A))))),
% 0.69/0.89      inference('sup-', [status(thm)], ['66', '68'])).
% 0.69/0.89  thf('70', plain,
% 0.69/0.89      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.69/0.89        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.69/0.89      inference('demod', [status(thm)], ['3', '4'])).
% 0.69/0.89  thf('71', plain,
% 0.69/0.89      (![X18 : $i, X19 : $i]:
% 0.69/0.89         (~ (l1_pre_topc @ X18)
% 0.69/0.89          | ~ (v2_pre_topc @ X18)
% 0.69/0.89          | (v2_struct_0 @ X18)
% 0.69/0.89          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.69/0.89          | (v1_funct_1 @ (k7_tmap_1 @ X18 @ X19)))),
% 0.69/0.89      inference('cnf', [status(esa)], [dt_k7_tmap_1])).
% 0.69/0.89  thf('72', plain,
% 0.69/0.89      (((v1_funct_1 @ (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 0.69/0.89        | (v2_struct_0 @ sk_A)
% 0.69/0.89        | ~ (v2_pre_topc @ sk_A)
% 0.69/0.89        | ~ (l1_pre_topc @ sk_A))),
% 0.69/0.89      inference('sup-', [status(thm)], ['70', '71'])).
% 0.69/0.89  thf('73', plain, ((v2_pre_topc @ sk_A)),
% 0.69/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.89  thf('74', plain, ((l1_pre_topc @ sk_A)),
% 0.69/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.89  thf('75', plain,
% 0.69/0.89      (((v1_funct_1 @ (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 0.69/0.89        | (v2_struct_0 @ sk_A))),
% 0.69/0.89      inference('demod', [status(thm)], ['72', '73', '74'])).
% 0.69/0.89  thf('76', plain, (~ (v2_struct_0 @ sk_A)),
% 0.69/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.89  thf('77', plain, ((v1_funct_1 @ (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))),
% 0.69/0.89      inference('clc', [status(thm)], ['75', '76'])).
% 0.69/0.89  thf('78', plain,
% 0.69/0.89      (((k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B))
% 0.69/0.89         = (k6_partfun1 @ (u1_struct_0 @ sk_A)))),
% 0.69/0.89      inference('clc', [status(thm)], ['13', '14'])).
% 0.69/0.89  thf('79', plain, ((v1_funct_1 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)))),
% 0.69/0.89      inference('demod', [status(thm)], ['77', '78'])).
% 0.69/0.89  thf('80', plain,
% 0.69/0.89      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.69/0.89        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.69/0.89      inference('demod', [status(thm)], ['3', '4'])).
% 0.69/0.89  thf('81', plain,
% 0.69/0.89      (![X18 : $i, X19 : $i]:
% 0.69/0.89         (~ (l1_pre_topc @ X18)
% 0.69/0.89          | ~ (v2_pre_topc @ X18)
% 0.69/0.89          | (v2_struct_0 @ X18)
% 0.69/0.89          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.69/0.89          | (v1_funct_2 @ (k7_tmap_1 @ X18 @ X19) @ (u1_struct_0 @ X18) @ 
% 0.69/0.89             (u1_struct_0 @ (k6_tmap_1 @ X18 @ X19))))),
% 0.69/0.89      inference('cnf', [status(esa)], [dt_k7_tmap_1])).
% 0.69/0.89  thf('82', plain,
% 0.69/0.89      (((v1_funct_2 @ (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)) @ 
% 0.69/0.89         (u1_struct_0 @ sk_A) @ 
% 0.69/0.89         (u1_struct_0 @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B))))
% 0.69/0.89        | (v2_struct_0 @ sk_A)
% 0.69/0.89        | ~ (v2_pre_topc @ sk_A)
% 0.69/0.89        | ~ (l1_pre_topc @ sk_A))),
% 0.69/0.89      inference('sup-', [status(thm)], ['80', '81'])).
% 0.69/0.89  thf('83', plain,
% 0.69/0.89      (((k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B))
% 0.69/0.89         = (k6_partfun1 @ (u1_struct_0 @ sk_A)))),
% 0.69/0.89      inference('clc', [status(thm)], ['13', '14'])).
% 0.69/0.89  thf('84', plain, ((v2_pre_topc @ sk_A)),
% 0.69/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.89  thf('85', plain, ((l1_pre_topc @ sk_A)),
% 0.69/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.89  thf('86', plain,
% 0.69/0.89      (((v1_funct_2 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 0.69/0.89         (u1_struct_0 @ sk_A) @ 
% 0.69/0.89         (u1_struct_0 @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B))))
% 0.69/0.89        | (v2_struct_0 @ sk_A))),
% 0.69/0.89      inference('demod', [status(thm)], ['82', '83', '84', '85'])).
% 0.69/0.89  thf('87', plain, (~ (v2_struct_0 @ sk_A)),
% 0.69/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.89  thf('88', plain,
% 0.69/0.89      ((v1_funct_2 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 0.69/0.89        (u1_struct_0 @ sk_A) @ 
% 0.69/0.89        (u1_struct_0 @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B))))),
% 0.69/0.89      inference('clc', [status(thm)], ['86', '87'])).
% 0.69/0.89  thf('89', plain,
% 0.69/0.89      (((k8_tmap_1 @ sk_A @ sk_B) = (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))),
% 0.69/0.89      inference('clc', [status(thm)], ['52', '53'])).
% 0.69/0.89  thf('90', plain,
% 0.69/0.89      (((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 0.69/0.89      inference('clc', [status(thm)], ['62', '63'])).
% 0.69/0.89  thf('91', plain,
% 0.69/0.89      ((v1_funct_2 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 0.69/0.89        (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))),
% 0.69/0.89      inference('demod', [status(thm)], ['88', '89', '90'])).
% 0.69/0.89  thf('92', plain,
% 0.69/0.89      (![X0 : $i, X1 : $i]:
% 0.69/0.89         (~ (m1_subset_1 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 0.69/0.89             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ X0)))
% 0.69/0.89          | ~ (v1_funct_2 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ X1 @ X0)
% 0.69/0.89          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.69/0.89          | (v1_xboole_0 @ X0)
% 0.69/0.89          | (r1_funct_2 @ X1 @ X0 @ (u1_struct_0 @ sk_A) @ 
% 0.69/0.89             (u1_struct_0 @ sk_A) @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 0.69/0.89             (k6_partfun1 @ (u1_struct_0 @ sk_A))))),
% 0.69/0.89      inference('demod', [status(thm)], ['69', '79', '91'])).
% 0.69/0.89  thf('93', plain,
% 0.69/0.89      (((r1_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.69/0.89         (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.69/0.89         (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 0.69/0.89         (k6_partfun1 @ (u1_struct_0 @ sk_A)))
% 0.69/0.89        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.69/0.89        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.69/0.89        | ~ (v1_funct_2 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 0.69/0.89             (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 0.69/0.89      inference('sup-', [status(thm)], ['65', '92'])).
% 0.69/0.89  thf('94', plain,
% 0.69/0.89      ((v1_funct_2 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 0.69/0.89        (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))),
% 0.69/0.89      inference('demod', [status(thm)], ['88', '89', '90'])).
% 0.69/0.89  thf('95', plain,
% 0.69/0.89      (((r1_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.69/0.89         (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.69/0.89         (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 0.69/0.89         (k6_partfun1 @ (u1_struct_0 @ sk_A)))
% 0.69/0.89        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.69/0.89        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.69/0.89      inference('demod', [status(thm)], ['93', '94'])).
% 0.69/0.89  thf('96', plain,
% 0.69/0.89      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.69/0.89        | (r1_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.69/0.89           (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.69/0.89           (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 0.69/0.89           (k6_partfun1 @ (u1_struct_0 @ sk_A))))),
% 0.69/0.89      inference('simplify', [status(thm)], ['95'])).
% 0.69/0.89  thf('97', plain,
% 0.69/0.89      ((m1_subset_1 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 0.69/0.89        (k1_zfmisc_1 @ 
% 0.69/0.89         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))))),
% 0.69/0.89      inference('demod', [status(thm)], ['20', '54', '64'])).
% 0.69/0.89  thf('98', plain,
% 0.69/0.89      (((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 0.69/0.89      inference('clc', [status(thm)], ['62', '63'])).
% 0.69/0.89  thf(d12_tmap_1, axiom,
% 0.69/0.89    (![A:$i]:
% 0.69/0.89     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.69/0.89       ( ![B:$i]:
% 0.69/0.89         ( ( m1_pre_topc @ B @ A ) =>
% 0.69/0.89           ( ![C:$i]:
% 0.69/0.89             ( ( ( v1_funct_1 @ C ) & 
% 0.69/0.89                 ( v1_funct_2 @
% 0.69/0.89                   C @ ( u1_struct_0 @ A ) @ 
% 0.69/0.89                   ( u1_struct_0 @ ( k8_tmap_1 @ A @ B ) ) ) & 
% 0.69/0.89                 ( m1_subset_1 @
% 0.69/0.89                   C @ 
% 0.69/0.89                   ( k1_zfmisc_1 @
% 0.69/0.89                     ( k2_zfmisc_1 @
% 0.69/0.89                       ( u1_struct_0 @ A ) @ 
% 0.69/0.89                       ( u1_struct_0 @ ( k8_tmap_1 @ A @ B ) ) ) ) ) ) =>
% 0.69/0.89               ( ( ( C ) = ( k9_tmap_1 @ A @ B ) ) <=>
% 0.69/0.89                 ( ![D:$i]:
% 0.69/0.89                   ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.69/0.89                     ( ( ( D ) = ( u1_struct_0 @ B ) ) =>
% 0.69/0.89                       ( r1_funct_2 @
% 0.69/0.89                         ( u1_struct_0 @ A ) @ 
% 0.69/0.89                         ( u1_struct_0 @ ( k8_tmap_1 @ A @ B ) ) @ 
% 0.69/0.89                         ( u1_struct_0 @ A ) @ 
% 0.69/0.89                         ( u1_struct_0 @ ( k6_tmap_1 @ A @ D ) ) @ C @ 
% 0.69/0.89                         ( k7_tmap_1 @ A @ D ) ) ) ) ) ) ) ) ) ) ))).
% 0.69/0.89  thf('99', plain,
% 0.69/0.89      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.69/0.89         (~ (m1_pre_topc @ X14 @ X15)
% 0.69/0.89          | ((sk_D_1 @ X16 @ X14 @ X15) = (u1_struct_0 @ X14))
% 0.69/0.89          | ((X16) = (k9_tmap_1 @ X15 @ X14))
% 0.69/0.89          | ~ (m1_subset_1 @ X16 @ 
% 0.69/0.89               (k1_zfmisc_1 @ 
% 0.69/0.89                (k2_zfmisc_1 @ (u1_struct_0 @ X15) @ 
% 0.69/0.89                 (u1_struct_0 @ (k8_tmap_1 @ X15 @ X14)))))
% 0.69/0.89          | ~ (v1_funct_2 @ X16 @ (u1_struct_0 @ X15) @ 
% 0.69/0.89               (u1_struct_0 @ (k8_tmap_1 @ X15 @ X14)))
% 0.69/0.89          | ~ (v1_funct_1 @ X16)
% 0.69/0.89          | ~ (l1_pre_topc @ X15)
% 0.69/0.89          | ~ (v2_pre_topc @ X15)
% 0.69/0.89          | (v2_struct_0 @ X15))),
% 0.69/0.89      inference('cnf', [status(esa)], [d12_tmap_1])).
% 0.69/0.89  thf('100', plain,
% 0.69/0.89      (![X0 : $i]:
% 0.69/0.89         (~ (m1_subset_1 @ X0 @ 
% 0.69/0.89             (k1_zfmisc_1 @ 
% 0.69/0.89              (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))))
% 0.69/0.89          | (v2_struct_0 @ sk_A)
% 0.69/0.89          | ~ (v2_pre_topc @ sk_A)
% 0.69/0.89          | ~ (l1_pre_topc @ sk_A)
% 0.69/0.89          | ~ (v1_funct_1 @ X0)
% 0.69/0.89          | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_A) @ 
% 0.69/0.89               (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))
% 0.69/0.89          | ((X0) = (k9_tmap_1 @ sk_A @ sk_B))
% 0.69/0.89          | ((sk_D_1 @ X0 @ sk_B @ sk_A) = (u1_struct_0 @ sk_B))
% 0.69/0.89          | ~ (m1_pre_topc @ sk_B @ sk_A))),
% 0.69/0.89      inference('sup-', [status(thm)], ['98', '99'])).
% 0.69/0.89  thf('101', plain, ((v2_pre_topc @ sk_A)),
% 0.69/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.89  thf('102', plain, ((l1_pre_topc @ sk_A)),
% 0.69/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.89  thf('103', plain,
% 0.69/0.89      (((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 0.69/0.89      inference('clc', [status(thm)], ['62', '63'])).
% 0.69/0.89  thf('104', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.69/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.89  thf('105', plain,
% 0.69/0.89      (![X0 : $i]:
% 0.69/0.89         (~ (m1_subset_1 @ X0 @ 
% 0.69/0.89             (k1_zfmisc_1 @ 
% 0.69/0.89              (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))))
% 0.69/0.89          | (v2_struct_0 @ sk_A)
% 0.69/0.89          | ~ (v1_funct_1 @ X0)
% 0.69/0.89          | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.69/0.89          | ((X0) = (k9_tmap_1 @ sk_A @ sk_B))
% 0.69/0.89          | ((sk_D_1 @ X0 @ sk_B @ sk_A) = (u1_struct_0 @ sk_B)))),
% 0.69/0.89      inference('demod', [status(thm)], ['100', '101', '102', '103', '104'])).
% 0.69/0.89  thf('106', plain,
% 0.69/0.89      ((((sk_D_1 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ sk_B @ sk_A)
% 0.69/0.89          = (u1_struct_0 @ sk_B))
% 0.69/0.89        | ((k6_partfun1 @ (u1_struct_0 @ sk_A)) = (k9_tmap_1 @ sk_A @ sk_B))
% 0.69/0.89        | ~ (v1_funct_2 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 0.69/0.89             (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.69/0.89        | ~ (v1_funct_1 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)))
% 0.69/0.89        | (v2_struct_0 @ sk_A))),
% 0.69/0.89      inference('sup-', [status(thm)], ['97', '105'])).
% 0.69/0.89  thf('107', plain,
% 0.69/0.89      ((v1_funct_2 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 0.69/0.89        (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))),
% 0.69/0.89      inference('demod', [status(thm)], ['88', '89', '90'])).
% 0.69/0.89  thf('108', plain, ((v1_funct_1 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)))),
% 0.69/0.89      inference('demod', [status(thm)], ['77', '78'])).
% 0.69/0.89  thf('109', plain,
% 0.69/0.89      ((((sk_D_1 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ sk_B @ sk_A)
% 0.69/0.89          = (u1_struct_0 @ sk_B))
% 0.69/0.89        | ((k6_partfun1 @ (u1_struct_0 @ sk_A)) = (k9_tmap_1 @ sk_A @ sk_B))
% 0.69/0.89        | (v2_struct_0 @ sk_A))),
% 0.69/0.89      inference('demod', [status(thm)], ['106', '107', '108'])).
% 0.69/0.89  thf('110', plain, (~ (v2_struct_0 @ sk_A)),
% 0.69/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.89  thf('111', plain,
% 0.69/0.89      ((((k6_partfun1 @ (u1_struct_0 @ sk_A)) = (k9_tmap_1 @ sk_A @ sk_B))
% 0.69/0.89        | ((sk_D_1 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ sk_B @ sk_A)
% 0.69/0.89            = (u1_struct_0 @ sk_B)))),
% 0.69/0.89      inference('clc', [status(thm)], ['109', '110'])).
% 0.69/0.89  thf('112', plain,
% 0.69/0.89      ((((k6_partfun1 @ (u1_struct_0 @ sk_A)) = (k9_tmap_1 @ sk_A @ sk_B))
% 0.69/0.89        | ((sk_D_1 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ sk_B @ sk_A)
% 0.69/0.89            = (u1_struct_0 @ sk_B)))),
% 0.69/0.89      inference('clc', [status(thm)], ['109', '110'])).
% 0.69/0.89  thf('113', plain,
% 0.69/0.89      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.69/0.89         (~ (m1_pre_topc @ X14 @ X15)
% 0.69/0.89          | ~ (r1_funct_2 @ (u1_struct_0 @ X15) @ 
% 0.69/0.89               (u1_struct_0 @ (k8_tmap_1 @ X15 @ X14)) @ (u1_struct_0 @ X15) @ 
% 0.69/0.89               (u1_struct_0 @ (k6_tmap_1 @ X15 @ (sk_D_1 @ X16 @ X14 @ X15))) @ 
% 0.69/0.89               X16 @ (k7_tmap_1 @ X15 @ (sk_D_1 @ X16 @ X14 @ X15)))
% 0.69/0.89          | ((X16) = (k9_tmap_1 @ X15 @ X14))
% 0.69/0.89          | ~ (m1_subset_1 @ X16 @ 
% 0.69/0.89               (k1_zfmisc_1 @ 
% 0.69/0.89                (k2_zfmisc_1 @ (u1_struct_0 @ X15) @ 
% 0.69/0.89                 (u1_struct_0 @ (k8_tmap_1 @ X15 @ X14)))))
% 0.69/0.89          | ~ (v1_funct_2 @ X16 @ (u1_struct_0 @ X15) @ 
% 0.69/0.89               (u1_struct_0 @ (k8_tmap_1 @ X15 @ X14)))
% 0.69/0.89          | ~ (v1_funct_1 @ X16)
% 0.69/0.89          | ~ (l1_pre_topc @ X15)
% 0.69/0.89          | ~ (v2_pre_topc @ X15)
% 0.69/0.89          | (v2_struct_0 @ X15))),
% 0.69/0.89      inference('cnf', [status(esa)], [d12_tmap_1])).
% 0.69/0.89  thf('114', plain,
% 0.69/0.89      ((~ (r1_funct_2 @ (u1_struct_0 @ sk_A) @ 
% 0.69/0.89           (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)) @ (u1_struct_0 @ sk_A) @ 
% 0.69/0.89           (u1_struct_0 @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B))) @ 
% 0.69/0.89           (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 0.69/0.89           (k7_tmap_1 @ sk_A @ 
% 0.69/0.89            (sk_D_1 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ sk_B @ sk_A)))
% 0.69/0.89        | ((k6_partfun1 @ (u1_struct_0 @ sk_A)) = (k9_tmap_1 @ sk_A @ sk_B))
% 0.69/0.89        | (v2_struct_0 @ sk_A)
% 0.69/0.89        | ~ (v2_pre_topc @ sk_A)
% 0.69/0.89        | ~ (l1_pre_topc @ sk_A)
% 0.69/0.89        | ~ (v1_funct_1 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)))
% 0.69/0.89        | ~ (v1_funct_2 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 0.69/0.89             (u1_struct_0 @ sk_A) @ (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))
% 0.69/0.89        | ~ (m1_subset_1 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 0.69/0.89             (k1_zfmisc_1 @ 
% 0.69/0.89              (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.69/0.89               (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))))
% 0.69/0.89        | ((k6_partfun1 @ (u1_struct_0 @ sk_A)) = (k9_tmap_1 @ sk_A @ sk_B))
% 0.69/0.89        | ~ (m1_pre_topc @ sk_B @ sk_A))),
% 0.69/0.89      inference('sup-', [status(thm)], ['112', '113'])).
% 0.69/0.89  thf('115', plain,
% 0.69/0.89      (((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 0.69/0.89      inference('clc', [status(thm)], ['62', '63'])).
% 0.69/0.89  thf('116', plain,
% 0.69/0.89      (((k8_tmap_1 @ sk_A @ sk_B) = (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))),
% 0.69/0.89      inference('clc', [status(thm)], ['52', '53'])).
% 0.69/0.89  thf('117', plain,
% 0.69/0.89      (((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 0.69/0.89      inference('clc', [status(thm)], ['62', '63'])).
% 0.69/0.89  thf('118', plain, ((v2_pre_topc @ sk_A)),
% 0.69/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.89  thf('119', plain, ((l1_pre_topc @ sk_A)),
% 0.69/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.89  thf('120', plain, ((v1_funct_1 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)))),
% 0.69/0.89      inference('demod', [status(thm)], ['77', '78'])).
% 0.69/0.89  thf('121', plain,
% 0.69/0.89      (((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 0.69/0.89      inference('clc', [status(thm)], ['62', '63'])).
% 0.69/0.89  thf('122', plain,
% 0.69/0.89      ((v1_funct_2 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 0.69/0.89        (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))),
% 0.69/0.89      inference('demod', [status(thm)], ['88', '89', '90'])).
% 0.69/0.89  thf('123', plain,
% 0.69/0.89      (((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 0.69/0.89      inference('clc', [status(thm)], ['62', '63'])).
% 0.69/0.89  thf('124', plain,
% 0.69/0.89      ((m1_subset_1 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 0.69/0.89        (k1_zfmisc_1 @ 
% 0.69/0.89         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))))),
% 0.69/0.89      inference('demod', [status(thm)], ['20', '54', '64'])).
% 0.69/0.89  thf('125', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.69/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.89  thf('126', plain,
% 0.69/0.89      ((~ (r1_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.69/0.89           (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.69/0.89           (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 0.69/0.89           (k7_tmap_1 @ sk_A @ 
% 0.69/0.89            (sk_D_1 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ sk_B @ sk_A)))
% 0.69/0.89        | ((k6_partfun1 @ (u1_struct_0 @ sk_A)) = (k9_tmap_1 @ sk_A @ sk_B))
% 0.69/0.89        | (v2_struct_0 @ sk_A)
% 0.69/0.89        | ((k6_partfun1 @ (u1_struct_0 @ sk_A)) = (k9_tmap_1 @ sk_A @ sk_B)))),
% 0.69/0.89      inference('demod', [status(thm)],
% 0.69/0.89                ['114', '115', '116', '117', '118', '119', '120', '121', 
% 0.69/0.89                 '122', '123', '124', '125'])).
% 0.69/0.89  thf('127', plain,
% 0.69/0.89      (((v2_struct_0 @ sk_A)
% 0.69/0.89        | ((k6_partfun1 @ (u1_struct_0 @ sk_A)) = (k9_tmap_1 @ sk_A @ sk_B))
% 0.69/0.89        | ~ (r1_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.69/0.89             (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.69/0.89             (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 0.69/0.89             (k7_tmap_1 @ sk_A @ 
% 0.69/0.89              (sk_D_1 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ sk_B @ sk_A))))),
% 0.69/0.89      inference('simplify', [status(thm)], ['126'])).
% 0.69/0.89  thf('128', plain, (~ (v2_struct_0 @ sk_A)),
% 0.69/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.89  thf('129', plain,
% 0.69/0.89      ((~ (r1_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.69/0.89           (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.69/0.89           (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 0.69/0.89           (k7_tmap_1 @ sk_A @ 
% 0.69/0.89            (sk_D_1 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ sk_B @ sk_A)))
% 0.69/0.89        | ((k6_partfun1 @ (u1_struct_0 @ sk_A)) = (k9_tmap_1 @ sk_A @ sk_B)))),
% 0.69/0.89      inference('clc', [status(thm)], ['127', '128'])).
% 0.69/0.89  thf('130', plain,
% 0.69/0.89      ((~ (r1_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.69/0.89           (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.69/0.89           (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 0.69/0.89           (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 0.69/0.89        | ((k6_partfun1 @ (u1_struct_0 @ sk_A)) = (k9_tmap_1 @ sk_A @ sk_B))
% 0.69/0.89        | ((k6_partfun1 @ (u1_struct_0 @ sk_A)) = (k9_tmap_1 @ sk_A @ sk_B)))),
% 0.69/0.89      inference('sup-', [status(thm)], ['111', '129'])).
% 0.69/0.89  thf('131', plain,
% 0.69/0.89      (((k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B))
% 0.69/0.89         = (k6_partfun1 @ (u1_struct_0 @ sk_A)))),
% 0.69/0.89      inference('clc', [status(thm)], ['13', '14'])).
% 0.69/0.89  thf('132', plain,
% 0.69/0.89      ((~ (r1_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.69/0.89           (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.69/0.89           (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 0.69/0.89           (k6_partfun1 @ (u1_struct_0 @ sk_A)))
% 0.69/0.89        | ((k6_partfun1 @ (u1_struct_0 @ sk_A)) = (k9_tmap_1 @ sk_A @ sk_B))
% 0.69/0.89        | ((k6_partfun1 @ (u1_struct_0 @ sk_A)) = (k9_tmap_1 @ sk_A @ sk_B)))),
% 0.69/0.89      inference('demod', [status(thm)], ['130', '131'])).
% 0.69/0.89  thf('133', plain,
% 0.69/0.89      ((((k6_partfun1 @ (u1_struct_0 @ sk_A)) = (k9_tmap_1 @ sk_A @ sk_B))
% 0.69/0.89        | ~ (r1_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.69/0.89             (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.69/0.89             (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 0.69/0.89             (k6_partfun1 @ (u1_struct_0 @ sk_A))))),
% 0.69/0.89      inference('simplify', [status(thm)], ['132'])).
% 0.69/0.89  thf('134', plain,
% 0.69/0.89      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.69/0.89        | ((k6_partfun1 @ (u1_struct_0 @ sk_A)) = (k9_tmap_1 @ sk_A @ sk_B)))),
% 0.69/0.89      inference('sup-', [status(thm)], ['96', '133'])).
% 0.69/0.89  thf(fc2_struct_0, axiom,
% 0.69/0.89    (![A:$i]:
% 0.69/0.89     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.69/0.89       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.69/0.89  thf('135', plain,
% 0.69/0.89      (![X1 : $i]:
% 0.69/0.89         (~ (v1_xboole_0 @ (u1_struct_0 @ X1))
% 0.69/0.89          | ~ (l1_struct_0 @ X1)
% 0.69/0.89          | (v2_struct_0 @ X1))),
% 0.69/0.89      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.69/0.89  thf('136', plain,
% 0.69/0.89      ((((k6_partfun1 @ (u1_struct_0 @ sk_A)) = (k9_tmap_1 @ sk_A @ sk_B))
% 0.69/0.89        | (v2_struct_0 @ sk_A)
% 0.69/0.89        | ~ (l1_struct_0 @ sk_A))),
% 0.69/0.89      inference('sup-', [status(thm)], ['134', '135'])).
% 0.69/0.89  thf('137', plain, ((l1_pre_topc @ sk_A)),
% 0.69/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.89  thf(dt_l1_pre_topc, axiom,
% 0.69/0.89    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.69/0.89  thf('138', plain, (![X0 : $i]: ((l1_struct_0 @ X0) | ~ (l1_pre_topc @ X0))),
% 0.69/0.89      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.69/0.89  thf('139', plain, ((l1_struct_0 @ sk_A)),
% 0.69/0.89      inference('sup-', [status(thm)], ['137', '138'])).
% 0.69/0.89  thf('140', plain,
% 0.69/0.89      ((((k6_partfun1 @ (u1_struct_0 @ sk_A)) = (k9_tmap_1 @ sk_A @ sk_B))
% 0.69/0.89        | (v2_struct_0 @ sk_A))),
% 0.69/0.89      inference('demod', [status(thm)], ['136', '139'])).
% 0.69/0.89  thf('141', plain, (~ (v2_struct_0 @ sk_A)),
% 0.69/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.89  thf('142', plain,
% 0.69/0.89      (((k6_partfun1 @ (u1_struct_0 @ sk_A)) = (k9_tmap_1 @ sk_A @ sk_B))),
% 0.69/0.89      inference('clc', [status(thm)], ['140', '141'])).
% 0.69/0.89  thf('143', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_B))),
% 0.69/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.89  thf('144', plain,
% 0.69/0.89      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.69/0.89        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.69/0.89      inference('demod', [status(thm)], ['3', '4'])).
% 0.69/0.89  thf(t110_tmap_1, axiom,
% 0.69/0.89    (![A:$i]:
% 0.69/0.89     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.69/0.89       ( ![B:$i]:
% 0.69/0.89         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.69/0.89           ( ![C:$i]:
% 0.69/0.89             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.69/0.89               ( ( ( u1_struct_0 @ C ) = ( B ) ) =>
% 0.69/0.89                 ( ![D:$i]:
% 0.69/0.89                   ( ( m1_subset_1 @ D @ ( u1_struct_0 @ C ) ) =>
% 0.69/0.89                     ( r1_tmap_1 @
% 0.69/0.89                       C @ ( k6_tmap_1 @ A @ B ) @ 
% 0.69/0.89                       ( k2_tmap_1 @
% 0.69/0.89                         A @ ( k6_tmap_1 @ A @ B ) @ ( k7_tmap_1 @ A @ B ) @ C ) @ 
% 0.69/0.89                       D ) ) ) ) ) ) ) ) ))).
% 0.69/0.89  thf('145', plain,
% 0.69/0.89      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 0.69/0.89         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 0.69/0.89          | ((u1_struct_0 @ X24) != (X22))
% 0.69/0.89          | ~ (m1_subset_1 @ X25 @ (u1_struct_0 @ X24))
% 0.69/0.89          | (r1_tmap_1 @ X24 @ (k6_tmap_1 @ X23 @ X22) @ 
% 0.69/0.89             (k2_tmap_1 @ X23 @ (k6_tmap_1 @ X23 @ X22) @ 
% 0.69/0.89              (k7_tmap_1 @ X23 @ X22) @ X24) @ 
% 0.69/0.89             X25)
% 0.69/0.89          | ~ (m1_pre_topc @ X24 @ X23)
% 0.69/0.89          | (v2_struct_0 @ X24)
% 0.69/0.89          | ~ (l1_pre_topc @ X23)
% 0.69/0.89          | ~ (v2_pre_topc @ X23)
% 0.69/0.89          | (v2_struct_0 @ X23))),
% 0.69/0.89      inference('cnf', [status(esa)], [t110_tmap_1])).
% 0.69/0.89  thf('146', plain,
% 0.69/0.89      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.69/0.89         ((v2_struct_0 @ X23)
% 0.69/0.89          | ~ (v2_pre_topc @ X23)
% 0.69/0.89          | ~ (l1_pre_topc @ X23)
% 0.69/0.89          | (v2_struct_0 @ X24)
% 0.69/0.89          | ~ (m1_pre_topc @ X24 @ X23)
% 0.69/0.89          | (r1_tmap_1 @ X24 @ (k6_tmap_1 @ X23 @ (u1_struct_0 @ X24)) @ 
% 0.69/0.89             (k2_tmap_1 @ X23 @ (k6_tmap_1 @ X23 @ (u1_struct_0 @ X24)) @ 
% 0.69/0.89              (k7_tmap_1 @ X23 @ (u1_struct_0 @ X24)) @ X24) @ 
% 0.69/0.89             X25)
% 0.69/0.89          | ~ (m1_subset_1 @ X25 @ (u1_struct_0 @ X24))
% 0.69/0.89          | ~ (m1_subset_1 @ (u1_struct_0 @ X24) @ 
% 0.69/0.89               (k1_zfmisc_1 @ (u1_struct_0 @ X23))))),
% 0.69/0.89      inference('simplify', [status(thm)], ['145'])).
% 0.69/0.89  thf('147', plain,
% 0.69/0.89      (![X0 : $i]:
% 0.69/0.89         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B))
% 0.69/0.89          | (r1_tmap_1 @ sk_B @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)) @ 
% 0.69/0.89             (k2_tmap_1 @ sk_A @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)) @ 
% 0.69/0.89              (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)) @ sk_B) @ 
% 0.69/0.89             X0)
% 0.69/0.89          | ~ (m1_pre_topc @ sk_B @ sk_A)
% 0.69/0.89          | (v2_struct_0 @ sk_B)
% 0.69/0.89          | ~ (l1_pre_topc @ sk_A)
% 0.69/0.89          | ~ (v2_pre_topc @ sk_A)
% 0.69/0.89          | (v2_struct_0 @ sk_A))),
% 0.69/0.89      inference('sup-', [status(thm)], ['144', '146'])).
% 0.69/0.89  thf('148', plain,
% 0.69/0.89      (((k8_tmap_1 @ sk_A @ sk_B) = (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))),
% 0.69/0.89      inference('clc', [status(thm)], ['52', '53'])).
% 0.69/0.89  thf('149', plain,
% 0.69/0.89      (((k8_tmap_1 @ sk_A @ sk_B) = (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))),
% 0.69/0.89      inference('clc', [status(thm)], ['52', '53'])).
% 0.69/0.89  thf('150', plain,
% 0.69/0.89      (((k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B))
% 0.69/0.89         = (k6_partfun1 @ (u1_struct_0 @ sk_A)))),
% 0.69/0.89      inference('clc', [status(thm)], ['13', '14'])).
% 0.69/0.89  thf('151', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.69/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.89  thf('152', plain, ((l1_pre_topc @ sk_A)),
% 0.69/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.89  thf('153', plain, ((v2_pre_topc @ sk_A)),
% 0.69/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.89  thf('154', plain,
% 0.69/0.89      (![X0 : $i]:
% 0.69/0.89         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B))
% 0.69/0.89          | (r1_tmap_1 @ sk_B @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.69/0.89             (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.69/0.89              (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ sk_B) @ 
% 0.69/0.89             X0)
% 0.69/0.89          | (v2_struct_0 @ sk_B)
% 0.69/0.89          | (v2_struct_0 @ sk_A))),
% 0.69/0.89      inference('demod', [status(thm)],
% 0.69/0.89                ['147', '148', '149', '150', '151', '152', '153'])).
% 0.69/0.89  thf('155', plain,
% 0.69/0.89      (((v2_struct_0 @ sk_A)
% 0.69/0.89        | (v2_struct_0 @ sk_B)
% 0.69/0.89        | (r1_tmap_1 @ sk_B @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.69/0.89           (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.69/0.89            (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ sk_B) @ 
% 0.69/0.89           sk_C))),
% 0.69/0.89      inference('sup-', [status(thm)], ['143', '154'])).
% 0.69/0.89  thf('156', plain, (~ (v2_struct_0 @ sk_A)),
% 0.69/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.89  thf('157', plain,
% 0.69/0.89      (((r1_tmap_1 @ sk_B @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.69/0.89         (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.69/0.89          (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ sk_B) @ 
% 0.69/0.89         sk_C)
% 0.69/0.89        | (v2_struct_0 @ sk_B))),
% 0.69/0.89      inference('clc', [status(thm)], ['155', '156'])).
% 0.69/0.89  thf('158', plain, (~ (v2_struct_0 @ sk_B)),
% 0.69/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.89  thf('159', plain,
% 0.69/0.89      ((r1_tmap_1 @ sk_B @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.69/0.89        (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.69/0.89         (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ sk_B) @ 
% 0.69/0.89        sk_C)),
% 0.69/0.89      inference('clc', [status(thm)], ['157', '158'])).
% 0.69/0.89  thf('160', plain, ($false),
% 0.69/0.89      inference('demod', [status(thm)], ['0', '142', '159'])).
% 0.69/0.89  
% 0.69/0.89  % SZS output end Refutation
% 0.69/0.89  
% 0.73/0.89  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
