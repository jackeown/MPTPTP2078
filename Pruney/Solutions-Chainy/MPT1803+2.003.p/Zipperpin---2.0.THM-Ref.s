%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.XXVrdjHYLB

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:10:59 EST 2020

% Result     : Theorem 48.20s
% Output     : Refutation 48.20s
% Verified   : 
% Statistics : Number of formulae       :  223 (5187 expanded)
%              Number of leaves         :   41 (1517 expanded)
%              Depth                    :   30
%              Number of atoms          : 2330 (94098 expanded)
%              Number of equality atoms :   76 ( 746 expanded)
%              Maximal formula depth    :   20 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k9_tmap_1_type,type,(
    k9_tmap_1: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(r1_tmap_1_type,type,(
    r1_tmap_1: $i > $i > $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(k6_tmap_1_type,type,(
    k6_tmap_1: $i > $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r1_funct_2_type,type,(
    r1_funct_2: $i > $i > $i > $i > $i > $i > $o )).

thf(k8_tmap_1_type,type,(
    k8_tmap_1: $i > $i > $i )).

thf(k2_tmap_1_type,type,(
    k2_tmap_1: $i > $i > $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k7_tmap_1_type,type,(
    k7_tmap_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k5_tmap_1_type,type,(
    k5_tmap_1: $i > $i > $i )).

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
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_pre_topc @ sk_B_1 @ sk_A ),
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
    | ( m1_subset_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf(t104_tmap_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( ( u1_struct_0 @ ( k6_tmap_1 @ A @ B ) )
              = ( u1_struct_0 @ A ) )
            & ( ( u1_pre_topc @ ( k6_tmap_1 @ A @ B ) )
              = ( k5_tmap_1 @ A @ B ) ) ) ) ) )).

thf('6',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ( ( u1_struct_0 @ ( k6_tmap_1 @ X24 @ X23 ) )
        = ( u1_struct_0 @ X24 ) )
      | ~ ( l1_pre_topc @ X24 )
      | ~ ( v2_pre_topc @ X24 )
      | ( v2_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t104_tmap_1])).

thf('7',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B_1 ) ) )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B_1 ) ) )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['7','8','9'])).

thf('11',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B_1 ) ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['10','11'])).

thf(existence_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ? [B: $i] :
          ( m1_pre_topc @ B @ A ) ) )).

thf('13',plain,(
    ! [X1: $i] :
      ( ( m1_pre_topc @ ( sk_B @ X1 ) @ X1 )
      | ~ ( l1_pre_topc @ X1 ) ) ),
    inference(cnf,[status(esa)],[existence_m1_pre_topc])).

thf('14',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( m1_pre_topc @ X29 @ X30 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X29 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X30 ) ) )
      | ~ ( l1_pre_topc @ X30 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_subset_1 @ ( u1_struct_0 @ ( sk_B @ X0 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( u1_struct_0 @ ( sk_B @ X0 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,
    ( ( m1_subset_1 @ ( u1_struct_0 @ ( sk_B @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B_1 ) ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference('sup+',[status(thm)],['12','16'])).

thf('18',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
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

thf('19',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_pre_topc @ X11 @ X12 )
      | ( X13
       != ( k8_tmap_1 @ X12 @ X11 ) )
      | ( X14
       != ( u1_struct_0 @ X11 ) )
      | ( X13
        = ( k6_tmap_1 @ X12 @ X14 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ~ ( l1_pre_topc @ X13 )
      | ~ ( v2_pre_topc @ X13 )
      | ~ ( v1_pre_topc @ X13 )
      | ~ ( l1_pre_topc @ X12 )
      | ~ ( v2_pre_topc @ X12 )
      | ( v2_struct_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d11_tmap_1])).

thf('20',plain,(
    ! [X11: $i,X12: $i] :
      ( ( v2_struct_0 @ X12 )
      | ~ ( v2_pre_topc @ X12 )
      | ~ ( l1_pre_topc @ X12 )
      | ~ ( v1_pre_topc @ ( k8_tmap_1 @ X12 @ X11 ) )
      | ~ ( v2_pre_topc @ ( k8_tmap_1 @ X12 @ X11 ) )
      | ~ ( l1_pre_topc @ ( k8_tmap_1 @ X12 @ X11 ) )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X11 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ( ( k8_tmap_1 @ X12 @ X11 )
        = ( k6_tmap_1 @ X12 @ ( u1_struct_0 @ X11 ) ) )
      | ~ ( m1_pre_topc @ X11 @ X12 ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,
    ( ~ ( m1_pre_topc @ sk_B_1 @ sk_A )
    | ( ( k8_tmap_1 @ sk_A @ sk_B_1 )
      = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B_1 ) ) )
    | ~ ( l1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) )
    | ~ ( v2_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) )
    | ~ ( v1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['18','20'])).

thf('22',plain,(
    m1_pre_topc @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    m1_pre_topc @ sk_B_1 @ sk_A ),
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

thf('24',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( l1_pre_topc @ X21 )
      | ~ ( v2_pre_topc @ X21 )
      | ( v2_struct_0 @ X21 )
      | ~ ( m1_pre_topc @ X22 @ X21 )
      | ( l1_pre_topc @ ( k8_tmap_1 @ X21 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k8_tmap_1])).

thf('25',plain,
    ( ( l1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) )
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
    ( ( l1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['25','26','27'])).

thf('29',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    l1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) ),
    inference(clc,[status(thm)],['28','29'])).

thf('31',plain,(
    m1_pre_topc @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( l1_pre_topc @ X21 )
      | ~ ( v2_pre_topc @ X21 )
      | ( v2_struct_0 @ X21 )
      | ~ ( m1_pre_topc @ X22 @ X21 )
      | ( v2_pre_topc @ ( k8_tmap_1 @ X21 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k8_tmap_1])).

thf('33',plain,
    ( ( v2_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ( v2_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['33','34','35'])).

thf('37',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    v2_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) ),
    inference(clc,[status(thm)],['36','37'])).

thf('39',plain,(
    m1_pre_topc @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( l1_pre_topc @ X21 )
      | ~ ( v2_pre_topc @ X21 )
      | ( v2_struct_0 @ X21 )
      | ~ ( m1_pre_topc @ X22 @ X21 )
      | ( v1_pre_topc @ ( k8_tmap_1 @ X21 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k8_tmap_1])).

thf('41',plain,
    ( ( v1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,
    ( ( v1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['41','42','43'])).

thf('45',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    v1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) ),
    inference(clc,[status(thm)],['44','45'])).

thf('47',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( ( ( k8_tmap_1 @ sk_A @ sk_B_1 )
      = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B_1 ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['21','22','30','38','46','47','48'])).

thf('50',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,
    ( ( k8_tmap_1 @ sk_A @ sk_B_1 )
    = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['49','50'])).

thf('52',plain,
    ( ( k8_tmap_1 @ sk_A @ sk_B_1 )
    = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['49','50'])).

thf('53',plain,(
    l1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) ),
    inference(clc,[status(thm)],['28','29'])).

thf('54',plain,(
    m1_subset_1 @ ( u1_struct_0 @ ( sk_B @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['17','51','52','53'])).

thf(dt_k7_tmap_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( ( v1_funct_1 @ ( k7_tmap_1 @ A @ B ) )
        & ( v1_funct_2 @ ( k7_tmap_1 @ A @ B ) @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ A @ B ) ) )
        & ( m1_subset_1 @ ( k7_tmap_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ A @ B ) ) ) ) ) ) ) )).

thf('55',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( l1_pre_topc @ X19 )
      | ~ ( v2_pre_topc @ X19 )
      | ( v2_struct_0 @ X19 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ( m1_subset_1 @ ( k7_tmap_1 @ X19 @ X20 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X19 ) @ ( u1_struct_0 @ ( k6_tmap_1 @ X19 @ X20 ) ) ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_tmap_1])).

thf('56',plain,
    ( ( m1_subset_1 @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ ( sk_B @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) ) ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ ( sk_B @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) ) ) ) ) ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    m1_subset_1 @ ( u1_struct_0 @ ( sk_B @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['17','51','52','53'])).

thf(d10_tmap_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k7_tmap_1 @ A @ B )
            = ( k6_partfun1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('58',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ( ( k7_tmap_1 @ X10 @ X9 )
        = ( k6_partfun1 @ ( u1_struct_0 @ X10 ) ) )
      | ~ ( l1_pre_topc @ X10 )
      | ~ ( v2_pre_topc @ X10 )
      | ( v2_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d10_tmap_1])).

thf('59',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ ( sk_B @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) ) ) )
      = ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ ( sk_B @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) ) ) )
      = ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['59','60','61'])).

thf('63',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,
    ( ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ ( sk_B @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) ) ) )
    = ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['62','63'])).

thf('65',plain,(
    m1_subset_1 @ ( u1_struct_0 @ ( sk_B @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['17','51','52','53'])).

thf('66',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ( ( u1_struct_0 @ ( k6_tmap_1 @ X24 @ X23 ) )
        = ( u1_struct_0 @ X24 ) )
      | ~ ( l1_pre_topc @ X24 )
      | ~ ( v2_pre_topc @ X24 )
      | ( v2_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t104_tmap_1])).

thf('67',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ ( sk_B @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) ) ) ) )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ ( sk_B @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) ) ) ) )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['67','68','69'])).

thf('71',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,
    ( ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ ( sk_B @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) ) ) ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['70','71'])).

thf('73',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,
    ( ( m1_subset_1 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['56','64','72','73','74'])).

thf('76',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    m1_subset_1 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['75','76'])).

thf('78',plain,(
    m1_subset_1 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['75','76'])).

thf(reflexivity_r1_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ~ ( v1_xboole_0 @ B )
        & ~ ( v1_xboole_0 @ D )
        & ( v1_funct_1 @ E )
        & ( v1_funct_2 @ E @ A @ B )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ F )
        & ( v1_funct_2 @ F @ C @ D )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( r1_funct_2 @ A @ B @ C @ D @ E @ E ) ) )).

thf('79',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( r1_funct_2 @ X3 @ X4 @ X5 @ X6 @ X7 @ X7 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) ) )
      | ~ ( v1_funct_2 @ X7 @ X3 @ X4 )
      | ~ ( v1_funct_1 @ X7 )
      | ( v1_xboole_0 @ X6 )
      | ( v1_xboole_0 @ X4 )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_funct_2 @ X8 @ X5 @ X6 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X5 @ X6 ) ) ) ) ),
    inference(cnf,[status(esa)],[reflexivity_r1_funct_2])).

thf('80',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) )
      | ~ ( v1_funct_2 @ X2 @ X1 @ X0 )
      | ~ ( v1_funct_1 @ X2 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_funct_1 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v1_funct_2 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( r1_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ X1 @ X0 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('82',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( l1_pre_topc @ X19 )
      | ~ ( v2_pre_topc @ X19 )
      | ( v2_struct_0 @ X19 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ( v1_funct_1 @ ( k7_tmap_1 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_tmap_1])).

thf('83',plain,
    ( ( v1_funct_1 @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B_1 ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,
    ( ( v1_funct_1 @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B_1 ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['83','84','85'])).

thf('87',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    v1_funct_1 @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['86','87'])).

thf('89',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('90',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ( ( k7_tmap_1 @ X10 @ X9 )
        = ( k6_partfun1 @ ( u1_struct_0 @ X10 ) ) )
      | ~ ( l1_pre_topc @ X10 )
      | ~ ( v2_pre_topc @ X10 )
      | ( v2_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d10_tmap_1])).

thf('91',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B_1 ) )
      = ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B_1 ) )
      = ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['91','92','93'])).

thf('95',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,
    ( ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B_1 ) )
    = ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['94','95'])).

thf('97',plain,(
    v1_funct_1 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['88','96'])).

thf('98',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('99',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( l1_pre_topc @ X19 )
      | ~ ( v2_pre_topc @ X19 )
      | ( v2_struct_0 @ X19 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ( v1_funct_2 @ ( k7_tmap_1 @ X19 @ X20 ) @ ( u1_struct_0 @ X19 ) @ ( u1_struct_0 @ ( k6_tmap_1 @ X19 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_tmap_1])).

thf('100',plain,
    ( ( v1_funct_2 @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B_1 ) ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B_1 ) ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,
    ( ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B_1 ) )
    = ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['94','95'])).

thf('102',plain,
    ( ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B_1 ) ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['10','11'])).

thf('103',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,
    ( ( v1_funct_2 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['100','101','102','103','104'])).

thf('106',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,(
    v1_funct_2 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['105','106'])).

thf('108',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) )
      | ~ ( v1_funct_2 @ X2 @ X1 @ X0 )
      | ~ ( v1_funct_1 @ X2 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ X0 )
      | ( r1_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ X1 @ X0 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['80','97','107'])).

thf('109',plain,
    ( ( r1_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_funct_1 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( v1_funct_2 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['77','108'])).

thf('110',plain,(
    v1_funct_1 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['88','96'])).

thf('111',plain,(
    v1_funct_2 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['105','106'])).

thf('112',plain,
    ( ( r1_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['109','110','111'])).

thf('113',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r1_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['112'])).

thf('114',plain,(
    m1_subset_1 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['75','76'])).

thf('115',plain,
    ( ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B_1 ) ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['10','11'])).

thf('116',plain,
    ( ( k8_tmap_1 @ sk_A @ sk_B_1 )
    = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['49','50'])).

thf('117',plain,
    ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['115','116'])).

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

thf('118',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_pre_topc @ X15 @ X16 )
      | ( ( sk_D_1 @ X17 @ X15 @ X16 )
        = ( u1_struct_0 @ X15 ) )
      | ( X17
        = ( k9_tmap_1 @ X16 @ X15 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X16 ) @ ( u1_struct_0 @ ( k8_tmap_1 @ X16 @ X15 ) ) ) ) )
      | ~ ( v1_funct_2 @ X17 @ ( u1_struct_0 @ X16 ) @ ( u1_struct_0 @ ( k8_tmap_1 @ X16 @ X15 ) ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( l1_pre_topc @ X16 )
      | ~ ( v2_pre_topc @ X16 )
      | ( v2_struct_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d12_tmap_1])).

thf('119',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) ) )
      | ( X0
        = ( k9_tmap_1 @ sk_A @ sk_B_1 ) )
      | ( ( sk_D_1 @ X0 @ sk_B_1 @ sk_A )
        = ( u1_struct_0 @ sk_B_1 ) )
      | ~ ( m1_pre_topc @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['117','118'])).

thf('120',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('121',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,
    ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['115','116'])).

thf('123',plain,(
    m1_pre_topc @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( X0
        = ( k9_tmap_1 @ sk_A @ sk_B_1 ) )
      | ( ( sk_D_1 @ X0 @ sk_B_1 @ sk_A )
        = ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['119','120','121','122','123'])).

thf('125',plain,
    ( ( ( sk_D_1 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B_1 @ sk_A )
      = ( u1_struct_0 @ sk_B_1 ) )
    | ( ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) )
      = ( k9_tmap_1 @ sk_A @ sk_B_1 ) )
    | ~ ( v1_funct_2 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_funct_1 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['114','124'])).

thf('126',plain,(
    v1_funct_2 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['105','106'])).

thf('127',plain,(
    v1_funct_1 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['88','96'])).

thf('128',plain,
    ( ( ( sk_D_1 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B_1 @ sk_A )
      = ( u1_struct_0 @ sk_B_1 ) )
    | ( ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) )
      = ( k9_tmap_1 @ sk_A @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['125','126','127'])).

thf('129',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('130',plain,
    ( ( ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) )
      = ( k9_tmap_1 @ sk_A @ sk_B_1 ) )
    | ( ( sk_D_1 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B_1 @ sk_A )
      = ( u1_struct_0 @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['128','129'])).

thf('131',plain,
    ( ( ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) )
      = ( k9_tmap_1 @ sk_A @ sk_B_1 ) )
    | ( ( sk_D_1 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B_1 @ sk_A )
      = ( u1_struct_0 @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['128','129'])).

thf('132',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_pre_topc @ X15 @ X16 )
      | ~ ( r1_funct_2 @ ( u1_struct_0 @ X16 ) @ ( u1_struct_0 @ ( k8_tmap_1 @ X16 @ X15 ) ) @ ( u1_struct_0 @ X16 ) @ ( u1_struct_0 @ ( k6_tmap_1 @ X16 @ ( sk_D_1 @ X17 @ X15 @ X16 ) ) ) @ X17 @ ( k7_tmap_1 @ X16 @ ( sk_D_1 @ X17 @ X15 @ X16 ) ) )
      | ( X17
        = ( k9_tmap_1 @ X16 @ X15 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X16 ) @ ( u1_struct_0 @ ( k8_tmap_1 @ X16 @ X15 ) ) ) ) )
      | ~ ( v1_funct_2 @ X17 @ ( u1_struct_0 @ X16 ) @ ( u1_struct_0 @ ( k8_tmap_1 @ X16 @ X15 ) ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( l1_pre_topc @ X16 )
      | ~ ( v2_pre_topc @ X16 )
      | ( v2_struct_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d12_tmap_1])).

thf('133',plain,
    ( ~ ( r1_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B_1 ) ) ) @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( k7_tmap_1 @ sk_A @ ( sk_D_1 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B_1 @ sk_A ) ) )
    | ( ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) )
      = ( k9_tmap_1 @ sk_A @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v1_funct_1 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( v1_funct_2 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) ) )
    | ~ ( m1_subset_1 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) ) ) ) )
    | ( ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) )
      = ( k9_tmap_1 @ sk_A @ sk_B_1 ) )
    | ~ ( m1_pre_topc @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['131','132'])).

thf('134',plain,
    ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['115','116'])).

thf('135',plain,
    ( ( k8_tmap_1 @ sk_A @ sk_B_1 )
    = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['49','50'])).

thf('136',plain,
    ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['115','116'])).

thf('137',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('138',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('139',plain,(
    v1_funct_1 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['88','96'])).

thf('140',plain,
    ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['115','116'])).

thf('141',plain,(
    v1_funct_2 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['105','106'])).

thf('142',plain,
    ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['115','116'])).

thf('143',plain,(
    m1_subset_1 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['75','76'])).

thf('144',plain,(
    m1_pre_topc @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('145',plain,
    ( ~ ( r1_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( k7_tmap_1 @ sk_A @ ( sk_D_1 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B_1 @ sk_A ) ) )
    | ( ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) )
      = ( k9_tmap_1 @ sk_A @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A )
    | ( ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) )
      = ( k9_tmap_1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['133','134','135','136','137','138','139','140','141','142','143','144'])).

thf('146',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) )
      = ( k9_tmap_1 @ sk_A @ sk_B_1 ) )
    | ~ ( r1_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( k7_tmap_1 @ sk_A @ ( sk_D_1 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B_1 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['145'])).

thf('147',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('148',plain,
    ( ~ ( r1_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( k7_tmap_1 @ sk_A @ ( sk_D_1 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B_1 @ sk_A ) ) )
    | ( ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) )
      = ( k9_tmap_1 @ sk_A @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['146','147'])).

thf('149',plain,
    ( ~ ( r1_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B_1 ) ) )
    | ( ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) )
      = ( k9_tmap_1 @ sk_A @ sk_B_1 ) )
    | ( ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) )
      = ( k9_tmap_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['130','148'])).

thf('150',plain,
    ( ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B_1 ) )
    = ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['94','95'])).

thf('151',plain,
    ( ~ ( r1_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) )
      = ( k9_tmap_1 @ sk_A @ sk_B_1 ) )
    | ( ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) )
      = ( k9_tmap_1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['149','150'])).

thf('152',plain,
    ( ( ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) )
      = ( k9_tmap_1 @ sk_A @ sk_B_1 ) )
    | ~ ( r1_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['151'])).

thf('153',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) )
      = ( k9_tmap_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['113','152'])).

thf('154',plain,(
    ~ ( r1_tmap_1 @ sk_B_1 @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) @ ( k9_tmap_1 @ sk_A @ sk_B_1 ) @ sk_B_1 ) @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('155',plain,
    ( ~ ( r1_tmap_1 @ sk_B_1 @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B_1 ) @ sk_C )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['153','154'])).

thf('156',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('157',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
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

thf('158',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) )
      | ( ( u1_struct_0 @ X27 )
       != X25 )
      | ~ ( m1_subset_1 @ X28 @ ( u1_struct_0 @ X27 ) )
      | ( r1_tmap_1 @ X27 @ ( k6_tmap_1 @ X26 @ X25 ) @ ( k2_tmap_1 @ X26 @ ( k6_tmap_1 @ X26 @ X25 ) @ ( k7_tmap_1 @ X26 @ X25 ) @ X27 ) @ X28 )
      | ~ ( m1_pre_topc @ X27 @ X26 )
      | ( v2_struct_0 @ X27 )
      | ~ ( l1_pre_topc @ X26 )
      | ~ ( v2_pre_topc @ X26 )
      | ( v2_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t110_tmap_1])).

thf('159',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( v2_struct_0 @ X26 )
      | ~ ( v2_pre_topc @ X26 )
      | ~ ( l1_pre_topc @ X26 )
      | ( v2_struct_0 @ X27 )
      | ~ ( m1_pre_topc @ X27 @ X26 )
      | ( r1_tmap_1 @ X27 @ ( k6_tmap_1 @ X26 @ ( u1_struct_0 @ X27 ) ) @ ( k2_tmap_1 @ X26 @ ( k6_tmap_1 @ X26 @ ( u1_struct_0 @ X27 ) ) @ ( k7_tmap_1 @ X26 @ ( u1_struct_0 @ X27 ) ) @ X27 ) @ X28 )
      | ~ ( m1_subset_1 @ X28 @ ( u1_struct_0 @ X27 ) )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X27 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) ) ) ),
    inference(simplify,[status(thm)],['158'])).

thf('160',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B_1 ) )
      | ( r1_tmap_1 @ sk_B_1 @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B_1 ) ) @ ( k2_tmap_1 @ sk_A @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B_1 ) ) @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B_1 ) ) @ sk_B_1 ) @ X0 )
      | ~ ( m1_pre_topc @ sk_B_1 @ sk_A )
      | ( v2_struct_0 @ sk_B_1 )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['157','159'])).

thf('161',plain,
    ( ( k8_tmap_1 @ sk_A @ sk_B_1 )
    = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['49','50'])).

thf('162',plain,
    ( ( k8_tmap_1 @ sk_A @ sk_B_1 )
    = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['49','50'])).

thf('163',plain,
    ( ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B_1 ) )
    = ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['94','95'])).

thf('164',plain,(
    m1_pre_topc @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('165',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('166',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('167',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B_1 ) )
      | ( r1_tmap_1 @ sk_B_1 @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B_1 ) @ X0 )
      | ( v2_struct_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['160','161','162','163','164','165','166'])).

thf('168',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B_1 )
    | ( r1_tmap_1 @ sk_B_1 @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B_1 ) @ sk_C ) ),
    inference('sup-',[status(thm)],['156','167'])).

thf('169',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('170',plain,
    ( ( r1_tmap_1 @ sk_B_1 @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B_1 ) @ sk_C )
    | ( v2_struct_0 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['168','169'])).

thf('171',plain,(
    ~ ( v2_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('172',plain,(
    r1_tmap_1 @ sk_B_1 @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B_1 ) @ sk_C ),
    inference(clc,[status(thm)],['170','171'])).

thf('173',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['155','172'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('174',plain,(
    ! [X2: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X2 ) )
      | ~ ( l1_struct_0 @ X2 )
      | ( v2_struct_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('175',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['173','174'])).

thf('176',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('177',plain,(
    ! [X0: $i] :
      ( ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('178',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['176','177'])).

thf('179',plain,(
    v2_struct_0 @ sk_A ),
    inference(demod,[status(thm)],['175','178'])).

thf('180',plain,(
    $false ),
    inference(demod,[status(thm)],['0','179'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.XXVrdjHYLB
% 0.12/0.34  % Computer   : n012.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 12:58:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.35  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 48.20/48.42  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 48.20/48.42  % Solved by: fo/fo7.sh
% 48.20/48.42  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 48.20/48.42  % done 8077 iterations in 47.963s
% 48.20/48.42  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 48.20/48.42  % SZS output start Refutation
% 48.20/48.42  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 48.20/48.42  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 48.20/48.42  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 48.20/48.42  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 48.20/48.42  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 48.20/48.42  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 48.20/48.42  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 48.20/48.42  thf(k9_tmap_1_type, type, k9_tmap_1: $i > $i > $i).
% 48.20/48.42  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 48.20/48.42  thf(sk_A_type, type, sk_A: $i).
% 48.20/48.42  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 48.20/48.42  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 48.20/48.42  thf(r1_tmap_1_type, type, r1_tmap_1: $i > $i > $i > $i > $o).
% 48.20/48.42  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 48.20/48.42  thf(sk_B_1_type, type, sk_B_1: $i).
% 48.20/48.42  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i > $i).
% 48.20/48.42  thf(sk_B_type, type, sk_B: $i > $i).
% 48.20/48.42  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 48.20/48.42  thf(k6_tmap_1_type, type, k6_tmap_1: $i > $i > $i).
% 48.20/48.42  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 48.20/48.42  thf(sk_C_type, type, sk_C: $i).
% 48.20/48.42  thf(r1_funct_2_type, type, r1_funct_2: $i > $i > $i > $i > $i > $i > $o).
% 48.20/48.42  thf(k8_tmap_1_type, type, k8_tmap_1: $i > $i > $i).
% 48.20/48.42  thf(k2_tmap_1_type, type, k2_tmap_1: $i > $i > $i > $i > $i).
% 48.20/48.42  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 48.20/48.42  thf(k7_tmap_1_type, type, k7_tmap_1: $i > $i > $i).
% 48.20/48.42  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 48.20/48.42  thf(k5_tmap_1_type, type, k5_tmap_1: $i > $i > $i).
% 48.20/48.42  thf(t119_tmap_1, conjecture,
% 48.20/48.42    (![A:$i]:
% 48.20/48.42     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 48.20/48.42       ( ![B:$i]:
% 48.20/48.42         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 48.20/48.42           ( ![C:$i]:
% 48.20/48.42             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ B ) ) =>
% 48.20/48.42               ( r1_tmap_1 @
% 48.20/48.42                 B @ ( k8_tmap_1 @ A @ B ) @ 
% 48.20/48.42                 ( k2_tmap_1 @
% 48.20/48.42                   A @ ( k8_tmap_1 @ A @ B ) @ ( k9_tmap_1 @ A @ B ) @ B ) @ 
% 48.20/48.42                 C ) ) ) ) ) ))).
% 48.20/48.42  thf(zf_stmt_0, negated_conjecture,
% 48.20/48.42    (~( ![A:$i]:
% 48.20/48.42        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 48.20/48.42            ( l1_pre_topc @ A ) ) =>
% 48.20/48.42          ( ![B:$i]:
% 48.20/48.42            ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 48.20/48.42              ( ![C:$i]:
% 48.20/48.42                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ B ) ) =>
% 48.20/48.42                  ( r1_tmap_1 @
% 48.20/48.42                    B @ ( k8_tmap_1 @ A @ B ) @ 
% 48.20/48.42                    ( k2_tmap_1 @
% 48.20/48.42                      A @ ( k8_tmap_1 @ A @ B ) @ ( k9_tmap_1 @ A @ B ) @ B ) @ 
% 48.20/48.42                    C ) ) ) ) ) ) )),
% 48.20/48.42    inference('cnf.neg', [status(esa)], [t119_tmap_1])).
% 48.20/48.42  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 48.20/48.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 48.20/48.42  thf('1', plain, ((m1_pre_topc @ sk_B_1 @ sk_A)),
% 48.20/48.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 48.20/48.42  thf(t1_tsep_1, axiom,
% 48.20/48.42    (![A:$i]:
% 48.20/48.42     ( ( l1_pre_topc @ A ) =>
% 48.20/48.42       ( ![B:$i]:
% 48.20/48.42         ( ( m1_pre_topc @ B @ A ) =>
% 48.20/48.42           ( m1_subset_1 @
% 48.20/48.42             ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 48.20/48.42  thf('2', plain,
% 48.20/48.42      (![X29 : $i, X30 : $i]:
% 48.20/48.42         (~ (m1_pre_topc @ X29 @ X30)
% 48.20/48.42          | (m1_subset_1 @ (u1_struct_0 @ X29) @ 
% 48.20/48.42             (k1_zfmisc_1 @ (u1_struct_0 @ X30)))
% 48.20/48.42          | ~ (l1_pre_topc @ X30))),
% 48.20/48.42      inference('cnf', [status(esa)], [t1_tsep_1])).
% 48.20/48.42  thf('3', plain,
% 48.20/48.42      ((~ (l1_pre_topc @ sk_A)
% 48.20/48.42        | (m1_subset_1 @ (u1_struct_0 @ sk_B_1) @ 
% 48.20/48.42           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 48.20/48.42      inference('sup-', [status(thm)], ['1', '2'])).
% 48.20/48.42  thf('4', plain, ((l1_pre_topc @ sk_A)),
% 48.20/48.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 48.20/48.42  thf('5', plain,
% 48.20/48.42      ((m1_subset_1 @ (u1_struct_0 @ sk_B_1) @ 
% 48.20/48.42        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 48.20/48.42      inference('demod', [status(thm)], ['3', '4'])).
% 48.20/48.42  thf(t104_tmap_1, axiom,
% 48.20/48.42    (![A:$i]:
% 48.20/48.42     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 48.20/48.42       ( ![B:$i]:
% 48.20/48.42         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 48.20/48.42           ( ( ( u1_struct_0 @ ( k6_tmap_1 @ A @ B ) ) = ( u1_struct_0 @ A ) ) & 
% 48.20/48.42             ( ( u1_pre_topc @ ( k6_tmap_1 @ A @ B ) ) = ( k5_tmap_1 @ A @ B ) ) ) ) ) ))).
% 48.20/48.42  thf('6', plain,
% 48.20/48.42      (![X23 : $i, X24 : $i]:
% 48.20/48.42         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 48.20/48.42          | ((u1_struct_0 @ (k6_tmap_1 @ X24 @ X23)) = (u1_struct_0 @ X24))
% 48.20/48.42          | ~ (l1_pre_topc @ X24)
% 48.20/48.42          | ~ (v2_pre_topc @ X24)
% 48.20/48.42          | (v2_struct_0 @ X24))),
% 48.20/48.42      inference('cnf', [status(esa)], [t104_tmap_1])).
% 48.20/48.42  thf('7', plain,
% 48.20/48.42      (((v2_struct_0 @ sk_A)
% 48.20/48.42        | ~ (v2_pre_topc @ sk_A)
% 48.20/48.42        | ~ (l1_pre_topc @ sk_A)
% 48.20/48.42        | ((u1_struct_0 @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B_1)))
% 48.20/48.42            = (u1_struct_0 @ sk_A)))),
% 48.20/48.42      inference('sup-', [status(thm)], ['5', '6'])).
% 48.20/48.42  thf('8', plain, ((v2_pre_topc @ sk_A)),
% 48.20/48.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 48.20/48.42  thf('9', plain, ((l1_pre_topc @ sk_A)),
% 48.20/48.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 48.20/48.42  thf('10', plain,
% 48.20/48.42      (((v2_struct_0 @ sk_A)
% 48.20/48.42        | ((u1_struct_0 @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B_1)))
% 48.20/48.42            = (u1_struct_0 @ sk_A)))),
% 48.20/48.42      inference('demod', [status(thm)], ['7', '8', '9'])).
% 48.20/48.42  thf('11', plain, (~ (v2_struct_0 @ sk_A)),
% 48.20/48.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 48.20/48.42  thf('12', plain,
% 48.20/48.42      (((u1_struct_0 @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B_1)))
% 48.20/48.42         = (u1_struct_0 @ sk_A))),
% 48.20/48.42      inference('clc', [status(thm)], ['10', '11'])).
% 48.20/48.42  thf(existence_m1_pre_topc, axiom,
% 48.20/48.42    (![A:$i]: ( ( l1_pre_topc @ A ) => ( ?[B:$i]: ( m1_pre_topc @ B @ A ) ) ))).
% 48.20/48.42  thf('13', plain,
% 48.20/48.42      (![X1 : $i]: ((m1_pre_topc @ (sk_B @ X1) @ X1) | ~ (l1_pre_topc @ X1))),
% 48.20/48.42      inference('cnf', [status(esa)], [existence_m1_pre_topc])).
% 48.20/48.42  thf('14', plain,
% 48.20/48.42      (![X29 : $i, X30 : $i]:
% 48.20/48.42         (~ (m1_pre_topc @ X29 @ X30)
% 48.20/48.42          | (m1_subset_1 @ (u1_struct_0 @ X29) @ 
% 48.20/48.42             (k1_zfmisc_1 @ (u1_struct_0 @ X30)))
% 48.20/48.42          | ~ (l1_pre_topc @ X30))),
% 48.20/48.42      inference('cnf', [status(esa)], [t1_tsep_1])).
% 48.20/48.42  thf('15', plain,
% 48.20/48.42      (![X0 : $i]:
% 48.20/48.42         (~ (l1_pre_topc @ X0)
% 48.20/48.42          | ~ (l1_pre_topc @ X0)
% 48.20/48.42          | (m1_subset_1 @ (u1_struct_0 @ (sk_B @ X0)) @ 
% 48.20/48.42             (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 48.20/48.42      inference('sup-', [status(thm)], ['13', '14'])).
% 48.20/48.42  thf('16', plain,
% 48.20/48.42      (![X0 : $i]:
% 48.20/48.42         ((m1_subset_1 @ (u1_struct_0 @ (sk_B @ X0)) @ 
% 48.20/48.42           (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 48.20/48.42          | ~ (l1_pre_topc @ X0))),
% 48.20/48.42      inference('simplify', [status(thm)], ['15'])).
% 48.20/48.42  thf('17', plain,
% 48.20/48.42      (((m1_subset_1 @ 
% 48.20/48.42         (u1_struct_0 @ (sk_B @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B_1)))) @ 
% 48.20/48.42         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 48.20/48.42        | ~ (l1_pre_topc @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B_1))))),
% 48.20/48.42      inference('sup+', [status(thm)], ['12', '16'])).
% 48.20/48.42  thf('18', plain,
% 48.20/48.42      ((m1_subset_1 @ (u1_struct_0 @ sk_B_1) @ 
% 48.20/48.42        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 48.20/48.42      inference('demod', [status(thm)], ['3', '4'])).
% 48.20/48.42  thf(d11_tmap_1, axiom,
% 48.20/48.42    (![A:$i]:
% 48.20/48.42     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 48.20/48.42       ( ![B:$i]:
% 48.20/48.42         ( ( m1_pre_topc @ B @ A ) =>
% 48.20/48.42           ( ![C:$i]:
% 48.20/48.42             ( ( ( v1_pre_topc @ C ) & ( v2_pre_topc @ C ) & 
% 48.20/48.42                 ( l1_pre_topc @ C ) ) =>
% 48.20/48.42               ( ( ( C ) = ( k8_tmap_1 @ A @ B ) ) <=>
% 48.20/48.42                 ( ![D:$i]:
% 48.20/48.42                   ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 48.20/48.42                     ( ( ( D ) = ( u1_struct_0 @ B ) ) =>
% 48.20/48.42                       ( ( C ) = ( k6_tmap_1 @ A @ D ) ) ) ) ) ) ) ) ) ) ))).
% 48.20/48.42  thf('19', plain,
% 48.20/48.42      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 48.20/48.42         (~ (m1_pre_topc @ X11 @ X12)
% 48.20/48.42          | ((X13) != (k8_tmap_1 @ X12 @ X11))
% 48.20/48.42          | ((X14) != (u1_struct_0 @ X11))
% 48.20/48.42          | ((X13) = (k6_tmap_1 @ X12 @ X14))
% 48.20/48.42          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 48.20/48.42          | ~ (l1_pre_topc @ X13)
% 48.20/48.42          | ~ (v2_pre_topc @ X13)
% 48.20/48.42          | ~ (v1_pre_topc @ X13)
% 48.20/48.42          | ~ (l1_pre_topc @ X12)
% 48.20/48.42          | ~ (v2_pre_topc @ X12)
% 48.20/48.42          | (v2_struct_0 @ X12))),
% 48.20/48.42      inference('cnf', [status(esa)], [d11_tmap_1])).
% 48.20/48.42  thf('20', plain,
% 48.20/48.42      (![X11 : $i, X12 : $i]:
% 48.20/48.42         ((v2_struct_0 @ X12)
% 48.20/48.42          | ~ (v2_pre_topc @ X12)
% 48.20/48.42          | ~ (l1_pre_topc @ X12)
% 48.20/48.42          | ~ (v1_pre_topc @ (k8_tmap_1 @ X12 @ X11))
% 48.20/48.42          | ~ (v2_pre_topc @ (k8_tmap_1 @ X12 @ X11))
% 48.20/48.42          | ~ (l1_pre_topc @ (k8_tmap_1 @ X12 @ X11))
% 48.20/48.42          | ~ (m1_subset_1 @ (u1_struct_0 @ X11) @ 
% 48.20/48.42               (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 48.20/48.42          | ((k8_tmap_1 @ X12 @ X11) = (k6_tmap_1 @ X12 @ (u1_struct_0 @ X11)))
% 48.20/48.42          | ~ (m1_pre_topc @ X11 @ X12))),
% 48.20/48.42      inference('simplify', [status(thm)], ['19'])).
% 48.20/48.42  thf('21', plain,
% 48.20/48.42      ((~ (m1_pre_topc @ sk_B_1 @ sk_A)
% 48.20/48.42        | ((k8_tmap_1 @ sk_A @ sk_B_1)
% 48.20/48.42            = (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B_1)))
% 48.20/48.42        | ~ (l1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B_1))
% 48.20/48.42        | ~ (v2_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B_1))
% 48.20/48.42        | ~ (v1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B_1))
% 48.20/48.42        | ~ (l1_pre_topc @ sk_A)
% 48.20/48.42        | ~ (v2_pre_topc @ sk_A)
% 48.20/48.42        | (v2_struct_0 @ sk_A))),
% 48.20/48.42      inference('sup-', [status(thm)], ['18', '20'])).
% 48.20/48.42  thf('22', plain, ((m1_pre_topc @ sk_B_1 @ sk_A)),
% 48.20/48.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 48.20/48.42  thf('23', plain, ((m1_pre_topc @ sk_B_1 @ sk_A)),
% 48.20/48.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 48.20/48.42  thf(dt_k8_tmap_1, axiom,
% 48.20/48.42    (![A:$i,B:$i]:
% 48.20/48.42     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 48.20/48.42         ( l1_pre_topc @ A ) & ( m1_pre_topc @ B @ A ) ) =>
% 48.20/48.42       ( ( v1_pre_topc @ ( k8_tmap_1 @ A @ B ) ) & 
% 48.20/48.42         ( v2_pre_topc @ ( k8_tmap_1 @ A @ B ) ) & 
% 48.20/48.42         ( l1_pre_topc @ ( k8_tmap_1 @ A @ B ) ) ) ))).
% 48.20/48.42  thf('24', plain,
% 48.20/48.42      (![X21 : $i, X22 : $i]:
% 48.20/48.42         (~ (l1_pre_topc @ X21)
% 48.20/48.42          | ~ (v2_pre_topc @ X21)
% 48.20/48.42          | (v2_struct_0 @ X21)
% 48.20/48.42          | ~ (m1_pre_topc @ X22 @ X21)
% 48.20/48.42          | (l1_pre_topc @ (k8_tmap_1 @ X21 @ X22)))),
% 48.20/48.42      inference('cnf', [status(esa)], [dt_k8_tmap_1])).
% 48.20/48.42  thf('25', plain,
% 48.20/48.42      (((l1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B_1))
% 48.20/48.42        | (v2_struct_0 @ sk_A)
% 48.20/48.42        | ~ (v2_pre_topc @ sk_A)
% 48.20/48.42        | ~ (l1_pre_topc @ sk_A))),
% 48.20/48.42      inference('sup-', [status(thm)], ['23', '24'])).
% 48.20/48.42  thf('26', plain, ((v2_pre_topc @ sk_A)),
% 48.20/48.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 48.20/48.42  thf('27', plain, ((l1_pre_topc @ sk_A)),
% 48.20/48.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 48.20/48.42  thf('28', plain,
% 48.20/48.42      (((l1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B_1)) | (v2_struct_0 @ sk_A))),
% 48.20/48.42      inference('demod', [status(thm)], ['25', '26', '27'])).
% 48.20/48.42  thf('29', plain, (~ (v2_struct_0 @ sk_A)),
% 48.20/48.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 48.20/48.42  thf('30', plain, ((l1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B_1))),
% 48.20/48.42      inference('clc', [status(thm)], ['28', '29'])).
% 48.20/48.42  thf('31', plain, ((m1_pre_topc @ sk_B_1 @ sk_A)),
% 48.20/48.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 48.20/48.42  thf('32', plain,
% 48.20/48.42      (![X21 : $i, X22 : $i]:
% 48.20/48.42         (~ (l1_pre_topc @ X21)
% 48.20/48.42          | ~ (v2_pre_topc @ X21)
% 48.20/48.42          | (v2_struct_0 @ X21)
% 48.20/48.42          | ~ (m1_pre_topc @ X22 @ X21)
% 48.20/48.42          | (v2_pre_topc @ (k8_tmap_1 @ X21 @ X22)))),
% 48.20/48.42      inference('cnf', [status(esa)], [dt_k8_tmap_1])).
% 48.20/48.42  thf('33', plain,
% 48.20/48.42      (((v2_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B_1))
% 48.20/48.42        | (v2_struct_0 @ sk_A)
% 48.20/48.42        | ~ (v2_pre_topc @ sk_A)
% 48.20/48.42        | ~ (l1_pre_topc @ sk_A))),
% 48.20/48.42      inference('sup-', [status(thm)], ['31', '32'])).
% 48.20/48.42  thf('34', plain, ((v2_pre_topc @ sk_A)),
% 48.20/48.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 48.20/48.42  thf('35', plain, ((l1_pre_topc @ sk_A)),
% 48.20/48.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 48.20/48.42  thf('36', plain,
% 48.20/48.42      (((v2_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B_1)) | (v2_struct_0 @ sk_A))),
% 48.20/48.42      inference('demod', [status(thm)], ['33', '34', '35'])).
% 48.20/48.42  thf('37', plain, (~ (v2_struct_0 @ sk_A)),
% 48.20/48.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 48.20/48.42  thf('38', plain, ((v2_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B_1))),
% 48.20/48.42      inference('clc', [status(thm)], ['36', '37'])).
% 48.20/48.42  thf('39', plain, ((m1_pre_topc @ sk_B_1 @ sk_A)),
% 48.20/48.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 48.20/48.42  thf('40', plain,
% 48.20/48.42      (![X21 : $i, X22 : $i]:
% 48.20/48.42         (~ (l1_pre_topc @ X21)
% 48.20/48.42          | ~ (v2_pre_topc @ X21)
% 48.20/48.42          | (v2_struct_0 @ X21)
% 48.20/48.42          | ~ (m1_pre_topc @ X22 @ X21)
% 48.20/48.42          | (v1_pre_topc @ (k8_tmap_1 @ X21 @ X22)))),
% 48.20/48.42      inference('cnf', [status(esa)], [dt_k8_tmap_1])).
% 48.20/48.42  thf('41', plain,
% 48.20/48.42      (((v1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B_1))
% 48.20/48.42        | (v2_struct_0 @ sk_A)
% 48.20/48.42        | ~ (v2_pre_topc @ sk_A)
% 48.20/48.42        | ~ (l1_pre_topc @ sk_A))),
% 48.20/48.42      inference('sup-', [status(thm)], ['39', '40'])).
% 48.20/48.42  thf('42', plain, ((v2_pre_topc @ sk_A)),
% 48.20/48.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 48.20/48.42  thf('43', plain, ((l1_pre_topc @ sk_A)),
% 48.20/48.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 48.20/48.42  thf('44', plain,
% 48.20/48.42      (((v1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B_1)) | (v2_struct_0 @ sk_A))),
% 48.20/48.42      inference('demod', [status(thm)], ['41', '42', '43'])).
% 48.20/48.42  thf('45', plain, (~ (v2_struct_0 @ sk_A)),
% 48.20/48.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 48.20/48.42  thf('46', plain, ((v1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B_1))),
% 48.20/48.42      inference('clc', [status(thm)], ['44', '45'])).
% 48.20/48.42  thf('47', plain, ((l1_pre_topc @ sk_A)),
% 48.20/48.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 48.20/48.42  thf('48', plain, ((v2_pre_topc @ sk_A)),
% 48.20/48.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 48.20/48.42  thf('49', plain,
% 48.20/48.42      ((((k8_tmap_1 @ sk_A @ sk_B_1)
% 48.20/48.42          = (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B_1)))
% 48.20/48.42        | (v2_struct_0 @ sk_A))),
% 48.20/48.42      inference('demod', [status(thm)],
% 48.20/48.42                ['21', '22', '30', '38', '46', '47', '48'])).
% 48.20/48.42  thf('50', plain, (~ (v2_struct_0 @ sk_A)),
% 48.20/48.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 48.20/48.42  thf('51', plain,
% 48.20/48.42      (((k8_tmap_1 @ sk_A @ sk_B_1)
% 48.20/48.42         = (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B_1)))),
% 48.20/48.42      inference('clc', [status(thm)], ['49', '50'])).
% 48.20/48.42  thf('52', plain,
% 48.20/48.42      (((k8_tmap_1 @ sk_A @ sk_B_1)
% 48.20/48.42         = (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B_1)))),
% 48.20/48.42      inference('clc', [status(thm)], ['49', '50'])).
% 48.20/48.42  thf('53', plain, ((l1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B_1))),
% 48.20/48.42      inference('clc', [status(thm)], ['28', '29'])).
% 48.20/48.42  thf('54', plain,
% 48.20/48.42      ((m1_subset_1 @ (u1_struct_0 @ (sk_B @ (k8_tmap_1 @ sk_A @ sk_B_1))) @ 
% 48.20/48.42        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 48.20/48.42      inference('demod', [status(thm)], ['17', '51', '52', '53'])).
% 48.20/48.42  thf(dt_k7_tmap_1, axiom,
% 48.20/48.42    (![A:$i,B:$i]:
% 48.20/48.42     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 48.20/48.42         ( l1_pre_topc @ A ) & 
% 48.20/48.42         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 48.20/48.42       ( ( v1_funct_1 @ ( k7_tmap_1 @ A @ B ) ) & 
% 48.20/48.42         ( v1_funct_2 @
% 48.20/48.42           ( k7_tmap_1 @ A @ B ) @ ( u1_struct_0 @ A ) @ 
% 48.20/48.42           ( u1_struct_0 @ ( k6_tmap_1 @ A @ B ) ) ) & 
% 48.20/48.42         ( m1_subset_1 @
% 48.20/48.42           ( k7_tmap_1 @ A @ B ) @ 
% 48.20/48.42           ( k1_zfmisc_1 @
% 48.20/48.42             ( k2_zfmisc_1 @
% 48.20/48.42               ( u1_struct_0 @ A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ A @ B ) ) ) ) ) ) ))).
% 48.20/48.42  thf('55', plain,
% 48.20/48.42      (![X19 : $i, X20 : $i]:
% 48.20/48.42         (~ (l1_pre_topc @ X19)
% 48.20/48.42          | ~ (v2_pre_topc @ X19)
% 48.20/48.42          | (v2_struct_0 @ X19)
% 48.20/48.42          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 48.20/48.42          | (m1_subset_1 @ (k7_tmap_1 @ X19 @ X20) @ 
% 48.20/48.42             (k1_zfmisc_1 @ 
% 48.20/48.42              (k2_zfmisc_1 @ (u1_struct_0 @ X19) @ 
% 48.20/48.42               (u1_struct_0 @ (k6_tmap_1 @ X19 @ X20))))))),
% 48.20/48.42      inference('cnf', [status(esa)], [dt_k7_tmap_1])).
% 48.20/48.42  thf('56', plain,
% 48.20/48.42      (((m1_subset_1 @ 
% 48.20/48.42         (k7_tmap_1 @ sk_A @ 
% 48.20/48.42          (u1_struct_0 @ (sk_B @ (k8_tmap_1 @ sk_A @ sk_B_1)))) @ 
% 48.20/48.42         (k1_zfmisc_1 @ 
% 48.20/48.42          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 48.20/48.42           (u1_struct_0 @ 
% 48.20/48.42            (k6_tmap_1 @ sk_A @ 
% 48.20/48.42             (u1_struct_0 @ (sk_B @ (k8_tmap_1 @ sk_A @ sk_B_1))))))))
% 48.20/48.42        | (v2_struct_0 @ sk_A)
% 48.20/48.42        | ~ (v2_pre_topc @ sk_A)
% 48.20/48.42        | ~ (l1_pre_topc @ sk_A))),
% 48.20/48.42      inference('sup-', [status(thm)], ['54', '55'])).
% 48.20/48.42  thf('57', plain,
% 48.20/48.42      ((m1_subset_1 @ (u1_struct_0 @ (sk_B @ (k8_tmap_1 @ sk_A @ sk_B_1))) @ 
% 48.20/48.42        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 48.20/48.42      inference('demod', [status(thm)], ['17', '51', '52', '53'])).
% 48.20/48.42  thf(d10_tmap_1, axiom,
% 48.20/48.42    (![A:$i]:
% 48.20/48.42     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 48.20/48.42       ( ![B:$i]:
% 48.20/48.42         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 48.20/48.42           ( ( k7_tmap_1 @ A @ B ) = ( k6_partfun1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 48.20/48.42  thf('58', plain,
% 48.20/48.42      (![X9 : $i, X10 : $i]:
% 48.20/48.42         (~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 48.20/48.42          | ((k7_tmap_1 @ X10 @ X9) = (k6_partfun1 @ (u1_struct_0 @ X10)))
% 48.20/48.42          | ~ (l1_pre_topc @ X10)
% 48.20/48.42          | ~ (v2_pre_topc @ X10)
% 48.20/48.42          | (v2_struct_0 @ X10))),
% 48.20/48.42      inference('cnf', [status(esa)], [d10_tmap_1])).
% 48.20/48.42  thf('59', plain,
% 48.20/48.42      (((v2_struct_0 @ sk_A)
% 48.20/48.42        | ~ (v2_pre_topc @ sk_A)
% 48.20/48.42        | ~ (l1_pre_topc @ sk_A)
% 48.20/48.42        | ((k7_tmap_1 @ sk_A @ 
% 48.20/48.42            (u1_struct_0 @ (sk_B @ (k8_tmap_1 @ sk_A @ sk_B_1))))
% 48.20/48.42            = (k6_partfun1 @ (u1_struct_0 @ sk_A))))),
% 48.20/48.42      inference('sup-', [status(thm)], ['57', '58'])).
% 48.20/48.42  thf('60', plain, ((v2_pre_topc @ sk_A)),
% 48.20/48.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 48.20/48.42  thf('61', plain, ((l1_pre_topc @ sk_A)),
% 48.20/48.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 48.20/48.42  thf('62', plain,
% 48.20/48.42      (((v2_struct_0 @ sk_A)
% 48.20/48.42        | ((k7_tmap_1 @ sk_A @ 
% 48.20/48.42            (u1_struct_0 @ (sk_B @ (k8_tmap_1 @ sk_A @ sk_B_1))))
% 48.20/48.42            = (k6_partfun1 @ (u1_struct_0 @ sk_A))))),
% 48.20/48.42      inference('demod', [status(thm)], ['59', '60', '61'])).
% 48.20/48.42  thf('63', plain, (~ (v2_struct_0 @ sk_A)),
% 48.20/48.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 48.20/48.42  thf('64', plain,
% 48.20/48.42      (((k7_tmap_1 @ sk_A @ 
% 48.20/48.42         (u1_struct_0 @ (sk_B @ (k8_tmap_1 @ sk_A @ sk_B_1))))
% 48.20/48.42         = (k6_partfun1 @ (u1_struct_0 @ sk_A)))),
% 48.20/48.42      inference('clc', [status(thm)], ['62', '63'])).
% 48.20/48.42  thf('65', plain,
% 48.20/48.42      ((m1_subset_1 @ (u1_struct_0 @ (sk_B @ (k8_tmap_1 @ sk_A @ sk_B_1))) @ 
% 48.20/48.42        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 48.20/48.42      inference('demod', [status(thm)], ['17', '51', '52', '53'])).
% 48.20/48.42  thf('66', plain,
% 48.20/48.42      (![X23 : $i, X24 : $i]:
% 48.20/48.42         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 48.20/48.42          | ((u1_struct_0 @ (k6_tmap_1 @ X24 @ X23)) = (u1_struct_0 @ X24))
% 48.20/48.42          | ~ (l1_pre_topc @ X24)
% 48.20/48.42          | ~ (v2_pre_topc @ X24)
% 48.20/48.42          | (v2_struct_0 @ X24))),
% 48.20/48.42      inference('cnf', [status(esa)], [t104_tmap_1])).
% 48.20/48.42  thf('67', plain,
% 48.20/48.42      (((v2_struct_0 @ sk_A)
% 48.20/48.42        | ~ (v2_pre_topc @ sk_A)
% 48.20/48.42        | ~ (l1_pre_topc @ sk_A)
% 48.20/48.42        | ((u1_struct_0 @ 
% 48.20/48.42            (k6_tmap_1 @ sk_A @ 
% 48.20/48.42             (u1_struct_0 @ (sk_B @ (k8_tmap_1 @ sk_A @ sk_B_1)))))
% 48.20/48.42            = (u1_struct_0 @ sk_A)))),
% 48.20/48.42      inference('sup-', [status(thm)], ['65', '66'])).
% 48.20/48.42  thf('68', plain, ((v2_pre_topc @ sk_A)),
% 48.20/48.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 48.20/48.42  thf('69', plain, ((l1_pre_topc @ sk_A)),
% 48.20/48.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 48.20/48.42  thf('70', plain,
% 48.20/48.42      (((v2_struct_0 @ sk_A)
% 48.20/48.42        | ((u1_struct_0 @ 
% 48.20/48.42            (k6_tmap_1 @ sk_A @ 
% 48.20/48.42             (u1_struct_0 @ (sk_B @ (k8_tmap_1 @ sk_A @ sk_B_1)))))
% 48.20/48.42            = (u1_struct_0 @ sk_A)))),
% 48.20/48.42      inference('demod', [status(thm)], ['67', '68', '69'])).
% 48.20/48.42  thf('71', plain, (~ (v2_struct_0 @ sk_A)),
% 48.20/48.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 48.20/48.42  thf('72', plain,
% 48.20/48.42      (((u1_struct_0 @ 
% 48.20/48.42         (k6_tmap_1 @ sk_A @ 
% 48.20/48.42          (u1_struct_0 @ (sk_B @ (k8_tmap_1 @ sk_A @ sk_B_1)))))
% 48.20/48.42         = (u1_struct_0 @ sk_A))),
% 48.20/48.42      inference('clc', [status(thm)], ['70', '71'])).
% 48.20/48.42  thf('73', plain, ((v2_pre_topc @ sk_A)),
% 48.20/48.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 48.20/48.42  thf('74', plain, ((l1_pre_topc @ sk_A)),
% 48.20/48.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 48.20/48.42  thf('75', plain,
% 48.20/48.42      (((m1_subset_1 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 48.20/48.42         (k1_zfmisc_1 @ 
% 48.20/48.42          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))))
% 48.20/48.42        | (v2_struct_0 @ sk_A))),
% 48.20/48.42      inference('demod', [status(thm)], ['56', '64', '72', '73', '74'])).
% 48.20/48.42  thf('76', plain, (~ (v2_struct_0 @ sk_A)),
% 48.20/48.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 48.20/48.42  thf('77', plain,
% 48.20/48.42      ((m1_subset_1 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 48.20/48.42        (k1_zfmisc_1 @ 
% 48.20/48.42         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))))),
% 48.20/48.42      inference('clc', [status(thm)], ['75', '76'])).
% 48.20/48.42  thf('78', plain,
% 48.20/48.42      ((m1_subset_1 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 48.20/48.42        (k1_zfmisc_1 @ 
% 48.20/48.42         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))))),
% 48.20/48.42      inference('clc', [status(thm)], ['75', '76'])).
% 48.20/48.42  thf(reflexivity_r1_funct_2, axiom,
% 48.20/48.42    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 48.20/48.42     ( ( ( ~( v1_xboole_0 @ B ) ) & ( ~( v1_xboole_0 @ D ) ) & 
% 48.20/48.42         ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ A @ B ) & 
% 48.20/48.42         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 48.20/48.42         ( v1_funct_1 @ F ) & ( v1_funct_2 @ F @ C @ D ) & 
% 48.20/48.42         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 48.20/48.42       ( r1_funct_2 @ A @ B @ C @ D @ E @ E ) ))).
% 48.20/48.42  thf('79', plain,
% 48.20/48.42      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 48.20/48.42         ((r1_funct_2 @ X3 @ X4 @ X5 @ X6 @ X7 @ X7)
% 48.20/48.42          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X4)))
% 48.20/48.42          | ~ (v1_funct_2 @ X7 @ X3 @ X4)
% 48.20/48.42          | ~ (v1_funct_1 @ X7)
% 48.20/48.42          | (v1_xboole_0 @ X6)
% 48.20/48.42          | (v1_xboole_0 @ X4)
% 48.20/48.42          | ~ (v1_funct_1 @ X8)
% 48.20/48.42          | ~ (v1_funct_2 @ X8 @ X5 @ X6)
% 48.20/48.42          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X5 @ X6))))),
% 48.20/48.42      inference('cnf', [status(esa)], [reflexivity_r1_funct_2])).
% 48.20/48.42  thf('80', plain,
% 48.20/48.42      (![X0 : $i, X1 : $i, X2 : $i]:
% 48.20/48.42         (~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ X0)))
% 48.20/48.42          | ~ (v1_funct_2 @ X2 @ X1 @ X0)
% 48.20/48.42          | ~ (v1_funct_1 @ X2)
% 48.20/48.42          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 48.20/48.42          | (v1_xboole_0 @ X0)
% 48.20/48.42          | ~ (v1_funct_1 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)))
% 48.20/48.42          | ~ (v1_funct_2 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 48.20/48.42               (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))
% 48.20/48.42          | (r1_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ X1 @ 
% 48.20/48.42             X0 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 48.20/48.42             (k6_partfun1 @ (u1_struct_0 @ sk_A))))),
% 48.20/48.42      inference('sup-', [status(thm)], ['78', '79'])).
% 48.20/48.42  thf('81', plain,
% 48.20/48.42      ((m1_subset_1 @ (u1_struct_0 @ sk_B_1) @ 
% 48.20/48.42        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 48.20/48.42      inference('demod', [status(thm)], ['3', '4'])).
% 48.20/48.42  thf('82', plain,
% 48.20/48.42      (![X19 : $i, X20 : $i]:
% 48.20/48.42         (~ (l1_pre_topc @ X19)
% 48.20/48.42          | ~ (v2_pre_topc @ X19)
% 48.20/48.42          | (v2_struct_0 @ X19)
% 48.20/48.42          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 48.20/48.42          | (v1_funct_1 @ (k7_tmap_1 @ X19 @ X20)))),
% 48.20/48.42      inference('cnf', [status(esa)], [dt_k7_tmap_1])).
% 48.20/48.42  thf('83', plain,
% 48.20/48.42      (((v1_funct_1 @ (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B_1)))
% 48.20/48.42        | (v2_struct_0 @ sk_A)
% 48.20/48.42        | ~ (v2_pre_topc @ sk_A)
% 48.20/48.42        | ~ (l1_pre_topc @ sk_A))),
% 48.20/48.42      inference('sup-', [status(thm)], ['81', '82'])).
% 48.20/48.42  thf('84', plain, ((v2_pre_topc @ sk_A)),
% 48.20/48.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 48.20/48.42  thf('85', plain, ((l1_pre_topc @ sk_A)),
% 48.20/48.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 48.20/48.42  thf('86', plain,
% 48.20/48.42      (((v1_funct_1 @ (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B_1)))
% 48.20/48.42        | (v2_struct_0 @ sk_A))),
% 48.20/48.42      inference('demod', [status(thm)], ['83', '84', '85'])).
% 48.20/48.42  thf('87', plain, (~ (v2_struct_0 @ sk_A)),
% 48.20/48.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 48.20/48.42  thf('88', plain,
% 48.20/48.42      ((v1_funct_1 @ (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B_1)))),
% 48.20/48.42      inference('clc', [status(thm)], ['86', '87'])).
% 48.20/48.42  thf('89', plain,
% 48.20/48.42      ((m1_subset_1 @ (u1_struct_0 @ sk_B_1) @ 
% 48.20/48.42        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 48.20/48.42      inference('demod', [status(thm)], ['3', '4'])).
% 48.20/48.42  thf('90', plain,
% 48.20/48.42      (![X9 : $i, X10 : $i]:
% 48.20/48.42         (~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 48.20/48.42          | ((k7_tmap_1 @ X10 @ X9) = (k6_partfun1 @ (u1_struct_0 @ X10)))
% 48.20/48.42          | ~ (l1_pre_topc @ X10)
% 48.20/48.42          | ~ (v2_pre_topc @ X10)
% 48.20/48.42          | (v2_struct_0 @ X10))),
% 48.20/48.42      inference('cnf', [status(esa)], [d10_tmap_1])).
% 48.20/48.42  thf('91', plain,
% 48.20/48.42      (((v2_struct_0 @ sk_A)
% 48.20/48.42        | ~ (v2_pre_topc @ sk_A)
% 48.20/48.42        | ~ (l1_pre_topc @ sk_A)
% 48.20/48.42        | ((k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B_1))
% 48.20/48.42            = (k6_partfun1 @ (u1_struct_0 @ sk_A))))),
% 48.20/48.42      inference('sup-', [status(thm)], ['89', '90'])).
% 48.20/48.42  thf('92', plain, ((v2_pre_topc @ sk_A)),
% 48.20/48.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 48.20/48.42  thf('93', plain, ((l1_pre_topc @ sk_A)),
% 48.20/48.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 48.20/48.42  thf('94', plain,
% 48.20/48.42      (((v2_struct_0 @ sk_A)
% 48.20/48.42        | ((k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B_1))
% 48.20/48.42            = (k6_partfun1 @ (u1_struct_0 @ sk_A))))),
% 48.20/48.42      inference('demod', [status(thm)], ['91', '92', '93'])).
% 48.20/48.42  thf('95', plain, (~ (v2_struct_0 @ sk_A)),
% 48.20/48.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 48.20/48.42  thf('96', plain,
% 48.20/48.42      (((k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B_1))
% 48.20/48.42         = (k6_partfun1 @ (u1_struct_0 @ sk_A)))),
% 48.20/48.42      inference('clc', [status(thm)], ['94', '95'])).
% 48.20/48.42  thf('97', plain, ((v1_funct_1 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)))),
% 48.20/48.42      inference('demod', [status(thm)], ['88', '96'])).
% 48.20/48.42  thf('98', plain,
% 48.20/48.42      ((m1_subset_1 @ (u1_struct_0 @ sk_B_1) @ 
% 48.20/48.42        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 48.20/48.42      inference('demod', [status(thm)], ['3', '4'])).
% 48.20/48.42  thf('99', plain,
% 48.20/48.42      (![X19 : $i, X20 : $i]:
% 48.20/48.42         (~ (l1_pre_topc @ X19)
% 48.20/48.42          | ~ (v2_pre_topc @ X19)
% 48.20/48.42          | (v2_struct_0 @ X19)
% 48.20/48.42          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 48.20/48.42          | (v1_funct_2 @ (k7_tmap_1 @ X19 @ X20) @ (u1_struct_0 @ X19) @ 
% 48.20/48.42             (u1_struct_0 @ (k6_tmap_1 @ X19 @ X20))))),
% 48.20/48.42      inference('cnf', [status(esa)], [dt_k7_tmap_1])).
% 48.20/48.42  thf('100', plain,
% 48.20/48.42      (((v1_funct_2 @ (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B_1)) @ 
% 48.20/48.42         (u1_struct_0 @ sk_A) @ 
% 48.20/48.42         (u1_struct_0 @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B_1))))
% 48.20/48.42        | (v2_struct_0 @ sk_A)
% 48.20/48.42        | ~ (v2_pre_topc @ sk_A)
% 48.20/48.42        | ~ (l1_pre_topc @ sk_A))),
% 48.20/48.42      inference('sup-', [status(thm)], ['98', '99'])).
% 48.20/48.42  thf('101', plain,
% 48.20/48.42      (((k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B_1))
% 48.20/48.42         = (k6_partfun1 @ (u1_struct_0 @ sk_A)))),
% 48.20/48.42      inference('clc', [status(thm)], ['94', '95'])).
% 48.20/48.42  thf('102', plain,
% 48.20/48.42      (((u1_struct_0 @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B_1)))
% 48.20/48.42         = (u1_struct_0 @ sk_A))),
% 48.20/48.42      inference('clc', [status(thm)], ['10', '11'])).
% 48.20/48.42  thf('103', plain, ((v2_pre_topc @ sk_A)),
% 48.20/48.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 48.20/48.42  thf('104', plain, ((l1_pre_topc @ sk_A)),
% 48.20/48.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 48.20/48.42  thf('105', plain,
% 48.20/48.42      (((v1_funct_2 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 48.20/48.42         (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))
% 48.20/48.42        | (v2_struct_0 @ sk_A))),
% 48.20/48.42      inference('demod', [status(thm)], ['100', '101', '102', '103', '104'])).
% 48.20/48.42  thf('106', plain, (~ (v2_struct_0 @ sk_A)),
% 48.20/48.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 48.20/48.42  thf('107', plain,
% 48.20/48.42      ((v1_funct_2 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 48.20/48.42        (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))),
% 48.20/48.42      inference('clc', [status(thm)], ['105', '106'])).
% 48.20/48.42  thf('108', plain,
% 48.20/48.42      (![X0 : $i, X1 : $i, X2 : $i]:
% 48.20/48.42         (~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ X0)))
% 48.20/48.42          | ~ (v1_funct_2 @ X2 @ X1 @ X0)
% 48.20/48.42          | ~ (v1_funct_1 @ X2)
% 48.20/48.42          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 48.20/48.42          | (v1_xboole_0 @ X0)
% 48.20/48.42          | (r1_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ X1 @ 
% 48.20/48.42             X0 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 48.20/48.42             (k6_partfun1 @ (u1_struct_0 @ sk_A))))),
% 48.20/48.42      inference('demod', [status(thm)], ['80', '97', '107'])).
% 48.20/48.42  thf('109', plain,
% 48.20/48.42      (((r1_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 48.20/48.42         (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 48.20/48.42         (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 48.20/48.42         (k6_partfun1 @ (u1_struct_0 @ sk_A)))
% 48.20/48.42        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 48.20/48.42        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 48.20/48.42        | ~ (v1_funct_1 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)))
% 48.20/48.42        | ~ (v1_funct_2 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 48.20/48.42             (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 48.20/48.42      inference('sup-', [status(thm)], ['77', '108'])).
% 48.20/48.42  thf('110', plain, ((v1_funct_1 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)))),
% 48.20/48.42      inference('demod', [status(thm)], ['88', '96'])).
% 48.20/48.42  thf('111', plain,
% 48.20/48.42      ((v1_funct_2 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 48.20/48.42        (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))),
% 48.20/48.42      inference('clc', [status(thm)], ['105', '106'])).
% 48.20/48.42  thf('112', plain,
% 48.20/48.42      (((r1_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 48.20/48.42         (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 48.20/48.42         (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 48.20/48.42         (k6_partfun1 @ (u1_struct_0 @ sk_A)))
% 48.20/48.42        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 48.20/48.42        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 48.20/48.42      inference('demod', [status(thm)], ['109', '110', '111'])).
% 48.20/48.42  thf('113', plain,
% 48.20/48.42      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 48.20/48.42        | (r1_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 48.20/48.42           (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 48.20/48.42           (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 48.20/48.42           (k6_partfun1 @ (u1_struct_0 @ sk_A))))),
% 48.20/48.42      inference('simplify', [status(thm)], ['112'])).
% 48.20/48.42  thf('114', plain,
% 48.20/48.42      ((m1_subset_1 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 48.20/48.42        (k1_zfmisc_1 @ 
% 48.20/48.42         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))))),
% 48.20/48.42      inference('clc', [status(thm)], ['75', '76'])).
% 48.20/48.42  thf('115', plain,
% 48.20/48.42      (((u1_struct_0 @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B_1)))
% 48.20/48.42         = (u1_struct_0 @ sk_A))),
% 48.20/48.42      inference('clc', [status(thm)], ['10', '11'])).
% 48.20/48.42  thf('116', plain,
% 48.20/48.42      (((k8_tmap_1 @ sk_A @ sk_B_1)
% 48.20/48.42         = (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B_1)))),
% 48.20/48.42      inference('clc', [status(thm)], ['49', '50'])).
% 48.20/48.42  thf('117', plain,
% 48.20/48.42      (((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B_1)) = (u1_struct_0 @ sk_A))),
% 48.20/48.42      inference('demod', [status(thm)], ['115', '116'])).
% 48.20/48.42  thf(d12_tmap_1, axiom,
% 48.20/48.42    (![A:$i]:
% 48.20/48.42     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 48.20/48.42       ( ![B:$i]:
% 48.20/48.42         ( ( m1_pre_topc @ B @ A ) =>
% 48.20/48.42           ( ![C:$i]:
% 48.20/48.42             ( ( ( v1_funct_1 @ C ) & 
% 48.20/48.42                 ( v1_funct_2 @
% 48.20/48.42                   C @ ( u1_struct_0 @ A ) @ 
% 48.20/48.42                   ( u1_struct_0 @ ( k8_tmap_1 @ A @ B ) ) ) & 
% 48.20/48.42                 ( m1_subset_1 @
% 48.20/48.42                   C @ 
% 48.20/48.42                   ( k1_zfmisc_1 @
% 48.20/48.42                     ( k2_zfmisc_1 @
% 48.20/48.42                       ( u1_struct_0 @ A ) @ 
% 48.20/48.42                       ( u1_struct_0 @ ( k8_tmap_1 @ A @ B ) ) ) ) ) ) =>
% 48.20/48.42               ( ( ( C ) = ( k9_tmap_1 @ A @ B ) ) <=>
% 48.20/48.42                 ( ![D:$i]:
% 48.20/48.42                   ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 48.20/48.42                     ( ( ( D ) = ( u1_struct_0 @ B ) ) =>
% 48.20/48.42                       ( r1_funct_2 @
% 48.20/48.42                         ( u1_struct_0 @ A ) @ 
% 48.20/48.42                         ( u1_struct_0 @ ( k8_tmap_1 @ A @ B ) ) @ 
% 48.20/48.42                         ( u1_struct_0 @ A ) @ 
% 48.20/48.42                         ( u1_struct_0 @ ( k6_tmap_1 @ A @ D ) ) @ C @ 
% 48.20/48.42                         ( k7_tmap_1 @ A @ D ) ) ) ) ) ) ) ) ) ) ))).
% 48.20/48.42  thf('118', plain,
% 48.20/48.42      (![X15 : $i, X16 : $i, X17 : $i]:
% 48.20/48.42         (~ (m1_pre_topc @ X15 @ X16)
% 48.20/48.42          | ((sk_D_1 @ X17 @ X15 @ X16) = (u1_struct_0 @ X15))
% 48.20/48.42          | ((X17) = (k9_tmap_1 @ X16 @ X15))
% 48.20/48.42          | ~ (m1_subset_1 @ X17 @ 
% 48.20/48.42               (k1_zfmisc_1 @ 
% 48.20/48.42                (k2_zfmisc_1 @ (u1_struct_0 @ X16) @ 
% 48.20/48.42                 (u1_struct_0 @ (k8_tmap_1 @ X16 @ X15)))))
% 48.20/48.42          | ~ (v1_funct_2 @ X17 @ (u1_struct_0 @ X16) @ 
% 48.20/48.42               (u1_struct_0 @ (k8_tmap_1 @ X16 @ X15)))
% 48.20/48.42          | ~ (v1_funct_1 @ X17)
% 48.20/48.42          | ~ (l1_pre_topc @ X16)
% 48.20/48.42          | ~ (v2_pre_topc @ X16)
% 48.20/48.42          | (v2_struct_0 @ X16))),
% 48.20/48.42      inference('cnf', [status(esa)], [d12_tmap_1])).
% 48.20/48.42  thf('119', plain,
% 48.20/48.42      (![X0 : $i]:
% 48.20/48.42         (~ (m1_subset_1 @ X0 @ 
% 48.20/48.42             (k1_zfmisc_1 @ 
% 48.20/48.42              (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))))
% 48.20/48.42          | (v2_struct_0 @ sk_A)
% 48.20/48.42          | ~ (v2_pre_topc @ sk_A)
% 48.20/48.42          | ~ (l1_pre_topc @ sk_A)
% 48.20/48.42          | ~ (v1_funct_1 @ X0)
% 48.20/48.42          | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_A) @ 
% 48.20/48.42               (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B_1)))
% 48.20/48.42          | ((X0) = (k9_tmap_1 @ sk_A @ sk_B_1))
% 48.20/48.42          | ((sk_D_1 @ X0 @ sk_B_1 @ sk_A) = (u1_struct_0 @ sk_B_1))
% 48.20/48.42          | ~ (m1_pre_topc @ sk_B_1 @ sk_A))),
% 48.20/48.42      inference('sup-', [status(thm)], ['117', '118'])).
% 48.20/48.42  thf('120', plain, ((v2_pre_topc @ sk_A)),
% 48.20/48.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 48.20/48.42  thf('121', plain, ((l1_pre_topc @ sk_A)),
% 48.20/48.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 48.20/48.42  thf('122', plain,
% 48.20/48.42      (((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B_1)) = (u1_struct_0 @ sk_A))),
% 48.20/48.42      inference('demod', [status(thm)], ['115', '116'])).
% 48.20/48.42  thf('123', plain, ((m1_pre_topc @ sk_B_1 @ sk_A)),
% 48.20/48.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 48.20/48.42  thf('124', plain,
% 48.20/48.42      (![X0 : $i]:
% 48.20/48.42         (~ (m1_subset_1 @ X0 @ 
% 48.20/48.42             (k1_zfmisc_1 @ 
% 48.20/48.42              (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))))
% 48.20/48.42          | (v2_struct_0 @ sk_A)
% 48.20/48.42          | ~ (v1_funct_1 @ X0)
% 48.20/48.42          | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))
% 48.20/48.42          | ((X0) = (k9_tmap_1 @ sk_A @ sk_B_1))
% 48.20/48.42          | ((sk_D_1 @ X0 @ sk_B_1 @ sk_A) = (u1_struct_0 @ sk_B_1)))),
% 48.20/48.42      inference('demod', [status(thm)], ['119', '120', '121', '122', '123'])).
% 48.20/48.42  thf('125', plain,
% 48.20/48.42      ((((sk_D_1 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ sk_B_1 @ sk_A)
% 48.20/48.42          = (u1_struct_0 @ sk_B_1))
% 48.20/48.42        | ((k6_partfun1 @ (u1_struct_0 @ sk_A)) = (k9_tmap_1 @ sk_A @ sk_B_1))
% 48.20/48.42        | ~ (v1_funct_2 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 48.20/48.42             (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))
% 48.20/48.42        | ~ (v1_funct_1 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)))
% 48.20/48.42        | (v2_struct_0 @ sk_A))),
% 48.20/48.42      inference('sup-', [status(thm)], ['114', '124'])).
% 48.20/48.42  thf('126', plain,
% 48.20/48.42      ((v1_funct_2 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 48.20/48.42        (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))),
% 48.20/48.42      inference('clc', [status(thm)], ['105', '106'])).
% 48.20/48.42  thf('127', plain, ((v1_funct_1 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)))),
% 48.20/48.42      inference('demod', [status(thm)], ['88', '96'])).
% 48.20/48.42  thf('128', plain,
% 48.20/48.42      ((((sk_D_1 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ sk_B_1 @ sk_A)
% 48.20/48.42          = (u1_struct_0 @ sk_B_1))
% 48.20/48.42        | ((k6_partfun1 @ (u1_struct_0 @ sk_A)) = (k9_tmap_1 @ sk_A @ sk_B_1))
% 48.20/48.42        | (v2_struct_0 @ sk_A))),
% 48.20/48.42      inference('demod', [status(thm)], ['125', '126', '127'])).
% 48.20/48.42  thf('129', plain, (~ (v2_struct_0 @ sk_A)),
% 48.20/48.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 48.20/48.42  thf('130', plain,
% 48.20/48.42      ((((k6_partfun1 @ (u1_struct_0 @ sk_A)) = (k9_tmap_1 @ sk_A @ sk_B_1))
% 48.20/48.42        | ((sk_D_1 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ sk_B_1 @ sk_A)
% 48.20/48.42            = (u1_struct_0 @ sk_B_1)))),
% 48.20/48.42      inference('clc', [status(thm)], ['128', '129'])).
% 48.20/48.42  thf('131', plain,
% 48.20/48.42      ((((k6_partfun1 @ (u1_struct_0 @ sk_A)) = (k9_tmap_1 @ sk_A @ sk_B_1))
% 48.20/48.42        | ((sk_D_1 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ sk_B_1 @ sk_A)
% 48.20/48.42            = (u1_struct_0 @ sk_B_1)))),
% 48.20/48.42      inference('clc', [status(thm)], ['128', '129'])).
% 48.20/48.42  thf('132', plain,
% 48.20/48.42      (![X15 : $i, X16 : $i, X17 : $i]:
% 48.20/48.42         (~ (m1_pre_topc @ X15 @ X16)
% 48.20/48.42          | ~ (r1_funct_2 @ (u1_struct_0 @ X16) @ 
% 48.20/48.42               (u1_struct_0 @ (k8_tmap_1 @ X16 @ X15)) @ (u1_struct_0 @ X16) @ 
% 48.20/48.42               (u1_struct_0 @ (k6_tmap_1 @ X16 @ (sk_D_1 @ X17 @ X15 @ X16))) @ 
% 48.20/48.42               X17 @ (k7_tmap_1 @ X16 @ (sk_D_1 @ X17 @ X15 @ X16)))
% 48.20/48.42          | ((X17) = (k9_tmap_1 @ X16 @ X15))
% 48.20/48.42          | ~ (m1_subset_1 @ X17 @ 
% 48.20/48.42               (k1_zfmisc_1 @ 
% 48.20/48.42                (k2_zfmisc_1 @ (u1_struct_0 @ X16) @ 
% 48.20/48.42                 (u1_struct_0 @ (k8_tmap_1 @ X16 @ X15)))))
% 48.20/48.42          | ~ (v1_funct_2 @ X17 @ (u1_struct_0 @ X16) @ 
% 48.20/48.42               (u1_struct_0 @ (k8_tmap_1 @ X16 @ X15)))
% 48.20/48.42          | ~ (v1_funct_1 @ X17)
% 48.20/48.42          | ~ (l1_pre_topc @ X16)
% 48.20/48.42          | ~ (v2_pre_topc @ X16)
% 48.20/48.42          | (v2_struct_0 @ X16))),
% 48.20/48.42      inference('cnf', [status(esa)], [d12_tmap_1])).
% 48.20/48.42  thf('133', plain,
% 48.20/48.42      ((~ (r1_funct_2 @ (u1_struct_0 @ sk_A) @ 
% 48.20/48.42           (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B_1)) @ 
% 48.20/48.42           (u1_struct_0 @ sk_A) @ 
% 48.20/48.42           (u1_struct_0 @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B_1))) @ 
% 48.20/48.42           (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 48.20/48.42           (k7_tmap_1 @ sk_A @ 
% 48.20/48.42            (sk_D_1 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ sk_B_1 @ sk_A)))
% 48.20/48.42        | ((k6_partfun1 @ (u1_struct_0 @ sk_A)) = (k9_tmap_1 @ sk_A @ sk_B_1))
% 48.20/48.42        | (v2_struct_0 @ sk_A)
% 48.20/48.42        | ~ (v2_pre_topc @ sk_A)
% 48.20/48.42        | ~ (l1_pre_topc @ sk_A)
% 48.20/48.42        | ~ (v1_funct_1 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)))
% 48.20/48.42        | ~ (v1_funct_2 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 48.20/48.42             (u1_struct_0 @ sk_A) @ (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B_1)))
% 48.20/48.42        | ~ (m1_subset_1 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 48.20/48.42             (k1_zfmisc_1 @ 
% 48.20/48.42              (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 48.20/48.42               (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B_1)))))
% 48.20/48.42        | ((k6_partfun1 @ (u1_struct_0 @ sk_A)) = (k9_tmap_1 @ sk_A @ sk_B_1))
% 48.20/48.42        | ~ (m1_pre_topc @ sk_B_1 @ sk_A))),
% 48.20/48.42      inference('sup-', [status(thm)], ['131', '132'])).
% 48.20/48.42  thf('134', plain,
% 48.20/48.42      (((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B_1)) = (u1_struct_0 @ sk_A))),
% 48.20/48.42      inference('demod', [status(thm)], ['115', '116'])).
% 48.20/48.42  thf('135', plain,
% 48.20/48.42      (((k8_tmap_1 @ sk_A @ sk_B_1)
% 48.20/48.42         = (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B_1)))),
% 48.20/48.42      inference('clc', [status(thm)], ['49', '50'])).
% 48.20/48.42  thf('136', plain,
% 48.20/48.42      (((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B_1)) = (u1_struct_0 @ sk_A))),
% 48.20/48.42      inference('demod', [status(thm)], ['115', '116'])).
% 48.20/48.42  thf('137', plain, ((v2_pre_topc @ sk_A)),
% 48.20/48.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 48.20/48.42  thf('138', plain, ((l1_pre_topc @ sk_A)),
% 48.20/48.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 48.20/48.42  thf('139', plain, ((v1_funct_1 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)))),
% 48.20/48.42      inference('demod', [status(thm)], ['88', '96'])).
% 48.20/48.42  thf('140', plain,
% 48.20/48.42      (((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B_1)) = (u1_struct_0 @ sk_A))),
% 48.20/48.42      inference('demod', [status(thm)], ['115', '116'])).
% 48.20/48.42  thf('141', plain,
% 48.20/48.42      ((v1_funct_2 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 48.20/48.42        (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))),
% 48.20/48.42      inference('clc', [status(thm)], ['105', '106'])).
% 48.20/48.42  thf('142', plain,
% 48.20/48.42      (((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B_1)) = (u1_struct_0 @ sk_A))),
% 48.20/48.42      inference('demod', [status(thm)], ['115', '116'])).
% 48.20/48.42  thf('143', plain,
% 48.20/48.42      ((m1_subset_1 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 48.20/48.42        (k1_zfmisc_1 @ 
% 48.20/48.42         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))))),
% 48.20/48.42      inference('clc', [status(thm)], ['75', '76'])).
% 48.20/48.42  thf('144', plain, ((m1_pre_topc @ sk_B_1 @ sk_A)),
% 48.20/48.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 48.20/48.42  thf('145', plain,
% 48.20/48.42      ((~ (r1_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 48.20/48.42           (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 48.20/48.42           (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 48.20/48.42           (k7_tmap_1 @ sk_A @ 
% 48.20/48.42            (sk_D_1 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ sk_B_1 @ sk_A)))
% 48.20/48.42        | ((k6_partfun1 @ (u1_struct_0 @ sk_A)) = (k9_tmap_1 @ sk_A @ sk_B_1))
% 48.20/48.42        | (v2_struct_0 @ sk_A)
% 48.20/48.42        | ((k6_partfun1 @ (u1_struct_0 @ sk_A)) = (k9_tmap_1 @ sk_A @ sk_B_1)))),
% 48.20/48.42      inference('demod', [status(thm)],
% 48.20/48.42                ['133', '134', '135', '136', '137', '138', '139', '140', 
% 48.20/48.42                 '141', '142', '143', '144'])).
% 48.20/48.42  thf('146', plain,
% 48.20/48.42      (((v2_struct_0 @ sk_A)
% 48.20/48.42        | ((k6_partfun1 @ (u1_struct_0 @ sk_A)) = (k9_tmap_1 @ sk_A @ sk_B_1))
% 48.20/48.42        | ~ (r1_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 48.20/48.42             (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 48.20/48.42             (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 48.20/48.42             (k7_tmap_1 @ sk_A @ 
% 48.20/48.42              (sk_D_1 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ sk_B_1 @ sk_A))))),
% 48.20/48.42      inference('simplify', [status(thm)], ['145'])).
% 48.20/48.42  thf('147', plain, (~ (v2_struct_0 @ sk_A)),
% 48.20/48.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 48.20/48.42  thf('148', plain,
% 48.20/48.42      ((~ (r1_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 48.20/48.42           (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 48.20/48.42           (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 48.20/48.42           (k7_tmap_1 @ sk_A @ 
% 48.20/48.42            (sk_D_1 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ sk_B_1 @ sk_A)))
% 48.20/48.42        | ((k6_partfun1 @ (u1_struct_0 @ sk_A)) = (k9_tmap_1 @ sk_A @ sk_B_1)))),
% 48.20/48.42      inference('clc', [status(thm)], ['146', '147'])).
% 48.20/48.42  thf('149', plain,
% 48.20/48.42      ((~ (r1_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 48.20/48.42           (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 48.20/48.42           (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 48.20/48.42           (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B_1)))
% 48.20/48.42        | ((k6_partfun1 @ (u1_struct_0 @ sk_A)) = (k9_tmap_1 @ sk_A @ sk_B_1))
% 48.20/48.42        | ((k6_partfun1 @ (u1_struct_0 @ sk_A)) = (k9_tmap_1 @ sk_A @ sk_B_1)))),
% 48.20/48.42      inference('sup-', [status(thm)], ['130', '148'])).
% 48.20/48.42  thf('150', plain,
% 48.20/48.42      (((k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B_1))
% 48.20/48.42         = (k6_partfun1 @ (u1_struct_0 @ sk_A)))),
% 48.20/48.42      inference('clc', [status(thm)], ['94', '95'])).
% 48.20/48.42  thf('151', plain,
% 48.20/48.42      ((~ (r1_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 48.20/48.42           (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 48.20/48.42           (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 48.20/48.42           (k6_partfun1 @ (u1_struct_0 @ sk_A)))
% 48.20/48.42        | ((k6_partfun1 @ (u1_struct_0 @ sk_A)) = (k9_tmap_1 @ sk_A @ sk_B_1))
% 48.20/48.42        | ((k6_partfun1 @ (u1_struct_0 @ sk_A)) = (k9_tmap_1 @ sk_A @ sk_B_1)))),
% 48.20/48.42      inference('demod', [status(thm)], ['149', '150'])).
% 48.20/48.42  thf('152', plain,
% 48.20/48.42      ((((k6_partfun1 @ (u1_struct_0 @ sk_A)) = (k9_tmap_1 @ sk_A @ sk_B_1))
% 48.20/48.42        | ~ (r1_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 48.20/48.42             (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 48.20/48.42             (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 48.20/48.42             (k6_partfun1 @ (u1_struct_0 @ sk_A))))),
% 48.20/48.42      inference('simplify', [status(thm)], ['151'])).
% 48.20/48.42  thf('153', plain,
% 48.20/48.42      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 48.20/48.42        | ((k6_partfun1 @ (u1_struct_0 @ sk_A)) = (k9_tmap_1 @ sk_A @ sk_B_1)))),
% 48.20/48.42      inference('sup-', [status(thm)], ['113', '152'])).
% 48.20/48.42  thf('154', plain,
% 48.20/48.42      (~ (r1_tmap_1 @ sk_B_1 @ (k8_tmap_1 @ sk_A @ sk_B_1) @ 
% 48.20/48.42          (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B_1) @ 
% 48.20/48.42           (k9_tmap_1 @ sk_A @ sk_B_1) @ sk_B_1) @ 
% 48.20/48.42          sk_C)),
% 48.20/48.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 48.20/48.42  thf('155', plain,
% 48.20/48.42      ((~ (r1_tmap_1 @ sk_B_1 @ (k8_tmap_1 @ sk_A @ sk_B_1) @ 
% 48.20/48.42           (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B_1) @ 
% 48.20/48.42            (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ sk_B_1) @ 
% 48.20/48.42           sk_C)
% 48.20/48.42        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 48.20/48.42      inference('sup-', [status(thm)], ['153', '154'])).
% 48.20/48.42  thf('156', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_B_1))),
% 48.20/48.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 48.20/48.42  thf('157', plain,
% 48.20/48.42      ((m1_subset_1 @ (u1_struct_0 @ sk_B_1) @ 
% 48.20/48.42        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 48.20/48.42      inference('demod', [status(thm)], ['3', '4'])).
% 48.20/48.42  thf(t110_tmap_1, axiom,
% 48.20/48.42    (![A:$i]:
% 48.20/48.42     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 48.20/48.42       ( ![B:$i]:
% 48.20/48.42         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 48.20/48.42           ( ![C:$i]:
% 48.20/48.42             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 48.20/48.42               ( ( ( u1_struct_0 @ C ) = ( B ) ) =>
% 48.20/48.42                 ( ![D:$i]:
% 48.20/48.42                   ( ( m1_subset_1 @ D @ ( u1_struct_0 @ C ) ) =>
% 48.20/48.42                     ( r1_tmap_1 @
% 48.20/48.42                       C @ ( k6_tmap_1 @ A @ B ) @ 
% 48.20/48.42                       ( k2_tmap_1 @
% 48.20/48.42                         A @ ( k6_tmap_1 @ A @ B ) @ ( k7_tmap_1 @ A @ B ) @ C ) @ 
% 48.20/48.42                       D ) ) ) ) ) ) ) ) ))).
% 48.20/48.42  thf('158', plain,
% 48.20/48.42      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 48.20/48.42         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X26)))
% 48.20/48.42          | ((u1_struct_0 @ X27) != (X25))
% 48.20/48.42          | ~ (m1_subset_1 @ X28 @ (u1_struct_0 @ X27))
% 48.20/48.42          | (r1_tmap_1 @ X27 @ (k6_tmap_1 @ X26 @ X25) @ 
% 48.20/48.42             (k2_tmap_1 @ X26 @ (k6_tmap_1 @ X26 @ X25) @ 
% 48.20/48.42              (k7_tmap_1 @ X26 @ X25) @ X27) @ 
% 48.20/48.42             X28)
% 48.20/48.42          | ~ (m1_pre_topc @ X27 @ X26)
% 48.20/48.42          | (v2_struct_0 @ X27)
% 48.20/48.42          | ~ (l1_pre_topc @ X26)
% 48.20/48.42          | ~ (v2_pre_topc @ X26)
% 48.20/48.42          | (v2_struct_0 @ X26))),
% 48.20/48.42      inference('cnf', [status(esa)], [t110_tmap_1])).
% 48.20/48.42  thf('159', plain,
% 48.20/48.42      (![X26 : $i, X27 : $i, X28 : $i]:
% 48.20/48.42         ((v2_struct_0 @ X26)
% 48.20/48.42          | ~ (v2_pre_topc @ X26)
% 48.20/48.42          | ~ (l1_pre_topc @ X26)
% 48.20/48.42          | (v2_struct_0 @ X27)
% 48.20/48.42          | ~ (m1_pre_topc @ X27 @ X26)
% 48.20/48.42          | (r1_tmap_1 @ X27 @ (k6_tmap_1 @ X26 @ (u1_struct_0 @ X27)) @ 
% 48.20/48.42             (k2_tmap_1 @ X26 @ (k6_tmap_1 @ X26 @ (u1_struct_0 @ X27)) @ 
% 48.20/48.42              (k7_tmap_1 @ X26 @ (u1_struct_0 @ X27)) @ X27) @ 
% 48.20/48.42             X28)
% 48.20/48.42          | ~ (m1_subset_1 @ X28 @ (u1_struct_0 @ X27))
% 48.20/48.42          | ~ (m1_subset_1 @ (u1_struct_0 @ X27) @ 
% 48.20/48.42               (k1_zfmisc_1 @ (u1_struct_0 @ X26))))),
% 48.20/48.42      inference('simplify', [status(thm)], ['158'])).
% 48.20/48.42  thf('160', plain,
% 48.20/48.42      (![X0 : $i]:
% 48.20/48.42         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B_1))
% 48.20/48.42          | (r1_tmap_1 @ sk_B_1 @ 
% 48.20/48.42             (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B_1)) @ 
% 48.20/48.42             (k2_tmap_1 @ sk_A @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B_1)) @ 
% 48.20/48.42              (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B_1)) @ sk_B_1) @ 
% 48.20/48.42             X0)
% 48.20/48.42          | ~ (m1_pre_topc @ sk_B_1 @ sk_A)
% 48.20/48.42          | (v2_struct_0 @ sk_B_1)
% 48.20/48.42          | ~ (l1_pre_topc @ sk_A)
% 48.20/48.42          | ~ (v2_pre_topc @ sk_A)
% 48.20/48.42          | (v2_struct_0 @ sk_A))),
% 48.20/48.42      inference('sup-', [status(thm)], ['157', '159'])).
% 48.20/48.42  thf('161', plain,
% 48.20/48.42      (((k8_tmap_1 @ sk_A @ sk_B_1)
% 48.20/48.42         = (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B_1)))),
% 48.20/48.42      inference('clc', [status(thm)], ['49', '50'])).
% 48.20/48.42  thf('162', plain,
% 48.20/48.42      (((k8_tmap_1 @ sk_A @ sk_B_1)
% 48.20/48.42         = (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B_1)))),
% 48.20/48.42      inference('clc', [status(thm)], ['49', '50'])).
% 48.20/48.42  thf('163', plain,
% 48.20/48.42      (((k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B_1))
% 48.20/48.42         = (k6_partfun1 @ (u1_struct_0 @ sk_A)))),
% 48.20/48.42      inference('clc', [status(thm)], ['94', '95'])).
% 48.20/48.42  thf('164', plain, ((m1_pre_topc @ sk_B_1 @ sk_A)),
% 48.20/48.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 48.20/48.42  thf('165', plain, ((l1_pre_topc @ sk_A)),
% 48.20/48.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 48.20/48.42  thf('166', plain, ((v2_pre_topc @ sk_A)),
% 48.20/48.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 48.20/48.42  thf('167', plain,
% 48.20/48.42      (![X0 : $i]:
% 48.20/48.42         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B_1))
% 48.20/48.42          | (r1_tmap_1 @ sk_B_1 @ (k8_tmap_1 @ sk_A @ sk_B_1) @ 
% 48.20/48.42             (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B_1) @ 
% 48.20/48.42              (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ sk_B_1) @ 
% 48.20/48.42             X0)
% 48.20/48.42          | (v2_struct_0 @ sk_B_1)
% 48.20/48.42          | (v2_struct_0 @ sk_A))),
% 48.20/48.42      inference('demod', [status(thm)],
% 48.20/48.42                ['160', '161', '162', '163', '164', '165', '166'])).
% 48.20/48.42  thf('168', plain,
% 48.20/48.42      (((v2_struct_0 @ sk_A)
% 48.20/48.42        | (v2_struct_0 @ sk_B_1)
% 48.20/48.42        | (r1_tmap_1 @ sk_B_1 @ (k8_tmap_1 @ sk_A @ sk_B_1) @ 
% 48.20/48.42           (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B_1) @ 
% 48.20/48.42            (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ sk_B_1) @ 
% 48.20/48.42           sk_C))),
% 48.20/48.42      inference('sup-', [status(thm)], ['156', '167'])).
% 48.20/48.42  thf('169', plain, (~ (v2_struct_0 @ sk_A)),
% 48.20/48.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 48.20/48.42  thf('170', plain,
% 48.20/48.42      (((r1_tmap_1 @ sk_B_1 @ (k8_tmap_1 @ sk_A @ sk_B_1) @ 
% 48.20/48.42         (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B_1) @ 
% 48.20/48.42          (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ sk_B_1) @ 
% 48.20/48.42         sk_C)
% 48.20/48.42        | (v2_struct_0 @ sk_B_1))),
% 48.20/48.42      inference('clc', [status(thm)], ['168', '169'])).
% 48.20/48.42  thf('171', plain, (~ (v2_struct_0 @ sk_B_1)),
% 48.20/48.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 48.20/48.42  thf('172', plain,
% 48.20/48.42      ((r1_tmap_1 @ sk_B_1 @ (k8_tmap_1 @ sk_A @ sk_B_1) @ 
% 48.20/48.42        (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B_1) @ 
% 48.20/48.42         (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ sk_B_1) @ 
% 48.20/48.42        sk_C)),
% 48.20/48.42      inference('clc', [status(thm)], ['170', '171'])).
% 48.20/48.42  thf('173', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 48.20/48.42      inference('demod', [status(thm)], ['155', '172'])).
% 48.20/48.42  thf(fc2_struct_0, axiom,
% 48.20/48.42    (![A:$i]:
% 48.20/48.42     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 48.20/48.42       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 48.20/48.42  thf('174', plain,
% 48.20/48.42      (![X2 : $i]:
% 48.20/48.42         (~ (v1_xboole_0 @ (u1_struct_0 @ X2))
% 48.20/48.42          | ~ (l1_struct_0 @ X2)
% 48.20/48.42          | (v2_struct_0 @ X2))),
% 48.20/48.42      inference('cnf', [status(esa)], [fc2_struct_0])).
% 48.20/48.42  thf('175', plain, (((v2_struct_0 @ sk_A) | ~ (l1_struct_0 @ sk_A))),
% 48.20/48.42      inference('sup-', [status(thm)], ['173', '174'])).
% 48.20/48.42  thf('176', plain, ((l1_pre_topc @ sk_A)),
% 48.20/48.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 48.20/48.42  thf(dt_l1_pre_topc, axiom,
% 48.20/48.42    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 48.20/48.42  thf('177', plain, (![X0 : $i]: ((l1_struct_0 @ X0) | ~ (l1_pre_topc @ X0))),
% 48.20/48.42      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 48.20/48.42  thf('178', plain, ((l1_struct_0 @ sk_A)),
% 48.20/48.42      inference('sup-', [status(thm)], ['176', '177'])).
% 48.20/48.42  thf('179', plain, ((v2_struct_0 @ sk_A)),
% 48.20/48.42      inference('demod', [status(thm)], ['175', '178'])).
% 48.20/48.42  thf('180', plain, ($false), inference('demod', [status(thm)], ['0', '179'])).
% 48.20/48.42  
% 48.20/48.42  % SZS output end Refutation
% 48.20/48.42  
% 48.20/48.43  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
