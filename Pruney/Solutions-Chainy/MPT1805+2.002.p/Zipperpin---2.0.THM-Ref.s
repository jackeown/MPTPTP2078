%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.2nxREFJlRF

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:11:01 EST 2020

% Result     : Theorem 0.80s
% Output     : Refutation 0.80s
% Verified   : 
% Statistics : Number of formulae       :  250 (3174 expanded)
%              Number of leaves         :   36 ( 929 expanded)
%              Depth                    :   24
%              Number of atoms          : 3007 (113316 expanded)
%              Number of equality atoms :   55 ( 362 expanded)
%              Maximal formula depth    :   23 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k7_tmap_1_type,type,(
    k7_tmap_1: $i > $i > $i )).

thf(k2_tmap_1_type,type,(
    k2_tmap_1: $i > $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k9_tmap_1_type,type,(
    k9_tmap_1: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v5_pre_topc_type,type,(
    v5_pre_topc: $i > $i > $i > $o )).

thf(k6_tmap_1_type,type,(
    k6_tmap_1: $i > $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k8_tmap_1_type,type,(
    k8_tmap_1: $i > $i > $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(r1_funct_2_type,type,(
    r1_funct_2: $i > $i > $i > $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(t121_tmap_1,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( m1_pre_topc @ B @ A ) )
         => ( ( v1_funct_1 @ ( k2_tmap_1 @ A @ ( k8_tmap_1 @ A @ B ) @ ( k9_tmap_1 @ A @ B ) @ B ) )
            & ( v1_funct_2 @ ( k2_tmap_1 @ A @ ( k8_tmap_1 @ A @ B ) @ ( k9_tmap_1 @ A @ B ) @ B ) @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ ( k8_tmap_1 @ A @ B ) ) )
            & ( v5_pre_topc @ ( k2_tmap_1 @ A @ ( k8_tmap_1 @ A @ B ) @ ( k9_tmap_1 @ A @ B ) @ B ) @ B @ ( k8_tmap_1 @ A @ B ) )
            & ( m1_subset_1 @ ( k2_tmap_1 @ A @ ( k8_tmap_1 @ A @ B ) @ ( k9_tmap_1 @ A @ B ) @ B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ ( k8_tmap_1 @ A @ B ) ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( ~ ( v2_struct_0 @ B )
              & ( m1_pre_topc @ B @ A ) )
           => ( ( v1_funct_1 @ ( k2_tmap_1 @ A @ ( k8_tmap_1 @ A @ B ) @ ( k9_tmap_1 @ A @ B ) @ B ) )
              & ( v1_funct_2 @ ( k2_tmap_1 @ A @ ( k8_tmap_1 @ A @ B ) @ ( k9_tmap_1 @ A @ B ) @ B ) @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ ( k8_tmap_1 @ A @ B ) ) )
              & ( v5_pre_topc @ ( k2_tmap_1 @ A @ ( k8_tmap_1 @ A @ B ) @ ( k9_tmap_1 @ A @ B ) @ B ) @ B @ ( k8_tmap_1 @ A @ B ) )
              & ( m1_subset_1 @ ( k2_tmap_1 @ A @ ( k8_tmap_1 @ A @ B ) @ ( k9_tmap_1 @ A @ B ) @ B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ ( k8_tmap_1 @ A @ B ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t121_tmap_1])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_B_1 ) ),
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
    ! [X30: $i,X31: $i] :
      ( ~ ( m1_pre_topc @ X30 @ X31 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X30 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X31 ) ) )
      | ~ ( l1_pre_topc @ X31 ) ) ),
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

thf(t112_tmap_1,axiom,(
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
               => ( ( v1_funct_1 @ ( k2_tmap_1 @ A @ ( k6_tmap_1 @ A @ B ) @ ( k7_tmap_1 @ A @ B ) @ C ) )
                  & ( v1_funct_2 @ ( k2_tmap_1 @ A @ ( k6_tmap_1 @ A @ B ) @ ( k7_tmap_1 @ A @ B ) @ C ) @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ ( k6_tmap_1 @ A @ B ) ) )
                  & ( v5_pre_topc @ ( k2_tmap_1 @ A @ ( k6_tmap_1 @ A @ B ) @ ( k7_tmap_1 @ A @ B ) @ C ) @ C @ ( k6_tmap_1 @ A @ B ) )
                  & ( m1_subset_1 @ ( k2_tmap_1 @ A @ ( k6_tmap_1 @ A @ B ) @ ( k7_tmap_1 @ A @ B ) @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ ( k6_tmap_1 @ A @ B ) ) ) ) ) ) ) ) ) ) )).

thf('6',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ( ( u1_struct_0 @ X29 )
       != X27 )
      | ( m1_subset_1 @ ( k2_tmap_1 @ X28 @ ( k6_tmap_1 @ X28 @ X27 ) @ ( k7_tmap_1 @ X28 @ X27 ) @ X29 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X29 ) @ ( u1_struct_0 @ ( k6_tmap_1 @ X28 @ X27 ) ) ) ) )
      | ~ ( m1_pre_topc @ X29 @ X28 )
      | ( v2_struct_0 @ X29 )
      | ~ ( l1_pre_topc @ X28 )
      | ~ ( v2_pre_topc @ X28 )
      | ( v2_struct_0 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t112_tmap_1])).

thf('7',plain,(
    ! [X28: $i,X29: $i] :
      ( ( v2_struct_0 @ X28 )
      | ~ ( v2_pre_topc @ X28 )
      | ~ ( l1_pre_topc @ X28 )
      | ( v2_struct_0 @ X29 )
      | ~ ( m1_pre_topc @ X29 @ X28 )
      | ( m1_subset_1 @ ( k2_tmap_1 @ X28 @ ( k6_tmap_1 @ X28 @ ( u1_struct_0 @ X29 ) ) @ ( k7_tmap_1 @ X28 @ ( u1_struct_0 @ X29 ) ) @ X29 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X29 ) @ ( u1_struct_0 @ ( k6_tmap_1 @ X28 @ ( u1_struct_0 @ X29 ) ) ) ) ) )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X29 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,
    ( ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B_1 ) ) @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B_1 ) ) @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B_1 ) ) ) ) ) )
    | ~ ( m1_pre_topc @ sk_B_1 @ sk_A )
    | ( v2_struct_0 @ sk_B_1 )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['5','7'])).

thf('9',plain,(
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

thf('10',plain,(
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

thf('11',plain,(
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
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,
    ( ~ ( m1_pre_topc @ sk_B_1 @ sk_A )
    | ( ( k8_tmap_1 @ sk_A @ sk_B_1 )
      = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B_1 ) ) )
    | ~ ( l1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) )
    | ~ ( v2_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) )
    | ~ ( v1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['9','11'])).

thf('13',plain,(
    m1_pre_topc @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
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

thf('15',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( l1_pre_topc @ X21 )
      | ~ ( v2_pre_topc @ X21 )
      | ( v2_struct_0 @ X21 )
      | ~ ( m1_pre_topc @ X22 @ X21 )
      | ( l1_pre_topc @ ( k8_tmap_1 @ X21 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k8_tmap_1])).

thf('16',plain,
    ( ( l1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( l1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['16','17','18'])).

thf('20',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    l1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) ),
    inference(clc,[status(thm)],['19','20'])).

thf('22',plain,(
    m1_pre_topc @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( l1_pre_topc @ X21 )
      | ~ ( v2_pre_topc @ X21 )
      | ( v2_struct_0 @ X21 )
      | ~ ( m1_pre_topc @ X22 @ X21 )
      | ( v2_pre_topc @ ( k8_tmap_1 @ X21 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k8_tmap_1])).

thf('24',plain,
    ( ( v2_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,
    ( ( v2_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['24','25','26'])).

thf('28',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    v2_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) ),
    inference(clc,[status(thm)],['27','28'])).

thf('30',plain,(
    m1_pre_topc @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( l1_pre_topc @ X21 )
      | ~ ( v2_pre_topc @ X21 )
      | ( v2_struct_0 @ X21 )
      | ~ ( m1_pre_topc @ X22 @ X21 )
      | ( v1_pre_topc @ ( k8_tmap_1 @ X21 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k8_tmap_1])).

thf('32',plain,
    ( ( v1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( v1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['32','33','34'])).

thf('36',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    v1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) ),
    inference(clc,[status(thm)],['35','36'])).

thf('38',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,
    ( ( ( k8_tmap_1 @ sk_A @ sk_B_1 )
      = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B_1 ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['12','13','21','29','37','38','39'])).

thf('41',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( ( k8_tmap_1 @ sk_A @ sk_B_1 )
    = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['40','41'])).

thf('43',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
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

thf('44',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ( ( k7_tmap_1 @ X10 @ X9 )
        = ( k6_partfun1 @ ( u1_struct_0 @ X10 ) ) )
      | ~ ( l1_pre_topc @ X10 )
      | ~ ( v2_pre_topc @ X10 )
      | ( v2_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d10_tmap_1])).

thf('45',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B_1 ) )
      = ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B_1 ) )
      = ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['45','46','47'])).

thf('49',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,
    ( ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B_1 ) )
    = ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['48','49'])).

thf('51',plain,
    ( ( k8_tmap_1 @ sk_A @ sk_B_1 )
    = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['40','41'])).

thf('52',plain,(
    m1_pre_topc @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) ) ) ) )
    | ( v2_struct_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['8','42','50','51','52','53','54'])).

thf('56',plain,
    ( ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) @ ( k9_tmap_1 @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
    | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) @ ( k9_tmap_1 @ sk_A @ sk_B_1 ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) ) )
    | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) @ ( k9_tmap_1 @ sk_A @ sk_B_1 ) @ sk_B_1 ) @ sk_B_1 @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) )
    | ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) @ ( k9_tmap_1 @ sk_A @ sk_B_1 ) @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,
    ( ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) @ ( k9_tmap_1 @ sk_A @ sk_B_1 ) @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) ) ) ) )
   <= ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) @ ( k9_tmap_1 @ sk_A @ sk_B_1 ) @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) ) ) ) ) ),
    inference(split,[status(esa)],['56'])).

thf('58',plain,(
    m1_pre_topc @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k9_tmap_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_pre_topc @ B @ A ) )
     => ( ( v1_funct_1 @ ( k9_tmap_1 @ A @ B ) )
        & ( v1_funct_2 @ ( k9_tmap_1 @ A @ B ) @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ A @ B ) ) )
        & ( m1_subset_1 @ ( k9_tmap_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ A @ B ) ) ) ) ) ) ) )).

thf('59',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( l1_pre_topc @ X23 )
      | ~ ( v2_pre_topc @ X23 )
      | ( v2_struct_0 @ X23 )
      | ~ ( m1_pre_topc @ X24 @ X23 )
      | ( m1_subset_1 @ ( k9_tmap_1 @ X23 @ X24 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X23 ) @ ( u1_struct_0 @ ( k8_tmap_1 @ X23 @ X24 ) ) ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k9_tmap_1])).

thf('60',plain,
    ( ( m1_subset_1 @ ( k9_tmap_1 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) ) ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,
    ( ( m1_subset_1 @ ( k9_tmap_1 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) ) ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['60','61','62'])).

thf('64',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    m1_subset_1 @ ( k9_tmap_1 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) ) ) ) ),
    inference(clc,[status(thm)],['63','64'])).

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

thf('66',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_pre_topc @ X15 @ X16 )
      | ( X17
       != ( k9_tmap_1 @ X16 @ X15 ) )
      | ( X18
       != ( u1_struct_0 @ X15 ) )
      | ( r1_funct_2 @ ( u1_struct_0 @ X16 ) @ ( u1_struct_0 @ ( k8_tmap_1 @ X16 @ X15 ) ) @ ( u1_struct_0 @ X16 ) @ ( u1_struct_0 @ ( k6_tmap_1 @ X16 @ X18 ) ) @ X17 @ ( k7_tmap_1 @ X16 @ X18 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X16 ) @ ( u1_struct_0 @ ( k8_tmap_1 @ X16 @ X15 ) ) ) ) )
      | ~ ( v1_funct_2 @ X17 @ ( u1_struct_0 @ X16 ) @ ( u1_struct_0 @ ( k8_tmap_1 @ X16 @ X15 ) ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( l1_pre_topc @ X16 )
      | ~ ( v2_pre_topc @ X16 )
      | ( v2_struct_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d12_tmap_1])).

thf('67',plain,(
    ! [X15: $i,X16: $i] :
      ( ( v2_struct_0 @ X16 )
      | ~ ( v2_pre_topc @ X16 )
      | ~ ( l1_pre_topc @ X16 )
      | ~ ( v1_funct_1 @ ( k9_tmap_1 @ X16 @ X15 ) )
      | ~ ( v1_funct_2 @ ( k9_tmap_1 @ X16 @ X15 ) @ ( u1_struct_0 @ X16 ) @ ( u1_struct_0 @ ( k8_tmap_1 @ X16 @ X15 ) ) )
      | ~ ( m1_subset_1 @ ( k9_tmap_1 @ X16 @ X15 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X16 ) @ ( u1_struct_0 @ ( k8_tmap_1 @ X16 @ X15 ) ) ) ) )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X15 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ( r1_funct_2 @ ( u1_struct_0 @ X16 ) @ ( u1_struct_0 @ ( k8_tmap_1 @ X16 @ X15 ) ) @ ( u1_struct_0 @ X16 ) @ ( u1_struct_0 @ ( k6_tmap_1 @ X16 @ ( u1_struct_0 @ X15 ) ) ) @ ( k9_tmap_1 @ X16 @ X15 ) @ ( k7_tmap_1 @ X16 @ ( u1_struct_0 @ X15 ) ) )
      | ~ ( m1_pre_topc @ X15 @ X16 ) ) ),
    inference(simplify,[status(thm)],['66'])).

thf('68',plain,
    ( ~ ( m1_pre_topc @ sk_B_1 @ sk_A )
    | ( r1_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B_1 ) ) ) @ ( k9_tmap_1 @ sk_A @ sk_B_1 ) @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B_1 ) ) )
    | ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( v1_funct_2 @ ( k9_tmap_1 @ sk_A @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) ) )
    | ~ ( v1_funct_1 @ ( k9_tmap_1 @ sk_A @ sk_B_1 ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['65','67'])).

thf('69',plain,(
    m1_pre_topc @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,
    ( ( k8_tmap_1 @ sk_A @ sk_B_1 )
    = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['40','41'])).

thf('71',plain,
    ( ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B_1 ) )
    = ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['48','49'])).

thf('72',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('73',plain,(
    m1_pre_topc @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( l1_pre_topc @ X23 )
      | ~ ( v2_pre_topc @ X23 )
      | ( v2_struct_0 @ X23 )
      | ~ ( m1_pre_topc @ X24 @ X23 )
      | ( v1_funct_2 @ ( k9_tmap_1 @ X23 @ X24 ) @ ( u1_struct_0 @ X23 ) @ ( u1_struct_0 @ ( k8_tmap_1 @ X23 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k9_tmap_1])).

thf('75',plain,
    ( ( v1_funct_2 @ ( k9_tmap_1 @ sk_A @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,
    ( ( v1_funct_2 @ ( k9_tmap_1 @ sk_A @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['75','76','77'])).

thf('79',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    v1_funct_2 @ ( k9_tmap_1 @ sk_A @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['78','79'])).

thf('81',plain,(
    m1_pre_topc @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( l1_pre_topc @ X23 )
      | ~ ( v2_pre_topc @ X23 )
      | ( v2_struct_0 @ X23 )
      | ~ ( m1_pre_topc @ X24 @ X23 )
      | ( v1_funct_1 @ ( k9_tmap_1 @ X23 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k9_tmap_1])).

thf('83',plain,
    ( ( v1_funct_1 @ ( k9_tmap_1 @ sk_A @ sk_B_1 ) )
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
    ( ( v1_funct_1 @ ( k9_tmap_1 @ sk_A @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['83','84','85'])).

thf('87',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    v1_funct_1 @ ( k9_tmap_1 @ sk_A @ sk_B_1 ) ),
    inference(clc,[status(thm)],['86','87'])).

thf('89',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,
    ( ( r1_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) ) @ ( k9_tmap_1 @ sk_A @ sk_B_1 ) @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['68','69','70','71','72','80','88','89','90'])).

thf('92',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    r1_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) ) @ ( k9_tmap_1 @ sk_A @ sk_B_1 ) @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['91','92'])).

thf('94',plain,(
    m1_subset_1 @ ( k9_tmap_1 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) ) ) ) ),
    inference(clc,[status(thm)],['63','64'])).

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

thf('95',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X4 @ X5 ) ) )
      | ~ ( v1_funct_2 @ X3 @ X4 @ X5 )
      | ~ ( v1_funct_1 @ X3 )
      | ( v1_xboole_0 @ X6 )
      | ( v1_xboole_0 @ X5 )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_funct_2 @ X7 @ X8 @ X6 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X6 ) ) )
      | ( X3 = X7 )
      | ~ ( r1_funct_2 @ X4 @ X5 @ X8 @ X6 @ X3 @ X7 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_funct_2])).

thf('96',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) ) @ X2 @ X1 @ ( k9_tmap_1 @ sk_A @ sk_B_1 ) @ X0 )
      | ( ( k9_tmap_1 @ sk_A @ sk_B_1 )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_2 @ X0 @ X2 @ X1 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) ) )
      | ( v1_xboole_0 @ X1 )
      | ~ ( v1_funct_1 @ ( k9_tmap_1 @ sk_A @ sk_B_1 ) )
      | ~ ( v1_funct_2 @ ( k9_tmap_1 @ sk_A @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,(
    v1_funct_1 @ ( k9_tmap_1 @ sk_A @ sk_B_1 ) ),
    inference(clc,[status(thm)],['86','87'])).

thf('98',plain,(
    v1_funct_2 @ ( k9_tmap_1 @ sk_A @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['78','79'])).

thf('99',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) ) @ X2 @ X1 @ ( k9_tmap_1 @ sk_A @ sk_B_1 ) @ X0 )
      | ( ( k9_tmap_1 @ sk_A @ sk_B_1 )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_2 @ X0 @ X2 @ X1 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) ) )
      | ( v1_xboole_0 @ X1 ) ) ),
    inference(demod,[status(thm)],['96','97','98'])).

thf('100',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) ) )
    | ~ ( v1_funct_1 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( v1_funct_2 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) ) )
    | ~ ( m1_subset_1 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) ) ) ) )
    | ( ( k9_tmap_1 @ sk_A @ sk_B_1 )
      = ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['93','99'])).

thf('101',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
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

thf('102',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( l1_pre_topc @ X19 )
      | ~ ( v2_pre_topc @ X19 )
      | ( v2_struct_0 @ X19 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ( v1_funct_1 @ ( k7_tmap_1 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_tmap_1])).

thf('103',plain,
    ( ( v1_funct_1 @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B_1 ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,
    ( ( v1_funct_1 @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B_1 ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['103','104','105'])).

thf('107',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,(
    v1_funct_1 @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['106','107'])).

thf('109',plain,
    ( ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B_1 ) )
    = ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['48','49'])).

thf('110',plain,(
    v1_funct_1 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['108','109'])).

thf('111',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('112',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( l1_pre_topc @ X19 )
      | ~ ( v2_pre_topc @ X19 )
      | ( v2_struct_0 @ X19 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ( v1_funct_2 @ ( k7_tmap_1 @ X19 @ X20 ) @ ( u1_struct_0 @ X19 ) @ ( u1_struct_0 @ ( k6_tmap_1 @ X19 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_tmap_1])).

thf('113',plain,
    ( ( v1_funct_2 @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B_1 ) ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B_1 ) ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['111','112'])).

thf('114',plain,
    ( ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B_1 ) )
    = ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['48','49'])).

thf('115',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,
    ( ( v1_funct_2 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B_1 ) ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['113','114','115','116'])).

thf('118',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,(
    v1_funct_2 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference(clc,[status(thm)],['117','118'])).

thf('120',plain,
    ( ( k8_tmap_1 @ sk_A @ sk_B_1 )
    = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['40','41'])).

thf('121',plain,(
    v1_funct_2 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['119','120'])).

thf('122',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('123',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( l1_pre_topc @ X19 )
      | ~ ( v2_pre_topc @ X19 )
      | ( v2_struct_0 @ X19 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ( m1_subset_1 @ ( k7_tmap_1 @ X19 @ X20 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X19 ) @ ( u1_struct_0 @ ( k6_tmap_1 @ X19 @ X20 ) ) ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_tmap_1])).

thf('124',plain,
    ( ( m1_subset_1 @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B_1 ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B_1 ) ) ) ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['122','123'])).

thf('125',plain,
    ( ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B_1 ) )
    = ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['48','49'])).

thf('126',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('128',plain,
    ( ( m1_subset_1 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B_1 ) ) ) ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['124','125','126','127'])).

thf('129',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('130',plain,(
    m1_subset_1 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B_1 ) ) ) ) ) ),
    inference(clc,[status(thm)],['128','129'])).

thf('131',plain,
    ( ( k8_tmap_1 @ sk_A @ sk_B_1 )
    = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['40','41'])).

thf('132',plain,(
    m1_subset_1 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) ) ) ) ),
    inference(demod,[status(thm)],['130','131'])).

thf('133',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) ) )
    | ( ( k9_tmap_1 @ sk_A @ sk_B_1 )
      = ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['100','110','121','132'])).

thf('134',plain,
    ( ( ( k9_tmap_1 @ sk_A @ sk_B_1 )
      = ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) ) ) ),
    inference(simplify,[status(thm)],['133'])).

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
    ( ( ( k9_tmap_1 @ sk_A @ sk_B_1 )
      = ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v2_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) )
    | ~ ( l1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['134','135'])).

thf('137',plain,(
    l1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) ),
    inference(clc,[status(thm)],['19','20'])).

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
    l1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['137','138'])).

thf('140',plain,
    ( ( ( k9_tmap_1 @ sk_A @ sk_B_1 )
      = ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v2_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['136','139'])).

thf(fc5_tmap_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_pre_topc @ B @ A ) )
     => ( ~ ( v2_struct_0 @ ( k8_tmap_1 @ A @ B ) )
        & ( v1_pre_topc @ ( k8_tmap_1 @ A @ B ) )
        & ( v2_pre_topc @ ( k8_tmap_1 @ A @ B ) ) ) ) )).

thf('141',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( l1_pre_topc @ X25 )
      | ~ ( v2_pre_topc @ X25 )
      | ( v2_struct_0 @ X25 )
      | ~ ( m1_pre_topc @ X26 @ X25 )
      | ~ ( v2_struct_0 @ ( k8_tmap_1 @ X25 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[fc5_tmap_1])).

thf('142',plain,
    ( ( ( k9_tmap_1 @ sk_A @ sk_B_1 )
      = ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( m1_pre_topc @ sk_B_1 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['140','141'])).

thf('143',plain,(
    m1_pre_topc @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('144',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('145',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('146',plain,
    ( ( ( k9_tmap_1 @ sk_A @ sk_B_1 )
      = ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['142','143','144','145'])).

thf('147',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('148',plain,
    ( ( k9_tmap_1 @ sk_A @ sk_B_1 )
    = ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['146','147'])).

thf('149',plain,
    ( ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) ) ) ) )
   <= ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) @ ( k9_tmap_1 @ sk_A @ sk_B_1 ) @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) ) ) ) ) ),
    inference(demod,[status(thm)],['57','148'])).

thf('150',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('151',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ( ( u1_struct_0 @ X29 )
       != X27 )
      | ( v1_funct_2 @ ( k2_tmap_1 @ X28 @ ( k6_tmap_1 @ X28 @ X27 ) @ ( k7_tmap_1 @ X28 @ X27 ) @ X29 ) @ ( u1_struct_0 @ X29 ) @ ( u1_struct_0 @ ( k6_tmap_1 @ X28 @ X27 ) ) )
      | ~ ( m1_pre_topc @ X29 @ X28 )
      | ( v2_struct_0 @ X29 )
      | ~ ( l1_pre_topc @ X28 )
      | ~ ( v2_pre_topc @ X28 )
      | ( v2_struct_0 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t112_tmap_1])).

thf('152',plain,(
    ! [X28: $i,X29: $i] :
      ( ( v2_struct_0 @ X28 )
      | ~ ( v2_pre_topc @ X28 )
      | ~ ( l1_pre_topc @ X28 )
      | ( v2_struct_0 @ X29 )
      | ~ ( m1_pre_topc @ X29 @ X28 )
      | ( v1_funct_2 @ ( k2_tmap_1 @ X28 @ ( k6_tmap_1 @ X28 @ ( u1_struct_0 @ X29 ) ) @ ( k7_tmap_1 @ X28 @ ( u1_struct_0 @ X29 ) ) @ X29 ) @ ( u1_struct_0 @ X29 ) @ ( u1_struct_0 @ ( k6_tmap_1 @ X28 @ ( u1_struct_0 @ X29 ) ) ) )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X29 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) ) ) ),
    inference(simplify,[status(thm)],['151'])).

thf('153',plain,
    ( ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B_1 ) ) @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B_1 ) ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B_1 ) ) ) )
    | ~ ( m1_pre_topc @ sk_B_1 @ sk_A )
    | ( v2_struct_0 @ sk_B_1 )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['150','152'])).

thf('154',plain,
    ( ( k8_tmap_1 @ sk_A @ sk_B_1 )
    = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['40','41'])).

thf('155',plain,
    ( ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B_1 ) )
    = ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['48','49'])).

thf('156',plain,
    ( ( k8_tmap_1 @ sk_A @ sk_B_1 )
    = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['40','41'])).

thf('157',plain,(
    m1_pre_topc @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('158',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('159',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('160',plain,
    ( ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) ) )
    | ( v2_struct_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['153','154','155','156','157','158','159'])).

thf('161',plain,(
    ~ ( v2_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('162',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) ) ) ),
    inference(clc,[status(thm)],['160','161'])).

thf('163',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('164',plain,(
    v1_funct_2 @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['162','163'])).

thf('165',plain,
    ( ( k9_tmap_1 @ sk_A @ sk_B_1 )
    = ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['146','147'])).

thf('166',plain,
    ( ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) @ ( k9_tmap_1 @ sk_A @ sk_B_1 ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) ) )
   <= ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) @ ( k9_tmap_1 @ sk_A @ sk_B_1 ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) ) ) ),
    inference(split,[status(esa)],['56'])).

thf('167',plain,
    ( ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) ) )
   <= ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) @ ( k9_tmap_1 @ sk_A @ sk_B_1 ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['165','166'])).

thf('168',plain,(
    v1_funct_2 @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) @ ( k9_tmap_1 @ sk_A @ sk_B_1 ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['164','167'])).

thf('169',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('170',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ( ( u1_struct_0 @ X29 )
       != X27 )
      | ( v1_funct_1 @ ( k2_tmap_1 @ X28 @ ( k6_tmap_1 @ X28 @ X27 ) @ ( k7_tmap_1 @ X28 @ X27 ) @ X29 ) )
      | ~ ( m1_pre_topc @ X29 @ X28 )
      | ( v2_struct_0 @ X29 )
      | ~ ( l1_pre_topc @ X28 )
      | ~ ( v2_pre_topc @ X28 )
      | ( v2_struct_0 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t112_tmap_1])).

thf('171',plain,(
    ! [X28: $i,X29: $i] :
      ( ( v2_struct_0 @ X28 )
      | ~ ( v2_pre_topc @ X28 )
      | ~ ( l1_pre_topc @ X28 )
      | ( v2_struct_0 @ X29 )
      | ~ ( m1_pre_topc @ X29 @ X28 )
      | ( v1_funct_1 @ ( k2_tmap_1 @ X28 @ ( k6_tmap_1 @ X28 @ ( u1_struct_0 @ X29 ) ) @ ( k7_tmap_1 @ X28 @ ( u1_struct_0 @ X29 ) ) @ X29 ) )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X29 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) ) ) ),
    inference(simplify,[status(thm)],['170'])).

thf('172',plain,
    ( ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B_1 ) ) @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B_1 ) ) @ sk_B_1 ) )
    | ~ ( m1_pre_topc @ sk_B_1 @ sk_A )
    | ( v2_struct_0 @ sk_B_1 )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['169','171'])).

thf('173',plain,
    ( ( k8_tmap_1 @ sk_A @ sk_B_1 )
    = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['40','41'])).

thf('174',plain,
    ( ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B_1 ) )
    = ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['48','49'])).

thf('175',plain,(
    m1_pre_topc @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('176',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('177',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('178',plain,
    ( ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['172','173','174','175','176','177'])).

thf('179',plain,(
    ~ ( v2_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('180',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['178','179'])).

thf('181',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('182',plain,(
    v1_funct_1 @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B_1 ) ),
    inference(clc,[status(thm)],['180','181'])).

thf('183',plain,
    ( ( k9_tmap_1 @ sk_A @ sk_B_1 )
    = ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['146','147'])).

thf('184',plain,
    ( ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) @ ( k9_tmap_1 @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
   <= ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) @ ( k9_tmap_1 @ sk_A @ sk_B_1 ) @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['56'])).

thf('185',plain,
    ( ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B_1 ) )
   <= ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) @ ( k9_tmap_1 @ sk_A @ sk_B_1 ) @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['183','184'])).

thf('186',plain,(
    v1_funct_1 @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) @ ( k9_tmap_1 @ sk_A @ sk_B_1 ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['182','185'])).

thf('187',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('188',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ( ( u1_struct_0 @ X29 )
       != X27 )
      | ( v5_pre_topc @ ( k2_tmap_1 @ X28 @ ( k6_tmap_1 @ X28 @ X27 ) @ ( k7_tmap_1 @ X28 @ X27 ) @ X29 ) @ X29 @ ( k6_tmap_1 @ X28 @ X27 ) )
      | ~ ( m1_pre_topc @ X29 @ X28 )
      | ( v2_struct_0 @ X29 )
      | ~ ( l1_pre_topc @ X28 )
      | ~ ( v2_pre_topc @ X28 )
      | ( v2_struct_0 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t112_tmap_1])).

thf('189',plain,(
    ! [X28: $i,X29: $i] :
      ( ( v2_struct_0 @ X28 )
      | ~ ( v2_pre_topc @ X28 )
      | ~ ( l1_pre_topc @ X28 )
      | ( v2_struct_0 @ X29 )
      | ~ ( m1_pre_topc @ X29 @ X28 )
      | ( v5_pre_topc @ ( k2_tmap_1 @ X28 @ ( k6_tmap_1 @ X28 @ ( u1_struct_0 @ X29 ) ) @ ( k7_tmap_1 @ X28 @ ( u1_struct_0 @ X29 ) ) @ X29 ) @ X29 @ ( k6_tmap_1 @ X28 @ ( u1_struct_0 @ X29 ) ) )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X29 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) ) ) ),
    inference(simplify,[status(thm)],['188'])).

thf('190',plain,
    ( ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B_1 ) ) @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B_1 ) ) @ sk_B_1 ) @ sk_B_1 @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B_1 ) ) )
    | ~ ( m1_pre_topc @ sk_B_1 @ sk_A )
    | ( v2_struct_0 @ sk_B_1 )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['187','189'])).

thf('191',plain,
    ( ( k8_tmap_1 @ sk_A @ sk_B_1 )
    = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['40','41'])).

thf('192',plain,
    ( ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B_1 ) )
    = ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['48','49'])).

thf('193',plain,
    ( ( k8_tmap_1 @ sk_A @ sk_B_1 )
    = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['40','41'])).

thf('194',plain,(
    m1_pre_topc @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('195',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('196',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('197',plain,
    ( ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B_1 ) @ sk_B_1 @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['190','191','192','193','194','195','196'])).

thf('198',plain,(
    ~ ( v2_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('199',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B_1 ) @ sk_B_1 @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['197','198'])).

thf('200',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('201',plain,(
    v5_pre_topc @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B_1 ) @ sk_B_1 @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) ),
    inference(clc,[status(thm)],['199','200'])).

thf('202',plain,
    ( ( k9_tmap_1 @ sk_A @ sk_B_1 )
    = ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['146','147'])).

thf('203',plain,
    ( ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) @ ( k9_tmap_1 @ sk_A @ sk_B_1 ) @ sk_B_1 ) @ sk_B_1 @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) )
   <= ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) @ ( k9_tmap_1 @ sk_A @ sk_B_1 ) @ sk_B_1 ) @ sk_B_1 @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['56'])).

thf('204',plain,
    ( ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B_1 ) @ sk_B_1 @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) )
   <= ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) @ ( k9_tmap_1 @ sk_A @ sk_B_1 ) @ sk_B_1 ) @ sk_B_1 @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['202','203'])).

thf('205',plain,(
    v5_pre_topc @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) @ ( k9_tmap_1 @ sk_A @ sk_B_1 ) @ sk_B_1 ) @ sk_B_1 @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['201','204'])).

thf('206',plain,
    ( ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) @ ( k9_tmap_1 @ sk_A @ sk_B_1 ) @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) ) ) ) )
    | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) @ ( k9_tmap_1 @ sk_A @ sk_B_1 ) @ sk_B_1 ) @ sk_B_1 @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) )
    | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) @ ( k9_tmap_1 @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
    | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) @ ( k9_tmap_1 @ sk_A @ sk_B_1 ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) ) ) ),
    inference(split,[status(esa)],['56'])).

thf('207',plain,(
    ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) @ ( k9_tmap_1 @ sk_A @ sk_B_1 ) @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) ) ) ) ) ),
    inference('sat_resolution*',[status(thm)],['168','186','205','206'])).

thf('208',plain,(
    ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) ) ) ) ) ),
    inference(simpl_trail,[status(thm)],['149','207'])).

thf('209',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['55','208'])).

thf('210',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('211',plain,(
    v2_struct_0 @ sk_B_1 ),
    inference(clc,[status(thm)],['209','210'])).

thf('212',plain,(
    $false ),
    inference(demod,[status(thm)],['0','211'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.2nxREFJlRF
% 0.14/0.35  % Computer   : n008.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 12:36:30 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.21/0.36  % Running in FO mode
% 0.80/1.01  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.80/1.01  % Solved by: fo/fo7.sh
% 0.80/1.01  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.80/1.01  % done 223 iterations in 0.542s
% 0.80/1.01  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.80/1.01  % SZS output start Refutation
% 0.80/1.01  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.80/1.01  thf(sk_A_type, type, sk_A: $i).
% 0.80/1.01  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.80/1.01  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.80/1.01  thf(k7_tmap_1_type, type, k7_tmap_1: $i > $i > $i).
% 0.80/1.01  thf(k2_tmap_1_type, type, k2_tmap_1: $i > $i > $i > $i > $i).
% 0.80/1.01  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.80/1.01  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 0.80/1.01  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.80/1.01  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.80/1.01  thf(k9_tmap_1_type, type, k9_tmap_1: $i > $i > $i).
% 0.80/1.01  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.80/1.01  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.80/1.01  thf(v5_pre_topc_type, type, v5_pre_topc: $i > $i > $i > $o).
% 0.80/1.01  thf(k6_tmap_1_type, type, k6_tmap_1: $i > $i > $i).
% 0.80/1.01  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.80/1.01  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.80/1.01  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.80/1.01  thf(k8_tmap_1_type, type, k8_tmap_1: $i > $i > $i).
% 0.80/1.01  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 0.80/1.01  thf(r1_funct_2_type, type, r1_funct_2: $i > $i > $i > $i > $i > $i > $o).
% 0.80/1.01  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.80/1.01  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.80/1.01  thf(t121_tmap_1, conjecture,
% 0.80/1.01    (![A:$i]:
% 0.80/1.01     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.80/1.01       ( ![B:$i]:
% 0.80/1.01         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.80/1.01           ( ( v1_funct_1 @
% 0.80/1.01               ( k2_tmap_1 @
% 0.80/1.01                 A @ ( k8_tmap_1 @ A @ B ) @ ( k9_tmap_1 @ A @ B ) @ B ) ) & 
% 0.80/1.01             ( v1_funct_2 @
% 0.80/1.01               ( k2_tmap_1 @
% 0.80/1.01                 A @ ( k8_tmap_1 @ A @ B ) @ ( k9_tmap_1 @ A @ B ) @ B ) @ 
% 0.80/1.01               ( u1_struct_0 @ B ) @ ( u1_struct_0 @ ( k8_tmap_1 @ A @ B ) ) ) & 
% 0.80/1.01             ( v5_pre_topc @
% 0.80/1.01               ( k2_tmap_1 @
% 0.80/1.01                 A @ ( k8_tmap_1 @ A @ B ) @ ( k9_tmap_1 @ A @ B ) @ B ) @ 
% 0.80/1.01               B @ ( k8_tmap_1 @ A @ B ) ) & 
% 0.80/1.01             ( m1_subset_1 @
% 0.80/1.01               ( k2_tmap_1 @
% 0.80/1.01                 A @ ( k8_tmap_1 @ A @ B ) @ ( k9_tmap_1 @ A @ B ) @ B ) @ 
% 0.80/1.01               ( k1_zfmisc_1 @
% 0.80/1.01                 ( k2_zfmisc_1 @
% 0.80/1.01                   ( u1_struct_0 @ B ) @ 
% 0.80/1.01                   ( u1_struct_0 @ ( k8_tmap_1 @ A @ B ) ) ) ) ) ) ) ) ))).
% 0.80/1.01  thf(zf_stmt_0, negated_conjecture,
% 0.80/1.01    (~( ![A:$i]:
% 0.80/1.01        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.80/1.01            ( l1_pre_topc @ A ) ) =>
% 0.80/1.01          ( ![B:$i]:
% 0.80/1.01            ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.80/1.01              ( ( v1_funct_1 @
% 0.80/1.01                  ( k2_tmap_1 @
% 0.80/1.01                    A @ ( k8_tmap_1 @ A @ B ) @ ( k9_tmap_1 @ A @ B ) @ B ) ) & 
% 0.80/1.01                ( v1_funct_2 @
% 0.80/1.01                  ( k2_tmap_1 @
% 0.80/1.01                    A @ ( k8_tmap_1 @ A @ B ) @ ( k9_tmap_1 @ A @ B ) @ B ) @ 
% 0.80/1.01                  ( u1_struct_0 @ B ) @ ( u1_struct_0 @ ( k8_tmap_1 @ A @ B ) ) ) & 
% 0.80/1.01                ( v5_pre_topc @
% 0.80/1.01                  ( k2_tmap_1 @
% 0.80/1.01                    A @ ( k8_tmap_1 @ A @ B ) @ ( k9_tmap_1 @ A @ B ) @ B ) @ 
% 0.80/1.01                  B @ ( k8_tmap_1 @ A @ B ) ) & 
% 0.80/1.01                ( m1_subset_1 @
% 0.80/1.01                  ( k2_tmap_1 @
% 0.80/1.01                    A @ ( k8_tmap_1 @ A @ B ) @ ( k9_tmap_1 @ A @ B ) @ B ) @ 
% 0.80/1.01                  ( k1_zfmisc_1 @
% 0.80/1.01                    ( k2_zfmisc_1 @
% 0.80/1.01                      ( u1_struct_0 @ B ) @ 
% 0.80/1.01                      ( u1_struct_0 @ ( k8_tmap_1 @ A @ B ) ) ) ) ) ) ) ) ) )),
% 0.80/1.01    inference('cnf.neg', [status(esa)], [t121_tmap_1])).
% 0.80/1.01  thf('0', plain, (~ (v2_struct_0 @ sk_B_1)),
% 0.80/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.01  thf('1', plain, ((m1_pre_topc @ sk_B_1 @ sk_A)),
% 0.80/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.01  thf(t1_tsep_1, axiom,
% 0.80/1.01    (![A:$i]:
% 0.80/1.01     ( ( l1_pre_topc @ A ) =>
% 0.80/1.01       ( ![B:$i]:
% 0.80/1.01         ( ( m1_pre_topc @ B @ A ) =>
% 0.80/1.01           ( m1_subset_1 @
% 0.80/1.01             ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.80/1.01  thf('2', plain,
% 0.80/1.01      (![X30 : $i, X31 : $i]:
% 0.80/1.01         (~ (m1_pre_topc @ X30 @ X31)
% 0.80/1.01          | (m1_subset_1 @ (u1_struct_0 @ X30) @ 
% 0.80/1.01             (k1_zfmisc_1 @ (u1_struct_0 @ X31)))
% 0.80/1.01          | ~ (l1_pre_topc @ X31))),
% 0.80/1.01      inference('cnf', [status(esa)], [t1_tsep_1])).
% 0.80/1.01  thf('3', plain,
% 0.80/1.01      ((~ (l1_pre_topc @ sk_A)
% 0.80/1.01        | (m1_subset_1 @ (u1_struct_0 @ sk_B_1) @ 
% 0.80/1.01           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.80/1.01      inference('sup-', [status(thm)], ['1', '2'])).
% 0.80/1.01  thf('4', plain, ((l1_pre_topc @ sk_A)),
% 0.80/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.01  thf('5', plain,
% 0.80/1.01      ((m1_subset_1 @ (u1_struct_0 @ sk_B_1) @ 
% 0.80/1.01        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.80/1.01      inference('demod', [status(thm)], ['3', '4'])).
% 0.80/1.01  thf(t112_tmap_1, axiom,
% 0.80/1.01    (![A:$i]:
% 0.80/1.01     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.80/1.01       ( ![B:$i]:
% 0.80/1.01         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.80/1.01           ( ![C:$i]:
% 0.80/1.01             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.80/1.01               ( ( ( u1_struct_0 @ C ) = ( B ) ) =>
% 0.80/1.01                 ( ( v1_funct_1 @
% 0.80/1.01                     ( k2_tmap_1 @
% 0.80/1.01                       A @ ( k6_tmap_1 @ A @ B ) @ ( k7_tmap_1 @ A @ B ) @ C ) ) & 
% 0.80/1.01                   ( v1_funct_2 @
% 0.80/1.01                     ( k2_tmap_1 @
% 0.80/1.01                       A @ ( k6_tmap_1 @ A @ B ) @ ( k7_tmap_1 @ A @ B ) @ C ) @ 
% 0.80/1.01                     ( u1_struct_0 @ C ) @ 
% 0.80/1.01                     ( u1_struct_0 @ ( k6_tmap_1 @ A @ B ) ) ) & 
% 0.80/1.01                   ( v5_pre_topc @
% 0.80/1.01                     ( k2_tmap_1 @
% 0.80/1.01                       A @ ( k6_tmap_1 @ A @ B ) @ ( k7_tmap_1 @ A @ B ) @ C ) @ 
% 0.80/1.01                     C @ ( k6_tmap_1 @ A @ B ) ) & 
% 0.80/1.01                   ( m1_subset_1 @
% 0.80/1.01                     ( k2_tmap_1 @
% 0.80/1.01                       A @ ( k6_tmap_1 @ A @ B ) @ ( k7_tmap_1 @ A @ B ) @ C ) @ 
% 0.80/1.01                     ( k1_zfmisc_1 @
% 0.80/1.01                       ( k2_zfmisc_1 @
% 0.80/1.01                         ( u1_struct_0 @ C ) @ 
% 0.80/1.01                         ( u1_struct_0 @ ( k6_tmap_1 @ A @ B ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.80/1.01  thf('6', plain,
% 0.80/1.01      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.80/1.01         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 0.80/1.01          | ((u1_struct_0 @ X29) != (X27))
% 0.80/1.01          | (m1_subset_1 @ 
% 0.80/1.01             (k2_tmap_1 @ X28 @ (k6_tmap_1 @ X28 @ X27) @ 
% 0.80/1.01              (k7_tmap_1 @ X28 @ X27) @ X29) @ 
% 0.80/1.01             (k1_zfmisc_1 @ 
% 0.80/1.01              (k2_zfmisc_1 @ (u1_struct_0 @ X29) @ 
% 0.80/1.01               (u1_struct_0 @ (k6_tmap_1 @ X28 @ X27)))))
% 0.80/1.01          | ~ (m1_pre_topc @ X29 @ X28)
% 0.80/1.01          | (v2_struct_0 @ X29)
% 0.80/1.01          | ~ (l1_pre_topc @ X28)
% 0.80/1.01          | ~ (v2_pre_topc @ X28)
% 0.80/1.01          | (v2_struct_0 @ X28))),
% 0.80/1.01      inference('cnf', [status(esa)], [t112_tmap_1])).
% 0.80/1.01  thf('7', plain,
% 0.80/1.01      (![X28 : $i, X29 : $i]:
% 0.80/1.01         ((v2_struct_0 @ X28)
% 0.80/1.01          | ~ (v2_pre_topc @ X28)
% 0.80/1.01          | ~ (l1_pre_topc @ X28)
% 0.80/1.01          | (v2_struct_0 @ X29)
% 0.80/1.01          | ~ (m1_pre_topc @ X29 @ X28)
% 0.80/1.01          | (m1_subset_1 @ 
% 0.80/1.01             (k2_tmap_1 @ X28 @ (k6_tmap_1 @ X28 @ (u1_struct_0 @ X29)) @ 
% 0.80/1.01              (k7_tmap_1 @ X28 @ (u1_struct_0 @ X29)) @ X29) @ 
% 0.80/1.01             (k1_zfmisc_1 @ 
% 0.80/1.01              (k2_zfmisc_1 @ (u1_struct_0 @ X29) @ 
% 0.80/1.01               (u1_struct_0 @ (k6_tmap_1 @ X28 @ (u1_struct_0 @ X29))))))
% 0.80/1.01          | ~ (m1_subset_1 @ (u1_struct_0 @ X29) @ 
% 0.80/1.01               (k1_zfmisc_1 @ (u1_struct_0 @ X28))))),
% 0.80/1.01      inference('simplify', [status(thm)], ['6'])).
% 0.80/1.01  thf('8', plain,
% 0.80/1.01      (((m1_subset_1 @ 
% 0.80/1.01         (k2_tmap_1 @ sk_A @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B_1)) @ 
% 0.80/1.01          (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B_1)) @ sk_B_1) @ 
% 0.80/1.01         (k1_zfmisc_1 @ 
% 0.80/1.01          (k2_zfmisc_1 @ (u1_struct_0 @ sk_B_1) @ 
% 0.80/1.01           (u1_struct_0 @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B_1))))))
% 0.80/1.01        | ~ (m1_pre_topc @ sk_B_1 @ sk_A)
% 0.80/1.01        | (v2_struct_0 @ sk_B_1)
% 0.80/1.01        | ~ (l1_pre_topc @ sk_A)
% 0.80/1.01        | ~ (v2_pre_topc @ sk_A)
% 0.80/1.01        | (v2_struct_0 @ sk_A))),
% 0.80/1.01      inference('sup-', [status(thm)], ['5', '7'])).
% 0.80/1.01  thf('9', plain,
% 0.80/1.01      ((m1_subset_1 @ (u1_struct_0 @ sk_B_1) @ 
% 0.80/1.01        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.80/1.01      inference('demod', [status(thm)], ['3', '4'])).
% 0.80/1.01  thf(d11_tmap_1, axiom,
% 0.80/1.01    (![A:$i]:
% 0.80/1.01     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.80/1.01       ( ![B:$i]:
% 0.80/1.01         ( ( m1_pre_topc @ B @ A ) =>
% 0.80/1.01           ( ![C:$i]:
% 0.80/1.01             ( ( ( v1_pre_topc @ C ) & ( v2_pre_topc @ C ) & 
% 0.80/1.01                 ( l1_pre_topc @ C ) ) =>
% 0.80/1.01               ( ( ( C ) = ( k8_tmap_1 @ A @ B ) ) <=>
% 0.80/1.01                 ( ![D:$i]:
% 0.80/1.01                   ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.80/1.01                     ( ( ( D ) = ( u1_struct_0 @ B ) ) =>
% 0.80/1.01                       ( ( C ) = ( k6_tmap_1 @ A @ D ) ) ) ) ) ) ) ) ) ) ))).
% 0.80/1.01  thf('10', plain,
% 0.80/1.01      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.80/1.01         (~ (m1_pre_topc @ X11 @ X12)
% 0.80/1.01          | ((X13) != (k8_tmap_1 @ X12 @ X11))
% 0.80/1.01          | ((X14) != (u1_struct_0 @ X11))
% 0.80/1.01          | ((X13) = (k6_tmap_1 @ X12 @ X14))
% 0.80/1.01          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.80/1.01          | ~ (l1_pre_topc @ X13)
% 0.80/1.01          | ~ (v2_pre_topc @ X13)
% 0.80/1.01          | ~ (v1_pre_topc @ X13)
% 0.80/1.01          | ~ (l1_pre_topc @ X12)
% 0.80/1.01          | ~ (v2_pre_topc @ X12)
% 0.80/1.01          | (v2_struct_0 @ X12))),
% 0.80/1.01      inference('cnf', [status(esa)], [d11_tmap_1])).
% 0.80/1.01  thf('11', plain,
% 0.80/1.01      (![X11 : $i, X12 : $i]:
% 0.80/1.01         ((v2_struct_0 @ X12)
% 0.80/1.01          | ~ (v2_pre_topc @ X12)
% 0.80/1.01          | ~ (l1_pre_topc @ X12)
% 0.80/1.01          | ~ (v1_pre_topc @ (k8_tmap_1 @ X12 @ X11))
% 0.80/1.01          | ~ (v2_pre_topc @ (k8_tmap_1 @ X12 @ X11))
% 0.80/1.01          | ~ (l1_pre_topc @ (k8_tmap_1 @ X12 @ X11))
% 0.80/1.01          | ~ (m1_subset_1 @ (u1_struct_0 @ X11) @ 
% 0.80/1.01               (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.80/1.01          | ((k8_tmap_1 @ X12 @ X11) = (k6_tmap_1 @ X12 @ (u1_struct_0 @ X11)))
% 0.80/1.01          | ~ (m1_pre_topc @ X11 @ X12))),
% 0.80/1.01      inference('simplify', [status(thm)], ['10'])).
% 0.80/1.01  thf('12', plain,
% 0.80/1.01      ((~ (m1_pre_topc @ sk_B_1 @ sk_A)
% 0.80/1.01        | ((k8_tmap_1 @ sk_A @ sk_B_1)
% 0.80/1.01            = (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B_1)))
% 0.80/1.01        | ~ (l1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B_1))
% 0.80/1.01        | ~ (v2_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B_1))
% 0.80/1.01        | ~ (v1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B_1))
% 0.80/1.01        | ~ (l1_pre_topc @ sk_A)
% 0.80/1.01        | ~ (v2_pre_topc @ sk_A)
% 0.80/1.01        | (v2_struct_0 @ sk_A))),
% 0.80/1.01      inference('sup-', [status(thm)], ['9', '11'])).
% 0.80/1.01  thf('13', plain, ((m1_pre_topc @ sk_B_1 @ sk_A)),
% 0.80/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.01  thf('14', plain, ((m1_pre_topc @ sk_B_1 @ sk_A)),
% 0.80/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.01  thf(dt_k8_tmap_1, axiom,
% 0.80/1.01    (![A:$i,B:$i]:
% 0.80/1.01     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.80/1.01         ( l1_pre_topc @ A ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.80/1.01       ( ( v1_pre_topc @ ( k8_tmap_1 @ A @ B ) ) & 
% 0.80/1.01         ( v2_pre_topc @ ( k8_tmap_1 @ A @ B ) ) & 
% 0.80/1.01         ( l1_pre_topc @ ( k8_tmap_1 @ A @ B ) ) ) ))).
% 0.80/1.01  thf('15', plain,
% 0.80/1.01      (![X21 : $i, X22 : $i]:
% 0.80/1.01         (~ (l1_pre_topc @ X21)
% 0.80/1.01          | ~ (v2_pre_topc @ X21)
% 0.80/1.01          | (v2_struct_0 @ X21)
% 0.80/1.01          | ~ (m1_pre_topc @ X22 @ X21)
% 0.80/1.01          | (l1_pre_topc @ (k8_tmap_1 @ X21 @ X22)))),
% 0.80/1.01      inference('cnf', [status(esa)], [dt_k8_tmap_1])).
% 0.80/1.01  thf('16', plain,
% 0.80/1.01      (((l1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B_1))
% 0.80/1.01        | (v2_struct_0 @ sk_A)
% 0.80/1.01        | ~ (v2_pre_topc @ sk_A)
% 0.80/1.01        | ~ (l1_pre_topc @ sk_A))),
% 0.80/1.01      inference('sup-', [status(thm)], ['14', '15'])).
% 0.80/1.01  thf('17', plain, ((v2_pre_topc @ sk_A)),
% 0.80/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.01  thf('18', plain, ((l1_pre_topc @ sk_A)),
% 0.80/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.01  thf('19', plain,
% 0.80/1.01      (((l1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B_1)) | (v2_struct_0 @ sk_A))),
% 0.80/1.01      inference('demod', [status(thm)], ['16', '17', '18'])).
% 0.80/1.01  thf('20', plain, (~ (v2_struct_0 @ sk_A)),
% 0.80/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.01  thf('21', plain, ((l1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B_1))),
% 0.80/1.01      inference('clc', [status(thm)], ['19', '20'])).
% 0.80/1.01  thf('22', plain, ((m1_pre_topc @ sk_B_1 @ sk_A)),
% 0.80/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.01  thf('23', plain,
% 0.80/1.01      (![X21 : $i, X22 : $i]:
% 0.80/1.01         (~ (l1_pre_topc @ X21)
% 0.80/1.01          | ~ (v2_pre_topc @ X21)
% 0.80/1.01          | (v2_struct_0 @ X21)
% 0.80/1.01          | ~ (m1_pre_topc @ X22 @ X21)
% 0.80/1.01          | (v2_pre_topc @ (k8_tmap_1 @ X21 @ X22)))),
% 0.80/1.01      inference('cnf', [status(esa)], [dt_k8_tmap_1])).
% 0.80/1.01  thf('24', plain,
% 0.80/1.01      (((v2_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B_1))
% 0.80/1.01        | (v2_struct_0 @ sk_A)
% 0.80/1.01        | ~ (v2_pre_topc @ sk_A)
% 0.80/1.01        | ~ (l1_pre_topc @ sk_A))),
% 0.80/1.01      inference('sup-', [status(thm)], ['22', '23'])).
% 0.80/1.01  thf('25', plain, ((v2_pre_topc @ sk_A)),
% 0.80/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.01  thf('26', plain, ((l1_pre_topc @ sk_A)),
% 0.80/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.01  thf('27', plain,
% 0.80/1.01      (((v2_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B_1)) | (v2_struct_0 @ sk_A))),
% 0.80/1.01      inference('demod', [status(thm)], ['24', '25', '26'])).
% 0.80/1.01  thf('28', plain, (~ (v2_struct_0 @ sk_A)),
% 0.80/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.01  thf('29', plain, ((v2_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B_1))),
% 0.80/1.01      inference('clc', [status(thm)], ['27', '28'])).
% 0.80/1.01  thf('30', plain, ((m1_pre_topc @ sk_B_1 @ sk_A)),
% 0.80/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.01  thf('31', plain,
% 0.80/1.01      (![X21 : $i, X22 : $i]:
% 0.80/1.01         (~ (l1_pre_topc @ X21)
% 0.80/1.01          | ~ (v2_pre_topc @ X21)
% 0.80/1.01          | (v2_struct_0 @ X21)
% 0.80/1.01          | ~ (m1_pre_topc @ X22 @ X21)
% 0.80/1.01          | (v1_pre_topc @ (k8_tmap_1 @ X21 @ X22)))),
% 0.80/1.01      inference('cnf', [status(esa)], [dt_k8_tmap_1])).
% 0.80/1.01  thf('32', plain,
% 0.80/1.01      (((v1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B_1))
% 0.80/1.01        | (v2_struct_0 @ sk_A)
% 0.80/1.01        | ~ (v2_pre_topc @ sk_A)
% 0.80/1.01        | ~ (l1_pre_topc @ sk_A))),
% 0.80/1.01      inference('sup-', [status(thm)], ['30', '31'])).
% 0.80/1.01  thf('33', plain, ((v2_pre_topc @ sk_A)),
% 0.80/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.01  thf('34', plain, ((l1_pre_topc @ sk_A)),
% 0.80/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.01  thf('35', plain,
% 0.80/1.01      (((v1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B_1)) | (v2_struct_0 @ sk_A))),
% 0.80/1.01      inference('demod', [status(thm)], ['32', '33', '34'])).
% 0.80/1.01  thf('36', plain, (~ (v2_struct_0 @ sk_A)),
% 0.80/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.01  thf('37', plain, ((v1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B_1))),
% 0.80/1.01      inference('clc', [status(thm)], ['35', '36'])).
% 0.80/1.01  thf('38', plain, ((l1_pre_topc @ sk_A)),
% 0.80/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.01  thf('39', plain, ((v2_pre_topc @ sk_A)),
% 0.80/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.01  thf('40', plain,
% 0.80/1.01      ((((k8_tmap_1 @ sk_A @ sk_B_1)
% 0.80/1.01          = (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B_1)))
% 0.80/1.01        | (v2_struct_0 @ sk_A))),
% 0.80/1.01      inference('demod', [status(thm)],
% 0.80/1.01                ['12', '13', '21', '29', '37', '38', '39'])).
% 0.80/1.01  thf('41', plain, (~ (v2_struct_0 @ sk_A)),
% 0.80/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.01  thf('42', plain,
% 0.80/1.01      (((k8_tmap_1 @ sk_A @ sk_B_1)
% 0.80/1.01         = (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B_1)))),
% 0.80/1.01      inference('clc', [status(thm)], ['40', '41'])).
% 0.80/1.01  thf('43', plain,
% 0.80/1.01      ((m1_subset_1 @ (u1_struct_0 @ sk_B_1) @ 
% 0.80/1.01        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.80/1.01      inference('demod', [status(thm)], ['3', '4'])).
% 0.80/1.01  thf(d10_tmap_1, axiom,
% 0.80/1.01    (![A:$i]:
% 0.80/1.01     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.80/1.01       ( ![B:$i]:
% 0.80/1.01         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.80/1.01           ( ( k7_tmap_1 @ A @ B ) = ( k6_partfun1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.80/1.01  thf('44', plain,
% 0.80/1.01      (![X9 : $i, X10 : $i]:
% 0.80/1.01         (~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 0.80/1.01          | ((k7_tmap_1 @ X10 @ X9) = (k6_partfun1 @ (u1_struct_0 @ X10)))
% 0.80/1.01          | ~ (l1_pre_topc @ X10)
% 0.80/1.01          | ~ (v2_pre_topc @ X10)
% 0.80/1.01          | (v2_struct_0 @ X10))),
% 0.80/1.01      inference('cnf', [status(esa)], [d10_tmap_1])).
% 0.80/1.01  thf('45', plain,
% 0.80/1.01      (((v2_struct_0 @ sk_A)
% 0.80/1.01        | ~ (v2_pre_topc @ sk_A)
% 0.80/1.01        | ~ (l1_pre_topc @ sk_A)
% 0.80/1.01        | ((k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B_1))
% 0.80/1.01            = (k6_partfun1 @ (u1_struct_0 @ sk_A))))),
% 0.80/1.01      inference('sup-', [status(thm)], ['43', '44'])).
% 0.80/1.01  thf('46', plain, ((v2_pre_topc @ sk_A)),
% 0.80/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.01  thf('47', plain, ((l1_pre_topc @ sk_A)),
% 0.80/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.01  thf('48', plain,
% 0.80/1.01      (((v2_struct_0 @ sk_A)
% 0.80/1.01        | ((k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B_1))
% 0.80/1.01            = (k6_partfun1 @ (u1_struct_0 @ sk_A))))),
% 0.80/1.01      inference('demod', [status(thm)], ['45', '46', '47'])).
% 0.80/1.01  thf('49', plain, (~ (v2_struct_0 @ sk_A)),
% 0.80/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.01  thf('50', plain,
% 0.80/1.01      (((k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B_1))
% 0.80/1.01         = (k6_partfun1 @ (u1_struct_0 @ sk_A)))),
% 0.80/1.01      inference('clc', [status(thm)], ['48', '49'])).
% 0.80/1.01  thf('51', plain,
% 0.80/1.01      (((k8_tmap_1 @ sk_A @ sk_B_1)
% 0.80/1.01         = (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B_1)))),
% 0.80/1.01      inference('clc', [status(thm)], ['40', '41'])).
% 0.80/1.01  thf('52', plain, ((m1_pre_topc @ sk_B_1 @ sk_A)),
% 0.80/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.01  thf('53', plain, ((l1_pre_topc @ sk_A)),
% 0.80/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.01  thf('54', plain, ((v2_pre_topc @ sk_A)),
% 0.80/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.01  thf('55', plain,
% 0.80/1.01      (((m1_subset_1 @ 
% 0.80/1.01         (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B_1) @ 
% 0.80/1.01          (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ sk_B_1) @ 
% 0.80/1.01         (k1_zfmisc_1 @ 
% 0.80/1.01          (k2_zfmisc_1 @ (u1_struct_0 @ sk_B_1) @ 
% 0.80/1.01           (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B_1)))))
% 0.80/1.01        | (v2_struct_0 @ sk_B_1)
% 0.80/1.01        | (v2_struct_0 @ sk_A))),
% 0.80/1.01      inference('demod', [status(thm)],
% 0.80/1.01                ['8', '42', '50', '51', '52', '53', '54'])).
% 0.80/1.01  thf('56', plain,
% 0.80/1.01      ((~ (v1_funct_1 @ 
% 0.80/1.01           (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B_1) @ 
% 0.80/1.01            (k9_tmap_1 @ sk_A @ sk_B_1) @ sk_B_1))
% 0.80/1.01        | ~ (v1_funct_2 @ 
% 0.80/1.01             (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B_1) @ 
% 0.80/1.01              (k9_tmap_1 @ sk_A @ sk_B_1) @ sk_B_1) @ 
% 0.80/1.01             (u1_struct_0 @ sk_B_1) @ 
% 0.80/1.01             (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B_1)))
% 0.80/1.01        | ~ (v5_pre_topc @ 
% 0.80/1.01             (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B_1) @ 
% 0.80/1.01              (k9_tmap_1 @ sk_A @ sk_B_1) @ sk_B_1) @ 
% 0.80/1.01             sk_B_1 @ (k8_tmap_1 @ sk_A @ sk_B_1))
% 0.80/1.01        | ~ (m1_subset_1 @ 
% 0.80/1.01             (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B_1) @ 
% 0.80/1.01              (k9_tmap_1 @ sk_A @ sk_B_1) @ sk_B_1) @ 
% 0.80/1.01             (k1_zfmisc_1 @ 
% 0.80/1.01              (k2_zfmisc_1 @ (u1_struct_0 @ sk_B_1) @ 
% 0.80/1.01               (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B_1))))))),
% 0.80/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.01  thf('57', plain,
% 0.80/1.01      ((~ (m1_subset_1 @ 
% 0.80/1.01           (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B_1) @ 
% 0.80/1.01            (k9_tmap_1 @ sk_A @ sk_B_1) @ sk_B_1) @ 
% 0.80/1.01           (k1_zfmisc_1 @ 
% 0.80/1.01            (k2_zfmisc_1 @ (u1_struct_0 @ sk_B_1) @ 
% 0.80/1.01             (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B_1))))))
% 0.80/1.01         <= (~
% 0.80/1.01             ((m1_subset_1 @ 
% 0.80/1.01               (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B_1) @ 
% 0.80/1.01                (k9_tmap_1 @ sk_A @ sk_B_1) @ sk_B_1) @ 
% 0.80/1.01               (k1_zfmisc_1 @ 
% 0.80/1.01                (k2_zfmisc_1 @ (u1_struct_0 @ sk_B_1) @ 
% 0.80/1.01                 (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B_1)))))))),
% 0.80/1.01      inference('split', [status(esa)], ['56'])).
% 0.80/1.01  thf('58', plain, ((m1_pre_topc @ sk_B_1 @ sk_A)),
% 0.80/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.01  thf(dt_k9_tmap_1, axiom,
% 0.80/1.01    (![A:$i,B:$i]:
% 0.80/1.01     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.80/1.01         ( l1_pre_topc @ A ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.80/1.01       ( ( v1_funct_1 @ ( k9_tmap_1 @ A @ B ) ) & 
% 0.80/1.01         ( v1_funct_2 @
% 0.80/1.01           ( k9_tmap_1 @ A @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.80/1.01           ( u1_struct_0 @ ( k8_tmap_1 @ A @ B ) ) ) & 
% 0.80/1.01         ( m1_subset_1 @
% 0.80/1.01           ( k9_tmap_1 @ A @ B ) @ 
% 0.80/1.01           ( k1_zfmisc_1 @
% 0.80/1.01             ( k2_zfmisc_1 @
% 0.80/1.01               ( u1_struct_0 @ A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ A @ B ) ) ) ) ) ) ))).
% 0.80/1.01  thf('59', plain,
% 0.80/1.01      (![X23 : $i, X24 : $i]:
% 0.80/1.01         (~ (l1_pre_topc @ X23)
% 0.80/1.01          | ~ (v2_pre_topc @ X23)
% 0.80/1.01          | (v2_struct_0 @ X23)
% 0.80/1.01          | ~ (m1_pre_topc @ X24 @ X23)
% 0.80/1.01          | (m1_subset_1 @ (k9_tmap_1 @ X23 @ X24) @ 
% 0.80/1.01             (k1_zfmisc_1 @ 
% 0.80/1.01              (k2_zfmisc_1 @ (u1_struct_0 @ X23) @ 
% 0.80/1.01               (u1_struct_0 @ (k8_tmap_1 @ X23 @ X24))))))),
% 0.80/1.01      inference('cnf', [status(esa)], [dt_k9_tmap_1])).
% 0.80/1.01  thf('60', plain,
% 0.80/1.01      (((m1_subset_1 @ (k9_tmap_1 @ sk_A @ sk_B_1) @ 
% 0.80/1.01         (k1_zfmisc_1 @ 
% 0.80/1.01          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.80/1.01           (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B_1)))))
% 0.80/1.01        | (v2_struct_0 @ sk_A)
% 0.80/1.01        | ~ (v2_pre_topc @ sk_A)
% 0.80/1.01        | ~ (l1_pre_topc @ sk_A))),
% 0.80/1.01      inference('sup-', [status(thm)], ['58', '59'])).
% 0.80/1.01  thf('61', plain, ((v2_pre_topc @ sk_A)),
% 0.80/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.01  thf('62', plain, ((l1_pre_topc @ sk_A)),
% 0.80/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.01  thf('63', plain,
% 0.80/1.01      (((m1_subset_1 @ (k9_tmap_1 @ sk_A @ sk_B_1) @ 
% 0.80/1.01         (k1_zfmisc_1 @ 
% 0.80/1.01          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.80/1.01           (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B_1)))))
% 0.80/1.01        | (v2_struct_0 @ sk_A))),
% 0.80/1.01      inference('demod', [status(thm)], ['60', '61', '62'])).
% 0.80/1.01  thf('64', plain, (~ (v2_struct_0 @ sk_A)),
% 0.80/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.01  thf('65', plain,
% 0.80/1.01      ((m1_subset_1 @ (k9_tmap_1 @ sk_A @ sk_B_1) @ 
% 0.80/1.01        (k1_zfmisc_1 @ 
% 0.80/1.01         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.80/1.01          (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B_1)))))),
% 0.80/1.01      inference('clc', [status(thm)], ['63', '64'])).
% 0.80/1.01  thf(d12_tmap_1, axiom,
% 0.80/1.01    (![A:$i]:
% 0.80/1.01     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.80/1.01       ( ![B:$i]:
% 0.80/1.01         ( ( m1_pre_topc @ B @ A ) =>
% 0.80/1.01           ( ![C:$i]:
% 0.80/1.01             ( ( ( v1_funct_1 @ C ) & 
% 0.80/1.01                 ( v1_funct_2 @
% 0.80/1.01                   C @ ( u1_struct_0 @ A ) @ 
% 0.80/1.01                   ( u1_struct_0 @ ( k8_tmap_1 @ A @ B ) ) ) & 
% 0.80/1.01                 ( m1_subset_1 @
% 0.80/1.01                   C @ 
% 0.80/1.01                   ( k1_zfmisc_1 @
% 0.80/1.01                     ( k2_zfmisc_1 @
% 0.80/1.01                       ( u1_struct_0 @ A ) @ 
% 0.80/1.01                       ( u1_struct_0 @ ( k8_tmap_1 @ A @ B ) ) ) ) ) ) =>
% 0.80/1.01               ( ( ( C ) = ( k9_tmap_1 @ A @ B ) ) <=>
% 0.80/1.01                 ( ![D:$i]:
% 0.80/1.01                   ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.80/1.01                     ( ( ( D ) = ( u1_struct_0 @ B ) ) =>
% 0.80/1.01                       ( r1_funct_2 @
% 0.80/1.01                         ( u1_struct_0 @ A ) @ 
% 0.80/1.01                         ( u1_struct_0 @ ( k8_tmap_1 @ A @ B ) ) @ 
% 0.80/1.01                         ( u1_struct_0 @ A ) @ 
% 0.80/1.01                         ( u1_struct_0 @ ( k6_tmap_1 @ A @ D ) ) @ C @ 
% 0.80/1.01                         ( k7_tmap_1 @ A @ D ) ) ) ) ) ) ) ) ) ) ))).
% 0.80/1.01  thf('66', plain,
% 0.80/1.01      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.80/1.01         (~ (m1_pre_topc @ X15 @ X16)
% 0.80/1.01          | ((X17) != (k9_tmap_1 @ X16 @ X15))
% 0.80/1.01          | ((X18) != (u1_struct_0 @ X15))
% 0.80/1.01          | (r1_funct_2 @ (u1_struct_0 @ X16) @ 
% 0.80/1.01             (u1_struct_0 @ (k8_tmap_1 @ X16 @ X15)) @ (u1_struct_0 @ X16) @ 
% 0.80/1.01             (u1_struct_0 @ (k6_tmap_1 @ X16 @ X18)) @ X17 @ 
% 0.80/1.01             (k7_tmap_1 @ X16 @ X18))
% 0.80/1.01          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.80/1.01          | ~ (m1_subset_1 @ X17 @ 
% 0.80/1.01               (k1_zfmisc_1 @ 
% 0.80/1.01                (k2_zfmisc_1 @ (u1_struct_0 @ X16) @ 
% 0.80/1.01                 (u1_struct_0 @ (k8_tmap_1 @ X16 @ X15)))))
% 0.80/1.01          | ~ (v1_funct_2 @ X17 @ (u1_struct_0 @ X16) @ 
% 0.80/1.01               (u1_struct_0 @ (k8_tmap_1 @ X16 @ X15)))
% 0.80/1.01          | ~ (v1_funct_1 @ X17)
% 0.80/1.01          | ~ (l1_pre_topc @ X16)
% 0.80/1.01          | ~ (v2_pre_topc @ X16)
% 0.80/1.01          | (v2_struct_0 @ X16))),
% 0.80/1.01      inference('cnf', [status(esa)], [d12_tmap_1])).
% 0.80/1.01  thf('67', plain,
% 0.80/1.01      (![X15 : $i, X16 : $i]:
% 0.80/1.01         ((v2_struct_0 @ X16)
% 0.80/1.01          | ~ (v2_pre_topc @ X16)
% 0.80/1.01          | ~ (l1_pre_topc @ X16)
% 0.80/1.01          | ~ (v1_funct_1 @ (k9_tmap_1 @ X16 @ X15))
% 0.80/1.01          | ~ (v1_funct_2 @ (k9_tmap_1 @ X16 @ X15) @ (u1_struct_0 @ X16) @ 
% 0.80/1.01               (u1_struct_0 @ (k8_tmap_1 @ X16 @ X15)))
% 0.80/1.01          | ~ (m1_subset_1 @ (k9_tmap_1 @ X16 @ X15) @ 
% 0.80/1.01               (k1_zfmisc_1 @ 
% 0.80/1.01                (k2_zfmisc_1 @ (u1_struct_0 @ X16) @ 
% 0.80/1.01                 (u1_struct_0 @ (k8_tmap_1 @ X16 @ X15)))))
% 0.80/1.01          | ~ (m1_subset_1 @ (u1_struct_0 @ X15) @ 
% 0.80/1.01               (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.80/1.01          | (r1_funct_2 @ (u1_struct_0 @ X16) @ 
% 0.80/1.01             (u1_struct_0 @ (k8_tmap_1 @ X16 @ X15)) @ (u1_struct_0 @ X16) @ 
% 0.80/1.01             (u1_struct_0 @ (k6_tmap_1 @ X16 @ (u1_struct_0 @ X15))) @ 
% 0.80/1.01             (k9_tmap_1 @ X16 @ X15) @ (k7_tmap_1 @ X16 @ (u1_struct_0 @ X15)))
% 0.80/1.01          | ~ (m1_pre_topc @ X15 @ X16))),
% 0.80/1.01      inference('simplify', [status(thm)], ['66'])).
% 0.80/1.01  thf('68', plain,
% 0.80/1.01      ((~ (m1_pre_topc @ sk_B_1 @ sk_A)
% 0.80/1.01        | (r1_funct_2 @ (u1_struct_0 @ sk_A) @ 
% 0.80/1.01           (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B_1)) @ 
% 0.80/1.01           (u1_struct_0 @ sk_A) @ 
% 0.80/1.01           (u1_struct_0 @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B_1))) @ 
% 0.80/1.01           (k9_tmap_1 @ sk_A @ sk_B_1) @ 
% 0.80/1.01           (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B_1)))
% 0.80/1.01        | ~ (m1_subset_1 @ (u1_struct_0 @ sk_B_1) @ 
% 0.80/1.01             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.80/1.01        | ~ (v1_funct_2 @ (k9_tmap_1 @ sk_A @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 0.80/1.01             (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B_1)))
% 0.80/1.01        | ~ (v1_funct_1 @ (k9_tmap_1 @ sk_A @ sk_B_1))
% 0.80/1.01        | ~ (l1_pre_topc @ sk_A)
% 0.80/1.01        | ~ (v2_pre_topc @ sk_A)
% 0.80/1.01        | (v2_struct_0 @ sk_A))),
% 0.80/1.01      inference('sup-', [status(thm)], ['65', '67'])).
% 0.80/1.01  thf('69', plain, ((m1_pre_topc @ sk_B_1 @ sk_A)),
% 0.80/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.01  thf('70', plain,
% 0.80/1.01      (((k8_tmap_1 @ sk_A @ sk_B_1)
% 0.80/1.01         = (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B_1)))),
% 0.80/1.01      inference('clc', [status(thm)], ['40', '41'])).
% 0.80/1.01  thf('71', plain,
% 0.80/1.01      (((k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B_1))
% 0.80/1.01         = (k6_partfun1 @ (u1_struct_0 @ sk_A)))),
% 0.80/1.01      inference('clc', [status(thm)], ['48', '49'])).
% 0.80/1.01  thf('72', plain,
% 0.80/1.01      ((m1_subset_1 @ (u1_struct_0 @ sk_B_1) @ 
% 0.80/1.01        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.80/1.01      inference('demod', [status(thm)], ['3', '4'])).
% 0.80/1.01  thf('73', plain, ((m1_pre_topc @ sk_B_1 @ sk_A)),
% 0.80/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.01  thf('74', plain,
% 0.80/1.01      (![X23 : $i, X24 : $i]:
% 0.80/1.01         (~ (l1_pre_topc @ X23)
% 0.80/1.01          | ~ (v2_pre_topc @ X23)
% 0.80/1.01          | (v2_struct_0 @ X23)
% 0.80/1.01          | ~ (m1_pre_topc @ X24 @ X23)
% 0.80/1.01          | (v1_funct_2 @ (k9_tmap_1 @ X23 @ X24) @ (u1_struct_0 @ X23) @ 
% 0.80/1.01             (u1_struct_0 @ (k8_tmap_1 @ X23 @ X24))))),
% 0.80/1.01      inference('cnf', [status(esa)], [dt_k9_tmap_1])).
% 0.80/1.01  thf('75', plain,
% 0.80/1.01      (((v1_funct_2 @ (k9_tmap_1 @ sk_A @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 0.80/1.01         (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B_1)))
% 0.80/1.01        | (v2_struct_0 @ sk_A)
% 0.80/1.01        | ~ (v2_pre_topc @ sk_A)
% 0.80/1.01        | ~ (l1_pre_topc @ sk_A))),
% 0.80/1.01      inference('sup-', [status(thm)], ['73', '74'])).
% 0.80/1.01  thf('76', plain, ((v2_pre_topc @ sk_A)),
% 0.80/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.01  thf('77', plain, ((l1_pre_topc @ sk_A)),
% 0.80/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.01  thf('78', plain,
% 0.80/1.01      (((v1_funct_2 @ (k9_tmap_1 @ sk_A @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 0.80/1.01         (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B_1)))
% 0.80/1.01        | (v2_struct_0 @ sk_A))),
% 0.80/1.01      inference('demod', [status(thm)], ['75', '76', '77'])).
% 0.80/1.01  thf('79', plain, (~ (v2_struct_0 @ sk_A)),
% 0.80/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.01  thf('80', plain,
% 0.80/1.01      ((v1_funct_2 @ (k9_tmap_1 @ sk_A @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 0.80/1.01        (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B_1)))),
% 0.80/1.01      inference('clc', [status(thm)], ['78', '79'])).
% 0.80/1.01  thf('81', plain, ((m1_pre_topc @ sk_B_1 @ sk_A)),
% 0.80/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.01  thf('82', plain,
% 0.80/1.01      (![X23 : $i, X24 : $i]:
% 0.80/1.01         (~ (l1_pre_topc @ X23)
% 0.80/1.01          | ~ (v2_pre_topc @ X23)
% 0.80/1.01          | (v2_struct_0 @ X23)
% 0.80/1.01          | ~ (m1_pre_topc @ X24 @ X23)
% 0.80/1.01          | (v1_funct_1 @ (k9_tmap_1 @ X23 @ X24)))),
% 0.80/1.01      inference('cnf', [status(esa)], [dt_k9_tmap_1])).
% 0.80/1.01  thf('83', plain,
% 0.80/1.01      (((v1_funct_1 @ (k9_tmap_1 @ sk_A @ sk_B_1))
% 0.80/1.01        | (v2_struct_0 @ sk_A)
% 0.80/1.01        | ~ (v2_pre_topc @ sk_A)
% 0.80/1.01        | ~ (l1_pre_topc @ sk_A))),
% 0.80/1.01      inference('sup-', [status(thm)], ['81', '82'])).
% 0.80/1.01  thf('84', plain, ((v2_pre_topc @ sk_A)),
% 0.80/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.01  thf('85', plain, ((l1_pre_topc @ sk_A)),
% 0.80/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.01  thf('86', plain,
% 0.80/1.01      (((v1_funct_1 @ (k9_tmap_1 @ sk_A @ sk_B_1)) | (v2_struct_0 @ sk_A))),
% 0.80/1.01      inference('demod', [status(thm)], ['83', '84', '85'])).
% 0.80/1.01  thf('87', plain, (~ (v2_struct_0 @ sk_A)),
% 0.80/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.01  thf('88', plain, ((v1_funct_1 @ (k9_tmap_1 @ sk_A @ sk_B_1))),
% 0.80/1.01      inference('clc', [status(thm)], ['86', '87'])).
% 0.80/1.01  thf('89', plain, ((l1_pre_topc @ sk_A)),
% 0.80/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.01  thf('90', plain, ((v2_pre_topc @ sk_A)),
% 0.80/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.01  thf('91', plain,
% 0.80/1.01      (((r1_funct_2 @ (u1_struct_0 @ sk_A) @ 
% 0.80/1.01         (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B_1)) @ (u1_struct_0 @ sk_A) @ 
% 0.80/1.01         (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B_1)) @ 
% 0.80/1.01         (k9_tmap_1 @ sk_A @ sk_B_1) @ (k6_partfun1 @ (u1_struct_0 @ sk_A)))
% 0.80/1.01        | (v2_struct_0 @ sk_A))),
% 0.80/1.01      inference('demod', [status(thm)],
% 0.80/1.01                ['68', '69', '70', '71', '72', '80', '88', '89', '90'])).
% 0.80/1.01  thf('92', plain, (~ (v2_struct_0 @ sk_A)),
% 0.80/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.01  thf('93', plain,
% 0.80/1.01      ((r1_funct_2 @ (u1_struct_0 @ sk_A) @ 
% 0.80/1.01        (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B_1)) @ (u1_struct_0 @ sk_A) @ 
% 0.80/1.01        (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B_1)) @ 
% 0.80/1.01        (k9_tmap_1 @ sk_A @ sk_B_1) @ (k6_partfun1 @ (u1_struct_0 @ sk_A)))),
% 0.80/1.01      inference('clc', [status(thm)], ['91', '92'])).
% 0.80/1.01  thf('94', plain,
% 0.80/1.01      ((m1_subset_1 @ (k9_tmap_1 @ sk_A @ sk_B_1) @ 
% 0.80/1.01        (k1_zfmisc_1 @ 
% 0.80/1.01         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.80/1.01          (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B_1)))))),
% 0.80/1.01      inference('clc', [status(thm)], ['63', '64'])).
% 0.80/1.01  thf(redefinition_r1_funct_2, axiom,
% 0.80/1.01    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.80/1.01     ( ( ( ~( v1_xboole_0 @ B ) ) & ( ~( v1_xboole_0 @ D ) ) & 
% 0.80/1.01         ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ A @ B ) & 
% 0.80/1.01         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.80/1.01         ( v1_funct_1 @ F ) & ( v1_funct_2 @ F @ C @ D ) & 
% 0.80/1.01         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.80/1.01       ( ( r1_funct_2 @ A @ B @ C @ D @ E @ F ) <=> ( ( E ) = ( F ) ) ) ))).
% 0.80/1.01  thf('95', plain,
% 0.80/1.01      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.80/1.01         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X4 @ X5)))
% 0.80/1.01          | ~ (v1_funct_2 @ X3 @ X4 @ X5)
% 0.80/1.01          | ~ (v1_funct_1 @ X3)
% 0.80/1.01          | (v1_xboole_0 @ X6)
% 0.80/1.01          | (v1_xboole_0 @ X5)
% 0.80/1.01          | ~ (v1_funct_1 @ X7)
% 0.80/1.01          | ~ (v1_funct_2 @ X7 @ X8 @ X6)
% 0.80/1.01          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X6)))
% 0.80/1.01          | ((X3) = (X7))
% 0.80/1.01          | ~ (r1_funct_2 @ X4 @ X5 @ X8 @ X6 @ X3 @ X7))),
% 0.80/1.01      inference('cnf', [status(esa)], [redefinition_r1_funct_2])).
% 0.80/1.01  thf('96', plain,
% 0.80/1.01      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.80/1.01         (~ (r1_funct_2 @ (u1_struct_0 @ sk_A) @ 
% 0.80/1.01             (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B_1)) @ X2 @ X1 @ 
% 0.80/1.01             (k9_tmap_1 @ sk_A @ sk_B_1) @ X0)
% 0.80/1.01          | ((k9_tmap_1 @ sk_A @ sk_B_1) = (X0))
% 0.80/1.01          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.80/1.01          | ~ (v1_funct_2 @ X0 @ X2 @ X1)
% 0.80/1.01          | ~ (v1_funct_1 @ X0)
% 0.80/1.01          | (v1_xboole_0 @ (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B_1)))
% 0.80/1.01          | (v1_xboole_0 @ X1)
% 0.80/1.01          | ~ (v1_funct_1 @ (k9_tmap_1 @ sk_A @ sk_B_1))
% 0.80/1.01          | ~ (v1_funct_2 @ (k9_tmap_1 @ sk_A @ sk_B_1) @ 
% 0.80/1.01               (u1_struct_0 @ sk_A) @ 
% 0.80/1.01               (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B_1))))),
% 0.80/1.01      inference('sup-', [status(thm)], ['94', '95'])).
% 0.80/1.01  thf('97', plain, ((v1_funct_1 @ (k9_tmap_1 @ sk_A @ sk_B_1))),
% 0.80/1.01      inference('clc', [status(thm)], ['86', '87'])).
% 0.80/1.01  thf('98', plain,
% 0.80/1.01      ((v1_funct_2 @ (k9_tmap_1 @ sk_A @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 0.80/1.01        (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B_1)))),
% 0.80/1.01      inference('clc', [status(thm)], ['78', '79'])).
% 0.80/1.01  thf('99', plain,
% 0.80/1.01      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.80/1.01         (~ (r1_funct_2 @ (u1_struct_0 @ sk_A) @ 
% 0.80/1.01             (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B_1)) @ X2 @ X1 @ 
% 0.80/1.01             (k9_tmap_1 @ sk_A @ sk_B_1) @ X0)
% 0.80/1.01          | ((k9_tmap_1 @ sk_A @ sk_B_1) = (X0))
% 0.80/1.01          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.80/1.01          | ~ (v1_funct_2 @ X0 @ X2 @ X1)
% 0.80/1.01          | ~ (v1_funct_1 @ X0)
% 0.80/1.01          | (v1_xboole_0 @ (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B_1)))
% 0.80/1.01          | (v1_xboole_0 @ X1))),
% 0.80/1.01      inference('demod', [status(thm)], ['96', '97', '98'])).
% 0.80/1.01  thf('100', plain,
% 0.80/1.01      (((v1_xboole_0 @ (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B_1)))
% 0.80/1.01        | (v1_xboole_0 @ (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B_1)))
% 0.80/1.01        | ~ (v1_funct_1 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)))
% 0.80/1.01        | ~ (v1_funct_2 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 0.80/1.01             (u1_struct_0 @ sk_A) @ (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B_1)))
% 0.80/1.01        | ~ (m1_subset_1 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 0.80/1.01             (k1_zfmisc_1 @ 
% 0.80/1.01              (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.80/1.01               (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B_1)))))
% 0.80/1.01        | ((k9_tmap_1 @ sk_A @ sk_B_1) = (k6_partfun1 @ (u1_struct_0 @ sk_A))))),
% 0.80/1.01      inference('sup-', [status(thm)], ['93', '99'])).
% 0.80/1.01  thf('101', plain,
% 0.80/1.01      ((m1_subset_1 @ (u1_struct_0 @ sk_B_1) @ 
% 0.80/1.01        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.80/1.01      inference('demod', [status(thm)], ['3', '4'])).
% 0.80/1.01  thf(dt_k7_tmap_1, axiom,
% 0.80/1.01    (![A:$i,B:$i]:
% 0.80/1.01     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.80/1.01         ( l1_pre_topc @ A ) & 
% 0.80/1.01         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.80/1.01       ( ( v1_funct_1 @ ( k7_tmap_1 @ A @ B ) ) & 
% 0.80/1.01         ( v1_funct_2 @
% 0.80/1.01           ( k7_tmap_1 @ A @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.80/1.01           ( u1_struct_0 @ ( k6_tmap_1 @ A @ B ) ) ) & 
% 0.80/1.01         ( m1_subset_1 @
% 0.80/1.01           ( k7_tmap_1 @ A @ B ) @ 
% 0.80/1.01           ( k1_zfmisc_1 @
% 0.80/1.01             ( k2_zfmisc_1 @
% 0.80/1.01               ( u1_struct_0 @ A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ A @ B ) ) ) ) ) ) ))).
% 0.80/1.01  thf('102', plain,
% 0.80/1.01      (![X19 : $i, X20 : $i]:
% 0.80/1.01         (~ (l1_pre_topc @ X19)
% 0.80/1.01          | ~ (v2_pre_topc @ X19)
% 0.80/1.01          | (v2_struct_0 @ X19)
% 0.80/1.01          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.80/1.01          | (v1_funct_1 @ (k7_tmap_1 @ X19 @ X20)))),
% 0.80/1.01      inference('cnf', [status(esa)], [dt_k7_tmap_1])).
% 0.80/1.01  thf('103', plain,
% 0.80/1.01      (((v1_funct_1 @ (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B_1)))
% 0.80/1.01        | (v2_struct_0 @ sk_A)
% 0.80/1.01        | ~ (v2_pre_topc @ sk_A)
% 0.80/1.01        | ~ (l1_pre_topc @ sk_A))),
% 0.80/1.01      inference('sup-', [status(thm)], ['101', '102'])).
% 0.80/1.01  thf('104', plain, ((v2_pre_topc @ sk_A)),
% 0.80/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.01  thf('105', plain, ((l1_pre_topc @ sk_A)),
% 0.80/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.01  thf('106', plain,
% 0.80/1.01      (((v1_funct_1 @ (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B_1)))
% 0.80/1.01        | (v2_struct_0 @ sk_A))),
% 0.80/1.01      inference('demod', [status(thm)], ['103', '104', '105'])).
% 0.80/1.01  thf('107', plain, (~ (v2_struct_0 @ sk_A)),
% 0.80/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.01  thf('108', plain,
% 0.80/1.01      ((v1_funct_1 @ (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B_1)))),
% 0.80/1.01      inference('clc', [status(thm)], ['106', '107'])).
% 0.80/1.01  thf('109', plain,
% 0.80/1.01      (((k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B_1))
% 0.80/1.01         = (k6_partfun1 @ (u1_struct_0 @ sk_A)))),
% 0.80/1.01      inference('clc', [status(thm)], ['48', '49'])).
% 0.80/1.01  thf('110', plain, ((v1_funct_1 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)))),
% 0.80/1.01      inference('demod', [status(thm)], ['108', '109'])).
% 0.80/1.01  thf('111', plain,
% 0.80/1.01      ((m1_subset_1 @ (u1_struct_0 @ sk_B_1) @ 
% 0.80/1.01        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.80/1.01      inference('demod', [status(thm)], ['3', '4'])).
% 0.80/1.01  thf('112', plain,
% 0.80/1.01      (![X19 : $i, X20 : $i]:
% 0.80/1.01         (~ (l1_pre_topc @ X19)
% 0.80/1.01          | ~ (v2_pre_topc @ X19)
% 0.80/1.01          | (v2_struct_0 @ X19)
% 0.80/1.01          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.80/1.01          | (v1_funct_2 @ (k7_tmap_1 @ X19 @ X20) @ (u1_struct_0 @ X19) @ 
% 0.80/1.01             (u1_struct_0 @ (k6_tmap_1 @ X19 @ X20))))),
% 0.80/1.01      inference('cnf', [status(esa)], [dt_k7_tmap_1])).
% 0.80/1.01  thf('113', plain,
% 0.80/1.01      (((v1_funct_2 @ (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B_1)) @ 
% 0.80/1.01         (u1_struct_0 @ sk_A) @ 
% 0.80/1.01         (u1_struct_0 @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B_1))))
% 0.80/1.01        | (v2_struct_0 @ sk_A)
% 0.80/1.01        | ~ (v2_pre_topc @ sk_A)
% 0.80/1.01        | ~ (l1_pre_topc @ sk_A))),
% 0.80/1.01      inference('sup-', [status(thm)], ['111', '112'])).
% 0.80/1.01  thf('114', plain,
% 0.80/1.01      (((k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B_1))
% 0.80/1.01         = (k6_partfun1 @ (u1_struct_0 @ sk_A)))),
% 0.80/1.01      inference('clc', [status(thm)], ['48', '49'])).
% 0.80/1.01  thf('115', plain, ((v2_pre_topc @ sk_A)),
% 0.80/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.01  thf('116', plain, ((l1_pre_topc @ sk_A)),
% 0.80/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.01  thf('117', plain,
% 0.80/1.01      (((v1_funct_2 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 0.80/1.01         (u1_struct_0 @ sk_A) @ 
% 0.80/1.01         (u1_struct_0 @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B_1))))
% 0.80/1.01        | (v2_struct_0 @ sk_A))),
% 0.80/1.01      inference('demod', [status(thm)], ['113', '114', '115', '116'])).
% 0.80/1.01  thf('118', plain, (~ (v2_struct_0 @ sk_A)),
% 0.80/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.01  thf('119', plain,
% 0.80/1.01      ((v1_funct_2 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 0.80/1.01        (u1_struct_0 @ sk_A) @ 
% 0.80/1.01        (u1_struct_0 @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B_1))))),
% 0.80/1.01      inference('clc', [status(thm)], ['117', '118'])).
% 0.80/1.01  thf('120', plain,
% 0.80/1.01      (((k8_tmap_1 @ sk_A @ sk_B_1)
% 0.80/1.01         = (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B_1)))),
% 0.80/1.01      inference('clc', [status(thm)], ['40', '41'])).
% 0.80/1.01  thf('121', plain,
% 0.80/1.01      ((v1_funct_2 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 0.80/1.01        (u1_struct_0 @ sk_A) @ (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B_1)))),
% 0.80/1.01      inference('demod', [status(thm)], ['119', '120'])).
% 0.80/1.01  thf('122', plain,
% 0.80/1.01      ((m1_subset_1 @ (u1_struct_0 @ sk_B_1) @ 
% 0.80/1.01        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.80/1.01      inference('demod', [status(thm)], ['3', '4'])).
% 0.80/1.01  thf('123', plain,
% 0.80/1.01      (![X19 : $i, X20 : $i]:
% 0.80/1.01         (~ (l1_pre_topc @ X19)
% 0.80/1.01          | ~ (v2_pre_topc @ X19)
% 0.80/1.01          | (v2_struct_0 @ X19)
% 0.80/1.01          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.80/1.01          | (m1_subset_1 @ (k7_tmap_1 @ X19 @ X20) @ 
% 0.80/1.01             (k1_zfmisc_1 @ 
% 0.80/1.01              (k2_zfmisc_1 @ (u1_struct_0 @ X19) @ 
% 0.80/1.01               (u1_struct_0 @ (k6_tmap_1 @ X19 @ X20))))))),
% 0.80/1.01      inference('cnf', [status(esa)], [dt_k7_tmap_1])).
% 0.80/1.01  thf('124', plain,
% 0.80/1.01      (((m1_subset_1 @ (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B_1)) @ 
% 0.80/1.01         (k1_zfmisc_1 @ 
% 0.80/1.01          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.80/1.01           (u1_struct_0 @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B_1))))))
% 0.80/1.01        | (v2_struct_0 @ sk_A)
% 0.80/1.01        | ~ (v2_pre_topc @ sk_A)
% 0.80/1.01        | ~ (l1_pre_topc @ sk_A))),
% 0.80/1.01      inference('sup-', [status(thm)], ['122', '123'])).
% 0.80/1.01  thf('125', plain,
% 0.80/1.01      (((k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B_1))
% 0.80/1.01         = (k6_partfun1 @ (u1_struct_0 @ sk_A)))),
% 0.80/1.01      inference('clc', [status(thm)], ['48', '49'])).
% 0.80/1.01  thf('126', plain, ((v2_pre_topc @ sk_A)),
% 0.80/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.01  thf('127', plain, ((l1_pre_topc @ sk_A)),
% 0.80/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.01  thf('128', plain,
% 0.80/1.01      (((m1_subset_1 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 0.80/1.01         (k1_zfmisc_1 @ 
% 0.80/1.01          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.80/1.01           (u1_struct_0 @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B_1))))))
% 0.80/1.01        | (v2_struct_0 @ sk_A))),
% 0.80/1.01      inference('demod', [status(thm)], ['124', '125', '126', '127'])).
% 0.80/1.01  thf('129', plain, (~ (v2_struct_0 @ sk_A)),
% 0.80/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.01  thf('130', plain,
% 0.80/1.01      ((m1_subset_1 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 0.80/1.01        (k1_zfmisc_1 @ 
% 0.80/1.01         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.80/1.01          (u1_struct_0 @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B_1))))))),
% 0.80/1.01      inference('clc', [status(thm)], ['128', '129'])).
% 0.80/1.01  thf('131', plain,
% 0.80/1.01      (((k8_tmap_1 @ sk_A @ sk_B_1)
% 0.80/1.01         = (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B_1)))),
% 0.80/1.01      inference('clc', [status(thm)], ['40', '41'])).
% 0.80/1.01  thf('132', plain,
% 0.80/1.01      ((m1_subset_1 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 0.80/1.01        (k1_zfmisc_1 @ 
% 0.80/1.01         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.80/1.01          (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B_1)))))),
% 0.80/1.01      inference('demod', [status(thm)], ['130', '131'])).
% 0.80/1.01  thf('133', plain,
% 0.80/1.01      (((v1_xboole_0 @ (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B_1)))
% 0.80/1.01        | (v1_xboole_0 @ (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B_1)))
% 0.80/1.01        | ((k9_tmap_1 @ sk_A @ sk_B_1) = (k6_partfun1 @ (u1_struct_0 @ sk_A))))),
% 0.80/1.01      inference('demod', [status(thm)], ['100', '110', '121', '132'])).
% 0.80/1.01  thf('134', plain,
% 0.80/1.01      ((((k9_tmap_1 @ sk_A @ sk_B_1) = (k6_partfun1 @ (u1_struct_0 @ sk_A)))
% 0.80/1.01        | (v1_xboole_0 @ (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B_1))))),
% 0.80/1.01      inference('simplify', [status(thm)], ['133'])).
% 0.80/1.01  thf(fc2_struct_0, axiom,
% 0.80/1.01    (![A:$i]:
% 0.80/1.01     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.80/1.01       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.80/1.01  thf('135', plain,
% 0.80/1.01      (![X1 : $i]:
% 0.80/1.01         (~ (v1_xboole_0 @ (u1_struct_0 @ X1))
% 0.80/1.01          | ~ (l1_struct_0 @ X1)
% 0.80/1.01          | (v2_struct_0 @ X1))),
% 0.80/1.01      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.80/1.01  thf('136', plain,
% 0.80/1.01      ((((k9_tmap_1 @ sk_A @ sk_B_1) = (k6_partfun1 @ (u1_struct_0 @ sk_A)))
% 0.80/1.01        | (v2_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B_1))
% 0.80/1.01        | ~ (l1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B_1)))),
% 0.80/1.01      inference('sup-', [status(thm)], ['134', '135'])).
% 0.80/1.01  thf('137', plain, ((l1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B_1))),
% 0.80/1.01      inference('clc', [status(thm)], ['19', '20'])).
% 0.80/1.01  thf(dt_l1_pre_topc, axiom,
% 0.80/1.01    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.80/1.01  thf('138', plain, (![X0 : $i]: ((l1_struct_0 @ X0) | ~ (l1_pre_topc @ X0))),
% 0.80/1.01      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.80/1.01  thf('139', plain, ((l1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B_1))),
% 0.80/1.01      inference('sup-', [status(thm)], ['137', '138'])).
% 0.80/1.01  thf('140', plain,
% 0.80/1.01      ((((k9_tmap_1 @ sk_A @ sk_B_1) = (k6_partfun1 @ (u1_struct_0 @ sk_A)))
% 0.80/1.01        | (v2_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B_1)))),
% 0.80/1.01      inference('demod', [status(thm)], ['136', '139'])).
% 0.80/1.01  thf(fc5_tmap_1, axiom,
% 0.80/1.01    (![A:$i,B:$i]:
% 0.80/1.01     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.80/1.01         ( l1_pre_topc @ A ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.80/1.01       ( ( ~( v2_struct_0 @ ( k8_tmap_1 @ A @ B ) ) ) & 
% 0.80/1.01         ( v1_pre_topc @ ( k8_tmap_1 @ A @ B ) ) & 
% 0.80/1.01         ( v2_pre_topc @ ( k8_tmap_1 @ A @ B ) ) ) ))).
% 0.80/1.01  thf('141', plain,
% 0.80/1.01      (![X25 : $i, X26 : $i]:
% 0.80/1.01         (~ (l1_pre_topc @ X25)
% 0.80/1.01          | ~ (v2_pre_topc @ X25)
% 0.80/1.01          | (v2_struct_0 @ X25)
% 0.80/1.01          | ~ (m1_pre_topc @ X26 @ X25)
% 0.80/1.01          | ~ (v2_struct_0 @ (k8_tmap_1 @ X25 @ X26)))),
% 0.80/1.01      inference('cnf', [status(esa)], [fc5_tmap_1])).
% 0.80/1.01  thf('142', plain,
% 0.80/1.01      ((((k9_tmap_1 @ sk_A @ sk_B_1) = (k6_partfun1 @ (u1_struct_0 @ sk_A)))
% 0.80/1.01        | ~ (m1_pre_topc @ sk_B_1 @ sk_A)
% 0.80/1.01        | (v2_struct_0 @ sk_A)
% 0.80/1.01        | ~ (v2_pre_topc @ sk_A)
% 0.80/1.01        | ~ (l1_pre_topc @ sk_A))),
% 0.80/1.01      inference('sup-', [status(thm)], ['140', '141'])).
% 0.80/1.01  thf('143', plain, ((m1_pre_topc @ sk_B_1 @ sk_A)),
% 0.80/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.01  thf('144', plain, ((v2_pre_topc @ sk_A)),
% 0.80/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.01  thf('145', plain, ((l1_pre_topc @ sk_A)),
% 0.80/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.01  thf('146', plain,
% 0.80/1.01      ((((k9_tmap_1 @ sk_A @ sk_B_1) = (k6_partfun1 @ (u1_struct_0 @ sk_A)))
% 0.80/1.01        | (v2_struct_0 @ sk_A))),
% 0.80/1.01      inference('demod', [status(thm)], ['142', '143', '144', '145'])).
% 0.80/1.01  thf('147', plain, (~ (v2_struct_0 @ sk_A)),
% 0.80/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.01  thf('148', plain,
% 0.80/1.01      (((k9_tmap_1 @ sk_A @ sk_B_1) = (k6_partfun1 @ (u1_struct_0 @ sk_A)))),
% 0.80/1.01      inference('clc', [status(thm)], ['146', '147'])).
% 0.80/1.01  thf('149', plain,
% 0.80/1.01      ((~ (m1_subset_1 @ 
% 0.80/1.01           (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B_1) @ 
% 0.80/1.01            (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ sk_B_1) @ 
% 0.80/1.01           (k1_zfmisc_1 @ 
% 0.80/1.01            (k2_zfmisc_1 @ (u1_struct_0 @ sk_B_1) @ 
% 0.80/1.01             (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B_1))))))
% 0.80/1.01         <= (~
% 0.80/1.01             ((m1_subset_1 @ 
% 0.80/1.01               (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B_1) @ 
% 0.80/1.01                (k9_tmap_1 @ sk_A @ sk_B_1) @ sk_B_1) @ 
% 0.80/1.01               (k1_zfmisc_1 @ 
% 0.80/1.01                (k2_zfmisc_1 @ (u1_struct_0 @ sk_B_1) @ 
% 0.80/1.01                 (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B_1)))))))),
% 0.80/1.01      inference('demod', [status(thm)], ['57', '148'])).
% 0.80/1.01  thf('150', plain,
% 0.80/1.01      ((m1_subset_1 @ (u1_struct_0 @ sk_B_1) @ 
% 0.80/1.01        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.80/1.01      inference('demod', [status(thm)], ['3', '4'])).
% 0.80/1.01  thf('151', plain,
% 0.80/1.01      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.80/1.01         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 0.80/1.01          | ((u1_struct_0 @ X29) != (X27))
% 0.80/1.01          | (v1_funct_2 @ 
% 0.80/1.01             (k2_tmap_1 @ X28 @ (k6_tmap_1 @ X28 @ X27) @ 
% 0.80/1.01              (k7_tmap_1 @ X28 @ X27) @ X29) @ 
% 0.80/1.01             (u1_struct_0 @ X29) @ (u1_struct_0 @ (k6_tmap_1 @ X28 @ X27)))
% 0.80/1.01          | ~ (m1_pre_topc @ X29 @ X28)
% 0.80/1.01          | (v2_struct_0 @ X29)
% 0.80/1.01          | ~ (l1_pre_topc @ X28)
% 0.80/1.01          | ~ (v2_pre_topc @ X28)
% 0.80/1.01          | (v2_struct_0 @ X28))),
% 0.80/1.01      inference('cnf', [status(esa)], [t112_tmap_1])).
% 0.80/1.01  thf('152', plain,
% 0.80/1.01      (![X28 : $i, X29 : $i]:
% 0.80/1.01         ((v2_struct_0 @ X28)
% 0.80/1.01          | ~ (v2_pre_topc @ X28)
% 0.80/1.01          | ~ (l1_pre_topc @ X28)
% 0.80/1.01          | (v2_struct_0 @ X29)
% 0.80/1.01          | ~ (m1_pre_topc @ X29 @ X28)
% 0.80/1.01          | (v1_funct_2 @ 
% 0.80/1.01             (k2_tmap_1 @ X28 @ (k6_tmap_1 @ X28 @ (u1_struct_0 @ X29)) @ 
% 0.80/1.01              (k7_tmap_1 @ X28 @ (u1_struct_0 @ X29)) @ X29) @ 
% 0.80/1.01             (u1_struct_0 @ X29) @ 
% 0.80/1.01             (u1_struct_0 @ (k6_tmap_1 @ X28 @ (u1_struct_0 @ X29))))
% 0.80/1.01          | ~ (m1_subset_1 @ (u1_struct_0 @ X29) @ 
% 0.80/1.01               (k1_zfmisc_1 @ (u1_struct_0 @ X28))))),
% 0.80/1.01      inference('simplify', [status(thm)], ['151'])).
% 0.80/1.01  thf('153', plain,
% 0.80/1.01      (((v1_funct_2 @ 
% 0.80/1.01         (k2_tmap_1 @ sk_A @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B_1)) @ 
% 0.80/1.01          (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B_1)) @ sk_B_1) @ 
% 0.80/1.01         (u1_struct_0 @ sk_B_1) @ 
% 0.80/1.01         (u1_struct_0 @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B_1))))
% 0.80/1.01        | ~ (m1_pre_topc @ sk_B_1 @ sk_A)
% 0.80/1.01        | (v2_struct_0 @ sk_B_1)
% 0.80/1.01        | ~ (l1_pre_topc @ sk_A)
% 0.80/1.01        | ~ (v2_pre_topc @ sk_A)
% 0.80/1.01        | (v2_struct_0 @ sk_A))),
% 0.80/1.01      inference('sup-', [status(thm)], ['150', '152'])).
% 0.80/1.01  thf('154', plain,
% 0.80/1.01      (((k8_tmap_1 @ sk_A @ sk_B_1)
% 0.80/1.01         = (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B_1)))),
% 0.80/1.01      inference('clc', [status(thm)], ['40', '41'])).
% 0.80/1.01  thf('155', plain,
% 0.80/1.01      (((k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B_1))
% 0.80/1.01         = (k6_partfun1 @ (u1_struct_0 @ sk_A)))),
% 0.80/1.01      inference('clc', [status(thm)], ['48', '49'])).
% 0.80/1.01  thf('156', plain,
% 0.80/1.01      (((k8_tmap_1 @ sk_A @ sk_B_1)
% 0.80/1.01         = (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B_1)))),
% 0.80/1.01      inference('clc', [status(thm)], ['40', '41'])).
% 0.80/1.01  thf('157', plain, ((m1_pre_topc @ sk_B_1 @ sk_A)),
% 0.80/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.01  thf('158', plain, ((l1_pre_topc @ sk_A)),
% 0.80/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.01  thf('159', plain, ((v2_pre_topc @ sk_A)),
% 0.80/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.01  thf('160', plain,
% 0.80/1.01      (((v1_funct_2 @ 
% 0.80/1.01         (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B_1) @ 
% 0.80/1.01          (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ sk_B_1) @ 
% 0.80/1.01         (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B_1)))
% 0.80/1.01        | (v2_struct_0 @ sk_B_1)
% 0.80/1.01        | (v2_struct_0 @ sk_A))),
% 0.80/1.01      inference('demod', [status(thm)],
% 0.80/1.01                ['153', '154', '155', '156', '157', '158', '159'])).
% 0.80/1.01  thf('161', plain, (~ (v2_struct_0 @ sk_B_1)),
% 0.80/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.01  thf('162', plain,
% 0.80/1.01      (((v2_struct_0 @ sk_A)
% 0.80/1.01        | (v1_funct_2 @ 
% 0.80/1.01           (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B_1) @ 
% 0.80/1.01            (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ sk_B_1) @ 
% 0.80/1.01           (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B_1))))),
% 0.80/1.01      inference('clc', [status(thm)], ['160', '161'])).
% 0.80/1.01  thf('163', plain, (~ (v2_struct_0 @ sk_A)),
% 0.80/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.01  thf('164', plain,
% 0.80/1.01      ((v1_funct_2 @ 
% 0.80/1.01        (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B_1) @ 
% 0.80/1.01         (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ sk_B_1) @ 
% 0.80/1.01        (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B_1)))),
% 0.80/1.01      inference('clc', [status(thm)], ['162', '163'])).
% 0.80/1.01  thf('165', plain,
% 0.80/1.01      (((k9_tmap_1 @ sk_A @ sk_B_1) = (k6_partfun1 @ (u1_struct_0 @ sk_A)))),
% 0.80/1.01      inference('clc', [status(thm)], ['146', '147'])).
% 0.80/1.01  thf('166', plain,
% 0.80/1.01      ((~ (v1_funct_2 @ 
% 0.80/1.01           (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B_1) @ 
% 0.80/1.01            (k9_tmap_1 @ sk_A @ sk_B_1) @ sk_B_1) @ 
% 0.80/1.01           (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B_1))))
% 0.80/1.01         <= (~
% 0.80/1.01             ((v1_funct_2 @ 
% 0.80/1.01               (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B_1) @ 
% 0.80/1.01                (k9_tmap_1 @ sk_A @ sk_B_1) @ sk_B_1) @ 
% 0.80/1.01               (u1_struct_0 @ sk_B_1) @ 
% 0.80/1.01               (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B_1)))))),
% 0.80/1.01      inference('split', [status(esa)], ['56'])).
% 0.80/1.01  thf('167', plain,
% 0.80/1.01      ((~ (v1_funct_2 @ 
% 0.80/1.01           (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B_1) @ 
% 0.80/1.01            (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ sk_B_1) @ 
% 0.80/1.01           (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B_1))))
% 0.80/1.01         <= (~
% 0.80/1.01             ((v1_funct_2 @ 
% 0.80/1.01               (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B_1) @ 
% 0.80/1.01                (k9_tmap_1 @ sk_A @ sk_B_1) @ sk_B_1) @ 
% 0.80/1.01               (u1_struct_0 @ sk_B_1) @ 
% 0.80/1.01               (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B_1)))))),
% 0.80/1.01      inference('sup-', [status(thm)], ['165', '166'])).
% 0.80/1.01  thf('168', plain,
% 0.80/1.01      (((v1_funct_2 @ 
% 0.80/1.01         (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B_1) @ 
% 0.80/1.01          (k9_tmap_1 @ sk_A @ sk_B_1) @ sk_B_1) @ 
% 0.80/1.01         (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B_1))))),
% 0.80/1.01      inference('sup-', [status(thm)], ['164', '167'])).
% 0.80/1.01  thf('169', plain,
% 0.80/1.01      ((m1_subset_1 @ (u1_struct_0 @ sk_B_1) @ 
% 0.80/1.01        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.80/1.01      inference('demod', [status(thm)], ['3', '4'])).
% 0.80/1.01  thf('170', plain,
% 0.80/1.01      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.80/1.01         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 0.80/1.01          | ((u1_struct_0 @ X29) != (X27))
% 0.80/1.01          | (v1_funct_1 @ 
% 0.80/1.01             (k2_tmap_1 @ X28 @ (k6_tmap_1 @ X28 @ X27) @ 
% 0.80/1.01              (k7_tmap_1 @ X28 @ X27) @ X29))
% 0.80/1.01          | ~ (m1_pre_topc @ X29 @ X28)
% 0.80/1.01          | (v2_struct_0 @ X29)
% 0.80/1.01          | ~ (l1_pre_topc @ X28)
% 0.80/1.01          | ~ (v2_pre_topc @ X28)
% 0.80/1.01          | (v2_struct_0 @ X28))),
% 0.80/1.01      inference('cnf', [status(esa)], [t112_tmap_1])).
% 0.80/1.01  thf('171', plain,
% 0.80/1.01      (![X28 : $i, X29 : $i]:
% 0.80/1.01         ((v2_struct_0 @ X28)
% 0.80/1.01          | ~ (v2_pre_topc @ X28)
% 0.80/1.01          | ~ (l1_pre_topc @ X28)
% 0.80/1.01          | (v2_struct_0 @ X29)
% 0.80/1.01          | ~ (m1_pre_topc @ X29 @ X28)
% 0.80/1.01          | (v1_funct_1 @ 
% 0.80/1.01             (k2_tmap_1 @ X28 @ (k6_tmap_1 @ X28 @ (u1_struct_0 @ X29)) @ 
% 0.80/1.01              (k7_tmap_1 @ X28 @ (u1_struct_0 @ X29)) @ X29))
% 0.80/1.01          | ~ (m1_subset_1 @ (u1_struct_0 @ X29) @ 
% 0.80/1.01               (k1_zfmisc_1 @ (u1_struct_0 @ X28))))),
% 0.80/1.01      inference('simplify', [status(thm)], ['170'])).
% 0.80/1.01  thf('172', plain,
% 0.80/1.01      (((v1_funct_1 @ 
% 0.80/1.01         (k2_tmap_1 @ sk_A @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B_1)) @ 
% 0.80/1.01          (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B_1)) @ sk_B_1))
% 0.80/1.01        | ~ (m1_pre_topc @ sk_B_1 @ sk_A)
% 0.80/1.01        | (v2_struct_0 @ sk_B_1)
% 0.80/1.01        | ~ (l1_pre_topc @ sk_A)
% 0.80/1.01        | ~ (v2_pre_topc @ sk_A)
% 0.80/1.01        | (v2_struct_0 @ sk_A))),
% 0.80/1.01      inference('sup-', [status(thm)], ['169', '171'])).
% 0.80/1.01  thf('173', plain,
% 0.80/1.01      (((k8_tmap_1 @ sk_A @ sk_B_1)
% 0.80/1.01         = (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B_1)))),
% 0.80/1.01      inference('clc', [status(thm)], ['40', '41'])).
% 0.80/1.01  thf('174', plain,
% 0.80/1.01      (((k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B_1))
% 0.80/1.01         = (k6_partfun1 @ (u1_struct_0 @ sk_A)))),
% 0.80/1.01      inference('clc', [status(thm)], ['48', '49'])).
% 0.80/1.01  thf('175', plain, ((m1_pre_topc @ sk_B_1 @ sk_A)),
% 0.80/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.01  thf('176', plain, ((l1_pre_topc @ sk_A)),
% 0.80/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.01  thf('177', plain, ((v2_pre_topc @ sk_A)),
% 0.80/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.01  thf('178', plain,
% 0.80/1.01      (((v1_funct_1 @ 
% 0.80/1.01         (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B_1) @ 
% 0.80/1.01          (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ sk_B_1))
% 0.80/1.01        | (v2_struct_0 @ sk_B_1)
% 0.80/1.01        | (v2_struct_0 @ sk_A))),
% 0.80/1.01      inference('demod', [status(thm)],
% 0.80/1.01                ['172', '173', '174', '175', '176', '177'])).
% 0.80/1.01  thf('179', plain, (~ (v2_struct_0 @ sk_B_1)),
% 0.80/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.01  thf('180', plain,
% 0.80/1.01      (((v2_struct_0 @ sk_A)
% 0.80/1.01        | (v1_funct_1 @ 
% 0.80/1.01           (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B_1) @ 
% 0.80/1.01            (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ sk_B_1)))),
% 0.80/1.01      inference('clc', [status(thm)], ['178', '179'])).
% 0.80/1.01  thf('181', plain, (~ (v2_struct_0 @ sk_A)),
% 0.80/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.01  thf('182', plain,
% 0.80/1.01      ((v1_funct_1 @ 
% 0.80/1.01        (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B_1) @ 
% 0.80/1.01         (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ sk_B_1))),
% 0.80/1.01      inference('clc', [status(thm)], ['180', '181'])).
% 0.80/1.01  thf('183', plain,
% 0.80/1.01      (((k9_tmap_1 @ sk_A @ sk_B_1) = (k6_partfun1 @ (u1_struct_0 @ sk_A)))),
% 0.80/1.01      inference('clc', [status(thm)], ['146', '147'])).
% 0.80/1.01  thf('184', plain,
% 0.80/1.01      ((~ (v1_funct_1 @ 
% 0.80/1.01           (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B_1) @ 
% 0.80/1.01            (k9_tmap_1 @ sk_A @ sk_B_1) @ sk_B_1)))
% 0.80/1.01         <= (~
% 0.80/1.01             ((v1_funct_1 @ 
% 0.80/1.01               (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B_1) @ 
% 0.80/1.01                (k9_tmap_1 @ sk_A @ sk_B_1) @ sk_B_1))))),
% 0.80/1.01      inference('split', [status(esa)], ['56'])).
% 0.80/1.01  thf('185', plain,
% 0.80/1.01      ((~ (v1_funct_1 @ 
% 0.80/1.01           (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B_1) @ 
% 0.80/1.01            (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ sk_B_1)))
% 0.80/1.01         <= (~
% 0.80/1.01             ((v1_funct_1 @ 
% 0.80/1.01               (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B_1) @ 
% 0.80/1.01                (k9_tmap_1 @ sk_A @ sk_B_1) @ sk_B_1))))),
% 0.80/1.01      inference('sup-', [status(thm)], ['183', '184'])).
% 0.80/1.01  thf('186', plain,
% 0.80/1.01      (((v1_funct_1 @ 
% 0.80/1.01         (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B_1) @ 
% 0.80/1.01          (k9_tmap_1 @ sk_A @ sk_B_1) @ sk_B_1)))),
% 0.80/1.01      inference('sup-', [status(thm)], ['182', '185'])).
% 0.80/1.01  thf('187', plain,
% 0.80/1.01      ((m1_subset_1 @ (u1_struct_0 @ sk_B_1) @ 
% 0.80/1.01        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.80/1.01      inference('demod', [status(thm)], ['3', '4'])).
% 0.80/1.01  thf('188', plain,
% 0.80/1.01      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.80/1.01         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 0.80/1.01          | ((u1_struct_0 @ X29) != (X27))
% 0.80/1.01          | (v5_pre_topc @ 
% 0.80/1.01             (k2_tmap_1 @ X28 @ (k6_tmap_1 @ X28 @ X27) @ 
% 0.80/1.01              (k7_tmap_1 @ X28 @ X27) @ X29) @ 
% 0.80/1.01             X29 @ (k6_tmap_1 @ X28 @ X27))
% 0.80/1.01          | ~ (m1_pre_topc @ X29 @ X28)
% 0.80/1.01          | (v2_struct_0 @ X29)
% 0.80/1.01          | ~ (l1_pre_topc @ X28)
% 0.80/1.01          | ~ (v2_pre_topc @ X28)
% 0.80/1.01          | (v2_struct_0 @ X28))),
% 0.80/1.01      inference('cnf', [status(esa)], [t112_tmap_1])).
% 0.80/1.01  thf('189', plain,
% 0.80/1.01      (![X28 : $i, X29 : $i]:
% 0.80/1.01         ((v2_struct_0 @ X28)
% 0.80/1.01          | ~ (v2_pre_topc @ X28)
% 0.80/1.01          | ~ (l1_pre_topc @ X28)
% 0.80/1.01          | (v2_struct_0 @ X29)
% 0.80/1.01          | ~ (m1_pre_topc @ X29 @ X28)
% 0.80/1.01          | (v5_pre_topc @ 
% 0.80/1.01             (k2_tmap_1 @ X28 @ (k6_tmap_1 @ X28 @ (u1_struct_0 @ X29)) @ 
% 0.80/1.01              (k7_tmap_1 @ X28 @ (u1_struct_0 @ X29)) @ X29) @ 
% 0.80/1.01             X29 @ (k6_tmap_1 @ X28 @ (u1_struct_0 @ X29)))
% 0.80/1.01          | ~ (m1_subset_1 @ (u1_struct_0 @ X29) @ 
% 0.80/1.01               (k1_zfmisc_1 @ (u1_struct_0 @ X28))))),
% 0.80/1.01      inference('simplify', [status(thm)], ['188'])).
% 0.80/1.01  thf('190', plain,
% 0.80/1.01      (((v5_pre_topc @ 
% 0.80/1.01         (k2_tmap_1 @ sk_A @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B_1)) @ 
% 0.80/1.01          (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B_1)) @ sk_B_1) @ 
% 0.80/1.01         sk_B_1 @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B_1)))
% 0.80/1.01        | ~ (m1_pre_topc @ sk_B_1 @ sk_A)
% 0.80/1.01        | (v2_struct_0 @ sk_B_1)
% 0.80/1.01        | ~ (l1_pre_topc @ sk_A)
% 0.80/1.01        | ~ (v2_pre_topc @ sk_A)
% 0.80/1.01        | (v2_struct_0 @ sk_A))),
% 0.80/1.01      inference('sup-', [status(thm)], ['187', '189'])).
% 0.80/1.01  thf('191', plain,
% 0.80/1.01      (((k8_tmap_1 @ sk_A @ sk_B_1)
% 0.80/1.01         = (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B_1)))),
% 0.80/1.01      inference('clc', [status(thm)], ['40', '41'])).
% 0.80/1.01  thf('192', plain,
% 0.80/1.01      (((k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B_1))
% 0.80/1.01         = (k6_partfun1 @ (u1_struct_0 @ sk_A)))),
% 0.80/1.01      inference('clc', [status(thm)], ['48', '49'])).
% 0.80/1.01  thf('193', plain,
% 0.80/1.01      (((k8_tmap_1 @ sk_A @ sk_B_1)
% 0.80/1.01         = (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B_1)))),
% 0.80/1.01      inference('clc', [status(thm)], ['40', '41'])).
% 0.80/1.01  thf('194', plain, ((m1_pre_topc @ sk_B_1 @ sk_A)),
% 0.80/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.01  thf('195', plain, ((l1_pre_topc @ sk_A)),
% 0.80/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.01  thf('196', plain, ((v2_pre_topc @ sk_A)),
% 0.80/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.01  thf('197', plain,
% 0.80/1.01      (((v5_pre_topc @ 
% 0.80/1.01         (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B_1) @ 
% 0.80/1.01          (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ sk_B_1) @ 
% 0.80/1.01         sk_B_1 @ (k8_tmap_1 @ sk_A @ sk_B_1))
% 0.80/1.01        | (v2_struct_0 @ sk_B_1)
% 0.80/1.01        | (v2_struct_0 @ sk_A))),
% 0.80/1.01      inference('demod', [status(thm)],
% 0.80/1.01                ['190', '191', '192', '193', '194', '195', '196'])).
% 0.80/1.01  thf('198', plain, (~ (v2_struct_0 @ sk_B_1)),
% 0.80/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.01  thf('199', plain,
% 0.80/1.01      (((v2_struct_0 @ sk_A)
% 0.80/1.01        | (v5_pre_topc @ 
% 0.80/1.01           (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B_1) @ 
% 0.80/1.01            (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ sk_B_1) @ 
% 0.80/1.01           sk_B_1 @ (k8_tmap_1 @ sk_A @ sk_B_1)))),
% 0.80/1.01      inference('clc', [status(thm)], ['197', '198'])).
% 0.80/1.01  thf('200', plain, (~ (v2_struct_0 @ sk_A)),
% 0.80/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.01  thf('201', plain,
% 0.80/1.01      ((v5_pre_topc @ 
% 0.80/1.01        (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B_1) @ 
% 0.80/1.01         (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ sk_B_1) @ 
% 0.80/1.01        sk_B_1 @ (k8_tmap_1 @ sk_A @ sk_B_1))),
% 0.80/1.01      inference('clc', [status(thm)], ['199', '200'])).
% 0.80/1.01  thf('202', plain,
% 0.80/1.01      (((k9_tmap_1 @ sk_A @ sk_B_1) = (k6_partfun1 @ (u1_struct_0 @ sk_A)))),
% 0.80/1.01      inference('clc', [status(thm)], ['146', '147'])).
% 0.80/1.01  thf('203', plain,
% 0.80/1.01      ((~ (v5_pre_topc @ 
% 0.80/1.01           (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B_1) @ 
% 0.80/1.01            (k9_tmap_1 @ sk_A @ sk_B_1) @ sk_B_1) @ 
% 0.80/1.01           sk_B_1 @ (k8_tmap_1 @ sk_A @ sk_B_1)))
% 0.80/1.01         <= (~
% 0.80/1.01             ((v5_pre_topc @ 
% 0.80/1.01               (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B_1) @ 
% 0.80/1.01                (k9_tmap_1 @ sk_A @ sk_B_1) @ sk_B_1) @ 
% 0.80/1.01               sk_B_1 @ (k8_tmap_1 @ sk_A @ sk_B_1))))),
% 0.80/1.01      inference('split', [status(esa)], ['56'])).
% 0.80/1.01  thf('204', plain,
% 0.80/1.01      ((~ (v5_pre_topc @ 
% 0.80/1.01           (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B_1) @ 
% 0.80/1.01            (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ sk_B_1) @ 
% 0.80/1.01           sk_B_1 @ (k8_tmap_1 @ sk_A @ sk_B_1)))
% 0.80/1.01         <= (~
% 0.80/1.01             ((v5_pre_topc @ 
% 0.80/1.01               (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B_1) @ 
% 0.80/1.01                (k9_tmap_1 @ sk_A @ sk_B_1) @ sk_B_1) @ 
% 0.80/1.01               sk_B_1 @ (k8_tmap_1 @ sk_A @ sk_B_1))))),
% 0.80/1.01      inference('sup-', [status(thm)], ['202', '203'])).
% 0.80/1.01  thf('205', plain,
% 0.80/1.01      (((v5_pre_topc @ 
% 0.80/1.01         (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B_1) @ 
% 0.80/1.01          (k9_tmap_1 @ sk_A @ sk_B_1) @ sk_B_1) @ 
% 0.80/1.01         sk_B_1 @ (k8_tmap_1 @ sk_A @ sk_B_1)))),
% 0.80/1.01      inference('sup-', [status(thm)], ['201', '204'])).
% 0.80/1.01  thf('206', plain,
% 0.80/1.01      (~
% 0.80/1.01       ((m1_subset_1 @ 
% 0.80/1.01         (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B_1) @ 
% 0.80/1.01          (k9_tmap_1 @ sk_A @ sk_B_1) @ sk_B_1) @ 
% 0.80/1.01         (k1_zfmisc_1 @ 
% 0.80/1.01          (k2_zfmisc_1 @ (u1_struct_0 @ sk_B_1) @ 
% 0.80/1.01           (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B_1)))))) | 
% 0.80/1.01       ~
% 0.80/1.01       ((v5_pre_topc @ 
% 0.80/1.01         (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B_1) @ 
% 0.80/1.01          (k9_tmap_1 @ sk_A @ sk_B_1) @ sk_B_1) @ 
% 0.80/1.01         sk_B_1 @ (k8_tmap_1 @ sk_A @ sk_B_1))) | 
% 0.80/1.01       ~
% 0.80/1.01       ((v1_funct_1 @ 
% 0.80/1.01         (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B_1) @ 
% 0.80/1.01          (k9_tmap_1 @ sk_A @ sk_B_1) @ sk_B_1))) | 
% 0.80/1.01       ~
% 0.80/1.01       ((v1_funct_2 @ 
% 0.80/1.01         (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B_1) @ 
% 0.80/1.01          (k9_tmap_1 @ sk_A @ sk_B_1) @ sk_B_1) @ 
% 0.80/1.01         (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B_1))))),
% 0.80/1.01      inference('split', [status(esa)], ['56'])).
% 0.80/1.01  thf('207', plain,
% 0.80/1.01      (~
% 0.80/1.01       ((m1_subset_1 @ 
% 0.80/1.01         (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B_1) @ 
% 0.80/1.01          (k9_tmap_1 @ sk_A @ sk_B_1) @ sk_B_1) @ 
% 0.80/1.01         (k1_zfmisc_1 @ 
% 0.80/1.01          (k2_zfmisc_1 @ (u1_struct_0 @ sk_B_1) @ 
% 0.80/1.01           (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B_1))))))),
% 0.80/1.01      inference('sat_resolution*', [status(thm)], ['168', '186', '205', '206'])).
% 0.80/1.01  thf('208', plain,
% 0.80/1.01      (~ (m1_subset_1 @ 
% 0.80/1.01          (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B_1) @ 
% 0.80/1.01           (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ sk_B_1) @ 
% 0.80/1.01          (k1_zfmisc_1 @ 
% 0.80/1.01           (k2_zfmisc_1 @ (u1_struct_0 @ sk_B_1) @ 
% 0.80/1.01            (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B_1)))))),
% 0.80/1.01      inference('simpl_trail', [status(thm)], ['149', '207'])).
% 0.80/1.01  thf('209', plain, (((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_B_1))),
% 0.80/1.01      inference('clc', [status(thm)], ['55', '208'])).
% 0.80/1.01  thf('210', plain, (~ (v2_struct_0 @ sk_A)),
% 0.80/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.01  thf('211', plain, ((v2_struct_0 @ sk_B_1)),
% 0.80/1.01      inference('clc', [status(thm)], ['209', '210'])).
% 0.80/1.01  thf('212', plain, ($false), inference('demod', [status(thm)], ['0', '211'])).
% 0.80/1.01  
% 0.80/1.01  % SZS output end Refutation
% 0.80/1.01  
% 0.80/1.02  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
