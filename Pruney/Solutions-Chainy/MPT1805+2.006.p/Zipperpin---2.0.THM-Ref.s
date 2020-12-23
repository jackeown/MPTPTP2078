%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.du5CyC0BLC

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:11:02 EST 2020

% Result     : Theorem 0.38s
% Output     : Refutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :  269 (3509 expanded)
%              Number of leaves         :   36 (1022 expanded)
%              Depth                    :   24
%              Number of atoms          : 3168 (128352 expanded)
%              Number of equality atoms :   57 ( 594 expanded)
%              Maximal formula depth    :   23 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(r1_funct_2_type,type,(
    r1_funct_2: $i > $i > $i > $i > $i > $i > $o )).

thf(v5_pre_topc_type,type,(
    v5_pre_topc: $i > $i > $i > $o )).

thf(k6_tmap_1_type,type,(
    k6_tmap_1: $i > $i > $i )).

thf(k5_tmap_1_type,type,(
    k5_tmap_1: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(k2_tmap_1_type,type,(
    k2_tmap_1: $i > $i > $i > $i > $i )).

thf(k7_tmap_1_type,type,(
    k7_tmap_1: $i > $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k9_tmap_1_type,type,(
    k9_tmap_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(k8_tmap_1_type,type,(
    k8_tmap_1: $i > $i > $i )).

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
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
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

thf('2',plain,(
    ! [X25: $i,X26: $i] :
      ( ( v2_struct_0 @ X25 )
      | ~ ( m1_pre_topc @ X25 @ X26 )
      | ( ( u1_struct_0 @ ( k8_tmap_1 @ X26 @ X25 ) )
        = ( u1_struct_0 @ X26 ) )
      | ~ ( l1_pre_topc @ X26 )
      | ~ ( v2_pre_topc @ X26 )
      | ( v2_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t114_tmap_1])).

thf('3',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
      = ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
      = ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['3','4','5'])).

thf('7',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['6','7'])).

thf('9',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['8','9'])).

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

thf('11',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_pre_topc @ X12 @ X13 )
      | ( X14
       != ( k9_tmap_1 @ X13 @ X12 ) )
      | ( X15
       != ( u1_struct_0 @ X12 ) )
      | ( r1_funct_2 @ ( u1_struct_0 @ X13 ) @ ( u1_struct_0 @ ( k8_tmap_1 @ X13 @ X12 ) ) @ ( u1_struct_0 @ X13 ) @ ( u1_struct_0 @ ( k6_tmap_1 @ X13 @ X15 ) ) @ X14 @ ( k7_tmap_1 @ X13 @ X15 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X13 ) @ ( u1_struct_0 @ ( k8_tmap_1 @ X13 @ X12 ) ) ) ) )
      | ~ ( v1_funct_2 @ X14 @ ( u1_struct_0 @ X13 ) @ ( u1_struct_0 @ ( k8_tmap_1 @ X13 @ X12 ) ) )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( l1_pre_topc @ X13 )
      | ~ ( v2_pre_topc @ X13 )
      | ( v2_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d12_tmap_1])).

thf('12',plain,(
    ! [X12: $i,X13: $i] :
      ( ( v2_struct_0 @ X13 )
      | ~ ( v2_pre_topc @ X13 )
      | ~ ( l1_pre_topc @ X13 )
      | ~ ( v1_funct_1 @ ( k9_tmap_1 @ X13 @ X12 ) )
      | ~ ( v1_funct_2 @ ( k9_tmap_1 @ X13 @ X12 ) @ ( u1_struct_0 @ X13 ) @ ( u1_struct_0 @ ( k8_tmap_1 @ X13 @ X12 ) ) )
      | ~ ( m1_subset_1 @ ( k9_tmap_1 @ X13 @ X12 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X13 ) @ ( u1_struct_0 @ ( k8_tmap_1 @ X13 @ X12 ) ) ) ) )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X12 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ( r1_funct_2 @ ( u1_struct_0 @ X13 ) @ ( u1_struct_0 @ ( k8_tmap_1 @ X13 @ X12 ) ) @ ( u1_struct_0 @ X13 ) @ ( u1_struct_0 @ ( k6_tmap_1 @ X13 @ ( u1_struct_0 @ X12 ) ) ) @ ( k9_tmap_1 @ X13 @ X12 ) @ ( k7_tmap_1 @ X13 @ ( u1_struct_0 @ X12 ) ) )
      | ~ ( m1_pre_topc @ X12 @ X13 ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,
    ( ~ ( m1_subset_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ~ ( m1_pre_topc @ sk_B @ sk_A )
    | ( r1_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
    | ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( v1_funct_2 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) )
    | ~ ( v1_funct_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['10','12'])).

thf('14',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
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

thf('15',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( l1_pre_topc @ X20 )
      | ~ ( v2_pre_topc @ X20 )
      | ( v2_struct_0 @ X20 )
      | ~ ( m1_pre_topc @ X21 @ X20 )
      | ( m1_subset_1 @ ( k9_tmap_1 @ X20 @ X21 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X20 ) @ ( u1_struct_0 @ ( k8_tmap_1 @ X20 @ X21 ) ) ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k9_tmap_1])).

thf('16',plain,
    ( ( m1_subset_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,
    ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['8','9'])).

thf('18',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ( m1_subset_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['16','17','18','19'])).

thf('21',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    m1_subset_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['20','21'])).

thf('23',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['8','9'])).

thf('25',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t1_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( m1_subset_1 @ ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('26',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( m1_pre_topc @ X28 @ X29 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X28 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) )
      | ~ ( l1_pre_topc @ X29 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('27',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['27','28'])).

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

thf('30',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ~ ( m1_pre_topc @ X8 @ X9 )
      | ( X10
       != ( k8_tmap_1 @ X9 @ X8 ) )
      | ( X11
       != ( u1_struct_0 @ X8 ) )
      | ( X10
        = ( k6_tmap_1 @ X9 @ X11 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ~ ( l1_pre_topc @ X10 )
      | ~ ( v2_pre_topc @ X10 )
      | ~ ( v1_pre_topc @ X10 )
      | ~ ( l1_pre_topc @ X9 )
      | ~ ( v2_pre_topc @ X9 )
      | ( v2_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d11_tmap_1])).

thf('31',plain,(
    ! [X8: $i,X9: $i] :
      ( ( v2_struct_0 @ X9 )
      | ~ ( v2_pre_topc @ X9 )
      | ~ ( l1_pre_topc @ X9 )
      | ~ ( v1_pre_topc @ ( k8_tmap_1 @ X9 @ X8 ) )
      | ~ ( v2_pre_topc @ ( k8_tmap_1 @ X9 @ X8 ) )
      | ~ ( l1_pre_topc @ ( k8_tmap_1 @ X9 @ X8 ) )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X8 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ( ( k8_tmap_1 @ X9 @ X8 )
        = ( k6_tmap_1 @ X9 @ ( u1_struct_0 @ X8 ) ) )
      | ~ ( m1_pre_topc @ X8 @ X9 ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,
    ( ~ ( m1_pre_topc @ sk_B @ sk_A )
    | ( ( k8_tmap_1 @ sk_A @ sk_B )
      = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
    | ~ ( l1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( v2_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( v1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['29','31'])).

thf('33',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
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

thf('35',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( l1_pre_topc @ X18 )
      | ~ ( v2_pre_topc @ X18 )
      | ( v2_struct_0 @ X18 )
      | ~ ( m1_pre_topc @ X19 @ X18 )
      | ( l1_pre_topc @ ( k8_tmap_1 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k8_tmap_1])).

thf('36',plain,
    ( ( l1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
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
    ( ( l1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['36','37','38'])).

thf('40',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    l1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['39','40'])).

thf('42',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( l1_pre_topc @ X18 )
      | ~ ( v2_pre_topc @ X18 )
      | ( v2_struct_0 @ X18 )
      | ~ ( m1_pre_topc @ X19 @ X18 )
      | ( v2_pre_topc @ ( k8_tmap_1 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k8_tmap_1])).

thf('44',plain,
    ( ( v2_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
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
    ( ( v2_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['44','45','46'])).

thf('48',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    v2_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['47','48'])).

thf('50',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( l1_pre_topc @ X18 )
      | ~ ( v2_pre_topc @ X18 )
      | ( v2_struct_0 @ X18 )
      | ~ ( m1_pre_topc @ X19 @ X18 )
      | ( v1_pre_topc @ ( k8_tmap_1 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k8_tmap_1])).

thf('52',plain,
    ( ( v1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( ( v1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['52','53','54'])).

thf('56',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    v1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['55','56'])).

thf('58',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,
    ( ( ( k8_tmap_1 @ sk_A @ sk_B )
      = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['32','33','41','49','57','58','59'])).

thf('61',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,
    ( ( k8_tmap_1 @ sk_A @ sk_B )
    = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['60','61'])).

thf('63',plain,
    ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['8','9'])).

thf('64',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('65',plain,
    ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['8','9'])).

thf('66',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( l1_pre_topc @ X20 )
      | ~ ( v2_pre_topc @ X20 )
      | ( v2_struct_0 @ X20 )
      | ~ ( m1_pre_topc @ X21 @ X20 )
      | ( v1_funct_2 @ ( k9_tmap_1 @ X20 @ X21 ) @ ( u1_struct_0 @ X20 ) @ ( u1_struct_0 @ ( k8_tmap_1 @ X20 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k9_tmap_1])).

thf('68',plain,
    ( ( v1_funct_2 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,
    ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['8','9'])).

thf('70',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,
    ( ( v1_funct_2 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['68','69','70','71'])).

thf('73',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    v1_funct_2 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['72','73'])).

thf('75',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( l1_pre_topc @ X20 )
      | ~ ( v2_pre_topc @ X20 )
      | ( v2_struct_0 @ X20 )
      | ~ ( m1_pre_topc @ X21 @ X20 )
      | ( v1_funct_1 @ ( k9_tmap_1 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k9_tmap_1])).

thf('77',plain,
    ( ( v1_funct_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,
    ( ( v1_funct_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['77','78','79'])).

thf('81',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    v1_funct_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['80','81'])).

thf('83',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,
    ( ( r1_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['13','22','23','24','62','63','64','65','74','82','83','84'])).

thf('86',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    r1_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['85','86'])).

thf('88',plain,(
    m1_subset_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['20','21'])).

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

thf('89',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) ) )
      | ~ ( v1_funct_2 @ X2 @ X3 @ X4 )
      | ~ ( v1_funct_1 @ X2 )
      | ( v1_xboole_0 @ X5 )
      | ( v1_xboole_0 @ X4 )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_funct_2 @ X6 @ X7 @ X5 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X5 ) ) )
      | ( X2 = X6 )
      | ~ ( r1_funct_2 @ X3 @ X4 @ X7 @ X5 @ X2 @ X6 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_funct_2])).

thf('90',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ X2 @ X1 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ X0 )
      | ( ( k9_tmap_1 @ sk_A @ sk_B )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_2 @ X0 @ X2 @ X1 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ X1 )
      | ~ ( v1_funct_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) )
      | ~ ( v1_funct_2 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,(
    v1_funct_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['80','81'])).

thf('92',plain,(
    v1_funct_2 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['72','73'])).

thf('93',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ X2 @ X1 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ X0 )
      | ( ( k9_tmap_1 @ sk_A @ sk_B )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_2 @ X0 @ X2 @ X1 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ X1 ) ) ),
    inference(demod,[status(thm)],['90','91','92'])).

thf('94',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_funct_1 @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
    | ~ ( v1_funct_2 @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( m1_subset_1 @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ( ( k9_tmap_1 @ sk_A @ sk_B )
      = ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['87','93'])).

thf('95',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf(dt_k7_tmap_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( ( v1_funct_1 @ ( k7_tmap_1 @ A @ B ) )
        & ( v1_funct_2 @ ( k7_tmap_1 @ A @ B ) @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ A @ B ) ) )
        & ( m1_subset_1 @ ( k7_tmap_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ A @ B ) ) ) ) ) ) ) )).

thf('96',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( l1_pre_topc @ X16 )
      | ~ ( v2_pre_topc @ X16 )
      | ( v2_struct_0 @ X16 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ( v1_funct_1 @ ( k7_tmap_1 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_tmap_1])).

thf('97',plain,
    ( ( v1_funct_1 @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,
    ( ( v1_funct_1 @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['97','98','99'])).

thf('101',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    v1_funct_1 @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['100','101'])).

thf('103',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('104',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( l1_pre_topc @ X16 )
      | ~ ( v2_pre_topc @ X16 )
      | ( v2_struct_0 @ X16 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ( v1_funct_2 @ ( k7_tmap_1 @ X16 @ X17 ) @ ( u1_struct_0 @ X16 ) @ ( u1_struct_0 @ ( k6_tmap_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_tmap_1])).

thf('105',plain,
    ( ( v1_funct_2 @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,
    ( ( v1_funct_2 @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['105','106','107'])).

thf('109',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,(
    v1_funct_2 @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['108','109'])).

thf('111',plain,
    ( ( k8_tmap_1 @ sk_A @ sk_B )
    = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['60','61'])).

thf('112',plain,
    ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['8','9'])).

thf('113',plain,(
    v1_funct_2 @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['110','111','112'])).

thf('114',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('115',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( l1_pre_topc @ X16 )
      | ~ ( v2_pre_topc @ X16 )
      | ( v2_struct_0 @ X16 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ( m1_subset_1 @ ( k7_tmap_1 @ X16 @ X17 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X16 ) @ ( u1_struct_0 @ ( k6_tmap_1 @ X16 @ X17 ) ) ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_tmap_1])).

thf('116',plain,
    ( ( m1_subset_1 @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ) ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['114','115'])).

thf('117',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,
    ( ( m1_subset_1 @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ) ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['116','117','118'])).

thf('120',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('121',plain,(
    m1_subset_1 @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ) ) ) ),
    inference(clc,[status(thm)],['119','120'])).

thf('122',plain,
    ( ( k8_tmap_1 @ sk_A @ sk_B )
    = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['60','61'])).

thf('123',plain,
    ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['8','9'])).

thf('124',plain,(
    m1_subset_1 @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['121','122','123'])).

thf('125',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( ( k9_tmap_1 @ sk_A @ sk_B )
      = ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['94','102','113','124'])).

thf('126',plain,
    ( ( ( k9_tmap_1 @ sk_A @ sk_B )
      = ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['125'])).

thf('127',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['27','28'])).

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

thf('128',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ( ( u1_struct_0 @ X24 )
       != X22 )
      | ( m1_subset_1 @ ( k2_tmap_1 @ X23 @ ( k6_tmap_1 @ X23 @ X22 ) @ ( k7_tmap_1 @ X23 @ X22 ) @ X24 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X24 ) @ ( u1_struct_0 @ ( k6_tmap_1 @ X23 @ X22 ) ) ) ) )
      | ~ ( m1_pre_topc @ X24 @ X23 )
      | ( v2_struct_0 @ X24 )
      | ~ ( l1_pre_topc @ X23 )
      | ~ ( v2_pre_topc @ X23 )
      | ( v2_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t112_tmap_1])).

thf('129',plain,(
    ! [X23: $i,X24: $i] :
      ( ( v2_struct_0 @ X23 )
      | ~ ( v2_pre_topc @ X23 )
      | ~ ( l1_pre_topc @ X23 )
      | ( v2_struct_0 @ X24 )
      | ~ ( m1_pre_topc @ X24 @ X23 )
      | ( m1_subset_1 @ ( k2_tmap_1 @ X23 @ ( k6_tmap_1 @ X23 @ ( u1_struct_0 @ X24 ) ) @ ( k7_tmap_1 @ X23 @ ( u1_struct_0 @ X24 ) ) @ X24 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X24 ) @ ( u1_struct_0 @ ( k6_tmap_1 @ X23 @ ( u1_struct_0 @ X24 ) ) ) ) ) )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X24 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) ) ) ),
    inference(simplify,[status(thm)],['128'])).

thf('130',plain,
    ( ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ) ) ) )
    | ~ ( m1_pre_topc @ sk_B @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['127','129'])).

thf('131',plain,
    ( ( k8_tmap_1 @ sk_A @ sk_B )
    = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['60','61'])).

thf('132',plain,
    ( ( k8_tmap_1 @ sk_A @ sk_B )
    = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['60','61'])).

thf('133',plain,
    ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['8','9'])).

thf('134',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('135',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('136',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('137',plain,
    ( ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['130','131','132','133','134','135','136'])).

thf('138',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('139',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(clc,[status(thm)],['137','138'])).

thf('140',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('141',plain,(
    m1_subset_1 @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['139','140'])).

thf('142',plain,
    ( ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['126','141'])).

thf('143',plain,
    ( ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_B ) )
    | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) )
    | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_B ) @ sk_B @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('144',plain,
    ( ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ) )
   <= ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ) ) ),
    inference(split,[status(esa)],['143'])).

thf('145',plain,
    ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['8','9'])).

thf('146',plain,
    ( ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ) ) ),
    inference(demod,[status(thm)],['144','145'])).

thf('147',plain,
    ( ( ( k9_tmap_1 @ sk_A @ sk_B )
      = ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['125'])).

thf('148',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('149',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ( ( u1_struct_0 @ X24 )
       != X22 )
      | ( v1_funct_2 @ ( k2_tmap_1 @ X23 @ ( k6_tmap_1 @ X23 @ X22 ) @ ( k7_tmap_1 @ X23 @ X22 ) @ X24 ) @ ( u1_struct_0 @ X24 ) @ ( u1_struct_0 @ ( k6_tmap_1 @ X23 @ X22 ) ) )
      | ~ ( m1_pre_topc @ X24 @ X23 )
      | ( v2_struct_0 @ X24 )
      | ~ ( l1_pre_topc @ X23 )
      | ~ ( v2_pre_topc @ X23 )
      | ( v2_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t112_tmap_1])).

thf('150',plain,(
    ! [X23: $i,X24: $i] :
      ( ( v2_struct_0 @ X23 )
      | ~ ( v2_pre_topc @ X23 )
      | ~ ( l1_pre_topc @ X23 )
      | ( v2_struct_0 @ X24 )
      | ~ ( m1_pre_topc @ X24 @ X23 )
      | ( v1_funct_2 @ ( k2_tmap_1 @ X23 @ ( k6_tmap_1 @ X23 @ ( u1_struct_0 @ X24 ) ) @ ( k7_tmap_1 @ X23 @ ( u1_struct_0 @ X24 ) ) @ X24 ) @ ( u1_struct_0 @ X24 ) @ ( u1_struct_0 @ ( k6_tmap_1 @ X23 @ ( u1_struct_0 @ X24 ) ) ) )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X24 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) ) ) ),
    inference(simplify,[status(thm)],['149'])).

thf('151',plain,
    ( ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( m1_pre_topc @ sk_B @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['148','150'])).

thf('152',plain,
    ( ( k8_tmap_1 @ sk_A @ sk_B )
    = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['60','61'])).

thf('153',plain,
    ( ( k8_tmap_1 @ sk_A @ sk_B )
    = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['60','61'])).

thf('154',plain,
    ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['8','9'])).

thf('155',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('156',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('157',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('158',plain,
    ( ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['151','152','153','154','155','156','157'])).

thf('159',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('160',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['158','159'])).

thf('161',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('162',plain,(
    v1_funct_2 @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['160','161'])).

thf('163',plain,
    ( ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['147','162'])).

thf('164',plain,
    ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['8','9'])).

thf('165',plain,
    ( ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) )
   <= ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['143'])).

thf('166',plain,
    ( ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['164','165'])).

thf('167',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['163','166'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('168',plain,(
    ! [X1: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X1 ) )
      | ~ ( l1_struct_0 @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('169',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['167','168'])).

thf('170',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('171',plain,(
    ! [X0: $i] :
      ( ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('172',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['170','171'])).

thf('173',plain,
    ( ( v2_struct_0 @ sk_A )
   <= ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['169','172'])).

thf('174',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('175',plain,(
    v1_funct_2 @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['173','174'])).

thf('176',plain,
    ( ( ( k9_tmap_1 @ sk_A @ sk_B )
      = ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['125'])).

thf('177',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('178',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ( ( u1_struct_0 @ X24 )
       != X22 )
      | ( v1_funct_1 @ ( k2_tmap_1 @ X23 @ ( k6_tmap_1 @ X23 @ X22 ) @ ( k7_tmap_1 @ X23 @ X22 ) @ X24 ) )
      | ~ ( m1_pre_topc @ X24 @ X23 )
      | ( v2_struct_0 @ X24 )
      | ~ ( l1_pre_topc @ X23 )
      | ~ ( v2_pre_topc @ X23 )
      | ( v2_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t112_tmap_1])).

thf('179',plain,(
    ! [X23: $i,X24: $i] :
      ( ( v2_struct_0 @ X23 )
      | ~ ( v2_pre_topc @ X23 )
      | ~ ( l1_pre_topc @ X23 )
      | ( v2_struct_0 @ X24 )
      | ~ ( m1_pre_topc @ X24 @ X23 )
      | ( v1_funct_1 @ ( k2_tmap_1 @ X23 @ ( k6_tmap_1 @ X23 @ ( u1_struct_0 @ X24 ) ) @ ( k7_tmap_1 @ X23 @ ( u1_struct_0 @ X24 ) ) @ X24 ) )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X24 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) ) ) ),
    inference(simplify,[status(thm)],['178'])).

thf('180',plain,
    ( ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) @ sk_B ) )
    | ~ ( m1_pre_topc @ sk_B @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['177','179'])).

thf('181',plain,
    ( ( k8_tmap_1 @ sk_A @ sk_B )
    = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['60','61'])).

thf('182',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('183',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('184',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('185',plain,
    ( ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['180','181','182','183','184'])).

thf('186',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('187',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) @ sk_B ) ) ),
    inference(clc,[status(thm)],['185','186'])).

thf('188',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('189',plain,(
    v1_funct_1 @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) @ sk_B ) ),
    inference(clc,[status(thm)],['187','188'])).

thf('190',plain,
    ( ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['176','189'])).

thf('191',plain,
    ( ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_B ) )
   <= ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference(split,[status(esa)],['143'])).

thf('192',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['190','191'])).

thf('193',plain,(
    ! [X1: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X1 ) )
      | ~ ( l1_struct_0 @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('194',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['192','193'])).

thf('195',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['170','171'])).

thf('196',plain,
    ( ( v2_struct_0 @ sk_A )
   <= ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['194','195'])).

thf('197',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('198',plain,(
    v1_funct_1 @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['196','197'])).

thf('199',plain,
    ( ( ( k9_tmap_1 @ sk_A @ sk_B )
      = ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['125'])).

thf('200',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('201',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ( ( u1_struct_0 @ X24 )
       != X22 )
      | ( v5_pre_topc @ ( k2_tmap_1 @ X23 @ ( k6_tmap_1 @ X23 @ X22 ) @ ( k7_tmap_1 @ X23 @ X22 ) @ X24 ) @ X24 @ ( k6_tmap_1 @ X23 @ X22 ) )
      | ~ ( m1_pre_topc @ X24 @ X23 )
      | ( v2_struct_0 @ X24 )
      | ~ ( l1_pre_topc @ X23 )
      | ~ ( v2_pre_topc @ X23 )
      | ( v2_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t112_tmap_1])).

thf('202',plain,(
    ! [X23: $i,X24: $i] :
      ( ( v2_struct_0 @ X23 )
      | ~ ( v2_pre_topc @ X23 )
      | ~ ( l1_pre_topc @ X23 )
      | ( v2_struct_0 @ X24 )
      | ~ ( m1_pre_topc @ X24 @ X23 )
      | ( v5_pre_topc @ ( k2_tmap_1 @ X23 @ ( k6_tmap_1 @ X23 @ ( u1_struct_0 @ X24 ) ) @ ( k7_tmap_1 @ X23 @ ( u1_struct_0 @ X24 ) ) @ X24 ) @ X24 @ ( k6_tmap_1 @ X23 @ ( u1_struct_0 @ X24 ) ) )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X24 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) ) ) ),
    inference(simplify,[status(thm)],['201'])).

thf('203',plain,
    ( ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) @ sk_B ) @ sk_B @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
    | ~ ( m1_pre_topc @ sk_B @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['200','202'])).

thf('204',plain,
    ( ( k8_tmap_1 @ sk_A @ sk_B )
    = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['60','61'])).

thf('205',plain,
    ( ( k8_tmap_1 @ sk_A @ sk_B )
    = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['60','61'])).

thf('206',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('207',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('208',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('209',plain,
    ( ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) @ sk_B ) @ sk_B @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['203','204','205','206','207','208'])).

thf('210',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('211',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) @ sk_B ) @ sk_B @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['209','210'])).

thf('212',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('213',plain,(
    v5_pre_topc @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) @ sk_B ) @ sk_B @ ( k8_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['211','212'])).

thf('214',plain,
    ( ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_B ) @ sk_B @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['199','213'])).

thf('215',plain,
    ( ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_B ) @ sk_B @ ( k8_tmap_1 @ sk_A @ sk_B ) )
   <= ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_B ) @ sk_B @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['143'])).

thf('216',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
   <= ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_B ) @ sk_B @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['214','215'])).

thf('217',plain,(
    ! [X1: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X1 ) )
      | ~ ( l1_struct_0 @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('218',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_B ) @ sk_B @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['216','217'])).

thf('219',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['170','171'])).

thf('220',plain,
    ( ( v2_struct_0 @ sk_A )
   <= ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_B ) @ sk_B @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['218','219'])).

thf('221',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('222',plain,(
    v5_pre_topc @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_B ) @ sk_B @ ( k8_tmap_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['220','221'])).

thf('223',plain,
    ( ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ) )
    | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_B ) @ sk_B @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_B ) )
    | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['143'])).

thf('224',plain,(
    ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ) ) ),
    inference('sat_resolution*',[status(thm)],['175','198','222','223'])).

thf('225',plain,(
    ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(simpl_trail,[status(thm)],['146','224'])).

thf('226',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['142','225'])).

thf('227',plain,(
    ! [X1: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X1 ) )
      | ~ ( l1_struct_0 @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('228',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['226','227'])).

thf('229',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['170','171'])).

thf('230',plain,(
    v2_struct_0 @ sk_A ),
    inference(demod,[status(thm)],['228','229'])).

thf('231',plain,(
    $false ),
    inference(demod,[status(thm)],['0','230'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.du5CyC0BLC
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:30:57 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.38/0.61  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.38/0.61  % Solved by: fo/fo7.sh
% 0.38/0.61  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.38/0.61  % done 224 iterations in 0.161s
% 0.38/0.61  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.38/0.61  % SZS output start Refutation
% 0.38/0.61  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.38/0.61  thf(r1_funct_2_type, type, r1_funct_2: $i > $i > $i > $i > $i > $i > $o).
% 0.38/0.61  thf(v5_pre_topc_type, type, v5_pre_topc: $i > $i > $i > $o).
% 0.38/0.61  thf(k6_tmap_1_type, type, k6_tmap_1: $i > $i > $i).
% 0.38/0.61  thf(k5_tmap_1_type, type, k5_tmap_1: $i > $i > $i).
% 0.38/0.61  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.38/0.61  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.38/0.61  thf(sk_B_type, type, sk_B: $i).
% 0.38/0.61  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.38/0.61  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 0.38/0.61  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.38/0.61  thf(sk_A_type, type, sk_A: $i).
% 0.38/0.61  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.38/0.61  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.38/0.61  thf(k2_tmap_1_type, type, k2_tmap_1: $i > $i > $i > $i > $i).
% 0.38/0.61  thf(k7_tmap_1_type, type, k7_tmap_1: $i > $i > $i).
% 0.38/0.61  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.38/0.61  thf(k9_tmap_1_type, type, k9_tmap_1: $i > $i > $i).
% 0.38/0.61  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.38/0.61  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.38/0.61  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.38/0.61  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 0.38/0.61  thf(k8_tmap_1_type, type, k8_tmap_1: $i > $i > $i).
% 0.38/0.61  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.38/0.61  thf(t121_tmap_1, conjecture,
% 0.38/0.61    (![A:$i]:
% 0.38/0.61     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.38/0.61       ( ![B:$i]:
% 0.38/0.61         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.38/0.61           ( ( v1_funct_1 @
% 0.38/0.61               ( k2_tmap_1 @
% 0.38/0.61                 A @ ( k8_tmap_1 @ A @ B ) @ ( k9_tmap_1 @ A @ B ) @ B ) ) & 
% 0.38/0.61             ( v1_funct_2 @
% 0.38/0.61               ( k2_tmap_1 @
% 0.38/0.61                 A @ ( k8_tmap_1 @ A @ B ) @ ( k9_tmap_1 @ A @ B ) @ B ) @ 
% 0.38/0.61               ( u1_struct_0 @ B ) @ ( u1_struct_0 @ ( k8_tmap_1 @ A @ B ) ) ) & 
% 0.38/0.61             ( v5_pre_topc @
% 0.38/0.61               ( k2_tmap_1 @
% 0.38/0.61                 A @ ( k8_tmap_1 @ A @ B ) @ ( k9_tmap_1 @ A @ B ) @ B ) @ 
% 0.38/0.61               B @ ( k8_tmap_1 @ A @ B ) ) & 
% 0.38/0.61             ( m1_subset_1 @
% 0.38/0.61               ( k2_tmap_1 @
% 0.38/0.61                 A @ ( k8_tmap_1 @ A @ B ) @ ( k9_tmap_1 @ A @ B ) @ B ) @ 
% 0.38/0.61               ( k1_zfmisc_1 @
% 0.38/0.61                 ( k2_zfmisc_1 @
% 0.38/0.61                   ( u1_struct_0 @ B ) @ 
% 0.38/0.61                   ( u1_struct_0 @ ( k8_tmap_1 @ A @ B ) ) ) ) ) ) ) ) ))).
% 0.38/0.61  thf(zf_stmt_0, negated_conjecture,
% 0.38/0.61    (~( ![A:$i]:
% 0.38/0.61        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.38/0.61            ( l1_pre_topc @ A ) ) =>
% 0.38/0.61          ( ![B:$i]:
% 0.38/0.61            ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.38/0.61              ( ( v1_funct_1 @
% 0.38/0.61                  ( k2_tmap_1 @
% 0.38/0.61                    A @ ( k8_tmap_1 @ A @ B ) @ ( k9_tmap_1 @ A @ B ) @ B ) ) & 
% 0.38/0.61                ( v1_funct_2 @
% 0.38/0.61                  ( k2_tmap_1 @
% 0.38/0.61                    A @ ( k8_tmap_1 @ A @ B ) @ ( k9_tmap_1 @ A @ B ) @ B ) @ 
% 0.38/0.62                  ( u1_struct_0 @ B ) @ ( u1_struct_0 @ ( k8_tmap_1 @ A @ B ) ) ) & 
% 0.38/0.62                ( v5_pre_topc @
% 0.38/0.62                  ( k2_tmap_1 @
% 0.38/0.62                    A @ ( k8_tmap_1 @ A @ B ) @ ( k9_tmap_1 @ A @ B ) @ B ) @ 
% 0.38/0.62                  B @ ( k8_tmap_1 @ A @ B ) ) & 
% 0.38/0.62                ( m1_subset_1 @
% 0.38/0.62                  ( k2_tmap_1 @
% 0.38/0.62                    A @ ( k8_tmap_1 @ A @ B ) @ ( k9_tmap_1 @ A @ B ) @ B ) @ 
% 0.38/0.62                  ( k1_zfmisc_1 @
% 0.38/0.62                    ( k2_zfmisc_1 @
% 0.38/0.62                      ( u1_struct_0 @ B ) @ 
% 0.38/0.62                      ( u1_struct_0 @ ( k8_tmap_1 @ A @ B ) ) ) ) ) ) ) ) ) )),
% 0.38/0.62    inference('cnf.neg', [status(esa)], [t121_tmap_1])).
% 0.38/0.62  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.38/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.62  thf('1', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.38/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.62  thf(t114_tmap_1, axiom,
% 0.38/0.62    (![A:$i]:
% 0.38/0.62     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.38/0.62       ( ![B:$i]:
% 0.38/0.62         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.38/0.62           ( ( ( u1_struct_0 @ ( k8_tmap_1 @ A @ B ) ) = ( u1_struct_0 @ A ) ) & 
% 0.38/0.62             ( ![C:$i]:
% 0.38/0.62               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.38/0.62                 ( ( ( C ) = ( u1_struct_0 @ B ) ) =>
% 0.38/0.62                   ( ( u1_pre_topc @ ( k8_tmap_1 @ A @ B ) ) =
% 0.38/0.62                     ( k5_tmap_1 @ A @ C ) ) ) ) ) ) ) ) ))).
% 0.38/0.62  thf('2', plain,
% 0.38/0.62      (![X25 : $i, X26 : $i]:
% 0.38/0.62         ((v2_struct_0 @ X25)
% 0.38/0.62          | ~ (m1_pre_topc @ X25 @ X26)
% 0.38/0.62          | ((u1_struct_0 @ (k8_tmap_1 @ X26 @ X25)) = (u1_struct_0 @ X26))
% 0.38/0.62          | ~ (l1_pre_topc @ X26)
% 0.38/0.62          | ~ (v2_pre_topc @ X26)
% 0.38/0.62          | (v2_struct_0 @ X26))),
% 0.38/0.62      inference('cnf', [status(esa)], [t114_tmap_1])).
% 0.38/0.62  thf('3', plain,
% 0.38/0.62      (((v2_struct_0 @ sk_A)
% 0.38/0.62        | ~ (v2_pre_topc @ sk_A)
% 0.38/0.62        | ~ (l1_pre_topc @ sk_A)
% 0.38/0.62        | ((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))
% 0.38/0.62        | (v2_struct_0 @ sk_B))),
% 0.38/0.62      inference('sup-', [status(thm)], ['1', '2'])).
% 0.38/0.62  thf('4', plain, ((v2_pre_topc @ sk_A)),
% 0.38/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.62  thf('5', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.62  thf('6', plain,
% 0.38/0.62      (((v2_struct_0 @ sk_A)
% 0.38/0.62        | ((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))
% 0.38/0.62        | (v2_struct_0 @ sk_B))),
% 0.38/0.62      inference('demod', [status(thm)], ['3', '4', '5'])).
% 0.38/0.62  thf('7', plain, (~ (v2_struct_0 @ sk_A)),
% 0.38/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.62  thf('8', plain,
% 0.38/0.62      (((v2_struct_0 @ sk_B)
% 0.38/0.62        | ((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A)))),
% 0.38/0.62      inference('clc', [status(thm)], ['6', '7'])).
% 0.38/0.62  thf('9', plain, (~ (v2_struct_0 @ sk_B)),
% 0.38/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.62  thf('10', plain,
% 0.38/0.62      (((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 0.38/0.62      inference('clc', [status(thm)], ['8', '9'])).
% 0.38/0.62  thf(d12_tmap_1, axiom,
% 0.38/0.62    (![A:$i]:
% 0.38/0.62     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.38/0.62       ( ![B:$i]:
% 0.38/0.62         ( ( m1_pre_topc @ B @ A ) =>
% 0.38/0.62           ( ![C:$i]:
% 0.38/0.62             ( ( ( v1_funct_1 @ C ) & 
% 0.38/0.62                 ( v1_funct_2 @
% 0.38/0.62                   C @ ( u1_struct_0 @ A ) @ 
% 0.38/0.62                   ( u1_struct_0 @ ( k8_tmap_1 @ A @ B ) ) ) & 
% 0.38/0.62                 ( m1_subset_1 @
% 0.38/0.62                   C @ 
% 0.38/0.62                   ( k1_zfmisc_1 @
% 0.38/0.62                     ( k2_zfmisc_1 @
% 0.38/0.62                       ( u1_struct_0 @ A ) @ 
% 0.38/0.62                       ( u1_struct_0 @ ( k8_tmap_1 @ A @ B ) ) ) ) ) ) =>
% 0.38/0.62               ( ( ( C ) = ( k9_tmap_1 @ A @ B ) ) <=>
% 0.38/0.62                 ( ![D:$i]:
% 0.38/0.62                   ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.38/0.62                     ( ( ( D ) = ( u1_struct_0 @ B ) ) =>
% 0.38/0.62                       ( r1_funct_2 @
% 0.38/0.62                         ( u1_struct_0 @ A ) @ 
% 0.38/0.62                         ( u1_struct_0 @ ( k8_tmap_1 @ A @ B ) ) @ 
% 0.38/0.62                         ( u1_struct_0 @ A ) @ 
% 0.38/0.62                         ( u1_struct_0 @ ( k6_tmap_1 @ A @ D ) ) @ C @ 
% 0.38/0.62                         ( k7_tmap_1 @ A @ D ) ) ) ) ) ) ) ) ) ) ))).
% 0.38/0.62  thf('11', plain,
% 0.38/0.62      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.38/0.62         (~ (m1_pre_topc @ X12 @ X13)
% 0.38/0.62          | ((X14) != (k9_tmap_1 @ X13 @ X12))
% 0.38/0.62          | ((X15) != (u1_struct_0 @ X12))
% 0.38/0.62          | (r1_funct_2 @ (u1_struct_0 @ X13) @ 
% 0.38/0.62             (u1_struct_0 @ (k8_tmap_1 @ X13 @ X12)) @ (u1_struct_0 @ X13) @ 
% 0.38/0.62             (u1_struct_0 @ (k6_tmap_1 @ X13 @ X15)) @ X14 @ 
% 0.38/0.62             (k7_tmap_1 @ X13 @ X15))
% 0.38/0.62          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.38/0.62          | ~ (m1_subset_1 @ X14 @ 
% 0.38/0.62               (k1_zfmisc_1 @ 
% 0.38/0.62                (k2_zfmisc_1 @ (u1_struct_0 @ X13) @ 
% 0.38/0.62                 (u1_struct_0 @ (k8_tmap_1 @ X13 @ X12)))))
% 0.38/0.62          | ~ (v1_funct_2 @ X14 @ (u1_struct_0 @ X13) @ 
% 0.38/0.62               (u1_struct_0 @ (k8_tmap_1 @ X13 @ X12)))
% 0.38/0.62          | ~ (v1_funct_1 @ X14)
% 0.38/0.62          | ~ (l1_pre_topc @ X13)
% 0.38/0.62          | ~ (v2_pre_topc @ X13)
% 0.38/0.62          | (v2_struct_0 @ X13))),
% 0.38/0.62      inference('cnf', [status(esa)], [d12_tmap_1])).
% 0.38/0.62  thf('12', plain,
% 0.38/0.62      (![X12 : $i, X13 : $i]:
% 0.38/0.62         ((v2_struct_0 @ X13)
% 0.38/0.62          | ~ (v2_pre_topc @ X13)
% 0.38/0.62          | ~ (l1_pre_topc @ X13)
% 0.38/0.62          | ~ (v1_funct_1 @ (k9_tmap_1 @ X13 @ X12))
% 0.38/0.62          | ~ (v1_funct_2 @ (k9_tmap_1 @ X13 @ X12) @ (u1_struct_0 @ X13) @ 
% 0.38/0.62               (u1_struct_0 @ (k8_tmap_1 @ X13 @ X12)))
% 0.38/0.62          | ~ (m1_subset_1 @ (k9_tmap_1 @ X13 @ X12) @ 
% 0.38/0.62               (k1_zfmisc_1 @ 
% 0.38/0.62                (k2_zfmisc_1 @ (u1_struct_0 @ X13) @ 
% 0.38/0.62                 (u1_struct_0 @ (k8_tmap_1 @ X13 @ X12)))))
% 0.38/0.62          | ~ (m1_subset_1 @ (u1_struct_0 @ X12) @ 
% 0.38/0.62               (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.38/0.62          | (r1_funct_2 @ (u1_struct_0 @ X13) @ 
% 0.38/0.62             (u1_struct_0 @ (k8_tmap_1 @ X13 @ X12)) @ (u1_struct_0 @ X13) @ 
% 0.38/0.62             (u1_struct_0 @ (k6_tmap_1 @ X13 @ (u1_struct_0 @ X12))) @ 
% 0.38/0.62             (k9_tmap_1 @ X13 @ X12) @ (k7_tmap_1 @ X13 @ (u1_struct_0 @ X12)))
% 0.38/0.62          | ~ (m1_pre_topc @ X12 @ X13))),
% 0.38/0.62      inference('simplify', [status(thm)], ['11'])).
% 0.38/0.62  thf('13', plain,
% 0.38/0.62      ((~ (m1_subset_1 @ (k9_tmap_1 @ sk_A @ sk_B) @ 
% 0.38/0.62           (k1_zfmisc_1 @ 
% 0.38/0.62            (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))))
% 0.38/0.62        | ~ (m1_pre_topc @ sk_B @ sk_A)
% 0.38/0.62        | (r1_funct_2 @ (u1_struct_0 @ sk_A) @ 
% 0.38/0.62           (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)) @ (u1_struct_0 @ sk_A) @ 
% 0.38/0.62           (u1_struct_0 @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B))) @ 
% 0.38/0.62           (k9_tmap_1 @ sk_A @ sk_B) @ 
% 0.38/0.62           (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 0.38/0.62        | ~ (m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.38/0.62             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.38/0.62        | ~ (v1_funct_2 @ (k9_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.38/0.62             (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))
% 0.38/0.62        | ~ (v1_funct_1 @ (k9_tmap_1 @ sk_A @ sk_B))
% 0.38/0.62        | ~ (l1_pre_topc @ sk_A)
% 0.38/0.62        | ~ (v2_pre_topc @ sk_A)
% 0.38/0.62        | (v2_struct_0 @ sk_A))),
% 0.38/0.62      inference('sup-', [status(thm)], ['10', '12'])).
% 0.38/0.62  thf('14', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.38/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.62  thf(dt_k9_tmap_1, axiom,
% 0.38/0.62    (![A:$i,B:$i]:
% 0.38/0.62     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.38/0.62         ( l1_pre_topc @ A ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.38/0.62       ( ( v1_funct_1 @ ( k9_tmap_1 @ A @ B ) ) & 
% 0.38/0.62         ( v1_funct_2 @
% 0.38/0.62           ( k9_tmap_1 @ A @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.38/0.62           ( u1_struct_0 @ ( k8_tmap_1 @ A @ B ) ) ) & 
% 0.38/0.62         ( m1_subset_1 @
% 0.38/0.62           ( k9_tmap_1 @ A @ B ) @ 
% 0.38/0.62           ( k1_zfmisc_1 @
% 0.38/0.62             ( k2_zfmisc_1 @
% 0.38/0.62               ( u1_struct_0 @ A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ A @ B ) ) ) ) ) ) ))).
% 0.38/0.62  thf('15', plain,
% 0.38/0.62      (![X20 : $i, X21 : $i]:
% 0.38/0.62         (~ (l1_pre_topc @ X20)
% 0.38/0.62          | ~ (v2_pre_topc @ X20)
% 0.38/0.62          | (v2_struct_0 @ X20)
% 0.38/0.62          | ~ (m1_pre_topc @ X21 @ X20)
% 0.38/0.62          | (m1_subset_1 @ (k9_tmap_1 @ X20 @ X21) @ 
% 0.38/0.62             (k1_zfmisc_1 @ 
% 0.38/0.62              (k2_zfmisc_1 @ (u1_struct_0 @ X20) @ 
% 0.38/0.62               (u1_struct_0 @ (k8_tmap_1 @ X20 @ X21))))))),
% 0.38/0.62      inference('cnf', [status(esa)], [dt_k9_tmap_1])).
% 0.38/0.62  thf('16', plain,
% 0.38/0.62      (((m1_subset_1 @ (k9_tmap_1 @ sk_A @ sk_B) @ 
% 0.38/0.62         (k1_zfmisc_1 @ 
% 0.38/0.62          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.38/0.62           (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))))
% 0.38/0.62        | (v2_struct_0 @ sk_A)
% 0.38/0.62        | ~ (v2_pre_topc @ sk_A)
% 0.38/0.62        | ~ (l1_pre_topc @ sk_A))),
% 0.38/0.62      inference('sup-', [status(thm)], ['14', '15'])).
% 0.38/0.62  thf('17', plain,
% 0.38/0.62      (((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 0.38/0.62      inference('clc', [status(thm)], ['8', '9'])).
% 0.38/0.62  thf('18', plain, ((v2_pre_topc @ sk_A)),
% 0.38/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.62  thf('19', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.62  thf('20', plain,
% 0.38/0.62      (((m1_subset_1 @ (k9_tmap_1 @ sk_A @ sk_B) @ 
% 0.38/0.62         (k1_zfmisc_1 @ 
% 0.38/0.62          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))))
% 0.38/0.62        | (v2_struct_0 @ sk_A))),
% 0.38/0.62      inference('demod', [status(thm)], ['16', '17', '18', '19'])).
% 0.38/0.62  thf('21', plain, (~ (v2_struct_0 @ sk_A)),
% 0.38/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.62  thf('22', plain,
% 0.38/0.62      ((m1_subset_1 @ (k9_tmap_1 @ sk_A @ sk_B) @ 
% 0.38/0.62        (k1_zfmisc_1 @ 
% 0.38/0.62         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))))),
% 0.38/0.62      inference('clc', [status(thm)], ['20', '21'])).
% 0.38/0.62  thf('23', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.38/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.62  thf('24', plain,
% 0.38/0.62      (((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 0.38/0.62      inference('clc', [status(thm)], ['8', '9'])).
% 0.38/0.62  thf('25', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.38/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.62  thf(t1_tsep_1, axiom,
% 0.38/0.62    (![A:$i]:
% 0.38/0.62     ( ( l1_pre_topc @ A ) =>
% 0.38/0.62       ( ![B:$i]:
% 0.38/0.62         ( ( m1_pre_topc @ B @ A ) =>
% 0.38/0.62           ( m1_subset_1 @
% 0.38/0.62             ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.38/0.62  thf('26', plain,
% 0.38/0.62      (![X28 : $i, X29 : $i]:
% 0.38/0.62         (~ (m1_pre_topc @ X28 @ X29)
% 0.38/0.62          | (m1_subset_1 @ (u1_struct_0 @ X28) @ 
% 0.38/0.62             (k1_zfmisc_1 @ (u1_struct_0 @ X29)))
% 0.38/0.62          | ~ (l1_pre_topc @ X29))),
% 0.38/0.62      inference('cnf', [status(esa)], [t1_tsep_1])).
% 0.38/0.62  thf('27', plain,
% 0.38/0.62      ((~ (l1_pre_topc @ sk_A)
% 0.38/0.62        | (m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.38/0.62           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.38/0.62      inference('sup-', [status(thm)], ['25', '26'])).
% 0.38/0.62  thf('28', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.62  thf('29', plain,
% 0.38/0.62      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.38/0.62        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.38/0.62      inference('demod', [status(thm)], ['27', '28'])).
% 0.38/0.62  thf(d11_tmap_1, axiom,
% 0.38/0.62    (![A:$i]:
% 0.38/0.62     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.38/0.62       ( ![B:$i]:
% 0.38/0.62         ( ( m1_pre_topc @ B @ A ) =>
% 0.38/0.62           ( ![C:$i]:
% 0.38/0.62             ( ( ( v1_pre_topc @ C ) & ( v2_pre_topc @ C ) & 
% 0.38/0.62                 ( l1_pre_topc @ C ) ) =>
% 0.38/0.62               ( ( ( C ) = ( k8_tmap_1 @ A @ B ) ) <=>
% 0.38/0.62                 ( ![D:$i]:
% 0.38/0.62                   ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.38/0.62                     ( ( ( D ) = ( u1_struct_0 @ B ) ) =>
% 0.38/0.62                       ( ( C ) = ( k6_tmap_1 @ A @ D ) ) ) ) ) ) ) ) ) ) ))).
% 0.38/0.62  thf('30', plain,
% 0.38/0.62      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.38/0.62         (~ (m1_pre_topc @ X8 @ X9)
% 0.38/0.62          | ((X10) != (k8_tmap_1 @ X9 @ X8))
% 0.38/0.62          | ((X11) != (u1_struct_0 @ X8))
% 0.38/0.62          | ((X10) = (k6_tmap_1 @ X9 @ X11))
% 0.38/0.62          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.38/0.62          | ~ (l1_pre_topc @ X10)
% 0.38/0.62          | ~ (v2_pre_topc @ X10)
% 0.38/0.62          | ~ (v1_pre_topc @ X10)
% 0.38/0.62          | ~ (l1_pre_topc @ X9)
% 0.38/0.62          | ~ (v2_pre_topc @ X9)
% 0.38/0.62          | (v2_struct_0 @ X9))),
% 0.38/0.62      inference('cnf', [status(esa)], [d11_tmap_1])).
% 0.38/0.62  thf('31', plain,
% 0.38/0.62      (![X8 : $i, X9 : $i]:
% 0.38/0.62         ((v2_struct_0 @ X9)
% 0.38/0.62          | ~ (v2_pre_topc @ X9)
% 0.38/0.62          | ~ (l1_pre_topc @ X9)
% 0.38/0.62          | ~ (v1_pre_topc @ (k8_tmap_1 @ X9 @ X8))
% 0.38/0.62          | ~ (v2_pre_topc @ (k8_tmap_1 @ X9 @ X8))
% 0.38/0.62          | ~ (l1_pre_topc @ (k8_tmap_1 @ X9 @ X8))
% 0.38/0.62          | ~ (m1_subset_1 @ (u1_struct_0 @ X8) @ 
% 0.38/0.62               (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.38/0.62          | ((k8_tmap_1 @ X9 @ X8) = (k6_tmap_1 @ X9 @ (u1_struct_0 @ X8)))
% 0.38/0.62          | ~ (m1_pre_topc @ X8 @ X9))),
% 0.38/0.62      inference('simplify', [status(thm)], ['30'])).
% 0.38/0.62  thf('32', plain,
% 0.38/0.62      ((~ (m1_pre_topc @ sk_B @ sk_A)
% 0.38/0.62        | ((k8_tmap_1 @ sk_A @ sk_B)
% 0.38/0.62            = (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 0.38/0.62        | ~ (l1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.38/0.62        | ~ (v2_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.38/0.62        | ~ (v1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.38/0.62        | ~ (l1_pre_topc @ sk_A)
% 0.38/0.62        | ~ (v2_pre_topc @ sk_A)
% 0.38/0.62        | (v2_struct_0 @ sk_A))),
% 0.38/0.62      inference('sup-', [status(thm)], ['29', '31'])).
% 0.38/0.62  thf('33', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.38/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.62  thf('34', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.38/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.62  thf(dt_k8_tmap_1, axiom,
% 0.38/0.62    (![A:$i,B:$i]:
% 0.38/0.62     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.38/0.62         ( l1_pre_topc @ A ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.38/0.62       ( ( v1_pre_topc @ ( k8_tmap_1 @ A @ B ) ) & 
% 0.38/0.62         ( v2_pre_topc @ ( k8_tmap_1 @ A @ B ) ) & 
% 0.38/0.62         ( l1_pre_topc @ ( k8_tmap_1 @ A @ B ) ) ) ))).
% 0.38/0.62  thf('35', plain,
% 0.38/0.62      (![X18 : $i, X19 : $i]:
% 0.38/0.62         (~ (l1_pre_topc @ X18)
% 0.38/0.62          | ~ (v2_pre_topc @ X18)
% 0.38/0.62          | (v2_struct_0 @ X18)
% 0.38/0.62          | ~ (m1_pre_topc @ X19 @ X18)
% 0.38/0.62          | (l1_pre_topc @ (k8_tmap_1 @ X18 @ X19)))),
% 0.38/0.62      inference('cnf', [status(esa)], [dt_k8_tmap_1])).
% 0.38/0.62  thf('36', plain,
% 0.38/0.62      (((l1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.38/0.62        | (v2_struct_0 @ sk_A)
% 0.38/0.62        | ~ (v2_pre_topc @ sk_A)
% 0.38/0.62        | ~ (l1_pre_topc @ sk_A))),
% 0.38/0.62      inference('sup-', [status(thm)], ['34', '35'])).
% 0.38/0.62  thf('37', plain, ((v2_pre_topc @ sk_A)),
% 0.38/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.62  thf('38', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.62  thf('39', plain,
% 0.38/0.62      (((l1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B)) | (v2_struct_0 @ sk_A))),
% 0.38/0.62      inference('demod', [status(thm)], ['36', '37', '38'])).
% 0.38/0.62  thf('40', plain, (~ (v2_struct_0 @ sk_A)),
% 0.38/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.62  thf('41', plain, ((l1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))),
% 0.38/0.62      inference('clc', [status(thm)], ['39', '40'])).
% 0.38/0.62  thf('42', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.38/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.62  thf('43', plain,
% 0.38/0.62      (![X18 : $i, X19 : $i]:
% 0.38/0.62         (~ (l1_pre_topc @ X18)
% 0.38/0.62          | ~ (v2_pre_topc @ X18)
% 0.38/0.62          | (v2_struct_0 @ X18)
% 0.38/0.62          | ~ (m1_pre_topc @ X19 @ X18)
% 0.38/0.62          | (v2_pre_topc @ (k8_tmap_1 @ X18 @ X19)))),
% 0.38/0.62      inference('cnf', [status(esa)], [dt_k8_tmap_1])).
% 0.38/0.62  thf('44', plain,
% 0.38/0.62      (((v2_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.38/0.62        | (v2_struct_0 @ sk_A)
% 0.38/0.62        | ~ (v2_pre_topc @ sk_A)
% 0.38/0.62        | ~ (l1_pre_topc @ sk_A))),
% 0.38/0.62      inference('sup-', [status(thm)], ['42', '43'])).
% 0.38/0.62  thf('45', plain, ((v2_pre_topc @ sk_A)),
% 0.38/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.62  thf('46', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.62  thf('47', plain,
% 0.38/0.62      (((v2_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B)) | (v2_struct_0 @ sk_A))),
% 0.38/0.62      inference('demod', [status(thm)], ['44', '45', '46'])).
% 0.38/0.62  thf('48', plain, (~ (v2_struct_0 @ sk_A)),
% 0.38/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.62  thf('49', plain, ((v2_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))),
% 0.38/0.62      inference('clc', [status(thm)], ['47', '48'])).
% 0.38/0.62  thf('50', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.38/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.62  thf('51', plain,
% 0.38/0.62      (![X18 : $i, X19 : $i]:
% 0.38/0.62         (~ (l1_pre_topc @ X18)
% 0.38/0.62          | ~ (v2_pre_topc @ X18)
% 0.38/0.62          | (v2_struct_0 @ X18)
% 0.38/0.62          | ~ (m1_pre_topc @ X19 @ X18)
% 0.38/0.62          | (v1_pre_topc @ (k8_tmap_1 @ X18 @ X19)))),
% 0.38/0.62      inference('cnf', [status(esa)], [dt_k8_tmap_1])).
% 0.38/0.62  thf('52', plain,
% 0.38/0.62      (((v1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.38/0.62        | (v2_struct_0 @ sk_A)
% 0.38/0.62        | ~ (v2_pre_topc @ sk_A)
% 0.38/0.62        | ~ (l1_pre_topc @ sk_A))),
% 0.38/0.62      inference('sup-', [status(thm)], ['50', '51'])).
% 0.38/0.62  thf('53', plain, ((v2_pre_topc @ sk_A)),
% 0.38/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.62  thf('54', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.62  thf('55', plain,
% 0.38/0.62      (((v1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B)) | (v2_struct_0 @ sk_A))),
% 0.38/0.62      inference('demod', [status(thm)], ['52', '53', '54'])).
% 0.38/0.62  thf('56', plain, (~ (v2_struct_0 @ sk_A)),
% 0.38/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.62  thf('57', plain, ((v1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))),
% 0.38/0.62      inference('clc', [status(thm)], ['55', '56'])).
% 0.38/0.62  thf('58', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.62  thf('59', plain, ((v2_pre_topc @ sk_A)),
% 0.38/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.62  thf('60', plain,
% 0.38/0.62      ((((k8_tmap_1 @ sk_A @ sk_B) = (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 0.38/0.62        | (v2_struct_0 @ sk_A))),
% 0.38/0.62      inference('demod', [status(thm)],
% 0.38/0.62                ['32', '33', '41', '49', '57', '58', '59'])).
% 0.38/0.62  thf('61', plain, (~ (v2_struct_0 @ sk_A)),
% 0.38/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.62  thf('62', plain,
% 0.38/0.62      (((k8_tmap_1 @ sk_A @ sk_B) = (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))),
% 0.38/0.62      inference('clc', [status(thm)], ['60', '61'])).
% 0.38/0.62  thf('63', plain,
% 0.38/0.62      (((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 0.38/0.62      inference('clc', [status(thm)], ['8', '9'])).
% 0.38/0.62  thf('64', plain,
% 0.38/0.62      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.38/0.62        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.38/0.62      inference('demod', [status(thm)], ['27', '28'])).
% 0.38/0.62  thf('65', plain,
% 0.38/0.62      (((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 0.38/0.62      inference('clc', [status(thm)], ['8', '9'])).
% 0.38/0.62  thf('66', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.38/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.62  thf('67', plain,
% 0.38/0.62      (![X20 : $i, X21 : $i]:
% 0.38/0.62         (~ (l1_pre_topc @ X20)
% 0.38/0.62          | ~ (v2_pre_topc @ X20)
% 0.38/0.62          | (v2_struct_0 @ X20)
% 0.38/0.62          | ~ (m1_pre_topc @ X21 @ X20)
% 0.38/0.62          | (v1_funct_2 @ (k9_tmap_1 @ X20 @ X21) @ (u1_struct_0 @ X20) @ 
% 0.38/0.62             (u1_struct_0 @ (k8_tmap_1 @ X20 @ X21))))),
% 0.38/0.62      inference('cnf', [status(esa)], [dt_k9_tmap_1])).
% 0.38/0.62  thf('68', plain,
% 0.38/0.62      (((v1_funct_2 @ (k9_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.38/0.62         (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))
% 0.38/0.62        | (v2_struct_0 @ sk_A)
% 0.38/0.62        | ~ (v2_pre_topc @ sk_A)
% 0.38/0.62        | ~ (l1_pre_topc @ sk_A))),
% 0.38/0.62      inference('sup-', [status(thm)], ['66', '67'])).
% 0.38/0.62  thf('69', plain,
% 0.38/0.62      (((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 0.38/0.62      inference('clc', [status(thm)], ['8', '9'])).
% 0.38/0.62  thf('70', plain, ((v2_pre_topc @ sk_A)),
% 0.38/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.62  thf('71', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.62  thf('72', plain,
% 0.38/0.62      (((v1_funct_2 @ (k9_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.38/0.62         (u1_struct_0 @ sk_A))
% 0.38/0.62        | (v2_struct_0 @ sk_A))),
% 0.38/0.62      inference('demod', [status(thm)], ['68', '69', '70', '71'])).
% 0.38/0.62  thf('73', plain, (~ (v2_struct_0 @ sk_A)),
% 0.38/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.62  thf('74', plain,
% 0.38/0.62      ((v1_funct_2 @ (k9_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.38/0.62        (u1_struct_0 @ sk_A))),
% 0.38/0.62      inference('clc', [status(thm)], ['72', '73'])).
% 0.38/0.62  thf('75', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.38/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.62  thf('76', plain,
% 0.38/0.62      (![X20 : $i, X21 : $i]:
% 0.38/0.62         (~ (l1_pre_topc @ X20)
% 0.38/0.62          | ~ (v2_pre_topc @ X20)
% 0.38/0.62          | (v2_struct_0 @ X20)
% 0.38/0.62          | ~ (m1_pre_topc @ X21 @ X20)
% 0.38/0.62          | (v1_funct_1 @ (k9_tmap_1 @ X20 @ X21)))),
% 0.38/0.62      inference('cnf', [status(esa)], [dt_k9_tmap_1])).
% 0.38/0.62  thf('77', plain,
% 0.38/0.62      (((v1_funct_1 @ (k9_tmap_1 @ sk_A @ sk_B))
% 0.38/0.62        | (v2_struct_0 @ sk_A)
% 0.38/0.62        | ~ (v2_pre_topc @ sk_A)
% 0.38/0.62        | ~ (l1_pre_topc @ sk_A))),
% 0.38/0.62      inference('sup-', [status(thm)], ['75', '76'])).
% 0.38/0.62  thf('78', plain, ((v2_pre_topc @ sk_A)),
% 0.38/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.62  thf('79', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.62  thf('80', plain,
% 0.38/0.62      (((v1_funct_1 @ (k9_tmap_1 @ sk_A @ sk_B)) | (v2_struct_0 @ sk_A))),
% 0.38/0.62      inference('demod', [status(thm)], ['77', '78', '79'])).
% 0.38/0.62  thf('81', plain, (~ (v2_struct_0 @ sk_A)),
% 0.38/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.62  thf('82', plain, ((v1_funct_1 @ (k9_tmap_1 @ sk_A @ sk_B))),
% 0.38/0.62      inference('clc', [status(thm)], ['80', '81'])).
% 0.38/0.62  thf('83', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.62  thf('84', plain, ((v2_pre_topc @ sk_A)),
% 0.38/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.62  thf('85', plain,
% 0.38/0.62      (((r1_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.38/0.62         (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.38/0.62         (k9_tmap_1 @ sk_A @ sk_B) @ (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 0.38/0.62        | (v2_struct_0 @ sk_A))),
% 0.38/0.62      inference('demod', [status(thm)],
% 0.38/0.62                ['13', '22', '23', '24', '62', '63', '64', '65', '74', '82', 
% 0.38/0.62                 '83', '84'])).
% 0.38/0.62  thf('86', plain, (~ (v2_struct_0 @ sk_A)),
% 0.38/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.62  thf('87', plain,
% 0.38/0.62      ((r1_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.38/0.62        (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.38/0.62        (k9_tmap_1 @ sk_A @ sk_B) @ (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))),
% 0.38/0.62      inference('clc', [status(thm)], ['85', '86'])).
% 0.38/0.62  thf('88', plain,
% 0.38/0.62      ((m1_subset_1 @ (k9_tmap_1 @ sk_A @ sk_B) @ 
% 0.38/0.62        (k1_zfmisc_1 @ 
% 0.38/0.62         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))))),
% 0.38/0.62      inference('clc', [status(thm)], ['20', '21'])).
% 0.38/0.62  thf(redefinition_r1_funct_2, axiom,
% 0.38/0.62    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.38/0.62     ( ( ( ~( v1_xboole_0 @ B ) ) & ( ~( v1_xboole_0 @ D ) ) & 
% 0.38/0.62         ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ A @ B ) & 
% 0.38/0.62         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.38/0.62         ( v1_funct_1 @ F ) & ( v1_funct_2 @ F @ C @ D ) & 
% 0.38/0.62         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.38/0.62       ( ( r1_funct_2 @ A @ B @ C @ D @ E @ F ) <=> ( ( E ) = ( F ) ) ) ))).
% 0.38/0.62  thf('89', plain,
% 0.38/0.62      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.38/0.62         (~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X4)))
% 0.38/0.62          | ~ (v1_funct_2 @ X2 @ X3 @ X4)
% 0.38/0.62          | ~ (v1_funct_1 @ X2)
% 0.38/0.62          | (v1_xboole_0 @ X5)
% 0.38/0.62          | (v1_xboole_0 @ X4)
% 0.38/0.62          | ~ (v1_funct_1 @ X6)
% 0.38/0.62          | ~ (v1_funct_2 @ X6 @ X7 @ X5)
% 0.38/0.62          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X5)))
% 0.38/0.62          | ((X2) = (X6))
% 0.38/0.62          | ~ (r1_funct_2 @ X3 @ X4 @ X7 @ X5 @ X2 @ X6))),
% 0.38/0.62      inference('cnf', [status(esa)], [redefinition_r1_funct_2])).
% 0.38/0.62  thf('90', plain,
% 0.38/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.38/0.62         (~ (r1_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ X2 @ 
% 0.38/0.62             X1 @ (k9_tmap_1 @ sk_A @ sk_B) @ X0)
% 0.38/0.62          | ((k9_tmap_1 @ sk_A @ sk_B) = (X0))
% 0.38/0.62          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.38/0.62          | ~ (v1_funct_2 @ X0 @ X2 @ X1)
% 0.38/0.62          | ~ (v1_funct_1 @ X0)
% 0.38/0.62          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.38/0.62          | (v1_xboole_0 @ X1)
% 0.38/0.62          | ~ (v1_funct_1 @ (k9_tmap_1 @ sk_A @ sk_B))
% 0.38/0.62          | ~ (v1_funct_2 @ (k9_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.38/0.62               (u1_struct_0 @ sk_A)))),
% 0.38/0.62      inference('sup-', [status(thm)], ['88', '89'])).
% 0.38/0.62  thf('91', plain, ((v1_funct_1 @ (k9_tmap_1 @ sk_A @ sk_B))),
% 0.38/0.62      inference('clc', [status(thm)], ['80', '81'])).
% 0.38/0.62  thf('92', plain,
% 0.38/0.62      ((v1_funct_2 @ (k9_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.38/0.62        (u1_struct_0 @ sk_A))),
% 0.38/0.62      inference('clc', [status(thm)], ['72', '73'])).
% 0.38/0.62  thf('93', plain,
% 0.38/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.38/0.62         (~ (r1_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ X2 @ 
% 0.38/0.62             X1 @ (k9_tmap_1 @ sk_A @ sk_B) @ X0)
% 0.38/0.62          | ((k9_tmap_1 @ sk_A @ sk_B) = (X0))
% 0.38/0.62          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.38/0.62          | ~ (v1_funct_2 @ X0 @ X2 @ X1)
% 0.38/0.62          | ~ (v1_funct_1 @ X0)
% 0.38/0.62          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.38/0.62          | (v1_xboole_0 @ X1))),
% 0.38/0.62      inference('demod', [status(thm)], ['90', '91', '92'])).
% 0.38/0.62  thf('94', plain,
% 0.38/0.62      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.38/0.62        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.38/0.62        | ~ (v1_funct_1 @ (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 0.38/0.62        | ~ (v1_funct_2 @ (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)) @ 
% 0.38/0.62             (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.38/0.62        | ~ (m1_subset_1 @ (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)) @ 
% 0.38/0.62             (k1_zfmisc_1 @ 
% 0.38/0.62              (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))))
% 0.38/0.62        | ((k9_tmap_1 @ sk_A @ sk_B)
% 0.38/0.62            = (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B))))),
% 0.38/0.62      inference('sup-', [status(thm)], ['87', '93'])).
% 0.38/0.62  thf('95', plain,
% 0.38/0.62      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.38/0.62        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.38/0.62      inference('demod', [status(thm)], ['27', '28'])).
% 0.38/0.62  thf(dt_k7_tmap_1, axiom,
% 0.38/0.62    (![A:$i,B:$i]:
% 0.38/0.62     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.38/0.62         ( l1_pre_topc @ A ) & 
% 0.38/0.62         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.38/0.62       ( ( v1_funct_1 @ ( k7_tmap_1 @ A @ B ) ) & 
% 0.38/0.62         ( v1_funct_2 @
% 0.38/0.62           ( k7_tmap_1 @ A @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.38/0.62           ( u1_struct_0 @ ( k6_tmap_1 @ A @ B ) ) ) & 
% 0.38/0.62         ( m1_subset_1 @
% 0.38/0.62           ( k7_tmap_1 @ A @ B ) @ 
% 0.38/0.62           ( k1_zfmisc_1 @
% 0.38/0.62             ( k2_zfmisc_1 @
% 0.38/0.62               ( u1_struct_0 @ A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ A @ B ) ) ) ) ) ) ))).
% 0.38/0.62  thf('96', plain,
% 0.38/0.62      (![X16 : $i, X17 : $i]:
% 0.38/0.62         (~ (l1_pre_topc @ X16)
% 0.38/0.62          | ~ (v2_pre_topc @ X16)
% 0.38/0.62          | (v2_struct_0 @ X16)
% 0.38/0.62          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.38/0.62          | (v1_funct_1 @ (k7_tmap_1 @ X16 @ X17)))),
% 0.38/0.62      inference('cnf', [status(esa)], [dt_k7_tmap_1])).
% 0.38/0.62  thf('97', plain,
% 0.38/0.62      (((v1_funct_1 @ (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 0.38/0.62        | (v2_struct_0 @ sk_A)
% 0.38/0.62        | ~ (v2_pre_topc @ sk_A)
% 0.38/0.62        | ~ (l1_pre_topc @ sk_A))),
% 0.38/0.62      inference('sup-', [status(thm)], ['95', '96'])).
% 0.38/0.62  thf('98', plain, ((v2_pre_topc @ sk_A)),
% 0.38/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.62  thf('99', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.62  thf('100', plain,
% 0.38/0.62      (((v1_funct_1 @ (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 0.38/0.62        | (v2_struct_0 @ sk_A))),
% 0.38/0.62      inference('demod', [status(thm)], ['97', '98', '99'])).
% 0.38/0.62  thf('101', plain, (~ (v2_struct_0 @ sk_A)),
% 0.38/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.62  thf('102', plain, ((v1_funct_1 @ (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))),
% 0.38/0.62      inference('clc', [status(thm)], ['100', '101'])).
% 0.38/0.62  thf('103', plain,
% 0.38/0.62      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.38/0.62        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.38/0.62      inference('demod', [status(thm)], ['27', '28'])).
% 0.38/0.62  thf('104', plain,
% 0.38/0.62      (![X16 : $i, X17 : $i]:
% 0.38/0.62         (~ (l1_pre_topc @ X16)
% 0.38/0.62          | ~ (v2_pre_topc @ X16)
% 0.38/0.62          | (v2_struct_0 @ X16)
% 0.38/0.62          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.38/0.62          | (v1_funct_2 @ (k7_tmap_1 @ X16 @ X17) @ (u1_struct_0 @ X16) @ 
% 0.38/0.62             (u1_struct_0 @ (k6_tmap_1 @ X16 @ X17))))),
% 0.38/0.62      inference('cnf', [status(esa)], [dt_k7_tmap_1])).
% 0.38/0.62  thf('105', plain,
% 0.38/0.62      (((v1_funct_2 @ (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)) @ 
% 0.38/0.62         (u1_struct_0 @ sk_A) @ 
% 0.38/0.62         (u1_struct_0 @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B))))
% 0.38/0.62        | (v2_struct_0 @ sk_A)
% 0.38/0.62        | ~ (v2_pre_topc @ sk_A)
% 0.38/0.62        | ~ (l1_pre_topc @ sk_A))),
% 0.38/0.62      inference('sup-', [status(thm)], ['103', '104'])).
% 0.38/0.62  thf('106', plain, ((v2_pre_topc @ sk_A)),
% 0.38/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.62  thf('107', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.62  thf('108', plain,
% 0.38/0.62      (((v1_funct_2 @ (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)) @ 
% 0.38/0.62         (u1_struct_0 @ sk_A) @ 
% 0.38/0.62         (u1_struct_0 @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B))))
% 0.38/0.62        | (v2_struct_0 @ sk_A))),
% 0.38/0.62      inference('demod', [status(thm)], ['105', '106', '107'])).
% 0.38/0.62  thf('109', plain, (~ (v2_struct_0 @ sk_A)),
% 0.38/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.62  thf('110', plain,
% 0.38/0.62      ((v1_funct_2 @ (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)) @ 
% 0.38/0.62        (u1_struct_0 @ sk_A) @ 
% 0.38/0.62        (u1_struct_0 @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B))))),
% 0.38/0.62      inference('clc', [status(thm)], ['108', '109'])).
% 0.38/0.62  thf('111', plain,
% 0.38/0.62      (((k8_tmap_1 @ sk_A @ sk_B) = (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))),
% 0.38/0.62      inference('clc', [status(thm)], ['60', '61'])).
% 0.38/0.62  thf('112', plain,
% 0.38/0.62      (((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 0.38/0.62      inference('clc', [status(thm)], ['8', '9'])).
% 0.38/0.62  thf('113', plain,
% 0.38/0.62      ((v1_funct_2 @ (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)) @ 
% 0.38/0.62        (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))),
% 0.38/0.62      inference('demod', [status(thm)], ['110', '111', '112'])).
% 0.38/0.62  thf('114', plain,
% 0.38/0.62      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.38/0.62        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.38/0.62      inference('demod', [status(thm)], ['27', '28'])).
% 0.38/0.62  thf('115', plain,
% 0.38/0.62      (![X16 : $i, X17 : $i]:
% 0.38/0.62         (~ (l1_pre_topc @ X16)
% 0.38/0.62          | ~ (v2_pre_topc @ X16)
% 0.38/0.62          | (v2_struct_0 @ X16)
% 0.38/0.62          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.38/0.62          | (m1_subset_1 @ (k7_tmap_1 @ X16 @ X17) @ 
% 0.38/0.62             (k1_zfmisc_1 @ 
% 0.38/0.62              (k2_zfmisc_1 @ (u1_struct_0 @ X16) @ 
% 0.38/0.62               (u1_struct_0 @ (k6_tmap_1 @ X16 @ X17))))))),
% 0.38/0.62      inference('cnf', [status(esa)], [dt_k7_tmap_1])).
% 0.38/0.62  thf('116', plain,
% 0.38/0.62      (((m1_subset_1 @ (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)) @ 
% 0.38/0.62         (k1_zfmisc_1 @ 
% 0.38/0.62          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.38/0.62           (u1_struct_0 @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B))))))
% 0.38/0.62        | (v2_struct_0 @ sk_A)
% 0.38/0.62        | ~ (v2_pre_topc @ sk_A)
% 0.38/0.62        | ~ (l1_pre_topc @ sk_A))),
% 0.38/0.62      inference('sup-', [status(thm)], ['114', '115'])).
% 0.38/0.62  thf('117', plain, ((v2_pre_topc @ sk_A)),
% 0.38/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.62  thf('118', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.62  thf('119', plain,
% 0.38/0.62      (((m1_subset_1 @ (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)) @ 
% 0.38/0.62         (k1_zfmisc_1 @ 
% 0.38/0.62          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.38/0.62           (u1_struct_0 @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B))))))
% 0.38/0.62        | (v2_struct_0 @ sk_A))),
% 0.38/0.62      inference('demod', [status(thm)], ['116', '117', '118'])).
% 0.38/0.62  thf('120', plain, (~ (v2_struct_0 @ sk_A)),
% 0.38/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.62  thf('121', plain,
% 0.38/0.62      ((m1_subset_1 @ (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)) @ 
% 0.38/0.62        (k1_zfmisc_1 @ 
% 0.38/0.62         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.38/0.62          (u1_struct_0 @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B))))))),
% 0.38/0.62      inference('clc', [status(thm)], ['119', '120'])).
% 0.38/0.62  thf('122', plain,
% 0.38/0.62      (((k8_tmap_1 @ sk_A @ sk_B) = (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))),
% 0.38/0.62      inference('clc', [status(thm)], ['60', '61'])).
% 0.38/0.62  thf('123', plain,
% 0.38/0.62      (((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 0.38/0.62      inference('clc', [status(thm)], ['8', '9'])).
% 0.38/0.62  thf('124', plain,
% 0.38/0.62      ((m1_subset_1 @ (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)) @ 
% 0.38/0.62        (k1_zfmisc_1 @ 
% 0.38/0.62         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))))),
% 0.38/0.62      inference('demod', [status(thm)], ['121', '122', '123'])).
% 0.38/0.62  thf('125', plain,
% 0.38/0.62      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.38/0.62        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.38/0.62        | ((k9_tmap_1 @ sk_A @ sk_B)
% 0.38/0.62            = (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B))))),
% 0.38/0.62      inference('demod', [status(thm)], ['94', '102', '113', '124'])).
% 0.38/0.62  thf('126', plain,
% 0.38/0.62      ((((k9_tmap_1 @ sk_A @ sk_B) = (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 0.38/0.62        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.38/0.62      inference('simplify', [status(thm)], ['125'])).
% 0.38/0.62  thf('127', plain,
% 0.38/0.62      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.38/0.62        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.38/0.62      inference('demod', [status(thm)], ['27', '28'])).
% 0.38/0.62  thf(t112_tmap_1, axiom,
% 0.38/0.62    (![A:$i]:
% 0.38/0.62     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.38/0.62       ( ![B:$i]:
% 0.38/0.62         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.38/0.62           ( ![C:$i]:
% 0.38/0.62             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.38/0.62               ( ( ( u1_struct_0 @ C ) = ( B ) ) =>
% 0.38/0.62                 ( ( v1_funct_1 @
% 0.38/0.62                     ( k2_tmap_1 @
% 0.38/0.62                       A @ ( k6_tmap_1 @ A @ B ) @ ( k7_tmap_1 @ A @ B ) @ C ) ) & 
% 0.38/0.62                   ( v1_funct_2 @
% 0.38/0.62                     ( k2_tmap_1 @
% 0.38/0.62                       A @ ( k6_tmap_1 @ A @ B ) @ ( k7_tmap_1 @ A @ B ) @ C ) @ 
% 0.38/0.62                     ( u1_struct_0 @ C ) @ 
% 0.38/0.62                     ( u1_struct_0 @ ( k6_tmap_1 @ A @ B ) ) ) & 
% 0.38/0.62                   ( v5_pre_topc @
% 0.38/0.62                     ( k2_tmap_1 @
% 0.38/0.62                       A @ ( k6_tmap_1 @ A @ B ) @ ( k7_tmap_1 @ A @ B ) @ C ) @ 
% 0.38/0.62                     C @ ( k6_tmap_1 @ A @ B ) ) & 
% 0.38/0.62                   ( m1_subset_1 @
% 0.38/0.62                     ( k2_tmap_1 @
% 0.38/0.62                       A @ ( k6_tmap_1 @ A @ B ) @ ( k7_tmap_1 @ A @ B ) @ C ) @ 
% 0.38/0.62                     ( k1_zfmisc_1 @
% 0.38/0.62                       ( k2_zfmisc_1 @
% 0.38/0.62                         ( u1_struct_0 @ C ) @ 
% 0.38/0.62                         ( u1_struct_0 @ ( k6_tmap_1 @ A @ B ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.38/0.62  thf('128', plain,
% 0.38/0.62      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.38/0.62         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 0.38/0.62          | ((u1_struct_0 @ X24) != (X22))
% 0.38/0.62          | (m1_subset_1 @ 
% 0.38/0.62             (k2_tmap_1 @ X23 @ (k6_tmap_1 @ X23 @ X22) @ 
% 0.38/0.62              (k7_tmap_1 @ X23 @ X22) @ X24) @ 
% 0.38/0.62             (k1_zfmisc_1 @ 
% 0.38/0.62              (k2_zfmisc_1 @ (u1_struct_0 @ X24) @ 
% 0.38/0.62               (u1_struct_0 @ (k6_tmap_1 @ X23 @ X22)))))
% 0.38/0.62          | ~ (m1_pre_topc @ X24 @ X23)
% 0.38/0.62          | (v2_struct_0 @ X24)
% 0.38/0.62          | ~ (l1_pre_topc @ X23)
% 0.38/0.62          | ~ (v2_pre_topc @ X23)
% 0.38/0.62          | (v2_struct_0 @ X23))),
% 0.38/0.62      inference('cnf', [status(esa)], [t112_tmap_1])).
% 0.38/0.62  thf('129', plain,
% 0.38/0.62      (![X23 : $i, X24 : $i]:
% 0.38/0.62         ((v2_struct_0 @ X23)
% 0.38/0.62          | ~ (v2_pre_topc @ X23)
% 0.38/0.62          | ~ (l1_pre_topc @ X23)
% 0.38/0.62          | (v2_struct_0 @ X24)
% 0.38/0.62          | ~ (m1_pre_topc @ X24 @ X23)
% 0.38/0.62          | (m1_subset_1 @ 
% 0.38/0.62             (k2_tmap_1 @ X23 @ (k6_tmap_1 @ X23 @ (u1_struct_0 @ X24)) @ 
% 0.38/0.62              (k7_tmap_1 @ X23 @ (u1_struct_0 @ X24)) @ X24) @ 
% 0.38/0.62             (k1_zfmisc_1 @ 
% 0.38/0.62              (k2_zfmisc_1 @ (u1_struct_0 @ X24) @ 
% 0.38/0.62               (u1_struct_0 @ (k6_tmap_1 @ X23 @ (u1_struct_0 @ X24))))))
% 0.38/0.62          | ~ (m1_subset_1 @ (u1_struct_0 @ X24) @ 
% 0.38/0.62               (k1_zfmisc_1 @ (u1_struct_0 @ X23))))),
% 0.38/0.62      inference('simplify', [status(thm)], ['128'])).
% 0.38/0.62  thf('130', plain,
% 0.38/0.62      (((m1_subset_1 @ 
% 0.38/0.62         (k2_tmap_1 @ sk_A @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)) @ 
% 0.38/0.62          (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)) @ sk_B) @ 
% 0.38/0.62         (k1_zfmisc_1 @ 
% 0.38/0.62          (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ 
% 0.38/0.62           (u1_struct_0 @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B))))))
% 0.38/0.62        | ~ (m1_pre_topc @ sk_B @ sk_A)
% 0.38/0.62        | (v2_struct_0 @ sk_B)
% 0.38/0.62        | ~ (l1_pre_topc @ sk_A)
% 0.38/0.62        | ~ (v2_pre_topc @ sk_A)
% 0.38/0.62        | (v2_struct_0 @ sk_A))),
% 0.38/0.62      inference('sup-', [status(thm)], ['127', '129'])).
% 0.38/0.62  thf('131', plain,
% 0.38/0.62      (((k8_tmap_1 @ sk_A @ sk_B) = (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))),
% 0.38/0.62      inference('clc', [status(thm)], ['60', '61'])).
% 0.38/0.62  thf('132', plain,
% 0.38/0.62      (((k8_tmap_1 @ sk_A @ sk_B) = (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))),
% 0.38/0.62      inference('clc', [status(thm)], ['60', '61'])).
% 0.38/0.62  thf('133', plain,
% 0.38/0.62      (((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 0.38/0.62      inference('clc', [status(thm)], ['8', '9'])).
% 0.38/0.62  thf('134', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.38/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.62  thf('135', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.62  thf('136', plain, ((v2_pre_topc @ sk_A)),
% 0.38/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.62  thf('137', plain,
% 0.38/0.62      (((m1_subset_1 @ 
% 0.38/0.62         (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.38/0.62          (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)) @ sk_B) @ 
% 0.38/0.62         (k1_zfmisc_1 @ 
% 0.38/0.62          (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))
% 0.38/0.62        | (v2_struct_0 @ sk_B)
% 0.38/0.62        | (v2_struct_0 @ sk_A))),
% 0.38/0.62      inference('demod', [status(thm)],
% 0.38/0.62                ['130', '131', '132', '133', '134', '135', '136'])).
% 0.38/0.62  thf('138', plain, (~ (v2_struct_0 @ sk_B)),
% 0.38/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.62  thf('139', plain,
% 0.38/0.62      (((v2_struct_0 @ sk_A)
% 0.38/0.62        | (m1_subset_1 @ 
% 0.38/0.62           (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.38/0.62            (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)) @ sk_B) @ 
% 0.38/0.62           (k1_zfmisc_1 @ 
% 0.38/0.62            (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A)))))),
% 0.38/0.62      inference('clc', [status(thm)], ['137', '138'])).
% 0.38/0.62  thf('140', plain, (~ (v2_struct_0 @ sk_A)),
% 0.38/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.62  thf('141', plain,
% 0.38/0.62      ((m1_subset_1 @ 
% 0.38/0.62        (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.38/0.62         (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)) @ sk_B) @ 
% 0.38/0.62        (k1_zfmisc_1 @ 
% 0.38/0.62         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.38/0.62      inference('clc', [status(thm)], ['139', '140'])).
% 0.38/0.62  thf('142', plain,
% 0.38/0.62      (((m1_subset_1 @ 
% 0.38/0.62         (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.38/0.62          (k9_tmap_1 @ sk_A @ sk_B) @ sk_B) @ 
% 0.38/0.62         (k1_zfmisc_1 @ 
% 0.38/0.62          (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))
% 0.38/0.62        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.38/0.62      inference('sup+', [status(thm)], ['126', '141'])).
% 0.38/0.62  thf('143', plain,
% 0.38/0.62      ((~ (v1_funct_1 @ 
% 0.38/0.62           (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.38/0.62            (k9_tmap_1 @ sk_A @ sk_B) @ sk_B))
% 0.38/0.62        | ~ (v1_funct_2 @ 
% 0.38/0.62             (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.38/0.62              (k9_tmap_1 @ sk_A @ sk_B) @ sk_B) @ 
% 0.38/0.62             (u1_struct_0 @ sk_B) @ (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))
% 0.38/0.62        | ~ (v5_pre_topc @ 
% 0.38/0.62             (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.38/0.62              (k9_tmap_1 @ sk_A @ sk_B) @ sk_B) @ 
% 0.38/0.62             sk_B @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.38/0.62        | ~ (m1_subset_1 @ 
% 0.38/0.62             (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.38/0.62              (k9_tmap_1 @ sk_A @ sk_B) @ sk_B) @ 
% 0.38/0.62             (k1_zfmisc_1 @ 
% 0.38/0.62              (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ 
% 0.38/0.62               (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B))))))),
% 0.38/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.62  thf('144', plain,
% 0.38/0.62      ((~ (m1_subset_1 @ 
% 0.38/0.62           (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.38/0.62            (k9_tmap_1 @ sk_A @ sk_B) @ sk_B) @ 
% 0.38/0.62           (k1_zfmisc_1 @ 
% 0.38/0.62            (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ 
% 0.38/0.62             (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B))))))
% 0.38/0.62         <= (~
% 0.38/0.62             ((m1_subset_1 @ 
% 0.38/0.62               (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.38/0.62                (k9_tmap_1 @ sk_A @ sk_B) @ sk_B) @ 
% 0.38/0.62               (k1_zfmisc_1 @ 
% 0.38/0.62                (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ 
% 0.38/0.62                 (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))))))),
% 0.38/0.62      inference('split', [status(esa)], ['143'])).
% 0.38/0.62  thf('145', plain,
% 0.38/0.62      (((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 0.38/0.62      inference('clc', [status(thm)], ['8', '9'])).
% 0.38/0.62  thf('146', plain,
% 0.38/0.62      ((~ (m1_subset_1 @ 
% 0.38/0.62           (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.38/0.62            (k9_tmap_1 @ sk_A @ sk_B) @ sk_B) @ 
% 0.38/0.62           (k1_zfmisc_1 @ 
% 0.38/0.62            (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A)))))
% 0.38/0.62         <= (~
% 0.38/0.62             ((m1_subset_1 @ 
% 0.38/0.62               (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.38/0.62                (k9_tmap_1 @ sk_A @ sk_B) @ sk_B) @ 
% 0.38/0.62               (k1_zfmisc_1 @ 
% 0.38/0.62                (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ 
% 0.38/0.62                 (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))))))),
% 0.38/0.62      inference('demod', [status(thm)], ['144', '145'])).
% 0.38/0.62  thf('147', plain,
% 0.38/0.62      ((((k9_tmap_1 @ sk_A @ sk_B) = (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 0.38/0.62        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.38/0.62      inference('simplify', [status(thm)], ['125'])).
% 0.38/0.62  thf('148', plain,
% 0.38/0.62      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.38/0.62        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.38/0.62      inference('demod', [status(thm)], ['27', '28'])).
% 0.38/0.62  thf('149', plain,
% 0.38/0.62      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.38/0.62         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 0.38/0.62          | ((u1_struct_0 @ X24) != (X22))
% 0.38/0.62          | (v1_funct_2 @ 
% 0.38/0.62             (k2_tmap_1 @ X23 @ (k6_tmap_1 @ X23 @ X22) @ 
% 0.38/0.62              (k7_tmap_1 @ X23 @ X22) @ X24) @ 
% 0.38/0.62             (u1_struct_0 @ X24) @ (u1_struct_0 @ (k6_tmap_1 @ X23 @ X22)))
% 0.38/0.62          | ~ (m1_pre_topc @ X24 @ X23)
% 0.38/0.62          | (v2_struct_0 @ X24)
% 0.38/0.62          | ~ (l1_pre_topc @ X23)
% 0.38/0.62          | ~ (v2_pre_topc @ X23)
% 0.38/0.62          | (v2_struct_0 @ X23))),
% 0.38/0.62      inference('cnf', [status(esa)], [t112_tmap_1])).
% 0.38/0.62  thf('150', plain,
% 0.38/0.62      (![X23 : $i, X24 : $i]:
% 0.38/0.62         ((v2_struct_0 @ X23)
% 0.38/0.62          | ~ (v2_pre_topc @ X23)
% 0.38/0.62          | ~ (l1_pre_topc @ X23)
% 0.38/0.62          | (v2_struct_0 @ X24)
% 0.38/0.62          | ~ (m1_pre_topc @ X24 @ X23)
% 0.38/0.62          | (v1_funct_2 @ 
% 0.38/0.62             (k2_tmap_1 @ X23 @ (k6_tmap_1 @ X23 @ (u1_struct_0 @ X24)) @ 
% 0.38/0.62              (k7_tmap_1 @ X23 @ (u1_struct_0 @ X24)) @ X24) @ 
% 0.38/0.62             (u1_struct_0 @ X24) @ 
% 0.38/0.62             (u1_struct_0 @ (k6_tmap_1 @ X23 @ (u1_struct_0 @ X24))))
% 0.38/0.62          | ~ (m1_subset_1 @ (u1_struct_0 @ X24) @ 
% 0.38/0.62               (k1_zfmisc_1 @ (u1_struct_0 @ X23))))),
% 0.38/0.62      inference('simplify', [status(thm)], ['149'])).
% 0.38/0.62  thf('151', plain,
% 0.38/0.62      (((v1_funct_2 @ 
% 0.38/0.62         (k2_tmap_1 @ sk_A @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)) @ 
% 0.38/0.62          (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)) @ sk_B) @ 
% 0.38/0.62         (u1_struct_0 @ sk_B) @ 
% 0.38/0.62         (u1_struct_0 @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B))))
% 0.38/0.62        | ~ (m1_pre_topc @ sk_B @ sk_A)
% 0.38/0.62        | (v2_struct_0 @ sk_B)
% 0.38/0.62        | ~ (l1_pre_topc @ sk_A)
% 0.38/0.62        | ~ (v2_pre_topc @ sk_A)
% 0.38/0.62        | (v2_struct_0 @ sk_A))),
% 0.38/0.62      inference('sup-', [status(thm)], ['148', '150'])).
% 0.38/0.62  thf('152', plain,
% 0.38/0.62      (((k8_tmap_1 @ sk_A @ sk_B) = (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))),
% 0.38/0.62      inference('clc', [status(thm)], ['60', '61'])).
% 0.38/0.62  thf('153', plain,
% 0.38/0.62      (((k8_tmap_1 @ sk_A @ sk_B) = (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))),
% 0.38/0.62      inference('clc', [status(thm)], ['60', '61'])).
% 0.38/0.62  thf('154', plain,
% 0.38/0.62      (((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 0.38/0.62      inference('clc', [status(thm)], ['8', '9'])).
% 0.38/0.62  thf('155', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.38/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.62  thf('156', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.62  thf('157', plain, ((v2_pre_topc @ sk_A)),
% 0.38/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.62  thf('158', plain,
% 0.38/0.62      (((v1_funct_2 @ 
% 0.38/0.62         (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.38/0.62          (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)) @ sk_B) @ 
% 0.38/0.62         (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.38/0.62        | (v2_struct_0 @ sk_B)
% 0.38/0.62        | (v2_struct_0 @ sk_A))),
% 0.38/0.62      inference('demod', [status(thm)],
% 0.38/0.62                ['151', '152', '153', '154', '155', '156', '157'])).
% 0.38/0.62  thf('159', plain, (~ (v2_struct_0 @ sk_B)),
% 0.38/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.62  thf('160', plain,
% 0.38/0.62      (((v2_struct_0 @ sk_A)
% 0.38/0.62        | (v1_funct_2 @ 
% 0.38/0.62           (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.38/0.62            (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)) @ sk_B) @ 
% 0.38/0.62           (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 0.38/0.62      inference('clc', [status(thm)], ['158', '159'])).
% 0.38/0.62  thf('161', plain, (~ (v2_struct_0 @ sk_A)),
% 0.38/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.62  thf('162', plain,
% 0.38/0.62      ((v1_funct_2 @ 
% 0.38/0.62        (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.38/0.62         (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)) @ sk_B) @ 
% 0.38/0.62        (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.38/0.62      inference('clc', [status(thm)], ['160', '161'])).
% 0.38/0.62  thf('163', plain,
% 0.38/0.62      (((v1_funct_2 @ 
% 0.38/0.62         (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.38/0.62          (k9_tmap_1 @ sk_A @ sk_B) @ sk_B) @ 
% 0.38/0.62         (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.38/0.62        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.38/0.62      inference('sup+', [status(thm)], ['147', '162'])).
% 0.38/0.62  thf('164', plain,
% 0.38/0.62      (((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 0.38/0.62      inference('clc', [status(thm)], ['8', '9'])).
% 0.38/0.62  thf('165', plain,
% 0.38/0.62      ((~ (v1_funct_2 @ 
% 0.38/0.62           (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.38/0.62            (k9_tmap_1 @ sk_A @ sk_B) @ sk_B) @ 
% 0.38/0.62           (u1_struct_0 @ sk_B) @ (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B))))
% 0.38/0.62         <= (~
% 0.38/0.62             ((v1_funct_2 @ 
% 0.38/0.62               (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.38/0.62                (k9_tmap_1 @ sk_A @ sk_B) @ sk_B) @ 
% 0.38/0.62               (u1_struct_0 @ sk_B) @ (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))))),
% 0.38/0.62      inference('split', [status(esa)], ['143'])).
% 0.38/0.62  thf('166', plain,
% 0.38/0.62      ((~ (v1_funct_2 @ 
% 0.38/0.62           (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.38/0.62            (k9_tmap_1 @ sk_A @ sk_B) @ sk_B) @ 
% 0.38/0.62           (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A)))
% 0.38/0.62         <= (~
% 0.38/0.62             ((v1_funct_2 @ 
% 0.38/0.62               (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.38/0.62                (k9_tmap_1 @ sk_A @ sk_B) @ sk_B) @ 
% 0.38/0.62               (u1_struct_0 @ sk_B) @ (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))))),
% 0.38/0.62      inference('sup-', [status(thm)], ['164', '165'])).
% 0.38/0.62  thf('167', plain,
% 0.38/0.62      (((v1_xboole_0 @ (u1_struct_0 @ sk_A)))
% 0.38/0.62         <= (~
% 0.38/0.62             ((v1_funct_2 @ 
% 0.38/0.62               (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.38/0.62                (k9_tmap_1 @ sk_A @ sk_B) @ sk_B) @ 
% 0.38/0.62               (u1_struct_0 @ sk_B) @ (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))))),
% 0.38/0.62      inference('sup-', [status(thm)], ['163', '166'])).
% 0.38/0.62  thf(fc2_struct_0, axiom,
% 0.38/0.62    (![A:$i]:
% 0.38/0.62     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.38/0.62       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.38/0.62  thf('168', plain,
% 0.38/0.62      (![X1 : $i]:
% 0.38/0.62         (~ (v1_xboole_0 @ (u1_struct_0 @ X1))
% 0.38/0.62          | ~ (l1_struct_0 @ X1)
% 0.38/0.62          | (v2_struct_0 @ X1))),
% 0.38/0.62      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.38/0.62  thf('169', plain,
% 0.38/0.62      ((((v2_struct_0 @ sk_A) | ~ (l1_struct_0 @ sk_A)))
% 0.38/0.62         <= (~
% 0.38/0.62             ((v1_funct_2 @ 
% 0.38/0.62               (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.38/0.62                (k9_tmap_1 @ sk_A @ sk_B) @ sk_B) @ 
% 0.38/0.62               (u1_struct_0 @ sk_B) @ (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))))),
% 0.38/0.62      inference('sup-', [status(thm)], ['167', '168'])).
% 0.38/0.62  thf('170', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.62  thf(dt_l1_pre_topc, axiom,
% 0.38/0.62    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.38/0.62  thf('171', plain, (![X0 : $i]: ((l1_struct_0 @ X0) | ~ (l1_pre_topc @ X0))),
% 0.38/0.62      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.38/0.62  thf('172', plain, ((l1_struct_0 @ sk_A)),
% 0.38/0.62      inference('sup-', [status(thm)], ['170', '171'])).
% 0.38/0.62  thf('173', plain,
% 0.38/0.62      (((v2_struct_0 @ sk_A))
% 0.38/0.62         <= (~
% 0.38/0.62             ((v1_funct_2 @ 
% 0.38/0.62               (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.38/0.62                (k9_tmap_1 @ sk_A @ sk_B) @ sk_B) @ 
% 0.38/0.62               (u1_struct_0 @ sk_B) @ (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))))),
% 0.38/0.62      inference('demod', [status(thm)], ['169', '172'])).
% 0.38/0.62  thf('174', plain, (~ (v2_struct_0 @ sk_A)),
% 0.38/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.62  thf('175', plain,
% 0.38/0.62      (((v1_funct_2 @ 
% 0.38/0.62         (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.38/0.62          (k9_tmap_1 @ sk_A @ sk_B) @ sk_B) @ 
% 0.38/0.62         (u1_struct_0 @ sk_B) @ (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B))))),
% 0.38/0.62      inference('sup-', [status(thm)], ['173', '174'])).
% 0.38/0.62  thf('176', plain,
% 0.38/0.62      ((((k9_tmap_1 @ sk_A @ sk_B) = (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 0.38/0.62        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.38/0.62      inference('simplify', [status(thm)], ['125'])).
% 0.38/0.62  thf('177', plain,
% 0.38/0.62      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.38/0.62        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.38/0.62      inference('demod', [status(thm)], ['27', '28'])).
% 0.38/0.62  thf('178', plain,
% 0.38/0.62      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.38/0.62         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 0.38/0.62          | ((u1_struct_0 @ X24) != (X22))
% 0.38/0.62          | (v1_funct_1 @ 
% 0.38/0.62             (k2_tmap_1 @ X23 @ (k6_tmap_1 @ X23 @ X22) @ 
% 0.38/0.62              (k7_tmap_1 @ X23 @ X22) @ X24))
% 0.38/0.62          | ~ (m1_pre_topc @ X24 @ X23)
% 0.38/0.62          | (v2_struct_0 @ X24)
% 0.38/0.62          | ~ (l1_pre_topc @ X23)
% 0.38/0.62          | ~ (v2_pre_topc @ X23)
% 0.38/0.62          | (v2_struct_0 @ X23))),
% 0.38/0.62      inference('cnf', [status(esa)], [t112_tmap_1])).
% 0.38/0.62  thf('179', plain,
% 0.38/0.62      (![X23 : $i, X24 : $i]:
% 0.38/0.62         ((v2_struct_0 @ X23)
% 0.38/0.62          | ~ (v2_pre_topc @ X23)
% 0.38/0.62          | ~ (l1_pre_topc @ X23)
% 0.38/0.62          | (v2_struct_0 @ X24)
% 0.38/0.62          | ~ (m1_pre_topc @ X24 @ X23)
% 0.38/0.62          | (v1_funct_1 @ 
% 0.38/0.62             (k2_tmap_1 @ X23 @ (k6_tmap_1 @ X23 @ (u1_struct_0 @ X24)) @ 
% 0.38/0.62              (k7_tmap_1 @ X23 @ (u1_struct_0 @ X24)) @ X24))
% 0.38/0.62          | ~ (m1_subset_1 @ (u1_struct_0 @ X24) @ 
% 0.38/0.62               (k1_zfmisc_1 @ (u1_struct_0 @ X23))))),
% 0.38/0.62      inference('simplify', [status(thm)], ['178'])).
% 0.38/0.62  thf('180', plain,
% 0.38/0.62      (((v1_funct_1 @ 
% 0.38/0.62         (k2_tmap_1 @ sk_A @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)) @ 
% 0.38/0.62          (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)) @ sk_B))
% 0.38/0.62        | ~ (m1_pre_topc @ sk_B @ sk_A)
% 0.38/0.62        | (v2_struct_0 @ sk_B)
% 0.38/0.62        | ~ (l1_pre_topc @ sk_A)
% 0.38/0.62        | ~ (v2_pre_topc @ sk_A)
% 0.38/0.62        | (v2_struct_0 @ sk_A))),
% 0.38/0.62      inference('sup-', [status(thm)], ['177', '179'])).
% 0.38/0.62  thf('181', plain,
% 0.38/0.62      (((k8_tmap_1 @ sk_A @ sk_B) = (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))),
% 0.38/0.62      inference('clc', [status(thm)], ['60', '61'])).
% 0.38/0.62  thf('182', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.38/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.62  thf('183', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.62  thf('184', plain, ((v2_pre_topc @ sk_A)),
% 0.38/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.62  thf('185', plain,
% 0.38/0.62      (((v1_funct_1 @ 
% 0.38/0.62         (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.38/0.62          (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)) @ sk_B))
% 0.38/0.62        | (v2_struct_0 @ sk_B)
% 0.38/0.62        | (v2_struct_0 @ sk_A))),
% 0.38/0.62      inference('demod', [status(thm)], ['180', '181', '182', '183', '184'])).
% 0.38/0.62  thf('186', plain, (~ (v2_struct_0 @ sk_B)),
% 0.38/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.62  thf('187', plain,
% 0.38/0.62      (((v2_struct_0 @ sk_A)
% 0.38/0.62        | (v1_funct_1 @ 
% 0.38/0.62           (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.38/0.62            (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)) @ sk_B)))),
% 0.38/0.62      inference('clc', [status(thm)], ['185', '186'])).
% 0.38/0.62  thf('188', plain, (~ (v2_struct_0 @ sk_A)),
% 0.38/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.62  thf('189', plain,
% 0.38/0.62      ((v1_funct_1 @ 
% 0.38/0.62        (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.38/0.62         (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)) @ sk_B))),
% 0.38/0.62      inference('clc', [status(thm)], ['187', '188'])).
% 0.38/0.62  thf('190', plain,
% 0.38/0.62      (((v1_funct_1 @ 
% 0.38/0.62         (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.38/0.62          (k9_tmap_1 @ sk_A @ sk_B) @ sk_B))
% 0.38/0.62        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.38/0.62      inference('sup+', [status(thm)], ['176', '189'])).
% 0.38/0.62  thf('191', plain,
% 0.38/0.62      ((~ (v1_funct_1 @ 
% 0.38/0.62           (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.38/0.62            (k9_tmap_1 @ sk_A @ sk_B) @ sk_B)))
% 0.38/0.62         <= (~
% 0.38/0.62             ((v1_funct_1 @ 
% 0.38/0.62               (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.38/0.62                (k9_tmap_1 @ sk_A @ sk_B) @ sk_B))))),
% 0.38/0.62      inference('split', [status(esa)], ['143'])).
% 0.38/0.62  thf('192', plain,
% 0.38/0.62      (((v1_xboole_0 @ (u1_struct_0 @ sk_A)))
% 0.38/0.62         <= (~
% 0.38/0.62             ((v1_funct_1 @ 
% 0.38/0.62               (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.38/0.62                (k9_tmap_1 @ sk_A @ sk_B) @ sk_B))))),
% 0.38/0.62      inference('sup-', [status(thm)], ['190', '191'])).
% 0.38/0.62  thf('193', plain,
% 0.38/0.62      (![X1 : $i]:
% 0.38/0.62         (~ (v1_xboole_0 @ (u1_struct_0 @ X1))
% 0.38/0.62          | ~ (l1_struct_0 @ X1)
% 0.38/0.62          | (v2_struct_0 @ X1))),
% 0.38/0.62      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.38/0.62  thf('194', plain,
% 0.38/0.62      ((((v2_struct_0 @ sk_A) | ~ (l1_struct_0 @ sk_A)))
% 0.38/0.62         <= (~
% 0.38/0.62             ((v1_funct_1 @ 
% 0.38/0.62               (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.38/0.62                (k9_tmap_1 @ sk_A @ sk_B) @ sk_B))))),
% 0.38/0.62      inference('sup-', [status(thm)], ['192', '193'])).
% 0.38/0.62  thf('195', plain, ((l1_struct_0 @ sk_A)),
% 0.38/0.62      inference('sup-', [status(thm)], ['170', '171'])).
% 0.38/0.62  thf('196', plain,
% 0.38/0.62      (((v2_struct_0 @ sk_A))
% 0.38/0.62         <= (~
% 0.38/0.62             ((v1_funct_1 @ 
% 0.38/0.62               (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.38/0.62                (k9_tmap_1 @ sk_A @ sk_B) @ sk_B))))),
% 0.38/0.62      inference('demod', [status(thm)], ['194', '195'])).
% 0.38/0.62  thf('197', plain, (~ (v2_struct_0 @ sk_A)),
% 0.38/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.62  thf('198', plain,
% 0.38/0.62      (((v1_funct_1 @ 
% 0.38/0.62         (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.38/0.62          (k9_tmap_1 @ sk_A @ sk_B) @ sk_B)))),
% 0.38/0.62      inference('sup-', [status(thm)], ['196', '197'])).
% 0.38/0.62  thf('199', plain,
% 0.38/0.62      ((((k9_tmap_1 @ sk_A @ sk_B) = (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 0.38/0.62        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.38/0.62      inference('simplify', [status(thm)], ['125'])).
% 0.38/0.62  thf('200', plain,
% 0.38/0.62      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.38/0.62        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.38/0.62      inference('demod', [status(thm)], ['27', '28'])).
% 0.38/0.62  thf('201', plain,
% 0.38/0.62      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.38/0.62         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 0.38/0.62          | ((u1_struct_0 @ X24) != (X22))
% 0.38/0.62          | (v5_pre_topc @ 
% 0.38/0.62             (k2_tmap_1 @ X23 @ (k6_tmap_1 @ X23 @ X22) @ 
% 0.38/0.62              (k7_tmap_1 @ X23 @ X22) @ X24) @ 
% 0.38/0.62             X24 @ (k6_tmap_1 @ X23 @ X22))
% 0.38/0.62          | ~ (m1_pre_topc @ X24 @ X23)
% 0.38/0.62          | (v2_struct_0 @ X24)
% 0.38/0.62          | ~ (l1_pre_topc @ X23)
% 0.38/0.62          | ~ (v2_pre_topc @ X23)
% 0.38/0.62          | (v2_struct_0 @ X23))),
% 0.38/0.62      inference('cnf', [status(esa)], [t112_tmap_1])).
% 0.38/0.62  thf('202', plain,
% 0.38/0.62      (![X23 : $i, X24 : $i]:
% 0.38/0.62         ((v2_struct_0 @ X23)
% 0.38/0.62          | ~ (v2_pre_topc @ X23)
% 0.38/0.62          | ~ (l1_pre_topc @ X23)
% 0.38/0.62          | (v2_struct_0 @ X24)
% 0.38/0.62          | ~ (m1_pre_topc @ X24 @ X23)
% 0.38/0.62          | (v5_pre_topc @ 
% 0.38/0.62             (k2_tmap_1 @ X23 @ (k6_tmap_1 @ X23 @ (u1_struct_0 @ X24)) @ 
% 0.38/0.62              (k7_tmap_1 @ X23 @ (u1_struct_0 @ X24)) @ X24) @ 
% 0.38/0.62             X24 @ (k6_tmap_1 @ X23 @ (u1_struct_0 @ X24)))
% 0.38/0.62          | ~ (m1_subset_1 @ (u1_struct_0 @ X24) @ 
% 0.38/0.62               (k1_zfmisc_1 @ (u1_struct_0 @ X23))))),
% 0.38/0.62      inference('simplify', [status(thm)], ['201'])).
% 0.38/0.62  thf('203', plain,
% 0.38/0.62      (((v5_pre_topc @ 
% 0.38/0.62         (k2_tmap_1 @ sk_A @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)) @ 
% 0.38/0.62          (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)) @ sk_B) @ 
% 0.38/0.62         sk_B @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 0.38/0.62        | ~ (m1_pre_topc @ sk_B @ sk_A)
% 0.38/0.62        | (v2_struct_0 @ sk_B)
% 0.38/0.62        | ~ (l1_pre_topc @ sk_A)
% 0.38/0.62        | ~ (v2_pre_topc @ sk_A)
% 0.38/0.62        | (v2_struct_0 @ sk_A))),
% 0.38/0.62      inference('sup-', [status(thm)], ['200', '202'])).
% 0.38/0.62  thf('204', plain,
% 0.38/0.62      (((k8_tmap_1 @ sk_A @ sk_B) = (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))),
% 0.38/0.62      inference('clc', [status(thm)], ['60', '61'])).
% 0.38/0.62  thf('205', plain,
% 0.38/0.62      (((k8_tmap_1 @ sk_A @ sk_B) = (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))),
% 0.38/0.62      inference('clc', [status(thm)], ['60', '61'])).
% 0.38/0.62  thf('206', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.38/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.62  thf('207', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.62  thf('208', plain, ((v2_pre_topc @ sk_A)),
% 0.38/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.62  thf('209', plain,
% 0.38/0.62      (((v5_pre_topc @ 
% 0.38/0.62         (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.38/0.62          (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)) @ sk_B) @ 
% 0.38/0.62         sk_B @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.38/0.62        | (v2_struct_0 @ sk_B)
% 0.38/0.62        | (v2_struct_0 @ sk_A))),
% 0.38/0.62      inference('demod', [status(thm)],
% 0.38/0.62                ['203', '204', '205', '206', '207', '208'])).
% 0.38/0.62  thf('210', plain, (~ (v2_struct_0 @ sk_B)),
% 0.38/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.62  thf('211', plain,
% 0.38/0.62      (((v2_struct_0 @ sk_A)
% 0.38/0.62        | (v5_pre_topc @ 
% 0.38/0.62           (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.38/0.62            (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)) @ sk_B) @ 
% 0.38/0.62           sk_B @ (k8_tmap_1 @ sk_A @ sk_B)))),
% 0.38/0.62      inference('clc', [status(thm)], ['209', '210'])).
% 0.38/0.62  thf('212', plain, (~ (v2_struct_0 @ sk_A)),
% 0.38/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.62  thf('213', plain,
% 0.38/0.62      ((v5_pre_topc @ 
% 0.38/0.62        (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.38/0.62         (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)) @ sk_B) @ 
% 0.38/0.62        sk_B @ (k8_tmap_1 @ sk_A @ sk_B))),
% 0.38/0.62      inference('clc', [status(thm)], ['211', '212'])).
% 0.38/0.62  thf('214', plain,
% 0.38/0.62      (((v5_pre_topc @ 
% 0.38/0.62         (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.38/0.62          (k9_tmap_1 @ sk_A @ sk_B) @ sk_B) @ 
% 0.38/0.62         sk_B @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.38/0.62        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.38/0.62      inference('sup+', [status(thm)], ['199', '213'])).
% 0.38/0.62  thf('215', plain,
% 0.38/0.62      ((~ (v5_pre_topc @ 
% 0.38/0.62           (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.38/0.62            (k9_tmap_1 @ sk_A @ sk_B) @ sk_B) @ 
% 0.38/0.62           sk_B @ (k8_tmap_1 @ sk_A @ sk_B)))
% 0.38/0.62         <= (~
% 0.38/0.62             ((v5_pre_topc @ 
% 0.38/0.62               (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.38/0.62                (k9_tmap_1 @ sk_A @ sk_B) @ sk_B) @ 
% 0.38/0.62               sk_B @ (k8_tmap_1 @ sk_A @ sk_B))))),
% 0.38/0.62      inference('split', [status(esa)], ['143'])).
% 0.38/0.62  thf('216', plain,
% 0.38/0.62      (((v1_xboole_0 @ (u1_struct_0 @ sk_A)))
% 0.38/0.62         <= (~
% 0.38/0.62             ((v5_pre_topc @ 
% 0.38/0.62               (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.38/0.62                (k9_tmap_1 @ sk_A @ sk_B) @ sk_B) @ 
% 0.38/0.62               sk_B @ (k8_tmap_1 @ sk_A @ sk_B))))),
% 0.38/0.62      inference('sup-', [status(thm)], ['214', '215'])).
% 0.38/0.62  thf('217', plain,
% 0.38/0.62      (![X1 : $i]:
% 0.38/0.62         (~ (v1_xboole_0 @ (u1_struct_0 @ X1))
% 0.38/0.62          | ~ (l1_struct_0 @ X1)
% 0.38/0.62          | (v2_struct_0 @ X1))),
% 0.38/0.62      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.38/0.62  thf('218', plain,
% 0.38/0.62      ((((v2_struct_0 @ sk_A) | ~ (l1_struct_0 @ sk_A)))
% 0.38/0.62         <= (~
% 0.38/0.62             ((v5_pre_topc @ 
% 0.38/0.62               (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.38/0.62                (k9_tmap_1 @ sk_A @ sk_B) @ sk_B) @ 
% 0.38/0.62               sk_B @ (k8_tmap_1 @ sk_A @ sk_B))))),
% 0.38/0.62      inference('sup-', [status(thm)], ['216', '217'])).
% 0.38/0.62  thf('219', plain, ((l1_struct_0 @ sk_A)),
% 0.38/0.62      inference('sup-', [status(thm)], ['170', '171'])).
% 0.38/0.62  thf('220', plain,
% 0.38/0.62      (((v2_struct_0 @ sk_A))
% 0.38/0.62         <= (~
% 0.38/0.62             ((v5_pre_topc @ 
% 0.38/0.62               (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.38/0.62                (k9_tmap_1 @ sk_A @ sk_B) @ sk_B) @ 
% 0.38/0.62               sk_B @ (k8_tmap_1 @ sk_A @ sk_B))))),
% 0.38/0.62      inference('demod', [status(thm)], ['218', '219'])).
% 0.38/0.62  thf('221', plain, (~ (v2_struct_0 @ sk_A)),
% 0.38/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.62  thf('222', plain,
% 0.38/0.62      (((v5_pre_topc @ 
% 0.38/0.62         (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.38/0.62          (k9_tmap_1 @ sk_A @ sk_B) @ sk_B) @ 
% 0.38/0.62         sk_B @ (k8_tmap_1 @ sk_A @ sk_B)))),
% 0.38/0.62      inference('sup-', [status(thm)], ['220', '221'])).
% 0.38/0.62  thf('223', plain,
% 0.38/0.62      (~
% 0.38/0.62       ((m1_subset_1 @ 
% 0.38/0.62         (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.38/0.62          (k9_tmap_1 @ sk_A @ sk_B) @ sk_B) @ 
% 0.38/0.62         (k1_zfmisc_1 @ 
% 0.38/0.62          (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ 
% 0.38/0.62           (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))))) | 
% 0.38/0.62       ~
% 0.38/0.62       ((v5_pre_topc @ 
% 0.38/0.62         (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.38/0.62          (k9_tmap_1 @ sk_A @ sk_B) @ sk_B) @ 
% 0.38/0.62         sk_B @ (k8_tmap_1 @ sk_A @ sk_B))) | 
% 0.38/0.62       ~
% 0.38/0.62       ((v1_funct_1 @ 
% 0.38/0.62         (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.38/0.62          (k9_tmap_1 @ sk_A @ sk_B) @ sk_B))) | 
% 0.38/0.62       ~
% 0.38/0.62       ((v1_funct_2 @ 
% 0.38/0.62         (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.38/0.62          (k9_tmap_1 @ sk_A @ sk_B) @ sk_B) @ 
% 0.38/0.62         (u1_struct_0 @ sk_B) @ (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B))))),
% 0.38/0.62      inference('split', [status(esa)], ['143'])).
% 0.38/0.62  thf('224', plain,
% 0.38/0.62      (~
% 0.38/0.62       ((m1_subset_1 @ 
% 0.38/0.62         (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.38/0.62          (k9_tmap_1 @ sk_A @ sk_B) @ sk_B) @ 
% 0.38/0.62         (k1_zfmisc_1 @ 
% 0.38/0.62          (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ 
% 0.38/0.62           (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B))))))),
% 0.38/0.62      inference('sat_resolution*', [status(thm)], ['175', '198', '222', '223'])).
% 0.38/0.62  thf('225', plain,
% 0.38/0.62      (~ (m1_subset_1 @ 
% 0.38/0.62          (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.38/0.62           (k9_tmap_1 @ sk_A @ sk_B) @ sk_B) @ 
% 0.38/0.62          (k1_zfmisc_1 @ 
% 0.38/0.62           (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.38/0.62      inference('simpl_trail', [status(thm)], ['146', '224'])).
% 0.38/0.62  thf('226', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.38/0.62      inference('clc', [status(thm)], ['142', '225'])).
% 0.38/0.62  thf('227', plain,
% 0.38/0.62      (![X1 : $i]:
% 0.38/0.62         (~ (v1_xboole_0 @ (u1_struct_0 @ X1))
% 0.38/0.62          | ~ (l1_struct_0 @ X1)
% 0.38/0.62          | (v2_struct_0 @ X1))),
% 0.38/0.62      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.38/0.62  thf('228', plain, (((v2_struct_0 @ sk_A) | ~ (l1_struct_0 @ sk_A))),
% 0.38/0.62      inference('sup-', [status(thm)], ['226', '227'])).
% 0.38/0.62  thf('229', plain, ((l1_struct_0 @ sk_A)),
% 0.38/0.62      inference('sup-', [status(thm)], ['170', '171'])).
% 0.38/0.62  thf('230', plain, ((v2_struct_0 @ sk_A)),
% 0.38/0.62      inference('demod', [status(thm)], ['228', '229'])).
% 0.38/0.62  thf('231', plain, ($false), inference('demod', [status(thm)], ['0', '230'])).
% 0.38/0.62  
% 0.38/0.62  % SZS output end Refutation
% 0.38/0.62  
% 0.38/0.63  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
