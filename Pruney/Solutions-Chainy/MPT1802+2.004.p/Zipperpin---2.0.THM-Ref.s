%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.aAnWKnuso6

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:10:58 EST 2020

% Result     : Theorem 3.04s
% Output     : Refutation 3.14s
% Verified   : 
% Statistics : Number of formulae       :  217 (1609 expanded)
%              Number of leaves         :   43 ( 483 expanded)
%              Depth                    :   20
%              Number of atoms          : 2061 (34648 expanded)
%              Number of equality atoms :   39 ( 210 expanded)
%              Maximal formula depth    :   23 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k7_tmap_1_type,type,(
    k7_tmap_1: $i > $i > $i )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k6_tmap_1_type,type,(
    k6_tmap_1: $i > $i > $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(k9_tmap_1_type,type,(
    k9_tmap_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k5_tmap_1_type,type,(
    k5_tmap_1: $i > $i > $i )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(sk_D_2_type,type,(
    sk_D_2: $i )).

thf(k2_tmap_1_type,type,(
    k2_tmap_1: $i > $i > $i > $i > $i )).

thf(k8_tmap_1_type,type,(
    k8_tmap_1: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r1_tsep_1_type,type,(
    r1_tsep_1: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r1_funct_2_type,type,(
    r1_funct_2: $i > $i > $i > $i > $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(r1_tmap_1_type,type,(
    r1_tmap_1: $i > $i > $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(t118_tmap_1,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( m1_pre_topc @ B @ A ) )
         => ! [C: $i] :
              ( ( ~ ( v2_struct_0 @ C )
                & ( m1_pre_topc @ C @ A ) )
             => ( ( r1_tsep_1 @ B @ C )
               => ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( u1_struct_0 @ C ) )
                   => ( r1_tmap_1 @ C @ ( k8_tmap_1 @ A @ B ) @ ( k2_tmap_1 @ A @ ( k8_tmap_1 @ A @ B ) @ ( k9_tmap_1 @ A @ B ) @ C ) @ D ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( ~ ( v2_struct_0 @ B )
              & ( m1_pre_topc @ B @ A ) )
           => ! [C: $i] :
                ( ( ~ ( v2_struct_0 @ C )
                  & ( m1_pre_topc @ C @ A ) )
               => ( ( r1_tsep_1 @ B @ C )
                 => ! [D: $i] :
                      ( ( m1_subset_1 @ D @ ( u1_struct_0 @ C ) )
                     => ( r1_tmap_1 @ C @ ( k8_tmap_1 @ A @ B ) @ ( k2_tmap_1 @ A @ ( k8_tmap_1 @ A @ B ) @ ( k9_tmap_1 @ A @ B ) @ C ) @ D ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t118_tmap_1])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
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
    ! [X34: $i,X35: $i] :
      ( ~ ( m1_pre_topc @ X34 @ X35 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X34 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X35 ) ) )
      | ~ ( l1_pre_topc @ X35 ) ) ),
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
    ! [X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) )
      | ( ( u1_struct_0 @ ( k6_tmap_1 @ X29 @ X28 ) )
        = ( u1_struct_0 @ X29 ) )
      | ~ ( l1_pre_topc @ X29 )
      | ~ ( v2_pre_topc @ X29 )
      | ( v2_struct_0 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t104_tmap_1])).

thf('7',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
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
    | ( ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['7','8','9'])).

thf('11',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['10','11'])).

thf('13',plain,(
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

thf('14',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_pre_topc @ X12 @ X13 )
      | ( X14
       != ( k8_tmap_1 @ X13 @ X12 ) )
      | ( X15
       != ( u1_struct_0 @ X12 ) )
      | ( X14
        = ( k6_tmap_1 @ X13 @ X15 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ~ ( l1_pre_topc @ X14 )
      | ~ ( v2_pre_topc @ X14 )
      | ~ ( v1_pre_topc @ X14 )
      | ~ ( l1_pre_topc @ X13 )
      | ~ ( v2_pre_topc @ X13 )
      | ( v2_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d11_tmap_1])).

thf('15',plain,(
    ! [X12: $i,X13: $i] :
      ( ( v2_struct_0 @ X13 )
      | ~ ( v2_pre_topc @ X13 )
      | ~ ( l1_pre_topc @ X13 )
      | ~ ( v1_pre_topc @ ( k8_tmap_1 @ X13 @ X12 ) )
      | ~ ( v2_pre_topc @ ( k8_tmap_1 @ X13 @ X12 ) )
      | ~ ( l1_pre_topc @ ( k8_tmap_1 @ X13 @ X12 ) )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X12 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ( ( k8_tmap_1 @ X13 @ X12 )
        = ( k6_tmap_1 @ X13 @ ( u1_struct_0 @ X12 ) ) )
      | ~ ( m1_pre_topc @ X12 @ X13 ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,
    ( ~ ( m1_pre_topc @ sk_B @ sk_A )
    | ( ( k8_tmap_1 @ sk_A @ sk_B )
      = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
    | ~ ( l1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( v2_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( v1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['13','15'])).

thf('17',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
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

thf('19',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( l1_pre_topc @ X24 )
      | ~ ( v2_pre_topc @ X24 )
      | ( v2_struct_0 @ X24 )
      | ~ ( m1_pre_topc @ X25 @ X24 )
      | ( l1_pre_topc @ ( k8_tmap_1 @ X24 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k8_tmap_1])).

thf('20',plain,
    ( ( l1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ( l1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['20','21','22'])).

thf('24',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    l1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['23','24'])).

thf('26',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( l1_pre_topc @ X24 )
      | ~ ( v2_pre_topc @ X24 )
      | ( v2_struct_0 @ X24 )
      | ~ ( m1_pre_topc @ X25 @ X24 )
      | ( v2_pre_topc @ ( k8_tmap_1 @ X24 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k8_tmap_1])).

thf('28',plain,
    ( ( v2_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
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
    ( ( v2_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['28','29','30'])).

thf('32',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    v2_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['31','32'])).

thf('34',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( l1_pre_topc @ X24 )
      | ~ ( v2_pre_topc @ X24 )
      | ( v2_struct_0 @ X24 )
      | ~ ( m1_pre_topc @ X25 @ X24 )
      | ( v1_pre_topc @ ( k8_tmap_1 @ X24 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k8_tmap_1])).

thf('36',plain,
    ( ( v1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
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
    ( ( v1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['36','37','38'])).

thf('40',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    v1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['39','40'])).

thf('42',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,
    ( ( ( k8_tmap_1 @ sk_A @ sk_B )
      = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['16','17','25','33','41','42','43'])).

thf('45',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( ( k8_tmap_1 @ sk_A @ sk_B )
    = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['44','45'])).

thf('47',plain,
    ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['12','46'])).

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

thf('48',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_pre_topc @ X16 @ X17 )
      | ( X18
       != ( k9_tmap_1 @ X17 @ X16 ) )
      | ( X19
       != ( u1_struct_0 @ X16 ) )
      | ( r1_funct_2 @ ( u1_struct_0 @ X17 ) @ ( u1_struct_0 @ ( k8_tmap_1 @ X17 @ X16 ) ) @ ( u1_struct_0 @ X17 ) @ ( u1_struct_0 @ ( k6_tmap_1 @ X17 @ X19 ) ) @ X18 @ ( k7_tmap_1 @ X17 @ X19 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X17 ) @ ( u1_struct_0 @ ( k8_tmap_1 @ X17 @ X16 ) ) ) ) )
      | ~ ( v1_funct_2 @ X18 @ ( u1_struct_0 @ X17 ) @ ( u1_struct_0 @ ( k8_tmap_1 @ X17 @ X16 ) ) )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( l1_pre_topc @ X17 )
      | ~ ( v2_pre_topc @ X17 )
      | ( v2_struct_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d12_tmap_1])).

thf('49',plain,(
    ! [X16: $i,X17: $i] :
      ( ( v2_struct_0 @ X17 )
      | ~ ( v2_pre_topc @ X17 )
      | ~ ( l1_pre_topc @ X17 )
      | ~ ( v1_funct_1 @ ( k9_tmap_1 @ X17 @ X16 ) )
      | ~ ( v1_funct_2 @ ( k9_tmap_1 @ X17 @ X16 ) @ ( u1_struct_0 @ X17 ) @ ( u1_struct_0 @ ( k8_tmap_1 @ X17 @ X16 ) ) )
      | ~ ( m1_subset_1 @ ( k9_tmap_1 @ X17 @ X16 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X17 ) @ ( u1_struct_0 @ ( k8_tmap_1 @ X17 @ X16 ) ) ) ) )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X16 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ( r1_funct_2 @ ( u1_struct_0 @ X17 ) @ ( u1_struct_0 @ ( k8_tmap_1 @ X17 @ X16 ) ) @ ( u1_struct_0 @ X17 ) @ ( u1_struct_0 @ ( k6_tmap_1 @ X17 @ ( u1_struct_0 @ X16 ) ) ) @ ( k9_tmap_1 @ X17 @ X16 ) @ ( k7_tmap_1 @ X17 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( m1_pre_topc @ X16 @ X17 ) ) ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,
    ( ~ ( m1_subset_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ~ ( m1_pre_topc @ sk_B @ sk_A )
    | ( r1_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
    | ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( v1_funct_2 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) )
    | ~ ( v1_funct_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['47','49'])).

thf('51',plain,(
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

thf('52',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( l1_pre_topc @ X26 )
      | ~ ( v2_pre_topc @ X26 )
      | ( v2_struct_0 @ X26 )
      | ~ ( m1_pre_topc @ X27 @ X26 )
      | ( m1_subset_1 @ ( k9_tmap_1 @ X26 @ X27 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X26 ) @ ( u1_struct_0 @ ( k8_tmap_1 @ X26 @ X27 ) ) ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k9_tmap_1])).

thf('53',plain,
    ( ( m1_subset_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,
    ( ( m1_subset_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['53','54','55'])).

thf('57',plain,
    ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['12','46'])).

thf('58',plain,
    ( ( m1_subset_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    m1_subset_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['58','59'])).

thf('61',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,
    ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['12','46'])).

thf('63',plain,
    ( ( k8_tmap_1 @ sk_A @ sk_B )
    = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['44','45'])).

thf('64',plain,
    ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['12','46'])).

thf('65',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('66',plain,
    ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['12','46'])).

thf('67',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( l1_pre_topc @ X26 )
      | ~ ( v2_pre_topc @ X26 )
      | ( v2_struct_0 @ X26 )
      | ~ ( m1_pre_topc @ X27 @ X26 )
      | ( v1_funct_2 @ ( k9_tmap_1 @ X26 @ X27 ) @ ( u1_struct_0 @ X26 ) @ ( u1_struct_0 @ ( k8_tmap_1 @ X26 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k9_tmap_1])).

thf('69',plain,
    ( ( v1_funct_2 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,
    ( ( v1_funct_2 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['69','70','71'])).

thf('73',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    v1_funct_2 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['72','73'])).

thf('75',plain,
    ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['12','46'])).

thf('76',plain,(
    v1_funct_2 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['74','75'])).

thf('77',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( l1_pre_topc @ X26 )
      | ~ ( v2_pre_topc @ X26 )
      | ( v2_struct_0 @ X26 )
      | ~ ( m1_pre_topc @ X27 @ X26 )
      | ( v1_funct_1 @ ( k9_tmap_1 @ X26 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k9_tmap_1])).

thf('79',plain,
    ( ( v1_funct_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,
    ( ( v1_funct_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['79','80','81'])).

thf('83',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    v1_funct_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['82','83'])).

thf('85',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,
    ( ( r1_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['50','60','61','62','63','64','65','66','76','84','85','86'])).

thf('88',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    r1_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['87','88'])).

thf('90',plain,(
    m1_subset_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['58','59'])).

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

thf('91',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) )
      | ~ ( v1_funct_2 @ X6 @ X7 @ X8 )
      | ~ ( v1_funct_1 @ X6 )
      | ( v1_xboole_0 @ X9 )
      | ( v1_xboole_0 @ X8 )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_funct_2 @ X10 @ X11 @ X9 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X9 ) ) )
      | ( X6 = X10 )
      | ~ ( r1_funct_2 @ X7 @ X8 @ X11 @ X9 @ X6 @ X10 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_funct_2])).

thf('92',plain,(
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
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,(
    v1_funct_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['82','83'])).

thf('94',plain,(
    v1_funct_2 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['74','75'])).

thf('95',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ X2 @ X1 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ X0 )
      | ( ( k9_tmap_1 @ sk_A @ sk_B )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_2 @ X0 @ X2 @ X1 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ X1 ) ) ),
    inference(demod,[status(thm)],['92','93','94'])).

thf('96',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_funct_1 @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
    | ~ ( v1_funct_2 @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( m1_subset_1 @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ( ( k9_tmap_1 @ sk_A @ sk_B )
      = ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['89','95'])).

thf('97',plain,(
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

thf('98',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( l1_pre_topc @ X22 )
      | ~ ( v2_pre_topc @ X22 )
      | ( v2_struct_0 @ X22 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ( v1_funct_1 @ ( k7_tmap_1 @ X22 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_tmap_1])).

thf('99',plain,
    ( ( v1_funct_1 @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,
    ( ( v1_funct_1 @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['99','100','101'])).

thf('103',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,(
    v1_funct_1 @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['102','103'])).

thf('105',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('106',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( l1_pre_topc @ X22 )
      | ~ ( v2_pre_topc @ X22 )
      | ( v2_struct_0 @ X22 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ( v1_funct_2 @ ( k7_tmap_1 @ X22 @ X23 ) @ ( u1_struct_0 @ X22 ) @ ( u1_struct_0 @ ( k6_tmap_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_tmap_1])).

thf('107',plain,
    ( ( v1_funct_2 @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['105','106'])).

thf('108',plain,
    ( ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['10','11'])).

thf('109',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,
    ( ( v1_funct_2 @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['107','108','109','110'])).

thf('112',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,(
    v1_funct_2 @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['111','112'])).

thf('114',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('115',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( l1_pre_topc @ X22 )
      | ~ ( v2_pre_topc @ X22 )
      | ( v2_struct_0 @ X22 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ( m1_subset_1 @ ( k7_tmap_1 @ X22 @ X23 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X22 ) @ ( u1_struct_0 @ ( k6_tmap_1 @ X22 @ X23 ) ) ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_tmap_1])).

thf('116',plain,
    ( ( m1_subset_1 @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ) ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['114','115'])).

thf('117',plain,
    ( ( k8_tmap_1 @ sk_A @ sk_B )
    = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['44','45'])).

thf('118',plain,
    ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['12','46'])).

thf('119',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('121',plain,
    ( ( m1_subset_1 @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['116','117','118','119','120'])).

thf('122',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,(
    m1_subset_1 @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['121','122'])).

thf('124',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( ( k9_tmap_1 @ sk_A @ sk_B )
      = ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['96','104','113','123'])).

thf('125',plain,
    ( ( ( k9_tmap_1 @ sk_A @ sk_B )
      = ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['124'])).

thf('126',plain,(
    m1_subset_1 @ sk_D_2 @ ( u1_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,(
    r1_tsep_1 @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ! [B: $i] :
          ( ( l1_struct_0 @ B )
         => ( ( r1_tsep_1 @ A @ B )
          <=> ( r1_xboole_0 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) )).

thf('128',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( l1_struct_0 @ X20 )
      | ~ ( r1_tsep_1 @ X21 @ X20 )
      | ( r1_xboole_0 @ ( u1_struct_0 @ X21 ) @ ( u1_struct_0 @ X20 ) )
      | ~ ( l1_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d3_tsep_1])).

thf('129',plain,
    ( ~ ( l1_struct_0 @ sk_B )
    | ( r1_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) )
    | ~ ( l1_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['127','128'])).

thf('130',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('131',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_pre_topc @ X3 @ X4 )
      | ( l1_pre_topc @ X3 )
      | ~ ( l1_pre_topc @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('132',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['130','131'])).

thf('133',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('134',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['132','133'])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('135',plain,(
    ! [X2: $i] :
      ( ( l1_struct_0 @ X2 )
      | ~ ( l1_pre_topc @ X2 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('136',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['134','135'])).

thf('137',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('138',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_pre_topc @ X3 @ X4 )
      | ( l1_pre_topc @ X3 )
      | ~ ( l1_pre_topc @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('139',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_C ) ),
    inference('sup-',[status(thm)],['137','138'])).

thf('140',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('141',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['139','140'])).

thf('142',plain,(
    ! [X2: $i] :
      ( ( l1_struct_0 @ X2 )
      | ~ ( l1_pre_topc @ X2 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('143',plain,(
    l1_struct_0 @ sk_C ),
    inference('sup-',[status(thm)],['141','142'])).

thf('144',plain,(
    r1_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['129','136','143'])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('145',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('146',plain,(
    r1_xboole_0 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['144','145'])).

thf('147',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf(t109_tmap_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( ~ ( v2_struct_0 @ C )
                & ( m1_pre_topc @ C @ A ) )
             => ( ( r1_xboole_0 @ ( u1_struct_0 @ C ) @ B )
               => ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( u1_struct_0 @ C ) )
                   => ( r1_tmap_1 @ C @ ( k6_tmap_1 @ A @ B ) @ ( k2_tmap_1 @ A @ ( k6_tmap_1 @ A @ B ) @ ( k7_tmap_1 @ A @ B ) @ C ) @ D ) ) ) ) ) ) )).

thf('148',plain,(
    ! [X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X31 ) ) )
      | ~ ( r1_xboole_0 @ ( u1_struct_0 @ X32 ) @ X30 )
      | ~ ( m1_subset_1 @ X33 @ ( u1_struct_0 @ X32 ) )
      | ( r1_tmap_1 @ X32 @ ( k6_tmap_1 @ X31 @ X30 ) @ ( k2_tmap_1 @ X31 @ ( k6_tmap_1 @ X31 @ X30 ) @ ( k7_tmap_1 @ X31 @ X30 ) @ X32 ) @ X33 )
      | ~ ( m1_pre_topc @ X32 @ X31 )
      | ( v2_struct_0 @ X32 )
      | ~ ( l1_pre_topc @ X31 )
      | ~ ( v2_pre_topc @ X31 )
      | ( v2_struct_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t109_tmap_1])).

thf('149',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( r1_tmap_1 @ X0 @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) @ ( k2_tmap_1 @ sk_A @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) @ X0 ) @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( r1_xboole_0 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['147','148'])).

thf('150',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('151',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('152',plain,
    ( ( k8_tmap_1 @ sk_A @ sk_B )
    = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['44','45'])).

thf('153',plain,
    ( ( k8_tmap_1 @ sk_A @ sk_B )
    = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['44','45'])).

thf('154',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( r1_tmap_1 @ X0 @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) @ X0 ) @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( r1_xboole_0 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['149','150','151','152','153'])).

thf('155',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_C ) )
      | ( r1_tmap_1 @ sk_C @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) @ sk_C ) @ X0 )
      | ~ ( m1_pre_topc @ sk_C @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['146','154'])).

thf('156',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('157',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_C ) )
      | ( r1_tmap_1 @ sk_C @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) @ sk_C ) @ X0 )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['155','156'])).

thf('158',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( r1_tmap_1 @ sk_C @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) @ sk_C ) @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['126','157'])).

thf('159',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('160',plain,
    ( ( r1_tmap_1 @ sk_C @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) @ sk_C ) @ sk_D_2 )
    | ( v2_struct_0 @ sk_C ) ),
    inference(clc,[status(thm)],['158','159'])).

thf('161',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('162',plain,(
    r1_tmap_1 @ sk_C @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) @ sk_C ) @ sk_D_2 ),
    inference(clc,[status(thm)],['160','161'])).

thf('163',plain,
    ( ( r1_tmap_1 @ sk_C @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_C ) @ sk_D_2 )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['125','162'])).

thf('164',plain,(
    ~ ( r1_tmap_1 @ sk_C @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_C ) @ sk_D_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('165',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['163','164'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('166',plain,(
    ! [X5: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X5 ) )
      | ~ ( l1_struct_0 @ X5 )
      | ( v2_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('167',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['165','166'])).

thf('168',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('169',plain,(
    ! [X2: $i] :
      ( ( l1_struct_0 @ X2 )
      | ~ ( l1_pre_topc @ X2 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('170',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['168','169'])).

thf('171',plain,(
    v2_struct_0 @ sk_A ),
    inference(demod,[status(thm)],['167','170'])).

thf('172',plain,(
    $false ),
    inference(demod,[status(thm)],['0','171'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.aAnWKnuso6
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:30:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 3.04/3.31  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 3.04/3.31  % Solved by: fo/fo7.sh
% 3.04/3.31  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 3.04/3.31  % done 1501 iterations in 2.844s
% 3.04/3.31  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 3.04/3.31  % SZS output start Refutation
% 3.04/3.31  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 3.04/3.31  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 3.04/3.31  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 3.04/3.31  thf(k7_tmap_1_type, type, k7_tmap_1: $i > $i > $i).
% 3.04/3.31  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 3.04/3.31  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 3.04/3.31  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 3.04/3.31  thf(k6_tmap_1_type, type, k6_tmap_1: $i > $i > $i).
% 3.04/3.31  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 3.04/3.31  thf(k9_tmap_1_type, type, k9_tmap_1: $i > $i > $i).
% 3.04/3.31  thf(sk_A_type, type, sk_A: $i).
% 3.04/3.31  thf(k5_tmap_1_type, type, k5_tmap_1: $i > $i > $i).
% 3.04/3.31  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 3.04/3.31  thf(sk_D_2_type, type, sk_D_2: $i).
% 3.04/3.31  thf(k2_tmap_1_type, type, k2_tmap_1: $i > $i > $i > $i > $i).
% 3.04/3.31  thf(k8_tmap_1_type, type, k8_tmap_1: $i > $i > $i).
% 3.04/3.31  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 3.04/3.31  thf(sk_C_type, type, sk_C: $i).
% 3.04/3.31  thf(r1_tsep_1_type, type, r1_tsep_1: $i > $i > $o).
% 3.04/3.31  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 3.04/3.31  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 3.04/3.31  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 3.04/3.31  thf(sk_B_type, type, sk_B: $i).
% 3.04/3.31  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 3.04/3.31  thf(r1_funct_2_type, type, r1_funct_2: $i > $i > $i > $i > $i > $i > $o).
% 3.04/3.31  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 3.04/3.31  thf(r1_tmap_1_type, type, r1_tmap_1: $i > $i > $i > $i > $o).
% 3.04/3.31  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 3.04/3.31  thf(t118_tmap_1, conjecture,
% 3.04/3.31    (![A:$i]:
% 3.04/3.31     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 3.04/3.31       ( ![B:$i]:
% 3.04/3.31         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 3.04/3.31           ( ![C:$i]:
% 3.04/3.31             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 3.04/3.31               ( ( r1_tsep_1 @ B @ C ) =>
% 3.04/3.31                 ( ![D:$i]:
% 3.04/3.31                   ( ( m1_subset_1 @ D @ ( u1_struct_0 @ C ) ) =>
% 3.04/3.31                     ( r1_tmap_1 @
% 3.04/3.31                       C @ ( k8_tmap_1 @ A @ B ) @ 
% 3.04/3.31                       ( k2_tmap_1 @
% 3.04/3.31                         A @ ( k8_tmap_1 @ A @ B ) @ ( k9_tmap_1 @ A @ B ) @ C ) @ 
% 3.04/3.31                       D ) ) ) ) ) ) ) ) ))).
% 3.04/3.31  thf(zf_stmt_0, negated_conjecture,
% 3.04/3.31    (~( ![A:$i]:
% 3.04/3.31        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 3.04/3.31            ( l1_pre_topc @ A ) ) =>
% 3.04/3.31          ( ![B:$i]:
% 3.04/3.31            ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 3.04/3.31              ( ![C:$i]:
% 3.04/3.31                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 3.04/3.31                  ( ( r1_tsep_1 @ B @ C ) =>
% 3.04/3.31                    ( ![D:$i]:
% 3.04/3.31                      ( ( m1_subset_1 @ D @ ( u1_struct_0 @ C ) ) =>
% 3.04/3.31                        ( r1_tmap_1 @
% 3.04/3.31                          C @ ( k8_tmap_1 @ A @ B ) @ 
% 3.04/3.31                          ( k2_tmap_1 @
% 3.04/3.31                            A @ ( k8_tmap_1 @ A @ B ) @ 
% 3.04/3.31                            ( k9_tmap_1 @ A @ B ) @ C ) @ 
% 3.04/3.31                          D ) ) ) ) ) ) ) ) ) )),
% 3.04/3.31    inference('cnf.neg', [status(esa)], [t118_tmap_1])).
% 3.04/3.31  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 3.04/3.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.04/3.31  thf('1', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 3.04/3.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.04/3.31  thf(t1_tsep_1, axiom,
% 3.04/3.31    (![A:$i]:
% 3.04/3.31     ( ( l1_pre_topc @ A ) =>
% 3.04/3.31       ( ![B:$i]:
% 3.04/3.31         ( ( m1_pre_topc @ B @ A ) =>
% 3.04/3.31           ( m1_subset_1 @
% 3.04/3.31             ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 3.04/3.31  thf('2', plain,
% 3.04/3.31      (![X34 : $i, X35 : $i]:
% 3.04/3.31         (~ (m1_pre_topc @ X34 @ X35)
% 3.04/3.31          | (m1_subset_1 @ (u1_struct_0 @ X34) @ 
% 3.04/3.31             (k1_zfmisc_1 @ (u1_struct_0 @ X35)))
% 3.04/3.31          | ~ (l1_pre_topc @ X35))),
% 3.04/3.31      inference('cnf', [status(esa)], [t1_tsep_1])).
% 3.04/3.31  thf('3', plain,
% 3.04/3.31      ((~ (l1_pre_topc @ sk_A)
% 3.04/3.31        | (m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 3.04/3.31           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 3.04/3.31      inference('sup-', [status(thm)], ['1', '2'])).
% 3.04/3.31  thf('4', plain, ((l1_pre_topc @ sk_A)),
% 3.04/3.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.04/3.31  thf('5', plain,
% 3.04/3.31      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 3.04/3.31        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.04/3.31      inference('demod', [status(thm)], ['3', '4'])).
% 3.04/3.31  thf(t104_tmap_1, axiom,
% 3.04/3.31    (![A:$i]:
% 3.04/3.31     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 3.04/3.31       ( ![B:$i]:
% 3.04/3.31         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 3.04/3.31           ( ( ( u1_struct_0 @ ( k6_tmap_1 @ A @ B ) ) = ( u1_struct_0 @ A ) ) & 
% 3.04/3.31             ( ( u1_pre_topc @ ( k6_tmap_1 @ A @ B ) ) = ( k5_tmap_1 @ A @ B ) ) ) ) ) ))).
% 3.04/3.31  thf('6', plain,
% 3.04/3.31      (![X28 : $i, X29 : $i]:
% 3.04/3.31         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (u1_struct_0 @ X29)))
% 3.04/3.31          | ((u1_struct_0 @ (k6_tmap_1 @ X29 @ X28)) = (u1_struct_0 @ X29))
% 3.04/3.31          | ~ (l1_pre_topc @ X29)
% 3.04/3.31          | ~ (v2_pre_topc @ X29)
% 3.04/3.31          | (v2_struct_0 @ X29))),
% 3.04/3.31      inference('cnf', [status(esa)], [t104_tmap_1])).
% 3.04/3.31  thf('7', plain,
% 3.04/3.31      (((v2_struct_0 @ sk_A)
% 3.04/3.31        | ~ (v2_pre_topc @ sk_A)
% 3.04/3.31        | ~ (l1_pre_topc @ sk_A)
% 3.04/3.31        | ((u1_struct_0 @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 3.04/3.31            = (u1_struct_0 @ sk_A)))),
% 3.04/3.31      inference('sup-', [status(thm)], ['5', '6'])).
% 3.04/3.31  thf('8', plain, ((v2_pre_topc @ sk_A)),
% 3.04/3.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.04/3.31  thf('9', plain, ((l1_pre_topc @ sk_A)),
% 3.04/3.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.04/3.31  thf('10', plain,
% 3.04/3.31      (((v2_struct_0 @ sk_A)
% 3.04/3.31        | ((u1_struct_0 @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 3.04/3.31            = (u1_struct_0 @ sk_A)))),
% 3.04/3.31      inference('demod', [status(thm)], ['7', '8', '9'])).
% 3.04/3.31  thf('11', plain, (~ (v2_struct_0 @ sk_A)),
% 3.04/3.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.04/3.31  thf('12', plain,
% 3.04/3.31      (((u1_struct_0 @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 3.04/3.31         = (u1_struct_0 @ sk_A))),
% 3.04/3.31      inference('clc', [status(thm)], ['10', '11'])).
% 3.04/3.31  thf('13', plain,
% 3.04/3.31      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 3.04/3.31        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.04/3.31      inference('demod', [status(thm)], ['3', '4'])).
% 3.04/3.31  thf(d11_tmap_1, axiom,
% 3.04/3.31    (![A:$i]:
% 3.04/3.31     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 3.04/3.31       ( ![B:$i]:
% 3.04/3.31         ( ( m1_pre_topc @ B @ A ) =>
% 3.04/3.31           ( ![C:$i]:
% 3.04/3.31             ( ( ( v1_pre_topc @ C ) & ( v2_pre_topc @ C ) & 
% 3.04/3.31                 ( l1_pre_topc @ C ) ) =>
% 3.04/3.31               ( ( ( C ) = ( k8_tmap_1 @ A @ B ) ) <=>
% 3.04/3.31                 ( ![D:$i]:
% 3.04/3.31                   ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 3.04/3.31                     ( ( ( D ) = ( u1_struct_0 @ B ) ) =>
% 3.04/3.31                       ( ( C ) = ( k6_tmap_1 @ A @ D ) ) ) ) ) ) ) ) ) ) ))).
% 3.04/3.31  thf('14', plain,
% 3.04/3.31      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 3.04/3.31         (~ (m1_pre_topc @ X12 @ X13)
% 3.04/3.31          | ((X14) != (k8_tmap_1 @ X13 @ X12))
% 3.04/3.31          | ((X15) != (u1_struct_0 @ X12))
% 3.04/3.31          | ((X14) = (k6_tmap_1 @ X13 @ X15))
% 3.04/3.31          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 3.04/3.31          | ~ (l1_pre_topc @ X14)
% 3.04/3.31          | ~ (v2_pre_topc @ X14)
% 3.04/3.31          | ~ (v1_pre_topc @ X14)
% 3.04/3.31          | ~ (l1_pre_topc @ X13)
% 3.04/3.31          | ~ (v2_pre_topc @ X13)
% 3.04/3.31          | (v2_struct_0 @ X13))),
% 3.04/3.31      inference('cnf', [status(esa)], [d11_tmap_1])).
% 3.04/3.31  thf('15', plain,
% 3.04/3.31      (![X12 : $i, X13 : $i]:
% 3.04/3.31         ((v2_struct_0 @ X13)
% 3.04/3.31          | ~ (v2_pre_topc @ X13)
% 3.04/3.31          | ~ (l1_pre_topc @ X13)
% 3.04/3.31          | ~ (v1_pre_topc @ (k8_tmap_1 @ X13 @ X12))
% 3.04/3.31          | ~ (v2_pre_topc @ (k8_tmap_1 @ X13 @ X12))
% 3.04/3.31          | ~ (l1_pre_topc @ (k8_tmap_1 @ X13 @ X12))
% 3.04/3.31          | ~ (m1_subset_1 @ (u1_struct_0 @ X12) @ 
% 3.04/3.31               (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 3.04/3.31          | ((k8_tmap_1 @ X13 @ X12) = (k6_tmap_1 @ X13 @ (u1_struct_0 @ X12)))
% 3.04/3.31          | ~ (m1_pre_topc @ X12 @ X13))),
% 3.04/3.31      inference('simplify', [status(thm)], ['14'])).
% 3.04/3.31  thf('16', plain,
% 3.04/3.31      ((~ (m1_pre_topc @ sk_B @ sk_A)
% 3.04/3.31        | ((k8_tmap_1 @ sk_A @ sk_B)
% 3.04/3.31            = (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 3.04/3.31        | ~ (l1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 3.04/3.31        | ~ (v2_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 3.04/3.31        | ~ (v1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 3.04/3.31        | ~ (l1_pre_topc @ sk_A)
% 3.04/3.31        | ~ (v2_pre_topc @ sk_A)
% 3.04/3.31        | (v2_struct_0 @ sk_A))),
% 3.04/3.31      inference('sup-', [status(thm)], ['13', '15'])).
% 3.04/3.31  thf('17', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 3.04/3.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.04/3.31  thf('18', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 3.04/3.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.04/3.31  thf(dt_k8_tmap_1, axiom,
% 3.04/3.31    (![A:$i,B:$i]:
% 3.04/3.31     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 3.04/3.31         ( l1_pre_topc @ A ) & ( m1_pre_topc @ B @ A ) ) =>
% 3.04/3.31       ( ( v1_pre_topc @ ( k8_tmap_1 @ A @ B ) ) & 
% 3.04/3.31         ( v2_pre_topc @ ( k8_tmap_1 @ A @ B ) ) & 
% 3.04/3.31         ( l1_pre_topc @ ( k8_tmap_1 @ A @ B ) ) ) ))).
% 3.04/3.31  thf('19', plain,
% 3.04/3.31      (![X24 : $i, X25 : $i]:
% 3.04/3.31         (~ (l1_pre_topc @ X24)
% 3.04/3.31          | ~ (v2_pre_topc @ X24)
% 3.04/3.31          | (v2_struct_0 @ X24)
% 3.04/3.31          | ~ (m1_pre_topc @ X25 @ X24)
% 3.04/3.31          | (l1_pre_topc @ (k8_tmap_1 @ X24 @ X25)))),
% 3.04/3.31      inference('cnf', [status(esa)], [dt_k8_tmap_1])).
% 3.04/3.31  thf('20', plain,
% 3.04/3.31      (((l1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 3.04/3.31        | (v2_struct_0 @ sk_A)
% 3.04/3.31        | ~ (v2_pre_topc @ sk_A)
% 3.04/3.31        | ~ (l1_pre_topc @ sk_A))),
% 3.04/3.31      inference('sup-', [status(thm)], ['18', '19'])).
% 3.04/3.31  thf('21', plain, ((v2_pre_topc @ sk_A)),
% 3.04/3.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.04/3.31  thf('22', plain, ((l1_pre_topc @ sk_A)),
% 3.04/3.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.04/3.31  thf('23', plain,
% 3.04/3.31      (((l1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B)) | (v2_struct_0 @ sk_A))),
% 3.04/3.31      inference('demod', [status(thm)], ['20', '21', '22'])).
% 3.04/3.31  thf('24', plain, (~ (v2_struct_0 @ sk_A)),
% 3.04/3.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.04/3.31  thf('25', plain, ((l1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))),
% 3.04/3.31      inference('clc', [status(thm)], ['23', '24'])).
% 3.04/3.31  thf('26', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 3.04/3.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.04/3.31  thf('27', plain,
% 3.04/3.31      (![X24 : $i, X25 : $i]:
% 3.04/3.31         (~ (l1_pre_topc @ X24)
% 3.04/3.31          | ~ (v2_pre_topc @ X24)
% 3.04/3.31          | (v2_struct_0 @ X24)
% 3.04/3.31          | ~ (m1_pre_topc @ X25 @ X24)
% 3.04/3.31          | (v2_pre_topc @ (k8_tmap_1 @ X24 @ X25)))),
% 3.04/3.31      inference('cnf', [status(esa)], [dt_k8_tmap_1])).
% 3.04/3.31  thf('28', plain,
% 3.04/3.31      (((v2_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 3.04/3.31        | (v2_struct_0 @ sk_A)
% 3.04/3.31        | ~ (v2_pre_topc @ sk_A)
% 3.04/3.31        | ~ (l1_pre_topc @ sk_A))),
% 3.04/3.31      inference('sup-', [status(thm)], ['26', '27'])).
% 3.04/3.31  thf('29', plain, ((v2_pre_topc @ sk_A)),
% 3.04/3.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.04/3.31  thf('30', plain, ((l1_pre_topc @ sk_A)),
% 3.04/3.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.04/3.31  thf('31', plain,
% 3.04/3.31      (((v2_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B)) | (v2_struct_0 @ sk_A))),
% 3.04/3.31      inference('demod', [status(thm)], ['28', '29', '30'])).
% 3.04/3.31  thf('32', plain, (~ (v2_struct_0 @ sk_A)),
% 3.04/3.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.04/3.31  thf('33', plain, ((v2_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))),
% 3.04/3.31      inference('clc', [status(thm)], ['31', '32'])).
% 3.04/3.31  thf('34', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 3.04/3.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.04/3.31  thf('35', plain,
% 3.04/3.31      (![X24 : $i, X25 : $i]:
% 3.04/3.31         (~ (l1_pre_topc @ X24)
% 3.04/3.31          | ~ (v2_pre_topc @ X24)
% 3.04/3.31          | (v2_struct_0 @ X24)
% 3.04/3.31          | ~ (m1_pre_topc @ X25 @ X24)
% 3.04/3.31          | (v1_pre_topc @ (k8_tmap_1 @ X24 @ X25)))),
% 3.04/3.31      inference('cnf', [status(esa)], [dt_k8_tmap_1])).
% 3.04/3.31  thf('36', plain,
% 3.04/3.31      (((v1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 3.04/3.31        | (v2_struct_0 @ sk_A)
% 3.04/3.31        | ~ (v2_pre_topc @ sk_A)
% 3.04/3.31        | ~ (l1_pre_topc @ sk_A))),
% 3.04/3.31      inference('sup-', [status(thm)], ['34', '35'])).
% 3.04/3.31  thf('37', plain, ((v2_pre_topc @ sk_A)),
% 3.04/3.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.04/3.31  thf('38', plain, ((l1_pre_topc @ sk_A)),
% 3.04/3.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.04/3.31  thf('39', plain,
% 3.04/3.31      (((v1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B)) | (v2_struct_0 @ sk_A))),
% 3.04/3.31      inference('demod', [status(thm)], ['36', '37', '38'])).
% 3.04/3.31  thf('40', plain, (~ (v2_struct_0 @ sk_A)),
% 3.04/3.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.04/3.31  thf('41', plain, ((v1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))),
% 3.04/3.31      inference('clc', [status(thm)], ['39', '40'])).
% 3.04/3.31  thf('42', plain, ((l1_pre_topc @ sk_A)),
% 3.04/3.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.04/3.31  thf('43', plain, ((v2_pre_topc @ sk_A)),
% 3.04/3.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.04/3.31  thf('44', plain,
% 3.04/3.31      ((((k8_tmap_1 @ sk_A @ sk_B) = (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 3.04/3.31        | (v2_struct_0 @ sk_A))),
% 3.04/3.31      inference('demod', [status(thm)],
% 3.04/3.31                ['16', '17', '25', '33', '41', '42', '43'])).
% 3.04/3.31  thf('45', plain, (~ (v2_struct_0 @ sk_A)),
% 3.04/3.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.04/3.31  thf('46', plain,
% 3.04/3.31      (((k8_tmap_1 @ sk_A @ sk_B) = (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))),
% 3.04/3.31      inference('clc', [status(thm)], ['44', '45'])).
% 3.04/3.31  thf('47', plain,
% 3.04/3.31      (((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 3.04/3.31      inference('demod', [status(thm)], ['12', '46'])).
% 3.04/3.31  thf(d12_tmap_1, axiom,
% 3.04/3.31    (![A:$i]:
% 3.04/3.31     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 3.04/3.31       ( ![B:$i]:
% 3.04/3.31         ( ( m1_pre_topc @ B @ A ) =>
% 3.04/3.31           ( ![C:$i]:
% 3.04/3.31             ( ( ( v1_funct_1 @ C ) & 
% 3.04/3.31                 ( v1_funct_2 @
% 3.04/3.31                   C @ ( u1_struct_0 @ A ) @ 
% 3.04/3.31                   ( u1_struct_0 @ ( k8_tmap_1 @ A @ B ) ) ) & 
% 3.04/3.31                 ( m1_subset_1 @
% 3.04/3.31                   C @ 
% 3.04/3.31                   ( k1_zfmisc_1 @
% 3.04/3.31                     ( k2_zfmisc_1 @
% 3.04/3.31                       ( u1_struct_0 @ A ) @ 
% 3.04/3.31                       ( u1_struct_0 @ ( k8_tmap_1 @ A @ B ) ) ) ) ) ) =>
% 3.04/3.31               ( ( ( C ) = ( k9_tmap_1 @ A @ B ) ) <=>
% 3.04/3.31                 ( ![D:$i]:
% 3.04/3.31                   ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 3.04/3.31                     ( ( ( D ) = ( u1_struct_0 @ B ) ) =>
% 3.04/3.31                       ( r1_funct_2 @
% 3.04/3.31                         ( u1_struct_0 @ A ) @ 
% 3.04/3.31                         ( u1_struct_0 @ ( k8_tmap_1 @ A @ B ) ) @ 
% 3.04/3.31                         ( u1_struct_0 @ A ) @ 
% 3.04/3.31                         ( u1_struct_0 @ ( k6_tmap_1 @ A @ D ) ) @ C @ 
% 3.04/3.31                         ( k7_tmap_1 @ A @ D ) ) ) ) ) ) ) ) ) ) ))).
% 3.04/3.31  thf('48', plain,
% 3.04/3.31      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 3.04/3.31         (~ (m1_pre_topc @ X16 @ X17)
% 3.04/3.31          | ((X18) != (k9_tmap_1 @ X17 @ X16))
% 3.04/3.31          | ((X19) != (u1_struct_0 @ X16))
% 3.04/3.31          | (r1_funct_2 @ (u1_struct_0 @ X17) @ 
% 3.04/3.31             (u1_struct_0 @ (k8_tmap_1 @ X17 @ X16)) @ (u1_struct_0 @ X17) @ 
% 3.04/3.31             (u1_struct_0 @ (k6_tmap_1 @ X17 @ X19)) @ X18 @ 
% 3.04/3.31             (k7_tmap_1 @ X17 @ X19))
% 3.04/3.31          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 3.04/3.31          | ~ (m1_subset_1 @ X18 @ 
% 3.04/3.31               (k1_zfmisc_1 @ 
% 3.04/3.31                (k2_zfmisc_1 @ (u1_struct_0 @ X17) @ 
% 3.04/3.31                 (u1_struct_0 @ (k8_tmap_1 @ X17 @ X16)))))
% 3.04/3.31          | ~ (v1_funct_2 @ X18 @ (u1_struct_0 @ X17) @ 
% 3.04/3.31               (u1_struct_0 @ (k8_tmap_1 @ X17 @ X16)))
% 3.04/3.31          | ~ (v1_funct_1 @ X18)
% 3.04/3.31          | ~ (l1_pre_topc @ X17)
% 3.04/3.31          | ~ (v2_pre_topc @ X17)
% 3.04/3.31          | (v2_struct_0 @ X17))),
% 3.04/3.31      inference('cnf', [status(esa)], [d12_tmap_1])).
% 3.04/3.31  thf('49', plain,
% 3.04/3.31      (![X16 : $i, X17 : $i]:
% 3.04/3.31         ((v2_struct_0 @ X17)
% 3.04/3.31          | ~ (v2_pre_topc @ X17)
% 3.04/3.31          | ~ (l1_pre_topc @ X17)
% 3.04/3.31          | ~ (v1_funct_1 @ (k9_tmap_1 @ X17 @ X16))
% 3.04/3.31          | ~ (v1_funct_2 @ (k9_tmap_1 @ X17 @ X16) @ (u1_struct_0 @ X17) @ 
% 3.04/3.31               (u1_struct_0 @ (k8_tmap_1 @ X17 @ X16)))
% 3.04/3.31          | ~ (m1_subset_1 @ (k9_tmap_1 @ X17 @ X16) @ 
% 3.04/3.31               (k1_zfmisc_1 @ 
% 3.04/3.31                (k2_zfmisc_1 @ (u1_struct_0 @ X17) @ 
% 3.04/3.31                 (u1_struct_0 @ (k8_tmap_1 @ X17 @ X16)))))
% 3.04/3.31          | ~ (m1_subset_1 @ (u1_struct_0 @ X16) @ 
% 3.04/3.31               (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 3.04/3.31          | (r1_funct_2 @ (u1_struct_0 @ X17) @ 
% 3.04/3.31             (u1_struct_0 @ (k8_tmap_1 @ X17 @ X16)) @ (u1_struct_0 @ X17) @ 
% 3.04/3.31             (u1_struct_0 @ (k6_tmap_1 @ X17 @ (u1_struct_0 @ X16))) @ 
% 3.04/3.31             (k9_tmap_1 @ X17 @ X16) @ (k7_tmap_1 @ X17 @ (u1_struct_0 @ X16)))
% 3.04/3.31          | ~ (m1_pre_topc @ X16 @ X17))),
% 3.04/3.31      inference('simplify', [status(thm)], ['48'])).
% 3.04/3.31  thf('50', plain,
% 3.04/3.31      ((~ (m1_subset_1 @ (k9_tmap_1 @ sk_A @ sk_B) @ 
% 3.04/3.31           (k1_zfmisc_1 @ 
% 3.04/3.31            (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))))
% 3.04/3.31        | ~ (m1_pre_topc @ sk_B @ sk_A)
% 3.04/3.31        | (r1_funct_2 @ (u1_struct_0 @ sk_A) @ 
% 3.04/3.31           (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)) @ (u1_struct_0 @ sk_A) @ 
% 3.04/3.31           (u1_struct_0 @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B))) @ 
% 3.04/3.31           (k9_tmap_1 @ sk_A @ sk_B) @ 
% 3.04/3.31           (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 3.04/3.31        | ~ (m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 3.04/3.31             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 3.04/3.31        | ~ (v1_funct_2 @ (k9_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 3.04/3.31             (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))
% 3.04/3.31        | ~ (v1_funct_1 @ (k9_tmap_1 @ sk_A @ sk_B))
% 3.04/3.31        | ~ (l1_pre_topc @ sk_A)
% 3.04/3.31        | ~ (v2_pre_topc @ sk_A)
% 3.04/3.31        | (v2_struct_0 @ sk_A))),
% 3.04/3.31      inference('sup-', [status(thm)], ['47', '49'])).
% 3.04/3.31  thf('51', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 3.04/3.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.04/3.31  thf(dt_k9_tmap_1, axiom,
% 3.04/3.31    (![A:$i,B:$i]:
% 3.04/3.31     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 3.04/3.31         ( l1_pre_topc @ A ) & ( m1_pre_topc @ B @ A ) ) =>
% 3.04/3.31       ( ( v1_funct_1 @ ( k9_tmap_1 @ A @ B ) ) & 
% 3.04/3.31         ( v1_funct_2 @
% 3.04/3.31           ( k9_tmap_1 @ A @ B ) @ ( u1_struct_0 @ A ) @ 
% 3.04/3.31           ( u1_struct_0 @ ( k8_tmap_1 @ A @ B ) ) ) & 
% 3.04/3.31         ( m1_subset_1 @
% 3.04/3.31           ( k9_tmap_1 @ A @ B ) @ 
% 3.04/3.31           ( k1_zfmisc_1 @
% 3.04/3.31             ( k2_zfmisc_1 @
% 3.04/3.31               ( u1_struct_0 @ A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ A @ B ) ) ) ) ) ) ))).
% 3.14/3.31  thf('52', plain,
% 3.14/3.31      (![X26 : $i, X27 : $i]:
% 3.14/3.31         (~ (l1_pre_topc @ X26)
% 3.14/3.31          | ~ (v2_pre_topc @ X26)
% 3.14/3.31          | (v2_struct_0 @ X26)
% 3.14/3.31          | ~ (m1_pre_topc @ X27 @ X26)
% 3.14/3.31          | (m1_subset_1 @ (k9_tmap_1 @ X26 @ X27) @ 
% 3.14/3.31             (k1_zfmisc_1 @ 
% 3.14/3.31              (k2_zfmisc_1 @ (u1_struct_0 @ X26) @ 
% 3.14/3.31               (u1_struct_0 @ (k8_tmap_1 @ X26 @ X27))))))),
% 3.14/3.31      inference('cnf', [status(esa)], [dt_k9_tmap_1])).
% 3.14/3.31  thf('53', plain,
% 3.14/3.31      (((m1_subset_1 @ (k9_tmap_1 @ sk_A @ sk_B) @ 
% 3.14/3.31         (k1_zfmisc_1 @ 
% 3.14/3.31          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 3.14/3.31           (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))))
% 3.14/3.31        | (v2_struct_0 @ sk_A)
% 3.14/3.31        | ~ (v2_pre_topc @ sk_A)
% 3.14/3.31        | ~ (l1_pre_topc @ sk_A))),
% 3.14/3.31      inference('sup-', [status(thm)], ['51', '52'])).
% 3.14/3.31  thf('54', plain, ((v2_pre_topc @ sk_A)),
% 3.14/3.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.14/3.31  thf('55', plain, ((l1_pre_topc @ sk_A)),
% 3.14/3.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.14/3.31  thf('56', plain,
% 3.14/3.31      (((m1_subset_1 @ (k9_tmap_1 @ sk_A @ sk_B) @ 
% 3.14/3.31         (k1_zfmisc_1 @ 
% 3.14/3.31          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 3.14/3.31           (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))))
% 3.14/3.31        | (v2_struct_0 @ sk_A))),
% 3.14/3.31      inference('demod', [status(thm)], ['53', '54', '55'])).
% 3.14/3.31  thf('57', plain,
% 3.14/3.31      (((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 3.14/3.31      inference('demod', [status(thm)], ['12', '46'])).
% 3.14/3.31  thf('58', plain,
% 3.14/3.31      (((m1_subset_1 @ (k9_tmap_1 @ sk_A @ sk_B) @ 
% 3.14/3.31         (k1_zfmisc_1 @ 
% 3.14/3.31          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))))
% 3.14/3.31        | (v2_struct_0 @ sk_A))),
% 3.14/3.31      inference('demod', [status(thm)], ['56', '57'])).
% 3.14/3.31  thf('59', plain, (~ (v2_struct_0 @ sk_A)),
% 3.14/3.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.14/3.31  thf('60', plain,
% 3.14/3.31      ((m1_subset_1 @ (k9_tmap_1 @ sk_A @ sk_B) @ 
% 3.14/3.31        (k1_zfmisc_1 @ 
% 3.14/3.31         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))))),
% 3.14/3.31      inference('clc', [status(thm)], ['58', '59'])).
% 3.14/3.31  thf('61', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 3.14/3.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.14/3.31  thf('62', plain,
% 3.14/3.31      (((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 3.14/3.31      inference('demod', [status(thm)], ['12', '46'])).
% 3.14/3.31  thf('63', plain,
% 3.14/3.31      (((k8_tmap_1 @ sk_A @ sk_B) = (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))),
% 3.14/3.31      inference('clc', [status(thm)], ['44', '45'])).
% 3.14/3.31  thf('64', plain,
% 3.14/3.31      (((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 3.14/3.31      inference('demod', [status(thm)], ['12', '46'])).
% 3.14/3.31  thf('65', plain,
% 3.14/3.31      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 3.14/3.31        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.14/3.31      inference('demod', [status(thm)], ['3', '4'])).
% 3.14/3.31  thf('66', plain,
% 3.14/3.31      (((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 3.14/3.31      inference('demod', [status(thm)], ['12', '46'])).
% 3.14/3.31  thf('67', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 3.14/3.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.14/3.31  thf('68', plain,
% 3.14/3.31      (![X26 : $i, X27 : $i]:
% 3.14/3.31         (~ (l1_pre_topc @ X26)
% 3.14/3.31          | ~ (v2_pre_topc @ X26)
% 3.14/3.31          | (v2_struct_0 @ X26)
% 3.14/3.31          | ~ (m1_pre_topc @ X27 @ X26)
% 3.14/3.31          | (v1_funct_2 @ (k9_tmap_1 @ X26 @ X27) @ (u1_struct_0 @ X26) @ 
% 3.14/3.31             (u1_struct_0 @ (k8_tmap_1 @ X26 @ X27))))),
% 3.14/3.31      inference('cnf', [status(esa)], [dt_k9_tmap_1])).
% 3.14/3.31  thf('69', plain,
% 3.14/3.31      (((v1_funct_2 @ (k9_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 3.14/3.31         (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))
% 3.14/3.31        | (v2_struct_0 @ sk_A)
% 3.14/3.31        | ~ (v2_pre_topc @ sk_A)
% 3.14/3.31        | ~ (l1_pre_topc @ sk_A))),
% 3.14/3.31      inference('sup-', [status(thm)], ['67', '68'])).
% 3.14/3.31  thf('70', plain, ((v2_pre_topc @ sk_A)),
% 3.14/3.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.14/3.31  thf('71', plain, ((l1_pre_topc @ sk_A)),
% 3.14/3.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.14/3.31  thf('72', plain,
% 3.14/3.31      (((v1_funct_2 @ (k9_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 3.14/3.31         (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))
% 3.14/3.31        | (v2_struct_0 @ sk_A))),
% 3.14/3.31      inference('demod', [status(thm)], ['69', '70', '71'])).
% 3.14/3.31  thf('73', plain, (~ (v2_struct_0 @ sk_A)),
% 3.14/3.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.14/3.31  thf('74', plain,
% 3.14/3.31      ((v1_funct_2 @ (k9_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 3.14/3.31        (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))),
% 3.14/3.31      inference('clc', [status(thm)], ['72', '73'])).
% 3.14/3.31  thf('75', plain,
% 3.14/3.31      (((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 3.14/3.31      inference('demod', [status(thm)], ['12', '46'])).
% 3.14/3.31  thf('76', plain,
% 3.14/3.31      ((v1_funct_2 @ (k9_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 3.14/3.31        (u1_struct_0 @ sk_A))),
% 3.14/3.31      inference('demod', [status(thm)], ['74', '75'])).
% 3.14/3.31  thf('77', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 3.14/3.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.14/3.31  thf('78', plain,
% 3.14/3.31      (![X26 : $i, X27 : $i]:
% 3.14/3.31         (~ (l1_pre_topc @ X26)
% 3.14/3.31          | ~ (v2_pre_topc @ X26)
% 3.14/3.31          | (v2_struct_0 @ X26)
% 3.14/3.31          | ~ (m1_pre_topc @ X27 @ X26)
% 3.14/3.31          | (v1_funct_1 @ (k9_tmap_1 @ X26 @ X27)))),
% 3.14/3.31      inference('cnf', [status(esa)], [dt_k9_tmap_1])).
% 3.14/3.31  thf('79', plain,
% 3.14/3.31      (((v1_funct_1 @ (k9_tmap_1 @ sk_A @ sk_B))
% 3.14/3.31        | (v2_struct_0 @ sk_A)
% 3.14/3.31        | ~ (v2_pre_topc @ sk_A)
% 3.14/3.31        | ~ (l1_pre_topc @ sk_A))),
% 3.14/3.31      inference('sup-', [status(thm)], ['77', '78'])).
% 3.14/3.31  thf('80', plain, ((v2_pre_topc @ sk_A)),
% 3.14/3.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.14/3.31  thf('81', plain, ((l1_pre_topc @ sk_A)),
% 3.14/3.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.14/3.31  thf('82', plain,
% 3.14/3.31      (((v1_funct_1 @ (k9_tmap_1 @ sk_A @ sk_B)) | (v2_struct_0 @ sk_A))),
% 3.14/3.31      inference('demod', [status(thm)], ['79', '80', '81'])).
% 3.14/3.31  thf('83', plain, (~ (v2_struct_0 @ sk_A)),
% 3.14/3.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.14/3.31  thf('84', plain, ((v1_funct_1 @ (k9_tmap_1 @ sk_A @ sk_B))),
% 3.14/3.31      inference('clc', [status(thm)], ['82', '83'])).
% 3.14/3.31  thf('85', plain, ((l1_pre_topc @ sk_A)),
% 3.14/3.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.14/3.31  thf('86', plain, ((v2_pre_topc @ sk_A)),
% 3.14/3.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.14/3.31  thf('87', plain,
% 3.14/3.31      (((r1_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 3.14/3.31         (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 3.14/3.31         (k9_tmap_1 @ sk_A @ sk_B) @ (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 3.14/3.31        | (v2_struct_0 @ sk_A))),
% 3.14/3.31      inference('demod', [status(thm)],
% 3.14/3.31                ['50', '60', '61', '62', '63', '64', '65', '66', '76', '84', 
% 3.14/3.31                 '85', '86'])).
% 3.14/3.31  thf('88', plain, (~ (v2_struct_0 @ sk_A)),
% 3.14/3.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.14/3.31  thf('89', plain,
% 3.14/3.31      ((r1_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 3.14/3.31        (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 3.14/3.31        (k9_tmap_1 @ sk_A @ sk_B) @ (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))),
% 3.14/3.31      inference('clc', [status(thm)], ['87', '88'])).
% 3.14/3.31  thf('90', plain,
% 3.14/3.31      ((m1_subset_1 @ (k9_tmap_1 @ sk_A @ sk_B) @ 
% 3.14/3.31        (k1_zfmisc_1 @ 
% 3.14/3.31         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))))),
% 3.14/3.31      inference('clc', [status(thm)], ['58', '59'])).
% 3.14/3.31  thf(redefinition_r1_funct_2, axiom,
% 3.14/3.31    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 3.14/3.31     ( ( ( ~( v1_xboole_0 @ B ) ) & ( ~( v1_xboole_0 @ D ) ) & 
% 3.14/3.31         ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ A @ B ) & 
% 3.14/3.31         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 3.14/3.31         ( v1_funct_1 @ F ) & ( v1_funct_2 @ F @ C @ D ) & 
% 3.14/3.31         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 3.14/3.31       ( ( r1_funct_2 @ A @ B @ C @ D @ E @ F ) <=> ( ( E ) = ( F ) ) ) ))).
% 3.14/3.31  thf('91', plain,
% 3.14/3.31      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 3.14/3.31         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8)))
% 3.14/3.31          | ~ (v1_funct_2 @ X6 @ X7 @ X8)
% 3.14/3.31          | ~ (v1_funct_1 @ X6)
% 3.14/3.31          | (v1_xboole_0 @ X9)
% 3.14/3.31          | (v1_xboole_0 @ X8)
% 3.14/3.31          | ~ (v1_funct_1 @ X10)
% 3.14/3.31          | ~ (v1_funct_2 @ X10 @ X11 @ X9)
% 3.14/3.31          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X9)))
% 3.14/3.31          | ((X6) = (X10))
% 3.14/3.31          | ~ (r1_funct_2 @ X7 @ X8 @ X11 @ X9 @ X6 @ X10))),
% 3.14/3.31      inference('cnf', [status(esa)], [redefinition_r1_funct_2])).
% 3.14/3.31  thf('92', plain,
% 3.14/3.31      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.14/3.31         (~ (r1_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ X2 @ 
% 3.14/3.31             X1 @ (k9_tmap_1 @ sk_A @ sk_B) @ X0)
% 3.14/3.31          | ((k9_tmap_1 @ sk_A @ sk_B) = (X0))
% 3.14/3.31          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 3.14/3.31          | ~ (v1_funct_2 @ X0 @ X2 @ X1)
% 3.14/3.31          | ~ (v1_funct_1 @ X0)
% 3.14/3.31          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 3.14/3.31          | (v1_xboole_0 @ X1)
% 3.14/3.31          | ~ (v1_funct_1 @ (k9_tmap_1 @ sk_A @ sk_B))
% 3.14/3.31          | ~ (v1_funct_2 @ (k9_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 3.14/3.31               (u1_struct_0 @ sk_A)))),
% 3.14/3.31      inference('sup-', [status(thm)], ['90', '91'])).
% 3.14/3.31  thf('93', plain, ((v1_funct_1 @ (k9_tmap_1 @ sk_A @ sk_B))),
% 3.14/3.31      inference('clc', [status(thm)], ['82', '83'])).
% 3.14/3.31  thf('94', plain,
% 3.14/3.31      ((v1_funct_2 @ (k9_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 3.14/3.31        (u1_struct_0 @ sk_A))),
% 3.14/3.31      inference('demod', [status(thm)], ['74', '75'])).
% 3.14/3.31  thf('95', plain,
% 3.14/3.31      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.14/3.31         (~ (r1_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ X2 @ 
% 3.14/3.31             X1 @ (k9_tmap_1 @ sk_A @ sk_B) @ X0)
% 3.14/3.31          | ((k9_tmap_1 @ sk_A @ sk_B) = (X0))
% 3.14/3.31          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 3.14/3.31          | ~ (v1_funct_2 @ X0 @ X2 @ X1)
% 3.14/3.31          | ~ (v1_funct_1 @ X0)
% 3.14/3.31          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 3.14/3.31          | (v1_xboole_0 @ X1))),
% 3.14/3.31      inference('demod', [status(thm)], ['92', '93', '94'])).
% 3.14/3.31  thf('96', plain,
% 3.14/3.31      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 3.14/3.31        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 3.14/3.31        | ~ (v1_funct_1 @ (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 3.14/3.31        | ~ (v1_funct_2 @ (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)) @ 
% 3.14/3.31             (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))
% 3.14/3.31        | ~ (m1_subset_1 @ (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)) @ 
% 3.14/3.31             (k1_zfmisc_1 @ 
% 3.14/3.31              (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))))
% 3.14/3.31        | ((k9_tmap_1 @ sk_A @ sk_B)
% 3.14/3.31            = (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B))))),
% 3.14/3.31      inference('sup-', [status(thm)], ['89', '95'])).
% 3.14/3.31  thf('97', plain,
% 3.14/3.31      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 3.14/3.31        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.14/3.31      inference('demod', [status(thm)], ['3', '4'])).
% 3.14/3.31  thf(dt_k7_tmap_1, axiom,
% 3.14/3.31    (![A:$i,B:$i]:
% 3.14/3.31     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 3.14/3.31         ( l1_pre_topc @ A ) & 
% 3.14/3.31         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 3.14/3.31       ( ( v1_funct_1 @ ( k7_tmap_1 @ A @ B ) ) & 
% 3.14/3.31         ( v1_funct_2 @
% 3.14/3.31           ( k7_tmap_1 @ A @ B ) @ ( u1_struct_0 @ A ) @ 
% 3.14/3.31           ( u1_struct_0 @ ( k6_tmap_1 @ A @ B ) ) ) & 
% 3.14/3.31         ( m1_subset_1 @
% 3.14/3.31           ( k7_tmap_1 @ A @ B ) @ 
% 3.14/3.31           ( k1_zfmisc_1 @
% 3.14/3.31             ( k2_zfmisc_1 @
% 3.14/3.31               ( u1_struct_0 @ A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ A @ B ) ) ) ) ) ) ))).
% 3.14/3.31  thf('98', plain,
% 3.14/3.31      (![X22 : $i, X23 : $i]:
% 3.14/3.31         (~ (l1_pre_topc @ X22)
% 3.14/3.31          | ~ (v2_pre_topc @ X22)
% 3.14/3.31          | (v2_struct_0 @ X22)
% 3.14/3.31          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 3.14/3.31          | (v1_funct_1 @ (k7_tmap_1 @ X22 @ X23)))),
% 3.14/3.31      inference('cnf', [status(esa)], [dt_k7_tmap_1])).
% 3.14/3.31  thf('99', plain,
% 3.14/3.31      (((v1_funct_1 @ (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 3.14/3.31        | (v2_struct_0 @ sk_A)
% 3.14/3.31        | ~ (v2_pre_topc @ sk_A)
% 3.14/3.31        | ~ (l1_pre_topc @ sk_A))),
% 3.14/3.31      inference('sup-', [status(thm)], ['97', '98'])).
% 3.14/3.31  thf('100', plain, ((v2_pre_topc @ sk_A)),
% 3.14/3.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.14/3.31  thf('101', plain, ((l1_pre_topc @ sk_A)),
% 3.14/3.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.14/3.31  thf('102', plain,
% 3.14/3.31      (((v1_funct_1 @ (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 3.14/3.31        | (v2_struct_0 @ sk_A))),
% 3.14/3.31      inference('demod', [status(thm)], ['99', '100', '101'])).
% 3.14/3.31  thf('103', plain, (~ (v2_struct_0 @ sk_A)),
% 3.14/3.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.14/3.31  thf('104', plain, ((v1_funct_1 @ (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))),
% 3.14/3.31      inference('clc', [status(thm)], ['102', '103'])).
% 3.14/3.31  thf('105', plain,
% 3.14/3.31      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 3.14/3.31        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.14/3.31      inference('demod', [status(thm)], ['3', '4'])).
% 3.14/3.31  thf('106', plain,
% 3.14/3.31      (![X22 : $i, X23 : $i]:
% 3.14/3.31         (~ (l1_pre_topc @ X22)
% 3.14/3.31          | ~ (v2_pre_topc @ X22)
% 3.14/3.31          | (v2_struct_0 @ X22)
% 3.14/3.31          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 3.14/3.31          | (v1_funct_2 @ (k7_tmap_1 @ X22 @ X23) @ (u1_struct_0 @ X22) @ 
% 3.14/3.31             (u1_struct_0 @ (k6_tmap_1 @ X22 @ X23))))),
% 3.14/3.31      inference('cnf', [status(esa)], [dt_k7_tmap_1])).
% 3.14/3.31  thf('107', plain,
% 3.14/3.31      (((v1_funct_2 @ (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)) @ 
% 3.14/3.31         (u1_struct_0 @ sk_A) @ 
% 3.14/3.31         (u1_struct_0 @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B))))
% 3.14/3.31        | (v2_struct_0 @ sk_A)
% 3.14/3.31        | ~ (v2_pre_topc @ sk_A)
% 3.14/3.31        | ~ (l1_pre_topc @ sk_A))),
% 3.14/3.31      inference('sup-', [status(thm)], ['105', '106'])).
% 3.14/3.31  thf('108', plain,
% 3.14/3.31      (((u1_struct_0 @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 3.14/3.31         = (u1_struct_0 @ sk_A))),
% 3.14/3.31      inference('clc', [status(thm)], ['10', '11'])).
% 3.14/3.31  thf('109', plain, ((v2_pre_topc @ sk_A)),
% 3.14/3.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.14/3.31  thf('110', plain, ((l1_pre_topc @ sk_A)),
% 3.14/3.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.14/3.31  thf('111', plain,
% 3.14/3.31      (((v1_funct_2 @ (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)) @ 
% 3.14/3.31         (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))
% 3.14/3.31        | (v2_struct_0 @ sk_A))),
% 3.14/3.31      inference('demod', [status(thm)], ['107', '108', '109', '110'])).
% 3.14/3.31  thf('112', plain, (~ (v2_struct_0 @ sk_A)),
% 3.14/3.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.14/3.31  thf('113', plain,
% 3.14/3.31      ((v1_funct_2 @ (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)) @ 
% 3.14/3.31        (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))),
% 3.14/3.31      inference('clc', [status(thm)], ['111', '112'])).
% 3.14/3.31  thf('114', plain,
% 3.14/3.31      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 3.14/3.31        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.14/3.31      inference('demod', [status(thm)], ['3', '4'])).
% 3.14/3.31  thf('115', plain,
% 3.14/3.31      (![X22 : $i, X23 : $i]:
% 3.14/3.31         (~ (l1_pre_topc @ X22)
% 3.14/3.31          | ~ (v2_pre_topc @ X22)
% 3.14/3.31          | (v2_struct_0 @ X22)
% 3.14/3.31          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 3.14/3.31          | (m1_subset_1 @ (k7_tmap_1 @ X22 @ X23) @ 
% 3.14/3.31             (k1_zfmisc_1 @ 
% 3.14/3.31              (k2_zfmisc_1 @ (u1_struct_0 @ X22) @ 
% 3.14/3.31               (u1_struct_0 @ (k6_tmap_1 @ X22 @ X23))))))),
% 3.14/3.31      inference('cnf', [status(esa)], [dt_k7_tmap_1])).
% 3.14/3.31  thf('116', plain,
% 3.14/3.31      (((m1_subset_1 @ (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)) @ 
% 3.14/3.31         (k1_zfmisc_1 @ 
% 3.14/3.31          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 3.14/3.31           (u1_struct_0 @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B))))))
% 3.14/3.31        | (v2_struct_0 @ sk_A)
% 3.14/3.31        | ~ (v2_pre_topc @ sk_A)
% 3.14/3.31        | ~ (l1_pre_topc @ sk_A))),
% 3.14/3.31      inference('sup-', [status(thm)], ['114', '115'])).
% 3.14/3.31  thf('117', plain,
% 3.14/3.31      (((k8_tmap_1 @ sk_A @ sk_B) = (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))),
% 3.14/3.31      inference('clc', [status(thm)], ['44', '45'])).
% 3.14/3.31  thf('118', plain,
% 3.14/3.31      (((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 3.14/3.31      inference('demod', [status(thm)], ['12', '46'])).
% 3.14/3.31  thf('119', plain, ((v2_pre_topc @ sk_A)),
% 3.14/3.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.14/3.31  thf('120', plain, ((l1_pre_topc @ sk_A)),
% 3.14/3.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.14/3.31  thf('121', plain,
% 3.14/3.31      (((m1_subset_1 @ (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)) @ 
% 3.14/3.31         (k1_zfmisc_1 @ 
% 3.14/3.31          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))))
% 3.14/3.31        | (v2_struct_0 @ sk_A))),
% 3.14/3.31      inference('demod', [status(thm)], ['116', '117', '118', '119', '120'])).
% 3.14/3.31  thf('122', plain, (~ (v2_struct_0 @ sk_A)),
% 3.14/3.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.14/3.31  thf('123', plain,
% 3.14/3.31      ((m1_subset_1 @ (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)) @ 
% 3.14/3.31        (k1_zfmisc_1 @ 
% 3.14/3.31         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))))),
% 3.14/3.31      inference('clc', [status(thm)], ['121', '122'])).
% 3.14/3.31  thf('124', plain,
% 3.14/3.31      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 3.14/3.31        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 3.14/3.31        | ((k9_tmap_1 @ sk_A @ sk_B)
% 3.14/3.31            = (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B))))),
% 3.14/3.31      inference('demod', [status(thm)], ['96', '104', '113', '123'])).
% 3.14/3.31  thf('125', plain,
% 3.14/3.31      ((((k9_tmap_1 @ sk_A @ sk_B) = (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 3.14/3.31        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 3.14/3.31      inference('simplify', [status(thm)], ['124'])).
% 3.14/3.31  thf('126', plain, ((m1_subset_1 @ sk_D_2 @ (u1_struct_0 @ sk_C))),
% 3.14/3.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.14/3.31  thf('127', plain, ((r1_tsep_1 @ sk_B @ sk_C)),
% 3.14/3.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.14/3.31  thf(d3_tsep_1, axiom,
% 3.14/3.31    (![A:$i]:
% 3.14/3.31     ( ( l1_struct_0 @ A ) =>
% 3.14/3.31       ( ![B:$i]:
% 3.14/3.31         ( ( l1_struct_0 @ B ) =>
% 3.14/3.31           ( ( r1_tsep_1 @ A @ B ) <=>
% 3.14/3.31             ( r1_xboole_0 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) ))).
% 3.14/3.31  thf('128', plain,
% 3.14/3.31      (![X20 : $i, X21 : $i]:
% 3.14/3.31         (~ (l1_struct_0 @ X20)
% 3.14/3.31          | ~ (r1_tsep_1 @ X21 @ X20)
% 3.14/3.31          | (r1_xboole_0 @ (u1_struct_0 @ X21) @ (u1_struct_0 @ X20))
% 3.14/3.31          | ~ (l1_struct_0 @ X21))),
% 3.14/3.31      inference('cnf', [status(esa)], [d3_tsep_1])).
% 3.14/3.31  thf('129', plain,
% 3.14/3.31      ((~ (l1_struct_0 @ sk_B)
% 3.14/3.31        | (r1_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C))
% 3.14/3.31        | ~ (l1_struct_0 @ sk_C))),
% 3.14/3.31      inference('sup-', [status(thm)], ['127', '128'])).
% 3.14/3.31  thf('130', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 3.14/3.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.14/3.31  thf(dt_m1_pre_topc, axiom,
% 3.14/3.31    (![A:$i]:
% 3.14/3.31     ( ( l1_pre_topc @ A ) =>
% 3.14/3.31       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 3.14/3.31  thf('131', plain,
% 3.14/3.31      (![X3 : $i, X4 : $i]:
% 3.14/3.31         (~ (m1_pre_topc @ X3 @ X4) | (l1_pre_topc @ X3) | ~ (l1_pre_topc @ X4))),
% 3.14/3.31      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 3.14/3.31  thf('132', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_B))),
% 3.14/3.31      inference('sup-', [status(thm)], ['130', '131'])).
% 3.14/3.31  thf('133', plain, ((l1_pre_topc @ sk_A)),
% 3.14/3.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.14/3.31  thf('134', plain, ((l1_pre_topc @ sk_B)),
% 3.14/3.31      inference('demod', [status(thm)], ['132', '133'])).
% 3.14/3.31  thf(dt_l1_pre_topc, axiom,
% 3.14/3.31    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 3.14/3.31  thf('135', plain, (![X2 : $i]: ((l1_struct_0 @ X2) | ~ (l1_pre_topc @ X2))),
% 3.14/3.31      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 3.14/3.31  thf('136', plain, ((l1_struct_0 @ sk_B)),
% 3.14/3.31      inference('sup-', [status(thm)], ['134', '135'])).
% 3.14/3.31  thf('137', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 3.14/3.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.14/3.31  thf('138', plain,
% 3.14/3.31      (![X3 : $i, X4 : $i]:
% 3.14/3.31         (~ (m1_pre_topc @ X3 @ X4) | (l1_pre_topc @ X3) | ~ (l1_pre_topc @ X4))),
% 3.14/3.31      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 3.14/3.31  thf('139', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_C))),
% 3.14/3.31      inference('sup-', [status(thm)], ['137', '138'])).
% 3.14/3.31  thf('140', plain, ((l1_pre_topc @ sk_A)),
% 3.14/3.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.14/3.31  thf('141', plain, ((l1_pre_topc @ sk_C)),
% 3.14/3.31      inference('demod', [status(thm)], ['139', '140'])).
% 3.14/3.31  thf('142', plain, (![X2 : $i]: ((l1_struct_0 @ X2) | ~ (l1_pre_topc @ X2))),
% 3.14/3.31      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 3.14/3.31  thf('143', plain, ((l1_struct_0 @ sk_C)),
% 3.14/3.31      inference('sup-', [status(thm)], ['141', '142'])).
% 3.14/3.31  thf('144', plain,
% 3.14/3.31      ((r1_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C))),
% 3.14/3.31      inference('demod', [status(thm)], ['129', '136', '143'])).
% 3.14/3.31  thf(symmetry_r1_xboole_0, axiom,
% 3.14/3.31    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 3.14/3.31  thf('145', plain,
% 3.14/3.31      (![X0 : $i, X1 : $i]:
% 3.14/3.31         ((r1_xboole_0 @ X0 @ X1) | ~ (r1_xboole_0 @ X1 @ X0))),
% 3.14/3.31      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 3.14/3.31  thf('146', plain,
% 3.14/3.31      ((r1_xboole_0 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 3.14/3.31      inference('sup-', [status(thm)], ['144', '145'])).
% 3.14/3.31  thf('147', plain,
% 3.14/3.31      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 3.14/3.31        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.14/3.31      inference('demod', [status(thm)], ['3', '4'])).
% 3.14/3.31  thf(t109_tmap_1, axiom,
% 3.14/3.31    (![A:$i]:
% 3.14/3.31     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 3.14/3.31       ( ![B:$i]:
% 3.14/3.31         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 3.14/3.31           ( ![C:$i]:
% 3.14/3.31             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 3.14/3.31               ( ( r1_xboole_0 @ ( u1_struct_0 @ C ) @ B ) =>
% 3.14/3.31                 ( ![D:$i]:
% 3.14/3.31                   ( ( m1_subset_1 @ D @ ( u1_struct_0 @ C ) ) =>
% 3.14/3.31                     ( r1_tmap_1 @
% 3.14/3.31                       C @ ( k6_tmap_1 @ A @ B ) @ 
% 3.14/3.31                       ( k2_tmap_1 @
% 3.14/3.31                         A @ ( k6_tmap_1 @ A @ B ) @ ( k7_tmap_1 @ A @ B ) @ C ) @ 
% 3.14/3.31                       D ) ) ) ) ) ) ) ) ))).
% 3.14/3.31  thf('148', plain,
% 3.14/3.31      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 3.14/3.31         (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ X31)))
% 3.14/3.31          | ~ (r1_xboole_0 @ (u1_struct_0 @ X32) @ X30)
% 3.14/3.31          | ~ (m1_subset_1 @ X33 @ (u1_struct_0 @ X32))
% 3.14/3.31          | (r1_tmap_1 @ X32 @ (k6_tmap_1 @ X31 @ X30) @ 
% 3.14/3.31             (k2_tmap_1 @ X31 @ (k6_tmap_1 @ X31 @ X30) @ 
% 3.14/3.31              (k7_tmap_1 @ X31 @ X30) @ X32) @ 
% 3.14/3.31             X33)
% 3.14/3.31          | ~ (m1_pre_topc @ X32 @ X31)
% 3.14/3.31          | (v2_struct_0 @ X32)
% 3.14/3.31          | ~ (l1_pre_topc @ X31)
% 3.14/3.31          | ~ (v2_pre_topc @ X31)
% 3.14/3.31          | (v2_struct_0 @ X31))),
% 3.14/3.31      inference('cnf', [status(esa)], [t109_tmap_1])).
% 3.14/3.31  thf('149', plain,
% 3.14/3.31      (![X0 : $i, X1 : $i]:
% 3.14/3.31         ((v2_struct_0 @ sk_A)
% 3.14/3.31          | ~ (v2_pre_topc @ sk_A)
% 3.14/3.31          | ~ (l1_pre_topc @ sk_A)
% 3.14/3.31          | (v2_struct_0 @ X0)
% 3.14/3.31          | ~ (m1_pre_topc @ X0 @ sk_A)
% 3.14/3.31          | (r1_tmap_1 @ X0 @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)) @ 
% 3.14/3.31             (k2_tmap_1 @ sk_A @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)) @ 
% 3.14/3.31              (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)) @ X0) @ 
% 3.14/3.31             X1)
% 3.14/3.31          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 3.14/3.31          | ~ (r1_xboole_0 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B)))),
% 3.14/3.31      inference('sup-', [status(thm)], ['147', '148'])).
% 3.14/3.31  thf('150', plain, ((v2_pre_topc @ sk_A)),
% 3.14/3.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.14/3.31  thf('151', plain, ((l1_pre_topc @ sk_A)),
% 3.14/3.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.14/3.31  thf('152', plain,
% 3.14/3.31      (((k8_tmap_1 @ sk_A @ sk_B) = (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))),
% 3.14/3.31      inference('clc', [status(thm)], ['44', '45'])).
% 3.14/3.31  thf('153', plain,
% 3.14/3.31      (((k8_tmap_1 @ sk_A @ sk_B) = (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))),
% 3.14/3.31      inference('clc', [status(thm)], ['44', '45'])).
% 3.14/3.31  thf('154', plain,
% 3.14/3.31      (![X0 : $i, X1 : $i]:
% 3.14/3.31         ((v2_struct_0 @ sk_A)
% 3.14/3.31          | (v2_struct_0 @ X0)
% 3.14/3.31          | ~ (m1_pre_topc @ X0 @ sk_A)
% 3.14/3.31          | (r1_tmap_1 @ X0 @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 3.14/3.31             (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 3.14/3.31              (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)) @ X0) @ 
% 3.14/3.31             X1)
% 3.14/3.31          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 3.14/3.31          | ~ (r1_xboole_0 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B)))),
% 3.14/3.31      inference('demod', [status(thm)], ['149', '150', '151', '152', '153'])).
% 3.14/3.31  thf('155', plain,
% 3.14/3.31      (![X0 : $i]:
% 3.14/3.31         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_C))
% 3.14/3.31          | (r1_tmap_1 @ sk_C @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 3.14/3.31             (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 3.14/3.31              (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)) @ sk_C) @ 
% 3.14/3.31             X0)
% 3.14/3.31          | ~ (m1_pre_topc @ sk_C @ sk_A)
% 3.14/3.31          | (v2_struct_0 @ sk_C)
% 3.14/3.31          | (v2_struct_0 @ sk_A))),
% 3.14/3.31      inference('sup-', [status(thm)], ['146', '154'])).
% 3.14/3.31  thf('156', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 3.14/3.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.14/3.31  thf('157', plain,
% 3.14/3.31      (![X0 : $i]:
% 3.14/3.31         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_C))
% 3.14/3.31          | (r1_tmap_1 @ sk_C @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 3.14/3.31             (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 3.14/3.31              (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)) @ sk_C) @ 
% 3.14/3.31             X0)
% 3.14/3.31          | (v2_struct_0 @ sk_C)
% 3.14/3.31          | (v2_struct_0 @ sk_A))),
% 3.14/3.31      inference('demod', [status(thm)], ['155', '156'])).
% 3.14/3.31  thf('158', plain,
% 3.14/3.31      (((v2_struct_0 @ sk_A)
% 3.14/3.31        | (v2_struct_0 @ sk_C)
% 3.14/3.31        | (r1_tmap_1 @ sk_C @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 3.14/3.31           (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 3.14/3.31            (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)) @ sk_C) @ 
% 3.14/3.31           sk_D_2))),
% 3.14/3.31      inference('sup-', [status(thm)], ['126', '157'])).
% 3.14/3.31  thf('159', plain, (~ (v2_struct_0 @ sk_A)),
% 3.14/3.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.14/3.31  thf('160', plain,
% 3.14/3.31      (((r1_tmap_1 @ sk_C @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 3.14/3.31         (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 3.14/3.31          (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)) @ sk_C) @ 
% 3.14/3.31         sk_D_2)
% 3.14/3.31        | (v2_struct_0 @ sk_C))),
% 3.14/3.31      inference('clc', [status(thm)], ['158', '159'])).
% 3.14/3.31  thf('161', plain, (~ (v2_struct_0 @ sk_C)),
% 3.14/3.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.14/3.31  thf('162', plain,
% 3.14/3.31      ((r1_tmap_1 @ sk_C @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 3.14/3.31        (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 3.14/3.31         (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)) @ sk_C) @ 
% 3.14/3.31        sk_D_2)),
% 3.14/3.31      inference('clc', [status(thm)], ['160', '161'])).
% 3.14/3.31  thf('163', plain,
% 3.14/3.31      (((r1_tmap_1 @ sk_C @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 3.14/3.31         (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 3.14/3.31          (k9_tmap_1 @ sk_A @ sk_B) @ sk_C) @ 
% 3.14/3.31         sk_D_2)
% 3.14/3.31        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 3.14/3.31      inference('sup+', [status(thm)], ['125', '162'])).
% 3.14/3.31  thf('164', plain,
% 3.14/3.31      (~ (r1_tmap_1 @ sk_C @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 3.14/3.31          (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 3.14/3.31           (k9_tmap_1 @ sk_A @ sk_B) @ sk_C) @ 
% 3.14/3.31          sk_D_2)),
% 3.14/3.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.14/3.31  thf('165', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 3.14/3.31      inference('clc', [status(thm)], ['163', '164'])).
% 3.14/3.31  thf(fc2_struct_0, axiom,
% 3.14/3.31    (![A:$i]:
% 3.14/3.31     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 3.14/3.31       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 3.14/3.31  thf('166', plain,
% 3.14/3.31      (![X5 : $i]:
% 3.14/3.31         (~ (v1_xboole_0 @ (u1_struct_0 @ X5))
% 3.14/3.31          | ~ (l1_struct_0 @ X5)
% 3.14/3.31          | (v2_struct_0 @ X5))),
% 3.14/3.31      inference('cnf', [status(esa)], [fc2_struct_0])).
% 3.14/3.31  thf('167', plain, (((v2_struct_0 @ sk_A) | ~ (l1_struct_0 @ sk_A))),
% 3.14/3.31      inference('sup-', [status(thm)], ['165', '166'])).
% 3.14/3.31  thf('168', plain, ((l1_pre_topc @ sk_A)),
% 3.14/3.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.14/3.31  thf('169', plain, (![X2 : $i]: ((l1_struct_0 @ X2) | ~ (l1_pre_topc @ X2))),
% 3.14/3.31      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 3.14/3.31  thf('170', plain, ((l1_struct_0 @ sk_A)),
% 3.14/3.31      inference('sup-', [status(thm)], ['168', '169'])).
% 3.14/3.31  thf('171', plain, ((v2_struct_0 @ sk_A)),
% 3.14/3.31      inference('demod', [status(thm)], ['167', '170'])).
% 3.14/3.31  thf('172', plain, ($false), inference('demod', [status(thm)], ['0', '171'])).
% 3.14/3.31  
% 3.14/3.31  % SZS output end Refutation
% 3.14/3.31  
% 3.14/3.32  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
