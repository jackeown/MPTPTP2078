%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.IozMeEY8vb

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:11:01 EST 2020

% Result     : Theorem 0.57s
% Output     : Refutation 0.57s
% Verified   : 
% Statistics : Number of formulae       :  267 (5897 expanded)
%              Number of leaves         :   36 (1710 expanded)
%              Depth                    :   25
%              Number of atoms          : 3145 (209876 expanded)
%              Number of equality atoms :   55 ( 822 expanded)
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

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k5_tmap_1_type,type,(
    k5_tmap_1: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(k2_tmap_1_type,type,(
    k2_tmap_1: $i > $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

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

thf(sk_A_type,type,(
    sk_A: $i )).

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

thf(t1_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( m1_subset_1 @ ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('2',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( m1_pre_topc @ X27 @ X28 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X27 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ~ ( l1_pre_topc @ X28 ) ) ),
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
    ! [X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ( ( u1_struct_0 @ ( k6_tmap_1 @ X23 @ X22 ) )
        = ( u1_struct_0 @ X23 ) )
      | ~ ( l1_pre_topc @ X23 )
      | ~ ( v2_pre_topc @ X23 )
      | ( v2_struct_0 @ X23 ) ) ),
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

thf('15',plain,(
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
    ! [X18: $i,X19: $i] :
      ( ~ ( l1_pre_topc @ X18 )
      | ~ ( v2_pre_topc @ X18 )
      | ( v2_struct_0 @ X18 )
      | ~ ( m1_pre_topc @ X19 @ X18 )
      | ( l1_pre_topc @ ( k8_tmap_1 @ X18 @ X19 ) ) ) ),
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
    ! [X18: $i,X19: $i] :
      ( ~ ( l1_pre_topc @ X18 )
      | ~ ( v2_pre_topc @ X18 )
      | ( v2_struct_0 @ X18 )
      | ~ ( m1_pre_topc @ X19 @ X18 )
      | ( v2_pre_topc @ ( k8_tmap_1 @ X18 @ X19 ) ) ) ),
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
    ! [X18: $i,X19: $i] :
      ( ~ ( l1_pre_topc @ X18 )
      | ~ ( v2_pre_topc @ X18 )
      | ( v2_struct_0 @ X18 )
      | ~ ( m1_pre_topc @ X19 @ X18 )
      | ( v1_pre_topc @ ( k8_tmap_1 @ X18 @ X19 ) ) ) ),
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

thf('49',plain,(
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
    ! [X20: $i,X21: $i] :
      ( ~ ( l1_pre_topc @ X20 )
      | ~ ( v2_pre_topc @ X20 )
      | ( v2_struct_0 @ X20 )
      | ~ ( m1_pre_topc @ X21 @ X20 )
      | ( m1_subset_1 @ ( k9_tmap_1 @ X20 @ X21 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X20 ) @ ( u1_struct_0 @ ( k8_tmap_1 @ X20 @ X21 ) ) ) ) ) ) ),
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

thf('57',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    m1_subset_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ) ),
    inference(clc,[status(thm)],['56','57'])).

thf('59',plain,
    ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['12','46'])).

thf('60',plain,(
    m1_subset_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['58','59'])).

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
    ! [X20: $i,X21: $i] :
      ( ~ ( l1_pre_topc @ X20 )
      | ~ ( v2_pre_topc @ X20 )
      | ( v2_struct_0 @ X20 )
      | ~ ( m1_pre_topc @ X21 @ X20 )
      | ( v1_funct_2 @ ( k9_tmap_1 @ X20 @ X21 ) @ ( u1_struct_0 @ X20 ) @ ( u1_struct_0 @ ( k8_tmap_1 @ X20 @ X21 ) ) ) ) ),
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
    ! [X20: $i,X21: $i] :
      ( ~ ( l1_pre_topc @ X20 )
      | ~ ( v2_pre_topc @ X20 )
      | ( v2_struct_0 @ X20 )
      | ~ ( m1_pre_topc @ X21 @ X20 )
      | ( v1_funct_1 @ ( k9_tmap_1 @ X20 @ X21 ) ) ) ),
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
    inference(demod,[status(thm)],['58','59'])).

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
    ! [X16: $i,X17: $i] :
      ( ~ ( l1_pre_topc @ X16 )
      | ~ ( v2_pre_topc @ X16 )
      | ( v2_struct_0 @ X16 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ( v1_funct_1 @ ( k7_tmap_1 @ X16 @ X17 ) ) ) ),
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
    ! [X16: $i,X17: $i] :
      ( ~ ( l1_pre_topc @ X16 )
      | ~ ( v2_pre_topc @ X16 )
      | ( v2_struct_0 @ X16 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ( v1_funct_2 @ ( k7_tmap_1 @ X16 @ X17 ) @ ( u1_struct_0 @ X16 ) @ ( u1_struct_0 @ ( k6_tmap_1 @ X16 @ X17 ) ) ) ) ),
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

thf('117',plain,
    ( ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['10','11'])).

thf('118',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,
    ( ( m1_subset_1 @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['116','117','118','119'])).

thf('121',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,(
    m1_subset_1 @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['120','121'])).

thf('123',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( ( k9_tmap_1 @ sk_A @ sk_B )
      = ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['96','104','113','122'])).

thf('124',plain,
    ( ( ( k9_tmap_1 @ sk_A @ sk_B )
      = ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['123'])).

thf('125',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
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

thf('126',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) )
      | ( ( u1_struct_0 @ X26 )
       != X24 )
      | ( m1_subset_1 @ ( k2_tmap_1 @ X25 @ ( k6_tmap_1 @ X25 @ X24 ) @ ( k7_tmap_1 @ X25 @ X24 ) @ X26 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X26 ) @ ( u1_struct_0 @ ( k6_tmap_1 @ X25 @ X24 ) ) ) ) )
      | ~ ( m1_pre_topc @ X26 @ X25 )
      | ( v2_struct_0 @ X26 )
      | ~ ( l1_pre_topc @ X25 )
      | ~ ( v2_pre_topc @ X25 )
      | ( v2_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t112_tmap_1])).

thf('127',plain,(
    ! [X25: $i,X26: $i] :
      ( ( v2_struct_0 @ X25 )
      | ~ ( v2_pre_topc @ X25 )
      | ~ ( l1_pre_topc @ X25 )
      | ( v2_struct_0 @ X26 )
      | ~ ( m1_pre_topc @ X26 @ X25 )
      | ( m1_subset_1 @ ( k2_tmap_1 @ X25 @ ( k6_tmap_1 @ X25 @ ( u1_struct_0 @ X26 ) ) @ ( k7_tmap_1 @ X25 @ ( u1_struct_0 @ X26 ) ) @ X26 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X26 ) @ ( u1_struct_0 @ ( k6_tmap_1 @ X25 @ ( u1_struct_0 @ X26 ) ) ) ) ) )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X26 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) ) ) ),
    inference(simplify,[status(thm)],['126'])).

thf('128',plain,
    ( ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ) ) ) )
    | ~ ( m1_pre_topc @ sk_B @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['125','127'])).

thf('129',plain,
    ( ( k8_tmap_1 @ sk_A @ sk_B )
    = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['44','45'])).

thf('130',plain,
    ( ( k8_tmap_1 @ sk_A @ sk_B )
    = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['44','45'])).

thf('131',plain,
    ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['12','46'])).

thf('132',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('133',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('134',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('135',plain,
    ( ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['128','129','130','131','132','133','134'])).

thf('136',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('137',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(clc,[status(thm)],['135','136'])).

thf('138',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('139',plain,(
    m1_subset_1 @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['137','138'])).

thf('140',plain,
    ( ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['124','139'])).

thf('141',plain,
    ( ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_B ) )
    | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) )
    | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_B ) @ sk_B @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('142',plain,
    ( ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ) )
   <= ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ) ) ),
    inference(split,[status(esa)],['141'])).

thf('143',plain,
    ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['12','46'])).

thf('144',plain,
    ( ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ) ) ),
    inference(demod,[status(thm)],['142','143'])).

thf('145',plain,
    ( ( ( k9_tmap_1 @ sk_A @ sk_B )
      = ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['123'])).

thf('146',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('147',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) )
      | ( ( u1_struct_0 @ X26 )
       != X24 )
      | ( v1_funct_2 @ ( k2_tmap_1 @ X25 @ ( k6_tmap_1 @ X25 @ X24 ) @ ( k7_tmap_1 @ X25 @ X24 ) @ X26 ) @ ( u1_struct_0 @ X26 ) @ ( u1_struct_0 @ ( k6_tmap_1 @ X25 @ X24 ) ) )
      | ~ ( m1_pre_topc @ X26 @ X25 )
      | ( v2_struct_0 @ X26 )
      | ~ ( l1_pre_topc @ X25 )
      | ~ ( v2_pre_topc @ X25 )
      | ( v2_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t112_tmap_1])).

thf('148',plain,(
    ! [X25: $i,X26: $i] :
      ( ( v2_struct_0 @ X25 )
      | ~ ( v2_pre_topc @ X25 )
      | ~ ( l1_pre_topc @ X25 )
      | ( v2_struct_0 @ X26 )
      | ~ ( m1_pre_topc @ X26 @ X25 )
      | ( v1_funct_2 @ ( k2_tmap_1 @ X25 @ ( k6_tmap_1 @ X25 @ ( u1_struct_0 @ X26 ) ) @ ( k7_tmap_1 @ X25 @ ( u1_struct_0 @ X26 ) ) @ X26 ) @ ( u1_struct_0 @ X26 ) @ ( u1_struct_0 @ ( k6_tmap_1 @ X25 @ ( u1_struct_0 @ X26 ) ) ) )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X26 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) ) ) ),
    inference(simplify,[status(thm)],['147'])).

thf('149',plain,
    ( ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( m1_pre_topc @ sk_B @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['146','148'])).

thf('150',plain,
    ( ( k8_tmap_1 @ sk_A @ sk_B )
    = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['44','45'])).

thf('151',plain,
    ( ( k8_tmap_1 @ sk_A @ sk_B )
    = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['44','45'])).

thf('152',plain,
    ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['12','46'])).

thf('153',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('154',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('155',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('156',plain,
    ( ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['149','150','151','152','153','154','155'])).

thf('157',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('158',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['156','157'])).

thf('159',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('160',plain,(
    v1_funct_2 @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['158','159'])).

thf('161',plain,
    ( ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['145','160'])).

thf('162',plain,
    ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['12','46'])).

thf('163',plain,
    ( ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) )
   <= ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['141'])).

thf('164',plain,
    ( ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['162','163'])).

thf('165',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['161','164'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('166',plain,(
    ! [X1: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X1 ) )
      | ~ ( l1_struct_0 @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('167',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['165','166'])).

thf('168',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('169',plain,(
    ! [X0: $i] :
      ( ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('170',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['168','169'])).

thf('171',plain,
    ( ( v2_struct_0 @ sk_A )
   <= ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['167','170'])).

thf('172',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('173',plain,(
    v1_funct_2 @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['171','172'])).

thf('174',plain,
    ( ( ( k9_tmap_1 @ sk_A @ sk_B )
      = ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['123'])).

thf('175',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('176',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) )
      | ( ( u1_struct_0 @ X26 )
       != X24 )
      | ( v1_funct_1 @ ( k2_tmap_1 @ X25 @ ( k6_tmap_1 @ X25 @ X24 ) @ ( k7_tmap_1 @ X25 @ X24 ) @ X26 ) )
      | ~ ( m1_pre_topc @ X26 @ X25 )
      | ( v2_struct_0 @ X26 )
      | ~ ( l1_pre_topc @ X25 )
      | ~ ( v2_pre_topc @ X25 )
      | ( v2_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t112_tmap_1])).

thf('177',plain,(
    ! [X25: $i,X26: $i] :
      ( ( v2_struct_0 @ X25 )
      | ~ ( v2_pre_topc @ X25 )
      | ~ ( l1_pre_topc @ X25 )
      | ( v2_struct_0 @ X26 )
      | ~ ( m1_pre_topc @ X26 @ X25 )
      | ( v1_funct_1 @ ( k2_tmap_1 @ X25 @ ( k6_tmap_1 @ X25 @ ( u1_struct_0 @ X26 ) ) @ ( k7_tmap_1 @ X25 @ ( u1_struct_0 @ X26 ) ) @ X26 ) )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X26 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) ) ) ),
    inference(simplify,[status(thm)],['176'])).

thf('178',plain,
    ( ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) @ sk_B ) )
    | ~ ( m1_pre_topc @ sk_B @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['175','177'])).

thf('179',plain,
    ( ( k8_tmap_1 @ sk_A @ sk_B )
    = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['44','45'])).

thf('180',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('181',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('182',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('183',plain,
    ( ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['178','179','180','181','182'])).

thf('184',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('185',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) @ sk_B ) ) ),
    inference(clc,[status(thm)],['183','184'])).

thf('186',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('187',plain,(
    v1_funct_1 @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) @ sk_B ) ),
    inference(clc,[status(thm)],['185','186'])).

thf('188',plain,
    ( ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['174','187'])).

thf('189',plain,
    ( ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_B ) )
   <= ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference(split,[status(esa)],['141'])).

thf('190',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['188','189'])).

thf('191',plain,(
    ! [X1: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X1 ) )
      | ~ ( l1_struct_0 @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('192',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['190','191'])).

thf('193',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['168','169'])).

thf('194',plain,
    ( ( v2_struct_0 @ sk_A )
   <= ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['192','193'])).

thf('195',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('196',plain,(
    v1_funct_1 @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['194','195'])).

thf('197',plain,
    ( ( ( k9_tmap_1 @ sk_A @ sk_B )
      = ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['123'])).

thf('198',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('199',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) )
      | ( ( u1_struct_0 @ X26 )
       != X24 )
      | ( v5_pre_topc @ ( k2_tmap_1 @ X25 @ ( k6_tmap_1 @ X25 @ X24 ) @ ( k7_tmap_1 @ X25 @ X24 ) @ X26 ) @ X26 @ ( k6_tmap_1 @ X25 @ X24 ) )
      | ~ ( m1_pre_topc @ X26 @ X25 )
      | ( v2_struct_0 @ X26 )
      | ~ ( l1_pre_topc @ X25 )
      | ~ ( v2_pre_topc @ X25 )
      | ( v2_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t112_tmap_1])).

thf('200',plain,(
    ! [X25: $i,X26: $i] :
      ( ( v2_struct_0 @ X25 )
      | ~ ( v2_pre_topc @ X25 )
      | ~ ( l1_pre_topc @ X25 )
      | ( v2_struct_0 @ X26 )
      | ~ ( m1_pre_topc @ X26 @ X25 )
      | ( v5_pre_topc @ ( k2_tmap_1 @ X25 @ ( k6_tmap_1 @ X25 @ ( u1_struct_0 @ X26 ) ) @ ( k7_tmap_1 @ X25 @ ( u1_struct_0 @ X26 ) ) @ X26 ) @ X26 @ ( k6_tmap_1 @ X25 @ ( u1_struct_0 @ X26 ) ) )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X26 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) ) ) ),
    inference(simplify,[status(thm)],['199'])).

thf('201',plain,
    ( ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) @ sk_B ) @ sk_B @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
    | ~ ( m1_pre_topc @ sk_B @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['198','200'])).

thf('202',plain,
    ( ( k8_tmap_1 @ sk_A @ sk_B )
    = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['44','45'])).

thf('203',plain,
    ( ( k8_tmap_1 @ sk_A @ sk_B )
    = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['44','45'])).

thf('204',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('205',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('206',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('207',plain,
    ( ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) @ sk_B ) @ sk_B @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['201','202','203','204','205','206'])).

thf('208',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('209',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) @ sk_B ) @ sk_B @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['207','208'])).

thf('210',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('211',plain,(
    v5_pre_topc @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) @ sk_B ) @ sk_B @ ( k8_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['209','210'])).

thf('212',plain,
    ( ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_B ) @ sk_B @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['197','211'])).

thf('213',plain,
    ( ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_B ) @ sk_B @ ( k8_tmap_1 @ sk_A @ sk_B ) )
   <= ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_B ) @ sk_B @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['141'])).

thf('214',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
   <= ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_B ) @ sk_B @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['212','213'])).

thf('215',plain,(
    ! [X1: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X1 ) )
      | ~ ( l1_struct_0 @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('216',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_B ) @ sk_B @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['214','215'])).

thf('217',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['168','169'])).

thf('218',plain,
    ( ( v2_struct_0 @ sk_A )
   <= ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_B ) @ sk_B @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['216','217'])).

thf('219',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('220',plain,(
    v5_pre_topc @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_B ) @ sk_B @ ( k8_tmap_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['218','219'])).

thf('221',plain,
    ( ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ) )
    | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_B ) @ sk_B @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_B ) )
    | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['141'])).

thf('222',plain,(
    ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ) ) ),
    inference('sat_resolution*',[status(thm)],['173','196','220','221'])).

thf('223',plain,(
    ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(simpl_trail,[status(thm)],['144','222'])).

thf('224',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['140','223'])).

thf('225',plain,(
    ! [X1: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X1 ) )
      | ~ ( l1_struct_0 @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('226',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['224','225'])).

thf('227',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['168','169'])).

thf('228',plain,(
    v2_struct_0 @ sk_A ),
    inference(demod,[status(thm)],['226','227'])).

thf('229',plain,(
    $false ),
    inference(demod,[status(thm)],['0','228'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.IozMeEY8vb
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:39:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.57/0.73  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.57/0.73  % Solved by: fo/fo7.sh
% 0.57/0.73  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.57/0.73  % done 234 iterations in 0.275s
% 0.57/0.73  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.57/0.73  % SZS output start Refutation
% 0.57/0.73  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.57/0.73  thf(r1_funct_2_type, type, r1_funct_2: $i > $i > $i > $i > $i > $i > $o).
% 0.57/0.73  thf(v5_pre_topc_type, type, v5_pre_topc: $i > $i > $i > $o).
% 0.57/0.73  thf(k6_tmap_1_type, type, k6_tmap_1: $i > $i > $i).
% 0.57/0.73  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 0.57/0.73  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.57/0.73  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.57/0.73  thf(k5_tmap_1_type, type, k5_tmap_1: $i > $i > $i).
% 0.57/0.73  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.57/0.73  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.57/0.73  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.57/0.73  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.57/0.73  thf(k2_tmap_1_type, type, k2_tmap_1: $i > $i > $i > $i > $i).
% 0.57/0.73  thf(sk_B_type, type, sk_B: $i).
% 0.57/0.73  thf(k7_tmap_1_type, type, k7_tmap_1: $i > $i > $i).
% 0.57/0.73  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.57/0.73  thf(k9_tmap_1_type, type, k9_tmap_1: $i > $i > $i).
% 0.57/0.73  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.57/0.73  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.57/0.73  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.57/0.73  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 0.57/0.73  thf(sk_A_type, type, sk_A: $i).
% 0.57/0.73  thf(k8_tmap_1_type, type, k8_tmap_1: $i > $i > $i).
% 0.57/0.73  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.57/0.73  thf(t121_tmap_1, conjecture,
% 0.57/0.73    (![A:$i]:
% 0.57/0.73     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.57/0.73       ( ![B:$i]:
% 0.57/0.73         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.57/0.73           ( ( v1_funct_1 @
% 0.57/0.73               ( k2_tmap_1 @
% 0.57/0.73                 A @ ( k8_tmap_1 @ A @ B ) @ ( k9_tmap_1 @ A @ B ) @ B ) ) & 
% 0.57/0.73             ( v1_funct_2 @
% 0.57/0.73               ( k2_tmap_1 @
% 0.57/0.73                 A @ ( k8_tmap_1 @ A @ B ) @ ( k9_tmap_1 @ A @ B ) @ B ) @ 
% 0.57/0.73               ( u1_struct_0 @ B ) @ ( u1_struct_0 @ ( k8_tmap_1 @ A @ B ) ) ) & 
% 0.57/0.73             ( v5_pre_topc @
% 0.57/0.73               ( k2_tmap_1 @
% 0.57/0.73                 A @ ( k8_tmap_1 @ A @ B ) @ ( k9_tmap_1 @ A @ B ) @ B ) @ 
% 0.57/0.73               B @ ( k8_tmap_1 @ A @ B ) ) & 
% 0.57/0.73             ( m1_subset_1 @
% 0.57/0.73               ( k2_tmap_1 @
% 0.57/0.73                 A @ ( k8_tmap_1 @ A @ B ) @ ( k9_tmap_1 @ A @ B ) @ B ) @ 
% 0.57/0.73               ( k1_zfmisc_1 @
% 0.57/0.73                 ( k2_zfmisc_1 @
% 0.57/0.73                   ( u1_struct_0 @ B ) @ 
% 0.57/0.73                   ( u1_struct_0 @ ( k8_tmap_1 @ A @ B ) ) ) ) ) ) ) ) ))).
% 0.57/0.73  thf(zf_stmt_0, negated_conjecture,
% 0.57/0.73    (~( ![A:$i]:
% 0.57/0.73        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.57/0.73            ( l1_pre_topc @ A ) ) =>
% 0.57/0.73          ( ![B:$i]:
% 0.57/0.73            ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.57/0.73              ( ( v1_funct_1 @
% 0.57/0.73                  ( k2_tmap_1 @
% 0.57/0.73                    A @ ( k8_tmap_1 @ A @ B ) @ ( k9_tmap_1 @ A @ B ) @ B ) ) & 
% 0.57/0.73                ( v1_funct_2 @
% 0.57/0.73                  ( k2_tmap_1 @
% 0.57/0.73                    A @ ( k8_tmap_1 @ A @ B ) @ ( k9_tmap_1 @ A @ B ) @ B ) @ 
% 0.57/0.73                  ( u1_struct_0 @ B ) @ ( u1_struct_0 @ ( k8_tmap_1 @ A @ B ) ) ) & 
% 0.57/0.73                ( v5_pre_topc @
% 0.57/0.73                  ( k2_tmap_1 @
% 0.57/0.73                    A @ ( k8_tmap_1 @ A @ B ) @ ( k9_tmap_1 @ A @ B ) @ B ) @ 
% 0.57/0.73                  B @ ( k8_tmap_1 @ A @ B ) ) & 
% 0.57/0.73                ( m1_subset_1 @
% 0.57/0.73                  ( k2_tmap_1 @
% 0.57/0.73                    A @ ( k8_tmap_1 @ A @ B ) @ ( k9_tmap_1 @ A @ B ) @ B ) @ 
% 0.57/0.73                  ( k1_zfmisc_1 @
% 0.57/0.73                    ( k2_zfmisc_1 @
% 0.57/0.73                      ( u1_struct_0 @ B ) @ 
% 0.57/0.73                      ( u1_struct_0 @ ( k8_tmap_1 @ A @ B ) ) ) ) ) ) ) ) ) )),
% 0.57/0.73    inference('cnf.neg', [status(esa)], [t121_tmap_1])).
% 0.57/0.73  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.57/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.73  thf('1', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.57/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.73  thf(t1_tsep_1, axiom,
% 0.57/0.73    (![A:$i]:
% 0.57/0.73     ( ( l1_pre_topc @ A ) =>
% 0.57/0.73       ( ![B:$i]:
% 0.57/0.73         ( ( m1_pre_topc @ B @ A ) =>
% 0.57/0.73           ( m1_subset_1 @
% 0.57/0.73             ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.57/0.73  thf('2', plain,
% 0.57/0.73      (![X27 : $i, X28 : $i]:
% 0.57/0.73         (~ (m1_pre_topc @ X27 @ X28)
% 0.57/0.73          | (m1_subset_1 @ (u1_struct_0 @ X27) @ 
% 0.57/0.73             (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 0.57/0.73          | ~ (l1_pre_topc @ X28))),
% 0.57/0.73      inference('cnf', [status(esa)], [t1_tsep_1])).
% 0.57/0.73  thf('3', plain,
% 0.57/0.73      ((~ (l1_pre_topc @ sk_A)
% 0.57/0.73        | (m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.57/0.73           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.57/0.73      inference('sup-', [status(thm)], ['1', '2'])).
% 0.57/0.73  thf('4', plain, ((l1_pre_topc @ sk_A)),
% 0.57/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.73  thf('5', plain,
% 0.57/0.73      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.57/0.73        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.57/0.73      inference('demod', [status(thm)], ['3', '4'])).
% 0.57/0.73  thf(t104_tmap_1, axiom,
% 0.57/0.73    (![A:$i]:
% 0.57/0.73     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.57/0.73       ( ![B:$i]:
% 0.57/0.73         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.57/0.73           ( ( ( u1_struct_0 @ ( k6_tmap_1 @ A @ B ) ) = ( u1_struct_0 @ A ) ) & 
% 0.57/0.73             ( ( u1_pre_topc @ ( k6_tmap_1 @ A @ B ) ) = ( k5_tmap_1 @ A @ B ) ) ) ) ) ))).
% 0.57/0.73  thf('6', plain,
% 0.57/0.73      (![X22 : $i, X23 : $i]:
% 0.57/0.73         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 0.57/0.73          | ((u1_struct_0 @ (k6_tmap_1 @ X23 @ X22)) = (u1_struct_0 @ X23))
% 0.57/0.73          | ~ (l1_pre_topc @ X23)
% 0.57/0.73          | ~ (v2_pre_topc @ X23)
% 0.57/0.73          | (v2_struct_0 @ X23))),
% 0.57/0.73      inference('cnf', [status(esa)], [t104_tmap_1])).
% 0.57/0.73  thf('7', plain,
% 0.57/0.73      (((v2_struct_0 @ sk_A)
% 0.57/0.73        | ~ (v2_pre_topc @ sk_A)
% 0.57/0.73        | ~ (l1_pre_topc @ sk_A)
% 0.57/0.73        | ((u1_struct_0 @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 0.57/0.73            = (u1_struct_0 @ sk_A)))),
% 0.57/0.73      inference('sup-', [status(thm)], ['5', '6'])).
% 0.57/0.73  thf('8', plain, ((v2_pre_topc @ sk_A)),
% 0.57/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.73  thf('9', plain, ((l1_pre_topc @ sk_A)),
% 0.57/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.73  thf('10', plain,
% 0.57/0.73      (((v2_struct_0 @ sk_A)
% 0.57/0.73        | ((u1_struct_0 @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 0.57/0.73            = (u1_struct_0 @ sk_A)))),
% 0.57/0.73      inference('demod', [status(thm)], ['7', '8', '9'])).
% 0.57/0.73  thf('11', plain, (~ (v2_struct_0 @ sk_A)),
% 0.57/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.73  thf('12', plain,
% 0.57/0.73      (((u1_struct_0 @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 0.57/0.73         = (u1_struct_0 @ sk_A))),
% 0.57/0.73      inference('clc', [status(thm)], ['10', '11'])).
% 0.57/0.73  thf('13', plain,
% 0.57/0.73      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.57/0.73        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.57/0.73      inference('demod', [status(thm)], ['3', '4'])).
% 0.57/0.73  thf(d11_tmap_1, axiom,
% 0.57/0.73    (![A:$i]:
% 0.57/0.73     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.57/0.73       ( ![B:$i]:
% 0.57/0.73         ( ( m1_pre_topc @ B @ A ) =>
% 0.57/0.73           ( ![C:$i]:
% 0.57/0.73             ( ( ( v1_pre_topc @ C ) & ( v2_pre_topc @ C ) & 
% 0.57/0.73                 ( l1_pre_topc @ C ) ) =>
% 0.57/0.73               ( ( ( C ) = ( k8_tmap_1 @ A @ B ) ) <=>
% 0.57/0.73                 ( ![D:$i]:
% 0.57/0.73                   ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.57/0.73                     ( ( ( D ) = ( u1_struct_0 @ B ) ) =>
% 0.57/0.73                       ( ( C ) = ( k6_tmap_1 @ A @ D ) ) ) ) ) ) ) ) ) ) ))).
% 0.57/0.73  thf('14', plain,
% 0.57/0.73      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.57/0.73         (~ (m1_pre_topc @ X8 @ X9)
% 0.57/0.73          | ((X10) != (k8_tmap_1 @ X9 @ X8))
% 0.57/0.73          | ((X11) != (u1_struct_0 @ X8))
% 0.57/0.73          | ((X10) = (k6_tmap_1 @ X9 @ X11))
% 0.57/0.73          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.57/0.73          | ~ (l1_pre_topc @ X10)
% 0.57/0.73          | ~ (v2_pre_topc @ X10)
% 0.57/0.73          | ~ (v1_pre_topc @ X10)
% 0.57/0.73          | ~ (l1_pre_topc @ X9)
% 0.57/0.73          | ~ (v2_pre_topc @ X9)
% 0.57/0.73          | (v2_struct_0 @ X9))),
% 0.57/0.73      inference('cnf', [status(esa)], [d11_tmap_1])).
% 0.57/0.73  thf('15', plain,
% 0.57/0.73      (![X8 : $i, X9 : $i]:
% 0.57/0.73         ((v2_struct_0 @ X9)
% 0.57/0.73          | ~ (v2_pre_topc @ X9)
% 0.57/0.73          | ~ (l1_pre_topc @ X9)
% 0.57/0.73          | ~ (v1_pre_topc @ (k8_tmap_1 @ X9 @ X8))
% 0.57/0.73          | ~ (v2_pre_topc @ (k8_tmap_1 @ X9 @ X8))
% 0.57/0.73          | ~ (l1_pre_topc @ (k8_tmap_1 @ X9 @ X8))
% 0.57/0.73          | ~ (m1_subset_1 @ (u1_struct_0 @ X8) @ 
% 0.57/0.73               (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.57/0.73          | ((k8_tmap_1 @ X9 @ X8) = (k6_tmap_1 @ X9 @ (u1_struct_0 @ X8)))
% 0.57/0.73          | ~ (m1_pre_topc @ X8 @ X9))),
% 0.57/0.73      inference('simplify', [status(thm)], ['14'])).
% 0.57/0.73  thf('16', plain,
% 0.57/0.73      ((~ (m1_pre_topc @ sk_B @ sk_A)
% 0.57/0.73        | ((k8_tmap_1 @ sk_A @ sk_B)
% 0.57/0.73            = (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 0.57/0.73        | ~ (l1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.57/0.73        | ~ (v2_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.57/0.73        | ~ (v1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.57/0.73        | ~ (l1_pre_topc @ sk_A)
% 0.57/0.73        | ~ (v2_pre_topc @ sk_A)
% 0.57/0.73        | (v2_struct_0 @ sk_A))),
% 0.57/0.73      inference('sup-', [status(thm)], ['13', '15'])).
% 0.57/0.73  thf('17', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.57/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.73  thf('18', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.57/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.73  thf(dt_k8_tmap_1, axiom,
% 0.57/0.73    (![A:$i,B:$i]:
% 0.57/0.73     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.57/0.73         ( l1_pre_topc @ A ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.57/0.73       ( ( v1_pre_topc @ ( k8_tmap_1 @ A @ B ) ) & 
% 0.57/0.73         ( v2_pre_topc @ ( k8_tmap_1 @ A @ B ) ) & 
% 0.57/0.73         ( l1_pre_topc @ ( k8_tmap_1 @ A @ B ) ) ) ))).
% 0.57/0.73  thf('19', plain,
% 0.57/0.73      (![X18 : $i, X19 : $i]:
% 0.57/0.73         (~ (l1_pre_topc @ X18)
% 0.57/0.73          | ~ (v2_pre_topc @ X18)
% 0.57/0.73          | (v2_struct_0 @ X18)
% 0.57/0.73          | ~ (m1_pre_topc @ X19 @ X18)
% 0.57/0.73          | (l1_pre_topc @ (k8_tmap_1 @ X18 @ X19)))),
% 0.57/0.73      inference('cnf', [status(esa)], [dt_k8_tmap_1])).
% 0.57/0.73  thf('20', plain,
% 0.57/0.73      (((l1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.57/0.73        | (v2_struct_0 @ sk_A)
% 0.57/0.73        | ~ (v2_pre_topc @ sk_A)
% 0.57/0.73        | ~ (l1_pre_topc @ sk_A))),
% 0.57/0.73      inference('sup-', [status(thm)], ['18', '19'])).
% 0.57/0.73  thf('21', plain, ((v2_pre_topc @ sk_A)),
% 0.57/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.73  thf('22', plain, ((l1_pre_topc @ sk_A)),
% 0.57/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.73  thf('23', plain,
% 0.57/0.73      (((l1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B)) | (v2_struct_0 @ sk_A))),
% 0.57/0.73      inference('demod', [status(thm)], ['20', '21', '22'])).
% 0.57/0.73  thf('24', plain, (~ (v2_struct_0 @ sk_A)),
% 0.57/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.73  thf('25', plain, ((l1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))),
% 0.57/0.73      inference('clc', [status(thm)], ['23', '24'])).
% 0.57/0.73  thf('26', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.57/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.73  thf('27', plain,
% 0.57/0.73      (![X18 : $i, X19 : $i]:
% 0.57/0.73         (~ (l1_pre_topc @ X18)
% 0.57/0.73          | ~ (v2_pre_topc @ X18)
% 0.57/0.73          | (v2_struct_0 @ X18)
% 0.57/0.73          | ~ (m1_pre_topc @ X19 @ X18)
% 0.57/0.73          | (v2_pre_topc @ (k8_tmap_1 @ X18 @ X19)))),
% 0.57/0.73      inference('cnf', [status(esa)], [dt_k8_tmap_1])).
% 0.57/0.73  thf('28', plain,
% 0.57/0.73      (((v2_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.57/0.73        | (v2_struct_0 @ sk_A)
% 0.57/0.73        | ~ (v2_pre_topc @ sk_A)
% 0.57/0.73        | ~ (l1_pre_topc @ sk_A))),
% 0.57/0.73      inference('sup-', [status(thm)], ['26', '27'])).
% 0.57/0.73  thf('29', plain, ((v2_pre_topc @ sk_A)),
% 0.57/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.73  thf('30', plain, ((l1_pre_topc @ sk_A)),
% 0.57/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.73  thf('31', plain,
% 0.57/0.73      (((v2_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B)) | (v2_struct_0 @ sk_A))),
% 0.57/0.73      inference('demod', [status(thm)], ['28', '29', '30'])).
% 0.57/0.73  thf('32', plain, (~ (v2_struct_0 @ sk_A)),
% 0.57/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.73  thf('33', plain, ((v2_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))),
% 0.57/0.73      inference('clc', [status(thm)], ['31', '32'])).
% 0.57/0.73  thf('34', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.57/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.73  thf('35', plain,
% 0.57/0.73      (![X18 : $i, X19 : $i]:
% 0.57/0.73         (~ (l1_pre_topc @ X18)
% 0.57/0.73          | ~ (v2_pre_topc @ X18)
% 0.57/0.73          | (v2_struct_0 @ X18)
% 0.57/0.73          | ~ (m1_pre_topc @ X19 @ X18)
% 0.57/0.73          | (v1_pre_topc @ (k8_tmap_1 @ X18 @ X19)))),
% 0.57/0.73      inference('cnf', [status(esa)], [dt_k8_tmap_1])).
% 0.57/0.73  thf('36', plain,
% 0.57/0.73      (((v1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.57/0.73        | (v2_struct_0 @ sk_A)
% 0.57/0.73        | ~ (v2_pre_topc @ sk_A)
% 0.57/0.73        | ~ (l1_pre_topc @ sk_A))),
% 0.57/0.73      inference('sup-', [status(thm)], ['34', '35'])).
% 0.57/0.73  thf('37', plain, ((v2_pre_topc @ sk_A)),
% 0.57/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.73  thf('38', plain, ((l1_pre_topc @ sk_A)),
% 0.57/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.73  thf('39', plain,
% 0.57/0.73      (((v1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B)) | (v2_struct_0 @ sk_A))),
% 0.57/0.73      inference('demod', [status(thm)], ['36', '37', '38'])).
% 0.57/0.73  thf('40', plain, (~ (v2_struct_0 @ sk_A)),
% 0.57/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.73  thf('41', plain, ((v1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))),
% 0.57/0.73      inference('clc', [status(thm)], ['39', '40'])).
% 0.57/0.73  thf('42', plain, ((l1_pre_topc @ sk_A)),
% 0.57/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.73  thf('43', plain, ((v2_pre_topc @ sk_A)),
% 0.57/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.73  thf('44', plain,
% 0.57/0.73      ((((k8_tmap_1 @ sk_A @ sk_B) = (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 0.57/0.73        | (v2_struct_0 @ sk_A))),
% 0.57/0.73      inference('demod', [status(thm)],
% 0.57/0.73                ['16', '17', '25', '33', '41', '42', '43'])).
% 0.57/0.73  thf('45', plain, (~ (v2_struct_0 @ sk_A)),
% 0.57/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.73  thf('46', plain,
% 0.57/0.73      (((k8_tmap_1 @ sk_A @ sk_B) = (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))),
% 0.57/0.73      inference('clc', [status(thm)], ['44', '45'])).
% 0.57/0.73  thf('47', plain,
% 0.57/0.73      (((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 0.57/0.73      inference('demod', [status(thm)], ['12', '46'])).
% 0.57/0.74  thf(d12_tmap_1, axiom,
% 0.57/0.74    (![A:$i]:
% 0.57/0.74     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.57/0.74       ( ![B:$i]:
% 0.57/0.74         ( ( m1_pre_topc @ B @ A ) =>
% 0.57/0.74           ( ![C:$i]:
% 0.57/0.74             ( ( ( v1_funct_1 @ C ) & 
% 0.57/0.74                 ( v1_funct_2 @
% 0.57/0.74                   C @ ( u1_struct_0 @ A ) @ 
% 0.57/0.74                   ( u1_struct_0 @ ( k8_tmap_1 @ A @ B ) ) ) & 
% 0.57/0.74                 ( m1_subset_1 @
% 0.57/0.74                   C @ 
% 0.57/0.74                   ( k1_zfmisc_1 @
% 0.57/0.74                     ( k2_zfmisc_1 @
% 0.57/0.74                       ( u1_struct_0 @ A ) @ 
% 0.57/0.74                       ( u1_struct_0 @ ( k8_tmap_1 @ A @ B ) ) ) ) ) ) =>
% 0.57/0.74               ( ( ( C ) = ( k9_tmap_1 @ A @ B ) ) <=>
% 0.57/0.74                 ( ![D:$i]:
% 0.57/0.74                   ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.57/0.74                     ( ( ( D ) = ( u1_struct_0 @ B ) ) =>
% 0.57/0.74                       ( r1_funct_2 @
% 0.57/0.74                         ( u1_struct_0 @ A ) @ 
% 0.57/0.74                         ( u1_struct_0 @ ( k8_tmap_1 @ A @ B ) ) @ 
% 0.57/0.74                         ( u1_struct_0 @ A ) @ 
% 0.57/0.74                         ( u1_struct_0 @ ( k6_tmap_1 @ A @ D ) ) @ C @ 
% 0.57/0.74                         ( k7_tmap_1 @ A @ D ) ) ) ) ) ) ) ) ) ) ))).
% 0.57/0.74  thf('48', plain,
% 0.57/0.74      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.57/0.74         (~ (m1_pre_topc @ X12 @ X13)
% 0.57/0.74          | ((X14) != (k9_tmap_1 @ X13 @ X12))
% 0.57/0.74          | ((X15) != (u1_struct_0 @ X12))
% 0.57/0.74          | (r1_funct_2 @ (u1_struct_0 @ X13) @ 
% 0.57/0.74             (u1_struct_0 @ (k8_tmap_1 @ X13 @ X12)) @ (u1_struct_0 @ X13) @ 
% 0.57/0.74             (u1_struct_0 @ (k6_tmap_1 @ X13 @ X15)) @ X14 @ 
% 0.57/0.74             (k7_tmap_1 @ X13 @ X15))
% 0.57/0.74          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.57/0.74          | ~ (m1_subset_1 @ X14 @ 
% 0.57/0.74               (k1_zfmisc_1 @ 
% 0.57/0.74                (k2_zfmisc_1 @ (u1_struct_0 @ X13) @ 
% 0.57/0.74                 (u1_struct_0 @ (k8_tmap_1 @ X13 @ X12)))))
% 0.57/0.74          | ~ (v1_funct_2 @ X14 @ (u1_struct_0 @ X13) @ 
% 0.57/0.74               (u1_struct_0 @ (k8_tmap_1 @ X13 @ X12)))
% 0.57/0.74          | ~ (v1_funct_1 @ X14)
% 0.57/0.74          | ~ (l1_pre_topc @ X13)
% 0.57/0.74          | ~ (v2_pre_topc @ X13)
% 0.57/0.74          | (v2_struct_0 @ X13))),
% 0.57/0.74      inference('cnf', [status(esa)], [d12_tmap_1])).
% 0.57/0.74  thf('49', plain,
% 0.57/0.74      (![X12 : $i, X13 : $i]:
% 0.57/0.74         ((v2_struct_0 @ X13)
% 0.57/0.74          | ~ (v2_pre_topc @ X13)
% 0.57/0.74          | ~ (l1_pre_topc @ X13)
% 0.57/0.74          | ~ (v1_funct_1 @ (k9_tmap_1 @ X13 @ X12))
% 0.57/0.74          | ~ (v1_funct_2 @ (k9_tmap_1 @ X13 @ X12) @ (u1_struct_0 @ X13) @ 
% 0.57/0.74               (u1_struct_0 @ (k8_tmap_1 @ X13 @ X12)))
% 0.57/0.74          | ~ (m1_subset_1 @ (k9_tmap_1 @ X13 @ X12) @ 
% 0.57/0.74               (k1_zfmisc_1 @ 
% 0.57/0.74                (k2_zfmisc_1 @ (u1_struct_0 @ X13) @ 
% 0.57/0.74                 (u1_struct_0 @ (k8_tmap_1 @ X13 @ X12)))))
% 0.57/0.74          | ~ (m1_subset_1 @ (u1_struct_0 @ X12) @ 
% 0.57/0.74               (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.57/0.74          | (r1_funct_2 @ (u1_struct_0 @ X13) @ 
% 0.57/0.74             (u1_struct_0 @ (k8_tmap_1 @ X13 @ X12)) @ (u1_struct_0 @ X13) @ 
% 0.57/0.74             (u1_struct_0 @ (k6_tmap_1 @ X13 @ (u1_struct_0 @ X12))) @ 
% 0.57/0.74             (k9_tmap_1 @ X13 @ X12) @ (k7_tmap_1 @ X13 @ (u1_struct_0 @ X12)))
% 0.57/0.74          | ~ (m1_pre_topc @ X12 @ X13))),
% 0.57/0.74      inference('simplify', [status(thm)], ['48'])).
% 0.57/0.74  thf('50', plain,
% 0.57/0.74      ((~ (m1_subset_1 @ (k9_tmap_1 @ sk_A @ sk_B) @ 
% 0.57/0.74           (k1_zfmisc_1 @ 
% 0.57/0.74            (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))))
% 0.57/0.74        | ~ (m1_pre_topc @ sk_B @ sk_A)
% 0.57/0.74        | (r1_funct_2 @ (u1_struct_0 @ sk_A) @ 
% 0.57/0.74           (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)) @ (u1_struct_0 @ sk_A) @ 
% 0.57/0.74           (u1_struct_0 @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B))) @ 
% 0.57/0.74           (k9_tmap_1 @ sk_A @ sk_B) @ 
% 0.57/0.74           (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 0.57/0.74        | ~ (m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.57/0.74             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.57/0.74        | ~ (v1_funct_2 @ (k9_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.57/0.74             (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))
% 0.57/0.74        | ~ (v1_funct_1 @ (k9_tmap_1 @ sk_A @ sk_B))
% 0.57/0.74        | ~ (l1_pre_topc @ sk_A)
% 0.57/0.74        | ~ (v2_pre_topc @ sk_A)
% 0.57/0.74        | (v2_struct_0 @ sk_A))),
% 0.57/0.74      inference('sup-', [status(thm)], ['47', '49'])).
% 0.57/0.74  thf('51', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.57/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.74  thf(dt_k9_tmap_1, axiom,
% 0.57/0.74    (![A:$i,B:$i]:
% 0.57/0.74     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.57/0.74         ( l1_pre_topc @ A ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.57/0.74       ( ( v1_funct_1 @ ( k9_tmap_1 @ A @ B ) ) & 
% 0.57/0.74         ( v1_funct_2 @
% 0.57/0.74           ( k9_tmap_1 @ A @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.57/0.74           ( u1_struct_0 @ ( k8_tmap_1 @ A @ B ) ) ) & 
% 0.57/0.74         ( m1_subset_1 @
% 0.57/0.74           ( k9_tmap_1 @ A @ B ) @ 
% 0.57/0.74           ( k1_zfmisc_1 @
% 0.57/0.74             ( k2_zfmisc_1 @
% 0.57/0.74               ( u1_struct_0 @ A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ A @ B ) ) ) ) ) ) ))).
% 0.57/0.74  thf('52', plain,
% 0.57/0.74      (![X20 : $i, X21 : $i]:
% 0.57/0.74         (~ (l1_pre_topc @ X20)
% 0.57/0.74          | ~ (v2_pre_topc @ X20)
% 0.57/0.74          | (v2_struct_0 @ X20)
% 0.57/0.74          | ~ (m1_pre_topc @ X21 @ X20)
% 0.57/0.74          | (m1_subset_1 @ (k9_tmap_1 @ X20 @ X21) @ 
% 0.57/0.74             (k1_zfmisc_1 @ 
% 0.57/0.74              (k2_zfmisc_1 @ (u1_struct_0 @ X20) @ 
% 0.57/0.74               (u1_struct_0 @ (k8_tmap_1 @ X20 @ X21))))))),
% 0.57/0.74      inference('cnf', [status(esa)], [dt_k9_tmap_1])).
% 0.57/0.74  thf('53', plain,
% 0.57/0.74      (((m1_subset_1 @ (k9_tmap_1 @ sk_A @ sk_B) @ 
% 0.57/0.74         (k1_zfmisc_1 @ 
% 0.57/0.74          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.57/0.74           (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))))
% 0.57/0.74        | (v2_struct_0 @ sk_A)
% 0.57/0.74        | ~ (v2_pre_topc @ sk_A)
% 0.57/0.74        | ~ (l1_pre_topc @ sk_A))),
% 0.57/0.74      inference('sup-', [status(thm)], ['51', '52'])).
% 0.57/0.74  thf('54', plain, ((v2_pre_topc @ sk_A)),
% 0.57/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.74  thf('55', plain, ((l1_pre_topc @ sk_A)),
% 0.57/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.74  thf('56', plain,
% 0.57/0.74      (((m1_subset_1 @ (k9_tmap_1 @ sk_A @ sk_B) @ 
% 0.57/0.74         (k1_zfmisc_1 @ 
% 0.57/0.74          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.57/0.74           (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))))
% 0.57/0.74        | (v2_struct_0 @ sk_A))),
% 0.57/0.74      inference('demod', [status(thm)], ['53', '54', '55'])).
% 0.57/0.74  thf('57', plain, (~ (v2_struct_0 @ sk_A)),
% 0.57/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.74  thf('58', plain,
% 0.57/0.74      ((m1_subset_1 @ (k9_tmap_1 @ sk_A @ sk_B) @ 
% 0.57/0.74        (k1_zfmisc_1 @ 
% 0.57/0.74         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.57/0.74          (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))))),
% 0.57/0.74      inference('clc', [status(thm)], ['56', '57'])).
% 0.57/0.74  thf('59', plain,
% 0.57/0.74      (((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 0.57/0.74      inference('demod', [status(thm)], ['12', '46'])).
% 0.57/0.74  thf('60', plain,
% 0.57/0.74      ((m1_subset_1 @ (k9_tmap_1 @ sk_A @ sk_B) @ 
% 0.57/0.74        (k1_zfmisc_1 @ 
% 0.57/0.74         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))))),
% 0.57/0.74      inference('demod', [status(thm)], ['58', '59'])).
% 0.57/0.74  thf('61', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.57/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.74  thf('62', plain,
% 0.57/0.74      (((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 0.57/0.74      inference('demod', [status(thm)], ['12', '46'])).
% 0.57/0.74  thf('63', plain,
% 0.57/0.74      (((k8_tmap_1 @ sk_A @ sk_B) = (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))),
% 0.57/0.74      inference('clc', [status(thm)], ['44', '45'])).
% 0.57/0.74  thf('64', plain,
% 0.57/0.74      (((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 0.57/0.74      inference('demod', [status(thm)], ['12', '46'])).
% 0.57/0.74  thf('65', plain,
% 0.57/0.74      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.57/0.74        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.57/0.74      inference('demod', [status(thm)], ['3', '4'])).
% 0.57/0.74  thf('66', plain,
% 0.57/0.74      (((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 0.57/0.74      inference('demod', [status(thm)], ['12', '46'])).
% 0.57/0.74  thf('67', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.57/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.74  thf('68', plain,
% 0.57/0.74      (![X20 : $i, X21 : $i]:
% 0.57/0.74         (~ (l1_pre_topc @ X20)
% 0.57/0.74          | ~ (v2_pre_topc @ X20)
% 0.57/0.74          | (v2_struct_0 @ X20)
% 0.57/0.74          | ~ (m1_pre_topc @ X21 @ X20)
% 0.57/0.74          | (v1_funct_2 @ (k9_tmap_1 @ X20 @ X21) @ (u1_struct_0 @ X20) @ 
% 0.57/0.74             (u1_struct_0 @ (k8_tmap_1 @ X20 @ X21))))),
% 0.57/0.74      inference('cnf', [status(esa)], [dt_k9_tmap_1])).
% 0.57/0.74  thf('69', plain,
% 0.57/0.74      (((v1_funct_2 @ (k9_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.57/0.74         (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))
% 0.57/0.74        | (v2_struct_0 @ sk_A)
% 0.57/0.74        | ~ (v2_pre_topc @ sk_A)
% 0.57/0.74        | ~ (l1_pre_topc @ sk_A))),
% 0.57/0.74      inference('sup-', [status(thm)], ['67', '68'])).
% 0.57/0.74  thf('70', plain, ((v2_pre_topc @ sk_A)),
% 0.57/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.74  thf('71', plain, ((l1_pre_topc @ sk_A)),
% 0.57/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.74  thf('72', plain,
% 0.57/0.74      (((v1_funct_2 @ (k9_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.57/0.74         (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))
% 0.57/0.74        | (v2_struct_0 @ sk_A))),
% 0.57/0.74      inference('demod', [status(thm)], ['69', '70', '71'])).
% 0.57/0.74  thf('73', plain, (~ (v2_struct_0 @ sk_A)),
% 0.57/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.74  thf('74', plain,
% 0.57/0.74      ((v1_funct_2 @ (k9_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.57/0.74        (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))),
% 0.57/0.74      inference('clc', [status(thm)], ['72', '73'])).
% 0.57/0.74  thf('75', plain,
% 0.57/0.74      (((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 0.57/0.74      inference('demod', [status(thm)], ['12', '46'])).
% 0.57/0.74  thf('76', plain,
% 0.57/0.74      ((v1_funct_2 @ (k9_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.57/0.74        (u1_struct_0 @ sk_A))),
% 0.57/0.74      inference('demod', [status(thm)], ['74', '75'])).
% 0.57/0.74  thf('77', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.57/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.74  thf('78', plain,
% 0.57/0.74      (![X20 : $i, X21 : $i]:
% 0.57/0.74         (~ (l1_pre_topc @ X20)
% 0.57/0.74          | ~ (v2_pre_topc @ X20)
% 0.57/0.74          | (v2_struct_0 @ X20)
% 0.57/0.74          | ~ (m1_pre_topc @ X21 @ X20)
% 0.57/0.74          | (v1_funct_1 @ (k9_tmap_1 @ X20 @ X21)))),
% 0.57/0.74      inference('cnf', [status(esa)], [dt_k9_tmap_1])).
% 0.57/0.74  thf('79', plain,
% 0.57/0.74      (((v1_funct_1 @ (k9_tmap_1 @ sk_A @ sk_B))
% 0.57/0.74        | (v2_struct_0 @ sk_A)
% 0.57/0.74        | ~ (v2_pre_topc @ sk_A)
% 0.57/0.74        | ~ (l1_pre_topc @ sk_A))),
% 0.57/0.74      inference('sup-', [status(thm)], ['77', '78'])).
% 0.57/0.74  thf('80', plain, ((v2_pre_topc @ sk_A)),
% 0.57/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.74  thf('81', plain, ((l1_pre_topc @ sk_A)),
% 0.57/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.74  thf('82', plain,
% 0.57/0.74      (((v1_funct_1 @ (k9_tmap_1 @ sk_A @ sk_B)) | (v2_struct_0 @ sk_A))),
% 0.57/0.74      inference('demod', [status(thm)], ['79', '80', '81'])).
% 0.57/0.74  thf('83', plain, (~ (v2_struct_0 @ sk_A)),
% 0.57/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.74  thf('84', plain, ((v1_funct_1 @ (k9_tmap_1 @ sk_A @ sk_B))),
% 0.57/0.74      inference('clc', [status(thm)], ['82', '83'])).
% 0.57/0.74  thf('85', plain, ((l1_pre_topc @ sk_A)),
% 0.57/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.74  thf('86', plain, ((v2_pre_topc @ sk_A)),
% 0.57/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.74  thf('87', plain,
% 0.57/0.74      (((r1_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.57/0.74         (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.57/0.74         (k9_tmap_1 @ sk_A @ sk_B) @ (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 0.57/0.74        | (v2_struct_0 @ sk_A))),
% 0.57/0.74      inference('demod', [status(thm)],
% 0.57/0.74                ['50', '60', '61', '62', '63', '64', '65', '66', '76', '84', 
% 0.57/0.74                 '85', '86'])).
% 0.57/0.74  thf('88', plain, (~ (v2_struct_0 @ sk_A)),
% 0.57/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.74  thf('89', plain,
% 0.57/0.74      ((r1_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.57/0.74        (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.57/0.74        (k9_tmap_1 @ sk_A @ sk_B) @ (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))),
% 0.57/0.74      inference('clc', [status(thm)], ['87', '88'])).
% 0.57/0.74  thf('90', plain,
% 0.57/0.74      ((m1_subset_1 @ (k9_tmap_1 @ sk_A @ sk_B) @ 
% 0.57/0.74        (k1_zfmisc_1 @ 
% 0.57/0.74         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))))),
% 0.57/0.74      inference('demod', [status(thm)], ['58', '59'])).
% 0.57/0.74  thf(redefinition_r1_funct_2, axiom,
% 0.57/0.74    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.57/0.74     ( ( ( ~( v1_xboole_0 @ B ) ) & ( ~( v1_xboole_0 @ D ) ) & 
% 0.57/0.74         ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ A @ B ) & 
% 0.57/0.74         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.57/0.74         ( v1_funct_1 @ F ) & ( v1_funct_2 @ F @ C @ D ) & 
% 0.57/0.74         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.57/0.74       ( ( r1_funct_2 @ A @ B @ C @ D @ E @ F ) <=> ( ( E ) = ( F ) ) ) ))).
% 0.57/0.74  thf('91', plain,
% 0.57/0.74      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.57/0.74         (~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X4)))
% 0.57/0.74          | ~ (v1_funct_2 @ X2 @ X3 @ X4)
% 0.57/0.74          | ~ (v1_funct_1 @ X2)
% 0.57/0.74          | (v1_xboole_0 @ X5)
% 0.57/0.74          | (v1_xboole_0 @ X4)
% 0.57/0.74          | ~ (v1_funct_1 @ X6)
% 0.57/0.74          | ~ (v1_funct_2 @ X6 @ X7 @ X5)
% 0.57/0.74          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X5)))
% 0.57/0.74          | ((X2) = (X6))
% 0.57/0.74          | ~ (r1_funct_2 @ X3 @ X4 @ X7 @ X5 @ X2 @ X6))),
% 0.57/0.74      inference('cnf', [status(esa)], [redefinition_r1_funct_2])).
% 0.57/0.74  thf('92', plain,
% 0.57/0.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.57/0.74         (~ (r1_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ X2 @ 
% 0.57/0.74             X1 @ (k9_tmap_1 @ sk_A @ sk_B) @ X0)
% 0.57/0.74          | ((k9_tmap_1 @ sk_A @ sk_B) = (X0))
% 0.57/0.74          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.57/0.74          | ~ (v1_funct_2 @ X0 @ X2 @ X1)
% 0.57/0.74          | ~ (v1_funct_1 @ X0)
% 0.57/0.74          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.57/0.74          | (v1_xboole_0 @ X1)
% 0.57/0.74          | ~ (v1_funct_1 @ (k9_tmap_1 @ sk_A @ sk_B))
% 0.57/0.74          | ~ (v1_funct_2 @ (k9_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.57/0.74               (u1_struct_0 @ sk_A)))),
% 0.57/0.74      inference('sup-', [status(thm)], ['90', '91'])).
% 0.57/0.74  thf('93', plain, ((v1_funct_1 @ (k9_tmap_1 @ sk_A @ sk_B))),
% 0.57/0.74      inference('clc', [status(thm)], ['82', '83'])).
% 0.57/0.74  thf('94', plain,
% 0.57/0.74      ((v1_funct_2 @ (k9_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.57/0.74        (u1_struct_0 @ sk_A))),
% 0.57/0.74      inference('demod', [status(thm)], ['74', '75'])).
% 0.57/0.74  thf('95', plain,
% 0.57/0.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.57/0.74         (~ (r1_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ X2 @ 
% 0.57/0.74             X1 @ (k9_tmap_1 @ sk_A @ sk_B) @ X0)
% 0.57/0.74          | ((k9_tmap_1 @ sk_A @ sk_B) = (X0))
% 0.57/0.74          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.57/0.74          | ~ (v1_funct_2 @ X0 @ X2 @ X1)
% 0.57/0.74          | ~ (v1_funct_1 @ X0)
% 0.57/0.74          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.57/0.74          | (v1_xboole_0 @ X1))),
% 0.57/0.74      inference('demod', [status(thm)], ['92', '93', '94'])).
% 0.57/0.74  thf('96', plain,
% 0.57/0.74      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.57/0.74        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.57/0.74        | ~ (v1_funct_1 @ (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 0.57/0.74        | ~ (v1_funct_2 @ (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)) @ 
% 0.57/0.74             (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.57/0.74        | ~ (m1_subset_1 @ (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)) @ 
% 0.57/0.74             (k1_zfmisc_1 @ 
% 0.57/0.74              (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))))
% 0.57/0.74        | ((k9_tmap_1 @ sk_A @ sk_B)
% 0.57/0.74            = (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B))))),
% 0.57/0.74      inference('sup-', [status(thm)], ['89', '95'])).
% 0.57/0.74  thf('97', plain,
% 0.57/0.74      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.57/0.74        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.57/0.74      inference('demod', [status(thm)], ['3', '4'])).
% 0.57/0.74  thf(dt_k7_tmap_1, axiom,
% 0.57/0.74    (![A:$i,B:$i]:
% 0.57/0.74     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.57/0.74         ( l1_pre_topc @ A ) & 
% 0.57/0.74         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.57/0.74       ( ( v1_funct_1 @ ( k7_tmap_1 @ A @ B ) ) & 
% 0.57/0.74         ( v1_funct_2 @
% 0.57/0.74           ( k7_tmap_1 @ A @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.57/0.74           ( u1_struct_0 @ ( k6_tmap_1 @ A @ B ) ) ) & 
% 0.57/0.74         ( m1_subset_1 @
% 0.57/0.74           ( k7_tmap_1 @ A @ B ) @ 
% 0.57/0.74           ( k1_zfmisc_1 @
% 0.57/0.74             ( k2_zfmisc_1 @
% 0.57/0.74               ( u1_struct_0 @ A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ A @ B ) ) ) ) ) ) ))).
% 0.57/0.74  thf('98', plain,
% 0.57/0.74      (![X16 : $i, X17 : $i]:
% 0.57/0.74         (~ (l1_pre_topc @ X16)
% 0.57/0.74          | ~ (v2_pre_topc @ X16)
% 0.57/0.74          | (v2_struct_0 @ X16)
% 0.57/0.74          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.57/0.74          | (v1_funct_1 @ (k7_tmap_1 @ X16 @ X17)))),
% 0.57/0.74      inference('cnf', [status(esa)], [dt_k7_tmap_1])).
% 0.57/0.74  thf('99', plain,
% 0.57/0.74      (((v1_funct_1 @ (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 0.57/0.74        | (v2_struct_0 @ sk_A)
% 0.57/0.74        | ~ (v2_pre_topc @ sk_A)
% 0.57/0.74        | ~ (l1_pre_topc @ sk_A))),
% 0.57/0.74      inference('sup-', [status(thm)], ['97', '98'])).
% 0.57/0.74  thf('100', plain, ((v2_pre_topc @ sk_A)),
% 0.57/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.74  thf('101', plain, ((l1_pre_topc @ sk_A)),
% 0.57/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.74  thf('102', plain,
% 0.57/0.74      (((v1_funct_1 @ (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 0.57/0.74        | (v2_struct_0 @ sk_A))),
% 0.57/0.74      inference('demod', [status(thm)], ['99', '100', '101'])).
% 0.57/0.74  thf('103', plain, (~ (v2_struct_0 @ sk_A)),
% 0.57/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.74  thf('104', plain, ((v1_funct_1 @ (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))),
% 0.57/0.74      inference('clc', [status(thm)], ['102', '103'])).
% 0.57/0.74  thf('105', plain,
% 0.57/0.74      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.57/0.74        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.57/0.74      inference('demod', [status(thm)], ['3', '4'])).
% 0.57/0.74  thf('106', plain,
% 0.57/0.74      (![X16 : $i, X17 : $i]:
% 0.57/0.74         (~ (l1_pre_topc @ X16)
% 0.57/0.74          | ~ (v2_pre_topc @ X16)
% 0.57/0.74          | (v2_struct_0 @ X16)
% 0.57/0.74          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.57/0.74          | (v1_funct_2 @ (k7_tmap_1 @ X16 @ X17) @ (u1_struct_0 @ X16) @ 
% 0.57/0.74             (u1_struct_0 @ (k6_tmap_1 @ X16 @ X17))))),
% 0.57/0.74      inference('cnf', [status(esa)], [dt_k7_tmap_1])).
% 0.57/0.74  thf('107', plain,
% 0.57/0.74      (((v1_funct_2 @ (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)) @ 
% 0.57/0.74         (u1_struct_0 @ sk_A) @ 
% 0.57/0.74         (u1_struct_0 @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B))))
% 0.57/0.74        | (v2_struct_0 @ sk_A)
% 0.57/0.74        | ~ (v2_pre_topc @ sk_A)
% 0.57/0.74        | ~ (l1_pre_topc @ sk_A))),
% 0.57/0.74      inference('sup-', [status(thm)], ['105', '106'])).
% 0.57/0.74  thf('108', plain,
% 0.57/0.74      (((u1_struct_0 @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 0.57/0.74         = (u1_struct_0 @ sk_A))),
% 0.57/0.74      inference('clc', [status(thm)], ['10', '11'])).
% 0.57/0.74  thf('109', plain, ((v2_pre_topc @ sk_A)),
% 0.57/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.74  thf('110', plain, ((l1_pre_topc @ sk_A)),
% 0.57/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.74  thf('111', plain,
% 0.57/0.74      (((v1_funct_2 @ (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)) @ 
% 0.57/0.74         (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.57/0.74        | (v2_struct_0 @ sk_A))),
% 0.57/0.74      inference('demod', [status(thm)], ['107', '108', '109', '110'])).
% 0.57/0.74  thf('112', plain, (~ (v2_struct_0 @ sk_A)),
% 0.57/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.74  thf('113', plain,
% 0.57/0.74      ((v1_funct_2 @ (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)) @ 
% 0.57/0.74        (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))),
% 0.57/0.74      inference('clc', [status(thm)], ['111', '112'])).
% 0.57/0.74  thf('114', plain,
% 0.57/0.74      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.57/0.74        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.57/0.74      inference('demod', [status(thm)], ['3', '4'])).
% 0.57/0.74  thf('115', plain,
% 0.57/0.74      (![X16 : $i, X17 : $i]:
% 0.57/0.74         (~ (l1_pre_topc @ X16)
% 0.57/0.74          | ~ (v2_pre_topc @ X16)
% 0.57/0.74          | (v2_struct_0 @ X16)
% 0.57/0.74          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.57/0.74          | (m1_subset_1 @ (k7_tmap_1 @ X16 @ X17) @ 
% 0.57/0.74             (k1_zfmisc_1 @ 
% 0.57/0.74              (k2_zfmisc_1 @ (u1_struct_0 @ X16) @ 
% 0.57/0.74               (u1_struct_0 @ (k6_tmap_1 @ X16 @ X17))))))),
% 0.57/0.74      inference('cnf', [status(esa)], [dt_k7_tmap_1])).
% 0.57/0.74  thf('116', plain,
% 0.57/0.74      (((m1_subset_1 @ (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)) @ 
% 0.57/0.74         (k1_zfmisc_1 @ 
% 0.57/0.74          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.57/0.74           (u1_struct_0 @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B))))))
% 0.57/0.74        | (v2_struct_0 @ sk_A)
% 0.57/0.74        | ~ (v2_pre_topc @ sk_A)
% 0.57/0.74        | ~ (l1_pre_topc @ sk_A))),
% 0.57/0.74      inference('sup-', [status(thm)], ['114', '115'])).
% 0.57/0.74  thf('117', plain,
% 0.57/0.74      (((u1_struct_0 @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 0.57/0.74         = (u1_struct_0 @ sk_A))),
% 0.57/0.74      inference('clc', [status(thm)], ['10', '11'])).
% 0.57/0.74  thf('118', plain, ((v2_pre_topc @ sk_A)),
% 0.57/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.74  thf('119', plain, ((l1_pre_topc @ sk_A)),
% 0.57/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.74  thf('120', plain,
% 0.57/0.74      (((m1_subset_1 @ (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)) @ 
% 0.57/0.74         (k1_zfmisc_1 @ 
% 0.57/0.74          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))))
% 0.57/0.74        | (v2_struct_0 @ sk_A))),
% 0.57/0.74      inference('demod', [status(thm)], ['116', '117', '118', '119'])).
% 0.57/0.74  thf('121', plain, (~ (v2_struct_0 @ sk_A)),
% 0.57/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.74  thf('122', plain,
% 0.57/0.74      ((m1_subset_1 @ (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)) @ 
% 0.57/0.74        (k1_zfmisc_1 @ 
% 0.57/0.74         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))))),
% 0.57/0.74      inference('clc', [status(thm)], ['120', '121'])).
% 0.57/0.74  thf('123', plain,
% 0.57/0.74      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.57/0.74        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.57/0.74        | ((k9_tmap_1 @ sk_A @ sk_B)
% 0.57/0.74            = (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B))))),
% 0.57/0.74      inference('demod', [status(thm)], ['96', '104', '113', '122'])).
% 0.57/0.74  thf('124', plain,
% 0.57/0.74      ((((k9_tmap_1 @ sk_A @ sk_B) = (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 0.57/0.74        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.57/0.74      inference('simplify', [status(thm)], ['123'])).
% 0.57/0.74  thf('125', plain,
% 0.57/0.74      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.57/0.74        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.57/0.74      inference('demod', [status(thm)], ['3', '4'])).
% 0.57/0.74  thf(t112_tmap_1, axiom,
% 0.57/0.74    (![A:$i]:
% 0.57/0.74     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.57/0.74       ( ![B:$i]:
% 0.57/0.74         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.57/0.74           ( ![C:$i]:
% 0.57/0.74             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.57/0.74               ( ( ( u1_struct_0 @ C ) = ( B ) ) =>
% 0.57/0.74                 ( ( v1_funct_1 @
% 0.57/0.74                     ( k2_tmap_1 @
% 0.57/0.74                       A @ ( k6_tmap_1 @ A @ B ) @ ( k7_tmap_1 @ A @ B ) @ C ) ) & 
% 0.57/0.74                   ( v1_funct_2 @
% 0.57/0.74                     ( k2_tmap_1 @
% 0.57/0.74                       A @ ( k6_tmap_1 @ A @ B ) @ ( k7_tmap_1 @ A @ B ) @ C ) @ 
% 0.57/0.74                     ( u1_struct_0 @ C ) @ 
% 0.57/0.74                     ( u1_struct_0 @ ( k6_tmap_1 @ A @ B ) ) ) & 
% 0.57/0.74                   ( v5_pre_topc @
% 0.57/0.74                     ( k2_tmap_1 @
% 0.57/0.74                       A @ ( k6_tmap_1 @ A @ B ) @ ( k7_tmap_1 @ A @ B ) @ C ) @ 
% 0.57/0.74                     C @ ( k6_tmap_1 @ A @ B ) ) & 
% 0.57/0.74                   ( m1_subset_1 @
% 0.57/0.74                     ( k2_tmap_1 @
% 0.57/0.74                       A @ ( k6_tmap_1 @ A @ B ) @ ( k7_tmap_1 @ A @ B ) @ C ) @ 
% 0.57/0.74                     ( k1_zfmisc_1 @
% 0.57/0.74                       ( k2_zfmisc_1 @
% 0.57/0.74                         ( u1_struct_0 @ C ) @ 
% 0.57/0.74                         ( u1_struct_0 @ ( k6_tmap_1 @ A @ B ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.57/0.74  thf('126', plain,
% 0.57/0.74      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.57/0.74         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 0.57/0.74          | ((u1_struct_0 @ X26) != (X24))
% 0.57/0.74          | (m1_subset_1 @ 
% 0.57/0.74             (k2_tmap_1 @ X25 @ (k6_tmap_1 @ X25 @ X24) @ 
% 0.57/0.74              (k7_tmap_1 @ X25 @ X24) @ X26) @ 
% 0.57/0.74             (k1_zfmisc_1 @ 
% 0.57/0.74              (k2_zfmisc_1 @ (u1_struct_0 @ X26) @ 
% 0.57/0.74               (u1_struct_0 @ (k6_tmap_1 @ X25 @ X24)))))
% 0.57/0.74          | ~ (m1_pre_topc @ X26 @ X25)
% 0.57/0.74          | (v2_struct_0 @ X26)
% 0.57/0.74          | ~ (l1_pre_topc @ X25)
% 0.57/0.74          | ~ (v2_pre_topc @ X25)
% 0.57/0.74          | (v2_struct_0 @ X25))),
% 0.57/0.74      inference('cnf', [status(esa)], [t112_tmap_1])).
% 0.57/0.74  thf('127', plain,
% 0.57/0.74      (![X25 : $i, X26 : $i]:
% 0.57/0.74         ((v2_struct_0 @ X25)
% 0.57/0.74          | ~ (v2_pre_topc @ X25)
% 0.57/0.74          | ~ (l1_pre_topc @ X25)
% 0.57/0.74          | (v2_struct_0 @ X26)
% 0.57/0.74          | ~ (m1_pre_topc @ X26 @ X25)
% 0.57/0.74          | (m1_subset_1 @ 
% 0.57/0.74             (k2_tmap_1 @ X25 @ (k6_tmap_1 @ X25 @ (u1_struct_0 @ X26)) @ 
% 0.57/0.74              (k7_tmap_1 @ X25 @ (u1_struct_0 @ X26)) @ X26) @ 
% 0.57/0.74             (k1_zfmisc_1 @ 
% 0.57/0.74              (k2_zfmisc_1 @ (u1_struct_0 @ X26) @ 
% 0.57/0.74               (u1_struct_0 @ (k6_tmap_1 @ X25 @ (u1_struct_0 @ X26))))))
% 0.57/0.74          | ~ (m1_subset_1 @ (u1_struct_0 @ X26) @ 
% 0.57/0.74               (k1_zfmisc_1 @ (u1_struct_0 @ X25))))),
% 0.57/0.74      inference('simplify', [status(thm)], ['126'])).
% 0.57/0.74  thf('128', plain,
% 0.57/0.74      (((m1_subset_1 @ 
% 0.57/0.74         (k2_tmap_1 @ sk_A @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)) @ 
% 0.57/0.74          (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)) @ sk_B) @ 
% 0.57/0.74         (k1_zfmisc_1 @ 
% 0.57/0.74          (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ 
% 0.57/0.74           (u1_struct_0 @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B))))))
% 0.57/0.74        | ~ (m1_pre_topc @ sk_B @ sk_A)
% 0.57/0.74        | (v2_struct_0 @ sk_B)
% 0.57/0.74        | ~ (l1_pre_topc @ sk_A)
% 0.57/0.74        | ~ (v2_pre_topc @ sk_A)
% 0.57/0.74        | (v2_struct_0 @ sk_A))),
% 0.57/0.74      inference('sup-', [status(thm)], ['125', '127'])).
% 0.57/0.74  thf('129', plain,
% 0.57/0.74      (((k8_tmap_1 @ sk_A @ sk_B) = (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))),
% 0.57/0.74      inference('clc', [status(thm)], ['44', '45'])).
% 0.57/0.74  thf('130', plain,
% 0.57/0.74      (((k8_tmap_1 @ sk_A @ sk_B) = (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))),
% 0.57/0.74      inference('clc', [status(thm)], ['44', '45'])).
% 0.57/0.74  thf('131', plain,
% 0.57/0.74      (((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 0.57/0.74      inference('demod', [status(thm)], ['12', '46'])).
% 0.57/0.74  thf('132', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.57/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.74  thf('133', plain, ((l1_pre_topc @ sk_A)),
% 0.57/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.74  thf('134', plain, ((v2_pre_topc @ sk_A)),
% 0.57/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.74  thf('135', plain,
% 0.57/0.74      (((m1_subset_1 @ 
% 0.57/0.74         (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.57/0.74          (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)) @ sk_B) @ 
% 0.57/0.74         (k1_zfmisc_1 @ 
% 0.57/0.74          (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))
% 0.57/0.74        | (v2_struct_0 @ sk_B)
% 0.57/0.74        | (v2_struct_0 @ sk_A))),
% 0.57/0.74      inference('demod', [status(thm)],
% 0.57/0.74                ['128', '129', '130', '131', '132', '133', '134'])).
% 0.57/0.74  thf('136', plain, (~ (v2_struct_0 @ sk_B)),
% 0.57/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.74  thf('137', plain,
% 0.57/0.74      (((v2_struct_0 @ sk_A)
% 0.57/0.74        | (m1_subset_1 @ 
% 0.57/0.74           (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.57/0.74            (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)) @ sk_B) @ 
% 0.57/0.74           (k1_zfmisc_1 @ 
% 0.57/0.74            (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A)))))),
% 0.57/0.74      inference('clc', [status(thm)], ['135', '136'])).
% 0.57/0.74  thf('138', plain, (~ (v2_struct_0 @ sk_A)),
% 0.57/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.74  thf('139', plain,
% 0.57/0.74      ((m1_subset_1 @ 
% 0.57/0.74        (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.57/0.74         (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)) @ sk_B) @ 
% 0.57/0.74        (k1_zfmisc_1 @ 
% 0.57/0.74         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.57/0.74      inference('clc', [status(thm)], ['137', '138'])).
% 0.57/0.74  thf('140', plain,
% 0.57/0.74      (((m1_subset_1 @ 
% 0.57/0.74         (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.57/0.74          (k9_tmap_1 @ sk_A @ sk_B) @ sk_B) @ 
% 0.57/0.74         (k1_zfmisc_1 @ 
% 0.57/0.74          (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))
% 0.57/0.74        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.57/0.74      inference('sup+', [status(thm)], ['124', '139'])).
% 0.57/0.74  thf('141', plain,
% 0.57/0.74      ((~ (v1_funct_1 @ 
% 0.57/0.74           (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.57/0.74            (k9_tmap_1 @ sk_A @ sk_B) @ sk_B))
% 0.57/0.74        | ~ (v1_funct_2 @ 
% 0.57/0.74             (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.57/0.74              (k9_tmap_1 @ sk_A @ sk_B) @ sk_B) @ 
% 0.57/0.74             (u1_struct_0 @ sk_B) @ (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))
% 0.57/0.74        | ~ (v5_pre_topc @ 
% 0.57/0.74             (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.57/0.74              (k9_tmap_1 @ sk_A @ sk_B) @ sk_B) @ 
% 0.57/0.74             sk_B @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.57/0.74        | ~ (m1_subset_1 @ 
% 0.57/0.74             (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.57/0.74              (k9_tmap_1 @ sk_A @ sk_B) @ sk_B) @ 
% 0.57/0.74             (k1_zfmisc_1 @ 
% 0.57/0.74              (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ 
% 0.57/0.74               (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B))))))),
% 0.57/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.74  thf('142', plain,
% 0.57/0.74      ((~ (m1_subset_1 @ 
% 0.57/0.74           (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.57/0.74            (k9_tmap_1 @ sk_A @ sk_B) @ sk_B) @ 
% 0.57/0.74           (k1_zfmisc_1 @ 
% 0.57/0.74            (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ 
% 0.57/0.74             (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B))))))
% 0.57/0.74         <= (~
% 0.57/0.74             ((m1_subset_1 @ 
% 0.57/0.74               (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.57/0.74                (k9_tmap_1 @ sk_A @ sk_B) @ sk_B) @ 
% 0.57/0.74               (k1_zfmisc_1 @ 
% 0.57/0.74                (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ 
% 0.57/0.74                 (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))))))),
% 0.57/0.74      inference('split', [status(esa)], ['141'])).
% 0.57/0.74  thf('143', plain,
% 0.57/0.74      (((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 0.57/0.74      inference('demod', [status(thm)], ['12', '46'])).
% 0.57/0.74  thf('144', plain,
% 0.57/0.74      ((~ (m1_subset_1 @ 
% 0.57/0.74           (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.57/0.74            (k9_tmap_1 @ sk_A @ sk_B) @ sk_B) @ 
% 0.57/0.74           (k1_zfmisc_1 @ 
% 0.57/0.74            (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A)))))
% 0.57/0.74         <= (~
% 0.57/0.74             ((m1_subset_1 @ 
% 0.57/0.74               (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.57/0.74                (k9_tmap_1 @ sk_A @ sk_B) @ sk_B) @ 
% 0.57/0.74               (k1_zfmisc_1 @ 
% 0.57/0.74                (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ 
% 0.57/0.74                 (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))))))),
% 0.57/0.74      inference('demod', [status(thm)], ['142', '143'])).
% 0.57/0.74  thf('145', plain,
% 0.57/0.74      ((((k9_tmap_1 @ sk_A @ sk_B) = (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 0.57/0.74        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.57/0.74      inference('simplify', [status(thm)], ['123'])).
% 0.57/0.74  thf('146', plain,
% 0.57/0.74      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.57/0.74        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.57/0.74      inference('demod', [status(thm)], ['3', '4'])).
% 0.57/0.74  thf('147', plain,
% 0.57/0.74      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.57/0.74         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 0.57/0.74          | ((u1_struct_0 @ X26) != (X24))
% 0.57/0.74          | (v1_funct_2 @ 
% 0.57/0.74             (k2_tmap_1 @ X25 @ (k6_tmap_1 @ X25 @ X24) @ 
% 0.57/0.74              (k7_tmap_1 @ X25 @ X24) @ X26) @ 
% 0.57/0.74             (u1_struct_0 @ X26) @ (u1_struct_0 @ (k6_tmap_1 @ X25 @ X24)))
% 0.57/0.74          | ~ (m1_pre_topc @ X26 @ X25)
% 0.57/0.74          | (v2_struct_0 @ X26)
% 0.57/0.74          | ~ (l1_pre_topc @ X25)
% 0.57/0.74          | ~ (v2_pre_topc @ X25)
% 0.57/0.74          | (v2_struct_0 @ X25))),
% 0.57/0.74      inference('cnf', [status(esa)], [t112_tmap_1])).
% 0.57/0.74  thf('148', plain,
% 0.57/0.74      (![X25 : $i, X26 : $i]:
% 0.57/0.74         ((v2_struct_0 @ X25)
% 0.57/0.74          | ~ (v2_pre_topc @ X25)
% 0.57/0.74          | ~ (l1_pre_topc @ X25)
% 0.57/0.74          | (v2_struct_0 @ X26)
% 0.57/0.74          | ~ (m1_pre_topc @ X26 @ X25)
% 0.57/0.74          | (v1_funct_2 @ 
% 0.57/0.74             (k2_tmap_1 @ X25 @ (k6_tmap_1 @ X25 @ (u1_struct_0 @ X26)) @ 
% 0.57/0.74              (k7_tmap_1 @ X25 @ (u1_struct_0 @ X26)) @ X26) @ 
% 0.57/0.74             (u1_struct_0 @ X26) @ 
% 0.57/0.74             (u1_struct_0 @ (k6_tmap_1 @ X25 @ (u1_struct_0 @ X26))))
% 0.57/0.74          | ~ (m1_subset_1 @ (u1_struct_0 @ X26) @ 
% 0.57/0.74               (k1_zfmisc_1 @ (u1_struct_0 @ X25))))),
% 0.57/0.74      inference('simplify', [status(thm)], ['147'])).
% 0.57/0.74  thf('149', plain,
% 0.57/0.74      (((v1_funct_2 @ 
% 0.57/0.74         (k2_tmap_1 @ sk_A @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)) @ 
% 0.57/0.74          (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)) @ sk_B) @ 
% 0.57/0.74         (u1_struct_0 @ sk_B) @ 
% 0.57/0.74         (u1_struct_0 @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B))))
% 0.57/0.74        | ~ (m1_pre_topc @ sk_B @ sk_A)
% 0.57/0.74        | (v2_struct_0 @ sk_B)
% 0.57/0.74        | ~ (l1_pre_topc @ sk_A)
% 0.57/0.74        | ~ (v2_pre_topc @ sk_A)
% 0.57/0.74        | (v2_struct_0 @ sk_A))),
% 0.57/0.74      inference('sup-', [status(thm)], ['146', '148'])).
% 0.57/0.74  thf('150', plain,
% 0.57/0.74      (((k8_tmap_1 @ sk_A @ sk_B) = (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))),
% 0.57/0.74      inference('clc', [status(thm)], ['44', '45'])).
% 0.57/0.74  thf('151', plain,
% 0.57/0.74      (((k8_tmap_1 @ sk_A @ sk_B) = (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))),
% 0.57/0.74      inference('clc', [status(thm)], ['44', '45'])).
% 0.57/0.74  thf('152', plain,
% 0.57/0.74      (((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 0.57/0.74      inference('demod', [status(thm)], ['12', '46'])).
% 0.57/0.74  thf('153', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.57/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.74  thf('154', plain, ((l1_pre_topc @ sk_A)),
% 0.57/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.74  thf('155', plain, ((v2_pre_topc @ sk_A)),
% 0.57/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.74  thf('156', plain,
% 0.57/0.74      (((v1_funct_2 @ 
% 0.57/0.74         (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.57/0.74          (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)) @ sk_B) @ 
% 0.57/0.74         (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.57/0.74        | (v2_struct_0 @ sk_B)
% 0.57/0.74        | (v2_struct_0 @ sk_A))),
% 0.57/0.74      inference('demod', [status(thm)],
% 0.57/0.74                ['149', '150', '151', '152', '153', '154', '155'])).
% 0.57/0.74  thf('157', plain, (~ (v2_struct_0 @ sk_B)),
% 0.57/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.74  thf('158', plain,
% 0.57/0.74      (((v2_struct_0 @ sk_A)
% 0.57/0.74        | (v1_funct_2 @ 
% 0.57/0.74           (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.57/0.74            (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)) @ sk_B) @ 
% 0.57/0.74           (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 0.57/0.74      inference('clc', [status(thm)], ['156', '157'])).
% 0.57/0.74  thf('159', plain, (~ (v2_struct_0 @ sk_A)),
% 0.57/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.74  thf('160', plain,
% 0.57/0.74      ((v1_funct_2 @ 
% 0.57/0.74        (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.57/0.74         (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)) @ sk_B) @ 
% 0.57/0.74        (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.57/0.74      inference('clc', [status(thm)], ['158', '159'])).
% 0.57/0.74  thf('161', plain,
% 0.57/0.74      (((v1_funct_2 @ 
% 0.57/0.74         (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.57/0.74          (k9_tmap_1 @ sk_A @ sk_B) @ sk_B) @ 
% 0.57/0.74         (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.57/0.74        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.57/0.74      inference('sup+', [status(thm)], ['145', '160'])).
% 0.57/0.74  thf('162', plain,
% 0.57/0.74      (((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 0.57/0.74      inference('demod', [status(thm)], ['12', '46'])).
% 0.57/0.74  thf('163', plain,
% 0.57/0.74      ((~ (v1_funct_2 @ 
% 0.57/0.74           (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.57/0.74            (k9_tmap_1 @ sk_A @ sk_B) @ sk_B) @ 
% 0.57/0.74           (u1_struct_0 @ sk_B) @ (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B))))
% 0.57/0.74         <= (~
% 0.57/0.74             ((v1_funct_2 @ 
% 0.57/0.74               (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.57/0.74                (k9_tmap_1 @ sk_A @ sk_B) @ sk_B) @ 
% 0.57/0.74               (u1_struct_0 @ sk_B) @ (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))))),
% 0.57/0.74      inference('split', [status(esa)], ['141'])).
% 0.57/0.74  thf('164', plain,
% 0.57/0.74      ((~ (v1_funct_2 @ 
% 0.57/0.74           (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.57/0.74            (k9_tmap_1 @ sk_A @ sk_B) @ sk_B) @ 
% 0.57/0.74           (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A)))
% 0.57/0.74         <= (~
% 0.57/0.74             ((v1_funct_2 @ 
% 0.57/0.74               (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.57/0.74                (k9_tmap_1 @ sk_A @ sk_B) @ sk_B) @ 
% 0.57/0.74               (u1_struct_0 @ sk_B) @ (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))))),
% 0.57/0.74      inference('sup-', [status(thm)], ['162', '163'])).
% 0.57/0.74  thf('165', plain,
% 0.57/0.74      (((v1_xboole_0 @ (u1_struct_0 @ sk_A)))
% 0.57/0.74         <= (~
% 0.57/0.74             ((v1_funct_2 @ 
% 0.57/0.74               (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.57/0.74                (k9_tmap_1 @ sk_A @ sk_B) @ sk_B) @ 
% 0.57/0.74               (u1_struct_0 @ sk_B) @ (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))))),
% 0.57/0.74      inference('sup-', [status(thm)], ['161', '164'])).
% 0.57/0.74  thf(fc2_struct_0, axiom,
% 0.57/0.74    (![A:$i]:
% 0.57/0.74     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.57/0.74       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.57/0.74  thf('166', plain,
% 0.57/0.74      (![X1 : $i]:
% 0.57/0.74         (~ (v1_xboole_0 @ (u1_struct_0 @ X1))
% 0.57/0.74          | ~ (l1_struct_0 @ X1)
% 0.57/0.74          | (v2_struct_0 @ X1))),
% 0.57/0.74      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.57/0.74  thf('167', plain,
% 0.57/0.74      ((((v2_struct_0 @ sk_A) | ~ (l1_struct_0 @ sk_A)))
% 0.57/0.74         <= (~
% 0.57/0.74             ((v1_funct_2 @ 
% 0.57/0.74               (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.57/0.74                (k9_tmap_1 @ sk_A @ sk_B) @ sk_B) @ 
% 0.57/0.74               (u1_struct_0 @ sk_B) @ (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))))),
% 0.57/0.74      inference('sup-', [status(thm)], ['165', '166'])).
% 0.57/0.74  thf('168', plain, ((l1_pre_topc @ sk_A)),
% 0.57/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.74  thf(dt_l1_pre_topc, axiom,
% 0.57/0.74    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.57/0.74  thf('169', plain, (![X0 : $i]: ((l1_struct_0 @ X0) | ~ (l1_pre_topc @ X0))),
% 0.57/0.74      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.57/0.74  thf('170', plain, ((l1_struct_0 @ sk_A)),
% 0.57/0.74      inference('sup-', [status(thm)], ['168', '169'])).
% 0.57/0.74  thf('171', plain,
% 0.57/0.74      (((v2_struct_0 @ sk_A))
% 0.57/0.74         <= (~
% 0.57/0.74             ((v1_funct_2 @ 
% 0.57/0.74               (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.57/0.74                (k9_tmap_1 @ sk_A @ sk_B) @ sk_B) @ 
% 0.57/0.74               (u1_struct_0 @ sk_B) @ (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))))),
% 0.57/0.74      inference('demod', [status(thm)], ['167', '170'])).
% 0.57/0.74  thf('172', plain, (~ (v2_struct_0 @ sk_A)),
% 0.57/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.74  thf('173', plain,
% 0.57/0.74      (((v1_funct_2 @ 
% 0.57/0.74         (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.57/0.74          (k9_tmap_1 @ sk_A @ sk_B) @ sk_B) @ 
% 0.57/0.74         (u1_struct_0 @ sk_B) @ (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B))))),
% 0.57/0.74      inference('sup-', [status(thm)], ['171', '172'])).
% 0.57/0.74  thf('174', plain,
% 0.57/0.74      ((((k9_tmap_1 @ sk_A @ sk_B) = (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 0.57/0.74        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.57/0.74      inference('simplify', [status(thm)], ['123'])).
% 0.57/0.74  thf('175', plain,
% 0.57/0.74      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.57/0.74        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.57/0.74      inference('demod', [status(thm)], ['3', '4'])).
% 0.57/0.74  thf('176', plain,
% 0.57/0.74      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.57/0.74         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 0.57/0.74          | ((u1_struct_0 @ X26) != (X24))
% 0.57/0.74          | (v1_funct_1 @ 
% 0.57/0.74             (k2_tmap_1 @ X25 @ (k6_tmap_1 @ X25 @ X24) @ 
% 0.57/0.74              (k7_tmap_1 @ X25 @ X24) @ X26))
% 0.57/0.74          | ~ (m1_pre_topc @ X26 @ X25)
% 0.57/0.74          | (v2_struct_0 @ X26)
% 0.57/0.74          | ~ (l1_pre_topc @ X25)
% 0.57/0.74          | ~ (v2_pre_topc @ X25)
% 0.57/0.74          | (v2_struct_0 @ X25))),
% 0.57/0.74      inference('cnf', [status(esa)], [t112_tmap_1])).
% 0.57/0.74  thf('177', plain,
% 0.57/0.74      (![X25 : $i, X26 : $i]:
% 0.57/0.74         ((v2_struct_0 @ X25)
% 0.57/0.74          | ~ (v2_pre_topc @ X25)
% 0.57/0.74          | ~ (l1_pre_topc @ X25)
% 0.57/0.74          | (v2_struct_0 @ X26)
% 0.57/0.74          | ~ (m1_pre_topc @ X26 @ X25)
% 0.57/0.74          | (v1_funct_1 @ 
% 0.57/0.74             (k2_tmap_1 @ X25 @ (k6_tmap_1 @ X25 @ (u1_struct_0 @ X26)) @ 
% 0.57/0.74              (k7_tmap_1 @ X25 @ (u1_struct_0 @ X26)) @ X26))
% 0.57/0.74          | ~ (m1_subset_1 @ (u1_struct_0 @ X26) @ 
% 0.57/0.74               (k1_zfmisc_1 @ (u1_struct_0 @ X25))))),
% 0.57/0.74      inference('simplify', [status(thm)], ['176'])).
% 0.57/0.74  thf('178', plain,
% 0.57/0.74      (((v1_funct_1 @ 
% 0.57/0.74         (k2_tmap_1 @ sk_A @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)) @ 
% 0.57/0.74          (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)) @ sk_B))
% 0.57/0.74        | ~ (m1_pre_topc @ sk_B @ sk_A)
% 0.57/0.74        | (v2_struct_0 @ sk_B)
% 0.57/0.74        | ~ (l1_pre_topc @ sk_A)
% 0.57/0.74        | ~ (v2_pre_topc @ sk_A)
% 0.57/0.74        | (v2_struct_0 @ sk_A))),
% 0.57/0.74      inference('sup-', [status(thm)], ['175', '177'])).
% 0.57/0.74  thf('179', plain,
% 0.57/0.74      (((k8_tmap_1 @ sk_A @ sk_B) = (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))),
% 0.57/0.74      inference('clc', [status(thm)], ['44', '45'])).
% 0.57/0.74  thf('180', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.57/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.74  thf('181', plain, ((l1_pre_topc @ sk_A)),
% 0.57/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.74  thf('182', plain, ((v2_pre_topc @ sk_A)),
% 0.57/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.74  thf('183', plain,
% 0.57/0.74      (((v1_funct_1 @ 
% 0.57/0.74         (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.57/0.74          (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)) @ sk_B))
% 0.57/0.74        | (v2_struct_0 @ sk_B)
% 0.57/0.74        | (v2_struct_0 @ sk_A))),
% 0.57/0.74      inference('demod', [status(thm)], ['178', '179', '180', '181', '182'])).
% 0.57/0.74  thf('184', plain, (~ (v2_struct_0 @ sk_B)),
% 0.57/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.74  thf('185', plain,
% 0.57/0.74      (((v2_struct_0 @ sk_A)
% 0.57/0.74        | (v1_funct_1 @ 
% 0.57/0.74           (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.57/0.74            (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)) @ sk_B)))),
% 0.57/0.74      inference('clc', [status(thm)], ['183', '184'])).
% 0.57/0.74  thf('186', plain, (~ (v2_struct_0 @ sk_A)),
% 0.57/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.74  thf('187', plain,
% 0.57/0.74      ((v1_funct_1 @ 
% 0.57/0.74        (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.57/0.74         (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)) @ sk_B))),
% 0.57/0.74      inference('clc', [status(thm)], ['185', '186'])).
% 0.57/0.74  thf('188', plain,
% 0.57/0.74      (((v1_funct_1 @ 
% 0.57/0.74         (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.57/0.74          (k9_tmap_1 @ sk_A @ sk_B) @ sk_B))
% 0.57/0.74        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.57/0.74      inference('sup+', [status(thm)], ['174', '187'])).
% 0.57/0.74  thf('189', plain,
% 0.57/0.74      ((~ (v1_funct_1 @ 
% 0.57/0.74           (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.57/0.74            (k9_tmap_1 @ sk_A @ sk_B) @ sk_B)))
% 0.57/0.74         <= (~
% 0.57/0.74             ((v1_funct_1 @ 
% 0.57/0.74               (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.57/0.74                (k9_tmap_1 @ sk_A @ sk_B) @ sk_B))))),
% 0.57/0.74      inference('split', [status(esa)], ['141'])).
% 0.57/0.74  thf('190', plain,
% 0.57/0.74      (((v1_xboole_0 @ (u1_struct_0 @ sk_A)))
% 0.57/0.74         <= (~
% 0.57/0.74             ((v1_funct_1 @ 
% 0.57/0.74               (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.57/0.74                (k9_tmap_1 @ sk_A @ sk_B) @ sk_B))))),
% 0.57/0.74      inference('sup-', [status(thm)], ['188', '189'])).
% 0.57/0.74  thf('191', plain,
% 0.57/0.74      (![X1 : $i]:
% 0.57/0.74         (~ (v1_xboole_0 @ (u1_struct_0 @ X1))
% 0.57/0.74          | ~ (l1_struct_0 @ X1)
% 0.57/0.74          | (v2_struct_0 @ X1))),
% 0.57/0.74      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.57/0.74  thf('192', plain,
% 0.57/0.74      ((((v2_struct_0 @ sk_A) | ~ (l1_struct_0 @ sk_A)))
% 0.57/0.74         <= (~
% 0.57/0.74             ((v1_funct_1 @ 
% 0.57/0.74               (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.57/0.74                (k9_tmap_1 @ sk_A @ sk_B) @ sk_B))))),
% 0.57/0.74      inference('sup-', [status(thm)], ['190', '191'])).
% 0.57/0.74  thf('193', plain, ((l1_struct_0 @ sk_A)),
% 0.57/0.74      inference('sup-', [status(thm)], ['168', '169'])).
% 0.57/0.74  thf('194', plain,
% 0.57/0.74      (((v2_struct_0 @ sk_A))
% 0.57/0.74         <= (~
% 0.57/0.74             ((v1_funct_1 @ 
% 0.57/0.74               (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.57/0.74                (k9_tmap_1 @ sk_A @ sk_B) @ sk_B))))),
% 0.57/0.74      inference('demod', [status(thm)], ['192', '193'])).
% 0.57/0.74  thf('195', plain, (~ (v2_struct_0 @ sk_A)),
% 0.57/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.74  thf('196', plain,
% 0.57/0.74      (((v1_funct_1 @ 
% 0.57/0.74         (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.57/0.74          (k9_tmap_1 @ sk_A @ sk_B) @ sk_B)))),
% 0.57/0.74      inference('sup-', [status(thm)], ['194', '195'])).
% 0.57/0.74  thf('197', plain,
% 0.57/0.74      ((((k9_tmap_1 @ sk_A @ sk_B) = (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 0.57/0.74        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.57/0.74      inference('simplify', [status(thm)], ['123'])).
% 0.57/0.74  thf('198', plain,
% 0.57/0.74      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.57/0.74        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.57/0.74      inference('demod', [status(thm)], ['3', '4'])).
% 0.57/0.74  thf('199', plain,
% 0.57/0.74      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.57/0.74         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 0.57/0.74          | ((u1_struct_0 @ X26) != (X24))
% 0.57/0.74          | (v5_pre_topc @ 
% 0.57/0.74             (k2_tmap_1 @ X25 @ (k6_tmap_1 @ X25 @ X24) @ 
% 0.57/0.74              (k7_tmap_1 @ X25 @ X24) @ X26) @ 
% 0.57/0.74             X26 @ (k6_tmap_1 @ X25 @ X24))
% 0.57/0.74          | ~ (m1_pre_topc @ X26 @ X25)
% 0.57/0.74          | (v2_struct_0 @ X26)
% 0.57/0.74          | ~ (l1_pre_topc @ X25)
% 0.57/0.74          | ~ (v2_pre_topc @ X25)
% 0.57/0.74          | (v2_struct_0 @ X25))),
% 0.57/0.74      inference('cnf', [status(esa)], [t112_tmap_1])).
% 0.57/0.74  thf('200', plain,
% 0.57/0.74      (![X25 : $i, X26 : $i]:
% 0.57/0.74         ((v2_struct_0 @ X25)
% 0.57/0.74          | ~ (v2_pre_topc @ X25)
% 0.57/0.74          | ~ (l1_pre_topc @ X25)
% 0.57/0.74          | (v2_struct_0 @ X26)
% 0.57/0.74          | ~ (m1_pre_topc @ X26 @ X25)
% 0.57/0.74          | (v5_pre_topc @ 
% 0.57/0.74             (k2_tmap_1 @ X25 @ (k6_tmap_1 @ X25 @ (u1_struct_0 @ X26)) @ 
% 0.57/0.74              (k7_tmap_1 @ X25 @ (u1_struct_0 @ X26)) @ X26) @ 
% 0.57/0.74             X26 @ (k6_tmap_1 @ X25 @ (u1_struct_0 @ X26)))
% 0.57/0.74          | ~ (m1_subset_1 @ (u1_struct_0 @ X26) @ 
% 0.57/0.74               (k1_zfmisc_1 @ (u1_struct_0 @ X25))))),
% 0.57/0.74      inference('simplify', [status(thm)], ['199'])).
% 0.57/0.74  thf('201', plain,
% 0.57/0.74      (((v5_pre_topc @ 
% 0.57/0.74         (k2_tmap_1 @ sk_A @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)) @ 
% 0.57/0.74          (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)) @ sk_B) @ 
% 0.57/0.74         sk_B @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 0.57/0.74        | ~ (m1_pre_topc @ sk_B @ sk_A)
% 0.57/0.74        | (v2_struct_0 @ sk_B)
% 0.57/0.74        | ~ (l1_pre_topc @ sk_A)
% 0.57/0.74        | ~ (v2_pre_topc @ sk_A)
% 0.57/0.74        | (v2_struct_0 @ sk_A))),
% 0.57/0.74      inference('sup-', [status(thm)], ['198', '200'])).
% 0.57/0.74  thf('202', plain,
% 0.57/0.74      (((k8_tmap_1 @ sk_A @ sk_B) = (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))),
% 0.57/0.74      inference('clc', [status(thm)], ['44', '45'])).
% 0.57/0.74  thf('203', plain,
% 0.57/0.74      (((k8_tmap_1 @ sk_A @ sk_B) = (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))),
% 0.57/0.74      inference('clc', [status(thm)], ['44', '45'])).
% 0.57/0.74  thf('204', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.57/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.74  thf('205', plain, ((l1_pre_topc @ sk_A)),
% 0.57/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.74  thf('206', plain, ((v2_pre_topc @ sk_A)),
% 0.57/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.74  thf('207', plain,
% 0.57/0.74      (((v5_pre_topc @ 
% 0.57/0.74         (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.57/0.74          (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)) @ sk_B) @ 
% 0.57/0.74         sk_B @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.57/0.74        | (v2_struct_0 @ sk_B)
% 0.57/0.74        | (v2_struct_0 @ sk_A))),
% 0.57/0.74      inference('demod', [status(thm)],
% 0.57/0.74                ['201', '202', '203', '204', '205', '206'])).
% 0.57/0.74  thf('208', plain, (~ (v2_struct_0 @ sk_B)),
% 0.57/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.74  thf('209', plain,
% 0.57/0.74      (((v2_struct_0 @ sk_A)
% 0.57/0.74        | (v5_pre_topc @ 
% 0.57/0.74           (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.57/0.74            (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)) @ sk_B) @ 
% 0.57/0.74           sk_B @ (k8_tmap_1 @ sk_A @ sk_B)))),
% 0.57/0.74      inference('clc', [status(thm)], ['207', '208'])).
% 0.57/0.74  thf('210', plain, (~ (v2_struct_0 @ sk_A)),
% 0.57/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.74  thf('211', plain,
% 0.57/0.74      ((v5_pre_topc @ 
% 0.57/0.74        (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.57/0.74         (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)) @ sk_B) @ 
% 0.57/0.74        sk_B @ (k8_tmap_1 @ sk_A @ sk_B))),
% 0.57/0.74      inference('clc', [status(thm)], ['209', '210'])).
% 0.57/0.74  thf('212', plain,
% 0.57/0.74      (((v5_pre_topc @ 
% 0.57/0.74         (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.57/0.74          (k9_tmap_1 @ sk_A @ sk_B) @ sk_B) @ 
% 0.57/0.74         sk_B @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.57/0.74        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.57/0.74      inference('sup+', [status(thm)], ['197', '211'])).
% 0.57/0.74  thf('213', plain,
% 0.57/0.74      ((~ (v5_pre_topc @ 
% 0.57/0.74           (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.57/0.74            (k9_tmap_1 @ sk_A @ sk_B) @ sk_B) @ 
% 0.57/0.74           sk_B @ (k8_tmap_1 @ sk_A @ sk_B)))
% 0.57/0.74         <= (~
% 0.57/0.74             ((v5_pre_topc @ 
% 0.57/0.74               (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.57/0.74                (k9_tmap_1 @ sk_A @ sk_B) @ sk_B) @ 
% 0.57/0.74               sk_B @ (k8_tmap_1 @ sk_A @ sk_B))))),
% 0.57/0.74      inference('split', [status(esa)], ['141'])).
% 0.57/0.74  thf('214', plain,
% 0.57/0.74      (((v1_xboole_0 @ (u1_struct_0 @ sk_A)))
% 0.57/0.74         <= (~
% 0.57/0.74             ((v5_pre_topc @ 
% 0.57/0.74               (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.57/0.74                (k9_tmap_1 @ sk_A @ sk_B) @ sk_B) @ 
% 0.57/0.74               sk_B @ (k8_tmap_1 @ sk_A @ sk_B))))),
% 0.57/0.74      inference('sup-', [status(thm)], ['212', '213'])).
% 0.57/0.74  thf('215', plain,
% 0.57/0.74      (![X1 : $i]:
% 0.57/0.74         (~ (v1_xboole_0 @ (u1_struct_0 @ X1))
% 0.57/0.74          | ~ (l1_struct_0 @ X1)
% 0.57/0.74          | (v2_struct_0 @ X1))),
% 0.57/0.74      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.57/0.74  thf('216', plain,
% 0.57/0.74      ((((v2_struct_0 @ sk_A) | ~ (l1_struct_0 @ sk_A)))
% 0.57/0.74         <= (~
% 0.57/0.74             ((v5_pre_topc @ 
% 0.57/0.74               (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.57/0.74                (k9_tmap_1 @ sk_A @ sk_B) @ sk_B) @ 
% 0.57/0.74               sk_B @ (k8_tmap_1 @ sk_A @ sk_B))))),
% 0.57/0.74      inference('sup-', [status(thm)], ['214', '215'])).
% 0.57/0.74  thf('217', plain, ((l1_struct_0 @ sk_A)),
% 0.57/0.74      inference('sup-', [status(thm)], ['168', '169'])).
% 0.57/0.74  thf('218', plain,
% 0.57/0.74      (((v2_struct_0 @ sk_A))
% 0.57/0.74         <= (~
% 0.57/0.74             ((v5_pre_topc @ 
% 0.57/0.74               (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.57/0.74                (k9_tmap_1 @ sk_A @ sk_B) @ sk_B) @ 
% 0.57/0.74               sk_B @ (k8_tmap_1 @ sk_A @ sk_B))))),
% 0.57/0.74      inference('demod', [status(thm)], ['216', '217'])).
% 0.57/0.74  thf('219', plain, (~ (v2_struct_0 @ sk_A)),
% 0.57/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.74  thf('220', plain,
% 0.57/0.74      (((v5_pre_topc @ 
% 0.57/0.74         (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.57/0.74          (k9_tmap_1 @ sk_A @ sk_B) @ sk_B) @ 
% 0.57/0.74         sk_B @ (k8_tmap_1 @ sk_A @ sk_B)))),
% 0.57/0.74      inference('sup-', [status(thm)], ['218', '219'])).
% 0.57/0.74  thf('221', plain,
% 0.57/0.74      (~
% 0.57/0.74       ((m1_subset_1 @ 
% 0.57/0.74         (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.57/0.74          (k9_tmap_1 @ sk_A @ sk_B) @ sk_B) @ 
% 0.57/0.74         (k1_zfmisc_1 @ 
% 0.57/0.74          (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ 
% 0.57/0.74           (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))))) | 
% 0.57/0.74       ~
% 0.57/0.74       ((v5_pre_topc @ 
% 0.57/0.74         (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.57/0.74          (k9_tmap_1 @ sk_A @ sk_B) @ sk_B) @ 
% 0.57/0.74         sk_B @ (k8_tmap_1 @ sk_A @ sk_B))) | 
% 0.57/0.74       ~
% 0.57/0.74       ((v1_funct_1 @ 
% 0.57/0.74         (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.57/0.74          (k9_tmap_1 @ sk_A @ sk_B) @ sk_B))) | 
% 0.57/0.74       ~
% 0.57/0.74       ((v1_funct_2 @ 
% 0.57/0.74         (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.57/0.74          (k9_tmap_1 @ sk_A @ sk_B) @ sk_B) @ 
% 0.57/0.74         (u1_struct_0 @ sk_B) @ (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B))))),
% 0.57/0.74      inference('split', [status(esa)], ['141'])).
% 0.57/0.74  thf('222', plain,
% 0.57/0.74      (~
% 0.57/0.74       ((m1_subset_1 @ 
% 0.57/0.74         (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.57/0.74          (k9_tmap_1 @ sk_A @ sk_B) @ sk_B) @ 
% 0.57/0.74         (k1_zfmisc_1 @ 
% 0.57/0.74          (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ 
% 0.57/0.74           (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B))))))),
% 0.57/0.74      inference('sat_resolution*', [status(thm)], ['173', '196', '220', '221'])).
% 0.57/0.74  thf('223', plain,
% 0.57/0.74      (~ (m1_subset_1 @ 
% 0.57/0.74          (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.57/0.74           (k9_tmap_1 @ sk_A @ sk_B) @ sk_B) @ 
% 0.57/0.74          (k1_zfmisc_1 @ 
% 0.57/0.74           (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.57/0.74      inference('simpl_trail', [status(thm)], ['144', '222'])).
% 0.57/0.74  thf('224', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.57/0.74      inference('clc', [status(thm)], ['140', '223'])).
% 0.57/0.74  thf('225', plain,
% 0.57/0.74      (![X1 : $i]:
% 0.57/0.74         (~ (v1_xboole_0 @ (u1_struct_0 @ X1))
% 0.57/0.74          | ~ (l1_struct_0 @ X1)
% 0.57/0.74          | (v2_struct_0 @ X1))),
% 0.57/0.74      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.57/0.74  thf('226', plain, (((v2_struct_0 @ sk_A) | ~ (l1_struct_0 @ sk_A))),
% 0.57/0.74      inference('sup-', [status(thm)], ['224', '225'])).
% 0.57/0.74  thf('227', plain, ((l1_struct_0 @ sk_A)),
% 0.57/0.74      inference('sup-', [status(thm)], ['168', '169'])).
% 0.57/0.74  thf('228', plain, ((v2_struct_0 @ sk_A)),
% 0.57/0.74      inference('demod', [status(thm)], ['226', '227'])).
% 0.57/0.74  thf('229', plain, ($false), inference('demod', [status(thm)], ['0', '228'])).
% 0.57/0.74  
% 0.57/0.74  % SZS output end Refutation
% 0.57/0.74  
% 0.57/0.74  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
