%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.qZUOF0CE2R

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:10:58 EST 2020

% Result     : Theorem 3.03s
% Output     : Refutation 3.03s
% Verified   : 
% Statistics : Number of formulae       :  220 (1636 expanded)
%              Number of leaves         :   43 ( 491 expanded)
%              Depth                    :   20
%              Number of atoms          : 2078 (35035 expanded)
%              Number of equality atoms :   39 ( 210 expanded)
%              Maximal formula depth    :   23 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_tsep_1_type,type,(
    r1_tsep_1: $i > $i > $o )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k8_tmap_1_type,type,(
    k8_tmap_1: $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k5_tmap_1_type,type,(
    k5_tmap_1: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_D_2_type,type,(
    sk_D_2: $i )).

thf(k7_tmap_1_type,type,(
    k7_tmap_1: $i > $i > $i )).

thf(k6_tmap_1_type,type,(
    k6_tmap_1: $i > $i > $i )).

thf(k2_tmap_1_type,type,(
    k2_tmap_1: $i > $i > $i > $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r1_funct_2_type,type,(
    r1_funct_2: $i > $i > $i > $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k9_tmap_1_type,type,(
    k9_tmap_1: $i > $i > $i )).

thf(r1_tmap_1_type,type,(
    r1_tmap_1: $i > $i > $i > $i > $o )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

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

thf('15',plain,(
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
    ! [X22: $i,X23: $i] :
      ( ~ ( l1_pre_topc @ X22 )
      | ~ ( v2_pre_topc @ X22 )
      | ( v2_struct_0 @ X22 )
      | ~ ( m1_pre_topc @ X23 @ X22 )
      | ( l1_pre_topc @ ( k8_tmap_1 @ X22 @ X23 ) ) ) ),
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
    ! [X22: $i,X23: $i] :
      ( ~ ( l1_pre_topc @ X22 )
      | ~ ( v2_pre_topc @ X22 )
      | ( v2_struct_0 @ X22 )
      | ~ ( m1_pre_topc @ X23 @ X22 )
      | ( v2_pre_topc @ ( k8_tmap_1 @ X22 @ X23 ) ) ) ),
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
    ! [X22: $i,X23: $i] :
      ( ~ ( l1_pre_topc @ X22 )
      | ~ ( v2_pre_topc @ X22 )
      | ( v2_struct_0 @ X22 )
      | ~ ( m1_pre_topc @ X23 @ X22 )
      | ( v1_pre_topc @ ( k8_tmap_1 @ X22 @ X23 ) ) ) ),
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
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_pre_topc @ X14 @ X15 )
      | ( X16
       != ( k9_tmap_1 @ X15 @ X14 ) )
      | ( X17
       != ( u1_struct_0 @ X14 ) )
      | ( r1_funct_2 @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ ( k8_tmap_1 @ X15 @ X14 ) ) @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ ( k6_tmap_1 @ X15 @ X17 ) ) @ X16 @ ( k7_tmap_1 @ X15 @ X17 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ ( k8_tmap_1 @ X15 @ X14 ) ) ) ) )
      | ~ ( v1_funct_2 @ X16 @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ ( k8_tmap_1 @ X15 @ X14 ) ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( l1_pre_topc @ X15 )
      | ~ ( v2_pre_topc @ X15 )
      | ( v2_struct_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d12_tmap_1])).

thf('49',plain,(
    ! [X14: $i,X15: $i] :
      ( ( v2_struct_0 @ X15 )
      | ~ ( v2_pre_topc @ X15 )
      | ~ ( l1_pre_topc @ X15 )
      | ~ ( v1_funct_1 @ ( k9_tmap_1 @ X15 @ X14 ) )
      | ~ ( v1_funct_2 @ ( k9_tmap_1 @ X15 @ X14 ) @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ ( k8_tmap_1 @ X15 @ X14 ) ) )
      | ~ ( m1_subset_1 @ ( k9_tmap_1 @ X15 @ X14 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ ( k8_tmap_1 @ X15 @ X14 ) ) ) ) )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X14 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ( r1_funct_2 @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ ( k8_tmap_1 @ X15 @ X14 ) ) @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ ( k6_tmap_1 @ X15 @ ( u1_struct_0 @ X14 ) ) ) @ ( k9_tmap_1 @ X15 @ X14 ) @ ( k7_tmap_1 @ X15 @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( m1_pre_topc @ X14 @ X15 ) ) ),
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
    ! [X24: $i,X25: $i] :
      ( ~ ( l1_pre_topc @ X24 )
      | ~ ( v2_pre_topc @ X24 )
      | ( v2_struct_0 @ X24 )
      | ~ ( m1_pre_topc @ X25 @ X24 )
      | ( m1_subset_1 @ ( k9_tmap_1 @ X24 @ X25 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X24 ) @ ( u1_struct_0 @ ( k8_tmap_1 @ X24 @ X25 ) ) ) ) ) ) ),
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
    ! [X24: $i,X25: $i] :
      ( ~ ( l1_pre_topc @ X24 )
      | ~ ( v2_pre_topc @ X24 )
      | ( v2_struct_0 @ X24 )
      | ~ ( m1_pre_topc @ X25 @ X24 )
      | ( v1_funct_2 @ ( k9_tmap_1 @ X24 @ X25 ) @ ( u1_struct_0 @ X24 ) @ ( u1_struct_0 @ ( k8_tmap_1 @ X24 @ X25 ) ) ) ) ),
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
    ! [X24: $i,X25: $i] :
      ( ~ ( l1_pre_topc @ X24 )
      | ~ ( v2_pre_topc @ X24 )
      | ( v2_struct_0 @ X24 )
      | ~ ( m1_pre_topc @ X25 @ X24 )
      | ( v1_funct_1 @ ( k9_tmap_1 @ X24 @ X25 ) ) ) ),
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
    ! [X4: $i,X5: $i,X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X5 @ X6 ) ) )
      | ~ ( v1_funct_2 @ X4 @ X5 @ X6 )
      | ~ ( v1_funct_1 @ X4 )
      | ( v1_xboole_0 @ X7 )
      | ( v1_xboole_0 @ X6 )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_funct_2 @ X8 @ X9 @ X7 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X7 ) ) )
      | ( X4 = X8 )
      | ~ ( r1_funct_2 @ X5 @ X6 @ X9 @ X7 @ X4 @ X8 ) ) ),
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
    ! [X20: $i,X21: $i] :
      ( ~ ( l1_pre_topc @ X20 )
      | ~ ( v2_pre_topc @ X20 )
      | ( v2_struct_0 @ X20 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ( v1_funct_1 @ ( k7_tmap_1 @ X20 @ X21 ) ) ) ),
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
    ! [X20: $i,X21: $i] :
      ( ~ ( l1_pre_topc @ X20 )
      | ~ ( v2_pre_topc @ X20 )
      | ( v2_struct_0 @ X20 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ( v1_funct_2 @ ( k7_tmap_1 @ X20 @ X21 ) @ ( u1_struct_0 @ X20 ) @ ( u1_struct_0 @ ( k6_tmap_1 @ X20 @ X21 ) ) ) ) ),
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
    ! [X20: $i,X21: $i] :
      ( ~ ( l1_pre_topc @ X20 )
      | ~ ( v2_pre_topc @ X20 )
      | ( v2_struct_0 @ X20 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ( m1_subset_1 @ ( k7_tmap_1 @ X20 @ X21 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X20 ) @ ( u1_struct_0 @ ( k6_tmap_1 @ X20 @ X21 ) ) ) ) ) ) ),
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

thf(symmetry_r1_tsep_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_struct_0 @ A )
        & ( l1_struct_0 @ B ) )
     => ( ( r1_tsep_1 @ A @ B )
       => ( r1_tsep_1 @ B @ A ) ) ) )).

thf('128',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( l1_struct_0 @ X26 )
      | ~ ( l1_struct_0 @ X27 )
      | ( r1_tsep_1 @ X27 @ X26 )
      | ~ ( r1_tsep_1 @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_tsep_1])).

thf('129',plain,
    ( ( r1_tsep_1 @ sk_C @ sk_B )
    | ~ ( l1_struct_0 @ sk_C )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['127','128'])).

thf('130',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('131',plain,(
    ! [X1: $i,X2: $i] :
      ( ~ ( m1_pre_topc @ X1 @ X2 )
      | ( l1_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X2 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('132',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_C ) ),
    inference('sup-',[status(thm)],['130','131'])).

thf('133',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('134',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['132','133'])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('135',plain,(
    ! [X0: $i] :
      ( ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('136',plain,(
    l1_struct_0 @ sk_C ),
    inference('sup-',[status(thm)],['134','135'])).

thf('137',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('138',plain,(
    ! [X1: $i,X2: $i] :
      ( ~ ( m1_pre_topc @ X1 @ X2 )
      | ( l1_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X2 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('139',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['137','138'])).

thf('140',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('141',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['139','140'])).

thf('142',plain,(
    ! [X0: $i] :
      ( ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('143',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['141','142'])).

thf('144',plain,(
    r1_tsep_1 @ sk_C @ sk_B ),
    inference(demod,[status(thm)],['129','136','143'])).

thf(d3_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ! [B: $i] :
          ( ( l1_struct_0 @ B )
         => ( ( r1_tsep_1 @ A @ B )
          <=> ( r1_xboole_0 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) )).

thf('145',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( l1_struct_0 @ X18 )
      | ~ ( r1_tsep_1 @ X19 @ X18 )
      | ( r1_xboole_0 @ ( u1_struct_0 @ X19 ) @ ( u1_struct_0 @ X18 ) )
      | ~ ( l1_struct_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[d3_tsep_1])).

thf('146',plain,
    ( ~ ( l1_struct_0 @ sk_C )
    | ( r1_xboole_0 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['144','145'])).

thf('147',plain,(
    l1_struct_0 @ sk_C ),
    inference('sup-',[status(thm)],['134','135'])).

thf('148',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['141','142'])).

thf('149',plain,(
    r1_xboole_0 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['146','147','148'])).

thf('150',plain,(
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

thf('151',plain,(
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

thf('152',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( r1_tmap_1 @ X0 @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) @ ( k2_tmap_1 @ sk_A @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) @ X0 ) @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( r1_xboole_0 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['150','151'])).

thf('153',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('154',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('155',plain,
    ( ( k8_tmap_1 @ sk_A @ sk_B )
    = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['44','45'])).

thf('156',plain,
    ( ( k8_tmap_1 @ sk_A @ sk_B )
    = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['44','45'])).

thf('157',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( r1_tmap_1 @ X0 @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) @ X0 ) @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( r1_xboole_0 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['152','153','154','155','156'])).

thf('158',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_C ) )
      | ( r1_tmap_1 @ sk_C @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) @ sk_C ) @ X0 )
      | ~ ( m1_pre_topc @ sk_C @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['149','157'])).

thf('159',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('160',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_C ) )
      | ( r1_tmap_1 @ sk_C @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) @ sk_C ) @ X0 )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['158','159'])).

thf('161',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( r1_tmap_1 @ sk_C @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) @ sk_C ) @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['126','160'])).

thf('162',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('163',plain,
    ( ( r1_tmap_1 @ sk_C @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) @ sk_C ) @ sk_D_2 )
    | ( v2_struct_0 @ sk_C ) ),
    inference(clc,[status(thm)],['161','162'])).

thf('164',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('165',plain,(
    r1_tmap_1 @ sk_C @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) @ sk_C ) @ sk_D_2 ),
    inference(clc,[status(thm)],['163','164'])).

thf('166',plain,
    ( ( r1_tmap_1 @ sk_C @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_C ) @ sk_D_2 )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['125','165'])).

thf('167',plain,(
    ~ ( r1_tmap_1 @ sk_C @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_C ) @ sk_D_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('168',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['166','167'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('169',plain,(
    ! [X3: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X3 ) )
      | ~ ( l1_struct_0 @ X3 )
      | ( v2_struct_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('170',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['168','169'])).

thf('171',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('172',plain,(
    ! [X0: $i] :
      ( ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('173',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['171','172'])).

thf('174',plain,(
    v2_struct_0 @ sk_A ),
    inference(demod,[status(thm)],['170','173'])).

thf('175',plain,(
    $false ),
    inference(demod,[status(thm)],['0','174'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.qZUOF0CE2R
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:43:24 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 3.03/3.22  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 3.03/3.22  % Solved by: fo/fo7.sh
% 3.03/3.22  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 3.03/3.22  % done 1482 iterations in 2.765s
% 3.03/3.22  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 3.03/3.22  % SZS output start Refutation
% 3.03/3.22  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 3.03/3.22  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 3.03/3.22  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 3.03/3.22  thf(r1_tsep_1_type, type, r1_tsep_1: $i > $i > $o).
% 3.03/3.22  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 3.03/3.22  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 3.03/3.22  thf(k8_tmap_1_type, type, k8_tmap_1: $i > $i > $i).
% 3.03/3.22  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 3.03/3.22  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 3.03/3.22  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 3.03/3.22  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 3.03/3.22  thf(sk_A_type, type, sk_A: $i).
% 3.03/3.22  thf(k5_tmap_1_type, type, k5_tmap_1: $i > $i > $i).
% 3.03/3.22  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 3.03/3.22  thf(sk_D_2_type, type, sk_D_2: $i).
% 3.03/3.22  thf(k7_tmap_1_type, type, k7_tmap_1: $i > $i > $i).
% 3.03/3.22  thf(k6_tmap_1_type, type, k6_tmap_1: $i > $i > $i).
% 3.03/3.22  thf(k2_tmap_1_type, type, k2_tmap_1: $i > $i > $i > $i > $i).
% 3.03/3.22  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 3.03/3.22  thf(sk_C_type, type, sk_C: $i).
% 3.03/3.22  thf(r1_funct_2_type, type, r1_funct_2: $i > $i > $i > $i > $i > $i > $o).
% 3.03/3.22  thf(sk_B_type, type, sk_B: $i).
% 3.03/3.22  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 3.03/3.22  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 3.03/3.22  thf(k9_tmap_1_type, type, k9_tmap_1: $i > $i > $i).
% 3.03/3.22  thf(r1_tmap_1_type, type, r1_tmap_1: $i > $i > $i > $i > $o).
% 3.03/3.22  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 3.03/3.22  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 3.03/3.22  thf(t118_tmap_1, conjecture,
% 3.03/3.22    (![A:$i]:
% 3.03/3.22     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 3.03/3.22       ( ![B:$i]:
% 3.03/3.22         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 3.03/3.22           ( ![C:$i]:
% 3.03/3.22             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 3.03/3.22               ( ( r1_tsep_1 @ B @ C ) =>
% 3.03/3.22                 ( ![D:$i]:
% 3.03/3.22                   ( ( m1_subset_1 @ D @ ( u1_struct_0 @ C ) ) =>
% 3.03/3.22                     ( r1_tmap_1 @
% 3.03/3.22                       C @ ( k8_tmap_1 @ A @ B ) @ 
% 3.03/3.22                       ( k2_tmap_1 @
% 3.03/3.22                         A @ ( k8_tmap_1 @ A @ B ) @ ( k9_tmap_1 @ A @ B ) @ C ) @ 
% 3.03/3.22                       D ) ) ) ) ) ) ) ) ))).
% 3.03/3.22  thf(zf_stmt_0, negated_conjecture,
% 3.03/3.22    (~( ![A:$i]:
% 3.03/3.22        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 3.03/3.22            ( l1_pre_topc @ A ) ) =>
% 3.03/3.22          ( ![B:$i]:
% 3.03/3.22            ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 3.03/3.22              ( ![C:$i]:
% 3.03/3.22                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 3.03/3.22                  ( ( r1_tsep_1 @ B @ C ) =>
% 3.03/3.22                    ( ![D:$i]:
% 3.03/3.22                      ( ( m1_subset_1 @ D @ ( u1_struct_0 @ C ) ) =>
% 3.03/3.22                        ( r1_tmap_1 @
% 3.03/3.22                          C @ ( k8_tmap_1 @ A @ B ) @ 
% 3.03/3.22                          ( k2_tmap_1 @
% 3.03/3.22                            A @ ( k8_tmap_1 @ A @ B ) @ 
% 3.03/3.22                            ( k9_tmap_1 @ A @ B ) @ C ) @ 
% 3.03/3.22                          D ) ) ) ) ) ) ) ) ) )),
% 3.03/3.22    inference('cnf.neg', [status(esa)], [t118_tmap_1])).
% 3.03/3.22  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 3.03/3.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.03/3.22  thf('1', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 3.03/3.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.03/3.22  thf(t1_tsep_1, axiom,
% 3.03/3.22    (![A:$i]:
% 3.03/3.22     ( ( l1_pre_topc @ A ) =>
% 3.03/3.22       ( ![B:$i]:
% 3.03/3.22         ( ( m1_pre_topc @ B @ A ) =>
% 3.03/3.22           ( m1_subset_1 @
% 3.03/3.22             ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 3.03/3.22  thf('2', plain,
% 3.03/3.22      (![X34 : $i, X35 : $i]:
% 3.03/3.22         (~ (m1_pre_topc @ X34 @ X35)
% 3.03/3.22          | (m1_subset_1 @ (u1_struct_0 @ X34) @ 
% 3.03/3.22             (k1_zfmisc_1 @ (u1_struct_0 @ X35)))
% 3.03/3.22          | ~ (l1_pre_topc @ X35))),
% 3.03/3.22      inference('cnf', [status(esa)], [t1_tsep_1])).
% 3.03/3.22  thf('3', plain,
% 3.03/3.22      ((~ (l1_pre_topc @ sk_A)
% 3.03/3.22        | (m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 3.03/3.22           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 3.03/3.22      inference('sup-', [status(thm)], ['1', '2'])).
% 3.03/3.22  thf('4', plain, ((l1_pre_topc @ sk_A)),
% 3.03/3.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.03/3.22  thf('5', plain,
% 3.03/3.22      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 3.03/3.22        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.03/3.22      inference('demod', [status(thm)], ['3', '4'])).
% 3.03/3.22  thf(t104_tmap_1, axiom,
% 3.03/3.22    (![A:$i]:
% 3.03/3.22     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 3.03/3.22       ( ![B:$i]:
% 3.03/3.22         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 3.03/3.22           ( ( ( u1_struct_0 @ ( k6_tmap_1 @ A @ B ) ) = ( u1_struct_0 @ A ) ) & 
% 3.03/3.22             ( ( u1_pre_topc @ ( k6_tmap_1 @ A @ B ) ) = ( k5_tmap_1 @ A @ B ) ) ) ) ) ))).
% 3.03/3.22  thf('6', plain,
% 3.03/3.22      (![X28 : $i, X29 : $i]:
% 3.03/3.22         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (u1_struct_0 @ X29)))
% 3.03/3.22          | ((u1_struct_0 @ (k6_tmap_1 @ X29 @ X28)) = (u1_struct_0 @ X29))
% 3.03/3.22          | ~ (l1_pre_topc @ X29)
% 3.03/3.22          | ~ (v2_pre_topc @ X29)
% 3.03/3.22          | (v2_struct_0 @ X29))),
% 3.03/3.22      inference('cnf', [status(esa)], [t104_tmap_1])).
% 3.03/3.22  thf('7', plain,
% 3.03/3.22      (((v2_struct_0 @ sk_A)
% 3.03/3.22        | ~ (v2_pre_topc @ sk_A)
% 3.03/3.22        | ~ (l1_pre_topc @ sk_A)
% 3.03/3.22        | ((u1_struct_0 @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 3.03/3.22            = (u1_struct_0 @ sk_A)))),
% 3.03/3.22      inference('sup-', [status(thm)], ['5', '6'])).
% 3.03/3.22  thf('8', plain, ((v2_pre_topc @ sk_A)),
% 3.03/3.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.03/3.22  thf('9', plain, ((l1_pre_topc @ sk_A)),
% 3.03/3.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.03/3.22  thf('10', plain,
% 3.03/3.22      (((v2_struct_0 @ sk_A)
% 3.03/3.22        | ((u1_struct_0 @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 3.03/3.22            = (u1_struct_0 @ sk_A)))),
% 3.03/3.22      inference('demod', [status(thm)], ['7', '8', '9'])).
% 3.03/3.22  thf('11', plain, (~ (v2_struct_0 @ sk_A)),
% 3.03/3.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.03/3.22  thf('12', plain,
% 3.03/3.22      (((u1_struct_0 @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 3.03/3.22         = (u1_struct_0 @ sk_A))),
% 3.03/3.22      inference('clc', [status(thm)], ['10', '11'])).
% 3.03/3.22  thf('13', plain,
% 3.03/3.22      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 3.03/3.22        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.03/3.22      inference('demod', [status(thm)], ['3', '4'])).
% 3.03/3.22  thf(d11_tmap_1, axiom,
% 3.03/3.22    (![A:$i]:
% 3.03/3.22     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 3.03/3.22       ( ![B:$i]:
% 3.03/3.22         ( ( m1_pre_topc @ B @ A ) =>
% 3.03/3.22           ( ![C:$i]:
% 3.03/3.22             ( ( ( v1_pre_topc @ C ) & ( v2_pre_topc @ C ) & 
% 3.03/3.22                 ( l1_pre_topc @ C ) ) =>
% 3.03/3.22               ( ( ( C ) = ( k8_tmap_1 @ A @ B ) ) <=>
% 3.03/3.22                 ( ![D:$i]:
% 3.03/3.22                   ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 3.03/3.22                     ( ( ( D ) = ( u1_struct_0 @ B ) ) =>
% 3.03/3.22                       ( ( C ) = ( k6_tmap_1 @ A @ D ) ) ) ) ) ) ) ) ) ) ))).
% 3.03/3.22  thf('14', plain,
% 3.03/3.22      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 3.03/3.22         (~ (m1_pre_topc @ X10 @ X11)
% 3.03/3.22          | ((X12) != (k8_tmap_1 @ X11 @ X10))
% 3.03/3.22          | ((X13) != (u1_struct_0 @ X10))
% 3.03/3.22          | ((X12) = (k6_tmap_1 @ X11 @ X13))
% 3.03/3.22          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 3.03/3.22          | ~ (l1_pre_topc @ X12)
% 3.03/3.22          | ~ (v2_pre_topc @ X12)
% 3.03/3.22          | ~ (v1_pre_topc @ X12)
% 3.03/3.22          | ~ (l1_pre_topc @ X11)
% 3.03/3.22          | ~ (v2_pre_topc @ X11)
% 3.03/3.22          | (v2_struct_0 @ X11))),
% 3.03/3.23      inference('cnf', [status(esa)], [d11_tmap_1])).
% 3.03/3.23  thf('15', plain,
% 3.03/3.23      (![X10 : $i, X11 : $i]:
% 3.03/3.23         ((v2_struct_0 @ X11)
% 3.03/3.23          | ~ (v2_pre_topc @ X11)
% 3.03/3.23          | ~ (l1_pre_topc @ X11)
% 3.03/3.23          | ~ (v1_pre_topc @ (k8_tmap_1 @ X11 @ X10))
% 3.03/3.23          | ~ (v2_pre_topc @ (k8_tmap_1 @ X11 @ X10))
% 3.03/3.23          | ~ (l1_pre_topc @ (k8_tmap_1 @ X11 @ X10))
% 3.03/3.23          | ~ (m1_subset_1 @ (u1_struct_0 @ X10) @ 
% 3.03/3.23               (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 3.03/3.23          | ((k8_tmap_1 @ X11 @ X10) = (k6_tmap_1 @ X11 @ (u1_struct_0 @ X10)))
% 3.03/3.23          | ~ (m1_pre_topc @ X10 @ X11))),
% 3.03/3.23      inference('simplify', [status(thm)], ['14'])).
% 3.03/3.23  thf('16', plain,
% 3.03/3.23      ((~ (m1_pre_topc @ sk_B @ sk_A)
% 3.03/3.23        | ((k8_tmap_1 @ sk_A @ sk_B)
% 3.03/3.23            = (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 3.03/3.23        | ~ (l1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 3.03/3.23        | ~ (v2_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 3.03/3.23        | ~ (v1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 3.03/3.23        | ~ (l1_pre_topc @ sk_A)
% 3.03/3.23        | ~ (v2_pre_topc @ sk_A)
% 3.03/3.23        | (v2_struct_0 @ sk_A))),
% 3.03/3.23      inference('sup-', [status(thm)], ['13', '15'])).
% 3.03/3.23  thf('17', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 3.03/3.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.03/3.23  thf('18', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 3.03/3.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.03/3.23  thf(dt_k8_tmap_1, axiom,
% 3.03/3.23    (![A:$i,B:$i]:
% 3.03/3.23     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 3.03/3.23         ( l1_pre_topc @ A ) & ( m1_pre_topc @ B @ A ) ) =>
% 3.03/3.23       ( ( v1_pre_topc @ ( k8_tmap_1 @ A @ B ) ) & 
% 3.03/3.23         ( v2_pre_topc @ ( k8_tmap_1 @ A @ B ) ) & 
% 3.03/3.23         ( l1_pre_topc @ ( k8_tmap_1 @ A @ B ) ) ) ))).
% 3.03/3.23  thf('19', plain,
% 3.03/3.23      (![X22 : $i, X23 : $i]:
% 3.03/3.23         (~ (l1_pre_topc @ X22)
% 3.03/3.23          | ~ (v2_pre_topc @ X22)
% 3.03/3.23          | (v2_struct_0 @ X22)
% 3.03/3.23          | ~ (m1_pre_topc @ X23 @ X22)
% 3.03/3.23          | (l1_pre_topc @ (k8_tmap_1 @ X22 @ X23)))),
% 3.03/3.23      inference('cnf', [status(esa)], [dt_k8_tmap_1])).
% 3.03/3.23  thf('20', plain,
% 3.03/3.23      (((l1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 3.03/3.23        | (v2_struct_0 @ sk_A)
% 3.03/3.23        | ~ (v2_pre_topc @ sk_A)
% 3.03/3.23        | ~ (l1_pre_topc @ sk_A))),
% 3.03/3.23      inference('sup-', [status(thm)], ['18', '19'])).
% 3.03/3.23  thf('21', plain, ((v2_pre_topc @ sk_A)),
% 3.03/3.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.03/3.23  thf('22', plain, ((l1_pre_topc @ sk_A)),
% 3.03/3.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.03/3.23  thf('23', plain,
% 3.03/3.23      (((l1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B)) | (v2_struct_0 @ sk_A))),
% 3.03/3.23      inference('demod', [status(thm)], ['20', '21', '22'])).
% 3.03/3.23  thf('24', plain, (~ (v2_struct_0 @ sk_A)),
% 3.03/3.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.03/3.23  thf('25', plain, ((l1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))),
% 3.03/3.23      inference('clc', [status(thm)], ['23', '24'])).
% 3.03/3.23  thf('26', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 3.03/3.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.03/3.23  thf('27', plain,
% 3.03/3.23      (![X22 : $i, X23 : $i]:
% 3.03/3.23         (~ (l1_pre_topc @ X22)
% 3.03/3.23          | ~ (v2_pre_topc @ X22)
% 3.03/3.23          | (v2_struct_0 @ X22)
% 3.03/3.23          | ~ (m1_pre_topc @ X23 @ X22)
% 3.03/3.23          | (v2_pre_topc @ (k8_tmap_1 @ X22 @ X23)))),
% 3.03/3.23      inference('cnf', [status(esa)], [dt_k8_tmap_1])).
% 3.03/3.23  thf('28', plain,
% 3.03/3.23      (((v2_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 3.03/3.23        | (v2_struct_0 @ sk_A)
% 3.03/3.23        | ~ (v2_pre_topc @ sk_A)
% 3.03/3.23        | ~ (l1_pre_topc @ sk_A))),
% 3.03/3.23      inference('sup-', [status(thm)], ['26', '27'])).
% 3.03/3.23  thf('29', plain, ((v2_pre_topc @ sk_A)),
% 3.03/3.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.03/3.23  thf('30', plain, ((l1_pre_topc @ sk_A)),
% 3.03/3.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.03/3.23  thf('31', plain,
% 3.03/3.23      (((v2_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B)) | (v2_struct_0 @ sk_A))),
% 3.03/3.23      inference('demod', [status(thm)], ['28', '29', '30'])).
% 3.03/3.23  thf('32', plain, (~ (v2_struct_0 @ sk_A)),
% 3.03/3.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.03/3.23  thf('33', plain, ((v2_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))),
% 3.03/3.23      inference('clc', [status(thm)], ['31', '32'])).
% 3.03/3.23  thf('34', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 3.03/3.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.03/3.23  thf('35', plain,
% 3.03/3.23      (![X22 : $i, X23 : $i]:
% 3.03/3.23         (~ (l1_pre_topc @ X22)
% 3.03/3.23          | ~ (v2_pre_topc @ X22)
% 3.03/3.23          | (v2_struct_0 @ X22)
% 3.03/3.23          | ~ (m1_pre_topc @ X23 @ X22)
% 3.03/3.23          | (v1_pre_topc @ (k8_tmap_1 @ X22 @ X23)))),
% 3.03/3.23      inference('cnf', [status(esa)], [dt_k8_tmap_1])).
% 3.03/3.23  thf('36', plain,
% 3.03/3.23      (((v1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 3.03/3.23        | (v2_struct_0 @ sk_A)
% 3.03/3.23        | ~ (v2_pre_topc @ sk_A)
% 3.03/3.23        | ~ (l1_pre_topc @ sk_A))),
% 3.03/3.23      inference('sup-', [status(thm)], ['34', '35'])).
% 3.03/3.23  thf('37', plain, ((v2_pre_topc @ sk_A)),
% 3.03/3.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.03/3.23  thf('38', plain, ((l1_pre_topc @ sk_A)),
% 3.03/3.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.03/3.23  thf('39', plain,
% 3.03/3.23      (((v1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B)) | (v2_struct_0 @ sk_A))),
% 3.03/3.23      inference('demod', [status(thm)], ['36', '37', '38'])).
% 3.03/3.23  thf('40', plain, (~ (v2_struct_0 @ sk_A)),
% 3.03/3.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.03/3.23  thf('41', plain, ((v1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))),
% 3.03/3.23      inference('clc', [status(thm)], ['39', '40'])).
% 3.03/3.23  thf('42', plain, ((l1_pre_topc @ sk_A)),
% 3.03/3.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.03/3.23  thf('43', plain, ((v2_pre_topc @ sk_A)),
% 3.03/3.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.03/3.23  thf('44', plain,
% 3.03/3.23      ((((k8_tmap_1 @ sk_A @ sk_B) = (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 3.03/3.23        | (v2_struct_0 @ sk_A))),
% 3.03/3.23      inference('demod', [status(thm)],
% 3.03/3.23                ['16', '17', '25', '33', '41', '42', '43'])).
% 3.03/3.23  thf('45', plain, (~ (v2_struct_0 @ sk_A)),
% 3.03/3.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.03/3.23  thf('46', plain,
% 3.03/3.23      (((k8_tmap_1 @ sk_A @ sk_B) = (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))),
% 3.03/3.23      inference('clc', [status(thm)], ['44', '45'])).
% 3.03/3.23  thf('47', plain,
% 3.03/3.23      (((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 3.03/3.23      inference('demod', [status(thm)], ['12', '46'])).
% 3.03/3.23  thf(d12_tmap_1, axiom,
% 3.03/3.23    (![A:$i]:
% 3.03/3.23     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 3.03/3.23       ( ![B:$i]:
% 3.03/3.23         ( ( m1_pre_topc @ B @ A ) =>
% 3.03/3.23           ( ![C:$i]:
% 3.03/3.23             ( ( ( v1_funct_1 @ C ) & 
% 3.03/3.23                 ( v1_funct_2 @
% 3.03/3.23                   C @ ( u1_struct_0 @ A ) @ 
% 3.03/3.23                   ( u1_struct_0 @ ( k8_tmap_1 @ A @ B ) ) ) & 
% 3.03/3.23                 ( m1_subset_1 @
% 3.03/3.23                   C @ 
% 3.03/3.23                   ( k1_zfmisc_1 @
% 3.03/3.23                     ( k2_zfmisc_1 @
% 3.03/3.23                       ( u1_struct_0 @ A ) @ 
% 3.03/3.23                       ( u1_struct_0 @ ( k8_tmap_1 @ A @ B ) ) ) ) ) ) =>
% 3.03/3.23               ( ( ( C ) = ( k9_tmap_1 @ A @ B ) ) <=>
% 3.03/3.23                 ( ![D:$i]:
% 3.03/3.23                   ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 3.03/3.23                     ( ( ( D ) = ( u1_struct_0 @ B ) ) =>
% 3.03/3.23                       ( r1_funct_2 @
% 3.03/3.23                         ( u1_struct_0 @ A ) @ 
% 3.03/3.23                         ( u1_struct_0 @ ( k8_tmap_1 @ A @ B ) ) @ 
% 3.03/3.23                         ( u1_struct_0 @ A ) @ 
% 3.03/3.23                         ( u1_struct_0 @ ( k6_tmap_1 @ A @ D ) ) @ C @ 
% 3.03/3.23                         ( k7_tmap_1 @ A @ D ) ) ) ) ) ) ) ) ) ) ))).
% 3.03/3.23  thf('48', plain,
% 3.03/3.23      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 3.03/3.23         (~ (m1_pre_topc @ X14 @ X15)
% 3.03/3.23          | ((X16) != (k9_tmap_1 @ X15 @ X14))
% 3.03/3.23          | ((X17) != (u1_struct_0 @ X14))
% 3.03/3.23          | (r1_funct_2 @ (u1_struct_0 @ X15) @ 
% 3.03/3.23             (u1_struct_0 @ (k8_tmap_1 @ X15 @ X14)) @ (u1_struct_0 @ X15) @ 
% 3.03/3.23             (u1_struct_0 @ (k6_tmap_1 @ X15 @ X17)) @ X16 @ 
% 3.03/3.23             (k7_tmap_1 @ X15 @ X17))
% 3.03/3.23          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 3.03/3.23          | ~ (m1_subset_1 @ X16 @ 
% 3.03/3.23               (k1_zfmisc_1 @ 
% 3.03/3.23                (k2_zfmisc_1 @ (u1_struct_0 @ X15) @ 
% 3.03/3.23                 (u1_struct_0 @ (k8_tmap_1 @ X15 @ X14)))))
% 3.03/3.23          | ~ (v1_funct_2 @ X16 @ (u1_struct_0 @ X15) @ 
% 3.03/3.23               (u1_struct_0 @ (k8_tmap_1 @ X15 @ X14)))
% 3.03/3.23          | ~ (v1_funct_1 @ X16)
% 3.03/3.23          | ~ (l1_pre_topc @ X15)
% 3.03/3.23          | ~ (v2_pre_topc @ X15)
% 3.03/3.23          | (v2_struct_0 @ X15))),
% 3.03/3.23      inference('cnf', [status(esa)], [d12_tmap_1])).
% 3.03/3.23  thf('49', plain,
% 3.03/3.23      (![X14 : $i, X15 : $i]:
% 3.03/3.23         ((v2_struct_0 @ X15)
% 3.03/3.23          | ~ (v2_pre_topc @ X15)
% 3.03/3.23          | ~ (l1_pre_topc @ X15)
% 3.03/3.23          | ~ (v1_funct_1 @ (k9_tmap_1 @ X15 @ X14))
% 3.03/3.23          | ~ (v1_funct_2 @ (k9_tmap_1 @ X15 @ X14) @ (u1_struct_0 @ X15) @ 
% 3.03/3.23               (u1_struct_0 @ (k8_tmap_1 @ X15 @ X14)))
% 3.03/3.23          | ~ (m1_subset_1 @ (k9_tmap_1 @ X15 @ X14) @ 
% 3.03/3.23               (k1_zfmisc_1 @ 
% 3.03/3.23                (k2_zfmisc_1 @ (u1_struct_0 @ X15) @ 
% 3.03/3.23                 (u1_struct_0 @ (k8_tmap_1 @ X15 @ X14)))))
% 3.03/3.23          | ~ (m1_subset_1 @ (u1_struct_0 @ X14) @ 
% 3.03/3.23               (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 3.03/3.23          | (r1_funct_2 @ (u1_struct_0 @ X15) @ 
% 3.03/3.23             (u1_struct_0 @ (k8_tmap_1 @ X15 @ X14)) @ (u1_struct_0 @ X15) @ 
% 3.03/3.23             (u1_struct_0 @ (k6_tmap_1 @ X15 @ (u1_struct_0 @ X14))) @ 
% 3.03/3.23             (k9_tmap_1 @ X15 @ X14) @ (k7_tmap_1 @ X15 @ (u1_struct_0 @ X14)))
% 3.03/3.23          | ~ (m1_pre_topc @ X14 @ X15))),
% 3.03/3.23      inference('simplify', [status(thm)], ['48'])).
% 3.03/3.23  thf('50', plain,
% 3.03/3.23      ((~ (m1_subset_1 @ (k9_tmap_1 @ sk_A @ sk_B) @ 
% 3.03/3.23           (k1_zfmisc_1 @ 
% 3.03/3.23            (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))))
% 3.03/3.23        | ~ (m1_pre_topc @ sk_B @ sk_A)
% 3.03/3.23        | (r1_funct_2 @ (u1_struct_0 @ sk_A) @ 
% 3.03/3.23           (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)) @ (u1_struct_0 @ sk_A) @ 
% 3.03/3.23           (u1_struct_0 @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B))) @ 
% 3.03/3.23           (k9_tmap_1 @ sk_A @ sk_B) @ 
% 3.03/3.23           (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 3.03/3.23        | ~ (m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 3.03/3.23             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 3.03/3.23        | ~ (v1_funct_2 @ (k9_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 3.03/3.23             (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))
% 3.03/3.23        | ~ (v1_funct_1 @ (k9_tmap_1 @ sk_A @ sk_B))
% 3.03/3.23        | ~ (l1_pre_topc @ sk_A)
% 3.03/3.23        | ~ (v2_pre_topc @ sk_A)
% 3.03/3.23        | (v2_struct_0 @ sk_A))),
% 3.03/3.23      inference('sup-', [status(thm)], ['47', '49'])).
% 3.03/3.23  thf('51', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 3.03/3.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.03/3.23  thf(dt_k9_tmap_1, axiom,
% 3.03/3.23    (![A:$i,B:$i]:
% 3.03/3.23     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 3.03/3.23         ( l1_pre_topc @ A ) & ( m1_pre_topc @ B @ A ) ) =>
% 3.03/3.23       ( ( v1_funct_1 @ ( k9_tmap_1 @ A @ B ) ) & 
% 3.03/3.23         ( v1_funct_2 @
% 3.03/3.23           ( k9_tmap_1 @ A @ B ) @ ( u1_struct_0 @ A ) @ 
% 3.03/3.23           ( u1_struct_0 @ ( k8_tmap_1 @ A @ B ) ) ) & 
% 3.03/3.23         ( m1_subset_1 @
% 3.03/3.23           ( k9_tmap_1 @ A @ B ) @ 
% 3.03/3.23           ( k1_zfmisc_1 @
% 3.03/3.23             ( k2_zfmisc_1 @
% 3.03/3.23               ( u1_struct_0 @ A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ A @ B ) ) ) ) ) ) ))).
% 3.03/3.23  thf('52', plain,
% 3.03/3.23      (![X24 : $i, X25 : $i]:
% 3.03/3.23         (~ (l1_pre_topc @ X24)
% 3.03/3.23          | ~ (v2_pre_topc @ X24)
% 3.03/3.23          | (v2_struct_0 @ X24)
% 3.03/3.23          | ~ (m1_pre_topc @ X25 @ X24)
% 3.03/3.23          | (m1_subset_1 @ (k9_tmap_1 @ X24 @ X25) @ 
% 3.03/3.23             (k1_zfmisc_1 @ 
% 3.03/3.23              (k2_zfmisc_1 @ (u1_struct_0 @ X24) @ 
% 3.03/3.23               (u1_struct_0 @ (k8_tmap_1 @ X24 @ X25))))))),
% 3.03/3.23      inference('cnf', [status(esa)], [dt_k9_tmap_1])).
% 3.03/3.23  thf('53', plain,
% 3.03/3.23      (((m1_subset_1 @ (k9_tmap_1 @ sk_A @ sk_B) @ 
% 3.03/3.23         (k1_zfmisc_1 @ 
% 3.03/3.23          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 3.03/3.23           (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))))
% 3.03/3.23        | (v2_struct_0 @ sk_A)
% 3.03/3.23        | ~ (v2_pre_topc @ sk_A)
% 3.03/3.23        | ~ (l1_pre_topc @ sk_A))),
% 3.03/3.23      inference('sup-', [status(thm)], ['51', '52'])).
% 3.03/3.23  thf('54', plain, ((v2_pre_topc @ sk_A)),
% 3.03/3.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.03/3.23  thf('55', plain, ((l1_pre_topc @ sk_A)),
% 3.03/3.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.03/3.23  thf('56', plain,
% 3.03/3.23      (((m1_subset_1 @ (k9_tmap_1 @ sk_A @ sk_B) @ 
% 3.03/3.23         (k1_zfmisc_1 @ 
% 3.03/3.23          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 3.03/3.23           (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))))
% 3.03/3.23        | (v2_struct_0 @ sk_A))),
% 3.03/3.23      inference('demod', [status(thm)], ['53', '54', '55'])).
% 3.03/3.23  thf('57', plain,
% 3.03/3.23      (((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 3.03/3.23      inference('demod', [status(thm)], ['12', '46'])).
% 3.03/3.23  thf('58', plain,
% 3.03/3.23      (((m1_subset_1 @ (k9_tmap_1 @ sk_A @ sk_B) @ 
% 3.03/3.23         (k1_zfmisc_1 @ 
% 3.03/3.23          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))))
% 3.03/3.23        | (v2_struct_0 @ sk_A))),
% 3.03/3.23      inference('demod', [status(thm)], ['56', '57'])).
% 3.03/3.23  thf('59', plain, (~ (v2_struct_0 @ sk_A)),
% 3.03/3.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.03/3.23  thf('60', plain,
% 3.03/3.23      ((m1_subset_1 @ (k9_tmap_1 @ sk_A @ sk_B) @ 
% 3.03/3.23        (k1_zfmisc_1 @ 
% 3.03/3.23         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))))),
% 3.03/3.23      inference('clc', [status(thm)], ['58', '59'])).
% 3.03/3.23  thf('61', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 3.03/3.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.03/3.23  thf('62', plain,
% 3.03/3.23      (((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 3.03/3.23      inference('demod', [status(thm)], ['12', '46'])).
% 3.03/3.23  thf('63', plain,
% 3.03/3.23      (((k8_tmap_1 @ sk_A @ sk_B) = (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))),
% 3.03/3.23      inference('clc', [status(thm)], ['44', '45'])).
% 3.03/3.23  thf('64', plain,
% 3.03/3.23      (((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 3.03/3.23      inference('demod', [status(thm)], ['12', '46'])).
% 3.03/3.23  thf('65', plain,
% 3.03/3.23      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 3.03/3.23        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.03/3.23      inference('demod', [status(thm)], ['3', '4'])).
% 3.03/3.23  thf('66', plain,
% 3.03/3.23      (((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 3.03/3.23      inference('demod', [status(thm)], ['12', '46'])).
% 3.03/3.23  thf('67', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 3.03/3.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.03/3.23  thf('68', plain,
% 3.03/3.23      (![X24 : $i, X25 : $i]:
% 3.03/3.23         (~ (l1_pre_topc @ X24)
% 3.03/3.23          | ~ (v2_pre_topc @ X24)
% 3.03/3.23          | (v2_struct_0 @ X24)
% 3.03/3.23          | ~ (m1_pre_topc @ X25 @ X24)
% 3.03/3.23          | (v1_funct_2 @ (k9_tmap_1 @ X24 @ X25) @ (u1_struct_0 @ X24) @ 
% 3.03/3.23             (u1_struct_0 @ (k8_tmap_1 @ X24 @ X25))))),
% 3.03/3.23      inference('cnf', [status(esa)], [dt_k9_tmap_1])).
% 3.03/3.23  thf('69', plain,
% 3.03/3.23      (((v1_funct_2 @ (k9_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 3.03/3.23         (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))
% 3.03/3.23        | (v2_struct_0 @ sk_A)
% 3.03/3.23        | ~ (v2_pre_topc @ sk_A)
% 3.03/3.23        | ~ (l1_pre_topc @ sk_A))),
% 3.03/3.23      inference('sup-', [status(thm)], ['67', '68'])).
% 3.03/3.23  thf('70', plain, ((v2_pre_topc @ sk_A)),
% 3.03/3.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.03/3.23  thf('71', plain, ((l1_pre_topc @ sk_A)),
% 3.03/3.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.03/3.23  thf('72', plain,
% 3.03/3.23      (((v1_funct_2 @ (k9_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 3.03/3.23         (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))
% 3.03/3.23        | (v2_struct_0 @ sk_A))),
% 3.03/3.23      inference('demod', [status(thm)], ['69', '70', '71'])).
% 3.03/3.23  thf('73', plain, (~ (v2_struct_0 @ sk_A)),
% 3.03/3.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.03/3.23  thf('74', plain,
% 3.03/3.23      ((v1_funct_2 @ (k9_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 3.03/3.23        (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))),
% 3.03/3.23      inference('clc', [status(thm)], ['72', '73'])).
% 3.03/3.23  thf('75', plain,
% 3.03/3.23      (((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 3.03/3.23      inference('demod', [status(thm)], ['12', '46'])).
% 3.03/3.23  thf('76', plain,
% 3.03/3.23      ((v1_funct_2 @ (k9_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 3.03/3.23        (u1_struct_0 @ sk_A))),
% 3.03/3.23      inference('demod', [status(thm)], ['74', '75'])).
% 3.03/3.23  thf('77', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 3.03/3.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.03/3.23  thf('78', plain,
% 3.03/3.23      (![X24 : $i, X25 : $i]:
% 3.03/3.23         (~ (l1_pre_topc @ X24)
% 3.03/3.23          | ~ (v2_pre_topc @ X24)
% 3.03/3.23          | (v2_struct_0 @ X24)
% 3.03/3.23          | ~ (m1_pre_topc @ X25 @ X24)
% 3.03/3.23          | (v1_funct_1 @ (k9_tmap_1 @ X24 @ X25)))),
% 3.03/3.23      inference('cnf', [status(esa)], [dt_k9_tmap_1])).
% 3.03/3.23  thf('79', plain,
% 3.03/3.23      (((v1_funct_1 @ (k9_tmap_1 @ sk_A @ sk_B))
% 3.03/3.23        | (v2_struct_0 @ sk_A)
% 3.03/3.23        | ~ (v2_pre_topc @ sk_A)
% 3.03/3.23        | ~ (l1_pre_topc @ sk_A))),
% 3.03/3.23      inference('sup-', [status(thm)], ['77', '78'])).
% 3.03/3.23  thf('80', plain, ((v2_pre_topc @ sk_A)),
% 3.03/3.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.03/3.23  thf('81', plain, ((l1_pre_topc @ sk_A)),
% 3.03/3.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.03/3.23  thf('82', plain,
% 3.03/3.23      (((v1_funct_1 @ (k9_tmap_1 @ sk_A @ sk_B)) | (v2_struct_0 @ sk_A))),
% 3.03/3.23      inference('demod', [status(thm)], ['79', '80', '81'])).
% 3.03/3.23  thf('83', plain, (~ (v2_struct_0 @ sk_A)),
% 3.03/3.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.03/3.23  thf('84', plain, ((v1_funct_1 @ (k9_tmap_1 @ sk_A @ sk_B))),
% 3.03/3.23      inference('clc', [status(thm)], ['82', '83'])).
% 3.03/3.23  thf('85', plain, ((l1_pre_topc @ sk_A)),
% 3.03/3.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.03/3.23  thf('86', plain, ((v2_pre_topc @ sk_A)),
% 3.03/3.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.03/3.23  thf('87', plain,
% 3.03/3.23      (((r1_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 3.03/3.23         (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 3.03/3.23         (k9_tmap_1 @ sk_A @ sk_B) @ (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 3.03/3.23        | (v2_struct_0 @ sk_A))),
% 3.03/3.23      inference('demod', [status(thm)],
% 3.03/3.23                ['50', '60', '61', '62', '63', '64', '65', '66', '76', '84', 
% 3.03/3.23                 '85', '86'])).
% 3.03/3.23  thf('88', plain, (~ (v2_struct_0 @ sk_A)),
% 3.03/3.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.03/3.23  thf('89', plain,
% 3.03/3.23      ((r1_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 3.03/3.23        (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 3.03/3.23        (k9_tmap_1 @ sk_A @ sk_B) @ (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))),
% 3.03/3.23      inference('clc', [status(thm)], ['87', '88'])).
% 3.03/3.23  thf('90', plain,
% 3.03/3.23      ((m1_subset_1 @ (k9_tmap_1 @ sk_A @ sk_B) @ 
% 3.03/3.23        (k1_zfmisc_1 @ 
% 3.03/3.23         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))))),
% 3.03/3.23      inference('clc', [status(thm)], ['58', '59'])).
% 3.03/3.23  thf(redefinition_r1_funct_2, axiom,
% 3.03/3.23    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 3.03/3.23     ( ( ( ~( v1_xboole_0 @ B ) ) & ( ~( v1_xboole_0 @ D ) ) & 
% 3.03/3.23         ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ A @ B ) & 
% 3.03/3.23         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 3.03/3.23         ( v1_funct_1 @ F ) & ( v1_funct_2 @ F @ C @ D ) & 
% 3.03/3.23         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 3.03/3.23       ( ( r1_funct_2 @ A @ B @ C @ D @ E @ F ) <=> ( ( E ) = ( F ) ) ) ))).
% 3.03/3.23  thf('91', plain,
% 3.03/3.23      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 3.03/3.23         (~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X5 @ X6)))
% 3.03/3.23          | ~ (v1_funct_2 @ X4 @ X5 @ X6)
% 3.03/3.23          | ~ (v1_funct_1 @ X4)
% 3.03/3.23          | (v1_xboole_0 @ X7)
% 3.03/3.23          | (v1_xboole_0 @ X6)
% 3.03/3.23          | ~ (v1_funct_1 @ X8)
% 3.03/3.23          | ~ (v1_funct_2 @ X8 @ X9 @ X7)
% 3.03/3.23          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X7)))
% 3.03/3.23          | ((X4) = (X8))
% 3.03/3.23          | ~ (r1_funct_2 @ X5 @ X6 @ X9 @ X7 @ X4 @ X8))),
% 3.03/3.23      inference('cnf', [status(esa)], [redefinition_r1_funct_2])).
% 3.03/3.23  thf('92', plain,
% 3.03/3.23      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.03/3.23         (~ (r1_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ X2 @ 
% 3.03/3.23             X1 @ (k9_tmap_1 @ sk_A @ sk_B) @ X0)
% 3.03/3.23          | ((k9_tmap_1 @ sk_A @ sk_B) = (X0))
% 3.03/3.23          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 3.03/3.23          | ~ (v1_funct_2 @ X0 @ X2 @ X1)
% 3.03/3.23          | ~ (v1_funct_1 @ X0)
% 3.03/3.23          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 3.03/3.23          | (v1_xboole_0 @ X1)
% 3.03/3.23          | ~ (v1_funct_1 @ (k9_tmap_1 @ sk_A @ sk_B))
% 3.03/3.23          | ~ (v1_funct_2 @ (k9_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 3.03/3.23               (u1_struct_0 @ sk_A)))),
% 3.03/3.23      inference('sup-', [status(thm)], ['90', '91'])).
% 3.03/3.23  thf('93', plain, ((v1_funct_1 @ (k9_tmap_1 @ sk_A @ sk_B))),
% 3.03/3.23      inference('clc', [status(thm)], ['82', '83'])).
% 3.03/3.23  thf('94', plain,
% 3.03/3.23      ((v1_funct_2 @ (k9_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 3.03/3.23        (u1_struct_0 @ sk_A))),
% 3.03/3.23      inference('demod', [status(thm)], ['74', '75'])).
% 3.03/3.23  thf('95', plain,
% 3.03/3.23      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.03/3.23         (~ (r1_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ X2 @ 
% 3.03/3.23             X1 @ (k9_tmap_1 @ sk_A @ sk_B) @ X0)
% 3.03/3.23          | ((k9_tmap_1 @ sk_A @ sk_B) = (X0))
% 3.03/3.23          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 3.03/3.23          | ~ (v1_funct_2 @ X0 @ X2 @ X1)
% 3.03/3.23          | ~ (v1_funct_1 @ X0)
% 3.03/3.23          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 3.03/3.23          | (v1_xboole_0 @ X1))),
% 3.03/3.23      inference('demod', [status(thm)], ['92', '93', '94'])).
% 3.03/3.23  thf('96', plain,
% 3.03/3.23      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 3.03/3.23        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 3.03/3.23        | ~ (v1_funct_1 @ (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 3.03/3.23        | ~ (v1_funct_2 @ (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)) @ 
% 3.03/3.23             (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))
% 3.03/3.23        | ~ (m1_subset_1 @ (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)) @ 
% 3.03/3.23             (k1_zfmisc_1 @ 
% 3.03/3.23              (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))))
% 3.03/3.23        | ((k9_tmap_1 @ sk_A @ sk_B)
% 3.03/3.23            = (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B))))),
% 3.03/3.23      inference('sup-', [status(thm)], ['89', '95'])).
% 3.03/3.23  thf('97', plain,
% 3.03/3.23      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 3.03/3.23        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.03/3.23      inference('demod', [status(thm)], ['3', '4'])).
% 3.03/3.23  thf(dt_k7_tmap_1, axiom,
% 3.03/3.23    (![A:$i,B:$i]:
% 3.03/3.23     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 3.03/3.23         ( l1_pre_topc @ A ) & 
% 3.03/3.23         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 3.03/3.23       ( ( v1_funct_1 @ ( k7_tmap_1 @ A @ B ) ) & 
% 3.03/3.23         ( v1_funct_2 @
% 3.03/3.23           ( k7_tmap_1 @ A @ B ) @ ( u1_struct_0 @ A ) @ 
% 3.03/3.23           ( u1_struct_0 @ ( k6_tmap_1 @ A @ B ) ) ) & 
% 3.03/3.23         ( m1_subset_1 @
% 3.03/3.23           ( k7_tmap_1 @ A @ B ) @ 
% 3.03/3.23           ( k1_zfmisc_1 @
% 3.03/3.23             ( k2_zfmisc_1 @
% 3.03/3.23               ( u1_struct_0 @ A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ A @ B ) ) ) ) ) ) ))).
% 3.03/3.23  thf('98', plain,
% 3.03/3.23      (![X20 : $i, X21 : $i]:
% 3.03/3.23         (~ (l1_pre_topc @ X20)
% 3.03/3.23          | ~ (v2_pre_topc @ X20)
% 3.03/3.23          | (v2_struct_0 @ X20)
% 3.03/3.23          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 3.03/3.23          | (v1_funct_1 @ (k7_tmap_1 @ X20 @ X21)))),
% 3.03/3.23      inference('cnf', [status(esa)], [dt_k7_tmap_1])).
% 3.03/3.23  thf('99', plain,
% 3.03/3.23      (((v1_funct_1 @ (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 3.03/3.23        | (v2_struct_0 @ sk_A)
% 3.03/3.23        | ~ (v2_pre_topc @ sk_A)
% 3.03/3.23        | ~ (l1_pre_topc @ sk_A))),
% 3.03/3.23      inference('sup-', [status(thm)], ['97', '98'])).
% 3.03/3.23  thf('100', plain, ((v2_pre_topc @ sk_A)),
% 3.03/3.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.03/3.23  thf('101', plain, ((l1_pre_topc @ sk_A)),
% 3.03/3.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.03/3.23  thf('102', plain,
% 3.03/3.23      (((v1_funct_1 @ (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 3.03/3.23        | (v2_struct_0 @ sk_A))),
% 3.03/3.23      inference('demod', [status(thm)], ['99', '100', '101'])).
% 3.03/3.23  thf('103', plain, (~ (v2_struct_0 @ sk_A)),
% 3.03/3.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.03/3.23  thf('104', plain, ((v1_funct_1 @ (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))),
% 3.03/3.23      inference('clc', [status(thm)], ['102', '103'])).
% 3.03/3.23  thf('105', plain,
% 3.03/3.23      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 3.03/3.23        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.03/3.23      inference('demod', [status(thm)], ['3', '4'])).
% 3.03/3.23  thf('106', plain,
% 3.03/3.23      (![X20 : $i, X21 : $i]:
% 3.03/3.23         (~ (l1_pre_topc @ X20)
% 3.03/3.23          | ~ (v2_pre_topc @ X20)
% 3.03/3.23          | (v2_struct_0 @ X20)
% 3.03/3.23          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 3.03/3.23          | (v1_funct_2 @ (k7_tmap_1 @ X20 @ X21) @ (u1_struct_0 @ X20) @ 
% 3.03/3.23             (u1_struct_0 @ (k6_tmap_1 @ X20 @ X21))))),
% 3.03/3.23      inference('cnf', [status(esa)], [dt_k7_tmap_1])).
% 3.03/3.23  thf('107', plain,
% 3.03/3.23      (((v1_funct_2 @ (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)) @ 
% 3.03/3.23         (u1_struct_0 @ sk_A) @ 
% 3.03/3.23         (u1_struct_0 @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B))))
% 3.03/3.23        | (v2_struct_0 @ sk_A)
% 3.03/3.23        | ~ (v2_pre_topc @ sk_A)
% 3.03/3.23        | ~ (l1_pre_topc @ sk_A))),
% 3.03/3.23      inference('sup-', [status(thm)], ['105', '106'])).
% 3.03/3.23  thf('108', plain,
% 3.03/3.23      (((u1_struct_0 @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 3.03/3.23         = (u1_struct_0 @ sk_A))),
% 3.03/3.23      inference('clc', [status(thm)], ['10', '11'])).
% 3.03/3.23  thf('109', plain, ((v2_pre_topc @ sk_A)),
% 3.03/3.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.03/3.23  thf('110', plain, ((l1_pre_topc @ sk_A)),
% 3.03/3.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.03/3.23  thf('111', plain,
% 3.03/3.23      (((v1_funct_2 @ (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)) @ 
% 3.03/3.23         (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))
% 3.03/3.23        | (v2_struct_0 @ sk_A))),
% 3.03/3.23      inference('demod', [status(thm)], ['107', '108', '109', '110'])).
% 3.03/3.23  thf('112', plain, (~ (v2_struct_0 @ sk_A)),
% 3.03/3.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.03/3.23  thf('113', plain,
% 3.03/3.23      ((v1_funct_2 @ (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)) @ 
% 3.03/3.23        (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))),
% 3.03/3.23      inference('clc', [status(thm)], ['111', '112'])).
% 3.03/3.23  thf('114', plain,
% 3.03/3.23      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 3.03/3.23        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.03/3.23      inference('demod', [status(thm)], ['3', '4'])).
% 3.03/3.23  thf('115', plain,
% 3.03/3.23      (![X20 : $i, X21 : $i]:
% 3.03/3.23         (~ (l1_pre_topc @ X20)
% 3.03/3.23          | ~ (v2_pre_topc @ X20)
% 3.03/3.23          | (v2_struct_0 @ X20)
% 3.03/3.23          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 3.03/3.23          | (m1_subset_1 @ (k7_tmap_1 @ X20 @ X21) @ 
% 3.03/3.23             (k1_zfmisc_1 @ 
% 3.03/3.23              (k2_zfmisc_1 @ (u1_struct_0 @ X20) @ 
% 3.03/3.23               (u1_struct_0 @ (k6_tmap_1 @ X20 @ X21))))))),
% 3.03/3.23      inference('cnf', [status(esa)], [dt_k7_tmap_1])).
% 3.03/3.23  thf('116', plain,
% 3.03/3.23      (((m1_subset_1 @ (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)) @ 
% 3.03/3.23         (k1_zfmisc_1 @ 
% 3.03/3.23          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 3.03/3.23           (u1_struct_0 @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B))))))
% 3.03/3.23        | (v2_struct_0 @ sk_A)
% 3.03/3.23        | ~ (v2_pre_topc @ sk_A)
% 3.03/3.23        | ~ (l1_pre_topc @ sk_A))),
% 3.03/3.23      inference('sup-', [status(thm)], ['114', '115'])).
% 3.03/3.23  thf('117', plain,
% 3.03/3.23      (((k8_tmap_1 @ sk_A @ sk_B) = (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))),
% 3.03/3.23      inference('clc', [status(thm)], ['44', '45'])).
% 3.03/3.23  thf('118', plain,
% 3.03/3.23      (((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 3.03/3.23      inference('demod', [status(thm)], ['12', '46'])).
% 3.03/3.23  thf('119', plain, ((v2_pre_topc @ sk_A)),
% 3.03/3.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.03/3.23  thf('120', plain, ((l1_pre_topc @ sk_A)),
% 3.03/3.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.03/3.23  thf('121', plain,
% 3.03/3.23      (((m1_subset_1 @ (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)) @ 
% 3.03/3.23         (k1_zfmisc_1 @ 
% 3.03/3.23          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))))
% 3.03/3.23        | (v2_struct_0 @ sk_A))),
% 3.03/3.23      inference('demod', [status(thm)], ['116', '117', '118', '119', '120'])).
% 3.03/3.23  thf('122', plain, (~ (v2_struct_0 @ sk_A)),
% 3.03/3.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.03/3.23  thf('123', plain,
% 3.03/3.23      ((m1_subset_1 @ (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)) @ 
% 3.03/3.23        (k1_zfmisc_1 @ 
% 3.03/3.23         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))))),
% 3.03/3.23      inference('clc', [status(thm)], ['121', '122'])).
% 3.03/3.23  thf('124', plain,
% 3.03/3.23      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 3.03/3.23        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 3.03/3.23        | ((k9_tmap_1 @ sk_A @ sk_B)
% 3.03/3.23            = (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B))))),
% 3.03/3.23      inference('demod', [status(thm)], ['96', '104', '113', '123'])).
% 3.03/3.23  thf('125', plain,
% 3.03/3.23      ((((k9_tmap_1 @ sk_A @ sk_B) = (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 3.03/3.23        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 3.03/3.23      inference('simplify', [status(thm)], ['124'])).
% 3.03/3.23  thf('126', plain, ((m1_subset_1 @ sk_D_2 @ (u1_struct_0 @ sk_C))),
% 3.03/3.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.03/3.23  thf('127', plain, ((r1_tsep_1 @ sk_B @ sk_C)),
% 3.03/3.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.03/3.23  thf(symmetry_r1_tsep_1, axiom,
% 3.03/3.23    (![A:$i,B:$i]:
% 3.03/3.23     ( ( ( l1_struct_0 @ A ) & ( l1_struct_0 @ B ) ) =>
% 3.03/3.23       ( ( r1_tsep_1 @ A @ B ) => ( r1_tsep_1 @ B @ A ) ) ))).
% 3.03/3.23  thf('128', plain,
% 3.03/3.23      (![X26 : $i, X27 : $i]:
% 3.03/3.23         (~ (l1_struct_0 @ X26)
% 3.03/3.23          | ~ (l1_struct_0 @ X27)
% 3.03/3.23          | (r1_tsep_1 @ X27 @ X26)
% 3.03/3.23          | ~ (r1_tsep_1 @ X26 @ X27))),
% 3.03/3.23      inference('cnf', [status(esa)], [symmetry_r1_tsep_1])).
% 3.03/3.23  thf('129', plain,
% 3.03/3.23      (((r1_tsep_1 @ sk_C @ sk_B)
% 3.03/3.23        | ~ (l1_struct_0 @ sk_C)
% 3.03/3.23        | ~ (l1_struct_0 @ sk_B))),
% 3.03/3.23      inference('sup-', [status(thm)], ['127', '128'])).
% 3.03/3.23  thf('130', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 3.03/3.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.03/3.23  thf(dt_m1_pre_topc, axiom,
% 3.03/3.23    (![A:$i]:
% 3.03/3.23     ( ( l1_pre_topc @ A ) =>
% 3.03/3.23       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 3.03/3.23  thf('131', plain,
% 3.03/3.23      (![X1 : $i, X2 : $i]:
% 3.03/3.23         (~ (m1_pre_topc @ X1 @ X2) | (l1_pre_topc @ X1) | ~ (l1_pre_topc @ X2))),
% 3.03/3.23      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 3.03/3.23  thf('132', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_C))),
% 3.03/3.23      inference('sup-', [status(thm)], ['130', '131'])).
% 3.03/3.23  thf('133', plain, ((l1_pre_topc @ sk_A)),
% 3.03/3.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.03/3.23  thf('134', plain, ((l1_pre_topc @ sk_C)),
% 3.03/3.23      inference('demod', [status(thm)], ['132', '133'])).
% 3.03/3.23  thf(dt_l1_pre_topc, axiom,
% 3.03/3.23    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 3.03/3.23  thf('135', plain, (![X0 : $i]: ((l1_struct_0 @ X0) | ~ (l1_pre_topc @ X0))),
% 3.03/3.23      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 3.03/3.23  thf('136', plain, ((l1_struct_0 @ sk_C)),
% 3.03/3.23      inference('sup-', [status(thm)], ['134', '135'])).
% 3.03/3.23  thf('137', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 3.03/3.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.03/3.23  thf('138', plain,
% 3.03/3.23      (![X1 : $i, X2 : $i]:
% 3.03/3.23         (~ (m1_pre_topc @ X1 @ X2) | (l1_pre_topc @ X1) | ~ (l1_pre_topc @ X2))),
% 3.03/3.23      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 3.03/3.23  thf('139', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_B))),
% 3.03/3.23      inference('sup-', [status(thm)], ['137', '138'])).
% 3.03/3.23  thf('140', plain, ((l1_pre_topc @ sk_A)),
% 3.03/3.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.03/3.23  thf('141', plain, ((l1_pre_topc @ sk_B)),
% 3.03/3.23      inference('demod', [status(thm)], ['139', '140'])).
% 3.03/3.23  thf('142', plain, (![X0 : $i]: ((l1_struct_0 @ X0) | ~ (l1_pre_topc @ X0))),
% 3.03/3.23      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 3.03/3.23  thf('143', plain, ((l1_struct_0 @ sk_B)),
% 3.03/3.23      inference('sup-', [status(thm)], ['141', '142'])).
% 3.03/3.23  thf('144', plain, ((r1_tsep_1 @ sk_C @ sk_B)),
% 3.03/3.23      inference('demod', [status(thm)], ['129', '136', '143'])).
% 3.03/3.23  thf(d3_tsep_1, axiom,
% 3.03/3.23    (![A:$i]:
% 3.03/3.23     ( ( l1_struct_0 @ A ) =>
% 3.03/3.23       ( ![B:$i]:
% 3.03/3.23         ( ( l1_struct_0 @ B ) =>
% 3.03/3.23           ( ( r1_tsep_1 @ A @ B ) <=>
% 3.03/3.23             ( r1_xboole_0 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) ))).
% 3.03/3.23  thf('145', plain,
% 3.03/3.23      (![X18 : $i, X19 : $i]:
% 3.03/3.23         (~ (l1_struct_0 @ X18)
% 3.03/3.23          | ~ (r1_tsep_1 @ X19 @ X18)
% 3.03/3.23          | (r1_xboole_0 @ (u1_struct_0 @ X19) @ (u1_struct_0 @ X18))
% 3.03/3.23          | ~ (l1_struct_0 @ X19))),
% 3.03/3.23      inference('cnf', [status(esa)], [d3_tsep_1])).
% 3.03/3.23  thf('146', plain,
% 3.03/3.23      ((~ (l1_struct_0 @ sk_C)
% 3.03/3.23        | (r1_xboole_0 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))
% 3.03/3.23        | ~ (l1_struct_0 @ sk_B))),
% 3.03/3.23      inference('sup-', [status(thm)], ['144', '145'])).
% 3.03/3.23  thf('147', plain, ((l1_struct_0 @ sk_C)),
% 3.03/3.23      inference('sup-', [status(thm)], ['134', '135'])).
% 3.03/3.23  thf('148', plain, ((l1_struct_0 @ sk_B)),
% 3.03/3.23      inference('sup-', [status(thm)], ['141', '142'])).
% 3.03/3.23  thf('149', plain,
% 3.03/3.23      ((r1_xboole_0 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 3.03/3.23      inference('demod', [status(thm)], ['146', '147', '148'])).
% 3.03/3.23  thf('150', plain,
% 3.03/3.23      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 3.03/3.23        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.03/3.23      inference('demod', [status(thm)], ['3', '4'])).
% 3.03/3.23  thf(t109_tmap_1, axiom,
% 3.03/3.23    (![A:$i]:
% 3.03/3.23     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 3.03/3.23       ( ![B:$i]:
% 3.03/3.23         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 3.03/3.23           ( ![C:$i]:
% 3.03/3.23             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 3.03/3.23               ( ( r1_xboole_0 @ ( u1_struct_0 @ C ) @ B ) =>
% 3.03/3.23                 ( ![D:$i]:
% 3.03/3.23                   ( ( m1_subset_1 @ D @ ( u1_struct_0 @ C ) ) =>
% 3.03/3.23                     ( r1_tmap_1 @
% 3.03/3.23                       C @ ( k6_tmap_1 @ A @ B ) @ 
% 3.03/3.23                       ( k2_tmap_1 @
% 3.03/3.23                         A @ ( k6_tmap_1 @ A @ B ) @ ( k7_tmap_1 @ A @ B ) @ C ) @ 
% 3.03/3.23                       D ) ) ) ) ) ) ) ) ))).
% 3.03/3.23  thf('151', plain,
% 3.03/3.23      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 3.03/3.23         (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ X31)))
% 3.03/3.23          | ~ (r1_xboole_0 @ (u1_struct_0 @ X32) @ X30)
% 3.03/3.23          | ~ (m1_subset_1 @ X33 @ (u1_struct_0 @ X32))
% 3.03/3.23          | (r1_tmap_1 @ X32 @ (k6_tmap_1 @ X31 @ X30) @ 
% 3.03/3.23             (k2_tmap_1 @ X31 @ (k6_tmap_1 @ X31 @ X30) @ 
% 3.03/3.23              (k7_tmap_1 @ X31 @ X30) @ X32) @ 
% 3.03/3.23             X33)
% 3.03/3.23          | ~ (m1_pre_topc @ X32 @ X31)
% 3.03/3.23          | (v2_struct_0 @ X32)
% 3.03/3.23          | ~ (l1_pre_topc @ X31)
% 3.03/3.23          | ~ (v2_pre_topc @ X31)
% 3.03/3.23          | (v2_struct_0 @ X31))),
% 3.03/3.23      inference('cnf', [status(esa)], [t109_tmap_1])).
% 3.03/3.23  thf('152', plain,
% 3.03/3.23      (![X0 : $i, X1 : $i]:
% 3.03/3.23         ((v2_struct_0 @ sk_A)
% 3.03/3.23          | ~ (v2_pre_topc @ sk_A)
% 3.03/3.23          | ~ (l1_pre_topc @ sk_A)
% 3.03/3.23          | (v2_struct_0 @ X0)
% 3.03/3.23          | ~ (m1_pre_topc @ X0 @ sk_A)
% 3.03/3.23          | (r1_tmap_1 @ X0 @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)) @ 
% 3.03/3.23             (k2_tmap_1 @ sk_A @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)) @ 
% 3.03/3.23              (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)) @ X0) @ 
% 3.03/3.23             X1)
% 3.03/3.23          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 3.03/3.23          | ~ (r1_xboole_0 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B)))),
% 3.03/3.23      inference('sup-', [status(thm)], ['150', '151'])).
% 3.03/3.23  thf('153', plain, ((v2_pre_topc @ sk_A)),
% 3.03/3.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.03/3.23  thf('154', plain, ((l1_pre_topc @ sk_A)),
% 3.03/3.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.03/3.23  thf('155', plain,
% 3.03/3.23      (((k8_tmap_1 @ sk_A @ sk_B) = (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))),
% 3.03/3.23      inference('clc', [status(thm)], ['44', '45'])).
% 3.03/3.23  thf('156', plain,
% 3.03/3.23      (((k8_tmap_1 @ sk_A @ sk_B) = (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))),
% 3.03/3.23      inference('clc', [status(thm)], ['44', '45'])).
% 3.03/3.23  thf('157', plain,
% 3.03/3.23      (![X0 : $i, X1 : $i]:
% 3.03/3.23         ((v2_struct_0 @ sk_A)
% 3.03/3.23          | (v2_struct_0 @ X0)
% 3.03/3.23          | ~ (m1_pre_topc @ X0 @ sk_A)
% 3.03/3.23          | (r1_tmap_1 @ X0 @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 3.03/3.23             (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 3.03/3.23              (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)) @ X0) @ 
% 3.03/3.23             X1)
% 3.03/3.23          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 3.03/3.23          | ~ (r1_xboole_0 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B)))),
% 3.03/3.23      inference('demod', [status(thm)], ['152', '153', '154', '155', '156'])).
% 3.03/3.23  thf('158', plain,
% 3.03/3.23      (![X0 : $i]:
% 3.03/3.23         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_C))
% 3.03/3.23          | (r1_tmap_1 @ sk_C @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 3.03/3.23             (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 3.03/3.23              (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)) @ sk_C) @ 
% 3.03/3.23             X0)
% 3.03/3.23          | ~ (m1_pre_topc @ sk_C @ sk_A)
% 3.03/3.23          | (v2_struct_0 @ sk_C)
% 3.03/3.23          | (v2_struct_0 @ sk_A))),
% 3.03/3.23      inference('sup-', [status(thm)], ['149', '157'])).
% 3.03/3.23  thf('159', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 3.03/3.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.03/3.23  thf('160', plain,
% 3.03/3.23      (![X0 : $i]:
% 3.03/3.23         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_C))
% 3.03/3.23          | (r1_tmap_1 @ sk_C @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 3.03/3.23             (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 3.03/3.23              (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)) @ sk_C) @ 
% 3.03/3.23             X0)
% 3.03/3.23          | (v2_struct_0 @ sk_C)
% 3.03/3.23          | (v2_struct_0 @ sk_A))),
% 3.03/3.23      inference('demod', [status(thm)], ['158', '159'])).
% 3.03/3.23  thf('161', plain,
% 3.03/3.23      (((v2_struct_0 @ sk_A)
% 3.03/3.23        | (v2_struct_0 @ sk_C)
% 3.03/3.23        | (r1_tmap_1 @ sk_C @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 3.03/3.23           (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 3.03/3.23            (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)) @ sk_C) @ 
% 3.03/3.23           sk_D_2))),
% 3.03/3.23      inference('sup-', [status(thm)], ['126', '160'])).
% 3.03/3.23  thf('162', plain, (~ (v2_struct_0 @ sk_A)),
% 3.03/3.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.03/3.23  thf('163', plain,
% 3.03/3.23      (((r1_tmap_1 @ sk_C @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 3.03/3.23         (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 3.03/3.23          (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)) @ sk_C) @ 
% 3.03/3.23         sk_D_2)
% 3.03/3.23        | (v2_struct_0 @ sk_C))),
% 3.03/3.23      inference('clc', [status(thm)], ['161', '162'])).
% 3.03/3.23  thf('164', plain, (~ (v2_struct_0 @ sk_C)),
% 3.03/3.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.03/3.23  thf('165', plain,
% 3.03/3.23      ((r1_tmap_1 @ sk_C @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 3.03/3.23        (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 3.03/3.23         (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)) @ sk_C) @ 
% 3.03/3.23        sk_D_2)),
% 3.03/3.23      inference('clc', [status(thm)], ['163', '164'])).
% 3.03/3.23  thf('166', plain,
% 3.03/3.23      (((r1_tmap_1 @ sk_C @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 3.03/3.23         (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 3.03/3.23          (k9_tmap_1 @ sk_A @ sk_B) @ sk_C) @ 
% 3.03/3.23         sk_D_2)
% 3.03/3.23        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 3.03/3.23      inference('sup+', [status(thm)], ['125', '165'])).
% 3.03/3.23  thf('167', plain,
% 3.03/3.23      (~ (r1_tmap_1 @ sk_C @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 3.03/3.23          (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 3.03/3.23           (k9_tmap_1 @ sk_A @ sk_B) @ sk_C) @ 
% 3.03/3.23          sk_D_2)),
% 3.03/3.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.03/3.23  thf('168', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 3.03/3.23      inference('clc', [status(thm)], ['166', '167'])).
% 3.03/3.23  thf(fc2_struct_0, axiom,
% 3.03/3.23    (![A:$i]:
% 3.03/3.23     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 3.03/3.23       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 3.03/3.23  thf('169', plain,
% 3.03/3.23      (![X3 : $i]:
% 3.03/3.23         (~ (v1_xboole_0 @ (u1_struct_0 @ X3))
% 3.03/3.23          | ~ (l1_struct_0 @ X3)
% 3.03/3.23          | (v2_struct_0 @ X3))),
% 3.03/3.23      inference('cnf', [status(esa)], [fc2_struct_0])).
% 3.03/3.23  thf('170', plain, (((v2_struct_0 @ sk_A) | ~ (l1_struct_0 @ sk_A))),
% 3.03/3.23      inference('sup-', [status(thm)], ['168', '169'])).
% 3.03/3.23  thf('171', plain, ((l1_pre_topc @ sk_A)),
% 3.03/3.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.03/3.23  thf('172', plain, (![X0 : $i]: ((l1_struct_0 @ X0) | ~ (l1_pre_topc @ X0))),
% 3.03/3.23      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 3.03/3.23  thf('173', plain, ((l1_struct_0 @ sk_A)),
% 3.03/3.23      inference('sup-', [status(thm)], ['171', '172'])).
% 3.03/3.23  thf('174', plain, ((v2_struct_0 @ sk_A)),
% 3.03/3.23      inference('demod', [status(thm)], ['170', '173'])).
% 3.03/3.23  thf('175', plain, ($false), inference('demod', [status(thm)], ['0', '174'])).
% 3.03/3.23  
% 3.03/3.23  % SZS output end Refutation
% 3.03/3.23  
% 3.03/3.23  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
