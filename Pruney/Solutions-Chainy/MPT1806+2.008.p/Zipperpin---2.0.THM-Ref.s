%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.tkZWCP2C5f

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:11:03 EST 2020

% Result     : Theorem 2.82s
% Output     : Refutation 2.93s
% Verified   : 
% Statistics : Number of formulae       :  276 (7848 expanded)
%              Number of leaves         :   39 (2264 expanded)
%              Depth                    :   30
%              Number of atoms          : 2982 (210483 expanded)
%              Number of equality atoms :   56 (1087 expanded)
%              Maximal formula depth    :   23 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_tsep_1_type,type,(
    v1_tsep_1: $i > $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

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

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k5_tmap_1_type,type,(
    k5_tmap_1: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k7_tmap_1_type,type,(
    k7_tmap_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k6_tmap_1_type,type,(
    k6_tmap_1: $i > $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(r1_funct_2_type,type,(
    r1_funct_2: $i > $i > $i > $i > $i > $i > $o )).

thf(v5_pre_topc_type,type,(
    v5_pre_topc: $i > $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k9_tmap_1_type,type,(
    k9_tmap_1: $i > $i > $i )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(t122_tmap_1,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( ( ( v1_tsep_1 @ B @ A )
              & ( m1_pre_topc @ B @ A ) )
          <=> ( ( v1_funct_1 @ ( k9_tmap_1 @ A @ B ) )
              & ( v1_funct_2 @ ( k9_tmap_1 @ A @ B ) @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ A @ B ) ) )
              & ( v5_pre_topc @ ( k9_tmap_1 @ A @ B ) @ A @ ( k8_tmap_1 @ A @ B ) )
              & ( m1_subset_1 @ ( k9_tmap_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ A @ B ) ) ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( m1_pre_topc @ B @ A )
           => ( ( ( v1_tsep_1 @ B @ A )
                & ( m1_pre_topc @ B @ A ) )
            <=> ( ( v1_funct_1 @ ( k9_tmap_1 @ A @ B ) )
                & ( v1_funct_2 @ ( k9_tmap_1 @ A @ B ) @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ A @ B ) ) )
                & ( v5_pre_topc @ ( k9_tmap_1 @ A @ B ) @ A @ ( k8_tmap_1 @ A @ B ) )
                & ( m1_subset_1 @ ( k9_tmap_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ A @ B ) ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t122_tmap_1])).

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
    ! [X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
      | ( ( u1_struct_0 @ ( k6_tmap_1 @ X27 @ X26 ) )
        = ( u1_struct_0 @ X27 ) )
      | ~ ( l1_pre_topc @ X27 )
      | ~ ( v2_pre_topc @ X27 )
      | ( v2_struct_0 @ X27 ) ) ),
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

thf('13',plain,(
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

thf('14',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ~ ( m1_pre_topc @ X9 @ X10 )
      | ( X11
       != ( k8_tmap_1 @ X10 @ X9 ) )
      | ( X12
       != ( u1_struct_0 @ X9 ) )
      | ( X11
        = ( k6_tmap_1 @ X10 @ X12 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ~ ( l1_pre_topc @ X11 )
      | ~ ( v2_pre_topc @ X11 )
      | ~ ( v1_pre_topc @ X11 )
      | ~ ( l1_pre_topc @ X10 )
      | ~ ( v2_pre_topc @ X10 )
      | ( v2_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d11_tmap_1])).

thf('15',plain,(
    ! [X9: $i,X10: $i] :
      ( ( v2_struct_0 @ X10 )
      | ~ ( v2_pre_topc @ X10 )
      | ~ ( l1_pre_topc @ X10 )
      | ~ ( v1_pre_topc @ ( k8_tmap_1 @ X10 @ X9 ) )
      | ~ ( v2_pre_topc @ ( k8_tmap_1 @ X10 @ X9 ) )
      | ~ ( l1_pre_topc @ ( k8_tmap_1 @ X10 @ X9 ) )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X9 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ( ( k8_tmap_1 @ X10 @ X9 )
        = ( k6_tmap_1 @ X10 @ ( u1_struct_0 @ X9 ) ) )
      | ~ ( m1_pre_topc @ X9 @ X10 ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,
    ( ~ ( m1_pre_topc @ sk_B_1 @ sk_A )
    | ( ( k8_tmap_1 @ sk_A @ sk_B_1 )
      = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B_1 ) ) )
    | ~ ( l1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) )
    | ~ ( v2_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) )
    | ~ ( v1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['13','15'])).

thf('17',plain,(
    m1_pre_topc @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
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

thf('19',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( l1_pre_topc @ X22 )
      | ~ ( v2_pre_topc @ X22 )
      | ( v2_struct_0 @ X22 )
      | ~ ( m1_pre_topc @ X23 @ X22 )
      | ( l1_pre_topc @ ( k8_tmap_1 @ X22 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k8_tmap_1])).

thf('20',plain,
    ( ( l1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) )
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
    ( ( l1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['20','21','22'])).

thf('24',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    l1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) ),
    inference(clc,[status(thm)],['23','24'])).

thf('26',plain,(
    m1_pre_topc @ sk_B_1 @ sk_A ),
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
    ( ( v2_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) )
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
    ( ( v2_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['28','29','30'])).

thf('32',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    v2_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) ),
    inference(clc,[status(thm)],['31','32'])).

thf('34',plain,(
    m1_pre_topc @ sk_B_1 @ sk_A ),
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
    ( ( v1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) )
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
    ( ( v1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['36','37','38'])).

thf('40',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    v1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) ),
    inference(clc,[status(thm)],['39','40'])).

thf('42',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,
    ( ( ( k8_tmap_1 @ sk_A @ sk_B_1 )
      = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B_1 ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['16','17','25','33','41','42','43'])).

thf('45',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( ( k8_tmap_1 @ sk_A @ sk_B_1 )
    = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['44','45'])).

thf('47',plain,
    ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['12','46'])).

thf('48',plain,
    ( ( v1_funct_2 @ ( k9_tmap_1 @ sk_A @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) ) )
    | ( v1_tsep_1 @ sk_B_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( ( v1_funct_2 @ ( k9_tmap_1 @ sk_A @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) ) )
   <= ( v1_funct_2 @ ( k9_tmap_1 @ sk_A @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) ) ) ),
    inference(split,[status(esa)],['48'])).

thf('50',plain,
    ( ( v1_funct_2 @ ( k9_tmap_1 @ sk_A @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
   <= ( v1_funct_2 @ ( k9_tmap_1 @ sk_A @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) ) ) ),
    inference('sup+',[status(thm)],['47','49'])).

thf('51',plain,
    ( ( m1_subset_1 @ ( k9_tmap_1 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) ) ) ) )
    | ( v1_tsep_1 @ sk_B_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,
    ( ( m1_subset_1 @ ( k9_tmap_1 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) ) ) ) )
   <= ( m1_subset_1 @ ( k9_tmap_1 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) ) ) ) ) ),
    inference(split,[status(esa)],['51'])).

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

thf('53',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ~ ( m1_pre_topc @ X13 @ X14 )
      | ( X15
       != ( k9_tmap_1 @ X14 @ X13 ) )
      | ( X16
       != ( u1_struct_0 @ X13 ) )
      | ( r1_funct_2 @ ( u1_struct_0 @ X14 ) @ ( u1_struct_0 @ ( k8_tmap_1 @ X14 @ X13 ) ) @ ( u1_struct_0 @ X14 ) @ ( u1_struct_0 @ ( k6_tmap_1 @ X14 @ X16 ) ) @ X15 @ ( k7_tmap_1 @ X14 @ X16 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X14 ) @ ( u1_struct_0 @ ( k8_tmap_1 @ X14 @ X13 ) ) ) ) )
      | ~ ( v1_funct_2 @ X15 @ ( u1_struct_0 @ X14 ) @ ( u1_struct_0 @ ( k8_tmap_1 @ X14 @ X13 ) ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( l1_pre_topc @ X14 )
      | ~ ( v2_pre_topc @ X14 )
      | ( v2_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d12_tmap_1])).

thf('54',plain,(
    ! [X13: $i,X14: $i] :
      ( ( v2_struct_0 @ X14 )
      | ~ ( v2_pre_topc @ X14 )
      | ~ ( l1_pre_topc @ X14 )
      | ~ ( v1_funct_1 @ ( k9_tmap_1 @ X14 @ X13 ) )
      | ~ ( v1_funct_2 @ ( k9_tmap_1 @ X14 @ X13 ) @ ( u1_struct_0 @ X14 ) @ ( u1_struct_0 @ ( k8_tmap_1 @ X14 @ X13 ) ) )
      | ~ ( m1_subset_1 @ ( k9_tmap_1 @ X14 @ X13 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X14 ) @ ( u1_struct_0 @ ( k8_tmap_1 @ X14 @ X13 ) ) ) ) )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X13 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ( r1_funct_2 @ ( u1_struct_0 @ X14 ) @ ( u1_struct_0 @ ( k8_tmap_1 @ X14 @ X13 ) ) @ ( u1_struct_0 @ X14 ) @ ( u1_struct_0 @ ( k6_tmap_1 @ X14 @ ( u1_struct_0 @ X13 ) ) ) @ ( k9_tmap_1 @ X14 @ X13 ) @ ( k7_tmap_1 @ X14 @ ( u1_struct_0 @ X13 ) ) )
      | ~ ( m1_pre_topc @ X13 @ X14 ) ) ),
    inference(simplify,[status(thm)],['53'])).

thf('55',plain,
    ( ( ~ ( m1_pre_topc @ sk_B_1 @ sk_A )
      | ( r1_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B_1 ) ) ) @ ( k9_tmap_1 @ sk_A @ sk_B_1 ) @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B_1 ) ) )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v1_funct_2 @ ( k9_tmap_1 @ sk_A @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) ) )
      | ~ ( v1_funct_1 @ ( k9_tmap_1 @ sk_A @ sk_B_1 ) )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ( m1_subset_1 @ ( k9_tmap_1 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['52','54'])).

thf('56',plain,(
    m1_pre_topc @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,
    ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['12','46'])).

thf('58',plain,
    ( ( k8_tmap_1 @ sk_A @ sk_B_1 )
    = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['44','45'])).

thf('59',plain,
    ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['12','46'])).

thf('60',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('61',plain,
    ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['12','46'])).

thf('62',plain,(
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

thf('63',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( l1_pre_topc @ X24 )
      | ~ ( v2_pre_topc @ X24 )
      | ( v2_struct_0 @ X24 )
      | ~ ( m1_pre_topc @ X25 @ X24 )
      | ( v1_funct_1 @ ( k9_tmap_1 @ X24 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k9_tmap_1])).

thf('64',plain,
    ( ( v1_funct_1 @ ( k9_tmap_1 @ sk_A @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,
    ( ( v1_funct_1 @ ( k9_tmap_1 @ sk_A @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['64','65','66'])).

thf('68',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    v1_funct_1 @ ( k9_tmap_1 @ sk_A @ sk_B_1 ) ),
    inference(clc,[status(thm)],['67','68'])).

thf('70',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,
    ( ( ( r1_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k9_tmap_1 @ sk_A @ sk_B_1 ) @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B_1 ) ) )
      | ~ ( v1_funct_2 @ ( k9_tmap_1 @ sk_A @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( m1_subset_1 @ ( k9_tmap_1 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) ) ) ) ) ),
    inference(demod,[status(thm)],['55','56','57','58','59','60','61','69','70','71'])).

thf('73',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,
    ( ( ~ ( v1_funct_2 @ ( k9_tmap_1 @ sk_A @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( r1_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k9_tmap_1 @ sk_A @ sk_B_1 ) @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B_1 ) ) ) )
   <= ( m1_subset_1 @ ( k9_tmap_1 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) ) ) ) ) ),
    inference(clc,[status(thm)],['72','73'])).

thf('75',plain,
    ( ( r1_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k9_tmap_1 @ sk_A @ sk_B_1 ) @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B_1 ) ) )
   <= ( ( v1_funct_2 @ ( k9_tmap_1 @ sk_A @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) ) )
      & ( m1_subset_1 @ ( k9_tmap_1 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['50','74'])).

thf('76',plain,(
    m1_pre_topc @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( l1_pre_topc @ X24 )
      | ~ ( v2_pre_topc @ X24 )
      | ( v2_struct_0 @ X24 )
      | ~ ( m1_pre_topc @ X25 @ X24 )
      | ( v1_funct_2 @ ( k9_tmap_1 @ X24 @ X25 ) @ ( u1_struct_0 @ X24 ) @ ( u1_struct_0 @ ( k8_tmap_1 @ X24 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k9_tmap_1])).

thf('78',plain,
    ( ( v1_funct_2 @ ( k9_tmap_1 @ sk_A @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,
    ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['12','46'])).

thf('80',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,
    ( ( v1_funct_2 @ ( k9_tmap_1 @ sk_A @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['78','79','80','81'])).

thf('83',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    v1_funct_2 @ ( k9_tmap_1 @ sk_A @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['82','83'])).

thf('85',plain,
    ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['12','46'])).

thf('86',plain,
    ( ~ ( m1_subset_1 @ ( k9_tmap_1 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) ) ) ) )
    | ~ ( v5_pre_topc @ ( k9_tmap_1 @ sk_A @ sk_B_1 ) @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) )
    | ~ ( v1_funct_2 @ ( k9_tmap_1 @ sk_A @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) ) )
    | ~ ( v1_funct_1 @ ( k9_tmap_1 @ sk_A @ sk_B_1 ) )
    | ~ ( m1_pre_topc @ sk_B_1 @ sk_A )
    | ~ ( v1_tsep_1 @ sk_B_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,
    ( ~ ( v1_funct_2 @ ( k9_tmap_1 @ sk_A @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) ) )
   <= ~ ( v1_funct_2 @ ( k9_tmap_1 @ sk_A @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) ) ) ),
    inference(split,[status(esa)],['86'])).

thf('88',plain,
    ( ~ ( v1_funct_2 @ ( k9_tmap_1 @ sk_A @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_funct_2 @ ( k9_tmap_1 @ sk_A @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['85','87'])).

thf('89',plain,(
    v1_funct_2 @ ( k9_tmap_1 @ sk_A @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['84','88'])).

thf('90',plain,(
    v1_funct_2 @ ( k9_tmap_1 @ sk_A @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sat_resolution*',[status(thm)],['89'])).

thf('91',plain,
    ( ( r1_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k9_tmap_1 @ sk_A @ sk_B_1 ) @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B_1 ) ) )
   <= ( m1_subset_1 @ ( k9_tmap_1 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) ) ) ) ) ),
    inference(simpl_trail,[status(thm)],['75','90'])).

thf('92',plain,(
    m1_pre_topc @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( l1_pre_topc @ X24 )
      | ~ ( v2_pre_topc @ X24 )
      | ( v2_struct_0 @ X24 )
      | ~ ( m1_pre_topc @ X25 @ X24 )
      | ( m1_subset_1 @ ( k9_tmap_1 @ X24 @ X25 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X24 ) @ ( u1_struct_0 @ ( k8_tmap_1 @ X24 @ X25 ) ) ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k9_tmap_1])).

thf('94',plain,
    ( ( m1_subset_1 @ ( k9_tmap_1 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) ) ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,
    ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['12','46'])).

thf('96',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,
    ( ( m1_subset_1 @ ( k9_tmap_1 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['94','95','96','97'])).

thf('99',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    m1_subset_1 @ ( k9_tmap_1 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['98','99'])).

thf('101',plain,
    ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['12','46'])).

thf('102',plain,
    ( ~ ( m1_subset_1 @ ( k9_tmap_1 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) ) ) ) )
   <= ~ ( m1_subset_1 @ ( k9_tmap_1 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) ) ) ) ) ),
    inference(split,[status(esa)],['86'])).

thf('103',plain,
    ( ~ ( m1_subset_1 @ ( k9_tmap_1 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ~ ( m1_subset_1 @ ( k9_tmap_1 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,(
    m1_subset_1 @ ( k9_tmap_1 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['100','103'])).

thf('105',plain,(
    m1_subset_1 @ ( k9_tmap_1 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) ) ) ) ),
    inference('sat_resolution*',[status(thm)],['104'])).

thf('106',plain,(
    r1_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k9_tmap_1 @ sk_A @ sk_B_1 ) @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference(simpl_trail,[status(thm)],['91','105'])).

thf('107',plain,(
    m1_subset_1 @ ( k9_tmap_1 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['98','99'])).

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

thf('108',plain,(
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

thf('109',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ X2 @ X1 @ ( k9_tmap_1 @ sk_A @ sk_B_1 ) @ X0 )
      | ( ( k9_tmap_1 @ sk_A @ sk_B_1 )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_2 @ X0 @ X2 @ X1 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ X1 )
      | ~ ( v1_funct_1 @ ( k9_tmap_1 @ sk_A @ sk_B_1 ) )
      | ~ ( v1_funct_2 @ ( k9_tmap_1 @ sk_A @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['107','108'])).

thf('110',plain,(
    v1_funct_1 @ ( k9_tmap_1 @ sk_A @ sk_B_1 ) ),
    inference(clc,[status(thm)],['67','68'])).

thf('111',plain,(
    v1_funct_2 @ ( k9_tmap_1 @ sk_A @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['82','83'])).

thf('112',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ X2 @ X1 @ ( k9_tmap_1 @ sk_A @ sk_B_1 ) @ X0 )
      | ( ( k9_tmap_1 @ sk_A @ sk_B_1 )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_2 @ X0 @ X2 @ X1 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ X1 ) ) ),
    inference(demod,[status(thm)],['109','110','111'])).

thf('113',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_funct_1 @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B_1 ) ) )
    | ~ ( v1_funct_2 @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B_1 ) ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( m1_subset_1 @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B_1 ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ( ( k9_tmap_1 @ sk_A @ sk_B_1 )
      = ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['106','112'])).

thf('114',plain,(
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

thf('115',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( l1_pre_topc @ X20 )
      | ~ ( v2_pre_topc @ X20 )
      | ( v2_struct_0 @ X20 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ( v1_funct_1 @ ( k7_tmap_1 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_tmap_1])).

thf('116',plain,
    ( ( v1_funct_1 @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B_1 ) ) )
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
    ( ( v1_funct_1 @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B_1 ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['116','117','118'])).

thf('120',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('121',plain,(
    v1_funct_1 @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['119','120'])).

thf('122',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('123',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( l1_pre_topc @ X20 )
      | ~ ( v2_pre_topc @ X20 )
      | ( v2_struct_0 @ X20 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ( v1_funct_2 @ ( k7_tmap_1 @ X20 @ X21 ) @ ( u1_struct_0 @ X20 ) @ ( u1_struct_0 @ ( k6_tmap_1 @ X20 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_tmap_1])).

thf('124',plain,
    ( ( v1_funct_2 @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B_1 ) ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B_1 ) ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['122','123'])).

thf('125',plain,
    ( ( k8_tmap_1 @ sk_A @ sk_B_1 )
    = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['44','45'])).

thf('126',plain,
    ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['12','46'])).

thf('127',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('128',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('129',plain,
    ( ( v1_funct_2 @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B_1 ) ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['124','125','126','127','128'])).

thf('130',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('131',plain,(
    v1_funct_2 @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B_1 ) ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['129','130'])).

thf('132',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('133',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( l1_pre_topc @ X20 )
      | ~ ( v2_pre_topc @ X20 )
      | ( v2_struct_0 @ X20 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ( m1_subset_1 @ ( k7_tmap_1 @ X20 @ X21 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X20 ) @ ( u1_struct_0 @ ( k6_tmap_1 @ X20 @ X21 ) ) ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_tmap_1])).

thf('134',plain,
    ( ( m1_subset_1 @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B_1 ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B_1 ) ) ) ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['132','133'])).

thf('135',plain,
    ( ( k8_tmap_1 @ sk_A @ sk_B_1 )
    = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['44','45'])).

thf('136',plain,
    ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['12','46'])).

thf('137',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('138',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('139',plain,
    ( ( m1_subset_1 @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B_1 ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['134','135','136','137','138'])).

thf('140',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('141',plain,(
    m1_subset_1 @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B_1 ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['139','140'])).

thf('142',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( ( k9_tmap_1 @ sk_A @ sk_B_1 )
      = ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['113','121','131','141'])).

thf('143',plain,
    ( ( ( k9_tmap_1 @ sk_A @ sk_B_1 )
      = ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B_1 ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['142'])).

thf('144',plain,
    ( ( k8_tmap_1 @ sk_A @ sk_B_1 )
    = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['44','45'])).

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

thf('145',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) )
      | ~ ( v1_funct_1 @ ( k7_tmap_1 @ X29 @ X28 ) )
      | ~ ( v1_funct_2 @ ( k7_tmap_1 @ X29 @ X28 ) @ ( u1_struct_0 @ X29 ) @ ( u1_struct_0 @ ( k6_tmap_1 @ X29 @ X28 ) ) )
      | ~ ( v5_pre_topc @ ( k7_tmap_1 @ X29 @ X28 ) @ X29 @ ( k6_tmap_1 @ X29 @ X28 ) )
      | ~ ( m1_subset_1 @ ( k7_tmap_1 @ X29 @ X28 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X29 ) @ ( u1_struct_0 @ ( k6_tmap_1 @ X29 @ X28 ) ) ) ) )
      | ( v3_pre_topc @ X28 @ X29 )
      | ~ ( l1_pre_topc @ X29 )
      | ~ ( v2_pre_topc @ X29 )
      | ( v2_struct_0 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t113_tmap_1])).

thf('146',plain,
    ( ~ ( m1_subset_1 @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B_1 ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) ) ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v3_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ sk_A )
    | ~ ( v5_pre_topc @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B_1 ) ) @ sk_A @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B_1 ) ) )
    | ~ ( v1_funct_2 @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B_1 ) ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B_1 ) ) ) )
    | ~ ( v1_funct_1 @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B_1 ) ) )
    | ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['144','145'])).

thf('147',plain,
    ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['12','46'])).

thf('148',plain,(
    m1_subset_1 @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B_1 ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['139','140'])).

thf('149',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('150',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('151',plain,
    ( ( k8_tmap_1 @ sk_A @ sk_B_1 )
    = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['44','45'])).

thf('152',plain,
    ( ( k8_tmap_1 @ sk_A @ sk_B_1 )
    = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['44','45'])).

thf('153',plain,
    ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['12','46'])).

thf('154',plain,(
    v1_funct_2 @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B_1 ) ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['129','130'])).

thf('155',plain,(
    v1_funct_1 @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['119','120'])).

thf('156',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('157',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v3_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ sk_A )
    | ~ ( v5_pre_topc @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B_1 ) ) @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['146','147','148','149','150','151','152','153','154','155','156'])).

thf('158',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('159',plain,
    ( ~ ( v5_pre_topc @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B_1 ) ) @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) )
    | ( v3_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ sk_A ) ),
    inference(clc,[status(thm)],['157','158'])).

thf('160',plain,
    ( ~ ( v5_pre_topc @ ( k9_tmap_1 @ sk_A @ sk_B_1 ) @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v3_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['143','159'])).

thf('161',plain,
    ( ( v5_pre_topc @ ( k9_tmap_1 @ sk_A @ sk_B_1 ) @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) )
    | ( v1_tsep_1 @ sk_B_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('162',plain,
    ( ( v5_pre_topc @ ( k9_tmap_1 @ sk_A @ sk_B_1 ) @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) )
   <= ( v5_pre_topc @ ( k9_tmap_1 @ sk_A @ sk_B_1 ) @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['161'])).

thf('163',plain,
    ( ( ( k9_tmap_1 @ sk_A @ sk_B_1 )
      = ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B_1 ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['142'])).

thf('164',plain,
    ( ( v1_funct_1 @ ( k9_tmap_1 @ sk_A @ sk_B_1 ) )
    | ( v1_tsep_1 @ sk_B_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('165',plain,
    ( ( v1_tsep_1 @ sk_B_1 @ sk_A )
   <= ( v1_tsep_1 @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['164'])).

thf('166',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf(d1_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( ( v1_tsep_1 @ B @ A )
          <=> ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
               => ( ( C
                    = ( u1_struct_0 @ B ) )
                 => ( v3_pre_topc @ C @ A ) ) ) ) ) ) )).

thf('167',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_pre_topc @ X17 @ X18 )
      | ~ ( v1_tsep_1 @ X17 @ X18 )
      | ( X19
       != ( u1_struct_0 @ X17 ) )
      | ( v3_pre_topc @ X19 @ X18 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( l1_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[d1_tsep_1])).

thf('168',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( l1_pre_topc @ X18 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X17 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ( v3_pre_topc @ ( u1_struct_0 @ X17 ) @ X18 )
      | ~ ( v1_tsep_1 @ X17 @ X18 )
      | ~ ( m1_pre_topc @ X17 @ X18 ) ) ),
    inference(simplify,[status(thm)],['167'])).

thf('169',plain,
    ( ~ ( m1_pre_topc @ sk_B_1 @ sk_A )
    | ~ ( v1_tsep_1 @ sk_B_1 @ sk_A )
    | ( v3_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['166','168'])).

thf('170',plain,(
    m1_pre_topc @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('171',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('172',plain,
    ( ~ ( v1_tsep_1 @ sk_B_1 @ sk_A )
    | ( v3_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ sk_A ) ),
    inference(demod,[status(thm)],['169','170','171'])).

thf('173',plain,
    ( ( v3_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ sk_A )
   <= ( v1_tsep_1 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['165','172'])).

thf('174',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('175',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) )
      | ~ ( v3_pre_topc @ X28 @ X29 )
      | ( v5_pre_topc @ ( k7_tmap_1 @ X29 @ X28 ) @ X29 @ ( k6_tmap_1 @ X29 @ X28 ) )
      | ~ ( l1_pre_topc @ X29 )
      | ~ ( v2_pre_topc @ X29 )
      | ( v2_struct_0 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t113_tmap_1])).

thf('176',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v5_pre_topc @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B_1 ) ) @ sk_A @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B_1 ) ) )
    | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['174','175'])).

thf('177',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('178',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('179',plain,
    ( ( k8_tmap_1 @ sk_A @ sk_B_1 )
    = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['44','45'])).

thf('180',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v5_pre_topc @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B_1 ) ) @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) )
    | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ sk_A ) ),
    inference(demod,[status(thm)],['176','177','178','179'])).

thf('181',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('182',plain,
    ( ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ sk_A )
    | ( v5_pre_topc @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B_1 ) ) @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['180','181'])).

thf('183',plain,
    ( ( v5_pre_topc @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B_1 ) ) @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) )
   <= ( v1_tsep_1 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['173','182'])).

thf('184',plain,
    ( ( ( v5_pre_topc @ ( k9_tmap_1 @ sk_A @ sk_B_1 ) @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( v1_tsep_1 @ sk_B_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['163','183'])).

thf('185',plain,(
    v1_funct_2 @ ( k9_tmap_1 @ sk_A @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['82','83'])).

thf('186',plain,
    ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['12','46'])).

thf('187',plain,
    ( ( m1_subset_1 @ ( k9_tmap_1 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) ) ) ) )
   <= ( m1_subset_1 @ ( k9_tmap_1 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) ) ) ) ) ),
    inference(split,[status(esa)],['51'])).

thf('188',plain,
    ( ( m1_subset_1 @ ( k9_tmap_1 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ( m1_subset_1 @ ( k9_tmap_1 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) ) ) ) ) ),
    inference('sup+',[status(thm)],['186','187'])).

thf('189',plain,
    ( ~ ( m1_subset_1 @ ( k9_tmap_1 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) ) ) ) )
    | ~ ( v5_pre_topc @ ( k9_tmap_1 @ sk_A @ sk_B_1 ) @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) )
    | ~ ( v1_funct_2 @ ( k9_tmap_1 @ sk_A @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) ) )
    | ~ ( v1_funct_1 @ ( k9_tmap_1 @ sk_A @ sk_B_1 ) )
    | ~ ( m1_pre_topc @ sk_B_1 @ sk_A )
    | ~ ( v1_tsep_1 @ sk_B_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('190',plain,
    ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['12','46'])).

thf('191',plain,
    ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['12','46'])).

thf('192',plain,(
    v1_funct_1 @ ( k9_tmap_1 @ sk_A @ sk_B_1 ) ),
    inference(clc,[status(thm)],['67','68'])).

thf('193',plain,(
    m1_pre_topc @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('194',plain,
    ( ~ ( m1_subset_1 @ ( k9_tmap_1 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ~ ( v5_pre_topc @ ( k9_tmap_1 @ sk_A @ sk_B_1 ) @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) )
    | ~ ( v1_funct_2 @ ( k9_tmap_1 @ sk_A @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_tsep_1 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['189','190','191','192','193'])).

thf('195',plain,
    ( ( ~ ( v1_tsep_1 @ sk_B_1 @ sk_A )
      | ~ ( v1_funct_2 @ ( k9_tmap_1 @ sk_A @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v5_pre_topc @ ( k9_tmap_1 @ sk_A @ sk_B_1 ) @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) ) )
   <= ( m1_subset_1 @ ( k9_tmap_1 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['188','194'])).

thf('196',plain,
    ( ( ~ ( v5_pre_topc @ ( k9_tmap_1 @ sk_A @ sk_B_1 ) @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) )
      | ~ ( v1_tsep_1 @ sk_B_1 @ sk_A ) )
   <= ( m1_subset_1 @ ( k9_tmap_1 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['185','195'])).

thf('197',plain,(
    m1_subset_1 @ ( k9_tmap_1 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) ) ) ) ),
    inference('sat_resolution*',[status(thm)],['104'])).

thf('198',plain,
    ( ~ ( v5_pre_topc @ ( k9_tmap_1 @ sk_A @ sk_B_1 ) @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) )
    | ~ ( v1_tsep_1 @ sk_B_1 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['196','197'])).

thf('199',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_tsep_1 @ sk_B_1 @ sk_A ) )
   <= ( v1_tsep_1 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['184','198'])).

thf('200',plain,
    ( ( v1_tsep_1 @ sk_B_1 @ sk_A )
   <= ( v1_tsep_1 @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['164'])).

thf('201',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
   <= ( v1_tsep_1 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['199','200'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('202',plain,(
    ! [X2: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X2 ) )
      | ~ ( l1_struct_0 @ X2 )
      | ( v2_struct_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('203',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( v1_tsep_1 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['201','202'])).

thf('204',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('205',plain,(
    ! [X0: $i] :
      ( ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('206',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['204','205'])).

thf('207',plain,
    ( ( v2_struct_0 @ sk_A )
   <= ( v1_tsep_1 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['203','206'])).

thf('208',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('209',plain,(
    ~ ( v1_tsep_1 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['207','208'])).

thf('210',plain,
    ( ( v5_pre_topc @ ( k9_tmap_1 @ sk_A @ sk_B_1 ) @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) )
    | ( v1_tsep_1 @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['161'])).

thf('211',plain,(
    v5_pre_topc @ ( k9_tmap_1 @ sk_A @ sk_B_1 ) @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) ),
    inference('sat_resolution*',[status(thm)],['209','210'])).

thf('212',plain,(
    v5_pre_topc @ ( k9_tmap_1 @ sk_A @ sk_B_1 ) @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) ),
    inference(simpl_trail,[status(thm)],['162','211'])).

thf('213',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v3_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ sk_A ) ),
    inference(demod,[status(thm)],['160','212'])).

thf('214',plain,(
    m1_pre_topc @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('215',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( m1_pre_topc @ X17 @ X18 )
      | ( ( sk_C @ X17 @ X18 )
        = ( u1_struct_0 @ X17 ) )
      | ( v1_tsep_1 @ X17 @ X18 )
      | ~ ( l1_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[d1_tsep_1])).

thf('216',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v1_tsep_1 @ sk_B_1 @ sk_A )
    | ( ( sk_C @ sk_B_1 @ sk_A )
      = ( u1_struct_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['214','215'])).

thf('217',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('218',plain,
    ( ( v1_tsep_1 @ sk_B_1 @ sk_A )
    | ( ( sk_C @ sk_B_1 @ sk_A )
      = ( u1_struct_0 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['216','217'])).

thf('219',plain,
    ( ~ ( v1_tsep_1 @ sk_B_1 @ sk_A )
   <= ~ ( v1_tsep_1 @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['86'])).

thf('220',plain,
    ( ( ( sk_C @ sk_B_1 @ sk_A )
      = ( u1_struct_0 @ sk_B_1 ) )
   <= ~ ( v1_tsep_1 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['218','219'])).

thf('221',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( m1_pre_topc @ X17 @ X18 )
      | ~ ( v3_pre_topc @ ( sk_C @ X17 @ X18 ) @ X18 )
      | ( v1_tsep_1 @ X17 @ X18 )
      | ~ ( l1_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[d1_tsep_1])).

thf('222',plain,
    ( ( ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v1_tsep_1 @ sk_B_1 @ sk_A )
      | ~ ( m1_pre_topc @ sk_B_1 @ sk_A ) )
   <= ~ ( v1_tsep_1 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['220','221'])).

thf('223',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('224',plain,(
    m1_pre_topc @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('225',plain,
    ( ( ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ sk_A )
      | ( v1_tsep_1 @ sk_B_1 @ sk_A ) )
   <= ~ ( v1_tsep_1 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['222','223','224'])).

thf('226',plain,
    ( ~ ( v1_tsep_1 @ sk_B_1 @ sk_A )
   <= ~ ( v1_tsep_1 @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['86'])).

thf('227',plain,
    ( ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ sk_A )
   <= ~ ( v1_tsep_1 @ sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['225','226'])).

thf('228',plain,(
    ~ ( v1_tsep_1 @ sk_B_1 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['209'])).

thf('229',plain,(
    ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['227','228'])).

thf('230',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['213','229'])).

thf('231',plain,(
    ! [X2: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X2 ) )
      | ~ ( l1_struct_0 @ X2 )
      | ( v2_struct_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('232',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['230','231'])).

thf('233',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['204','205'])).

thf('234',plain,(
    v2_struct_0 @ sk_A ),
    inference(demod,[status(thm)],['232','233'])).

thf('235',plain,(
    $false ),
    inference(demod,[status(thm)],['0','234'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.tkZWCP2C5f
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:04:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 2.82/3.09  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 2.82/3.09  % Solved by: fo/fo7.sh
% 2.82/3.09  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.82/3.09  % done 1164 iterations in 2.626s
% 2.82/3.09  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 2.82/3.09  % SZS output start Refutation
% 2.82/3.09  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 2.82/3.09  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 2.82/3.09  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 2.82/3.09  thf(v1_tsep_1_type, type, v1_tsep_1: $i > $i > $o).
% 2.82/3.09  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 2.82/3.09  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 2.82/3.09  thf(k8_tmap_1_type, type, k8_tmap_1: $i > $i > $i).
% 2.82/3.09  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 2.82/3.09  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 2.82/3.09  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 2.82/3.09  thf(sk_A_type, type, sk_A: $i).
% 2.82/3.09  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 2.82/3.09  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 2.82/3.09  thf(k5_tmap_1_type, type, k5_tmap_1: $i > $i > $i).
% 2.82/3.09  thf(sk_B_1_type, type, sk_B_1: $i).
% 2.82/3.09  thf(k7_tmap_1_type, type, k7_tmap_1: $i > $i > $i).
% 2.82/3.09  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 2.82/3.09  thf(k6_tmap_1_type, type, k6_tmap_1: $i > $i > $i).
% 2.82/3.09  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 2.82/3.09  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 2.82/3.09  thf(r1_funct_2_type, type, r1_funct_2: $i > $i > $i > $i > $i > $i > $o).
% 2.82/3.09  thf(v5_pre_topc_type, type, v5_pre_topc: $i > $i > $i > $o).
% 2.82/3.09  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 2.82/3.09  thf(k9_tmap_1_type, type, k9_tmap_1: $i > $i > $i).
% 2.82/3.09  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 2.82/3.09  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 2.82/3.09  thf(t122_tmap_1, conjecture,
% 2.82/3.09    (![A:$i]:
% 2.82/3.09     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 2.82/3.09       ( ![B:$i]:
% 2.82/3.09         ( ( m1_pre_topc @ B @ A ) =>
% 2.82/3.09           ( ( ( v1_tsep_1 @ B @ A ) & ( m1_pre_topc @ B @ A ) ) <=>
% 2.82/3.09             ( ( v1_funct_1 @ ( k9_tmap_1 @ A @ B ) ) & 
% 2.82/3.09               ( v1_funct_2 @
% 2.82/3.09                 ( k9_tmap_1 @ A @ B ) @ ( u1_struct_0 @ A ) @ 
% 2.82/3.09                 ( u1_struct_0 @ ( k8_tmap_1 @ A @ B ) ) ) & 
% 2.82/3.09               ( v5_pre_topc @
% 2.82/3.09                 ( k9_tmap_1 @ A @ B ) @ A @ ( k8_tmap_1 @ A @ B ) ) & 
% 2.82/3.09               ( m1_subset_1 @
% 2.82/3.09                 ( k9_tmap_1 @ A @ B ) @ 
% 2.82/3.09                 ( k1_zfmisc_1 @
% 2.82/3.09                   ( k2_zfmisc_1 @
% 2.82/3.09                     ( u1_struct_0 @ A ) @ 
% 2.82/3.09                     ( u1_struct_0 @ ( k8_tmap_1 @ A @ B ) ) ) ) ) ) ) ) ) ))).
% 2.82/3.09  thf(zf_stmt_0, negated_conjecture,
% 2.82/3.09    (~( ![A:$i]:
% 2.82/3.09        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 2.82/3.09            ( l1_pre_topc @ A ) ) =>
% 2.82/3.09          ( ![B:$i]:
% 2.82/3.09            ( ( m1_pre_topc @ B @ A ) =>
% 2.82/3.09              ( ( ( v1_tsep_1 @ B @ A ) & ( m1_pre_topc @ B @ A ) ) <=>
% 2.82/3.09                ( ( v1_funct_1 @ ( k9_tmap_1 @ A @ B ) ) & 
% 2.82/3.09                  ( v1_funct_2 @
% 2.82/3.09                    ( k9_tmap_1 @ A @ B ) @ ( u1_struct_0 @ A ) @ 
% 2.82/3.09                    ( u1_struct_0 @ ( k8_tmap_1 @ A @ B ) ) ) & 
% 2.82/3.09                  ( v5_pre_topc @
% 2.82/3.09                    ( k9_tmap_1 @ A @ B ) @ A @ ( k8_tmap_1 @ A @ B ) ) & 
% 2.82/3.09                  ( m1_subset_1 @
% 2.82/3.09                    ( k9_tmap_1 @ A @ B ) @ 
% 2.82/3.09                    ( k1_zfmisc_1 @
% 2.82/3.09                      ( k2_zfmisc_1 @
% 2.82/3.09                        ( u1_struct_0 @ A ) @ 
% 2.82/3.09                        ( u1_struct_0 @ ( k8_tmap_1 @ A @ B ) ) ) ) ) ) ) ) ) ) )),
% 2.82/3.09    inference('cnf.neg', [status(esa)], [t122_tmap_1])).
% 2.82/3.09  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 2.82/3.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.82/3.09  thf('1', plain, ((m1_pre_topc @ sk_B_1 @ sk_A)),
% 2.82/3.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.82/3.09  thf(t1_tsep_1, axiom,
% 2.82/3.09    (![A:$i]:
% 2.82/3.09     ( ( l1_pre_topc @ A ) =>
% 2.82/3.09       ( ![B:$i]:
% 2.82/3.09         ( ( m1_pre_topc @ B @ A ) =>
% 2.82/3.09           ( m1_subset_1 @
% 2.82/3.09             ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 2.82/3.09  thf('2', plain,
% 2.82/3.09      (![X30 : $i, X31 : $i]:
% 2.82/3.09         (~ (m1_pre_topc @ X30 @ X31)
% 2.82/3.09          | (m1_subset_1 @ (u1_struct_0 @ X30) @ 
% 2.82/3.09             (k1_zfmisc_1 @ (u1_struct_0 @ X31)))
% 2.82/3.09          | ~ (l1_pre_topc @ X31))),
% 2.82/3.09      inference('cnf', [status(esa)], [t1_tsep_1])).
% 2.82/3.09  thf('3', plain,
% 2.82/3.09      ((~ (l1_pre_topc @ sk_A)
% 2.82/3.09        | (m1_subset_1 @ (u1_struct_0 @ sk_B_1) @ 
% 2.82/3.09           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 2.82/3.09      inference('sup-', [status(thm)], ['1', '2'])).
% 2.82/3.09  thf('4', plain, ((l1_pre_topc @ sk_A)),
% 2.82/3.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.82/3.09  thf('5', plain,
% 2.82/3.09      ((m1_subset_1 @ (u1_struct_0 @ sk_B_1) @ 
% 2.82/3.09        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.82/3.09      inference('demod', [status(thm)], ['3', '4'])).
% 2.82/3.09  thf(t104_tmap_1, axiom,
% 2.82/3.09    (![A:$i]:
% 2.82/3.09     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 2.82/3.09       ( ![B:$i]:
% 2.82/3.09         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.82/3.09           ( ( ( u1_struct_0 @ ( k6_tmap_1 @ A @ B ) ) = ( u1_struct_0 @ A ) ) & 
% 2.82/3.09             ( ( u1_pre_topc @ ( k6_tmap_1 @ A @ B ) ) = ( k5_tmap_1 @ A @ B ) ) ) ) ) ))).
% 2.82/3.09  thf('6', plain,
% 2.82/3.09      (![X26 : $i, X27 : $i]:
% 2.82/3.09         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 2.82/3.09          | ((u1_struct_0 @ (k6_tmap_1 @ X27 @ X26)) = (u1_struct_0 @ X27))
% 2.82/3.09          | ~ (l1_pre_topc @ X27)
% 2.82/3.09          | ~ (v2_pre_topc @ X27)
% 2.82/3.09          | (v2_struct_0 @ X27))),
% 2.82/3.09      inference('cnf', [status(esa)], [t104_tmap_1])).
% 2.82/3.09  thf('7', plain,
% 2.82/3.09      (((v2_struct_0 @ sk_A)
% 2.82/3.09        | ~ (v2_pre_topc @ sk_A)
% 2.82/3.09        | ~ (l1_pre_topc @ sk_A)
% 2.82/3.09        | ((u1_struct_0 @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B_1)))
% 2.82/3.09            = (u1_struct_0 @ sk_A)))),
% 2.82/3.09      inference('sup-', [status(thm)], ['5', '6'])).
% 2.82/3.09  thf('8', plain, ((v2_pre_topc @ sk_A)),
% 2.82/3.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.82/3.09  thf('9', plain, ((l1_pre_topc @ sk_A)),
% 2.82/3.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.82/3.09  thf('10', plain,
% 2.82/3.09      (((v2_struct_0 @ sk_A)
% 2.82/3.09        | ((u1_struct_0 @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B_1)))
% 2.82/3.09            = (u1_struct_0 @ sk_A)))),
% 2.82/3.09      inference('demod', [status(thm)], ['7', '8', '9'])).
% 2.82/3.09  thf('11', plain, (~ (v2_struct_0 @ sk_A)),
% 2.82/3.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.82/3.09  thf('12', plain,
% 2.82/3.09      (((u1_struct_0 @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B_1)))
% 2.82/3.09         = (u1_struct_0 @ sk_A))),
% 2.82/3.09      inference('clc', [status(thm)], ['10', '11'])).
% 2.82/3.09  thf('13', plain,
% 2.82/3.09      ((m1_subset_1 @ (u1_struct_0 @ sk_B_1) @ 
% 2.82/3.09        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.82/3.09      inference('demod', [status(thm)], ['3', '4'])).
% 2.82/3.09  thf(d11_tmap_1, axiom,
% 2.82/3.09    (![A:$i]:
% 2.82/3.09     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 2.82/3.09       ( ![B:$i]:
% 2.82/3.09         ( ( m1_pre_topc @ B @ A ) =>
% 2.82/3.09           ( ![C:$i]:
% 2.82/3.09             ( ( ( v1_pre_topc @ C ) & ( v2_pre_topc @ C ) & 
% 2.82/3.09                 ( l1_pre_topc @ C ) ) =>
% 2.82/3.09               ( ( ( C ) = ( k8_tmap_1 @ A @ B ) ) <=>
% 2.82/3.09                 ( ![D:$i]:
% 2.82/3.09                   ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.82/3.09                     ( ( ( D ) = ( u1_struct_0 @ B ) ) =>
% 2.82/3.09                       ( ( C ) = ( k6_tmap_1 @ A @ D ) ) ) ) ) ) ) ) ) ) ))).
% 2.82/3.09  thf('14', plain,
% 2.82/3.09      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 2.82/3.09         (~ (m1_pre_topc @ X9 @ X10)
% 2.82/3.09          | ((X11) != (k8_tmap_1 @ X10 @ X9))
% 2.82/3.09          | ((X12) != (u1_struct_0 @ X9))
% 2.82/3.09          | ((X11) = (k6_tmap_1 @ X10 @ X12))
% 2.82/3.09          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 2.82/3.09          | ~ (l1_pre_topc @ X11)
% 2.82/3.09          | ~ (v2_pre_topc @ X11)
% 2.82/3.09          | ~ (v1_pre_topc @ X11)
% 2.82/3.09          | ~ (l1_pre_topc @ X10)
% 2.82/3.09          | ~ (v2_pre_topc @ X10)
% 2.82/3.09          | (v2_struct_0 @ X10))),
% 2.82/3.09      inference('cnf', [status(esa)], [d11_tmap_1])).
% 2.82/3.09  thf('15', plain,
% 2.82/3.09      (![X9 : $i, X10 : $i]:
% 2.82/3.09         ((v2_struct_0 @ X10)
% 2.82/3.09          | ~ (v2_pre_topc @ X10)
% 2.82/3.09          | ~ (l1_pre_topc @ X10)
% 2.82/3.09          | ~ (v1_pre_topc @ (k8_tmap_1 @ X10 @ X9))
% 2.82/3.09          | ~ (v2_pre_topc @ (k8_tmap_1 @ X10 @ X9))
% 2.82/3.09          | ~ (l1_pre_topc @ (k8_tmap_1 @ X10 @ X9))
% 2.82/3.09          | ~ (m1_subset_1 @ (u1_struct_0 @ X9) @ 
% 2.82/3.09               (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 2.82/3.09          | ((k8_tmap_1 @ X10 @ X9) = (k6_tmap_1 @ X10 @ (u1_struct_0 @ X9)))
% 2.82/3.09          | ~ (m1_pre_topc @ X9 @ X10))),
% 2.82/3.09      inference('simplify', [status(thm)], ['14'])).
% 2.82/3.09  thf('16', plain,
% 2.82/3.09      ((~ (m1_pre_topc @ sk_B_1 @ sk_A)
% 2.82/3.09        | ((k8_tmap_1 @ sk_A @ sk_B_1)
% 2.82/3.09            = (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B_1)))
% 2.82/3.09        | ~ (l1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B_1))
% 2.82/3.09        | ~ (v2_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B_1))
% 2.82/3.09        | ~ (v1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B_1))
% 2.82/3.09        | ~ (l1_pre_topc @ sk_A)
% 2.82/3.09        | ~ (v2_pre_topc @ sk_A)
% 2.82/3.09        | (v2_struct_0 @ sk_A))),
% 2.82/3.09      inference('sup-', [status(thm)], ['13', '15'])).
% 2.82/3.09  thf('17', plain, ((m1_pre_topc @ sk_B_1 @ sk_A)),
% 2.82/3.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.82/3.09  thf('18', plain, ((m1_pre_topc @ sk_B_1 @ sk_A)),
% 2.82/3.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.82/3.09  thf(dt_k8_tmap_1, axiom,
% 2.82/3.09    (![A:$i,B:$i]:
% 2.82/3.09     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 2.82/3.09         ( l1_pre_topc @ A ) & ( m1_pre_topc @ B @ A ) ) =>
% 2.82/3.09       ( ( v1_pre_topc @ ( k8_tmap_1 @ A @ B ) ) & 
% 2.82/3.09         ( v2_pre_topc @ ( k8_tmap_1 @ A @ B ) ) & 
% 2.82/3.09         ( l1_pre_topc @ ( k8_tmap_1 @ A @ B ) ) ) ))).
% 2.82/3.09  thf('19', plain,
% 2.82/3.09      (![X22 : $i, X23 : $i]:
% 2.82/3.09         (~ (l1_pre_topc @ X22)
% 2.82/3.09          | ~ (v2_pre_topc @ X22)
% 2.82/3.09          | (v2_struct_0 @ X22)
% 2.82/3.09          | ~ (m1_pre_topc @ X23 @ X22)
% 2.82/3.09          | (l1_pre_topc @ (k8_tmap_1 @ X22 @ X23)))),
% 2.82/3.09      inference('cnf', [status(esa)], [dt_k8_tmap_1])).
% 2.82/3.09  thf('20', plain,
% 2.82/3.09      (((l1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B_1))
% 2.82/3.09        | (v2_struct_0 @ sk_A)
% 2.82/3.09        | ~ (v2_pre_topc @ sk_A)
% 2.82/3.09        | ~ (l1_pre_topc @ sk_A))),
% 2.82/3.09      inference('sup-', [status(thm)], ['18', '19'])).
% 2.82/3.09  thf('21', plain, ((v2_pre_topc @ sk_A)),
% 2.82/3.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.82/3.09  thf('22', plain, ((l1_pre_topc @ sk_A)),
% 2.82/3.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.82/3.09  thf('23', plain,
% 2.82/3.09      (((l1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B_1)) | (v2_struct_0 @ sk_A))),
% 2.82/3.09      inference('demod', [status(thm)], ['20', '21', '22'])).
% 2.82/3.09  thf('24', plain, (~ (v2_struct_0 @ sk_A)),
% 2.82/3.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.82/3.09  thf('25', plain, ((l1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B_1))),
% 2.82/3.09      inference('clc', [status(thm)], ['23', '24'])).
% 2.82/3.09  thf('26', plain, ((m1_pre_topc @ sk_B_1 @ sk_A)),
% 2.82/3.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.82/3.09  thf('27', plain,
% 2.82/3.09      (![X22 : $i, X23 : $i]:
% 2.82/3.09         (~ (l1_pre_topc @ X22)
% 2.82/3.09          | ~ (v2_pre_topc @ X22)
% 2.82/3.09          | (v2_struct_0 @ X22)
% 2.82/3.09          | ~ (m1_pre_topc @ X23 @ X22)
% 2.82/3.09          | (v2_pre_topc @ (k8_tmap_1 @ X22 @ X23)))),
% 2.82/3.09      inference('cnf', [status(esa)], [dt_k8_tmap_1])).
% 2.82/3.09  thf('28', plain,
% 2.82/3.09      (((v2_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B_1))
% 2.82/3.09        | (v2_struct_0 @ sk_A)
% 2.82/3.09        | ~ (v2_pre_topc @ sk_A)
% 2.82/3.09        | ~ (l1_pre_topc @ sk_A))),
% 2.82/3.09      inference('sup-', [status(thm)], ['26', '27'])).
% 2.82/3.09  thf('29', plain, ((v2_pre_topc @ sk_A)),
% 2.82/3.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.82/3.09  thf('30', plain, ((l1_pre_topc @ sk_A)),
% 2.82/3.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.82/3.09  thf('31', plain,
% 2.82/3.09      (((v2_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B_1)) | (v2_struct_0 @ sk_A))),
% 2.82/3.09      inference('demod', [status(thm)], ['28', '29', '30'])).
% 2.82/3.09  thf('32', plain, (~ (v2_struct_0 @ sk_A)),
% 2.82/3.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.82/3.09  thf('33', plain, ((v2_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B_1))),
% 2.82/3.09      inference('clc', [status(thm)], ['31', '32'])).
% 2.82/3.09  thf('34', plain, ((m1_pre_topc @ sk_B_1 @ sk_A)),
% 2.82/3.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.82/3.09  thf('35', plain,
% 2.82/3.09      (![X22 : $i, X23 : $i]:
% 2.82/3.09         (~ (l1_pre_topc @ X22)
% 2.82/3.09          | ~ (v2_pre_topc @ X22)
% 2.82/3.09          | (v2_struct_0 @ X22)
% 2.82/3.09          | ~ (m1_pre_topc @ X23 @ X22)
% 2.82/3.09          | (v1_pre_topc @ (k8_tmap_1 @ X22 @ X23)))),
% 2.82/3.09      inference('cnf', [status(esa)], [dt_k8_tmap_1])).
% 2.82/3.09  thf('36', plain,
% 2.82/3.09      (((v1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B_1))
% 2.82/3.09        | (v2_struct_0 @ sk_A)
% 2.82/3.09        | ~ (v2_pre_topc @ sk_A)
% 2.82/3.09        | ~ (l1_pre_topc @ sk_A))),
% 2.82/3.09      inference('sup-', [status(thm)], ['34', '35'])).
% 2.82/3.09  thf('37', plain, ((v2_pre_topc @ sk_A)),
% 2.82/3.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.82/3.09  thf('38', plain, ((l1_pre_topc @ sk_A)),
% 2.82/3.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.82/3.09  thf('39', plain,
% 2.82/3.09      (((v1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B_1)) | (v2_struct_0 @ sk_A))),
% 2.82/3.09      inference('demod', [status(thm)], ['36', '37', '38'])).
% 2.82/3.09  thf('40', plain, (~ (v2_struct_0 @ sk_A)),
% 2.82/3.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.82/3.09  thf('41', plain, ((v1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B_1))),
% 2.82/3.09      inference('clc', [status(thm)], ['39', '40'])).
% 2.82/3.09  thf('42', plain, ((l1_pre_topc @ sk_A)),
% 2.82/3.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.82/3.09  thf('43', plain, ((v2_pre_topc @ sk_A)),
% 2.82/3.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.82/3.09  thf('44', plain,
% 2.82/3.09      ((((k8_tmap_1 @ sk_A @ sk_B_1)
% 2.82/3.09          = (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B_1)))
% 2.82/3.09        | (v2_struct_0 @ sk_A))),
% 2.82/3.09      inference('demod', [status(thm)],
% 2.82/3.09                ['16', '17', '25', '33', '41', '42', '43'])).
% 2.82/3.09  thf('45', plain, (~ (v2_struct_0 @ sk_A)),
% 2.82/3.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.82/3.09  thf('46', plain,
% 2.82/3.09      (((k8_tmap_1 @ sk_A @ sk_B_1)
% 2.82/3.09         = (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B_1)))),
% 2.82/3.09      inference('clc', [status(thm)], ['44', '45'])).
% 2.82/3.09  thf('47', plain,
% 2.82/3.09      (((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B_1)) = (u1_struct_0 @ sk_A))),
% 2.82/3.09      inference('demod', [status(thm)], ['12', '46'])).
% 2.82/3.09  thf('48', plain,
% 2.82/3.09      (((v1_funct_2 @ (k9_tmap_1 @ sk_A @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 2.82/3.09         (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B_1)))
% 2.82/3.09        | (v1_tsep_1 @ sk_B_1 @ sk_A))),
% 2.82/3.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.82/3.09  thf('49', plain,
% 2.82/3.09      (((v1_funct_2 @ (k9_tmap_1 @ sk_A @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 2.82/3.09         (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B_1))))
% 2.82/3.09         <= (((v1_funct_2 @ (k9_tmap_1 @ sk_A @ sk_B_1) @ 
% 2.82/3.09               (u1_struct_0 @ sk_A) @ 
% 2.82/3.09               (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B_1)))))),
% 2.82/3.09      inference('split', [status(esa)], ['48'])).
% 2.82/3.09  thf('50', plain,
% 2.82/3.09      (((v1_funct_2 @ (k9_tmap_1 @ sk_A @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 2.82/3.09         (u1_struct_0 @ sk_A)))
% 2.82/3.09         <= (((v1_funct_2 @ (k9_tmap_1 @ sk_A @ sk_B_1) @ 
% 2.82/3.09               (u1_struct_0 @ sk_A) @ 
% 2.82/3.09               (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B_1)))))),
% 2.82/3.09      inference('sup+', [status(thm)], ['47', '49'])).
% 2.82/3.09  thf('51', plain,
% 2.82/3.09      (((m1_subset_1 @ (k9_tmap_1 @ sk_A @ sk_B_1) @ 
% 2.82/3.09         (k1_zfmisc_1 @ 
% 2.82/3.09          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 2.82/3.09           (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B_1)))))
% 2.82/3.09        | (v1_tsep_1 @ sk_B_1 @ sk_A))),
% 2.82/3.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.82/3.09  thf('52', plain,
% 2.82/3.09      (((m1_subset_1 @ (k9_tmap_1 @ sk_A @ sk_B_1) @ 
% 2.82/3.09         (k1_zfmisc_1 @ 
% 2.82/3.09          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 2.82/3.09           (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B_1))))))
% 2.82/3.09         <= (((m1_subset_1 @ (k9_tmap_1 @ sk_A @ sk_B_1) @ 
% 2.82/3.09               (k1_zfmisc_1 @ 
% 2.82/3.09                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 2.82/3.09                 (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B_1)))))))),
% 2.82/3.09      inference('split', [status(esa)], ['51'])).
% 2.82/3.09  thf(d12_tmap_1, axiom,
% 2.82/3.09    (![A:$i]:
% 2.82/3.09     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 2.82/3.09       ( ![B:$i]:
% 2.82/3.09         ( ( m1_pre_topc @ B @ A ) =>
% 2.82/3.09           ( ![C:$i]:
% 2.82/3.09             ( ( ( v1_funct_1 @ C ) & 
% 2.82/3.09                 ( v1_funct_2 @
% 2.82/3.09                   C @ ( u1_struct_0 @ A ) @ 
% 2.82/3.09                   ( u1_struct_0 @ ( k8_tmap_1 @ A @ B ) ) ) & 
% 2.82/3.09                 ( m1_subset_1 @
% 2.82/3.09                   C @ 
% 2.82/3.09                   ( k1_zfmisc_1 @
% 2.82/3.09                     ( k2_zfmisc_1 @
% 2.82/3.09                       ( u1_struct_0 @ A ) @ 
% 2.82/3.09                       ( u1_struct_0 @ ( k8_tmap_1 @ A @ B ) ) ) ) ) ) =>
% 2.82/3.09               ( ( ( C ) = ( k9_tmap_1 @ A @ B ) ) <=>
% 2.82/3.09                 ( ![D:$i]:
% 2.82/3.09                   ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.82/3.09                     ( ( ( D ) = ( u1_struct_0 @ B ) ) =>
% 2.82/3.09                       ( r1_funct_2 @
% 2.82/3.09                         ( u1_struct_0 @ A ) @ 
% 2.82/3.09                         ( u1_struct_0 @ ( k8_tmap_1 @ A @ B ) ) @ 
% 2.82/3.09                         ( u1_struct_0 @ A ) @ 
% 2.82/3.09                         ( u1_struct_0 @ ( k6_tmap_1 @ A @ D ) ) @ C @ 
% 2.82/3.09                         ( k7_tmap_1 @ A @ D ) ) ) ) ) ) ) ) ) ) ))).
% 2.82/3.09  thf('53', plain,
% 2.82/3.09      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 2.82/3.09         (~ (m1_pre_topc @ X13 @ X14)
% 2.82/3.09          | ((X15) != (k9_tmap_1 @ X14 @ X13))
% 2.82/3.09          | ((X16) != (u1_struct_0 @ X13))
% 2.82/3.09          | (r1_funct_2 @ (u1_struct_0 @ X14) @ 
% 2.82/3.09             (u1_struct_0 @ (k8_tmap_1 @ X14 @ X13)) @ (u1_struct_0 @ X14) @ 
% 2.82/3.09             (u1_struct_0 @ (k6_tmap_1 @ X14 @ X16)) @ X15 @ 
% 2.82/3.09             (k7_tmap_1 @ X14 @ X16))
% 2.82/3.09          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 2.82/3.09          | ~ (m1_subset_1 @ X15 @ 
% 2.82/3.09               (k1_zfmisc_1 @ 
% 2.82/3.09                (k2_zfmisc_1 @ (u1_struct_0 @ X14) @ 
% 2.82/3.09                 (u1_struct_0 @ (k8_tmap_1 @ X14 @ X13)))))
% 2.82/3.09          | ~ (v1_funct_2 @ X15 @ (u1_struct_0 @ X14) @ 
% 2.82/3.09               (u1_struct_0 @ (k8_tmap_1 @ X14 @ X13)))
% 2.82/3.09          | ~ (v1_funct_1 @ X15)
% 2.82/3.09          | ~ (l1_pre_topc @ X14)
% 2.82/3.09          | ~ (v2_pre_topc @ X14)
% 2.82/3.09          | (v2_struct_0 @ X14))),
% 2.82/3.09      inference('cnf', [status(esa)], [d12_tmap_1])).
% 2.82/3.09  thf('54', plain,
% 2.82/3.09      (![X13 : $i, X14 : $i]:
% 2.82/3.09         ((v2_struct_0 @ X14)
% 2.82/3.09          | ~ (v2_pre_topc @ X14)
% 2.82/3.09          | ~ (l1_pre_topc @ X14)
% 2.82/3.09          | ~ (v1_funct_1 @ (k9_tmap_1 @ X14 @ X13))
% 2.82/3.09          | ~ (v1_funct_2 @ (k9_tmap_1 @ X14 @ X13) @ (u1_struct_0 @ X14) @ 
% 2.82/3.09               (u1_struct_0 @ (k8_tmap_1 @ X14 @ X13)))
% 2.82/3.09          | ~ (m1_subset_1 @ (k9_tmap_1 @ X14 @ X13) @ 
% 2.82/3.09               (k1_zfmisc_1 @ 
% 2.82/3.09                (k2_zfmisc_1 @ (u1_struct_0 @ X14) @ 
% 2.82/3.09                 (u1_struct_0 @ (k8_tmap_1 @ X14 @ X13)))))
% 2.82/3.09          | ~ (m1_subset_1 @ (u1_struct_0 @ X13) @ 
% 2.82/3.09               (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 2.82/3.09          | (r1_funct_2 @ (u1_struct_0 @ X14) @ 
% 2.82/3.09             (u1_struct_0 @ (k8_tmap_1 @ X14 @ X13)) @ (u1_struct_0 @ X14) @ 
% 2.82/3.09             (u1_struct_0 @ (k6_tmap_1 @ X14 @ (u1_struct_0 @ X13))) @ 
% 2.82/3.09             (k9_tmap_1 @ X14 @ X13) @ (k7_tmap_1 @ X14 @ (u1_struct_0 @ X13)))
% 2.82/3.09          | ~ (m1_pre_topc @ X13 @ X14))),
% 2.82/3.09      inference('simplify', [status(thm)], ['53'])).
% 2.82/3.09  thf('55', plain,
% 2.82/3.09      (((~ (m1_pre_topc @ sk_B_1 @ sk_A)
% 2.82/3.09         | (r1_funct_2 @ (u1_struct_0 @ sk_A) @ 
% 2.82/3.09            (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B_1)) @ 
% 2.82/3.09            (u1_struct_0 @ sk_A) @ 
% 2.82/3.09            (u1_struct_0 @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B_1))) @ 
% 2.82/3.09            (k9_tmap_1 @ sk_A @ sk_B_1) @ 
% 2.82/3.09            (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B_1)))
% 2.82/3.09         | ~ (m1_subset_1 @ (u1_struct_0 @ sk_B_1) @ 
% 2.82/3.09              (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 2.82/3.09         | ~ (v1_funct_2 @ (k9_tmap_1 @ sk_A @ sk_B_1) @ 
% 2.82/3.09              (u1_struct_0 @ sk_A) @ 
% 2.82/3.09              (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B_1)))
% 2.82/3.09         | ~ (v1_funct_1 @ (k9_tmap_1 @ sk_A @ sk_B_1))
% 2.82/3.09         | ~ (l1_pre_topc @ sk_A)
% 2.82/3.09         | ~ (v2_pre_topc @ sk_A)
% 2.82/3.09         | (v2_struct_0 @ sk_A)))
% 2.82/3.09         <= (((m1_subset_1 @ (k9_tmap_1 @ sk_A @ sk_B_1) @ 
% 2.82/3.09               (k1_zfmisc_1 @ 
% 2.82/3.09                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 2.82/3.09                 (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B_1)))))))),
% 2.82/3.09      inference('sup-', [status(thm)], ['52', '54'])).
% 2.82/3.09  thf('56', plain, ((m1_pre_topc @ sk_B_1 @ sk_A)),
% 2.82/3.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.82/3.09  thf('57', plain,
% 2.82/3.09      (((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B_1)) = (u1_struct_0 @ sk_A))),
% 2.82/3.09      inference('demod', [status(thm)], ['12', '46'])).
% 2.82/3.09  thf('58', plain,
% 2.82/3.09      (((k8_tmap_1 @ sk_A @ sk_B_1)
% 2.82/3.09         = (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B_1)))),
% 2.82/3.09      inference('clc', [status(thm)], ['44', '45'])).
% 2.82/3.09  thf('59', plain,
% 2.82/3.09      (((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B_1)) = (u1_struct_0 @ sk_A))),
% 2.82/3.09      inference('demod', [status(thm)], ['12', '46'])).
% 2.82/3.09  thf('60', plain,
% 2.82/3.09      ((m1_subset_1 @ (u1_struct_0 @ sk_B_1) @ 
% 2.82/3.09        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.82/3.09      inference('demod', [status(thm)], ['3', '4'])).
% 2.82/3.09  thf('61', plain,
% 2.82/3.09      (((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B_1)) = (u1_struct_0 @ sk_A))),
% 2.82/3.09      inference('demod', [status(thm)], ['12', '46'])).
% 2.82/3.09  thf('62', plain, ((m1_pre_topc @ sk_B_1 @ sk_A)),
% 2.82/3.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.82/3.09  thf(dt_k9_tmap_1, axiom,
% 2.82/3.09    (![A:$i,B:$i]:
% 2.82/3.09     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 2.82/3.09         ( l1_pre_topc @ A ) & ( m1_pre_topc @ B @ A ) ) =>
% 2.82/3.09       ( ( v1_funct_1 @ ( k9_tmap_1 @ A @ B ) ) & 
% 2.82/3.09         ( v1_funct_2 @
% 2.82/3.09           ( k9_tmap_1 @ A @ B ) @ ( u1_struct_0 @ A ) @ 
% 2.82/3.09           ( u1_struct_0 @ ( k8_tmap_1 @ A @ B ) ) ) & 
% 2.82/3.09         ( m1_subset_1 @
% 2.82/3.09           ( k9_tmap_1 @ A @ B ) @ 
% 2.82/3.09           ( k1_zfmisc_1 @
% 2.82/3.09             ( k2_zfmisc_1 @
% 2.82/3.09               ( u1_struct_0 @ A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ A @ B ) ) ) ) ) ) ))).
% 2.82/3.09  thf('63', plain,
% 2.82/3.09      (![X24 : $i, X25 : $i]:
% 2.82/3.09         (~ (l1_pre_topc @ X24)
% 2.82/3.09          | ~ (v2_pre_topc @ X24)
% 2.82/3.09          | (v2_struct_0 @ X24)
% 2.82/3.09          | ~ (m1_pre_topc @ X25 @ X24)
% 2.82/3.09          | (v1_funct_1 @ (k9_tmap_1 @ X24 @ X25)))),
% 2.82/3.09      inference('cnf', [status(esa)], [dt_k9_tmap_1])).
% 2.82/3.09  thf('64', plain,
% 2.82/3.09      (((v1_funct_1 @ (k9_tmap_1 @ sk_A @ sk_B_1))
% 2.82/3.09        | (v2_struct_0 @ sk_A)
% 2.82/3.09        | ~ (v2_pre_topc @ sk_A)
% 2.82/3.09        | ~ (l1_pre_topc @ sk_A))),
% 2.82/3.09      inference('sup-', [status(thm)], ['62', '63'])).
% 2.82/3.09  thf('65', plain, ((v2_pre_topc @ sk_A)),
% 2.82/3.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.82/3.09  thf('66', plain, ((l1_pre_topc @ sk_A)),
% 2.82/3.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.82/3.09  thf('67', plain,
% 2.82/3.09      (((v1_funct_1 @ (k9_tmap_1 @ sk_A @ sk_B_1)) | (v2_struct_0 @ sk_A))),
% 2.82/3.09      inference('demod', [status(thm)], ['64', '65', '66'])).
% 2.82/3.09  thf('68', plain, (~ (v2_struct_0 @ sk_A)),
% 2.82/3.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.82/3.09  thf('69', plain, ((v1_funct_1 @ (k9_tmap_1 @ sk_A @ sk_B_1))),
% 2.82/3.09      inference('clc', [status(thm)], ['67', '68'])).
% 2.82/3.09  thf('70', plain, ((l1_pre_topc @ sk_A)),
% 2.82/3.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.82/3.09  thf('71', plain, ((v2_pre_topc @ sk_A)),
% 2.82/3.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.82/3.09  thf('72', plain,
% 2.82/3.09      ((((r1_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 2.82/3.09          (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 2.82/3.09          (k9_tmap_1 @ sk_A @ sk_B_1) @ 
% 2.82/3.09          (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B_1)))
% 2.82/3.09         | ~ (v1_funct_2 @ (k9_tmap_1 @ sk_A @ sk_B_1) @ 
% 2.82/3.09              (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))
% 2.82/3.09         | (v2_struct_0 @ sk_A)))
% 2.82/3.09         <= (((m1_subset_1 @ (k9_tmap_1 @ sk_A @ sk_B_1) @ 
% 2.82/3.09               (k1_zfmisc_1 @ 
% 2.82/3.09                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 2.82/3.09                 (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B_1)))))))),
% 2.82/3.09      inference('demod', [status(thm)],
% 2.82/3.09                ['55', '56', '57', '58', '59', '60', '61', '69', '70', '71'])).
% 2.82/3.09  thf('73', plain, (~ (v2_struct_0 @ sk_A)),
% 2.82/3.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.82/3.09  thf('74', plain,
% 2.82/3.09      (((~ (v1_funct_2 @ (k9_tmap_1 @ sk_A @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 2.82/3.09            (u1_struct_0 @ sk_A))
% 2.82/3.09         | (r1_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 2.82/3.09            (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 2.82/3.09            (k9_tmap_1 @ sk_A @ sk_B_1) @ 
% 2.82/3.09            (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B_1)))))
% 2.82/3.09         <= (((m1_subset_1 @ (k9_tmap_1 @ sk_A @ sk_B_1) @ 
% 2.82/3.09               (k1_zfmisc_1 @ 
% 2.82/3.09                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 2.82/3.09                 (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B_1)))))))),
% 2.82/3.09      inference('clc', [status(thm)], ['72', '73'])).
% 2.82/3.09  thf('75', plain,
% 2.82/3.09      (((r1_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 2.82/3.09         (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 2.82/3.09         (k9_tmap_1 @ sk_A @ sk_B_1) @ 
% 2.82/3.09         (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B_1))))
% 2.82/3.09         <= (((v1_funct_2 @ (k9_tmap_1 @ sk_A @ sk_B_1) @ 
% 2.82/3.09               (u1_struct_0 @ sk_A) @ 
% 2.82/3.09               (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B_1)))) & 
% 2.82/3.09             ((m1_subset_1 @ (k9_tmap_1 @ sk_A @ sk_B_1) @ 
% 2.82/3.09               (k1_zfmisc_1 @ 
% 2.82/3.09                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 2.82/3.09                 (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B_1)))))))),
% 2.82/3.09      inference('sup-', [status(thm)], ['50', '74'])).
% 2.82/3.09  thf('76', plain, ((m1_pre_topc @ sk_B_1 @ sk_A)),
% 2.82/3.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.82/3.09  thf('77', plain,
% 2.82/3.09      (![X24 : $i, X25 : $i]:
% 2.82/3.09         (~ (l1_pre_topc @ X24)
% 2.82/3.09          | ~ (v2_pre_topc @ X24)
% 2.82/3.09          | (v2_struct_0 @ X24)
% 2.82/3.09          | ~ (m1_pre_topc @ X25 @ X24)
% 2.82/3.09          | (v1_funct_2 @ (k9_tmap_1 @ X24 @ X25) @ (u1_struct_0 @ X24) @ 
% 2.82/3.09             (u1_struct_0 @ (k8_tmap_1 @ X24 @ X25))))),
% 2.82/3.09      inference('cnf', [status(esa)], [dt_k9_tmap_1])).
% 2.82/3.09  thf('78', plain,
% 2.82/3.09      (((v1_funct_2 @ (k9_tmap_1 @ sk_A @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 2.82/3.09         (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B_1)))
% 2.82/3.09        | (v2_struct_0 @ sk_A)
% 2.82/3.09        | ~ (v2_pre_topc @ sk_A)
% 2.82/3.09        | ~ (l1_pre_topc @ sk_A))),
% 2.82/3.09      inference('sup-', [status(thm)], ['76', '77'])).
% 2.82/3.09  thf('79', plain,
% 2.82/3.09      (((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B_1)) = (u1_struct_0 @ sk_A))),
% 2.82/3.09      inference('demod', [status(thm)], ['12', '46'])).
% 2.82/3.09  thf('80', plain, ((v2_pre_topc @ sk_A)),
% 2.82/3.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.82/3.09  thf('81', plain, ((l1_pre_topc @ sk_A)),
% 2.82/3.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.82/3.09  thf('82', plain,
% 2.82/3.09      (((v1_funct_2 @ (k9_tmap_1 @ sk_A @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 2.82/3.09         (u1_struct_0 @ sk_A))
% 2.82/3.09        | (v2_struct_0 @ sk_A))),
% 2.82/3.09      inference('demod', [status(thm)], ['78', '79', '80', '81'])).
% 2.82/3.09  thf('83', plain, (~ (v2_struct_0 @ sk_A)),
% 2.82/3.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.82/3.09  thf('84', plain,
% 2.82/3.09      ((v1_funct_2 @ (k9_tmap_1 @ sk_A @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 2.82/3.09        (u1_struct_0 @ sk_A))),
% 2.82/3.09      inference('clc', [status(thm)], ['82', '83'])).
% 2.82/3.09  thf('85', plain,
% 2.82/3.09      (((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B_1)) = (u1_struct_0 @ sk_A))),
% 2.82/3.09      inference('demod', [status(thm)], ['12', '46'])).
% 2.82/3.09  thf('86', plain,
% 2.82/3.09      ((~ (m1_subset_1 @ (k9_tmap_1 @ sk_A @ sk_B_1) @ 
% 2.82/3.09           (k1_zfmisc_1 @ 
% 2.82/3.09            (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 2.82/3.09             (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B_1)))))
% 2.82/3.09        | ~ (v5_pre_topc @ (k9_tmap_1 @ sk_A @ sk_B_1) @ sk_A @ 
% 2.82/3.09             (k8_tmap_1 @ sk_A @ sk_B_1))
% 2.82/3.09        | ~ (v1_funct_2 @ (k9_tmap_1 @ sk_A @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 2.82/3.09             (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B_1)))
% 2.82/3.09        | ~ (v1_funct_1 @ (k9_tmap_1 @ sk_A @ sk_B_1))
% 2.82/3.09        | ~ (m1_pre_topc @ sk_B_1 @ sk_A)
% 2.82/3.09        | ~ (v1_tsep_1 @ sk_B_1 @ sk_A))),
% 2.82/3.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.82/3.09  thf('87', plain,
% 2.82/3.09      ((~ (v1_funct_2 @ (k9_tmap_1 @ sk_A @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 2.82/3.09           (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B_1))))
% 2.82/3.09         <= (~
% 2.82/3.09             ((v1_funct_2 @ (k9_tmap_1 @ sk_A @ sk_B_1) @ 
% 2.82/3.09               (u1_struct_0 @ sk_A) @ 
% 2.82/3.09               (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B_1)))))),
% 2.82/3.09      inference('split', [status(esa)], ['86'])).
% 2.82/3.09  thf('88', plain,
% 2.82/3.09      ((~ (v1_funct_2 @ (k9_tmap_1 @ sk_A @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 2.82/3.09           (u1_struct_0 @ sk_A)))
% 2.82/3.09         <= (~
% 2.82/3.09             ((v1_funct_2 @ (k9_tmap_1 @ sk_A @ sk_B_1) @ 
% 2.82/3.09               (u1_struct_0 @ sk_A) @ 
% 2.82/3.09               (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B_1)))))),
% 2.82/3.09      inference('sup-', [status(thm)], ['85', '87'])).
% 2.82/3.09  thf('89', plain,
% 2.82/3.09      (((v1_funct_2 @ (k9_tmap_1 @ sk_A @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 2.82/3.09         (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B_1))))),
% 2.82/3.09      inference('sup-', [status(thm)], ['84', '88'])).
% 2.82/3.09  thf('90', plain,
% 2.82/3.09      (((v1_funct_2 @ (k9_tmap_1 @ sk_A @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 2.82/3.09         (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B_1))))),
% 2.82/3.09      inference('sat_resolution*', [status(thm)], ['89'])).
% 2.82/3.09  thf('91', plain,
% 2.82/3.09      (((r1_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 2.82/3.09         (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 2.82/3.09         (k9_tmap_1 @ sk_A @ sk_B_1) @ 
% 2.82/3.09         (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B_1))))
% 2.82/3.09         <= (((m1_subset_1 @ (k9_tmap_1 @ sk_A @ sk_B_1) @ 
% 2.82/3.09               (k1_zfmisc_1 @ 
% 2.82/3.09                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 2.82/3.09                 (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B_1)))))))),
% 2.82/3.09      inference('simpl_trail', [status(thm)], ['75', '90'])).
% 2.82/3.09  thf('92', plain, ((m1_pre_topc @ sk_B_1 @ sk_A)),
% 2.82/3.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.82/3.09  thf('93', plain,
% 2.82/3.09      (![X24 : $i, X25 : $i]:
% 2.82/3.09         (~ (l1_pre_topc @ X24)
% 2.82/3.09          | ~ (v2_pre_topc @ X24)
% 2.82/3.09          | (v2_struct_0 @ X24)
% 2.82/3.09          | ~ (m1_pre_topc @ X25 @ X24)
% 2.82/3.09          | (m1_subset_1 @ (k9_tmap_1 @ X24 @ X25) @ 
% 2.82/3.09             (k1_zfmisc_1 @ 
% 2.82/3.09              (k2_zfmisc_1 @ (u1_struct_0 @ X24) @ 
% 2.82/3.09               (u1_struct_0 @ (k8_tmap_1 @ X24 @ X25))))))),
% 2.82/3.09      inference('cnf', [status(esa)], [dt_k9_tmap_1])).
% 2.82/3.09  thf('94', plain,
% 2.82/3.09      (((m1_subset_1 @ (k9_tmap_1 @ sk_A @ sk_B_1) @ 
% 2.82/3.09         (k1_zfmisc_1 @ 
% 2.82/3.09          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 2.82/3.09           (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B_1)))))
% 2.82/3.09        | (v2_struct_0 @ sk_A)
% 2.82/3.09        | ~ (v2_pre_topc @ sk_A)
% 2.82/3.09        | ~ (l1_pre_topc @ sk_A))),
% 2.82/3.09      inference('sup-', [status(thm)], ['92', '93'])).
% 2.82/3.09  thf('95', plain,
% 2.82/3.09      (((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B_1)) = (u1_struct_0 @ sk_A))),
% 2.82/3.09      inference('demod', [status(thm)], ['12', '46'])).
% 2.82/3.09  thf('96', plain, ((v2_pre_topc @ sk_A)),
% 2.82/3.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.82/3.09  thf('97', plain, ((l1_pre_topc @ sk_A)),
% 2.82/3.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.82/3.09  thf('98', plain,
% 2.82/3.09      (((m1_subset_1 @ (k9_tmap_1 @ sk_A @ sk_B_1) @ 
% 2.82/3.09         (k1_zfmisc_1 @ 
% 2.82/3.09          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))))
% 2.82/3.09        | (v2_struct_0 @ sk_A))),
% 2.82/3.09      inference('demod', [status(thm)], ['94', '95', '96', '97'])).
% 2.82/3.09  thf('99', plain, (~ (v2_struct_0 @ sk_A)),
% 2.82/3.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.82/3.09  thf('100', plain,
% 2.82/3.09      ((m1_subset_1 @ (k9_tmap_1 @ sk_A @ sk_B_1) @ 
% 2.82/3.09        (k1_zfmisc_1 @ 
% 2.82/3.09         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))))),
% 2.82/3.09      inference('clc', [status(thm)], ['98', '99'])).
% 2.82/3.09  thf('101', plain,
% 2.82/3.09      (((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B_1)) = (u1_struct_0 @ sk_A))),
% 2.82/3.09      inference('demod', [status(thm)], ['12', '46'])).
% 2.82/3.09  thf('102', plain,
% 2.82/3.09      ((~ (m1_subset_1 @ (k9_tmap_1 @ sk_A @ sk_B_1) @ 
% 2.82/3.09           (k1_zfmisc_1 @ 
% 2.82/3.09            (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 2.82/3.09             (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B_1))))))
% 2.82/3.09         <= (~
% 2.82/3.09             ((m1_subset_1 @ (k9_tmap_1 @ sk_A @ sk_B_1) @ 
% 2.93/3.09               (k1_zfmisc_1 @ 
% 2.93/3.09                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 2.93/3.09                 (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B_1)))))))),
% 2.93/3.09      inference('split', [status(esa)], ['86'])).
% 2.93/3.09  thf('103', plain,
% 2.93/3.09      ((~ (m1_subset_1 @ (k9_tmap_1 @ sk_A @ sk_B_1) @ 
% 2.93/3.09           (k1_zfmisc_1 @ 
% 2.93/3.09            (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A)))))
% 2.93/3.09         <= (~
% 2.93/3.09             ((m1_subset_1 @ (k9_tmap_1 @ sk_A @ sk_B_1) @ 
% 2.93/3.09               (k1_zfmisc_1 @ 
% 2.93/3.09                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 2.93/3.09                 (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B_1)))))))),
% 2.93/3.09      inference('sup-', [status(thm)], ['101', '102'])).
% 2.93/3.09  thf('104', plain,
% 2.93/3.09      (((m1_subset_1 @ (k9_tmap_1 @ sk_A @ sk_B_1) @ 
% 2.93/3.09         (k1_zfmisc_1 @ 
% 2.93/3.09          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 2.93/3.09           (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B_1))))))),
% 2.93/3.09      inference('sup-', [status(thm)], ['100', '103'])).
% 2.93/3.09  thf('105', plain,
% 2.93/3.09      (((m1_subset_1 @ (k9_tmap_1 @ sk_A @ sk_B_1) @ 
% 2.93/3.09         (k1_zfmisc_1 @ 
% 2.93/3.09          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 2.93/3.09           (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B_1))))))),
% 2.93/3.09      inference('sat_resolution*', [status(thm)], ['104'])).
% 2.93/3.09  thf('106', plain,
% 2.93/3.09      ((r1_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 2.93/3.09        (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 2.93/3.09        (k9_tmap_1 @ sk_A @ sk_B_1) @ 
% 2.93/3.09        (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B_1)))),
% 2.93/3.09      inference('simpl_trail', [status(thm)], ['91', '105'])).
% 2.93/3.09  thf('107', plain,
% 2.93/3.09      ((m1_subset_1 @ (k9_tmap_1 @ sk_A @ sk_B_1) @ 
% 2.93/3.09        (k1_zfmisc_1 @ 
% 2.93/3.09         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))))),
% 2.93/3.09      inference('clc', [status(thm)], ['98', '99'])).
% 2.93/3.09  thf(redefinition_r1_funct_2, axiom,
% 2.93/3.09    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 2.93/3.09     ( ( ( ~( v1_xboole_0 @ B ) ) & ( ~( v1_xboole_0 @ D ) ) & 
% 2.93/3.09         ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ A @ B ) & 
% 2.93/3.09         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 2.93/3.09         ( v1_funct_1 @ F ) & ( v1_funct_2 @ F @ C @ D ) & 
% 2.93/3.09         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 2.93/3.09       ( ( r1_funct_2 @ A @ B @ C @ D @ E @ F ) <=> ( ( E ) = ( F ) ) ) ))).
% 2.93/3.09  thf('108', plain,
% 2.93/3.09      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 2.93/3.09         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X4 @ X5)))
% 2.93/3.09          | ~ (v1_funct_2 @ X3 @ X4 @ X5)
% 2.93/3.09          | ~ (v1_funct_1 @ X3)
% 2.93/3.09          | (v1_xboole_0 @ X6)
% 2.93/3.09          | (v1_xboole_0 @ X5)
% 2.93/3.09          | ~ (v1_funct_1 @ X7)
% 2.93/3.09          | ~ (v1_funct_2 @ X7 @ X8 @ X6)
% 2.93/3.09          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X6)))
% 2.93/3.09          | ((X3) = (X7))
% 2.93/3.09          | ~ (r1_funct_2 @ X4 @ X5 @ X8 @ X6 @ X3 @ X7))),
% 2.93/3.09      inference('cnf', [status(esa)], [redefinition_r1_funct_2])).
% 2.93/3.09  thf('109', plain,
% 2.93/3.09      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.93/3.09         (~ (r1_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ X2 @ 
% 2.93/3.09             X1 @ (k9_tmap_1 @ sk_A @ sk_B_1) @ X0)
% 2.93/3.09          | ((k9_tmap_1 @ sk_A @ sk_B_1) = (X0))
% 2.93/3.09          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 2.93/3.09          | ~ (v1_funct_2 @ X0 @ X2 @ X1)
% 2.93/3.09          | ~ (v1_funct_1 @ X0)
% 2.93/3.09          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 2.93/3.09          | (v1_xboole_0 @ X1)
% 2.93/3.09          | ~ (v1_funct_1 @ (k9_tmap_1 @ sk_A @ sk_B_1))
% 2.93/3.09          | ~ (v1_funct_2 @ (k9_tmap_1 @ sk_A @ sk_B_1) @ 
% 2.93/3.09               (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 2.93/3.09      inference('sup-', [status(thm)], ['107', '108'])).
% 2.93/3.09  thf('110', plain, ((v1_funct_1 @ (k9_tmap_1 @ sk_A @ sk_B_1))),
% 2.93/3.09      inference('clc', [status(thm)], ['67', '68'])).
% 2.93/3.09  thf('111', plain,
% 2.93/3.09      ((v1_funct_2 @ (k9_tmap_1 @ sk_A @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 2.93/3.09        (u1_struct_0 @ sk_A))),
% 2.93/3.09      inference('clc', [status(thm)], ['82', '83'])).
% 2.93/3.09  thf('112', plain,
% 2.93/3.09      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.93/3.09         (~ (r1_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ X2 @ 
% 2.93/3.09             X1 @ (k9_tmap_1 @ sk_A @ sk_B_1) @ X0)
% 2.93/3.09          | ((k9_tmap_1 @ sk_A @ sk_B_1) = (X0))
% 2.93/3.09          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 2.93/3.09          | ~ (v1_funct_2 @ X0 @ X2 @ X1)
% 2.93/3.09          | ~ (v1_funct_1 @ X0)
% 2.93/3.09          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 2.93/3.09          | (v1_xboole_0 @ X1))),
% 2.93/3.09      inference('demod', [status(thm)], ['109', '110', '111'])).
% 2.93/3.09  thf('113', plain,
% 2.93/3.09      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 2.93/3.09        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 2.93/3.09        | ~ (v1_funct_1 @ (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B_1)))
% 2.93/3.09        | ~ (v1_funct_2 @ (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B_1)) @ 
% 2.93/3.09             (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))
% 2.93/3.09        | ~ (m1_subset_1 @ (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B_1)) @ 
% 2.93/3.09             (k1_zfmisc_1 @ 
% 2.93/3.09              (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))))
% 2.93/3.09        | ((k9_tmap_1 @ sk_A @ sk_B_1)
% 2.93/3.09            = (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B_1))))),
% 2.93/3.09      inference('sup-', [status(thm)], ['106', '112'])).
% 2.93/3.09  thf('114', plain,
% 2.93/3.09      ((m1_subset_1 @ (u1_struct_0 @ sk_B_1) @ 
% 2.93/3.09        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.93/3.09      inference('demod', [status(thm)], ['3', '4'])).
% 2.93/3.09  thf(dt_k7_tmap_1, axiom,
% 2.93/3.09    (![A:$i,B:$i]:
% 2.93/3.09     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 2.93/3.09         ( l1_pre_topc @ A ) & 
% 2.93/3.09         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 2.93/3.09       ( ( v1_funct_1 @ ( k7_tmap_1 @ A @ B ) ) & 
% 2.93/3.09         ( v1_funct_2 @
% 2.93/3.09           ( k7_tmap_1 @ A @ B ) @ ( u1_struct_0 @ A ) @ 
% 2.93/3.09           ( u1_struct_0 @ ( k6_tmap_1 @ A @ B ) ) ) & 
% 2.93/3.09         ( m1_subset_1 @
% 2.93/3.09           ( k7_tmap_1 @ A @ B ) @ 
% 2.93/3.09           ( k1_zfmisc_1 @
% 2.93/3.09             ( k2_zfmisc_1 @
% 2.93/3.09               ( u1_struct_0 @ A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ A @ B ) ) ) ) ) ) ))).
% 2.93/3.09  thf('115', plain,
% 2.93/3.09      (![X20 : $i, X21 : $i]:
% 2.93/3.09         (~ (l1_pre_topc @ X20)
% 2.93/3.09          | ~ (v2_pre_topc @ X20)
% 2.93/3.09          | (v2_struct_0 @ X20)
% 2.93/3.09          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 2.93/3.09          | (v1_funct_1 @ (k7_tmap_1 @ X20 @ X21)))),
% 2.93/3.09      inference('cnf', [status(esa)], [dt_k7_tmap_1])).
% 2.93/3.09  thf('116', plain,
% 2.93/3.09      (((v1_funct_1 @ (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B_1)))
% 2.93/3.09        | (v2_struct_0 @ sk_A)
% 2.93/3.09        | ~ (v2_pre_topc @ sk_A)
% 2.93/3.09        | ~ (l1_pre_topc @ sk_A))),
% 2.93/3.09      inference('sup-', [status(thm)], ['114', '115'])).
% 2.93/3.09  thf('117', plain, ((v2_pre_topc @ sk_A)),
% 2.93/3.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.93/3.09  thf('118', plain, ((l1_pre_topc @ sk_A)),
% 2.93/3.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.93/3.09  thf('119', plain,
% 2.93/3.09      (((v1_funct_1 @ (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B_1)))
% 2.93/3.09        | (v2_struct_0 @ sk_A))),
% 2.93/3.09      inference('demod', [status(thm)], ['116', '117', '118'])).
% 2.93/3.09  thf('120', plain, (~ (v2_struct_0 @ sk_A)),
% 2.93/3.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.93/3.09  thf('121', plain,
% 2.93/3.09      ((v1_funct_1 @ (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B_1)))),
% 2.93/3.09      inference('clc', [status(thm)], ['119', '120'])).
% 2.93/3.09  thf('122', plain,
% 2.93/3.09      ((m1_subset_1 @ (u1_struct_0 @ sk_B_1) @ 
% 2.93/3.09        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.93/3.09      inference('demod', [status(thm)], ['3', '4'])).
% 2.93/3.09  thf('123', plain,
% 2.93/3.09      (![X20 : $i, X21 : $i]:
% 2.93/3.09         (~ (l1_pre_topc @ X20)
% 2.93/3.09          | ~ (v2_pre_topc @ X20)
% 2.93/3.09          | (v2_struct_0 @ X20)
% 2.93/3.09          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 2.93/3.09          | (v1_funct_2 @ (k7_tmap_1 @ X20 @ X21) @ (u1_struct_0 @ X20) @ 
% 2.93/3.09             (u1_struct_0 @ (k6_tmap_1 @ X20 @ X21))))),
% 2.93/3.09      inference('cnf', [status(esa)], [dt_k7_tmap_1])).
% 2.93/3.09  thf('124', plain,
% 2.93/3.09      (((v1_funct_2 @ (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B_1)) @ 
% 2.93/3.09         (u1_struct_0 @ sk_A) @ 
% 2.93/3.09         (u1_struct_0 @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B_1))))
% 2.93/3.09        | (v2_struct_0 @ sk_A)
% 2.93/3.09        | ~ (v2_pre_topc @ sk_A)
% 2.93/3.09        | ~ (l1_pre_topc @ sk_A))),
% 2.93/3.09      inference('sup-', [status(thm)], ['122', '123'])).
% 2.93/3.09  thf('125', plain,
% 2.93/3.09      (((k8_tmap_1 @ sk_A @ sk_B_1)
% 2.93/3.09         = (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B_1)))),
% 2.93/3.09      inference('clc', [status(thm)], ['44', '45'])).
% 2.93/3.09  thf('126', plain,
% 2.93/3.09      (((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B_1)) = (u1_struct_0 @ sk_A))),
% 2.93/3.09      inference('demod', [status(thm)], ['12', '46'])).
% 2.93/3.09  thf('127', plain, ((v2_pre_topc @ sk_A)),
% 2.93/3.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.93/3.09  thf('128', plain, ((l1_pre_topc @ sk_A)),
% 2.93/3.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.93/3.09  thf('129', plain,
% 2.93/3.09      (((v1_funct_2 @ (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B_1)) @ 
% 2.93/3.09         (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))
% 2.93/3.09        | (v2_struct_0 @ sk_A))),
% 2.93/3.09      inference('demod', [status(thm)], ['124', '125', '126', '127', '128'])).
% 2.93/3.09  thf('130', plain, (~ (v2_struct_0 @ sk_A)),
% 2.93/3.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.93/3.09  thf('131', plain,
% 2.93/3.09      ((v1_funct_2 @ (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B_1)) @ 
% 2.93/3.09        (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))),
% 2.93/3.09      inference('clc', [status(thm)], ['129', '130'])).
% 2.93/3.09  thf('132', plain,
% 2.93/3.09      ((m1_subset_1 @ (u1_struct_0 @ sk_B_1) @ 
% 2.93/3.09        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.93/3.09      inference('demod', [status(thm)], ['3', '4'])).
% 2.93/3.09  thf('133', plain,
% 2.93/3.09      (![X20 : $i, X21 : $i]:
% 2.93/3.09         (~ (l1_pre_topc @ X20)
% 2.93/3.09          | ~ (v2_pre_topc @ X20)
% 2.93/3.09          | (v2_struct_0 @ X20)
% 2.93/3.09          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 2.93/3.09          | (m1_subset_1 @ (k7_tmap_1 @ X20 @ X21) @ 
% 2.93/3.09             (k1_zfmisc_1 @ 
% 2.93/3.09              (k2_zfmisc_1 @ (u1_struct_0 @ X20) @ 
% 2.93/3.09               (u1_struct_0 @ (k6_tmap_1 @ X20 @ X21))))))),
% 2.93/3.09      inference('cnf', [status(esa)], [dt_k7_tmap_1])).
% 2.93/3.09  thf('134', plain,
% 2.93/3.09      (((m1_subset_1 @ (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B_1)) @ 
% 2.93/3.09         (k1_zfmisc_1 @ 
% 2.93/3.09          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 2.93/3.09           (u1_struct_0 @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B_1))))))
% 2.93/3.09        | (v2_struct_0 @ sk_A)
% 2.93/3.09        | ~ (v2_pre_topc @ sk_A)
% 2.93/3.09        | ~ (l1_pre_topc @ sk_A))),
% 2.93/3.09      inference('sup-', [status(thm)], ['132', '133'])).
% 2.93/3.09  thf('135', plain,
% 2.93/3.09      (((k8_tmap_1 @ sk_A @ sk_B_1)
% 2.93/3.09         = (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B_1)))),
% 2.93/3.09      inference('clc', [status(thm)], ['44', '45'])).
% 2.93/3.09  thf('136', plain,
% 2.93/3.09      (((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B_1)) = (u1_struct_0 @ sk_A))),
% 2.93/3.09      inference('demod', [status(thm)], ['12', '46'])).
% 2.93/3.09  thf('137', plain, ((v2_pre_topc @ sk_A)),
% 2.93/3.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.93/3.09  thf('138', plain, ((l1_pre_topc @ sk_A)),
% 2.93/3.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.93/3.09  thf('139', plain,
% 2.93/3.09      (((m1_subset_1 @ (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B_1)) @ 
% 2.93/3.09         (k1_zfmisc_1 @ 
% 2.93/3.09          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))))
% 2.93/3.09        | (v2_struct_0 @ sk_A))),
% 2.93/3.09      inference('demod', [status(thm)], ['134', '135', '136', '137', '138'])).
% 2.93/3.09  thf('140', plain, (~ (v2_struct_0 @ sk_A)),
% 2.93/3.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.93/3.09  thf('141', plain,
% 2.93/3.09      ((m1_subset_1 @ (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B_1)) @ 
% 2.93/3.09        (k1_zfmisc_1 @ 
% 2.93/3.09         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))))),
% 2.93/3.09      inference('clc', [status(thm)], ['139', '140'])).
% 2.93/3.09  thf('142', plain,
% 2.93/3.09      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 2.93/3.09        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 2.93/3.09        | ((k9_tmap_1 @ sk_A @ sk_B_1)
% 2.93/3.09            = (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B_1))))),
% 2.93/3.09      inference('demod', [status(thm)], ['113', '121', '131', '141'])).
% 2.93/3.09  thf('143', plain,
% 2.93/3.09      ((((k9_tmap_1 @ sk_A @ sk_B_1)
% 2.93/3.09          = (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B_1)))
% 2.93/3.09        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 2.93/3.09      inference('simplify', [status(thm)], ['142'])).
% 2.93/3.09  thf('144', plain,
% 2.93/3.09      (((k8_tmap_1 @ sk_A @ sk_B_1)
% 2.93/3.09         = (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B_1)))),
% 2.93/3.09      inference('clc', [status(thm)], ['44', '45'])).
% 2.93/3.09  thf(t113_tmap_1, axiom,
% 2.93/3.09    (![A:$i]:
% 2.93/3.09     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 2.93/3.09       ( ![B:$i]:
% 2.93/3.09         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.93/3.09           ( ( v3_pre_topc @ B @ A ) <=>
% 2.93/3.09             ( ( v1_funct_1 @ ( k7_tmap_1 @ A @ B ) ) & 
% 2.93/3.09               ( v1_funct_2 @
% 2.93/3.09                 ( k7_tmap_1 @ A @ B ) @ ( u1_struct_0 @ A ) @ 
% 2.93/3.09                 ( u1_struct_0 @ ( k6_tmap_1 @ A @ B ) ) ) & 
% 2.93/3.09               ( v5_pre_topc @
% 2.93/3.09                 ( k7_tmap_1 @ A @ B ) @ A @ ( k6_tmap_1 @ A @ B ) ) & 
% 2.93/3.09               ( m1_subset_1 @
% 2.93/3.09                 ( k7_tmap_1 @ A @ B ) @ 
% 2.93/3.09                 ( k1_zfmisc_1 @
% 2.93/3.09                   ( k2_zfmisc_1 @
% 2.93/3.09                     ( u1_struct_0 @ A ) @ 
% 2.93/3.09                     ( u1_struct_0 @ ( k6_tmap_1 @ A @ B ) ) ) ) ) ) ) ) ) ))).
% 2.93/3.09  thf('145', plain,
% 2.93/3.09      (![X28 : $i, X29 : $i]:
% 2.93/3.09         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (u1_struct_0 @ X29)))
% 2.93/3.09          | ~ (v1_funct_1 @ (k7_tmap_1 @ X29 @ X28))
% 2.93/3.09          | ~ (v1_funct_2 @ (k7_tmap_1 @ X29 @ X28) @ (u1_struct_0 @ X29) @ 
% 2.93/3.09               (u1_struct_0 @ (k6_tmap_1 @ X29 @ X28)))
% 2.93/3.09          | ~ (v5_pre_topc @ (k7_tmap_1 @ X29 @ X28) @ X29 @ 
% 2.93/3.09               (k6_tmap_1 @ X29 @ X28))
% 2.93/3.09          | ~ (m1_subset_1 @ (k7_tmap_1 @ X29 @ X28) @ 
% 2.93/3.09               (k1_zfmisc_1 @ 
% 2.93/3.09                (k2_zfmisc_1 @ (u1_struct_0 @ X29) @ 
% 2.93/3.09                 (u1_struct_0 @ (k6_tmap_1 @ X29 @ X28)))))
% 2.93/3.09          | (v3_pre_topc @ X28 @ X29)
% 2.93/3.09          | ~ (l1_pre_topc @ X29)
% 2.93/3.09          | ~ (v2_pre_topc @ X29)
% 2.93/3.09          | (v2_struct_0 @ X29))),
% 2.93/3.09      inference('cnf', [status(esa)], [t113_tmap_1])).
% 2.93/3.09  thf('146', plain,
% 2.93/3.09      ((~ (m1_subset_1 @ (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B_1)) @ 
% 2.93/3.09           (k1_zfmisc_1 @ 
% 2.93/3.09            (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 2.93/3.09             (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B_1)))))
% 2.93/3.09        | (v2_struct_0 @ sk_A)
% 2.93/3.09        | ~ (v2_pre_topc @ sk_A)
% 2.93/3.09        | ~ (l1_pre_topc @ sk_A)
% 2.93/3.09        | (v3_pre_topc @ (u1_struct_0 @ sk_B_1) @ sk_A)
% 2.93/3.09        | ~ (v5_pre_topc @ (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B_1)) @ 
% 2.93/3.09             sk_A @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B_1)))
% 2.93/3.09        | ~ (v1_funct_2 @ (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B_1)) @ 
% 2.93/3.09             (u1_struct_0 @ sk_A) @ 
% 2.93/3.09             (u1_struct_0 @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B_1))))
% 2.93/3.09        | ~ (v1_funct_1 @ (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B_1)))
% 2.93/3.09        | ~ (m1_subset_1 @ (u1_struct_0 @ sk_B_1) @ 
% 2.93/3.09             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 2.93/3.09      inference('sup-', [status(thm)], ['144', '145'])).
% 2.93/3.09  thf('147', plain,
% 2.93/3.09      (((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B_1)) = (u1_struct_0 @ sk_A))),
% 2.93/3.09      inference('demod', [status(thm)], ['12', '46'])).
% 2.93/3.09  thf('148', plain,
% 2.93/3.09      ((m1_subset_1 @ (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B_1)) @ 
% 2.93/3.09        (k1_zfmisc_1 @ 
% 2.93/3.09         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))))),
% 2.93/3.09      inference('clc', [status(thm)], ['139', '140'])).
% 2.93/3.09  thf('149', plain, ((v2_pre_topc @ sk_A)),
% 2.93/3.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.93/3.09  thf('150', plain, ((l1_pre_topc @ sk_A)),
% 2.93/3.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.93/3.09  thf('151', plain,
% 2.93/3.09      (((k8_tmap_1 @ sk_A @ sk_B_1)
% 2.93/3.09         = (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B_1)))),
% 2.93/3.09      inference('clc', [status(thm)], ['44', '45'])).
% 2.93/3.09  thf('152', plain,
% 2.93/3.09      (((k8_tmap_1 @ sk_A @ sk_B_1)
% 2.93/3.09         = (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B_1)))),
% 2.93/3.09      inference('clc', [status(thm)], ['44', '45'])).
% 2.93/3.09  thf('153', plain,
% 2.93/3.09      (((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B_1)) = (u1_struct_0 @ sk_A))),
% 2.93/3.09      inference('demod', [status(thm)], ['12', '46'])).
% 2.93/3.09  thf('154', plain,
% 2.93/3.09      ((v1_funct_2 @ (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B_1)) @ 
% 2.93/3.09        (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))),
% 2.93/3.09      inference('clc', [status(thm)], ['129', '130'])).
% 2.93/3.09  thf('155', plain,
% 2.93/3.09      ((v1_funct_1 @ (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B_1)))),
% 2.93/3.09      inference('clc', [status(thm)], ['119', '120'])).
% 2.93/3.09  thf('156', plain,
% 2.93/3.09      ((m1_subset_1 @ (u1_struct_0 @ sk_B_1) @ 
% 2.93/3.09        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.93/3.09      inference('demod', [status(thm)], ['3', '4'])).
% 2.93/3.09  thf('157', plain,
% 2.93/3.09      (((v2_struct_0 @ sk_A)
% 2.93/3.09        | (v3_pre_topc @ (u1_struct_0 @ sk_B_1) @ sk_A)
% 2.93/3.09        | ~ (v5_pre_topc @ (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B_1)) @ 
% 2.93/3.09             sk_A @ (k8_tmap_1 @ sk_A @ sk_B_1)))),
% 2.93/3.09      inference('demod', [status(thm)],
% 2.93/3.09                ['146', '147', '148', '149', '150', '151', '152', '153', 
% 2.93/3.09                 '154', '155', '156'])).
% 2.93/3.09  thf('158', plain, (~ (v2_struct_0 @ sk_A)),
% 2.93/3.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.93/3.09  thf('159', plain,
% 2.93/3.09      ((~ (v5_pre_topc @ (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B_1)) @ sk_A @ 
% 2.93/3.09           (k8_tmap_1 @ sk_A @ sk_B_1))
% 2.93/3.09        | (v3_pre_topc @ (u1_struct_0 @ sk_B_1) @ sk_A))),
% 2.93/3.09      inference('clc', [status(thm)], ['157', '158'])).
% 2.93/3.09  thf('160', plain,
% 2.93/3.09      ((~ (v5_pre_topc @ (k9_tmap_1 @ sk_A @ sk_B_1) @ sk_A @ 
% 2.93/3.09           (k8_tmap_1 @ sk_A @ sk_B_1))
% 2.93/3.09        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 2.93/3.09        | (v3_pre_topc @ (u1_struct_0 @ sk_B_1) @ sk_A))),
% 2.93/3.09      inference('sup-', [status(thm)], ['143', '159'])).
% 2.93/3.09  thf('161', plain,
% 2.93/3.09      (((v5_pre_topc @ (k9_tmap_1 @ sk_A @ sk_B_1) @ sk_A @ 
% 2.93/3.09         (k8_tmap_1 @ sk_A @ sk_B_1))
% 2.93/3.09        | (v1_tsep_1 @ sk_B_1 @ sk_A))),
% 2.93/3.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.93/3.09  thf('162', plain,
% 2.93/3.09      (((v5_pre_topc @ (k9_tmap_1 @ sk_A @ sk_B_1) @ sk_A @ 
% 2.93/3.09         (k8_tmap_1 @ sk_A @ sk_B_1)))
% 2.93/3.09         <= (((v5_pre_topc @ (k9_tmap_1 @ sk_A @ sk_B_1) @ sk_A @ 
% 2.93/3.09               (k8_tmap_1 @ sk_A @ sk_B_1))))),
% 2.93/3.09      inference('split', [status(esa)], ['161'])).
% 2.93/3.09  thf('163', plain,
% 2.93/3.09      ((((k9_tmap_1 @ sk_A @ sk_B_1)
% 2.93/3.09          = (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B_1)))
% 2.93/3.09        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 2.93/3.09      inference('simplify', [status(thm)], ['142'])).
% 2.93/3.09  thf('164', plain,
% 2.93/3.09      (((v1_funct_1 @ (k9_tmap_1 @ sk_A @ sk_B_1))
% 2.93/3.09        | (v1_tsep_1 @ sk_B_1 @ sk_A))),
% 2.93/3.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.93/3.09  thf('165', plain,
% 2.93/3.09      (((v1_tsep_1 @ sk_B_1 @ sk_A)) <= (((v1_tsep_1 @ sk_B_1 @ sk_A)))),
% 2.93/3.09      inference('split', [status(esa)], ['164'])).
% 2.93/3.09  thf('166', plain,
% 2.93/3.09      ((m1_subset_1 @ (u1_struct_0 @ sk_B_1) @ 
% 2.93/3.09        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.93/3.09      inference('demod', [status(thm)], ['3', '4'])).
% 2.93/3.09  thf(d1_tsep_1, axiom,
% 2.93/3.09    (![A:$i]:
% 2.93/3.09     ( ( l1_pre_topc @ A ) =>
% 2.93/3.09       ( ![B:$i]:
% 2.93/3.09         ( ( m1_pre_topc @ B @ A ) =>
% 2.93/3.09           ( ( v1_tsep_1 @ B @ A ) <=>
% 2.93/3.09             ( ![C:$i]:
% 2.93/3.09               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.93/3.09                 ( ( ( C ) = ( u1_struct_0 @ B ) ) => ( v3_pre_topc @ C @ A ) ) ) ) ) ) ) ))).
% 2.93/3.09  thf('167', plain,
% 2.93/3.09      (![X17 : $i, X18 : $i, X19 : $i]:
% 2.93/3.09         (~ (m1_pre_topc @ X17 @ X18)
% 2.93/3.09          | ~ (v1_tsep_1 @ X17 @ X18)
% 2.93/3.09          | ((X19) != (u1_struct_0 @ X17))
% 2.93/3.09          | (v3_pre_topc @ X19 @ X18)
% 2.93/3.09          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 2.93/3.09          | ~ (l1_pre_topc @ X18))),
% 2.93/3.09      inference('cnf', [status(esa)], [d1_tsep_1])).
% 2.93/3.09  thf('168', plain,
% 2.93/3.09      (![X17 : $i, X18 : $i]:
% 2.93/3.09         (~ (l1_pre_topc @ X18)
% 2.93/3.09          | ~ (m1_subset_1 @ (u1_struct_0 @ X17) @ 
% 2.93/3.09               (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 2.93/3.09          | (v3_pre_topc @ (u1_struct_0 @ X17) @ X18)
% 2.93/3.09          | ~ (v1_tsep_1 @ X17 @ X18)
% 2.93/3.09          | ~ (m1_pre_topc @ X17 @ X18))),
% 2.93/3.09      inference('simplify', [status(thm)], ['167'])).
% 2.93/3.09  thf('169', plain,
% 2.93/3.09      ((~ (m1_pre_topc @ sk_B_1 @ sk_A)
% 2.93/3.09        | ~ (v1_tsep_1 @ sk_B_1 @ sk_A)
% 2.93/3.09        | (v3_pre_topc @ (u1_struct_0 @ sk_B_1) @ sk_A)
% 2.93/3.09        | ~ (l1_pre_topc @ sk_A))),
% 2.93/3.09      inference('sup-', [status(thm)], ['166', '168'])).
% 2.93/3.09  thf('170', plain, ((m1_pre_topc @ sk_B_1 @ sk_A)),
% 2.93/3.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.93/3.09  thf('171', plain, ((l1_pre_topc @ sk_A)),
% 2.93/3.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.93/3.09  thf('172', plain,
% 2.93/3.09      ((~ (v1_tsep_1 @ sk_B_1 @ sk_A)
% 2.93/3.09        | (v3_pre_topc @ (u1_struct_0 @ sk_B_1) @ sk_A))),
% 2.93/3.09      inference('demod', [status(thm)], ['169', '170', '171'])).
% 2.93/3.09  thf('173', plain,
% 2.93/3.09      (((v3_pre_topc @ (u1_struct_0 @ sk_B_1) @ sk_A))
% 2.93/3.09         <= (((v1_tsep_1 @ sk_B_1 @ sk_A)))),
% 2.93/3.09      inference('sup-', [status(thm)], ['165', '172'])).
% 2.93/3.09  thf('174', plain,
% 2.93/3.09      ((m1_subset_1 @ (u1_struct_0 @ sk_B_1) @ 
% 2.93/3.09        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.93/3.09      inference('demod', [status(thm)], ['3', '4'])).
% 2.93/3.09  thf('175', plain,
% 2.93/3.09      (![X28 : $i, X29 : $i]:
% 2.93/3.09         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (u1_struct_0 @ X29)))
% 2.93/3.09          | ~ (v3_pre_topc @ X28 @ X29)
% 2.93/3.09          | (v5_pre_topc @ (k7_tmap_1 @ X29 @ X28) @ X29 @ 
% 2.93/3.09             (k6_tmap_1 @ X29 @ X28))
% 2.93/3.09          | ~ (l1_pre_topc @ X29)
% 2.93/3.09          | ~ (v2_pre_topc @ X29)
% 2.93/3.09          | (v2_struct_0 @ X29))),
% 2.93/3.09      inference('cnf', [status(esa)], [t113_tmap_1])).
% 2.93/3.09  thf('176', plain,
% 2.93/3.09      (((v2_struct_0 @ sk_A)
% 2.93/3.09        | ~ (v2_pre_topc @ sk_A)
% 2.93/3.09        | ~ (l1_pre_topc @ sk_A)
% 2.93/3.09        | (v5_pre_topc @ (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B_1)) @ sk_A @ 
% 2.93/3.09           (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B_1)))
% 2.93/3.09        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_B_1) @ sk_A))),
% 2.93/3.09      inference('sup-', [status(thm)], ['174', '175'])).
% 2.93/3.09  thf('177', plain, ((v2_pre_topc @ sk_A)),
% 2.93/3.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.93/3.09  thf('178', plain, ((l1_pre_topc @ sk_A)),
% 2.93/3.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.93/3.09  thf('179', plain,
% 2.93/3.09      (((k8_tmap_1 @ sk_A @ sk_B_1)
% 2.93/3.09         = (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B_1)))),
% 2.93/3.09      inference('clc', [status(thm)], ['44', '45'])).
% 2.93/3.09  thf('180', plain,
% 2.93/3.09      (((v2_struct_0 @ sk_A)
% 2.93/3.09        | (v5_pre_topc @ (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B_1)) @ sk_A @ 
% 2.93/3.09           (k8_tmap_1 @ sk_A @ sk_B_1))
% 2.93/3.09        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_B_1) @ sk_A))),
% 2.93/3.09      inference('demod', [status(thm)], ['176', '177', '178', '179'])).
% 2.93/3.09  thf('181', plain, (~ (v2_struct_0 @ sk_A)),
% 2.93/3.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.93/3.09  thf('182', plain,
% 2.93/3.09      ((~ (v3_pre_topc @ (u1_struct_0 @ sk_B_1) @ sk_A)
% 2.93/3.09        | (v5_pre_topc @ (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B_1)) @ sk_A @ 
% 2.93/3.09           (k8_tmap_1 @ sk_A @ sk_B_1)))),
% 2.93/3.09      inference('clc', [status(thm)], ['180', '181'])).
% 2.93/3.09  thf('183', plain,
% 2.93/3.09      (((v5_pre_topc @ (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B_1)) @ sk_A @ 
% 2.93/3.09         (k8_tmap_1 @ sk_A @ sk_B_1))) <= (((v1_tsep_1 @ sk_B_1 @ sk_A)))),
% 2.93/3.09      inference('sup-', [status(thm)], ['173', '182'])).
% 2.93/3.09  thf('184', plain,
% 2.93/3.09      ((((v5_pre_topc @ (k9_tmap_1 @ sk_A @ sk_B_1) @ sk_A @ 
% 2.93/3.09          (k8_tmap_1 @ sk_A @ sk_B_1))
% 2.93/3.09         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 2.93/3.09         <= (((v1_tsep_1 @ sk_B_1 @ sk_A)))),
% 2.93/3.09      inference('sup+', [status(thm)], ['163', '183'])).
% 2.93/3.09  thf('185', plain,
% 2.93/3.09      ((v1_funct_2 @ (k9_tmap_1 @ sk_A @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 2.93/3.09        (u1_struct_0 @ sk_A))),
% 2.93/3.09      inference('clc', [status(thm)], ['82', '83'])).
% 2.93/3.09  thf('186', plain,
% 2.93/3.09      (((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B_1)) = (u1_struct_0 @ sk_A))),
% 2.93/3.09      inference('demod', [status(thm)], ['12', '46'])).
% 2.93/3.09  thf('187', plain,
% 2.93/3.09      (((m1_subset_1 @ (k9_tmap_1 @ sk_A @ sk_B_1) @ 
% 2.93/3.09         (k1_zfmisc_1 @ 
% 2.93/3.09          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 2.93/3.09           (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B_1))))))
% 2.93/3.09         <= (((m1_subset_1 @ (k9_tmap_1 @ sk_A @ sk_B_1) @ 
% 2.93/3.09               (k1_zfmisc_1 @ 
% 2.93/3.09                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 2.93/3.09                 (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B_1)))))))),
% 2.93/3.09      inference('split', [status(esa)], ['51'])).
% 2.93/3.09  thf('188', plain,
% 2.93/3.09      (((m1_subset_1 @ (k9_tmap_1 @ sk_A @ sk_B_1) @ 
% 2.93/3.09         (k1_zfmisc_1 @ 
% 2.93/3.09          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A)))))
% 2.93/3.09         <= (((m1_subset_1 @ (k9_tmap_1 @ sk_A @ sk_B_1) @ 
% 2.93/3.09               (k1_zfmisc_1 @ 
% 2.93/3.09                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 2.93/3.09                 (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B_1)))))))),
% 2.93/3.09      inference('sup+', [status(thm)], ['186', '187'])).
% 2.93/3.09  thf('189', plain,
% 2.93/3.09      ((~ (m1_subset_1 @ (k9_tmap_1 @ sk_A @ sk_B_1) @ 
% 2.93/3.09           (k1_zfmisc_1 @ 
% 2.93/3.09            (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 2.93/3.09             (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B_1)))))
% 2.93/3.09        | ~ (v5_pre_topc @ (k9_tmap_1 @ sk_A @ sk_B_1) @ sk_A @ 
% 2.93/3.09             (k8_tmap_1 @ sk_A @ sk_B_1))
% 2.93/3.09        | ~ (v1_funct_2 @ (k9_tmap_1 @ sk_A @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 2.93/3.09             (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B_1)))
% 2.93/3.09        | ~ (v1_funct_1 @ (k9_tmap_1 @ sk_A @ sk_B_1))
% 2.93/3.09        | ~ (m1_pre_topc @ sk_B_1 @ sk_A)
% 2.93/3.09        | ~ (v1_tsep_1 @ sk_B_1 @ sk_A))),
% 2.93/3.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.93/3.09  thf('190', plain,
% 2.93/3.09      (((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B_1)) = (u1_struct_0 @ sk_A))),
% 2.93/3.09      inference('demod', [status(thm)], ['12', '46'])).
% 2.93/3.09  thf('191', plain,
% 2.93/3.09      (((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B_1)) = (u1_struct_0 @ sk_A))),
% 2.93/3.09      inference('demod', [status(thm)], ['12', '46'])).
% 2.93/3.09  thf('192', plain, ((v1_funct_1 @ (k9_tmap_1 @ sk_A @ sk_B_1))),
% 2.93/3.09      inference('clc', [status(thm)], ['67', '68'])).
% 2.93/3.09  thf('193', plain, ((m1_pre_topc @ sk_B_1 @ sk_A)),
% 2.93/3.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.93/3.09  thf('194', plain,
% 2.93/3.09      ((~ (m1_subset_1 @ (k9_tmap_1 @ sk_A @ sk_B_1) @ 
% 2.93/3.09           (k1_zfmisc_1 @ 
% 2.93/3.09            (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))))
% 2.93/3.09        | ~ (v5_pre_topc @ (k9_tmap_1 @ sk_A @ sk_B_1) @ sk_A @ 
% 2.93/3.09             (k8_tmap_1 @ sk_A @ sk_B_1))
% 2.93/3.09        | ~ (v1_funct_2 @ (k9_tmap_1 @ sk_A @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 2.93/3.09             (u1_struct_0 @ sk_A))
% 2.93/3.09        | ~ (v1_tsep_1 @ sk_B_1 @ sk_A))),
% 2.93/3.09      inference('demod', [status(thm)], ['189', '190', '191', '192', '193'])).
% 2.93/3.09  thf('195', plain,
% 2.93/3.09      (((~ (v1_tsep_1 @ sk_B_1 @ sk_A)
% 2.93/3.09         | ~ (v1_funct_2 @ (k9_tmap_1 @ sk_A @ sk_B_1) @ 
% 2.93/3.09              (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))
% 2.93/3.09         | ~ (v5_pre_topc @ (k9_tmap_1 @ sk_A @ sk_B_1) @ sk_A @ 
% 2.93/3.09              (k8_tmap_1 @ sk_A @ sk_B_1))))
% 2.93/3.09         <= (((m1_subset_1 @ (k9_tmap_1 @ sk_A @ sk_B_1) @ 
% 2.93/3.09               (k1_zfmisc_1 @ 
% 2.93/3.09                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 2.93/3.09                 (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B_1)))))))),
% 2.93/3.09      inference('sup-', [status(thm)], ['188', '194'])).
% 2.93/3.09  thf('196', plain,
% 2.93/3.09      (((~ (v5_pre_topc @ (k9_tmap_1 @ sk_A @ sk_B_1) @ sk_A @ 
% 2.93/3.09            (k8_tmap_1 @ sk_A @ sk_B_1))
% 2.93/3.09         | ~ (v1_tsep_1 @ sk_B_1 @ sk_A)))
% 2.93/3.09         <= (((m1_subset_1 @ (k9_tmap_1 @ sk_A @ sk_B_1) @ 
% 2.93/3.09               (k1_zfmisc_1 @ 
% 2.93/3.09                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 2.93/3.09                 (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B_1)))))))),
% 2.93/3.09      inference('sup-', [status(thm)], ['185', '195'])).
% 2.93/3.09  thf('197', plain,
% 2.93/3.09      (((m1_subset_1 @ (k9_tmap_1 @ sk_A @ sk_B_1) @ 
% 2.93/3.09         (k1_zfmisc_1 @ 
% 2.93/3.09          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 2.93/3.09           (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B_1))))))),
% 2.93/3.09      inference('sat_resolution*', [status(thm)], ['104'])).
% 2.93/3.09  thf('198', plain,
% 2.93/3.09      ((~ (v5_pre_topc @ (k9_tmap_1 @ sk_A @ sk_B_1) @ sk_A @ 
% 2.93/3.09           (k8_tmap_1 @ sk_A @ sk_B_1))
% 2.93/3.09        | ~ (v1_tsep_1 @ sk_B_1 @ sk_A))),
% 2.93/3.09      inference('simpl_trail', [status(thm)], ['196', '197'])).
% 2.93/3.09  thf('199', plain,
% 2.93/3.09      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A)) | ~ (v1_tsep_1 @ sk_B_1 @ sk_A)))
% 2.93/3.09         <= (((v1_tsep_1 @ sk_B_1 @ sk_A)))),
% 2.93/3.09      inference('sup-', [status(thm)], ['184', '198'])).
% 2.93/3.09  thf('200', plain,
% 2.93/3.09      (((v1_tsep_1 @ sk_B_1 @ sk_A)) <= (((v1_tsep_1 @ sk_B_1 @ sk_A)))),
% 2.93/3.09      inference('split', [status(esa)], ['164'])).
% 2.93/3.09  thf('201', plain,
% 2.93/3.09      (((v1_xboole_0 @ (u1_struct_0 @ sk_A)))
% 2.93/3.09         <= (((v1_tsep_1 @ sk_B_1 @ sk_A)))),
% 2.93/3.09      inference('demod', [status(thm)], ['199', '200'])).
% 2.93/3.09  thf(fc2_struct_0, axiom,
% 2.93/3.09    (![A:$i]:
% 2.93/3.09     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 2.93/3.09       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 2.93/3.09  thf('202', plain,
% 2.93/3.09      (![X2 : $i]:
% 2.93/3.09         (~ (v1_xboole_0 @ (u1_struct_0 @ X2))
% 2.93/3.09          | ~ (l1_struct_0 @ X2)
% 2.93/3.09          | (v2_struct_0 @ X2))),
% 2.93/3.09      inference('cnf', [status(esa)], [fc2_struct_0])).
% 2.93/3.09  thf('203', plain,
% 2.93/3.09      ((((v2_struct_0 @ sk_A) | ~ (l1_struct_0 @ sk_A)))
% 2.93/3.09         <= (((v1_tsep_1 @ sk_B_1 @ sk_A)))),
% 2.93/3.09      inference('sup-', [status(thm)], ['201', '202'])).
% 2.93/3.09  thf('204', plain, ((l1_pre_topc @ sk_A)),
% 2.93/3.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.93/3.09  thf(dt_l1_pre_topc, axiom,
% 2.93/3.09    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 2.93/3.09  thf('205', plain, (![X0 : $i]: ((l1_struct_0 @ X0) | ~ (l1_pre_topc @ X0))),
% 2.93/3.09      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 2.93/3.09  thf('206', plain, ((l1_struct_0 @ sk_A)),
% 2.93/3.09      inference('sup-', [status(thm)], ['204', '205'])).
% 2.93/3.09  thf('207', plain,
% 2.93/3.09      (((v2_struct_0 @ sk_A)) <= (((v1_tsep_1 @ sk_B_1 @ sk_A)))),
% 2.93/3.09      inference('demod', [status(thm)], ['203', '206'])).
% 2.93/3.09  thf('208', plain, (~ (v2_struct_0 @ sk_A)),
% 2.93/3.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.93/3.09  thf('209', plain, (~ ((v1_tsep_1 @ sk_B_1 @ sk_A))),
% 2.93/3.09      inference('sup-', [status(thm)], ['207', '208'])).
% 2.93/3.09  thf('210', plain,
% 2.93/3.09      (((v5_pre_topc @ (k9_tmap_1 @ sk_A @ sk_B_1) @ sk_A @ 
% 2.93/3.09         (k8_tmap_1 @ sk_A @ sk_B_1))) | 
% 2.93/3.09       ((v1_tsep_1 @ sk_B_1 @ sk_A))),
% 2.93/3.09      inference('split', [status(esa)], ['161'])).
% 2.93/3.09  thf('211', plain,
% 2.93/3.09      (((v5_pre_topc @ (k9_tmap_1 @ sk_A @ sk_B_1) @ sk_A @ 
% 2.93/3.09         (k8_tmap_1 @ sk_A @ sk_B_1)))),
% 2.93/3.09      inference('sat_resolution*', [status(thm)], ['209', '210'])).
% 2.93/3.09  thf('212', plain,
% 2.93/3.09      ((v5_pre_topc @ (k9_tmap_1 @ sk_A @ sk_B_1) @ sk_A @ 
% 2.93/3.09        (k8_tmap_1 @ sk_A @ sk_B_1))),
% 2.93/3.09      inference('simpl_trail', [status(thm)], ['162', '211'])).
% 2.93/3.09  thf('213', plain,
% 2.93/3.09      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 2.93/3.09        | (v3_pre_topc @ (u1_struct_0 @ sk_B_1) @ sk_A))),
% 2.93/3.09      inference('demod', [status(thm)], ['160', '212'])).
% 2.93/3.09  thf('214', plain, ((m1_pre_topc @ sk_B_1 @ sk_A)),
% 2.93/3.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.93/3.09  thf('215', plain,
% 2.93/3.09      (![X17 : $i, X18 : $i]:
% 2.93/3.09         (~ (m1_pre_topc @ X17 @ X18)
% 2.93/3.09          | ((sk_C @ X17 @ X18) = (u1_struct_0 @ X17))
% 2.93/3.09          | (v1_tsep_1 @ X17 @ X18)
% 2.93/3.09          | ~ (l1_pre_topc @ X18))),
% 2.93/3.09      inference('cnf', [status(esa)], [d1_tsep_1])).
% 2.93/3.09  thf('216', plain,
% 2.93/3.09      ((~ (l1_pre_topc @ sk_A)
% 2.93/3.09        | (v1_tsep_1 @ sk_B_1 @ sk_A)
% 2.93/3.09        | ((sk_C @ sk_B_1 @ sk_A) = (u1_struct_0 @ sk_B_1)))),
% 2.93/3.09      inference('sup-', [status(thm)], ['214', '215'])).
% 2.93/3.09  thf('217', plain, ((l1_pre_topc @ sk_A)),
% 2.93/3.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.93/3.09  thf('218', plain,
% 2.93/3.09      (((v1_tsep_1 @ sk_B_1 @ sk_A)
% 2.93/3.09        | ((sk_C @ sk_B_1 @ sk_A) = (u1_struct_0 @ sk_B_1)))),
% 2.93/3.09      inference('demod', [status(thm)], ['216', '217'])).
% 2.93/3.09  thf('219', plain,
% 2.93/3.09      ((~ (v1_tsep_1 @ sk_B_1 @ sk_A)) <= (~ ((v1_tsep_1 @ sk_B_1 @ sk_A)))),
% 2.93/3.09      inference('split', [status(esa)], ['86'])).
% 2.93/3.09  thf('220', plain,
% 2.93/3.09      ((((sk_C @ sk_B_1 @ sk_A) = (u1_struct_0 @ sk_B_1)))
% 2.93/3.09         <= (~ ((v1_tsep_1 @ sk_B_1 @ sk_A)))),
% 2.93/3.09      inference('sup-', [status(thm)], ['218', '219'])).
% 2.93/3.09  thf('221', plain,
% 2.93/3.09      (![X17 : $i, X18 : $i]:
% 2.93/3.09         (~ (m1_pre_topc @ X17 @ X18)
% 2.93/3.09          | ~ (v3_pre_topc @ (sk_C @ X17 @ X18) @ X18)
% 2.93/3.09          | (v1_tsep_1 @ X17 @ X18)
% 2.93/3.09          | ~ (l1_pre_topc @ X18))),
% 2.93/3.09      inference('cnf', [status(esa)], [d1_tsep_1])).
% 2.93/3.09  thf('222', plain,
% 2.93/3.09      (((~ (v3_pre_topc @ (u1_struct_0 @ sk_B_1) @ sk_A)
% 2.93/3.09         | ~ (l1_pre_topc @ sk_A)
% 2.93/3.09         | (v1_tsep_1 @ sk_B_1 @ sk_A)
% 2.93/3.09         | ~ (m1_pre_topc @ sk_B_1 @ sk_A)))
% 2.93/3.09         <= (~ ((v1_tsep_1 @ sk_B_1 @ sk_A)))),
% 2.93/3.09      inference('sup-', [status(thm)], ['220', '221'])).
% 2.93/3.09  thf('223', plain, ((l1_pre_topc @ sk_A)),
% 2.93/3.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.93/3.09  thf('224', plain, ((m1_pre_topc @ sk_B_1 @ sk_A)),
% 2.93/3.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.93/3.09  thf('225', plain,
% 2.93/3.09      (((~ (v3_pre_topc @ (u1_struct_0 @ sk_B_1) @ sk_A)
% 2.93/3.09         | (v1_tsep_1 @ sk_B_1 @ sk_A))) <= (~ ((v1_tsep_1 @ sk_B_1 @ sk_A)))),
% 2.93/3.09      inference('demod', [status(thm)], ['222', '223', '224'])).
% 2.93/3.09  thf('226', plain,
% 2.93/3.09      ((~ (v1_tsep_1 @ sk_B_1 @ sk_A)) <= (~ ((v1_tsep_1 @ sk_B_1 @ sk_A)))),
% 2.93/3.09      inference('split', [status(esa)], ['86'])).
% 2.93/3.09  thf('227', plain,
% 2.93/3.09      ((~ (v3_pre_topc @ (u1_struct_0 @ sk_B_1) @ sk_A))
% 2.93/3.09         <= (~ ((v1_tsep_1 @ sk_B_1 @ sk_A)))),
% 2.93/3.09      inference('clc', [status(thm)], ['225', '226'])).
% 2.93/3.09  thf('228', plain, (~ ((v1_tsep_1 @ sk_B_1 @ sk_A))),
% 2.93/3.09      inference('sat_resolution*', [status(thm)], ['209'])).
% 2.93/3.09  thf('229', plain, (~ (v3_pre_topc @ (u1_struct_0 @ sk_B_1) @ sk_A)),
% 2.93/3.09      inference('simpl_trail', [status(thm)], ['227', '228'])).
% 2.93/3.09  thf('230', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 2.93/3.09      inference('clc', [status(thm)], ['213', '229'])).
% 2.93/3.09  thf('231', plain,
% 2.93/3.09      (![X2 : $i]:
% 2.93/3.09         (~ (v1_xboole_0 @ (u1_struct_0 @ X2))
% 2.93/3.09          | ~ (l1_struct_0 @ X2)
% 2.93/3.09          | (v2_struct_0 @ X2))),
% 2.93/3.09      inference('cnf', [status(esa)], [fc2_struct_0])).
% 2.93/3.09  thf('232', plain, (((v2_struct_0 @ sk_A) | ~ (l1_struct_0 @ sk_A))),
% 2.93/3.09      inference('sup-', [status(thm)], ['230', '231'])).
% 2.93/3.09  thf('233', plain, ((l1_struct_0 @ sk_A)),
% 2.93/3.09      inference('sup-', [status(thm)], ['204', '205'])).
% 2.93/3.09  thf('234', plain, ((v2_struct_0 @ sk_A)),
% 2.93/3.09      inference('demod', [status(thm)], ['232', '233'])).
% 2.93/3.09  thf('235', plain, ($false), inference('demod', [status(thm)], ['0', '234'])).
% 2.93/3.09  
% 2.93/3.09  % SZS output end Refutation
% 2.93/3.09  
% 2.93/3.10  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
