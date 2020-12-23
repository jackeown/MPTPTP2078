%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.nYopWfiY56

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:11:03 EST 2020

% Result     : Theorem 0.45s
% Output     : Refutation 0.45s
% Verified   : 
% Statistics : Number of formulae       :  270 (7342 expanded)
%              Number of leaves         :   39 (2122 expanded)
%              Depth                    :   31
%              Number of atoms          : 3064 (197221 expanded)
%              Number of equality atoms :   61 (1034 expanded)
%              Maximal formula depth    :   23 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k5_tmap_1_type,type,(
    k5_tmap_1: $i > $i > $i )).

thf(k7_tmap_1_type,type,(
    k7_tmap_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k9_tmap_1_type,type,(
    k9_tmap_1: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(r1_funct_2_type,type,(
    r1_funct_2: $i > $i > $i > $i > $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(v5_pre_topc_type,type,(
    v5_pre_topc: $i > $i > $i > $o )).

thf(k6_tmap_1_type,type,(
    k6_tmap_1: $i > $i > $i )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(k8_tmap_1_type,type,(
    k8_tmap_1: $i > $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_tsep_1_type,type,(
    v1_tsep_1: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

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

thf('1',plain,
    ( ( m1_subset_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ) )
    | ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,
    ( ( m1_subset_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ) )
   <= ( m1_subset_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ) ) ),
    inference(split,[status(esa)],['1'])).

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

thf('3',plain,(
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

thf('4',plain,(
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
    inference(simplify,[status(thm)],['3'])).

thf('5',plain,
    ( ( ~ ( m1_pre_topc @ sk_B @ sk_A )
      | ( r1_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v1_funct_2 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) )
      | ~ ( v1_funct_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ( m1_subset_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['2','4'])).

thf('6',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t1_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( m1_subset_1 @ ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('8',plain,(
    ! [X30: $i,X31: $i] :
      ( ~ ( m1_pre_topc @ X30 @ X31 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X30 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X31 ) ) )
      | ~ ( l1_pre_topc @ X31 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('9',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['9','10'])).

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

thf('12',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
      | ( ( u1_struct_0 @ ( k6_tmap_1 @ X27 @ X26 ) )
        = ( u1_struct_0 @ X27 ) )
      | ~ ( l1_pre_topc @ X27 )
      | ~ ( v2_pre_topc @ X27 )
      | ( v2_struct_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t104_tmap_1])).

thf('13',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['13','14','15'])).

thf('17',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['16','17'])).

thf('19',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['9','10'])).

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

thf('20',plain,(
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

thf('21',plain,(
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
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,
    ( ~ ( m1_pre_topc @ sk_B @ sk_A )
    | ( ( k8_tmap_1 @ sk_A @ sk_B )
      = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
    | ~ ( l1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( v2_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( v1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['19','21'])).

thf('23',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
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

thf('25',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( l1_pre_topc @ X22 )
      | ~ ( v2_pre_topc @ X22 )
      | ( v2_struct_0 @ X22 )
      | ~ ( m1_pre_topc @ X23 @ X22 )
      | ( l1_pre_topc @ ( k8_tmap_1 @ X22 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k8_tmap_1])).

thf('26',plain,
    ( ( l1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ( l1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['26','27','28'])).

thf('30',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    l1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['29','30'])).

thf('32',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( l1_pre_topc @ X22 )
      | ~ ( v2_pre_topc @ X22 )
      | ( v2_struct_0 @ X22 )
      | ~ ( m1_pre_topc @ X23 @ X22 )
      | ( v2_pre_topc @ ( k8_tmap_1 @ X22 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k8_tmap_1])).

thf('34',plain,
    ( ( v2_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ( v2_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['34','35','36'])).

thf('38',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    v2_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['37','38'])).

thf('40',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( l1_pre_topc @ X22 )
      | ~ ( v2_pre_topc @ X22 )
      | ( v2_struct_0 @ X22 )
      | ~ ( m1_pre_topc @ X23 @ X22 )
      | ( v1_pre_topc @ ( k8_tmap_1 @ X22 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k8_tmap_1])).

thf('42',plain,
    ( ( v1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ( v1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['42','43','44'])).

thf('46',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    v1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['45','46'])).

thf('48',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,
    ( ( ( k8_tmap_1 @ sk_A @ sk_B )
      = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['22','23','31','39','47','48','49'])).

thf('51',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,
    ( ( k8_tmap_1 @ sk_A @ sk_B )
    = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['50','51'])).

thf('53',plain,
    ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['18','52'])).

thf('54',plain,
    ( ( k8_tmap_1 @ sk_A @ sk_B )
    = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['50','51'])).

thf('55',plain,
    ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['18','52'])).

thf('56',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('57',plain,
    ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['18','52'])).

thf('58',plain,(
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

thf('59',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( l1_pre_topc @ X24 )
      | ~ ( v2_pre_topc @ X24 )
      | ( v2_struct_0 @ X24 )
      | ~ ( m1_pre_topc @ X25 @ X24 )
      | ( v1_funct_1 @ ( k9_tmap_1 @ X24 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k9_tmap_1])).

thf('60',plain,
    ( ( v1_funct_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) )
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
    ( ( v1_funct_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['60','61','62'])).

thf('64',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    v1_funct_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['63','64'])).

thf('66',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,
    ( ( ( r1_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
      | ~ ( v1_funct_2 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( m1_subset_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ) ) ),
    inference(demod,[status(thm)],['5','6','53','54','55','56','57','65','66','67'])).

thf('69',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( l1_pre_topc @ X24 )
      | ~ ( v2_pre_topc @ X24 )
      | ( v2_struct_0 @ X24 )
      | ~ ( m1_pre_topc @ X25 @ X24 )
      | ( v1_funct_2 @ ( k9_tmap_1 @ X24 @ X25 ) @ ( u1_struct_0 @ X24 ) @ ( u1_struct_0 @ ( k8_tmap_1 @ X24 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k9_tmap_1])).

thf('71',plain,
    ( ( v1_funct_2 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,
    ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['18','52'])).

thf('73',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,
    ( ( v1_funct_2 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['71','72','73','74'])).

thf('76',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    v1_funct_2 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['75','76'])).

thf('78',plain,
    ( ( ( r1_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( m1_subset_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ) ) ),
    inference(demod,[status(thm)],['68','77'])).

thf('79',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,
    ( ( r1_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
   <= ( m1_subset_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ) ) ),
    inference(clc,[status(thm)],['78','79'])).

thf('81',plain,(
    v1_funct_2 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['75','76'])).

thf('82',plain,
    ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['18','52'])).

thf('83',plain,
    ( ( m1_subset_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ) )
   <= ( m1_subset_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ) ) ),
    inference(split,[status(esa)],['1'])).

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

thf('84',plain,(
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

thf('85',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ~ ( r1_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) @ X2 @ X1 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ X0 )
        | ( ( k9_tmap_1 @ sk_A @ sk_B )
          = X0 )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
        | ~ ( v1_funct_2 @ X0 @ X2 @ X1 )
        | ~ ( v1_funct_1 @ X0 )
        | ( v1_xboole_0 @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) )
        | ( v1_xboole_0 @ X1 )
        | ~ ( v1_funct_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) )
        | ~ ( v1_funct_2 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) )
   <= ( m1_subset_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    v1_funct_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['63','64'])).

thf('87',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ~ ( r1_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) @ X2 @ X1 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ X0 )
        | ( ( k9_tmap_1 @ sk_A @ sk_B )
          = X0 )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
        | ~ ( v1_funct_2 @ X0 @ X2 @ X1 )
        | ~ ( v1_funct_1 @ X0 )
        | ( v1_xboole_0 @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) )
        | ( v1_xboole_0 @ X1 )
        | ~ ( v1_funct_2 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) )
   <= ( m1_subset_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ) ) ),
    inference(demod,[status(thm)],['85','86'])).

thf('88',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ~ ( v1_funct_2 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
        | ( v1_xboole_0 @ X0 )
        | ( v1_xboole_0 @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) )
        | ~ ( v1_funct_1 @ X1 )
        | ~ ( v1_funct_2 @ X1 @ X2 @ X0 )
        | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
        | ( ( k9_tmap_1 @ sk_A @ sk_B )
          = X1 )
        | ~ ( r1_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) @ X2 @ X0 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ X1 ) )
   <= ( m1_subset_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['82','87'])).

thf('89',plain,
    ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['18','52'])).

thf('90',plain,
    ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['18','52'])).

thf('91',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ~ ( v1_funct_2 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
        | ( v1_xboole_0 @ X0 )
        | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( v1_funct_1 @ X1 )
        | ~ ( v1_funct_2 @ X1 @ X2 @ X0 )
        | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
        | ( ( k9_tmap_1 @ sk_A @ sk_B )
          = X1 )
        | ~ ( r1_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ X2 @ X0 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ X1 ) )
   <= ( m1_subset_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ) ) ),
    inference(demod,[status(thm)],['88','89','90'])).

thf('92',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ~ ( r1_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ X2 @ X1 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ X0 )
        | ( ( k9_tmap_1 @ sk_A @ sk_B )
          = X0 )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
        | ~ ( v1_funct_2 @ X0 @ X2 @ X1 )
        | ~ ( v1_funct_1 @ X0 )
        | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
        | ( v1_xboole_0 @ X1 ) )
   <= ( m1_subset_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['81','91'])).

thf('93',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_1 @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
      | ~ ( v1_funct_2 @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) )
      | ( ( k9_tmap_1 @ sk_A @ sk_B )
        = ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ) )
   <= ( m1_subset_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['80','92'])).

thf('94',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf(dt_k7_tmap_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( ( v1_funct_1 @ ( k7_tmap_1 @ A @ B ) )
        & ( v1_funct_2 @ ( k7_tmap_1 @ A @ B ) @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ A @ B ) ) )
        & ( m1_subset_1 @ ( k7_tmap_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ A @ B ) ) ) ) ) ) ) )).

thf('95',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( l1_pre_topc @ X20 )
      | ~ ( v2_pre_topc @ X20 )
      | ( v2_struct_0 @ X20 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ( v1_funct_1 @ ( k7_tmap_1 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_tmap_1])).

thf('96',plain,
    ( ( v1_funct_1 @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,
    ( ( v1_funct_1 @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['96','97','98'])).

thf('100',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,(
    v1_funct_1 @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['99','100'])).

thf('102',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('103',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( l1_pre_topc @ X20 )
      | ~ ( v2_pre_topc @ X20 )
      | ( v2_struct_0 @ X20 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ( m1_subset_1 @ ( k7_tmap_1 @ X20 @ X21 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X20 ) @ ( u1_struct_0 @ ( k6_tmap_1 @ X20 @ X21 ) ) ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_tmap_1])).

thf('104',plain,
    ( ( m1_subset_1 @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ) ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['102','103'])).

thf('105',plain,
    ( ( k8_tmap_1 @ sk_A @ sk_B )
    = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['50','51'])).

thf('106',plain,
    ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['18','52'])).

thf('107',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,
    ( ( m1_subset_1 @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['104','105','106','107','108'])).

thf('110',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,(
    m1_subset_1 @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['109','110'])).

thf('112',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_2 @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( ( k9_tmap_1 @ sk_A @ sk_B )
        = ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ) )
   <= ( m1_subset_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ) ) ),
    inference(demod,[status(thm)],['93','101','111'])).

thf('113',plain,
    ( ( ( ( k9_tmap_1 @ sk_A @ sk_B )
        = ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
      | ~ ( v1_funct_2 @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_subset_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ) ) ),
    inference(simplify,[status(thm)],['112'])).

thf('114',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('115',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( l1_pre_topc @ X20 )
      | ~ ( v2_pre_topc @ X20 )
      | ( v2_struct_0 @ X20 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ( v1_funct_2 @ ( k7_tmap_1 @ X20 @ X21 ) @ ( u1_struct_0 @ X20 ) @ ( u1_struct_0 @ ( k6_tmap_1 @ X20 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_tmap_1])).

thf('116',plain,
    ( ( v1_funct_2 @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['114','115'])).

thf('117',plain,
    ( ( k8_tmap_1 @ sk_A @ sk_B )
    = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['50','51'])).

thf('118',plain,
    ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['18','52'])).

thf('119',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('121',plain,
    ( ( v1_funct_2 @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['116','117','118','119','120'])).

thf('122',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,(
    v1_funct_2 @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['121','122'])).

thf('124',plain,
    ( ( ( ( k9_tmap_1 @ sk_A @ sk_B )
        = ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_subset_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ) ) ),
    inference(demod,[status(thm)],['113','123'])).

thf('125',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( l1_pre_topc @ X24 )
      | ~ ( v2_pre_topc @ X24 )
      | ( v2_struct_0 @ X24 )
      | ~ ( m1_pre_topc @ X25 @ X24 )
      | ( m1_subset_1 @ ( k9_tmap_1 @ X24 @ X25 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X24 ) @ ( u1_struct_0 @ ( k8_tmap_1 @ X24 @ X25 ) ) ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k9_tmap_1])).

thf('127',plain,
    ( ( m1_subset_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['125','126'])).

thf('128',plain,
    ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['18','52'])).

thf('129',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('130',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('131',plain,
    ( ( m1_subset_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['127','128','129','130'])).

thf('132',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('133',plain,(
    m1_subset_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['131','132'])).

thf('134',plain,
    ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['18','52'])).

thf('135',plain,
    ( ~ ( m1_subset_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ) )
    | ~ ( v5_pre_topc @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( v1_funct_2 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) )
    | ~ ( v1_funct_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( m1_pre_topc @ sk_B @ sk_A )
    | ~ ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('136',plain,
    ( ~ ( m1_subset_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ) )
   <= ~ ( m1_subset_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ) ) ),
    inference(split,[status(esa)],['135'])).

thf('137',plain,
    ( ~ ( m1_subset_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ~ ( m1_subset_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['134','136'])).

thf('138',plain,(
    m1_subset_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['133','137'])).

thf('139',plain,(
    m1_subset_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ) ),
    inference('sat_resolution*',[status(thm)],['138'])).

thf('140',plain,
    ( ( ( k9_tmap_1 @ sk_A @ sk_B )
      = ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simpl_trail,[status(thm)],['124','139'])).

thf('141',plain,
    ( ( k8_tmap_1 @ sk_A @ sk_B )
    = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['50','51'])).

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

thf('142',plain,(
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

thf('143',plain,
    ( ~ ( m1_subset_1 @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v3_pre_topc @ ( u1_struct_0 @ sk_B ) @ sk_A )
    | ~ ( v5_pre_topc @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) @ sk_A @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
    | ~ ( v1_funct_2 @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( v1_funct_1 @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
    | ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['141','142'])).

thf('144',plain,
    ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['18','52'])).

thf('145',plain,(
    m1_subset_1 @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['109','110'])).

thf('146',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('147',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('148',plain,
    ( ( k8_tmap_1 @ sk_A @ sk_B )
    = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['50','51'])).

thf('149',plain,
    ( ( k8_tmap_1 @ sk_A @ sk_B )
    = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['50','51'])).

thf('150',plain,
    ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['18','52'])).

thf('151',plain,(
    v1_funct_2 @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['121','122'])).

thf('152',plain,(
    v1_funct_1 @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['99','100'])).

thf('153',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('154',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v3_pre_topc @ ( u1_struct_0 @ sk_B ) @ sk_A )
    | ~ ( v5_pre_topc @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['143','144','145','146','147','148','149','150','151','152','153'])).

thf('155',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('156',plain,
    ( ~ ( v5_pre_topc @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v3_pre_topc @ ( u1_struct_0 @ sk_B ) @ sk_A ) ),
    inference(clc,[status(thm)],['154','155'])).

thf('157',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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

thf('158',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( m1_pre_topc @ X17 @ X18 )
      | ( ( sk_C @ X17 @ X18 )
        = ( u1_struct_0 @ X17 ) )
      | ( v1_tsep_1 @ X17 @ X18 )
      | ~ ( l1_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[d1_tsep_1])).

thf('159',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v1_tsep_1 @ sk_B @ sk_A )
    | ( ( sk_C @ sk_B @ sk_A )
      = ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['157','158'])).

thf('160',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('161',plain,
    ( ( v1_tsep_1 @ sk_B @ sk_A )
    | ( ( sk_C @ sk_B @ sk_A )
      = ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['159','160'])).

thf('162',plain,
    ( ~ ( v1_tsep_1 @ sk_B @ sk_A )
   <= ~ ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['135'])).

thf('163',plain,
    ( ( ( sk_C @ sk_B @ sk_A )
      = ( u1_struct_0 @ sk_B ) )
   <= ~ ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['161','162'])).

thf('164',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( m1_pre_topc @ X17 @ X18 )
      | ~ ( v3_pre_topc @ ( sk_C @ X17 @ X18 ) @ X18 )
      | ( v1_tsep_1 @ X17 @ X18 )
      | ~ ( l1_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[d1_tsep_1])).

thf('165',plain,
    ( ( ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_B ) @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v1_tsep_1 @ sk_B @ sk_A )
      | ~ ( m1_pre_topc @ sk_B @ sk_A ) )
   <= ~ ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['163','164'])).

thf('166',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('167',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('168',plain,
    ( ( ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_B ) @ sk_A )
      | ( v1_tsep_1 @ sk_B @ sk_A ) )
   <= ~ ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['165','166','167'])).

thf('169',plain,
    ( ~ ( v1_tsep_1 @ sk_B @ sk_A )
   <= ~ ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['135'])).

thf('170',plain,
    ( ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_B ) @ sk_A )
   <= ~ ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['168','169'])).

thf('171',plain,
    ( ( ( k9_tmap_1 @ sk_A @ sk_B )
      = ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simpl_trail,[status(thm)],['124','139'])).

thf('172',plain,
    ( ( v1_funct_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) )
    | ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('173',plain,
    ( ( v1_tsep_1 @ sk_B @ sk_A )
   <= ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['172'])).

thf('174',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('175',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_pre_topc @ X17 @ X18 )
      | ~ ( v1_tsep_1 @ X17 @ X18 )
      | ( X19
       != ( u1_struct_0 @ X17 ) )
      | ( v3_pre_topc @ X19 @ X18 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( l1_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[d1_tsep_1])).

thf('176',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( l1_pre_topc @ X18 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X17 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ( v3_pre_topc @ ( u1_struct_0 @ X17 ) @ X18 )
      | ~ ( v1_tsep_1 @ X17 @ X18 )
      | ~ ( m1_pre_topc @ X17 @ X18 ) ) ),
    inference(simplify,[status(thm)],['175'])).

thf('177',plain,
    ( ~ ( m1_pre_topc @ sk_B @ sk_A )
    | ~ ( v1_tsep_1 @ sk_B @ sk_A )
    | ( v3_pre_topc @ ( u1_struct_0 @ sk_B ) @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['174','176'])).

thf('178',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('179',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('180',plain,
    ( ~ ( v1_tsep_1 @ sk_B @ sk_A )
    | ( v3_pre_topc @ ( u1_struct_0 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['177','178','179'])).

thf('181',plain,
    ( ( v3_pre_topc @ ( u1_struct_0 @ sk_B ) @ sk_A )
   <= ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['173','180'])).

thf('182',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('183',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) )
      | ~ ( v3_pre_topc @ X28 @ X29 )
      | ( v5_pre_topc @ ( k7_tmap_1 @ X29 @ X28 ) @ X29 @ ( k6_tmap_1 @ X29 @ X28 ) )
      | ~ ( l1_pre_topc @ X29 )
      | ~ ( v2_pre_topc @ X29 )
      | ( v2_struct_0 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t113_tmap_1])).

thf('184',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v5_pre_topc @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) @ sk_A @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
    | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['182','183'])).

thf('185',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('186',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('187',plain,
    ( ( k8_tmap_1 @ sk_A @ sk_B )
    = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['50','51'])).

thf('188',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v5_pre_topc @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['184','185','186','187'])).

thf('189',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('190',plain,
    ( ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_B ) @ sk_A )
    | ( v5_pre_topc @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['188','189'])).

thf('191',plain,
    ( ( v5_pre_topc @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) )
   <= ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['181','190'])).

thf('192',plain,
    ( ( ( v5_pre_topc @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['171','191'])).

thf('193',plain,
    ( ~ ( m1_subset_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ) )
    | ~ ( v5_pre_topc @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( v1_funct_2 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) )
    | ~ ( v1_funct_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( m1_pre_topc @ sk_B @ sk_A )
    | ~ ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('194',plain,(
    v1_funct_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['63','64'])).

thf('195',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('196',plain,
    ( ~ ( m1_subset_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ) )
    | ~ ( v5_pre_topc @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( v1_funct_2 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) )
    | ~ ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['193','194','195'])).

thf('197',plain,
    ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['18','52'])).

thf('198',plain,
    ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['18','52'])).

thf('199',plain,
    ( ~ ( m1_subset_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ~ ( v5_pre_topc @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( v1_funct_2 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['196','197','198'])).

thf('200',plain,(
    v1_funct_2 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['75','76'])).

thf('201',plain,
    ( ~ ( m1_subset_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ~ ( v5_pre_topc @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['199','200'])).

thf('202',plain,(
    m1_subset_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['131','132'])).

thf('203',plain,
    ( ~ ( v5_pre_topc @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['201','202'])).

thf('204',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_tsep_1 @ sk_B @ sk_A ) )
   <= ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['192','203'])).

thf('205',plain,
    ( ( v1_tsep_1 @ sk_B @ sk_A )
   <= ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['172'])).

thf('206',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
   <= ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['204','205'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('207',plain,(
    ! [X2: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X2 ) )
      | ~ ( l1_struct_0 @ X2 )
      | ( v2_struct_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('208',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['206','207'])).

thf('209',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('210',plain,(
    ! [X0: $i] :
      ( ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('211',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['209','210'])).

thf('212',plain,
    ( ( v2_struct_0 @ sk_A )
   <= ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['208','211'])).

thf('213',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('214',plain,(
    ~ ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['212','213'])).

thf('215',plain,(
    ~ ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['214'])).

thf('216',plain,(
    ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_B ) @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['170','215'])).

thf('217',plain,(
    ~ ( v5_pre_topc @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['156','216'])).

thf('218',plain,
    ( ~ ( v5_pre_topc @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['140','217'])).

thf('219',plain,
    ( ( v5_pre_topc @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('220',plain,
    ( ( v5_pre_topc @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) )
   <= ( v5_pre_topc @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['219'])).

thf('221',plain,
    ( ( v5_pre_topc @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['219'])).

thf('222',plain,(
    v5_pre_topc @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['214','221'])).

thf('223',plain,(
    v5_pre_topc @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['220','222'])).

thf('224',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['218','223'])).

thf('225',plain,(
    ! [X2: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X2 ) )
      | ~ ( l1_struct_0 @ X2 )
      | ( v2_struct_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('226',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['224','225'])).

thf('227',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['209','210'])).

thf('228',plain,(
    v2_struct_0 @ sk_A ),
    inference(demod,[status(thm)],['226','227'])).

thf('229',plain,(
    $false ),
    inference(demod,[status(thm)],['0','228'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.nYopWfiY56
% 0.11/0.31  % Computer   : n017.cluster.edu
% 0.11/0.31  % Model      : x86_64 x86_64
% 0.11/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.31  % Memory     : 8042.1875MB
% 0.11/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.31  % CPULimit   : 60
% 0.11/0.31  % DateTime   : Tue Dec  1 19:40:02 EST 2020
% 0.11/0.32  % CPUTime    : 
% 0.11/0.32  % Running portfolio for 600 s
% 0.11/0.32  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.11/0.32  % Number of cores: 8
% 0.11/0.32  % Python version: Python 3.6.8
% 0.11/0.32  % Running in FO mode
% 0.45/0.67  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.45/0.67  % Solved by: fo/fo7.sh
% 0.45/0.67  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.45/0.67  % done 357 iterations in 0.238s
% 0.45/0.67  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.45/0.67  % SZS output start Refutation
% 0.45/0.67  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.45/0.67  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.45/0.67  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.45/0.67  thf(k5_tmap_1_type, type, k5_tmap_1: $i > $i > $i).
% 0.45/0.67  thf(k7_tmap_1_type, type, k7_tmap_1: $i > $i > $i).
% 0.45/0.67  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.45/0.67  thf(k9_tmap_1_type, type, k9_tmap_1: $i > $i > $i).
% 0.45/0.67  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.45/0.67  thf(r1_funct_2_type, type, r1_funct_2: $i > $i > $i > $i > $i > $i > $o).
% 0.45/0.67  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.45/0.67  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.45/0.67  thf(v5_pre_topc_type, type, v5_pre_topc: $i > $i > $i > $o).
% 0.45/0.67  thf(k6_tmap_1_type, type, k6_tmap_1: $i > $i > $i).
% 0.45/0.67  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 0.45/0.67  thf(k8_tmap_1_type, type, k8_tmap_1: $i > $i > $i).
% 0.45/0.67  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.45/0.67  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.45/0.67  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.45/0.67  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.45/0.67  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 0.45/0.67  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.45/0.67  thf(sk_A_type, type, sk_A: $i).
% 0.45/0.67  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.45/0.67  thf(sk_B_type, type, sk_B: $i).
% 0.45/0.67  thf(v1_tsep_1_type, type, v1_tsep_1: $i > $i > $o).
% 0.45/0.67  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.45/0.67  thf(t122_tmap_1, conjecture,
% 0.45/0.67    (![A:$i]:
% 0.45/0.67     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.45/0.67       ( ![B:$i]:
% 0.45/0.67         ( ( m1_pre_topc @ B @ A ) =>
% 0.45/0.67           ( ( ( v1_tsep_1 @ B @ A ) & ( m1_pre_topc @ B @ A ) ) <=>
% 0.45/0.67             ( ( v1_funct_1 @ ( k9_tmap_1 @ A @ B ) ) & 
% 0.45/0.67               ( v1_funct_2 @
% 0.45/0.67                 ( k9_tmap_1 @ A @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.45/0.67                 ( u1_struct_0 @ ( k8_tmap_1 @ A @ B ) ) ) & 
% 0.45/0.67               ( v5_pre_topc @
% 0.45/0.67                 ( k9_tmap_1 @ A @ B ) @ A @ ( k8_tmap_1 @ A @ B ) ) & 
% 0.45/0.67               ( m1_subset_1 @
% 0.45/0.67                 ( k9_tmap_1 @ A @ B ) @ 
% 0.45/0.67                 ( k1_zfmisc_1 @
% 0.45/0.67                   ( k2_zfmisc_1 @
% 0.45/0.67                     ( u1_struct_0 @ A ) @ 
% 0.45/0.67                     ( u1_struct_0 @ ( k8_tmap_1 @ A @ B ) ) ) ) ) ) ) ) ) ))).
% 0.45/0.67  thf(zf_stmt_0, negated_conjecture,
% 0.45/0.67    (~( ![A:$i]:
% 0.45/0.67        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.45/0.67            ( l1_pre_topc @ A ) ) =>
% 0.45/0.67          ( ![B:$i]:
% 0.45/0.67            ( ( m1_pre_topc @ B @ A ) =>
% 0.45/0.67              ( ( ( v1_tsep_1 @ B @ A ) & ( m1_pre_topc @ B @ A ) ) <=>
% 0.45/0.67                ( ( v1_funct_1 @ ( k9_tmap_1 @ A @ B ) ) & 
% 0.45/0.67                  ( v1_funct_2 @
% 0.45/0.67                    ( k9_tmap_1 @ A @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.45/0.67                    ( u1_struct_0 @ ( k8_tmap_1 @ A @ B ) ) ) & 
% 0.45/0.67                  ( v5_pre_topc @
% 0.45/0.67                    ( k9_tmap_1 @ A @ B ) @ A @ ( k8_tmap_1 @ A @ B ) ) & 
% 0.45/0.67                  ( m1_subset_1 @
% 0.45/0.67                    ( k9_tmap_1 @ A @ B ) @ 
% 0.45/0.67                    ( k1_zfmisc_1 @
% 0.45/0.67                      ( k2_zfmisc_1 @
% 0.45/0.67                        ( u1_struct_0 @ A ) @ 
% 0.45/0.67                        ( u1_struct_0 @ ( k8_tmap_1 @ A @ B ) ) ) ) ) ) ) ) ) ) )),
% 0.45/0.67    inference('cnf.neg', [status(esa)], [t122_tmap_1])).
% 0.45/0.67  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('1', plain,
% 0.45/0.67      (((m1_subset_1 @ (k9_tmap_1 @ sk_A @ sk_B) @ 
% 0.45/0.67         (k1_zfmisc_1 @ 
% 0.45/0.67          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.45/0.67           (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))))
% 0.45/0.67        | (v1_tsep_1 @ sk_B @ sk_A))),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('2', plain,
% 0.45/0.67      (((m1_subset_1 @ (k9_tmap_1 @ sk_A @ sk_B) @ 
% 0.45/0.67         (k1_zfmisc_1 @ 
% 0.45/0.67          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.45/0.67           (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B))))))
% 0.45/0.67         <= (((m1_subset_1 @ (k9_tmap_1 @ sk_A @ sk_B) @ 
% 0.45/0.67               (k1_zfmisc_1 @ 
% 0.45/0.67                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.45/0.67                 (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))))))),
% 0.45/0.67      inference('split', [status(esa)], ['1'])).
% 0.45/0.67  thf(d12_tmap_1, axiom,
% 0.45/0.67    (![A:$i]:
% 0.45/0.67     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.45/0.67       ( ![B:$i]:
% 0.45/0.67         ( ( m1_pre_topc @ B @ A ) =>
% 0.45/0.67           ( ![C:$i]:
% 0.45/0.67             ( ( ( v1_funct_1 @ C ) & 
% 0.45/0.67                 ( v1_funct_2 @
% 0.45/0.67                   C @ ( u1_struct_0 @ A ) @ 
% 0.45/0.67                   ( u1_struct_0 @ ( k8_tmap_1 @ A @ B ) ) ) & 
% 0.45/0.67                 ( m1_subset_1 @
% 0.45/0.67                   C @ 
% 0.45/0.67                   ( k1_zfmisc_1 @
% 0.45/0.67                     ( k2_zfmisc_1 @
% 0.45/0.67                       ( u1_struct_0 @ A ) @ 
% 0.45/0.67                       ( u1_struct_0 @ ( k8_tmap_1 @ A @ B ) ) ) ) ) ) =>
% 0.45/0.67               ( ( ( C ) = ( k9_tmap_1 @ A @ B ) ) <=>
% 0.45/0.67                 ( ![D:$i]:
% 0.45/0.67                   ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.45/0.67                     ( ( ( D ) = ( u1_struct_0 @ B ) ) =>
% 0.45/0.67                       ( r1_funct_2 @
% 0.45/0.67                         ( u1_struct_0 @ A ) @ 
% 0.45/0.67                         ( u1_struct_0 @ ( k8_tmap_1 @ A @ B ) ) @ 
% 0.45/0.67                         ( u1_struct_0 @ A ) @ 
% 0.45/0.67                         ( u1_struct_0 @ ( k6_tmap_1 @ A @ D ) ) @ C @ 
% 0.45/0.67                         ( k7_tmap_1 @ A @ D ) ) ) ) ) ) ) ) ) ) ))).
% 0.45/0.67  thf('3', plain,
% 0.45/0.67      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.45/0.67         (~ (m1_pre_topc @ X13 @ X14)
% 0.45/0.67          | ((X15) != (k9_tmap_1 @ X14 @ X13))
% 0.45/0.67          | ((X16) != (u1_struct_0 @ X13))
% 0.45/0.67          | (r1_funct_2 @ (u1_struct_0 @ X14) @ 
% 0.45/0.67             (u1_struct_0 @ (k8_tmap_1 @ X14 @ X13)) @ (u1_struct_0 @ X14) @ 
% 0.45/0.67             (u1_struct_0 @ (k6_tmap_1 @ X14 @ X16)) @ X15 @ 
% 0.45/0.67             (k7_tmap_1 @ X14 @ X16))
% 0.45/0.67          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.45/0.67          | ~ (m1_subset_1 @ X15 @ 
% 0.45/0.67               (k1_zfmisc_1 @ 
% 0.45/0.67                (k2_zfmisc_1 @ (u1_struct_0 @ X14) @ 
% 0.45/0.67                 (u1_struct_0 @ (k8_tmap_1 @ X14 @ X13)))))
% 0.45/0.67          | ~ (v1_funct_2 @ X15 @ (u1_struct_0 @ X14) @ 
% 0.45/0.67               (u1_struct_0 @ (k8_tmap_1 @ X14 @ X13)))
% 0.45/0.67          | ~ (v1_funct_1 @ X15)
% 0.45/0.67          | ~ (l1_pre_topc @ X14)
% 0.45/0.67          | ~ (v2_pre_topc @ X14)
% 0.45/0.67          | (v2_struct_0 @ X14))),
% 0.45/0.67      inference('cnf', [status(esa)], [d12_tmap_1])).
% 0.45/0.67  thf('4', plain,
% 0.45/0.67      (![X13 : $i, X14 : $i]:
% 0.45/0.67         ((v2_struct_0 @ X14)
% 0.45/0.67          | ~ (v2_pre_topc @ X14)
% 0.45/0.67          | ~ (l1_pre_topc @ X14)
% 0.45/0.67          | ~ (v1_funct_1 @ (k9_tmap_1 @ X14 @ X13))
% 0.45/0.67          | ~ (v1_funct_2 @ (k9_tmap_1 @ X14 @ X13) @ (u1_struct_0 @ X14) @ 
% 0.45/0.67               (u1_struct_0 @ (k8_tmap_1 @ X14 @ X13)))
% 0.45/0.67          | ~ (m1_subset_1 @ (k9_tmap_1 @ X14 @ X13) @ 
% 0.45/0.67               (k1_zfmisc_1 @ 
% 0.45/0.67                (k2_zfmisc_1 @ (u1_struct_0 @ X14) @ 
% 0.45/0.67                 (u1_struct_0 @ (k8_tmap_1 @ X14 @ X13)))))
% 0.45/0.67          | ~ (m1_subset_1 @ (u1_struct_0 @ X13) @ 
% 0.45/0.67               (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.45/0.67          | (r1_funct_2 @ (u1_struct_0 @ X14) @ 
% 0.45/0.67             (u1_struct_0 @ (k8_tmap_1 @ X14 @ X13)) @ (u1_struct_0 @ X14) @ 
% 0.45/0.67             (u1_struct_0 @ (k6_tmap_1 @ X14 @ (u1_struct_0 @ X13))) @ 
% 0.45/0.67             (k9_tmap_1 @ X14 @ X13) @ (k7_tmap_1 @ X14 @ (u1_struct_0 @ X13)))
% 0.45/0.67          | ~ (m1_pre_topc @ X13 @ X14))),
% 0.45/0.67      inference('simplify', [status(thm)], ['3'])).
% 0.45/0.67  thf('5', plain,
% 0.45/0.67      (((~ (m1_pre_topc @ sk_B @ sk_A)
% 0.45/0.67         | (r1_funct_2 @ (u1_struct_0 @ sk_A) @ 
% 0.45/0.67            (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)) @ (u1_struct_0 @ sk_A) @ 
% 0.45/0.67            (u1_struct_0 @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B))) @ 
% 0.45/0.67            (k9_tmap_1 @ sk_A @ sk_B) @ 
% 0.45/0.67            (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 0.45/0.67         | ~ (m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.45/0.67              (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.45/0.67         | ~ (v1_funct_2 @ (k9_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.45/0.67              (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))
% 0.45/0.67         | ~ (v1_funct_1 @ (k9_tmap_1 @ sk_A @ sk_B))
% 0.45/0.67         | ~ (l1_pre_topc @ sk_A)
% 0.45/0.67         | ~ (v2_pre_topc @ sk_A)
% 0.45/0.67         | (v2_struct_0 @ sk_A)))
% 0.45/0.67         <= (((m1_subset_1 @ (k9_tmap_1 @ sk_A @ sk_B) @ 
% 0.45/0.67               (k1_zfmisc_1 @ 
% 0.45/0.67                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.45/0.67                 (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))))))),
% 0.45/0.67      inference('sup-', [status(thm)], ['2', '4'])).
% 0.45/0.67  thf('6', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('7', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf(t1_tsep_1, axiom,
% 0.45/0.67    (![A:$i]:
% 0.45/0.67     ( ( l1_pre_topc @ A ) =>
% 0.45/0.67       ( ![B:$i]:
% 0.45/0.67         ( ( m1_pre_topc @ B @ A ) =>
% 0.45/0.67           ( m1_subset_1 @
% 0.45/0.67             ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.45/0.67  thf('8', plain,
% 0.45/0.67      (![X30 : $i, X31 : $i]:
% 0.45/0.67         (~ (m1_pre_topc @ X30 @ X31)
% 0.45/0.67          | (m1_subset_1 @ (u1_struct_0 @ X30) @ 
% 0.45/0.67             (k1_zfmisc_1 @ (u1_struct_0 @ X31)))
% 0.45/0.67          | ~ (l1_pre_topc @ X31))),
% 0.45/0.67      inference('cnf', [status(esa)], [t1_tsep_1])).
% 0.45/0.67  thf('9', plain,
% 0.45/0.67      ((~ (l1_pre_topc @ sk_A)
% 0.45/0.67        | (m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.45/0.67           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.45/0.67      inference('sup-', [status(thm)], ['7', '8'])).
% 0.45/0.67  thf('10', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('11', plain,
% 0.45/0.67      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.45/0.67        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.67      inference('demod', [status(thm)], ['9', '10'])).
% 0.45/0.67  thf(t104_tmap_1, axiom,
% 0.45/0.67    (![A:$i]:
% 0.45/0.67     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.45/0.67       ( ![B:$i]:
% 0.45/0.67         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.45/0.67           ( ( ( u1_struct_0 @ ( k6_tmap_1 @ A @ B ) ) = ( u1_struct_0 @ A ) ) & 
% 0.45/0.67             ( ( u1_pre_topc @ ( k6_tmap_1 @ A @ B ) ) = ( k5_tmap_1 @ A @ B ) ) ) ) ) ))).
% 0.45/0.67  thf('12', plain,
% 0.45/0.67      (![X26 : $i, X27 : $i]:
% 0.45/0.67         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 0.45/0.67          | ((u1_struct_0 @ (k6_tmap_1 @ X27 @ X26)) = (u1_struct_0 @ X27))
% 0.45/0.67          | ~ (l1_pre_topc @ X27)
% 0.45/0.67          | ~ (v2_pre_topc @ X27)
% 0.45/0.67          | (v2_struct_0 @ X27))),
% 0.45/0.67      inference('cnf', [status(esa)], [t104_tmap_1])).
% 0.45/0.67  thf('13', plain,
% 0.45/0.67      (((v2_struct_0 @ sk_A)
% 0.45/0.67        | ~ (v2_pre_topc @ sk_A)
% 0.45/0.67        | ~ (l1_pre_topc @ sk_A)
% 0.45/0.67        | ((u1_struct_0 @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 0.45/0.67            = (u1_struct_0 @ sk_A)))),
% 0.45/0.67      inference('sup-', [status(thm)], ['11', '12'])).
% 0.45/0.67  thf('14', plain, ((v2_pre_topc @ sk_A)),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('15', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('16', plain,
% 0.45/0.67      (((v2_struct_0 @ sk_A)
% 0.45/0.67        | ((u1_struct_0 @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 0.45/0.67            = (u1_struct_0 @ sk_A)))),
% 0.45/0.67      inference('demod', [status(thm)], ['13', '14', '15'])).
% 0.45/0.67  thf('17', plain, (~ (v2_struct_0 @ sk_A)),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('18', plain,
% 0.45/0.67      (((u1_struct_0 @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 0.45/0.67         = (u1_struct_0 @ sk_A))),
% 0.45/0.67      inference('clc', [status(thm)], ['16', '17'])).
% 0.45/0.67  thf('19', plain,
% 0.45/0.67      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.45/0.67        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.67      inference('demod', [status(thm)], ['9', '10'])).
% 0.45/0.67  thf(d11_tmap_1, axiom,
% 0.45/0.67    (![A:$i]:
% 0.45/0.67     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.45/0.67       ( ![B:$i]:
% 0.45/0.67         ( ( m1_pre_topc @ B @ A ) =>
% 0.45/0.67           ( ![C:$i]:
% 0.45/0.67             ( ( ( v1_pre_topc @ C ) & ( v2_pre_topc @ C ) & 
% 0.45/0.67                 ( l1_pre_topc @ C ) ) =>
% 0.45/0.67               ( ( ( C ) = ( k8_tmap_1 @ A @ B ) ) <=>
% 0.45/0.67                 ( ![D:$i]:
% 0.45/0.67                   ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.45/0.67                     ( ( ( D ) = ( u1_struct_0 @ B ) ) =>
% 0.45/0.67                       ( ( C ) = ( k6_tmap_1 @ A @ D ) ) ) ) ) ) ) ) ) ) ))).
% 0.45/0.67  thf('20', plain,
% 0.45/0.67      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.45/0.67         (~ (m1_pre_topc @ X9 @ X10)
% 0.45/0.67          | ((X11) != (k8_tmap_1 @ X10 @ X9))
% 0.45/0.67          | ((X12) != (u1_struct_0 @ X9))
% 0.45/0.67          | ((X11) = (k6_tmap_1 @ X10 @ X12))
% 0.45/0.67          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 0.45/0.67          | ~ (l1_pre_topc @ X11)
% 0.45/0.67          | ~ (v2_pre_topc @ X11)
% 0.45/0.67          | ~ (v1_pre_topc @ X11)
% 0.45/0.67          | ~ (l1_pre_topc @ X10)
% 0.45/0.67          | ~ (v2_pre_topc @ X10)
% 0.45/0.67          | (v2_struct_0 @ X10))),
% 0.45/0.67      inference('cnf', [status(esa)], [d11_tmap_1])).
% 0.45/0.67  thf('21', plain,
% 0.45/0.67      (![X9 : $i, X10 : $i]:
% 0.45/0.67         ((v2_struct_0 @ X10)
% 0.45/0.67          | ~ (v2_pre_topc @ X10)
% 0.45/0.67          | ~ (l1_pre_topc @ X10)
% 0.45/0.67          | ~ (v1_pre_topc @ (k8_tmap_1 @ X10 @ X9))
% 0.45/0.67          | ~ (v2_pre_topc @ (k8_tmap_1 @ X10 @ X9))
% 0.45/0.67          | ~ (l1_pre_topc @ (k8_tmap_1 @ X10 @ X9))
% 0.45/0.67          | ~ (m1_subset_1 @ (u1_struct_0 @ X9) @ 
% 0.45/0.67               (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 0.45/0.67          | ((k8_tmap_1 @ X10 @ X9) = (k6_tmap_1 @ X10 @ (u1_struct_0 @ X9)))
% 0.45/0.67          | ~ (m1_pre_topc @ X9 @ X10))),
% 0.45/0.67      inference('simplify', [status(thm)], ['20'])).
% 0.45/0.67  thf('22', plain,
% 0.45/0.67      ((~ (m1_pre_topc @ sk_B @ sk_A)
% 0.45/0.67        | ((k8_tmap_1 @ sk_A @ sk_B)
% 0.45/0.67            = (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 0.45/0.67        | ~ (l1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.45/0.67        | ~ (v2_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.45/0.67        | ~ (v1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.45/0.67        | ~ (l1_pre_topc @ sk_A)
% 0.45/0.67        | ~ (v2_pre_topc @ sk_A)
% 0.45/0.67        | (v2_struct_0 @ sk_A))),
% 0.45/0.67      inference('sup-', [status(thm)], ['19', '21'])).
% 0.45/0.67  thf('23', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('24', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf(dt_k8_tmap_1, axiom,
% 0.45/0.67    (![A:$i,B:$i]:
% 0.45/0.67     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.45/0.67         ( l1_pre_topc @ A ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.45/0.67       ( ( v1_pre_topc @ ( k8_tmap_1 @ A @ B ) ) & 
% 0.45/0.67         ( v2_pre_topc @ ( k8_tmap_1 @ A @ B ) ) & 
% 0.45/0.67         ( l1_pre_topc @ ( k8_tmap_1 @ A @ B ) ) ) ))).
% 0.45/0.67  thf('25', plain,
% 0.45/0.67      (![X22 : $i, X23 : $i]:
% 0.45/0.67         (~ (l1_pre_topc @ X22)
% 0.45/0.67          | ~ (v2_pre_topc @ X22)
% 0.45/0.67          | (v2_struct_0 @ X22)
% 0.45/0.67          | ~ (m1_pre_topc @ X23 @ X22)
% 0.45/0.67          | (l1_pre_topc @ (k8_tmap_1 @ X22 @ X23)))),
% 0.45/0.67      inference('cnf', [status(esa)], [dt_k8_tmap_1])).
% 0.45/0.67  thf('26', plain,
% 0.45/0.67      (((l1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.45/0.67        | (v2_struct_0 @ sk_A)
% 0.45/0.67        | ~ (v2_pre_topc @ sk_A)
% 0.45/0.67        | ~ (l1_pre_topc @ sk_A))),
% 0.45/0.67      inference('sup-', [status(thm)], ['24', '25'])).
% 0.45/0.67  thf('27', plain, ((v2_pre_topc @ sk_A)),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('28', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('29', plain,
% 0.45/0.67      (((l1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B)) | (v2_struct_0 @ sk_A))),
% 0.45/0.67      inference('demod', [status(thm)], ['26', '27', '28'])).
% 0.45/0.67  thf('30', plain, (~ (v2_struct_0 @ sk_A)),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('31', plain, ((l1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))),
% 0.45/0.67      inference('clc', [status(thm)], ['29', '30'])).
% 0.45/0.67  thf('32', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('33', plain,
% 0.45/0.67      (![X22 : $i, X23 : $i]:
% 0.45/0.67         (~ (l1_pre_topc @ X22)
% 0.45/0.67          | ~ (v2_pre_topc @ X22)
% 0.45/0.67          | (v2_struct_0 @ X22)
% 0.45/0.67          | ~ (m1_pre_topc @ X23 @ X22)
% 0.45/0.67          | (v2_pre_topc @ (k8_tmap_1 @ X22 @ X23)))),
% 0.45/0.67      inference('cnf', [status(esa)], [dt_k8_tmap_1])).
% 0.45/0.67  thf('34', plain,
% 0.45/0.67      (((v2_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.45/0.67        | (v2_struct_0 @ sk_A)
% 0.45/0.67        | ~ (v2_pre_topc @ sk_A)
% 0.45/0.67        | ~ (l1_pre_topc @ sk_A))),
% 0.45/0.67      inference('sup-', [status(thm)], ['32', '33'])).
% 0.45/0.67  thf('35', plain, ((v2_pre_topc @ sk_A)),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('36', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('37', plain,
% 0.45/0.67      (((v2_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B)) | (v2_struct_0 @ sk_A))),
% 0.45/0.67      inference('demod', [status(thm)], ['34', '35', '36'])).
% 0.45/0.67  thf('38', plain, (~ (v2_struct_0 @ sk_A)),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('39', plain, ((v2_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))),
% 0.45/0.67      inference('clc', [status(thm)], ['37', '38'])).
% 0.45/0.67  thf('40', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('41', plain,
% 0.45/0.67      (![X22 : $i, X23 : $i]:
% 0.45/0.67         (~ (l1_pre_topc @ X22)
% 0.45/0.67          | ~ (v2_pre_topc @ X22)
% 0.45/0.67          | (v2_struct_0 @ X22)
% 0.45/0.67          | ~ (m1_pre_topc @ X23 @ X22)
% 0.45/0.67          | (v1_pre_topc @ (k8_tmap_1 @ X22 @ X23)))),
% 0.45/0.67      inference('cnf', [status(esa)], [dt_k8_tmap_1])).
% 0.45/0.67  thf('42', plain,
% 0.45/0.67      (((v1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.45/0.67        | (v2_struct_0 @ sk_A)
% 0.45/0.67        | ~ (v2_pre_topc @ sk_A)
% 0.45/0.67        | ~ (l1_pre_topc @ sk_A))),
% 0.45/0.67      inference('sup-', [status(thm)], ['40', '41'])).
% 0.45/0.67  thf('43', plain, ((v2_pre_topc @ sk_A)),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('44', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('45', plain,
% 0.45/0.67      (((v1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B)) | (v2_struct_0 @ sk_A))),
% 0.45/0.67      inference('demod', [status(thm)], ['42', '43', '44'])).
% 0.45/0.67  thf('46', plain, (~ (v2_struct_0 @ sk_A)),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('47', plain, ((v1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))),
% 0.45/0.67      inference('clc', [status(thm)], ['45', '46'])).
% 0.45/0.67  thf('48', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('49', plain, ((v2_pre_topc @ sk_A)),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('50', plain,
% 0.45/0.67      ((((k8_tmap_1 @ sk_A @ sk_B) = (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 0.45/0.67        | (v2_struct_0 @ sk_A))),
% 0.45/0.67      inference('demod', [status(thm)],
% 0.45/0.67                ['22', '23', '31', '39', '47', '48', '49'])).
% 0.45/0.67  thf('51', plain, (~ (v2_struct_0 @ sk_A)),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('52', plain,
% 0.45/0.67      (((k8_tmap_1 @ sk_A @ sk_B) = (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))),
% 0.45/0.67      inference('clc', [status(thm)], ['50', '51'])).
% 0.45/0.67  thf('53', plain,
% 0.45/0.67      (((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 0.45/0.67      inference('demod', [status(thm)], ['18', '52'])).
% 0.45/0.67  thf('54', plain,
% 0.45/0.67      (((k8_tmap_1 @ sk_A @ sk_B) = (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))),
% 0.45/0.67      inference('clc', [status(thm)], ['50', '51'])).
% 0.45/0.67  thf('55', plain,
% 0.45/0.67      (((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 0.45/0.67      inference('demod', [status(thm)], ['18', '52'])).
% 0.45/0.67  thf('56', plain,
% 0.45/0.67      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.45/0.67        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.67      inference('demod', [status(thm)], ['9', '10'])).
% 0.45/0.67  thf('57', plain,
% 0.45/0.67      (((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 0.45/0.67      inference('demod', [status(thm)], ['18', '52'])).
% 0.45/0.67  thf('58', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf(dt_k9_tmap_1, axiom,
% 0.45/0.67    (![A:$i,B:$i]:
% 0.45/0.67     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.45/0.67         ( l1_pre_topc @ A ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.45/0.67       ( ( v1_funct_1 @ ( k9_tmap_1 @ A @ B ) ) & 
% 0.45/0.67         ( v1_funct_2 @
% 0.45/0.67           ( k9_tmap_1 @ A @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.45/0.67           ( u1_struct_0 @ ( k8_tmap_1 @ A @ B ) ) ) & 
% 0.45/0.67         ( m1_subset_1 @
% 0.45/0.67           ( k9_tmap_1 @ A @ B ) @ 
% 0.45/0.67           ( k1_zfmisc_1 @
% 0.45/0.67             ( k2_zfmisc_1 @
% 0.45/0.67               ( u1_struct_0 @ A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ A @ B ) ) ) ) ) ) ))).
% 0.45/0.67  thf('59', plain,
% 0.45/0.67      (![X24 : $i, X25 : $i]:
% 0.45/0.67         (~ (l1_pre_topc @ X24)
% 0.45/0.67          | ~ (v2_pre_topc @ X24)
% 0.45/0.67          | (v2_struct_0 @ X24)
% 0.45/0.67          | ~ (m1_pre_topc @ X25 @ X24)
% 0.45/0.67          | (v1_funct_1 @ (k9_tmap_1 @ X24 @ X25)))),
% 0.45/0.67      inference('cnf', [status(esa)], [dt_k9_tmap_1])).
% 0.45/0.67  thf('60', plain,
% 0.45/0.67      (((v1_funct_1 @ (k9_tmap_1 @ sk_A @ sk_B))
% 0.45/0.67        | (v2_struct_0 @ sk_A)
% 0.45/0.67        | ~ (v2_pre_topc @ sk_A)
% 0.45/0.67        | ~ (l1_pre_topc @ sk_A))),
% 0.45/0.67      inference('sup-', [status(thm)], ['58', '59'])).
% 0.45/0.67  thf('61', plain, ((v2_pre_topc @ sk_A)),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('62', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('63', plain,
% 0.45/0.67      (((v1_funct_1 @ (k9_tmap_1 @ sk_A @ sk_B)) | (v2_struct_0 @ sk_A))),
% 0.45/0.67      inference('demod', [status(thm)], ['60', '61', '62'])).
% 0.45/0.67  thf('64', plain, (~ (v2_struct_0 @ sk_A)),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('65', plain, ((v1_funct_1 @ (k9_tmap_1 @ sk_A @ sk_B))),
% 0.45/0.67      inference('clc', [status(thm)], ['63', '64'])).
% 0.45/0.67  thf('66', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('67', plain, ((v2_pre_topc @ sk_A)),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('68', plain,
% 0.45/0.67      ((((r1_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.45/0.67          (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.45/0.67          (k9_tmap_1 @ sk_A @ sk_B) @ (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 0.45/0.67         | ~ (v1_funct_2 @ (k9_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.45/0.67              (u1_struct_0 @ sk_A))
% 0.45/0.67         | (v2_struct_0 @ sk_A)))
% 0.45/0.67         <= (((m1_subset_1 @ (k9_tmap_1 @ sk_A @ sk_B) @ 
% 0.45/0.67               (k1_zfmisc_1 @ 
% 0.45/0.67                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.45/0.67                 (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))))))),
% 0.45/0.67      inference('demod', [status(thm)],
% 0.45/0.67                ['5', '6', '53', '54', '55', '56', '57', '65', '66', '67'])).
% 0.45/0.67  thf('69', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('70', plain,
% 0.45/0.67      (![X24 : $i, X25 : $i]:
% 0.45/0.67         (~ (l1_pre_topc @ X24)
% 0.45/0.67          | ~ (v2_pre_topc @ X24)
% 0.45/0.67          | (v2_struct_0 @ X24)
% 0.45/0.67          | ~ (m1_pre_topc @ X25 @ X24)
% 0.45/0.67          | (v1_funct_2 @ (k9_tmap_1 @ X24 @ X25) @ (u1_struct_0 @ X24) @ 
% 0.45/0.67             (u1_struct_0 @ (k8_tmap_1 @ X24 @ X25))))),
% 0.45/0.67      inference('cnf', [status(esa)], [dt_k9_tmap_1])).
% 0.45/0.67  thf('71', plain,
% 0.45/0.67      (((v1_funct_2 @ (k9_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.45/0.67         (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))
% 0.45/0.67        | (v2_struct_0 @ sk_A)
% 0.45/0.67        | ~ (v2_pre_topc @ sk_A)
% 0.45/0.67        | ~ (l1_pre_topc @ sk_A))),
% 0.45/0.67      inference('sup-', [status(thm)], ['69', '70'])).
% 0.45/0.67  thf('72', plain,
% 0.45/0.67      (((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 0.45/0.67      inference('demod', [status(thm)], ['18', '52'])).
% 0.45/0.67  thf('73', plain, ((v2_pre_topc @ sk_A)),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('74', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('75', plain,
% 0.45/0.67      (((v1_funct_2 @ (k9_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.45/0.67         (u1_struct_0 @ sk_A))
% 0.45/0.67        | (v2_struct_0 @ sk_A))),
% 0.45/0.67      inference('demod', [status(thm)], ['71', '72', '73', '74'])).
% 0.45/0.67  thf('76', plain, (~ (v2_struct_0 @ sk_A)),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('77', plain,
% 0.45/0.67      ((v1_funct_2 @ (k9_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.45/0.67        (u1_struct_0 @ sk_A))),
% 0.45/0.67      inference('clc', [status(thm)], ['75', '76'])).
% 0.45/0.67  thf('78', plain,
% 0.45/0.67      ((((r1_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.45/0.67          (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.45/0.67          (k9_tmap_1 @ sk_A @ sk_B) @ (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 0.45/0.67         | (v2_struct_0 @ sk_A)))
% 0.45/0.67         <= (((m1_subset_1 @ (k9_tmap_1 @ sk_A @ sk_B) @ 
% 0.45/0.67               (k1_zfmisc_1 @ 
% 0.45/0.67                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.45/0.67                 (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))))))),
% 0.45/0.67      inference('demod', [status(thm)], ['68', '77'])).
% 0.45/0.67  thf('79', plain, (~ (v2_struct_0 @ sk_A)),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('80', plain,
% 0.45/0.67      (((r1_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.45/0.67         (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.45/0.67         (k9_tmap_1 @ sk_A @ sk_B) @ (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B))))
% 0.45/0.67         <= (((m1_subset_1 @ (k9_tmap_1 @ sk_A @ sk_B) @ 
% 0.45/0.67               (k1_zfmisc_1 @ 
% 0.45/0.67                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.45/0.67                 (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))))))),
% 0.45/0.67      inference('clc', [status(thm)], ['78', '79'])).
% 0.45/0.67  thf('81', plain,
% 0.45/0.67      ((v1_funct_2 @ (k9_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.45/0.67        (u1_struct_0 @ sk_A))),
% 0.45/0.67      inference('clc', [status(thm)], ['75', '76'])).
% 0.45/0.67  thf('82', plain,
% 0.45/0.67      (((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 0.45/0.67      inference('demod', [status(thm)], ['18', '52'])).
% 0.45/0.67  thf('83', plain,
% 0.45/0.67      (((m1_subset_1 @ (k9_tmap_1 @ sk_A @ sk_B) @ 
% 0.45/0.67         (k1_zfmisc_1 @ 
% 0.45/0.67          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.45/0.67           (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B))))))
% 0.45/0.67         <= (((m1_subset_1 @ (k9_tmap_1 @ sk_A @ sk_B) @ 
% 0.45/0.67               (k1_zfmisc_1 @ 
% 0.45/0.67                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.45/0.67                 (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))))))),
% 0.45/0.67      inference('split', [status(esa)], ['1'])).
% 0.45/0.67  thf(redefinition_r1_funct_2, axiom,
% 0.45/0.67    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.45/0.67     ( ( ( ~( v1_xboole_0 @ B ) ) & ( ~( v1_xboole_0 @ D ) ) & 
% 0.45/0.67         ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ A @ B ) & 
% 0.45/0.67         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.45/0.67         ( v1_funct_1 @ F ) & ( v1_funct_2 @ F @ C @ D ) & 
% 0.45/0.67         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.45/0.67       ( ( r1_funct_2 @ A @ B @ C @ D @ E @ F ) <=> ( ( E ) = ( F ) ) ) ))).
% 0.45/0.67  thf('84', plain,
% 0.45/0.67      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.45/0.67         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X4 @ X5)))
% 0.45/0.67          | ~ (v1_funct_2 @ X3 @ X4 @ X5)
% 0.45/0.67          | ~ (v1_funct_1 @ X3)
% 0.45/0.67          | (v1_xboole_0 @ X6)
% 0.45/0.67          | (v1_xboole_0 @ X5)
% 0.45/0.67          | ~ (v1_funct_1 @ X7)
% 0.45/0.67          | ~ (v1_funct_2 @ X7 @ X8 @ X6)
% 0.45/0.67          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X6)))
% 0.45/0.67          | ((X3) = (X7))
% 0.45/0.67          | ~ (r1_funct_2 @ X4 @ X5 @ X8 @ X6 @ X3 @ X7))),
% 0.45/0.67      inference('cnf', [status(esa)], [redefinition_r1_funct_2])).
% 0.45/0.67  thf('85', plain,
% 0.45/0.67      ((![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.67          (~ (r1_funct_2 @ (u1_struct_0 @ sk_A) @ 
% 0.45/0.67              (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)) @ X2 @ X1 @ 
% 0.45/0.67              (k9_tmap_1 @ sk_A @ sk_B) @ X0)
% 0.45/0.67           | ((k9_tmap_1 @ sk_A @ sk_B) = (X0))
% 0.45/0.67           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.45/0.67           | ~ (v1_funct_2 @ X0 @ X2 @ X1)
% 0.45/0.67           | ~ (v1_funct_1 @ X0)
% 0.45/0.67           | (v1_xboole_0 @ (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))
% 0.45/0.67           | (v1_xboole_0 @ X1)
% 0.45/0.67           | ~ (v1_funct_1 @ (k9_tmap_1 @ sk_A @ sk_B))
% 0.45/0.67           | ~ (v1_funct_2 @ (k9_tmap_1 @ sk_A @ sk_B) @ 
% 0.45/0.67                (u1_struct_0 @ sk_A) @ 
% 0.45/0.67                (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))))
% 0.45/0.67         <= (((m1_subset_1 @ (k9_tmap_1 @ sk_A @ sk_B) @ 
% 0.45/0.67               (k1_zfmisc_1 @ 
% 0.45/0.67                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.45/0.67                 (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))))))),
% 0.45/0.67      inference('sup-', [status(thm)], ['83', '84'])).
% 0.45/0.67  thf('86', plain, ((v1_funct_1 @ (k9_tmap_1 @ sk_A @ sk_B))),
% 0.45/0.67      inference('clc', [status(thm)], ['63', '64'])).
% 0.45/0.67  thf('87', plain,
% 0.45/0.67      ((![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.67          (~ (r1_funct_2 @ (u1_struct_0 @ sk_A) @ 
% 0.45/0.67              (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)) @ X2 @ X1 @ 
% 0.45/0.67              (k9_tmap_1 @ sk_A @ sk_B) @ X0)
% 0.45/0.67           | ((k9_tmap_1 @ sk_A @ sk_B) = (X0))
% 0.45/0.67           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.45/0.67           | ~ (v1_funct_2 @ X0 @ X2 @ X1)
% 0.45/0.67           | ~ (v1_funct_1 @ X0)
% 0.45/0.67           | (v1_xboole_0 @ (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))
% 0.45/0.67           | (v1_xboole_0 @ X1)
% 0.45/0.67           | ~ (v1_funct_2 @ (k9_tmap_1 @ sk_A @ sk_B) @ 
% 0.45/0.67                (u1_struct_0 @ sk_A) @ 
% 0.45/0.67                (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))))
% 0.45/0.67         <= (((m1_subset_1 @ (k9_tmap_1 @ sk_A @ sk_B) @ 
% 0.45/0.67               (k1_zfmisc_1 @ 
% 0.45/0.67                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.45/0.67                 (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))))))),
% 0.45/0.67      inference('demod', [status(thm)], ['85', '86'])).
% 0.45/0.67  thf('88', plain,
% 0.45/0.67      ((![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.67          (~ (v1_funct_2 @ (k9_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.45/0.67              (u1_struct_0 @ sk_A))
% 0.45/0.67           | (v1_xboole_0 @ X0)
% 0.45/0.67           | (v1_xboole_0 @ (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))
% 0.45/0.67           | ~ (v1_funct_1 @ X1)
% 0.45/0.67           | ~ (v1_funct_2 @ X1 @ X2 @ X0)
% 0.45/0.67           | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 0.45/0.67           | ((k9_tmap_1 @ sk_A @ sk_B) = (X1))
% 0.45/0.67           | ~ (r1_funct_2 @ (u1_struct_0 @ sk_A) @ 
% 0.45/0.67                (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)) @ X2 @ X0 @ 
% 0.45/0.67                (k9_tmap_1 @ sk_A @ sk_B) @ X1)))
% 0.45/0.67         <= (((m1_subset_1 @ (k9_tmap_1 @ sk_A @ sk_B) @ 
% 0.45/0.67               (k1_zfmisc_1 @ 
% 0.45/0.67                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.45/0.67                 (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))))))),
% 0.45/0.67      inference('sup-', [status(thm)], ['82', '87'])).
% 0.45/0.67  thf('89', plain,
% 0.45/0.67      (((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 0.45/0.67      inference('demod', [status(thm)], ['18', '52'])).
% 0.45/0.67  thf('90', plain,
% 0.45/0.67      (((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 0.45/0.67      inference('demod', [status(thm)], ['18', '52'])).
% 0.45/0.67  thf('91', plain,
% 0.45/0.67      ((![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.67          (~ (v1_funct_2 @ (k9_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.45/0.67              (u1_struct_0 @ sk_A))
% 0.45/0.67           | (v1_xboole_0 @ X0)
% 0.45/0.67           | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.45/0.67           | ~ (v1_funct_1 @ X1)
% 0.45/0.67           | ~ (v1_funct_2 @ X1 @ X2 @ X0)
% 0.45/0.67           | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 0.45/0.67           | ((k9_tmap_1 @ sk_A @ sk_B) = (X1))
% 0.45/0.67           | ~ (r1_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.45/0.67                X2 @ X0 @ (k9_tmap_1 @ sk_A @ sk_B) @ X1)))
% 0.45/0.67         <= (((m1_subset_1 @ (k9_tmap_1 @ sk_A @ sk_B) @ 
% 0.45/0.67               (k1_zfmisc_1 @ 
% 0.45/0.67                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.45/0.67                 (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))))))),
% 0.45/0.67      inference('demod', [status(thm)], ['88', '89', '90'])).
% 0.45/0.67  thf('92', plain,
% 0.45/0.67      ((![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.67          (~ (r1_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ X2 @ 
% 0.45/0.67              X1 @ (k9_tmap_1 @ sk_A @ sk_B) @ X0)
% 0.45/0.67           | ((k9_tmap_1 @ sk_A @ sk_B) = (X0))
% 0.45/0.67           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.45/0.67           | ~ (v1_funct_2 @ X0 @ X2 @ X1)
% 0.45/0.67           | ~ (v1_funct_1 @ X0)
% 0.45/0.67           | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.45/0.67           | (v1_xboole_0 @ X1)))
% 0.45/0.67         <= (((m1_subset_1 @ (k9_tmap_1 @ sk_A @ sk_B) @ 
% 0.45/0.67               (k1_zfmisc_1 @ 
% 0.45/0.67                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.45/0.67                 (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))))))),
% 0.45/0.67      inference('sup-', [status(thm)], ['81', '91'])).
% 0.45/0.67  thf('93', plain,
% 0.45/0.67      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.45/0.67         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.45/0.67         | ~ (v1_funct_1 @ (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 0.45/0.67         | ~ (v1_funct_2 @ (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)) @ 
% 0.45/0.67              (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.45/0.67         | ~ (m1_subset_1 @ (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)) @ 
% 0.45/0.67              (k1_zfmisc_1 @ 
% 0.45/0.67               (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))))
% 0.45/0.67         | ((k9_tmap_1 @ sk_A @ sk_B)
% 0.45/0.67             = (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))))
% 0.45/0.67         <= (((m1_subset_1 @ (k9_tmap_1 @ sk_A @ sk_B) @ 
% 0.45/0.67               (k1_zfmisc_1 @ 
% 0.45/0.67                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.45/0.67                 (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))))))),
% 0.45/0.67      inference('sup-', [status(thm)], ['80', '92'])).
% 0.45/0.67  thf('94', plain,
% 0.45/0.67      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.45/0.67        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.67      inference('demod', [status(thm)], ['9', '10'])).
% 0.45/0.67  thf(dt_k7_tmap_1, axiom,
% 0.45/0.67    (![A:$i,B:$i]:
% 0.45/0.67     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.45/0.67         ( l1_pre_topc @ A ) & 
% 0.45/0.67         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.45/0.67       ( ( v1_funct_1 @ ( k7_tmap_1 @ A @ B ) ) & 
% 0.45/0.67         ( v1_funct_2 @
% 0.45/0.67           ( k7_tmap_1 @ A @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.45/0.67           ( u1_struct_0 @ ( k6_tmap_1 @ A @ B ) ) ) & 
% 0.45/0.67         ( m1_subset_1 @
% 0.45/0.67           ( k7_tmap_1 @ A @ B ) @ 
% 0.45/0.67           ( k1_zfmisc_1 @
% 0.45/0.67             ( k2_zfmisc_1 @
% 0.45/0.67               ( u1_struct_0 @ A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ A @ B ) ) ) ) ) ) ))).
% 0.45/0.67  thf('95', plain,
% 0.45/0.67      (![X20 : $i, X21 : $i]:
% 0.45/0.67         (~ (l1_pre_topc @ X20)
% 0.45/0.67          | ~ (v2_pre_topc @ X20)
% 0.45/0.67          | (v2_struct_0 @ X20)
% 0.45/0.67          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.45/0.67          | (v1_funct_1 @ (k7_tmap_1 @ X20 @ X21)))),
% 0.45/0.67      inference('cnf', [status(esa)], [dt_k7_tmap_1])).
% 0.45/0.67  thf('96', plain,
% 0.45/0.67      (((v1_funct_1 @ (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 0.45/0.67        | (v2_struct_0 @ sk_A)
% 0.45/0.67        | ~ (v2_pre_topc @ sk_A)
% 0.45/0.67        | ~ (l1_pre_topc @ sk_A))),
% 0.45/0.67      inference('sup-', [status(thm)], ['94', '95'])).
% 0.45/0.67  thf('97', plain, ((v2_pre_topc @ sk_A)),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('98', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('99', plain,
% 0.45/0.67      (((v1_funct_1 @ (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 0.45/0.67        | (v2_struct_0 @ sk_A))),
% 0.45/0.67      inference('demod', [status(thm)], ['96', '97', '98'])).
% 0.45/0.67  thf('100', plain, (~ (v2_struct_0 @ sk_A)),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('101', plain, ((v1_funct_1 @ (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))),
% 0.45/0.67      inference('clc', [status(thm)], ['99', '100'])).
% 0.45/0.67  thf('102', plain,
% 0.45/0.67      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.45/0.67        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.67      inference('demod', [status(thm)], ['9', '10'])).
% 0.45/0.67  thf('103', plain,
% 0.45/0.67      (![X20 : $i, X21 : $i]:
% 0.45/0.67         (~ (l1_pre_topc @ X20)
% 0.45/0.67          | ~ (v2_pre_topc @ X20)
% 0.45/0.67          | (v2_struct_0 @ X20)
% 0.45/0.67          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.45/0.67          | (m1_subset_1 @ (k7_tmap_1 @ X20 @ X21) @ 
% 0.45/0.67             (k1_zfmisc_1 @ 
% 0.45/0.67              (k2_zfmisc_1 @ (u1_struct_0 @ X20) @ 
% 0.45/0.67               (u1_struct_0 @ (k6_tmap_1 @ X20 @ X21))))))),
% 0.45/0.67      inference('cnf', [status(esa)], [dt_k7_tmap_1])).
% 0.45/0.67  thf('104', plain,
% 0.45/0.67      (((m1_subset_1 @ (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)) @ 
% 0.45/0.67         (k1_zfmisc_1 @ 
% 0.45/0.67          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.45/0.67           (u1_struct_0 @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B))))))
% 0.45/0.67        | (v2_struct_0 @ sk_A)
% 0.45/0.67        | ~ (v2_pre_topc @ sk_A)
% 0.45/0.67        | ~ (l1_pre_topc @ sk_A))),
% 0.45/0.67      inference('sup-', [status(thm)], ['102', '103'])).
% 0.45/0.67  thf('105', plain,
% 0.45/0.67      (((k8_tmap_1 @ sk_A @ sk_B) = (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))),
% 0.45/0.67      inference('clc', [status(thm)], ['50', '51'])).
% 0.45/0.67  thf('106', plain,
% 0.45/0.67      (((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 0.45/0.67      inference('demod', [status(thm)], ['18', '52'])).
% 0.45/0.67  thf('107', plain, ((v2_pre_topc @ sk_A)),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('108', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('109', plain,
% 0.45/0.67      (((m1_subset_1 @ (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)) @ 
% 0.45/0.67         (k1_zfmisc_1 @ 
% 0.45/0.67          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))))
% 0.45/0.67        | (v2_struct_0 @ sk_A))),
% 0.45/0.67      inference('demod', [status(thm)], ['104', '105', '106', '107', '108'])).
% 0.45/0.67  thf('110', plain, (~ (v2_struct_0 @ sk_A)),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('111', plain,
% 0.45/0.67      ((m1_subset_1 @ (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)) @ 
% 0.45/0.67        (k1_zfmisc_1 @ 
% 0.45/0.67         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))))),
% 0.45/0.67      inference('clc', [status(thm)], ['109', '110'])).
% 0.45/0.67  thf('112', plain,
% 0.45/0.67      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.45/0.67         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.45/0.67         | ~ (v1_funct_2 @ (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)) @ 
% 0.45/0.67              (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.45/0.67         | ((k9_tmap_1 @ sk_A @ sk_B)
% 0.45/0.67             = (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))))
% 0.45/0.67         <= (((m1_subset_1 @ (k9_tmap_1 @ sk_A @ sk_B) @ 
% 0.45/0.67               (k1_zfmisc_1 @ 
% 0.45/0.67                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.45/0.67                 (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))))))),
% 0.45/0.67      inference('demod', [status(thm)], ['93', '101', '111'])).
% 0.45/0.67  thf('113', plain,
% 0.45/0.67      (((((k9_tmap_1 @ sk_A @ sk_B) = (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 0.45/0.67         | ~ (v1_funct_2 @ (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)) @ 
% 0.45/0.67              (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.45/0.67         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.45/0.67         <= (((m1_subset_1 @ (k9_tmap_1 @ sk_A @ sk_B) @ 
% 0.45/0.67               (k1_zfmisc_1 @ 
% 0.45/0.67                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.45/0.67                 (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))))))),
% 0.45/0.67      inference('simplify', [status(thm)], ['112'])).
% 0.45/0.67  thf('114', plain,
% 0.45/0.67      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.45/0.67        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.67      inference('demod', [status(thm)], ['9', '10'])).
% 0.45/0.67  thf('115', plain,
% 0.45/0.67      (![X20 : $i, X21 : $i]:
% 0.45/0.67         (~ (l1_pre_topc @ X20)
% 0.45/0.67          | ~ (v2_pre_topc @ X20)
% 0.45/0.67          | (v2_struct_0 @ X20)
% 0.45/0.67          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.45/0.67          | (v1_funct_2 @ (k7_tmap_1 @ X20 @ X21) @ (u1_struct_0 @ X20) @ 
% 0.45/0.67             (u1_struct_0 @ (k6_tmap_1 @ X20 @ X21))))),
% 0.45/0.67      inference('cnf', [status(esa)], [dt_k7_tmap_1])).
% 0.45/0.67  thf('116', plain,
% 0.45/0.67      (((v1_funct_2 @ (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)) @ 
% 0.45/0.67         (u1_struct_0 @ sk_A) @ 
% 0.45/0.67         (u1_struct_0 @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B))))
% 0.45/0.67        | (v2_struct_0 @ sk_A)
% 0.45/0.67        | ~ (v2_pre_topc @ sk_A)
% 0.45/0.67        | ~ (l1_pre_topc @ sk_A))),
% 0.45/0.67      inference('sup-', [status(thm)], ['114', '115'])).
% 0.45/0.67  thf('117', plain,
% 0.45/0.67      (((k8_tmap_1 @ sk_A @ sk_B) = (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))),
% 0.45/0.67      inference('clc', [status(thm)], ['50', '51'])).
% 0.45/0.67  thf('118', plain,
% 0.45/0.67      (((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 0.45/0.67      inference('demod', [status(thm)], ['18', '52'])).
% 0.45/0.67  thf('119', plain, ((v2_pre_topc @ sk_A)),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('120', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('121', plain,
% 0.45/0.67      (((v1_funct_2 @ (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)) @ 
% 0.45/0.67         (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.45/0.67        | (v2_struct_0 @ sk_A))),
% 0.45/0.67      inference('demod', [status(thm)], ['116', '117', '118', '119', '120'])).
% 0.45/0.67  thf('122', plain, (~ (v2_struct_0 @ sk_A)),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('123', plain,
% 0.45/0.67      ((v1_funct_2 @ (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)) @ 
% 0.45/0.67        (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))),
% 0.45/0.67      inference('clc', [status(thm)], ['121', '122'])).
% 0.45/0.67  thf('124', plain,
% 0.45/0.67      (((((k9_tmap_1 @ sk_A @ sk_B) = (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 0.45/0.67         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.45/0.67         <= (((m1_subset_1 @ (k9_tmap_1 @ sk_A @ sk_B) @ 
% 0.45/0.67               (k1_zfmisc_1 @ 
% 0.45/0.67                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.45/0.67                 (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))))))),
% 0.45/0.67      inference('demod', [status(thm)], ['113', '123'])).
% 0.45/0.67  thf('125', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('126', plain,
% 0.45/0.67      (![X24 : $i, X25 : $i]:
% 0.45/0.67         (~ (l1_pre_topc @ X24)
% 0.45/0.67          | ~ (v2_pre_topc @ X24)
% 0.45/0.67          | (v2_struct_0 @ X24)
% 0.45/0.67          | ~ (m1_pre_topc @ X25 @ X24)
% 0.45/0.67          | (m1_subset_1 @ (k9_tmap_1 @ X24 @ X25) @ 
% 0.45/0.67             (k1_zfmisc_1 @ 
% 0.45/0.67              (k2_zfmisc_1 @ (u1_struct_0 @ X24) @ 
% 0.45/0.67               (u1_struct_0 @ (k8_tmap_1 @ X24 @ X25))))))),
% 0.45/0.67      inference('cnf', [status(esa)], [dt_k9_tmap_1])).
% 0.45/0.67  thf('127', plain,
% 0.45/0.67      (((m1_subset_1 @ (k9_tmap_1 @ sk_A @ sk_B) @ 
% 0.45/0.67         (k1_zfmisc_1 @ 
% 0.45/0.67          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.45/0.67           (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))))
% 0.45/0.67        | (v2_struct_0 @ sk_A)
% 0.45/0.67        | ~ (v2_pre_topc @ sk_A)
% 0.45/0.67        | ~ (l1_pre_topc @ sk_A))),
% 0.45/0.67      inference('sup-', [status(thm)], ['125', '126'])).
% 0.45/0.67  thf('128', plain,
% 0.45/0.67      (((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 0.45/0.67      inference('demod', [status(thm)], ['18', '52'])).
% 0.45/0.67  thf('129', plain, ((v2_pre_topc @ sk_A)),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('130', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('131', plain,
% 0.45/0.67      (((m1_subset_1 @ (k9_tmap_1 @ sk_A @ sk_B) @ 
% 0.45/0.67         (k1_zfmisc_1 @ 
% 0.45/0.67          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))))
% 0.45/0.67        | (v2_struct_0 @ sk_A))),
% 0.45/0.67      inference('demod', [status(thm)], ['127', '128', '129', '130'])).
% 0.45/0.67  thf('132', plain, (~ (v2_struct_0 @ sk_A)),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('133', plain,
% 0.45/0.67      ((m1_subset_1 @ (k9_tmap_1 @ sk_A @ sk_B) @ 
% 0.45/0.67        (k1_zfmisc_1 @ 
% 0.45/0.67         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))))),
% 0.45/0.67      inference('clc', [status(thm)], ['131', '132'])).
% 0.45/0.67  thf('134', plain,
% 0.45/0.67      (((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 0.45/0.67      inference('demod', [status(thm)], ['18', '52'])).
% 0.45/0.67  thf('135', plain,
% 0.45/0.67      ((~ (m1_subset_1 @ (k9_tmap_1 @ sk_A @ sk_B) @ 
% 0.45/0.67           (k1_zfmisc_1 @ 
% 0.45/0.67            (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.45/0.67             (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))))
% 0.45/0.67        | ~ (v5_pre_topc @ (k9_tmap_1 @ sk_A @ sk_B) @ sk_A @ 
% 0.45/0.67             (k8_tmap_1 @ sk_A @ sk_B))
% 0.45/0.67        | ~ (v1_funct_2 @ (k9_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.45/0.67             (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))
% 0.45/0.67        | ~ (v1_funct_1 @ (k9_tmap_1 @ sk_A @ sk_B))
% 0.45/0.67        | ~ (m1_pre_topc @ sk_B @ sk_A)
% 0.45/0.67        | ~ (v1_tsep_1 @ sk_B @ sk_A))),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('136', plain,
% 0.45/0.67      ((~ (m1_subset_1 @ (k9_tmap_1 @ sk_A @ sk_B) @ 
% 0.45/0.67           (k1_zfmisc_1 @ 
% 0.45/0.67            (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.45/0.67             (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B))))))
% 0.45/0.67         <= (~
% 0.45/0.67             ((m1_subset_1 @ (k9_tmap_1 @ sk_A @ sk_B) @ 
% 0.45/0.67               (k1_zfmisc_1 @ 
% 0.45/0.67                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.45/0.67                 (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))))))),
% 0.45/0.67      inference('split', [status(esa)], ['135'])).
% 0.45/0.67  thf('137', plain,
% 0.45/0.67      ((~ (m1_subset_1 @ (k9_tmap_1 @ sk_A @ sk_B) @ 
% 0.45/0.67           (k1_zfmisc_1 @ 
% 0.45/0.67            (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A)))))
% 0.45/0.67         <= (~
% 0.45/0.67             ((m1_subset_1 @ (k9_tmap_1 @ sk_A @ sk_B) @ 
% 0.45/0.67               (k1_zfmisc_1 @ 
% 0.45/0.67                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.45/0.67                 (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))))))),
% 0.45/0.67      inference('sup-', [status(thm)], ['134', '136'])).
% 0.45/0.67  thf('138', plain,
% 0.45/0.67      (((m1_subset_1 @ (k9_tmap_1 @ sk_A @ sk_B) @ 
% 0.45/0.67         (k1_zfmisc_1 @ 
% 0.45/0.67          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.45/0.67           (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B))))))),
% 0.45/0.67      inference('sup-', [status(thm)], ['133', '137'])).
% 0.45/0.67  thf('139', plain,
% 0.45/0.67      (((m1_subset_1 @ (k9_tmap_1 @ sk_A @ sk_B) @ 
% 0.45/0.67         (k1_zfmisc_1 @ 
% 0.45/0.67          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.45/0.67           (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B))))))),
% 0.45/0.67      inference('sat_resolution*', [status(thm)], ['138'])).
% 0.45/0.67  thf('140', plain,
% 0.45/0.67      ((((k9_tmap_1 @ sk_A @ sk_B) = (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 0.45/0.67        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.67      inference('simpl_trail', [status(thm)], ['124', '139'])).
% 0.45/0.67  thf('141', plain,
% 0.45/0.67      (((k8_tmap_1 @ sk_A @ sk_B) = (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))),
% 0.45/0.67      inference('clc', [status(thm)], ['50', '51'])).
% 0.45/0.67  thf(t113_tmap_1, axiom,
% 0.45/0.67    (![A:$i]:
% 0.45/0.67     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.45/0.67       ( ![B:$i]:
% 0.45/0.67         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.45/0.67           ( ( v3_pre_topc @ B @ A ) <=>
% 0.45/0.67             ( ( v1_funct_1 @ ( k7_tmap_1 @ A @ B ) ) & 
% 0.45/0.67               ( v1_funct_2 @
% 0.45/0.67                 ( k7_tmap_1 @ A @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.45/0.67                 ( u1_struct_0 @ ( k6_tmap_1 @ A @ B ) ) ) & 
% 0.45/0.67               ( v5_pre_topc @
% 0.45/0.67                 ( k7_tmap_1 @ A @ B ) @ A @ ( k6_tmap_1 @ A @ B ) ) & 
% 0.45/0.67               ( m1_subset_1 @
% 0.45/0.67                 ( k7_tmap_1 @ A @ B ) @ 
% 0.45/0.67                 ( k1_zfmisc_1 @
% 0.45/0.67                   ( k2_zfmisc_1 @
% 0.45/0.67                     ( u1_struct_0 @ A ) @ 
% 0.45/0.67                     ( u1_struct_0 @ ( k6_tmap_1 @ A @ B ) ) ) ) ) ) ) ) ) ))).
% 0.45/0.67  thf('142', plain,
% 0.45/0.67      (![X28 : $i, X29 : $i]:
% 0.45/0.67         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (u1_struct_0 @ X29)))
% 0.45/0.67          | ~ (v1_funct_1 @ (k7_tmap_1 @ X29 @ X28))
% 0.45/0.67          | ~ (v1_funct_2 @ (k7_tmap_1 @ X29 @ X28) @ (u1_struct_0 @ X29) @ 
% 0.45/0.67               (u1_struct_0 @ (k6_tmap_1 @ X29 @ X28)))
% 0.45/0.67          | ~ (v5_pre_topc @ (k7_tmap_1 @ X29 @ X28) @ X29 @ 
% 0.45/0.67               (k6_tmap_1 @ X29 @ X28))
% 0.45/0.67          | ~ (m1_subset_1 @ (k7_tmap_1 @ X29 @ X28) @ 
% 0.45/0.67               (k1_zfmisc_1 @ 
% 0.45/0.67                (k2_zfmisc_1 @ (u1_struct_0 @ X29) @ 
% 0.45/0.67                 (u1_struct_0 @ (k6_tmap_1 @ X29 @ X28)))))
% 0.45/0.67          | (v3_pre_topc @ X28 @ X29)
% 0.45/0.67          | ~ (l1_pre_topc @ X29)
% 0.45/0.67          | ~ (v2_pre_topc @ X29)
% 0.45/0.67          | (v2_struct_0 @ X29))),
% 0.45/0.67      inference('cnf', [status(esa)], [t113_tmap_1])).
% 0.45/0.67  thf('143', plain,
% 0.45/0.67      ((~ (m1_subset_1 @ (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)) @ 
% 0.45/0.67           (k1_zfmisc_1 @ 
% 0.45/0.67            (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.45/0.67             (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))))
% 0.45/0.67        | (v2_struct_0 @ sk_A)
% 0.45/0.67        | ~ (v2_pre_topc @ sk_A)
% 0.45/0.67        | ~ (l1_pre_topc @ sk_A)
% 0.45/0.67        | (v3_pre_topc @ (u1_struct_0 @ sk_B) @ sk_A)
% 0.45/0.67        | ~ (v5_pre_topc @ (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)) @ sk_A @ 
% 0.45/0.67             (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 0.45/0.67        | ~ (v1_funct_2 @ (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)) @ 
% 0.45/0.67             (u1_struct_0 @ sk_A) @ 
% 0.45/0.67             (u1_struct_0 @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B))))
% 0.45/0.67        | ~ (v1_funct_1 @ (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 0.45/0.67        | ~ (m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.45/0.67             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.45/0.67      inference('sup-', [status(thm)], ['141', '142'])).
% 0.45/0.67  thf('144', plain,
% 0.45/0.67      (((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 0.45/0.67      inference('demod', [status(thm)], ['18', '52'])).
% 0.45/0.67  thf('145', plain,
% 0.45/0.67      ((m1_subset_1 @ (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)) @ 
% 0.45/0.67        (k1_zfmisc_1 @ 
% 0.45/0.67         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))))),
% 0.45/0.67      inference('clc', [status(thm)], ['109', '110'])).
% 0.45/0.67  thf('146', plain, ((v2_pre_topc @ sk_A)),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('147', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('148', plain,
% 0.45/0.67      (((k8_tmap_1 @ sk_A @ sk_B) = (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))),
% 0.45/0.67      inference('clc', [status(thm)], ['50', '51'])).
% 0.45/0.67  thf('149', plain,
% 0.45/0.67      (((k8_tmap_1 @ sk_A @ sk_B) = (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))),
% 0.45/0.67      inference('clc', [status(thm)], ['50', '51'])).
% 0.45/0.67  thf('150', plain,
% 0.45/0.67      (((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 0.45/0.67      inference('demod', [status(thm)], ['18', '52'])).
% 0.45/0.67  thf('151', plain,
% 0.45/0.67      ((v1_funct_2 @ (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)) @ 
% 0.45/0.67        (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))),
% 0.45/0.67      inference('clc', [status(thm)], ['121', '122'])).
% 0.45/0.67  thf('152', plain, ((v1_funct_1 @ (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))),
% 0.45/0.67      inference('clc', [status(thm)], ['99', '100'])).
% 0.45/0.67  thf('153', plain,
% 0.45/0.67      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.45/0.67        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.67      inference('demod', [status(thm)], ['9', '10'])).
% 0.45/0.67  thf('154', plain,
% 0.45/0.67      (((v2_struct_0 @ sk_A)
% 0.45/0.67        | (v3_pre_topc @ (u1_struct_0 @ sk_B) @ sk_A)
% 0.45/0.67        | ~ (v5_pre_topc @ (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)) @ sk_A @ 
% 0.45/0.67             (k8_tmap_1 @ sk_A @ sk_B)))),
% 0.45/0.67      inference('demod', [status(thm)],
% 0.45/0.67                ['143', '144', '145', '146', '147', '148', '149', '150', 
% 0.45/0.67                 '151', '152', '153'])).
% 0.45/0.67  thf('155', plain, (~ (v2_struct_0 @ sk_A)),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('156', plain,
% 0.45/0.67      ((~ (v5_pre_topc @ (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)) @ sk_A @ 
% 0.45/0.67           (k8_tmap_1 @ sk_A @ sk_B))
% 0.45/0.67        | (v3_pre_topc @ (u1_struct_0 @ sk_B) @ sk_A))),
% 0.45/0.67      inference('clc', [status(thm)], ['154', '155'])).
% 0.45/0.67  thf('157', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf(d1_tsep_1, axiom,
% 0.45/0.67    (![A:$i]:
% 0.45/0.67     ( ( l1_pre_topc @ A ) =>
% 0.45/0.67       ( ![B:$i]:
% 0.45/0.67         ( ( m1_pre_topc @ B @ A ) =>
% 0.45/0.67           ( ( v1_tsep_1 @ B @ A ) <=>
% 0.45/0.67             ( ![C:$i]:
% 0.45/0.67               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.45/0.67                 ( ( ( C ) = ( u1_struct_0 @ B ) ) => ( v3_pre_topc @ C @ A ) ) ) ) ) ) ) ))).
% 0.45/0.67  thf('158', plain,
% 0.45/0.67      (![X17 : $i, X18 : $i]:
% 0.45/0.67         (~ (m1_pre_topc @ X17 @ X18)
% 0.45/0.67          | ((sk_C @ X17 @ X18) = (u1_struct_0 @ X17))
% 0.45/0.67          | (v1_tsep_1 @ X17 @ X18)
% 0.45/0.67          | ~ (l1_pre_topc @ X18))),
% 0.45/0.67      inference('cnf', [status(esa)], [d1_tsep_1])).
% 0.45/0.67  thf('159', plain,
% 0.45/0.67      ((~ (l1_pre_topc @ sk_A)
% 0.45/0.67        | (v1_tsep_1 @ sk_B @ sk_A)
% 0.45/0.67        | ((sk_C @ sk_B @ sk_A) = (u1_struct_0 @ sk_B)))),
% 0.45/0.67      inference('sup-', [status(thm)], ['157', '158'])).
% 0.45/0.67  thf('160', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('161', plain,
% 0.45/0.67      (((v1_tsep_1 @ sk_B @ sk_A)
% 0.45/0.67        | ((sk_C @ sk_B @ sk_A) = (u1_struct_0 @ sk_B)))),
% 0.45/0.67      inference('demod', [status(thm)], ['159', '160'])).
% 0.45/0.67  thf('162', plain,
% 0.45/0.67      ((~ (v1_tsep_1 @ sk_B @ sk_A)) <= (~ ((v1_tsep_1 @ sk_B @ sk_A)))),
% 0.45/0.67      inference('split', [status(esa)], ['135'])).
% 0.45/0.67  thf('163', plain,
% 0.45/0.67      ((((sk_C @ sk_B @ sk_A) = (u1_struct_0 @ sk_B)))
% 0.45/0.67         <= (~ ((v1_tsep_1 @ sk_B @ sk_A)))),
% 0.45/0.67      inference('sup-', [status(thm)], ['161', '162'])).
% 0.45/0.67  thf('164', plain,
% 0.45/0.67      (![X17 : $i, X18 : $i]:
% 0.45/0.67         (~ (m1_pre_topc @ X17 @ X18)
% 0.45/0.67          | ~ (v3_pre_topc @ (sk_C @ X17 @ X18) @ X18)
% 0.45/0.67          | (v1_tsep_1 @ X17 @ X18)
% 0.45/0.67          | ~ (l1_pre_topc @ X18))),
% 0.45/0.67      inference('cnf', [status(esa)], [d1_tsep_1])).
% 0.45/0.67  thf('165', plain,
% 0.45/0.67      (((~ (v3_pre_topc @ (u1_struct_0 @ sk_B) @ sk_A)
% 0.45/0.67         | ~ (l1_pre_topc @ sk_A)
% 0.45/0.67         | (v1_tsep_1 @ sk_B @ sk_A)
% 0.45/0.67         | ~ (m1_pre_topc @ sk_B @ sk_A))) <= (~ ((v1_tsep_1 @ sk_B @ sk_A)))),
% 0.45/0.67      inference('sup-', [status(thm)], ['163', '164'])).
% 0.45/0.67  thf('166', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('167', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('168', plain,
% 0.45/0.67      (((~ (v3_pre_topc @ (u1_struct_0 @ sk_B) @ sk_A)
% 0.45/0.67         | (v1_tsep_1 @ sk_B @ sk_A))) <= (~ ((v1_tsep_1 @ sk_B @ sk_A)))),
% 0.45/0.67      inference('demod', [status(thm)], ['165', '166', '167'])).
% 0.45/0.67  thf('169', plain,
% 0.45/0.67      ((~ (v1_tsep_1 @ sk_B @ sk_A)) <= (~ ((v1_tsep_1 @ sk_B @ sk_A)))),
% 0.45/0.67      inference('split', [status(esa)], ['135'])).
% 0.45/0.67  thf('170', plain,
% 0.45/0.67      ((~ (v3_pre_topc @ (u1_struct_0 @ sk_B) @ sk_A))
% 0.45/0.67         <= (~ ((v1_tsep_1 @ sk_B @ sk_A)))),
% 0.45/0.67      inference('clc', [status(thm)], ['168', '169'])).
% 0.45/0.67  thf('171', plain,
% 0.45/0.67      ((((k9_tmap_1 @ sk_A @ sk_B) = (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 0.45/0.67        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.67      inference('simpl_trail', [status(thm)], ['124', '139'])).
% 0.45/0.67  thf('172', plain,
% 0.45/0.67      (((v1_funct_1 @ (k9_tmap_1 @ sk_A @ sk_B)) | (v1_tsep_1 @ sk_B @ sk_A))),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('173', plain,
% 0.45/0.67      (((v1_tsep_1 @ sk_B @ sk_A)) <= (((v1_tsep_1 @ sk_B @ sk_A)))),
% 0.45/0.67      inference('split', [status(esa)], ['172'])).
% 0.45/0.67  thf('174', plain,
% 0.45/0.67      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.45/0.67        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.67      inference('demod', [status(thm)], ['9', '10'])).
% 0.45/0.67  thf('175', plain,
% 0.45/0.67      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.45/0.67         (~ (m1_pre_topc @ X17 @ X18)
% 0.45/0.67          | ~ (v1_tsep_1 @ X17 @ X18)
% 0.45/0.67          | ((X19) != (u1_struct_0 @ X17))
% 0.45/0.67          | (v3_pre_topc @ X19 @ X18)
% 0.45/0.67          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.45/0.67          | ~ (l1_pre_topc @ X18))),
% 0.45/0.67      inference('cnf', [status(esa)], [d1_tsep_1])).
% 0.45/0.67  thf('176', plain,
% 0.45/0.67      (![X17 : $i, X18 : $i]:
% 0.45/0.67         (~ (l1_pre_topc @ X18)
% 0.45/0.67          | ~ (m1_subset_1 @ (u1_struct_0 @ X17) @ 
% 0.45/0.67               (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.45/0.67          | (v3_pre_topc @ (u1_struct_0 @ X17) @ X18)
% 0.45/0.67          | ~ (v1_tsep_1 @ X17 @ X18)
% 0.45/0.67          | ~ (m1_pre_topc @ X17 @ X18))),
% 0.45/0.67      inference('simplify', [status(thm)], ['175'])).
% 0.45/0.67  thf('177', plain,
% 0.45/0.67      ((~ (m1_pre_topc @ sk_B @ sk_A)
% 0.45/0.67        | ~ (v1_tsep_1 @ sk_B @ sk_A)
% 0.45/0.67        | (v3_pre_topc @ (u1_struct_0 @ sk_B) @ sk_A)
% 0.45/0.67        | ~ (l1_pre_topc @ sk_A))),
% 0.45/0.67      inference('sup-', [status(thm)], ['174', '176'])).
% 0.45/0.67  thf('178', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('179', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('180', plain,
% 0.45/0.67      ((~ (v1_tsep_1 @ sk_B @ sk_A)
% 0.45/0.67        | (v3_pre_topc @ (u1_struct_0 @ sk_B) @ sk_A))),
% 0.45/0.67      inference('demod', [status(thm)], ['177', '178', '179'])).
% 0.45/0.67  thf('181', plain,
% 0.45/0.67      (((v3_pre_topc @ (u1_struct_0 @ sk_B) @ sk_A))
% 0.45/0.67         <= (((v1_tsep_1 @ sk_B @ sk_A)))),
% 0.45/0.67      inference('sup-', [status(thm)], ['173', '180'])).
% 0.45/0.67  thf('182', plain,
% 0.45/0.67      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.45/0.67        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.67      inference('demod', [status(thm)], ['9', '10'])).
% 0.45/0.67  thf('183', plain,
% 0.45/0.67      (![X28 : $i, X29 : $i]:
% 0.45/0.67         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (u1_struct_0 @ X29)))
% 0.45/0.67          | ~ (v3_pre_topc @ X28 @ X29)
% 0.45/0.67          | (v5_pre_topc @ (k7_tmap_1 @ X29 @ X28) @ X29 @ 
% 0.45/0.67             (k6_tmap_1 @ X29 @ X28))
% 0.45/0.67          | ~ (l1_pre_topc @ X29)
% 0.45/0.67          | ~ (v2_pre_topc @ X29)
% 0.45/0.67          | (v2_struct_0 @ X29))),
% 0.45/0.67      inference('cnf', [status(esa)], [t113_tmap_1])).
% 0.45/0.67  thf('184', plain,
% 0.45/0.67      (((v2_struct_0 @ sk_A)
% 0.45/0.67        | ~ (v2_pre_topc @ sk_A)
% 0.45/0.67        | ~ (l1_pre_topc @ sk_A)
% 0.45/0.67        | (v5_pre_topc @ (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)) @ sk_A @ 
% 0.45/0.67           (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 0.45/0.67        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_B) @ sk_A))),
% 0.45/0.67      inference('sup-', [status(thm)], ['182', '183'])).
% 0.45/0.67  thf('185', plain, ((v2_pre_topc @ sk_A)),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('186', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('187', plain,
% 0.45/0.67      (((k8_tmap_1 @ sk_A @ sk_B) = (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))),
% 0.45/0.67      inference('clc', [status(thm)], ['50', '51'])).
% 0.45/0.67  thf('188', plain,
% 0.45/0.67      (((v2_struct_0 @ sk_A)
% 0.45/0.67        | (v5_pre_topc @ (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)) @ sk_A @ 
% 0.45/0.67           (k8_tmap_1 @ sk_A @ sk_B))
% 0.45/0.67        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_B) @ sk_A))),
% 0.45/0.67      inference('demod', [status(thm)], ['184', '185', '186', '187'])).
% 0.45/0.67  thf('189', plain, (~ (v2_struct_0 @ sk_A)),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('190', plain,
% 0.45/0.67      ((~ (v3_pre_topc @ (u1_struct_0 @ sk_B) @ sk_A)
% 0.45/0.67        | (v5_pre_topc @ (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)) @ sk_A @ 
% 0.45/0.67           (k8_tmap_1 @ sk_A @ sk_B)))),
% 0.45/0.67      inference('clc', [status(thm)], ['188', '189'])).
% 0.45/0.67  thf('191', plain,
% 0.45/0.67      (((v5_pre_topc @ (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)) @ sk_A @ 
% 0.45/0.67         (k8_tmap_1 @ sk_A @ sk_B))) <= (((v1_tsep_1 @ sk_B @ sk_A)))),
% 0.45/0.67      inference('sup-', [status(thm)], ['181', '190'])).
% 0.45/0.67  thf('192', plain,
% 0.45/0.67      ((((v5_pre_topc @ (k9_tmap_1 @ sk_A @ sk_B) @ sk_A @ 
% 0.45/0.67          (k8_tmap_1 @ sk_A @ sk_B))
% 0.45/0.67         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.45/0.67         <= (((v1_tsep_1 @ sk_B @ sk_A)))),
% 0.45/0.67      inference('sup+', [status(thm)], ['171', '191'])).
% 0.45/0.67  thf('193', plain,
% 0.45/0.67      ((~ (m1_subset_1 @ (k9_tmap_1 @ sk_A @ sk_B) @ 
% 0.45/0.67           (k1_zfmisc_1 @ 
% 0.45/0.67            (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.45/0.67             (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))))
% 0.45/0.67        | ~ (v5_pre_topc @ (k9_tmap_1 @ sk_A @ sk_B) @ sk_A @ 
% 0.45/0.67             (k8_tmap_1 @ sk_A @ sk_B))
% 0.45/0.67        | ~ (v1_funct_2 @ (k9_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.45/0.67             (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))
% 0.45/0.67        | ~ (v1_funct_1 @ (k9_tmap_1 @ sk_A @ sk_B))
% 0.45/0.67        | ~ (m1_pre_topc @ sk_B @ sk_A)
% 0.45/0.67        | ~ (v1_tsep_1 @ sk_B @ sk_A))),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('194', plain, ((v1_funct_1 @ (k9_tmap_1 @ sk_A @ sk_B))),
% 0.45/0.67      inference('clc', [status(thm)], ['63', '64'])).
% 0.45/0.67  thf('195', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('196', plain,
% 0.45/0.67      ((~ (m1_subset_1 @ (k9_tmap_1 @ sk_A @ sk_B) @ 
% 0.45/0.67           (k1_zfmisc_1 @ 
% 0.45/0.67            (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.45/0.67             (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))))
% 0.45/0.67        | ~ (v5_pre_topc @ (k9_tmap_1 @ sk_A @ sk_B) @ sk_A @ 
% 0.45/0.67             (k8_tmap_1 @ sk_A @ sk_B))
% 0.45/0.67        | ~ (v1_funct_2 @ (k9_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.45/0.67             (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))
% 0.45/0.67        | ~ (v1_tsep_1 @ sk_B @ sk_A))),
% 0.45/0.67      inference('demod', [status(thm)], ['193', '194', '195'])).
% 0.45/0.67  thf('197', plain,
% 0.45/0.67      (((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 0.45/0.67      inference('demod', [status(thm)], ['18', '52'])).
% 0.45/0.67  thf('198', plain,
% 0.45/0.67      (((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 0.45/0.67      inference('demod', [status(thm)], ['18', '52'])).
% 0.45/0.67  thf('199', plain,
% 0.45/0.67      ((~ (m1_subset_1 @ (k9_tmap_1 @ sk_A @ sk_B) @ 
% 0.45/0.67           (k1_zfmisc_1 @ 
% 0.45/0.67            (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))))
% 0.45/0.67        | ~ (v5_pre_topc @ (k9_tmap_1 @ sk_A @ sk_B) @ sk_A @ 
% 0.45/0.67             (k8_tmap_1 @ sk_A @ sk_B))
% 0.45/0.67        | ~ (v1_funct_2 @ (k9_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.45/0.67             (u1_struct_0 @ sk_A))
% 0.45/0.67        | ~ (v1_tsep_1 @ sk_B @ sk_A))),
% 0.45/0.67      inference('demod', [status(thm)], ['196', '197', '198'])).
% 0.45/0.67  thf('200', plain,
% 0.45/0.67      ((v1_funct_2 @ (k9_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.45/0.67        (u1_struct_0 @ sk_A))),
% 0.45/0.67      inference('clc', [status(thm)], ['75', '76'])).
% 0.45/0.67  thf('201', plain,
% 0.45/0.67      ((~ (m1_subset_1 @ (k9_tmap_1 @ sk_A @ sk_B) @ 
% 0.45/0.67           (k1_zfmisc_1 @ 
% 0.45/0.67            (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))))
% 0.45/0.67        | ~ (v5_pre_topc @ (k9_tmap_1 @ sk_A @ sk_B) @ sk_A @ 
% 0.45/0.67             (k8_tmap_1 @ sk_A @ sk_B))
% 0.45/0.67        | ~ (v1_tsep_1 @ sk_B @ sk_A))),
% 0.45/0.67      inference('demod', [status(thm)], ['199', '200'])).
% 0.45/0.67  thf('202', plain,
% 0.45/0.67      ((m1_subset_1 @ (k9_tmap_1 @ sk_A @ sk_B) @ 
% 0.45/0.67        (k1_zfmisc_1 @ 
% 0.45/0.67         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))))),
% 0.45/0.67      inference('clc', [status(thm)], ['131', '132'])).
% 0.45/0.67  thf('203', plain,
% 0.45/0.67      ((~ (v5_pre_topc @ (k9_tmap_1 @ sk_A @ sk_B) @ sk_A @ 
% 0.45/0.67           (k8_tmap_1 @ sk_A @ sk_B))
% 0.45/0.67        | ~ (v1_tsep_1 @ sk_B @ sk_A))),
% 0.45/0.67      inference('demod', [status(thm)], ['201', '202'])).
% 0.45/0.67  thf('204', plain,
% 0.45/0.67      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A)) | ~ (v1_tsep_1 @ sk_B @ sk_A)))
% 0.45/0.67         <= (((v1_tsep_1 @ sk_B @ sk_A)))),
% 0.45/0.67      inference('sup-', [status(thm)], ['192', '203'])).
% 0.45/0.67  thf('205', plain,
% 0.45/0.67      (((v1_tsep_1 @ sk_B @ sk_A)) <= (((v1_tsep_1 @ sk_B @ sk_A)))),
% 0.45/0.67      inference('split', [status(esa)], ['172'])).
% 0.45/0.67  thf('206', plain,
% 0.45/0.67      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))) <= (((v1_tsep_1 @ sk_B @ sk_A)))),
% 0.45/0.67      inference('demod', [status(thm)], ['204', '205'])).
% 0.45/0.67  thf(fc2_struct_0, axiom,
% 0.45/0.67    (![A:$i]:
% 0.45/0.67     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.45/0.67       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.45/0.67  thf('207', plain,
% 0.45/0.67      (![X2 : $i]:
% 0.45/0.67         (~ (v1_xboole_0 @ (u1_struct_0 @ X2))
% 0.45/0.67          | ~ (l1_struct_0 @ X2)
% 0.45/0.67          | (v2_struct_0 @ X2))),
% 0.45/0.67      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.45/0.67  thf('208', plain,
% 0.45/0.67      ((((v2_struct_0 @ sk_A) | ~ (l1_struct_0 @ sk_A)))
% 0.45/0.67         <= (((v1_tsep_1 @ sk_B @ sk_A)))),
% 0.45/0.67      inference('sup-', [status(thm)], ['206', '207'])).
% 0.45/0.67  thf('209', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf(dt_l1_pre_topc, axiom,
% 0.45/0.67    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.45/0.67  thf('210', plain, (![X0 : $i]: ((l1_struct_0 @ X0) | ~ (l1_pre_topc @ X0))),
% 0.45/0.67      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.45/0.67  thf('211', plain, ((l1_struct_0 @ sk_A)),
% 0.45/0.67      inference('sup-', [status(thm)], ['209', '210'])).
% 0.45/0.67  thf('212', plain, (((v2_struct_0 @ sk_A)) <= (((v1_tsep_1 @ sk_B @ sk_A)))),
% 0.45/0.67      inference('demod', [status(thm)], ['208', '211'])).
% 0.45/0.67  thf('213', plain, (~ (v2_struct_0 @ sk_A)),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('214', plain, (~ ((v1_tsep_1 @ sk_B @ sk_A))),
% 0.45/0.67      inference('sup-', [status(thm)], ['212', '213'])).
% 0.45/0.67  thf('215', plain, (~ ((v1_tsep_1 @ sk_B @ sk_A))),
% 0.45/0.67      inference('sat_resolution*', [status(thm)], ['214'])).
% 0.45/0.67  thf('216', plain, (~ (v3_pre_topc @ (u1_struct_0 @ sk_B) @ sk_A)),
% 0.45/0.67      inference('simpl_trail', [status(thm)], ['170', '215'])).
% 0.45/0.67  thf('217', plain,
% 0.45/0.67      (~ (v5_pre_topc @ (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)) @ sk_A @ 
% 0.45/0.67          (k8_tmap_1 @ sk_A @ sk_B))),
% 0.45/0.67      inference('clc', [status(thm)], ['156', '216'])).
% 0.45/0.67  thf('218', plain,
% 0.45/0.67      ((~ (v5_pre_topc @ (k9_tmap_1 @ sk_A @ sk_B) @ sk_A @ 
% 0.45/0.67           (k8_tmap_1 @ sk_A @ sk_B))
% 0.45/0.67        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.67      inference('sup-', [status(thm)], ['140', '217'])).
% 0.45/0.67  thf('219', plain,
% 0.45/0.67      (((v5_pre_topc @ (k9_tmap_1 @ sk_A @ sk_B) @ sk_A @ 
% 0.45/0.67         (k8_tmap_1 @ sk_A @ sk_B))
% 0.45/0.67        | (v1_tsep_1 @ sk_B @ sk_A))),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('220', plain,
% 0.45/0.67      (((v5_pre_topc @ (k9_tmap_1 @ sk_A @ sk_B) @ sk_A @ 
% 0.45/0.67         (k8_tmap_1 @ sk_A @ sk_B)))
% 0.45/0.67         <= (((v5_pre_topc @ (k9_tmap_1 @ sk_A @ sk_B) @ sk_A @ 
% 0.45/0.67               (k8_tmap_1 @ sk_A @ sk_B))))),
% 0.45/0.67      inference('split', [status(esa)], ['219'])).
% 0.45/0.67  thf('221', plain,
% 0.45/0.67      (((v5_pre_topc @ (k9_tmap_1 @ sk_A @ sk_B) @ sk_A @ 
% 0.45/0.67         (k8_tmap_1 @ sk_A @ sk_B))) | 
% 0.45/0.67       ((v1_tsep_1 @ sk_B @ sk_A))),
% 0.45/0.67      inference('split', [status(esa)], ['219'])).
% 0.45/0.67  thf('222', plain,
% 0.45/0.67      (((v5_pre_topc @ (k9_tmap_1 @ sk_A @ sk_B) @ sk_A @ 
% 0.45/0.67         (k8_tmap_1 @ sk_A @ sk_B)))),
% 0.45/0.67      inference('sat_resolution*', [status(thm)], ['214', '221'])).
% 0.45/0.67  thf('223', plain,
% 0.45/0.67      ((v5_pre_topc @ (k9_tmap_1 @ sk_A @ sk_B) @ sk_A @ 
% 0.45/0.67        (k8_tmap_1 @ sk_A @ sk_B))),
% 0.45/0.67      inference('simpl_trail', [status(thm)], ['220', '222'])).
% 0.45/0.67  thf('224', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.45/0.67      inference('demod', [status(thm)], ['218', '223'])).
% 0.45/0.67  thf('225', plain,
% 0.45/0.67      (![X2 : $i]:
% 0.45/0.67         (~ (v1_xboole_0 @ (u1_struct_0 @ X2))
% 0.45/0.67          | ~ (l1_struct_0 @ X2)
% 0.45/0.67          | (v2_struct_0 @ X2))),
% 0.45/0.67      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.45/0.67  thf('226', plain, (((v2_struct_0 @ sk_A) | ~ (l1_struct_0 @ sk_A))),
% 0.45/0.67      inference('sup-', [status(thm)], ['224', '225'])).
% 0.45/0.67  thf('227', plain, ((l1_struct_0 @ sk_A)),
% 0.45/0.67      inference('sup-', [status(thm)], ['209', '210'])).
% 0.45/0.67  thf('228', plain, ((v2_struct_0 @ sk_A)),
% 0.45/0.67      inference('demod', [status(thm)], ['226', '227'])).
% 0.45/0.67  thf('229', plain, ($false), inference('demod', [status(thm)], ['0', '228'])).
% 0.45/0.67  
% 0.45/0.67  % SZS output end Refutation
% 0.45/0.67  
% 0.45/0.68  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
