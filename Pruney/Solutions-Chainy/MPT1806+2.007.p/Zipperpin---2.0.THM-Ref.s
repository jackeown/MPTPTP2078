%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.7PtMssd8G9

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:11:03 EST 2020

% Result     : Theorem 0.45s
% Output     : Refutation 0.45s
% Verified   : 
% Statistics : Number of formulae       :  272 (8530 expanded)
%              Number of leaves         :   40 (2449 expanded)
%              Depth                    :   30
%              Number of atoms          : 2938 (226422 expanded)
%              Number of equality atoms :   63 (1734 expanded)
%              Maximal formula depth    :   23 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v5_pre_topc_type,type,(
    v5_pre_topc: $i > $i > $i > $o )).

thf(r1_funct_2_type,type,(
    r1_funct_2: $i > $i > $i > $i > $i > $i > $o )).

thf(k6_tmap_1_type,type,(
    k6_tmap_1: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_tsep_1_type,type,(
    v1_tsep_1: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(k7_tmap_1_type,type,(
    k7_tmap_1: $i > $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k5_tmap_1_type,type,(
    k5_tmap_1: $i > $i > $i )).

thf(k9_tmap_1_type,type,(
    k9_tmap_1: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k8_tmap_1_type,type,(
    k8_tmap_1: $i > $i > $i )).

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

thf('4',plain,(
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
    ! [X29: $i,X30: $i] :
      ( ~ ( m1_pre_topc @ X29 @ X30 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X29 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X30 ) ) )
      | ~ ( l1_pre_topc @ X30 ) ) ),
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
    ! [X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) )
      | ( ( u1_struct_0 @ ( k6_tmap_1 @ X26 @ X25 ) )
        = ( u1_struct_0 @ X26 ) )
      | ~ ( l1_pre_topc @ X26 )
      | ~ ( v2_pre_topc @ X26 )
      | ( v2_struct_0 @ X26 ) ) ),
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
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( m1_pre_topc @ X8 @ X9 )
      | ( ( sk_D @ X10 @ X8 @ X9 )
        = ( u1_struct_0 @ X8 ) )
      | ( X10
        = ( k8_tmap_1 @ X9 @ X8 ) )
      | ~ ( l1_pre_topc @ X10 )
      | ~ ( v2_pre_topc @ X10 )
      | ~ ( v1_pre_topc @ X10 )
      | ~ ( l1_pre_topc @ X9 )
      | ~ ( v2_pre_topc @ X9 )
      | ( v2_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d11_tmap_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( X0
        = ( k8_tmap_1 @ sk_A @ sk_B ) )
      | ( ( sk_D @ X0 @ sk_B @ sk_A )
        = ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( X0
        = ( k8_tmap_1 @ sk_A @ sk_B ) )
      | ( ( sk_D @ X0 @ sk_B @ sk_A )
        = ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['21','22','23'])).

thf('25',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( m1_pre_topc @ X8 @ X9 )
      | ( X10
       != ( k6_tmap_1 @ X9 @ ( sk_D @ X10 @ X8 @ X9 ) ) )
      | ( X10
        = ( k8_tmap_1 @ X9 @ X8 ) )
      | ~ ( l1_pre_topc @ X10 )
      | ~ ( v2_pre_topc @ X10 )
      | ~ ( v1_pre_topc @ X10 )
      | ~ ( l1_pre_topc @ X9 )
      | ~ ( v2_pre_topc @ X9 )
      | ( v2_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d11_tmap_1])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( X0
       != ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
      | ( X0
        = ( k8_tmap_1 @ sk_A @ sk_B ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( v1_pre_topc @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( X0
        = ( k8_tmap_1 @ sk_A @ sk_B ) )
      | ~ ( m1_pre_topc @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( X0
       != ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
      | ( X0
        = ( k8_tmap_1 @ sk_A @ sk_B ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( v1_pre_topc @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( X0
        = ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['26','27','28','29'])).

thf('31',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v1_pre_topc @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
    | ~ ( v2_pre_topc @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
    | ~ ( l1_pre_topc @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
    | ( ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) )
      = ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf(dt_k6_tmap_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( ( v1_pre_topc @ ( k6_tmap_1 @ A @ B ) )
        & ( v2_pre_topc @ ( k6_tmap_1 @ A @ B ) )
        & ( l1_pre_topc @ ( k6_tmap_1 @ A @ B ) ) ) ) )).

thf('33',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( l1_pre_topc @ X19 )
      | ~ ( v2_pre_topc @ X19 )
      | ( v2_struct_0 @ X19 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ( l1_pre_topc @ ( k6_tmap_1 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_tmap_1])).

thf('34',plain,
    ( ( l1_pre_topc @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
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
    ( ( l1_pre_topc @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['34','35','36'])).

thf('38',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    l1_pre_topc @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['37','38'])).

thf('40',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('41',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( l1_pre_topc @ X19 )
      | ~ ( v2_pre_topc @ X19 )
      | ( v2_struct_0 @ X19 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ( v2_pre_topc @ ( k6_tmap_1 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_tmap_1])).

thf('42',plain,
    ( ( v2_pre_topc @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
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
    ( ( v2_pre_topc @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['42','43','44'])).

thf('46',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    v2_pre_topc @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['45','46'])).

thf('48',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('49',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( l1_pre_topc @ X19 )
      | ~ ( v2_pre_topc @ X19 )
      | ( v2_struct_0 @ X19 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ( v1_pre_topc @ ( k6_tmap_1 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_tmap_1])).

thf('50',plain,
    ( ( v1_pre_topc @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,
    ( ( v1_pre_topc @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['50','51','52'])).

thf('54',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    v1_pre_topc @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['53','54'])).

thf('56',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) )
      = ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('simplify_reflect+',[status(thm)],['31','39','47','55'])).

thf('57',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,
    ( ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) )
    = ( k8_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['56','57'])).

thf('59',plain,
    ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['18','58'])).

thf('60',plain,
    ( ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) )
    = ( k8_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['56','57'])).

thf('61',plain,
    ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['18','58'])).

thf('62',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('63',plain,
    ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['18','58'])).

thf('64',plain,(
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

thf('65',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( l1_pre_topc @ X23 )
      | ~ ( v2_pre_topc @ X23 )
      | ( v2_struct_0 @ X23 )
      | ~ ( m1_pre_topc @ X24 @ X23 )
      | ( v1_funct_2 @ ( k9_tmap_1 @ X23 @ X24 ) @ ( u1_struct_0 @ X23 ) @ ( u1_struct_0 @ ( k8_tmap_1 @ X23 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k9_tmap_1])).

thf('66',plain,
    ( ( v1_funct_2 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,
    ( ( v1_funct_2 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['66','67','68'])).

thf('70',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    v1_funct_2 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['69','70'])).

thf('72',plain,
    ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['18','58'])).

thf('73',plain,(
    v1_funct_2 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('74',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( l1_pre_topc @ X23 )
      | ~ ( v2_pre_topc @ X23 )
      | ( v2_struct_0 @ X23 )
      | ~ ( m1_pre_topc @ X24 @ X23 )
      | ( v1_funct_1 @ ( k9_tmap_1 @ X23 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k9_tmap_1])).

thf('76',plain,
    ( ( v1_funct_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,
    ( ( v1_funct_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['76','77','78'])).

thf('80',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    v1_funct_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['79','80'])).

thf('82',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,
    ( ( ( r1_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( m1_subset_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ) ) ),
    inference(demod,[status(thm)],['5','6','59','60','61','62','63','73','81','82','83'])).

thf('85',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,
    ( ( r1_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
   <= ( m1_subset_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ) ) ),
    inference(clc,[status(thm)],['84','85'])).

thf('87',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( l1_pre_topc @ X23 )
      | ~ ( v2_pre_topc @ X23 )
      | ( v2_struct_0 @ X23 )
      | ~ ( m1_pre_topc @ X24 @ X23 )
      | ( m1_subset_1 @ ( k9_tmap_1 @ X23 @ X24 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X23 ) @ ( u1_struct_0 @ ( k8_tmap_1 @ X23 @ X24 ) ) ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k9_tmap_1])).

thf('89',plain,
    ( ( m1_subset_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,
    ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['18','58'])).

thf('91',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,
    ( ( m1_subset_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['89','90','91','92'])).

thf('94',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    m1_subset_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['93','94'])).

thf('96',plain,
    ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['18','58'])).

thf('97',plain,
    ( ~ ( m1_subset_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ) )
    | ~ ( v5_pre_topc @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( v1_funct_2 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) )
    | ~ ( v1_funct_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( m1_pre_topc @ sk_B @ sk_A )
    | ~ ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,
    ( ~ ( m1_subset_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ) )
   <= ~ ( m1_subset_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ) ) ),
    inference(split,[status(esa)],['97'])).

thf('99',plain,
    ( ~ ( m1_subset_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ~ ( m1_subset_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['96','98'])).

thf('100',plain,(
    m1_subset_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['95','99'])).

thf('101',plain,(
    m1_subset_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ) ),
    inference('sat_resolution*',[status(thm)],['100'])).

thf('102',plain,(
    r1_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ),
    inference(simpl_trail,[status(thm)],['86','101'])).

thf('103',plain,
    ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['18','58'])).

thf('104',plain,
    ( ( m1_subset_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ) )
   <= ( m1_subset_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ) ) ),
    inference(split,[status(esa)],['1'])).

thf('105',plain,
    ( ( m1_subset_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ( m1_subset_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ) ) ),
    inference('sup+',[status(thm)],['103','104'])).

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

thf('106',plain,(
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

thf('107',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ~ ( r1_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ X2 @ X1 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ X0 )
        | ( ( k9_tmap_1 @ sk_A @ sk_B )
          = X0 )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
        | ~ ( v1_funct_2 @ X0 @ X2 @ X1 )
        | ~ ( v1_funct_1 @ X0 )
        | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
        | ( v1_xboole_0 @ X1 )
        | ~ ( v1_funct_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) )
        | ~ ( v1_funct_2 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_subset_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['105','106'])).

thf('108',plain,(
    v1_funct_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['79','80'])).

thf('109',plain,(
    v1_funct_2 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('110',plain,
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
    inference(demod,[status(thm)],['107','108','109'])).

thf('111',plain,(
    m1_subset_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ) ),
    inference('sat_resolution*',[status(thm)],['100'])).

thf('112',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ X2 @ X1 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ X0 )
      | ( ( k9_tmap_1 @ sk_A @ sk_B )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_2 @ X0 @ X2 @ X1 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ X1 ) ) ),
    inference(simpl_trail,[status(thm)],['110','111'])).

thf('113',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_funct_1 @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
    | ~ ( v1_funct_2 @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( m1_subset_1 @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ( ( k9_tmap_1 @ sk_A @ sk_B )
      = ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['102','112'])).

thf('114',plain,(
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

thf('115',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( l1_pre_topc @ X21 )
      | ~ ( v2_pre_topc @ X21 )
      | ( v2_struct_0 @ X21 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ( v1_funct_1 @ ( k7_tmap_1 @ X21 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_tmap_1])).

thf('116',plain,
    ( ( v1_funct_1 @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
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
    ( ( v1_funct_1 @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['116','117','118'])).

thf('120',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('121',plain,(
    v1_funct_1 @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['119','120'])).

thf('122',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('123',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( l1_pre_topc @ X21 )
      | ~ ( v2_pre_topc @ X21 )
      | ( v2_struct_0 @ X21 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ( v1_funct_2 @ ( k7_tmap_1 @ X21 @ X22 ) @ ( u1_struct_0 @ X21 ) @ ( u1_struct_0 @ ( k6_tmap_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_tmap_1])).

thf('124',plain,
    ( ( v1_funct_2 @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['122','123'])).

thf('125',plain,
    ( ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) )
    = ( k8_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['56','57'])).

thf('126',plain,
    ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['18','58'])).

thf('127',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('128',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('129',plain,
    ( ( v1_funct_2 @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['124','125','126','127','128'])).

thf('130',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('131',plain,(
    v1_funct_2 @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['129','130'])).

thf('132',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('133',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( l1_pre_topc @ X21 )
      | ~ ( v2_pre_topc @ X21 )
      | ( v2_struct_0 @ X21 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ( m1_subset_1 @ ( k7_tmap_1 @ X21 @ X22 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X21 ) @ ( u1_struct_0 @ ( k6_tmap_1 @ X21 @ X22 ) ) ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_tmap_1])).

thf('134',plain,
    ( ( m1_subset_1 @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ) ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['132','133'])).

thf('135',plain,
    ( ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) )
    = ( k8_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['56','57'])).

thf('136',plain,
    ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['18','58'])).

thf('137',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('138',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('139',plain,
    ( ( m1_subset_1 @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['134','135','136','137','138'])).

thf('140',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('141',plain,(
    m1_subset_1 @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['139','140'])).

thf('142',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( ( k9_tmap_1 @ sk_A @ sk_B )
      = ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['113','121','131','141'])).

thf('143',plain,
    ( ( ( k9_tmap_1 @ sk_A @ sk_B )
      = ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['142'])).

thf('144',plain,
    ( ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) )
    = ( k8_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['56','57'])).

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
    ! [X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ~ ( v1_funct_1 @ ( k7_tmap_1 @ X28 @ X27 ) )
      | ~ ( v1_funct_2 @ ( k7_tmap_1 @ X28 @ X27 ) @ ( u1_struct_0 @ X28 ) @ ( u1_struct_0 @ ( k6_tmap_1 @ X28 @ X27 ) ) )
      | ~ ( v5_pre_topc @ ( k7_tmap_1 @ X28 @ X27 ) @ X28 @ ( k6_tmap_1 @ X28 @ X27 ) )
      | ~ ( m1_subset_1 @ ( k7_tmap_1 @ X28 @ X27 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X28 ) @ ( u1_struct_0 @ ( k6_tmap_1 @ X28 @ X27 ) ) ) ) )
      | ( v3_pre_topc @ X27 @ X28 )
      | ~ ( l1_pre_topc @ X28 )
      | ~ ( v2_pre_topc @ X28 )
      | ( v2_struct_0 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t113_tmap_1])).

thf('146',plain,
    ( ~ ( m1_subset_1 @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v3_pre_topc @ ( u1_struct_0 @ sk_B ) @ sk_A )
    | ~ ( v5_pre_topc @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) @ sk_A @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
    | ~ ( v1_funct_2 @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( v1_funct_1 @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
    | ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['144','145'])).

thf('147',plain,
    ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['18','58'])).

thf('148',plain,(
    m1_subset_1 @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['139','140'])).

thf('149',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('150',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('151',plain,
    ( ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) )
    = ( k8_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['56','57'])).

thf('152',plain,
    ( ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) )
    = ( k8_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['56','57'])).

thf('153',plain,
    ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['18','58'])).

thf('154',plain,(
    v1_funct_2 @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['129','130'])).

thf('155',plain,(
    v1_funct_1 @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['119','120'])).

thf('156',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('157',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v3_pre_topc @ ( u1_struct_0 @ sk_B ) @ sk_A )
    | ~ ( v5_pre_topc @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['146','147','148','149','150','151','152','153','154','155','156'])).

thf('158',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('159',plain,
    ( ~ ( v5_pre_topc @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v3_pre_topc @ ( u1_struct_0 @ sk_B ) @ sk_A ) ),
    inference(clc,[status(thm)],['157','158'])).

thf('160',plain,
    ( ~ ( v5_pre_topc @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v3_pre_topc @ ( u1_struct_0 @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['143','159'])).

thf('161',plain,
    ( ( v5_pre_topc @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('162',plain,
    ( ( v5_pre_topc @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) )
   <= ( v5_pre_topc @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['161'])).

thf('163',plain,
    ( ~ ( v1_tsep_1 @ sk_B @ sk_A )
    | ~ ( v5_pre_topc @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( m1_pre_topc @ sk_B @ sk_A )
    | ~ ( v1_funct_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( v1_funct_2 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) )
    | ~ ( m1_subset_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ) ) ),
    inference(split,[status(esa)],['97'])).

thf('164',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('165',plain,
    ( ~ ( m1_pre_topc @ sk_B @ sk_A )
   <= ~ ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['97'])).

thf('166',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['164','165'])).

thf('167',plain,(
    v1_funct_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['79','80'])).

thf('168',plain,
    ( ~ ( v1_funct_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) )
   <= ~ ( v1_funct_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['97'])).

thf('169',plain,(
    v1_funct_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['167','168'])).

thf('170',plain,(
    v1_funct_2 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['69','70'])).

thf('171',plain,
    ( ~ ( v1_funct_2 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) )
   <= ~ ( v1_funct_2 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['97'])).

thf('172',plain,(
    v1_funct_2 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['170','171'])).

thf('173',plain,
    ( ( ( k9_tmap_1 @ sk_A @ sk_B )
      = ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['142'])).

thf('174',plain,
    ( ( v1_funct_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) )
    | ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('175',plain,
    ( ( v1_tsep_1 @ sk_B @ sk_A )
   <= ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['174'])).

thf('176',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['9','10'])).

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

thf('177',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_pre_topc @ X16 @ X17 )
      | ~ ( v1_tsep_1 @ X16 @ X17 )
      | ( X18
       != ( u1_struct_0 @ X16 ) )
      | ( v3_pre_topc @ X18 @ X17 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[d1_tsep_1])).

thf('178',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( l1_pre_topc @ X17 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X16 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ( v3_pre_topc @ ( u1_struct_0 @ X16 ) @ X17 )
      | ~ ( v1_tsep_1 @ X16 @ X17 )
      | ~ ( m1_pre_topc @ X16 @ X17 ) ) ),
    inference(simplify,[status(thm)],['177'])).

thf('179',plain,
    ( ~ ( m1_pre_topc @ sk_B @ sk_A )
    | ~ ( v1_tsep_1 @ sk_B @ sk_A )
    | ( v3_pre_topc @ ( u1_struct_0 @ sk_B ) @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['176','178'])).

thf('180',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('181',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('182',plain,
    ( ~ ( v1_tsep_1 @ sk_B @ sk_A )
    | ( v3_pre_topc @ ( u1_struct_0 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['179','180','181'])).

thf('183',plain,
    ( ( v3_pre_topc @ ( u1_struct_0 @ sk_B ) @ sk_A )
   <= ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['175','182'])).

thf('184',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('185',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ~ ( v3_pre_topc @ X27 @ X28 )
      | ( v5_pre_topc @ ( k7_tmap_1 @ X28 @ X27 ) @ X28 @ ( k6_tmap_1 @ X28 @ X27 ) )
      | ~ ( l1_pre_topc @ X28 )
      | ~ ( v2_pre_topc @ X28 )
      | ( v2_struct_0 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t113_tmap_1])).

thf('186',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v5_pre_topc @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) @ sk_A @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
    | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['184','185'])).

thf('187',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('188',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('189',plain,
    ( ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) )
    = ( k8_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['56','57'])).

thf('190',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v5_pre_topc @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['186','187','188','189'])).

thf('191',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('192',plain,
    ( ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_B ) @ sk_A )
    | ( v5_pre_topc @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['190','191'])).

thf('193',plain,
    ( ( v5_pre_topc @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) )
   <= ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['183','192'])).

thf('194',plain,
    ( ( ( v5_pre_topc @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['173','193'])).

thf('195',plain,
    ( ~ ( v5_pre_topc @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) )
   <= ~ ( v5_pre_topc @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['97'])).

thf('196',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
   <= ( ~ ( v5_pre_topc @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) )
      & ( v1_tsep_1 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['194','195'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('197',plain,(
    ! [X1: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X1 ) )
      | ~ ( l1_struct_0 @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('198',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( ~ ( v5_pre_topc @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) )
      & ( v1_tsep_1 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['196','197'])).

thf('199',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('200',plain,(
    ! [X0: $i] :
      ( ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('201',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['199','200'])).

thf('202',plain,
    ( ( v2_struct_0 @ sk_A )
   <= ( ~ ( v5_pre_topc @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) )
      & ( v1_tsep_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['198','201'])).

thf('203',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('204',plain,
    ( ( v5_pre_topc @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['202','203'])).

thf('205',plain,
    ( ( v5_pre_topc @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['161'])).

thf('206',plain,(
    v5_pre_topc @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['163','166','169','172','100','204','205'])).

thf('207',plain,(
    v5_pre_topc @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['162','206'])).

thf('208',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v3_pre_topc @ ( u1_struct_0 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['160','207'])).

thf('209',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('210',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( m1_pre_topc @ X16 @ X17 )
      | ( ( sk_C @ X16 @ X17 )
        = ( u1_struct_0 @ X16 ) )
      | ( v1_tsep_1 @ X16 @ X17 )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[d1_tsep_1])).

thf('211',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v1_tsep_1 @ sk_B @ sk_A )
    | ( ( sk_C @ sk_B @ sk_A )
      = ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['209','210'])).

thf('212',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('213',plain,
    ( ( v1_tsep_1 @ sk_B @ sk_A )
    | ( ( sk_C @ sk_B @ sk_A )
      = ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['211','212'])).

thf('214',plain,
    ( ~ ( v1_tsep_1 @ sk_B @ sk_A )
   <= ~ ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['97'])).

thf('215',plain,
    ( ( ( sk_C @ sk_B @ sk_A )
      = ( u1_struct_0 @ sk_B ) )
   <= ~ ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['213','214'])).

thf('216',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( m1_pre_topc @ X16 @ X17 )
      | ~ ( v3_pre_topc @ ( sk_C @ X16 @ X17 ) @ X17 )
      | ( v1_tsep_1 @ X16 @ X17 )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[d1_tsep_1])).

thf('217',plain,
    ( ( ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_B ) @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v1_tsep_1 @ sk_B @ sk_A )
      | ~ ( m1_pre_topc @ sk_B @ sk_A ) )
   <= ~ ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['215','216'])).

thf('218',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('219',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('220',plain,
    ( ( ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_B ) @ sk_A )
      | ( v1_tsep_1 @ sk_B @ sk_A ) )
   <= ~ ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['217','218','219'])).

thf('221',plain,
    ( ~ ( v1_tsep_1 @ sk_B @ sk_A )
   <= ~ ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['97'])).

thf('222',plain,
    ( ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_B ) @ sk_A )
   <= ~ ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['220','221'])).

thf('223',plain,(
    ~ ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['163','166','169','172','100','204'])).

thf('224',plain,(
    ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_B ) @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['222','223'])).

thf('225',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['208','224'])).

thf('226',plain,(
    ! [X1: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X1 ) )
      | ~ ( l1_struct_0 @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('227',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['225','226'])).

thf('228',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['199','200'])).

thf('229',plain,(
    v2_struct_0 @ sk_A ),
    inference(demod,[status(thm)],['227','228'])).

thf('230',plain,(
    $false ),
    inference(demod,[status(thm)],['0','229'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.7PtMssd8G9
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:20:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.45/0.65  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.45/0.65  % Solved by: fo/fo7.sh
% 0.45/0.65  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.45/0.65  % done 364 iterations in 0.197s
% 0.45/0.65  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.45/0.65  % SZS output start Refutation
% 0.45/0.65  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.45/0.65  thf(v5_pre_topc_type, type, v5_pre_topc: $i > $i > $i > $o).
% 0.45/0.65  thf(r1_funct_2_type, type, r1_funct_2: $i > $i > $i > $i > $i > $i > $o).
% 0.45/0.65  thf(k6_tmap_1_type, type, k6_tmap_1: $i > $i > $i).
% 0.45/0.65  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.45/0.65  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.45/0.65  thf(v1_tsep_1_type, type, v1_tsep_1: $i > $i > $o).
% 0.45/0.65  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.45/0.65  thf(sk_B_type, type, sk_B: $i).
% 0.45/0.65  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.45/0.65  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.45/0.65  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.45/0.65  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.45/0.65  thf(k7_tmap_1_type, type, k7_tmap_1: $i > $i > $i).
% 0.45/0.65  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.45/0.65  thf(k5_tmap_1_type, type, k5_tmap_1: $i > $i > $i).
% 0.45/0.65  thf(k9_tmap_1_type, type, k9_tmap_1: $i > $i > $i).
% 0.45/0.65  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.45/0.65  thf(sk_A_type, type, sk_A: $i).
% 0.45/0.65  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.45/0.65  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.45/0.65  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.45/0.65  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 0.45/0.65  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 0.45/0.65  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.45/0.65  thf(k8_tmap_1_type, type, k8_tmap_1: $i > $i > $i).
% 0.45/0.65  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.45/0.65  thf(t122_tmap_1, conjecture,
% 0.45/0.65    (![A:$i]:
% 0.45/0.65     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.45/0.65       ( ![B:$i]:
% 0.45/0.65         ( ( m1_pre_topc @ B @ A ) =>
% 0.45/0.65           ( ( ( v1_tsep_1 @ B @ A ) & ( m1_pre_topc @ B @ A ) ) <=>
% 0.45/0.65             ( ( v1_funct_1 @ ( k9_tmap_1 @ A @ B ) ) & 
% 0.45/0.65               ( v1_funct_2 @
% 0.45/0.65                 ( k9_tmap_1 @ A @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.45/0.65                 ( u1_struct_0 @ ( k8_tmap_1 @ A @ B ) ) ) & 
% 0.45/0.65               ( v5_pre_topc @
% 0.45/0.65                 ( k9_tmap_1 @ A @ B ) @ A @ ( k8_tmap_1 @ A @ B ) ) & 
% 0.45/0.65               ( m1_subset_1 @
% 0.45/0.65                 ( k9_tmap_1 @ A @ B ) @ 
% 0.45/0.65                 ( k1_zfmisc_1 @
% 0.45/0.65                   ( k2_zfmisc_1 @
% 0.45/0.65                     ( u1_struct_0 @ A ) @ 
% 0.45/0.65                     ( u1_struct_0 @ ( k8_tmap_1 @ A @ B ) ) ) ) ) ) ) ) ) ))).
% 0.45/0.65  thf(zf_stmt_0, negated_conjecture,
% 0.45/0.65    (~( ![A:$i]:
% 0.45/0.65        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.45/0.65            ( l1_pre_topc @ A ) ) =>
% 0.45/0.65          ( ![B:$i]:
% 0.45/0.65            ( ( m1_pre_topc @ B @ A ) =>
% 0.45/0.65              ( ( ( v1_tsep_1 @ B @ A ) & ( m1_pre_topc @ B @ A ) ) <=>
% 0.45/0.65                ( ( v1_funct_1 @ ( k9_tmap_1 @ A @ B ) ) & 
% 0.45/0.65                  ( v1_funct_2 @
% 0.45/0.65                    ( k9_tmap_1 @ A @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.45/0.65                    ( u1_struct_0 @ ( k8_tmap_1 @ A @ B ) ) ) & 
% 0.45/0.65                  ( v5_pre_topc @
% 0.45/0.65                    ( k9_tmap_1 @ A @ B ) @ A @ ( k8_tmap_1 @ A @ B ) ) & 
% 0.45/0.65                  ( m1_subset_1 @
% 0.45/0.65                    ( k9_tmap_1 @ A @ B ) @ 
% 0.45/0.65                    ( k1_zfmisc_1 @
% 0.45/0.65                      ( k2_zfmisc_1 @
% 0.45/0.65                        ( u1_struct_0 @ A ) @ 
% 0.45/0.65                        ( u1_struct_0 @ ( k8_tmap_1 @ A @ B ) ) ) ) ) ) ) ) ) ) )),
% 0.45/0.65    inference('cnf.neg', [status(esa)], [t122_tmap_1])).
% 0.45/0.65  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('1', plain,
% 0.45/0.65      (((m1_subset_1 @ (k9_tmap_1 @ sk_A @ sk_B) @ 
% 0.45/0.65         (k1_zfmisc_1 @ 
% 0.45/0.65          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.45/0.65           (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))))
% 0.45/0.65        | (v1_tsep_1 @ sk_B @ sk_A))),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('2', plain,
% 0.45/0.65      (((m1_subset_1 @ (k9_tmap_1 @ sk_A @ sk_B) @ 
% 0.45/0.65         (k1_zfmisc_1 @ 
% 0.45/0.65          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.45/0.65           (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B))))))
% 0.45/0.65         <= (((m1_subset_1 @ (k9_tmap_1 @ sk_A @ sk_B) @ 
% 0.45/0.65               (k1_zfmisc_1 @ 
% 0.45/0.65                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.45/0.65                 (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))))))),
% 0.45/0.65      inference('split', [status(esa)], ['1'])).
% 0.45/0.65  thf(d12_tmap_1, axiom,
% 0.45/0.65    (![A:$i]:
% 0.45/0.65     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.45/0.65       ( ![B:$i]:
% 0.45/0.65         ( ( m1_pre_topc @ B @ A ) =>
% 0.45/0.65           ( ![C:$i]:
% 0.45/0.65             ( ( ( v1_funct_1 @ C ) & 
% 0.45/0.65                 ( v1_funct_2 @
% 0.45/0.65                   C @ ( u1_struct_0 @ A ) @ 
% 0.45/0.65                   ( u1_struct_0 @ ( k8_tmap_1 @ A @ B ) ) ) & 
% 0.45/0.65                 ( m1_subset_1 @
% 0.45/0.65                   C @ 
% 0.45/0.65                   ( k1_zfmisc_1 @
% 0.45/0.65                     ( k2_zfmisc_1 @
% 0.45/0.65                       ( u1_struct_0 @ A ) @ 
% 0.45/0.65                       ( u1_struct_0 @ ( k8_tmap_1 @ A @ B ) ) ) ) ) ) =>
% 0.45/0.65               ( ( ( C ) = ( k9_tmap_1 @ A @ B ) ) <=>
% 0.45/0.65                 ( ![D:$i]:
% 0.45/0.65                   ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.45/0.65                     ( ( ( D ) = ( u1_struct_0 @ B ) ) =>
% 0.45/0.65                       ( r1_funct_2 @
% 0.45/0.65                         ( u1_struct_0 @ A ) @ 
% 0.45/0.65                         ( u1_struct_0 @ ( k8_tmap_1 @ A @ B ) ) @ 
% 0.45/0.65                         ( u1_struct_0 @ A ) @ 
% 0.45/0.65                         ( u1_struct_0 @ ( k6_tmap_1 @ A @ D ) ) @ C @ 
% 0.45/0.65                         ( k7_tmap_1 @ A @ D ) ) ) ) ) ) ) ) ) ) ))).
% 0.45/0.65  thf('3', plain,
% 0.45/0.65      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.45/0.65         (~ (m1_pre_topc @ X12 @ X13)
% 0.45/0.65          | ((X14) != (k9_tmap_1 @ X13 @ X12))
% 0.45/0.65          | ((X15) != (u1_struct_0 @ X12))
% 0.45/0.65          | (r1_funct_2 @ (u1_struct_0 @ X13) @ 
% 0.45/0.65             (u1_struct_0 @ (k8_tmap_1 @ X13 @ X12)) @ (u1_struct_0 @ X13) @ 
% 0.45/0.65             (u1_struct_0 @ (k6_tmap_1 @ X13 @ X15)) @ X14 @ 
% 0.45/0.65             (k7_tmap_1 @ X13 @ X15))
% 0.45/0.65          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.45/0.65          | ~ (m1_subset_1 @ X14 @ 
% 0.45/0.65               (k1_zfmisc_1 @ 
% 0.45/0.65                (k2_zfmisc_1 @ (u1_struct_0 @ X13) @ 
% 0.45/0.65                 (u1_struct_0 @ (k8_tmap_1 @ X13 @ X12)))))
% 0.45/0.65          | ~ (v1_funct_2 @ X14 @ (u1_struct_0 @ X13) @ 
% 0.45/0.65               (u1_struct_0 @ (k8_tmap_1 @ X13 @ X12)))
% 0.45/0.65          | ~ (v1_funct_1 @ X14)
% 0.45/0.65          | ~ (l1_pre_topc @ X13)
% 0.45/0.65          | ~ (v2_pre_topc @ X13)
% 0.45/0.65          | (v2_struct_0 @ X13))),
% 0.45/0.65      inference('cnf', [status(esa)], [d12_tmap_1])).
% 0.45/0.65  thf('4', plain,
% 0.45/0.65      (![X12 : $i, X13 : $i]:
% 0.45/0.65         ((v2_struct_0 @ X13)
% 0.45/0.65          | ~ (v2_pre_topc @ X13)
% 0.45/0.65          | ~ (l1_pre_topc @ X13)
% 0.45/0.65          | ~ (v1_funct_1 @ (k9_tmap_1 @ X13 @ X12))
% 0.45/0.65          | ~ (v1_funct_2 @ (k9_tmap_1 @ X13 @ X12) @ (u1_struct_0 @ X13) @ 
% 0.45/0.65               (u1_struct_0 @ (k8_tmap_1 @ X13 @ X12)))
% 0.45/0.65          | ~ (m1_subset_1 @ (k9_tmap_1 @ X13 @ X12) @ 
% 0.45/0.65               (k1_zfmisc_1 @ 
% 0.45/0.65                (k2_zfmisc_1 @ (u1_struct_0 @ X13) @ 
% 0.45/0.65                 (u1_struct_0 @ (k8_tmap_1 @ X13 @ X12)))))
% 0.45/0.65          | ~ (m1_subset_1 @ (u1_struct_0 @ X12) @ 
% 0.45/0.65               (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.45/0.65          | (r1_funct_2 @ (u1_struct_0 @ X13) @ 
% 0.45/0.65             (u1_struct_0 @ (k8_tmap_1 @ X13 @ X12)) @ (u1_struct_0 @ X13) @ 
% 0.45/0.65             (u1_struct_0 @ (k6_tmap_1 @ X13 @ (u1_struct_0 @ X12))) @ 
% 0.45/0.65             (k9_tmap_1 @ X13 @ X12) @ (k7_tmap_1 @ X13 @ (u1_struct_0 @ X12)))
% 0.45/0.65          | ~ (m1_pre_topc @ X12 @ X13))),
% 0.45/0.65      inference('simplify', [status(thm)], ['3'])).
% 0.45/0.65  thf('5', plain,
% 0.45/0.65      (((~ (m1_pre_topc @ sk_B @ sk_A)
% 0.45/0.65         | (r1_funct_2 @ (u1_struct_0 @ sk_A) @ 
% 0.45/0.65            (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)) @ (u1_struct_0 @ sk_A) @ 
% 0.45/0.65            (u1_struct_0 @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B))) @ 
% 0.45/0.65            (k9_tmap_1 @ sk_A @ sk_B) @ 
% 0.45/0.65            (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 0.45/0.65         | ~ (m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.45/0.65              (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.45/0.65         | ~ (v1_funct_2 @ (k9_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.45/0.65              (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))
% 0.45/0.65         | ~ (v1_funct_1 @ (k9_tmap_1 @ sk_A @ sk_B))
% 0.45/0.65         | ~ (l1_pre_topc @ sk_A)
% 0.45/0.65         | ~ (v2_pre_topc @ sk_A)
% 0.45/0.65         | (v2_struct_0 @ sk_A)))
% 0.45/0.65         <= (((m1_subset_1 @ (k9_tmap_1 @ sk_A @ sk_B) @ 
% 0.45/0.65               (k1_zfmisc_1 @ 
% 0.45/0.65                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.45/0.65                 (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))))))),
% 0.45/0.65      inference('sup-', [status(thm)], ['2', '4'])).
% 0.45/0.65  thf('6', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('7', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf(t1_tsep_1, axiom,
% 0.45/0.65    (![A:$i]:
% 0.45/0.65     ( ( l1_pre_topc @ A ) =>
% 0.45/0.65       ( ![B:$i]:
% 0.45/0.65         ( ( m1_pre_topc @ B @ A ) =>
% 0.45/0.65           ( m1_subset_1 @
% 0.45/0.65             ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.45/0.65  thf('8', plain,
% 0.45/0.65      (![X29 : $i, X30 : $i]:
% 0.45/0.65         (~ (m1_pre_topc @ X29 @ X30)
% 0.45/0.65          | (m1_subset_1 @ (u1_struct_0 @ X29) @ 
% 0.45/0.65             (k1_zfmisc_1 @ (u1_struct_0 @ X30)))
% 0.45/0.65          | ~ (l1_pre_topc @ X30))),
% 0.45/0.65      inference('cnf', [status(esa)], [t1_tsep_1])).
% 0.45/0.65  thf('9', plain,
% 0.45/0.65      ((~ (l1_pre_topc @ sk_A)
% 0.45/0.65        | (m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.45/0.65           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.45/0.65      inference('sup-', [status(thm)], ['7', '8'])).
% 0.45/0.65  thf('10', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('11', plain,
% 0.45/0.65      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.45/0.65        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.65      inference('demod', [status(thm)], ['9', '10'])).
% 0.45/0.65  thf(t104_tmap_1, axiom,
% 0.45/0.65    (![A:$i]:
% 0.45/0.65     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.45/0.65       ( ![B:$i]:
% 0.45/0.65         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.45/0.65           ( ( ( u1_struct_0 @ ( k6_tmap_1 @ A @ B ) ) = ( u1_struct_0 @ A ) ) & 
% 0.45/0.65             ( ( u1_pre_topc @ ( k6_tmap_1 @ A @ B ) ) = ( k5_tmap_1 @ A @ B ) ) ) ) ) ))).
% 0.45/0.65  thf('12', plain,
% 0.45/0.65      (![X25 : $i, X26 : $i]:
% 0.45/0.65         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X26)))
% 0.45/0.65          | ((u1_struct_0 @ (k6_tmap_1 @ X26 @ X25)) = (u1_struct_0 @ X26))
% 0.45/0.65          | ~ (l1_pre_topc @ X26)
% 0.45/0.65          | ~ (v2_pre_topc @ X26)
% 0.45/0.65          | (v2_struct_0 @ X26))),
% 0.45/0.65      inference('cnf', [status(esa)], [t104_tmap_1])).
% 0.45/0.65  thf('13', plain,
% 0.45/0.65      (((v2_struct_0 @ sk_A)
% 0.45/0.65        | ~ (v2_pre_topc @ sk_A)
% 0.45/0.65        | ~ (l1_pre_topc @ sk_A)
% 0.45/0.65        | ((u1_struct_0 @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 0.45/0.65            = (u1_struct_0 @ sk_A)))),
% 0.45/0.65      inference('sup-', [status(thm)], ['11', '12'])).
% 0.45/0.65  thf('14', plain, ((v2_pre_topc @ sk_A)),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('15', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('16', plain,
% 0.45/0.65      (((v2_struct_0 @ sk_A)
% 0.45/0.65        | ((u1_struct_0 @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 0.45/0.65            = (u1_struct_0 @ sk_A)))),
% 0.45/0.65      inference('demod', [status(thm)], ['13', '14', '15'])).
% 0.45/0.65  thf('17', plain, (~ (v2_struct_0 @ sk_A)),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('18', plain,
% 0.45/0.65      (((u1_struct_0 @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 0.45/0.65         = (u1_struct_0 @ sk_A))),
% 0.45/0.65      inference('clc', [status(thm)], ['16', '17'])).
% 0.45/0.65  thf('19', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf(d11_tmap_1, axiom,
% 0.45/0.65    (![A:$i]:
% 0.45/0.65     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.45/0.65       ( ![B:$i]:
% 0.45/0.65         ( ( m1_pre_topc @ B @ A ) =>
% 0.45/0.65           ( ![C:$i]:
% 0.45/0.65             ( ( ( v1_pre_topc @ C ) & ( v2_pre_topc @ C ) & 
% 0.45/0.65                 ( l1_pre_topc @ C ) ) =>
% 0.45/0.65               ( ( ( C ) = ( k8_tmap_1 @ A @ B ) ) <=>
% 0.45/0.65                 ( ![D:$i]:
% 0.45/0.65                   ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.45/0.65                     ( ( ( D ) = ( u1_struct_0 @ B ) ) =>
% 0.45/0.65                       ( ( C ) = ( k6_tmap_1 @ A @ D ) ) ) ) ) ) ) ) ) ) ))).
% 0.45/0.65  thf('20', plain,
% 0.45/0.65      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.45/0.65         (~ (m1_pre_topc @ X8 @ X9)
% 0.45/0.65          | ((sk_D @ X10 @ X8 @ X9) = (u1_struct_0 @ X8))
% 0.45/0.65          | ((X10) = (k8_tmap_1 @ X9 @ X8))
% 0.45/0.65          | ~ (l1_pre_topc @ X10)
% 0.45/0.65          | ~ (v2_pre_topc @ X10)
% 0.45/0.65          | ~ (v1_pre_topc @ X10)
% 0.45/0.65          | ~ (l1_pre_topc @ X9)
% 0.45/0.65          | ~ (v2_pre_topc @ X9)
% 0.45/0.65          | (v2_struct_0 @ X9))),
% 0.45/0.65      inference('cnf', [status(esa)], [d11_tmap_1])).
% 0.45/0.65  thf('21', plain,
% 0.45/0.65      (![X0 : $i]:
% 0.45/0.65         ((v2_struct_0 @ sk_A)
% 0.45/0.65          | ~ (v2_pre_topc @ sk_A)
% 0.45/0.65          | ~ (l1_pre_topc @ sk_A)
% 0.45/0.65          | ~ (v1_pre_topc @ X0)
% 0.45/0.65          | ~ (v2_pre_topc @ X0)
% 0.45/0.65          | ~ (l1_pre_topc @ X0)
% 0.45/0.65          | ((X0) = (k8_tmap_1 @ sk_A @ sk_B))
% 0.45/0.65          | ((sk_D @ X0 @ sk_B @ sk_A) = (u1_struct_0 @ sk_B)))),
% 0.45/0.65      inference('sup-', [status(thm)], ['19', '20'])).
% 0.45/0.65  thf('22', plain, ((v2_pre_topc @ sk_A)),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('23', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('24', plain,
% 0.45/0.65      (![X0 : $i]:
% 0.45/0.65         ((v2_struct_0 @ sk_A)
% 0.45/0.65          | ~ (v1_pre_topc @ X0)
% 0.45/0.65          | ~ (v2_pre_topc @ X0)
% 0.45/0.65          | ~ (l1_pre_topc @ X0)
% 0.45/0.65          | ((X0) = (k8_tmap_1 @ sk_A @ sk_B))
% 0.45/0.65          | ((sk_D @ X0 @ sk_B @ sk_A) = (u1_struct_0 @ sk_B)))),
% 0.45/0.65      inference('demod', [status(thm)], ['21', '22', '23'])).
% 0.45/0.65  thf('25', plain,
% 0.45/0.65      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.45/0.65         (~ (m1_pre_topc @ X8 @ X9)
% 0.45/0.65          | ((X10) != (k6_tmap_1 @ X9 @ (sk_D @ X10 @ X8 @ X9)))
% 0.45/0.65          | ((X10) = (k8_tmap_1 @ X9 @ X8))
% 0.45/0.65          | ~ (l1_pre_topc @ X10)
% 0.45/0.65          | ~ (v2_pre_topc @ X10)
% 0.45/0.65          | ~ (v1_pre_topc @ X10)
% 0.45/0.65          | ~ (l1_pre_topc @ X9)
% 0.45/0.65          | ~ (v2_pre_topc @ X9)
% 0.45/0.65          | (v2_struct_0 @ X9))),
% 0.45/0.65      inference('cnf', [status(esa)], [d11_tmap_1])).
% 0.45/0.65  thf('26', plain,
% 0.45/0.65      (![X0 : $i]:
% 0.45/0.65         (((X0) != (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 0.45/0.65          | ((X0) = (k8_tmap_1 @ sk_A @ sk_B))
% 0.45/0.65          | ~ (l1_pre_topc @ X0)
% 0.45/0.65          | ~ (v2_pre_topc @ X0)
% 0.45/0.65          | ~ (v1_pre_topc @ X0)
% 0.45/0.65          | (v2_struct_0 @ sk_A)
% 0.45/0.65          | (v2_struct_0 @ sk_A)
% 0.45/0.65          | ~ (v2_pre_topc @ sk_A)
% 0.45/0.65          | ~ (l1_pre_topc @ sk_A)
% 0.45/0.65          | ~ (v1_pre_topc @ X0)
% 0.45/0.65          | ~ (v2_pre_topc @ X0)
% 0.45/0.65          | ~ (l1_pre_topc @ X0)
% 0.45/0.65          | ((X0) = (k8_tmap_1 @ sk_A @ sk_B))
% 0.45/0.65          | ~ (m1_pre_topc @ sk_B @ sk_A))),
% 0.45/0.65      inference('sup-', [status(thm)], ['24', '25'])).
% 0.45/0.65  thf('27', plain, ((v2_pre_topc @ sk_A)),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('28', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('29', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('30', plain,
% 0.45/0.65      (![X0 : $i]:
% 0.45/0.65         (((X0) != (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 0.45/0.65          | ((X0) = (k8_tmap_1 @ sk_A @ sk_B))
% 0.45/0.65          | ~ (l1_pre_topc @ X0)
% 0.45/0.65          | ~ (v2_pre_topc @ X0)
% 0.45/0.65          | ~ (v1_pre_topc @ X0)
% 0.45/0.65          | (v2_struct_0 @ sk_A)
% 0.45/0.65          | (v2_struct_0 @ sk_A)
% 0.45/0.65          | ~ (v1_pre_topc @ X0)
% 0.45/0.65          | ~ (v2_pre_topc @ X0)
% 0.45/0.65          | ~ (l1_pre_topc @ X0)
% 0.45/0.65          | ((X0) = (k8_tmap_1 @ sk_A @ sk_B)))),
% 0.45/0.65      inference('demod', [status(thm)], ['26', '27', '28', '29'])).
% 0.45/0.65  thf('31', plain,
% 0.45/0.65      (((v2_struct_0 @ sk_A)
% 0.45/0.65        | ~ (v1_pre_topc @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 0.45/0.65        | ~ (v2_pre_topc @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 0.45/0.65        | ~ (l1_pre_topc @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 0.45/0.65        | ((k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B))
% 0.45/0.65            = (k8_tmap_1 @ sk_A @ sk_B)))),
% 0.45/0.65      inference('simplify', [status(thm)], ['30'])).
% 0.45/0.65  thf('32', plain,
% 0.45/0.65      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.45/0.65        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.65      inference('demod', [status(thm)], ['9', '10'])).
% 0.45/0.65  thf(dt_k6_tmap_1, axiom,
% 0.45/0.65    (![A:$i,B:$i]:
% 0.45/0.65     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.45/0.65         ( l1_pre_topc @ A ) & 
% 0.45/0.65         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.45/0.65       ( ( v1_pre_topc @ ( k6_tmap_1 @ A @ B ) ) & 
% 0.45/0.65         ( v2_pre_topc @ ( k6_tmap_1 @ A @ B ) ) & 
% 0.45/0.65         ( l1_pre_topc @ ( k6_tmap_1 @ A @ B ) ) ) ))).
% 0.45/0.65  thf('33', plain,
% 0.45/0.65      (![X19 : $i, X20 : $i]:
% 0.45/0.65         (~ (l1_pre_topc @ X19)
% 0.45/0.65          | ~ (v2_pre_topc @ X19)
% 0.45/0.65          | (v2_struct_0 @ X19)
% 0.45/0.65          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.45/0.65          | (l1_pre_topc @ (k6_tmap_1 @ X19 @ X20)))),
% 0.45/0.65      inference('cnf', [status(esa)], [dt_k6_tmap_1])).
% 0.45/0.65  thf('34', plain,
% 0.45/0.65      (((l1_pre_topc @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 0.45/0.65        | (v2_struct_0 @ sk_A)
% 0.45/0.65        | ~ (v2_pre_topc @ sk_A)
% 0.45/0.65        | ~ (l1_pre_topc @ sk_A))),
% 0.45/0.65      inference('sup-', [status(thm)], ['32', '33'])).
% 0.45/0.65  thf('35', plain, ((v2_pre_topc @ sk_A)),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('36', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('37', plain,
% 0.45/0.65      (((l1_pre_topc @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 0.45/0.65        | (v2_struct_0 @ sk_A))),
% 0.45/0.65      inference('demod', [status(thm)], ['34', '35', '36'])).
% 0.45/0.65  thf('38', plain, (~ (v2_struct_0 @ sk_A)),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('39', plain, ((l1_pre_topc @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))),
% 0.45/0.65      inference('clc', [status(thm)], ['37', '38'])).
% 0.45/0.65  thf('40', plain,
% 0.45/0.65      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.45/0.65        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.65      inference('demod', [status(thm)], ['9', '10'])).
% 0.45/0.65  thf('41', plain,
% 0.45/0.65      (![X19 : $i, X20 : $i]:
% 0.45/0.65         (~ (l1_pre_topc @ X19)
% 0.45/0.65          | ~ (v2_pre_topc @ X19)
% 0.45/0.65          | (v2_struct_0 @ X19)
% 0.45/0.65          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.45/0.65          | (v2_pre_topc @ (k6_tmap_1 @ X19 @ X20)))),
% 0.45/0.65      inference('cnf', [status(esa)], [dt_k6_tmap_1])).
% 0.45/0.65  thf('42', plain,
% 0.45/0.65      (((v2_pre_topc @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 0.45/0.65        | (v2_struct_0 @ sk_A)
% 0.45/0.65        | ~ (v2_pre_topc @ sk_A)
% 0.45/0.65        | ~ (l1_pre_topc @ sk_A))),
% 0.45/0.65      inference('sup-', [status(thm)], ['40', '41'])).
% 0.45/0.65  thf('43', plain, ((v2_pre_topc @ sk_A)),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('44', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('45', plain,
% 0.45/0.65      (((v2_pre_topc @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 0.45/0.65        | (v2_struct_0 @ sk_A))),
% 0.45/0.65      inference('demod', [status(thm)], ['42', '43', '44'])).
% 0.45/0.65  thf('46', plain, (~ (v2_struct_0 @ sk_A)),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('47', plain, ((v2_pre_topc @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))),
% 0.45/0.65      inference('clc', [status(thm)], ['45', '46'])).
% 0.45/0.65  thf('48', plain,
% 0.45/0.65      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.45/0.65        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.65      inference('demod', [status(thm)], ['9', '10'])).
% 0.45/0.65  thf('49', plain,
% 0.45/0.65      (![X19 : $i, X20 : $i]:
% 0.45/0.65         (~ (l1_pre_topc @ X19)
% 0.45/0.65          | ~ (v2_pre_topc @ X19)
% 0.45/0.65          | (v2_struct_0 @ X19)
% 0.45/0.65          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.45/0.65          | (v1_pre_topc @ (k6_tmap_1 @ X19 @ X20)))),
% 0.45/0.65      inference('cnf', [status(esa)], [dt_k6_tmap_1])).
% 0.45/0.65  thf('50', plain,
% 0.45/0.65      (((v1_pre_topc @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 0.45/0.65        | (v2_struct_0 @ sk_A)
% 0.45/0.65        | ~ (v2_pre_topc @ sk_A)
% 0.45/0.65        | ~ (l1_pre_topc @ sk_A))),
% 0.45/0.65      inference('sup-', [status(thm)], ['48', '49'])).
% 0.45/0.65  thf('51', plain, ((v2_pre_topc @ sk_A)),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('52', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('53', plain,
% 0.45/0.65      (((v1_pre_topc @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 0.45/0.65        | (v2_struct_0 @ sk_A))),
% 0.45/0.65      inference('demod', [status(thm)], ['50', '51', '52'])).
% 0.45/0.65  thf('54', plain, (~ (v2_struct_0 @ sk_A)),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('55', plain, ((v1_pre_topc @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))),
% 0.45/0.65      inference('clc', [status(thm)], ['53', '54'])).
% 0.45/0.65  thf('56', plain,
% 0.45/0.65      (((v2_struct_0 @ sk_A)
% 0.45/0.65        | ((k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B))
% 0.45/0.65            = (k8_tmap_1 @ sk_A @ sk_B)))),
% 0.45/0.65      inference('simplify_reflect+', [status(thm)], ['31', '39', '47', '55'])).
% 0.45/0.65  thf('57', plain, (~ (v2_struct_0 @ sk_A)),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('58', plain,
% 0.45/0.65      (((k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)) = (k8_tmap_1 @ sk_A @ sk_B))),
% 0.45/0.65      inference('clc', [status(thm)], ['56', '57'])).
% 0.45/0.65  thf('59', plain,
% 0.45/0.65      (((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 0.45/0.65      inference('demod', [status(thm)], ['18', '58'])).
% 0.45/0.65  thf('60', plain,
% 0.45/0.65      (((k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)) = (k8_tmap_1 @ sk_A @ sk_B))),
% 0.45/0.65      inference('clc', [status(thm)], ['56', '57'])).
% 0.45/0.65  thf('61', plain,
% 0.45/0.65      (((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 0.45/0.65      inference('demod', [status(thm)], ['18', '58'])).
% 0.45/0.65  thf('62', plain,
% 0.45/0.65      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.45/0.65        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.65      inference('demod', [status(thm)], ['9', '10'])).
% 0.45/0.65  thf('63', plain,
% 0.45/0.65      (((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 0.45/0.65      inference('demod', [status(thm)], ['18', '58'])).
% 0.45/0.65  thf('64', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf(dt_k9_tmap_1, axiom,
% 0.45/0.65    (![A:$i,B:$i]:
% 0.45/0.65     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.45/0.65         ( l1_pre_topc @ A ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.45/0.65       ( ( v1_funct_1 @ ( k9_tmap_1 @ A @ B ) ) & 
% 0.45/0.65         ( v1_funct_2 @
% 0.45/0.65           ( k9_tmap_1 @ A @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.45/0.65           ( u1_struct_0 @ ( k8_tmap_1 @ A @ B ) ) ) & 
% 0.45/0.65         ( m1_subset_1 @
% 0.45/0.65           ( k9_tmap_1 @ A @ B ) @ 
% 0.45/0.65           ( k1_zfmisc_1 @
% 0.45/0.65             ( k2_zfmisc_1 @
% 0.45/0.65               ( u1_struct_0 @ A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ A @ B ) ) ) ) ) ) ))).
% 0.45/0.65  thf('65', plain,
% 0.45/0.65      (![X23 : $i, X24 : $i]:
% 0.45/0.65         (~ (l1_pre_topc @ X23)
% 0.45/0.65          | ~ (v2_pre_topc @ X23)
% 0.45/0.65          | (v2_struct_0 @ X23)
% 0.45/0.65          | ~ (m1_pre_topc @ X24 @ X23)
% 0.45/0.65          | (v1_funct_2 @ (k9_tmap_1 @ X23 @ X24) @ (u1_struct_0 @ X23) @ 
% 0.45/0.65             (u1_struct_0 @ (k8_tmap_1 @ X23 @ X24))))),
% 0.45/0.65      inference('cnf', [status(esa)], [dt_k9_tmap_1])).
% 0.45/0.65  thf('66', plain,
% 0.45/0.65      (((v1_funct_2 @ (k9_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.45/0.65         (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))
% 0.45/0.65        | (v2_struct_0 @ sk_A)
% 0.45/0.65        | ~ (v2_pre_topc @ sk_A)
% 0.45/0.65        | ~ (l1_pre_topc @ sk_A))),
% 0.45/0.65      inference('sup-', [status(thm)], ['64', '65'])).
% 0.45/0.65  thf('67', plain, ((v2_pre_topc @ sk_A)),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('68', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('69', plain,
% 0.45/0.65      (((v1_funct_2 @ (k9_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.45/0.65         (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))
% 0.45/0.65        | (v2_struct_0 @ sk_A))),
% 0.45/0.65      inference('demod', [status(thm)], ['66', '67', '68'])).
% 0.45/0.65  thf('70', plain, (~ (v2_struct_0 @ sk_A)),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('71', plain,
% 0.45/0.65      ((v1_funct_2 @ (k9_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.45/0.65        (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))),
% 0.45/0.65      inference('clc', [status(thm)], ['69', '70'])).
% 0.45/0.65  thf('72', plain,
% 0.45/0.65      (((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 0.45/0.65      inference('demod', [status(thm)], ['18', '58'])).
% 0.45/0.65  thf('73', plain,
% 0.45/0.65      ((v1_funct_2 @ (k9_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.45/0.65        (u1_struct_0 @ sk_A))),
% 0.45/0.65      inference('demod', [status(thm)], ['71', '72'])).
% 0.45/0.65  thf('74', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('75', plain,
% 0.45/0.65      (![X23 : $i, X24 : $i]:
% 0.45/0.65         (~ (l1_pre_topc @ X23)
% 0.45/0.65          | ~ (v2_pre_topc @ X23)
% 0.45/0.65          | (v2_struct_0 @ X23)
% 0.45/0.65          | ~ (m1_pre_topc @ X24 @ X23)
% 0.45/0.65          | (v1_funct_1 @ (k9_tmap_1 @ X23 @ X24)))),
% 0.45/0.65      inference('cnf', [status(esa)], [dt_k9_tmap_1])).
% 0.45/0.65  thf('76', plain,
% 0.45/0.65      (((v1_funct_1 @ (k9_tmap_1 @ sk_A @ sk_B))
% 0.45/0.65        | (v2_struct_0 @ sk_A)
% 0.45/0.65        | ~ (v2_pre_topc @ sk_A)
% 0.45/0.65        | ~ (l1_pre_topc @ sk_A))),
% 0.45/0.65      inference('sup-', [status(thm)], ['74', '75'])).
% 0.45/0.65  thf('77', plain, ((v2_pre_topc @ sk_A)),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('78', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('79', plain,
% 0.45/0.65      (((v1_funct_1 @ (k9_tmap_1 @ sk_A @ sk_B)) | (v2_struct_0 @ sk_A))),
% 0.45/0.65      inference('demod', [status(thm)], ['76', '77', '78'])).
% 0.45/0.65  thf('80', plain, (~ (v2_struct_0 @ sk_A)),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('81', plain, ((v1_funct_1 @ (k9_tmap_1 @ sk_A @ sk_B))),
% 0.45/0.65      inference('clc', [status(thm)], ['79', '80'])).
% 0.45/0.65  thf('82', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('83', plain, ((v2_pre_topc @ sk_A)),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('84', plain,
% 0.45/0.65      ((((r1_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.45/0.65          (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.45/0.65          (k9_tmap_1 @ sk_A @ sk_B) @ (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 0.45/0.65         | (v2_struct_0 @ sk_A)))
% 0.45/0.65         <= (((m1_subset_1 @ (k9_tmap_1 @ sk_A @ sk_B) @ 
% 0.45/0.65               (k1_zfmisc_1 @ 
% 0.45/0.65                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.45/0.65                 (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))))))),
% 0.45/0.65      inference('demod', [status(thm)],
% 0.45/0.65                ['5', '6', '59', '60', '61', '62', '63', '73', '81', '82', '83'])).
% 0.45/0.65  thf('85', plain, (~ (v2_struct_0 @ sk_A)),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('86', plain,
% 0.45/0.65      (((r1_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.45/0.65         (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.45/0.65         (k9_tmap_1 @ sk_A @ sk_B) @ (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B))))
% 0.45/0.65         <= (((m1_subset_1 @ (k9_tmap_1 @ sk_A @ sk_B) @ 
% 0.45/0.65               (k1_zfmisc_1 @ 
% 0.45/0.65                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.45/0.65                 (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))))))),
% 0.45/0.65      inference('clc', [status(thm)], ['84', '85'])).
% 0.45/0.65  thf('87', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('88', plain,
% 0.45/0.65      (![X23 : $i, X24 : $i]:
% 0.45/0.65         (~ (l1_pre_topc @ X23)
% 0.45/0.65          | ~ (v2_pre_topc @ X23)
% 0.45/0.65          | (v2_struct_0 @ X23)
% 0.45/0.65          | ~ (m1_pre_topc @ X24 @ X23)
% 0.45/0.65          | (m1_subset_1 @ (k9_tmap_1 @ X23 @ X24) @ 
% 0.45/0.65             (k1_zfmisc_1 @ 
% 0.45/0.65              (k2_zfmisc_1 @ (u1_struct_0 @ X23) @ 
% 0.45/0.65               (u1_struct_0 @ (k8_tmap_1 @ X23 @ X24))))))),
% 0.45/0.65      inference('cnf', [status(esa)], [dt_k9_tmap_1])).
% 0.45/0.65  thf('89', plain,
% 0.45/0.65      (((m1_subset_1 @ (k9_tmap_1 @ sk_A @ sk_B) @ 
% 0.45/0.65         (k1_zfmisc_1 @ 
% 0.45/0.65          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.45/0.65           (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))))
% 0.45/0.65        | (v2_struct_0 @ sk_A)
% 0.45/0.65        | ~ (v2_pre_topc @ sk_A)
% 0.45/0.65        | ~ (l1_pre_topc @ sk_A))),
% 0.45/0.65      inference('sup-', [status(thm)], ['87', '88'])).
% 0.45/0.65  thf('90', plain,
% 0.45/0.65      (((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 0.45/0.65      inference('demod', [status(thm)], ['18', '58'])).
% 0.45/0.65  thf('91', plain, ((v2_pre_topc @ sk_A)),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('92', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('93', plain,
% 0.45/0.65      (((m1_subset_1 @ (k9_tmap_1 @ sk_A @ sk_B) @ 
% 0.45/0.65         (k1_zfmisc_1 @ 
% 0.45/0.65          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))))
% 0.45/0.65        | (v2_struct_0 @ sk_A))),
% 0.45/0.65      inference('demod', [status(thm)], ['89', '90', '91', '92'])).
% 0.45/0.65  thf('94', plain, (~ (v2_struct_0 @ sk_A)),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('95', plain,
% 0.45/0.65      ((m1_subset_1 @ (k9_tmap_1 @ sk_A @ sk_B) @ 
% 0.45/0.65        (k1_zfmisc_1 @ 
% 0.45/0.65         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))))),
% 0.45/0.65      inference('clc', [status(thm)], ['93', '94'])).
% 0.45/0.65  thf('96', plain,
% 0.45/0.65      (((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 0.45/0.65      inference('demod', [status(thm)], ['18', '58'])).
% 0.45/0.65  thf('97', plain,
% 0.45/0.65      ((~ (m1_subset_1 @ (k9_tmap_1 @ sk_A @ sk_B) @ 
% 0.45/0.65           (k1_zfmisc_1 @ 
% 0.45/0.65            (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.45/0.65             (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))))
% 0.45/0.65        | ~ (v5_pre_topc @ (k9_tmap_1 @ sk_A @ sk_B) @ sk_A @ 
% 0.45/0.65             (k8_tmap_1 @ sk_A @ sk_B))
% 0.45/0.65        | ~ (v1_funct_2 @ (k9_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.45/0.65             (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))
% 0.45/0.65        | ~ (v1_funct_1 @ (k9_tmap_1 @ sk_A @ sk_B))
% 0.45/0.65        | ~ (m1_pre_topc @ sk_B @ sk_A)
% 0.45/0.65        | ~ (v1_tsep_1 @ sk_B @ sk_A))),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('98', plain,
% 0.45/0.65      ((~ (m1_subset_1 @ (k9_tmap_1 @ sk_A @ sk_B) @ 
% 0.45/0.65           (k1_zfmisc_1 @ 
% 0.45/0.65            (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.45/0.65             (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B))))))
% 0.45/0.65         <= (~
% 0.45/0.65             ((m1_subset_1 @ (k9_tmap_1 @ sk_A @ sk_B) @ 
% 0.45/0.65               (k1_zfmisc_1 @ 
% 0.45/0.65                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.45/0.65                 (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))))))),
% 0.45/0.65      inference('split', [status(esa)], ['97'])).
% 0.45/0.65  thf('99', plain,
% 0.45/0.65      ((~ (m1_subset_1 @ (k9_tmap_1 @ sk_A @ sk_B) @ 
% 0.45/0.65           (k1_zfmisc_1 @ 
% 0.45/0.65            (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A)))))
% 0.45/0.65         <= (~
% 0.45/0.65             ((m1_subset_1 @ (k9_tmap_1 @ sk_A @ sk_B) @ 
% 0.45/0.65               (k1_zfmisc_1 @ 
% 0.45/0.65                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.45/0.65                 (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))))))),
% 0.45/0.65      inference('sup-', [status(thm)], ['96', '98'])).
% 0.45/0.65  thf('100', plain,
% 0.45/0.65      (((m1_subset_1 @ (k9_tmap_1 @ sk_A @ sk_B) @ 
% 0.45/0.65         (k1_zfmisc_1 @ 
% 0.45/0.65          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.45/0.65           (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B))))))),
% 0.45/0.65      inference('sup-', [status(thm)], ['95', '99'])).
% 0.45/0.65  thf('101', plain,
% 0.45/0.65      (((m1_subset_1 @ (k9_tmap_1 @ sk_A @ sk_B) @ 
% 0.45/0.65         (k1_zfmisc_1 @ 
% 0.45/0.65          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.45/0.65           (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B))))))),
% 0.45/0.65      inference('sat_resolution*', [status(thm)], ['100'])).
% 0.45/0.65  thf('102', plain,
% 0.45/0.65      ((r1_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.45/0.65        (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.45/0.65        (k9_tmap_1 @ sk_A @ sk_B) @ (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))),
% 0.45/0.65      inference('simpl_trail', [status(thm)], ['86', '101'])).
% 0.45/0.65  thf('103', plain,
% 0.45/0.65      (((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 0.45/0.65      inference('demod', [status(thm)], ['18', '58'])).
% 0.45/0.65  thf('104', plain,
% 0.45/0.65      (((m1_subset_1 @ (k9_tmap_1 @ sk_A @ sk_B) @ 
% 0.45/0.65         (k1_zfmisc_1 @ 
% 0.45/0.65          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.45/0.65           (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B))))))
% 0.45/0.65         <= (((m1_subset_1 @ (k9_tmap_1 @ sk_A @ sk_B) @ 
% 0.45/0.65               (k1_zfmisc_1 @ 
% 0.45/0.65                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.45/0.65                 (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))))))),
% 0.45/0.65      inference('split', [status(esa)], ['1'])).
% 0.45/0.65  thf('105', plain,
% 0.45/0.65      (((m1_subset_1 @ (k9_tmap_1 @ sk_A @ sk_B) @ 
% 0.45/0.65         (k1_zfmisc_1 @ 
% 0.45/0.65          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A)))))
% 0.45/0.65         <= (((m1_subset_1 @ (k9_tmap_1 @ sk_A @ sk_B) @ 
% 0.45/0.65               (k1_zfmisc_1 @ 
% 0.45/0.65                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.45/0.65                 (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))))))),
% 0.45/0.65      inference('sup+', [status(thm)], ['103', '104'])).
% 0.45/0.65  thf(redefinition_r1_funct_2, axiom,
% 0.45/0.65    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.45/0.65     ( ( ( ~( v1_xboole_0 @ B ) ) & ( ~( v1_xboole_0 @ D ) ) & 
% 0.45/0.65         ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ A @ B ) & 
% 0.45/0.65         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.45/0.65         ( v1_funct_1 @ F ) & ( v1_funct_2 @ F @ C @ D ) & 
% 0.45/0.65         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.45/0.65       ( ( r1_funct_2 @ A @ B @ C @ D @ E @ F ) <=> ( ( E ) = ( F ) ) ) ))).
% 0.45/0.65  thf('106', plain,
% 0.45/0.65      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.45/0.65         (~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X4)))
% 0.45/0.65          | ~ (v1_funct_2 @ X2 @ X3 @ X4)
% 0.45/0.65          | ~ (v1_funct_1 @ X2)
% 0.45/0.65          | (v1_xboole_0 @ X5)
% 0.45/0.65          | (v1_xboole_0 @ X4)
% 0.45/0.65          | ~ (v1_funct_1 @ X6)
% 0.45/0.65          | ~ (v1_funct_2 @ X6 @ X7 @ X5)
% 0.45/0.65          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X5)))
% 0.45/0.65          | ((X2) = (X6))
% 0.45/0.65          | ~ (r1_funct_2 @ X3 @ X4 @ X7 @ X5 @ X2 @ X6))),
% 0.45/0.65      inference('cnf', [status(esa)], [redefinition_r1_funct_2])).
% 0.45/0.65  thf('107', plain,
% 0.45/0.65      ((![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.65          (~ (r1_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ X2 @ 
% 0.45/0.65              X1 @ (k9_tmap_1 @ sk_A @ sk_B) @ X0)
% 0.45/0.65           | ((k9_tmap_1 @ sk_A @ sk_B) = (X0))
% 0.45/0.65           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.45/0.65           | ~ (v1_funct_2 @ X0 @ X2 @ X1)
% 0.45/0.65           | ~ (v1_funct_1 @ X0)
% 0.45/0.65           | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.45/0.65           | (v1_xboole_0 @ X1)
% 0.45/0.65           | ~ (v1_funct_1 @ (k9_tmap_1 @ sk_A @ sk_B))
% 0.45/0.65           | ~ (v1_funct_2 @ (k9_tmap_1 @ sk_A @ sk_B) @ 
% 0.45/0.65                (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))))
% 0.45/0.65         <= (((m1_subset_1 @ (k9_tmap_1 @ sk_A @ sk_B) @ 
% 0.45/0.65               (k1_zfmisc_1 @ 
% 0.45/0.65                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.45/0.65                 (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))))))),
% 0.45/0.65      inference('sup-', [status(thm)], ['105', '106'])).
% 0.45/0.65  thf('108', plain, ((v1_funct_1 @ (k9_tmap_1 @ sk_A @ sk_B))),
% 0.45/0.65      inference('clc', [status(thm)], ['79', '80'])).
% 0.45/0.65  thf('109', plain,
% 0.45/0.65      ((v1_funct_2 @ (k9_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.45/0.65        (u1_struct_0 @ sk_A))),
% 0.45/0.65      inference('demod', [status(thm)], ['71', '72'])).
% 0.45/0.65  thf('110', plain,
% 0.45/0.65      ((![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.65          (~ (r1_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ X2 @ 
% 0.45/0.65              X1 @ (k9_tmap_1 @ sk_A @ sk_B) @ X0)
% 0.45/0.65           | ((k9_tmap_1 @ sk_A @ sk_B) = (X0))
% 0.45/0.65           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.45/0.65           | ~ (v1_funct_2 @ X0 @ X2 @ X1)
% 0.45/0.65           | ~ (v1_funct_1 @ X0)
% 0.45/0.65           | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.45/0.65           | (v1_xboole_0 @ X1)))
% 0.45/0.65         <= (((m1_subset_1 @ (k9_tmap_1 @ sk_A @ sk_B) @ 
% 0.45/0.65               (k1_zfmisc_1 @ 
% 0.45/0.65                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.45/0.65                 (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))))))),
% 0.45/0.65      inference('demod', [status(thm)], ['107', '108', '109'])).
% 0.45/0.65  thf('111', plain,
% 0.45/0.65      (((m1_subset_1 @ (k9_tmap_1 @ sk_A @ sk_B) @ 
% 0.45/0.65         (k1_zfmisc_1 @ 
% 0.45/0.65          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.45/0.65           (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B))))))),
% 0.45/0.65      inference('sat_resolution*', [status(thm)], ['100'])).
% 0.45/0.65  thf('112', plain,
% 0.45/0.65      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.65         (~ (r1_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ X2 @ 
% 0.45/0.65             X1 @ (k9_tmap_1 @ sk_A @ sk_B) @ X0)
% 0.45/0.65          | ((k9_tmap_1 @ sk_A @ sk_B) = (X0))
% 0.45/0.65          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.45/0.65          | ~ (v1_funct_2 @ X0 @ X2 @ X1)
% 0.45/0.65          | ~ (v1_funct_1 @ X0)
% 0.45/0.65          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.45/0.65          | (v1_xboole_0 @ X1))),
% 0.45/0.65      inference('simpl_trail', [status(thm)], ['110', '111'])).
% 0.45/0.65  thf('113', plain,
% 0.45/0.65      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.45/0.65        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.45/0.65        | ~ (v1_funct_1 @ (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 0.45/0.65        | ~ (v1_funct_2 @ (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)) @ 
% 0.45/0.65             (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.45/0.65        | ~ (m1_subset_1 @ (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)) @ 
% 0.45/0.65             (k1_zfmisc_1 @ 
% 0.45/0.65              (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))))
% 0.45/0.65        | ((k9_tmap_1 @ sk_A @ sk_B)
% 0.45/0.65            = (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B))))),
% 0.45/0.65      inference('sup-', [status(thm)], ['102', '112'])).
% 0.45/0.65  thf('114', plain,
% 0.45/0.65      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.45/0.65        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.65      inference('demod', [status(thm)], ['9', '10'])).
% 0.45/0.65  thf(dt_k7_tmap_1, axiom,
% 0.45/0.65    (![A:$i,B:$i]:
% 0.45/0.65     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.45/0.65         ( l1_pre_topc @ A ) & 
% 0.45/0.65         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.45/0.65       ( ( v1_funct_1 @ ( k7_tmap_1 @ A @ B ) ) & 
% 0.45/0.65         ( v1_funct_2 @
% 0.45/0.65           ( k7_tmap_1 @ A @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.45/0.65           ( u1_struct_0 @ ( k6_tmap_1 @ A @ B ) ) ) & 
% 0.45/0.65         ( m1_subset_1 @
% 0.45/0.65           ( k7_tmap_1 @ A @ B ) @ 
% 0.45/0.65           ( k1_zfmisc_1 @
% 0.45/0.65             ( k2_zfmisc_1 @
% 0.45/0.65               ( u1_struct_0 @ A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ A @ B ) ) ) ) ) ) ))).
% 0.45/0.65  thf('115', plain,
% 0.45/0.65      (![X21 : $i, X22 : $i]:
% 0.45/0.65         (~ (l1_pre_topc @ X21)
% 0.45/0.65          | ~ (v2_pre_topc @ X21)
% 0.45/0.65          | (v2_struct_0 @ X21)
% 0.45/0.65          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.45/0.65          | (v1_funct_1 @ (k7_tmap_1 @ X21 @ X22)))),
% 0.45/0.65      inference('cnf', [status(esa)], [dt_k7_tmap_1])).
% 0.45/0.65  thf('116', plain,
% 0.45/0.65      (((v1_funct_1 @ (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 0.45/0.65        | (v2_struct_0 @ sk_A)
% 0.45/0.65        | ~ (v2_pre_topc @ sk_A)
% 0.45/0.65        | ~ (l1_pre_topc @ sk_A))),
% 0.45/0.65      inference('sup-', [status(thm)], ['114', '115'])).
% 0.45/0.65  thf('117', plain, ((v2_pre_topc @ sk_A)),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('118', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('119', plain,
% 0.45/0.65      (((v1_funct_1 @ (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 0.45/0.65        | (v2_struct_0 @ sk_A))),
% 0.45/0.65      inference('demod', [status(thm)], ['116', '117', '118'])).
% 0.45/0.65  thf('120', plain, (~ (v2_struct_0 @ sk_A)),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('121', plain, ((v1_funct_1 @ (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))),
% 0.45/0.65      inference('clc', [status(thm)], ['119', '120'])).
% 0.45/0.65  thf('122', plain,
% 0.45/0.65      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.45/0.65        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.65      inference('demod', [status(thm)], ['9', '10'])).
% 0.45/0.65  thf('123', plain,
% 0.45/0.65      (![X21 : $i, X22 : $i]:
% 0.45/0.65         (~ (l1_pre_topc @ X21)
% 0.45/0.65          | ~ (v2_pre_topc @ X21)
% 0.45/0.65          | (v2_struct_0 @ X21)
% 0.45/0.65          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.45/0.65          | (v1_funct_2 @ (k7_tmap_1 @ X21 @ X22) @ (u1_struct_0 @ X21) @ 
% 0.45/0.65             (u1_struct_0 @ (k6_tmap_1 @ X21 @ X22))))),
% 0.45/0.65      inference('cnf', [status(esa)], [dt_k7_tmap_1])).
% 0.45/0.65  thf('124', plain,
% 0.45/0.65      (((v1_funct_2 @ (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)) @ 
% 0.45/0.65         (u1_struct_0 @ sk_A) @ 
% 0.45/0.65         (u1_struct_0 @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B))))
% 0.45/0.65        | (v2_struct_0 @ sk_A)
% 0.45/0.65        | ~ (v2_pre_topc @ sk_A)
% 0.45/0.65        | ~ (l1_pre_topc @ sk_A))),
% 0.45/0.65      inference('sup-', [status(thm)], ['122', '123'])).
% 0.45/0.65  thf('125', plain,
% 0.45/0.65      (((k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)) = (k8_tmap_1 @ sk_A @ sk_B))),
% 0.45/0.65      inference('clc', [status(thm)], ['56', '57'])).
% 0.45/0.65  thf('126', plain,
% 0.45/0.65      (((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 0.45/0.65      inference('demod', [status(thm)], ['18', '58'])).
% 0.45/0.65  thf('127', plain, ((v2_pre_topc @ sk_A)),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('128', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('129', plain,
% 0.45/0.65      (((v1_funct_2 @ (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)) @ 
% 0.45/0.65         (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.45/0.65        | (v2_struct_0 @ sk_A))),
% 0.45/0.65      inference('demod', [status(thm)], ['124', '125', '126', '127', '128'])).
% 0.45/0.65  thf('130', plain, (~ (v2_struct_0 @ sk_A)),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('131', plain,
% 0.45/0.65      ((v1_funct_2 @ (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)) @ 
% 0.45/0.65        (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))),
% 0.45/0.65      inference('clc', [status(thm)], ['129', '130'])).
% 0.45/0.65  thf('132', plain,
% 0.45/0.65      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.45/0.65        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.65      inference('demod', [status(thm)], ['9', '10'])).
% 0.45/0.65  thf('133', plain,
% 0.45/0.65      (![X21 : $i, X22 : $i]:
% 0.45/0.65         (~ (l1_pre_topc @ X21)
% 0.45/0.65          | ~ (v2_pre_topc @ X21)
% 0.45/0.65          | (v2_struct_0 @ X21)
% 0.45/0.65          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.45/0.65          | (m1_subset_1 @ (k7_tmap_1 @ X21 @ X22) @ 
% 0.45/0.65             (k1_zfmisc_1 @ 
% 0.45/0.65              (k2_zfmisc_1 @ (u1_struct_0 @ X21) @ 
% 0.45/0.65               (u1_struct_0 @ (k6_tmap_1 @ X21 @ X22))))))),
% 0.45/0.65      inference('cnf', [status(esa)], [dt_k7_tmap_1])).
% 0.45/0.65  thf('134', plain,
% 0.45/0.65      (((m1_subset_1 @ (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)) @ 
% 0.45/0.65         (k1_zfmisc_1 @ 
% 0.45/0.65          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.45/0.65           (u1_struct_0 @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B))))))
% 0.45/0.65        | (v2_struct_0 @ sk_A)
% 0.45/0.65        | ~ (v2_pre_topc @ sk_A)
% 0.45/0.65        | ~ (l1_pre_topc @ sk_A))),
% 0.45/0.65      inference('sup-', [status(thm)], ['132', '133'])).
% 0.45/0.65  thf('135', plain,
% 0.45/0.65      (((k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)) = (k8_tmap_1 @ sk_A @ sk_B))),
% 0.45/0.65      inference('clc', [status(thm)], ['56', '57'])).
% 0.45/0.65  thf('136', plain,
% 0.45/0.65      (((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 0.45/0.65      inference('demod', [status(thm)], ['18', '58'])).
% 0.45/0.65  thf('137', plain, ((v2_pre_topc @ sk_A)),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('138', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('139', plain,
% 0.45/0.65      (((m1_subset_1 @ (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)) @ 
% 0.45/0.65         (k1_zfmisc_1 @ 
% 0.45/0.65          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))))
% 0.45/0.65        | (v2_struct_0 @ sk_A))),
% 0.45/0.65      inference('demod', [status(thm)], ['134', '135', '136', '137', '138'])).
% 0.45/0.65  thf('140', plain, (~ (v2_struct_0 @ sk_A)),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('141', plain,
% 0.45/0.65      ((m1_subset_1 @ (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)) @ 
% 0.45/0.65        (k1_zfmisc_1 @ 
% 0.45/0.65         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))))),
% 0.45/0.65      inference('clc', [status(thm)], ['139', '140'])).
% 0.45/0.65  thf('142', plain,
% 0.45/0.65      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.45/0.65        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.45/0.65        | ((k9_tmap_1 @ sk_A @ sk_B)
% 0.45/0.65            = (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B))))),
% 0.45/0.65      inference('demod', [status(thm)], ['113', '121', '131', '141'])).
% 0.45/0.65  thf('143', plain,
% 0.45/0.65      ((((k9_tmap_1 @ sk_A @ sk_B) = (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 0.45/0.65        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.65      inference('simplify', [status(thm)], ['142'])).
% 0.45/0.65  thf('144', plain,
% 0.45/0.65      (((k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)) = (k8_tmap_1 @ sk_A @ sk_B))),
% 0.45/0.65      inference('clc', [status(thm)], ['56', '57'])).
% 0.45/0.65  thf(t113_tmap_1, axiom,
% 0.45/0.65    (![A:$i]:
% 0.45/0.65     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.45/0.65       ( ![B:$i]:
% 0.45/0.65         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.45/0.65           ( ( v3_pre_topc @ B @ A ) <=>
% 0.45/0.65             ( ( v1_funct_1 @ ( k7_tmap_1 @ A @ B ) ) & 
% 0.45/0.65               ( v1_funct_2 @
% 0.45/0.65                 ( k7_tmap_1 @ A @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.45/0.65                 ( u1_struct_0 @ ( k6_tmap_1 @ A @ B ) ) ) & 
% 0.45/0.65               ( v5_pre_topc @
% 0.45/0.65                 ( k7_tmap_1 @ A @ B ) @ A @ ( k6_tmap_1 @ A @ B ) ) & 
% 0.45/0.65               ( m1_subset_1 @
% 0.45/0.65                 ( k7_tmap_1 @ A @ B ) @ 
% 0.45/0.65                 ( k1_zfmisc_1 @
% 0.45/0.65                   ( k2_zfmisc_1 @
% 0.45/0.65                     ( u1_struct_0 @ A ) @ 
% 0.45/0.65                     ( u1_struct_0 @ ( k6_tmap_1 @ A @ B ) ) ) ) ) ) ) ) ) ))).
% 0.45/0.65  thf('145', plain,
% 0.45/0.65      (![X27 : $i, X28 : $i]:
% 0.45/0.65         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 0.45/0.65          | ~ (v1_funct_1 @ (k7_tmap_1 @ X28 @ X27))
% 0.45/0.65          | ~ (v1_funct_2 @ (k7_tmap_1 @ X28 @ X27) @ (u1_struct_0 @ X28) @ 
% 0.45/0.65               (u1_struct_0 @ (k6_tmap_1 @ X28 @ X27)))
% 0.45/0.65          | ~ (v5_pre_topc @ (k7_tmap_1 @ X28 @ X27) @ X28 @ 
% 0.45/0.65               (k6_tmap_1 @ X28 @ X27))
% 0.45/0.65          | ~ (m1_subset_1 @ (k7_tmap_1 @ X28 @ X27) @ 
% 0.45/0.65               (k1_zfmisc_1 @ 
% 0.45/0.65                (k2_zfmisc_1 @ (u1_struct_0 @ X28) @ 
% 0.45/0.65                 (u1_struct_0 @ (k6_tmap_1 @ X28 @ X27)))))
% 0.45/0.65          | (v3_pre_topc @ X27 @ X28)
% 0.45/0.65          | ~ (l1_pre_topc @ X28)
% 0.45/0.65          | ~ (v2_pre_topc @ X28)
% 0.45/0.65          | (v2_struct_0 @ X28))),
% 0.45/0.65      inference('cnf', [status(esa)], [t113_tmap_1])).
% 0.45/0.65  thf('146', plain,
% 0.45/0.65      ((~ (m1_subset_1 @ (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)) @ 
% 0.45/0.65           (k1_zfmisc_1 @ 
% 0.45/0.65            (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.45/0.65             (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))))
% 0.45/0.65        | (v2_struct_0 @ sk_A)
% 0.45/0.65        | ~ (v2_pre_topc @ sk_A)
% 0.45/0.65        | ~ (l1_pre_topc @ sk_A)
% 0.45/0.65        | (v3_pre_topc @ (u1_struct_0 @ sk_B) @ sk_A)
% 0.45/0.65        | ~ (v5_pre_topc @ (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)) @ sk_A @ 
% 0.45/0.65             (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 0.45/0.65        | ~ (v1_funct_2 @ (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)) @ 
% 0.45/0.65             (u1_struct_0 @ sk_A) @ 
% 0.45/0.65             (u1_struct_0 @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B))))
% 0.45/0.65        | ~ (v1_funct_1 @ (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 0.45/0.65        | ~ (m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.45/0.65             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.45/0.65      inference('sup-', [status(thm)], ['144', '145'])).
% 0.45/0.65  thf('147', plain,
% 0.45/0.65      (((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 0.45/0.65      inference('demod', [status(thm)], ['18', '58'])).
% 0.45/0.65  thf('148', plain,
% 0.45/0.65      ((m1_subset_1 @ (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)) @ 
% 0.45/0.65        (k1_zfmisc_1 @ 
% 0.45/0.65         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))))),
% 0.45/0.65      inference('clc', [status(thm)], ['139', '140'])).
% 0.45/0.65  thf('149', plain, ((v2_pre_topc @ sk_A)),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('150', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('151', plain,
% 0.45/0.65      (((k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)) = (k8_tmap_1 @ sk_A @ sk_B))),
% 0.45/0.65      inference('clc', [status(thm)], ['56', '57'])).
% 0.45/0.65  thf('152', plain,
% 0.45/0.65      (((k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)) = (k8_tmap_1 @ sk_A @ sk_B))),
% 0.45/0.65      inference('clc', [status(thm)], ['56', '57'])).
% 0.45/0.65  thf('153', plain,
% 0.45/0.65      (((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 0.45/0.65      inference('demod', [status(thm)], ['18', '58'])).
% 0.45/0.65  thf('154', plain,
% 0.45/0.65      ((v1_funct_2 @ (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)) @ 
% 0.45/0.65        (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))),
% 0.45/0.65      inference('clc', [status(thm)], ['129', '130'])).
% 0.45/0.65  thf('155', plain, ((v1_funct_1 @ (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))),
% 0.45/0.65      inference('clc', [status(thm)], ['119', '120'])).
% 0.45/0.65  thf('156', plain,
% 0.45/0.65      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.45/0.65        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.65      inference('demod', [status(thm)], ['9', '10'])).
% 0.45/0.65  thf('157', plain,
% 0.45/0.65      (((v2_struct_0 @ sk_A)
% 0.45/0.65        | (v3_pre_topc @ (u1_struct_0 @ sk_B) @ sk_A)
% 0.45/0.65        | ~ (v5_pre_topc @ (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)) @ sk_A @ 
% 0.45/0.65             (k8_tmap_1 @ sk_A @ sk_B)))),
% 0.45/0.65      inference('demod', [status(thm)],
% 0.45/0.65                ['146', '147', '148', '149', '150', '151', '152', '153', 
% 0.45/0.65                 '154', '155', '156'])).
% 0.45/0.65  thf('158', plain, (~ (v2_struct_0 @ sk_A)),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('159', plain,
% 0.45/0.65      ((~ (v5_pre_topc @ (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)) @ sk_A @ 
% 0.45/0.65           (k8_tmap_1 @ sk_A @ sk_B))
% 0.45/0.65        | (v3_pre_topc @ (u1_struct_0 @ sk_B) @ sk_A))),
% 0.45/0.65      inference('clc', [status(thm)], ['157', '158'])).
% 0.45/0.65  thf('160', plain,
% 0.45/0.65      ((~ (v5_pre_topc @ (k9_tmap_1 @ sk_A @ sk_B) @ sk_A @ 
% 0.45/0.65           (k8_tmap_1 @ sk_A @ sk_B))
% 0.45/0.65        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.45/0.65        | (v3_pre_topc @ (u1_struct_0 @ sk_B) @ sk_A))),
% 0.45/0.65      inference('sup-', [status(thm)], ['143', '159'])).
% 0.45/0.65  thf('161', plain,
% 0.45/0.65      (((v5_pre_topc @ (k9_tmap_1 @ sk_A @ sk_B) @ sk_A @ 
% 0.45/0.65         (k8_tmap_1 @ sk_A @ sk_B))
% 0.45/0.65        | (v1_tsep_1 @ sk_B @ sk_A))),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('162', plain,
% 0.45/0.65      (((v5_pre_topc @ (k9_tmap_1 @ sk_A @ sk_B) @ sk_A @ 
% 0.45/0.65         (k8_tmap_1 @ sk_A @ sk_B)))
% 0.45/0.65         <= (((v5_pre_topc @ (k9_tmap_1 @ sk_A @ sk_B) @ sk_A @ 
% 0.45/0.65               (k8_tmap_1 @ sk_A @ sk_B))))),
% 0.45/0.65      inference('split', [status(esa)], ['161'])).
% 0.45/0.65  thf('163', plain,
% 0.45/0.65      (~ ((v1_tsep_1 @ sk_B @ sk_A)) | 
% 0.45/0.65       ~
% 0.45/0.65       ((v5_pre_topc @ (k9_tmap_1 @ sk_A @ sk_B) @ sk_A @ 
% 0.45/0.65         (k8_tmap_1 @ sk_A @ sk_B))) | 
% 0.45/0.65       ~ ((m1_pre_topc @ sk_B @ sk_A)) | 
% 0.45/0.65       ~ ((v1_funct_1 @ (k9_tmap_1 @ sk_A @ sk_B))) | 
% 0.45/0.65       ~
% 0.45/0.65       ((v1_funct_2 @ (k9_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.45/0.65         (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))) | 
% 0.45/0.65       ~
% 0.45/0.65       ((m1_subset_1 @ (k9_tmap_1 @ sk_A @ sk_B) @ 
% 0.45/0.65         (k1_zfmisc_1 @ 
% 0.45/0.65          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.45/0.65           (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B))))))),
% 0.45/0.65      inference('split', [status(esa)], ['97'])).
% 0.45/0.65  thf('164', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('165', plain,
% 0.45/0.65      ((~ (m1_pre_topc @ sk_B @ sk_A)) <= (~ ((m1_pre_topc @ sk_B @ sk_A)))),
% 0.45/0.65      inference('split', [status(esa)], ['97'])).
% 0.45/0.65  thf('166', plain, (((m1_pre_topc @ sk_B @ sk_A))),
% 0.45/0.65      inference('sup-', [status(thm)], ['164', '165'])).
% 0.45/0.65  thf('167', plain, ((v1_funct_1 @ (k9_tmap_1 @ sk_A @ sk_B))),
% 0.45/0.65      inference('clc', [status(thm)], ['79', '80'])).
% 0.45/0.65  thf('168', plain,
% 0.45/0.65      ((~ (v1_funct_1 @ (k9_tmap_1 @ sk_A @ sk_B)))
% 0.45/0.65         <= (~ ((v1_funct_1 @ (k9_tmap_1 @ sk_A @ sk_B))))),
% 0.45/0.65      inference('split', [status(esa)], ['97'])).
% 0.45/0.65  thf('169', plain, (((v1_funct_1 @ (k9_tmap_1 @ sk_A @ sk_B)))),
% 0.45/0.65      inference('sup-', [status(thm)], ['167', '168'])).
% 0.45/0.65  thf('170', plain,
% 0.45/0.65      ((v1_funct_2 @ (k9_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.45/0.65        (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))),
% 0.45/0.65      inference('clc', [status(thm)], ['69', '70'])).
% 0.45/0.65  thf('171', plain,
% 0.45/0.65      ((~ (v1_funct_2 @ (k9_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.45/0.65           (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B))))
% 0.45/0.65         <= (~
% 0.45/0.65             ((v1_funct_2 @ (k9_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.45/0.65               (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))))),
% 0.45/0.65      inference('split', [status(esa)], ['97'])).
% 0.45/0.65  thf('172', plain,
% 0.45/0.65      (((v1_funct_2 @ (k9_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.45/0.65         (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B))))),
% 0.45/0.65      inference('sup-', [status(thm)], ['170', '171'])).
% 0.45/0.65  thf('173', plain,
% 0.45/0.65      ((((k9_tmap_1 @ sk_A @ sk_B) = (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 0.45/0.65        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.65      inference('simplify', [status(thm)], ['142'])).
% 0.45/0.65  thf('174', plain,
% 0.45/0.65      (((v1_funct_1 @ (k9_tmap_1 @ sk_A @ sk_B)) | (v1_tsep_1 @ sk_B @ sk_A))),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('175', plain,
% 0.45/0.65      (((v1_tsep_1 @ sk_B @ sk_A)) <= (((v1_tsep_1 @ sk_B @ sk_A)))),
% 0.45/0.65      inference('split', [status(esa)], ['174'])).
% 0.45/0.65  thf('176', plain,
% 0.45/0.65      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.45/0.65        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.65      inference('demod', [status(thm)], ['9', '10'])).
% 0.45/0.65  thf(d1_tsep_1, axiom,
% 0.45/0.65    (![A:$i]:
% 0.45/0.65     ( ( l1_pre_topc @ A ) =>
% 0.45/0.65       ( ![B:$i]:
% 0.45/0.65         ( ( m1_pre_topc @ B @ A ) =>
% 0.45/0.65           ( ( v1_tsep_1 @ B @ A ) <=>
% 0.45/0.65             ( ![C:$i]:
% 0.45/0.65               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.45/0.65                 ( ( ( C ) = ( u1_struct_0 @ B ) ) => ( v3_pre_topc @ C @ A ) ) ) ) ) ) ) ))).
% 0.45/0.65  thf('177', plain,
% 0.45/0.65      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.45/0.65         (~ (m1_pre_topc @ X16 @ X17)
% 0.45/0.65          | ~ (v1_tsep_1 @ X16 @ X17)
% 0.45/0.65          | ((X18) != (u1_struct_0 @ X16))
% 0.45/0.65          | (v3_pre_topc @ X18 @ X17)
% 0.45/0.65          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.45/0.65          | ~ (l1_pre_topc @ X17))),
% 0.45/0.65      inference('cnf', [status(esa)], [d1_tsep_1])).
% 0.45/0.65  thf('178', plain,
% 0.45/0.65      (![X16 : $i, X17 : $i]:
% 0.45/0.65         (~ (l1_pre_topc @ X17)
% 0.45/0.65          | ~ (m1_subset_1 @ (u1_struct_0 @ X16) @ 
% 0.45/0.65               (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.45/0.65          | (v3_pre_topc @ (u1_struct_0 @ X16) @ X17)
% 0.45/0.65          | ~ (v1_tsep_1 @ X16 @ X17)
% 0.45/0.65          | ~ (m1_pre_topc @ X16 @ X17))),
% 0.45/0.65      inference('simplify', [status(thm)], ['177'])).
% 0.45/0.65  thf('179', plain,
% 0.45/0.65      ((~ (m1_pre_topc @ sk_B @ sk_A)
% 0.45/0.65        | ~ (v1_tsep_1 @ sk_B @ sk_A)
% 0.45/0.65        | (v3_pre_topc @ (u1_struct_0 @ sk_B) @ sk_A)
% 0.45/0.65        | ~ (l1_pre_topc @ sk_A))),
% 0.45/0.65      inference('sup-', [status(thm)], ['176', '178'])).
% 0.45/0.65  thf('180', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('181', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('182', plain,
% 0.45/0.65      ((~ (v1_tsep_1 @ sk_B @ sk_A)
% 0.45/0.65        | (v3_pre_topc @ (u1_struct_0 @ sk_B) @ sk_A))),
% 0.45/0.65      inference('demod', [status(thm)], ['179', '180', '181'])).
% 0.45/0.65  thf('183', plain,
% 0.45/0.65      (((v3_pre_topc @ (u1_struct_0 @ sk_B) @ sk_A))
% 0.45/0.65         <= (((v1_tsep_1 @ sk_B @ sk_A)))),
% 0.45/0.65      inference('sup-', [status(thm)], ['175', '182'])).
% 0.45/0.65  thf('184', plain,
% 0.45/0.65      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.45/0.65        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.65      inference('demod', [status(thm)], ['9', '10'])).
% 0.45/0.65  thf('185', plain,
% 0.45/0.65      (![X27 : $i, X28 : $i]:
% 0.45/0.65         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 0.45/0.65          | ~ (v3_pre_topc @ X27 @ X28)
% 0.45/0.65          | (v5_pre_topc @ (k7_tmap_1 @ X28 @ X27) @ X28 @ 
% 0.45/0.65             (k6_tmap_1 @ X28 @ X27))
% 0.45/0.65          | ~ (l1_pre_topc @ X28)
% 0.45/0.65          | ~ (v2_pre_topc @ X28)
% 0.45/0.65          | (v2_struct_0 @ X28))),
% 0.45/0.65      inference('cnf', [status(esa)], [t113_tmap_1])).
% 0.45/0.65  thf('186', plain,
% 0.45/0.65      (((v2_struct_0 @ sk_A)
% 0.45/0.65        | ~ (v2_pre_topc @ sk_A)
% 0.45/0.65        | ~ (l1_pre_topc @ sk_A)
% 0.45/0.65        | (v5_pre_topc @ (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)) @ sk_A @ 
% 0.45/0.65           (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 0.45/0.65        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_B) @ sk_A))),
% 0.45/0.65      inference('sup-', [status(thm)], ['184', '185'])).
% 0.45/0.65  thf('187', plain, ((v2_pre_topc @ sk_A)),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('188', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('189', plain,
% 0.45/0.65      (((k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)) = (k8_tmap_1 @ sk_A @ sk_B))),
% 0.45/0.65      inference('clc', [status(thm)], ['56', '57'])).
% 0.45/0.65  thf('190', plain,
% 0.45/0.65      (((v2_struct_0 @ sk_A)
% 0.45/0.65        | (v5_pre_topc @ (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)) @ sk_A @ 
% 0.45/0.65           (k8_tmap_1 @ sk_A @ sk_B))
% 0.45/0.65        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_B) @ sk_A))),
% 0.45/0.65      inference('demod', [status(thm)], ['186', '187', '188', '189'])).
% 0.45/0.65  thf('191', plain, (~ (v2_struct_0 @ sk_A)),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('192', plain,
% 0.45/0.65      ((~ (v3_pre_topc @ (u1_struct_0 @ sk_B) @ sk_A)
% 0.45/0.65        | (v5_pre_topc @ (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)) @ sk_A @ 
% 0.45/0.65           (k8_tmap_1 @ sk_A @ sk_B)))),
% 0.45/0.65      inference('clc', [status(thm)], ['190', '191'])).
% 0.45/0.65  thf('193', plain,
% 0.45/0.65      (((v5_pre_topc @ (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)) @ sk_A @ 
% 0.45/0.65         (k8_tmap_1 @ sk_A @ sk_B))) <= (((v1_tsep_1 @ sk_B @ sk_A)))),
% 0.45/0.65      inference('sup-', [status(thm)], ['183', '192'])).
% 0.45/0.65  thf('194', plain,
% 0.45/0.65      ((((v5_pre_topc @ (k9_tmap_1 @ sk_A @ sk_B) @ sk_A @ 
% 0.45/0.65          (k8_tmap_1 @ sk_A @ sk_B))
% 0.45/0.65         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.45/0.65         <= (((v1_tsep_1 @ sk_B @ sk_A)))),
% 0.45/0.65      inference('sup+', [status(thm)], ['173', '193'])).
% 0.45/0.65  thf('195', plain,
% 0.45/0.65      ((~ (v5_pre_topc @ (k9_tmap_1 @ sk_A @ sk_B) @ sk_A @ 
% 0.45/0.65           (k8_tmap_1 @ sk_A @ sk_B)))
% 0.45/0.65         <= (~
% 0.45/0.65             ((v5_pre_topc @ (k9_tmap_1 @ sk_A @ sk_B) @ sk_A @ 
% 0.45/0.65               (k8_tmap_1 @ sk_A @ sk_B))))),
% 0.45/0.65      inference('split', [status(esa)], ['97'])).
% 0.45/0.65  thf('196', plain,
% 0.45/0.65      (((v1_xboole_0 @ (u1_struct_0 @ sk_A)))
% 0.45/0.65         <= (~
% 0.45/0.65             ((v5_pre_topc @ (k9_tmap_1 @ sk_A @ sk_B) @ sk_A @ 
% 0.45/0.65               (k8_tmap_1 @ sk_A @ sk_B))) & 
% 0.45/0.65             ((v1_tsep_1 @ sk_B @ sk_A)))),
% 0.45/0.65      inference('sup-', [status(thm)], ['194', '195'])).
% 0.45/0.65  thf(fc2_struct_0, axiom,
% 0.45/0.65    (![A:$i]:
% 0.45/0.65     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.45/0.65       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.45/0.65  thf('197', plain,
% 0.45/0.65      (![X1 : $i]:
% 0.45/0.65         (~ (v1_xboole_0 @ (u1_struct_0 @ X1))
% 0.45/0.65          | ~ (l1_struct_0 @ X1)
% 0.45/0.65          | (v2_struct_0 @ X1))),
% 0.45/0.65      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.45/0.65  thf('198', plain,
% 0.45/0.65      ((((v2_struct_0 @ sk_A) | ~ (l1_struct_0 @ sk_A)))
% 0.45/0.65         <= (~
% 0.45/0.65             ((v5_pre_topc @ (k9_tmap_1 @ sk_A @ sk_B) @ sk_A @ 
% 0.45/0.65               (k8_tmap_1 @ sk_A @ sk_B))) & 
% 0.45/0.65             ((v1_tsep_1 @ sk_B @ sk_A)))),
% 0.45/0.65      inference('sup-', [status(thm)], ['196', '197'])).
% 0.45/0.65  thf('199', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf(dt_l1_pre_topc, axiom,
% 0.45/0.65    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.45/0.65  thf('200', plain, (![X0 : $i]: ((l1_struct_0 @ X0) | ~ (l1_pre_topc @ X0))),
% 0.45/0.65      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.45/0.65  thf('201', plain, ((l1_struct_0 @ sk_A)),
% 0.45/0.65      inference('sup-', [status(thm)], ['199', '200'])).
% 0.45/0.65  thf('202', plain,
% 0.45/0.65      (((v2_struct_0 @ sk_A))
% 0.45/0.65         <= (~
% 0.45/0.65             ((v5_pre_topc @ (k9_tmap_1 @ sk_A @ sk_B) @ sk_A @ 
% 0.45/0.66               (k8_tmap_1 @ sk_A @ sk_B))) & 
% 0.45/0.66             ((v1_tsep_1 @ sk_B @ sk_A)))),
% 0.45/0.66      inference('demod', [status(thm)], ['198', '201'])).
% 0.45/0.66  thf('203', plain, (~ (v2_struct_0 @ sk_A)),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('204', plain,
% 0.45/0.66      (((v5_pre_topc @ (k9_tmap_1 @ sk_A @ sk_B) @ sk_A @ 
% 0.45/0.66         (k8_tmap_1 @ sk_A @ sk_B))) | 
% 0.45/0.66       ~ ((v1_tsep_1 @ sk_B @ sk_A))),
% 0.45/0.66      inference('sup-', [status(thm)], ['202', '203'])).
% 0.45/0.66  thf('205', plain,
% 0.45/0.66      (((v5_pre_topc @ (k9_tmap_1 @ sk_A @ sk_B) @ sk_A @ 
% 0.45/0.66         (k8_tmap_1 @ sk_A @ sk_B))) | 
% 0.45/0.66       ((v1_tsep_1 @ sk_B @ sk_A))),
% 0.45/0.66      inference('split', [status(esa)], ['161'])).
% 0.45/0.66  thf('206', plain,
% 0.45/0.66      (((v5_pre_topc @ (k9_tmap_1 @ sk_A @ sk_B) @ sk_A @ 
% 0.45/0.66         (k8_tmap_1 @ sk_A @ sk_B)))),
% 0.45/0.66      inference('sat_resolution*', [status(thm)],
% 0.45/0.66                ['163', '166', '169', '172', '100', '204', '205'])).
% 0.45/0.66  thf('207', plain,
% 0.45/0.66      ((v5_pre_topc @ (k9_tmap_1 @ sk_A @ sk_B) @ sk_A @ 
% 0.45/0.66        (k8_tmap_1 @ sk_A @ sk_B))),
% 0.45/0.66      inference('simpl_trail', [status(thm)], ['162', '206'])).
% 0.45/0.66  thf('208', plain,
% 0.45/0.66      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.45/0.66        | (v3_pre_topc @ (u1_struct_0 @ sk_B) @ sk_A))),
% 0.45/0.66      inference('demod', [status(thm)], ['160', '207'])).
% 0.45/0.66  thf('209', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('210', plain,
% 0.45/0.66      (![X16 : $i, X17 : $i]:
% 0.45/0.66         (~ (m1_pre_topc @ X16 @ X17)
% 0.45/0.66          | ((sk_C @ X16 @ X17) = (u1_struct_0 @ X16))
% 0.45/0.66          | (v1_tsep_1 @ X16 @ X17)
% 0.45/0.66          | ~ (l1_pre_topc @ X17))),
% 0.45/0.66      inference('cnf', [status(esa)], [d1_tsep_1])).
% 0.45/0.66  thf('211', plain,
% 0.45/0.66      ((~ (l1_pre_topc @ sk_A)
% 0.45/0.66        | (v1_tsep_1 @ sk_B @ sk_A)
% 0.45/0.66        | ((sk_C @ sk_B @ sk_A) = (u1_struct_0 @ sk_B)))),
% 0.45/0.66      inference('sup-', [status(thm)], ['209', '210'])).
% 0.45/0.66  thf('212', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('213', plain,
% 0.45/0.66      (((v1_tsep_1 @ sk_B @ sk_A)
% 0.45/0.66        | ((sk_C @ sk_B @ sk_A) = (u1_struct_0 @ sk_B)))),
% 0.45/0.66      inference('demod', [status(thm)], ['211', '212'])).
% 0.45/0.66  thf('214', plain,
% 0.45/0.66      ((~ (v1_tsep_1 @ sk_B @ sk_A)) <= (~ ((v1_tsep_1 @ sk_B @ sk_A)))),
% 0.45/0.66      inference('split', [status(esa)], ['97'])).
% 0.45/0.66  thf('215', plain,
% 0.45/0.66      ((((sk_C @ sk_B @ sk_A) = (u1_struct_0 @ sk_B)))
% 0.45/0.66         <= (~ ((v1_tsep_1 @ sk_B @ sk_A)))),
% 0.45/0.66      inference('sup-', [status(thm)], ['213', '214'])).
% 0.45/0.66  thf('216', plain,
% 0.45/0.66      (![X16 : $i, X17 : $i]:
% 0.45/0.66         (~ (m1_pre_topc @ X16 @ X17)
% 0.45/0.66          | ~ (v3_pre_topc @ (sk_C @ X16 @ X17) @ X17)
% 0.45/0.66          | (v1_tsep_1 @ X16 @ X17)
% 0.45/0.66          | ~ (l1_pre_topc @ X17))),
% 0.45/0.66      inference('cnf', [status(esa)], [d1_tsep_1])).
% 0.45/0.66  thf('217', plain,
% 0.45/0.66      (((~ (v3_pre_topc @ (u1_struct_0 @ sk_B) @ sk_A)
% 0.45/0.66         | ~ (l1_pre_topc @ sk_A)
% 0.45/0.66         | (v1_tsep_1 @ sk_B @ sk_A)
% 0.45/0.66         | ~ (m1_pre_topc @ sk_B @ sk_A))) <= (~ ((v1_tsep_1 @ sk_B @ sk_A)))),
% 0.45/0.66      inference('sup-', [status(thm)], ['215', '216'])).
% 0.45/0.66  thf('218', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('219', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('220', plain,
% 0.45/0.66      (((~ (v3_pre_topc @ (u1_struct_0 @ sk_B) @ sk_A)
% 0.45/0.66         | (v1_tsep_1 @ sk_B @ sk_A))) <= (~ ((v1_tsep_1 @ sk_B @ sk_A)))),
% 0.45/0.66      inference('demod', [status(thm)], ['217', '218', '219'])).
% 0.45/0.66  thf('221', plain,
% 0.45/0.66      ((~ (v1_tsep_1 @ sk_B @ sk_A)) <= (~ ((v1_tsep_1 @ sk_B @ sk_A)))),
% 0.45/0.66      inference('split', [status(esa)], ['97'])).
% 0.45/0.66  thf('222', plain,
% 0.45/0.66      ((~ (v3_pre_topc @ (u1_struct_0 @ sk_B) @ sk_A))
% 0.45/0.66         <= (~ ((v1_tsep_1 @ sk_B @ sk_A)))),
% 0.45/0.66      inference('clc', [status(thm)], ['220', '221'])).
% 0.45/0.66  thf('223', plain, (~ ((v1_tsep_1 @ sk_B @ sk_A))),
% 0.45/0.66      inference('sat_resolution*', [status(thm)],
% 0.45/0.66                ['163', '166', '169', '172', '100', '204'])).
% 0.45/0.66  thf('224', plain, (~ (v3_pre_topc @ (u1_struct_0 @ sk_B) @ sk_A)),
% 0.45/0.66      inference('simpl_trail', [status(thm)], ['222', '223'])).
% 0.45/0.66  thf('225', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.45/0.66      inference('clc', [status(thm)], ['208', '224'])).
% 0.45/0.66  thf('226', plain,
% 0.45/0.66      (![X1 : $i]:
% 0.45/0.66         (~ (v1_xboole_0 @ (u1_struct_0 @ X1))
% 0.45/0.66          | ~ (l1_struct_0 @ X1)
% 0.45/0.66          | (v2_struct_0 @ X1))),
% 0.45/0.66      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.45/0.66  thf('227', plain, (((v2_struct_0 @ sk_A) | ~ (l1_struct_0 @ sk_A))),
% 0.45/0.66      inference('sup-', [status(thm)], ['225', '226'])).
% 0.45/0.66  thf('228', plain, ((l1_struct_0 @ sk_A)),
% 0.45/0.66      inference('sup-', [status(thm)], ['199', '200'])).
% 0.45/0.66  thf('229', plain, ((v2_struct_0 @ sk_A)),
% 0.45/0.66      inference('demod', [status(thm)], ['227', '228'])).
% 0.45/0.66  thf('230', plain, ($false), inference('demod', [status(thm)], ['0', '229'])).
% 0.45/0.66  
% 0.45/0.66  % SZS output end Refutation
% 0.45/0.66  
% 0.45/0.66  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
