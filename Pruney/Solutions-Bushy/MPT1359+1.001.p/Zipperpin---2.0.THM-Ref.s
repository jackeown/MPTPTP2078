%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT1359+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.3Eg6rv02XM

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:53:33 EST 2020

% Result     : Theorem 39.13s
% Output     : Refutation 39.13s
% Verified   : 
% Statistics : Number of formulae       :  237 ( 541 expanded)
%              Number of leaves         :   25 ( 152 expanded)
%              Depth                    :   38
%              Number of atoms          : 6042 (15887 expanded)
%              Number of equality atoms :  596 (1413 expanded)
%              Maximal formula depth    :   21 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_finset_1_type,type,(
    v1_finset_1: $i > $o )).

thf(v2_tops_2_type,type,(
    v2_tops_2: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v3_finset_1_type,type,(
    v3_finset_1: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v1_compts_1_type,type,(
    v1_compts_1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k6_setfam_1_type,type,(
    k6_setfam_1: $i > $i > $i )).

thf(t14_compts_1,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( ( v1_compts_1 @ A )
      <=> ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
           => ~ ( ( B != k1_xboole_0 )
                & ( v2_tops_2 @ B @ A )
                & ( ( k6_setfam_1 @ ( u1_struct_0 @ A ) @ B )
                  = k1_xboole_0 )
                & ! [C: $i] :
                    ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
                   => ~ ( ( C != k1_xboole_0 )
                        & ( r1_tarski @ C @ B )
                        & ( v1_finset_1 @ C )
                        & ( ( k6_setfam_1 @ ( u1_struct_0 @ A ) @ C )
                          = k1_xboole_0 ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ( ( v1_compts_1 @ A )
        <=> ! [B: $i] :
              ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
             => ~ ( ( B != k1_xboole_0 )
                  & ( v2_tops_2 @ B @ A )
                  & ( ( k6_setfam_1 @ ( u1_struct_0 @ A ) @ B )
                    = k1_xboole_0 )
                  & ! [C: $i] :
                      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
                     => ~ ( ( C != k1_xboole_0 )
                          & ( r1_tarski @ C @ B )
                          & ( v1_finset_1 @ C )
                          & ( ( k6_setfam_1 @ ( u1_struct_0 @ A ) @ C )
                            = k1_xboole_0 ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t14_compts_1])).

thf('0',plain,(
    ! [X14: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
      | ( X14 = k1_xboole_0 )
      | ~ ( v2_tops_2 @ X14 @ sk_A )
      | ( ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ X14 )
       != k1_xboole_0 )
      | ( ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ X14 ) )
        = k1_xboole_0 )
      | ( v1_compts_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ! [X14: $i] :
        ( ( X14 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
        | ~ ( v2_tops_2 @ X14 @ sk_A )
        | ( ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ X14 )
         != k1_xboole_0 )
        | ( ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ X14 ) )
          = k1_xboole_0 ) )
    | ( v1_compts_1 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    ! [X14: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
      | ( X14 = k1_xboole_0 )
      | ~ ( v2_tops_2 @ X14 @ sk_A )
      | ( ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ X14 )
       != k1_xboole_0 )
      | ( v1_finset_1 @ ( sk_C @ X14 ) )
      | ( v1_compts_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ! [X14: $i] :
        ( ( X14 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
        | ~ ( v2_tops_2 @ X14 @ sk_A )
        | ( ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ X14 )
         != k1_xboole_0 )
        | ( v1_finset_1 @ ( sk_C @ X14 ) ) )
    | ( v1_compts_1 @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,(
    ! [X14: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
      | ( X14 = k1_xboole_0 )
      | ~ ( v2_tops_2 @ X14 @ sk_A )
      | ( ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ X14 )
       != k1_xboole_0 )
      | ( ( sk_C @ X14 )
       != k1_xboole_0 )
      | ( v1_compts_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ! [X14: $i] :
        ( ( X14 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
        | ~ ( v2_tops_2 @ X14 @ sk_A )
        | ( ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ X14 )
         != k1_xboole_0 )
        | ( ( sk_C @ X14 )
         != k1_xboole_0 ) )
    | ( v1_compts_1 @ sk_A ) ),
    inference(split,[status(esa)],['4'])).

thf('6',plain,(
    ! [X13: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
      | ( X13 = k1_xboole_0 )
      | ~ ( r1_tarski @ X13 @ sk_B_2 )
      | ~ ( v1_finset_1 @ X13 )
      | ( ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ X13 )
       != k1_xboole_0 )
      | ~ ( v1_compts_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ! [X13: $i] :
        ( ( X13 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
        | ~ ( r1_tarski @ X13 @ sk_B_2 )
        | ~ ( v1_finset_1 @ X13 )
        | ( ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ X13 )
         != k1_xboole_0 ) )
    | ~ ( v1_compts_1 @ sk_A ) ),
    inference(split,[status(esa)],['6'])).

thf('8',plain,
    ( ( ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 )
      = k1_xboole_0 )
    | ~ ( v1_compts_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 )
      = k1_xboole_0 )
    | ~ ( v1_compts_1 @ sk_A ) ),
    inference(split,[status(esa)],['8'])).

thf('10',plain,
    ( ( v2_tops_2 @ sk_B_2 @ sk_A )
    | ~ ( v1_compts_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( v2_tops_2 @ sk_B_2 @ sk_A )
    | ~ ( v1_compts_1 @ sk_A ) ),
    inference(split,[status(esa)],['10'])).

thf('12',plain,
    ( ( sk_B_2 != k1_xboole_0 )
    | ~ ( v1_compts_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,
    ( ( sk_B_2 != k1_xboole_0 )
    | ~ ( v1_compts_1 @ sk_A ) ),
    inference(split,[status(esa)],['12'])).

thf('14',plain,
    ( ( m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
    | ~ ( v1_compts_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ( m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
    | ~ ( v1_compts_1 @ sk_A ) ),
    inference(split,[status(esa)],['14'])).

thf('16',plain,
    ( ( m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ( m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(split,[status(esa)],['14'])).

thf(redefinition_k6_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k6_setfam_1 @ A @ B )
        = ( k1_setfam_1 @ B ) ) ) )).

thf('17',plain,(
    ! [X3: $i,X4: $i] :
      ( ( ( k6_setfam_1 @ X4 @ X3 )
        = ( k1_setfam_1 @ X3 ) )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X4 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_setfam_1])).

thf('18',plain,
    ( ( ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 )
      = ( k1_setfam_1 @ sk_B_2 ) )
   <= ( m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( ( ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 )
      = k1_xboole_0 )
   <= ( ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['8'])).

thf('20',plain,
    ( ( ( k1_setfam_1 @ sk_B_2 )
      = k1_xboole_0 )
   <= ( ( ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 )
        = k1_xboole_0 )
      & ( m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf(d3_finset_1,axiom,(
    ! [A: $i] :
      ( ( v3_finset_1 @ A )
    <=> ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( ( B != k1_xboole_0 )
              & ( r1_tarski @ B @ A )
              & ( v1_finset_1 @ B )
              & ( ( k1_setfam_1 @ B )
                = k1_xboole_0 ) ) ) ) )).

thf('21',plain,(
    ! [X2: $i] :
      ( ( v3_finset_1 @ X2 )
      | ( v1_finset_1 @ ( sk_B @ X2 ) )
      | ( X2 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d3_finset_1])).

thf('22',plain,
    ( ( sk_B_2 != k1_xboole_0 )
   <= ( sk_B_2 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['12'])).

thf('23',plain,
    ( ! [X0: $i] :
        ( ( sk_B_2 != X0 )
        | ( v1_finset_1 @ ( sk_B @ X0 ) )
        | ( v3_finset_1 @ X0 ) )
   <= ( sk_B_2 != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,
    ( ( ( v3_finset_1 @ sk_B_2 )
      | ( v1_finset_1 @ ( sk_B @ sk_B_2 ) ) )
   <= ( sk_B_2 != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,(
    ! [X2: $i] :
      ( ( v3_finset_1 @ X2 )
      | ( r1_tarski @ ( sk_B @ X2 ) @ X2 )
      | ( X2 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d3_finset_1])).

thf('26',plain,
    ( ( m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ( m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(split,[status(esa)],['14'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('27',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r1_tarski @ X10 @ X11 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('28',plain,
    ( ( r1_tarski @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X2: $i] :
      ( ( v3_finset_1 @ X2 )
      | ( r1_tarski @ ( sk_B @ X2 ) @ X2 )
      | ( X2 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d3_finset_1])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('30',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r1_tarski @ X7 @ X8 )
      | ~ ( r1_tarski @ X8 @ X9 )
      | ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( v3_finset_1 @ X0 )
      | ( r1_tarski @ ( sk_B @ X0 ) @ X1 )
      | ~ ( r1_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,
    ( ( ( r1_tarski @ ( sk_B @ sk_B_2 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v3_finset_1 @ sk_B_2 )
      | ( sk_B_2 = k1_xboole_0 ) )
   <= ( m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['28','31'])).

thf('33',plain,(
    ! [X10: $i,X12: $i] :
      ( ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X12 ) )
      | ~ ( r1_tarski @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('34',plain,
    ( ( ( sk_B_2 = k1_xboole_0 )
      | ( v3_finset_1 @ sk_B_2 )
      | ( m1_subset_1 @ ( sk_B @ sk_B_2 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) )
   <= ( m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X3: $i,X4: $i] :
      ( ( ( k6_setfam_1 @ X4 @ X3 )
        = ( k1_setfam_1 @ X3 ) )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X4 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_setfam_1])).

thf('36',plain,
    ( ( ( v3_finset_1 @ sk_B_2 )
      | ( sk_B_2 = k1_xboole_0 )
      | ( ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ sk_B_2 ) )
        = ( k1_setfam_1 @ ( sk_B @ sk_B_2 ) ) ) )
   <= ( m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,
    ( ( ( sk_B_2 = k1_xboole_0 )
      | ( v3_finset_1 @ sk_B_2 )
      | ( m1_subset_1 @ ( sk_B @ sk_B_2 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) )
   <= ( m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('38',plain,
    ( ! [X13: $i] :
        ( ( X13 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
        | ~ ( r1_tarski @ X13 @ sk_B_2 )
        | ~ ( v1_finset_1 @ X13 )
        | ( ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ X13 )
         != k1_xboole_0 ) )
   <= ! [X13: $i] :
        ( ( X13 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
        | ~ ( r1_tarski @ X13 @ sk_B_2 )
        | ~ ( v1_finset_1 @ X13 )
        | ( ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ X13 )
         != k1_xboole_0 ) ) ),
    inference(split,[status(esa)],['6'])).

thf('39',plain,
    ( ( ( v3_finset_1 @ sk_B_2 )
      | ( sk_B_2 = k1_xboole_0 )
      | ( ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ sk_B_2 ) )
       != k1_xboole_0 )
      | ~ ( v1_finset_1 @ ( sk_B @ sk_B_2 ) )
      | ~ ( r1_tarski @ ( sk_B @ sk_B_2 ) @ sk_B_2 )
      | ( ( sk_B @ sk_B_2 )
        = k1_xboole_0 ) )
   <= ( ! [X13: $i] :
          ( ( X13 = k1_xboole_0 )
          | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
          | ~ ( r1_tarski @ X13 @ sk_B_2 )
          | ~ ( v1_finset_1 @ X13 )
          | ( ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ X13 )
           != k1_xboole_0 ) )
      & ( m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,
    ( ( ( ( k1_setfam_1 @ ( sk_B @ sk_B_2 ) )
       != k1_xboole_0 )
      | ( sk_B_2 = k1_xboole_0 )
      | ( v3_finset_1 @ sk_B_2 )
      | ( ( sk_B @ sk_B_2 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ ( sk_B @ sk_B_2 ) @ sk_B_2 )
      | ~ ( v1_finset_1 @ ( sk_B @ sk_B_2 ) )
      | ( sk_B_2 = k1_xboole_0 )
      | ( v3_finset_1 @ sk_B_2 ) )
   <= ( ! [X13: $i] :
          ( ( X13 = k1_xboole_0 )
          | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
          | ~ ( r1_tarski @ X13 @ sk_B_2 )
          | ~ ( v1_finset_1 @ X13 )
          | ( ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ X13 )
           != k1_xboole_0 ) )
      & ( m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['36','39'])).

thf('41',plain,
    ( ( ~ ( v1_finset_1 @ ( sk_B @ sk_B_2 ) )
      | ~ ( r1_tarski @ ( sk_B @ sk_B_2 ) @ sk_B_2 )
      | ( ( sk_B @ sk_B_2 )
        = k1_xboole_0 )
      | ( v3_finset_1 @ sk_B_2 )
      | ( sk_B_2 = k1_xboole_0 )
      | ( ( k1_setfam_1 @ ( sk_B @ sk_B_2 ) )
       != k1_xboole_0 ) )
   <= ( ! [X13: $i] :
          ( ( X13 = k1_xboole_0 )
          | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
          | ~ ( r1_tarski @ X13 @ sk_B_2 )
          | ~ ( v1_finset_1 @ X13 )
          | ( ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ X13 )
           != k1_xboole_0 ) )
      & ( m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,
    ( ( ( sk_B_2 = k1_xboole_0 )
      | ( v3_finset_1 @ sk_B_2 )
      | ( ( k1_setfam_1 @ ( sk_B @ sk_B_2 ) )
       != k1_xboole_0 )
      | ( sk_B_2 = k1_xboole_0 )
      | ( v3_finset_1 @ sk_B_2 )
      | ( ( sk_B @ sk_B_2 )
        = k1_xboole_0 )
      | ~ ( v1_finset_1 @ ( sk_B @ sk_B_2 ) ) )
   <= ( ! [X13: $i] :
          ( ( X13 = k1_xboole_0 )
          | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
          | ~ ( r1_tarski @ X13 @ sk_B_2 )
          | ~ ( v1_finset_1 @ X13 )
          | ( ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ X13 )
           != k1_xboole_0 ) )
      & ( m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['25','41'])).

thf('43',plain,
    ( ( ~ ( v1_finset_1 @ ( sk_B @ sk_B_2 ) )
      | ( ( sk_B @ sk_B_2 )
        = k1_xboole_0 )
      | ( ( k1_setfam_1 @ ( sk_B @ sk_B_2 ) )
       != k1_xboole_0 )
      | ( v3_finset_1 @ sk_B_2 )
      | ( sk_B_2 = k1_xboole_0 ) )
   <= ( ! [X13: $i] :
          ( ( X13 = k1_xboole_0 )
          | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
          | ~ ( r1_tarski @ X13 @ sk_B_2 )
          | ~ ( v1_finset_1 @ X13 )
          | ( ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ X13 )
           != k1_xboole_0 ) )
      & ( m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ) ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,
    ( ( ( v3_finset_1 @ sk_B_2 )
      | ( sk_B_2 = k1_xboole_0 )
      | ( v3_finset_1 @ sk_B_2 )
      | ( ( k1_setfam_1 @ ( sk_B @ sk_B_2 ) )
       != k1_xboole_0 )
      | ( ( sk_B @ sk_B_2 )
        = k1_xboole_0 ) )
   <= ( ( sk_B_2 != k1_xboole_0 )
      & ! [X13: $i] :
          ( ( X13 = k1_xboole_0 )
          | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
          | ~ ( r1_tarski @ X13 @ sk_B_2 )
          | ~ ( v1_finset_1 @ X13 )
          | ( ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ X13 )
           != k1_xboole_0 ) )
      & ( m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['24','43'])).

thf('45',plain,
    ( ( ( ( sk_B @ sk_B_2 )
        = k1_xboole_0 )
      | ( ( k1_setfam_1 @ ( sk_B @ sk_B_2 ) )
       != k1_xboole_0 )
      | ( sk_B_2 = k1_xboole_0 )
      | ( v3_finset_1 @ sk_B_2 ) )
   <= ( ( sk_B_2 != k1_xboole_0 )
      & ! [X13: $i] :
          ( ( X13 = k1_xboole_0 )
          | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
          | ~ ( r1_tarski @ X13 @ sk_B_2 )
          | ~ ( v1_finset_1 @ X13 )
          | ( ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ X13 )
           != k1_xboole_0 ) )
      & ( m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,
    ( ( sk_B_2 != k1_xboole_0 )
   <= ( sk_B_2 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['12'])).

thf('47',plain,
    ( ( ( ( sk_B @ sk_B_2 )
        = k1_xboole_0 )
      | ( ( k1_setfam_1 @ ( sk_B @ sk_B_2 ) )
       != k1_xboole_0 )
      | ( v3_finset_1 @ sk_B_2 ) )
   <= ( ( sk_B_2 != k1_xboole_0 )
      & ! [X13: $i] :
          ( ( X13 = k1_xboole_0 )
          | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
          | ~ ( r1_tarski @ X13 @ sk_B_2 )
          | ~ ( v1_finset_1 @ X13 )
          | ( ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ X13 )
           != k1_xboole_0 ) )
      & ( m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X2: $i] :
      ( ( v3_finset_1 @ X2 )
      | ( ( k1_setfam_1 @ ( sk_B @ X2 ) )
        = k1_xboole_0 )
      | ( X2 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d3_finset_1])).

thf('49',plain,
    ( ( sk_B_2 != k1_xboole_0 )
   <= ( sk_B_2 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['12'])).

thf('50',plain,
    ( ! [X0: $i] :
        ( ( sk_B_2 != X0 )
        | ( ( k1_setfam_1 @ ( sk_B @ X0 ) )
          = k1_xboole_0 )
        | ( v3_finset_1 @ X0 ) )
   <= ( sk_B_2 != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,
    ( ( ( v3_finset_1 @ sk_B_2 )
      | ( ( k1_setfam_1 @ ( sk_B @ sk_B_2 ) )
        = k1_xboole_0 ) )
   <= ( sk_B_2 != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['50'])).

thf('52',plain,
    ( ( ( v3_finset_1 @ sk_B_2 )
      | ( ( sk_B @ sk_B_2 )
        = k1_xboole_0 ) )
   <= ( ( sk_B_2 != k1_xboole_0 )
      & ! [X13: $i] :
          ( ( X13 = k1_xboole_0 )
          | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
          | ~ ( r1_tarski @ X13 @ sk_B_2 )
          | ~ ( v1_finset_1 @ X13 )
          | ( ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ X13 )
           != k1_xboole_0 ) )
      & ( m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ) ),
    inference(clc,[status(thm)],['47','51'])).

thf('53',plain,
    ( ( v1_compts_1 @ sk_A )
   <= ( v1_compts_1 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('54',plain,
    ( ( v2_tops_2 @ sk_B_2 @ sk_A )
   <= ( v2_tops_2 @ sk_B_2 @ sk_A ) ),
    inference(split,[status(esa)],['10'])).

thf('55',plain,
    ( ( m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ( m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(split,[status(esa)],['14'])).

thf(t13_compts_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( ( v1_compts_1 @ A )
      <=> ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
           => ~ ( ( v3_finset_1 @ B )
                & ( v2_tops_2 @ B @ A )
                & ( ( k6_setfam_1 @ ( u1_struct_0 @ A ) @ B )
                  = k1_xboole_0 ) ) ) ) ) )).

thf('56',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v1_compts_1 @ X5 )
      | ( ( k6_setfam_1 @ ( u1_struct_0 @ X5 ) @ X6 )
       != k1_xboole_0 )
      | ~ ( v2_tops_2 @ X6 @ X5 )
      | ~ ( v3_finset_1 @ X6 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) ) )
      | ~ ( l1_pre_topc @ X5 )
      | ~ ( v2_pre_topc @ X5 )
      | ( v2_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t13_compts_1])).

thf('57',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v3_finset_1 @ sk_B_2 )
      | ~ ( v2_tops_2 @ sk_B_2 @ sk_A )
      | ( ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 )
       != k1_xboole_0 )
      | ~ ( v1_compts_1 @ sk_A ) )
   <= ( m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,
    ( ( ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 )
      = ( k1_setfam_1 @ sk_B_2 ) )
   <= ( m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('61',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v3_finset_1 @ sk_B_2 )
      | ~ ( v2_tops_2 @ sk_B_2 @ sk_A )
      | ( ( k1_setfam_1 @ sk_B_2 )
       != k1_xboole_0 )
      | ~ ( v1_compts_1 @ sk_A ) )
   <= ( m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['57','58','59','60'])).

thf('62',plain,
    ( ( ~ ( v1_compts_1 @ sk_A )
      | ( ( k1_setfam_1 @ sk_B_2 )
       != k1_xboole_0 )
      | ~ ( v3_finset_1 @ sk_B_2 )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( v2_tops_2 @ sk_B_2 @ sk_A )
      & ( m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['54','61'])).

thf('63',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v3_finset_1 @ sk_B_2 )
      | ( ( k1_setfam_1 @ sk_B_2 )
       != k1_xboole_0 ) )
   <= ( ( v1_compts_1 @ sk_A )
      & ( v2_tops_2 @ sk_B_2 @ sk_A )
      & ( m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['53','62'])).

thf('64',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,
    ( ( ( ( k1_setfam_1 @ sk_B_2 )
       != k1_xboole_0 )
      | ~ ( v3_finset_1 @ sk_B_2 ) )
   <= ( ( v1_compts_1 @ sk_A )
      & ( v2_tops_2 @ sk_B_2 @ sk_A )
      & ( m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ) ),
    inference(clc,[status(thm)],['63','64'])).

thf('66',plain,
    ( ( ( ( sk_B @ sk_B_2 )
        = k1_xboole_0 )
      | ( ( k1_setfam_1 @ sk_B_2 )
       != k1_xboole_0 ) )
   <= ( ( sk_B_2 != k1_xboole_0 )
      & ! [X13: $i] :
          ( ( X13 = k1_xboole_0 )
          | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
          | ~ ( r1_tarski @ X13 @ sk_B_2 )
          | ~ ( v1_finset_1 @ X13 )
          | ( ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ X13 )
           != k1_xboole_0 ) )
      & ( v1_compts_1 @ sk_A )
      & ( v2_tops_2 @ sk_B_2 @ sk_A )
      & ( m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['52','65'])).

thf('67',plain,
    ( ( ( ( k1_setfam_1 @ sk_B_2 )
       != ( k1_setfam_1 @ sk_B_2 ) )
      | ( ( sk_B @ sk_B_2 )
        = k1_xboole_0 ) )
   <= ( ( sk_B_2 != k1_xboole_0 )
      & ! [X13: $i] :
          ( ( X13 = k1_xboole_0 )
          | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
          | ~ ( r1_tarski @ X13 @ sk_B_2 )
          | ~ ( v1_finset_1 @ X13 )
          | ( ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ X13 )
           != k1_xboole_0 ) )
      & ( v1_compts_1 @ sk_A )
      & ( ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 )
        = k1_xboole_0 )
      & ( v2_tops_2 @ sk_B_2 @ sk_A )
      & ( m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['20','66'])).

thf('68',plain,
    ( ( ( k1_setfam_1 @ sk_B_2 )
      = k1_xboole_0 )
   <= ( ( ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 )
        = k1_xboole_0 )
      & ( m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('69',plain,
    ( ( ( ( k1_setfam_1 @ sk_B_2 )
       != ( k1_setfam_1 @ sk_B_2 ) )
      | ( ( sk_B @ sk_B_2 )
        = ( k1_setfam_1 @ sk_B_2 ) ) )
   <= ( ( sk_B_2 != k1_xboole_0 )
      & ! [X13: $i] :
          ( ( X13 = k1_xboole_0 )
          | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
          | ~ ( r1_tarski @ X13 @ sk_B_2 )
          | ~ ( v1_finset_1 @ X13 )
          | ( ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ X13 )
           != k1_xboole_0 ) )
      & ( v1_compts_1 @ sk_A )
      & ( ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 )
        = k1_xboole_0 )
      & ( v2_tops_2 @ sk_B_2 @ sk_A )
      & ( m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('70',plain,
    ( ( ( sk_B @ sk_B_2 )
      = ( k1_setfam_1 @ sk_B_2 ) )
   <= ( ( sk_B_2 != k1_xboole_0 )
      & ! [X13: $i] :
          ( ( X13 = k1_xboole_0 )
          | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
          | ~ ( r1_tarski @ X13 @ sk_B_2 )
          | ~ ( v1_finset_1 @ X13 )
          | ( ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ X13 )
           != k1_xboole_0 ) )
      & ( v1_compts_1 @ sk_A )
      & ( ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 )
        = k1_xboole_0 )
      & ( v2_tops_2 @ sk_B_2 @ sk_A )
      & ( m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ) ),
    inference(simplify,[status(thm)],['69'])).

thf('71',plain,
    ( ( ( k1_setfam_1 @ sk_B_2 )
      = k1_xboole_0 )
   <= ( ( ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 )
        = k1_xboole_0 )
      & ( m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('72',plain,(
    ! [X2: $i] :
      ( ( v3_finset_1 @ X2 )
      | ( ( sk_B @ X2 )
       != k1_xboole_0 )
      | ( X2 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d3_finset_1])).

thf('73',plain,
    ( ! [X0: $i] :
        ( ( ( sk_B @ X0 )
         != ( k1_setfam_1 @ sk_B_2 ) )
        | ( X0 = k1_xboole_0 )
        | ( v3_finset_1 @ X0 ) )
   <= ( ( ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 )
        = k1_xboole_0 )
      & ( m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,
    ( ( ( k1_setfam_1 @ sk_B_2 )
      = k1_xboole_0 )
   <= ( ( ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 )
        = k1_xboole_0 )
      & ( m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('75',plain,
    ( ! [X0: $i] :
        ( ( ( sk_B @ X0 )
         != ( k1_setfam_1 @ sk_B_2 ) )
        | ( X0
          = ( k1_setfam_1 @ sk_B_2 ) )
        | ( v3_finset_1 @ X0 ) )
   <= ( ( ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 )
        = k1_xboole_0 )
      & ( m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('76',plain,
    ( ( ( ( k1_setfam_1 @ sk_B_2 )
       != ( k1_setfam_1 @ sk_B_2 ) )
      | ( v3_finset_1 @ sk_B_2 )
      | ( sk_B_2
        = ( k1_setfam_1 @ sk_B_2 ) ) )
   <= ( ( sk_B_2 != k1_xboole_0 )
      & ! [X13: $i] :
          ( ( X13 = k1_xboole_0 )
          | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
          | ~ ( r1_tarski @ X13 @ sk_B_2 )
          | ~ ( v1_finset_1 @ X13 )
          | ( ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ X13 )
           != k1_xboole_0 ) )
      & ( v1_compts_1 @ sk_A )
      & ( ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 )
        = k1_xboole_0 )
      & ( v2_tops_2 @ sk_B_2 @ sk_A )
      & ( m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['70','75'])).

thf('77',plain,
    ( ( ( sk_B_2
        = ( k1_setfam_1 @ sk_B_2 ) )
      | ( v3_finset_1 @ sk_B_2 ) )
   <= ( ( sk_B_2 != k1_xboole_0 )
      & ! [X13: $i] :
          ( ( X13 = k1_xboole_0 )
          | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
          | ~ ( r1_tarski @ X13 @ sk_B_2 )
          | ~ ( v1_finset_1 @ X13 )
          | ( ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ X13 )
           != k1_xboole_0 ) )
      & ( v1_compts_1 @ sk_A )
      & ( ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 )
        = k1_xboole_0 )
      & ( v2_tops_2 @ sk_B_2 @ sk_A )
      & ( m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ) ),
    inference(simplify,[status(thm)],['76'])).

thf('78',plain,
    ( ( ( k1_setfam_1 @ sk_B_2 )
      = k1_xboole_0 )
   <= ( ( ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 )
        = k1_xboole_0 )
      & ( m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('79',plain,
    ( ( sk_B_2 != k1_xboole_0 )
   <= ( sk_B_2 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['12'])).

thf('80',plain,
    ( ( sk_B_2
     != ( k1_setfam_1 @ sk_B_2 ) )
   <= ( ( sk_B_2 != k1_xboole_0 )
      & ( ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 )
        = k1_xboole_0 )
      & ( m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,
    ( ( v3_finset_1 @ sk_B_2 )
   <= ( ( sk_B_2 != k1_xboole_0 )
      & ! [X13: $i] :
          ( ( X13 = k1_xboole_0 )
          | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
          | ~ ( r1_tarski @ X13 @ sk_B_2 )
          | ~ ( v1_finset_1 @ X13 )
          | ( ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ X13 )
           != k1_xboole_0 ) )
      & ( v1_compts_1 @ sk_A )
      & ( ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 )
        = k1_xboole_0 )
      & ( v2_tops_2 @ sk_B_2 @ sk_A )
      & ( m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['77','80'])).

thf('82',plain,
    ( ( ( ( k1_setfam_1 @ sk_B_2 )
       != k1_xboole_0 )
      | ~ ( v3_finset_1 @ sk_B_2 ) )
   <= ( ( v1_compts_1 @ sk_A )
      & ( v2_tops_2 @ sk_B_2 @ sk_A )
      & ( m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ) ),
    inference(clc,[status(thm)],['63','64'])).

thf('83',plain,
    ( ( ( k1_setfam_1 @ sk_B_2 )
     != k1_xboole_0 )
   <= ( ( sk_B_2 != k1_xboole_0 )
      & ! [X13: $i] :
          ( ( X13 = k1_xboole_0 )
          | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
          | ~ ( r1_tarski @ X13 @ sk_B_2 )
          | ~ ( v1_finset_1 @ X13 )
          | ( ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ X13 )
           != k1_xboole_0 ) )
      & ( v1_compts_1 @ sk_A )
      & ( ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 )
        = k1_xboole_0 )
      & ( v2_tops_2 @ sk_B_2 @ sk_A )
      & ( m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,
    ( ( ( k1_setfam_1 @ sk_B_2 )
      = k1_xboole_0 )
   <= ( ( ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 )
        = k1_xboole_0 )
      & ( m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('85',plain,
    ( ( ( k1_setfam_1 @ sk_B_2 )
     != ( k1_setfam_1 @ sk_B_2 ) )
   <= ( ( sk_B_2 != k1_xboole_0 )
      & ! [X13: $i] :
          ( ( X13 = k1_xboole_0 )
          | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
          | ~ ( r1_tarski @ X13 @ sk_B_2 )
          | ~ ( v1_finset_1 @ X13 )
          | ( ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ X13 )
           != k1_xboole_0 ) )
      & ( v1_compts_1 @ sk_A )
      & ( ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 )
        = k1_xboole_0 )
      & ( v2_tops_2 @ sk_B_2 @ sk_A )
      & ( m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['83','84'])).

thf('86',plain,
    ( ~ ( m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
    | ~ ( v1_compts_1 @ sk_A )
    | ( ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 )
     != k1_xboole_0 )
    | ~ ( v2_tops_2 @ sk_B_2 @ sk_A )
    | ~ ! [X13: $i] :
          ( ( X13 = k1_xboole_0 )
          | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
          | ~ ( r1_tarski @ X13 @ sk_B_2 )
          | ~ ( v1_finset_1 @ X13 )
          | ( ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ X13 )
           != k1_xboole_0 ) )
    | ( sk_B_2 = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['85'])).

thf('87',plain,(
    ! [X14: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
      | ( X14 = k1_xboole_0 )
      | ~ ( v2_tops_2 @ X14 @ sk_A )
      | ( ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ X14 )
       != k1_xboole_0 )
      | ( r1_tarski @ ( sk_C @ X14 ) @ X14 )
      | ( v1_compts_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,
    ( ! [X14: $i] :
        ( ( X14 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
        | ~ ( v2_tops_2 @ X14 @ sk_A )
        | ( ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ X14 )
         != k1_xboole_0 )
        | ( r1_tarski @ ( sk_C @ X14 ) @ X14 ) )
    | ( v1_compts_1 @ sk_A ) ),
    inference(split,[status(esa)],['87'])).

thf('89',plain,(
    ! [X5: $i] :
      ( ( v3_finset_1 @ ( sk_B_1 @ X5 ) )
      | ( v1_compts_1 @ X5 )
      | ~ ( l1_pre_topc @ X5 )
      | ~ ( v2_pre_topc @ X5 )
      | ( v2_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t13_compts_1])).

thf('90',plain,(
    ! [X5: $i] :
      ( ( v2_tops_2 @ ( sk_B_1 @ X5 ) @ X5 )
      | ( v1_compts_1 @ X5 )
      | ~ ( l1_pre_topc @ X5 )
      | ~ ( v2_pre_topc @ X5 )
      | ( v2_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t13_compts_1])).

thf('91',plain,(
    ! [X5: $i] :
      ( ( ( k6_setfam_1 @ ( u1_struct_0 @ X5 ) @ ( sk_B_1 @ X5 ) )
        = k1_xboole_0 )
      | ( v1_compts_1 @ X5 )
      | ~ ( l1_pre_topc @ X5 )
      | ~ ( v2_pre_topc @ X5 )
      | ( v2_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t13_compts_1])).

thf('92',plain,(
    ! [X5: $i] :
      ( ( m1_subset_1 @ ( sk_B_1 @ X5 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) ) )
      | ( v1_compts_1 @ X5 )
      | ~ ( l1_pre_topc @ X5 )
      | ~ ( v2_pre_topc @ X5 )
      | ( v2_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t13_compts_1])).

thf('93',plain,(
    ! [X14: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
      | ( X14 = k1_xboole_0 )
      | ~ ( v2_tops_2 @ X14 @ sk_A )
      | ( ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ X14 )
       != k1_xboole_0 )
      | ( r1_tarski @ ( sk_C @ X14 ) @ X14 )
      | ( v1_compts_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,
    ( ! [X14: $i] :
        ( ( X14 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
        | ~ ( v2_tops_2 @ X14 @ sk_A )
        | ( ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ X14 )
         != k1_xboole_0 )
        | ( r1_tarski @ ( sk_C @ X14 ) @ X14 ) )
   <= ! [X14: $i] :
        ( ( X14 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
        | ~ ( v2_tops_2 @ X14 @ sk_A )
        | ( ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ X14 )
         != k1_xboole_0 )
        | ( r1_tarski @ ( sk_C @ X14 ) @ X14 ) ) ),
    inference(split,[status(esa)],['93'])).

thf('95',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( r1_tarski @ ( sk_C @ ( sk_B_1 @ sk_A ) ) @ ( sk_B_1 @ sk_A ) )
      | ( ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B_1 @ sk_A ) )
       != k1_xboole_0 )
      | ~ ( v2_tops_2 @ ( sk_B_1 @ sk_A ) @ sk_A )
      | ( ( sk_B_1 @ sk_A )
        = k1_xboole_0 ) )
   <= ! [X14: $i] :
        ( ( X14 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
        | ~ ( v2_tops_2 @ X14 @ sk_A )
        | ( ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ X14 )
         != k1_xboole_0 )
        | ( r1_tarski @ ( sk_C @ X14 ) @ X14 ) ) ),
    inference('sup-',[status(thm)],['92','94'])).

thf('96',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( r1_tarski @ ( sk_C @ ( sk_B_1 @ sk_A ) ) @ ( sk_B_1 @ sk_A ) )
      | ( ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B_1 @ sk_A ) )
       != k1_xboole_0 )
      | ~ ( v2_tops_2 @ ( sk_B_1 @ sk_A ) @ sk_A )
      | ( ( sk_B_1 @ sk_A )
        = k1_xboole_0 ) )
   <= ! [X14: $i] :
        ( ( X14 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
        | ~ ( v2_tops_2 @ X14 @ sk_A )
        | ( ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ X14 )
         != k1_xboole_0 )
        | ( r1_tarski @ ( sk_C @ X14 ) @ X14 ) ) ),
    inference(demod,[status(thm)],['95','96','97'])).

thf('99',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( ( sk_B_1 @ sk_A )
        = k1_xboole_0 )
      | ~ ( v2_tops_2 @ ( sk_B_1 @ sk_A ) @ sk_A )
      | ( r1_tarski @ ( sk_C @ ( sk_B_1 @ sk_A ) ) @ ( sk_B_1 @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X14: $i] :
        ( ( X14 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
        | ~ ( v2_tops_2 @ X14 @ sk_A )
        | ( ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ X14 )
         != k1_xboole_0 )
        | ( r1_tarski @ ( sk_C @ X14 ) @ X14 ) ) ),
    inference('sup-',[status(thm)],['91','98'])).

thf('100',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( ( sk_B_1 @ sk_A )
        = k1_xboole_0 )
      | ~ ( v2_tops_2 @ ( sk_B_1 @ sk_A ) @ sk_A )
      | ( r1_tarski @ ( sk_C @ ( sk_B_1 @ sk_A ) ) @ ( sk_B_1 @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X14: $i] :
        ( ( X14 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
        | ~ ( v2_tops_2 @ X14 @ sk_A )
        | ( ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ X14 )
         != k1_xboole_0 )
        | ( r1_tarski @ ( sk_C @ X14 ) @ X14 ) ) ),
    inference(demod,[status(thm)],['99','100','101'])).

thf('103',plain,
    ( ( ( r1_tarski @ ( sk_C @ ( sk_B_1 @ sk_A ) ) @ ( sk_B_1 @ sk_A ) )
      | ~ ( v2_tops_2 @ ( sk_B_1 @ sk_A ) @ sk_A )
      | ( ( sk_B_1 @ sk_A )
        = k1_xboole_0 )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X14: $i] :
        ( ( X14 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
        | ~ ( v2_tops_2 @ X14 @ sk_A )
        | ( ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ X14 )
         != k1_xboole_0 )
        | ( r1_tarski @ ( sk_C @ X14 ) @ X14 ) ) ),
    inference(simplify,[status(thm)],['102'])).

thf('104',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( ( sk_B_1 @ sk_A )
        = k1_xboole_0 )
      | ( r1_tarski @ ( sk_C @ ( sk_B_1 @ sk_A ) ) @ ( sk_B_1 @ sk_A ) ) )
   <= ! [X14: $i] :
        ( ( X14 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
        | ~ ( v2_tops_2 @ X14 @ sk_A )
        | ( ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ X14 )
         != k1_xboole_0 )
        | ( r1_tarski @ ( sk_C @ X14 ) @ X14 ) ) ),
    inference('sup-',[status(thm)],['90','103'])).

thf('105',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( ( sk_B_1 @ sk_A )
        = k1_xboole_0 )
      | ( r1_tarski @ ( sk_C @ ( sk_B_1 @ sk_A ) ) @ ( sk_B_1 @ sk_A ) ) )
   <= ! [X14: $i] :
        ( ( X14 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
        | ~ ( v2_tops_2 @ X14 @ sk_A )
        | ( ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ X14 )
         != k1_xboole_0 )
        | ( r1_tarski @ ( sk_C @ X14 ) @ X14 ) ) ),
    inference(demod,[status(thm)],['104','105','106'])).

thf('108',plain,
    ( ( ( r1_tarski @ ( sk_C @ ( sk_B_1 @ sk_A ) ) @ ( sk_B_1 @ sk_A ) )
      | ( ( sk_B_1 @ sk_A )
        = k1_xboole_0 )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X14: $i] :
        ( ( X14 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
        | ~ ( v2_tops_2 @ X14 @ sk_A )
        | ( ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ X14 )
         != k1_xboole_0 )
        | ( r1_tarski @ ( sk_C @ X14 ) @ X14 ) ) ),
    inference(simplify,[status(thm)],['107'])).

thf('109',plain,(
    ! [X5: $i] :
      ( ( v2_tops_2 @ ( sk_B_1 @ X5 ) @ X5 )
      | ( v1_compts_1 @ X5 )
      | ~ ( l1_pre_topc @ X5 )
      | ~ ( v2_pre_topc @ X5 )
      | ( v2_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t13_compts_1])).

thf('110',plain,(
    ! [X5: $i] :
      ( ( ( k6_setfam_1 @ ( u1_struct_0 @ X5 ) @ ( sk_B_1 @ X5 ) )
        = k1_xboole_0 )
      | ( v1_compts_1 @ X5 )
      | ~ ( l1_pre_topc @ X5 )
      | ~ ( v2_pre_topc @ X5 )
      | ( v2_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t13_compts_1])).

thf('111',plain,(
    ! [X5: $i] :
      ( ( m1_subset_1 @ ( sk_B_1 @ X5 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) ) )
      | ( v1_compts_1 @ X5 )
      | ~ ( l1_pre_topc @ X5 )
      | ~ ( v2_pre_topc @ X5 )
      | ( v2_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t13_compts_1])).

thf('112',plain,
    ( ! [X14: $i] :
        ( ( X14 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
        | ~ ( v2_tops_2 @ X14 @ sk_A )
        | ( ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ X14 )
         != k1_xboole_0 )
        | ( v1_finset_1 @ ( sk_C @ X14 ) ) )
   <= ! [X14: $i] :
        ( ( X14 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
        | ~ ( v2_tops_2 @ X14 @ sk_A )
        | ( ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ X14 )
         != k1_xboole_0 )
        | ( v1_finset_1 @ ( sk_C @ X14 ) ) ) ),
    inference(split,[status(esa)],['2'])).

thf('113',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v1_finset_1 @ ( sk_C @ ( sk_B_1 @ sk_A ) ) )
      | ( ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B_1 @ sk_A ) )
       != k1_xboole_0 )
      | ~ ( v2_tops_2 @ ( sk_B_1 @ sk_A ) @ sk_A )
      | ( ( sk_B_1 @ sk_A )
        = k1_xboole_0 ) )
   <= ! [X14: $i] :
        ( ( X14 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
        | ~ ( v2_tops_2 @ X14 @ sk_A )
        | ( ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ X14 )
         != k1_xboole_0 )
        | ( v1_finset_1 @ ( sk_C @ X14 ) ) ) ),
    inference('sup-',[status(thm)],['111','112'])).

thf('114',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v1_finset_1 @ ( sk_C @ ( sk_B_1 @ sk_A ) ) )
      | ( ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B_1 @ sk_A ) )
       != k1_xboole_0 )
      | ~ ( v2_tops_2 @ ( sk_B_1 @ sk_A ) @ sk_A )
      | ( ( sk_B_1 @ sk_A )
        = k1_xboole_0 ) )
   <= ! [X14: $i] :
        ( ( X14 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
        | ~ ( v2_tops_2 @ X14 @ sk_A )
        | ( ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ X14 )
         != k1_xboole_0 )
        | ( v1_finset_1 @ ( sk_C @ X14 ) ) ) ),
    inference(demod,[status(thm)],['113','114','115'])).

thf('117',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( ( sk_B_1 @ sk_A )
        = k1_xboole_0 )
      | ~ ( v2_tops_2 @ ( sk_B_1 @ sk_A ) @ sk_A )
      | ( v1_finset_1 @ ( sk_C @ ( sk_B_1 @ sk_A ) ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X14: $i] :
        ( ( X14 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
        | ~ ( v2_tops_2 @ X14 @ sk_A )
        | ( ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ X14 )
         != k1_xboole_0 )
        | ( v1_finset_1 @ ( sk_C @ X14 ) ) ) ),
    inference('sup-',[status(thm)],['110','116'])).

thf('118',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( ( sk_B_1 @ sk_A )
        = k1_xboole_0 )
      | ~ ( v2_tops_2 @ ( sk_B_1 @ sk_A ) @ sk_A )
      | ( v1_finset_1 @ ( sk_C @ ( sk_B_1 @ sk_A ) ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X14: $i] :
        ( ( X14 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
        | ~ ( v2_tops_2 @ X14 @ sk_A )
        | ( ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ X14 )
         != k1_xboole_0 )
        | ( v1_finset_1 @ ( sk_C @ X14 ) ) ) ),
    inference(demod,[status(thm)],['117','118','119'])).

thf('121',plain,
    ( ( ( v1_finset_1 @ ( sk_C @ ( sk_B_1 @ sk_A ) ) )
      | ~ ( v2_tops_2 @ ( sk_B_1 @ sk_A ) @ sk_A )
      | ( ( sk_B_1 @ sk_A )
        = k1_xboole_0 )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X14: $i] :
        ( ( X14 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
        | ~ ( v2_tops_2 @ X14 @ sk_A )
        | ( ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ X14 )
         != k1_xboole_0 )
        | ( v1_finset_1 @ ( sk_C @ X14 ) ) ) ),
    inference(simplify,[status(thm)],['120'])).

thf('122',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( ( sk_B_1 @ sk_A )
        = k1_xboole_0 )
      | ( v1_finset_1 @ ( sk_C @ ( sk_B_1 @ sk_A ) ) ) )
   <= ! [X14: $i] :
        ( ( X14 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
        | ~ ( v2_tops_2 @ X14 @ sk_A )
        | ( ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ X14 )
         != k1_xboole_0 )
        | ( v1_finset_1 @ ( sk_C @ X14 ) ) ) ),
    inference('sup-',[status(thm)],['109','121'])).

thf('123',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('125',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( ( sk_B_1 @ sk_A )
        = k1_xboole_0 )
      | ( v1_finset_1 @ ( sk_C @ ( sk_B_1 @ sk_A ) ) ) )
   <= ! [X14: $i] :
        ( ( X14 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
        | ~ ( v2_tops_2 @ X14 @ sk_A )
        | ( ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ X14 )
         != k1_xboole_0 )
        | ( v1_finset_1 @ ( sk_C @ X14 ) ) ) ),
    inference(demod,[status(thm)],['122','123','124'])).

thf('126',plain,
    ( ( ( v1_finset_1 @ ( sk_C @ ( sk_B_1 @ sk_A ) ) )
      | ( ( sk_B_1 @ sk_A )
        = k1_xboole_0 )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X14: $i] :
        ( ( X14 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
        | ~ ( v2_tops_2 @ X14 @ sk_A )
        | ( ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ X14 )
         != k1_xboole_0 )
        | ( v1_finset_1 @ ( sk_C @ X14 ) ) ) ),
    inference(simplify,[status(thm)],['125'])).

thf('127',plain,(
    ! [X5: $i] :
      ( ( v2_tops_2 @ ( sk_B_1 @ X5 ) @ X5 )
      | ( v1_compts_1 @ X5 )
      | ~ ( l1_pre_topc @ X5 )
      | ~ ( v2_pre_topc @ X5 )
      | ( v2_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t13_compts_1])).

thf('128',plain,(
    ! [X5: $i] :
      ( ( ( k6_setfam_1 @ ( u1_struct_0 @ X5 ) @ ( sk_B_1 @ X5 ) )
        = k1_xboole_0 )
      | ( v1_compts_1 @ X5 )
      | ~ ( l1_pre_topc @ X5 )
      | ~ ( v2_pre_topc @ X5 )
      | ( v2_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t13_compts_1])).

thf('129',plain,(
    ! [X5: $i] :
      ( ( m1_subset_1 @ ( sk_B_1 @ X5 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) ) )
      | ( v1_compts_1 @ X5 )
      | ~ ( l1_pre_topc @ X5 )
      | ~ ( v2_pre_topc @ X5 )
      | ( v2_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t13_compts_1])).

thf('130',plain,(
    ! [X14: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
      | ( X14 = k1_xboole_0 )
      | ~ ( v2_tops_2 @ X14 @ sk_A )
      | ( ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ X14 )
       != k1_xboole_0 )
      | ( ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ X14 ) )
        = k1_xboole_0 )
      | ( v1_compts_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('131',plain,
    ( ! [X14: $i] :
        ( ( X14 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
        | ~ ( v2_tops_2 @ X14 @ sk_A )
        | ( ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ X14 )
         != k1_xboole_0 )
        | ( ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ X14 ) )
          = k1_xboole_0 ) )
   <= ! [X14: $i] :
        ( ( X14 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
        | ~ ( v2_tops_2 @ X14 @ sk_A )
        | ( ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ X14 )
         != k1_xboole_0 )
        | ( ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ X14 ) )
          = k1_xboole_0 ) ) ),
    inference(split,[status(esa)],['130'])).

thf('132',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ ( sk_B_1 @ sk_A ) ) )
        = k1_xboole_0 )
      | ( ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B_1 @ sk_A ) )
       != k1_xboole_0 )
      | ~ ( v2_tops_2 @ ( sk_B_1 @ sk_A ) @ sk_A )
      | ( ( sk_B_1 @ sk_A )
        = k1_xboole_0 ) )
   <= ! [X14: $i] :
        ( ( X14 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
        | ~ ( v2_tops_2 @ X14 @ sk_A )
        | ( ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ X14 )
         != k1_xboole_0 )
        | ( ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ X14 ) )
          = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['129','131'])).

thf('133',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('134',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('135',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ ( sk_B_1 @ sk_A ) ) )
        = k1_xboole_0 )
      | ( ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B_1 @ sk_A ) )
       != k1_xboole_0 )
      | ~ ( v2_tops_2 @ ( sk_B_1 @ sk_A ) @ sk_A )
      | ( ( sk_B_1 @ sk_A )
        = k1_xboole_0 ) )
   <= ! [X14: $i] :
        ( ( X14 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
        | ~ ( v2_tops_2 @ X14 @ sk_A )
        | ( ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ X14 )
         != k1_xboole_0 )
        | ( ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ X14 ) )
          = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['132','133','134'])).

thf('136',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( ( sk_B_1 @ sk_A )
        = k1_xboole_0 )
      | ~ ( v2_tops_2 @ ( sk_B_1 @ sk_A ) @ sk_A )
      | ( ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ ( sk_B_1 @ sk_A ) ) )
        = k1_xboole_0 )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X14: $i] :
        ( ( X14 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
        | ~ ( v2_tops_2 @ X14 @ sk_A )
        | ( ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ X14 )
         != k1_xboole_0 )
        | ( ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ X14 ) )
          = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['128','135'])).

thf('137',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('138',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('139',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( ( sk_B_1 @ sk_A )
        = k1_xboole_0 )
      | ~ ( v2_tops_2 @ ( sk_B_1 @ sk_A ) @ sk_A )
      | ( ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ ( sk_B_1 @ sk_A ) ) )
        = k1_xboole_0 )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X14: $i] :
        ( ( X14 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
        | ~ ( v2_tops_2 @ X14 @ sk_A )
        | ( ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ X14 )
         != k1_xboole_0 )
        | ( ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ X14 ) )
          = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['136','137','138'])).

thf('140',plain,
    ( ( ( ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ ( sk_B_1 @ sk_A ) ) )
        = k1_xboole_0 )
      | ~ ( v2_tops_2 @ ( sk_B_1 @ sk_A ) @ sk_A )
      | ( ( sk_B_1 @ sk_A )
        = k1_xboole_0 )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X14: $i] :
        ( ( X14 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
        | ~ ( v2_tops_2 @ X14 @ sk_A )
        | ( ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ X14 )
         != k1_xboole_0 )
        | ( ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ X14 ) )
          = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['139'])).

thf('141',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( ( sk_B_1 @ sk_A )
        = k1_xboole_0 )
      | ( ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ ( sk_B_1 @ sk_A ) ) )
        = k1_xboole_0 ) )
   <= ! [X14: $i] :
        ( ( X14 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
        | ~ ( v2_tops_2 @ X14 @ sk_A )
        | ( ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ X14 )
         != k1_xboole_0 )
        | ( ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ X14 ) )
          = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['127','140'])).

thf('142',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('143',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('144',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( ( sk_B_1 @ sk_A )
        = k1_xboole_0 )
      | ( ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ ( sk_B_1 @ sk_A ) ) )
        = k1_xboole_0 ) )
   <= ! [X14: $i] :
        ( ( X14 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
        | ~ ( v2_tops_2 @ X14 @ sk_A )
        | ( ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ X14 )
         != k1_xboole_0 )
        | ( ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ X14 ) )
          = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['141','142','143'])).

thf('145',plain,
    ( ( ( ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ ( sk_B_1 @ sk_A ) ) )
        = k1_xboole_0 )
      | ( ( sk_B_1 @ sk_A )
        = k1_xboole_0 )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X14: $i] :
        ( ( X14 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
        | ~ ( v2_tops_2 @ X14 @ sk_A )
        | ( ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ X14 )
         != k1_xboole_0 )
        | ( ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ X14 ) )
          = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['144'])).

thf('146',plain,(
    ! [X5: $i] :
      ( ( m1_subset_1 @ ( sk_B_1 @ X5 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) ) )
      | ( v1_compts_1 @ X5 )
      | ~ ( l1_pre_topc @ X5 )
      | ~ ( v2_pre_topc @ X5 )
      | ( v2_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t13_compts_1])).

thf('147',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r1_tarski @ X10 @ X11 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('148',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v1_compts_1 @ X0 )
      | ( r1_tarski @ ( sk_B_1 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['146','147'])).

thf('149',plain,
    ( ( ( r1_tarski @ ( sk_C @ ( sk_B_1 @ sk_A ) ) @ ( sk_B_1 @ sk_A ) )
      | ( ( sk_B_1 @ sk_A )
        = k1_xboole_0 )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X14: $i] :
        ( ( X14 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
        | ~ ( v2_tops_2 @ X14 @ sk_A )
        | ( ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ X14 )
         != k1_xboole_0 )
        | ( r1_tarski @ ( sk_C @ X14 ) @ X14 ) ) ),
    inference(simplify,[status(thm)],['107'])).

thf('150',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r1_tarski @ X7 @ X8 )
      | ~ ( r1_tarski @ X8 @ X9 )
      | ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('151',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( v1_compts_1 @ sk_A )
        | ( ( sk_B_1 @ sk_A )
          = k1_xboole_0 )
        | ( r1_tarski @ ( sk_C @ ( sk_B_1 @ sk_A ) ) @ X0 )
        | ~ ( r1_tarski @ ( sk_B_1 @ sk_A ) @ X0 ) )
   <= ! [X14: $i] :
        ( ( X14 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
        | ~ ( v2_tops_2 @ X14 @ sk_A )
        | ( ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ X14 )
         != k1_xboole_0 )
        | ( r1_tarski @ ( sk_C @ X14 ) @ X14 ) ) ),
    inference('sup-',[status(thm)],['149','150'])).

thf('152',plain,
    ( ( ( v1_compts_1 @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( r1_tarski @ ( sk_C @ ( sk_B_1 @ sk_A ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( ( sk_B_1 @ sk_A )
        = k1_xboole_0 )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X14: $i] :
        ( ( X14 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
        | ~ ( v2_tops_2 @ X14 @ sk_A )
        | ( ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ X14 )
         != k1_xboole_0 )
        | ( r1_tarski @ ( sk_C @ X14 ) @ X14 ) ) ),
    inference('sup-',[status(thm)],['148','151'])).

thf('153',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('154',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('155',plain,
    ( ( ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( r1_tarski @ ( sk_C @ ( sk_B_1 @ sk_A ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( ( sk_B_1 @ sk_A )
        = k1_xboole_0 )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X14: $i] :
        ( ( X14 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
        | ~ ( v2_tops_2 @ X14 @ sk_A )
        | ( ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ X14 )
         != k1_xboole_0 )
        | ( r1_tarski @ ( sk_C @ X14 ) @ X14 ) ) ),
    inference(demod,[status(thm)],['152','153','154'])).

thf('156',plain,
    ( ( ( ( sk_B_1 @ sk_A )
        = k1_xboole_0 )
      | ( r1_tarski @ ( sk_C @ ( sk_B_1 @ sk_A ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A ) )
   <= ! [X14: $i] :
        ( ( X14 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
        | ~ ( v2_tops_2 @ X14 @ sk_A )
        | ( ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ X14 )
         != k1_xboole_0 )
        | ( r1_tarski @ ( sk_C @ X14 ) @ X14 ) ) ),
    inference(simplify,[status(thm)],['155'])).

thf('157',plain,(
    ! [X10: $i,X12: $i] :
      ( ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X12 ) )
      | ~ ( r1_tarski @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('158',plain,
    ( ( ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_B_1 @ sk_A )
        = k1_xboole_0 )
      | ( m1_subset_1 @ ( sk_C @ ( sk_B_1 @ sk_A ) ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) )
   <= ! [X14: $i] :
        ( ( X14 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
        | ~ ( v2_tops_2 @ X14 @ sk_A )
        | ( ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ X14 )
         != k1_xboole_0 )
        | ( r1_tarski @ ( sk_C @ X14 ) @ X14 ) ) ),
    inference('sup-',[status(thm)],['156','157'])).

thf('159',plain,(
    ! [X3: $i,X4: $i] :
      ( ( ( k6_setfam_1 @ X4 @ X3 )
        = ( k1_setfam_1 @ X3 ) )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X4 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_setfam_1])).

thf('160',plain,
    ( ( ( ( sk_B_1 @ sk_A )
        = k1_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ ( sk_B_1 @ sk_A ) ) )
        = ( k1_setfam_1 @ ( sk_C @ ( sk_B_1 @ sk_A ) ) ) ) )
   <= ! [X14: $i] :
        ( ( X14 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
        | ~ ( v2_tops_2 @ X14 @ sk_A )
        | ( ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ X14 )
         != k1_xboole_0 )
        | ( r1_tarski @ ( sk_C @ X14 ) @ X14 ) ) ),
    inference('sup-',[status(thm)],['158','159'])).

thf('161',plain,
    ( ( ( k1_xboole_0
        = ( k1_setfam_1 @ ( sk_C @ ( sk_B_1 @ sk_A ) ) ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( ( sk_B_1 @ sk_A )
        = k1_xboole_0 )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_B_1 @ sk_A )
        = k1_xboole_0 ) )
   <= ( ! [X14: $i] :
          ( ( X14 = k1_xboole_0 )
          | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
          | ~ ( v2_tops_2 @ X14 @ sk_A )
          | ( ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ X14 )
           != k1_xboole_0 )
          | ( ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ X14 ) )
            = k1_xboole_0 ) )
      & ! [X14: $i] :
          ( ( X14 = k1_xboole_0 )
          | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
          | ~ ( v2_tops_2 @ X14 @ sk_A )
          | ( ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ X14 )
           != k1_xboole_0 )
          | ( r1_tarski @ ( sk_C @ X14 ) @ X14 ) ) ) ),
    inference('sup+',[status(thm)],['145','160'])).

thf('162',plain,
    ( ( ( ( sk_B_1 @ sk_A )
        = k1_xboole_0 )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( k1_xboole_0
        = ( k1_setfam_1 @ ( sk_C @ ( sk_B_1 @ sk_A ) ) ) ) )
   <= ( ! [X14: $i] :
          ( ( X14 = k1_xboole_0 )
          | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
          | ~ ( v2_tops_2 @ X14 @ sk_A )
          | ( ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ X14 )
           != k1_xboole_0 )
          | ( ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ X14 ) )
            = k1_xboole_0 ) )
      & ! [X14: $i] :
          ( ( X14 = k1_xboole_0 )
          | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
          | ~ ( v2_tops_2 @ X14 @ sk_A )
          | ( ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ X14 )
           != k1_xboole_0 )
          | ( r1_tarski @ ( sk_C @ X14 ) @ X14 ) ) ) ),
    inference(simplify,[status(thm)],['161'])).

thf('163',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_setfam_1 @ X1 )
       != k1_xboole_0 )
      | ~ ( v1_finset_1 @ X1 )
      | ~ ( r1_tarski @ X1 @ X0 )
      | ( X1 = k1_xboole_0 )
      | ~ ( v3_finset_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d3_finset_1])).

thf('164',plain,
    ( ! [X0: $i] :
        ( ( k1_xboole_0 != k1_xboole_0 )
        | ( v2_struct_0 @ sk_A )
        | ( v1_compts_1 @ sk_A )
        | ( ( sk_B_1 @ sk_A )
          = k1_xboole_0 )
        | ~ ( v3_finset_1 @ X0 )
        | ( ( sk_C @ ( sk_B_1 @ sk_A ) )
          = k1_xboole_0 )
        | ~ ( r1_tarski @ ( sk_C @ ( sk_B_1 @ sk_A ) ) @ X0 )
        | ~ ( v1_finset_1 @ ( sk_C @ ( sk_B_1 @ sk_A ) ) ) )
   <= ( ! [X14: $i] :
          ( ( X14 = k1_xboole_0 )
          | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
          | ~ ( v2_tops_2 @ X14 @ sk_A )
          | ( ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ X14 )
           != k1_xboole_0 )
          | ( ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ X14 ) )
            = k1_xboole_0 ) )
      & ! [X14: $i] :
          ( ( X14 = k1_xboole_0 )
          | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
          | ~ ( v2_tops_2 @ X14 @ sk_A )
          | ( ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ X14 )
           != k1_xboole_0 )
          | ( r1_tarski @ ( sk_C @ X14 ) @ X14 ) ) ) ),
    inference('sup-',[status(thm)],['162','163'])).

thf('165',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_finset_1 @ ( sk_C @ ( sk_B_1 @ sk_A ) ) )
        | ~ ( r1_tarski @ ( sk_C @ ( sk_B_1 @ sk_A ) ) @ X0 )
        | ( ( sk_C @ ( sk_B_1 @ sk_A ) )
          = k1_xboole_0 )
        | ~ ( v3_finset_1 @ X0 )
        | ( ( sk_B_1 @ sk_A )
          = k1_xboole_0 )
        | ( v1_compts_1 @ sk_A )
        | ( v2_struct_0 @ sk_A ) )
   <= ( ! [X14: $i] :
          ( ( X14 = k1_xboole_0 )
          | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
          | ~ ( v2_tops_2 @ X14 @ sk_A )
          | ( ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ X14 )
           != k1_xboole_0 )
          | ( ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ X14 ) )
            = k1_xboole_0 ) )
      & ! [X14: $i] :
          ( ( X14 = k1_xboole_0 )
          | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
          | ~ ( v2_tops_2 @ X14 @ sk_A )
          | ( ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ X14 )
           != k1_xboole_0 )
          | ( r1_tarski @ ( sk_C @ X14 ) @ X14 ) ) ) ),
    inference(simplify,[status(thm)],['164'])).

thf('166',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( v1_compts_1 @ sk_A )
        | ( ( sk_B_1 @ sk_A )
          = k1_xboole_0 )
        | ( v2_struct_0 @ sk_A )
        | ( v1_compts_1 @ sk_A )
        | ( ( sk_B_1 @ sk_A )
          = k1_xboole_0 )
        | ~ ( v3_finset_1 @ X0 )
        | ( ( sk_C @ ( sk_B_1 @ sk_A ) )
          = k1_xboole_0 )
        | ~ ( r1_tarski @ ( sk_C @ ( sk_B_1 @ sk_A ) ) @ X0 ) )
   <= ( ! [X14: $i] :
          ( ( X14 = k1_xboole_0 )
          | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
          | ~ ( v2_tops_2 @ X14 @ sk_A )
          | ( ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ X14 )
           != k1_xboole_0 )
          | ( ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ X14 ) )
            = k1_xboole_0 ) )
      & ! [X14: $i] :
          ( ( X14 = k1_xboole_0 )
          | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
          | ~ ( v2_tops_2 @ X14 @ sk_A )
          | ( ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ X14 )
           != k1_xboole_0 )
          | ( v1_finset_1 @ ( sk_C @ X14 ) ) )
      & ! [X14: $i] :
          ( ( X14 = k1_xboole_0 )
          | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
          | ~ ( v2_tops_2 @ X14 @ sk_A )
          | ( ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ X14 )
           != k1_xboole_0 )
          | ( r1_tarski @ ( sk_C @ X14 ) @ X14 ) ) ) ),
    inference('sup-',[status(thm)],['126','165'])).

thf('167',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_tarski @ ( sk_C @ ( sk_B_1 @ sk_A ) ) @ X0 )
        | ( ( sk_C @ ( sk_B_1 @ sk_A ) )
          = k1_xboole_0 )
        | ~ ( v3_finset_1 @ X0 )
        | ( ( sk_B_1 @ sk_A )
          = k1_xboole_0 )
        | ( v1_compts_1 @ sk_A )
        | ( v2_struct_0 @ sk_A ) )
   <= ( ! [X14: $i] :
          ( ( X14 = k1_xboole_0 )
          | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
          | ~ ( v2_tops_2 @ X14 @ sk_A )
          | ( ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ X14 )
           != k1_xboole_0 )
          | ( ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ X14 ) )
            = k1_xboole_0 ) )
      & ! [X14: $i] :
          ( ( X14 = k1_xboole_0 )
          | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
          | ~ ( v2_tops_2 @ X14 @ sk_A )
          | ( ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ X14 )
           != k1_xboole_0 )
          | ( v1_finset_1 @ ( sk_C @ X14 ) ) )
      & ! [X14: $i] :
          ( ( X14 = k1_xboole_0 )
          | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
          | ~ ( v2_tops_2 @ X14 @ sk_A )
          | ( ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ X14 )
           != k1_xboole_0 )
          | ( r1_tarski @ ( sk_C @ X14 ) @ X14 ) ) ) ),
    inference(simplify,[status(thm)],['166'])).

thf('168',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( ( sk_B_1 @ sk_A )
        = k1_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( ( sk_B_1 @ sk_A )
        = k1_xboole_0 )
      | ~ ( v3_finset_1 @ ( sk_B_1 @ sk_A ) )
      | ( ( sk_C @ ( sk_B_1 @ sk_A ) )
        = k1_xboole_0 ) )
   <= ( ! [X14: $i] :
          ( ( X14 = k1_xboole_0 )
          | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
          | ~ ( v2_tops_2 @ X14 @ sk_A )
          | ( ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ X14 )
           != k1_xboole_0 )
          | ( ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ X14 ) )
            = k1_xboole_0 ) )
      & ! [X14: $i] :
          ( ( X14 = k1_xboole_0 )
          | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
          | ~ ( v2_tops_2 @ X14 @ sk_A )
          | ( ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ X14 )
           != k1_xboole_0 )
          | ( v1_finset_1 @ ( sk_C @ X14 ) ) )
      & ! [X14: $i] :
          ( ( X14 = k1_xboole_0 )
          | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
          | ~ ( v2_tops_2 @ X14 @ sk_A )
          | ( ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ X14 )
           != k1_xboole_0 )
          | ( r1_tarski @ ( sk_C @ X14 ) @ X14 ) ) ) ),
    inference('sup-',[status(thm)],['108','167'])).

thf('169',plain,
    ( ( ( ( sk_C @ ( sk_B_1 @ sk_A ) )
        = k1_xboole_0 )
      | ~ ( v3_finset_1 @ ( sk_B_1 @ sk_A ) )
      | ( ( sk_B_1 @ sk_A )
        = k1_xboole_0 )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ! [X14: $i] :
          ( ( X14 = k1_xboole_0 )
          | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
          | ~ ( v2_tops_2 @ X14 @ sk_A )
          | ( ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ X14 )
           != k1_xboole_0 )
          | ( ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ X14 ) )
            = k1_xboole_0 ) )
      & ! [X14: $i] :
          ( ( X14 = k1_xboole_0 )
          | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
          | ~ ( v2_tops_2 @ X14 @ sk_A )
          | ( ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ X14 )
           != k1_xboole_0 )
          | ( v1_finset_1 @ ( sk_C @ X14 ) ) )
      & ! [X14: $i] :
          ( ( X14 = k1_xboole_0 )
          | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
          | ~ ( v2_tops_2 @ X14 @ sk_A )
          | ( ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ X14 )
           != k1_xboole_0 )
          | ( r1_tarski @ ( sk_C @ X14 ) @ X14 ) ) ) ),
    inference(simplify,[status(thm)],['168'])).

thf('170',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( ( sk_B_1 @ sk_A )
        = k1_xboole_0 )
      | ( ( sk_C @ ( sk_B_1 @ sk_A ) )
        = k1_xboole_0 ) )
   <= ( ! [X14: $i] :
          ( ( X14 = k1_xboole_0 )
          | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
          | ~ ( v2_tops_2 @ X14 @ sk_A )
          | ( ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ X14 )
           != k1_xboole_0 )
          | ( ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ X14 ) )
            = k1_xboole_0 ) )
      & ! [X14: $i] :
          ( ( X14 = k1_xboole_0 )
          | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
          | ~ ( v2_tops_2 @ X14 @ sk_A )
          | ( ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ X14 )
           != k1_xboole_0 )
          | ( v1_finset_1 @ ( sk_C @ X14 ) ) )
      & ! [X14: $i] :
          ( ( X14 = k1_xboole_0 )
          | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
          | ~ ( v2_tops_2 @ X14 @ sk_A )
          | ( ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ X14 )
           != k1_xboole_0 )
          | ( r1_tarski @ ( sk_C @ X14 ) @ X14 ) ) ) ),
    inference('sup-',[status(thm)],['89','169'])).

thf('171',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('172',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('173',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( ( sk_B_1 @ sk_A )
        = k1_xboole_0 )
      | ( ( sk_C @ ( sk_B_1 @ sk_A ) )
        = k1_xboole_0 ) )
   <= ( ! [X14: $i] :
          ( ( X14 = k1_xboole_0 )
          | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
          | ~ ( v2_tops_2 @ X14 @ sk_A )
          | ( ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ X14 )
           != k1_xboole_0 )
          | ( ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ X14 ) )
            = k1_xboole_0 ) )
      & ! [X14: $i] :
          ( ( X14 = k1_xboole_0 )
          | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
          | ~ ( v2_tops_2 @ X14 @ sk_A )
          | ( ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ X14 )
           != k1_xboole_0 )
          | ( v1_finset_1 @ ( sk_C @ X14 ) ) )
      & ! [X14: $i] :
          ( ( X14 = k1_xboole_0 )
          | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
          | ~ ( v2_tops_2 @ X14 @ sk_A )
          | ( ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ X14 )
           != k1_xboole_0 )
          | ( r1_tarski @ ( sk_C @ X14 ) @ X14 ) ) ) ),
    inference(demod,[status(thm)],['170','171','172'])).

thf('174',plain,
    ( ( ( ( sk_C @ ( sk_B_1 @ sk_A ) )
        = k1_xboole_0 )
      | ( ( sk_B_1 @ sk_A )
        = k1_xboole_0 )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ! [X14: $i] :
          ( ( X14 = k1_xboole_0 )
          | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
          | ~ ( v2_tops_2 @ X14 @ sk_A )
          | ( ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ X14 )
           != k1_xboole_0 )
          | ( ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ X14 ) )
            = k1_xboole_0 ) )
      & ! [X14: $i] :
          ( ( X14 = k1_xboole_0 )
          | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
          | ~ ( v2_tops_2 @ X14 @ sk_A )
          | ( ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ X14 )
           != k1_xboole_0 )
          | ( v1_finset_1 @ ( sk_C @ X14 ) ) )
      & ! [X14: $i] :
          ( ( X14 = k1_xboole_0 )
          | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
          | ~ ( v2_tops_2 @ X14 @ sk_A )
          | ( ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ X14 )
           != k1_xboole_0 )
          | ( r1_tarski @ ( sk_C @ X14 ) @ X14 ) ) ) ),
    inference(simplify,[status(thm)],['173'])).

thf('175',plain,(
    ! [X5: $i] :
      ( ( v2_tops_2 @ ( sk_B_1 @ X5 ) @ X5 )
      | ( v1_compts_1 @ X5 )
      | ~ ( l1_pre_topc @ X5 )
      | ~ ( v2_pre_topc @ X5 )
      | ( v2_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t13_compts_1])).

thf('176',plain,(
    ! [X5: $i] :
      ( ( ( k6_setfam_1 @ ( u1_struct_0 @ X5 ) @ ( sk_B_1 @ X5 ) )
        = k1_xboole_0 )
      | ( v1_compts_1 @ X5 )
      | ~ ( l1_pre_topc @ X5 )
      | ~ ( v2_pre_topc @ X5 )
      | ( v2_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t13_compts_1])).

thf('177',plain,(
    ! [X5: $i] :
      ( ( m1_subset_1 @ ( sk_B_1 @ X5 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) ) )
      | ( v1_compts_1 @ X5 )
      | ~ ( l1_pre_topc @ X5 )
      | ~ ( v2_pre_topc @ X5 )
      | ( v2_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t13_compts_1])).

thf('178',plain,
    ( ! [X14: $i] :
        ( ( X14 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
        | ~ ( v2_tops_2 @ X14 @ sk_A )
        | ( ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ X14 )
         != k1_xboole_0 )
        | ( ( sk_C @ X14 )
         != k1_xboole_0 ) )
   <= ! [X14: $i] :
        ( ( X14 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
        | ~ ( v2_tops_2 @ X14 @ sk_A )
        | ( ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ X14 )
         != k1_xboole_0 )
        | ( ( sk_C @ X14 )
         != k1_xboole_0 ) ) ),
    inference(split,[status(esa)],['4'])).

thf('179',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( ( sk_C @ ( sk_B_1 @ sk_A ) )
       != k1_xboole_0 )
      | ( ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B_1 @ sk_A ) )
       != k1_xboole_0 )
      | ~ ( v2_tops_2 @ ( sk_B_1 @ sk_A ) @ sk_A )
      | ( ( sk_B_1 @ sk_A )
        = k1_xboole_0 ) )
   <= ! [X14: $i] :
        ( ( X14 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
        | ~ ( v2_tops_2 @ X14 @ sk_A )
        | ( ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ X14 )
         != k1_xboole_0 )
        | ( ( sk_C @ X14 )
         != k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['177','178'])).

thf('180',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('181',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('182',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( ( sk_C @ ( sk_B_1 @ sk_A ) )
       != k1_xboole_0 )
      | ( ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B_1 @ sk_A ) )
       != k1_xboole_0 )
      | ~ ( v2_tops_2 @ ( sk_B_1 @ sk_A ) @ sk_A )
      | ( ( sk_B_1 @ sk_A )
        = k1_xboole_0 ) )
   <= ! [X14: $i] :
        ( ( X14 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
        | ~ ( v2_tops_2 @ X14 @ sk_A )
        | ( ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ X14 )
         != k1_xboole_0 )
        | ( ( sk_C @ X14 )
         != k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['179','180','181'])).

thf('183',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( ( sk_B_1 @ sk_A )
        = k1_xboole_0 )
      | ~ ( v2_tops_2 @ ( sk_B_1 @ sk_A ) @ sk_A )
      | ( ( sk_C @ ( sk_B_1 @ sk_A ) )
       != k1_xboole_0 )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X14: $i] :
        ( ( X14 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
        | ~ ( v2_tops_2 @ X14 @ sk_A )
        | ( ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ X14 )
         != k1_xboole_0 )
        | ( ( sk_C @ X14 )
         != k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['176','182'])).

thf('184',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('185',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('186',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( ( sk_B_1 @ sk_A )
        = k1_xboole_0 )
      | ~ ( v2_tops_2 @ ( sk_B_1 @ sk_A ) @ sk_A )
      | ( ( sk_C @ ( sk_B_1 @ sk_A ) )
       != k1_xboole_0 )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X14: $i] :
        ( ( X14 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
        | ~ ( v2_tops_2 @ X14 @ sk_A )
        | ( ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ X14 )
         != k1_xboole_0 )
        | ( ( sk_C @ X14 )
         != k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['183','184','185'])).

thf('187',plain,
    ( ( ( ( sk_C @ ( sk_B_1 @ sk_A ) )
       != k1_xboole_0 )
      | ~ ( v2_tops_2 @ ( sk_B_1 @ sk_A ) @ sk_A )
      | ( ( sk_B_1 @ sk_A )
        = k1_xboole_0 )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X14: $i] :
        ( ( X14 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
        | ~ ( v2_tops_2 @ X14 @ sk_A )
        | ( ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ X14 )
         != k1_xboole_0 )
        | ( ( sk_C @ X14 )
         != k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['186'])).

thf('188',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( ( sk_B_1 @ sk_A )
        = k1_xboole_0 )
      | ( ( sk_C @ ( sk_B_1 @ sk_A ) )
       != k1_xboole_0 ) )
   <= ! [X14: $i] :
        ( ( X14 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
        | ~ ( v2_tops_2 @ X14 @ sk_A )
        | ( ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ X14 )
         != k1_xboole_0 )
        | ( ( sk_C @ X14 )
         != k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['175','187'])).

thf('189',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('190',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('191',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( ( sk_B_1 @ sk_A )
        = k1_xboole_0 )
      | ( ( sk_C @ ( sk_B_1 @ sk_A ) )
       != k1_xboole_0 ) )
   <= ! [X14: $i] :
        ( ( X14 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
        | ~ ( v2_tops_2 @ X14 @ sk_A )
        | ( ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ X14 )
         != k1_xboole_0 )
        | ( ( sk_C @ X14 )
         != k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['188','189','190'])).

thf('192',plain,
    ( ( ( ( sk_C @ ( sk_B_1 @ sk_A ) )
       != k1_xboole_0 )
      | ( ( sk_B_1 @ sk_A )
        = k1_xboole_0 )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X14: $i] :
        ( ( X14 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
        | ~ ( v2_tops_2 @ X14 @ sk_A )
        | ( ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ X14 )
         != k1_xboole_0 )
        | ( ( sk_C @ X14 )
         != k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['191'])).

thf('193',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( ( sk_B_1 @ sk_A )
        = k1_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( ( sk_B_1 @ sk_A )
        = k1_xboole_0 ) )
   <= ( ! [X14: $i] :
          ( ( X14 = k1_xboole_0 )
          | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
          | ~ ( v2_tops_2 @ X14 @ sk_A )
          | ( ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ X14 )
           != k1_xboole_0 )
          | ( ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ X14 ) )
            = k1_xboole_0 ) )
      & ! [X14: $i] :
          ( ( X14 = k1_xboole_0 )
          | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
          | ~ ( v2_tops_2 @ X14 @ sk_A )
          | ( ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ X14 )
           != k1_xboole_0 )
          | ( v1_finset_1 @ ( sk_C @ X14 ) ) )
      & ! [X14: $i] :
          ( ( X14 = k1_xboole_0 )
          | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
          | ~ ( v2_tops_2 @ X14 @ sk_A )
          | ( ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ X14 )
           != k1_xboole_0 )
          | ( r1_tarski @ ( sk_C @ X14 ) @ X14 ) )
      & ! [X14: $i] :
          ( ( X14 = k1_xboole_0 )
          | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
          | ~ ( v2_tops_2 @ X14 @ sk_A )
          | ( ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ X14 )
           != k1_xboole_0 )
          | ( ( sk_C @ X14 )
           != k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['174','192'])).

thf('194',plain,
    ( ( ( ( sk_B_1 @ sk_A )
        = k1_xboole_0 )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ! [X14: $i] :
          ( ( X14 = k1_xboole_0 )
          | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
          | ~ ( v2_tops_2 @ X14 @ sk_A )
          | ( ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ X14 )
           != k1_xboole_0 )
          | ( ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ X14 ) )
            = k1_xboole_0 ) )
      & ! [X14: $i] :
          ( ( X14 = k1_xboole_0 )
          | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
          | ~ ( v2_tops_2 @ X14 @ sk_A )
          | ( ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ X14 )
           != k1_xboole_0 )
          | ( v1_finset_1 @ ( sk_C @ X14 ) ) )
      & ! [X14: $i] :
          ( ( X14 = k1_xboole_0 )
          | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
          | ~ ( v2_tops_2 @ X14 @ sk_A )
          | ( ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ X14 )
           != k1_xboole_0 )
          | ( r1_tarski @ ( sk_C @ X14 ) @ X14 ) )
      & ! [X14: $i] :
          ( ( X14 = k1_xboole_0 )
          | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
          | ~ ( v2_tops_2 @ X14 @ sk_A )
          | ( ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ X14 )
           != k1_xboole_0 )
          | ( ( sk_C @ X14 )
           != k1_xboole_0 ) ) ) ),
    inference(simplify,[status(thm)],['193'])).

thf('195',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('196',plain,
    ( ( ( v1_compts_1 @ sk_A )
      | ( ( sk_B_1 @ sk_A )
        = k1_xboole_0 ) )
   <= ( ! [X14: $i] :
          ( ( X14 = k1_xboole_0 )
          | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
          | ~ ( v2_tops_2 @ X14 @ sk_A )
          | ( ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ X14 )
           != k1_xboole_0 )
          | ( ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ X14 ) )
            = k1_xboole_0 ) )
      & ! [X14: $i] :
          ( ( X14 = k1_xboole_0 )
          | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
          | ~ ( v2_tops_2 @ X14 @ sk_A )
          | ( ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ X14 )
           != k1_xboole_0 )
          | ( v1_finset_1 @ ( sk_C @ X14 ) ) )
      & ! [X14: $i] :
          ( ( X14 = k1_xboole_0 )
          | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
          | ~ ( v2_tops_2 @ X14 @ sk_A )
          | ( ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ X14 )
           != k1_xboole_0 )
          | ( r1_tarski @ ( sk_C @ X14 ) @ X14 ) )
      & ! [X14: $i] :
          ( ( X14 = k1_xboole_0 )
          | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
          | ~ ( v2_tops_2 @ X14 @ sk_A )
          | ( ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ X14 )
           != k1_xboole_0 )
          | ( ( sk_C @ X14 )
           != k1_xboole_0 ) ) ) ),
    inference(clc,[status(thm)],['194','195'])).

thf('197',plain,(
    ! [X5: $i] :
      ( ( v3_finset_1 @ ( sk_B_1 @ X5 ) )
      | ( v1_compts_1 @ X5 )
      | ~ ( l1_pre_topc @ X5 )
      | ~ ( v2_pre_topc @ X5 )
      | ( v2_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t13_compts_1])).

thf('198',plain,
    ( ( ( v3_finset_1 @ k1_xboole_0 )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v1_compts_1 @ sk_A ) )
   <= ( ! [X14: $i] :
          ( ( X14 = k1_xboole_0 )
          | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
          | ~ ( v2_tops_2 @ X14 @ sk_A )
          | ( ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ X14 )
           != k1_xboole_0 )
          | ( ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ X14 ) )
            = k1_xboole_0 ) )
      & ! [X14: $i] :
          ( ( X14 = k1_xboole_0 )
          | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
          | ~ ( v2_tops_2 @ X14 @ sk_A )
          | ( ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ X14 )
           != k1_xboole_0 )
          | ( v1_finset_1 @ ( sk_C @ X14 ) ) )
      & ! [X14: $i] :
          ( ( X14 = k1_xboole_0 )
          | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
          | ~ ( v2_tops_2 @ X14 @ sk_A )
          | ( ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ X14 )
           != k1_xboole_0 )
          | ( r1_tarski @ ( sk_C @ X14 ) @ X14 ) )
      & ! [X14: $i] :
          ( ( X14 = k1_xboole_0 )
          | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
          | ~ ( v2_tops_2 @ X14 @ sk_A )
          | ( ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ X14 )
           != k1_xboole_0 )
          | ( ( sk_C @ X14 )
           != k1_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['196','197'])).

thf('199',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('200',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('201',plain,
    ( ( ( v3_finset_1 @ k1_xboole_0 )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A ) )
   <= ( ! [X14: $i] :
          ( ( X14 = k1_xboole_0 )
          | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
          | ~ ( v2_tops_2 @ X14 @ sk_A )
          | ( ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ X14 )
           != k1_xboole_0 )
          | ( ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ X14 ) )
            = k1_xboole_0 ) )
      & ! [X14: $i] :
          ( ( X14 = k1_xboole_0 )
          | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
          | ~ ( v2_tops_2 @ X14 @ sk_A )
          | ( ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ X14 )
           != k1_xboole_0 )
          | ( v1_finset_1 @ ( sk_C @ X14 ) ) )
      & ! [X14: $i] :
          ( ( X14 = k1_xboole_0 )
          | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
          | ~ ( v2_tops_2 @ X14 @ sk_A )
          | ( ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ X14 )
           != k1_xboole_0 )
          | ( r1_tarski @ ( sk_C @ X14 ) @ X14 ) )
      & ! [X14: $i] :
          ( ( X14 = k1_xboole_0 )
          | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
          | ~ ( v2_tops_2 @ X14 @ sk_A )
          | ( ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ X14 )
           != k1_xboole_0 )
          | ( ( sk_C @ X14 )
           != k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['198','199','200'])).

thf('202',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v3_finset_1 @ k1_xboole_0 ) )
   <= ( ! [X14: $i] :
          ( ( X14 = k1_xboole_0 )
          | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
          | ~ ( v2_tops_2 @ X14 @ sk_A )
          | ( ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ X14 )
           != k1_xboole_0 )
          | ( ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ X14 ) )
            = k1_xboole_0 ) )
      & ! [X14: $i] :
          ( ( X14 = k1_xboole_0 )
          | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
          | ~ ( v2_tops_2 @ X14 @ sk_A )
          | ( ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ X14 )
           != k1_xboole_0 )
          | ( v1_finset_1 @ ( sk_C @ X14 ) ) )
      & ! [X14: $i] :
          ( ( X14 = k1_xboole_0 )
          | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
          | ~ ( v2_tops_2 @ X14 @ sk_A )
          | ( ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ X14 )
           != k1_xboole_0 )
          | ( r1_tarski @ ( sk_C @ X14 ) @ X14 ) )
      & ! [X14: $i] :
          ( ( X14 = k1_xboole_0 )
          | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
          | ~ ( v2_tops_2 @ X14 @ sk_A )
          | ( ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ X14 )
           != k1_xboole_0 )
          | ( ( sk_C @ X14 )
           != k1_xboole_0 ) ) ) ),
    inference(simplify,[status(thm)],['201'])).

thf('203',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('204',plain,
    ( ( ( v3_finset_1 @ k1_xboole_0 )
      | ( v1_compts_1 @ sk_A ) )
   <= ( ! [X14: $i] :
          ( ( X14 = k1_xboole_0 )
          | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
          | ~ ( v2_tops_2 @ X14 @ sk_A )
          | ( ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ X14 )
           != k1_xboole_0 )
          | ( ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ X14 ) )
            = k1_xboole_0 ) )
      & ! [X14: $i] :
          ( ( X14 = k1_xboole_0 )
          | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
          | ~ ( v2_tops_2 @ X14 @ sk_A )
          | ( ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ X14 )
           != k1_xboole_0 )
          | ( v1_finset_1 @ ( sk_C @ X14 ) ) )
      & ! [X14: $i] :
          ( ( X14 = k1_xboole_0 )
          | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
          | ~ ( v2_tops_2 @ X14 @ sk_A )
          | ( ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ X14 )
           != k1_xboole_0 )
          | ( r1_tarski @ ( sk_C @ X14 ) @ X14 ) )
      & ! [X14: $i] :
          ( ( X14 = k1_xboole_0 )
          | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
          | ~ ( v2_tops_2 @ X14 @ sk_A )
          | ( ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ X14 )
           != k1_xboole_0 )
          | ( ( sk_C @ X14 )
           != k1_xboole_0 ) ) ) ),
    inference(clc,[status(thm)],['202','203'])).

thf('205',plain,(
    ! [X0: $i] :
      ( ( X0 != k1_xboole_0 )
      | ~ ( v3_finset_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d3_finset_1])).

thf('206',plain,(
    ~ ( v3_finset_1 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['205'])).

thf('207',plain,
    ( ( v1_compts_1 @ sk_A )
   <= ( ! [X14: $i] :
          ( ( X14 = k1_xboole_0 )
          | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
          | ~ ( v2_tops_2 @ X14 @ sk_A )
          | ( ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ X14 )
           != k1_xboole_0 )
          | ( ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ X14 ) )
            = k1_xboole_0 ) )
      & ! [X14: $i] :
          ( ( X14 = k1_xboole_0 )
          | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
          | ~ ( v2_tops_2 @ X14 @ sk_A )
          | ( ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ X14 )
           != k1_xboole_0 )
          | ( v1_finset_1 @ ( sk_C @ X14 ) ) )
      & ! [X14: $i] :
          ( ( X14 = k1_xboole_0 )
          | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
          | ~ ( v2_tops_2 @ X14 @ sk_A )
          | ( ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ X14 )
           != k1_xboole_0 )
          | ( r1_tarski @ ( sk_C @ X14 ) @ X14 ) )
      & ! [X14: $i] :
          ( ( X14 = k1_xboole_0 )
          | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
          | ~ ( v2_tops_2 @ X14 @ sk_A )
          | ( ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ X14 )
           != k1_xboole_0 )
          | ( ( sk_C @ X14 )
           != k1_xboole_0 ) ) ) ),
    inference(clc,[status(thm)],['204','206'])).

thf('208',plain,
    ( ~ ( v1_compts_1 @ sk_A )
   <= ~ ( v1_compts_1 @ sk_A ) ),
    inference(split,[status(esa)],['6'])).

thf('209',plain,
    ( ~ ! [X14: $i] :
          ( ( X14 = k1_xboole_0 )
          | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
          | ~ ( v2_tops_2 @ X14 @ sk_A )
          | ( ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ X14 )
           != k1_xboole_0 )
          | ( r1_tarski @ ( sk_C @ X14 ) @ X14 ) )
    | ~ ! [X14: $i] :
          ( ( X14 = k1_xboole_0 )
          | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
          | ~ ( v2_tops_2 @ X14 @ sk_A )
          | ( ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ X14 )
           != k1_xboole_0 )
          | ( ( sk_C @ X14 )
           != k1_xboole_0 ) )
    | ~ ! [X14: $i] :
          ( ( X14 = k1_xboole_0 )
          | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
          | ~ ( v2_tops_2 @ X14 @ sk_A )
          | ( ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ X14 )
           != k1_xboole_0 )
          | ( v1_finset_1 @ ( sk_C @ X14 ) ) )
    | ~ ! [X14: $i] :
          ( ( X14 = k1_xboole_0 )
          | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
          | ~ ( v2_tops_2 @ X14 @ sk_A )
          | ( ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ X14 )
           != k1_xboole_0 )
          | ( ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ X14 ) )
            = k1_xboole_0 ) )
    | ( v1_compts_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['207','208'])).

thf('210',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','3','5','7','9','11','13','15','86','88','209'])).


%------------------------------------------------------------------------------
