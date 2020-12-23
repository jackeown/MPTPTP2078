%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.e4NobHJvEt

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:13:17 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  117 ( 277 expanded)
%              Number of leaves         :   25 (  88 expanded)
%              Depth                    :   21
%              Number of atoms          :  984 (3098 expanded)
%              Number of equality atoms :   31 (  59 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v1_tops_1_type,type,(
    v1_tops_1: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(v3_tex_2_type,type,(
    v3_tex_2: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

thf(v1_tdlat_3_type,type,(
    v1_tdlat_3: $i > $o )).

thf(t49_tex_2,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( v1_tdlat_3 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v3_tex_2 @ B @ A )
          <=> ~ ( v1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( v1_tdlat_3 @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( ( v3_tex_2 @ B @ A )
            <=> ~ ( v1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t49_tex_2])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(rc4_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ? [B: $i] :
          ( ( v1_tops_1 @ B @ A )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('1',plain,(
    ! [X5: $i] :
      ( ( v1_tops_1 @ ( sk_B @ X5 ) @ X5 )
      | ~ ( l1_pre_topc @ X5 ) ) ),
    inference(cnf,[status(esa)],[rc4_tops_1])).

thf('2',plain,(
    ! [X5: $i] :
      ( ( m1_subset_1 @ ( sk_B @ X5 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) )
      | ~ ( l1_pre_topc @ X5 ) ) ),
    inference(cnf,[status(esa)],[rc4_tops_1])).

thf(t43_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( v1_tdlat_3 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( v2_tex_2 @ B @ A ) ) ) )).

thf('3',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ( v2_tex_2 @ X12 @ X13 )
      | ~ ( l1_pre_topc @ X13 )
      | ~ ( v1_tdlat_3 @ X13 )
      | ~ ( v2_pre_topc @ X13 )
      | ( v2_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t43_tex_2])).

thf('4',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( v1_tdlat_3 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_tex_2 @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( v2_tex_2 @ ( sk_B @ X0 ) @ X0 )
      | ~ ( v1_tdlat_3 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,(
    ! [X5: $i] :
      ( ( m1_subset_1 @ ( sk_B @ X5 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) )
      | ~ ( l1_pre_topc @ X5 ) ) ),
    inference(cnf,[status(esa)],[rc4_tops_1])).

thf(t48_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( ( v1_tops_1 @ B @ A )
              & ( v2_tex_2 @ B @ A ) )
           => ( v3_tex_2 @ B @ A ) ) ) ) )).

thf('7',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ( v3_tex_2 @ X14 @ X15 )
      | ~ ( v2_tex_2 @ X14 @ X15 )
      | ~ ( v1_tops_1 @ X14 @ X15 )
      | ~ ( l1_pre_topc @ X15 )
      | ~ ( v2_pre_topc @ X15 )
      | ( v2_struct_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t48_tex_2])).

thf('8',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_tops_1 @ ( sk_B @ X0 ) @ X0 )
      | ~ ( v2_tex_2 @ ( sk_B @ X0 ) @ X0 )
      | ( v3_tex_2 @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( v3_tex_2 @ ( sk_B @ X0 ) @ X0 )
      | ~ ( v2_tex_2 @ ( sk_B @ X0 ) @ X0 )
      | ~ ( v1_tops_1 @ ( sk_B @ X0 ) @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( v1_tdlat_3 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( v1_tops_1 @ ( sk_B @ X0 ) @ X0 )
      | ( v3_tex_2 @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( v3_tex_2 @ ( sk_B @ X0 ) @ X0 )
      | ~ ( v1_tops_1 @ ( sk_B @ X0 ) @ X0 )
      | ~ ( v1_tdlat_3 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( v1_tdlat_3 @ X0 )
      | ( v3_tex_2 @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( v3_tex_2 @ ( sk_B @ X0 ) @ X0 )
      | ~ ( v1_tdlat_3 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('14',plain,(
    ! [X1: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X1 ) @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k2_subset_1 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('16',plain,(
    ! [X1: $i] :
      ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ( v2_tex_2 @ X12 @ X13 )
      | ~ ( l1_pre_topc @ X13 )
      | ~ ( v1_tdlat_3 @ X13 )
      | ~ ( v2_pre_topc @ X13 )
      | ( v2_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t43_tex_2])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( v1_tdlat_3 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_tex_2 @ ( u1_struct_0 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X5: $i] :
      ( ( m1_subset_1 @ ( sk_B @ X5 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) )
      | ~ ( l1_pre_topc @ X5 ) ) ),
    inference(cnf,[status(esa)],[rc4_tops_1])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('20',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_tarski @ X2 @ X3 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( r1_tarski @ ( sk_B @ X0 ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X1: $i] :
      ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('23',plain,(
    ! [X5: $i] :
      ( ( m1_subset_1 @ ( sk_B @ X5 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) )
      | ~ ( l1_pre_topc @ X5 ) ) ),
    inference(cnf,[status(esa)],[rc4_tops_1])).

thf(d7_tex_2,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v3_tex_2 @ B @ A )
          <=> ( ( v2_tex_2 @ B @ A )
              & ! [C: $i] :
                  ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                 => ( ( ( v2_tex_2 @ C @ A )
                      & ( r1_tarski @ B @ C ) )
                   => ( B = C ) ) ) ) ) ) ) )).

thf('24',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ~ ( v3_tex_2 @ X9 @ X10 )
      | ~ ( v2_tex_2 @ X11 @ X10 )
      | ~ ( r1_tarski @ X9 @ X11 )
      | ( X9 = X11 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ~ ( l1_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[d7_tex_2])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( ( sk_B @ X0 )
        = X1 )
      | ~ ( r1_tarski @ ( sk_B @ X0 ) @ X1 )
      | ~ ( v2_tex_2 @ X1 @ X0 )
      | ~ ( v3_tex_2 @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_tex_2 @ ( sk_B @ X0 ) @ X0 )
      | ~ ( v2_tex_2 @ X1 @ X0 )
      | ~ ( r1_tarski @ ( sk_B @ X0 ) @ X1 )
      | ( ( sk_B @ X0 )
        = X1 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( sk_B @ X0 )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( r1_tarski @ ( sk_B @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v2_tex_2 @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( v3_tex_2 @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['22','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v3_tex_2 @ ( sk_B @ X0 ) @ X0 )
      | ~ ( v2_tex_2 @ ( u1_struct_0 @ X0 ) @ X0 )
      | ( ( sk_B @ X0 )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['21','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( ( sk_B @ X0 )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( v2_tex_2 @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( v3_tex_2 @ ( sk_B @ X0 ) @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_tdlat_3 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v3_tex_2 @ ( sk_B @ X0 ) @ X0 )
      | ( ( sk_B @ X0 )
        = ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['18','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( ( sk_B @ X0 )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( v3_tex_2 @ ( sk_B @ X0 ) @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( v1_tdlat_3 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( v1_tdlat_3 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_tdlat_3 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( ( sk_B @ X0 )
        = ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['13','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( ( sk_B @ X0 )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( v1_tdlat_3 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d7_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( v1_subset_1 @ B @ A )
      <=> ( B != A ) ) ) )).

thf('35',plain,(
    ! [X7: $i,X8: $i] :
      ( ( X8 = X7 )
      | ( v1_subset_1 @ X8 @ X7 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[d7_subset_1])).

thf('36',plain,
    ( ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
    | ( sk_B_1
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,
    ( ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
    | ( v3_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['37'])).

thf('39',plain,
    ( ( sk_B_1
      = ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['36','38'])).

thf('40',plain,
    ( ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
    | ( v3_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['37'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( v1_tdlat_3 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_tex_2 @ ( u1_struct_0 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('42',plain,(
    ! [X1: $i] :
      ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('43',plain,
    ( ( v3_tex_2 @ sk_B_1 @ sk_A )
   <= ( v3_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['37'])).

thf('44',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ~ ( v3_tex_2 @ X9 @ X10 )
      | ~ ( v2_tex_2 @ X11 @ X10 )
      | ~ ( r1_tarski @ X9 @ X11 )
      | ( X9 = X11 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ~ ( l1_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[d7_tex_2])).

thf('46',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( sk_B_1 = X0 )
      | ~ ( r1_tarski @ sk_B_1 @ X0 )
      | ~ ( v2_tex_2 @ X0 @ sk_A )
      | ~ ( v3_tex_2 @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( sk_B_1 = X0 )
      | ~ ( r1_tarski @ sk_B_1 @ X0 )
      | ~ ( v2_tex_2 @ X0 @ sk_A )
      | ~ ( v3_tex_2 @ sk_B_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,
    ( ! [X0: $i] :
        ( ~ ( v2_tex_2 @ X0 @ sk_A )
        | ~ ( r1_tarski @ sk_B_1 @ X0 )
        | ( sk_B_1 = X0 )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ( v3_tex_2 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['43','48'])).

thf('50',plain,
    ( ( ( sk_B_1
        = ( u1_struct_0 @ sk_A ) )
      | ~ ( r1_tarski @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v2_tex_2 @ ( u1_struct_0 @ sk_A ) @ sk_A ) )
   <= ( v3_tex_2 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['42','49'])).

thf('51',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_tarski @ X2 @ X3 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('53',plain,(
    r1_tarski @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,
    ( ( ( sk_B_1
        = ( u1_struct_0 @ sk_A ) )
      | ~ ( v2_tex_2 @ ( u1_struct_0 @ sk_A ) @ sk_A ) )
   <= ( v3_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['50','53'])).

thf('55',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( v1_tdlat_3 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( sk_B_1
        = ( u1_struct_0 @ sk_A ) ) )
   <= ( v3_tex_2 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['41','54'])).

thf('56',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    v1_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( sk_B_1
        = ( u1_struct_0 @ sk_A ) ) )
   <= ( v3_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['55','56','57','58'])).

thf('60',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,
    ( ( sk_B_1
      = ( u1_struct_0 @ sk_A ) )
   <= ( v3_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['59','60'])).

thf('62',plain,
    ( ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v3_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,
    ( ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
   <= ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['62'])).

thf('64',plain,
    ( ( v1_subset_1 @ sk_B_1 @ sk_B_1 )
   <= ( ( v3_tex_2 @ sk_B_1 @ sk_A )
      & ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['61','63'])).

thf('65',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v1_subset_1 @ X8 @ X7 )
      | ( X8 != X7 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[d7_subset_1])).

thf('66',plain,(
    ! [X7: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X7 ) )
      | ~ ( v1_subset_1 @ X7 @ X7 ) ) ),
    inference(simplify,[status(thm)],['65'])).

thf('67',plain,(
    ! [X1: $i] :
      ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('68',plain,(
    ! [X7: $i] :
      ~ ( v1_subset_1 @ X7 @ X7 ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('69',plain,
    ( ~ ( v3_tex_2 @ sk_B_1 @ sk_A )
    | ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['64','68'])).

thf('70',plain,(
    ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sat_resolution*',[status(thm)],['40','69'])).

thf('71',plain,
    ( sk_B_1
    = ( u1_struct_0 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['39','70'])).

thf('72',plain,
    ( ( sk_B_1
      = ( sk_B @ sk_A ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( v1_tdlat_3 @ sk_A ) ),
    inference('sup+',[status(thm)],['33','71'])).

thf('73',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    v1_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,
    ( ( sk_B_1
      = ( sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['72','73','74','75'])).

thf('77',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,
    ( sk_B_1
    = ( sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X0: $i] :
      ( ( v3_tex_2 @ ( sk_B @ X0 ) @ X0 )
      | ~ ( v1_tdlat_3 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('80',plain,
    ( ( v3_tex_2 @ sk_B_1 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( v1_tdlat_3 @ sk_A ) ),
    inference('sup+',[status(thm)],['78','79'])).

thf('81',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    v1_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,
    ( ( v3_tex_2 @ sk_B_1 @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['80','81','82','83'])).

thf('85',plain,
    ( ~ ( v3_tex_2 @ sk_B_1 @ sk_A )
   <= ~ ( v3_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['62'])).

thf('86',plain,
    ( ~ ( v3_tex_2 @ sk_B_1 @ sk_A )
    | ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['62'])).

thf('87',plain,(
    ~ ( v3_tex_2 @ sk_B_1 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['40','69','86'])).

thf('88',plain,(
    ~ ( v3_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['85','87'])).

thf('89',plain,(
    v2_struct_0 @ sk_A ),
    inference(clc,[status(thm)],['84','88'])).

thf('90',plain,(
    $false ),
    inference(demod,[status(thm)],['0','89'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.e4NobHJvEt
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:44:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.55  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.55  % Solved by: fo/fo7.sh
% 0.21/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.55  % done 171 iterations in 0.094s
% 0.21/0.55  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.55  % SZS output start Refutation
% 0.21/0.55  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.55  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.21/0.55  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.55  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.55  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.21/0.55  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.21/0.55  thf(v1_tops_1_type, type, v1_tops_1: $i > $i > $o).
% 0.21/0.55  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.21/0.55  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.21/0.55  thf(v3_tex_2_type, type, v3_tex_2: $i > $i > $o).
% 0.21/0.55  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.55  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.21/0.55  thf(sk_B_type, type, sk_B: $i > $i).
% 0.21/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.55  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 0.21/0.55  thf(v1_tdlat_3_type, type, v1_tdlat_3: $i > $o).
% 0.21/0.55  thf(t49_tex_2, conjecture,
% 0.21/0.55    (![A:$i]:
% 0.21/0.55     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v1_tdlat_3 @ A ) & 
% 0.21/0.55         ( l1_pre_topc @ A ) ) =>
% 0.21/0.55       ( ![B:$i]:
% 0.21/0.55         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.55           ( ( v3_tex_2 @ B @ A ) <=>
% 0.21/0.55             ( ~( v1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) ) ) ) ))).
% 0.21/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.55    (~( ![A:$i]:
% 0.21/0.55        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.21/0.55            ( v1_tdlat_3 @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.55          ( ![B:$i]:
% 0.21/0.55            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.55              ( ( v3_tex_2 @ B @ A ) <=>
% 0.21/0.55                ( ~( v1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) ) ) ) ) )),
% 0.21/0.55    inference('cnf.neg', [status(esa)], [t49_tex_2])).
% 0.21/0.55  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf(rc4_tops_1, axiom,
% 0.21/0.55    (![A:$i]:
% 0.21/0.55     ( ( l1_pre_topc @ A ) =>
% 0.21/0.55       ( ?[B:$i]:
% 0.21/0.55         ( ( v1_tops_1 @ B @ A ) & 
% 0.21/0.55           ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.21/0.55  thf('1', plain,
% 0.21/0.55      (![X5 : $i]: ((v1_tops_1 @ (sk_B @ X5) @ X5) | ~ (l1_pre_topc @ X5))),
% 0.21/0.55      inference('cnf', [status(esa)], [rc4_tops_1])).
% 0.21/0.55  thf('2', plain,
% 0.21/0.55      (![X5 : $i]:
% 0.21/0.55         ((m1_subset_1 @ (sk_B @ X5) @ (k1_zfmisc_1 @ (u1_struct_0 @ X5)))
% 0.21/0.55          | ~ (l1_pre_topc @ X5))),
% 0.21/0.55      inference('cnf', [status(esa)], [rc4_tops_1])).
% 0.21/0.55  thf(t43_tex_2, axiom,
% 0.21/0.55    (![A:$i]:
% 0.21/0.55     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v1_tdlat_3 @ A ) & 
% 0.21/0.55         ( l1_pre_topc @ A ) ) =>
% 0.21/0.55       ( ![B:$i]:
% 0.21/0.55         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.55           ( v2_tex_2 @ B @ A ) ) ) ))).
% 0.21/0.55  thf('3', plain,
% 0.21/0.55      (![X12 : $i, X13 : $i]:
% 0.21/0.55         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.21/0.55          | (v2_tex_2 @ X12 @ X13)
% 0.21/0.55          | ~ (l1_pre_topc @ X13)
% 0.21/0.55          | ~ (v1_tdlat_3 @ X13)
% 0.21/0.55          | ~ (v2_pre_topc @ X13)
% 0.21/0.55          | (v2_struct_0 @ X13))),
% 0.21/0.55      inference('cnf', [status(esa)], [t43_tex_2])).
% 0.21/0.55  thf('4', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         (~ (l1_pre_topc @ X0)
% 0.21/0.55          | (v2_struct_0 @ X0)
% 0.21/0.55          | ~ (v2_pre_topc @ X0)
% 0.21/0.55          | ~ (v1_tdlat_3 @ X0)
% 0.21/0.55          | ~ (l1_pre_topc @ X0)
% 0.21/0.55          | (v2_tex_2 @ (sk_B @ X0) @ X0))),
% 0.21/0.55      inference('sup-', [status(thm)], ['2', '3'])).
% 0.21/0.55  thf('5', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         ((v2_tex_2 @ (sk_B @ X0) @ X0)
% 0.21/0.55          | ~ (v1_tdlat_3 @ X0)
% 0.21/0.55          | ~ (v2_pre_topc @ X0)
% 0.21/0.55          | (v2_struct_0 @ X0)
% 0.21/0.55          | ~ (l1_pre_topc @ X0))),
% 0.21/0.55      inference('simplify', [status(thm)], ['4'])).
% 0.21/0.55  thf('6', plain,
% 0.21/0.55      (![X5 : $i]:
% 0.21/0.55         ((m1_subset_1 @ (sk_B @ X5) @ (k1_zfmisc_1 @ (u1_struct_0 @ X5)))
% 0.21/0.55          | ~ (l1_pre_topc @ X5))),
% 0.21/0.55      inference('cnf', [status(esa)], [rc4_tops_1])).
% 0.21/0.55  thf(t48_tex_2, axiom,
% 0.21/0.55    (![A:$i]:
% 0.21/0.55     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.55       ( ![B:$i]:
% 0.21/0.55         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.55           ( ( ( v1_tops_1 @ B @ A ) & ( v2_tex_2 @ B @ A ) ) =>
% 0.21/0.55             ( v3_tex_2 @ B @ A ) ) ) ) ))).
% 0.21/0.55  thf('7', plain,
% 0.21/0.55      (![X14 : $i, X15 : $i]:
% 0.21/0.55         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.21/0.55          | (v3_tex_2 @ X14 @ X15)
% 0.21/0.55          | ~ (v2_tex_2 @ X14 @ X15)
% 0.21/0.55          | ~ (v1_tops_1 @ X14 @ X15)
% 0.21/0.55          | ~ (l1_pre_topc @ X15)
% 0.21/0.55          | ~ (v2_pre_topc @ X15)
% 0.21/0.55          | (v2_struct_0 @ X15))),
% 0.21/0.55      inference('cnf', [status(esa)], [t48_tex_2])).
% 0.21/0.55  thf('8', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         (~ (l1_pre_topc @ X0)
% 0.21/0.55          | (v2_struct_0 @ X0)
% 0.21/0.55          | ~ (v2_pre_topc @ X0)
% 0.21/0.55          | ~ (l1_pre_topc @ X0)
% 0.21/0.55          | ~ (v1_tops_1 @ (sk_B @ X0) @ X0)
% 0.21/0.55          | ~ (v2_tex_2 @ (sk_B @ X0) @ X0)
% 0.21/0.55          | (v3_tex_2 @ (sk_B @ X0) @ X0))),
% 0.21/0.55      inference('sup-', [status(thm)], ['6', '7'])).
% 0.21/0.55  thf('9', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         ((v3_tex_2 @ (sk_B @ X0) @ X0)
% 0.21/0.55          | ~ (v2_tex_2 @ (sk_B @ X0) @ X0)
% 0.21/0.55          | ~ (v1_tops_1 @ (sk_B @ X0) @ X0)
% 0.21/0.55          | ~ (v2_pre_topc @ X0)
% 0.21/0.55          | (v2_struct_0 @ X0)
% 0.21/0.55          | ~ (l1_pre_topc @ X0))),
% 0.21/0.55      inference('simplify', [status(thm)], ['8'])).
% 0.21/0.55  thf('10', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         (~ (l1_pre_topc @ X0)
% 0.21/0.55          | (v2_struct_0 @ X0)
% 0.21/0.55          | ~ (v2_pre_topc @ X0)
% 0.21/0.55          | ~ (v1_tdlat_3 @ X0)
% 0.21/0.55          | ~ (l1_pre_topc @ X0)
% 0.21/0.55          | (v2_struct_0 @ X0)
% 0.21/0.55          | ~ (v2_pre_topc @ X0)
% 0.21/0.55          | ~ (v1_tops_1 @ (sk_B @ X0) @ X0)
% 0.21/0.55          | (v3_tex_2 @ (sk_B @ X0) @ X0))),
% 0.21/0.55      inference('sup-', [status(thm)], ['5', '9'])).
% 0.21/0.55  thf('11', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         ((v3_tex_2 @ (sk_B @ X0) @ X0)
% 0.21/0.55          | ~ (v1_tops_1 @ (sk_B @ X0) @ X0)
% 0.21/0.55          | ~ (v1_tdlat_3 @ X0)
% 0.21/0.55          | ~ (v2_pre_topc @ X0)
% 0.21/0.55          | (v2_struct_0 @ X0)
% 0.21/0.55          | ~ (l1_pre_topc @ X0))),
% 0.21/0.55      inference('simplify', [status(thm)], ['10'])).
% 0.21/0.55  thf('12', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         (~ (l1_pre_topc @ X0)
% 0.21/0.55          | ~ (l1_pre_topc @ X0)
% 0.21/0.55          | (v2_struct_0 @ X0)
% 0.21/0.55          | ~ (v2_pre_topc @ X0)
% 0.21/0.55          | ~ (v1_tdlat_3 @ X0)
% 0.21/0.55          | (v3_tex_2 @ (sk_B @ X0) @ X0))),
% 0.21/0.55      inference('sup-', [status(thm)], ['1', '11'])).
% 0.21/0.55  thf('13', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         ((v3_tex_2 @ (sk_B @ X0) @ X0)
% 0.21/0.55          | ~ (v1_tdlat_3 @ X0)
% 0.21/0.55          | ~ (v2_pre_topc @ X0)
% 0.21/0.55          | (v2_struct_0 @ X0)
% 0.21/0.55          | ~ (l1_pre_topc @ X0))),
% 0.21/0.55      inference('simplify', [status(thm)], ['12'])).
% 0.21/0.55  thf(dt_k2_subset_1, axiom,
% 0.21/0.55    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.21/0.55  thf('14', plain,
% 0.21/0.55      (![X1 : $i]: (m1_subset_1 @ (k2_subset_1 @ X1) @ (k1_zfmisc_1 @ X1))),
% 0.21/0.55      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 0.21/0.55  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.21/0.55  thf('15', plain, (![X0 : $i]: ((k2_subset_1 @ X0) = (X0))),
% 0.21/0.55      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.21/0.55  thf('16', plain, (![X1 : $i]: (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X1))),
% 0.21/0.55      inference('demod', [status(thm)], ['14', '15'])).
% 0.21/0.55  thf('17', plain,
% 0.21/0.55      (![X12 : $i, X13 : $i]:
% 0.21/0.55         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.21/0.55          | (v2_tex_2 @ X12 @ X13)
% 0.21/0.55          | ~ (l1_pre_topc @ X13)
% 0.21/0.55          | ~ (v1_tdlat_3 @ X13)
% 0.21/0.55          | ~ (v2_pre_topc @ X13)
% 0.21/0.55          | (v2_struct_0 @ X13))),
% 0.21/0.55      inference('cnf', [status(esa)], [t43_tex_2])).
% 0.21/0.55  thf('18', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         ((v2_struct_0 @ X0)
% 0.21/0.55          | ~ (v2_pre_topc @ X0)
% 0.21/0.55          | ~ (v1_tdlat_3 @ X0)
% 0.21/0.55          | ~ (l1_pre_topc @ X0)
% 0.21/0.55          | (v2_tex_2 @ (u1_struct_0 @ X0) @ X0))),
% 0.21/0.55      inference('sup-', [status(thm)], ['16', '17'])).
% 0.21/0.55  thf('19', plain,
% 0.21/0.55      (![X5 : $i]:
% 0.21/0.55         ((m1_subset_1 @ (sk_B @ X5) @ (k1_zfmisc_1 @ (u1_struct_0 @ X5)))
% 0.21/0.55          | ~ (l1_pre_topc @ X5))),
% 0.21/0.55      inference('cnf', [status(esa)], [rc4_tops_1])).
% 0.21/0.55  thf(t3_subset, axiom,
% 0.21/0.55    (![A:$i,B:$i]:
% 0.21/0.55     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.21/0.55  thf('20', plain,
% 0.21/0.55      (![X2 : $i, X3 : $i]:
% 0.21/0.55         ((r1_tarski @ X2 @ X3) | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X3)))),
% 0.21/0.55      inference('cnf', [status(esa)], [t3_subset])).
% 0.21/0.55  thf('21', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         (~ (l1_pre_topc @ X0) | (r1_tarski @ (sk_B @ X0) @ (u1_struct_0 @ X0)))),
% 0.21/0.55      inference('sup-', [status(thm)], ['19', '20'])).
% 0.21/0.55  thf('22', plain, (![X1 : $i]: (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X1))),
% 0.21/0.55      inference('demod', [status(thm)], ['14', '15'])).
% 0.21/0.55  thf('23', plain,
% 0.21/0.55      (![X5 : $i]:
% 0.21/0.55         ((m1_subset_1 @ (sk_B @ X5) @ (k1_zfmisc_1 @ (u1_struct_0 @ X5)))
% 0.21/0.55          | ~ (l1_pre_topc @ X5))),
% 0.21/0.55      inference('cnf', [status(esa)], [rc4_tops_1])).
% 0.21/0.55  thf(d7_tex_2, axiom,
% 0.21/0.55    (![A:$i]:
% 0.21/0.55     ( ( l1_pre_topc @ A ) =>
% 0.21/0.55       ( ![B:$i]:
% 0.21/0.55         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.55           ( ( v3_tex_2 @ B @ A ) <=>
% 0.21/0.55             ( ( v2_tex_2 @ B @ A ) & 
% 0.21/0.55               ( ![C:$i]:
% 0.21/0.55                 ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.55                   ( ( ( v2_tex_2 @ C @ A ) & ( r1_tarski @ B @ C ) ) =>
% 0.21/0.55                     ( ( B ) = ( C ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.55  thf('24', plain,
% 0.21/0.55      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.21/0.55         (~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 0.21/0.55          | ~ (v3_tex_2 @ X9 @ X10)
% 0.21/0.55          | ~ (v2_tex_2 @ X11 @ X10)
% 0.21/0.55          | ~ (r1_tarski @ X9 @ X11)
% 0.21/0.55          | ((X9) = (X11))
% 0.21/0.55          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 0.21/0.55          | ~ (l1_pre_topc @ X10))),
% 0.21/0.55      inference('cnf', [status(esa)], [d7_tex_2])).
% 0.21/0.55  thf('25', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i]:
% 0.21/0.55         (~ (l1_pre_topc @ X0)
% 0.21/0.55          | ~ (l1_pre_topc @ X0)
% 0.21/0.55          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.21/0.55          | ((sk_B @ X0) = (X1))
% 0.21/0.55          | ~ (r1_tarski @ (sk_B @ X0) @ X1)
% 0.21/0.55          | ~ (v2_tex_2 @ X1 @ X0)
% 0.21/0.55          | ~ (v3_tex_2 @ (sk_B @ X0) @ X0))),
% 0.21/0.55      inference('sup-', [status(thm)], ['23', '24'])).
% 0.21/0.55  thf('26', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i]:
% 0.21/0.55         (~ (v3_tex_2 @ (sk_B @ X0) @ X0)
% 0.21/0.55          | ~ (v2_tex_2 @ X1 @ X0)
% 0.21/0.55          | ~ (r1_tarski @ (sk_B @ X0) @ X1)
% 0.21/0.55          | ((sk_B @ X0) = (X1))
% 0.21/0.55          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.21/0.55          | ~ (l1_pre_topc @ X0))),
% 0.21/0.55      inference('simplify', [status(thm)], ['25'])).
% 0.21/0.55  thf('27', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         (~ (l1_pre_topc @ X0)
% 0.21/0.55          | ((sk_B @ X0) = (u1_struct_0 @ X0))
% 0.21/0.55          | ~ (r1_tarski @ (sk_B @ X0) @ (u1_struct_0 @ X0))
% 0.21/0.55          | ~ (v2_tex_2 @ (u1_struct_0 @ X0) @ X0)
% 0.21/0.55          | ~ (v3_tex_2 @ (sk_B @ X0) @ X0))),
% 0.21/0.55      inference('sup-', [status(thm)], ['22', '26'])).
% 0.21/0.55  thf('28', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         (~ (l1_pre_topc @ X0)
% 0.21/0.55          | ~ (v3_tex_2 @ (sk_B @ X0) @ X0)
% 0.21/0.55          | ~ (v2_tex_2 @ (u1_struct_0 @ X0) @ X0)
% 0.21/0.55          | ((sk_B @ X0) = (u1_struct_0 @ X0))
% 0.21/0.55          | ~ (l1_pre_topc @ X0))),
% 0.21/0.55      inference('sup-', [status(thm)], ['21', '27'])).
% 0.21/0.55  thf('29', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         (((sk_B @ X0) = (u1_struct_0 @ X0))
% 0.21/0.55          | ~ (v2_tex_2 @ (u1_struct_0 @ X0) @ X0)
% 0.21/0.55          | ~ (v3_tex_2 @ (sk_B @ X0) @ X0)
% 0.21/0.55          | ~ (l1_pre_topc @ X0))),
% 0.21/0.55      inference('simplify', [status(thm)], ['28'])).
% 0.21/0.55  thf('30', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         (~ (l1_pre_topc @ X0)
% 0.21/0.55          | ~ (v1_tdlat_3 @ X0)
% 0.21/0.55          | ~ (v2_pre_topc @ X0)
% 0.21/0.55          | (v2_struct_0 @ X0)
% 0.21/0.55          | ~ (l1_pre_topc @ X0)
% 0.21/0.55          | ~ (v3_tex_2 @ (sk_B @ X0) @ X0)
% 0.21/0.55          | ((sk_B @ X0) = (u1_struct_0 @ X0)))),
% 0.21/0.55      inference('sup-', [status(thm)], ['18', '29'])).
% 0.21/0.55  thf('31', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         (((sk_B @ X0) = (u1_struct_0 @ X0))
% 0.21/0.55          | ~ (v3_tex_2 @ (sk_B @ X0) @ X0)
% 0.21/0.55          | (v2_struct_0 @ X0)
% 0.21/0.55          | ~ (v2_pre_topc @ X0)
% 0.21/0.55          | ~ (v1_tdlat_3 @ X0)
% 0.21/0.55          | ~ (l1_pre_topc @ X0))),
% 0.21/0.55      inference('simplify', [status(thm)], ['30'])).
% 0.21/0.55  thf('32', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         (~ (l1_pre_topc @ X0)
% 0.21/0.55          | (v2_struct_0 @ X0)
% 0.21/0.55          | ~ (v2_pre_topc @ X0)
% 0.21/0.55          | ~ (v1_tdlat_3 @ X0)
% 0.21/0.55          | ~ (l1_pre_topc @ X0)
% 0.21/0.55          | ~ (v1_tdlat_3 @ X0)
% 0.21/0.55          | ~ (v2_pre_topc @ X0)
% 0.21/0.55          | (v2_struct_0 @ X0)
% 0.21/0.55          | ((sk_B @ X0) = (u1_struct_0 @ X0)))),
% 0.21/0.55      inference('sup-', [status(thm)], ['13', '31'])).
% 0.21/0.55  thf('33', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         (((sk_B @ X0) = (u1_struct_0 @ X0))
% 0.21/0.55          | ~ (v1_tdlat_3 @ X0)
% 0.21/0.55          | ~ (v2_pre_topc @ X0)
% 0.21/0.55          | (v2_struct_0 @ X0)
% 0.21/0.55          | ~ (l1_pre_topc @ X0))),
% 0.21/0.55      inference('simplify', [status(thm)], ['32'])).
% 0.21/0.55  thf('34', plain,
% 0.21/0.55      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf(d7_subset_1, axiom,
% 0.21/0.55    (![A:$i,B:$i]:
% 0.21/0.55     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.55       ( ( v1_subset_1 @ B @ A ) <=> ( ( B ) != ( A ) ) ) ))).
% 0.21/0.55  thf('35', plain,
% 0.21/0.55      (![X7 : $i, X8 : $i]:
% 0.21/0.55         (((X8) = (X7))
% 0.21/0.55          | (v1_subset_1 @ X8 @ X7)
% 0.21/0.55          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X7)))),
% 0.21/0.55      inference('cnf', [status(esa)], [d7_subset_1])).
% 0.21/0.55  thf('36', plain,
% 0.21/0.55      (((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 0.21/0.55        | ((sk_B_1) = (u1_struct_0 @ sk_A)))),
% 0.21/0.55      inference('sup-', [status(thm)], ['34', '35'])).
% 0.21/0.55  thf('37', plain,
% 0.21/0.55      ((~ (v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 0.21/0.55        | (v3_tex_2 @ sk_B_1 @ sk_A))),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('38', plain,
% 0.21/0.55      ((~ (v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.55         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.21/0.55      inference('split', [status(esa)], ['37'])).
% 0.21/0.55  thf('39', plain,
% 0.21/0.55      ((((sk_B_1) = (u1_struct_0 @ sk_A)))
% 0.21/0.55         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.21/0.55      inference('sup-', [status(thm)], ['36', '38'])).
% 0.21/0.55  thf('40', plain,
% 0.21/0.55      (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))) | 
% 0.21/0.55       ((v3_tex_2 @ sk_B_1 @ sk_A))),
% 0.21/0.55      inference('split', [status(esa)], ['37'])).
% 0.21/0.55  thf('41', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         ((v2_struct_0 @ X0)
% 0.21/0.55          | ~ (v2_pre_topc @ X0)
% 0.21/0.55          | ~ (v1_tdlat_3 @ X0)
% 0.21/0.55          | ~ (l1_pre_topc @ X0)
% 0.21/0.55          | (v2_tex_2 @ (u1_struct_0 @ X0) @ X0))),
% 0.21/0.55      inference('sup-', [status(thm)], ['16', '17'])).
% 0.21/0.55  thf('42', plain, (![X1 : $i]: (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X1))),
% 0.21/0.55      inference('demod', [status(thm)], ['14', '15'])).
% 0.21/0.55  thf('43', plain,
% 0.21/0.55      (((v3_tex_2 @ sk_B_1 @ sk_A)) <= (((v3_tex_2 @ sk_B_1 @ sk_A)))),
% 0.21/0.55      inference('split', [status(esa)], ['37'])).
% 0.21/0.55  thf('44', plain,
% 0.21/0.55      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('45', plain,
% 0.21/0.55      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.21/0.55         (~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 0.21/0.55          | ~ (v3_tex_2 @ X9 @ X10)
% 0.21/0.55          | ~ (v2_tex_2 @ X11 @ X10)
% 0.21/0.55          | ~ (r1_tarski @ X9 @ X11)
% 0.21/0.55          | ((X9) = (X11))
% 0.21/0.55          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 0.21/0.55          | ~ (l1_pre_topc @ X10))),
% 0.21/0.55      inference('cnf', [status(esa)], [d7_tex_2])).
% 0.21/0.55  thf('46', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         (~ (l1_pre_topc @ sk_A)
% 0.21/0.55          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.55          | ((sk_B_1) = (X0))
% 0.21/0.55          | ~ (r1_tarski @ sk_B_1 @ X0)
% 0.21/0.55          | ~ (v2_tex_2 @ X0 @ sk_A)
% 0.21/0.55          | ~ (v3_tex_2 @ sk_B_1 @ sk_A))),
% 0.21/0.55      inference('sup-', [status(thm)], ['44', '45'])).
% 0.21/0.55  thf('47', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('48', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.55          | ((sk_B_1) = (X0))
% 0.21/0.55          | ~ (r1_tarski @ sk_B_1 @ X0)
% 0.21/0.55          | ~ (v2_tex_2 @ X0 @ sk_A)
% 0.21/0.55          | ~ (v3_tex_2 @ sk_B_1 @ sk_A))),
% 0.21/0.55      inference('demod', [status(thm)], ['46', '47'])).
% 0.21/0.55  thf('49', plain,
% 0.21/0.55      ((![X0 : $i]:
% 0.21/0.55          (~ (v2_tex_2 @ X0 @ sk_A)
% 0.21/0.55           | ~ (r1_tarski @ sk_B_1 @ X0)
% 0.21/0.55           | ((sk_B_1) = (X0))
% 0.21/0.55           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))
% 0.21/0.55         <= (((v3_tex_2 @ sk_B_1 @ sk_A)))),
% 0.21/0.55      inference('sup-', [status(thm)], ['43', '48'])).
% 0.21/0.55  thf('50', plain,
% 0.21/0.55      (((((sk_B_1) = (u1_struct_0 @ sk_A))
% 0.21/0.55         | ~ (r1_tarski @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 0.21/0.55         | ~ (v2_tex_2 @ (u1_struct_0 @ sk_A) @ sk_A)))
% 0.21/0.55         <= (((v3_tex_2 @ sk_B_1 @ sk_A)))),
% 0.21/0.55      inference('sup-', [status(thm)], ['42', '49'])).
% 0.21/0.55  thf('51', plain,
% 0.21/0.55      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('52', plain,
% 0.21/0.55      (![X2 : $i, X3 : $i]:
% 0.21/0.55         ((r1_tarski @ X2 @ X3) | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X3)))),
% 0.21/0.55      inference('cnf', [status(esa)], [t3_subset])).
% 0.21/0.55  thf('53', plain, ((r1_tarski @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.21/0.55      inference('sup-', [status(thm)], ['51', '52'])).
% 0.21/0.55  thf('54', plain,
% 0.21/0.55      (((((sk_B_1) = (u1_struct_0 @ sk_A))
% 0.21/0.55         | ~ (v2_tex_2 @ (u1_struct_0 @ sk_A) @ sk_A)))
% 0.21/0.55         <= (((v3_tex_2 @ sk_B_1 @ sk_A)))),
% 0.21/0.55      inference('demod', [status(thm)], ['50', '53'])).
% 0.21/0.55  thf('55', plain,
% 0.21/0.55      (((~ (l1_pre_topc @ sk_A)
% 0.21/0.55         | ~ (v1_tdlat_3 @ sk_A)
% 0.21/0.55         | ~ (v2_pre_topc @ sk_A)
% 0.21/0.55         | (v2_struct_0 @ sk_A)
% 0.21/0.55         | ((sk_B_1) = (u1_struct_0 @ sk_A))))
% 0.21/0.55         <= (((v3_tex_2 @ sk_B_1 @ sk_A)))),
% 0.21/0.55      inference('sup-', [status(thm)], ['41', '54'])).
% 0.21/0.55  thf('56', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('57', plain, ((v1_tdlat_3 @ sk_A)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('58', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('59', plain,
% 0.21/0.55      ((((v2_struct_0 @ sk_A) | ((sk_B_1) = (u1_struct_0 @ sk_A))))
% 0.21/0.55         <= (((v3_tex_2 @ sk_B_1 @ sk_A)))),
% 0.21/0.55      inference('demod', [status(thm)], ['55', '56', '57', '58'])).
% 0.21/0.55  thf('60', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('61', plain,
% 0.21/0.55      ((((sk_B_1) = (u1_struct_0 @ sk_A))) <= (((v3_tex_2 @ sk_B_1 @ sk_A)))),
% 0.21/0.55      inference('clc', [status(thm)], ['59', '60'])).
% 0.21/0.55  thf('62', plain,
% 0.21/0.55      (((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 0.21/0.55        | ~ (v3_tex_2 @ sk_B_1 @ sk_A))),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('63', plain,
% 0.21/0.55      (((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.55         <= (((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.21/0.55      inference('split', [status(esa)], ['62'])).
% 0.21/0.55  thf('64', plain,
% 0.21/0.55      (((v1_subset_1 @ sk_B_1 @ sk_B_1))
% 0.21/0.55         <= (((v3_tex_2 @ sk_B_1 @ sk_A)) & 
% 0.21/0.55             ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.21/0.55      inference('sup+', [status(thm)], ['61', '63'])).
% 0.21/0.55  thf('65', plain,
% 0.21/0.55      (![X7 : $i, X8 : $i]:
% 0.21/0.55         (~ (v1_subset_1 @ X8 @ X7)
% 0.21/0.55          | ((X8) != (X7))
% 0.21/0.55          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X7)))),
% 0.21/0.55      inference('cnf', [status(esa)], [d7_subset_1])).
% 0.21/0.55  thf('66', plain,
% 0.21/0.55      (![X7 : $i]:
% 0.21/0.55         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X7)) | ~ (v1_subset_1 @ X7 @ X7))),
% 0.21/0.55      inference('simplify', [status(thm)], ['65'])).
% 0.21/0.55  thf('67', plain, (![X1 : $i]: (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X1))),
% 0.21/0.55      inference('demod', [status(thm)], ['14', '15'])).
% 0.21/0.55  thf('68', plain, (![X7 : $i]: ~ (v1_subset_1 @ X7 @ X7)),
% 0.21/0.55      inference('demod', [status(thm)], ['66', '67'])).
% 0.21/0.55  thf('69', plain,
% 0.21/0.55      (~ ((v3_tex_2 @ sk_B_1 @ sk_A)) | 
% 0.21/0.55       ~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.55      inference('sup-', [status(thm)], ['64', '68'])).
% 0.21/0.55  thf('70', plain, (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.55      inference('sat_resolution*', [status(thm)], ['40', '69'])).
% 0.21/0.55  thf('71', plain, (((sk_B_1) = (u1_struct_0 @ sk_A))),
% 0.21/0.55      inference('simpl_trail', [status(thm)], ['39', '70'])).
% 0.21/0.55  thf('72', plain,
% 0.21/0.55      ((((sk_B_1) = (sk_B @ sk_A))
% 0.21/0.55        | ~ (l1_pre_topc @ sk_A)
% 0.21/0.55        | (v2_struct_0 @ sk_A)
% 0.21/0.55        | ~ (v2_pre_topc @ sk_A)
% 0.21/0.55        | ~ (v1_tdlat_3 @ sk_A))),
% 0.21/0.55      inference('sup+', [status(thm)], ['33', '71'])).
% 0.21/0.55  thf('73', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('74', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('75', plain, ((v1_tdlat_3 @ sk_A)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('76', plain, ((((sk_B_1) = (sk_B @ sk_A)) | (v2_struct_0 @ sk_A))),
% 0.21/0.55      inference('demod', [status(thm)], ['72', '73', '74', '75'])).
% 0.21/0.55  thf('77', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('78', plain, (((sk_B_1) = (sk_B @ sk_A))),
% 0.21/0.55      inference('clc', [status(thm)], ['76', '77'])).
% 0.21/0.55  thf('79', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         ((v3_tex_2 @ (sk_B @ X0) @ X0)
% 0.21/0.55          | ~ (v1_tdlat_3 @ X0)
% 0.21/0.55          | ~ (v2_pre_topc @ X0)
% 0.21/0.55          | (v2_struct_0 @ X0)
% 0.21/0.55          | ~ (l1_pre_topc @ X0))),
% 0.21/0.55      inference('simplify', [status(thm)], ['12'])).
% 0.21/0.55  thf('80', plain,
% 0.21/0.55      (((v3_tex_2 @ sk_B_1 @ sk_A)
% 0.21/0.55        | ~ (l1_pre_topc @ sk_A)
% 0.21/0.55        | (v2_struct_0 @ sk_A)
% 0.21/0.55        | ~ (v2_pre_topc @ sk_A)
% 0.21/0.55        | ~ (v1_tdlat_3 @ sk_A))),
% 0.21/0.55      inference('sup+', [status(thm)], ['78', '79'])).
% 0.21/0.55  thf('81', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('82', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('83', plain, ((v1_tdlat_3 @ sk_A)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('84', plain, (((v3_tex_2 @ sk_B_1 @ sk_A) | (v2_struct_0 @ sk_A))),
% 0.21/0.55      inference('demod', [status(thm)], ['80', '81', '82', '83'])).
% 0.21/0.55  thf('85', plain,
% 0.21/0.55      ((~ (v3_tex_2 @ sk_B_1 @ sk_A)) <= (~ ((v3_tex_2 @ sk_B_1 @ sk_A)))),
% 0.21/0.55      inference('split', [status(esa)], ['62'])).
% 0.21/0.55  thf('86', plain,
% 0.21/0.55      (~ ((v3_tex_2 @ sk_B_1 @ sk_A)) | 
% 0.21/0.55       ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.55      inference('split', [status(esa)], ['62'])).
% 0.21/0.55  thf('87', plain, (~ ((v3_tex_2 @ sk_B_1 @ sk_A))),
% 0.21/0.55      inference('sat_resolution*', [status(thm)], ['40', '69', '86'])).
% 0.21/0.55  thf('88', plain, (~ (v3_tex_2 @ sk_B_1 @ sk_A)),
% 0.21/0.55      inference('simpl_trail', [status(thm)], ['85', '87'])).
% 0.21/0.55  thf('89', plain, ((v2_struct_0 @ sk_A)),
% 0.21/0.55      inference('clc', [status(thm)], ['84', '88'])).
% 0.21/0.55  thf('90', plain, ($false), inference('demod', [status(thm)], ['0', '89'])).
% 0.21/0.55  
% 0.21/0.55  % SZS output end Refutation
% 0.21/0.55  
% 0.21/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
