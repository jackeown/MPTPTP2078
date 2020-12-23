%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.boYk7MAP5G

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:05:15 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 641 expanded)
%              Number of leaves         :   17 ( 185 expanded)
%              Depth                    :   18
%              Number of atoms          : 1116 (10672 expanded)
%              Number of equality atoms :   25 ( 185 expanded)
%              Maximal formula depth    :   14 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v2_tops_2_type,type,(
    v2_tops_2: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_tops_2_type,type,(
    v1_tops_2: $i > $i > $o )).

thf(k7_setfam_1_type,type,(
    k7_setfam_1: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(t17_tops_2,conjecture,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
         => ( ( v1_tops_2 @ B @ A )
          <=> ( v2_tops_2 @ ( k7_setfam_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_pre_topc @ A )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
           => ( ( v1_tops_2 @ B @ A )
            <=> ( v2_tops_2 @ ( k7_setfam_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t17_tops_2])).

thf('0',plain,
    ( ~ ( v2_tops_2 @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ~ ( v1_tops_2 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( v2_tops_2 @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
   <= ~ ( v2_tops_2 @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( v2_tops_2 @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ~ ( v1_tops_2 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('3',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k7_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( m1_subset_1 @ ( k7_setfam_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) ) )).

thf('4',plain,(
    ! [X4: $i,X5: $i] :
      ( ( m1_subset_1 @ ( k7_setfam_1 @ X4 @ X5 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X4 ) ) )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X4 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_setfam_1])).

thf('5',plain,(
    m1_subset_1 @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d8_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
         => ( ( C
              = ( k7_setfam_1 @ A @ B ) )
          <=> ! [D: $i] :
                ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) )
               => ( ( r2_hidden @ D @ C )
                <=> ( r2_hidden @ ( k3_subset_1 @ A @ D ) @ B ) ) ) ) ) ) )).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X1 ) ) )
      | ( m1_subset_1 @ ( sk_D @ X0 @ X2 @ X1 ) @ ( k1_zfmisc_1 @ X1 ) )
      | ( X0
        = ( k7_setfam_1 @ X1 @ X2 ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X1 ) ) ) ) ),
    inference(cnf,[status(esa)],[d8_setfam_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
      | ( sk_B
        = ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) )
      | ( m1_subset_1 @ ( sk_D @ sk_B @ X0 @ ( u1_struct_0 @ sk_A ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,
    ( ( m1_subset_1 @ ( sk_D @ sk_B @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( sk_B
      = ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['5','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t49_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ( r2_hidden @ ( k3_subset_1 @ A @ C ) @ ( k7_setfam_1 @ A @ B ) )
          <=> ( r2_hidden @ C @ B ) ) ) ) )).

thf('11',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) )
      | ~ ( r2_hidden @ X6 @ X8 )
      | ( r2_hidden @ ( k3_subset_1 @ X7 @ X6 ) @ ( k7_setfam_1 @ X7 @ X8 ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X7 ) ) ) ) ),
    inference(cnf,[status(esa)],[t49_setfam_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,
    ( ( sk_B
      = ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) )
    | ~ ( r2_hidden @ ( sk_D @ sk_B @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ sk_B )
    | ( r2_hidden @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_D @ sk_B @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['9','12'])).

thf('14',plain,(
    m1_subset_1 @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('15',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X1 ) ) )
      | ( r2_hidden @ ( sk_D @ X0 @ X2 @ X1 ) @ X0 )
      | ( r2_hidden @ ( k3_subset_1 @ X1 @ ( sk_D @ X0 @ X2 @ X1 ) ) @ X2 )
      | ( X0
        = ( k7_setfam_1 @ X1 @ X2 ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X1 ) ) ) ) ),
    inference(cnf,[status(esa)],[d8_setfam_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
      | ( sk_B
        = ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) )
      | ( r2_hidden @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_D @ sk_B @ X0 @ ( u1_struct_0 @ sk_A ) ) ) @ X0 )
      | ( r2_hidden @ ( sk_D @ sk_B @ X0 @ ( u1_struct_0 @ sk_A ) ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ( r2_hidden @ ( sk_D @ sk_B @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ sk_B )
    | ( r2_hidden @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_D @ sk_B @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    | ( sk_B
      = ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['14','17'])).

thf('19',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) )
      | ~ ( r2_hidden @ ( k3_subset_1 @ X7 @ X6 ) @ ( k7_setfam_1 @ X7 @ X8 ) )
      | ( r2_hidden @ X6 @ X8 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X7 ) ) ) ) ),
    inference(cnf,[status(esa)],[t49_setfam_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_B )
      | ~ ( r2_hidden @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,
    ( ( sk_B
      = ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) )
    | ( r2_hidden @ ( sk_D @ sk_B @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ sk_B )
    | ~ ( m1_subset_1 @ ( sk_D @ sk_B @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( r2_hidden @ ( sk_D @ sk_B @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['18','21'])).

thf('23',plain,
    ( ~ ( m1_subset_1 @ ( sk_D @ sk_B @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( r2_hidden @ ( sk_D @ sk_B @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ sk_B )
    | ( sk_B
      = ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,
    ( ( m1_subset_1 @ ( sk_D @ sk_B @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( sk_B
      = ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['5','8'])).

thf('25',plain,
    ( ( sk_B
      = ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) )
    | ( r2_hidden @ ( sk_D @ sk_B @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ sk_B ) ),
    inference(clc,[status(thm)],['23','24'])).

thf('26',plain,
    ( ( r2_hidden @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_D @ sk_B @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    | ( sk_B
      = ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['13','25'])).

thf('27',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X1 ) ) )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X2 @ X1 ) @ X0 )
      | ~ ( r2_hidden @ ( k3_subset_1 @ X1 @ ( sk_D @ X0 @ X2 @ X1 ) ) @ X2 )
      | ( X0
        = ( k7_setfam_1 @ X1 @ X2 ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X1 ) ) ) ) ),
    inference(cnf,[status(esa)],[d8_setfam_1])).

thf('29',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
      | ( sk_B
        = ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) )
      | ~ ( r2_hidden @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_D @ sk_B @ X0 @ ( u1_struct_0 @ sk_A ) ) ) @ X0 )
      | ~ ( r2_hidden @ ( sk_D @ sk_B @ X0 @ ( u1_struct_0 @ sk_A ) ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,
    ( ( sk_B
      = ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) )
    | ~ ( r2_hidden @ ( sk_D @ sk_B @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ sk_B )
    | ( sk_B
      = ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) )
    | ~ ( m1_subset_1 @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['26','29'])).

thf('31',plain,(
    m1_subset_1 @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('32',plain,
    ( ( sk_B
      = ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) )
    | ~ ( r2_hidden @ ( sk_D @ sk_B @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ sk_B )
    | ( sk_B
      = ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,
    ( ~ ( r2_hidden @ ( sk_D @ sk_B @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ sk_B )
    | ( sk_B
      = ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,
    ( ( sk_B
      = ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) )
    | ( r2_hidden @ ( sk_D @ sk_B @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ sk_B ) ),
    inference(clc,[status(thm)],['23','24'])).

thf('35',plain,
    ( sk_B
    = ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(clc,[status(thm)],['33','34'])).

thf('36',plain,
    ( ( v2_tops_2 @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ( v1_tops_2 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ( v2_tops_2 @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
   <= ( v2_tops_2 @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference(split,[status(esa)],['36'])).

thf('38',plain,(
    m1_subset_1 @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(t16_tops_2,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
         => ( ( v2_tops_2 @ B @ A )
          <=> ( v1_tops_2 @ ( k7_setfam_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) )).

thf('39',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) ) )
      | ~ ( v2_tops_2 @ X9 @ X10 )
      | ( v1_tops_2 @ ( k7_setfam_1 @ ( u1_struct_0 @ X10 ) @ X9 ) @ X10 )
      | ~ ( l1_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[t16_tops_2])).

thf('40',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v1_tops_2 @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) @ sk_A )
    | ~ ( v2_tops_2 @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( ( v1_tops_2 @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) @ sk_A )
    | ~ ( v2_tops_2 @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,
    ( ( v1_tops_2 @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) @ sk_A )
   <= ( v2_tops_2 @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['37','42'])).

thf('44',plain,
    ( ( v1_tops_2 @ sk_B @ sk_A )
   <= ( v2_tops_2 @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference('sup+',[status(thm)],['35','43'])).

thf('45',plain,
    ( ~ ( v1_tops_2 @ sk_B @ sk_A )
   <= ~ ( v1_tops_2 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('46',plain,
    ( ( v1_tops_2 @ sk_B @ sk_A )
    | ~ ( v2_tops_2 @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ~ ( v2_tops_2 @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['2','46'])).

thf('48',plain,(
    ~ ( v2_tops_2 @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['1','47'])).

thf('49',plain,(
    m1_subset_1 @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('50',plain,(
    ! [X4: $i,X5: $i] :
      ( ( m1_subset_1 @ ( k7_setfam_1 @ X4 @ X5 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X4 ) ) )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X4 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_setfam_1])).

thf('51',plain,(
    m1_subset_1 @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X4: $i,X5: $i] :
      ( ( m1_subset_1 @ ( k7_setfam_1 @ X4 @ X5 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X4 ) ) )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X4 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_setfam_1])).

thf('53',plain,(
    m1_subset_1 @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) ) )
      | ~ ( v1_tops_2 @ ( k7_setfam_1 @ ( u1_struct_0 @ X10 ) @ X9 ) @ X10 )
      | ( v2_tops_2 @ X9 @ X10 )
      | ~ ( l1_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[t16_tops_2])).

thf('55',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v2_tops_2 @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) @ sk_A )
    | ~ ( v1_tops_2 @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,
    ( ( v2_tops_2 @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) @ sk_A )
    | ~ ( v1_tops_2 @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ) @ sk_A ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,
    ( sk_B
    = ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(clc,[status(thm)],['33','34'])).

thf('59',plain,
    ( sk_B
    = ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(clc,[status(thm)],['33','34'])).

thf('60',plain,
    ( sk_B
    = ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(clc,[status(thm)],['33','34'])).

thf('61',plain,
    ( ( v2_tops_2 @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ~ ( v1_tops_2 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['57','58','59','60'])).

thf('62',plain,
    ( ( v1_tops_2 @ sk_B @ sk_A )
   <= ( v1_tops_2 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['36'])).

thf('63',plain,
    ( ( v1_tops_2 @ sk_B @ sk_A )
    | ( v2_tops_2 @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference(split,[status(esa)],['36'])).

thf('64',plain,(
    v1_tops_2 @ sk_B @ sk_A ),
    inference('sat_resolution*',[status(thm)],['2','46','63'])).

thf('65',plain,(
    v1_tops_2 @ sk_B @ sk_A ),
    inference(simpl_trail,[status(thm)],['62','64'])).

thf('66',plain,(
    v2_tops_2 @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['61','65'])).

thf('67',plain,(
    $false ),
    inference(demod,[status(thm)],['48','66'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.boYk7MAP5G
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:49:29 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.57  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.57  % Solved by: fo/fo7.sh
% 0.20/0.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.57  % done 98 iterations in 0.112s
% 0.20/0.57  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.57  % SZS output start Refutation
% 0.20/0.57  thf(v2_tops_2_type, type, v2_tops_2: $i > $i > $o).
% 0.20/0.57  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.57  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.57  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.20/0.57  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.20/0.57  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.57  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.57  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.57  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.57  thf(v1_tops_2_type, type, v1_tops_2: $i > $i > $o).
% 0.20/0.57  thf(k7_setfam_1_type, type, k7_setfam_1: $i > $i > $i).
% 0.20/0.57  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.20/0.57  thf(t17_tops_2, conjecture,
% 0.20/0.57    (![A:$i]:
% 0.20/0.57     ( ( l1_pre_topc @ A ) =>
% 0.20/0.57       ( ![B:$i]:
% 0.20/0.57         ( ( m1_subset_1 @
% 0.20/0.57             B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.20/0.57           ( ( v1_tops_2 @ B @ A ) <=>
% 0.20/0.57             ( v2_tops_2 @ ( k7_setfam_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) ))).
% 0.20/0.57  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.57    (~( ![A:$i]:
% 0.20/0.57        ( ( l1_pre_topc @ A ) =>
% 0.20/0.57          ( ![B:$i]:
% 0.20/0.57            ( ( m1_subset_1 @
% 0.20/0.57                B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.20/0.57              ( ( v1_tops_2 @ B @ A ) <=>
% 0.20/0.57                ( v2_tops_2 @ ( k7_setfam_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) ) )),
% 0.20/0.57    inference('cnf.neg', [status(esa)], [t17_tops_2])).
% 0.20/0.57  thf('0', plain,
% 0.20/0.57      ((~ (v2_tops_2 @ (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 0.20/0.57        | ~ (v1_tops_2 @ sk_B @ sk_A))),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf('1', plain,
% 0.20/0.57      ((~ (v2_tops_2 @ (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A))
% 0.20/0.57         <= (~
% 0.20/0.57             ((v2_tops_2 @ (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)))),
% 0.20/0.57      inference('split', [status(esa)], ['0'])).
% 0.20/0.57  thf('2', plain,
% 0.20/0.57      (~ ((v2_tops_2 @ (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)) | 
% 0.20/0.57       ~ ((v1_tops_2 @ sk_B @ sk_A))),
% 0.20/0.57      inference('split', [status(esa)], ['0'])).
% 0.20/0.57  thf('3', plain,
% 0.20/0.57      ((m1_subset_1 @ sk_B @ 
% 0.20/0.57        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf(dt_k7_setfam_1, axiom,
% 0.20/0.57    (![A:$i,B:$i]:
% 0.20/0.57     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.20/0.57       ( m1_subset_1 @
% 0.20/0.57         ( k7_setfam_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) ))).
% 0.20/0.57  thf('4', plain,
% 0.20/0.57      (![X4 : $i, X5 : $i]:
% 0.20/0.57         ((m1_subset_1 @ (k7_setfam_1 @ X4 @ X5) @ 
% 0.20/0.57           (k1_zfmisc_1 @ (k1_zfmisc_1 @ X4)))
% 0.20/0.57          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X4))))),
% 0.20/0.57      inference('cnf', [status(esa)], [dt_k7_setfam_1])).
% 0.20/0.57  thf('5', plain,
% 0.20/0.57      ((m1_subset_1 @ (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.20/0.57        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.57      inference('sup-', [status(thm)], ['3', '4'])).
% 0.20/0.57  thf('6', plain,
% 0.20/0.57      ((m1_subset_1 @ sk_B @ 
% 0.20/0.57        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf(d8_setfam_1, axiom,
% 0.20/0.57    (![A:$i,B:$i]:
% 0.20/0.57     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.20/0.57       ( ![C:$i]:
% 0.20/0.57         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.20/0.57           ( ( ( C ) = ( k7_setfam_1 @ A @ B ) ) <=>
% 0.20/0.57             ( ![D:$i]:
% 0.20/0.57               ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.57                 ( ( r2_hidden @ D @ C ) <=>
% 0.20/0.57                   ( r2_hidden @ ( k3_subset_1 @ A @ D ) @ B ) ) ) ) ) ) ) ))).
% 0.20/0.57  thf('7', plain,
% 0.20/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.57         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X1)))
% 0.20/0.57          | (m1_subset_1 @ (sk_D @ X0 @ X2 @ X1) @ (k1_zfmisc_1 @ X1))
% 0.20/0.57          | ((X0) = (k7_setfam_1 @ X1 @ X2))
% 0.20/0.57          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X1))))),
% 0.20/0.57      inference('cnf', [status(esa)], [d8_setfam_1])).
% 0.20/0.57  thf('8', plain,
% 0.20/0.57      (![X0 : $i]:
% 0.20/0.57         (~ (m1_subset_1 @ X0 @ 
% 0.20/0.57             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.20/0.57          | ((sk_B) = (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ X0))
% 0.20/0.57          | (m1_subset_1 @ (sk_D @ sk_B @ X0 @ (u1_struct_0 @ sk_A)) @ 
% 0.20/0.57             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.57      inference('sup-', [status(thm)], ['6', '7'])).
% 0.20/0.57  thf('9', plain,
% 0.20/0.57      (((m1_subset_1 @ 
% 0.20/0.57         (sk_D @ sk_B @ (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.20/0.57          (u1_struct_0 @ sk_A)) @ 
% 0.20/0.57         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.57        | ((sk_B)
% 0.20/0.57            = (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.57               (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 0.20/0.57      inference('sup-', [status(thm)], ['5', '8'])).
% 0.20/0.57  thf('10', plain,
% 0.20/0.57      ((m1_subset_1 @ sk_B @ 
% 0.20/0.57        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf(t49_setfam_1, axiom,
% 0.20/0.57    (![A:$i,B:$i]:
% 0.20/0.57     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.20/0.57       ( ![C:$i]:
% 0.20/0.57         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.57           ( ( r2_hidden @ ( k3_subset_1 @ A @ C ) @ ( k7_setfam_1 @ A @ B ) ) <=>
% 0.20/0.57             ( r2_hidden @ C @ B ) ) ) ) ))).
% 0.20/0.57  thf('11', plain,
% 0.20/0.57      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.20/0.57         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7))
% 0.20/0.57          | ~ (r2_hidden @ X6 @ X8)
% 0.20/0.57          | (r2_hidden @ (k3_subset_1 @ X7 @ X6) @ (k7_setfam_1 @ X7 @ X8))
% 0.20/0.57          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X7))))),
% 0.20/0.57      inference('cnf', [status(esa)], [t49_setfam_1])).
% 0.20/0.57  thf('12', plain,
% 0.20/0.57      (![X0 : $i]:
% 0.20/0.57         ((r2_hidden @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ X0) @ 
% 0.20/0.57           (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.20/0.57          | ~ (r2_hidden @ X0 @ sk_B)
% 0.20/0.57          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.57      inference('sup-', [status(thm)], ['10', '11'])).
% 0.20/0.57  thf('13', plain,
% 0.20/0.57      ((((sk_B)
% 0.20/0.57          = (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.57             (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B)))
% 0.20/0.57        | ~ (r2_hidden @ 
% 0.20/0.57             (sk_D @ sk_B @ (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.20/0.57              (u1_struct_0 @ sk_A)) @ 
% 0.20/0.57             sk_B)
% 0.20/0.57        | (r2_hidden @ 
% 0.20/0.57           (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.57            (sk_D @ sk_B @ (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.20/0.57             (u1_struct_0 @ sk_A))) @ 
% 0.20/0.57           (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 0.20/0.57      inference('sup-', [status(thm)], ['9', '12'])).
% 0.20/0.57  thf('14', plain,
% 0.20/0.57      ((m1_subset_1 @ (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.20/0.57        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.57      inference('sup-', [status(thm)], ['3', '4'])).
% 0.20/0.57  thf('15', plain,
% 0.20/0.57      ((m1_subset_1 @ sk_B @ 
% 0.20/0.57        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf('16', plain,
% 0.20/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.57         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X1)))
% 0.20/0.57          | (r2_hidden @ (sk_D @ X0 @ X2 @ X1) @ X0)
% 0.20/0.57          | (r2_hidden @ (k3_subset_1 @ X1 @ (sk_D @ X0 @ X2 @ X1)) @ X2)
% 0.20/0.57          | ((X0) = (k7_setfam_1 @ X1 @ X2))
% 0.20/0.57          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X1))))),
% 0.20/0.57      inference('cnf', [status(esa)], [d8_setfam_1])).
% 0.20/0.57  thf('17', plain,
% 0.20/0.57      (![X0 : $i]:
% 0.20/0.57         (~ (m1_subset_1 @ X0 @ 
% 0.20/0.57             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.20/0.57          | ((sk_B) = (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ X0))
% 0.20/0.57          | (r2_hidden @ 
% 0.20/0.57             (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.57              (sk_D @ sk_B @ X0 @ (u1_struct_0 @ sk_A))) @ 
% 0.20/0.57             X0)
% 0.20/0.57          | (r2_hidden @ (sk_D @ sk_B @ X0 @ (u1_struct_0 @ sk_A)) @ sk_B))),
% 0.20/0.57      inference('sup-', [status(thm)], ['15', '16'])).
% 0.20/0.57  thf('18', plain,
% 0.20/0.57      (((r2_hidden @ 
% 0.20/0.57         (sk_D @ sk_B @ (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.20/0.57          (u1_struct_0 @ sk_A)) @ 
% 0.20/0.57         sk_B)
% 0.20/0.57        | (r2_hidden @ 
% 0.20/0.57           (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.57            (sk_D @ sk_B @ (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.20/0.57             (u1_struct_0 @ sk_A))) @ 
% 0.20/0.57           (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.20/0.57        | ((sk_B)
% 0.20/0.57            = (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.57               (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 0.20/0.57      inference('sup-', [status(thm)], ['14', '17'])).
% 0.20/0.57  thf('19', plain,
% 0.20/0.57      ((m1_subset_1 @ sk_B @ 
% 0.20/0.57        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf('20', plain,
% 0.20/0.57      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.20/0.57         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7))
% 0.20/0.57          | ~ (r2_hidden @ (k3_subset_1 @ X7 @ X6) @ (k7_setfam_1 @ X7 @ X8))
% 0.20/0.57          | (r2_hidden @ X6 @ X8)
% 0.20/0.57          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X7))))),
% 0.20/0.57      inference('cnf', [status(esa)], [t49_setfam_1])).
% 0.20/0.57  thf('21', plain,
% 0.20/0.57      (![X0 : $i]:
% 0.20/0.57         ((r2_hidden @ X0 @ sk_B)
% 0.20/0.57          | ~ (r2_hidden @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ X0) @ 
% 0.20/0.57               (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.20/0.57          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.57      inference('sup-', [status(thm)], ['19', '20'])).
% 0.20/0.57  thf('22', plain,
% 0.20/0.57      ((((sk_B)
% 0.20/0.57          = (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.57             (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B)))
% 0.20/0.57        | (r2_hidden @ 
% 0.20/0.57           (sk_D @ sk_B @ (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.20/0.57            (u1_struct_0 @ sk_A)) @ 
% 0.20/0.57           sk_B)
% 0.20/0.57        | ~ (m1_subset_1 @ 
% 0.20/0.57             (sk_D @ sk_B @ (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.20/0.57              (u1_struct_0 @ sk_A)) @ 
% 0.20/0.57             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.57        | (r2_hidden @ 
% 0.20/0.57           (sk_D @ sk_B @ (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.20/0.57            (u1_struct_0 @ sk_A)) @ 
% 0.20/0.57           sk_B))),
% 0.20/0.57      inference('sup-', [status(thm)], ['18', '21'])).
% 0.20/0.57  thf('23', plain,
% 0.20/0.57      ((~ (m1_subset_1 @ 
% 0.20/0.57           (sk_D @ sk_B @ (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.20/0.57            (u1_struct_0 @ sk_A)) @ 
% 0.20/0.57           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.57        | (r2_hidden @ 
% 0.20/0.57           (sk_D @ sk_B @ (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.20/0.57            (u1_struct_0 @ sk_A)) @ 
% 0.20/0.57           sk_B)
% 0.20/0.57        | ((sk_B)
% 0.20/0.57            = (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.57               (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 0.20/0.57      inference('simplify', [status(thm)], ['22'])).
% 0.20/0.57  thf('24', plain,
% 0.20/0.57      (((m1_subset_1 @ 
% 0.20/0.57         (sk_D @ sk_B @ (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.20/0.57          (u1_struct_0 @ sk_A)) @ 
% 0.20/0.57         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.57        | ((sk_B)
% 0.20/0.57            = (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.57               (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 0.20/0.57      inference('sup-', [status(thm)], ['5', '8'])).
% 0.20/0.57  thf('25', plain,
% 0.20/0.57      ((((sk_B)
% 0.20/0.57          = (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.57             (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B)))
% 0.20/0.57        | (r2_hidden @ 
% 0.20/0.57           (sk_D @ sk_B @ (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.20/0.57            (u1_struct_0 @ sk_A)) @ 
% 0.20/0.57           sk_B))),
% 0.20/0.57      inference('clc', [status(thm)], ['23', '24'])).
% 0.20/0.57  thf('26', plain,
% 0.20/0.57      (((r2_hidden @ 
% 0.20/0.57         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.57          (sk_D @ sk_B @ (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.20/0.57           (u1_struct_0 @ sk_A))) @ 
% 0.20/0.57         (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.20/0.57        | ((sk_B)
% 0.20/0.57            = (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.57               (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 0.20/0.57      inference('clc', [status(thm)], ['13', '25'])).
% 0.20/0.57  thf('27', plain,
% 0.20/0.57      ((m1_subset_1 @ sk_B @ 
% 0.20/0.57        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf('28', plain,
% 0.20/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.57         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X1)))
% 0.20/0.57          | ~ (r2_hidden @ (sk_D @ X0 @ X2 @ X1) @ X0)
% 0.20/0.57          | ~ (r2_hidden @ (k3_subset_1 @ X1 @ (sk_D @ X0 @ X2 @ X1)) @ X2)
% 0.20/0.57          | ((X0) = (k7_setfam_1 @ X1 @ X2))
% 0.20/0.57          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X1))))),
% 0.20/0.57      inference('cnf', [status(esa)], [d8_setfam_1])).
% 0.20/0.57  thf('29', plain,
% 0.20/0.57      (![X0 : $i]:
% 0.20/0.57         (~ (m1_subset_1 @ X0 @ 
% 0.20/0.57             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.20/0.57          | ((sk_B) = (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ X0))
% 0.20/0.57          | ~ (r2_hidden @ 
% 0.20/0.57               (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.57                (sk_D @ sk_B @ X0 @ (u1_struct_0 @ sk_A))) @ 
% 0.20/0.57               X0)
% 0.20/0.57          | ~ (r2_hidden @ (sk_D @ sk_B @ X0 @ (u1_struct_0 @ sk_A)) @ sk_B))),
% 0.20/0.57      inference('sup-', [status(thm)], ['27', '28'])).
% 0.20/0.57  thf('30', plain,
% 0.20/0.57      ((((sk_B)
% 0.20/0.57          = (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.57             (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B)))
% 0.20/0.57        | ~ (r2_hidden @ 
% 0.20/0.57             (sk_D @ sk_B @ (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.20/0.57              (u1_struct_0 @ sk_A)) @ 
% 0.20/0.57             sk_B)
% 0.20/0.57        | ((sk_B)
% 0.20/0.57            = (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.57               (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B)))
% 0.20/0.57        | ~ (m1_subset_1 @ (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.20/0.57             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.20/0.57      inference('sup-', [status(thm)], ['26', '29'])).
% 0.20/0.57  thf('31', plain,
% 0.20/0.57      ((m1_subset_1 @ (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.20/0.57        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.57      inference('sup-', [status(thm)], ['3', '4'])).
% 0.20/0.57  thf('32', plain,
% 0.20/0.57      ((((sk_B)
% 0.20/0.57          = (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.57             (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B)))
% 0.20/0.57        | ~ (r2_hidden @ 
% 0.20/0.57             (sk_D @ sk_B @ (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.20/0.57              (u1_struct_0 @ sk_A)) @ 
% 0.20/0.57             sk_B)
% 0.20/0.57        | ((sk_B)
% 0.20/0.57            = (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.57               (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 0.20/0.57      inference('demod', [status(thm)], ['30', '31'])).
% 0.20/0.57  thf('33', plain,
% 0.20/0.57      ((~ (r2_hidden @ 
% 0.20/0.57           (sk_D @ sk_B @ (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.20/0.57            (u1_struct_0 @ sk_A)) @ 
% 0.20/0.57           sk_B)
% 0.20/0.57        | ((sk_B)
% 0.20/0.57            = (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.57               (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 0.20/0.57      inference('simplify', [status(thm)], ['32'])).
% 0.20/0.57  thf('34', plain,
% 0.20/0.57      ((((sk_B)
% 0.20/0.57          = (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.57             (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B)))
% 0.20/0.57        | (r2_hidden @ 
% 0.20/0.57           (sk_D @ sk_B @ (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.20/0.57            (u1_struct_0 @ sk_A)) @ 
% 0.20/0.57           sk_B))),
% 0.20/0.57      inference('clc', [status(thm)], ['23', '24'])).
% 0.20/0.57  thf('35', plain,
% 0.20/0.57      (((sk_B)
% 0.20/0.57         = (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.57            (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 0.20/0.57      inference('clc', [status(thm)], ['33', '34'])).
% 0.20/0.57  thf('36', plain,
% 0.20/0.57      (((v2_tops_2 @ (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 0.20/0.57        | (v1_tops_2 @ sk_B @ sk_A))),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf('37', plain,
% 0.20/0.57      (((v2_tops_2 @ (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A))
% 0.20/0.57         <= (((v2_tops_2 @ (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)))),
% 0.20/0.57      inference('split', [status(esa)], ['36'])).
% 0.20/0.57  thf('38', plain,
% 0.20/0.57      ((m1_subset_1 @ (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.20/0.57        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.57      inference('sup-', [status(thm)], ['3', '4'])).
% 0.20/0.57  thf(t16_tops_2, axiom,
% 0.20/0.57    (![A:$i]:
% 0.20/0.57     ( ( l1_pre_topc @ A ) =>
% 0.20/0.57       ( ![B:$i]:
% 0.20/0.57         ( ( m1_subset_1 @
% 0.20/0.57             B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.20/0.57           ( ( v2_tops_2 @ B @ A ) <=>
% 0.20/0.57             ( v1_tops_2 @ ( k7_setfam_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) ))).
% 0.20/0.57  thf('39', plain,
% 0.20/0.57      (![X9 : $i, X10 : $i]:
% 0.20/0.57         (~ (m1_subset_1 @ X9 @ 
% 0.20/0.57             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10))))
% 0.20/0.57          | ~ (v2_tops_2 @ X9 @ X10)
% 0.20/0.57          | (v1_tops_2 @ (k7_setfam_1 @ (u1_struct_0 @ X10) @ X9) @ X10)
% 0.20/0.57          | ~ (l1_pre_topc @ X10))),
% 0.20/0.57      inference('cnf', [status(esa)], [t16_tops_2])).
% 0.20/0.57  thf('40', plain,
% 0.20/0.57      ((~ (l1_pre_topc @ sk_A)
% 0.20/0.57        | (v1_tops_2 @ 
% 0.20/0.57           (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.57            (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B)) @ 
% 0.20/0.57           sk_A)
% 0.20/0.57        | ~ (v2_tops_2 @ (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A))),
% 0.20/0.57      inference('sup-', [status(thm)], ['38', '39'])).
% 0.20/0.57  thf('41', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf('42', plain,
% 0.20/0.57      (((v1_tops_2 @ 
% 0.20/0.57         (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.57          (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B)) @ 
% 0.20/0.57         sk_A)
% 0.20/0.57        | ~ (v2_tops_2 @ (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A))),
% 0.20/0.57      inference('demod', [status(thm)], ['40', '41'])).
% 0.20/0.57  thf('43', plain,
% 0.20/0.57      (((v1_tops_2 @ 
% 0.20/0.57         (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.57          (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B)) @ 
% 0.20/0.57         sk_A))
% 0.20/0.57         <= (((v2_tops_2 @ (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)))),
% 0.20/0.57      inference('sup-', [status(thm)], ['37', '42'])).
% 0.20/0.57  thf('44', plain,
% 0.20/0.57      (((v1_tops_2 @ sk_B @ sk_A))
% 0.20/0.57         <= (((v2_tops_2 @ (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)))),
% 0.20/0.57      inference('sup+', [status(thm)], ['35', '43'])).
% 0.20/0.57  thf('45', plain,
% 0.20/0.57      ((~ (v1_tops_2 @ sk_B @ sk_A)) <= (~ ((v1_tops_2 @ sk_B @ sk_A)))),
% 0.20/0.57      inference('split', [status(esa)], ['0'])).
% 0.20/0.57  thf('46', plain,
% 0.20/0.57      (((v1_tops_2 @ sk_B @ sk_A)) | 
% 0.20/0.57       ~ ((v2_tops_2 @ (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A))),
% 0.20/0.57      inference('sup-', [status(thm)], ['44', '45'])).
% 0.20/0.57  thf('47', plain,
% 0.20/0.57      (~ ((v2_tops_2 @ (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A))),
% 0.20/0.57      inference('sat_resolution*', [status(thm)], ['2', '46'])).
% 0.20/0.57  thf('48', plain,
% 0.20/0.57      (~ (v2_tops_2 @ (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)),
% 0.20/0.57      inference('simpl_trail', [status(thm)], ['1', '47'])).
% 0.20/0.57  thf('49', plain,
% 0.20/0.57      ((m1_subset_1 @ (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.20/0.57        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.57      inference('sup-', [status(thm)], ['3', '4'])).
% 0.20/0.57  thf('50', plain,
% 0.20/0.57      (![X4 : $i, X5 : $i]:
% 0.20/0.57         ((m1_subset_1 @ (k7_setfam_1 @ X4 @ X5) @ 
% 0.20/0.57           (k1_zfmisc_1 @ (k1_zfmisc_1 @ X4)))
% 0.20/0.57          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X4))))),
% 0.20/0.57      inference('cnf', [status(esa)], [dt_k7_setfam_1])).
% 0.20/0.57  thf('51', plain,
% 0.20/0.57      ((m1_subset_1 @ 
% 0.20/0.57        (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.57         (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B)) @ 
% 0.20/0.57        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.57      inference('sup-', [status(thm)], ['49', '50'])).
% 0.20/0.57  thf('52', plain,
% 0.20/0.57      (![X4 : $i, X5 : $i]:
% 0.20/0.57         ((m1_subset_1 @ (k7_setfam_1 @ X4 @ X5) @ 
% 0.20/0.57           (k1_zfmisc_1 @ (k1_zfmisc_1 @ X4)))
% 0.20/0.57          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X4))))),
% 0.20/0.57      inference('cnf', [status(esa)], [dt_k7_setfam_1])).
% 0.20/0.57  thf('53', plain,
% 0.20/0.57      ((m1_subset_1 @ 
% 0.20/0.57        (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.57         (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.57          (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B))) @ 
% 0.20/0.57        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.57      inference('sup-', [status(thm)], ['51', '52'])).
% 0.20/0.57  thf('54', plain,
% 0.20/0.57      (![X9 : $i, X10 : $i]:
% 0.20/0.57         (~ (m1_subset_1 @ X9 @ 
% 0.20/0.57             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10))))
% 0.20/0.57          | ~ (v1_tops_2 @ (k7_setfam_1 @ (u1_struct_0 @ X10) @ X9) @ X10)
% 0.20/0.57          | (v2_tops_2 @ X9 @ X10)
% 0.20/0.57          | ~ (l1_pre_topc @ X10))),
% 0.20/0.57      inference('cnf', [status(esa)], [t16_tops_2])).
% 0.20/0.57  thf('55', plain,
% 0.20/0.57      ((~ (l1_pre_topc @ sk_A)
% 0.20/0.57        | (v2_tops_2 @ 
% 0.20/0.57           (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.57            (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.57             (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B))) @ 
% 0.20/0.57           sk_A)
% 0.20/0.57        | ~ (v1_tops_2 @ 
% 0.20/0.57             (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.57              (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.57               (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.57                (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B)))) @ 
% 0.20/0.57             sk_A))),
% 0.20/0.57      inference('sup-', [status(thm)], ['53', '54'])).
% 0.20/0.57  thf('56', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf('57', plain,
% 0.20/0.57      (((v2_tops_2 @ 
% 0.20/0.57         (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.57          (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.57           (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B))) @ 
% 0.20/0.57         sk_A)
% 0.20/0.57        | ~ (v1_tops_2 @ 
% 0.20/0.57             (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.57              (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.57               (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.57                (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B)))) @ 
% 0.20/0.57             sk_A))),
% 0.20/0.57      inference('demod', [status(thm)], ['55', '56'])).
% 0.20/0.57  thf('58', plain,
% 0.20/0.57      (((sk_B)
% 0.20/0.57         = (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.57            (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 0.20/0.57      inference('clc', [status(thm)], ['33', '34'])).
% 0.20/0.57  thf('59', plain,
% 0.20/0.57      (((sk_B)
% 0.20/0.57         = (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.57            (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 0.20/0.57      inference('clc', [status(thm)], ['33', '34'])).
% 0.20/0.57  thf('60', plain,
% 0.20/0.57      (((sk_B)
% 0.20/0.57         = (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.57            (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 0.20/0.57      inference('clc', [status(thm)], ['33', '34'])).
% 0.20/0.57  thf('61', plain,
% 0.20/0.57      (((v2_tops_2 @ (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 0.20/0.57        | ~ (v1_tops_2 @ sk_B @ sk_A))),
% 0.20/0.57      inference('demod', [status(thm)], ['57', '58', '59', '60'])).
% 0.20/0.57  thf('62', plain,
% 0.20/0.57      (((v1_tops_2 @ sk_B @ sk_A)) <= (((v1_tops_2 @ sk_B @ sk_A)))),
% 0.20/0.57      inference('split', [status(esa)], ['36'])).
% 0.20/0.57  thf('63', plain,
% 0.20/0.57      (((v1_tops_2 @ sk_B @ sk_A)) | 
% 0.20/0.57       ((v2_tops_2 @ (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A))),
% 0.20/0.57      inference('split', [status(esa)], ['36'])).
% 0.20/0.57  thf('64', plain, (((v1_tops_2 @ sk_B @ sk_A))),
% 0.20/0.57      inference('sat_resolution*', [status(thm)], ['2', '46', '63'])).
% 0.20/0.57  thf('65', plain, ((v1_tops_2 @ sk_B @ sk_A)),
% 0.20/0.57      inference('simpl_trail', [status(thm)], ['62', '64'])).
% 0.20/0.57  thf('66', plain,
% 0.20/0.57      ((v2_tops_2 @ (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)),
% 0.20/0.57      inference('demod', [status(thm)], ['61', '65'])).
% 0.20/0.57  thf('67', plain, ($false), inference('demod', [status(thm)], ['48', '66'])).
% 0.20/0.57  
% 0.20/0.57  % SZS output end Refutation
% 0.20/0.57  
% 0.20/0.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
