%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.eq6k83vX1c

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:06:33 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  104 ( 429 expanded)
%              Number of leaves         :   19 ( 120 expanded)
%              Depth                    :   21
%              Number of atoms          : 1025 (5200 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   14 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_tops_2_type,type,(
    v1_tops_2: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t78_tops_2,conjecture,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
         => ( ( v1_tops_2 @ B @ A )
          <=> ( r1_tarski @ B @ ( u1_pre_topc @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_pre_topc @ A )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
           => ( ( v1_tops_2 @ B @ A )
            <=> ( r1_tarski @ B @ ( u1_pre_topc @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t78_tops_2])).

thf('0',plain,
    ( ~ ( r1_tarski @ sk_B @ ( u1_pre_topc @ sk_A ) )
    | ~ ( v1_tops_2 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r1_tarski @ sk_B @ ( u1_pre_topc @ sk_A ) )
   <= ~ ( r1_tarski @ sk_B @ ( u1_pre_topc @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( r1_tarski @ sk_B @ ( u1_pre_topc @ sk_A ) )
    | ~ ( v1_tops_2 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf(dt_u1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( m1_subset_1 @ ( u1_pre_topc @ A ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('3',plain,(
    ! [X5: $i] :
      ( ( m1_subset_1 @ ( u1_pre_topc @ X5 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) ) )
      | ~ ( l1_pre_topc @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_pre_topc])).

thf(d1_tops_2,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
         => ( ( v1_tops_2 @ B @ A )
          <=> ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
               => ( ( r2_hidden @ C @ B )
                 => ( v3_pre_topc @ C @ A ) ) ) ) ) ) )).

thf('4',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) ) )
      | ( r2_hidden @ ( sk_C @ X6 @ X7 ) @ X6 )
      | ( v1_tops_2 @ X6 @ X7 )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[d1_tops_2])).

thf('5',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v1_tops_2 @ ( u1_pre_topc @ X0 ) @ X0 )
      | ( r2_hidden @ ( sk_C @ ( u1_pre_topc @ X0 ) @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ ( u1_pre_topc @ X0 ) @ X0 ) @ ( u1_pre_topc @ X0 ) )
      | ( v1_tops_2 @ ( u1_pre_topc @ X0 ) @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,(
    ! [X5: $i] :
      ( ( m1_subset_1 @ ( u1_pre_topc @ X5 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) ) )
      | ~ ( l1_pre_topc @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_pre_topc])).

thf('8',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) ) )
      | ( m1_subset_1 @ ( sk_C @ X6 @ X7 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) )
      | ( v1_tops_2 @ X6 @ X7 )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[d1_tops_2])).

thf('9',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v1_tops_2 @ ( u1_pre_topc @ X0 ) @ X0 )
      | ( m1_subset_1 @ ( sk_C @ ( u1_pre_topc @ X0 ) @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( sk_C @ ( u1_pre_topc @ X0 ) @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( v1_tops_2 @ ( u1_pre_topc @ X0 ) @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf(d5_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v3_pre_topc @ B @ A )
          <=> ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) ) ) ) )).

thf('11',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X4 ) ) )
      | ~ ( r2_hidden @ X3 @ ( u1_pre_topc @ X4 ) )
      | ( v3_pre_topc @ X3 @ X4 )
      | ~ ( l1_pre_topc @ X4 ) ) ),
    inference(cnf,[status(esa)],[d5_pre_topc])).

thf('12',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v1_tops_2 @ ( u1_pre_topc @ X0 ) @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v3_pre_topc @ ( sk_C @ ( u1_pre_topc @ X0 ) @ X0 ) @ X0 )
      | ~ ( r2_hidden @ ( sk_C @ ( u1_pre_topc @ X0 ) @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( sk_C @ ( u1_pre_topc @ X0 ) @ X0 ) @ ( u1_pre_topc @ X0 ) )
      | ( v3_pre_topc @ ( sk_C @ ( u1_pre_topc @ X0 ) @ X0 ) @ X0 )
      | ( v1_tops_2 @ ( u1_pre_topc @ X0 ) @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v1_tops_2 @ ( u1_pre_topc @ X0 ) @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v1_tops_2 @ ( u1_pre_topc @ X0 ) @ X0 )
      | ( v3_pre_topc @ ( sk_C @ ( u1_pre_topc @ X0 ) @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( v3_pre_topc @ ( sk_C @ ( u1_pre_topc @ X0 ) @ X0 ) @ X0 )
      | ( v1_tops_2 @ ( u1_pre_topc @ X0 ) @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    ! [X5: $i] :
      ( ( m1_subset_1 @ ( u1_pre_topc @ X5 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) ) )
      | ~ ( l1_pre_topc @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_pre_topc])).

thf('17',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) ) )
      | ~ ( v3_pre_topc @ ( sk_C @ X6 @ X7 ) @ X7 )
      | ( v1_tops_2 @ X6 @ X7 )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[d1_tops_2])).

thf('18',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v1_tops_2 @ ( u1_pre_topc @ X0 ) @ X0 )
      | ~ ( v3_pre_topc @ ( sk_C @ ( u1_pre_topc @ X0 ) @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( v3_pre_topc @ ( sk_C @ ( u1_pre_topc @ X0 ) @ X0 ) @ X0 )
      | ( v1_tops_2 @ ( u1_pre_topc @ X0 ) @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v1_tops_2 @ ( u1_pre_topc @ X0 ) @ X0 ) ) ),
    inference(clc,[status(thm)],['15','19'])).

thf('21',plain,
    ( ( r1_tarski @ sk_B @ ( u1_pre_topc @ sk_A ) )
    | ( v1_tops_2 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,
    ( ( r1_tarski @ sk_B @ ( u1_pre_topc @ sk_A ) )
   <= ( r1_tarski @ sk_B @ ( u1_pre_topc @ sk_A ) ) ),
    inference(split,[status(esa)],['21'])).

thf('23',plain,(
    ! [X5: $i] :
      ( ( m1_subset_1 @ ( u1_pre_topc @ X5 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) ) )
      | ~ ( l1_pre_topc @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_pre_topc])).

thf('24',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t18_tops_2,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
             => ( ( ( r1_tarski @ B @ C )
                  & ( v1_tops_2 @ C @ A ) )
               => ( v1_tops_2 @ B @ A ) ) ) ) ) )).

thf('25',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) ) )
      | ( v1_tops_2 @ X9 @ X10 )
      | ~ ( r1_tarski @ X9 @ X11 )
      | ~ ( v1_tops_2 @ X11 @ X10 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) ) )
      | ~ ( l1_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[t18_tops_2])).

thf('26',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
      | ~ ( v1_tops_2 @ X0 @ sk_A )
      | ~ ( r1_tarski @ sk_B @ X0 )
      | ( v1_tops_2 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
      | ~ ( v1_tops_2 @ X0 @ sk_A )
      | ~ ( r1_tarski @ sk_B @ X0 )
      | ( v1_tops_2 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v1_tops_2 @ sk_B @ sk_A )
    | ~ ( r1_tarski @ sk_B @ ( u1_pre_topc @ sk_A ) )
    | ~ ( v1_tops_2 @ ( u1_pre_topc @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['23','28'])).

thf('30',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( v1_tops_2 @ sk_B @ sk_A )
    | ~ ( r1_tarski @ sk_B @ ( u1_pre_topc @ sk_A ) )
    | ~ ( v1_tops_2 @ ( u1_pre_topc @ sk_A ) @ sk_A ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,
    ( ( ~ ( v1_tops_2 @ ( u1_pre_topc @ sk_A ) @ sk_A )
      | ( v1_tops_2 @ sk_B @ sk_A ) )
   <= ( r1_tarski @ sk_B @ ( u1_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['22','31'])).

thf('33',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ( v1_tops_2 @ sk_B @ sk_A ) )
   <= ( r1_tarski @ sk_B @ ( u1_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['20','32'])).

thf('34',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( v1_tops_2 @ sk_B @ sk_A )
   <= ( r1_tarski @ sk_B @ ( u1_pre_topc @ sk_A ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,
    ( ~ ( v1_tops_2 @ sk_B @ sk_A )
   <= ~ ( v1_tops_2 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('37',plain,
    ( ( v1_tops_2 @ sk_B @ sk_A )
    | ~ ( r1_tarski @ sk_B @ ( u1_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ~ ( r1_tarski @ sk_B @ ( u1_pre_topc @ sk_A ) ) ),
    inference('sat_resolution*',[status(thm)],['2','37'])).

thf('39',plain,(
    ~ ( r1_tarski @ sk_B @ ( u1_pre_topc @ sk_A ) ) ),
    inference(simpl_trail,[status(thm)],['1','38'])).

thf('40',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    ! [X5: $i] :
      ( ( m1_subset_1 @ ( u1_pre_topc @ X5 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) ) )
      | ~ ( l1_pre_topc @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_pre_topc])).

thf(t7_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ! [D: $i] :
                ( ( m1_subset_1 @ D @ A )
               => ( ( r2_hidden @ D @ B )
                 => ( r2_hidden @ D @ C ) ) )
           => ( r1_tarski @ B @ C ) ) ) ) )).

thf('42',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( r1_tarski @ X2 @ X0 )
      | ( m1_subset_1 @ ( sk_D @ X0 @ X2 @ X1 ) @ X1 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[t7_subset_1])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) )
      | ( m1_subset_1 @ ( sk_D @ ( u1_pre_topc @ X0 ) @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( r1_tarski @ X1 @ ( u1_pre_topc @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,
    ( ( r1_tarski @ sk_B @ ( u1_pre_topc @ sk_A ) )
    | ( m1_subset_1 @ ( sk_D @ ( u1_pre_topc @ sk_A ) @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['40','43'])).

thf('45',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( ( r1_tarski @ sk_B @ ( u1_pre_topc @ sk_A ) )
    | ( m1_subset_1 @ ( sk_D @ ( u1_pre_topc @ sk_A ) @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,(
    ~ ( r1_tarski @ sk_B @ ( u1_pre_topc @ sk_A ) ) ),
    inference(simpl_trail,[status(thm)],['1','38'])).

thf('48',plain,(
    m1_subset_1 @ ( sk_D @ ( u1_pre_topc @ sk_A ) @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X4 ) ) )
      | ~ ( v3_pre_topc @ X3 @ X4 )
      | ( r2_hidden @ X3 @ ( u1_pre_topc @ X4 ) )
      | ~ ( l1_pre_topc @ X4 ) ) ),
    inference(cnf,[status(esa)],[d5_pre_topc])).

thf('50',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r2_hidden @ ( sk_D @ ( u1_pre_topc @ sk_A ) @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) @ ( u1_pre_topc @ sk_A ) )
    | ~ ( v3_pre_topc @ ( sk_D @ ( u1_pre_topc @ sk_A ) @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,
    ( ( r2_hidden @ ( sk_D @ ( u1_pre_topc @ sk_A ) @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) @ ( u1_pre_topc @ sk_A ) )
    | ~ ( v3_pre_topc @ ( sk_D @ ( u1_pre_topc @ sk_A ) @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) @ sk_A ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    ! [X5: $i] :
      ( ( m1_subset_1 @ ( u1_pre_topc @ X5 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) ) )
      | ~ ( l1_pre_topc @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_pre_topc])).

thf('55',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( r1_tarski @ X2 @ X0 )
      | ( r2_hidden @ ( sk_D @ X0 @ X2 @ X1 ) @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[t7_subset_1])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) )
      | ( r2_hidden @ ( sk_D @ ( u1_pre_topc @ X0 ) @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) @ X1 )
      | ( r1_tarski @ X1 @ ( u1_pre_topc @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,
    ( ( r1_tarski @ sk_B @ ( u1_pre_topc @ sk_A ) )
    | ( r2_hidden @ ( sk_D @ ( u1_pre_topc @ sk_A ) @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) @ sk_B )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['53','56'])).

thf('58',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,
    ( ( r1_tarski @ sk_B @ ( u1_pre_topc @ sk_A ) )
    | ( r2_hidden @ ( sk_D @ ( u1_pre_topc @ sk_A ) @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) @ sk_B ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,(
    m1_subset_1 @ ( sk_D @ ( u1_pre_topc @ sk_A ) @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['46','47'])).

thf('61',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) ) )
      | ~ ( v1_tops_2 @ X6 @ X7 )
      | ~ ( r2_hidden @ X8 @ X6 )
      | ( v3_pre_topc @ X8 @ X7 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[d1_tops_2])).

thf('63',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v3_pre_topc @ X0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ sk_B )
      | ~ ( v1_tops_2 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v3_pre_topc @ X0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ sk_B )
      | ~ ( v1_tops_2 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('66',plain,
    ( ( v1_tops_2 @ sk_B @ sk_A )
   <= ( v1_tops_2 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['21'])).

thf('67',plain,
    ( ( v1_tops_2 @ sk_B @ sk_A )
    | ( r1_tarski @ sk_B @ ( u1_pre_topc @ sk_A ) ) ),
    inference(split,[status(esa)],['21'])).

thf('68',plain,(
    v1_tops_2 @ sk_B @ sk_A ),
    inference('sat_resolution*',[status(thm)],['2','37','67'])).

thf('69',plain,(
    v1_tops_2 @ sk_B @ sk_A ),
    inference(simpl_trail,[status(thm)],['66','68'])).

thf('70',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v3_pre_topc @ X0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['65','69'])).

thf('71',plain,
    ( ~ ( r2_hidden @ ( sk_D @ ( u1_pre_topc @ sk_A ) @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) @ sk_B )
    | ( v3_pre_topc @ ( sk_D @ ( u1_pre_topc @ sk_A ) @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['60','70'])).

thf('72',plain,
    ( ( r1_tarski @ sk_B @ ( u1_pre_topc @ sk_A ) )
    | ( v3_pre_topc @ ( sk_D @ ( u1_pre_topc @ sk_A ) @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['59','71'])).

thf('73',plain,(
    ~ ( r1_tarski @ sk_B @ ( u1_pre_topc @ sk_A ) ) ),
    inference(simpl_trail,[status(thm)],['1','38'])).

thf('74',plain,(
    v3_pre_topc @ ( sk_D @ ( u1_pre_topc @ sk_A ) @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) @ sk_A ),
    inference(clc,[status(thm)],['72','73'])).

thf('75',plain,(
    r2_hidden @ ( sk_D @ ( u1_pre_topc @ sk_A ) @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) @ ( u1_pre_topc @ sk_A ) ),
    inference(demod,[status(thm)],['52','74'])).

thf('76',plain,(
    ! [X5: $i] :
      ( ( m1_subset_1 @ ( u1_pre_topc @ X5 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) ) )
      | ~ ( l1_pre_topc @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_pre_topc])).

thf('77',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( r1_tarski @ X2 @ X0 )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X2 @ X1 ) @ X0 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[t7_subset_1])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( r2_hidden @ ( sk_D @ ( u1_pre_topc @ X0 ) @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) @ ( u1_pre_topc @ X0 ) )
      | ( r1_tarski @ X1 @ ( u1_pre_topc @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,
    ( ( r1_tarski @ sk_B @ ( u1_pre_topc @ sk_A ) )
    | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['75','78'])).

thf('80',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    r1_tarski @ sk_B @ ( u1_pre_topc @ sk_A ) ),
    inference(demod,[status(thm)],['79','80','81'])).

thf('83',plain,(
    $false ),
    inference(demod,[status(thm)],['39','82'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.eq6k83vX1c
% 0.13/0.33  % Computer   : n022.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:27:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.20/0.48  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.48  % Solved by: fo/fo7.sh
% 0.20/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.48  % done 62 iterations in 0.037s
% 0.20/0.48  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.48  % SZS output start Refutation
% 0.20/0.48  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.48  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.48  thf(v1_tops_2_type, type, v1_tops_2: $i > $i > $o).
% 0.20/0.48  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.48  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.48  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.20/0.48  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.20/0.48  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 0.20/0.48  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.20/0.48  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.48  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.48  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.20/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.48  thf(t78_tops_2, conjecture,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ( l1_pre_topc @ A ) =>
% 0.20/0.48       ( ![B:$i]:
% 0.20/0.48         ( ( m1_subset_1 @
% 0.20/0.48             B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.20/0.48           ( ( v1_tops_2 @ B @ A ) <=> ( r1_tarski @ B @ ( u1_pre_topc @ A ) ) ) ) ) ))).
% 0.20/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.48    (~( ![A:$i]:
% 0.20/0.48        ( ( l1_pre_topc @ A ) =>
% 0.20/0.48          ( ![B:$i]:
% 0.20/0.48            ( ( m1_subset_1 @
% 0.20/0.48                B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.20/0.48              ( ( v1_tops_2 @ B @ A ) <=>
% 0.20/0.48                ( r1_tarski @ B @ ( u1_pre_topc @ A ) ) ) ) ) ) )),
% 0.20/0.48    inference('cnf.neg', [status(esa)], [t78_tops_2])).
% 0.20/0.48  thf('0', plain,
% 0.20/0.48      ((~ (r1_tarski @ sk_B @ (u1_pre_topc @ sk_A))
% 0.20/0.48        | ~ (v1_tops_2 @ sk_B @ sk_A))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('1', plain,
% 0.20/0.48      ((~ (r1_tarski @ sk_B @ (u1_pre_topc @ sk_A)))
% 0.20/0.48         <= (~ ((r1_tarski @ sk_B @ (u1_pre_topc @ sk_A))))),
% 0.20/0.48      inference('split', [status(esa)], ['0'])).
% 0.20/0.48  thf('2', plain,
% 0.20/0.48      (~ ((r1_tarski @ sk_B @ (u1_pre_topc @ sk_A))) | 
% 0.20/0.48       ~ ((v1_tops_2 @ sk_B @ sk_A))),
% 0.20/0.48      inference('split', [status(esa)], ['0'])).
% 0.20/0.48  thf(dt_u1_pre_topc, axiom,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ( l1_pre_topc @ A ) =>
% 0.20/0.48       ( m1_subset_1 @
% 0.20/0.48         ( u1_pre_topc @ A ) @ 
% 0.20/0.48         ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ))).
% 0.20/0.48  thf('3', plain,
% 0.20/0.48      (![X5 : $i]:
% 0.20/0.48         ((m1_subset_1 @ (u1_pre_topc @ X5) @ 
% 0.20/0.48           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X5))))
% 0.20/0.48          | ~ (l1_pre_topc @ X5))),
% 0.20/0.48      inference('cnf', [status(esa)], [dt_u1_pre_topc])).
% 0.20/0.48  thf(d1_tops_2, axiom,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ( l1_pre_topc @ A ) =>
% 0.20/0.48       ( ![B:$i]:
% 0.20/0.48         ( ( m1_subset_1 @
% 0.20/0.48             B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.20/0.48           ( ( v1_tops_2 @ B @ A ) <=>
% 0.20/0.48             ( ![C:$i]:
% 0.20/0.48               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.48                 ( ( r2_hidden @ C @ B ) => ( v3_pre_topc @ C @ A ) ) ) ) ) ) ) ))).
% 0.20/0.48  thf('4', plain,
% 0.20/0.48      (![X6 : $i, X7 : $i]:
% 0.20/0.48         (~ (m1_subset_1 @ X6 @ 
% 0.20/0.48             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X7))))
% 0.20/0.48          | (r2_hidden @ (sk_C @ X6 @ X7) @ X6)
% 0.20/0.48          | (v1_tops_2 @ X6 @ X7)
% 0.20/0.48          | ~ (l1_pre_topc @ X7))),
% 0.20/0.48      inference('cnf', [status(esa)], [d1_tops_2])).
% 0.20/0.48  thf('5', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         (~ (l1_pre_topc @ X0)
% 0.20/0.48          | ~ (l1_pre_topc @ X0)
% 0.20/0.48          | (v1_tops_2 @ (u1_pre_topc @ X0) @ X0)
% 0.20/0.48          | (r2_hidden @ (sk_C @ (u1_pre_topc @ X0) @ X0) @ (u1_pre_topc @ X0)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['3', '4'])).
% 0.20/0.48  thf('6', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         ((r2_hidden @ (sk_C @ (u1_pre_topc @ X0) @ X0) @ (u1_pre_topc @ X0))
% 0.20/0.48          | (v1_tops_2 @ (u1_pre_topc @ X0) @ X0)
% 0.20/0.48          | ~ (l1_pre_topc @ X0))),
% 0.20/0.48      inference('simplify', [status(thm)], ['5'])).
% 0.20/0.48  thf('7', plain,
% 0.20/0.48      (![X5 : $i]:
% 0.20/0.48         ((m1_subset_1 @ (u1_pre_topc @ X5) @ 
% 0.20/0.48           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X5))))
% 0.20/0.48          | ~ (l1_pre_topc @ X5))),
% 0.20/0.48      inference('cnf', [status(esa)], [dt_u1_pre_topc])).
% 0.20/0.48  thf('8', plain,
% 0.20/0.48      (![X6 : $i, X7 : $i]:
% 0.20/0.48         (~ (m1_subset_1 @ X6 @ 
% 0.20/0.48             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X7))))
% 0.20/0.48          | (m1_subset_1 @ (sk_C @ X6 @ X7) @ 
% 0.20/0.48             (k1_zfmisc_1 @ (u1_struct_0 @ X7)))
% 0.20/0.48          | (v1_tops_2 @ X6 @ X7)
% 0.20/0.48          | ~ (l1_pre_topc @ X7))),
% 0.20/0.48      inference('cnf', [status(esa)], [d1_tops_2])).
% 0.20/0.48  thf('9', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         (~ (l1_pre_topc @ X0)
% 0.20/0.48          | ~ (l1_pre_topc @ X0)
% 0.20/0.48          | (v1_tops_2 @ (u1_pre_topc @ X0) @ X0)
% 0.20/0.48          | (m1_subset_1 @ (sk_C @ (u1_pre_topc @ X0) @ X0) @ 
% 0.20/0.48             (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.20/0.48      inference('sup-', [status(thm)], ['7', '8'])).
% 0.20/0.48  thf('10', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         ((m1_subset_1 @ (sk_C @ (u1_pre_topc @ X0) @ X0) @ 
% 0.20/0.48           (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.20/0.48          | (v1_tops_2 @ (u1_pre_topc @ X0) @ X0)
% 0.20/0.48          | ~ (l1_pre_topc @ X0))),
% 0.20/0.48      inference('simplify', [status(thm)], ['9'])).
% 0.20/0.48  thf(d5_pre_topc, axiom,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ( l1_pre_topc @ A ) =>
% 0.20/0.48       ( ![B:$i]:
% 0.20/0.48         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.48           ( ( v3_pre_topc @ B @ A ) <=>
% 0.20/0.48             ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) ) ) ) ))).
% 0.20/0.48  thf('11', plain,
% 0.20/0.48      (![X3 : $i, X4 : $i]:
% 0.20/0.48         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (u1_struct_0 @ X4)))
% 0.20/0.48          | ~ (r2_hidden @ X3 @ (u1_pre_topc @ X4))
% 0.20/0.48          | (v3_pre_topc @ X3 @ X4)
% 0.20/0.48          | ~ (l1_pre_topc @ X4))),
% 0.20/0.48      inference('cnf', [status(esa)], [d5_pre_topc])).
% 0.20/0.48  thf('12', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         (~ (l1_pre_topc @ X0)
% 0.20/0.48          | (v1_tops_2 @ (u1_pre_topc @ X0) @ X0)
% 0.20/0.48          | ~ (l1_pre_topc @ X0)
% 0.20/0.48          | (v3_pre_topc @ (sk_C @ (u1_pre_topc @ X0) @ X0) @ X0)
% 0.20/0.48          | ~ (r2_hidden @ (sk_C @ (u1_pre_topc @ X0) @ X0) @ 
% 0.20/0.48               (u1_pre_topc @ X0)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['10', '11'])).
% 0.20/0.48  thf('13', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         (~ (r2_hidden @ (sk_C @ (u1_pre_topc @ X0) @ X0) @ (u1_pre_topc @ X0))
% 0.20/0.48          | (v3_pre_topc @ (sk_C @ (u1_pre_topc @ X0) @ X0) @ X0)
% 0.20/0.48          | (v1_tops_2 @ (u1_pre_topc @ X0) @ X0)
% 0.20/0.48          | ~ (l1_pre_topc @ X0))),
% 0.20/0.48      inference('simplify', [status(thm)], ['12'])).
% 0.20/0.48  thf('14', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         (~ (l1_pre_topc @ X0)
% 0.20/0.48          | (v1_tops_2 @ (u1_pre_topc @ X0) @ X0)
% 0.20/0.48          | ~ (l1_pre_topc @ X0)
% 0.20/0.48          | (v1_tops_2 @ (u1_pre_topc @ X0) @ X0)
% 0.20/0.48          | (v3_pre_topc @ (sk_C @ (u1_pre_topc @ X0) @ X0) @ X0))),
% 0.20/0.48      inference('sup-', [status(thm)], ['6', '13'])).
% 0.20/0.48  thf('15', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         ((v3_pre_topc @ (sk_C @ (u1_pre_topc @ X0) @ X0) @ X0)
% 0.20/0.48          | (v1_tops_2 @ (u1_pre_topc @ X0) @ X0)
% 0.20/0.48          | ~ (l1_pre_topc @ X0))),
% 0.20/0.48      inference('simplify', [status(thm)], ['14'])).
% 0.20/0.48  thf('16', plain,
% 0.20/0.48      (![X5 : $i]:
% 0.20/0.48         ((m1_subset_1 @ (u1_pre_topc @ X5) @ 
% 0.20/0.48           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X5))))
% 0.20/0.48          | ~ (l1_pre_topc @ X5))),
% 0.20/0.48      inference('cnf', [status(esa)], [dt_u1_pre_topc])).
% 0.20/0.48  thf('17', plain,
% 0.20/0.48      (![X6 : $i, X7 : $i]:
% 0.20/0.48         (~ (m1_subset_1 @ X6 @ 
% 0.20/0.48             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X7))))
% 0.20/0.48          | ~ (v3_pre_topc @ (sk_C @ X6 @ X7) @ X7)
% 0.20/0.48          | (v1_tops_2 @ X6 @ X7)
% 0.20/0.48          | ~ (l1_pre_topc @ X7))),
% 0.20/0.48      inference('cnf', [status(esa)], [d1_tops_2])).
% 0.20/0.48  thf('18', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         (~ (l1_pre_topc @ X0)
% 0.20/0.48          | ~ (l1_pre_topc @ X0)
% 0.20/0.48          | (v1_tops_2 @ (u1_pre_topc @ X0) @ X0)
% 0.20/0.48          | ~ (v3_pre_topc @ (sk_C @ (u1_pre_topc @ X0) @ X0) @ X0))),
% 0.20/0.48      inference('sup-', [status(thm)], ['16', '17'])).
% 0.20/0.48  thf('19', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         (~ (v3_pre_topc @ (sk_C @ (u1_pre_topc @ X0) @ X0) @ X0)
% 0.20/0.48          | (v1_tops_2 @ (u1_pre_topc @ X0) @ X0)
% 0.20/0.48          | ~ (l1_pre_topc @ X0))),
% 0.20/0.48      inference('simplify', [status(thm)], ['18'])).
% 0.20/0.48  thf('20', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         (~ (l1_pre_topc @ X0) | (v1_tops_2 @ (u1_pre_topc @ X0) @ X0))),
% 0.20/0.48      inference('clc', [status(thm)], ['15', '19'])).
% 0.20/0.48  thf('21', plain,
% 0.20/0.48      (((r1_tarski @ sk_B @ (u1_pre_topc @ sk_A)) | (v1_tops_2 @ sk_B @ sk_A))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('22', plain,
% 0.20/0.48      (((r1_tarski @ sk_B @ (u1_pre_topc @ sk_A)))
% 0.20/0.48         <= (((r1_tarski @ sk_B @ (u1_pre_topc @ sk_A))))),
% 0.20/0.48      inference('split', [status(esa)], ['21'])).
% 0.20/0.48  thf('23', plain,
% 0.20/0.48      (![X5 : $i]:
% 0.20/0.48         ((m1_subset_1 @ (u1_pre_topc @ X5) @ 
% 0.20/0.48           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X5))))
% 0.20/0.48          | ~ (l1_pre_topc @ X5))),
% 0.20/0.48      inference('cnf', [status(esa)], [dt_u1_pre_topc])).
% 0.20/0.48  thf('24', plain,
% 0.20/0.48      ((m1_subset_1 @ sk_B @ 
% 0.20/0.48        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf(t18_tops_2, axiom,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ( l1_pre_topc @ A ) =>
% 0.20/0.48       ( ![B:$i]:
% 0.20/0.48         ( ( m1_subset_1 @
% 0.20/0.48             B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.20/0.48           ( ![C:$i]:
% 0.20/0.48             ( ( m1_subset_1 @
% 0.20/0.48                 C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.20/0.48               ( ( ( r1_tarski @ B @ C ) & ( v1_tops_2 @ C @ A ) ) =>
% 0.20/0.48                 ( v1_tops_2 @ B @ A ) ) ) ) ) ) ))).
% 0.20/0.48  thf('25', plain,
% 0.20/0.48      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.20/0.48         (~ (m1_subset_1 @ X9 @ 
% 0.20/0.48             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10))))
% 0.20/0.48          | (v1_tops_2 @ X9 @ X10)
% 0.20/0.48          | ~ (r1_tarski @ X9 @ X11)
% 0.20/0.48          | ~ (v1_tops_2 @ X11 @ X10)
% 0.20/0.48          | ~ (m1_subset_1 @ X11 @ 
% 0.20/0.48               (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10))))
% 0.20/0.48          | ~ (l1_pre_topc @ X10))),
% 0.20/0.48      inference('cnf', [status(esa)], [t18_tops_2])).
% 0.20/0.48  thf('26', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         (~ (l1_pre_topc @ sk_A)
% 0.20/0.48          | ~ (m1_subset_1 @ X0 @ 
% 0.20/0.48               (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.20/0.48          | ~ (v1_tops_2 @ X0 @ sk_A)
% 0.20/0.48          | ~ (r1_tarski @ sk_B @ X0)
% 0.20/0.48          | (v1_tops_2 @ sk_B @ sk_A))),
% 0.20/0.48      inference('sup-', [status(thm)], ['24', '25'])).
% 0.20/0.48  thf('27', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('28', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         (~ (m1_subset_1 @ X0 @ 
% 0.20/0.48             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.20/0.48          | ~ (v1_tops_2 @ X0 @ sk_A)
% 0.20/0.48          | ~ (r1_tarski @ sk_B @ X0)
% 0.20/0.48          | (v1_tops_2 @ sk_B @ sk_A))),
% 0.20/0.48      inference('demod', [status(thm)], ['26', '27'])).
% 0.20/0.48  thf('29', plain,
% 0.20/0.48      ((~ (l1_pre_topc @ sk_A)
% 0.20/0.48        | (v1_tops_2 @ sk_B @ sk_A)
% 0.20/0.48        | ~ (r1_tarski @ sk_B @ (u1_pre_topc @ sk_A))
% 0.20/0.48        | ~ (v1_tops_2 @ (u1_pre_topc @ sk_A) @ sk_A))),
% 0.20/0.48      inference('sup-', [status(thm)], ['23', '28'])).
% 0.20/0.48  thf('30', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('31', plain,
% 0.20/0.48      (((v1_tops_2 @ sk_B @ sk_A)
% 0.20/0.48        | ~ (r1_tarski @ sk_B @ (u1_pre_topc @ sk_A))
% 0.20/0.48        | ~ (v1_tops_2 @ (u1_pre_topc @ sk_A) @ sk_A))),
% 0.20/0.48      inference('demod', [status(thm)], ['29', '30'])).
% 0.20/0.48  thf('32', plain,
% 0.20/0.48      (((~ (v1_tops_2 @ (u1_pre_topc @ sk_A) @ sk_A)
% 0.20/0.48         | (v1_tops_2 @ sk_B @ sk_A)))
% 0.20/0.48         <= (((r1_tarski @ sk_B @ (u1_pre_topc @ sk_A))))),
% 0.20/0.48      inference('sup-', [status(thm)], ['22', '31'])).
% 0.20/0.48  thf('33', plain,
% 0.20/0.48      (((~ (l1_pre_topc @ sk_A) | (v1_tops_2 @ sk_B @ sk_A)))
% 0.20/0.48         <= (((r1_tarski @ sk_B @ (u1_pre_topc @ sk_A))))),
% 0.20/0.48      inference('sup-', [status(thm)], ['20', '32'])).
% 0.20/0.48  thf('34', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('35', plain,
% 0.20/0.48      (((v1_tops_2 @ sk_B @ sk_A))
% 0.20/0.48         <= (((r1_tarski @ sk_B @ (u1_pre_topc @ sk_A))))),
% 0.20/0.48      inference('demod', [status(thm)], ['33', '34'])).
% 0.20/0.48  thf('36', plain,
% 0.20/0.48      ((~ (v1_tops_2 @ sk_B @ sk_A)) <= (~ ((v1_tops_2 @ sk_B @ sk_A)))),
% 0.20/0.48      inference('split', [status(esa)], ['0'])).
% 0.20/0.48  thf('37', plain,
% 0.20/0.48      (((v1_tops_2 @ sk_B @ sk_A)) | 
% 0.20/0.48       ~ ((r1_tarski @ sk_B @ (u1_pre_topc @ sk_A)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['35', '36'])).
% 0.20/0.48  thf('38', plain, (~ ((r1_tarski @ sk_B @ (u1_pre_topc @ sk_A)))),
% 0.20/0.48      inference('sat_resolution*', [status(thm)], ['2', '37'])).
% 0.20/0.48  thf('39', plain, (~ (r1_tarski @ sk_B @ (u1_pre_topc @ sk_A))),
% 0.20/0.48      inference('simpl_trail', [status(thm)], ['1', '38'])).
% 0.20/0.48  thf('40', plain,
% 0.20/0.48      ((m1_subset_1 @ sk_B @ 
% 0.20/0.48        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('41', plain,
% 0.20/0.48      (![X5 : $i]:
% 0.20/0.48         ((m1_subset_1 @ (u1_pre_topc @ X5) @ 
% 0.20/0.48           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X5))))
% 0.20/0.48          | ~ (l1_pre_topc @ X5))),
% 0.20/0.48      inference('cnf', [status(esa)], [dt_u1_pre_topc])).
% 0.20/0.48  thf(t7_subset_1, axiom,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.48       ( ![C:$i]:
% 0.20/0.48         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.48           ( ( ![D:$i]:
% 0.20/0.48               ( ( m1_subset_1 @ D @ A ) =>
% 0.20/0.48                 ( ( r2_hidden @ D @ B ) => ( r2_hidden @ D @ C ) ) ) ) =>
% 0.20/0.48             ( r1_tarski @ B @ C ) ) ) ) ))).
% 0.20/0.48  thf('42', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.48         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.20/0.48          | (r1_tarski @ X2 @ X0)
% 0.20/0.48          | (m1_subset_1 @ (sk_D @ X0 @ X2 @ X1) @ X1)
% 0.20/0.48          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X1)))),
% 0.20/0.48      inference('cnf', [status(esa)], [t7_subset_1])).
% 0.20/0.48  thf('43', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i]:
% 0.20/0.48         (~ (l1_pre_topc @ X0)
% 0.20/0.48          | ~ (m1_subset_1 @ X1 @ 
% 0.20/0.48               (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0))))
% 0.20/0.48          | (m1_subset_1 @ 
% 0.20/0.48             (sk_D @ (u1_pre_topc @ X0) @ X1 @ 
% 0.20/0.48              (k1_zfmisc_1 @ (u1_struct_0 @ X0))) @ 
% 0.20/0.48             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.20/0.48          | (r1_tarski @ X1 @ (u1_pre_topc @ X0)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['41', '42'])).
% 0.20/0.48  thf('44', plain,
% 0.20/0.48      (((r1_tarski @ sk_B @ (u1_pre_topc @ sk_A))
% 0.20/0.48        | (m1_subset_1 @ 
% 0.20/0.48           (sk_D @ (u1_pre_topc @ sk_A) @ sk_B @ 
% 0.20/0.48            (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))) @ 
% 0.20/0.48           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.48        | ~ (l1_pre_topc @ sk_A))),
% 0.20/0.48      inference('sup-', [status(thm)], ['40', '43'])).
% 0.20/0.48  thf('45', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('46', plain,
% 0.20/0.48      (((r1_tarski @ sk_B @ (u1_pre_topc @ sk_A))
% 0.20/0.48        | (m1_subset_1 @ 
% 0.20/0.48           (sk_D @ (u1_pre_topc @ sk_A) @ sk_B @ 
% 0.20/0.48            (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))) @ 
% 0.20/0.48           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.48      inference('demod', [status(thm)], ['44', '45'])).
% 0.20/0.48  thf('47', plain, (~ (r1_tarski @ sk_B @ (u1_pre_topc @ sk_A))),
% 0.20/0.48      inference('simpl_trail', [status(thm)], ['1', '38'])).
% 0.20/0.48  thf('48', plain,
% 0.20/0.48      ((m1_subset_1 @ 
% 0.20/0.48        (sk_D @ (u1_pre_topc @ sk_A) @ sk_B @ 
% 0.20/0.48         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))) @ 
% 0.20/0.48        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.48      inference('clc', [status(thm)], ['46', '47'])).
% 0.20/0.48  thf('49', plain,
% 0.20/0.48      (![X3 : $i, X4 : $i]:
% 0.20/0.48         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (u1_struct_0 @ X4)))
% 0.20/0.48          | ~ (v3_pre_topc @ X3 @ X4)
% 0.20/0.48          | (r2_hidden @ X3 @ (u1_pre_topc @ X4))
% 0.20/0.48          | ~ (l1_pre_topc @ X4))),
% 0.20/0.48      inference('cnf', [status(esa)], [d5_pre_topc])).
% 0.20/0.48  thf('50', plain,
% 0.20/0.48      ((~ (l1_pre_topc @ sk_A)
% 0.20/0.48        | (r2_hidden @ 
% 0.20/0.48           (sk_D @ (u1_pre_topc @ sk_A) @ sk_B @ 
% 0.20/0.48            (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))) @ 
% 0.20/0.48           (u1_pre_topc @ sk_A))
% 0.20/0.48        | ~ (v3_pre_topc @ 
% 0.20/0.48             (sk_D @ (u1_pre_topc @ sk_A) @ sk_B @ 
% 0.20/0.48              (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))) @ 
% 0.20/0.48             sk_A))),
% 0.20/0.48      inference('sup-', [status(thm)], ['48', '49'])).
% 0.20/0.48  thf('51', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('52', plain,
% 0.20/0.48      (((r2_hidden @ 
% 0.20/0.48         (sk_D @ (u1_pre_topc @ sk_A) @ sk_B @ 
% 0.20/0.48          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))) @ 
% 0.20/0.48         (u1_pre_topc @ sk_A))
% 0.20/0.48        | ~ (v3_pre_topc @ 
% 0.20/0.48             (sk_D @ (u1_pre_topc @ sk_A) @ sk_B @ 
% 0.20/0.48              (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))) @ 
% 0.20/0.49             sk_A))),
% 0.20/0.49      inference('demod', [status(thm)], ['50', '51'])).
% 0.20/0.49  thf('53', plain,
% 0.20/0.49      ((m1_subset_1 @ sk_B @ 
% 0.20/0.49        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('54', plain,
% 0.20/0.49      (![X5 : $i]:
% 0.20/0.49         ((m1_subset_1 @ (u1_pre_topc @ X5) @ 
% 0.20/0.49           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X5))))
% 0.20/0.49          | ~ (l1_pre_topc @ X5))),
% 0.20/0.49      inference('cnf', [status(esa)], [dt_u1_pre_topc])).
% 0.20/0.49  thf('55', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.49         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.20/0.49          | (r1_tarski @ X2 @ X0)
% 0.20/0.49          | (r2_hidden @ (sk_D @ X0 @ X2 @ X1) @ X2)
% 0.20/0.49          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X1)))),
% 0.20/0.49      inference('cnf', [status(esa)], [t7_subset_1])).
% 0.20/0.49  thf('56', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]:
% 0.20/0.49         (~ (l1_pre_topc @ X0)
% 0.20/0.49          | ~ (m1_subset_1 @ X1 @ 
% 0.20/0.49               (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0))))
% 0.20/0.49          | (r2_hidden @ 
% 0.20/0.49             (sk_D @ (u1_pre_topc @ X0) @ X1 @ 
% 0.20/0.49              (k1_zfmisc_1 @ (u1_struct_0 @ X0))) @ 
% 0.20/0.49             X1)
% 0.20/0.49          | (r1_tarski @ X1 @ (u1_pre_topc @ X0)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['54', '55'])).
% 0.20/0.49  thf('57', plain,
% 0.20/0.49      (((r1_tarski @ sk_B @ (u1_pre_topc @ sk_A))
% 0.20/0.49        | (r2_hidden @ 
% 0.20/0.49           (sk_D @ (u1_pre_topc @ sk_A) @ sk_B @ 
% 0.20/0.49            (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))) @ 
% 0.20/0.49           sk_B)
% 0.20/0.49        | ~ (l1_pre_topc @ sk_A))),
% 0.20/0.49      inference('sup-', [status(thm)], ['53', '56'])).
% 0.20/0.49  thf('58', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('59', plain,
% 0.20/0.49      (((r1_tarski @ sk_B @ (u1_pre_topc @ sk_A))
% 0.20/0.49        | (r2_hidden @ 
% 0.20/0.49           (sk_D @ (u1_pre_topc @ sk_A) @ sk_B @ 
% 0.20/0.49            (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))) @ 
% 0.20/0.49           sk_B))),
% 0.20/0.49      inference('demod', [status(thm)], ['57', '58'])).
% 0.20/0.49  thf('60', plain,
% 0.20/0.49      ((m1_subset_1 @ 
% 0.20/0.49        (sk_D @ (u1_pre_topc @ sk_A) @ sk_B @ 
% 0.20/0.49         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))) @ 
% 0.20/0.49        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.49      inference('clc', [status(thm)], ['46', '47'])).
% 0.20/0.49  thf('61', plain,
% 0.20/0.49      ((m1_subset_1 @ sk_B @ 
% 0.20/0.49        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('62', plain,
% 0.20/0.49      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.20/0.49         (~ (m1_subset_1 @ X6 @ 
% 0.20/0.49             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X7))))
% 0.20/0.49          | ~ (v1_tops_2 @ X6 @ X7)
% 0.20/0.49          | ~ (r2_hidden @ X8 @ X6)
% 0.20/0.49          | (v3_pre_topc @ X8 @ X7)
% 0.20/0.49          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (u1_struct_0 @ X7)))
% 0.20/0.49          | ~ (l1_pre_topc @ X7))),
% 0.20/0.49      inference('cnf', [status(esa)], [d1_tops_2])).
% 0.20/0.49  thf('63', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (~ (l1_pre_topc @ sk_A)
% 0.20/0.49          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.49          | (v3_pre_topc @ X0 @ sk_A)
% 0.20/0.49          | ~ (r2_hidden @ X0 @ sk_B)
% 0.20/0.49          | ~ (v1_tops_2 @ sk_B @ sk_A))),
% 0.20/0.49      inference('sup-', [status(thm)], ['61', '62'])).
% 0.20/0.49  thf('64', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('65', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.49          | (v3_pre_topc @ X0 @ sk_A)
% 0.20/0.49          | ~ (r2_hidden @ X0 @ sk_B)
% 0.20/0.49          | ~ (v1_tops_2 @ sk_B @ sk_A))),
% 0.20/0.49      inference('demod', [status(thm)], ['63', '64'])).
% 0.20/0.49  thf('66', plain,
% 0.20/0.49      (((v1_tops_2 @ sk_B @ sk_A)) <= (((v1_tops_2 @ sk_B @ sk_A)))),
% 0.20/0.49      inference('split', [status(esa)], ['21'])).
% 0.20/0.49  thf('67', plain,
% 0.20/0.49      (((v1_tops_2 @ sk_B @ sk_A)) | 
% 0.20/0.49       ((r1_tarski @ sk_B @ (u1_pre_topc @ sk_A)))),
% 0.20/0.49      inference('split', [status(esa)], ['21'])).
% 0.20/0.49  thf('68', plain, (((v1_tops_2 @ sk_B @ sk_A))),
% 0.20/0.49      inference('sat_resolution*', [status(thm)], ['2', '37', '67'])).
% 0.20/0.49  thf('69', plain, ((v1_tops_2 @ sk_B @ sk_A)),
% 0.20/0.49      inference('simpl_trail', [status(thm)], ['66', '68'])).
% 0.20/0.49  thf('70', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.49          | (v3_pre_topc @ X0 @ sk_A)
% 0.20/0.49          | ~ (r2_hidden @ X0 @ sk_B))),
% 0.20/0.49      inference('demod', [status(thm)], ['65', '69'])).
% 0.20/0.49  thf('71', plain,
% 0.20/0.49      ((~ (r2_hidden @ 
% 0.20/0.49           (sk_D @ (u1_pre_topc @ sk_A) @ sk_B @ 
% 0.20/0.49            (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))) @ 
% 0.20/0.49           sk_B)
% 0.20/0.49        | (v3_pre_topc @ 
% 0.20/0.49           (sk_D @ (u1_pre_topc @ sk_A) @ sk_B @ 
% 0.20/0.49            (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))) @ 
% 0.20/0.49           sk_A))),
% 0.20/0.49      inference('sup-', [status(thm)], ['60', '70'])).
% 0.20/0.49  thf('72', plain,
% 0.20/0.49      (((r1_tarski @ sk_B @ (u1_pre_topc @ sk_A))
% 0.20/0.49        | (v3_pre_topc @ 
% 0.20/0.49           (sk_D @ (u1_pre_topc @ sk_A) @ sk_B @ 
% 0.20/0.49            (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))) @ 
% 0.20/0.49           sk_A))),
% 0.20/0.49      inference('sup-', [status(thm)], ['59', '71'])).
% 0.20/0.49  thf('73', plain, (~ (r1_tarski @ sk_B @ (u1_pre_topc @ sk_A))),
% 0.20/0.49      inference('simpl_trail', [status(thm)], ['1', '38'])).
% 0.20/0.49  thf('74', plain,
% 0.20/0.49      ((v3_pre_topc @ 
% 0.20/0.49        (sk_D @ (u1_pre_topc @ sk_A) @ sk_B @ 
% 0.20/0.49         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))) @ 
% 0.20/0.49        sk_A)),
% 0.20/0.49      inference('clc', [status(thm)], ['72', '73'])).
% 0.20/0.49  thf('75', plain,
% 0.20/0.49      ((r2_hidden @ 
% 0.20/0.49        (sk_D @ (u1_pre_topc @ sk_A) @ sk_B @ 
% 0.20/0.49         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))) @ 
% 0.20/0.49        (u1_pre_topc @ sk_A))),
% 0.20/0.49      inference('demod', [status(thm)], ['52', '74'])).
% 0.20/0.49  thf('76', plain,
% 0.20/0.49      (![X5 : $i]:
% 0.20/0.49         ((m1_subset_1 @ (u1_pre_topc @ X5) @ 
% 0.20/0.49           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X5))))
% 0.20/0.49          | ~ (l1_pre_topc @ X5))),
% 0.20/0.49      inference('cnf', [status(esa)], [dt_u1_pre_topc])).
% 0.20/0.49  thf('77', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.49         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.20/0.49          | (r1_tarski @ X2 @ X0)
% 0.20/0.49          | ~ (r2_hidden @ (sk_D @ X0 @ X2 @ X1) @ X0)
% 0.20/0.49          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X1)))),
% 0.20/0.49      inference('cnf', [status(esa)], [t7_subset_1])).
% 0.20/0.49  thf('78', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]:
% 0.20/0.49         (~ (l1_pre_topc @ X0)
% 0.20/0.49          | ~ (m1_subset_1 @ X1 @ 
% 0.20/0.49               (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0))))
% 0.20/0.49          | ~ (r2_hidden @ 
% 0.20/0.49               (sk_D @ (u1_pre_topc @ X0) @ X1 @ 
% 0.20/0.49                (k1_zfmisc_1 @ (u1_struct_0 @ X0))) @ 
% 0.20/0.49               (u1_pre_topc @ X0))
% 0.20/0.49          | (r1_tarski @ X1 @ (u1_pre_topc @ X0)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['76', '77'])).
% 0.20/0.49  thf('79', plain,
% 0.20/0.49      (((r1_tarski @ sk_B @ (u1_pre_topc @ sk_A))
% 0.20/0.49        | ~ (m1_subset_1 @ sk_B @ 
% 0.20/0.49             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.20/0.49        | ~ (l1_pre_topc @ sk_A))),
% 0.20/0.49      inference('sup-', [status(thm)], ['75', '78'])).
% 0.20/0.49  thf('80', plain,
% 0.20/0.49      ((m1_subset_1 @ sk_B @ 
% 0.20/0.49        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('81', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('82', plain, ((r1_tarski @ sk_B @ (u1_pre_topc @ sk_A))),
% 0.20/0.49      inference('demod', [status(thm)], ['79', '80', '81'])).
% 0.20/0.49  thf('83', plain, ($false), inference('demod', [status(thm)], ['39', '82'])).
% 0.20/0.49  
% 0.20/0.49  % SZS output end Refutation
% 0.20/0.49  
% 0.20/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
