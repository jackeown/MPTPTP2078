%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.t7kcpcaPUm

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:06:33 EST 2020

% Result     : Theorem 0.36s
% Output     : Refutation 0.36s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 357 expanded)
%              Number of leaves         :   20 ( 103 expanded)
%              Depth                    :   18
%              Number of atoms          :  933 (4090 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v1_tops_2_type,type,(
    v1_tops_2: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

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

thf('3',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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
    ! [X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) ) )
      | ( r2_hidden @ ( sk_C @ X12 @ X13 ) @ X12 )
      | ( v1_tops_2 @ X12 @ X13 )
      | ~ ( l1_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[d1_tops_2])).

thf('5',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v1_tops_2 @ sk_B @ sk_A )
    | ( r2_hidden @ ( sk_C @ sk_B @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( v1_tops_2 @ sk_B @ sk_A )
    | ( r2_hidden @ ( sk_C @ sk_B @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,
    ( ( r1_tarski @ sk_B @ ( u1_pre_topc @ sk_A ) )
    | ( v1_tops_2 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( r1_tarski @ sk_B @ ( u1_pre_topc @ sk_A ) )
   <= ( r1_tarski @ sk_B @ ( u1_pre_topc @ sk_A ) ) ),
    inference(split,[status(esa)],['8'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('10',plain,(
    ! [X6: $i,X8: $i] :
      ( ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X8 ) )
      | ~ ( r1_tarski @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('11',plain,
    ( ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_pre_topc @ sk_A ) ) )
   <= ( r1_tarski @ sk_B @ ( u1_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('13',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ X0 @ ( u1_pre_topc @ sk_A ) )
        | ~ ( r2_hidden @ X0 @ sk_B ) )
   <= ( r1_tarski @ sk_B @ ( u1_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,
    ( ( ( v1_tops_2 @ sk_B @ sk_A )
      | ( r2_hidden @ ( sk_C @ sk_B @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
   <= ( r1_tarski @ sk_B @ ( u1_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['7','13'])).

thf('15',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) ) )
      | ( m1_subset_1 @ ( sk_C @ X12 @ X13 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ( v1_tops_2 @ X12 @ X13 )
      | ~ ( l1_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[d1_tops_2])).

thf('17',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v1_tops_2 @ sk_B @ sk_A )
    | ( m1_subset_1 @ ( sk_C @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( v1_tops_2 @ sk_B @ sk_A )
    | ( m1_subset_1 @ ( sk_C @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf(d5_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v3_pre_topc @ B @ A )
          <=> ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) ) ) ) )).

thf('20',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ~ ( r2_hidden @ X9 @ ( u1_pre_topc @ X10 ) )
      | ( v3_pre_topc @ X9 @ X10 )
      | ~ ( l1_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[d5_pre_topc])).

thf('21',plain,
    ( ( v1_tops_2 @ sk_B @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v3_pre_topc @ ( sk_C @ sk_B @ sk_A ) @ sk_A )
    | ~ ( r2_hidden @ ( sk_C @ sk_B @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ( v1_tops_2 @ sk_B @ sk_A )
    | ( v3_pre_topc @ ( sk_C @ sk_B @ sk_A ) @ sk_A )
    | ~ ( r2_hidden @ ( sk_C @ sk_B @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) ) )
      | ~ ( v3_pre_topc @ ( sk_C @ X12 @ X13 ) @ X13 )
      | ( v1_tops_2 @ X12 @ X13 )
      | ~ ( l1_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[d1_tops_2])).

thf('26',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v1_tops_2 @ sk_B @ sk_A )
    | ~ ( v3_pre_topc @ ( sk_C @ sk_B @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( ( v1_tops_2 @ sk_B @ sk_A )
    | ~ ( v3_pre_topc @ ( sk_C @ sk_B @ sk_A ) @ sk_A ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,
    ( ~ ( r2_hidden @ ( sk_C @ sk_B @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
    | ( v1_tops_2 @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['23','28'])).

thf('30',plain,
    ( ( ( v1_tops_2 @ sk_B @ sk_A )
      | ( v1_tops_2 @ sk_B @ sk_A ) )
   <= ( r1_tarski @ sk_B @ ( u1_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['14','29'])).

thf('31',plain,
    ( ( v1_tops_2 @ sk_B @ sk_A )
   <= ( r1_tarski @ sk_B @ ( u1_pre_topc @ sk_A ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,
    ( ~ ( v1_tops_2 @ sk_B @ sk_A )
   <= ~ ( v1_tops_2 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('33',plain,
    ( ( v1_tops_2 @ sk_B @ sk_A )
    | ~ ( r1_tarski @ sk_B @ ( u1_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ~ ( r1_tarski @ sk_B @ ( u1_pre_topc @ sk_A ) ) ),
    inference('sat_resolution*',[status(thm)],['2','33'])).

thf('35',plain,(
    ~ ( r1_tarski @ sk_B @ ( u1_pre_topc @ sk_A ) ) ),
    inference(simpl_trail,[status(thm)],['1','34'])).

thf('36',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_u1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( m1_subset_1 @ ( u1_pre_topc @ A ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('37',plain,(
    ! [X11: $i] :
      ( ( m1_subset_1 @ ( u1_pre_topc @ X11 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) ) )
      | ~ ( l1_pre_topc @ X11 ) ) ),
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

thf('38',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( r1_tarski @ X5 @ X3 )
      | ( m1_subset_1 @ ( sk_D @ X3 @ X5 @ X4 ) @ X4 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t7_subset_1])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) )
      | ( m1_subset_1 @ ( sk_D @ ( u1_pre_topc @ X0 ) @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( r1_tarski @ X1 @ ( u1_pre_topc @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,
    ( ( r1_tarski @ sk_B @ ( u1_pre_topc @ sk_A ) )
    | ( m1_subset_1 @ ( sk_D @ ( u1_pre_topc @ sk_A ) @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['36','39'])).

thf('41',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( ( r1_tarski @ sk_B @ ( u1_pre_topc @ sk_A ) )
    | ( m1_subset_1 @ ( sk_D @ ( u1_pre_topc @ sk_A ) @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ~ ( v3_pre_topc @ X9 @ X10 )
      | ( r2_hidden @ X9 @ ( u1_pre_topc @ X10 ) )
      | ~ ( l1_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[d5_pre_topc])).

thf('44',plain,
    ( ( r1_tarski @ sk_B @ ( u1_pre_topc @ sk_A ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ( r2_hidden @ ( sk_D @ ( u1_pre_topc @ sk_A ) @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) @ ( u1_pre_topc @ sk_A ) )
    | ~ ( v3_pre_topc @ ( sk_D @ ( u1_pre_topc @ sk_A ) @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( ( r1_tarski @ sk_B @ ( u1_pre_topc @ sk_A ) )
    | ( r2_hidden @ ( sk_D @ ( u1_pre_topc @ sk_A ) @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) @ ( u1_pre_topc @ sk_A ) )
    | ~ ( v3_pre_topc @ ( sk_D @ ( u1_pre_topc @ sk_A ) @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) @ sk_A ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,
    ( ( r1_tarski @ sk_B @ ( u1_pre_topc @ sk_A ) )
    | ( m1_subset_1 @ ( sk_D @ ( u1_pre_topc @ sk_A ) @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('48',plain,
    ( ( v1_tops_2 @ sk_B @ sk_A )
   <= ( v1_tops_2 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['8'])).

thf('49',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) ) )
      | ~ ( v1_tops_2 @ X12 @ X13 )
      | ~ ( r2_hidden @ X14 @ X12 )
      | ( v3_pre_topc @ X14 @ X13 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ~ ( l1_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[d1_tops_2])).

thf('51',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v3_pre_topc @ X0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ sk_B )
      | ~ ( v1_tops_2 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v3_pre_topc @ X0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ sk_B )
      | ~ ( v1_tops_2 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ sk_B )
        | ( v3_pre_topc @ X0 @ sk_A )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ( v1_tops_2 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['48','53'])).

thf('55',plain,
    ( ( ( r1_tarski @ sk_B @ ( u1_pre_topc @ sk_A ) )
      | ( v3_pre_topc @ ( sk_D @ ( u1_pre_topc @ sk_A ) @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) @ sk_A )
      | ~ ( r2_hidden @ ( sk_D @ ( u1_pre_topc @ sk_A ) @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) @ sk_B ) )
   <= ( v1_tops_2 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['47','54'])).

thf('56',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    ! [X11: $i] :
      ( ( m1_subset_1 @ ( u1_pre_topc @ X11 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) ) )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_pre_topc])).

thf('58',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( r1_tarski @ X5 @ X3 )
      | ( r2_hidden @ ( sk_D @ X3 @ X5 @ X4 ) @ X5 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t7_subset_1])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) )
      | ( r2_hidden @ ( sk_D @ ( u1_pre_topc @ X0 ) @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) @ X1 )
      | ( r1_tarski @ X1 @ ( u1_pre_topc @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,
    ( ( r1_tarski @ sk_B @ ( u1_pre_topc @ sk_A ) )
    | ( r2_hidden @ ( sk_D @ ( u1_pre_topc @ sk_A ) @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) @ sk_B )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['56','59'])).

thf('61',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,
    ( ( r1_tarski @ sk_B @ ( u1_pre_topc @ sk_A ) )
    | ( r2_hidden @ ( sk_D @ ( u1_pre_topc @ sk_A ) @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) @ sk_B ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,
    ( ( ( v3_pre_topc @ ( sk_D @ ( u1_pre_topc @ sk_A ) @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) @ sk_A )
      | ( r1_tarski @ sk_B @ ( u1_pre_topc @ sk_A ) ) )
   <= ( v1_tops_2 @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['55','62'])).

thf('64',plain,
    ( ( v1_tops_2 @ sk_B @ sk_A )
    | ( r1_tarski @ sk_B @ ( u1_pre_topc @ sk_A ) ) ),
    inference(split,[status(esa)],['8'])).

thf('65',plain,(
    v1_tops_2 @ sk_B @ sk_A ),
    inference('sat_resolution*',[status(thm)],['2','33','64'])).

thf('66',plain,
    ( ( v3_pre_topc @ ( sk_D @ ( u1_pre_topc @ sk_A ) @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) @ sk_A )
    | ( r1_tarski @ sk_B @ ( u1_pre_topc @ sk_A ) ) ),
    inference(simpl_trail,[status(thm)],['63','65'])).

thf('67',plain,(
    ~ ( r1_tarski @ sk_B @ ( u1_pre_topc @ sk_A ) ) ),
    inference(simpl_trail,[status(thm)],['1','34'])).

thf('68',plain,(
    v3_pre_topc @ ( sk_D @ ( u1_pre_topc @ sk_A ) @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) @ sk_A ),
    inference(clc,[status(thm)],['66','67'])).

thf('69',plain,
    ( ( r1_tarski @ sk_B @ ( u1_pre_topc @ sk_A ) )
    | ( r2_hidden @ ( sk_D @ ( u1_pre_topc @ sk_A ) @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) @ ( u1_pre_topc @ sk_A ) ) ),
    inference(demod,[status(thm)],['46','68'])).

thf('70',plain,(
    ~ ( r1_tarski @ sk_B @ ( u1_pre_topc @ sk_A ) ) ),
    inference(simpl_trail,[status(thm)],['1','34'])).

thf('71',plain,(
    r2_hidden @ ( sk_D @ ( u1_pre_topc @ sk_A ) @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) @ ( u1_pre_topc @ sk_A ) ),
    inference(clc,[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X11: $i] :
      ( ( m1_subset_1 @ ( u1_pre_topc @ X11 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) ) )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_pre_topc])).

thf('73',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( r1_tarski @ X5 @ X3 )
      | ~ ( r2_hidden @ ( sk_D @ X3 @ X5 @ X4 ) @ X3 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t7_subset_1])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( r2_hidden @ ( sk_D @ ( u1_pre_topc @ X0 ) @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) @ ( u1_pre_topc @ X0 ) )
      | ( r1_tarski @ X1 @ ( u1_pre_topc @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,
    ( ( r1_tarski @ sk_B @ ( u1_pre_topc @ sk_A ) )
    | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['71','74'])).

thf('76',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    r1_tarski @ sk_B @ ( u1_pre_topc @ sk_A ) ),
    inference(demod,[status(thm)],['75','76','77'])).

thf('79',plain,(
    $false ),
    inference(demod,[status(thm)],['35','78'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.t7kcpcaPUm
% 0.14/0.35  % Computer   : n019.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 14:08:53 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.36/0.53  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.36/0.53  % Solved by: fo/fo7.sh
% 0.36/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.36/0.53  % done 118 iterations in 0.071s
% 0.36/0.53  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.36/0.53  % SZS output start Refutation
% 0.36/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.36/0.53  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.36/0.53  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.36/0.53  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 0.36/0.53  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.36/0.53  thf(v1_tops_2_type, type, v1_tops_2: $i > $i > $o).
% 0.36/0.53  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.36/0.53  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.36/0.53  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.36/0.53  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.36/0.53  thf(sk_B_type, type, sk_B: $i).
% 0.36/0.53  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.36/0.53  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.36/0.53  thf(t78_tops_2, conjecture,
% 0.36/0.53    (![A:$i]:
% 0.36/0.53     ( ( l1_pre_topc @ A ) =>
% 0.36/0.53       ( ![B:$i]:
% 0.36/0.53         ( ( m1_subset_1 @
% 0.36/0.53             B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.36/0.53           ( ( v1_tops_2 @ B @ A ) <=> ( r1_tarski @ B @ ( u1_pre_topc @ A ) ) ) ) ) ))).
% 0.36/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.36/0.53    (~( ![A:$i]:
% 0.36/0.53        ( ( l1_pre_topc @ A ) =>
% 0.36/0.53          ( ![B:$i]:
% 0.36/0.53            ( ( m1_subset_1 @
% 0.36/0.53                B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.36/0.53              ( ( v1_tops_2 @ B @ A ) <=>
% 0.36/0.53                ( r1_tarski @ B @ ( u1_pre_topc @ A ) ) ) ) ) ) )),
% 0.36/0.53    inference('cnf.neg', [status(esa)], [t78_tops_2])).
% 0.36/0.53  thf('0', plain,
% 0.36/0.53      ((~ (r1_tarski @ sk_B @ (u1_pre_topc @ sk_A))
% 0.36/0.53        | ~ (v1_tops_2 @ sk_B @ sk_A))),
% 0.36/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.53  thf('1', plain,
% 0.36/0.53      ((~ (r1_tarski @ sk_B @ (u1_pre_topc @ sk_A)))
% 0.36/0.53         <= (~ ((r1_tarski @ sk_B @ (u1_pre_topc @ sk_A))))),
% 0.36/0.53      inference('split', [status(esa)], ['0'])).
% 0.36/0.53  thf('2', plain,
% 0.36/0.53      (~ ((r1_tarski @ sk_B @ (u1_pre_topc @ sk_A))) | 
% 0.36/0.53       ~ ((v1_tops_2 @ sk_B @ sk_A))),
% 0.36/0.53      inference('split', [status(esa)], ['0'])).
% 0.36/0.53  thf('3', plain,
% 0.36/0.53      ((m1_subset_1 @ sk_B @ 
% 0.36/0.53        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.36/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.53  thf(d1_tops_2, axiom,
% 0.36/0.53    (![A:$i]:
% 0.36/0.53     ( ( l1_pre_topc @ A ) =>
% 0.36/0.53       ( ![B:$i]:
% 0.36/0.53         ( ( m1_subset_1 @
% 0.36/0.53             B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.36/0.53           ( ( v1_tops_2 @ B @ A ) <=>
% 0.36/0.53             ( ![C:$i]:
% 0.36/0.53               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.36/0.53                 ( ( r2_hidden @ C @ B ) => ( v3_pre_topc @ C @ A ) ) ) ) ) ) ) ))).
% 0.36/0.53  thf('4', plain,
% 0.36/0.53      (![X12 : $i, X13 : $i]:
% 0.36/0.53         (~ (m1_subset_1 @ X12 @ 
% 0.36/0.53             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13))))
% 0.36/0.53          | (r2_hidden @ (sk_C @ X12 @ X13) @ X12)
% 0.36/0.53          | (v1_tops_2 @ X12 @ X13)
% 0.36/0.53          | ~ (l1_pre_topc @ X13))),
% 0.36/0.53      inference('cnf', [status(esa)], [d1_tops_2])).
% 0.36/0.53  thf('5', plain,
% 0.36/0.53      ((~ (l1_pre_topc @ sk_A)
% 0.36/0.53        | (v1_tops_2 @ sk_B @ sk_A)
% 0.36/0.53        | (r2_hidden @ (sk_C @ sk_B @ sk_A) @ sk_B))),
% 0.36/0.53      inference('sup-', [status(thm)], ['3', '4'])).
% 0.36/0.53  thf('6', plain, ((l1_pre_topc @ sk_A)),
% 0.36/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.53  thf('7', plain,
% 0.36/0.53      (((v1_tops_2 @ sk_B @ sk_A) | (r2_hidden @ (sk_C @ sk_B @ sk_A) @ sk_B))),
% 0.36/0.53      inference('demod', [status(thm)], ['5', '6'])).
% 0.36/0.53  thf('8', plain,
% 0.36/0.53      (((r1_tarski @ sk_B @ (u1_pre_topc @ sk_A)) | (v1_tops_2 @ sk_B @ sk_A))),
% 0.36/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.53  thf('9', plain,
% 0.36/0.53      (((r1_tarski @ sk_B @ (u1_pre_topc @ sk_A)))
% 0.36/0.53         <= (((r1_tarski @ sk_B @ (u1_pre_topc @ sk_A))))),
% 0.36/0.53      inference('split', [status(esa)], ['8'])).
% 0.36/0.53  thf(t3_subset, axiom,
% 0.36/0.53    (![A:$i,B:$i]:
% 0.36/0.53     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.36/0.53  thf('10', plain,
% 0.36/0.53      (![X6 : $i, X8 : $i]:
% 0.36/0.53         ((m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X8)) | ~ (r1_tarski @ X6 @ X8))),
% 0.36/0.53      inference('cnf', [status(esa)], [t3_subset])).
% 0.36/0.53  thf('11', plain,
% 0.36/0.53      (((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_pre_topc @ sk_A))))
% 0.36/0.53         <= (((r1_tarski @ sk_B @ (u1_pre_topc @ sk_A))))),
% 0.36/0.53      inference('sup-', [status(thm)], ['9', '10'])).
% 0.36/0.53  thf(l3_subset_1, axiom,
% 0.36/0.53    (![A:$i,B:$i]:
% 0.36/0.53     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.36/0.53       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 0.36/0.53  thf('12', plain,
% 0.36/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.36/0.53         (~ (r2_hidden @ X0 @ X1)
% 0.36/0.53          | (r2_hidden @ X0 @ X2)
% 0.36/0.53          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X2)))),
% 0.36/0.53      inference('cnf', [status(esa)], [l3_subset_1])).
% 0.36/0.53  thf('13', plain,
% 0.36/0.53      ((![X0 : $i]:
% 0.36/0.53          ((r2_hidden @ X0 @ (u1_pre_topc @ sk_A)) | ~ (r2_hidden @ X0 @ sk_B)))
% 0.36/0.53         <= (((r1_tarski @ sk_B @ (u1_pre_topc @ sk_A))))),
% 0.36/0.53      inference('sup-', [status(thm)], ['11', '12'])).
% 0.36/0.53  thf('14', plain,
% 0.36/0.53      ((((v1_tops_2 @ sk_B @ sk_A)
% 0.36/0.53         | (r2_hidden @ (sk_C @ sk_B @ sk_A) @ (u1_pre_topc @ sk_A))))
% 0.36/0.53         <= (((r1_tarski @ sk_B @ (u1_pre_topc @ sk_A))))),
% 0.36/0.53      inference('sup-', [status(thm)], ['7', '13'])).
% 0.36/0.53  thf('15', plain,
% 0.36/0.53      ((m1_subset_1 @ sk_B @ 
% 0.36/0.53        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.36/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.53  thf('16', plain,
% 0.36/0.53      (![X12 : $i, X13 : $i]:
% 0.36/0.53         (~ (m1_subset_1 @ X12 @ 
% 0.36/0.53             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13))))
% 0.36/0.53          | (m1_subset_1 @ (sk_C @ X12 @ X13) @ 
% 0.36/0.53             (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.36/0.53          | (v1_tops_2 @ X12 @ X13)
% 0.36/0.53          | ~ (l1_pre_topc @ X13))),
% 0.36/0.53      inference('cnf', [status(esa)], [d1_tops_2])).
% 0.36/0.53  thf('17', plain,
% 0.36/0.53      ((~ (l1_pre_topc @ sk_A)
% 0.36/0.53        | (v1_tops_2 @ sk_B @ sk_A)
% 0.36/0.53        | (m1_subset_1 @ (sk_C @ sk_B @ sk_A) @ 
% 0.36/0.53           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.36/0.53      inference('sup-', [status(thm)], ['15', '16'])).
% 0.36/0.53  thf('18', plain, ((l1_pre_topc @ sk_A)),
% 0.36/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.53  thf('19', plain,
% 0.36/0.53      (((v1_tops_2 @ sk_B @ sk_A)
% 0.36/0.53        | (m1_subset_1 @ (sk_C @ sk_B @ sk_A) @ 
% 0.36/0.53           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.36/0.53      inference('demod', [status(thm)], ['17', '18'])).
% 0.36/0.53  thf(d5_pre_topc, axiom,
% 0.36/0.53    (![A:$i]:
% 0.36/0.53     ( ( l1_pre_topc @ A ) =>
% 0.36/0.53       ( ![B:$i]:
% 0.36/0.53         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.36/0.53           ( ( v3_pre_topc @ B @ A ) <=>
% 0.36/0.53             ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) ) ) ) ))).
% 0.36/0.53  thf('20', plain,
% 0.36/0.53      (![X9 : $i, X10 : $i]:
% 0.36/0.53         (~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 0.36/0.53          | ~ (r2_hidden @ X9 @ (u1_pre_topc @ X10))
% 0.36/0.53          | (v3_pre_topc @ X9 @ X10)
% 0.36/0.53          | ~ (l1_pre_topc @ X10))),
% 0.36/0.53      inference('cnf', [status(esa)], [d5_pre_topc])).
% 0.36/0.53  thf('21', plain,
% 0.36/0.53      (((v1_tops_2 @ sk_B @ sk_A)
% 0.36/0.53        | ~ (l1_pre_topc @ sk_A)
% 0.36/0.53        | (v3_pre_topc @ (sk_C @ sk_B @ sk_A) @ sk_A)
% 0.36/0.53        | ~ (r2_hidden @ (sk_C @ sk_B @ sk_A) @ (u1_pre_topc @ sk_A)))),
% 0.36/0.53      inference('sup-', [status(thm)], ['19', '20'])).
% 0.36/0.53  thf('22', plain, ((l1_pre_topc @ sk_A)),
% 0.36/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.53  thf('23', plain,
% 0.36/0.53      (((v1_tops_2 @ sk_B @ sk_A)
% 0.36/0.53        | (v3_pre_topc @ (sk_C @ sk_B @ sk_A) @ sk_A)
% 0.36/0.53        | ~ (r2_hidden @ (sk_C @ sk_B @ sk_A) @ (u1_pre_topc @ sk_A)))),
% 0.36/0.53      inference('demod', [status(thm)], ['21', '22'])).
% 0.36/0.53  thf('24', plain,
% 0.36/0.53      ((m1_subset_1 @ sk_B @ 
% 0.36/0.53        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.36/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.53  thf('25', plain,
% 0.36/0.53      (![X12 : $i, X13 : $i]:
% 0.36/0.53         (~ (m1_subset_1 @ X12 @ 
% 0.36/0.53             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13))))
% 0.36/0.53          | ~ (v3_pre_topc @ (sk_C @ X12 @ X13) @ X13)
% 0.36/0.53          | (v1_tops_2 @ X12 @ X13)
% 0.36/0.53          | ~ (l1_pre_topc @ X13))),
% 0.36/0.53      inference('cnf', [status(esa)], [d1_tops_2])).
% 0.36/0.53  thf('26', plain,
% 0.36/0.53      ((~ (l1_pre_topc @ sk_A)
% 0.36/0.53        | (v1_tops_2 @ sk_B @ sk_A)
% 0.36/0.53        | ~ (v3_pre_topc @ (sk_C @ sk_B @ sk_A) @ sk_A))),
% 0.36/0.53      inference('sup-', [status(thm)], ['24', '25'])).
% 0.36/0.53  thf('27', plain, ((l1_pre_topc @ sk_A)),
% 0.36/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.53  thf('28', plain,
% 0.36/0.53      (((v1_tops_2 @ sk_B @ sk_A)
% 0.36/0.53        | ~ (v3_pre_topc @ (sk_C @ sk_B @ sk_A) @ sk_A))),
% 0.36/0.53      inference('demod', [status(thm)], ['26', '27'])).
% 0.36/0.53  thf('29', plain,
% 0.36/0.53      ((~ (r2_hidden @ (sk_C @ sk_B @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.36/0.53        | (v1_tops_2 @ sk_B @ sk_A))),
% 0.36/0.53      inference('clc', [status(thm)], ['23', '28'])).
% 0.36/0.53  thf('30', plain,
% 0.36/0.53      ((((v1_tops_2 @ sk_B @ sk_A) | (v1_tops_2 @ sk_B @ sk_A)))
% 0.36/0.53         <= (((r1_tarski @ sk_B @ (u1_pre_topc @ sk_A))))),
% 0.36/0.53      inference('sup-', [status(thm)], ['14', '29'])).
% 0.36/0.53  thf('31', plain,
% 0.36/0.53      (((v1_tops_2 @ sk_B @ sk_A))
% 0.36/0.53         <= (((r1_tarski @ sk_B @ (u1_pre_topc @ sk_A))))),
% 0.36/0.53      inference('simplify', [status(thm)], ['30'])).
% 0.36/0.53  thf('32', plain,
% 0.36/0.53      ((~ (v1_tops_2 @ sk_B @ sk_A)) <= (~ ((v1_tops_2 @ sk_B @ sk_A)))),
% 0.36/0.53      inference('split', [status(esa)], ['0'])).
% 0.36/0.53  thf('33', plain,
% 0.36/0.53      (((v1_tops_2 @ sk_B @ sk_A)) | 
% 0.36/0.53       ~ ((r1_tarski @ sk_B @ (u1_pre_topc @ sk_A)))),
% 0.36/0.53      inference('sup-', [status(thm)], ['31', '32'])).
% 0.36/0.53  thf('34', plain, (~ ((r1_tarski @ sk_B @ (u1_pre_topc @ sk_A)))),
% 0.36/0.53      inference('sat_resolution*', [status(thm)], ['2', '33'])).
% 0.36/0.53  thf('35', plain, (~ (r1_tarski @ sk_B @ (u1_pre_topc @ sk_A))),
% 0.36/0.53      inference('simpl_trail', [status(thm)], ['1', '34'])).
% 0.36/0.53  thf('36', plain,
% 0.36/0.53      ((m1_subset_1 @ sk_B @ 
% 0.36/0.53        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf(dt_u1_pre_topc, axiom,
% 0.36/0.54    (![A:$i]:
% 0.36/0.54     ( ( l1_pre_topc @ A ) =>
% 0.36/0.54       ( m1_subset_1 @
% 0.36/0.54         ( u1_pre_topc @ A ) @ 
% 0.36/0.54         ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ))).
% 0.36/0.54  thf('37', plain,
% 0.36/0.54      (![X11 : $i]:
% 0.36/0.54         ((m1_subset_1 @ (u1_pre_topc @ X11) @ 
% 0.36/0.54           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11))))
% 0.36/0.54          | ~ (l1_pre_topc @ X11))),
% 0.36/0.54      inference('cnf', [status(esa)], [dt_u1_pre_topc])).
% 0.36/0.54  thf(t7_subset_1, axiom,
% 0.36/0.54    (![A:$i,B:$i]:
% 0.36/0.54     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.36/0.54       ( ![C:$i]:
% 0.36/0.54         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.36/0.54           ( ( ![D:$i]:
% 0.36/0.54               ( ( m1_subset_1 @ D @ A ) =>
% 0.36/0.54                 ( ( r2_hidden @ D @ B ) => ( r2_hidden @ D @ C ) ) ) ) =>
% 0.36/0.54             ( r1_tarski @ B @ C ) ) ) ) ))).
% 0.36/0.54  thf('38', plain,
% 0.36/0.54      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.36/0.54         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 0.36/0.54          | (r1_tarski @ X5 @ X3)
% 0.36/0.54          | (m1_subset_1 @ (sk_D @ X3 @ X5 @ X4) @ X4)
% 0.36/0.54          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X4)))),
% 0.36/0.54      inference('cnf', [status(esa)], [t7_subset_1])).
% 0.36/0.54  thf('39', plain,
% 0.36/0.54      (![X0 : $i, X1 : $i]:
% 0.36/0.54         (~ (l1_pre_topc @ X0)
% 0.36/0.54          | ~ (m1_subset_1 @ X1 @ 
% 0.36/0.54               (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0))))
% 0.36/0.54          | (m1_subset_1 @ 
% 0.36/0.54             (sk_D @ (u1_pre_topc @ X0) @ X1 @ 
% 0.36/0.54              (k1_zfmisc_1 @ (u1_struct_0 @ X0))) @ 
% 0.36/0.54             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.36/0.54          | (r1_tarski @ X1 @ (u1_pre_topc @ X0)))),
% 0.36/0.54      inference('sup-', [status(thm)], ['37', '38'])).
% 0.36/0.54  thf('40', plain,
% 0.36/0.54      (((r1_tarski @ sk_B @ (u1_pre_topc @ sk_A))
% 0.36/0.54        | (m1_subset_1 @ 
% 0.36/0.54           (sk_D @ (u1_pre_topc @ sk_A) @ sk_B @ 
% 0.36/0.54            (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))) @ 
% 0.36/0.54           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.36/0.54        | ~ (l1_pre_topc @ sk_A))),
% 0.36/0.54      inference('sup-', [status(thm)], ['36', '39'])).
% 0.36/0.54  thf('41', plain, ((l1_pre_topc @ sk_A)),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('42', plain,
% 0.36/0.54      (((r1_tarski @ sk_B @ (u1_pre_topc @ sk_A))
% 0.36/0.54        | (m1_subset_1 @ 
% 0.36/0.54           (sk_D @ (u1_pre_topc @ sk_A) @ sk_B @ 
% 0.36/0.54            (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))) @ 
% 0.36/0.54           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.36/0.54      inference('demod', [status(thm)], ['40', '41'])).
% 0.36/0.54  thf('43', plain,
% 0.36/0.54      (![X9 : $i, X10 : $i]:
% 0.36/0.54         (~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 0.36/0.54          | ~ (v3_pre_topc @ X9 @ X10)
% 0.36/0.54          | (r2_hidden @ X9 @ (u1_pre_topc @ X10))
% 0.36/0.54          | ~ (l1_pre_topc @ X10))),
% 0.36/0.54      inference('cnf', [status(esa)], [d5_pre_topc])).
% 0.36/0.54  thf('44', plain,
% 0.36/0.54      (((r1_tarski @ sk_B @ (u1_pre_topc @ sk_A))
% 0.36/0.54        | ~ (l1_pre_topc @ sk_A)
% 0.36/0.54        | (r2_hidden @ 
% 0.36/0.54           (sk_D @ (u1_pre_topc @ sk_A) @ sk_B @ 
% 0.36/0.54            (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))) @ 
% 0.36/0.54           (u1_pre_topc @ sk_A))
% 0.36/0.54        | ~ (v3_pre_topc @ 
% 0.36/0.54             (sk_D @ (u1_pre_topc @ sk_A) @ sk_B @ 
% 0.36/0.54              (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))) @ 
% 0.36/0.54             sk_A))),
% 0.36/0.54      inference('sup-', [status(thm)], ['42', '43'])).
% 0.36/0.54  thf('45', plain, ((l1_pre_topc @ sk_A)),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('46', plain,
% 0.36/0.54      (((r1_tarski @ sk_B @ (u1_pre_topc @ sk_A))
% 0.36/0.54        | (r2_hidden @ 
% 0.36/0.54           (sk_D @ (u1_pre_topc @ sk_A) @ sk_B @ 
% 0.36/0.54            (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))) @ 
% 0.36/0.54           (u1_pre_topc @ sk_A))
% 0.36/0.54        | ~ (v3_pre_topc @ 
% 0.36/0.54             (sk_D @ (u1_pre_topc @ sk_A) @ sk_B @ 
% 0.36/0.54              (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))) @ 
% 0.36/0.54             sk_A))),
% 0.36/0.54      inference('demod', [status(thm)], ['44', '45'])).
% 0.36/0.54  thf('47', plain,
% 0.36/0.54      (((r1_tarski @ sk_B @ (u1_pre_topc @ sk_A))
% 0.36/0.54        | (m1_subset_1 @ 
% 0.36/0.54           (sk_D @ (u1_pre_topc @ sk_A) @ sk_B @ 
% 0.36/0.54            (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))) @ 
% 0.36/0.54           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.36/0.54      inference('demod', [status(thm)], ['40', '41'])).
% 0.36/0.54  thf('48', plain,
% 0.36/0.54      (((v1_tops_2 @ sk_B @ sk_A)) <= (((v1_tops_2 @ sk_B @ sk_A)))),
% 0.36/0.54      inference('split', [status(esa)], ['8'])).
% 0.36/0.54  thf('49', plain,
% 0.36/0.54      ((m1_subset_1 @ sk_B @ 
% 0.36/0.54        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('50', plain,
% 0.36/0.54      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.36/0.54         (~ (m1_subset_1 @ X12 @ 
% 0.36/0.54             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13))))
% 0.36/0.54          | ~ (v1_tops_2 @ X12 @ X13)
% 0.36/0.54          | ~ (r2_hidden @ X14 @ X12)
% 0.36/0.54          | (v3_pre_topc @ X14 @ X13)
% 0.36/0.54          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.36/0.54          | ~ (l1_pre_topc @ X13))),
% 0.36/0.54      inference('cnf', [status(esa)], [d1_tops_2])).
% 0.36/0.54  thf('51', plain,
% 0.36/0.54      (![X0 : $i]:
% 0.36/0.54         (~ (l1_pre_topc @ sk_A)
% 0.36/0.54          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.36/0.54          | (v3_pre_topc @ X0 @ sk_A)
% 0.36/0.54          | ~ (r2_hidden @ X0 @ sk_B)
% 0.36/0.54          | ~ (v1_tops_2 @ sk_B @ sk_A))),
% 0.36/0.54      inference('sup-', [status(thm)], ['49', '50'])).
% 0.36/0.54  thf('52', plain, ((l1_pre_topc @ sk_A)),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('53', plain,
% 0.36/0.54      (![X0 : $i]:
% 0.36/0.54         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.36/0.54          | (v3_pre_topc @ X0 @ sk_A)
% 0.36/0.54          | ~ (r2_hidden @ X0 @ sk_B)
% 0.36/0.54          | ~ (v1_tops_2 @ sk_B @ sk_A))),
% 0.36/0.54      inference('demod', [status(thm)], ['51', '52'])).
% 0.36/0.54  thf('54', plain,
% 0.36/0.54      ((![X0 : $i]:
% 0.36/0.54          (~ (r2_hidden @ X0 @ sk_B)
% 0.36/0.54           | (v3_pre_topc @ X0 @ sk_A)
% 0.36/0.54           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))
% 0.36/0.54         <= (((v1_tops_2 @ sk_B @ sk_A)))),
% 0.36/0.54      inference('sup-', [status(thm)], ['48', '53'])).
% 0.36/0.54  thf('55', plain,
% 0.36/0.54      ((((r1_tarski @ sk_B @ (u1_pre_topc @ sk_A))
% 0.36/0.54         | (v3_pre_topc @ 
% 0.36/0.54            (sk_D @ (u1_pre_topc @ sk_A) @ sk_B @ 
% 0.36/0.54             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))) @ 
% 0.36/0.54            sk_A)
% 0.36/0.54         | ~ (r2_hidden @ 
% 0.36/0.54              (sk_D @ (u1_pre_topc @ sk_A) @ sk_B @ 
% 0.36/0.54               (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))) @ 
% 0.36/0.54              sk_B)))
% 0.36/0.54         <= (((v1_tops_2 @ sk_B @ sk_A)))),
% 0.36/0.54      inference('sup-', [status(thm)], ['47', '54'])).
% 0.36/0.54  thf('56', plain,
% 0.36/0.54      ((m1_subset_1 @ sk_B @ 
% 0.36/0.54        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('57', plain,
% 0.36/0.54      (![X11 : $i]:
% 0.36/0.54         ((m1_subset_1 @ (u1_pre_topc @ X11) @ 
% 0.36/0.54           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11))))
% 0.36/0.54          | ~ (l1_pre_topc @ X11))),
% 0.36/0.54      inference('cnf', [status(esa)], [dt_u1_pre_topc])).
% 0.36/0.54  thf('58', plain,
% 0.36/0.54      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.36/0.54         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 0.36/0.54          | (r1_tarski @ X5 @ X3)
% 0.36/0.54          | (r2_hidden @ (sk_D @ X3 @ X5 @ X4) @ X5)
% 0.36/0.54          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X4)))),
% 0.36/0.54      inference('cnf', [status(esa)], [t7_subset_1])).
% 0.36/0.54  thf('59', plain,
% 0.36/0.54      (![X0 : $i, X1 : $i]:
% 0.36/0.54         (~ (l1_pre_topc @ X0)
% 0.36/0.54          | ~ (m1_subset_1 @ X1 @ 
% 0.36/0.54               (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0))))
% 0.36/0.54          | (r2_hidden @ 
% 0.36/0.54             (sk_D @ (u1_pre_topc @ X0) @ X1 @ 
% 0.36/0.54              (k1_zfmisc_1 @ (u1_struct_0 @ X0))) @ 
% 0.36/0.54             X1)
% 0.36/0.54          | (r1_tarski @ X1 @ (u1_pre_topc @ X0)))),
% 0.36/0.54      inference('sup-', [status(thm)], ['57', '58'])).
% 0.36/0.54  thf('60', plain,
% 0.36/0.54      (((r1_tarski @ sk_B @ (u1_pre_topc @ sk_A))
% 0.36/0.54        | (r2_hidden @ 
% 0.36/0.54           (sk_D @ (u1_pre_topc @ sk_A) @ sk_B @ 
% 0.36/0.54            (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))) @ 
% 0.36/0.54           sk_B)
% 0.36/0.54        | ~ (l1_pre_topc @ sk_A))),
% 0.36/0.54      inference('sup-', [status(thm)], ['56', '59'])).
% 0.36/0.54  thf('61', plain, ((l1_pre_topc @ sk_A)),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('62', plain,
% 0.36/0.54      (((r1_tarski @ sk_B @ (u1_pre_topc @ sk_A))
% 0.36/0.54        | (r2_hidden @ 
% 0.36/0.54           (sk_D @ (u1_pre_topc @ sk_A) @ sk_B @ 
% 0.36/0.54            (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))) @ 
% 0.36/0.54           sk_B))),
% 0.36/0.54      inference('demod', [status(thm)], ['60', '61'])).
% 0.36/0.54  thf('63', plain,
% 0.36/0.54      ((((v3_pre_topc @ 
% 0.36/0.54          (sk_D @ (u1_pre_topc @ sk_A) @ sk_B @ 
% 0.36/0.54           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))) @ 
% 0.36/0.54          sk_A)
% 0.36/0.54         | (r1_tarski @ sk_B @ (u1_pre_topc @ sk_A))))
% 0.36/0.54         <= (((v1_tops_2 @ sk_B @ sk_A)))),
% 0.36/0.54      inference('clc', [status(thm)], ['55', '62'])).
% 0.36/0.54  thf('64', plain,
% 0.36/0.54      (((v1_tops_2 @ sk_B @ sk_A)) | 
% 0.36/0.54       ((r1_tarski @ sk_B @ (u1_pre_topc @ sk_A)))),
% 0.36/0.54      inference('split', [status(esa)], ['8'])).
% 0.36/0.54  thf('65', plain, (((v1_tops_2 @ sk_B @ sk_A))),
% 0.36/0.54      inference('sat_resolution*', [status(thm)], ['2', '33', '64'])).
% 0.36/0.54  thf('66', plain,
% 0.36/0.54      (((v3_pre_topc @ 
% 0.36/0.54         (sk_D @ (u1_pre_topc @ sk_A) @ sk_B @ 
% 0.36/0.54          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))) @ 
% 0.36/0.54         sk_A)
% 0.36/0.54        | (r1_tarski @ sk_B @ (u1_pre_topc @ sk_A)))),
% 0.36/0.54      inference('simpl_trail', [status(thm)], ['63', '65'])).
% 0.36/0.54  thf('67', plain, (~ (r1_tarski @ sk_B @ (u1_pre_topc @ sk_A))),
% 0.36/0.54      inference('simpl_trail', [status(thm)], ['1', '34'])).
% 0.36/0.54  thf('68', plain,
% 0.36/0.54      ((v3_pre_topc @ 
% 0.36/0.54        (sk_D @ (u1_pre_topc @ sk_A) @ sk_B @ 
% 0.36/0.54         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))) @ 
% 0.36/0.54        sk_A)),
% 0.36/0.54      inference('clc', [status(thm)], ['66', '67'])).
% 0.36/0.54  thf('69', plain,
% 0.36/0.54      (((r1_tarski @ sk_B @ (u1_pre_topc @ sk_A))
% 0.36/0.54        | (r2_hidden @ 
% 0.36/0.54           (sk_D @ (u1_pre_topc @ sk_A) @ sk_B @ 
% 0.36/0.54            (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))) @ 
% 0.36/0.54           (u1_pre_topc @ sk_A)))),
% 0.36/0.54      inference('demod', [status(thm)], ['46', '68'])).
% 0.36/0.54  thf('70', plain, (~ (r1_tarski @ sk_B @ (u1_pre_topc @ sk_A))),
% 0.36/0.54      inference('simpl_trail', [status(thm)], ['1', '34'])).
% 0.36/0.54  thf('71', plain,
% 0.36/0.54      ((r2_hidden @ 
% 0.36/0.54        (sk_D @ (u1_pre_topc @ sk_A) @ sk_B @ 
% 0.36/0.54         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))) @ 
% 0.36/0.54        (u1_pre_topc @ sk_A))),
% 0.36/0.54      inference('clc', [status(thm)], ['69', '70'])).
% 0.36/0.54  thf('72', plain,
% 0.36/0.54      (![X11 : $i]:
% 0.36/0.54         ((m1_subset_1 @ (u1_pre_topc @ X11) @ 
% 0.36/0.54           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11))))
% 0.36/0.54          | ~ (l1_pre_topc @ X11))),
% 0.36/0.54      inference('cnf', [status(esa)], [dt_u1_pre_topc])).
% 0.36/0.54  thf('73', plain,
% 0.36/0.54      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.36/0.54         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 0.36/0.54          | (r1_tarski @ X5 @ X3)
% 0.36/0.54          | ~ (r2_hidden @ (sk_D @ X3 @ X5 @ X4) @ X3)
% 0.36/0.54          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X4)))),
% 0.36/0.54      inference('cnf', [status(esa)], [t7_subset_1])).
% 0.36/0.54  thf('74', plain,
% 0.36/0.54      (![X0 : $i, X1 : $i]:
% 0.36/0.54         (~ (l1_pre_topc @ X0)
% 0.36/0.54          | ~ (m1_subset_1 @ X1 @ 
% 0.36/0.54               (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0))))
% 0.36/0.54          | ~ (r2_hidden @ 
% 0.36/0.54               (sk_D @ (u1_pre_topc @ X0) @ X1 @ 
% 0.36/0.54                (k1_zfmisc_1 @ (u1_struct_0 @ X0))) @ 
% 0.36/0.54               (u1_pre_topc @ X0))
% 0.36/0.54          | (r1_tarski @ X1 @ (u1_pre_topc @ X0)))),
% 0.36/0.54      inference('sup-', [status(thm)], ['72', '73'])).
% 0.36/0.54  thf('75', plain,
% 0.36/0.54      (((r1_tarski @ sk_B @ (u1_pre_topc @ sk_A))
% 0.36/0.54        | ~ (m1_subset_1 @ sk_B @ 
% 0.36/0.54             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.36/0.54        | ~ (l1_pre_topc @ sk_A))),
% 0.36/0.54      inference('sup-', [status(thm)], ['71', '74'])).
% 0.36/0.54  thf('76', plain,
% 0.36/0.54      ((m1_subset_1 @ sk_B @ 
% 0.36/0.54        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('77', plain, ((l1_pre_topc @ sk_A)),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('78', plain, ((r1_tarski @ sk_B @ (u1_pre_topc @ sk_A))),
% 0.36/0.54      inference('demod', [status(thm)], ['75', '76', '77'])).
% 0.36/0.54  thf('79', plain, ($false), inference('demod', [status(thm)], ['35', '78'])).
% 0.36/0.54  
% 0.36/0.54  % SZS output end Refutation
% 0.36/0.54  
% 0.38/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
