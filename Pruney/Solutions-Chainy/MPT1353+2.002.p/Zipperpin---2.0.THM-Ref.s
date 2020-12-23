%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.0JDqyhp7SG

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:06:32 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 408 expanded)
%              Number of leaves         :   19 ( 115 expanded)
%              Depth                    :   20
%              Number of atoms          :  856 (4681 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(v1_tops_2_type,type,(
    v1_tops_2: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

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
    ! [X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) ) )
      | ( r2_hidden @ ( sk_C_1 @ X10 @ X11 ) @ X10 )
      | ( v1_tops_2 @ X10 @ X11 )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[d1_tops_2])).

thf('5',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v1_tops_2 @ sk_B @ sk_A )
    | ( r2_hidden @ ( sk_C_1 @ sk_B @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( v1_tops_2 @ sk_B @ sk_A )
    | ( r2_hidden @ ( sk_C_1 @ sk_B @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,
    ( ( r1_tarski @ sk_B @ ( u1_pre_topc @ sk_A ) )
    | ( v1_tops_2 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( r1_tarski @ sk_B @ ( u1_pre_topc @ sk_A ) )
   <= ( r1_tarski @ sk_B @ ( u1_pre_topc @ sk_A ) ) ),
    inference(split,[status(esa)],['8'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('11',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ X0 @ ( u1_pre_topc @ sk_A ) )
        | ~ ( r2_hidden @ X0 @ sk_B ) )
   <= ( r1_tarski @ sk_B @ ( u1_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,
    ( ( ( v1_tops_2 @ sk_B @ sk_A )
      | ( r2_hidden @ ( sk_C_1 @ sk_B @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
   <= ( r1_tarski @ sk_B @ ( u1_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['7','11'])).

thf('13',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) ) )
      | ( m1_subset_1 @ ( sk_C_1 @ X10 @ X11 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ( v1_tops_2 @ X10 @ X11 )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[d1_tops_2])).

thf('15',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v1_tops_2 @ sk_B @ sk_A )
    | ( m1_subset_1 @ ( sk_C_1 @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ( v1_tops_2 @ sk_B @ sk_A )
    | ( m1_subset_1 @ ( sk_C_1 @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf(d5_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v3_pre_topc @ B @ A )
          <=> ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) ) ) ) )).

thf('18',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ~ ( r2_hidden @ X7 @ ( u1_pre_topc @ X8 ) )
      | ( v3_pre_topc @ X7 @ X8 )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[d5_pre_topc])).

thf('19',plain,
    ( ( v1_tops_2 @ sk_B @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v3_pre_topc @ ( sk_C_1 @ sk_B @ sk_A ) @ sk_A )
    | ~ ( r2_hidden @ ( sk_C_1 @ sk_B @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ( v1_tops_2 @ sk_B @ sk_A )
    | ( v3_pre_topc @ ( sk_C_1 @ sk_B @ sk_A ) @ sk_A )
    | ~ ( r2_hidden @ ( sk_C_1 @ sk_B @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) ) )
      | ~ ( v3_pre_topc @ ( sk_C_1 @ X10 @ X11 ) @ X11 )
      | ( v1_tops_2 @ X10 @ X11 )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[d1_tops_2])).

thf('24',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v1_tops_2 @ sk_B @ sk_A )
    | ~ ( v3_pre_topc @ ( sk_C_1 @ sk_B @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ( v1_tops_2 @ sk_B @ sk_A )
    | ~ ( v3_pre_topc @ ( sk_C_1 @ sk_B @ sk_A ) @ sk_A ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,
    ( ~ ( r2_hidden @ ( sk_C_1 @ sk_B @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
    | ( v1_tops_2 @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['21','26'])).

thf('28',plain,
    ( ( ( v1_tops_2 @ sk_B @ sk_A )
      | ( v1_tops_2 @ sk_B @ sk_A ) )
   <= ( r1_tarski @ sk_B @ ( u1_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['12','27'])).

thf('29',plain,
    ( ( v1_tops_2 @ sk_B @ sk_A )
   <= ( r1_tarski @ sk_B @ ( u1_pre_topc @ sk_A ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,
    ( ~ ( v1_tops_2 @ sk_B @ sk_A )
   <= ~ ( v1_tops_2 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('31',plain,
    ( ( v1_tops_2 @ sk_B @ sk_A )
    | ~ ( r1_tarski @ sk_B @ ( u1_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ~ ( r1_tarski @ sk_B @ ( u1_pre_topc @ sk_A ) ) ),
    inference('sat_resolution*',[status(thm)],['2','31'])).

thf('33',plain,(
    ~ ( r1_tarski @ sk_B @ ( u1_pre_topc @ sk_A ) ) ),
    inference(simpl_trail,[status(thm)],['1','32'])).

thf('34',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_u1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( m1_subset_1 @ ( u1_pre_topc @ A ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('35',plain,(
    ! [X9: $i] :
      ( ( m1_subset_1 @ ( u1_pre_topc @ X9 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) ) )
      | ~ ( l1_pre_topc @ X9 ) ) ),
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

thf('36',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) )
      | ( r1_tarski @ X6 @ X4 )
      | ( m1_subset_1 @ ( sk_D @ X4 @ X6 @ X5 ) @ X5 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t7_subset_1])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) )
      | ( m1_subset_1 @ ( sk_D @ ( u1_pre_topc @ X0 ) @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( r1_tarski @ X1 @ ( u1_pre_topc @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,
    ( ( r1_tarski @ sk_B @ ( u1_pre_topc @ sk_A ) )
    | ( m1_subset_1 @ ( sk_D @ ( u1_pre_topc @ sk_A ) @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['34','37'])).

thf('39',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,
    ( ( r1_tarski @ sk_B @ ( u1_pre_topc @ sk_A ) )
    | ( m1_subset_1 @ ( sk_D @ ( u1_pre_topc @ sk_A ) @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,(
    ~ ( r1_tarski @ sk_B @ ( u1_pre_topc @ sk_A ) ) ),
    inference(simpl_trail,[status(thm)],['1','32'])).

thf('42',plain,(
    m1_subset_1 @ ( sk_D @ ( u1_pre_topc @ sk_A ) @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ~ ( v3_pre_topc @ X7 @ X8 )
      | ( r2_hidden @ X7 @ ( u1_pre_topc @ X8 ) )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[d5_pre_topc])).

thf('44',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r2_hidden @ ( sk_D @ ( u1_pre_topc @ sk_A ) @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) @ ( u1_pre_topc @ sk_A ) )
    | ~ ( v3_pre_topc @ ( sk_D @ ( u1_pre_topc @ sk_A ) @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( ( r2_hidden @ ( sk_D @ ( u1_pre_topc @ sk_A ) @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) @ ( u1_pre_topc @ sk_A ) )
    | ~ ( v3_pre_topc @ ( sk_D @ ( u1_pre_topc @ sk_A ) @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) @ sk_A ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    ! [X9: $i] :
      ( ( m1_subset_1 @ ( u1_pre_topc @ X9 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) ) )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_pre_topc])).

thf('49',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) )
      | ( r1_tarski @ X6 @ X4 )
      | ( r2_hidden @ ( sk_D @ X4 @ X6 @ X5 ) @ X6 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t7_subset_1])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) )
      | ( r2_hidden @ ( sk_D @ ( u1_pre_topc @ X0 ) @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) @ X1 )
      | ( r1_tarski @ X1 @ ( u1_pre_topc @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,
    ( ( r1_tarski @ sk_B @ ( u1_pre_topc @ sk_A ) )
    | ( r2_hidden @ ( sk_D @ ( u1_pre_topc @ sk_A ) @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) @ sk_B )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['47','50'])).

thf('52',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,
    ( ( r1_tarski @ sk_B @ ( u1_pre_topc @ sk_A ) )
    | ( r2_hidden @ ( sk_D @ ( u1_pre_topc @ sk_A ) @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) @ sk_B ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,(
    m1_subset_1 @ ( sk_D @ ( u1_pre_topc @ sk_A ) @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['40','41'])).

thf('55',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) ) )
      | ~ ( v1_tops_2 @ X10 @ X11 )
      | ~ ( r2_hidden @ X12 @ X10 )
      | ( v3_pre_topc @ X12 @ X11 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[d1_tops_2])).

thf('57',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v3_pre_topc @ X0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ sk_B )
      | ~ ( v1_tops_2 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,
    ( ( v1_tops_2 @ sk_B @ sk_A )
   <= ( v1_tops_2 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['8'])).

thf('60',plain,
    ( ( v1_tops_2 @ sk_B @ sk_A )
    | ( r1_tarski @ sk_B @ ( u1_pre_topc @ sk_A ) ) ),
    inference(split,[status(esa)],['8'])).

thf('61',plain,(
    v1_tops_2 @ sk_B @ sk_A ),
    inference('sat_resolution*',[status(thm)],['2','31','60'])).

thf('62',plain,(
    v1_tops_2 @ sk_B @ sk_A ),
    inference(simpl_trail,[status(thm)],['59','61'])).

thf('63',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v3_pre_topc @ X0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['57','58','62'])).

thf('64',plain,
    ( ~ ( r2_hidden @ ( sk_D @ ( u1_pre_topc @ sk_A ) @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) @ sk_B )
    | ( v3_pre_topc @ ( sk_D @ ( u1_pre_topc @ sk_A ) @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['54','63'])).

thf('65',plain,
    ( ( r1_tarski @ sk_B @ ( u1_pre_topc @ sk_A ) )
    | ( v3_pre_topc @ ( sk_D @ ( u1_pre_topc @ sk_A ) @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['53','64'])).

thf('66',plain,(
    ~ ( r1_tarski @ sk_B @ ( u1_pre_topc @ sk_A ) ) ),
    inference(simpl_trail,[status(thm)],['1','32'])).

thf('67',plain,(
    v3_pre_topc @ ( sk_D @ ( u1_pre_topc @ sk_A ) @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) @ sk_A ),
    inference(clc,[status(thm)],['65','66'])).

thf('68',plain,(
    r2_hidden @ ( sk_D @ ( u1_pre_topc @ sk_A ) @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) @ ( u1_pre_topc @ sk_A ) ),
    inference(demod,[status(thm)],['46','67'])).

thf('69',plain,(
    ! [X9: $i] :
      ( ( m1_subset_1 @ ( u1_pre_topc @ X9 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) ) )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_pre_topc])).

thf('70',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) )
      | ( r1_tarski @ X6 @ X4 )
      | ~ ( r2_hidden @ ( sk_D @ X4 @ X6 @ X5 ) @ X4 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t7_subset_1])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( r2_hidden @ ( sk_D @ ( u1_pre_topc @ X0 ) @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) @ ( u1_pre_topc @ X0 ) )
      | ( r1_tarski @ X1 @ ( u1_pre_topc @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,
    ( ( r1_tarski @ sk_B @ ( u1_pre_topc @ sk_A ) )
    | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['68','71'])).

thf('73',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    r1_tarski @ sk_B @ ( u1_pre_topc @ sk_A ) ),
    inference(demod,[status(thm)],['72','73','74'])).

thf('76',plain,(
    $false ),
    inference(demod,[status(thm)],['33','75'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.0JDqyhp7SG
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:55:08 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.49  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.49  % Solved by: fo/fo7.sh
% 0.20/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.49  % done 58 iterations in 0.032s
% 0.20/0.49  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.49  % SZS output start Refutation
% 0.20/0.49  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.49  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.49  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.49  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.20/0.49  thf(v1_tops_2_type, type, v1_tops_2: $i > $i > $o).
% 0.20/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.49  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.49  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.49  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.20/0.49  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 0.20/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.49  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.20/0.49  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.20/0.49  thf(t78_tops_2, conjecture,
% 0.20/0.49    (![A:$i]:
% 0.20/0.49     ( ( l1_pre_topc @ A ) =>
% 0.20/0.49       ( ![B:$i]:
% 0.20/0.49         ( ( m1_subset_1 @
% 0.20/0.49             B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.20/0.49           ( ( v1_tops_2 @ B @ A ) <=> ( r1_tarski @ B @ ( u1_pre_topc @ A ) ) ) ) ) ))).
% 0.20/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.49    (~( ![A:$i]:
% 0.20/0.49        ( ( l1_pre_topc @ A ) =>
% 0.20/0.49          ( ![B:$i]:
% 0.20/0.49            ( ( m1_subset_1 @
% 0.20/0.49                B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.20/0.49              ( ( v1_tops_2 @ B @ A ) <=>
% 0.20/0.49                ( r1_tarski @ B @ ( u1_pre_topc @ A ) ) ) ) ) ) )),
% 0.20/0.49    inference('cnf.neg', [status(esa)], [t78_tops_2])).
% 0.20/0.49  thf('0', plain,
% 0.20/0.49      ((~ (r1_tarski @ sk_B @ (u1_pre_topc @ sk_A))
% 0.20/0.49        | ~ (v1_tops_2 @ sk_B @ sk_A))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('1', plain,
% 0.20/0.49      ((~ (r1_tarski @ sk_B @ (u1_pre_topc @ sk_A)))
% 0.20/0.49         <= (~ ((r1_tarski @ sk_B @ (u1_pre_topc @ sk_A))))),
% 0.20/0.49      inference('split', [status(esa)], ['0'])).
% 0.20/0.49  thf('2', plain,
% 0.20/0.49      (~ ((r1_tarski @ sk_B @ (u1_pre_topc @ sk_A))) | 
% 0.20/0.49       ~ ((v1_tops_2 @ sk_B @ sk_A))),
% 0.20/0.49      inference('split', [status(esa)], ['0'])).
% 0.20/0.49  thf('3', plain,
% 0.20/0.49      ((m1_subset_1 @ sk_B @ 
% 0.20/0.49        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf(d1_tops_2, axiom,
% 0.20/0.49    (![A:$i]:
% 0.20/0.49     ( ( l1_pre_topc @ A ) =>
% 0.20/0.49       ( ![B:$i]:
% 0.20/0.49         ( ( m1_subset_1 @
% 0.20/0.49             B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.20/0.49           ( ( v1_tops_2 @ B @ A ) <=>
% 0.20/0.49             ( ![C:$i]:
% 0.20/0.49               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.49                 ( ( r2_hidden @ C @ B ) => ( v3_pre_topc @ C @ A ) ) ) ) ) ) ) ))).
% 0.20/0.49  thf('4', plain,
% 0.20/0.49      (![X10 : $i, X11 : $i]:
% 0.20/0.49         (~ (m1_subset_1 @ X10 @ 
% 0.20/0.49             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11))))
% 0.20/0.49          | (r2_hidden @ (sk_C_1 @ X10 @ X11) @ X10)
% 0.20/0.49          | (v1_tops_2 @ X10 @ X11)
% 0.20/0.49          | ~ (l1_pre_topc @ X11))),
% 0.20/0.49      inference('cnf', [status(esa)], [d1_tops_2])).
% 0.20/0.49  thf('5', plain,
% 0.20/0.49      ((~ (l1_pre_topc @ sk_A)
% 0.20/0.49        | (v1_tops_2 @ sk_B @ sk_A)
% 0.20/0.49        | (r2_hidden @ (sk_C_1 @ sk_B @ sk_A) @ sk_B))),
% 0.20/0.49      inference('sup-', [status(thm)], ['3', '4'])).
% 0.20/0.49  thf('6', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('7', plain,
% 0.20/0.49      (((v1_tops_2 @ sk_B @ sk_A) | (r2_hidden @ (sk_C_1 @ sk_B @ sk_A) @ sk_B))),
% 0.20/0.49      inference('demod', [status(thm)], ['5', '6'])).
% 0.20/0.49  thf('8', plain,
% 0.20/0.49      (((r1_tarski @ sk_B @ (u1_pre_topc @ sk_A)) | (v1_tops_2 @ sk_B @ sk_A))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('9', plain,
% 0.20/0.49      (((r1_tarski @ sk_B @ (u1_pre_topc @ sk_A)))
% 0.20/0.49         <= (((r1_tarski @ sk_B @ (u1_pre_topc @ sk_A))))),
% 0.20/0.49      inference('split', [status(esa)], ['8'])).
% 0.20/0.49  thf(d3_tarski, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( r1_tarski @ A @ B ) <=>
% 0.20/0.49       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.20/0.49  thf('10', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.49         (~ (r2_hidden @ X0 @ X1)
% 0.20/0.49          | (r2_hidden @ X0 @ X2)
% 0.20/0.49          | ~ (r1_tarski @ X1 @ X2))),
% 0.20/0.49      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.49  thf('11', plain,
% 0.20/0.49      ((![X0 : $i]:
% 0.20/0.49          ((r2_hidden @ X0 @ (u1_pre_topc @ sk_A)) | ~ (r2_hidden @ X0 @ sk_B)))
% 0.20/0.49         <= (((r1_tarski @ sk_B @ (u1_pre_topc @ sk_A))))),
% 0.20/0.49      inference('sup-', [status(thm)], ['9', '10'])).
% 0.20/0.49  thf('12', plain,
% 0.20/0.49      ((((v1_tops_2 @ sk_B @ sk_A)
% 0.20/0.49         | (r2_hidden @ (sk_C_1 @ sk_B @ sk_A) @ (u1_pre_topc @ sk_A))))
% 0.20/0.49         <= (((r1_tarski @ sk_B @ (u1_pre_topc @ sk_A))))),
% 0.20/0.49      inference('sup-', [status(thm)], ['7', '11'])).
% 0.20/0.49  thf('13', plain,
% 0.20/0.49      ((m1_subset_1 @ sk_B @ 
% 0.20/0.49        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('14', plain,
% 0.20/0.49      (![X10 : $i, X11 : $i]:
% 0.20/0.49         (~ (m1_subset_1 @ X10 @ 
% 0.20/0.49             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11))))
% 0.20/0.49          | (m1_subset_1 @ (sk_C_1 @ X10 @ X11) @ 
% 0.20/0.49             (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.20/0.49          | (v1_tops_2 @ X10 @ X11)
% 0.20/0.49          | ~ (l1_pre_topc @ X11))),
% 0.20/0.49      inference('cnf', [status(esa)], [d1_tops_2])).
% 0.20/0.49  thf('15', plain,
% 0.20/0.49      ((~ (l1_pre_topc @ sk_A)
% 0.20/0.49        | (v1_tops_2 @ sk_B @ sk_A)
% 0.20/0.49        | (m1_subset_1 @ (sk_C_1 @ sk_B @ sk_A) @ 
% 0.20/0.49           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.49      inference('sup-', [status(thm)], ['13', '14'])).
% 0.20/0.49  thf('16', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('17', plain,
% 0.20/0.49      (((v1_tops_2 @ sk_B @ sk_A)
% 0.20/0.49        | (m1_subset_1 @ (sk_C_1 @ sk_B @ sk_A) @ 
% 0.20/0.49           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.49      inference('demod', [status(thm)], ['15', '16'])).
% 0.20/0.49  thf(d5_pre_topc, axiom,
% 0.20/0.49    (![A:$i]:
% 0.20/0.49     ( ( l1_pre_topc @ A ) =>
% 0.20/0.49       ( ![B:$i]:
% 0.20/0.49         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.49           ( ( v3_pre_topc @ B @ A ) <=>
% 0.20/0.49             ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) ) ) ) ))).
% 0.20/0.49  thf('18', plain,
% 0.20/0.49      (![X7 : $i, X8 : $i]:
% 0.20/0.49         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 0.20/0.49          | ~ (r2_hidden @ X7 @ (u1_pre_topc @ X8))
% 0.20/0.49          | (v3_pre_topc @ X7 @ X8)
% 0.20/0.49          | ~ (l1_pre_topc @ X8))),
% 0.20/0.49      inference('cnf', [status(esa)], [d5_pre_topc])).
% 0.20/0.49  thf('19', plain,
% 0.20/0.49      (((v1_tops_2 @ sk_B @ sk_A)
% 0.20/0.49        | ~ (l1_pre_topc @ sk_A)
% 0.20/0.49        | (v3_pre_topc @ (sk_C_1 @ sk_B @ sk_A) @ sk_A)
% 0.20/0.49        | ~ (r2_hidden @ (sk_C_1 @ sk_B @ sk_A) @ (u1_pre_topc @ sk_A)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['17', '18'])).
% 0.20/0.49  thf('20', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('21', plain,
% 0.20/0.49      (((v1_tops_2 @ sk_B @ sk_A)
% 0.20/0.49        | (v3_pre_topc @ (sk_C_1 @ sk_B @ sk_A) @ sk_A)
% 0.20/0.49        | ~ (r2_hidden @ (sk_C_1 @ sk_B @ sk_A) @ (u1_pre_topc @ sk_A)))),
% 0.20/0.49      inference('demod', [status(thm)], ['19', '20'])).
% 0.20/0.49  thf('22', plain,
% 0.20/0.49      ((m1_subset_1 @ sk_B @ 
% 0.20/0.49        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('23', plain,
% 0.20/0.49      (![X10 : $i, X11 : $i]:
% 0.20/0.49         (~ (m1_subset_1 @ X10 @ 
% 0.20/0.49             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11))))
% 0.20/0.49          | ~ (v3_pre_topc @ (sk_C_1 @ X10 @ X11) @ X11)
% 0.20/0.49          | (v1_tops_2 @ X10 @ X11)
% 0.20/0.49          | ~ (l1_pre_topc @ X11))),
% 0.20/0.49      inference('cnf', [status(esa)], [d1_tops_2])).
% 0.20/0.49  thf('24', plain,
% 0.20/0.49      ((~ (l1_pre_topc @ sk_A)
% 0.20/0.49        | (v1_tops_2 @ sk_B @ sk_A)
% 0.20/0.49        | ~ (v3_pre_topc @ (sk_C_1 @ sk_B @ sk_A) @ sk_A))),
% 0.20/0.49      inference('sup-', [status(thm)], ['22', '23'])).
% 0.20/0.49  thf('25', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('26', plain,
% 0.20/0.49      (((v1_tops_2 @ sk_B @ sk_A)
% 0.20/0.49        | ~ (v3_pre_topc @ (sk_C_1 @ sk_B @ sk_A) @ sk_A))),
% 0.20/0.49      inference('demod', [status(thm)], ['24', '25'])).
% 0.20/0.49  thf('27', plain,
% 0.20/0.49      ((~ (r2_hidden @ (sk_C_1 @ sk_B @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.20/0.49        | (v1_tops_2 @ sk_B @ sk_A))),
% 0.20/0.49      inference('clc', [status(thm)], ['21', '26'])).
% 0.20/0.49  thf('28', plain,
% 0.20/0.49      ((((v1_tops_2 @ sk_B @ sk_A) | (v1_tops_2 @ sk_B @ sk_A)))
% 0.20/0.49         <= (((r1_tarski @ sk_B @ (u1_pre_topc @ sk_A))))),
% 0.20/0.49      inference('sup-', [status(thm)], ['12', '27'])).
% 0.20/0.49  thf('29', plain,
% 0.20/0.49      (((v1_tops_2 @ sk_B @ sk_A))
% 0.20/0.49         <= (((r1_tarski @ sk_B @ (u1_pre_topc @ sk_A))))),
% 0.20/0.49      inference('simplify', [status(thm)], ['28'])).
% 0.20/0.49  thf('30', plain,
% 0.20/0.49      ((~ (v1_tops_2 @ sk_B @ sk_A)) <= (~ ((v1_tops_2 @ sk_B @ sk_A)))),
% 0.20/0.49      inference('split', [status(esa)], ['0'])).
% 0.20/0.49  thf('31', plain,
% 0.20/0.49      (((v1_tops_2 @ sk_B @ sk_A)) | 
% 0.20/0.49       ~ ((r1_tarski @ sk_B @ (u1_pre_topc @ sk_A)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['29', '30'])).
% 0.20/0.49  thf('32', plain, (~ ((r1_tarski @ sk_B @ (u1_pre_topc @ sk_A)))),
% 0.20/0.49      inference('sat_resolution*', [status(thm)], ['2', '31'])).
% 0.20/0.49  thf('33', plain, (~ (r1_tarski @ sk_B @ (u1_pre_topc @ sk_A))),
% 0.20/0.49      inference('simpl_trail', [status(thm)], ['1', '32'])).
% 0.20/0.49  thf('34', plain,
% 0.20/0.49      ((m1_subset_1 @ sk_B @ 
% 0.20/0.49        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf(dt_u1_pre_topc, axiom,
% 0.20/0.49    (![A:$i]:
% 0.20/0.49     ( ( l1_pre_topc @ A ) =>
% 0.20/0.49       ( m1_subset_1 @
% 0.20/0.49         ( u1_pre_topc @ A ) @ 
% 0.20/0.49         ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ))).
% 0.20/0.49  thf('35', plain,
% 0.20/0.49      (![X9 : $i]:
% 0.20/0.49         ((m1_subset_1 @ (u1_pre_topc @ X9) @ 
% 0.20/0.49           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9))))
% 0.20/0.49          | ~ (l1_pre_topc @ X9))),
% 0.20/0.49      inference('cnf', [status(esa)], [dt_u1_pre_topc])).
% 0.20/0.49  thf(t7_subset_1, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.49       ( ![C:$i]:
% 0.20/0.49         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.49           ( ( ![D:$i]:
% 0.20/0.49               ( ( m1_subset_1 @ D @ A ) =>
% 0.20/0.49                 ( ( r2_hidden @ D @ B ) => ( r2_hidden @ D @ C ) ) ) ) =>
% 0.20/0.49             ( r1_tarski @ B @ C ) ) ) ) ))).
% 0.20/0.49  thf('36', plain,
% 0.20/0.49      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.20/0.49         (~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5))
% 0.20/0.49          | (r1_tarski @ X6 @ X4)
% 0.20/0.49          | (m1_subset_1 @ (sk_D @ X4 @ X6 @ X5) @ X5)
% 0.20/0.49          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X5)))),
% 0.20/0.49      inference('cnf', [status(esa)], [t7_subset_1])).
% 0.20/0.49  thf('37', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]:
% 0.20/0.49         (~ (l1_pre_topc @ X0)
% 0.20/0.49          | ~ (m1_subset_1 @ X1 @ 
% 0.20/0.49               (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0))))
% 0.20/0.49          | (m1_subset_1 @ 
% 0.20/0.49             (sk_D @ (u1_pre_topc @ X0) @ X1 @ 
% 0.20/0.49              (k1_zfmisc_1 @ (u1_struct_0 @ X0))) @ 
% 0.20/0.49             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.20/0.49          | (r1_tarski @ X1 @ (u1_pre_topc @ X0)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['35', '36'])).
% 0.20/0.49  thf('38', plain,
% 0.20/0.49      (((r1_tarski @ sk_B @ (u1_pre_topc @ sk_A))
% 0.20/0.49        | (m1_subset_1 @ 
% 0.20/0.49           (sk_D @ (u1_pre_topc @ sk_A) @ sk_B @ 
% 0.20/0.49            (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))) @ 
% 0.20/0.49           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.49        | ~ (l1_pre_topc @ sk_A))),
% 0.20/0.49      inference('sup-', [status(thm)], ['34', '37'])).
% 0.20/0.49  thf('39', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('40', plain,
% 0.20/0.49      (((r1_tarski @ sk_B @ (u1_pre_topc @ sk_A))
% 0.20/0.49        | (m1_subset_1 @ 
% 0.20/0.49           (sk_D @ (u1_pre_topc @ sk_A) @ sk_B @ 
% 0.20/0.49            (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))) @ 
% 0.20/0.49           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.49      inference('demod', [status(thm)], ['38', '39'])).
% 0.20/0.49  thf('41', plain, (~ (r1_tarski @ sk_B @ (u1_pre_topc @ sk_A))),
% 0.20/0.49      inference('simpl_trail', [status(thm)], ['1', '32'])).
% 0.20/0.49  thf('42', plain,
% 0.20/0.49      ((m1_subset_1 @ 
% 0.20/0.49        (sk_D @ (u1_pre_topc @ sk_A) @ sk_B @ 
% 0.20/0.49         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))) @ 
% 0.20/0.49        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.49      inference('clc', [status(thm)], ['40', '41'])).
% 0.20/0.49  thf('43', plain,
% 0.20/0.49      (![X7 : $i, X8 : $i]:
% 0.20/0.49         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 0.20/0.49          | ~ (v3_pre_topc @ X7 @ X8)
% 0.20/0.49          | (r2_hidden @ X7 @ (u1_pre_topc @ X8))
% 0.20/0.49          | ~ (l1_pre_topc @ X8))),
% 0.20/0.49      inference('cnf', [status(esa)], [d5_pre_topc])).
% 0.20/0.49  thf('44', plain,
% 0.20/0.49      ((~ (l1_pre_topc @ sk_A)
% 0.20/0.49        | (r2_hidden @ 
% 0.20/0.49           (sk_D @ (u1_pre_topc @ sk_A) @ sk_B @ 
% 0.20/0.49            (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))) @ 
% 0.20/0.49           (u1_pre_topc @ sk_A))
% 0.20/0.49        | ~ (v3_pre_topc @ 
% 0.20/0.49             (sk_D @ (u1_pre_topc @ sk_A) @ sk_B @ 
% 0.20/0.49              (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))) @ 
% 0.20/0.49             sk_A))),
% 0.20/0.49      inference('sup-', [status(thm)], ['42', '43'])).
% 0.20/0.49  thf('45', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('46', plain,
% 0.20/0.49      (((r2_hidden @ 
% 0.20/0.49         (sk_D @ (u1_pre_topc @ sk_A) @ sk_B @ 
% 0.20/0.49          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))) @ 
% 0.20/0.49         (u1_pre_topc @ sk_A))
% 0.20/0.49        | ~ (v3_pre_topc @ 
% 0.20/0.49             (sk_D @ (u1_pre_topc @ sk_A) @ sk_B @ 
% 0.20/0.49              (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))) @ 
% 0.20/0.49             sk_A))),
% 0.20/0.49      inference('demod', [status(thm)], ['44', '45'])).
% 0.20/0.49  thf('47', plain,
% 0.20/0.49      ((m1_subset_1 @ sk_B @ 
% 0.20/0.49        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('48', plain,
% 0.20/0.49      (![X9 : $i]:
% 0.20/0.49         ((m1_subset_1 @ (u1_pre_topc @ X9) @ 
% 0.20/0.49           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9))))
% 0.20/0.49          | ~ (l1_pre_topc @ X9))),
% 0.20/0.49      inference('cnf', [status(esa)], [dt_u1_pre_topc])).
% 0.20/0.49  thf('49', plain,
% 0.20/0.49      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.20/0.49         (~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5))
% 0.20/0.49          | (r1_tarski @ X6 @ X4)
% 0.20/0.49          | (r2_hidden @ (sk_D @ X4 @ X6 @ X5) @ X6)
% 0.20/0.49          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X5)))),
% 0.20/0.49      inference('cnf', [status(esa)], [t7_subset_1])).
% 0.20/0.49  thf('50', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]:
% 0.20/0.49         (~ (l1_pre_topc @ X0)
% 0.20/0.49          | ~ (m1_subset_1 @ X1 @ 
% 0.20/0.49               (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0))))
% 0.20/0.49          | (r2_hidden @ 
% 0.20/0.49             (sk_D @ (u1_pre_topc @ X0) @ X1 @ 
% 0.20/0.49              (k1_zfmisc_1 @ (u1_struct_0 @ X0))) @ 
% 0.20/0.49             X1)
% 0.20/0.49          | (r1_tarski @ X1 @ (u1_pre_topc @ X0)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['48', '49'])).
% 0.20/0.49  thf('51', plain,
% 0.20/0.49      (((r1_tarski @ sk_B @ (u1_pre_topc @ sk_A))
% 0.20/0.49        | (r2_hidden @ 
% 0.20/0.49           (sk_D @ (u1_pre_topc @ sk_A) @ sk_B @ 
% 0.20/0.49            (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))) @ 
% 0.20/0.49           sk_B)
% 0.20/0.49        | ~ (l1_pre_topc @ sk_A))),
% 0.20/0.49      inference('sup-', [status(thm)], ['47', '50'])).
% 0.20/0.49  thf('52', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('53', plain,
% 0.20/0.49      (((r1_tarski @ sk_B @ (u1_pre_topc @ sk_A))
% 0.20/0.49        | (r2_hidden @ 
% 0.20/0.49           (sk_D @ (u1_pre_topc @ sk_A) @ sk_B @ 
% 0.20/0.49            (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))) @ 
% 0.20/0.49           sk_B))),
% 0.20/0.49      inference('demod', [status(thm)], ['51', '52'])).
% 0.20/0.49  thf('54', plain,
% 0.20/0.49      ((m1_subset_1 @ 
% 0.20/0.49        (sk_D @ (u1_pre_topc @ sk_A) @ sk_B @ 
% 0.20/0.49         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))) @ 
% 0.20/0.49        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.49      inference('clc', [status(thm)], ['40', '41'])).
% 0.20/0.49  thf('55', plain,
% 0.20/0.49      ((m1_subset_1 @ sk_B @ 
% 0.20/0.49        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('56', plain,
% 0.20/0.49      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.20/0.49         (~ (m1_subset_1 @ X10 @ 
% 0.20/0.49             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11))))
% 0.20/0.49          | ~ (v1_tops_2 @ X10 @ X11)
% 0.20/0.49          | ~ (r2_hidden @ X12 @ X10)
% 0.20/0.49          | (v3_pre_topc @ X12 @ X11)
% 0.20/0.49          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.20/0.49          | ~ (l1_pre_topc @ X11))),
% 0.20/0.49      inference('cnf', [status(esa)], [d1_tops_2])).
% 0.20/0.49  thf('57', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (~ (l1_pre_topc @ sk_A)
% 0.20/0.49          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.49          | (v3_pre_topc @ X0 @ sk_A)
% 0.20/0.49          | ~ (r2_hidden @ X0 @ sk_B)
% 0.20/0.49          | ~ (v1_tops_2 @ sk_B @ sk_A))),
% 0.20/0.49      inference('sup-', [status(thm)], ['55', '56'])).
% 0.20/0.49  thf('58', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('59', plain,
% 0.20/0.49      (((v1_tops_2 @ sk_B @ sk_A)) <= (((v1_tops_2 @ sk_B @ sk_A)))),
% 0.20/0.49      inference('split', [status(esa)], ['8'])).
% 0.20/0.49  thf('60', plain,
% 0.20/0.49      (((v1_tops_2 @ sk_B @ sk_A)) | 
% 0.20/0.49       ((r1_tarski @ sk_B @ (u1_pre_topc @ sk_A)))),
% 0.20/0.49      inference('split', [status(esa)], ['8'])).
% 0.20/0.49  thf('61', plain, (((v1_tops_2 @ sk_B @ sk_A))),
% 0.20/0.49      inference('sat_resolution*', [status(thm)], ['2', '31', '60'])).
% 0.20/0.49  thf('62', plain, ((v1_tops_2 @ sk_B @ sk_A)),
% 0.20/0.49      inference('simpl_trail', [status(thm)], ['59', '61'])).
% 0.20/0.49  thf('63', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.49          | (v3_pre_topc @ X0 @ sk_A)
% 0.20/0.49          | ~ (r2_hidden @ X0 @ sk_B))),
% 0.20/0.49      inference('demod', [status(thm)], ['57', '58', '62'])).
% 0.20/0.49  thf('64', plain,
% 0.20/0.49      ((~ (r2_hidden @ 
% 0.20/0.49           (sk_D @ (u1_pre_topc @ sk_A) @ sk_B @ 
% 0.20/0.49            (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))) @ 
% 0.20/0.49           sk_B)
% 0.20/0.49        | (v3_pre_topc @ 
% 0.20/0.49           (sk_D @ (u1_pre_topc @ sk_A) @ sk_B @ 
% 0.20/0.49            (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))) @ 
% 0.20/0.49           sk_A))),
% 0.20/0.49      inference('sup-', [status(thm)], ['54', '63'])).
% 0.20/0.49  thf('65', plain,
% 0.20/0.49      (((r1_tarski @ sk_B @ (u1_pre_topc @ sk_A))
% 0.20/0.49        | (v3_pre_topc @ 
% 0.20/0.49           (sk_D @ (u1_pre_topc @ sk_A) @ sk_B @ 
% 0.20/0.49            (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))) @ 
% 0.20/0.49           sk_A))),
% 0.20/0.49      inference('sup-', [status(thm)], ['53', '64'])).
% 0.20/0.49  thf('66', plain, (~ (r1_tarski @ sk_B @ (u1_pre_topc @ sk_A))),
% 0.20/0.49      inference('simpl_trail', [status(thm)], ['1', '32'])).
% 0.20/0.49  thf('67', plain,
% 0.20/0.49      ((v3_pre_topc @ 
% 0.20/0.49        (sk_D @ (u1_pre_topc @ sk_A) @ sk_B @ 
% 0.20/0.49         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))) @ 
% 0.20/0.49        sk_A)),
% 0.20/0.49      inference('clc', [status(thm)], ['65', '66'])).
% 0.20/0.49  thf('68', plain,
% 0.20/0.49      ((r2_hidden @ 
% 0.20/0.49        (sk_D @ (u1_pre_topc @ sk_A) @ sk_B @ 
% 0.20/0.49         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))) @ 
% 0.20/0.49        (u1_pre_topc @ sk_A))),
% 0.20/0.49      inference('demod', [status(thm)], ['46', '67'])).
% 0.20/0.49  thf('69', plain,
% 0.20/0.49      (![X9 : $i]:
% 0.20/0.49         ((m1_subset_1 @ (u1_pre_topc @ X9) @ 
% 0.20/0.49           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9))))
% 0.20/0.49          | ~ (l1_pre_topc @ X9))),
% 0.20/0.49      inference('cnf', [status(esa)], [dt_u1_pre_topc])).
% 0.20/0.49  thf('70', plain,
% 0.20/0.49      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.20/0.49         (~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5))
% 0.20/0.49          | (r1_tarski @ X6 @ X4)
% 0.20/0.49          | ~ (r2_hidden @ (sk_D @ X4 @ X6 @ X5) @ X4)
% 0.20/0.49          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X5)))),
% 0.20/0.49      inference('cnf', [status(esa)], [t7_subset_1])).
% 0.20/0.49  thf('71', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]:
% 0.20/0.49         (~ (l1_pre_topc @ X0)
% 0.20/0.49          | ~ (m1_subset_1 @ X1 @ 
% 0.20/0.49               (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0))))
% 0.20/0.49          | ~ (r2_hidden @ 
% 0.20/0.49               (sk_D @ (u1_pre_topc @ X0) @ X1 @ 
% 0.20/0.49                (k1_zfmisc_1 @ (u1_struct_0 @ X0))) @ 
% 0.20/0.49               (u1_pre_topc @ X0))
% 0.20/0.49          | (r1_tarski @ X1 @ (u1_pre_topc @ X0)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['69', '70'])).
% 0.20/0.49  thf('72', plain,
% 0.20/0.49      (((r1_tarski @ sk_B @ (u1_pre_topc @ sk_A))
% 0.20/0.49        | ~ (m1_subset_1 @ sk_B @ 
% 0.20/0.49             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.20/0.49        | ~ (l1_pre_topc @ sk_A))),
% 0.20/0.49      inference('sup-', [status(thm)], ['68', '71'])).
% 0.20/0.49  thf('73', plain,
% 0.20/0.49      ((m1_subset_1 @ sk_B @ 
% 0.20/0.49        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('74', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('75', plain, ((r1_tarski @ sk_B @ (u1_pre_topc @ sk_A))),
% 0.20/0.49      inference('demod', [status(thm)], ['72', '73', '74'])).
% 0.20/0.49  thf('76', plain, ($false), inference('demod', [status(thm)], ['33', '75'])).
% 0.20/0.49  
% 0.20/0.49  % SZS output end Refutation
% 0.20/0.49  
% 0.20/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
