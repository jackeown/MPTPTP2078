%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.V7rJmz7iUh

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:06:32 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 167 expanded)
%              Number of leaves         :   19 (  55 expanded)
%              Depth                    :   15
%              Number of atoms          :  725 (1648 expanded)
%              Number of equality atoms :    2 (   6 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_C_2_type,type,(
    sk_C_2: $i > $i > $i )).

thf(v1_tops_2_type,type,(
    v1_tops_2: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

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
    | ~ ( v1_tops_2 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('2',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('3',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('4',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r1_tarski @ X9 @ X10 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('5',plain,(
    r1_tarski @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['2','7'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('9',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X7 @ X6 )
      | ( r1_tarski @ X7 @ X5 )
      | ( X6
       != ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('10',plain,(
    ! [X5: $i,X7: $i] :
      ( ( r1_tarski @ X7 @ X5 )
      | ~ ( r2_hidden @ X7 @ ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( r1_tarski @ ( sk_C @ X0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['8','10'])).

thf('12',plain,(
    ! [X9: $i,X11: $i] :
      ( ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X11 ) )
      | ~ ( r1_tarski @ X9 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( m1_subset_1 @ ( sk_C @ X0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,
    ( ( r1_tarski @ sk_B @ ( u1_pre_topc @ sk_A ) )
    | ( v1_tops_2 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ( v1_tops_2 @ sk_B @ sk_A )
   <= ( v1_tops_2 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['14'])).

thf('16',plain,(
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

thf('17',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) ) )
      | ~ ( v1_tops_2 @ X14 @ X15 )
      | ~ ( r2_hidden @ X16 @ X14 )
      | ( v3_pre_topc @ X16 @ X15 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ~ ( l1_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[d1_tops_2])).

thf('18',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v3_pre_topc @ X0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ sk_B )
      | ~ ( v1_tops_2 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v3_pre_topc @ X0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ sk_B )
      | ~ ( v1_tops_2 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ sk_B )
        | ( v3_pre_topc @ X0 @ sk_A )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ( v1_tops_2 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['15','20'])).

thf('22',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ sk_B @ X0 )
        | ( v3_pre_topc @ ( sk_C @ X0 @ sk_B ) @ sk_A )
        | ~ ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ sk_B ) )
   <= ( v1_tops_2 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['13','21'])).

thf('23',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('24',plain,
    ( ! [X0: $i] :
        ( ( v3_pre_topc @ ( sk_C @ X0 @ sk_B ) @ sk_A )
        | ( r1_tarski @ sk_B @ X0 ) )
   <= ( v1_tops_2 @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( m1_subset_1 @ ( sk_C @ X0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf(d5_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v3_pre_topc @ B @ A )
          <=> ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) ) ) ) )).

thf('26',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ~ ( v3_pre_topc @ X12 @ X13 )
      | ( r2_hidden @ X12 @ ( u1_pre_topc @ X13 ) )
      | ~ ( l1_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[d5_pre_topc])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ~ ( l1_pre_topc @ sk_A )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ ( u1_pre_topc @ sk_A ) )
      | ~ ( v3_pre_topc @ ( sk_C @ X0 @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ ( u1_pre_topc @ sk_A ) )
      | ~ ( v3_pre_topc @ ( sk_C @ X0 @ sk_B ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ sk_B @ X0 )
        | ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ ( u1_pre_topc @ sk_A ) )
        | ( r1_tarski @ sk_B @ X0 ) )
   <= ( v1_tops_2 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['24','29'])).

thf('31',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ ( u1_pre_topc @ sk_A ) )
        | ( r1_tarski @ sk_B @ X0 ) )
   <= ( v1_tops_2 @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('33',plain,
    ( ( ( r1_tarski @ sk_B @ ( u1_pre_topc @ sk_A ) )
      | ( r1_tarski @ sk_B @ ( u1_pre_topc @ sk_A ) ) )
   <= ( v1_tops_2 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,
    ( ( r1_tarski @ sk_B @ ( u1_pre_topc @ sk_A ) )
   <= ( v1_tops_2 @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,
    ( ~ ( r1_tarski @ sk_B @ ( u1_pre_topc @ sk_A ) )
   <= ~ ( r1_tarski @ sk_B @ ( u1_pre_topc @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('36',plain,
    ( ( r1_tarski @ sk_B @ ( u1_pre_topc @ sk_A ) )
    | ~ ( v1_tops_2 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,
    ( ( r1_tarski @ sk_B @ ( u1_pre_topc @ sk_A ) )
    | ( v1_tops_2 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['14'])).

thf('38',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) ) )
      | ( r2_hidden @ ( sk_C_2 @ X14 @ X15 ) @ X14 )
      | ( v1_tops_2 @ X14 @ X15 )
      | ~ ( l1_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[d1_tops_2])).

thf('40',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v1_tops_2 @ sk_B @ sk_A )
    | ( r2_hidden @ ( sk_C_2 @ sk_B @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( ( v1_tops_2 @ sk_B @ sk_A )
    | ( r2_hidden @ ( sk_C_2 @ sk_B @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,
    ( ( r1_tarski @ sk_B @ ( u1_pre_topc @ sk_A ) )
   <= ( r1_tarski @ sk_B @ ( u1_pre_topc @ sk_A ) ) ),
    inference(split,[status(esa)],['14'])).

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('45',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ X0 @ ( u1_pre_topc @ sk_A ) )
        | ~ ( r2_hidden @ X0 @ sk_B ) )
   <= ( r1_tarski @ sk_B @ ( u1_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,
    ( ( ( v1_tops_2 @ sk_B @ sk_A )
      | ( r2_hidden @ ( sk_C_2 @ sk_B @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
   <= ( r1_tarski @ sk_B @ ( u1_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['42','45'])).

thf('47',plain,
    ( ( v1_tops_2 @ sk_B @ sk_A )
    | ( r2_hidden @ ( sk_C_2 @ sk_B @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('49',plain,
    ( ( v1_tops_2 @ sk_B @ sk_A )
    | ( r2_hidden @ ( sk_C_2 @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X5: $i,X7: $i] :
      ( ( r1_tarski @ X7 @ X5 )
      | ~ ( r2_hidden @ X7 @ ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('51',plain,
    ( ( v1_tops_2 @ sk_B @ sk_A )
    | ( r1_tarski @ ( sk_C_2 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X9: $i,X11: $i] :
      ( ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X11 ) )
      | ~ ( r1_tarski @ X9 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('53',plain,
    ( ( v1_tops_2 @ sk_B @ sk_A )
    | ( m1_subset_1 @ ( sk_C_2 @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ~ ( r2_hidden @ X12 @ ( u1_pre_topc @ X13 ) )
      | ( v3_pre_topc @ X12 @ X13 )
      | ~ ( l1_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[d5_pre_topc])).

thf('55',plain,
    ( ( v1_tops_2 @ sk_B @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v3_pre_topc @ ( sk_C_2 @ sk_B @ sk_A ) @ sk_A )
    | ~ ( r2_hidden @ ( sk_C_2 @ sk_B @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,
    ( ( v1_tops_2 @ sk_B @ sk_A )
    | ( v3_pre_topc @ ( sk_C_2 @ sk_B @ sk_A ) @ sk_A )
    | ~ ( r2_hidden @ ( sk_C_2 @ sk_B @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) ) )
      | ~ ( v3_pre_topc @ ( sk_C_2 @ X14 @ X15 ) @ X15 )
      | ( v1_tops_2 @ X14 @ X15 )
      | ~ ( l1_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[d1_tops_2])).

thf('60',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v1_tops_2 @ sk_B @ sk_A )
    | ~ ( v3_pre_topc @ ( sk_C_2 @ sk_B @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,
    ( ( v1_tops_2 @ sk_B @ sk_A )
    | ~ ( v3_pre_topc @ ( sk_C_2 @ sk_B @ sk_A ) @ sk_A ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,
    ( ~ ( r2_hidden @ ( sk_C_2 @ sk_B @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
    | ( v1_tops_2 @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['57','62'])).

thf('64',plain,
    ( ( ( v1_tops_2 @ sk_B @ sk_A )
      | ( v1_tops_2 @ sk_B @ sk_A ) )
   <= ( r1_tarski @ sk_B @ ( u1_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['46','63'])).

thf('65',plain,
    ( ( v1_tops_2 @ sk_B @ sk_A )
   <= ( r1_tarski @ sk_B @ ( u1_pre_topc @ sk_A ) ) ),
    inference(simplify,[status(thm)],['64'])).

thf('66',plain,
    ( ~ ( v1_tops_2 @ sk_B @ sk_A )
   <= ~ ( v1_tops_2 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('67',plain,
    ( ~ ( r1_tarski @ sk_B @ ( u1_pre_topc @ sk_A ) )
    | ( v1_tops_2 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','36','37','67'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.V7rJmz7iUh
% 0.12/0.33  % Computer   : n020.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 15:48:52 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running portfolio for 600 s
% 0.12/0.33  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.33  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.19/0.50  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.19/0.50  % Solved by: fo/fo7.sh
% 0.19/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.50  % done 118 iterations in 0.057s
% 0.19/0.50  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.19/0.50  % SZS output start Refutation
% 0.19/0.50  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.19/0.50  thf(sk_B_type, type, sk_B: $i).
% 0.19/0.50  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.19/0.50  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.19/0.50  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.19/0.50  thf(sk_C_2_type, type, sk_C_2: $i > $i > $i).
% 0.19/0.50  thf(v1_tops_2_type, type, v1_tops_2: $i > $i > $o).
% 0.19/0.50  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.19/0.50  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.19/0.50  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 0.19/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.50  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.19/0.50  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.19/0.50  thf(t78_tops_2, conjecture,
% 0.19/0.50    (![A:$i]:
% 0.19/0.50     ( ( l1_pre_topc @ A ) =>
% 0.19/0.50       ( ![B:$i]:
% 0.19/0.50         ( ( m1_subset_1 @
% 0.19/0.50             B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.19/0.50           ( ( v1_tops_2 @ B @ A ) <=> ( r1_tarski @ B @ ( u1_pre_topc @ A ) ) ) ) ) ))).
% 0.19/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.50    (~( ![A:$i]:
% 0.19/0.50        ( ( l1_pre_topc @ A ) =>
% 0.19/0.50          ( ![B:$i]:
% 0.19/0.50            ( ( m1_subset_1 @
% 0.19/0.50                B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.19/0.50              ( ( v1_tops_2 @ B @ A ) <=>
% 0.19/0.50                ( r1_tarski @ B @ ( u1_pre_topc @ A ) ) ) ) ) ) )),
% 0.19/0.50    inference('cnf.neg', [status(esa)], [t78_tops_2])).
% 0.19/0.50  thf('0', plain,
% 0.19/0.50      ((~ (r1_tarski @ sk_B @ (u1_pre_topc @ sk_A))
% 0.19/0.50        | ~ (v1_tops_2 @ sk_B @ sk_A))),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('1', plain,
% 0.19/0.50      (~ ((r1_tarski @ sk_B @ (u1_pre_topc @ sk_A))) | 
% 0.19/0.50       ~ ((v1_tops_2 @ sk_B @ sk_A))),
% 0.19/0.50      inference('split', [status(esa)], ['0'])).
% 0.19/0.50  thf(d3_tarski, axiom,
% 0.19/0.50    (![A:$i,B:$i]:
% 0.19/0.50     ( ( r1_tarski @ A @ B ) <=>
% 0.19/0.50       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.19/0.50  thf('2', plain,
% 0.19/0.50      (![X1 : $i, X3 : $i]:
% 0.19/0.50         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.19/0.50      inference('cnf', [status(esa)], [d3_tarski])).
% 0.19/0.50  thf('3', plain,
% 0.19/0.50      ((m1_subset_1 @ sk_B @ 
% 0.19/0.50        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf(t3_subset, axiom,
% 0.19/0.50    (![A:$i,B:$i]:
% 0.19/0.50     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.19/0.50  thf('4', plain,
% 0.19/0.50      (![X9 : $i, X10 : $i]:
% 0.19/0.50         ((r1_tarski @ X9 @ X10) | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10)))),
% 0.19/0.50      inference('cnf', [status(esa)], [t3_subset])).
% 0.19/0.50  thf('5', plain, ((r1_tarski @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.50      inference('sup-', [status(thm)], ['3', '4'])).
% 0.19/0.50  thf('6', plain,
% 0.19/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.50         (~ (r2_hidden @ X0 @ X1)
% 0.19/0.50          | (r2_hidden @ X0 @ X2)
% 0.19/0.50          | ~ (r1_tarski @ X1 @ X2))),
% 0.19/0.50      inference('cnf', [status(esa)], [d3_tarski])).
% 0.19/0.50  thf('7', plain,
% 0.19/0.50      (![X0 : $i]:
% 0.19/0.50         ((r2_hidden @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.19/0.50          | ~ (r2_hidden @ X0 @ sk_B))),
% 0.19/0.50      inference('sup-', [status(thm)], ['5', '6'])).
% 0.19/0.50  thf('8', plain,
% 0.19/0.50      (![X0 : $i]:
% 0.19/0.50         ((r1_tarski @ sk_B @ X0)
% 0.19/0.50          | (r2_hidden @ (sk_C @ X0 @ sk_B) @ 
% 0.19/0.50             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.19/0.50      inference('sup-', [status(thm)], ['2', '7'])).
% 0.19/0.50  thf(d1_zfmisc_1, axiom,
% 0.19/0.50    (![A:$i,B:$i]:
% 0.19/0.50     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.19/0.50       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.19/0.50  thf('9', plain,
% 0.19/0.50      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.19/0.50         (~ (r2_hidden @ X7 @ X6)
% 0.19/0.50          | (r1_tarski @ X7 @ X5)
% 0.19/0.50          | ((X6) != (k1_zfmisc_1 @ X5)))),
% 0.19/0.50      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.19/0.50  thf('10', plain,
% 0.19/0.50      (![X5 : $i, X7 : $i]:
% 0.19/0.50         ((r1_tarski @ X7 @ X5) | ~ (r2_hidden @ X7 @ (k1_zfmisc_1 @ X5)))),
% 0.19/0.50      inference('simplify', [status(thm)], ['9'])).
% 0.19/0.50  thf('11', plain,
% 0.19/0.50      (![X0 : $i]:
% 0.19/0.50         ((r1_tarski @ sk_B @ X0)
% 0.19/0.50          | (r1_tarski @ (sk_C @ X0 @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 0.19/0.50      inference('sup-', [status(thm)], ['8', '10'])).
% 0.19/0.50  thf('12', plain,
% 0.19/0.50      (![X9 : $i, X11 : $i]:
% 0.19/0.50         ((m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X11)) | ~ (r1_tarski @ X9 @ X11))),
% 0.19/0.50      inference('cnf', [status(esa)], [t3_subset])).
% 0.19/0.50  thf('13', plain,
% 0.19/0.50      (![X0 : $i]:
% 0.19/0.50         ((r1_tarski @ sk_B @ X0)
% 0.19/0.50          | (m1_subset_1 @ (sk_C @ X0 @ sk_B) @ 
% 0.19/0.50             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.19/0.50      inference('sup-', [status(thm)], ['11', '12'])).
% 0.19/0.50  thf('14', plain,
% 0.19/0.50      (((r1_tarski @ sk_B @ (u1_pre_topc @ sk_A)) | (v1_tops_2 @ sk_B @ sk_A))),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('15', plain,
% 0.19/0.50      (((v1_tops_2 @ sk_B @ sk_A)) <= (((v1_tops_2 @ sk_B @ sk_A)))),
% 0.19/0.50      inference('split', [status(esa)], ['14'])).
% 0.19/0.50  thf('16', plain,
% 0.19/0.50      ((m1_subset_1 @ sk_B @ 
% 0.19/0.50        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf(d1_tops_2, axiom,
% 0.19/0.50    (![A:$i]:
% 0.19/0.50     ( ( l1_pre_topc @ A ) =>
% 0.19/0.50       ( ![B:$i]:
% 0.19/0.50         ( ( m1_subset_1 @
% 0.19/0.50             B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.19/0.50           ( ( v1_tops_2 @ B @ A ) <=>
% 0.19/0.50             ( ![C:$i]:
% 0.19/0.50               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.19/0.50                 ( ( r2_hidden @ C @ B ) => ( v3_pre_topc @ C @ A ) ) ) ) ) ) ) ))).
% 0.19/0.50  thf('17', plain,
% 0.19/0.50      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.19/0.50         (~ (m1_subset_1 @ X14 @ 
% 0.19/0.50             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15))))
% 0.19/0.50          | ~ (v1_tops_2 @ X14 @ X15)
% 0.19/0.50          | ~ (r2_hidden @ X16 @ X14)
% 0.19/0.50          | (v3_pre_topc @ X16 @ X15)
% 0.19/0.50          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.19/0.50          | ~ (l1_pre_topc @ X15))),
% 0.19/0.50      inference('cnf', [status(esa)], [d1_tops_2])).
% 0.19/0.50  thf('18', plain,
% 0.19/0.50      (![X0 : $i]:
% 0.19/0.50         (~ (l1_pre_topc @ sk_A)
% 0.19/0.50          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.19/0.50          | (v3_pre_topc @ X0 @ sk_A)
% 0.19/0.50          | ~ (r2_hidden @ X0 @ sk_B)
% 0.19/0.50          | ~ (v1_tops_2 @ sk_B @ sk_A))),
% 0.19/0.50      inference('sup-', [status(thm)], ['16', '17'])).
% 0.19/0.50  thf('19', plain, ((l1_pre_topc @ sk_A)),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('20', plain,
% 0.19/0.50      (![X0 : $i]:
% 0.19/0.50         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.19/0.50          | (v3_pre_topc @ X0 @ sk_A)
% 0.19/0.50          | ~ (r2_hidden @ X0 @ sk_B)
% 0.19/0.50          | ~ (v1_tops_2 @ sk_B @ sk_A))),
% 0.19/0.50      inference('demod', [status(thm)], ['18', '19'])).
% 0.19/0.50  thf('21', plain,
% 0.19/0.50      ((![X0 : $i]:
% 0.19/0.50          (~ (r2_hidden @ X0 @ sk_B)
% 0.19/0.50           | (v3_pre_topc @ X0 @ sk_A)
% 0.19/0.50           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))
% 0.19/0.50         <= (((v1_tops_2 @ sk_B @ sk_A)))),
% 0.19/0.50      inference('sup-', [status(thm)], ['15', '20'])).
% 0.19/0.50  thf('22', plain,
% 0.19/0.50      ((![X0 : $i]:
% 0.19/0.50          ((r1_tarski @ sk_B @ X0)
% 0.19/0.50           | (v3_pre_topc @ (sk_C @ X0 @ sk_B) @ sk_A)
% 0.19/0.50           | ~ (r2_hidden @ (sk_C @ X0 @ sk_B) @ sk_B)))
% 0.19/0.50         <= (((v1_tops_2 @ sk_B @ sk_A)))),
% 0.19/0.50      inference('sup-', [status(thm)], ['13', '21'])).
% 0.19/0.50  thf('23', plain,
% 0.19/0.50      (![X1 : $i, X3 : $i]:
% 0.19/0.50         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.19/0.50      inference('cnf', [status(esa)], [d3_tarski])).
% 0.19/0.50  thf('24', plain,
% 0.19/0.50      ((![X0 : $i]:
% 0.19/0.50          ((v3_pre_topc @ (sk_C @ X0 @ sk_B) @ sk_A) | (r1_tarski @ sk_B @ X0)))
% 0.19/0.50         <= (((v1_tops_2 @ sk_B @ sk_A)))),
% 0.19/0.50      inference('clc', [status(thm)], ['22', '23'])).
% 0.19/0.50  thf('25', plain,
% 0.19/0.50      (![X0 : $i]:
% 0.19/0.50         ((r1_tarski @ sk_B @ X0)
% 0.19/0.50          | (m1_subset_1 @ (sk_C @ X0 @ sk_B) @ 
% 0.19/0.50             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.19/0.50      inference('sup-', [status(thm)], ['11', '12'])).
% 0.19/0.50  thf(d5_pre_topc, axiom,
% 0.19/0.50    (![A:$i]:
% 0.19/0.50     ( ( l1_pre_topc @ A ) =>
% 0.19/0.50       ( ![B:$i]:
% 0.19/0.50         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.19/0.50           ( ( v3_pre_topc @ B @ A ) <=>
% 0.19/0.50             ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) ) ) ) ))).
% 0.19/0.50  thf('26', plain,
% 0.19/0.50      (![X12 : $i, X13 : $i]:
% 0.19/0.50         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.19/0.50          | ~ (v3_pre_topc @ X12 @ X13)
% 0.19/0.50          | (r2_hidden @ X12 @ (u1_pre_topc @ X13))
% 0.19/0.50          | ~ (l1_pre_topc @ X13))),
% 0.19/0.50      inference('cnf', [status(esa)], [d5_pre_topc])).
% 0.19/0.50  thf('27', plain,
% 0.19/0.50      (![X0 : $i]:
% 0.19/0.50         ((r1_tarski @ sk_B @ X0)
% 0.19/0.50          | ~ (l1_pre_topc @ sk_A)
% 0.19/0.50          | (r2_hidden @ (sk_C @ X0 @ sk_B) @ (u1_pre_topc @ sk_A))
% 0.19/0.50          | ~ (v3_pre_topc @ (sk_C @ X0 @ sk_B) @ sk_A))),
% 0.19/0.50      inference('sup-', [status(thm)], ['25', '26'])).
% 0.19/0.50  thf('28', plain, ((l1_pre_topc @ sk_A)),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('29', plain,
% 0.19/0.50      (![X0 : $i]:
% 0.19/0.50         ((r1_tarski @ sk_B @ X0)
% 0.19/0.50          | (r2_hidden @ (sk_C @ X0 @ sk_B) @ (u1_pre_topc @ sk_A))
% 0.19/0.50          | ~ (v3_pre_topc @ (sk_C @ X0 @ sk_B) @ sk_A))),
% 0.19/0.50      inference('demod', [status(thm)], ['27', '28'])).
% 0.19/0.50  thf('30', plain,
% 0.19/0.50      ((![X0 : $i]:
% 0.19/0.50          ((r1_tarski @ sk_B @ X0)
% 0.19/0.50           | (r2_hidden @ (sk_C @ X0 @ sk_B) @ (u1_pre_topc @ sk_A))
% 0.19/0.50           | (r1_tarski @ sk_B @ X0)))
% 0.19/0.50         <= (((v1_tops_2 @ sk_B @ sk_A)))),
% 0.19/0.50      inference('sup-', [status(thm)], ['24', '29'])).
% 0.19/0.50  thf('31', plain,
% 0.19/0.50      ((![X0 : $i]:
% 0.19/0.50          ((r2_hidden @ (sk_C @ X0 @ sk_B) @ (u1_pre_topc @ sk_A))
% 0.19/0.50           | (r1_tarski @ sk_B @ X0)))
% 0.19/0.50         <= (((v1_tops_2 @ sk_B @ sk_A)))),
% 0.19/0.50      inference('simplify', [status(thm)], ['30'])).
% 0.19/0.50  thf('32', plain,
% 0.19/0.50      (![X1 : $i, X3 : $i]:
% 0.19/0.50         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.19/0.50      inference('cnf', [status(esa)], [d3_tarski])).
% 0.19/0.50  thf('33', plain,
% 0.19/0.50      ((((r1_tarski @ sk_B @ (u1_pre_topc @ sk_A))
% 0.19/0.50         | (r1_tarski @ sk_B @ (u1_pre_topc @ sk_A))))
% 0.19/0.50         <= (((v1_tops_2 @ sk_B @ sk_A)))),
% 0.19/0.50      inference('sup-', [status(thm)], ['31', '32'])).
% 0.19/0.50  thf('34', plain,
% 0.19/0.50      (((r1_tarski @ sk_B @ (u1_pre_topc @ sk_A)))
% 0.19/0.50         <= (((v1_tops_2 @ sk_B @ sk_A)))),
% 0.19/0.50      inference('simplify', [status(thm)], ['33'])).
% 0.19/0.50  thf('35', plain,
% 0.19/0.50      ((~ (r1_tarski @ sk_B @ (u1_pre_topc @ sk_A)))
% 0.19/0.50         <= (~ ((r1_tarski @ sk_B @ (u1_pre_topc @ sk_A))))),
% 0.19/0.50      inference('split', [status(esa)], ['0'])).
% 0.19/0.50  thf('36', plain,
% 0.19/0.50      (((r1_tarski @ sk_B @ (u1_pre_topc @ sk_A))) | 
% 0.19/0.50       ~ ((v1_tops_2 @ sk_B @ sk_A))),
% 0.19/0.50      inference('sup-', [status(thm)], ['34', '35'])).
% 0.19/0.50  thf('37', plain,
% 0.19/0.50      (((r1_tarski @ sk_B @ (u1_pre_topc @ sk_A))) | 
% 0.19/0.50       ((v1_tops_2 @ sk_B @ sk_A))),
% 0.19/0.50      inference('split', [status(esa)], ['14'])).
% 0.19/0.50  thf('38', plain,
% 0.19/0.50      ((m1_subset_1 @ sk_B @ 
% 0.19/0.50        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('39', plain,
% 0.19/0.50      (![X14 : $i, X15 : $i]:
% 0.19/0.50         (~ (m1_subset_1 @ X14 @ 
% 0.19/0.50             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15))))
% 0.19/0.50          | (r2_hidden @ (sk_C_2 @ X14 @ X15) @ X14)
% 0.19/0.50          | (v1_tops_2 @ X14 @ X15)
% 0.19/0.50          | ~ (l1_pre_topc @ X15))),
% 0.19/0.50      inference('cnf', [status(esa)], [d1_tops_2])).
% 0.19/0.50  thf('40', plain,
% 0.19/0.50      ((~ (l1_pre_topc @ sk_A)
% 0.19/0.50        | (v1_tops_2 @ sk_B @ sk_A)
% 0.19/0.50        | (r2_hidden @ (sk_C_2 @ sk_B @ sk_A) @ sk_B))),
% 0.19/0.50      inference('sup-', [status(thm)], ['38', '39'])).
% 0.19/0.50  thf('41', plain, ((l1_pre_topc @ sk_A)),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('42', plain,
% 0.19/0.50      (((v1_tops_2 @ sk_B @ sk_A) | (r2_hidden @ (sk_C_2 @ sk_B @ sk_A) @ sk_B))),
% 0.19/0.50      inference('demod', [status(thm)], ['40', '41'])).
% 0.19/0.50  thf('43', plain,
% 0.19/0.50      (((r1_tarski @ sk_B @ (u1_pre_topc @ sk_A)))
% 0.19/0.50         <= (((r1_tarski @ sk_B @ (u1_pre_topc @ sk_A))))),
% 0.19/0.50      inference('split', [status(esa)], ['14'])).
% 0.19/0.50  thf('44', plain,
% 0.19/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.50         (~ (r2_hidden @ X0 @ X1)
% 0.19/0.50          | (r2_hidden @ X0 @ X2)
% 0.19/0.50          | ~ (r1_tarski @ X1 @ X2))),
% 0.19/0.50      inference('cnf', [status(esa)], [d3_tarski])).
% 0.19/0.50  thf('45', plain,
% 0.19/0.50      ((![X0 : $i]:
% 0.19/0.50          ((r2_hidden @ X0 @ (u1_pre_topc @ sk_A)) | ~ (r2_hidden @ X0 @ sk_B)))
% 0.19/0.50         <= (((r1_tarski @ sk_B @ (u1_pre_topc @ sk_A))))),
% 0.19/0.50      inference('sup-', [status(thm)], ['43', '44'])).
% 0.19/0.50  thf('46', plain,
% 0.19/0.50      ((((v1_tops_2 @ sk_B @ sk_A)
% 0.19/0.50         | (r2_hidden @ (sk_C_2 @ sk_B @ sk_A) @ (u1_pre_topc @ sk_A))))
% 0.19/0.50         <= (((r1_tarski @ sk_B @ (u1_pre_topc @ sk_A))))),
% 0.19/0.50      inference('sup-', [status(thm)], ['42', '45'])).
% 0.19/0.50  thf('47', plain,
% 0.19/0.50      (((v1_tops_2 @ sk_B @ sk_A) | (r2_hidden @ (sk_C_2 @ sk_B @ sk_A) @ sk_B))),
% 0.19/0.50      inference('demod', [status(thm)], ['40', '41'])).
% 0.19/0.50  thf('48', plain,
% 0.19/0.50      (![X0 : $i]:
% 0.19/0.50         ((r2_hidden @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.19/0.50          | ~ (r2_hidden @ X0 @ sk_B))),
% 0.19/0.50      inference('sup-', [status(thm)], ['5', '6'])).
% 0.19/0.50  thf('49', plain,
% 0.19/0.50      (((v1_tops_2 @ sk_B @ sk_A)
% 0.19/0.50        | (r2_hidden @ (sk_C_2 @ sk_B @ sk_A) @ 
% 0.19/0.50           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.19/0.50      inference('sup-', [status(thm)], ['47', '48'])).
% 0.19/0.50  thf('50', plain,
% 0.19/0.50      (![X5 : $i, X7 : $i]:
% 0.19/0.50         ((r1_tarski @ X7 @ X5) | ~ (r2_hidden @ X7 @ (k1_zfmisc_1 @ X5)))),
% 0.19/0.50      inference('simplify', [status(thm)], ['9'])).
% 0.19/0.50  thf('51', plain,
% 0.19/0.50      (((v1_tops_2 @ sk_B @ sk_A)
% 0.19/0.50        | (r1_tarski @ (sk_C_2 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 0.19/0.50      inference('sup-', [status(thm)], ['49', '50'])).
% 0.19/0.50  thf('52', plain,
% 0.19/0.50      (![X9 : $i, X11 : $i]:
% 0.19/0.50         ((m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X11)) | ~ (r1_tarski @ X9 @ X11))),
% 0.19/0.50      inference('cnf', [status(esa)], [t3_subset])).
% 0.19/0.50  thf('53', plain,
% 0.19/0.50      (((v1_tops_2 @ sk_B @ sk_A)
% 0.19/0.50        | (m1_subset_1 @ (sk_C_2 @ sk_B @ sk_A) @ 
% 0.19/0.50           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.19/0.50      inference('sup-', [status(thm)], ['51', '52'])).
% 0.19/0.50  thf('54', plain,
% 0.19/0.50      (![X12 : $i, X13 : $i]:
% 0.19/0.50         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.19/0.50          | ~ (r2_hidden @ X12 @ (u1_pre_topc @ X13))
% 0.19/0.50          | (v3_pre_topc @ X12 @ X13)
% 0.19/0.50          | ~ (l1_pre_topc @ X13))),
% 0.19/0.50      inference('cnf', [status(esa)], [d5_pre_topc])).
% 0.19/0.50  thf('55', plain,
% 0.19/0.50      (((v1_tops_2 @ sk_B @ sk_A)
% 0.19/0.50        | ~ (l1_pre_topc @ sk_A)
% 0.19/0.50        | (v3_pre_topc @ (sk_C_2 @ sk_B @ sk_A) @ sk_A)
% 0.19/0.50        | ~ (r2_hidden @ (sk_C_2 @ sk_B @ sk_A) @ (u1_pre_topc @ sk_A)))),
% 0.19/0.50      inference('sup-', [status(thm)], ['53', '54'])).
% 0.19/0.50  thf('56', plain, ((l1_pre_topc @ sk_A)),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('57', plain,
% 0.19/0.50      (((v1_tops_2 @ sk_B @ sk_A)
% 0.19/0.50        | (v3_pre_topc @ (sk_C_2 @ sk_B @ sk_A) @ sk_A)
% 0.19/0.50        | ~ (r2_hidden @ (sk_C_2 @ sk_B @ sk_A) @ (u1_pre_topc @ sk_A)))),
% 0.19/0.50      inference('demod', [status(thm)], ['55', '56'])).
% 0.19/0.50  thf('58', plain,
% 0.19/0.50      ((m1_subset_1 @ sk_B @ 
% 0.19/0.50        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('59', plain,
% 0.19/0.50      (![X14 : $i, X15 : $i]:
% 0.19/0.50         (~ (m1_subset_1 @ X14 @ 
% 0.19/0.50             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15))))
% 0.19/0.50          | ~ (v3_pre_topc @ (sk_C_2 @ X14 @ X15) @ X15)
% 0.19/0.50          | (v1_tops_2 @ X14 @ X15)
% 0.19/0.50          | ~ (l1_pre_topc @ X15))),
% 0.19/0.50      inference('cnf', [status(esa)], [d1_tops_2])).
% 0.19/0.50  thf('60', plain,
% 0.19/0.50      ((~ (l1_pre_topc @ sk_A)
% 0.19/0.50        | (v1_tops_2 @ sk_B @ sk_A)
% 0.19/0.50        | ~ (v3_pre_topc @ (sk_C_2 @ sk_B @ sk_A) @ sk_A))),
% 0.19/0.50      inference('sup-', [status(thm)], ['58', '59'])).
% 0.19/0.50  thf('61', plain, ((l1_pre_topc @ sk_A)),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('62', plain,
% 0.19/0.50      (((v1_tops_2 @ sk_B @ sk_A)
% 0.19/0.50        | ~ (v3_pre_topc @ (sk_C_2 @ sk_B @ sk_A) @ sk_A))),
% 0.19/0.50      inference('demod', [status(thm)], ['60', '61'])).
% 0.19/0.50  thf('63', plain,
% 0.19/0.50      ((~ (r2_hidden @ (sk_C_2 @ sk_B @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.19/0.50        | (v1_tops_2 @ sk_B @ sk_A))),
% 0.19/0.50      inference('clc', [status(thm)], ['57', '62'])).
% 0.19/0.50  thf('64', plain,
% 0.19/0.50      ((((v1_tops_2 @ sk_B @ sk_A) | (v1_tops_2 @ sk_B @ sk_A)))
% 0.19/0.50         <= (((r1_tarski @ sk_B @ (u1_pre_topc @ sk_A))))),
% 0.19/0.50      inference('sup-', [status(thm)], ['46', '63'])).
% 0.19/0.50  thf('65', plain,
% 0.19/0.50      (((v1_tops_2 @ sk_B @ sk_A))
% 0.19/0.50         <= (((r1_tarski @ sk_B @ (u1_pre_topc @ sk_A))))),
% 0.19/0.50      inference('simplify', [status(thm)], ['64'])).
% 0.19/0.50  thf('66', plain,
% 0.19/0.50      ((~ (v1_tops_2 @ sk_B @ sk_A)) <= (~ ((v1_tops_2 @ sk_B @ sk_A)))),
% 0.19/0.50      inference('split', [status(esa)], ['0'])).
% 0.19/0.50  thf('67', plain,
% 0.19/0.50      (~ ((r1_tarski @ sk_B @ (u1_pre_topc @ sk_A))) | 
% 0.19/0.50       ((v1_tops_2 @ sk_B @ sk_A))),
% 0.19/0.50      inference('sup-', [status(thm)], ['65', '66'])).
% 0.19/0.50  thf('68', plain, ($false),
% 0.19/0.50      inference('sat_resolution*', [status(thm)], ['1', '36', '37', '67'])).
% 0.19/0.50  
% 0.19/0.50  % SZS output end Refutation
% 0.19/0.50  
% 0.19/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
