%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.X7C0gngP0e

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:05:23 EST 2020

% Result     : Theorem 1.75s
% Output     : Refutation 1.75s
% Verified   : 
% Statistics : Number of formulae       :  126 ( 738 expanded)
%              Number of leaves         :   28 ( 216 expanded)
%              Depth                    :   24
%              Number of atoms          : 1096 (9440 expanded)
%              Number of equality atoms :   19 ( 262 expanded)
%              Maximal formula depth    :   16 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(v2_tops_2_type,type,(
    v2_tops_2: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(d3_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            | ( r2_hidden @ D @ B ) ) ) ) )).

thf('0',plain,(
    ! [X3: $i,X5: $i,X7: $i] :
      ( ( X7
        = ( k2_xboole_0 @ X5 @ X3 ) )
      | ( r2_hidden @ ( sk_D @ X7 @ X3 @ X5 ) @ X3 )
      | ( r2_hidden @ ( sk_D @ X7 @ X3 @ X5 ) @ X5 )
      | ( r2_hidden @ ( sk_D @ X7 @ X3 @ X5 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ X0 @ X0 ) @ X1 )
      | ( r2_hidden @ ( sk_D @ X1 @ X0 @ X0 ) @ X0 )
      | ( X1
        = ( k2_xboole_0 @ X0 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['0'])).

thf('2',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k2_xboole_0 @ X0 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ X0 @ X0 @ X0 ) @ X0 ) ) ),
    inference(eq_fact,[status(thm)],['1'])).

thf('3',plain,(
    ! [X3: $i,X5: $i,X7: $i] :
      ( ( X7
        = ( k2_xboole_0 @ X5 @ X3 ) )
      | ~ ( r2_hidden @ ( sk_D @ X7 @ X3 @ X5 ) @ X3 )
      | ~ ( r2_hidden @ ( sk_D @ X7 @ X3 @ X5 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k2_xboole_0 @ X0 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X0 ) @ X0 )
      | ( X0
        = ( k2_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X0 ) @ X0 )
      | ( X0
        = ( k2_xboole_0 @ X0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k2_xboole_0 @ X0 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ X0 @ X0 @ X0 ) @ X0 ) ) ),
    inference(eq_fact,[status(thm)],['1'])).

thf('7',plain,(
    ! [X0: $i] :
      ( X0
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference(clc,[status(thm)],['5','6'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('9',plain,(
    ! [X14: $i,X15: $i] :
      ( r1_tarski @ X14 @ ( k2_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup+',[status(thm)],['7','10'])).

thf(t43_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) )
     => ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ) )).

thf('12',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X8 @ X9 ) @ X10 )
      | ~ ( r1_tarski @ X8 @ ( k2_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t43_xboole_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 ) @ X0 ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf(t23_tops_2,conjecture,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
             => ( ( ( v2_tops_2 @ B @ A )
                  & ( v2_tops_2 @ C @ A ) )
               => ( v2_tops_2 @ ( k4_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) @ B @ C ) @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_pre_topc @ A )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
               => ( ( ( v2_tops_2 @ B @ A )
                    & ( v2_tops_2 @ C @ A ) )
                 => ( v2_tops_2 @ ( k4_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) @ B @ C ) @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t23_tops_2])).

thf('14',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_tops_2,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
         => ! [C: $i] :
              ( ( r1_tarski @ C @ B )
             => ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) )).

thf('15',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) ) )
      | ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) ) )
      | ~ ( r1_tarski @ X28 @ X26 )
      | ~ ( l1_struct_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t3_tops_2])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ sk_A )
      | ~ ( r1_tarski @ X0 @ sk_C_1 )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('18',plain,(
    ! [X22: $i] :
      ( ( l1_struct_0 @ X22 )
      | ~ ( l1_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('19',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_C_1 )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['16','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ sk_C_1 ) @ X0 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['13','20'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('22',plain,(
    ! [X19: $i,X20: $i] :
      ( ( r1_tarski @ X19 @ X20 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('23',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ sk_C_1 ) @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf(t44_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('24',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( r1_tarski @ X11 @ ( k2_xboole_0 @ X12 @ X13 ) )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ X11 @ X12 ) @ X13 ) ) ),
    inference(cnf,[status(esa)],[t44_xboole_1])).

thf('25',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ X0 @ sk_C_1 ) @ ( k2_xboole_0 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( X0
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference(clc,[status(thm)],['5','6'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 ) @ X0 ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('28',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) ) )
      | ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) ) )
      | ~ ( r1_tarski @ X28 @ X26 )
      | ~ ( l1_struct_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t3_tops_2])).

thf('30',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ sk_A )
      | ~ ( r1_tarski @ X0 @ sk_B )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['17','18'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_B )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ sk_B ) @ X0 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['27','32'])).

thf('34',plain,(
    ! [X19: $i,X20: $i] :
      ( ( r1_tarski @ X19 @ X20 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('35',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ sk_B ) @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( r1_tarski @ X11 @ ( k2_xboole_0 @ X12 @ X13 ) )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ X11 @ X12 ) @ X13 ) ) ),
    inference(cnf,[status(esa)],[t44_xboole_1])).

thf('37',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ X0 @ sk_B ) @ ( k2_xboole_0 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    r1_tarski @ ( k2_xboole_0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['26','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('40',plain,(
    r1_tarski @ ( k2_xboole_0 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X19: $i,X21: $i] :
      ( ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X21 ) )
      | ~ ( r1_tarski @ X19 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('42',plain,(
    m1_subset_1 @ ( k2_xboole_0 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) ) )
      | ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) ) )
      | ~ ( r1_tarski @ X28 @ X26 )
      | ~ ( l1_struct_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t3_tops_2])).

thf('44',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ sk_A )
      | ~ ( r1_tarski @ X0 @ ( k2_xboole_0 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['17','18'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k2_xboole_0 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,(
    m1_subset_1 @ ( k2_xboole_0 @ sk_B @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['25','46'])).

thf(d2_tops_2,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
         => ( ( v2_tops_2 @ B @ A )
          <=> ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
               => ( ( r2_hidden @ C @ B )
                 => ( v4_pre_topc @ C @ A ) ) ) ) ) ) )).

thf('48',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) ) )
      | ( m1_subset_1 @ ( sk_C @ X23 @ X24 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ( v2_tops_2 @ X23 @ X24 )
      | ~ ( l1_pre_topc @ X24 ) ) ),
    inference(cnf,[status(esa)],[d2_tops_2])).

thf('49',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v2_tops_2 @ ( k2_xboole_0 @ sk_B @ sk_C_1 ) @ sk_A )
    | ( m1_subset_1 @ ( sk_C @ ( k2_xboole_0 @ sk_B @ sk_C_1 ) @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,
    ( ( v2_tops_2 @ ( k2_xboole_0 @ sk_B @ sk_C_1 ) @ sk_A )
    | ( m1_subset_1 @ ( sk_C @ ( k2_xboole_0 @ sk_B @ sk_C_1 ) @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,(
    ~ ( v2_tops_2 @ ( k4_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B @ sk_C_1 ) @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('55',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X17 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X17 ) )
      | ( ( k4_subset_1 @ X17 @ X16 @ X18 )
        = ( k2_xboole_0 @ X16 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B @ X0 )
        = ( k2_xboole_0 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,
    ( ( k4_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B @ sk_C_1 )
    = ( k2_xboole_0 @ sk_B @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['53','56'])).

thf('58',plain,(
    ~ ( v2_tops_2 @ ( k2_xboole_0 @ sk_B @ sk_C_1 ) @ sk_A ) ),
    inference(demod,[status(thm)],['52','57'])).

thf('59',plain,(
    m1_subset_1 @ ( sk_C @ ( k2_xboole_0 @ sk_B @ sk_C_1 ) @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['51','58'])).

thf('60',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) ) )
      | ~ ( v2_tops_2 @ X23 @ X24 )
      | ~ ( r2_hidden @ X25 @ X23 )
      | ( v4_pre_topc @ X25 @ X24 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ~ ( l1_pre_topc @ X24 ) ) ),
    inference(cnf,[status(esa)],[d2_tops_2])).

thf('62',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v4_pre_topc @ X0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ sk_C_1 )
      | ~ ( v2_tops_2 @ sk_C_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    v2_tops_2 @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v4_pre_topc @ X0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['62','63','64'])).

thf('66',plain,
    ( ~ ( r2_hidden @ ( sk_C @ ( k2_xboole_0 @ sk_B @ sk_C_1 ) @ sk_A ) @ sk_C_1 )
    | ( v4_pre_topc @ ( sk_C @ ( k2_xboole_0 @ sk_B @ sk_C_1 ) @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['59','65'])).

thf('67',plain,(
    m1_subset_1 @ ( k2_xboole_0 @ sk_B @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['25','46'])).

thf('68',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) ) )
      | ~ ( v4_pre_topc @ ( sk_C @ X23 @ X24 ) @ X24 )
      | ( v2_tops_2 @ X23 @ X24 )
      | ~ ( l1_pre_topc @ X24 ) ) ),
    inference(cnf,[status(esa)],[d2_tops_2])).

thf('69',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v2_tops_2 @ ( k2_xboole_0 @ sk_B @ sk_C_1 ) @ sk_A )
    | ~ ( v4_pre_topc @ ( sk_C @ ( k2_xboole_0 @ sk_B @ sk_C_1 ) @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,
    ( ( v2_tops_2 @ ( k2_xboole_0 @ sk_B @ sk_C_1 ) @ sk_A )
    | ~ ( v4_pre_topc @ ( sk_C @ ( k2_xboole_0 @ sk_B @ sk_C_1 ) @ sk_A ) @ sk_A ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('72',plain,(
    ~ ( v2_tops_2 @ ( k2_xboole_0 @ sk_B @ sk_C_1 ) @ sk_A ) ),
    inference(demod,[status(thm)],['52','57'])).

thf('73',plain,(
    ~ ( v4_pre_topc @ ( sk_C @ ( k2_xboole_0 @ sk_B @ sk_C_1 ) @ sk_A ) @ sk_A ) ),
    inference(clc,[status(thm)],['71','72'])).

thf('74',plain,(
    ~ ( r2_hidden @ ( sk_C @ ( k2_xboole_0 @ sk_B @ sk_C_1 ) @ sk_A ) @ sk_C_1 ) ),
    inference(clc,[status(thm)],['66','73'])).

thf('75',plain,(
    m1_subset_1 @ ( k2_xboole_0 @ sk_B @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['25','46'])).

thf('76',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) ) )
      | ( r2_hidden @ ( sk_C @ X23 @ X24 ) @ X23 )
      | ( v2_tops_2 @ X23 @ X24 )
      | ~ ( l1_pre_topc @ X24 ) ) ),
    inference(cnf,[status(esa)],[d2_tops_2])).

thf('77',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v2_tops_2 @ ( k2_xboole_0 @ sk_B @ sk_C_1 ) @ sk_A )
    | ( r2_hidden @ ( sk_C @ ( k2_xboole_0 @ sk_B @ sk_C_1 ) @ sk_A ) @ ( k2_xboole_0 @ sk_B @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,
    ( ( v2_tops_2 @ ( k2_xboole_0 @ sk_B @ sk_C_1 ) @ sk_A )
    | ( r2_hidden @ ( sk_C @ ( k2_xboole_0 @ sk_B @ sk_C_1 ) @ sk_A ) @ ( k2_xboole_0 @ sk_B @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['77','78'])).

thf('80',plain,(
    ~ ( v2_tops_2 @ ( k2_xboole_0 @ sk_B @ sk_C_1 ) @ sk_A ) ),
    inference(demod,[status(thm)],['52','57'])).

thf('81',plain,(
    r2_hidden @ ( sk_C @ ( k2_xboole_0 @ sk_B @ sk_C_1 ) @ sk_A ) @ ( k2_xboole_0 @ sk_B @ sk_C_1 ) ),
    inference(clc,[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ( r2_hidden @ X6 @ X5 )
      | ( r2_hidden @ X6 @ X3 )
      | ( X4
       != ( k2_xboole_0 @ X5 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('83',plain,(
    ! [X3: $i,X5: $i,X6: $i] :
      ( ( r2_hidden @ X6 @ X3 )
      | ( r2_hidden @ X6 @ X5 )
      | ~ ( r2_hidden @ X6 @ ( k2_xboole_0 @ X5 @ X3 ) ) ) ),
    inference(simplify,[status(thm)],['82'])).

thf('84',plain,
    ( ( r2_hidden @ ( sk_C @ ( k2_xboole_0 @ sk_B @ sk_C_1 ) @ sk_A ) @ sk_B )
    | ( r2_hidden @ ( sk_C @ ( k2_xboole_0 @ sk_B @ sk_C_1 ) @ sk_A ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['81','83'])).

thf('85',plain,(
    m1_subset_1 @ ( sk_C @ ( k2_xboole_0 @ sk_B @ sk_C_1 ) @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['51','58'])).

thf('86',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) ) )
      | ~ ( v2_tops_2 @ X23 @ X24 )
      | ~ ( r2_hidden @ X25 @ X23 )
      | ( v4_pre_topc @ X25 @ X24 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ~ ( l1_pre_topc @ X24 ) ) ),
    inference(cnf,[status(esa)],[d2_tops_2])).

thf('88',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v4_pre_topc @ X0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ sk_B )
      | ~ ( v2_tops_2 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    v2_tops_2 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v4_pre_topc @ X0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['88','89','90'])).

thf('92',plain,
    ( ~ ( r2_hidden @ ( sk_C @ ( k2_xboole_0 @ sk_B @ sk_C_1 ) @ sk_A ) @ sk_B )
    | ( v4_pre_topc @ ( sk_C @ ( k2_xboole_0 @ sk_B @ sk_C_1 ) @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['85','91'])).

thf('93',plain,(
    ~ ( v4_pre_topc @ ( sk_C @ ( k2_xboole_0 @ sk_B @ sk_C_1 ) @ sk_A ) @ sk_A ) ),
    inference(clc,[status(thm)],['71','72'])).

thf('94',plain,(
    ~ ( r2_hidden @ ( sk_C @ ( k2_xboole_0 @ sk_B @ sk_C_1 ) @ sk_A ) @ sk_B ) ),
    inference(clc,[status(thm)],['92','93'])).

thf('95',plain,(
    r2_hidden @ ( sk_C @ ( k2_xboole_0 @ sk_B @ sk_C_1 ) @ sk_A ) @ sk_C_1 ),
    inference(clc,[status(thm)],['84','94'])).

thf('96',plain,(
    $false ),
    inference(demod,[status(thm)],['74','95'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.X7C0gngP0e
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 15:59:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 1.75/1.99  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.75/1.99  % Solved by: fo/fo7.sh
% 1.75/1.99  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.75/1.99  % done 1825 iterations in 1.527s
% 1.75/1.99  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.75/1.99  % SZS output start Refutation
% 1.75/1.99  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.75/1.99  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 1.75/1.99  thf(sk_B_type, type, sk_B: $i).
% 1.75/1.99  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 1.75/1.99  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 1.75/1.99  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.75/1.99  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 1.75/1.99  thf(sk_A_type, type, sk_A: $i).
% 1.75/1.99  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.75/1.99  thf(sk_C_1_type, type, sk_C_1: $i).
% 1.75/1.99  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 1.75/1.99  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 1.75/1.99  thf(v2_tops_2_type, type, v2_tops_2: $i > $i > $o).
% 1.75/1.99  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.75/1.99  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.75/1.99  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 1.75/1.99  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.75/1.99  thf(d3_xboole_0, axiom,
% 1.75/1.99    (![A:$i,B:$i,C:$i]:
% 1.75/1.99     ( ( ( C ) = ( k2_xboole_0 @ A @ B ) ) <=>
% 1.75/1.99       ( ![D:$i]:
% 1.75/1.99         ( ( r2_hidden @ D @ C ) <=>
% 1.75/1.99           ( ( r2_hidden @ D @ A ) | ( r2_hidden @ D @ B ) ) ) ) ))).
% 1.75/1.99  thf('0', plain,
% 1.75/1.99      (![X3 : $i, X5 : $i, X7 : $i]:
% 1.75/1.99         (((X7) = (k2_xboole_0 @ X5 @ X3))
% 1.75/1.99          | (r2_hidden @ (sk_D @ X7 @ X3 @ X5) @ X3)
% 1.75/1.99          | (r2_hidden @ (sk_D @ X7 @ X3 @ X5) @ X5)
% 1.75/1.99          | (r2_hidden @ (sk_D @ X7 @ X3 @ X5) @ X7))),
% 1.75/1.99      inference('cnf', [status(esa)], [d3_xboole_0])).
% 1.75/1.99  thf('1', plain,
% 1.75/1.99      (![X0 : $i, X1 : $i]:
% 1.75/1.99         ((r2_hidden @ (sk_D @ X1 @ X0 @ X0) @ X1)
% 1.75/1.99          | (r2_hidden @ (sk_D @ X1 @ X0 @ X0) @ X0)
% 1.75/1.99          | ((X1) = (k2_xboole_0 @ X0 @ X0)))),
% 1.75/1.99      inference('eq_fact', [status(thm)], ['0'])).
% 1.75/1.99  thf('2', plain,
% 1.75/1.99      (![X0 : $i]:
% 1.75/1.99         (((X0) = (k2_xboole_0 @ X0 @ X0))
% 1.75/1.99          | (r2_hidden @ (sk_D @ X0 @ X0 @ X0) @ X0))),
% 1.75/1.99      inference('eq_fact', [status(thm)], ['1'])).
% 1.75/1.99  thf('3', plain,
% 1.75/1.99      (![X3 : $i, X5 : $i, X7 : $i]:
% 1.75/1.99         (((X7) = (k2_xboole_0 @ X5 @ X3))
% 1.75/1.99          | ~ (r2_hidden @ (sk_D @ X7 @ X3 @ X5) @ X3)
% 1.75/1.99          | ~ (r2_hidden @ (sk_D @ X7 @ X3 @ X5) @ X7))),
% 1.75/1.99      inference('cnf', [status(esa)], [d3_xboole_0])).
% 1.75/1.99  thf('4', plain,
% 1.75/1.99      (![X0 : $i]:
% 1.75/1.99         (((X0) = (k2_xboole_0 @ X0 @ X0))
% 1.75/1.99          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X0) @ X0)
% 1.75/1.99          | ((X0) = (k2_xboole_0 @ X0 @ X0)))),
% 1.75/1.99      inference('sup-', [status(thm)], ['2', '3'])).
% 1.75/1.99  thf('5', plain,
% 1.75/1.99      (![X0 : $i]:
% 1.75/1.99         (~ (r2_hidden @ (sk_D @ X0 @ X0 @ X0) @ X0)
% 1.75/1.99          | ((X0) = (k2_xboole_0 @ X0 @ X0)))),
% 1.75/1.99      inference('simplify', [status(thm)], ['4'])).
% 1.75/1.99  thf('6', plain,
% 1.75/1.99      (![X0 : $i]:
% 1.75/1.99         (((X0) = (k2_xboole_0 @ X0 @ X0))
% 1.75/1.99          | (r2_hidden @ (sk_D @ X0 @ X0 @ X0) @ X0))),
% 1.75/1.99      inference('eq_fact', [status(thm)], ['1'])).
% 1.75/1.99  thf('7', plain, (![X0 : $i]: ((X0) = (k2_xboole_0 @ X0 @ X0))),
% 1.75/1.99      inference('clc', [status(thm)], ['5', '6'])).
% 1.75/1.99  thf(commutativity_k2_xboole_0, axiom,
% 1.75/1.99    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 1.75/1.99  thf('8', plain,
% 1.75/1.99      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.75/1.99      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 1.75/1.99  thf(t7_xboole_1, axiom,
% 1.75/1.99    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 1.75/1.99  thf('9', plain,
% 1.75/1.99      (![X14 : $i, X15 : $i]: (r1_tarski @ X14 @ (k2_xboole_0 @ X14 @ X15))),
% 1.75/1.99      inference('cnf', [status(esa)], [t7_xboole_1])).
% 1.75/1.99  thf('10', plain,
% 1.75/1.99      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 1.75/1.99      inference('sup+', [status(thm)], ['8', '9'])).
% 1.75/1.99  thf('11', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 1.75/1.99      inference('sup+', [status(thm)], ['7', '10'])).
% 1.75/1.99  thf(t43_xboole_1, axiom,
% 1.75/1.99    (![A:$i,B:$i,C:$i]:
% 1.75/1.99     ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) =>
% 1.75/1.99       ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ))).
% 1.75/1.99  thf('12', plain,
% 1.75/1.99      (![X8 : $i, X9 : $i, X10 : $i]:
% 1.75/1.99         ((r1_tarski @ (k4_xboole_0 @ X8 @ X9) @ X10)
% 1.75/1.99          | ~ (r1_tarski @ X8 @ (k2_xboole_0 @ X9 @ X10)))),
% 1.75/1.99      inference('cnf', [status(esa)], [t43_xboole_1])).
% 1.75/1.99  thf('13', plain,
% 1.75/1.99      (![X0 : $i, X1 : $i]:
% 1.75/1.99         (r1_tarski @ (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1) @ X0)),
% 1.75/1.99      inference('sup-', [status(thm)], ['11', '12'])).
% 1.75/1.99  thf(t23_tops_2, conjecture,
% 1.75/1.99    (![A:$i]:
% 1.75/1.99     ( ( l1_pre_topc @ A ) =>
% 1.75/1.99       ( ![B:$i]:
% 1.75/1.99         ( ( m1_subset_1 @
% 1.75/1.99             B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 1.75/1.99           ( ![C:$i]:
% 1.75/1.99             ( ( m1_subset_1 @
% 1.75/1.99                 C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 1.75/1.99               ( ( ( v2_tops_2 @ B @ A ) & ( v2_tops_2 @ C @ A ) ) =>
% 1.75/1.99                 ( v2_tops_2 @
% 1.75/1.99                   ( k4_subset_1 @
% 1.75/1.99                     ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) @ B @ C ) @ 
% 1.75/1.99                   A ) ) ) ) ) ) ))).
% 1.75/1.99  thf(zf_stmt_0, negated_conjecture,
% 1.75/1.99    (~( ![A:$i]:
% 1.75/1.99        ( ( l1_pre_topc @ A ) =>
% 1.75/1.99          ( ![B:$i]:
% 1.75/1.99            ( ( m1_subset_1 @
% 1.75/1.99                B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 1.75/1.99              ( ![C:$i]:
% 1.75/1.99                ( ( m1_subset_1 @
% 1.75/1.99                    C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 1.75/1.99                  ( ( ( v2_tops_2 @ B @ A ) & ( v2_tops_2 @ C @ A ) ) =>
% 1.75/1.99                    ( v2_tops_2 @
% 1.75/1.99                      ( k4_subset_1 @
% 1.75/1.99                        ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) @ B @ C ) @ 
% 1.75/1.99                      A ) ) ) ) ) ) ) )),
% 1.75/1.99    inference('cnf.neg', [status(esa)], [t23_tops_2])).
% 1.75/1.99  thf('14', plain,
% 1.75/1.99      ((m1_subset_1 @ sk_C_1 @ 
% 1.75/1.99        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 1.75/1.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.75/1.99  thf(t3_tops_2, axiom,
% 1.75/1.99    (![A:$i]:
% 1.75/1.99     ( ( l1_struct_0 @ A ) =>
% 1.75/1.99       ( ![B:$i]:
% 1.75/1.99         ( ( m1_subset_1 @
% 1.75/1.99             B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 1.75/1.99           ( ![C:$i]:
% 1.75/1.99             ( ( r1_tarski @ C @ B ) =>
% 1.75/1.99               ( m1_subset_1 @
% 1.75/1.99                 C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ) ))).
% 1.75/1.99  thf('15', plain,
% 1.75/1.99      (![X26 : $i, X27 : $i, X28 : $i]:
% 1.75/1.99         (~ (m1_subset_1 @ X26 @ 
% 1.75/1.99             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27))))
% 1.75/1.99          | (m1_subset_1 @ X28 @ 
% 1.75/1.99             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27))))
% 1.75/1.99          | ~ (r1_tarski @ X28 @ X26)
% 1.75/1.99          | ~ (l1_struct_0 @ X27))),
% 1.75/1.99      inference('cnf', [status(esa)], [t3_tops_2])).
% 1.75/1.99  thf('16', plain,
% 1.75/1.99      (![X0 : $i]:
% 1.75/1.99         (~ (l1_struct_0 @ sk_A)
% 1.75/1.99          | ~ (r1_tarski @ X0 @ sk_C_1)
% 1.75/1.99          | (m1_subset_1 @ X0 @ 
% 1.75/1.99             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 1.75/1.99      inference('sup-', [status(thm)], ['14', '15'])).
% 1.75/1.99  thf('17', plain, ((l1_pre_topc @ sk_A)),
% 1.75/1.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.75/1.99  thf(dt_l1_pre_topc, axiom,
% 1.75/1.99    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 1.75/1.99  thf('18', plain,
% 1.75/1.99      (![X22 : $i]: ((l1_struct_0 @ X22) | ~ (l1_pre_topc @ X22))),
% 1.75/1.99      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 1.75/1.99  thf('19', plain, ((l1_struct_0 @ sk_A)),
% 1.75/1.99      inference('sup-', [status(thm)], ['17', '18'])).
% 1.75/1.99  thf('20', plain,
% 1.75/1.99      (![X0 : $i]:
% 1.75/1.99         (~ (r1_tarski @ X0 @ sk_C_1)
% 1.75/1.99          | (m1_subset_1 @ X0 @ 
% 1.75/1.99             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 1.75/1.99      inference('demod', [status(thm)], ['16', '19'])).
% 1.75/1.99  thf('21', plain,
% 1.75/1.99      (![X0 : $i]:
% 1.75/1.99         (m1_subset_1 @ (k4_xboole_0 @ (k2_xboole_0 @ X0 @ sk_C_1) @ X0) @ 
% 1.75/1.99          (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 1.75/1.99      inference('sup-', [status(thm)], ['13', '20'])).
% 1.75/1.99  thf(t3_subset, axiom,
% 1.75/1.99    (![A:$i,B:$i]:
% 1.75/1.99     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 1.75/1.99  thf('22', plain,
% 1.75/1.99      (![X19 : $i, X20 : $i]:
% 1.75/1.99         ((r1_tarski @ X19 @ X20) | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ X20)))),
% 1.75/1.99      inference('cnf', [status(esa)], [t3_subset])).
% 1.75/1.99  thf('23', plain,
% 1.75/1.99      (![X0 : $i]:
% 1.75/1.99         (r1_tarski @ (k4_xboole_0 @ (k2_xboole_0 @ X0 @ sk_C_1) @ X0) @ 
% 1.75/1.99          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.75/1.99      inference('sup-', [status(thm)], ['21', '22'])).
% 1.75/1.99  thf(t44_xboole_1, axiom,
% 1.75/1.99    (![A:$i,B:$i,C:$i]:
% 1.75/1.99     ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) =>
% 1.75/1.99       ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 1.75/1.99  thf('24', plain,
% 1.75/1.99      (![X11 : $i, X12 : $i, X13 : $i]:
% 1.75/1.99         ((r1_tarski @ X11 @ (k2_xboole_0 @ X12 @ X13))
% 1.75/1.99          | ~ (r1_tarski @ (k4_xboole_0 @ X11 @ X12) @ X13))),
% 1.75/1.99      inference('cnf', [status(esa)], [t44_xboole_1])).
% 1.75/1.99  thf('25', plain,
% 1.75/1.99      (![X0 : $i]:
% 1.75/1.99         (r1_tarski @ (k2_xboole_0 @ X0 @ sk_C_1) @ 
% 1.75/1.99          (k2_xboole_0 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 1.75/1.99      inference('sup-', [status(thm)], ['23', '24'])).
% 1.75/1.99  thf('26', plain, (![X0 : $i]: ((X0) = (k2_xboole_0 @ X0 @ X0))),
% 1.75/1.99      inference('clc', [status(thm)], ['5', '6'])).
% 1.75/1.99  thf('27', plain,
% 1.75/1.99      (![X0 : $i, X1 : $i]:
% 1.75/1.99         (r1_tarski @ (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1) @ X0)),
% 1.75/1.99      inference('sup-', [status(thm)], ['11', '12'])).
% 1.75/1.99  thf('28', plain,
% 1.75/1.99      ((m1_subset_1 @ sk_B @ 
% 1.75/1.99        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 1.75/1.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.75/1.99  thf('29', plain,
% 1.75/1.99      (![X26 : $i, X27 : $i, X28 : $i]:
% 1.75/1.99         (~ (m1_subset_1 @ X26 @ 
% 1.75/1.99             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27))))
% 1.75/1.99          | (m1_subset_1 @ X28 @ 
% 1.75/1.99             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27))))
% 1.75/1.99          | ~ (r1_tarski @ X28 @ X26)
% 1.75/1.99          | ~ (l1_struct_0 @ X27))),
% 1.75/1.99      inference('cnf', [status(esa)], [t3_tops_2])).
% 1.75/1.99  thf('30', plain,
% 1.75/1.99      (![X0 : $i]:
% 1.75/1.99         (~ (l1_struct_0 @ sk_A)
% 1.75/1.99          | ~ (r1_tarski @ X0 @ sk_B)
% 1.75/1.99          | (m1_subset_1 @ X0 @ 
% 1.75/1.99             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 1.75/1.99      inference('sup-', [status(thm)], ['28', '29'])).
% 1.75/1.99  thf('31', plain, ((l1_struct_0 @ sk_A)),
% 1.75/1.99      inference('sup-', [status(thm)], ['17', '18'])).
% 1.75/1.99  thf('32', plain,
% 1.75/1.99      (![X0 : $i]:
% 1.75/1.99         (~ (r1_tarski @ X0 @ sk_B)
% 1.75/1.99          | (m1_subset_1 @ X0 @ 
% 1.75/1.99             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 1.75/1.99      inference('demod', [status(thm)], ['30', '31'])).
% 1.75/1.99  thf('33', plain,
% 1.75/1.99      (![X0 : $i]:
% 1.75/1.99         (m1_subset_1 @ (k4_xboole_0 @ (k2_xboole_0 @ X0 @ sk_B) @ X0) @ 
% 1.75/1.99          (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 1.75/1.99      inference('sup-', [status(thm)], ['27', '32'])).
% 1.75/1.99  thf('34', plain,
% 1.75/1.99      (![X19 : $i, X20 : $i]:
% 1.75/1.99         ((r1_tarski @ X19 @ X20) | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ X20)))),
% 1.75/1.99      inference('cnf', [status(esa)], [t3_subset])).
% 1.75/1.99  thf('35', plain,
% 1.75/1.99      (![X0 : $i]:
% 1.75/1.99         (r1_tarski @ (k4_xboole_0 @ (k2_xboole_0 @ X0 @ sk_B) @ X0) @ 
% 1.75/1.99          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.75/1.99      inference('sup-', [status(thm)], ['33', '34'])).
% 1.75/1.99  thf('36', plain,
% 1.75/1.99      (![X11 : $i, X12 : $i, X13 : $i]:
% 1.75/1.99         ((r1_tarski @ X11 @ (k2_xboole_0 @ X12 @ X13))
% 1.75/1.99          | ~ (r1_tarski @ (k4_xboole_0 @ X11 @ X12) @ X13))),
% 1.75/1.99      inference('cnf', [status(esa)], [t44_xboole_1])).
% 1.75/1.99  thf('37', plain,
% 1.75/1.99      (![X0 : $i]:
% 1.75/1.99         (r1_tarski @ (k2_xboole_0 @ X0 @ sk_B) @ 
% 1.75/1.99          (k2_xboole_0 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 1.75/1.99      inference('sup-', [status(thm)], ['35', '36'])).
% 1.75/1.99  thf('38', plain,
% 1.75/1.99      ((r1_tarski @ 
% 1.75/1.99        (k2_xboole_0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ sk_B) @ 
% 1.75/1.99        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.75/1.99      inference('sup+', [status(thm)], ['26', '37'])).
% 1.75/1.99  thf('39', plain,
% 1.75/1.99      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.75/1.99      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 1.75/1.99  thf('40', plain,
% 1.75/1.99      ((r1_tarski @ 
% 1.75/1.99        (k2_xboole_0 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))) @ 
% 1.75/1.99        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.75/1.99      inference('demod', [status(thm)], ['38', '39'])).
% 1.75/1.99  thf('41', plain,
% 1.75/1.99      (![X19 : $i, X21 : $i]:
% 1.75/1.99         ((m1_subset_1 @ X19 @ (k1_zfmisc_1 @ X21)) | ~ (r1_tarski @ X19 @ X21))),
% 1.75/1.99      inference('cnf', [status(esa)], [t3_subset])).
% 1.75/1.99  thf('42', plain,
% 1.75/1.99      ((m1_subset_1 @ 
% 1.75/1.99        (k2_xboole_0 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))) @ 
% 1.75/1.99        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 1.75/1.99      inference('sup-', [status(thm)], ['40', '41'])).
% 1.75/1.99  thf('43', plain,
% 1.75/1.99      (![X26 : $i, X27 : $i, X28 : $i]:
% 1.75/1.99         (~ (m1_subset_1 @ X26 @ 
% 1.75/1.99             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27))))
% 1.75/1.99          | (m1_subset_1 @ X28 @ 
% 1.75/1.99             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27))))
% 1.75/1.99          | ~ (r1_tarski @ X28 @ X26)
% 1.75/1.99          | ~ (l1_struct_0 @ X27))),
% 1.75/1.99      inference('cnf', [status(esa)], [t3_tops_2])).
% 1.75/1.99  thf('44', plain,
% 1.75/1.99      (![X0 : $i]:
% 1.75/1.99         (~ (l1_struct_0 @ sk_A)
% 1.75/1.99          | ~ (r1_tarski @ X0 @ 
% 1.75/1.99               (k2_xboole_0 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 1.75/1.99          | (m1_subset_1 @ X0 @ 
% 1.75/1.99             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 1.75/1.99      inference('sup-', [status(thm)], ['42', '43'])).
% 1.75/1.99  thf('45', plain, ((l1_struct_0 @ sk_A)),
% 1.75/1.99      inference('sup-', [status(thm)], ['17', '18'])).
% 1.75/1.99  thf('46', plain,
% 1.75/1.99      (![X0 : $i]:
% 1.75/1.99         (~ (r1_tarski @ X0 @ 
% 1.75/1.99             (k2_xboole_0 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 1.75/1.99          | (m1_subset_1 @ X0 @ 
% 1.75/1.99             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 1.75/1.99      inference('demod', [status(thm)], ['44', '45'])).
% 1.75/1.99  thf('47', plain,
% 1.75/1.99      ((m1_subset_1 @ (k2_xboole_0 @ sk_B @ sk_C_1) @ 
% 1.75/1.99        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 1.75/1.99      inference('sup-', [status(thm)], ['25', '46'])).
% 1.75/1.99  thf(d2_tops_2, axiom,
% 1.75/1.99    (![A:$i]:
% 1.75/1.99     ( ( l1_pre_topc @ A ) =>
% 1.75/1.99       ( ![B:$i]:
% 1.75/1.99         ( ( m1_subset_1 @
% 1.75/1.99             B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 1.75/1.99           ( ( v2_tops_2 @ B @ A ) <=>
% 1.75/1.99             ( ![C:$i]:
% 1.75/1.99               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.75/1.99                 ( ( r2_hidden @ C @ B ) => ( v4_pre_topc @ C @ A ) ) ) ) ) ) ) ))).
% 1.75/1.99  thf('48', plain,
% 1.75/1.99      (![X23 : $i, X24 : $i]:
% 1.75/1.99         (~ (m1_subset_1 @ X23 @ 
% 1.75/1.99             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24))))
% 1.75/1.99          | (m1_subset_1 @ (sk_C @ X23 @ X24) @ 
% 1.75/1.99             (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 1.75/1.99          | (v2_tops_2 @ X23 @ X24)
% 1.75/1.99          | ~ (l1_pre_topc @ X24))),
% 1.75/1.99      inference('cnf', [status(esa)], [d2_tops_2])).
% 1.75/1.99  thf('49', plain,
% 1.75/1.99      ((~ (l1_pre_topc @ sk_A)
% 1.75/1.99        | (v2_tops_2 @ (k2_xboole_0 @ sk_B @ sk_C_1) @ sk_A)
% 1.75/1.99        | (m1_subset_1 @ (sk_C @ (k2_xboole_0 @ sk_B @ sk_C_1) @ sk_A) @ 
% 1.75/1.99           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 1.75/1.99      inference('sup-', [status(thm)], ['47', '48'])).
% 1.75/1.99  thf('50', plain, ((l1_pre_topc @ sk_A)),
% 1.75/1.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.75/1.99  thf('51', plain,
% 1.75/1.99      (((v2_tops_2 @ (k2_xboole_0 @ sk_B @ sk_C_1) @ sk_A)
% 1.75/1.99        | (m1_subset_1 @ (sk_C @ (k2_xboole_0 @ sk_B @ sk_C_1) @ sk_A) @ 
% 1.75/1.99           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 1.75/1.99      inference('demod', [status(thm)], ['49', '50'])).
% 1.75/1.99  thf('52', plain,
% 1.75/1.99      (~ (v2_tops_2 @ 
% 1.75/1.99          (k4_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ sk_B @ sk_C_1) @ 
% 1.75/1.99          sk_A)),
% 1.75/1.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.75/1.99  thf('53', plain,
% 1.75/1.99      ((m1_subset_1 @ sk_C_1 @ 
% 1.75/1.99        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 1.75/1.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.75/1.99  thf('54', plain,
% 1.75/1.99      ((m1_subset_1 @ sk_B @ 
% 1.75/1.99        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 1.75/1.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.75/1.99  thf(redefinition_k4_subset_1, axiom,
% 1.75/1.99    (![A:$i,B:$i,C:$i]:
% 1.75/1.99     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 1.75/1.99         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 1.75/1.99       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 1.75/1.99  thf('55', plain,
% 1.75/1.99      (![X16 : $i, X17 : $i, X18 : $i]:
% 1.75/1.99         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X17))
% 1.75/1.99          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X17))
% 1.75/1.99          | ((k4_subset_1 @ X17 @ X16 @ X18) = (k2_xboole_0 @ X16 @ X18)))),
% 1.75/1.99      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 1.75/1.99  thf('56', plain,
% 1.75/1.99      (![X0 : $i]:
% 1.75/1.99         (((k4_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ sk_B @ X0)
% 1.75/1.99            = (k2_xboole_0 @ sk_B @ X0))
% 1.75/1.99          | ~ (m1_subset_1 @ X0 @ 
% 1.75/1.99               (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 1.75/1.99      inference('sup-', [status(thm)], ['54', '55'])).
% 1.75/1.99  thf('57', plain,
% 1.75/1.99      (((k4_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ sk_B @ sk_C_1)
% 1.75/1.99         = (k2_xboole_0 @ sk_B @ sk_C_1))),
% 1.75/1.99      inference('sup-', [status(thm)], ['53', '56'])).
% 1.75/1.99  thf('58', plain, (~ (v2_tops_2 @ (k2_xboole_0 @ sk_B @ sk_C_1) @ sk_A)),
% 1.75/1.99      inference('demod', [status(thm)], ['52', '57'])).
% 1.75/1.99  thf('59', plain,
% 1.75/1.99      ((m1_subset_1 @ (sk_C @ (k2_xboole_0 @ sk_B @ sk_C_1) @ sk_A) @ 
% 1.75/1.99        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.75/1.99      inference('clc', [status(thm)], ['51', '58'])).
% 1.75/1.99  thf('60', plain,
% 1.75/1.99      ((m1_subset_1 @ sk_C_1 @ 
% 1.75/1.99        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 1.75/1.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.75/1.99  thf('61', plain,
% 1.75/1.99      (![X23 : $i, X24 : $i, X25 : $i]:
% 1.75/1.99         (~ (m1_subset_1 @ X23 @ 
% 1.75/1.99             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24))))
% 1.75/1.99          | ~ (v2_tops_2 @ X23 @ X24)
% 1.75/1.99          | ~ (r2_hidden @ X25 @ X23)
% 1.75/1.99          | (v4_pre_topc @ X25 @ X24)
% 1.75/1.99          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 1.75/1.99          | ~ (l1_pre_topc @ X24))),
% 1.75/1.99      inference('cnf', [status(esa)], [d2_tops_2])).
% 1.75/1.99  thf('62', plain,
% 1.75/1.99      (![X0 : $i]:
% 1.75/1.99         (~ (l1_pre_topc @ sk_A)
% 1.75/1.99          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.75/1.99          | (v4_pre_topc @ X0 @ sk_A)
% 1.75/1.99          | ~ (r2_hidden @ X0 @ sk_C_1)
% 1.75/1.99          | ~ (v2_tops_2 @ sk_C_1 @ sk_A))),
% 1.75/1.99      inference('sup-', [status(thm)], ['60', '61'])).
% 1.75/1.99  thf('63', plain, ((l1_pre_topc @ sk_A)),
% 1.75/1.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.75/1.99  thf('64', plain, ((v2_tops_2 @ sk_C_1 @ sk_A)),
% 1.75/1.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.75/1.99  thf('65', plain,
% 1.75/1.99      (![X0 : $i]:
% 1.75/1.99         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.75/1.99          | (v4_pre_topc @ X0 @ sk_A)
% 1.75/1.99          | ~ (r2_hidden @ X0 @ sk_C_1))),
% 1.75/1.99      inference('demod', [status(thm)], ['62', '63', '64'])).
% 1.75/1.99  thf('66', plain,
% 1.75/1.99      ((~ (r2_hidden @ (sk_C @ (k2_xboole_0 @ sk_B @ sk_C_1) @ sk_A) @ sk_C_1)
% 1.75/1.99        | (v4_pre_topc @ (sk_C @ (k2_xboole_0 @ sk_B @ sk_C_1) @ sk_A) @ sk_A))),
% 1.75/1.99      inference('sup-', [status(thm)], ['59', '65'])).
% 1.75/1.99  thf('67', plain,
% 1.75/1.99      ((m1_subset_1 @ (k2_xboole_0 @ sk_B @ sk_C_1) @ 
% 1.75/1.99        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 1.75/1.99      inference('sup-', [status(thm)], ['25', '46'])).
% 1.75/1.99  thf('68', plain,
% 1.75/1.99      (![X23 : $i, X24 : $i]:
% 1.75/1.99         (~ (m1_subset_1 @ X23 @ 
% 1.75/1.99             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24))))
% 1.75/1.99          | ~ (v4_pre_topc @ (sk_C @ X23 @ X24) @ X24)
% 1.75/1.99          | (v2_tops_2 @ X23 @ X24)
% 1.75/1.99          | ~ (l1_pre_topc @ X24))),
% 1.75/1.99      inference('cnf', [status(esa)], [d2_tops_2])).
% 1.75/1.99  thf('69', plain,
% 1.75/1.99      ((~ (l1_pre_topc @ sk_A)
% 1.75/1.99        | (v2_tops_2 @ (k2_xboole_0 @ sk_B @ sk_C_1) @ sk_A)
% 1.75/1.99        | ~ (v4_pre_topc @ (sk_C @ (k2_xboole_0 @ sk_B @ sk_C_1) @ sk_A) @ sk_A))),
% 1.75/1.99      inference('sup-', [status(thm)], ['67', '68'])).
% 1.75/1.99  thf('70', plain, ((l1_pre_topc @ sk_A)),
% 1.75/1.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.75/1.99  thf('71', plain,
% 1.75/1.99      (((v2_tops_2 @ (k2_xboole_0 @ sk_B @ sk_C_1) @ sk_A)
% 1.75/1.99        | ~ (v4_pre_topc @ (sk_C @ (k2_xboole_0 @ sk_B @ sk_C_1) @ sk_A) @ sk_A))),
% 1.75/1.99      inference('demod', [status(thm)], ['69', '70'])).
% 1.75/1.99  thf('72', plain, (~ (v2_tops_2 @ (k2_xboole_0 @ sk_B @ sk_C_1) @ sk_A)),
% 1.75/1.99      inference('demod', [status(thm)], ['52', '57'])).
% 1.75/1.99  thf('73', plain,
% 1.75/1.99      (~ (v4_pre_topc @ (sk_C @ (k2_xboole_0 @ sk_B @ sk_C_1) @ sk_A) @ sk_A)),
% 1.75/1.99      inference('clc', [status(thm)], ['71', '72'])).
% 1.75/1.99  thf('74', plain,
% 1.75/1.99      (~ (r2_hidden @ (sk_C @ (k2_xboole_0 @ sk_B @ sk_C_1) @ sk_A) @ sk_C_1)),
% 1.75/1.99      inference('clc', [status(thm)], ['66', '73'])).
% 1.75/1.99  thf('75', plain,
% 1.75/1.99      ((m1_subset_1 @ (k2_xboole_0 @ sk_B @ sk_C_1) @ 
% 1.75/1.99        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 1.75/1.99      inference('sup-', [status(thm)], ['25', '46'])).
% 1.75/1.99  thf('76', plain,
% 1.75/1.99      (![X23 : $i, X24 : $i]:
% 1.75/1.99         (~ (m1_subset_1 @ X23 @ 
% 1.75/1.99             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24))))
% 1.75/1.99          | (r2_hidden @ (sk_C @ X23 @ X24) @ X23)
% 1.75/1.99          | (v2_tops_2 @ X23 @ X24)
% 1.75/1.99          | ~ (l1_pre_topc @ X24))),
% 1.75/1.99      inference('cnf', [status(esa)], [d2_tops_2])).
% 1.75/1.99  thf('77', plain,
% 1.75/1.99      ((~ (l1_pre_topc @ sk_A)
% 1.75/1.99        | (v2_tops_2 @ (k2_xboole_0 @ sk_B @ sk_C_1) @ sk_A)
% 1.75/1.99        | (r2_hidden @ (sk_C @ (k2_xboole_0 @ sk_B @ sk_C_1) @ sk_A) @ 
% 1.75/1.99           (k2_xboole_0 @ sk_B @ sk_C_1)))),
% 1.75/1.99      inference('sup-', [status(thm)], ['75', '76'])).
% 1.75/1.99  thf('78', plain, ((l1_pre_topc @ sk_A)),
% 1.75/1.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.75/1.99  thf('79', plain,
% 1.75/1.99      (((v2_tops_2 @ (k2_xboole_0 @ sk_B @ sk_C_1) @ sk_A)
% 1.75/1.99        | (r2_hidden @ (sk_C @ (k2_xboole_0 @ sk_B @ sk_C_1) @ sk_A) @ 
% 1.75/1.99           (k2_xboole_0 @ sk_B @ sk_C_1)))),
% 1.75/1.99      inference('demod', [status(thm)], ['77', '78'])).
% 1.75/1.99  thf('80', plain, (~ (v2_tops_2 @ (k2_xboole_0 @ sk_B @ sk_C_1) @ sk_A)),
% 1.75/1.99      inference('demod', [status(thm)], ['52', '57'])).
% 1.75/1.99  thf('81', plain,
% 1.75/1.99      ((r2_hidden @ (sk_C @ (k2_xboole_0 @ sk_B @ sk_C_1) @ sk_A) @ 
% 1.75/1.99        (k2_xboole_0 @ sk_B @ sk_C_1))),
% 1.75/1.99      inference('clc', [status(thm)], ['79', '80'])).
% 1.75/1.99  thf('82', plain,
% 1.75/1.99      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 1.75/1.99         (~ (r2_hidden @ X6 @ X4)
% 1.75/1.99          | (r2_hidden @ X6 @ X5)
% 1.75/1.99          | (r2_hidden @ X6 @ X3)
% 1.75/1.99          | ((X4) != (k2_xboole_0 @ X5 @ X3)))),
% 1.75/1.99      inference('cnf', [status(esa)], [d3_xboole_0])).
% 1.75/1.99  thf('83', plain,
% 1.75/1.99      (![X3 : $i, X5 : $i, X6 : $i]:
% 1.75/1.99         ((r2_hidden @ X6 @ X3)
% 1.75/1.99          | (r2_hidden @ X6 @ X5)
% 1.75/1.99          | ~ (r2_hidden @ X6 @ (k2_xboole_0 @ X5 @ X3)))),
% 1.75/1.99      inference('simplify', [status(thm)], ['82'])).
% 1.75/1.99  thf('84', plain,
% 1.75/1.99      (((r2_hidden @ (sk_C @ (k2_xboole_0 @ sk_B @ sk_C_1) @ sk_A) @ sk_B)
% 1.75/1.99        | (r2_hidden @ (sk_C @ (k2_xboole_0 @ sk_B @ sk_C_1) @ sk_A) @ sk_C_1))),
% 1.75/1.99      inference('sup-', [status(thm)], ['81', '83'])).
% 1.75/1.99  thf('85', plain,
% 1.75/1.99      ((m1_subset_1 @ (sk_C @ (k2_xboole_0 @ sk_B @ sk_C_1) @ sk_A) @ 
% 1.75/1.99        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.75/1.99      inference('clc', [status(thm)], ['51', '58'])).
% 1.75/1.99  thf('86', plain,
% 1.75/1.99      ((m1_subset_1 @ sk_B @ 
% 1.75/1.99        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 1.75/1.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.75/1.99  thf('87', plain,
% 1.75/1.99      (![X23 : $i, X24 : $i, X25 : $i]:
% 1.75/1.99         (~ (m1_subset_1 @ X23 @ 
% 1.75/1.99             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24))))
% 1.75/1.99          | ~ (v2_tops_2 @ X23 @ X24)
% 1.75/1.99          | ~ (r2_hidden @ X25 @ X23)
% 1.75/1.99          | (v4_pre_topc @ X25 @ X24)
% 1.75/1.99          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 1.75/1.99          | ~ (l1_pre_topc @ X24))),
% 1.75/1.99      inference('cnf', [status(esa)], [d2_tops_2])).
% 1.75/1.99  thf('88', plain,
% 1.75/1.99      (![X0 : $i]:
% 1.75/1.99         (~ (l1_pre_topc @ sk_A)
% 1.75/1.99          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.75/1.99          | (v4_pre_topc @ X0 @ sk_A)
% 1.75/1.99          | ~ (r2_hidden @ X0 @ sk_B)
% 1.75/1.99          | ~ (v2_tops_2 @ sk_B @ sk_A))),
% 1.75/1.99      inference('sup-', [status(thm)], ['86', '87'])).
% 1.75/1.99  thf('89', plain, ((l1_pre_topc @ sk_A)),
% 1.75/1.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.75/1.99  thf('90', plain, ((v2_tops_2 @ sk_B @ sk_A)),
% 1.75/1.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.75/1.99  thf('91', plain,
% 1.75/1.99      (![X0 : $i]:
% 1.75/1.99         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.75/1.99          | (v4_pre_topc @ X0 @ sk_A)
% 1.75/1.99          | ~ (r2_hidden @ X0 @ sk_B))),
% 1.75/1.99      inference('demod', [status(thm)], ['88', '89', '90'])).
% 1.75/1.99  thf('92', plain,
% 1.75/1.99      ((~ (r2_hidden @ (sk_C @ (k2_xboole_0 @ sk_B @ sk_C_1) @ sk_A) @ sk_B)
% 1.75/1.99        | (v4_pre_topc @ (sk_C @ (k2_xboole_0 @ sk_B @ sk_C_1) @ sk_A) @ sk_A))),
% 1.75/1.99      inference('sup-', [status(thm)], ['85', '91'])).
% 1.75/1.99  thf('93', plain,
% 1.75/1.99      (~ (v4_pre_topc @ (sk_C @ (k2_xboole_0 @ sk_B @ sk_C_1) @ sk_A) @ sk_A)),
% 1.75/1.99      inference('clc', [status(thm)], ['71', '72'])).
% 1.75/1.99  thf('94', plain,
% 1.75/1.99      (~ (r2_hidden @ (sk_C @ (k2_xboole_0 @ sk_B @ sk_C_1) @ sk_A) @ sk_B)),
% 1.75/1.99      inference('clc', [status(thm)], ['92', '93'])).
% 1.75/1.99  thf('95', plain,
% 1.75/1.99      ((r2_hidden @ (sk_C @ (k2_xboole_0 @ sk_B @ sk_C_1) @ sk_A) @ sk_C_1)),
% 1.75/1.99      inference('clc', [status(thm)], ['84', '94'])).
% 1.75/1.99  thf('96', plain, ($false), inference('demod', [status(thm)], ['74', '95'])).
% 1.75/1.99  
% 1.75/1.99  % SZS output end Refutation
% 1.75/1.99  
% 1.86/2.00  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
