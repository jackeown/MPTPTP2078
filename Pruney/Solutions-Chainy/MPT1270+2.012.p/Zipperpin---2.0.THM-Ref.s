%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.aVa0BUqJAu

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:04:27 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  135 ( 387 expanded)
%              Number of leaves         :   32 ( 123 expanded)
%              Depth                    :   21
%              Number of atoms          :  948 (3218 expanded)
%              Number of equality atoms :   46 ( 132 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(v2_tops_1_type,type,(
    v2_tops_1: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(t88_tops_1,conjecture,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v2_tops_1 @ B @ A )
          <=> ( r1_tarski @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_pre_topc @ A )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( ( v2_tops_1 @ B @ A )
            <=> ( r1_tarski @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t88_tops_1])).

thf('0',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ~ ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('3',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t73_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_xboole_0 @ ( k1_tops_1 @ A @ B ) @ ( k2_tops_1 @ A @ B ) ) ) ) )).

thf('4',plain,(
    ! [X34: $i,X35: $i] :
      ( ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X35 ) ) )
      | ( r1_xboole_0 @ ( k1_tops_1 @ X35 @ X34 ) @ ( k2_tops_1 @ X35 @ X34 ) )
      | ~ ( l1_pre_topc @ X35 ) ) ),
    inference(cnf,[status(esa)],[t73_tops_1])).

thf('5',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    r1_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['5','6'])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('8',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k4_xboole_0 @ X6 @ X7 )
        = X6 )
      | ~ ( r1_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('9',plain,
    ( ( k4_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = ( k1_tops_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,
    ( ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
    | ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['10'])).

thf(t85_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_xboole_0 @ A @ ( k4_xboole_0 @ C @ B ) ) ) )).

thf('12',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( r1_tarski @ X9 @ X10 )
      | ( r1_xboole_0 @ X9 @ ( k4_xboole_0 @ X11 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t85_xboole_1])).

thf('13',plain,
    ( ! [X0: $i] :
        ( r1_xboole_0 @ sk_B @ ( k4_xboole_0 @ X0 @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,
    ( ( r1_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
   <= ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['9','13'])).

thf('15',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t44_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) )).

thf('16',plain,(
    ! [X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X33 ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ X33 @ X32 ) @ X32 )
      | ~ ( l1_pre_topc @ X33 ) ) ),
    inference(cnf,[status(esa)],[t44_tops_1])).

thf('17',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B ),
    inference(demod,[status(thm)],['17','18'])).

thf(t63_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ B @ C ) )
     => ( r1_xboole_0 @ A @ C ) ) )).

thf('20',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ~ ( r1_xboole_0 @ X4 @ X5 )
      | ( r1_xboole_0 @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t63_xboole_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ X0 )
      | ~ ( r1_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,
    ( ( r1_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) )
   <= ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['14','21'])).

thf('23',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k4_xboole_0 @ X6 @ X7 )
        = X6 )
      | ~ ( r1_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('24',plain,
    ( ( ( k4_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) )
      = ( k1_tops_1 @ sk_A @ sk_B ) )
   <= ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('26',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['25'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('27',plain,(
    ! [X20: $i,X22: $i] :
      ( ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X22 ) )
      | ~ ( r1_tarski @ X20 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('28',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('29',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k3_subset_1 @ X12 @ X13 )
        = ( k4_xboole_0 @ X12 @ X13 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('31',plain,(
    ! [X19: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('32',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k3_subset_1 @ X15 @ ( k3_subset_1 @ X15 @ X14 ) )
        = X14 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ ( k3_subset_1 @ X0 @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('35',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['25'])).

thf('36',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( r1_tarski @ X9 @ X10 )
      | ( r1_xboole_0 @ X9 @ ( k4_xboole_0 @ X11 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t85_xboole_1])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k4_xboole_0 @ X6 @ X7 )
        = X6 )
      | ~ ( r1_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k3_subset_1 @ X0 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['34','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('42',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k3_subset_1 @ X0 @ X0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X19: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('44',plain,(
    ! [X20: $i,X21: $i] :
      ( ( r1_tarski @ X20 @ X21 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('45',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ~ ( r1_xboole_0 @ X4 @ X5 )
      | ( r1_xboole_0 @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t63_xboole_1])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ k1_xboole_0 @ X1 )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['42','47'])).

thf('49',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k4_xboole_0 @ X6 @ X7 )
        = X6 )
      | ~ ( r1_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X19: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('54',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k3_subset_1 @ X12 @ X13 )
        = ( k4_xboole_0 @ X12 @ X13 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['52','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['33','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['30','57'])).

thf('59',plain,
    ( ( k1_xboole_0
      = ( k1_tops_1 @ sk_A @ sk_B ) )
   <= ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['24','58'])).

thf('60',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t84_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v2_tops_1 @ B @ A )
          <=> ( ( k1_tops_1 @ A @ B )
              = k1_xboole_0 ) ) ) ) )).

thf('61',plain,(
    ! [X36: $i,X37: $i] :
      ( ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X37 ) ) )
      | ( ( k1_tops_1 @ X37 @ X36 )
       != k1_xboole_0 )
      | ( v2_tops_1 @ X36 @ X37 )
      | ~ ( l1_pre_topc @ X37 ) ) ),
    inference(cnf,[status(esa)],[t84_tops_1])).

thf('62',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v2_tops_1 @ sk_B @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,
    ( ( v2_tops_1 @ sk_B @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
     != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( v2_tops_1 @ sk_B @ sk_A ) )
   <= ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['59','64'])).

thf('66',plain,
    ( ( v2_tops_1 @ sk_B @ sk_A )
   <= ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['65'])).

thf('67',plain,
    ( ~ ( v2_tops_1 @ sk_B @ sk_A )
   <= ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('68',plain,
    ( ( v2_tops_1 @ sk_B @ sk_A )
    | ~ ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    ~ ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sat_resolution*',[status(thm)],['2','68'])).

thf('70',plain,(
    ~ ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(simpl_trail,[status(thm)],['1','69'])).

thf('71',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t48_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_tarski @ B @ ( k2_pre_topc @ A @ B ) ) ) ) )).

thf('72',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) )
      | ( r1_tarski @ X28 @ ( k2_pre_topc @ X29 @ X28 ) )
      | ~ ( l1_pre_topc @ X29 ) ) ),
    inference(cnf,[status(esa)],[t48_pre_topc])).

thf('73',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ sk_B @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    r1_tarski @ sk_B @ ( k2_pre_topc @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('76',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l78_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_tops_1 @ A @ B )
            = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ ( k1_tops_1 @ A @ B ) ) ) ) ) )).

thf('77',plain,(
    ! [X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X31 ) ) )
      | ( ( k2_tops_1 @ X31 @ X30 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X31 ) @ ( k2_pre_topc @ X31 @ X30 ) @ ( k1_tops_1 @ X31 @ X30 ) ) )
      | ~ ( l1_pre_topc @ X31 ) ) ),
    inference(cnf,[status(esa)],[l78_tops_1])).

thf('78',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['78','79'])).

thf('81',plain,
    ( ( v2_tops_1 @ sk_B @ sk_A )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['10'])).

thf('82',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    ! [X36: $i,X37: $i] :
      ( ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X37 ) ) )
      | ~ ( v2_tops_1 @ X36 @ X37 )
      | ( ( k1_tops_1 @ X37 @ X36 )
        = k1_xboole_0 )
      | ~ ( l1_pre_topc @ X37 ) ) ),
    inference(cnf,[status(esa)],[t84_tops_1])).

thf('84',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('87',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['81','86'])).

thf('88',plain,
    ( ( v2_tops_1 @ sk_B @ sk_A )
    | ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['10'])).

thf('89',plain,(
    v2_tops_1 @ sk_B @ sk_A ),
    inference('sat_resolution*',[status(thm)],['2','68','88'])).

thf('90',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['87','89'])).

thf('91',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('92',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( l1_pre_topc @ X26 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X26 @ X27 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('93',plain,
    ( ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['93','94'])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('96',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X17 ) )
      | ( ( k7_subset_1 @ X17 @ X16 @ X18 )
        = ( k4_xboole_0 @ X16 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('97',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 )
      = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf('99',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k2_pre_topc @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['80','90','97','98'])).

thf('100',plain,(
    r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['75','99'])).

thf('101',plain,(
    $false ),
    inference(demod,[status(thm)],['70','100'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.aVa0BUqJAu
% 0.15/0.35  % Computer   : n024.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 17:00:21 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  % Running portfolio for 600 s
% 0.15/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.15/0.35  % Number of cores: 8
% 0.15/0.35  % Python version: Python 3.6.8
% 0.15/0.36  % Running in FO mode
% 0.22/0.68  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.22/0.68  % Solved by: fo/fo7.sh
% 0.22/0.68  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.68  % done 639 iterations in 0.214s
% 0.22/0.68  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.22/0.68  % SZS output start Refutation
% 0.22/0.68  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.22/0.68  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.68  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.68  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.22/0.68  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 0.22/0.68  thf(v2_tops_1_type, type, v2_tops_1: $i > $i > $o).
% 0.22/0.68  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.22/0.68  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.68  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.22/0.68  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.22/0.68  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.22/0.68  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.22/0.68  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 0.22/0.68  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.22/0.68  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.22/0.68  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.22/0.68  thf(t88_tops_1, conjecture,
% 0.22/0.68    (![A:$i]:
% 0.22/0.68     ( ( l1_pre_topc @ A ) =>
% 0.22/0.68       ( ![B:$i]:
% 0.22/0.68         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.68           ( ( v2_tops_1 @ B @ A ) <=>
% 0.22/0.68             ( r1_tarski @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.22/0.68  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.68    (~( ![A:$i]:
% 0.22/0.68        ( ( l1_pre_topc @ A ) =>
% 0.22/0.68          ( ![B:$i]:
% 0.22/0.68            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.68              ( ( v2_tops_1 @ B @ A ) <=>
% 0.22/0.68                ( r1_tarski @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ) )),
% 0.22/0.68    inference('cnf.neg', [status(esa)], [t88_tops_1])).
% 0.22/0.68  thf('0', plain,
% 0.22/0.68      ((~ (r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.22/0.68        | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 0.22/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.68  thf('1', plain,
% 0.22/0.68      ((~ (r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))
% 0.22/0.68         <= (~ ((r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))),
% 0.22/0.68      inference('split', [status(esa)], ['0'])).
% 0.22/0.68  thf('2', plain,
% 0.22/0.68      (~ ((r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))) | 
% 0.22/0.68       ~ ((v2_tops_1 @ sk_B @ sk_A))),
% 0.22/0.68      inference('split', [status(esa)], ['0'])).
% 0.22/0.68  thf('3', plain,
% 0.22/0.68      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.68  thf(t73_tops_1, axiom,
% 0.22/0.68    (![A:$i]:
% 0.22/0.68     ( ( l1_pre_topc @ A ) =>
% 0.22/0.68       ( ![B:$i]:
% 0.22/0.68         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.68           ( r1_xboole_0 @ ( k1_tops_1 @ A @ B ) @ ( k2_tops_1 @ A @ B ) ) ) ) ))).
% 0.22/0.68  thf('4', plain,
% 0.22/0.68      (![X34 : $i, X35 : $i]:
% 0.22/0.68         (~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (u1_struct_0 @ X35)))
% 0.22/0.68          | (r1_xboole_0 @ (k1_tops_1 @ X35 @ X34) @ (k2_tops_1 @ X35 @ X34))
% 0.22/0.68          | ~ (l1_pre_topc @ X35))),
% 0.22/0.68      inference('cnf', [status(esa)], [t73_tops_1])).
% 0.22/0.68  thf('5', plain,
% 0.22/0.68      ((~ (l1_pre_topc @ sk_A)
% 0.22/0.68        | (r1_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.22/0.68      inference('sup-', [status(thm)], ['3', '4'])).
% 0.22/0.68  thf('6', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.68  thf('7', plain,
% 0.22/0.68      ((r1_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ (k2_tops_1 @ sk_A @ sk_B))),
% 0.22/0.68      inference('demod', [status(thm)], ['5', '6'])).
% 0.22/0.68  thf(t83_xboole_1, axiom,
% 0.22/0.68    (![A:$i,B:$i]:
% 0.22/0.68     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.22/0.68  thf('8', plain,
% 0.22/0.68      (![X6 : $i, X7 : $i]:
% 0.22/0.68         (((k4_xboole_0 @ X6 @ X7) = (X6)) | ~ (r1_xboole_0 @ X6 @ X7))),
% 0.22/0.68      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.22/0.68  thf('9', plain,
% 0.22/0.68      (((k4_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ (k2_tops_1 @ sk_A @ sk_B))
% 0.22/0.68         = (k1_tops_1 @ sk_A @ sk_B))),
% 0.22/0.68      inference('sup-', [status(thm)], ['7', '8'])).
% 0.22/0.68  thf('10', plain,
% 0.22/0.68      (((r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.22/0.68        | (v2_tops_1 @ sk_B @ sk_A))),
% 0.22/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.68  thf('11', plain,
% 0.22/0.68      (((r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))
% 0.22/0.68         <= (((r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))),
% 0.22/0.68      inference('split', [status(esa)], ['10'])).
% 0.22/0.68  thf(t85_xboole_1, axiom,
% 0.22/0.68    (![A:$i,B:$i,C:$i]:
% 0.22/0.68     ( ( r1_tarski @ A @ B ) => ( r1_xboole_0 @ A @ ( k4_xboole_0 @ C @ B ) ) ))).
% 0.22/0.68  thf('12', plain,
% 0.22/0.68      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.22/0.68         (~ (r1_tarski @ X9 @ X10)
% 0.22/0.68          | (r1_xboole_0 @ X9 @ (k4_xboole_0 @ X11 @ X10)))),
% 0.22/0.68      inference('cnf', [status(esa)], [t85_xboole_1])).
% 0.22/0.68  thf('13', plain,
% 0.22/0.68      ((![X0 : $i]:
% 0.22/0.68          (r1_xboole_0 @ sk_B @ (k4_xboole_0 @ X0 @ (k2_tops_1 @ sk_A @ sk_B))))
% 0.22/0.68         <= (((r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))),
% 0.22/0.68      inference('sup-', [status(thm)], ['11', '12'])).
% 0.22/0.68  thf('14', plain,
% 0.22/0.68      (((r1_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))
% 0.22/0.68         <= (((r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))),
% 0.22/0.68      inference('sup+', [status(thm)], ['9', '13'])).
% 0.22/0.68  thf('15', plain,
% 0.22/0.68      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.68  thf(t44_tops_1, axiom,
% 0.22/0.68    (![A:$i]:
% 0.22/0.68     ( ( l1_pre_topc @ A ) =>
% 0.22/0.68       ( ![B:$i]:
% 0.22/0.68         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.68           ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) ))).
% 0.22/0.68  thf('16', plain,
% 0.22/0.68      (![X32 : $i, X33 : $i]:
% 0.22/0.68         (~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (u1_struct_0 @ X33)))
% 0.22/0.68          | (r1_tarski @ (k1_tops_1 @ X33 @ X32) @ X32)
% 0.22/0.68          | ~ (l1_pre_topc @ X33))),
% 0.22/0.68      inference('cnf', [status(esa)], [t44_tops_1])).
% 0.22/0.68  thf('17', plain,
% 0.22/0.68      ((~ (l1_pre_topc @ sk_A) | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B))),
% 0.22/0.68      inference('sup-', [status(thm)], ['15', '16'])).
% 0.22/0.68  thf('18', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.68  thf('19', plain, ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B)),
% 0.22/0.68      inference('demod', [status(thm)], ['17', '18'])).
% 0.22/0.68  thf(t63_xboole_1, axiom,
% 0.22/0.68    (![A:$i,B:$i,C:$i]:
% 0.22/0.68     ( ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ B @ C ) ) =>
% 0.22/0.68       ( r1_xboole_0 @ A @ C ) ))).
% 0.22/0.68  thf('20', plain,
% 0.22/0.68      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.22/0.68         (~ (r1_tarski @ X3 @ X4)
% 0.22/0.68          | ~ (r1_xboole_0 @ X4 @ X5)
% 0.22/0.68          | (r1_xboole_0 @ X3 @ X5))),
% 0.22/0.68      inference('cnf', [status(esa)], [t63_xboole_1])).
% 0.22/0.68  thf('21', plain,
% 0.22/0.68      (![X0 : $i]:
% 0.22/0.68         ((r1_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ X0)
% 0.22/0.68          | ~ (r1_xboole_0 @ sk_B @ X0))),
% 0.22/0.68      inference('sup-', [status(thm)], ['19', '20'])).
% 0.22/0.68  thf('22', plain,
% 0.22/0.68      (((r1_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ sk_B)))
% 0.22/0.68         <= (((r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))),
% 0.22/0.68      inference('sup-', [status(thm)], ['14', '21'])).
% 0.22/0.68  thf('23', plain,
% 0.22/0.68      (![X6 : $i, X7 : $i]:
% 0.22/0.68         (((k4_xboole_0 @ X6 @ X7) = (X6)) | ~ (r1_xboole_0 @ X6 @ X7))),
% 0.22/0.68      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.22/0.68  thf('24', plain,
% 0.22/0.68      ((((k4_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ sk_B))
% 0.22/0.68          = (k1_tops_1 @ sk_A @ sk_B)))
% 0.22/0.68         <= (((r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))),
% 0.22/0.68      inference('sup-', [status(thm)], ['22', '23'])).
% 0.22/0.68  thf(d10_xboole_0, axiom,
% 0.22/0.68    (![A:$i,B:$i]:
% 0.22/0.68     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.22/0.68  thf('25', plain,
% 0.22/0.68      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.22/0.68      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.22/0.68  thf('26', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.22/0.68      inference('simplify', [status(thm)], ['25'])).
% 0.22/0.68  thf(t3_subset, axiom,
% 0.22/0.68    (![A:$i,B:$i]:
% 0.22/0.68     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.22/0.68  thf('27', plain,
% 0.22/0.68      (![X20 : $i, X22 : $i]:
% 0.22/0.68         ((m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X22)) | ~ (r1_tarski @ X20 @ X22))),
% 0.22/0.68      inference('cnf', [status(esa)], [t3_subset])).
% 0.22/0.68  thf('28', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.22/0.68      inference('sup-', [status(thm)], ['26', '27'])).
% 0.22/0.68  thf(d5_subset_1, axiom,
% 0.22/0.68    (![A:$i,B:$i]:
% 0.22/0.68     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.22/0.68       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.22/0.68  thf('29', plain,
% 0.22/0.68      (![X12 : $i, X13 : $i]:
% 0.22/0.68         (((k3_subset_1 @ X12 @ X13) = (k4_xboole_0 @ X12 @ X13))
% 0.22/0.68          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X12)))),
% 0.22/0.68      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.22/0.68  thf('30', plain,
% 0.22/0.68      (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 0.22/0.68      inference('sup-', [status(thm)], ['28', '29'])).
% 0.22/0.68  thf(t4_subset_1, axiom,
% 0.22/0.68    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.22/0.68  thf('31', plain,
% 0.22/0.68      (![X19 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X19))),
% 0.22/0.68      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.22/0.68  thf(involutiveness_k3_subset_1, axiom,
% 0.22/0.68    (![A:$i,B:$i]:
% 0.22/0.68     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.22/0.68       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 0.22/0.68  thf('32', plain,
% 0.22/0.68      (![X14 : $i, X15 : $i]:
% 0.22/0.68         (((k3_subset_1 @ X15 @ (k3_subset_1 @ X15 @ X14)) = (X14))
% 0.22/0.68          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X15)))),
% 0.22/0.68      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.22/0.68  thf('33', plain,
% 0.22/0.68      (![X0 : $i]:
% 0.22/0.68         ((k3_subset_1 @ X0 @ (k3_subset_1 @ X0 @ k1_xboole_0)) = (k1_xboole_0))),
% 0.22/0.68      inference('sup-', [status(thm)], ['31', '32'])).
% 0.22/0.68  thf('34', plain,
% 0.22/0.68      (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 0.22/0.68      inference('sup-', [status(thm)], ['28', '29'])).
% 0.22/0.68  thf('35', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.22/0.68      inference('simplify', [status(thm)], ['25'])).
% 0.22/0.68  thf('36', plain,
% 0.22/0.68      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.22/0.68         (~ (r1_tarski @ X9 @ X10)
% 0.22/0.68          | (r1_xboole_0 @ X9 @ (k4_xboole_0 @ X11 @ X10)))),
% 0.22/0.68      inference('cnf', [status(esa)], [t85_xboole_1])).
% 0.22/0.68  thf('37', plain,
% 0.22/0.68      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))),
% 0.22/0.68      inference('sup-', [status(thm)], ['35', '36'])).
% 0.22/0.68  thf('38', plain,
% 0.22/0.68      (![X6 : $i, X7 : $i]:
% 0.22/0.68         (((k4_xboole_0 @ X6 @ X7) = (X6)) | ~ (r1_xboole_0 @ X6 @ X7))),
% 0.22/0.68      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.22/0.68  thf('39', plain,
% 0.22/0.68      (![X0 : $i, X1 : $i]:
% 0.22/0.68         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (X0))),
% 0.22/0.68      inference('sup-', [status(thm)], ['37', '38'])).
% 0.22/0.68  thf('40', plain,
% 0.22/0.68      (![X0 : $i]: ((k4_xboole_0 @ X0 @ (k3_subset_1 @ X0 @ X0)) = (X0))),
% 0.22/0.68      inference('sup+', [status(thm)], ['34', '39'])).
% 0.22/0.68  thf('41', plain,
% 0.22/0.68      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))),
% 0.22/0.68      inference('sup-', [status(thm)], ['35', '36'])).
% 0.22/0.68  thf('42', plain, (![X0 : $i]: (r1_xboole_0 @ (k3_subset_1 @ X0 @ X0) @ X0)),
% 0.22/0.68      inference('sup+', [status(thm)], ['40', '41'])).
% 0.22/0.68  thf('43', plain,
% 0.22/0.68      (![X19 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X19))),
% 0.22/0.68      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.22/0.68  thf('44', plain,
% 0.22/0.68      (![X20 : $i, X21 : $i]:
% 0.22/0.68         ((r1_tarski @ X20 @ X21) | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X21)))),
% 0.22/0.68      inference('cnf', [status(esa)], [t3_subset])).
% 0.22/0.68  thf('45', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.22/0.68      inference('sup-', [status(thm)], ['43', '44'])).
% 0.22/0.68  thf('46', plain,
% 0.22/0.68      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.22/0.68         (~ (r1_tarski @ X3 @ X4)
% 0.22/0.68          | ~ (r1_xboole_0 @ X4 @ X5)
% 0.22/0.68          | (r1_xboole_0 @ X3 @ X5))),
% 0.22/0.68      inference('cnf', [status(esa)], [t63_xboole_1])).
% 0.22/0.68  thf('47', plain,
% 0.22/0.68      (![X0 : $i, X1 : $i]:
% 0.22/0.68         ((r1_xboole_0 @ k1_xboole_0 @ X1) | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.22/0.68      inference('sup-', [status(thm)], ['45', '46'])).
% 0.22/0.68  thf('48', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.22/0.68      inference('sup-', [status(thm)], ['42', '47'])).
% 0.22/0.68  thf('49', plain,
% 0.22/0.68      (![X6 : $i, X7 : $i]:
% 0.22/0.68         (((k4_xboole_0 @ X6 @ X7) = (X6)) | ~ (r1_xboole_0 @ X6 @ X7))),
% 0.22/0.68      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.22/0.68  thf('50', plain,
% 0.22/0.68      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.22/0.68      inference('sup-', [status(thm)], ['48', '49'])).
% 0.22/0.68  thf('51', plain,
% 0.22/0.68      (![X0 : $i, X1 : $i]:
% 0.22/0.68         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (X0))),
% 0.22/0.68      inference('sup-', [status(thm)], ['37', '38'])).
% 0.22/0.68  thf('52', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.22/0.68      inference('sup+', [status(thm)], ['50', '51'])).
% 0.22/0.68  thf('53', plain,
% 0.22/0.68      (![X19 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X19))),
% 0.22/0.68      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.22/0.68  thf('54', plain,
% 0.22/0.68      (![X12 : $i, X13 : $i]:
% 0.22/0.68         (((k3_subset_1 @ X12 @ X13) = (k4_xboole_0 @ X12 @ X13))
% 0.22/0.68          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X12)))),
% 0.22/0.68      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.22/0.68  thf('55', plain,
% 0.22/0.68      (![X0 : $i]:
% 0.22/0.68         ((k3_subset_1 @ X0 @ k1_xboole_0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 0.22/0.68      inference('sup-', [status(thm)], ['53', '54'])).
% 0.22/0.68  thf('56', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ k1_xboole_0) = (X0))),
% 0.22/0.68      inference('sup+', [status(thm)], ['52', '55'])).
% 0.22/0.68  thf('57', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k1_xboole_0))),
% 0.22/0.68      inference('demod', [status(thm)], ['33', '56'])).
% 0.22/0.68  thf('58', plain, (![X0 : $i]: ((k1_xboole_0) = (k4_xboole_0 @ X0 @ X0))),
% 0.22/0.68      inference('demod', [status(thm)], ['30', '57'])).
% 0.22/0.68  thf('59', plain,
% 0.22/0.68      ((((k1_xboole_0) = (k1_tops_1 @ sk_A @ sk_B)))
% 0.22/0.68         <= (((r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))),
% 0.22/0.68      inference('demod', [status(thm)], ['24', '58'])).
% 0.22/0.68  thf('60', plain,
% 0.22/0.68      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.68  thf(t84_tops_1, axiom,
% 0.22/0.68    (![A:$i]:
% 0.22/0.68     ( ( l1_pre_topc @ A ) =>
% 0.22/0.68       ( ![B:$i]:
% 0.22/0.68         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.68           ( ( v2_tops_1 @ B @ A ) <=>
% 0.22/0.68             ( ( k1_tops_1 @ A @ B ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 0.22/0.68  thf('61', plain,
% 0.22/0.68      (![X36 : $i, X37 : $i]:
% 0.22/0.68         (~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (u1_struct_0 @ X37)))
% 0.22/0.68          | ((k1_tops_1 @ X37 @ X36) != (k1_xboole_0))
% 0.22/0.68          | (v2_tops_1 @ X36 @ X37)
% 0.22/0.68          | ~ (l1_pre_topc @ X37))),
% 0.22/0.68      inference('cnf', [status(esa)], [t84_tops_1])).
% 0.22/0.68  thf('62', plain,
% 0.22/0.68      ((~ (l1_pre_topc @ sk_A)
% 0.22/0.68        | (v2_tops_1 @ sk_B @ sk_A)
% 0.22/0.68        | ((k1_tops_1 @ sk_A @ sk_B) != (k1_xboole_0)))),
% 0.22/0.68      inference('sup-', [status(thm)], ['60', '61'])).
% 0.22/0.68  thf('63', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.68  thf('64', plain,
% 0.22/0.68      (((v2_tops_1 @ sk_B @ sk_A)
% 0.22/0.68        | ((k1_tops_1 @ sk_A @ sk_B) != (k1_xboole_0)))),
% 0.22/0.68      inference('demod', [status(thm)], ['62', '63'])).
% 0.22/0.68  thf('65', plain,
% 0.22/0.68      (((((k1_xboole_0) != (k1_xboole_0)) | (v2_tops_1 @ sk_B @ sk_A)))
% 0.22/0.68         <= (((r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))),
% 0.22/0.68      inference('sup-', [status(thm)], ['59', '64'])).
% 0.22/0.68  thf('66', plain,
% 0.22/0.68      (((v2_tops_1 @ sk_B @ sk_A))
% 0.22/0.68         <= (((r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))),
% 0.22/0.68      inference('simplify', [status(thm)], ['65'])).
% 0.22/0.68  thf('67', plain,
% 0.22/0.68      ((~ (v2_tops_1 @ sk_B @ sk_A)) <= (~ ((v2_tops_1 @ sk_B @ sk_A)))),
% 0.22/0.68      inference('split', [status(esa)], ['0'])).
% 0.22/0.68  thf('68', plain,
% 0.22/0.68      (((v2_tops_1 @ sk_B @ sk_A)) | 
% 0.22/0.68       ~ ((r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.22/0.68      inference('sup-', [status(thm)], ['66', '67'])).
% 0.22/0.68  thf('69', plain, (~ ((r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.22/0.68      inference('sat_resolution*', [status(thm)], ['2', '68'])).
% 0.22/0.68  thf('70', plain, (~ (r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))),
% 0.22/0.68      inference('simpl_trail', [status(thm)], ['1', '69'])).
% 0.22/0.68  thf('71', plain,
% 0.22/0.68      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.68  thf(t48_pre_topc, axiom,
% 0.22/0.68    (![A:$i]:
% 0.22/0.68     ( ( l1_pre_topc @ A ) =>
% 0.22/0.68       ( ![B:$i]:
% 0.22/0.68         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.68           ( r1_tarski @ B @ ( k2_pre_topc @ A @ B ) ) ) ) ))).
% 0.22/0.68  thf('72', plain,
% 0.22/0.68      (![X28 : $i, X29 : $i]:
% 0.22/0.68         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (u1_struct_0 @ X29)))
% 0.22/0.68          | (r1_tarski @ X28 @ (k2_pre_topc @ X29 @ X28))
% 0.22/0.68          | ~ (l1_pre_topc @ X29))),
% 0.22/0.68      inference('cnf', [status(esa)], [t48_pre_topc])).
% 0.22/0.68  thf('73', plain,
% 0.22/0.68      ((~ (l1_pre_topc @ sk_A)
% 0.22/0.68        | (r1_tarski @ sk_B @ (k2_pre_topc @ sk_A @ sk_B)))),
% 0.22/0.68      inference('sup-', [status(thm)], ['71', '72'])).
% 0.22/0.68  thf('74', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.68  thf('75', plain, ((r1_tarski @ sk_B @ (k2_pre_topc @ sk_A @ sk_B))),
% 0.22/0.68      inference('demod', [status(thm)], ['73', '74'])).
% 0.22/0.68  thf('76', plain,
% 0.22/0.68      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.68  thf(l78_tops_1, axiom,
% 0.22/0.68    (![A:$i]:
% 0.22/0.68     ( ( l1_pre_topc @ A ) =>
% 0.22/0.68       ( ![B:$i]:
% 0.22/0.68         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.68           ( ( k2_tops_1 @ A @ B ) =
% 0.22/0.68             ( k7_subset_1 @
% 0.22/0.68               ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 0.22/0.68               ( k1_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.22/0.68  thf('77', plain,
% 0.22/0.68      (![X30 : $i, X31 : $i]:
% 0.22/0.68         (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ X31)))
% 0.22/0.68          | ((k2_tops_1 @ X31 @ X30)
% 0.22/0.68              = (k7_subset_1 @ (u1_struct_0 @ X31) @ 
% 0.22/0.68                 (k2_pre_topc @ X31 @ X30) @ (k1_tops_1 @ X31 @ X30)))
% 0.22/0.68          | ~ (l1_pre_topc @ X31))),
% 0.22/0.68      inference('cnf', [status(esa)], [l78_tops_1])).
% 0.22/0.68  thf('78', plain,
% 0.22/0.68      ((~ (l1_pre_topc @ sk_A)
% 0.22/0.68        | ((k2_tops_1 @ sk_A @ sk_B)
% 0.22/0.68            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.22/0.68               (k2_pre_topc @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ sk_B))))),
% 0.22/0.68      inference('sup-', [status(thm)], ['76', '77'])).
% 0.22/0.68  thf('79', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.68  thf('80', plain,
% 0.22/0.68      (((k2_tops_1 @ sk_A @ sk_B)
% 0.22/0.68         = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.22/0.68            (k1_tops_1 @ sk_A @ sk_B)))),
% 0.22/0.68      inference('demod', [status(thm)], ['78', '79'])).
% 0.22/0.68  thf('81', plain,
% 0.22/0.68      (((v2_tops_1 @ sk_B @ sk_A)) <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.22/0.68      inference('split', [status(esa)], ['10'])).
% 0.22/0.68  thf('82', plain,
% 0.22/0.68      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.68  thf('83', plain,
% 0.22/0.68      (![X36 : $i, X37 : $i]:
% 0.22/0.68         (~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (u1_struct_0 @ X37)))
% 0.22/0.68          | ~ (v2_tops_1 @ X36 @ X37)
% 0.22/0.68          | ((k1_tops_1 @ X37 @ X36) = (k1_xboole_0))
% 0.22/0.68          | ~ (l1_pre_topc @ X37))),
% 0.22/0.68      inference('cnf', [status(esa)], [t84_tops_1])).
% 0.22/0.68  thf('84', plain,
% 0.22/0.68      ((~ (l1_pre_topc @ sk_A)
% 0.22/0.68        | ((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))
% 0.22/0.68        | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 0.22/0.68      inference('sup-', [status(thm)], ['82', '83'])).
% 0.22/0.68  thf('85', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.68  thf('86', plain,
% 0.22/0.68      ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))
% 0.22/0.68        | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 0.22/0.68      inference('demod', [status(thm)], ['84', '85'])).
% 0.22/0.68  thf('87', plain,
% 0.22/0.68      ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0)))
% 0.22/0.68         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.22/0.68      inference('sup-', [status(thm)], ['81', '86'])).
% 0.22/0.68  thf('88', plain,
% 0.22/0.68      (((v2_tops_1 @ sk_B @ sk_A)) | 
% 0.22/0.68       ((r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.22/0.68      inference('split', [status(esa)], ['10'])).
% 0.22/0.68  thf('89', plain, (((v2_tops_1 @ sk_B @ sk_A))),
% 0.22/0.68      inference('sat_resolution*', [status(thm)], ['2', '68', '88'])).
% 0.22/0.68  thf('90', plain, (((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.22/0.68      inference('simpl_trail', [status(thm)], ['87', '89'])).
% 0.22/0.68  thf('91', plain,
% 0.22/0.68      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.68  thf(dt_k2_pre_topc, axiom,
% 0.22/0.68    (![A:$i,B:$i]:
% 0.22/0.68     ( ( ( l1_pre_topc @ A ) & 
% 0.22/0.68         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.22/0.68       ( m1_subset_1 @
% 0.22/0.68         ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.22/0.68  thf('92', plain,
% 0.22/0.68      (![X26 : $i, X27 : $i]:
% 0.22/0.68         (~ (l1_pre_topc @ X26)
% 0.22/0.68          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ X26)))
% 0.22/0.68          | (m1_subset_1 @ (k2_pre_topc @ X26 @ X27) @ 
% 0.22/0.68             (k1_zfmisc_1 @ (u1_struct_0 @ X26))))),
% 0.22/0.68      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 0.22/0.68  thf('93', plain,
% 0.22/0.68      (((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.22/0.68         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.22/0.68        | ~ (l1_pre_topc @ sk_A))),
% 0.22/0.68      inference('sup-', [status(thm)], ['91', '92'])).
% 0.22/0.68  thf('94', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.68  thf('95', plain,
% 0.22/0.68      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.22/0.68        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.68      inference('demod', [status(thm)], ['93', '94'])).
% 0.22/0.68  thf(redefinition_k7_subset_1, axiom,
% 0.22/0.68    (![A:$i,B:$i,C:$i]:
% 0.22/0.68     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.22/0.68       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 0.22/0.68  thf('96', plain,
% 0.22/0.68      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.22/0.68         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X17))
% 0.22/0.68          | ((k7_subset_1 @ X17 @ X16 @ X18) = (k4_xboole_0 @ X16 @ X18)))),
% 0.22/0.68      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 0.22/0.68  thf('97', plain,
% 0.22/0.68      (![X0 : $i]:
% 0.22/0.68         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.22/0.68           X0) = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ X0))),
% 0.22/0.68      inference('sup-', [status(thm)], ['95', '96'])).
% 0.22/0.68  thf('98', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.22/0.68      inference('sup+', [status(thm)], ['50', '51'])).
% 0.22/0.68  thf('99', plain, (((k2_tops_1 @ sk_A @ sk_B) = (k2_pre_topc @ sk_A @ sk_B))),
% 0.22/0.68      inference('demod', [status(thm)], ['80', '90', '97', '98'])).
% 0.22/0.68  thf('100', plain, ((r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))),
% 0.22/0.68      inference('demod', [status(thm)], ['75', '99'])).
% 0.22/0.68  thf('101', plain, ($false), inference('demod', [status(thm)], ['70', '100'])).
% 0.22/0.68  
% 0.22/0.68  % SZS output end Refutation
% 0.22/0.68  
% 0.22/0.69  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
