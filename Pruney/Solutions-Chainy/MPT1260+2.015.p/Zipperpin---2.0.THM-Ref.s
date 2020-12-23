%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.AseWit65GC

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:24 EST 2020

% Result     : Theorem 3.09s
% Output     : Refutation 3.09s
% Verified   : 
% Statistics : Number of formulae       :  167 ( 314 expanded)
%              Number of leaves         :   42 ( 106 expanded)
%              Depth                    :   23
%              Number of atoms          : 1582 (3839 expanded)
%              Number of equality atoms :   99 ( 218 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(t76_tops_1,conjecture,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v3_pre_topc @ B @ A )
          <=> ( ( k2_tops_1 @ A @ B )
              = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( ( v3_pre_topc @ B @ A )
            <=> ( ( k2_tops_1 @ A @ B )
                = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t76_tops_1])).

thf('0',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
    | ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
    | ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
    | ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( v3_pre_topc @ sk_B @ sk_A )
   <= ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['3'])).

thf('5',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t56_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( ( v3_pre_topc @ B @ A )
                  & ( r1_tarski @ B @ C ) )
               => ( r1_tarski @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) )).

thf('6',plain,(
    ! [X50: $i,X51: $i,X52: $i] :
      ( ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X51 ) ) )
      | ~ ( v3_pre_topc @ X50 @ X51 )
      | ~ ( r1_tarski @ X50 @ X52 )
      | ( r1_tarski @ X50 @ ( k1_tops_1 @ X51 @ X52 ) )
      | ~ ( m1_subset_1 @ X52 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X51 ) ) )
      | ~ ( l1_pre_topc @ X51 ) ) ),
    inference(cnf,[status(esa)],[t56_tops_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ sk_B @ X0 )
      | ~ ( v3_pre_topc @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ sk_B @ X0 )
      | ~ ( v3_pre_topc @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_tarski @ sk_B @ X0 )
        | ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ X0 ) )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['4','9'])).

thf('11',plain,
    ( ( ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
      | ~ ( r1_tarski @ sk_B @ sk_B ) )
   <= ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['2','10'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('12',plain,(
    ! [X12: $i,X13: $i] :
      ( ( r1_tarski @ X12 @ X13 )
      | ( X12 != X13 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('13',plain,(
    ! [X13: $i] :
      ( r1_tarski @ X13 @ X13 ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,
    ( ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
   <= ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['11','13'])).

thf('15',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t74_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k1_tops_1 @ A @ B )
            = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('16',plain,(
    ! [X57: $i,X58: $i] :
      ( ~ ( m1_subset_1 @ X57 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X58 ) ) )
      | ( ( k1_tops_1 @ X58 @ X57 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X58 ) @ X57 @ ( k2_tops_1 @ X58 @ X57 ) ) )
      | ~ ( l1_pre_topc @ X58 ) ) ),
    inference(cnf,[status(esa)],[t74_tops_1])).

thf('17',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('20',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ X37 ) )
      | ( ( k7_subset_1 @ X37 @ X36 @ X38 )
        = ( k4_xboole_0 @ X36 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['17','18','21'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('23',plain,(
    ! [X20: $i,X21: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X20 @ X21 ) @ X20 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('24',plain,(
    ! [X12: $i,X14: $i] :
      ( ( X12 = X14 )
      | ~ ( r1_tarski @ X14 @ X12 )
      | ~ ( r1_tarski @ X12 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
    | ( sk_B
      = ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['22','25'])).

thf('27',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['17','18','21'])).

thf('28',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
    | ( sk_B
      = ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,
    ( ( sk_B
      = ( k1_tops_1 @ sk_A @ sk_B ) )
   <= ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['14','28'])).

thf('30',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l78_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_tops_1 @ A @ B )
            = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ ( k1_tops_1 @ A @ B ) ) ) ) ) )).

thf('31',plain,(
    ! [X48: $i,X49: $i] :
      ( ~ ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X49 ) ) )
      | ( ( k2_tops_1 @ X49 @ X48 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X49 ) @ ( k2_pre_topc @ X49 @ X48 ) @ ( k1_tops_1 @ X49 @ X48 ) ) )
      | ~ ( l1_pre_topc @ X49 ) ) ),
    inference(cnf,[status(esa)],[l78_tops_1])).

thf('32',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
   <= ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['29','34'])).

thf('36',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('37',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( ( ( k2_tops_1 @ sk_A @ sk_B )
       != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
      & ( v3_pre_topc @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
    | ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
    | ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['3'])).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('40',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k3_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X1 )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('41',plain,(
    ! [X39: $i,X40: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X39 @ X40 ) )
      = ( k3_xboole_0 @ X39 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('42',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k1_setfam_1 @ ( k2_tarski @ X1 @ X2 ) ) )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X1 )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('43',plain,(
    ! [X22: $i] :
      ( ( k4_xboole_0 @ X22 @ k1_xboole_0 )
      = X22 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('44',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X10 @ X9 )
      | ~ ( r2_hidden @ X10 @ X8 )
      | ( X9
       != ( k4_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('45',plain,(
    ! [X7: $i,X8: $i,X10: $i] :
      ( ~ ( r2_hidden @ X10 @ X8 )
      | ~ ( r2_hidden @ X10 @ ( k4_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['43','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ k1_xboole_0 @ X1 @ X0 ) @ X0 )
      | ( k1_xboole_0
        = ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['42','47'])).

thf('49',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k3_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X2 )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('50',plain,(
    ! [X39: $i,X40: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X39 @ X40 ) )
      = ( k3_xboole_0 @ X39 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('51',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k1_setfam_1 @ ( k2_tarski @ X1 @ X2 ) ) )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X2 )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['46'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ k1_xboole_0 @ X1 @ X0 ) @ X1 )
      | ( k1_xboole_0
        = ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference(split,[status(esa)],['3'])).

thf('55',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('56',plain,(
    ! [X44: $i,X45: $i] :
      ( ~ ( l1_pre_topc @ X44 )
      | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X44 ) ) )
      | ( m1_subset_1 @ ( k2_tops_1 @ X44 @ X45 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X44 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_1])).

thf('57',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( m1_subset_1 @ ( k4_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('61',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ X32 ) )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ X32 ) )
      | ( m1_subset_1 @ ( k4_subset_1 @ X32 @ X31 @ X33 ) @ ( k1_zfmisc_1 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k4_subset_1])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    m1_subset_1 @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['59','62'])).

thf('64',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t65_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_pre_topc @ A @ B )
            = ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('65',plain,(
    ! [X55: $i,X56: $i] :
      ( ~ ( m1_subset_1 @ X55 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X56 ) ) )
      | ( ( k2_pre_topc @ X56 @ X55 )
        = ( k4_subset_1 @ ( u1_struct_0 @ X56 ) @ X55 @ ( k2_tops_1 @ X56 @ X55 ) ) )
      | ~ ( l1_pre_topc @ X56 ) ) ),
    inference(cnf,[status(esa)],[t65_tops_1])).

thf('66',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
      = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('69',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['63','68'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('70',plain,(
    ! [X41: $i,X42: $i] :
      ( ( r1_tarski @ X41 @ X42 )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ X42 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('71',plain,(
    r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('72',plain,(
    ! [X17: $i,X18: $i] :
      ( ( ( k3_xboole_0 @ X17 @ X18 )
        = X17 )
      | ~ ( r1_tarski @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('73',plain,(
    ! [X39: $i,X40: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X39 @ X40 ) )
      = ( k3_xboole_0 @ X39 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('74',plain,(
    ! [X17: $i,X18: $i] :
      ( ( ( k1_setfam_1 @ ( k2_tarski @ X17 @ X18 ) )
        = X17 )
      | ~ ( r1_tarski @ X17 @ X18 ) ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('75',plain,
    ( ( k1_setfam_1 @ ( k2_tarski @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) )
    = ( k2_pre_topc @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['71','74'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('76',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k2_tarski @ X26 @ X25 )
      = ( k2_tarski @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf('77',plain,
    ( ( k1_setfam_1 @ ( k2_tarski @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) ) )
    = ( k2_pre_topc @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['75','76'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('78',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ X16 )
      = ( k5_xboole_0 @ X15 @ ( k3_xboole_0 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('79',plain,(
    ! [X39: $i,X40: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X39 @ X40 ) )
      = ( k3_xboole_0 @ X39 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('80',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ X16 )
      = ( k5_xboole_0 @ X15 @ ( k1_setfam_1 @ ( k2_tarski @ X15 @ X16 ) ) ) ) ),
    inference(demod,[status(thm)],['78','79'])).

thf('81',plain,
    ( ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) )
    = ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['77','80'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('82',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k4_xboole_0 @ X23 @ ( k4_xboole_0 @ X23 @ X24 ) )
      = ( k3_xboole_0 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('83',plain,(
    ! [X39: $i,X40: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X39 @ X40 ) )
      = ( k3_xboole_0 @ X39 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('84',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k4_xboole_0 @ X23 @ ( k4_xboole_0 @ X23 @ X24 ) )
      = ( k1_setfam_1 @ ( k2_tarski @ X23 @ X24 ) ) ) ),
    inference(demod,[status(thm)],['82','83'])).

thf('85',plain,
    ( ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) ) )
    = ( k1_setfam_1 @ ( k2_tarski @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['81','84'])).

thf('86',plain,
    ( ( k1_setfam_1 @ ( k2_tarski @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) ) )
    = ( k2_pre_topc @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['75','76'])).

thf('87',plain,
    ( ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) ) )
    = ( k2_pre_topc @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X20: $i,X21: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X20 @ X21 ) @ X20 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('89',plain,(
    ! [X41: $i,X43: $i] :
      ( ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ X43 ) )
      | ~ ( r1_tarski @ X41 @ X43 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('90',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ X37 ) )
      | ( ( k7_subset_1 @ X37 @ X36 @ X38 )
        = ( k4_xboole_0 @ X36 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('92',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k7_subset_1 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X2 )
      = ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,(
    ! [X7: $i,X8: $i,X10: $i] :
      ( ~ ( r2_hidden @ X10 @ X8 )
      | ~ ( r2_hidden @ X10 @ ( k4_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(simplify,[status(thm)],['44'])).

thf('94',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k7_subset_1 @ X2 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) )
      | ~ ( r2_hidden @ X3 @ X0 ) ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 ) )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['87','94'])).

thf('96',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ ( k2_tops_1 @ sk_A @ sk_B ) )
        | ~ ( r2_hidden @ X0 @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['54','95'])).

thf('97',plain,
    ( ! [X0: $i] :
        ( ( k1_xboole_0
          = ( k1_setfam_1 @ ( k2_tarski @ X0 @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) )
        | ~ ( r2_hidden @ ( sk_D @ k1_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ X0 ) @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['53','96'])).

thf('98',plain,
    ( ( ( k1_xboole_0
        = ( k1_setfam_1 @ ( k2_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) )
      | ( k1_xboole_0
        = ( k1_setfam_1 @ ( k2_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['48','97'])).

thf('99',plain,
    ( ( k1_xboole_0
      = ( k1_setfam_1 @ ( k2_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference(simplify,[status(thm)],['98'])).

thf('100',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k4_xboole_0 @ X23 @ ( k4_xboole_0 @ X23 @ X24 ) )
      = ( k1_setfam_1 @ ( k2_tarski @ X23 @ X24 ) ) ) ),
    inference(demod,[status(thm)],['82','83'])).

thf('101',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k4_xboole_0 @ X23 @ ( k4_xboole_0 @ X23 @ X24 ) )
      = ( k1_setfam_1 @ ( k2_tarski @ X23 @ X24 ) ) ) ),
    inference(demod,[status(thm)],['82','83'])).

thf('102',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) )
      = ( k1_setfam_1 @ ( k2_tarski @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['100','101'])).

thf('103',plain,(
    ! [X20: $i,X21: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X20 @ X21 ) @ X20 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('104',plain,(
    ! [X17: $i,X18: $i] :
      ( ( ( k1_setfam_1 @ ( k2_tarski @ X17 @ X18 ) )
        = X17 )
      | ~ ( r1_tarski @ X17 @ X18 ) ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('105',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k2_tarski @ X26 @ X25 )
      = ( k2_tarski @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf('107',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['105','106'])).

thf('108',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['102','107'])).

thf('109',plain,
    ( ( ( k4_xboole_0 @ sk_B @ k1_xboole_0 )
      = ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['99','108'])).

thf('110',plain,(
    ! [X22: $i] :
      ( ( k4_xboole_0 @ X22 @ k1_xboole_0 )
      = X22 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('111',plain,
    ( ( sk_B
      = ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['109','110'])).

thf('112',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['17','18','21'])).

thf('113',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['111','112'])).

thf('114',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc9_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ) )).

thf('115',plain,(
    ! [X46: $i,X47: $i] :
      ( ~ ( l1_pre_topc @ X46 )
      | ~ ( v2_pre_topc @ X46 )
      | ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X46 ) ) )
      | ( v3_pre_topc @ ( k1_tops_1 @ X46 @ X47 ) @ X46 ) ) ),
    inference(cnf,[status(esa)],[fc9_tops_1])).

thf('116',plain,
    ( ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['114','115'])).

thf('117',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,(
    v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['116','117','118'])).

thf('120',plain,
    ( ( v3_pre_topc @ sk_B @ sk_A )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['113','119'])).

thf('121',plain,
    ( ~ ( v3_pre_topc @ sk_B @ sk_A )
   <= ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('122',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
    | ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['120','121'])).

thf('123',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','38','39','122'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.AseWit65GC
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:36:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 3.09/3.28  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 3.09/3.28  % Solved by: fo/fo7.sh
% 3.09/3.28  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 3.09/3.28  % done 3521 iterations in 2.827s
% 3.09/3.28  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 3.09/3.28  % SZS output start Refutation
% 3.09/3.28  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 3.09/3.28  thf(sk_B_type, type, sk_B: $i).
% 3.09/3.28  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 3.09/3.28  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 3.09/3.28  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 3.09/3.28  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 3.09/3.28  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 3.09/3.28  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 3.09/3.28  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 3.09/3.28  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 3.09/3.28  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 3.09/3.28  thf(sk_A_type, type, sk_A: $i).
% 3.09/3.28  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 3.09/3.28  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 3.09/3.28  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 3.09/3.28  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 3.09/3.28  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 3.09/3.28  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 3.09/3.28  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 3.09/3.28  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 3.09/3.28  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 3.09/3.28  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 3.09/3.28  thf(t76_tops_1, conjecture,
% 3.09/3.28    (![A:$i]:
% 3.09/3.28     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 3.09/3.28       ( ![B:$i]:
% 3.09/3.28         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 3.09/3.28           ( ( v3_pre_topc @ B @ A ) <=>
% 3.09/3.28             ( ( k2_tops_1 @ A @ B ) =
% 3.09/3.28               ( k7_subset_1 @
% 3.09/3.28                 ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ B ) ) ) ) ) ))).
% 3.09/3.28  thf(zf_stmt_0, negated_conjecture,
% 3.09/3.28    (~( ![A:$i]:
% 3.09/3.28        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 3.09/3.28          ( ![B:$i]:
% 3.09/3.28            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 3.09/3.28              ( ( v3_pre_topc @ B @ A ) <=>
% 3.09/3.28                ( ( k2_tops_1 @ A @ B ) =
% 3.09/3.28                  ( k7_subset_1 @
% 3.09/3.28                    ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ B ) ) ) ) ) ) )),
% 3.09/3.28    inference('cnf.neg', [status(esa)], [t76_tops_1])).
% 3.09/3.28  thf('0', plain,
% 3.09/3.28      ((((k2_tops_1 @ sk_A @ sk_B)
% 3.09/3.28          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 3.09/3.28              (k2_pre_topc @ sk_A @ sk_B) @ sk_B))
% 3.09/3.28        | ~ (v3_pre_topc @ sk_B @ sk_A))),
% 3.09/3.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.09/3.28  thf('1', plain,
% 3.09/3.28      (~
% 3.09/3.28       (((k2_tops_1 @ sk_A @ sk_B)
% 3.09/3.28          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 3.09/3.28             (k2_pre_topc @ sk_A @ sk_B) @ sk_B))) | 
% 3.09/3.28       ~ ((v3_pre_topc @ sk_B @ sk_A))),
% 3.09/3.28      inference('split', [status(esa)], ['0'])).
% 3.09/3.28  thf('2', plain,
% 3.09/3.28      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.09/3.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.09/3.28  thf('3', plain,
% 3.09/3.28      ((((k2_tops_1 @ sk_A @ sk_B)
% 3.09/3.28          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 3.09/3.28             (k2_pre_topc @ sk_A @ sk_B) @ sk_B))
% 3.09/3.28        | (v3_pre_topc @ sk_B @ sk_A))),
% 3.09/3.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.09/3.28  thf('4', plain,
% 3.09/3.28      (((v3_pre_topc @ sk_B @ sk_A)) <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 3.09/3.28      inference('split', [status(esa)], ['3'])).
% 3.09/3.28  thf('5', plain,
% 3.09/3.28      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.09/3.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.09/3.28  thf(t56_tops_1, axiom,
% 3.09/3.28    (![A:$i]:
% 3.09/3.28     ( ( l1_pre_topc @ A ) =>
% 3.09/3.28       ( ![B:$i]:
% 3.09/3.28         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 3.09/3.28           ( ![C:$i]:
% 3.09/3.28             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 3.09/3.28               ( ( ( v3_pre_topc @ B @ A ) & ( r1_tarski @ B @ C ) ) =>
% 3.09/3.28                 ( r1_tarski @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 3.09/3.28  thf('6', plain,
% 3.09/3.28      (![X50 : $i, X51 : $i, X52 : $i]:
% 3.09/3.28         (~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ (u1_struct_0 @ X51)))
% 3.09/3.28          | ~ (v3_pre_topc @ X50 @ X51)
% 3.09/3.28          | ~ (r1_tarski @ X50 @ X52)
% 3.09/3.28          | (r1_tarski @ X50 @ (k1_tops_1 @ X51 @ X52))
% 3.09/3.28          | ~ (m1_subset_1 @ X52 @ (k1_zfmisc_1 @ (u1_struct_0 @ X51)))
% 3.09/3.28          | ~ (l1_pre_topc @ X51))),
% 3.09/3.29      inference('cnf', [status(esa)], [t56_tops_1])).
% 3.09/3.29  thf('7', plain,
% 3.09/3.29      (![X0 : $i]:
% 3.09/3.29         (~ (l1_pre_topc @ sk_A)
% 3.09/3.29          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 3.09/3.29          | (r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ X0))
% 3.09/3.29          | ~ (r1_tarski @ sk_B @ X0)
% 3.09/3.29          | ~ (v3_pre_topc @ sk_B @ sk_A))),
% 3.09/3.29      inference('sup-', [status(thm)], ['5', '6'])).
% 3.09/3.29  thf('8', plain, ((l1_pre_topc @ sk_A)),
% 3.09/3.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.09/3.29  thf('9', plain,
% 3.09/3.29      (![X0 : $i]:
% 3.09/3.29         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 3.09/3.29          | (r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ X0))
% 3.09/3.29          | ~ (r1_tarski @ sk_B @ X0)
% 3.09/3.29          | ~ (v3_pre_topc @ sk_B @ sk_A))),
% 3.09/3.29      inference('demod', [status(thm)], ['7', '8'])).
% 3.09/3.29  thf('10', plain,
% 3.09/3.29      ((![X0 : $i]:
% 3.09/3.29          (~ (r1_tarski @ sk_B @ X0)
% 3.09/3.29           | (r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ X0))
% 3.09/3.29           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))
% 3.09/3.29         <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 3.09/3.29      inference('sup-', [status(thm)], ['4', '9'])).
% 3.09/3.29  thf('11', plain,
% 3.09/3.29      ((((r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 3.09/3.29         | ~ (r1_tarski @ sk_B @ sk_B))) <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 3.09/3.29      inference('sup-', [status(thm)], ['2', '10'])).
% 3.09/3.29  thf(d10_xboole_0, axiom,
% 3.09/3.29    (![A:$i,B:$i]:
% 3.09/3.29     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 3.09/3.29  thf('12', plain,
% 3.09/3.29      (![X12 : $i, X13 : $i]: ((r1_tarski @ X12 @ X13) | ((X12) != (X13)))),
% 3.09/3.29      inference('cnf', [status(esa)], [d10_xboole_0])).
% 3.09/3.29  thf('13', plain, (![X13 : $i]: (r1_tarski @ X13 @ X13)),
% 3.09/3.29      inference('simplify', [status(thm)], ['12'])).
% 3.09/3.29  thf('14', plain,
% 3.09/3.29      (((r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))
% 3.09/3.29         <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 3.09/3.29      inference('demod', [status(thm)], ['11', '13'])).
% 3.09/3.29  thf('15', plain,
% 3.09/3.29      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.09/3.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.09/3.29  thf(t74_tops_1, axiom,
% 3.09/3.29    (![A:$i]:
% 3.09/3.29     ( ( l1_pre_topc @ A ) =>
% 3.09/3.29       ( ![B:$i]:
% 3.09/3.29         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 3.09/3.29           ( ( k1_tops_1 @ A @ B ) =
% 3.09/3.29             ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 3.09/3.29  thf('16', plain,
% 3.09/3.29      (![X57 : $i, X58 : $i]:
% 3.09/3.29         (~ (m1_subset_1 @ X57 @ (k1_zfmisc_1 @ (u1_struct_0 @ X58)))
% 3.09/3.29          | ((k1_tops_1 @ X58 @ X57)
% 3.09/3.29              = (k7_subset_1 @ (u1_struct_0 @ X58) @ X57 @ 
% 3.09/3.29                 (k2_tops_1 @ X58 @ X57)))
% 3.09/3.29          | ~ (l1_pre_topc @ X58))),
% 3.09/3.29      inference('cnf', [status(esa)], [t74_tops_1])).
% 3.09/3.29  thf('17', plain,
% 3.09/3.29      ((~ (l1_pre_topc @ sk_A)
% 3.09/3.29        | ((k1_tops_1 @ sk_A @ sk_B)
% 3.09/3.29            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 3.09/3.29               (k2_tops_1 @ sk_A @ sk_B))))),
% 3.09/3.29      inference('sup-', [status(thm)], ['15', '16'])).
% 3.09/3.29  thf('18', plain, ((l1_pre_topc @ sk_A)),
% 3.09/3.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.09/3.29  thf('19', plain,
% 3.09/3.29      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.09/3.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.09/3.29  thf(redefinition_k7_subset_1, axiom,
% 3.09/3.29    (![A:$i,B:$i,C:$i]:
% 3.09/3.29     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 3.09/3.29       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 3.09/3.29  thf('20', plain,
% 3.09/3.29      (![X36 : $i, X37 : $i, X38 : $i]:
% 3.09/3.29         (~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ X37))
% 3.09/3.29          | ((k7_subset_1 @ X37 @ X36 @ X38) = (k4_xboole_0 @ X36 @ X38)))),
% 3.09/3.29      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 3.09/3.29  thf('21', plain,
% 3.09/3.29      (![X0 : $i]:
% 3.09/3.29         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 3.09/3.29           = (k4_xboole_0 @ sk_B @ X0))),
% 3.09/3.29      inference('sup-', [status(thm)], ['19', '20'])).
% 3.09/3.29  thf('22', plain,
% 3.09/3.29      (((k1_tops_1 @ sk_A @ sk_B)
% 3.09/3.29         = (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 3.09/3.29      inference('demod', [status(thm)], ['17', '18', '21'])).
% 3.09/3.29  thf(t36_xboole_1, axiom,
% 3.09/3.29    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 3.09/3.29  thf('23', plain,
% 3.09/3.29      (![X20 : $i, X21 : $i]: (r1_tarski @ (k4_xboole_0 @ X20 @ X21) @ X20)),
% 3.09/3.29      inference('cnf', [status(esa)], [t36_xboole_1])).
% 3.09/3.29  thf('24', plain,
% 3.09/3.29      (![X12 : $i, X14 : $i]:
% 3.09/3.29         (((X12) = (X14))
% 3.09/3.29          | ~ (r1_tarski @ X14 @ X12)
% 3.09/3.29          | ~ (r1_tarski @ X12 @ X14))),
% 3.09/3.29      inference('cnf', [status(esa)], [d10_xboole_0])).
% 3.09/3.29  thf('25', plain,
% 3.09/3.29      (![X0 : $i, X1 : $i]:
% 3.09/3.29         (~ (r1_tarski @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 3.09/3.29          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 3.09/3.29      inference('sup-', [status(thm)], ['23', '24'])).
% 3.09/3.29  thf('26', plain,
% 3.09/3.29      ((~ (r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 3.09/3.29        | ((sk_B) = (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))),
% 3.09/3.29      inference('sup-', [status(thm)], ['22', '25'])).
% 3.09/3.29  thf('27', plain,
% 3.09/3.29      (((k1_tops_1 @ sk_A @ sk_B)
% 3.09/3.29         = (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 3.09/3.29      inference('demod', [status(thm)], ['17', '18', '21'])).
% 3.09/3.29  thf('28', plain,
% 3.09/3.29      ((~ (r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 3.09/3.29        | ((sk_B) = (k1_tops_1 @ sk_A @ sk_B)))),
% 3.09/3.29      inference('demod', [status(thm)], ['26', '27'])).
% 3.09/3.29  thf('29', plain,
% 3.09/3.29      ((((sk_B) = (k1_tops_1 @ sk_A @ sk_B)))
% 3.09/3.29         <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 3.09/3.29      inference('sup-', [status(thm)], ['14', '28'])).
% 3.09/3.29  thf('30', plain,
% 3.09/3.29      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.09/3.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.09/3.29  thf(l78_tops_1, axiom,
% 3.09/3.29    (![A:$i]:
% 3.09/3.29     ( ( l1_pre_topc @ A ) =>
% 3.09/3.29       ( ![B:$i]:
% 3.09/3.29         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 3.09/3.29           ( ( k2_tops_1 @ A @ B ) =
% 3.09/3.29             ( k7_subset_1 @
% 3.09/3.29               ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 3.09/3.29               ( k1_tops_1 @ A @ B ) ) ) ) ) ))).
% 3.09/3.29  thf('31', plain,
% 3.09/3.29      (![X48 : $i, X49 : $i]:
% 3.09/3.29         (~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ (u1_struct_0 @ X49)))
% 3.09/3.29          | ((k2_tops_1 @ X49 @ X48)
% 3.09/3.29              = (k7_subset_1 @ (u1_struct_0 @ X49) @ 
% 3.09/3.29                 (k2_pre_topc @ X49 @ X48) @ (k1_tops_1 @ X49 @ X48)))
% 3.09/3.29          | ~ (l1_pre_topc @ X49))),
% 3.09/3.29      inference('cnf', [status(esa)], [l78_tops_1])).
% 3.09/3.29  thf('32', plain,
% 3.09/3.29      ((~ (l1_pre_topc @ sk_A)
% 3.09/3.29        | ((k2_tops_1 @ sk_A @ sk_B)
% 3.09/3.29            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 3.09/3.29               (k2_pre_topc @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ sk_B))))),
% 3.09/3.29      inference('sup-', [status(thm)], ['30', '31'])).
% 3.09/3.29  thf('33', plain, ((l1_pre_topc @ sk_A)),
% 3.09/3.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.09/3.29  thf('34', plain,
% 3.09/3.29      (((k2_tops_1 @ sk_A @ sk_B)
% 3.09/3.29         = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 3.09/3.29            (k1_tops_1 @ sk_A @ sk_B)))),
% 3.09/3.29      inference('demod', [status(thm)], ['32', '33'])).
% 3.09/3.29  thf('35', plain,
% 3.09/3.29      ((((k2_tops_1 @ sk_A @ sk_B)
% 3.09/3.29          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 3.09/3.29             (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))
% 3.09/3.29         <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 3.09/3.29      inference('sup+', [status(thm)], ['29', '34'])).
% 3.09/3.29  thf('36', plain,
% 3.09/3.29      ((((k2_tops_1 @ sk_A @ sk_B)
% 3.09/3.29          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 3.09/3.29              (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))
% 3.09/3.29         <= (~
% 3.09/3.29             (((k2_tops_1 @ sk_A @ sk_B)
% 3.09/3.29                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 3.09/3.29                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 3.09/3.29      inference('split', [status(esa)], ['0'])).
% 3.09/3.29  thf('37', plain,
% 3.09/3.29      ((((k2_tops_1 @ sk_A @ sk_B) != (k2_tops_1 @ sk_A @ sk_B)))
% 3.09/3.29         <= (~
% 3.09/3.29             (((k2_tops_1 @ sk_A @ sk_B)
% 3.09/3.29                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 3.09/3.29                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))) & 
% 3.09/3.29             ((v3_pre_topc @ sk_B @ sk_A)))),
% 3.09/3.29      inference('sup-', [status(thm)], ['35', '36'])).
% 3.09/3.29  thf('38', plain,
% 3.09/3.29      ((((k2_tops_1 @ sk_A @ sk_B)
% 3.09/3.29          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 3.09/3.29             (k2_pre_topc @ sk_A @ sk_B) @ sk_B))) | 
% 3.09/3.29       ~ ((v3_pre_topc @ sk_B @ sk_A))),
% 3.09/3.29      inference('simplify', [status(thm)], ['37'])).
% 3.09/3.29  thf('39', plain,
% 3.09/3.29      ((((k2_tops_1 @ sk_A @ sk_B)
% 3.09/3.29          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 3.09/3.29             (k2_pre_topc @ sk_A @ sk_B) @ sk_B))) | 
% 3.09/3.29       ((v3_pre_topc @ sk_B @ sk_A))),
% 3.09/3.29      inference('split', [status(esa)], ['3'])).
% 3.09/3.29  thf(d4_xboole_0, axiom,
% 3.09/3.29    (![A:$i,B:$i,C:$i]:
% 3.09/3.29     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 3.09/3.29       ( ![D:$i]:
% 3.09/3.29         ( ( r2_hidden @ D @ C ) <=>
% 3.09/3.29           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 3.09/3.29  thf('40', plain,
% 3.09/3.29      (![X1 : $i, X2 : $i, X5 : $i]:
% 3.09/3.29         (((X5) = (k3_xboole_0 @ X1 @ X2))
% 3.09/3.29          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X1)
% 3.09/3.29          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 3.09/3.29      inference('cnf', [status(esa)], [d4_xboole_0])).
% 3.09/3.29  thf(t12_setfam_1, axiom,
% 3.09/3.29    (![A:$i,B:$i]:
% 3.09/3.29     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 3.09/3.29  thf('41', plain,
% 3.09/3.29      (![X39 : $i, X40 : $i]:
% 3.09/3.29         ((k1_setfam_1 @ (k2_tarski @ X39 @ X40)) = (k3_xboole_0 @ X39 @ X40))),
% 3.09/3.29      inference('cnf', [status(esa)], [t12_setfam_1])).
% 3.09/3.29  thf('42', plain,
% 3.09/3.29      (![X1 : $i, X2 : $i, X5 : $i]:
% 3.09/3.29         (((X5) = (k1_setfam_1 @ (k2_tarski @ X1 @ X2)))
% 3.09/3.29          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X1)
% 3.09/3.29          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 3.09/3.29      inference('demod', [status(thm)], ['40', '41'])).
% 3.09/3.29  thf(t3_boole, axiom,
% 3.09/3.29    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 3.09/3.29  thf('43', plain, (![X22 : $i]: ((k4_xboole_0 @ X22 @ k1_xboole_0) = (X22))),
% 3.09/3.29      inference('cnf', [status(esa)], [t3_boole])).
% 3.09/3.29  thf(d5_xboole_0, axiom,
% 3.09/3.29    (![A:$i,B:$i,C:$i]:
% 3.09/3.29     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 3.09/3.29       ( ![D:$i]:
% 3.09/3.29         ( ( r2_hidden @ D @ C ) <=>
% 3.09/3.29           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 3.09/3.29  thf('44', plain,
% 3.09/3.29      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 3.09/3.29         (~ (r2_hidden @ X10 @ X9)
% 3.09/3.29          | ~ (r2_hidden @ X10 @ X8)
% 3.09/3.29          | ((X9) != (k4_xboole_0 @ X7 @ X8)))),
% 3.09/3.29      inference('cnf', [status(esa)], [d5_xboole_0])).
% 3.09/3.29  thf('45', plain,
% 3.09/3.29      (![X7 : $i, X8 : $i, X10 : $i]:
% 3.09/3.29         (~ (r2_hidden @ X10 @ X8)
% 3.09/3.29          | ~ (r2_hidden @ X10 @ (k4_xboole_0 @ X7 @ X8)))),
% 3.09/3.29      inference('simplify', [status(thm)], ['44'])).
% 3.09/3.29  thf('46', plain,
% 3.09/3.29      (![X0 : $i, X1 : $i]:
% 3.09/3.29         (~ (r2_hidden @ X1 @ X0) | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 3.09/3.29      inference('sup-', [status(thm)], ['43', '45'])).
% 3.09/3.29  thf('47', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 3.09/3.29      inference('condensation', [status(thm)], ['46'])).
% 3.09/3.29  thf('48', plain,
% 3.09/3.29      (![X0 : $i, X1 : $i]:
% 3.09/3.29         ((r2_hidden @ (sk_D @ k1_xboole_0 @ X1 @ X0) @ X0)
% 3.09/3.29          | ((k1_xboole_0) = (k1_setfam_1 @ (k2_tarski @ X0 @ X1))))),
% 3.09/3.29      inference('sup-', [status(thm)], ['42', '47'])).
% 3.09/3.29  thf('49', plain,
% 3.09/3.29      (![X1 : $i, X2 : $i, X5 : $i]:
% 3.09/3.29         (((X5) = (k3_xboole_0 @ X1 @ X2))
% 3.09/3.29          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X2)
% 3.09/3.29          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 3.09/3.29      inference('cnf', [status(esa)], [d4_xboole_0])).
% 3.09/3.29  thf('50', plain,
% 3.09/3.29      (![X39 : $i, X40 : $i]:
% 3.09/3.29         ((k1_setfam_1 @ (k2_tarski @ X39 @ X40)) = (k3_xboole_0 @ X39 @ X40))),
% 3.09/3.29      inference('cnf', [status(esa)], [t12_setfam_1])).
% 3.09/3.29  thf('51', plain,
% 3.09/3.29      (![X1 : $i, X2 : $i, X5 : $i]:
% 3.09/3.29         (((X5) = (k1_setfam_1 @ (k2_tarski @ X1 @ X2)))
% 3.09/3.29          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X2)
% 3.09/3.29          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 3.09/3.29      inference('demod', [status(thm)], ['49', '50'])).
% 3.09/3.29  thf('52', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 3.09/3.29      inference('condensation', [status(thm)], ['46'])).
% 3.09/3.29  thf('53', plain,
% 3.09/3.29      (![X0 : $i, X1 : $i]:
% 3.09/3.29         ((r2_hidden @ (sk_D @ k1_xboole_0 @ X1 @ X0) @ X1)
% 3.09/3.29          | ((k1_xboole_0) = (k1_setfam_1 @ (k2_tarski @ X0 @ X1))))),
% 3.09/3.29      inference('sup-', [status(thm)], ['51', '52'])).
% 3.09/3.29  thf('54', plain,
% 3.09/3.29      ((((k2_tops_1 @ sk_A @ sk_B)
% 3.09/3.29          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 3.09/3.29             (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))
% 3.09/3.29         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 3.09/3.29                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 3.09/3.29                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 3.09/3.29      inference('split', [status(esa)], ['3'])).
% 3.09/3.29  thf('55', plain,
% 3.09/3.29      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.09/3.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.09/3.29  thf(dt_k2_tops_1, axiom,
% 3.09/3.29    (![A:$i,B:$i]:
% 3.09/3.29     ( ( ( l1_pre_topc @ A ) & 
% 3.09/3.29         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 3.09/3.29       ( m1_subset_1 @
% 3.09/3.29         ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 3.09/3.29  thf('56', plain,
% 3.09/3.29      (![X44 : $i, X45 : $i]:
% 3.09/3.29         (~ (l1_pre_topc @ X44)
% 3.09/3.29          | ~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (u1_struct_0 @ X44)))
% 3.09/3.29          | (m1_subset_1 @ (k2_tops_1 @ X44 @ X45) @ 
% 3.09/3.29             (k1_zfmisc_1 @ (u1_struct_0 @ X44))))),
% 3.09/3.29      inference('cnf', [status(esa)], [dt_k2_tops_1])).
% 3.09/3.29  thf('57', plain,
% 3.09/3.29      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 3.09/3.29         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 3.09/3.29        | ~ (l1_pre_topc @ sk_A))),
% 3.09/3.29      inference('sup-', [status(thm)], ['55', '56'])).
% 3.09/3.29  thf('58', plain, ((l1_pre_topc @ sk_A)),
% 3.09/3.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.09/3.29  thf('59', plain,
% 3.09/3.29      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 3.09/3.29        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.09/3.29      inference('demod', [status(thm)], ['57', '58'])).
% 3.09/3.29  thf('60', plain,
% 3.09/3.29      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.09/3.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.09/3.29  thf(dt_k4_subset_1, axiom,
% 3.09/3.29    (![A:$i,B:$i,C:$i]:
% 3.09/3.29     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 3.09/3.29         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 3.09/3.29       ( m1_subset_1 @ ( k4_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 3.09/3.29  thf('61', plain,
% 3.09/3.29      (![X31 : $i, X32 : $i, X33 : $i]:
% 3.09/3.29         (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ X32))
% 3.09/3.29          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ X32))
% 3.09/3.29          | (m1_subset_1 @ (k4_subset_1 @ X32 @ X31 @ X33) @ 
% 3.09/3.29             (k1_zfmisc_1 @ X32)))),
% 3.09/3.29      inference('cnf', [status(esa)], [dt_k4_subset_1])).
% 3.09/3.29  thf('62', plain,
% 3.09/3.29      (![X0 : $i]:
% 3.09/3.29         ((m1_subset_1 @ (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0) @ 
% 3.09/3.29           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 3.09/3.29          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 3.09/3.29      inference('sup-', [status(thm)], ['60', '61'])).
% 3.09/3.29  thf('63', plain,
% 3.09/3.29      ((m1_subset_1 @ 
% 3.09/3.29        (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)) @ 
% 3.09/3.29        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.09/3.29      inference('sup-', [status(thm)], ['59', '62'])).
% 3.09/3.29  thf('64', plain,
% 3.09/3.29      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.09/3.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.09/3.29  thf(t65_tops_1, axiom,
% 3.09/3.29    (![A:$i]:
% 3.09/3.29     ( ( l1_pre_topc @ A ) =>
% 3.09/3.29       ( ![B:$i]:
% 3.09/3.29         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 3.09/3.29           ( ( k2_pre_topc @ A @ B ) =
% 3.09/3.29             ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 3.09/3.29  thf('65', plain,
% 3.09/3.29      (![X55 : $i, X56 : $i]:
% 3.09/3.29         (~ (m1_subset_1 @ X55 @ (k1_zfmisc_1 @ (u1_struct_0 @ X56)))
% 3.09/3.29          | ((k2_pre_topc @ X56 @ X55)
% 3.09/3.29              = (k4_subset_1 @ (u1_struct_0 @ X56) @ X55 @ 
% 3.09/3.29                 (k2_tops_1 @ X56 @ X55)))
% 3.09/3.29          | ~ (l1_pre_topc @ X56))),
% 3.09/3.29      inference('cnf', [status(esa)], [t65_tops_1])).
% 3.09/3.29  thf('66', plain,
% 3.09/3.29      ((~ (l1_pre_topc @ sk_A)
% 3.09/3.29        | ((k2_pre_topc @ sk_A @ sk_B)
% 3.09/3.29            = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 3.09/3.29               (k2_tops_1 @ sk_A @ sk_B))))),
% 3.09/3.29      inference('sup-', [status(thm)], ['64', '65'])).
% 3.09/3.29  thf('67', plain, ((l1_pre_topc @ sk_A)),
% 3.09/3.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.09/3.29  thf('68', plain,
% 3.09/3.29      (((k2_pre_topc @ sk_A @ sk_B)
% 3.09/3.29         = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 3.09/3.29            (k2_tops_1 @ sk_A @ sk_B)))),
% 3.09/3.29      inference('demod', [status(thm)], ['66', '67'])).
% 3.09/3.29  thf('69', plain,
% 3.09/3.29      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 3.09/3.29        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.09/3.29      inference('demod', [status(thm)], ['63', '68'])).
% 3.09/3.29  thf(t3_subset, axiom,
% 3.09/3.29    (![A:$i,B:$i]:
% 3.09/3.29     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 3.09/3.29  thf('70', plain,
% 3.09/3.29      (![X41 : $i, X42 : $i]:
% 3.09/3.29         ((r1_tarski @ X41 @ X42) | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ X42)))),
% 3.09/3.29      inference('cnf', [status(esa)], [t3_subset])).
% 3.09/3.29  thf('71', plain,
% 3.09/3.29      ((r1_tarski @ (k2_pre_topc @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A))),
% 3.09/3.29      inference('sup-', [status(thm)], ['69', '70'])).
% 3.09/3.29  thf(t28_xboole_1, axiom,
% 3.09/3.29    (![A:$i,B:$i]:
% 3.09/3.29     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 3.09/3.29  thf('72', plain,
% 3.09/3.29      (![X17 : $i, X18 : $i]:
% 3.09/3.29         (((k3_xboole_0 @ X17 @ X18) = (X17)) | ~ (r1_tarski @ X17 @ X18))),
% 3.09/3.29      inference('cnf', [status(esa)], [t28_xboole_1])).
% 3.09/3.29  thf('73', plain,
% 3.09/3.29      (![X39 : $i, X40 : $i]:
% 3.09/3.29         ((k1_setfam_1 @ (k2_tarski @ X39 @ X40)) = (k3_xboole_0 @ X39 @ X40))),
% 3.09/3.29      inference('cnf', [status(esa)], [t12_setfam_1])).
% 3.09/3.29  thf('74', plain,
% 3.09/3.29      (![X17 : $i, X18 : $i]:
% 3.09/3.29         (((k1_setfam_1 @ (k2_tarski @ X17 @ X18)) = (X17))
% 3.09/3.29          | ~ (r1_tarski @ X17 @ X18))),
% 3.09/3.29      inference('demod', [status(thm)], ['72', '73'])).
% 3.09/3.29  thf('75', plain,
% 3.09/3.29      (((k1_setfam_1 @ 
% 3.09/3.29         (k2_tarski @ (k2_pre_topc @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A)))
% 3.09/3.29         = (k2_pre_topc @ sk_A @ sk_B))),
% 3.09/3.29      inference('sup-', [status(thm)], ['71', '74'])).
% 3.09/3.29  thf(commutativity_k2_tarski, axiom,
% 3.09/3.29    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 3.09/3.29  thf('76', plain,
% 3.09/3.29      (![X25 : $i, X26 : $i]:
% 3.09/3.29         ((k2_tarski @ X26 @ X25) = (k2_tarski @ X25 @ X26))),
% 3.09/3.29      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 3.09/3.29  thf('77', plain,
% 3.09/3.29      (((k1_setfam_1 @ 
% 3.09/3.29         (k2_tarski @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B)))
% 3.09/3.29         = (k2_pre_topc @ sk_A @ sk_B))),
% 3.09/3.29      inference('demod', [status(thm)], ['75', '76'])).
% 3.09/3.29  thf(t100_xboole_1, axiom,
% 3.09/3.29    (![A:$i,B:$i]:
% 3.09/3.29     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 3.09/3.29  thf('78', plain,
% 3.09/3.29      (![X15 : $i, X16 : $i]:
% 3.09/3.29         ((k4_xboole_0 @ X15 @ X16)
% 3.09/3.29           = (k5_xboole_0 @ X15 @ (k3_xboole_0 @ X15 @ X16)))),
% 3.09/3.29      inference('cnf', [status(esa)], [t100_xboole_1])).
% 3.09/3.29  thf('79', plain,
% 3.09/3.29      (![X39 : $i, X40 : $i]:
% 3.09/3.29         ((k1_setfam_1 @ (k2_tarski @ X39 @ X40)) = (k3_xboole_0 @ X39 @ X40))),
% 3.09/3.29      inference('cnf', [status(esa)], [t12_setfam_1])).
% 3.09/3.29  thf('80', plain,
% 3.09/3.29      (![X15 : $i, X16 : $i]:
% 3.09/3.29         ((k4_xboole_0 @ X15 @ X16)
% 3.09/3.29           = (k5_xboole_0 @ X15 @ (k1_setfam_1 @ (k2_tarski @ X15 @ X16))))),
% 3.09/3.29      inference('demod', [status(thm)], ['78', '79'])).
% 3.09/3.29  thf('81', plain,
% 3.09/3.29      (((k4_xboole_0 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B))
% 3.09/3.29         = (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B)))),
% 3.09/3.29      inference('sup+', [status(thm)], ['77', '80'])).
% 3.09/3.29  thf(t48_xboole_1, axiom,
% 3.09/3.29    (![A:$i,B:$i]:
% 3.09/3.29     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 3.09/3.29  thf('82', plain,
% 3.09/3.29      (![X23 : $i, X24 : $i]:
% 3.09/3.29         ((k4_xboole_0 @ X23 @ (k4_xboole_0 @ X23 @ X24))
% 3.09/3.29           = (k3_xboole_0 @ X23 @ X24))),
% 3.09/3.29      inference('cnf', [status(esa)], [t48_xboole_1])).
% 3.09/3.29  thf('83', plain,
% 3.09/3.29      (![X39 : $i, X40 : $i]:
% 3.09/3.29         ((k1_setfam_1 @ (k2_tarski @ X39 @ X40)) = (k3_xboole_0 @ X39 @ X40))),
% 3.09/3.29      inference('cnf', [status(esa)], [t12_setfam_1])).
% 3.09/3.29  thf('84', plain,
% 3.09/3.29      (![X23 : $i, X24 : $i]:
% 3.09/3.29         ((k4_xboole_0 @ X23 @ (k4_xboole_0 @ X23 @ X24))
% 3.09/3.29           = (k1_setfam_1 @ (k2_tarski @ X23 @ X24)))),
% 3.09/3.29      inference('demod', [status(thm)], ['82', '83'])).
% 3.09/3.29  thf('85', plain,
% 3.09/3.29      (((k4_xboole_0 @ (u1_struct_0 @ sk_A) @ 
% 3.09/3.29         (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B)))
% 3.09/3.29         = (k1_setfam_1 @ 
% 3.09/3.29            (k2_tarski @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B))))),
% 3.09/3.29      inference('sup+', [status(thm)], ['81', '84'])).
% 3.09/3.29  thf('86', plain,
% 3.09/3.29      (((k1_setfam_1 @ 
% 3.09/3.29         (k2_tarski @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B)))
% 3.09/3.29         = (k2_pre_topc @ sk_A @ sk_B))),
% 3.09/3.29      inference('demod', [status(thm)], ['75', '76'])).
% 3.09/3.29  thf('87', plain,
% 3.09/3.29      (((k4_xboole_0 @ (u1_struct_0 @ sk_A) @ 
% 3.09/3.29         (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B)))
% 3.09/3.29         = (k2_pre_topc @ sk_A @ sk_B))),
% 3.09/3.29      inference('demod', [status(thm)], ['85', '86'])).
% 3.09/3.29  thf('88', plain,
% 3.09/3.29      (![X20 : $i, X21 : $i]: (r1_tarski @ (k4_xboole_0 @ X20 @ X21) @ X20)),
% 3.09/3.29      inference('cnf', [status(esa)], [t36_xboole_1])).
% 3.09/3.29  thf('89', plain,
% 3.09/3.29      (![X41 : $i, X43 : $i]:
% 3.09/3.29         ((m1_subset_1 @ X41 @ (k1_zfmisc_1 @ X43)) | ~ (r1_tarski @ X41 @ X43))),
% 3.09/3.29      inference('cnf', [status(esa)], [t3_subset])).
% 3.09/3.29  thf('90', plain,
% 3.09/3.29      (![X0 : $i, X1 : $i]:
% 3.09/3.29         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 3.09/3.29      inference('sup-', [status(thm)], ['88', '89'])).
% 3.09/3.29  thf('91', plain,
% 3.09/3.29      (![X36 : $i, X37 : $i, X38 : $i]:
% 3.09/3.29         (~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ X37))
% 3.09/3.29          | ((k7_subset_1 @ X37 @ X36 @ X38) = (k4_xboole_0 @ X36 @ X38)))),
% 3.09/3.29      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 3.09/3.29  thf('92', plain,
% 3.09/3.29      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.09/3.29         ((k7_subset_1 @ X0 @ (k4_xboole_0 @ X0 @ X1) @ X2)
% 3.09/3.29           = (k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X2))),
% 3.09/3.29      inference('sup-', [status(thm)], ['90', '91'])).
% 3.09/3.29  thf('93', plain,
% 3.09/3.29      (![X7 : $i, X8 : $i, X10 : $i]:
% 3.09/3.29         (~ (r2_hidden @ X10 @ X8)
% 3.09/3.29          | ~ (r2_hidden @ X10 @ (k4_xboole_0 @ X7 @ X8)))),
% 3.09/3.29      inference('simplify', [status(thm)], ['44'])).
% 3.09/3.29  thf('94', plain,
% 3.09/3.29      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 3.09/3.29         (~ (r2_hidden @ X3 @ (k7_subset_1 @ X2 @ (k4_xboole_0 @ X2 @ X1) @ X0))
% 3.09/3.29          | ~ (r2_hidden @ X3 @ X0))),
% 3.09/3.29      inference('sup-', [status(thm)], ['92', '93'])).
% 3.09/3.29  thf('95', plain,
% 3.09/3.29      (![X0 : $i, X1 : $i]:
% 3.09/3.29         (~ (r2_hidden @ X1 @ 
% 3.09/3.29             (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 3.09/3.29              (k2_pre_topc @ sk_A @ sk_B) @ X0))
% 3.09/3.29          | ~ (r2_hidden @ X1 @ X0))),
% 3.09/3.29      inference('sup-', [status(thm)], ['87', '94'])).
% 3.09/3.29  thf('96', plain,
% 3.09/3.29      ((![X0 : $i]:
% 3.09/3.29          (~ (r2_hidden @ X0 @ (k2_tops_1 @ sk_A @ sk_B))
% 3.09/3.29           | ~ (r2_hidden @ X0 @ sk_B)))
% 3.09/3.29         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 3.09/3.29                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 3.09/3.29                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 3.09/3.29      inference('sup-', [status(thm)], ['54', '95'])).
% 3.09/3.29  thf('97', plain,
% 3.09/3.29      ((![X0 : $i]:
% 3.09/3.29          (((k1_xboole_0)
% 3.09/3.29             = (k1_setfam_1 @ (k2_tarski @ X0 @ (k2_tops_1 @ sk_A @ sk_B))))
% 3.09/3.29           | ~ (r2_hidden @ 
% 3.09/3.29                (sk_D @ k1_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ X0) @ sk_B)))
% 3.09/3.29         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 3.09/3.29                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 3.09/3.29                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 3.09/3.29      inference('sup-', [status(thm)], ['53', '96'])).
% 3.09/3.29  thf('98', plain,
% 3.09/3.29      (((((k1_xboole_0)
% 3.09/3.29           = (k1_setfam_1 @ (k2_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))
% 3.09/3.29         | ((k1_xboole_0)
% 3.09/3.29             = (k1_setfam_1 @ (k2_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))))
% 3.09/3.29         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 3.09/3.29                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 3.09/3.29                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 3.09/3.29      inference('sup-', [status(thm)], ['48', '97'])).
% 3.09/3.29  thf('99', plain,
% 3.09/3.29      ((((k1_xboole_0)
% 3.09/3.29          = (k1_setfam_1 @ (k2_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))))
% 3.09/3.29         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 3.09/3.29                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 3.09/3.29                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 3.09/3.29      inference('simplify', [status(thm)], ['98'])).
% 3.09/3.29  thf('100', plain,
% 3.09/3.29      (![X23 : $i, X24 : $i]:
% 3.09/3.29         ((k4_xboole_0 @ X23 @ (k4_xboole_0 @ X23 @ X24))
% 3.09/3.29           = (k1_setfam_1 @ (k2_tarski @ X23 @ X24)))),
% 3.09/3.29      inference('demod', [status(thm)], ['82', '83'])).
% 3.09/3.29  thf('101', plain,
% 3.09/3.29      (![X23 : $i, X24 : $i]:
% 3.09/3.29         ((k4_xboole_0 @ X23 @ (k4_xboole_0 @ X23 @ X24))
% 3.09/3.29           = (k1_setfam_1 @ (k2_tarski @ X23 @ X24)))),
% 3.09/3.29      inference('demod', [status(thm)], ['82', '83'])).
% 3.09/3.29  thf('102', plain,
% 3.09/3.29      (![X0 : $i, X1 : $i]:
% 3.09/3.29         ((k4_xboole_0 @ X1 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0)))
% 3.09/3.29           = (k1_setfam_1 @ (k2_tarski @ X1 @ (k4_xboole_0 @ X1 @ X0))))),
% 3.09/3.29      inference('sup+', [status(thm)], ['100', '101'])).
% 3.09/3.29  thf('103', plain,
% 3.09/3.29      (![X20 : $i, X21 : $i]: (r1_tarski @ (k4_xboole_0 @ X20 @ X21) @ X20)),
% 3.09/3.29      inference('cnf', [status(esa)], [t36_xboole_1])).
% 3.09/3.29  thf('104', plain,
% 3.09/3.29      (![X17 : $i, X18 : $i]:
% 3.09/3.29         (((k1_setfam_1 @ (k2_tarski @ X17 @ X18)) = (X17))
% 3.09/3.29          | ~ (r1_tarski @ X17 @ X18))),
% 3.09/3.29      inference('demod', [status(thm)], ['72', '73'])).
% 3.09/3.29  thf('105', plain,
% 3.09/3.29      (![X0 : $i, X1 : $i]:
% 3.09/3.29         ((k1_setfam_1 @ (k2_tarski @ (k4_xboole_0 @ X0 @ X1) @ X0))
% 3.09/3.29           = (k4_xboole_0 @ X0 @ X1))),
% 3.09/3.29      inference('sup-', [status(thm)], ['103', '104'])).
% 3.09/3.29  thf('106', plain,
% 3.09/3.29      (![X25 : $i, X26 : $i]:
% 3.09/3.29         ((k2_tarski @ X26 @ X25) = (k2_tarski @ X25 @ X26))),
% 3.09/3.29      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 3.09/3.29  thf('107', plain,
% 3.09/3.29      (![X0 : $i, X1 : $i]:
% 3.09/3.29         ((k1_setfam_1 @ (k2_tarski @ X0 @ (k4_xboole_0 @ X0 @ X1)))
% 3.09/3.29           = (k4_xboole_0 @ X0 @ X1))),
% 3.09/3.29      inference('demod', [status(thm)], ['105', '106'])).
% 3.09/3.29  thf('108', plain,
% 3.09/3.29      (![X0 : $i, X1 : $i]:
% 3.09/3.29         ((k4_xboole_0 @ X1 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0)))
% 3.09/3.29           = (k4_xboole_0 @ X1 @ X0))),
% 3.09/3.29      inference('sup+', [status(thm)], ['102', '107'])).
% 3.09/3.29  thf('109', plain,
% 3.09/3.29      ((((k4_xboole_0 @ sk_B @ k1_xboole_0)
% 3.09/3.29          = (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))
% 3.09/3.29         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 3.09/3.29                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 3.09/3.29                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 3.09/3.29      inference('sup+', [status(thm)], ['99', '108'])).
% 3.09/3.29  thf('110', plain, (![X22 : $i]: ((k4_xboole_0 @ X22 @ k1_xboole_0) = (X22))),
% 3.09/3.29      inference('cnf', [status(esa)], [t3_boole])).
% 3.09/3.29  thf('111', plain,
% 3.09/3.29      ((((sk_B) = (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))
% 3.09/3.29         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 3.09/3.29                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 3.09/3.29                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 3.09/3.29      inference('demod', [status(thm)], ['109', '110'])).
% 3.09/3.29  thf('112', plain,
% 3.09/3.29      (((k1_tops_1 @ sk_A @ sk_B)
% 3.09/3.29         = (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 3.09/3.29      inference('demod', [status(thm)], ['17', '18', '21'])).
% 3.09/3.29  thf('113', plain,
% 3.09/3.29      ((((k1_tops_1 @ sk_A @ sk_B) = (sk_B)))
% 3.09/3.29         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 3.09/3.29                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 3.09/3.29                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 3.09/3.29      inference('sup+', [status(thm)], ['111', '112'])).
% 3.09/3.29  thf('114', plain,
% 3.09/3.29      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.09/3.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.09/3.29  thf(fc9_tops_1, axiom,
% 3.09/3.29    (![A:$i,B:$i]:
% 3.09/3.29     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 3.09/3.29         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 3.09/3.29       ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ))).
% 3.09/3.29  thf('115', plain,
% 3.09/3.29      (![X46 : $i, X47 : $i]:
% 3.09/3.29         (~ (l1_pre_topc @ X46)
% 3.09/3.29          | ~ (v2_pre_topc @ X46)
% 3.09/3.29          | ~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ (u1_struct_0 @ X46)))
% 3.09/3.29          | (v3_pre_topc @ (k1_tops_1 @ X46 @ X47) @ X46))),
% 3.09/3.29      inference('cnf', [status(esa)], [fc9_tops_1])).
% 3.09/3.29  thf('116', plain,
% 3.09/3.29      (((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_B) @ sk_A)
% 3.09/3.29        | ~ (v2_pre_topc @ sk_A)
% 3.09/3.29        | ~ (l1_pre_topc @ sk_A))),
% 3.09/3.29      inference('sup-', [status(thm)], ['114', '115'])).
% 3.09/3.29  thf('117', plain, ((v2_pre_topc @ sk_A)),
% 3.09/3.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.09/3.29  thf('118', plain, ((l1_pre_topc @ sk_A)),
% 3.09/3.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.09/3.29  thf('119', plain, ((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_B) @ sk_A)),
% 3.09/3.29      inference('demod', [status(thm)], ['116', '117', '118'])).
% 3.09/3.29  thf('120', plain,
% 3.09/3.29      (((v3_pre_topc @ sk_B @ sk_A))
% 3.09/3.29         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 3.09/3.29                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 3.09/3.29                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 3.09/3.29      inference('sup+', [status(thm)], ['113', '119'])).
% 3.09/3.29  thf('121', plain,
% 3.09/3.29      ((~ (v3_pre_topc @ sk_B @ sk_A)) <= (~ ((v3_pre_topc @ sk_B @ sk_A)))),
% 3.09/3.29      inference('split', [status(esa)], ['0'])).
% 3.09/3.29  thf('122', plain,
% 3.09/3.29      (~
% 3.09/3.29       (((k2_tops_1 @ sk_A @ sk_B)
% 3.09/3.29          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 3.09/3.29             (k2_pre_topc @ sk_A @ sk_B) @ sk_B))) | 
% 3.09/3.29       ((v3_pre_topc @ sk_B @ sk_A))),
% 3.09/3.29      inference('sup-', [status(thm)], ['120', '121'])).
% 3.09/3.29  thf('123', plain, ($false),
% 3.09/3.29      inference('sat_resolution*', [status(thm)], ['1', '38', '39', '122'])).
% 3.09/3.29  
% 3.09/3.29  % SZS output end Refutation
% 3.09/3.29  
% 3.09/3.29  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
