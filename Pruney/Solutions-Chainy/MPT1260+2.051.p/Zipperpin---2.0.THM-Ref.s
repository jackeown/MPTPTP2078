%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.cKQvaen1CY

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:30 EST 2020

% Result     : Theorem 19.02s
% Output     : Refutation 19.02s
% Verified   : 
% Statistics : Number of formulae       :  164 ( 550 expanded)
%              Number of leaves         :   39 ( 182 expanded)
%              Depth                    :   18
%              Number of atoms          : 1596 (6566 expanded)
%              Number of equality atoms :  102 ( 383 expanded)
%              Maximal formula depth    :   14 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

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
    ( ( ( k2_tops_1 @ sk_A @ sk_B_1 )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
    | ~ ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B_1 )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
    | ~ ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
    | ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( v3_pre_topc @ sk_B_1 @ sk_A )
   <= ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['3'])).

thf('5',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
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
    ! [X56: $i,X57: $i,X58: $i] :
      ( ~ ( m1_subset_1 @ X56 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X57 ) ) )
      | ~ ( v3_pre_topc @ X56 @ X57 )
      | ~ ( r1_tarski @ X56 @ X58 )
      | ( r1_tarski @ X56 @ ( k1_tops_1 @ X57 @ X58 ) )
      | ~ ( m1_subset_1 @ X58 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X57 ) ) )
      | ~ ( l1_pre_topc @ X57 ) ) ),
    inference(cnf,[status(esa)],[t56_tops_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ sk_B_1 @ ( k1_tops_1 @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ sk_B_1 @ X0 )
      | ~ ( v3_pre_topc @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ sk_B_1 @ ( k1_tops_1 @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ sk_B_1 @ X0 )
      | ~ ( v3_pre_topc @ sk_B_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_tarski @ sk_B_1 @ X0 )
        | ( r1_tarski @ sk_B_1 @ ( k1_tops_1 @ sk_A @ X0 ) )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['4','9'])).

thf('11',plain,
    ( ( ( r1_tarski @ sk_B_1 @ ( k1_tops_1 @ sk_A @ sk_B_1 ) )
      | ~ ( r1_tarski @ sk_B_1 @ sk_B_1 ) )
   <= ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['2','10'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('12',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_tarski @ X8 @ X9 )
      | ( X8 != X9 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('13',plain,(
    ! [X9: $i] :
      ( r1_tarski @ X9 @ X9 ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,
    ( ( r1_tarski @ sk_B_1 @ ( k1_tops_1 @ sk_A @ sk_B_1 ) )
   <= ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['11','13'])).

thf('15',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t74_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k1_tops_1 @ A @ B )
            = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('16',plain,(
    ! [X63: $i,X64: $i] :
      ( ~ ( m1_subset_1 @ X63 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X64 ) ) )
      | ( ( k1_tops_1 @ X64 @ X63 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X64 ) @ X63 @ ( k2_tops_1 @ X64 @ X63 ) ) )
      | ~ ( l1_pre_topc @ X64 ) ) ),
    inference(cnf,[status(esa)],[t74_tops_1])).

thf('17',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('20',plain,(
    ! [X39: $i,X40: $i,X41: $i] :
      ( ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ X40 ) )
      | ( ( k7_subset_1 @ X40 @ X39 @ X41 )
        = ( k4_xboole_0 @ X39 @ X41 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ X0 )
      = ( k4_xboole_0 @ sk_B_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B_1 )
    = ( k4_xboole_0 @ sk_B_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['17','18','21'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('23',plain,(
    ! [X16: $i,X17: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X16 @ X17 ) @ X16 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('24',plain,(
    ! [X8: $i,X10: $i] :
      ( ( X8 = X10 )
      | ~ ( r1_tarski @ X10 @ X8 )
      | ~ ( r1_tarski @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,
    ( ~ ( r1_tarski @ sk_B_1 @ ( k1_tops_1 @ sk_A @ sk_B_1 ) )
    | ( sk_B_1
      = ( k4_xboole_0 @ sk_B_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['22','25'])).

thf('27',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B_1 )
    = ( k4_xboole_0 @ sk_B_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['17','18','21'])).

thf('28',plain,
    ( ~ ( r1_tarski @ sk_B_1 @ ( k1_tops_1 @ sk_A @ sk_B_1 ) )
    | ( sk_B_1
      = ( k1_tops_1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,
    ( ( sk_B_1
      = ( k1_tops_1 @ sk_A @ sk_B_1 ) )
   <= ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['14','28'])).

thf('30',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l78_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_tops_1 @ A @ B )
            = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ ( k1_tops_1 @ A @ B ) ) ) ) ) )).

thf('31',plain,(
    ! [X54: $i,X55: $i] :
      ( ~ ( m1_subset_1 @ X54 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X55 ) ) )
      | ( ( k2_tops_1 @ X55 @ X54 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X55 ) @ ( k2_pre_topc @ X55 @ X54 ) @ ( k1_tops_1 @ X55 @ X54 ) ) )
      | ~ ( l1_pre_topc @ X55 ) ) ),
    inference(cnf,[status(esa)],[l78_tops_1])).

thf('32',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ ( k1_tops_1 @ sk_A @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B_1 )
    = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ ( k1_tops_1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
   <= ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['29','34'])).

thf('36',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B_1 )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B_1 )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('37',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B_1 )
     != ( k2_tops_1 @ sk_A @ sk_B_1 ) )
   <= ( ( ( k2_tops_1 @ sk_A @ sk_B_1 )
       != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
      & ( v3_pre_topc @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
    | ~ ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
    | ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['3'])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('40',plain,(
    ! [X3: $i,X4: $i,X7: $i] :
      ( ( X7
        = ( k4_xboole_0 @ X3 @ X4 ) )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X3 )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['40'])).

thf('42',plain,(
    ! [X3: $i,X4: $i,X7: $i] :
      ( ( X7
        = ( k4_xboole_0 @ X3 @ X4 ) )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X4 )
      | ~ ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X3 )
      | ~ ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X1 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['40'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) )
      | ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X1 ) ) ),
    inference(clc,[status(thm)],['44','45'])).

thf('47',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('48',plain,(
    ! [X50: $i,X51: $i] :
      ( ~ ( l1_pre_topc @ X50 )
      | ~ ( m1_subset_1 @ X51 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X50 ) ) )
      | ( m1_subset_1 @ ( k2_tops_1 @ X50 @ X51 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X50 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_1])).

thf('49',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( m1_subset_1 @ ( k4_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('53',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ X28 ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ X28 ) )
      | ( m1_subset_1 @ ( k4_subset_1 @ X28 @ X27 @ X29 ) @ ( k1_zfmisc_1 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k4_subset_1])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    m1_subset_1 @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['51','54'])).

thf('56',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t65_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_pre_topc @ A @ B )
            = ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('57',plain,(
    ! [X61: $i,X62: $i] :
      ( ~ ( m1_subset_1 @ X61 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X62 ) ) )
      | ( ( k2_pre_topc @ X62 @ X61 )
        = ( k4_subset_1 @ ( u1_struct_0 @ X62 ) @ X61 @ ( k2_tops_1 @ X62 @ X61 ) ) )
      | ~ ( l1_pre_topc @ X62 ) ) ),
    inference(cnf,[status(esa)],[t65_tops_1])).

thf('58',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B_1 )
      = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B_1 )
    = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['55','60'])).

thf('62',plain,(
    ! [X39: $i,X40: $i,X41: $i] :
      ( ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ X40 ) )
      | ( ( k7_subset_1 @ X40 @ X39 @ X41 )
        = ( k4_xboole_0 @ X39 @ X41 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ X0 )
      = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['3'])).

thf('65',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['40'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('67',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k4_xboole_0 @ X21 @ ( k4_xboole_0 @ X21 @ X22 ) )
      = ( k3_xboole_0 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('68',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X5 )
      | ~ ( r2_hidden @ X6 @ X4 )
      | ( X5
       != ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('69',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['68'])).

thf('70',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['67','69'])).

thf('71',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 ) )
      | ~ ( r2_hidden @ ( sk_D @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['66','70'])).

thf('72',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ ( sk_D @ ( k3_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) @ X0 @ ( k3_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) ) @ ( k2_tops_1 @ sk_A @ sk_B_1 ) )
        | ( ( k3_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 )
          = ( k4_xboole_0 @ ( k3_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) @ X0 ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['65','71'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('74',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['49','50'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('75',plain,(
    ! [X47: $i,X48: $i] :
      ( ( r1_tarski @ X47 @ X48 )
      | ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ X48 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('76',plain,(
    r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('77',plain,(
    ! [X11: $i,X13: $i] :
      ( ( ( k4_xboole_0 @ X11 @ X13 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X11 @ X13 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('78',plain,
    ( ( k4_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k4_xboole_0 @ X21 @ ( k4_xboole_0 @ X21 @ X22 ) )
      = ( k3_xboole_0 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('80',plain,
    ( ( k4_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) @ k1_xboole_0 )
    = ( k3_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['78','79'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('81',plain,(
    ! [X18: $i] :
      ( ( k4_xboole_0 @ X18 @ k1_xboole_0 )
      = X18 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('83',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B_1 )
    = ( k3_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['80','81','82'])).

thf('84',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k4_xboole_0 @ X21 @ ( k4_xboole_0 @ X21 @ X22 ) )
      = ( k3_xboole_0 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('85',plain,(
    ! [X16: $i,X17: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X16 @ X17 ) @ X16 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('86',plain,(
    ! [X47: $i,X49: $i] :
      ( ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ X49 ) )
      | ~ ( r1_tarski @ X47 @ X49 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('87',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['84','87'])).

thf('89',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('90',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ X37 ) )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ X37 ) )
      | ( ( k4_subset_1 @ X37 @ X36 @ X38 )
        = ( k2_xboole_0 @ X36 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('91',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ X0 )
        = ( k2_xboole_0 @ sk_B_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X0: $i] :
      ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( k3_xboole_0 @ ( u1_struct_0 @ sk_A ) @ X0 ) )
      = ( k2_xboole_0 @ sk_B_1 @ ( k3_xboole_0 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['88','91'])).

thf('93',plain,
    ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) )
    = ( k2_xboole_0 @ sk_B_1 @ ( k3_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_1 @ sk_A @ sk_B_1 ) ) ) ),
    inference('sup+',[status(thm)],['83','92'])).

thf('94',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B_1 )
    = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('95',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B_1 )
    = ( k3_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['80','81','82'])).

thf('96',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B_1 )
    = ( k2_xboole_0 @ sk_B_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['93','94','95'])).

thf(t46_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = k1_xboole_0 ) )).

thf('97',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k4_xboole_0 @ X19 @ ( k2_xboole_0 @ X19 @ X20 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('98',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k4_xboole_0 @ X21 @ ( k4_xboole_0 @ X21 @ X22 ) )
      = ( k3_xboole_0 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('99',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['97','98'])).

thf('100',plain,(
    ! [X18: $i] :
      ( ( k4_xboole_0 @ X18 @ k1_xboole_0 )
      = X18 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('101',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['99','100'])).

thf('102',plain,
    ( sk_B_1
    = ( k3_xboole_0 @ sk_B_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['96','101'])).

thf('103',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('104',plain,
    ( sk_B_1
    = ( k3_xboole_0 @ sk_B_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['96','101'])).

thf('105',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('106',plain,
    ( sk_B_1
    = ( k3_xboole_0 @ sk_B_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['96','101'])).

thf('107',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('108',plain,
    ( sk_B_1
    = ( k3_xboole_0 @ sk_B_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['96','101'])).

thf('109',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ ( sk_D @ sk_B_1 @ X0 @ sk_B_1 ) @ ( k2_tops_1 @ sk_A @ sk_B_1 ) )
        | ( sk_B_1
          = ( k4_xboole_0 @ sk_B_1 @ X0 ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['72','73','102','103','104','105','106','107','108'])).

thf('110',plain,
    ( ( ( sk_B_1
        = ( k4_xboole_0 @ sk_B_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) ) )
      | ( sk_B_1
        = ( k4_xboole_0 @ sk_B_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['46','109'])).

thf('111',plain,
    ( ( sk_B_1
      = ( k4_xboole_0 @ sk_B_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) ) ),
    inference(simplify,[status(thm)],['110'])).

thf('112',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B_1 )
    = ( k4_xboole_0 @ sk_B_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['17','18','21'])).

thf('113',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B_1 )
      = sk_B_1 )
   <= ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['111','112'])).

thf('114',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc9_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ) )).

thf('115',plain,(
    ! [X52: $i,X53: $i] :
      ( ~ ( l1_pre_topc @ X52 )
      | ~ ( v2_pre_topc @ X52 )
      | ~ ( m1_subset_1 @ X53 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X52 ) ) )
      | ( v3_pre_topc @ ( k1_tops_1 @ X52 @ X53 ) @ X52 ) ) ),
    inference(cnf,[status(esa)],[fc9_tops_1])).

thf('116',plain,
    ( ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_B_1 ) @ sk_A )
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
    v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_B_1 ) @ sk_A ),
    inference(demod,[status(thm)],['116','117','118'])).

thf('120',plain,
    ( ( v3_pre_topc @ sk_B_1 @ sk_A )
   <= ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['113','119'])).

thf('121',plain,
    ( ~ ( v3_pre_topc @ sk_B_1 @ sk_A )
   <= ~ ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('122',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B_1 )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
    | ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['120','121'])).

thf('123',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','38','39','122'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.cKQvaen1CY
% 0.12/0.33  % Computer   : n006.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 15:14:22 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.19/0.34  % Number of cores: 8
% 0.19/0.34  % Python version: Python 3.6.8
% 0.19/0.34  % Running in FO mode
% 19.02/19.18  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 19.02/19.18  % Solved by: fo/fo7.sh
% 19.02/19.18  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 19.02/19.18  % done 15601 iterations in 18.730s
% 19.02/19.18  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 19.02/19.18  % SZS output start Refutation
% 19.02/19.18  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 19.02/19.18  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 19.02/19.18  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 19.02/19.18  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 19.02/19.18  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 19.02/19.18  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 19.02/19.18  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 19.02/19.18  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 19.02/19.18  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 19.02/19.18  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 19.02/19.18  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 19.02/19.18  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 19.02/19.18  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 19.02/19.18  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 19.02/19.18  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 19.02/19.18  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 19.02/19.18  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 19.02/19.18  thf(sk_A_type, type, sk_A: $i).
% 19.02/19.18  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 19.02/19.18  thf(sk_B_1_type, type, sk_B_1: $i).
% 19.02/19.18  thf(t76_tops_1, conjecture,
% 19.02/19.18    (![A:$i]:
% 19.02/19.18     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 19.02/19.18       ( ![B:$i]:
% 19.02/19.18         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 19.02/19.18           ( ( v3_pre_topc @ B @ A ) <=>
% 19.02/19.18             ( ( k2_tops_1 @ A @ B ) =
% 19.02/19.18               ( k7_subset_1 @
% 19.02/19.18                 ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ B ) ) ) ) ) ))).
% 19.02/19.18  thf(zf_stmt_0, negated_conjecture,
% 19.02/19.18    (~( ![A:$i]:
% 19.02/19.18        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 19.02/19.18          ( ![B:$i]:
% 19.02/19.18            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 19.02/19.18              ( ( v3_pre_topc @ B @ A ) <=>
% 19.02/19.18                ( ( k2_tops_1 @ A @ B ) =
% 19.02/19.18                  ( k7_subset_1 @
% 19.02/19.18                    ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ B ) ) ) ) ) ) )),
% 19.02/19.18    inference('cnf.neg', [status(esa)], [t76_tops_1])).
% 19.02/19.18  thf('0', plain,
% 19.02/19.18      ((((k2_tops_1 @ sk_A @ sk_B_1)
% 19.02/19.18          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 19.02/19.18              (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))
% 19.02/19.18        | ~ (v3_pre_topc @ sk_B_1 @ sk_A))),
% 19.02/19.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.02/19.18  thf('1', plain,
% 19.02/19.18      (~
% 19.02/19.18       (((k2_tops_1 @ sk_A @ sk_B_1)
% 19.02/19.18          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 19.02/19.18             (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))) | 
% 19.02/19.18       ~ ((v3_pre_topc @ sk_B_1 @ sk_A))),
% 19.02/19.18      inference('split', [status(esa)], ['0'])).
% 19.02/19.18  thf('2', plain,
% 19.02/19.18      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 19.02/19.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.02/19.18  thf('3', plain,
% 19.02/19.18      ((((k2_tops_1 @ sk_A @ sk_B_1)
% 19.02/19.18          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 19.02/19.18             (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))
% 19.02/19.18        | (v3_pre_topc @ sk_B_1 @ sk_A))),
% 19.02/19.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.02/19.18  thf('4', plain,
% 19.02/19.18      (((v3_pre_topc @ sk_B_1 @ sk_A)) <= (((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 19.02/19.18      inference('split', [status(esa)], ['3'])).
% 19.02/19.18  thf('5', plain,
% 19.02/19.18      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 19.02/19.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.02/19.18  thf(t56_tops_1, axiom,
% 19.02/19.18    (![A:$i]:
% 19.02/19.18     ( ( l1_pre_topc @ A ) =>
% 19.02/19.18       ( ![B:$i]:
% 19.02/19.18         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 19.02/19.18           ( ![C:$i]:
% 19.02/19.18             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 19.02/19.18               ( ( ( v3_pre_topc @ B @ A ) & ( r1_tarski @ B @ C ) ) =>
% 19.02/19.18                 ( r1_tarski @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 19.02/19.18  thf('6', plain,
% 19.02/19.18      (![X56 : $i, X57 : $i, X58 : $i]:
% 19.02/19.18         (~ (m1_subset_1 @ X56 @ (k1_zfmisc_1 @ (u1_struct_0 @ X57)))
% 19.02/19.18          | ~ (v3_pre_topc @ X56 @ X57)
% 19.02/19.18          | ~ (r1_tarski @ X56 @ X58)
% 19.02/19.18          | (r1_tarski @ X56 @ (k1_tops_1 @ X57 @ X58))
% 19.02/19.18          | ~ (m1_subset_1 @ X58 @ (k1_zfmisc_1 @ (u1_struct_0 @ X57)))
% 19.02/19.18          | ~ (l1_pre_topc @ X57))),
% 19.02/19.18      inference('cnf', [status(esa)], [t56_tops_1])).
% 19.02/19.18  thf('7', plain,
% 19.02/19.18      (![X0 : $i]:
% 19.02/19.18         (~ (l1_pre_topc @ sk_A)
% 19.02/19.18          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 19.02/19.18          | (r1_tarski @ sk_B_1 @ (k1_tops_1 @ sk_A @ X0))
% 19.02/19.18          | ~ (r1_tarski @ sk_B_1 @ X0)
% 19.02/19.18          | ~ (v3_pre_topc @ sk_B_1 @ sk_A))),
% 19.02/19.18      inference('sup-', [status(thm)], ['5', '6'])).
% 19.02/19.18  thf('8', plain, ((l1_pre_topc @ sk_A)),
% 19.02/19.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.02/19.18  thf('9', plain,
% 19.02/19.18      (![X0 : $i]:
% 19.02/19.18         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 19.02/19.18          | (r1_tarski @ sk_B_1 @ (k1_tops_1 @ sk_A @ X0))
% 19.02/19.18          | ~ (r1_tarski @ sk_B_1 @ X0)
% 19.02/19.18          | ~ (v3_pre_topc @ sk_B_1 @ sk_A))),
% 19.02/19.18      inference('demod', [status(thm)], ['7', '8'])).
% 19.02/19.18  thf('10', plain,
% 19.02/19.18      ((![X0 : $i]:
% 19.02/19.18          (~ (r1_tarski @ sk_B_1 @ X0)
% 19.02/19.18           | (r1_tarski @ sk_B_1 @ (k1_tops_1 @ sk_A @ X0))
% 19.02/19.18           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))
% 19.02/19.18         <= (((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 19.02/19.18      inference('sup-', [status(thm)], ['4', '9'])).
% 19.02/19.18  thf('11', plain,
% 19.02/19.18      ((((r1_tarski @ sk_B_1 @ (k1_tops_1 @ sk_A @ sk_B_1))
% 19.02/19.18         | ~ (r1_tarski @ sk_B_1 @ sk_B_1)))
% 19.02/19.18         <= (((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 19.02/19.18      inference('sup-', [status(thm)], ['2', '10'])).
% 19.02/19.18  thf(d10_xboole_0, axiom,
% 19.02/19.18    (![A:$i,B:$i]:
% 19.02/19.18     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 19.02/19.18  thf('12', plain,
% 19.02/19.18      (![X8 : $i, X9 : $i]: ((r1_tarski @ X8 @ X9) | ((X8) != (X9)))),
% 19.02/19.18      inference('cnf', [status(esa)], [d10_xboole_0])).
% 19.02/19.18  thf('13', plain, (![X9 : $i]: (r1_tarski @ X9 @ X9)),
% 19.02/19.18      inference('simplify', [status(thm)], ['12'])).
% 19.02/19.18  thf('14', plain,
% 19.02/19.18      (((r1_tarski @ sk_B_1 @ (k1_tops_1 @ sk_A @ sk_B_1)))
% 19.02/19.18         <= (((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 19.02/19.18      inference('demod', [status(thm)], ['11', '13'])).
% 19.02/19.18  thf('15', plain,
% 19.02/19.18      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 19.02/19.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.02/19.18  thf(t74_tops_1, axiom,
% 19.02/19.18    (![A:$i]:
% 19.02/19.18     ( ( l1_pre_topc @ A ) =>
% 19.02/19.18       ( ![B:$i]:
% 19.02/19.18         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 19.02/19.18           ( ( k1_tops_1 @ A @ B ) =
% 19.02/19.18             ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 19.02/19.18  thf('16', plain,
% 19.02/19.18      (![X63 : $i, X64 : $i]:
% 19.02/19.18         (~ (m1_subset_1 @ X63 @ (k1_zfmisc_1 @ (u1_struct_0 @ X64)))
% 19.02/19.18          | ((k1_tops_1 @ X64 @ X63)
% 19.02/19.18              = (k7_subset_1 @ (u1_struct_0 @ X64) @ X63 @ 
% 19.02/19.18                 (k2_tops_1 @ X64 @ X63)))
% 19.02/19.18          | ~ (l1_pre_topc @ X64))),
% 19.02/19.18      inference('cnf', [status(esa)], [t74_tops_1])).
% 19.02/19.18  thf('17', plain,
% 19.02/19.18      ((~ (l1_pre_topc @ sk_A)
% 19.02/19.18        | ((k1_tops_1 @ sk_A @ sk_B_1)
% 19.02/19.18            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ 
% 19.02/19.18               (k2_tops_1 @ sk_A @ sk_B_1))))),
% 19.02/19.18      inference('sup-', [status(thm)], ['15', '16'])).
% 19.02/19.18  thf('18', plain, ((l1_pre_topc @ sk_A)),
% 19.02/19.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.02/19.18  thf('19', plain,
% 19.02/19.18      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 19.02/19.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.02/19.18  thf(redefinition_k7_subset_1, axiom,
% 19.02/19.18    (![A:$i,B:$i,C:$i]:
% 19.02/19.18     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 19.02/19.18       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 19.02/19.18  thf('20', plain,
% 19.02/19.18      (![X39 : $i, X40 : $i, X41 : $i]:
% 19.02/19.18         (~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ X40))
% 19.02/19.18          | ((k7_subset_1 @ X40 @ X39 @ X41) = (k4_xboole_0 @ X39 @ X41)))),
% 19.02/19.18      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 19.02/19.18  thf('21', plain,
% 19.02/19.18      (![X0 : $i]:
% 19.02/19.18         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ X0)
% 19.02/19.18           = (k4_xboole_0 @ sk_B_1 @ X0))),
% 19.02/19.18      inference('sup-', [status(thm)], ['19', '20'])).
% 19.02/19.18  thf('22', plain,
% 19.02/19.18      (((k1_tops_1 @ sk_A @ sk_B_1)
% 19.02/19.18         = (k4_xboole_0 @ sk_B_1 @ (k2_tops_1 @ sk_A @ sk_B_1)))),
% 19.02/19.18      inference('demod', [status(thm)], ['17', '18', '21'])).
% 19.02/19.18  thf(t36_xboole_1, axiom,
% 19.02/19.18    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 19.02/19.18  thf('23', plain,
% 19.02/19.18      (![X16 : $i, X17 : $i]: (r1_tarski @ (k4_xboole_0 @ X16 @ X17) @ X16)),
% 19.02/19.18      inference('cnf', [status(esa)], [t36_xboole_1])).
% 19.02/19.18  thf('24', plain,
% 19.02/19.18      (![X8 : $i, X10 : $i]:
% 19.02/19.18         (((X8) = (X10)) | ~ (r1_tarski @ X10 @ X8) | ~ (r1_tarski @ X8 @ X10))),
% 19.02/19.18      inference('cnf', [status(esa)], [d10_xboole_0])).
% 19.02/19.18  thf('25', plain,
% 19.02/19.18      (![X0 : $i, X1 : $i]:
% 19.02/19.18         (~ (r1_tarski @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 19.02/19.18          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 19.02/19.18      inference('sup-', [status(thm)], ['23', '24'])).
% 19.02/19.18  thf('26', plain,
% 19.02/19.18      ((~ (r1_tarski @ sk_B_1 @ (k1_tops_1 @ sk_A @ sk_B_1))
% 19.02/19.18        | ((sk_B_1) = (k4_xboole_0 @ sk_B_1 @ (k2_tops_1 @ sk_A @ sk_B_1))))),
% 19.02/19.18      inference('sup-', [status(thm)], ['22', '25'])).
% 19.02/19.18  thf('27', plain,
% 19.02/19.18      (((k1_tops_1 @ sk_A @ sk_B_1)
% 19.02/19.18         = (k4_xboole_0 @ sk_B_1 @ (k2_tops_1 @ sk_A @ sk_B_1)))),
% 19.02/19.18      inference('demod', [status(thm)], ['17', '18', '21'])).
% 19.02/19.18  thf('28', plain,
% 19.02/19.18      ((~ (r1_tarski @ sk_B_1 @ (k1_tops_1 @ sk_A @ sk_B_1))
% 19.02/19.18        | ((sk_B_1) = (k1_tops_1 @ sk_A @ sk_B_1)))),
% 19.02/19.18      inference('demod', [status(thm)], ['26', '27'])).
% 19.02/19.18  thf('29', plain,
% 19.02/19.18      ((((sk_B_1) = (k1_tops_1 @ sk_A @ sk_B_1)))
% 19.02/19.18         <= (((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 19.02/19.18      inference('sup-', [status(thm)], ['14', '28'])).
% 19.02/19.18  thf('30', plain,
% 19.02/19.18      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 19.02/19.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.02/19.18  thf(l78_tops_1, axiom,
% 19.02/19.18    (![A:$i]:
% 19.02/19.18     ( ( l1_pre_topc @ A ) =>
% 19.02/19.18       ( ![B:$i]:
% 19.02/19.18         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 19.02/19.18           ( ( k2_tops_1 @ A @ B ) =
% 19.02/19.18             ( k7_subset_1 @
% 19.02/19.18               ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 19.02/19.18               ( k1_tops_1 @ A @ B ) ) ) ) ) ))).
% 19.02/19.18  thf('31', plain,
% 19.02/19.18      (![X54 : $i, X55 : $i]:
% 19.02/19.18         (~ (m1_subset_1 @ X54 @ (k1_zfmisc_1 @ (u1_struct_0 @ X55)))
% 19.02/19.18          | ((k2_tops_1 @ X55 @ X54)
% 19.02/19.18              = (k7_subset_1 @ (u1_struct_0 @ X55) @ 
% 19.02/19.18                 (k2_pre_topc @ X55 @ X54) @ (k1_tops_1 @ X55 @ X54)))
% 19.02/19.18          | ~ (l1_pre_topc @ X55))),
% 19.02/19.18      inference('cnf', [status(esa)], [l78_tops_1])).
% 19.02/19.18  thf('32', plain,
% 19.02/19.18      ((~ (l1_pre_topc @ sk_A)
% 19.02/19.18        | ((k2_tops_1 @ sk_A @ sk_B_1)
% 19.02/19.18            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 19.02/19.18               (k2_pre_topc @ sk_A @ sk_B_1) @ (k1_tops_1 @ sk_A @ sk_B_1))))),
% 19.02/19.18      inference('sup-', [status(thm)], ['30', '31'])).
% 19.02/19.18  thf('33', plain, ((l1_pre_topc @ sk_A)),
% 19.02/19.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.02/19.18  thf('34', plain,
% 19.02/19.18      (((k2_tops_1 @ sk_A @ sk_B_1)
% 19.02/19.18         = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 19.02/19.18            (k2_pre_topc @ sk_A @ sk_B_1) @ (k1_tops_1 @ sk_A @ sk_B_1)))),
% 19.02/19.18      inference('demod', [status(thm)], ['32', '33'])).
% 19.02/19.18  thf('35', plain,
% 19.02/19.18      ((((k2_tops_1 @ sk_A @ sk_B_1)
% 19.02/19.18          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 19.02/19.18             (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1)))
% 19.02/19.18         <= (((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 19.02/19.18      inference('sup+', [status(thm)], ['29', '34'])).
% 19.02/19.18  thf('36', plain,
% 19.02/19.18      ((((k2_tops_1 @ sk_A @ sk_B_1)
% 19.02/19.18          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 19.02/19.18              (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1)))
% 19.02/19.18         <= (~
% 19.02/19.18             (((k2_tops_1 @ sk_A @ sk_B_1)
% 19.02/19.18                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 19.02/19.18                   (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))))),
% 19.02/19.18      inference('split', [status(esa)], ['0'])).
% 19.02/19.18  thf('37', plain,
% 19.02/19.18      ((((k2_tops_1 @ sk_A @ sk_B_1) != (k2_tops_1 @ sk_A @ sk_B_1)))
% 19.02/19.18         <= (~
% 19.02/19.18             (((k2_tops_1 @ sk_A @ sk_B_1)
% 19.02/19.18                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 19.02/19.18                   (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))) & 
% 19.02/19.18             ((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 19.02/19.18      inference('sup-', [status(thm)], ['35', '36'])).
% 19.02/19.18  thf('38', plain,
% 19.02/19.18      ((((k2_tops_1 @ sk_A @ sk_B_1)
% 19.02/19.18          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 19.02/19.18             (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))) | 
% 19.02/19.18       ~ ((v3_pre_topc @ sk_B_1 @ sk_A))),
% 19.02/19.18      inference('simplify', [status(thm)], ['37'])).
% 19.02/19.18  thf('39', plain,
% 19.02/19.18      ((((k2_tops_1 @ sk_A @ sk_B_1)
% 19.02/19.18          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 19.02/19.18             (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))) | 
% 19.02/19.18       ((v3_pre_topc @ sk_B_1 @ sk_A))),
% 19.02/19.18      inference('split', [status(esa)], ['3'])).
% 19.02/19.18  thf(d5_xboole_0, axiom,
% 19.02/19.18    (![A:$i,B:$i,C:$i]:
% 19.02/19.18     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 19.02/19.18       ( ![D:$i]:
% 19.02/19.18         ( ( r2_hidden @ D @ C ) <=>
% 19.02/19.18           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 19.02/19.18  thf('40', plain,
% 19.02/19.18      (![X3 : $i, X4 : $i, X7 : $i]:
% 19.02/19.18         (((X7) = (k4_xboole_0 @ X3 @ X4))
% 19.02/19.18          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X3)
% 19.02/19.18          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X7))),
% 19.02/19.18      inference('cnf', [status(esa)], [d5_xboole_0])).
% 19.02/19.18  thf('41', plain,
% 19.02/19.18      (![X0 : $i, X1 : $i]:
% 19.02/19.18         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 19.02/19.18          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 19.02/19.18      inference('eq_fact', [status(thm)], ['40'])).
% 19.02/19.18  thf('42', plain,
% 19.02/19.18      (![X3 : $i, X4 : $i, X7 : $i]:
% 19.02/19.18         (((X7) = (k4_xboole_0 @ X3 @ X4))
% 19.02/19.18          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X4)
% 19.02/19.18          | ~ (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X3)
% 19.02/19.18          | ~ (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X7))),
% 19.02/19.18      inference('cnf', [status(esa)], [d5_xboole_0])).
% 19.02/19.18  thf('43', plain,
% 19.02/19.18      (![X0 : $i, X1 : $i]:
% 19.02/19.18         (((X0) = (k4_xboole_0 @ X0 @ X1))
% 19.02/19.18          | ~ (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 19.02/19.18          | (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X1)
% 19.02/19.18          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 19.02/19.18      inference('sup-', [status(thm)], ['41', '42'])).
% 19.02/19.18  thf('44', plain,
% 19.02/19.18      (![X0 : $i, X1 : $i]:
% 19.02/19.18         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X1)
% 19.02/19.18          | ~ (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 19.02/19.18          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 19.02/19.18      inference('simplify', [status(thm)], ['43'])).
% 19.02/19.18  thf('45', plain,
% 19.02/19.18      (![X0 : $i, X1 : $i]:
% 19.02/19.18         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 19.02/19.18          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 19.02/19.18      inference('eq_fact', [status(thm)], ['40'])).
% 19.02/19.18  thf('46', plain,
% 19.02/19.18      (![X0 : $i, X1 : $i]:
% 19.02/19.18         (((X0) = (k4_xboole_0 @ X0 @ X1))
% 19.02/19.18          | (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X1))),
% 19.02/19.18      inference('clc', [status(thm)], ['44', '45'])).
% 19.02/19.18  thf('47', plain,
% 19.02/19.18      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 19.02/19.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.02/19.18  thf(dt_k2_tops_1, axiom,
% 19.02/19.18    (![A:$i,B:$i]:
% 19.02/19.18     ( ( ( l1_pre_topc @ A ) & 
% 19.02/19.18         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 19.02/19.18       ( m1_subset_1 @
% 19.02/19.18         ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 19.02/19.18  thf('48', plain,
% 19.02/19.18      (![X50 : $i, X51 : $i]:
% 19.02/19.18         (~ (l1_pre_topc @ X50)
% 19.02/19.18          | ~ (m1_subset_1 @ X51 @ (k1_zfmisc_1 @ (u1_struct_0 @ X50)))
% 19.02/19.18          | (m1_subset_1 @ (k2_tops_1 @ X50 @ X51) @ 
% 19.02/19.18             (k1_zfmisc_1 @ (u1_struct_0 @ X50))))),
% 19.02/19.18      inference('cnf', [status(esa)], [dt_k2_tops_1])).
% 19.02/19.18  thf('49', plain,
% 19.02/19.18      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B_1) @ 
% 19.02/19.18         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 19.02/19.18        | ~ (l1_pre_topc @ sk_A))),
% 19.02/19.18      inference('sup-', [status(thm)], ['47', '48'])).
% 19.02/19.18  thf('50', plain, ((l1_pre_topc @ sk_A)),
% 19.02/19.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.02/19.18  thf('51', plain,
% 19.02/19.18      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B_1) @ 
% 19.02/19.18        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 19.02/19.18      inference('demod', [status(thm)], ['49', '50'])).
% 19.02/19.18  thf('52', plain,
% 19.02/19.18      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 19.02/19.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.02/19.18  thf(dt_k4_subset_1, axiom,
% 19.02/19.18    (![A:$i,B:$i,C:$i]:
% 19.02/19.18     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 19.02/19.18         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 19.02/19.18       ( m1_subset_1 @ ( k4_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 19.02/19.18  thf('53', plain,
% 19.02/19.18      (![X27 : $i, X28 : $i, X29 : $i]:
% 19.02/19.18         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ X28))
% 19.02/19.18          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ X28))
% 19.02/19.18          | (m1_subset_1 @ (k4_subset_1 @ X28 @ X27 @ X29) @ 
% 19.02/19.18             (k1_zfmisc_1 @ X28)))),
% 19.02/19.18      inference('cnf', [status(esa)], [dt_k4_subset_1])).
% 19.02/19.18  thf('54', plain,
% 19.02/19.18      (![X0 : $i]:
% 19.02/19.18         ((m1_subset_1 @ (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ X0) @ 
% 19.02/19.18           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 19.02/19.18          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 19.02/19.18      inference('sup-', [status(thm)], ['52', '53'])).
% 19.02/19.18  thf('55', plain,
% 19.02/19.18      ((m1_subset_1 @ 
% 19.02/19.18        (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ 
% 19.02/19.18         (k2_tops_1 @ sk_A @ sk_B_1)) @ 
% 19.02/19.18        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 19.02/19.18      inference('sup-', [status(thm)], ['51', '54'])).
% 19.02/19.18  thf('56', plain,
% 19.02/19.18      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 19.02/19.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.02/19.18  thf(t65_tops_1, axiom,
% 19.02/19.18    (![A:$i]:
% 19.02/19.18     ( ( l1_pre_topc @ A ) =>
% 19.02/19.18       ( ![B:$i]:
% 19.02/19.18         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 19.02/19.18           ( ( k2_pre_topc @ A @ B ) =
% 19.02/19.18             ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 19.02/19.18  thf('57', plain,
% 19.02/19.18      (![X61 : $i, X62 : $i]:
% 19.02/19.18         (~ (m1_subset_1 @ X61 @ (k1_zfmisc_1 @ (u1_struct_0 @ X62)))
% 19.02/19.18          | ((k2_pre_topc @ X62 @ X61)
% 19.02/19.18              = (k4_subset_1 @ (u1_struct_0 @ X62) @ X61 @ 
% 19.02/19.18                 (k2_tops_1 @ X62 @ X61)))
% 19.02/19.18          | ~ (l1_pre_topc @ X62))),
% 19.02/19.18      inference('cnf', [status(esa)], [t65_tops_1])).
% 19.02/19.18  thf('58', plain,
% 19.02/19.18      ((~ (l1_pre_topc @ sk_A)
% 19.02/19.18        | ((k2_pre_topc @ sk_A @ sk_B_1)
% 19.02/19.18            = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ 
% 19.02/19.18               (k2_tops_1 @ sk_A @ sk_B_1))))),
% 19.02/19.18      inference('sup-', [status(thm)], ['56', '57'])).
% 19.02/19.18  thf('59', plain, ((l1_pre_topc @ sk_A)),
% 19.02/19.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.02/19.18  thf('60', plain,
% 19.02/19.18      (((k2_pre_topc @ sk_A @ sk_B_1)
% 19.02/19.18         = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ 
% 19.02/19.18            (k2_tops_1 @ sk_A @ sk_B_1)))),
% 19.02/19.18      inference('demod', [status(thm)], ['58', '59'])).
% 19.02/19.18  thf('61', plain,
% 19.02/19.18      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B_1) @ 
% 19.02/19.18        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 19.02/19.18      inference('demod', [status(thm)], ['55', '60'])).
% 19.02/19.18  thf('62', plain,
% 19.02/19.18      (![X39 : $i, X40 : $i, X41 : $i]:
% 19.02/19.18         (~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ X40))
% 19.02/19.18          | ((k7_subset_1 @ X40 @ X39 @ X41) = (k4_xboole_0 @ X39 @ X41)))),
% 19.02/19.18      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 19.02/19.18  thf('63', plain,
% 19.02/19.18      (![X0 : $i]:
% 19.02/19.18         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 19.02/19.18           (k2_pre_topc @ sk_A @ sk_B_1) @ X0)
% 19.02/19.18           = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B_1) @ X0))),
% 19.02/19.18      inference('sup-', [status(thm)], ['61', '62'])).
% 19.02/19.18  thf('64', plain,
% 19.02/19.18      ((((k2_tops_1 @ sk_A @ sk_B_1)
% 19.02/19.18          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 19.02/19.18             (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1)))
% 19.02/19.18         <= ((((k2_tops_1 @ sk_A @ sk_B_1)
% 19.02/19.18                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 19.02/19.18                   (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))))),
% 19.02/19.18      inference('split', [status(esa)], ['3'])).
% 19.02/19.18  thf('65', plain,
% 19.02/19.18      ((((k2_tops_1 @ sk_A @ sk_B_1)
% 19.02/19.18          = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1)))
% 19.02/19.18         <= ((((k2_tops_1 @ sk_A @ sk_B_1)
% 19.02/19.18                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 19.02/19.18                   (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))))),
% 19.02/19.18      inference('sup+', [status(thm)], ['63', '64'])).
% 19.02/19.18  thf('66', plain,
% 19.02/19.18      (![X0 : $i, X1 : $i]:
% 19.02/19.18         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 19.02/19.18          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 19.02/19.18      inference('eq_fact', [status(thm)], ['40'])).
% 19.02/19.18  thf(t48_xboole_1, axiom,
% 19.02/19.18    (![A:$i,B:$i]:
% 19.02/19.18     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 19.02/19.18  thf('67', plain,
% 19.02/19.18      (![X21 : $i, X22 : $i]:
% 19.02/19.18         ((k4_xboole_0 @ X21 @ (k4_xboole_0 @ X21 @ X22))
% 19.02/19.18           = (k3_xboole_0 @ X21 @ X22))),
% 19.02/19.18      inference('cnf', [status(esa)], [t48_xboole_1])).
% 19.02/19.18  thf('68', plain,
% 19.02/19.18      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 19.02/19.18         (~ (r2_hidden @ X6 @ X5)
% 19.02/19.18          | ~ (r2_hidden @ X6 @ X4)
% 19.02/19.18          | ((X5) != (k4_xboole_0 @ X3 @ X4)))),
% 19.02/19.18      inference('cnf', [status(esa)], [d5_xboole_0])).
% 19.02/19.18  thf('69', plain,
% 19.02/19.18      (![X3 : $i, X4 : $i, X6 : $i]:
% 19.02/19.18         (~ (r2_hidden @ X6 @ X4)
% 19.02/19.18          | ~ (r2_hidden @ X6 @ (k4_xboole_0 @ X3 @ X4)))),
% 19.02/19.18      inference('simplify', [status(thm)], ['68'])).
% 19.02/19.18  thf('70', plain,
% 19.02/19.18      (![X0 : $i, X1 : $i, X2 : $i]:
% 19.02/19.18         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 19.02/19.18          | ~ (r2_hidden @ X2 @ (k4_xboole_0 @ X1 @ X0)))),
% 19.02/19.18      inference('sup-', [status(thm)], ['67', '69'])).
% 19.02/19.18  thf('71', plain,
% 19.02/19.18      (![X0 : $i, X1 : $i, X2 : $i]:
% 19.02/19.18         (((k3_xboole_0 @ X1 @ X0)
% 19.02/19.18            = (k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2))
% 19.02/19.18          | ~ (r2_hidden @ 
% 19.02/19.18               (sk_D @ (k3_xboole_0 @ X1 @ X0) @ X2 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 19.02/19.18               (k4_xboole_0 @ X1 @ X0)))),
% 19.02/19.18      inference('sup-', [status(thm)], ['66', '70'])).
% 19.02/19.18  thf('72', plain,
% 19.02/19.18      ((![X0 : $i]:
% 19.02/19.18          (~ (r2_hidden @ 
% 19.02/19.18              (sk_D @ (k3_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1) @ 
% 19.02/19.18               X0 @ (k3_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1)) @ 
% 19.02/19.18              (k2_tops_1 @ sk_A @ sk_B_1))
% 19.02/19.18           | ((k3_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1)
% 19.02/19.18               = (k4_xboole_0 @ 
% 19.02/19.18                  (k3_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1) @ X0))))
% 19.02/19.18         <= ((((k2_tops_1 @ sk_A @ sk_B_1)
% 19.02/19.18                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 19.02/19.18                   (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))))),
% 19.02/19.18      inference('sup-', [status(thm)], ['65', '71'])).
% 19.02/19.18  thf(commutativity_k3_xboole_0, axiom,
% 19.02/19.18    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 19.02/19.18  thf('73', plain,
% 19.02/19.18      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 19.02/19.18      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 19.02/19.18  thf('74', plain,
% 19.02/19.18      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B_1) @ 
% 19.02/19.18        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 19.02/19.18      inference('demod', [status(thm)], ['49', '50'])).
% 19.02/19.18  thf(t3_subset, axiom,
% 19.02/19.18    (![A:$i,B:$i]:
% 19.02/19.18     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 19.02/19.18  thf('75', plain,
% 19.02/19.18      (![X47 : $i, X48 : $i]:
% 19.02/19.18         ((r1_tarski @ X47 @ X48) | ~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ X48)))),
% 19.02/19.18      inference('cnf', [status(esa)], [t3_subset])).
% 19.02/19.18  thf('76', plain,
% 19.02/19.18      ((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B_1) @ (u1_struct_0 @ sk_A))),
% 19.02/19.18      inference('sup-', [status(thm)], ['74', '75'])).
% 19.02/19.18  thf(l32_xboole_1, axiom,
% 19.02/19.18    (![A:$i,B:$i]:
% 19.02/19.18     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 19.02/19.18  thf('77', plain,
% 19.02/19.18      (![X11 : $i, X13 : $i]:
% 19.02/19.18         (((k4_xboole_0 @ X11 @ X13) = (k1_xboole_0))
% 19.02/19.18          | ~ (r1_tarski @ X11 @ X13))),
% 19.02/19.18      inference('cnf', [status(esa)], [l32_xboole_1])).
% 19.02/19.18  thf('78', plain,
% 19.02/19.18      (((k4_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B_1) @ (u1_struct_0 @ sk_A))
% 19.02/19.18         = (k1_xboole_0))),
% 19.02/19.18      inference('sup-', [status(thm)], ['76', '77'])).
% 19.02/19.18  thf('79', plain,
% 19.02/19.18      (![X21 : $i, X22 : $i]:
% 19.02/19.18         ((k4_xboole_0 @ X21 @ (k4_xboole_0 @ X21 @ X22))
% 19.02/19.18           = (k3_xboole_0 @ X21 @ X22))),
% 19.02/19.18      inference('cnf', [status(esa)], [t48_xboole_1])).
% 19.02/19.18  thf('80', plain,
% 19.02/19.18      (((k4_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B_1) @ k1_xboole_0)
% 19.02/19.18         = (k3_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B_1) @ (u1_struct_0 @ sk_A)))),
% 19.02/19.18      inference('sup+', [status(thm)], ['78', '79'])).
% 19.02/19.18  thf(t3_boole, axiom,
% 19.02/19.18    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 19.02/19.18  thf('81', plain, (![X18 : $i]: ((k4_xboole_0 @ X18 @ k1_xboole_0) = (X18))),
% 19.02/19.18      inference('cnf', [status(esa)], [t3_boole])).
% 19.02/19.18  thf('82', plain,
% 19.02/19.18      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 19.02/19.18      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 19.02/19.18  thf('83', plain,
% 19.02/19.18      (((k2_tops_1 @ sk_A @ sk_B_1)
% 19.02/19.18         = (k3_xboole_0 @ (u1_struct_0 @ sk_A) @ (k2_tops_1 @ sk_A @ sk_B_1)))),
% 19.02/19.18      inference('demod', [status(thm)], ['80', '81', '82'])).
% 19.02/19.18  thf('84', plain,
% 19.02/19.18      (![X21 : $i, X22 : $i]:
% 19.02/19.18         ((k4_xboole_0 @ X21 @ (k4_xboole_0 @ X21 @ X22))
% 19.02/19.18           = (k3_xboole_0 @ X21 @ X22))),
% 19.02/19.18      inference('cnf', [status(esa)], [t48_xboole_1])).
% 19.02/19.18  thf('85', plain,
% 19.02/19.18      (![X16 : $i, X17 : $i]: (r1_tarski @ (k4_xboole_0 @ X16 @ X17) @ X16)),
% 19.02/19.18      inference('cnf', [status(esa)], [t36_xboole_1])).
% 19.02/19.18  thf('86', plain,
% 19.02/19.18      (![X47 : $i, X49 : $i]:
% 19.02/19.18         ((m1_subset_1 @ X47 @ (k1_zfmisc_1 @ X49)) | ~ (r1_tarski @ X47 @ X49))),
% 19.02/19.18      inference('cnf', [status(esa)], [t3_subset])).
% 19.02/19.18  thf('87', plain,
% 19.02/19.18      (![X0 : $i, X1 : $i]:
% 19.02/19.18         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 19.02/19.18      inference('sup-', [status(thm)], ['85', '86'])).
% 19.02/19.18  thf('88', plain,
% 19.02/19.18      (![X0 : $i, X1 : $i]:
% 19.02/19.18         (m1_subset_1 @ (k3_xboole_0 @ X1 @ X0) @ (k1_zfmisc_1 @ X1))),
% 19.02/19.18      inference('sup+', [status(thm)], ['84', '87'])).
% 19.02/19.18  thf('89', plain,
% 19.02/19.18      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 19.02/19.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.02/19.18  thf(redefinition_k4_subset_1, axiom,
% 19.02/19.18    (![A:$i,B:$i,C:$i]:
% 19.02/19.18     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 19.02/19.18         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 19.02/19.18       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 19.02/19.18  thf('90', plain,
% 19.02/19.18      (![X36 : $i, X37 : $i, X38 : $i]:
% 19.02/19.18         (~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ X37))
% 19.02/19.18          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ X37))
% 19.02/19.18          | ((k4_subset_1 @ X37 @ X36 @ X38) = (k2_xboole_0 @ X36 @ X38)))),
% 19.02/19.18      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 19.02/19.18  thf('91', plain,
% 19.02/19.18      (![X0 : $i]:
% 19.02/19.18         (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ X0)
% 19.02/19.18            = (k2_xboole_0 @ sk_B_1 @ X0))
% 19.02/19.18          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 19.02/19.18      inference('sup-', [status(thm)], ['89', '90'])).
% 19.02/19.18  thf('92', plain,
% 19.02/19.18      (![X0 : $i]:
% 19.02/19.18         ((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ 
% 19.02/19.18           (k3_xboole_0 @ (u1_struct_0 @ sk_A) @ X0))
% 19.02/19.18           = (k2_xboole_0 @ sk_B_1 @ (k3_xboole_0 @ (u1_struct_0 @ sk_A) @ X0)))),
% 19.02/19.18      inference('sup-', [status(thm)], ['88', '91'])).
% 19.02/19.18  thf('93', plain,
% 19.02/19.18      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ 
% 19.02/19.18         (k2_tops_1 @ sk_A @ sk_B_1))
% 19.02/19.18         = (k2_xboole_0 @ sk_B_1 @ 
% 19.02/19.18            (k3_xboole_0 @ (u1_struct_0 @ sk_A) @ (k2_tops_1 @ sk_A @ sk_B_1))))),
% 19.02/19.18      inference('sup+', [status(thm)], ['83', '92'])).
% 19.02/19.18  thf('94', plain,
% 19.02/19.18      (((k2_pre_topc @ sk_A @ sk_B_1)
% 19.02/19.18         = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ 
% 19.02/19.18            (k2_tops_1 @ sk_A @ sk_B_1)))),
% 19.02/19.18      inference('demod', [status(thm)], ['58', '59'])).
% 19.02/19.18  thf('95', plain,
% 19.02/19.18      (((k2_tops_1 @ sk_A @ sk_B_1)
% 19.02/19.18         = (k3_xboole_0 @ (u1_struct_0 @ sk_A) @ (k2_tops_1 @ sk_A @ sk_B_1)))),
% 19.02/19.18      inference('demod', [status(thm)], ['80', '81', '82'])).
% 19.02/19.18  thf('96', plain,
% 19.02/19.18      (((k2_pre_topc @ sk_A @ sk_B_1)
% 19.02/19.18         = (k2_xboole_0 @ sk_B_1 @ (k2_tops_1 @ sk_A @ sk_B_1)))),
% 19.02/19.18      inference('demod', [status(thm)], ['93', '94', '95'])).
% 19.02/19.18  thf(t46_xboole_1, axiom,
% 19.02/19.18    (![A:$i,B:$i]:
% 19.02/19.18     ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( k1_xboole_0 ) ))).
% 19.02/19.18  thf('97', plain,
% 19.02/19.18      (![X19 : $i, X20 : $i]:
% 19.02/19.18         ((k4_xboole_0 @ X19 @ (k2_xboole_0 @ X19 @ X20)) = (k1_xboole_0))),
% 19.02/19.18      inference('cnf', [status(esa)], [t46_xboole_1])).
% 19.02/19.18  thf('98', plain,
% 19.02/19.18      (![X21 : $i, X22 : $i]:
% 19.02/19.18         ((k4_xboole_0 @ X21 @ (k4_xboole_0 @ X21 @ X22))
% 19.02/19.18           = (k3_xboole_0 @ X21 @ X22))),
% 19.02/19.18      inference('cnf', [status(esa)], [t48_xboole_1])).
% 19.02/19.18  thf('99', plain,
% 19.02/19.18      (![X0 : $i, X1 : $i]:
% 19.02/19.18         ((k4_xboole_0 @ X1 @ k1_xboole_0)
% 19.02/19.18           = (k3_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 19.02/19.18      inference('sup+', [status(thm)], ['97', '98'])).
% 19.02/19.18  thf('100', plain, (![X18 : $i]: ((k4_xboole_0 @ X18 @ k1_xboole_0) = (X18))),
% 19.02/19.18      inference('cnf', [status(esa)], [t3_boole])).
% 19.02/19.18  thf('101', plain,
% 19.02/19.18      (![X0 : $i, X1 : $i]:
% 19.02/19.18         ((X1) = (k3_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 19.02/19.18      inference('demod', [status(thm)], ['99', '100'])).
% 19.02/19.18  thf('102', plain,
% 19.02/19.18      (((sk_B_1) = (k3_xboole_0 @ sk_B_1 @ (k2_pre_topc @ sk_A @ sk_B_1)))),
% 19.02/19.18      inference('sup+', [status(thm)], ['96', '101'])).
% 19.02/19.18  thf('103', plain,
% 19.02/19.18      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 19.02/19.18      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 19.02/19.18  thf('104', plain,
% 19.02/19.18      (((sk_B_1) = (k3_xboole_0 @ sk_B_1 @ (k2_pre_topc @ sk_A @ sk_B_1)))),
% 19.02/19.18      inference('sup+', [status(thm)], ['96', '101'])).
% 19.02/19.18  thf('105', plain,
% 19.02/19.18      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 19.02/19.18      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 19.02/19.18  thf('106', plain,
% 19.02/19.18      (((sk_B_1) = (k3_xboole_0 @ sk_B_1 @ (k2_pre_topc @ sk_A @ sk_B_1)))),
% 19.02/19.18      inference('sup+', [status(thm)], ['96', '101'])).
% 19.02/19.18  thf('107', plain,
% 19.02/19.18      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 19.02/19.18      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 19.02/19.18  thf('108', plain,
% 19.02/19.18      (((sk_B_1) = (k3_xboole_0 @ sk_B_1 @ (k2_pre_topc @ sk_A @ sk_B_1)))),
% 19.02/19.18      inference('sup+', [status(thm)], ['96', '101'])).
% 19.02/19.18  thf('109', plain,
% 19.02/19.18      ((![X0 : $i]:
% 19.02/19.18          (~ (r2_hidden @ (sk_D @ sk_B_1 @ X0 @ sk_B_1) @ 
% 19.02/19.18              (k2_tops_1 @ sk_A @ sk_B_1))
% 19.02/19.18           | ((sk_B_1) = (k4_xboole_0 @ sk_B_1 @ X0))))
% 19.02/19.18         <= ((((k2_tops_1 @ sk_A @ sk_B_1)
% 19.02/19.18                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 19.02/19.18                   (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))))),
% 19.02/19.18      inference('demod', [status(thm)],
% 19.02/19.18                ['72', '73', '102', '103', '104', '105', '106', '107', '108'])).
% 19.02/19.18  thf('110', plain,
% 19.02/19.18      (((((sk_B_1) = (k4_xboole_0 @ sk_B_1 @ (k2_tops_1 @ sk_A @ sk_B_1)))
% 19.02/19.18         | ((sk_B_1) = (k4_xboole_0 @ sk_B_1 @ (k2_tops_1 @ sk_A @ sk_B_1)))))
% 19.02/19.18         <= ((((k2_tops_1 @ sk_A @ sk_B_1)
% 19.02/19.18                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 19.02/19.18                   (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))))),
% 19.02/19.18      inference('sup-', [status(thm)], ['46', '109'])).
% 19.02/19.18  thf('111', plain,
% 19.02/19.18      ((((sk_B_1) = (k4_xboole_0 @ sk_B_1 @ (k2_tops_1 @ sk_A @ sk_B_1))))
% 19.02/19.18         <= ((((k2_tops_1 @ sk_A @ sk_B_1)
% 19.02/19.18                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 19.02/19.18                   (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))))),
% 19.02/19.18      inference('simplify', [status(thm)], ['110'])).
% 19.02/19.18  thf('112', plain,
% 19.02/19.18      (((k1_tops_1 @ sk_A @ sk_B_1)
% 19.02/19.18         = (k4_xboole_0 @ sk_B_1 @ (k2_tops_1 @ sk_A @ sk_B_1)))),
% 19.02/19.18      inference('demod', [status(thm)], ['17', '18', '21'])).
% 19.02/19.18  thf('113', plain,
% 19.02/19.18      ((((k1_tops_1 @ sk_A @ sk_B_1) = (sk_B_1)))
% 19.02/19.18         <= ((((k2_tops_1 @ sk_A @ sk_B_1)
% 19.02/19.18                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 19.02/19.18                   (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))))),
% 19.02/19.18      inference('sup+', [status(thm)], ['111', '112'])).
% 19.02/19.18  thf('114', plain,
% 19.02/19.18      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 19.02/19.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.02/19.18  thf(fc9_tops_1, axiom,
% 19.02/19.18    (![A:$i,B:$i]:
% 19.02/19.18     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 19.02/19.18         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 19.02/19.18       ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ))).
% 19.02/19.18  thf('115', plain,
% 19.02/19.18      (![X52 : $i, X53 : $i]:
% 19.02/19.18         (~ (l1_pre_topc @ X52)
% 19.02/19.18          | ~ (v2_pre_topc @ X52)
% 19.02/19.18          | ~ (m1_subset_1 @ X53 @ (k1_zfmisc_1 @ (u1_struct_0 @ X52)))
% 19.02/19.18          | (v3_pre_topc @ (k1_tops_1 @ X52 @ X53) @ X52))),
% 19.02/19.18      inference('cnf', [status(esa)], [fc9_tops_1])).
% 19.02/19.18  thf('116', plain,
% 19.02/19.18      (((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_B_1) @ sk_A)
% 19.02/19.18        | ~ (v2_pre_topc @ sk_A)
% 19.02/19.18        | ~ (l1_pre_topc @ sk_A))),
% 19.02/19.18      inference('sup-', [status(thm)], ['114', '115'])).
% 19.02/19.18  thf('117', plain, ((v2_pre_topc @ sk_A)),
% 19.02/19.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.02/19.18  thf('118', plain, ((l1_pre_topc @ sk_A)),
% 19.02/19.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.02/19.18  thf('119', plain, ((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_B_1) @ sk_A)),
% 19.02/19.18      inference('demod', [status(thm)], ['116', '117', '118'])).
% 19.02/19.18  thf('120', plain,
% 19.02/19.18      (((v3_pre_topc @ sk_B_1 @ sk_A))
% 19.02/19.18         <= ((((k2_tops_1 @ sk_A @ sk_B_1)
% 19.02/19.18                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 19.02/19.18                   (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))))),
% 19.02/19.18      inference('sup+', [status(thm)], ['113', '119'])).
% 19.02/19.18  thf('121', plain,
% 19.02/19.18      ((~ (v3_pre_topc @ sk_B_1 @ sk_A)) <= (~ ((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 19.02/19.18      inference('split', [status(esa)], ['0'])).
% 19.02/19.18  thf('122', plain,
% 19.02/19.18      (~
% 19.02/19.18       (((k2_tops_1 @ sk_A @ sk_B_1)
% 19.02/19.18          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 19.02/19.18             (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))) | 
% 19.02/19.18       ((v3_pre_topc @ sk_B_1 @ sk_A))),
% 19.02/19.18      inference('sup-', [status(thm)], ['120', '121'])).
% 19.02/19.18  thf('123', plain, ($false),
% 19.02/19.18      inference('sat_resolution*', [status(thm)], ['1', '38', '39', '122'])).
% 19.02/19.18  
% 19.02/19.18  % SZS output end Refutation
% 19.02/19.18  
% 19.02/19.19  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
