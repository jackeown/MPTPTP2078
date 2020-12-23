%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.4LJXIUn8ti

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:04:26 EST 2020

% Result     : Theorem 0.36s
% Output     : Refutation 0.36s
% Verified   : 
% Statistics : Number of formulae       :  135 ( 412 expanded)
%              Number of leaves         :   31 ( 125 expanded)
%              Depth                    :   23
%              Number of atoms          : 1172 (4342 expanded)
%              Number of equality atoms :   46 ( 123 expanded)
%              Maximal formula depth    :   12 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v2_tops_1_type,type,(
    v2_tops_1: $i > $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

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

thf(t74_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k1_tops_1 @ A @ B )
            = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('4',plain,(
    ! [X57: $i,X58: $i] :
      ( ~ ( m1_subset_1 @ X57 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X58 ) ) )
      | ( ( k1_tops_1 @ X58 @ X57 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X58 ) @ X57 @ ( k2_tops_1 @ X58 @ X57 ) ) )
      | ~ ( l1_pre_topc @ X58 ) ) ),
    inference(cnf,[status(esa)],[t74_tops_1])).

thf('5',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('8',plain,(
    ! [X44: $i,X45: $i,X46: $i] :
      ( ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ X45 ) )
      | ( ( k7_subset_1 @ X45 @ X44 @ X46 )
        = ( k4_xboole_0 @ X44 @ X46 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['5','6','9'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('11',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('12',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X7 )
      | ( r2_hidden @ X8 @ X5 )
      | ( X7
       != ( k4_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('13',plain,(
    ! [X5: $i,X6: $i,X8: $i] :
      ( ( r2_hidden @ X8 @ X5 )
      | ~ ( r2_hidden @ X8 @ ( k4_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['11','13'])).

thf('15',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('16',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X4 @ X5 )
      | ( r2_hidden @ X4 @ X6 )
      | ( r2_hidden @ X4 @ X7 )
      | ( X7
       != ( k4_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('17',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( r2_hidden @ X4 @ ( k4_xboole_0 @ X5 @ X6 ) )
      | ( r2_hidden @ X4 @ X6 )
      | ~ ( r2_hidden @ X4 @ X5 ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ ( k4_xboole_0 @ X0 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['15','17'])).

thf('19',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 ) @ X0 )
      | ( r1_tarski @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      | ( r1_tarski @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      | ( r2_hidden @ ( sk_C @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,
    ( ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
    | ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('25',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ X0 @ ( k2_tops_1 @ sk_A @ sk_B ) )
        | ~ ( r2_hidden @ X0 @ sk_B ) )
   <= ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ X0 @ ( k4_xboole_0 @ X0 @ sk_B ) )
        | ( r2_hidden @ ( sk_C @ ( k4_xboole_0 @ X0 @ sk_B ) @ X0 ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['21','25'])).

thf('27',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('28',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X7 )
      | ~ ( r2_hidden @ X8 @ X6 )
      | ( X7
       != ( k4_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('29',plain,(
    ! [X5: $i,X6: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X6 )
      | ~ ( r2_hidden @ X8 @ ( k4_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['27','29'])).

thf('31',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ ( k4_xboole_0 @ X0 @ ( k2_tops_1 @ sk_A @ sk_B ) ) @ ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ ( k2_tops_1 @ sk_A @ sk_B ) ) @ sk_B ) )
        | ( r1_tarski @ ( k4_xboole_0 @ X0 @ ( k2_tops_1 @ sk_A @ sk_B ) ) @ ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ ( k2_tops_1 @ sk_A @ sk_B ) ) @ sk_B ) ) )
   <= ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['26','30'])).

thf('32',plain,
    ( ! [X0: $i] :
        ( r1_tarski @ ( k4_xboole_0 @ X0 @ ( k2_tops_1 @ sk_A @ sk_B ) ) @ ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ ( k2_tops_1 @ sk_A @ sk_B ) ) @ sk_B ) )
   <= ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['11','13'])).

thf('34',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      | ( r1_tarski @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference(simplify,[status(thm)],['35'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('37',plain,(
    ! [X10: $i,X12: $i] :
      ( ( X10 = X12 )
      | ~ ( r1_tarski @ X12 @ X10 )
      | ~ ( r1_tarski @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,
    ( ! [X0: $i] :
        ( ( k4_xboole_0 @ X0 @ ( k2_tops_1 @ sk_A @ sk_B ) )
        = ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ ( k2_tops_1 @ sk_A @ sk_B ) ) @ sk_B ) )
   <= ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['32','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['27','29'])).

thf('41',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( r2_hidden @ ( sk_C @ X1 @ ( k4_xboole_0 @ X0 @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) @ sk_B )
        | ( r1_tarski @ ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ ( k2_tops_1 @ sk_A @ sk_B ) ) @ sk_B ) @ X1 ) )
   <= ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,
    ( ! [X0: $i] :
        ( ( k4_xboole_0 @ X0 @ ( k2_tops_1 @ sk_A @ sk_B ) )
        = ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ ( k2_tops_1 @ sk_A @ sk_B ) ) @ sk_B ) )
   <= ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['32','38'])).

thf('43',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( r2_hidden @ ( sk_C @ X1 @ ( k4_xboole_0 @ X0 @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) @ sk_B )
        | ( r1_tarski @ ( k4_xboole_0 @ X0 @ ( k2_tops_1 @ sk_A @ sk_B ) ) @ X1 ) )
   <= ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) @ X0 )
        | ( r1_tarski @ ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) @ X0 ) )
   <= ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['14','43'])).

thf('45',plain,
    ( ! [X0: $i] :
        ( r1_tarski @ ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) @ X0 )
   <= ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['11','13'])).

thf('47',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['27','29'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X0 @ X0 ) @ X1 )
      | ( r1_tarski @ ( k4_xboole_0 @ X0 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X0 @ X0 ) @ X1 ) ),
    inference(simplify,[status(thm)],['48'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('50',plain,(
    ! [X15: $i] :
      ( r1_tarski @ k1_xboole_0 @ X15 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('51',plain,(
    ! [X10: $i,X12: $i] :
      ( ( X10 = X12 )
      | ~ ( r1_tarski @ X12 @ X10 )
      | ~ ( r1_tarski @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('52',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['49','52'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('54',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ X14 )
      = ( k5_xboole_0 @ X13 @ ( k3_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('55',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X0 ) ) )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,
    ( ( ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = k1_xboole_0 )
   <= ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['45','57'])).

thf('59',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
   <= ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['10','58'])).

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
    ! [X59: $i,X60: $i] :
      ( ~ ( m1_subset_1 @ X59 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X60 ) ) )
      | ( ( k1_tops_1 @ X60 @ X59 )
       != k1_xboole_0 )
      | ( v2_tops_1 @ X59 @ X60 )
      | ~ ( l1_pre_topc @ X60 ) ) ),
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
    ! [X51: $i,X52: $i] :
      ( ~ ( m1_subset_1 @ X51 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X52 ) ) )
      | ( r1_tarski @ X51 @ ( k2_pre_topc @ X52 @ X51 ) )
      | ~ ( l1_pre_topc @ X52 ) ) ),
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

thf('76',plain,
    ( ( v2_tops_1 @ sk_B @ sk_A )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['22'])).

thf('77',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    ! [X59: $i,X60: $i] :
      ( ~ ( m1_subset_1 @ X59 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X60 ) ) )
      | ~ ( v2_tops_1 @ X59 @ X60 )
      | ( ( k1_tops_1 @ X60 @ X59 )
        = k1_xboole_0 )
      | ~ ( l1_pre_topc @ X60 ) ) ),
    inference(cnf,[status(esa)],[t84_tops_1])).

thf('79',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['79','80'])).

thf('82',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['76','81'])).

thf('83',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l78_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_tops_1 @ A @ B )
            = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ ( k1_tops_1 @ A @ B ) ) ) ) ) )).

thf('84',plain,(
    ! [X53: $i,X54: $i] :
      ( ~ ( m1_subset_1 @ X53 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X54 ) ) )
      | ( ( k2_tops_1 @ X54 @ X53 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X54 ) @ ( k2_pre_topc @ X54 @ X53 ) @ ( k1_tops_1 @ X54 @ X53 ) ) )
      | ~ ( l1_pre_topc @ X54 ) ) ),
    inference(cnf,[status(esa)],[l78_tops_1])).

thf('85',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['85','86'])).

thf('88',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ k1_xboole_0 ) )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['82','87'])).

thf('89',plain,
    ( ( v2_tops_1 @ sk_B @ sk_A )
    | ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['22'])).

thf('90',plain,(
    v2_tops_1 @ sk_B @ sk_A ),
    inference('sat_resolution*',[status(thm)],['2','68','89'])).

thf('91',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ k1_xboole_0 ) ),
    inference(simpl_trail,[status(thm)],['88','90'])).

thf('92',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('93',plain,(
    ! [X49: $i,X50: $i] :
      ( ~ ( l1_pre_topc @ X49 )
      | ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X49 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X49 @ X50 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X49 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('94',plain,
    ( ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['94','95'])).

thf('97',plain,(
    ! [X44: $i,X45: $i,X46: $i] :
      ( ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ X45 ) )
      | ( ( k7_subset_1 @ X45 @ X44 @ X46 )
        = ( k4_xboole_0 @ X44 @ X46 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('98',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 )
      = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('99',plain,(
    ! [X16: $i] :
      ( ( k4_xboole_0 @ X16 @ k1_xboole_0 )
      = X16 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('100',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k2_pre_topc @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['91','98','99'])).

thf('101',plain,(
    r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['75','100'])).

thf('102',plain,(
    $false ),
    inference(demod,[status(thm)],['70','101'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.4LJXIUn8ti
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:14:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.36/0.60  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.36/0.60  % Solved by: fo/fo7.sh
% 0.36/0.60  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.36/0.60  % done 309 iterations in 0.141s
% 0.36/0.60  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.36/0.60  % SZS output start Refutation
% 0.36/0.60  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 0.36/0.60  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.36/0.60  thf(sk_A_type, type, sk_A: $i).
% 0.36/0.60  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.36/0.60  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.36/0.60  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.36/0.60  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.36/0.60  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.36/0.60  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.36/0.60  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 0.36/0.60  thf(sk_B_type, type, sk_B: $i).
% 0.36/0.60  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.36/0.60  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.36/0.60  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.36/0.60  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.36/0.60  thf(v2_tops_1_type, type, v2_tops_1: $i > $i > $o).
% 0.36/0.60  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.36/0.60  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.36/0.60  thf(t88_tops_1, conjecture,
% 0.36/0.60    (![A:$i]:
% 0.36/0.60     ( ( l1_pre_topc @ A ) =>
% 0.36/0.60       ( ![B:$i]:
% 0.36/0.60         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.36/0.60           ( ( v2_tops_1 @ B @ A ) <=>
% 0.36/0.60             ( r1_tarski @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.36/0.60  thf(zf_stmt_0, negated_conjecture,
% 0.36/0.60    (~( ![A:$i]:
% 0.36/0.60        ( ( l1_pre_topc @ A ) =>
% 0.36/0.60          ( ![B:$i]:
% 0.36/0.60            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.36/0.60              ( ( v2_tops_1 @ B @ A ) <=>
% 0.36/0.60                ( r1_tarski @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ) )),
% 0.36/0.60    inference('cnf.neg', [status(esa)], [t88_tops_1])).
% 0.36/0.60  thf('0', plain,
% 0.36/0.60      ((~ (r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.36/0.60        | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 0.36/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.60  thf('1', plain,
% 0.36/0.60      ((~ (r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))
% 0.36/0.60         <= (~ ((r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))),
% 0.36/0.60      inference('split', [status(esa)], ['0'])).
% 0.36/0.60  thf('2', plain,
% 0.36/0.60      (~ ((r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))) | 
% 0.36/0.60       ~ ((v2_tops_1 @ sk_B @ sk_A))),
% 0.36/0.60      inference('split', [status(esa)], ['0'])).
% 0.36/0.60  thf('3', plain,
% 0.36/0.60      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.60  thf(t74_tops_1, axiom,
% 0.36/0.60    (![A:$i]:
% 0.36/0.60     ( ( l1_pre_topc @ A ) =>
% 0.36/0.60       ( ![B:$i]:
% 0.36/0.60         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.36/0.60           ( ( k1_tops_1 @ A @ B ) =
% 0.36/0.60             ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.36/0.60  thf('4', plain,
% 0.36/0.60      (![X57 : $i, X58 : $i]:
% 0.36/0.60         (~ (m1_subset_1 @ X57 @ (k1_zfmisc_1 @ (u1_struct_0 @ X58)))
% 0.36/0.60          | ((k1_tops_1 @ X58 @ X57)
% 0.36/0.60              = (k7_subset_1 @ (u1_struct_0 @ X58) @ X57 @ 
% 0.36/0.60                 (k2_tops_1 @ X58 @ X57)))
% 0.36/0.60          | ~ (l1_pre_topc @ X58))),
% 0.36/0.60      inference('cnf', [status(esa)], [t74_tops_1])).
% 0.36/0.60  thf('5', plain,
% 0.36/0.60      ((~ (l1_pre_topc @ sk_A)
% 0.36/0.60        | ((k1_tops_1 @ sk_A @ sk_B)
% 0.36/0.60            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.36/0.60               (k2_tops_1 @ sk_A @ sk_B))))),
% 0.36/0.60      inference('sup-', [status(thm)], ['3', '4'])).
% 0.36/0.60  thf('6', plain, ((l1_pre_topc @ sk_A)),
% 0.36/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.60  thf('7', plain,
% 0.36/0.60      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.60  thf(redefinition_k7_subset_1, axiom,
% 0.36/0.60    (![A:$i,B:$i,C:$i]:
% 0.36/0.60     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.36/0.60       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 0.36/0.60  thf('8', plain,
% 0.36/0.60      (![X44 : $i, X45 : $i, X46 : $i]:
% 0.36/0.60         (~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ X45))
% 0.36/0.60          | ((k7_subset_1 @ X45 @ X44 @ X46) = (k4_xboole_0 @ X44 @ X46)))),
% 0.36/0.60      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 0.36/0.60  thf('9', plain,
% 0.36/0.60      (![X0 : $i]:
% 0.36/0.60         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.36/0.60           = (k4_xboole_0 @ sk_B @ X0))),
% 0.36/0.60      inference('sup-', [status(thm)], ['7', '8'])).
% 0.36/0.60  thf('10', plain,
% 0.36/0.60      (((k1_tops_1 @ sk_A @ sk_B)
% 0.36/0.60         = (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.36/0.60      inference('demod', [status(thm)], ['5', '6', '9'])).
% 0.36/0.60  thf(d3_tarski, axiom,
% 0.36/0.60    (![A:$i,B:$i]:
% 0.36/0.60     ( ( r1_tarski @ A @ B ) <=>
% 0.36/0.60       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.36/0.60  thf('11', plain,
% 0.36/0.60      (![X1 : $i, X3 : $i]:
% 0.36/0.60         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.36/0.60      inference('cnf', [status(esa)], [d3_tarski])).
% 0.36/0.60  thf(d5_xboole_0, axiom,
% 0.36/0.60    (![A:$i,B:$i,C:$i]:
% 0.36/0.60     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.36/0.60       ( ![D:$i]:
% 0.36/0.60         ( ( r2_hidden @ D @ C ) <=>
% 0.36/0.60           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.36/0.60  thf('12', plain,
% 0.36/0.60      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.36/0.60         (~ (r2_hidden @ X8 @ X7)
% 0.36/0.60          | (r2_hidden @ X8 @ X5)
% 0.36/0.60          | ((X7) != (k4_xboole_0 @ X5 @ X6)))),
% 0.36/0.60      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.36/0.60  thf('13', plain,
% 0.36/0.60      (![X5 : $i, X6 : $i, X8 : $i]:
% 0.36/0.60         ((r2_hidden @ X8 @ X5) | ~ (r2_hidden @ X8 @ (k4_xboole_0 @ X5 @ X6)))),
% 0.36/0.60      inference('simplify', [status(thm)], ['12'])).
% 0.36/0.60  thf('14', plain,
% 0.36/0.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.36/0.60         ((r1_tarski @ (k4_xboole_0 @ X1 @ X0) @ X2)
% 0.36/0.60          | (r2_hidden @ (sk_C @ X2 @ (k4_xboole_0 @ X1 @ X0)) @ X1))),
% 0.36/0.60      inference('sup-', [status(thm)], ['11', '13'])).
% 0.36/0.60  thf('15', plain,
% 0.36/0.60      (![X1 : $i, X3 : $i]:
% 0.36/0.60         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.36/0.60      inference('cnf', [status(esa)], [d3_tarski])).
% 0.36/0.60  thf('16', plain,
% 0.36/0.60      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.36/0.60         (~ (r2_hidden @ X4 @ X5)
% 0.36/0.60          | (r2_hidden @ X4 @ X6)
% 0.36/0.60          | (r2_hidden @ X4 @ X7)
% 0.36/0.60          | ((X7) != (k4_xboole_0 @ X5 @ X6)))),
% 0.36/0.60      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.36/0.60  thf('17', plain,
% 0.36/0.60      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.36/0.60         ((r2_hidden @ X4 @ (k4_xboole_0 @ X5 @ X6))
% 0.36/0.60          | (r2_hidden @ X4 @ X6)
% 0.36/0.60          | ~ (r2_hidden @ X4 @ X5))),
% 0.36/0.60      inference('simplify', [status(thm)], ['16'])).
% 0.36/0.60  thf('18', plain,
% 0.36/0.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.36/0.60         ((r1_tarski @ X0 @ X1)
% 0.36/0.60          | (r2_hidden @ (sk_C @ X1 @ X0) @ X2)
% 0.36/0.60          | (r2_hidden @ (sk_C @ X1 @ X0) @ (k4_xboole_0 @ X0 @ X2)))),
% 0.36/0.60      inference('sup-', [status(thm)], ['15', '17'])).
% 0.36/0.60  thf('19', plain,
% 0.36/0.60      (![X1 : $i, X3 : $i]:
% 0.36/0.60         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.36/0.60      inference('cnf', [status(esa)], [d3_tarski])).
% 0.36/0.60  thf('20', plain,
% 0.36/0.60      (![X0 : $i, X1 : $i]:
% 0.36/0.60         ((r2_hidden @ (sk_C @ (k4_xboole_0 @ X1 @ X0) @ X1) @ X0)
% 0.36/0.60          | (r1_tarski @ X1 @ (k4_xboole_0 @ X1 @ X0))
% 0.36/0.60          | (r1_tarski @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.36/0.60      inference('sup-', [status(thm)], ['18', '19'])).
% 0.36/0.60  thf('21', plain,
% 0.36/0.60      (![X0 : $i, X1 : $i]:
% 0.36/0.60         ((r1_tarski @ X1 @ (k4_xboole_0 @ X1 @ X0))
% 0.36/0.60          | (r2_hidden @ (sk_C @ (k4_xboole_0 @ X1 @ X0) @ X1) @ X0))),
% 0.36/0.60      inference('simplify', [status(thm)], ['20'])).
% 0.36/0.60  thf('22', plain,
% 0.36/0.60      (((r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.36/0.60        | (v2_tops_1 @ sk_B @ sk_A))),
% 0.36/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.60  thf('23', plain,
% 0.36/0.60      (((r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))
% 0.36/0.60         <= (((r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))),
% 0.36/0.60      inference('split', [status(esa)], ['22'])).
% 0.36/0.60  thf('24', plain,
% 0.36/0.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.36/0.60         (~ (r2_hidden @ X0 @ X1)
% 0.36/0.60          | (r2_hidden @ X0 @ X2)
% 0.36/0.60          | ~ (r1_tarski @ X1 @ X2))),
% 0.36/0.60      inference('cnf', [status(esa)], [d3_tarski])).
% 0.36/0.60  thf('25', plain,
% 0.36/0.60      ((![X0 : $i]:
% 0.36/0.60          ((r2_hidden @ X0 @ (k2_tops_1 @ sk_A @ sk_B))
% 0.36/0.60           | ~ (r2_hidden @ X0 @ sk_B)))
% 0.36/0.60         <= (((r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))),
% 0.36/0.60      inference('sup-', [status(thm)], ['23', '24'])).
% 0.36/0.60  thf('26', plain,
% 0.36/0.60      ((![X0 : $i]:
% 0.36/0.60          ((r1_tarski @ X0 @ (k4_xboole_0 @ X0 @ sk_B))
% 0.36/0.60           | (r2_hidden @ (sk_C @ (k4_xboole_0 @ X0 @ sk_B) @ X0) @ 
% 0.36/0.60              (k2_tops_1 @ sk_A @ sk_B))))
% 0.36/0.60         <= (((r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))),
% 0.36/0.60      inference('sup-', [status(thm)], ['21', '25'])).
% 0.36/0.60  thf('27', plain,
% 0.36/0.60      (![X1 : $i, X3 : $i]:
% 0.36/0.60         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.36/0.60      inference('cnf', [status(esa)], [d3_tarski])).
% 0.36/0.60  thf('28', plain,
% 0.36/0.60      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.36/0.60         (~ (r2_hidden @ X8 @ X7)
% 0.36/0.60          | ~ (r2_hidden @ X8 @ X6)
% 0.36/0.60          | ((X7) != (k4_xboole_0 @ X5 @ X6)))),
% 0.36/0.60      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.36/0.60  thf('29', plain,
% 0.36/0.60      (![X5 : $i, X6 : $i, X8 : $i]:
% 0.36/0.60         (~ (r2_hidden @ X8 @ X6)
% 0.36/0.60          | ~ (r2_hidden @ X8 @ (k4_xboole_0 @ X5 @ X6)))),
% 0.36/0.60      inference('simplify', [status(thm)], ['28'])).
% 0.36/0.60  thf('30', plain,
% 0.36/0.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.36/0.60         ((r1_tarski @ (k4_xboole_0 @ X1 @ X0) @ X2)
% 0.36/0.60          | ~ (r2_hidden @ (sk_C @ X2 @ (k4_xboole_0 @ X1 @ X0)) @ X0))),
% 0.36/0.60      inference('sup-', [status(thm)], ['27', '29'])).
% 0.36/0.60  thf('31', plain,
% 0.36/0.60      ((![X0 : $i]:
% 0.36/0.60          ((r1_tarski @ (k4_xboole_0 @ X0 @ (k2_tops_1 @ sk_A @ sk_B)) @ 
% 0.36/0.60            (k4_xboole_0 @ (k4_xboole_0 @ X0 @ (k2_tops_1 @ sk_A @ sk_B)) @ 
% 0.36/0.60             sk_B))
% 0.36/0.60           | (r1_tarski @ (k4_xboole_0 @ X0 @ (k2_tops_1 @ sk_A @ sk_B)) @ 
% 0.36/0.60              (k4_xboole_0 @ (k4_xboole_0 @ X0 @ (k2_tops_1 @ sk_A @ sk_B)) @ 
% 0.36/0.60               sk_B))))
% 0.36/0.60         <= (((r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))),
% 0.36/0.60      inference('sup-', [status(thm)], ['26', '30'])).
% 0.36/0.60  thf('32', plain,
% 0.36/0.60      ((![X0 : $i]:
% 0.36/0.60          (r1_tarski @ (k4_xboole_0 @ X0 @ (k2_tops_1 @ sk_A @ sk_B)) @ 
% 0.36/0.60           (k4_xboole_0 @ (k4_xboole_0 @ X0 @ (k2_tops_1 @ sk_A @ sk_B)) @ sk_B)))
% 0.36/0.60         <= (((r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))),
% 0.36/0.60      inference('simplify', [status(thm)], ['31'])).
% 0.36/0.60  thf('33', plain,
% 0.36/0.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.36/0.60         ((r1_tarski @ (k4_xboole_0 @ X1 @ X0) @ X2)
% 0.36/0.60          | (r2_hidden @ (sk_C @ X2 @ (k4_xboole_0 @ X1 @ X0)) @ X1))),
% 0.36/0.60      inference('sup-', [status(thm)], ['11', '13'])).
% 0.36/0.60  thf('34', plain,
% 0.36/0.60      (![X1 : $i, X3 : $i]:
% 0.36/0.60         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.36/0.60      inference('cnf', [status(esa)], [d3_tarski])).
% 0.36/0.60  thf('35', plain,
% 0.36/0.60      (![X0 : $i, X1 : $i]:
% 0.36/0.60         ((r1_tarski @ (k4_xboole_0 @ X0 @ X1) @ X0)
% 0.36/0.60          | (r1_tarski @ (k4_xboole_0 @ X0 @ X1) @ X0))),
% 0.36/0.60      inference('sup-', [status(thm)], ['33', '34'])).
% 0.36/0.60  thf('36', plain,
% 0.36/0.60      (![X0 : $i, X1 : $i]: (r1_tarski @ (k4_xboole_0 @ X0 @ X1) @ X0)),
% 0.36/0.60      inference('simplify', [status(thm)], ['35'])).
% 0.36/0.60  thf(d10_xboole_0, axiom,
% 0.36/0.60    (![A:$i,B:$i]:
% 0.36/0.60     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.36/0.60  thf('37', plain,
% 0.36/0.60      (![X10 : $i, X12 : $i]:
% 0.36/0.60         (((X10) = (X12))
% 0.36/0.60          | ~ (r1_tarski @ X12 @ X10)
% 0.36/0.60          | ~ (r1_tarski @ X10 @ X12))),
% 0.36/0.60      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.36/0.60  thf('38', plain,
% 0.36/0.60      (![X0 : $i, X1 : $i]:
% 0.36/0.60         (~ (r1_tarski @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 0.36/0.60          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 0.36/0.60      inference('sup-', [status(thm)], ['36', '37'])).
% 0.36/0.60  thf('39', plain,
% 0.36/0.60      ((![X0 : $i]:
% 0.36/0.60          ((k4_xboole_0 @ X0 @ (k2_tops_1 @ sk_A @ sk_B))
% 0.36/0.60            = (k4_xboole_0 @ (k4_xboole_0 @ X0 @ (k2_tops_1 @ sk_A @ sk_B)) @ 
% 0.36/0.60               sk_B)))
% 0.36/0.60         <= (((r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))),
% 0.36/0.60      inference('sup-', [status(thm)], ['32', '38'])).
% 0.36/0.60  thf('40', plain,
% 0.36/0.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.36/0.60         ((r1_tarski @ (k4_xboole_0 @ X1 @ X0) @ X2)
% 0.36/0.60          | ~ (r2_hidden @ (sk_C @ X2 @ (k4_xboole_0 @ X1 @ X0)) @ X0))),
% 0.36/0.60      inference('sup-', [status(thm)], ['27', '29'])).
% 0.36/0.60  thf('41', plain,
% 0.36/0.60      ((![X0 : $i, X1 : $i]:
% 0.36/0.60          (~ (r2_hidden @ 
% 0.36/0.60              (sk_C @ X1 @ (k4_xboole_0 @ X0 @ (k2_tops_1 @ sk_A @ sk_B))) @ 
% 0.36/0.60              sk_B)
% 0.36/0.60           | (r1_tarski @ 
% 0.36/0.60              (k4_xboole_0 @ (k4_xboole_0 @ X0 @ (k2_tops_1 @ sk_A @ sk_B)) @ 
% 0.36/0.60               sk_B) @ 
% 0.36/0.60              X1)))
% 0.36/0.60         <= (((r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))),
% 0.36/0.60      inference('sup-', [status(thm)], ['39', '40'])).
% 0.36/0.60  thf('42', plain,
% 0.36/0.60      ((![X0 : $i]:
% 0.36/0.60          ((k4_xboole_0 @ X0 @ (k2_tops_1 @ sk_A @ sk_B))
% 0.36/0.60            = (k4_xboole_0 @ (k4_xboole_0 @ X0 @ (k2_tops_1 @ sk_A @ sk_B)) @ 
% 0.36/0.60               sk_B)))
% 0.36/0.60         <= (((r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))),
% 0.36/0.60      inference('sup-', [status(thm)], ['32', '38'])).
% 0.36/0.60  thf('43', plain,
% 0.36/0.60      ((![X0 : $i, X1 : $i]:
% 0.36/0.60          (~ (r2_hidden @ 
% 0.36/0.60              (sk_C @ X1 @ (k4_xboole_0 @ X0 @ (k2_tops_1 @ sk_A @ sk_B))) @ 
% 0.36/0.60              sk_B)
% 0.36/0.60           | (r1_tarski @ (k4_xboole_0 @ X0 @ (k2_tops_1 @ sk_A @ sk_B)) @ X1)))
% 0.36/0.60         <= (((r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))),
% 0.36/0.60      inference('demod', [status(thm)], ['41', '42'])).
% 0.36/0.60  thf('44', plain,
% 0.36/0.60      ((![X0 : $i]:
% 0.36/0.60          ((r1_tarski @ (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)) @ X0)
% 0.36/0.60           | (r1_tarski @ (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)) @ X0)))
% 0.36/0.60         <= (((r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))),
% 0.36/0.60      inference('sup-', [status(thm)], ['14', '43'])).
% 0.36/0.60  thf('45', plain,
% 0.36/0.60      ((![X0 : $i]:
% 0.36/0.60          (r1_tarski @ (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)) @ X0))
% 0.36/0.60         <= (((r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))),
% 0.36/0.60      inference('simplify', [status(thm)], ['44'])).
% 0.36/0.60  thf('46', plain,
% 0.36/0.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.36/0.60         ((r1_tarski @ (k4_xboole_0 @ X1 @ X0) @ X2)
% 0.36/0.60          | (r2_hidden @ (sk_C @ X2 @ (k4_xboole_0 @ X1 @ X0)) @ X1))),
% 0.36/0.60      inference('sup-', [status(thm)], ['11', '13'])).
% 0.36/0.60  thf('47', plain,
% 0.36/0.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.36/0.60         ((r1_tarski @ (k4_xboole_0 @ X1 @ X0) @ X2)
% 0.36/0.60          | ~ (r2_hidden @ (sk_C @ X2 @ (k4_xboole_0 @ X1 @ X0)) @ X0))),
% 0.36/0.60      inference('sup-', [status(thm)], ['27', '29'])).
% 0.36/0.60  thf('48', plain,
% 0.36/0.60      (![X0 : $i, X1 : $i]:
% 0.36/0.60         ((r1_tarski @ (k4_xboole_0 @ X0 @ X0) @ X1)
% 0.36/0.60          | (r1_tarski @ (k4_xboole_0 @ X0 @ X0) @ X1))),
% 0.36/0.60      inference('sup-', [status(thm)], ['46', '47'])).
% 0.36/0.60  thf('49', plain,
% 0.36/0.60      (![X0 : $i, X1 : $i]: (r1_tarski @ (k4_xboole_0 @ X0 @ X0) @ X1)),
% 0.36/0.60      inference('simplify', [status(thm)], ['48'])).
% 0.36/0.60  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.36/0.60  thf('50', plain, (![X15 : $i]: (r1_tarski @ k1_xboole_0 @ X15)),
% 0.36/0.60      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.36/0.60  thf('51', plain,
% 0.36/0.60      (![X10 : $i, X12 : $i]:
% 0.36/0.60         (((X10) = (X12))
% 0.36/0.60          | ~ (r1_tarski @ X12 @ X10)
% 0.36/0.60          | ~ (r1_tarski @ X10 @ X12))),
% 0.36/0.60      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.36/0.60  thf('52', plain,
% 0.36/0.60      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.36/0.60      inference('sup-', [status(thm)], ['50', '51'])).
% 0.36/0.60  thf('53', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.36/0.60      inference('sup-', [status(thm)], ['49', '52'])).
% 0.36/0.60  thf(t100_xboole_1, axiom,
% 0.36/0.60    (![A:$i,B:$i]:
% 0.36/0.60     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.36/0.60  thf('54', plain,
% 0.36/0.60      (![X13 : $i, X14 : $i]:
% 0.36/0.60         ((k4_xboole_0 @ X13 @ X14)
% 0.36/0.60           = (k5_xboole_0 @ X13 @ (k3_xboole_0 @ X13 @ X14)))),
% 0.36/0.60      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.36/0.60  thf('55', plain,
% 0.36/0.60      (![X0 : $i]:
% 0.36/0.60         ((k1_xboole_0) = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X0)))),
% 0.36/0.60      inference('sup+', [status(thm)], ['53', '54'])).
% 0.36/0.60  thf('56', plain,
% 0.36/0.60      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.36/0.60      inference('sup-', [status(thm)], ['50', '51'])).
% 0.36/0.60  thf('57', plain,
% 0.36/0.60      (![X0 : $i, X1 : $i]:
% 0.36/0.60         (~ (r1_tarski @ X1 @ (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X0)))
% 0.36/0.60          | ((X1) = (k1_xboole_0)))),
% 0.36/0.60      inference('sup-', [status(thm)], ['55', '56'])).
% 0.36/0.60  thf('58', plain,
% 0.36/0.60      ((((k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)) = (k1_xboole_0)))
% 0.36/0.60         <= (((r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))),
% 0.36/0.60      inference('sup-', [status(thm)], ['45', '57'])).
% 0.36/0.60  thf('59', plain,
% 0.36/0.60      ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0)))
% 0.36/0.60         <= (((r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))),
% 0.36/0.60      inference('sup+', [status(thm)], ['10', '58'])).
% 0.36/0.60  thf('60', plain,
% 0.36/0.60      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.60  thf(t84_tops_1, axiom,
% 0.36/0.60    (![A:$i]:
% 0.36/0.60     ( ( l1_pre_topc @ A ) =>
% 0.36/0.60       ( ![B:$i]:
% 0.36/0.60         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.36/0.60           ( ( v2_tops_1 @ B @ A ) <=>
% 0.36/0.60             ( ( k1_tops_1 @ A @ B ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 0.36/0.60  thf('61', plain,
% 0.36/0.60      (![X59 : $i, X60 : $i]:
% 0.36/0.60         (~ (m1_subset_1 @ X59 @ (k1_zfmisc_1 @ (u1_struct_0 @ X60)))
% 0.36/0.60          | ((k1_tops_1 @ X60 @ X59) != (k1_xboole_0))
% 0.36/0.60          | (v2_tops_1 @ X59 @ X60)
% 0.36/0.60          | ~ (l1_pre_topc @ X60))),
% 0.36/0.60      inference('cnf', [status(esa)], [t84_tops_1])).
% 0.36/0.60  thf('62', plain,
% 0.36/0.60      ((~ (l1_pre_topc @ sk_A)
% 0.36/0.60        | (v2_tops_1 @ sk_B @ sk_A)
% 0.36/0.60        | ((k1_tops_1 @ sk_A @ sk_B) != (k1_xboole_0)))),
% 0.36/0.60      inference('sup-', [status(thm)], ['60', '61'])).
% 0.36/0.60  thf('63', plain, ((l1_pre_topc @ sk_A)),
% 0.36/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.60  thf('64', plain,
% 0.36/0.60      (((v2_tops_1 @ sk_B @ sk_A)
% 0.36/0.60        | ((k1_tops_1 @ sk_A @ sk_B) != (k1_xboole_0)))),
% 0.36/0.60      inference('demod', [status(thm)], ['62', '63'])).
% 0.36/0.60  thf('65', plain,
% 0.36/0.60      (((((k1_xboole_0) != (k1_xboole_0)) | (v2_tops_1 @ sk_B @ sk_A)))
% 0.36/0.60         <= (((r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))),
% 0.36/0.60      inference('sup-', [status(thm)], ['59', '64'])).
% 0.36/0.60  thf('66', plain,
% 0.36/0.60      (((v2_tops_1 @ sk_B @ sk_A))
% 0.36/0.60         <= (((r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))),
% 0.36/0.60      inference('simplify', [status(thm)], ['65'])).
% 0.36/0.60  thf('67', plain,
% 0.36/0.60      ((~ (v2_tops_1 @ sk_B @ sk_A)) <= (~ ((v2_tops_1 @ sk_B @ sk_A)))),
% 0.36/0.60      inference('split', [status(esa)], ['0'])).
% 0.36/0.60  thf('68', plain,
% 0.36/0.60      (((v2_tops_1 @ sk_B @ sk_A)) | 
% 0.36/0.60       ~ ((r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.36/0.60      inference('sup-', [status(thm)], ['66', '67'])).
% 0.36/0.60  thf('69', plain, (~ ((r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.36/0.60      inference('sat_resolution*', [status(thm)], ['2', '68'])).
% 0.36/0.60  thf('70', plain, (~ (r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))),
% 0.36/0.60      inference('simpl_trail', [status(thm)], ['1', '69'])).
% 0.36/0.60  thf('71', plain,
% 0.36/0.60      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.60  thf(t48_pre_topc, axiom,
% 0.36/0.60    (![A:$i]:
% 0.36/0.60     ( ( l1_pre_topc @ A ) =>
% 0.36/0.60       ( ![B:$i]:
% 0.36/0.60         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.36/0.60           ( r1_tarski @ B @ ( k2_pre_topc @ A @ B ) ) ) ) ))).
% 0.36/0.60  thf('72', plain,
% 0.36/0.60      (![X51 : $i, X52 : $i]:
% 0.36/0.60         (~ (m1_subset_1 @ X51 @ (k1_zfmisc_1 @ (u1_struct_0 @ X52)))
% 0.36/0.60          | (r1_tarski @ X51 @ (k2_pre_topc @ X52 @ X51))
% 0.36/0.60          | ~ (l1_pre_topc @ X52))),
% 0.36/0.60      inference('cnf', [status(esa)], [t48_pre_topc])).
% 0.36/0.60  thf('73', plain,
% 0.36/0.60      ((~ (l1_pre_topc @ sk_A)
% 0.36/0.60        | (r1_tarski @ sk_B @ (k2_pre_topc @ sk_A @ sk_B)))),
% 0.36/0.60      inference('sup-', [status(thm)], ['71', '72'])).
% 0.36/0.60  thf('74', plain, ((l1_pre_topc @ sk_A)),
% 0.36/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.60  thf('75', plain, ((r1_tarski @ sk_B @ (k2_pre_topc @ sk_A @ sk_B))),
% 0.36/0.60      inference('demod', [status(thm)], ['73', '74'])).
% 0.36/0.60  thf('76', plain,
% 0.36/0.60      (((v2_tops_1 @ sk_B @ sk_A)) <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.36/0.60      inference('split', [status(esa)], ['22'])).
% 0.36/0.60  thf('77', plain,
% 0.36/0.60      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.60  thf('78', plain,
% 0.36/0.60      (![X59 : $i, X60 : $i]:
% 0.36/0.60         (~ (m1_subset_1 @ X59 @ (k1_zfmisc_1 @ (u1_struct_0 @ X60)))
% 0.36/0.60          | ~ (v2_tops_1 @ X59 @ X60)
% 0.36/0.60          | ((k1_tops_1 @ X60 @ X59) = (k1_xboole_0))
% 0.36/0.60          | ~ (l1_pre_topc @ X60))),
% 0.36/0.60      inference('cnf', [status(esa)], [t84_tops_1])).
% 0.36/0.60  thf('79', plain,
% 0.36/0.60      ((~ (l1_pre_topc @ sk_A)
% 0.36/0.60        | ((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))
% 0.36/0.60        | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 0.36/0.60      inference('sup-', [status(thm)], ['77', '78'])).
% 0.36/0.60  thf('80', plain, ((l1_pre_topc @ sk_A)),
% 0.36/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.60  thf('81', plain,
% 0.36/0.60      ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))
% 0.36/0.60        | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 0.36/0.60      inference('demod', [status(thm)], ['79', '80'])).
% 0.36/0.60  thf('82', plain,
% 0.36/0.60      ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0)))
% 0.36/0.60         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.36/0.60      inference('sup-', [status(thm)], ['76', '81'])).
% 0.36/0.60  thf('83', plain,
% 0.36/0.60      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.60  thf(l78_tops_1, axiom,
% 0.36/0.60    (![A:$i]:
% 0.36/0.60     ( ( l1_pre_topc @ A ) =>
% 0.36/0.60       ( ![B:$i]:
% 0.36/0.60         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.36/0.60           ( ( k2_tops_1 @ A @ B ) =
% 0.36/0.60             ( k7_subset_1 @
% 0.36/0.60               ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 0.36/0.60               ( k1_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.36/0.60  thf('84', plain,
% 0.36/0.60      (![X53 : $i, X54 : $i]:
% 0.36/0.60         (~ (m1_subset_1 @ X53 @ (k1_zfmisc_1 @ (u1_struct_0 @ X54)))
% 0.36/0.60          | ((k2_tops_1 @ X54 @ X53)
% 0.36/0.60              = (k7_subset_1 @ (u1_struct_0 @ X54) @ 
% 0.36/0.60                 (k2_pre_topc @ X54 @ X53) @ (k1_tops_1 @ X54 @ X53)))
% 0.36/0.60          | ~ (l1_pre_topc @ X54))),
% 0.36/0.60      inference('cnf', [status(esa)], [l78_tops_1])).
% 0.36/0.60  thf('85', plain,
% 0.36/0.60      ((~ (l1_pre_topc @ sk_A)
% 0.36/0.60        | ((k2_tops_1 @ sk_A @ sk_B)
% 0.36/0.60            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.36/0.60               (k2_pre_topc @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ sk_B))))),
% 0.36/0.60      inference('sup-', [status(thm)], ['83', '84'])).
% 0.36/0.60  thf('86', plain, ((l1_pre_topc @ sk_A)),
% 0.36/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.60  thf('87', plain,
% 0.36/0.60      (((k2_tops_1 @ sk_A @ sk_B)
% 0.36/0.60         = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.36/0.60            (k1_tops_1 @ sk_A @ sk_B)))),
% 0.36/0.60      inference('demod', [status(thm)], ['85', '86'])).
% 0.36/0.60  thf('88', plain,
% 0.36/0.60      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.36/0.60          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.36/0.60             (k2_pre_topc @ sk_A @ sk_B) @ k1_xboole_0)))
% 0.36/0.60         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.36/0.60      inference('sup+', [status(thm)], ['82', '87'])).
% 0.36/0.60  thf('89', plain,
% 0.36/0.60      (((v2_tops_1 @ sk_B @ sk_A)) | 
% 0.36/0.60       ((r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.36/0.60      inference('split', [status(esa)], ['22'])).
% 0.36/0.60  thf('90', plain, (((v2_tops_1 @ sk_B @ sk_A))),
% 0.36/0.60      inference('sat_resolution*', [status(thm)], ['2', '68', '89'])).
% 0.36/0.60  thf('91', plain,
% 0.36/0.60      (((k2_tops_1 @ sk_A @ sk_B)
% 0.36/0.60         = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.36/0.60            k1_xboole_0))),
% 0.36/0.60      inference('simpl_trail', [status(thm)], ['88', '90'])).
% 0.36/0.60  thf('92', plain,
% 0.36/0.60      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.60  thf(dt_k2_pre_topc, axiom,
% 0.36/0.60    (![A:$i,B:$i]:
% 0.36/0.60     ( ( ( l1_pre_topc @ A ) & 
% 0.36/0.60         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.36/0.60       ( m1_subset_1 @
% 0.36/0.60         ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.36/0.60  thf('93', plain,
% 0.36/0.60      (![X49 : $i, X50 : $i]:
% 0.36/0.60         (~ (l1_pre_topc @ X49)
% 0.36/0.60          | ~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ (u1_struct_0 @ X49)))
% 0.36/0.60          | (m1_subset_1 @ (k2_pre_topc @ X49 @ X50) @ 
% 0.36/0.60             (k1_zfmisc_1 @ (u1_struct_0 @ X49))))),
% 0.36/0.60      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 0.36/0.60  thf('94', plain,
% 0.36/0.60      (((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.36/0.60         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.36/0.60        | ~ (l1_pre_topc @ sk_A))),
% 0.36/0.60      inference('sup-', [status(thm)], ['92', '93'])).
% 0.36/0.60  thf('95', plain, ((l1_pre_topc @ sk_A)),
% 0.36/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.60  thf('96', plain,
% 0.36/0.60      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.36/0.60        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.60      inference('demod', [status(thm)], ['94', '95'])).
% 0.36/0.60  thf('97', plain,
% 0.36/0.60      (![X44 : $i, X45 : $i, X46 : $i]:
% 0.36/0.60         (~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ X45))
% 0.36/0.60          | ((k7_subset_1 @ X45 @ X44 @ X46) = (k4_xboole_0 @ X44 @ X46)))),
% 0.36/0.60      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 0.36/0.60  thf('98', plain,
% 0.36/0.60      (![X0 : $i]:
% 0.36/0.60         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.36/0.60           X0) = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ X0))),
% 0.36/0.60      inference('sup-', [status(thm)], ['96', '97'])).
% 0.36/0.60  thf(t3_boole, axiom,
% 0.36/0.60    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.36/0.60  thf('99', plain, (![X16 : $i]: ((k4_xboole_0 @ X16 @ k1_xboole_0) = (X16))),
% 0.36/0.60      inference('cnf', [status(esa)], [t3_boole])).
% 0.36/0.60  thf('100', plain,
% 0.36/0.60      (((k2_tops_1 @ sk_A @ sk_B) = (k2_pre_topc @ sk_A @ sk_B))),
% 0.36/0.60      inference('demod', [status(thm)], ['91', '98', '99'])).
% 0.36/0.60  thf('101', plain, ((r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))),
% 0.36/0.60      inference('demod', [status(thm)], ['75', '100'])).
% 0.36/0.60  thf('102', plain, ($false), inference('demod', [status(thm)], ['70', '101'])).
% 0.36/0.60  
% 0.36/0.60  % SZS output end Refutation
% 0.36/0.60  
% 0.36/0.61  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
