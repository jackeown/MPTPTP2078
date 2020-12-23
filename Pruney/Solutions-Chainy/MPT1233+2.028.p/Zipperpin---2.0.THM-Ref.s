%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.IeQs31k38x

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:02:53 EST 2020

% Result     : Theorem 0.46s
% Output     : Refutation 0.46s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 123 expanded)
%              Number of leaves         :   39 (  52 expanded)
%              Depth                    :   19
%              Number of atoms          :  636 ( 805 expanded)
%              Number of equality atoms :   54 (  69 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('0',plain,(
    ! [X46: $i] :
      ( ( ( k2_struct_0 @ X46 )
        = ( u1_struct_0 @ X46 ) )
      | ~ ( l1_struct_0 @ X46 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('1',plain,(
    ! [X46: $i] :
      ( ( ( k2_struct_0 @ X46 )
        = ( u1_struct_0 @ X46 ) )
      | ~ ( l1_struct_0 @ X46 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('2',plain,(
    ! [X36: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(cc2_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v1_xboole_0 @ B )
           => ( v4_pre_topc @ B @ A ) ) ) ) )).

thf('3',plain,(
    ! [X44: $i,X45: $i] :
      ( ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X45 ) ) )
      | ( v4_pre_topc @ X44 @ X45 )
      | ~ ( v1_xboole_0 @ X44 )
      | ~ ( l1_pre_topc @ X45 )
      | ~ ( v2_pre_topc @ X45 ) ) ),
    inference(cnf,[status(esa)],[cc2_pre_topc])).

thf('4',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( v4_pre_topc @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('5',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('6',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v4_pre_topc @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X36: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(t52_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( ( v4_pre_topc @ B @ A )
             => ( ( k2_pre_topc @ A @ B )
                = B ) )
            & ( ( ( v2_pre_topc @ A )
                & ( ( k2_pre_topc @ A @ B )
                  = B ) )
             => ( v4_pre_topc @ B @ A ) ) ) ) ) )).

thf('8',plain,(
    ! [X48: $i,X49: $i] :
      ( ~ ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X49 ) ) )
      | ~ ( v4_pre_topc @ X48 @ X49 )
      | ( ( k2_pre_topc @ X49 @ X48 )
        = X48 )
      | ~ ( l1_pre_topc @ X49 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('9',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( k2_pre_topc @ X0 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( v4_pre_topc @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( ( k2_pre_topc @ X0 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( ( k2_pre_topc @ X0 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf(t56_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( r2_hidden @ A @ B )
     => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) )).

thf('12',plain,(
    ! [X29: $i,X30: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X29 ) @ X30 )
      | ( r2_hidden @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t56_zfmisc_1])).

thf(t80_zfmisc_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ ( k1_tarski @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('13',plain,(
    ! [X31: $i] :
      ( r1_tarski @ ( k1_tarski @ X31 ) @ ( k1_zfmisc_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t80_zfmisc_1])).

thf(l3_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k1_tarski @ B ) )
    <=> ( ( A = k1_xboole_0 )
        | ( A
          = ( k1_tarski @ B ) ) ) ) )).

thf('14',plain,(
    ! [X21: $i,X22: $i] :
      ( ( r1_tarski @ X21 @ ( k1_tarski @ X22 ) )
      | ( X21
       != ( k1_tarski @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('15',plain,(
    ! [X22: $i] :
      ( r1_tarski @ ( k1_tarski @ X22 ) @ ( k1_tarski @ X22 ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf(t67_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ A @ C )
        & ( r1_xboole_0 @ B @ C ) )
     => ( A = k1_xboole_0 ) ) )).

thf('16',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( X8 = k1_xboole_0 )
      | ~ ( r1_tarski @ X8 @ X9 )
      | ~ ( r1_tarski @ X8 @ X10 )
      | ~ ( r1_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t67_xboole_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
      | ~ ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf(t20_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k1_tarski @ A ) )
    <=> ( A != B ) ) )).

thf('18',plain,(
    ! [X26: $i,X27: $i] :
      ( ( X27 != X26 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X27 ) @ ( k1_tarski @ X26 ) )
       != ( k1_tarski @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[t20_zfmisc_1])).

thf('19',plain,(
    ! [X26: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X26 ) @ ( k1_tarski @ X26 ) )
     != ( k1_tarski @ X26 ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('20',plain,(
    ! [X4: $i] :
      ( ( k4_xboole_0 @ X4 @ k1_xboole_0 )
      = X4 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('21',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ ( k4_xboole_0 @ X5 @ X6 ) )
      = ( k3_xboole_0 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('23',plain,(
    ! [X3: $i] :
      ( ( k3_xboole_0 @ X3 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X26: $i] :
      ( k1_xboole_0
     != ( k1_tarski @ X26 ) ) ),
    inference(demod,[status(thm)],['19','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ~ ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) ) ),
    inference(clc,[status(thm)],['17','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ~ ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','27'])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('29',plain,(
    ! [X37: $i,X38: $i] :
      ( ( m1_subset_1 @ X37 @ X38 )
      | ~ ( r2_hidden @ X37 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('30',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf(d1_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k1_tops_1 @ A @ B )
            = ( k3_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) )).

thf('31',plain,(
    ! [X50: $i,X51: $i] :
      ( ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X51 ) ) )
      | ( ( k1_tops_1 @ X51 @ X50 )
        = ( k3_subset_1 @ ( u1_struct_0 @ X51 ) @ ( k2_pre_topc @ X51 @ ( k3_subset_1 @ ( u1_struct_0 @ X51 ) @ X50 ) ) ) )
      | ~ ( l1_pre_topc @ X51 ) ) ),
    inference(cnf,[status(esa)],[d1_tops_1])).

thf('32',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( k1_tops_1 @ X0 @ ( u1_struct_0 @ X0 ) )
        = ( k3_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k2_pre_topc @ X0 @ ( k3_subset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X36: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('34',plain,(
    ! [X34: $i,X35: $i] :
      ( ( ( k3_subset_1 @ X35 @ ( k3_subset_1 @ X35 @ X34 ) )
        = X34 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ ( k3_subset_1 @ X0 @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X36: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('37',plain,(
    ! [X32: $i,X33: $i] :
      ( ( ( k3_subset_1 @ X32 @ X33 )
        = ( k4_xboole_0 @ X32 @ X33 ) )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X4: $i] :
      ( ( k4_xboole_0 @ X4 @ k1_xboole_0 )
      = X4 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['35','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( k1_tops_1 @ X0 @ ( u1_struct_0 @ X0 ) )
        = ( k3_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k2_pre_topc @ X0 @ k1_xboole_0 ) ) ) ) ),
    inference(demod,[status(thm)],['32','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( ( k1_tops_1 @ X0 @ ( u1_struct_0 @ X0 ) )
        = ( k3_subset_1 @ ( u1_struct_0 @ X0 ) @ k1_xboole_0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup+',[status(thm)],['11','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( ( k1_tops_1 @ X0 @ ( u1_struct_0 @ X0 ) )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( k1_tops_1 @ X0 @ ( u1_struct_0 @ X0 ) )
        = ( u1_struct_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( ( k1_tops_1 @ X0 @ ( k2_struct_0 @ X0 ) )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','46'])).

thf(t43_tops_1,conjecture,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( ( k1_tops_1 @ A @ ( k2_struct_0 @ A ) )
        = ( k2_struct_0 @ A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ( ( k1_tops_1 @ A @ ( k2_struct_0 @ A ) )
          = ( k2_struct_0 @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t43_tops_1])).

thf('48',plain,(
    ( k1_tops_1 @ sk_A @ ( k2_struct_0 @ sk_A ) )
 != ( k2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( ( ( u1_struct_0 @ sk_A )
     != ( k2_struct_0 @ sk_A ) )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('53',plain,(
    ! [X47: $i] :
      ( ( l1_struct_0 @ X47 )
      | ~ ( l1_pre_topc @ X47 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('54',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    ( u1_struct_0 @ sk_A )
 != ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['49','50','51','54'])).

thf('56',plain,
    ( ( ( k2_struct_0 @ sk_A )
     != ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['0','55'])).

thf('57',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['52','53'])).

thf('58',plain,(
    ( k2_struct_0 @ sk_A )
 != ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,(
    $false ),
    inference(simplify,[status(thm)],['58'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.IeQs31k38x
% 0.16/0.38  % Computer   : n016.cluster.edu
% 0.16/0.38  % Model      : x86_64 x86_64
% 0.16/0.38  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.38  % Memory     : 8042.1875MB
% 0.16/0.38  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.38  % CPULimit   : 60
% 0.16/0.38  % DateTime   : Tue Dec  1 14:50:34 EST 2020
% 0.16/0.38  % CPUTime    : 
% 0.16/0.38  % Running portfolio for 600 s
% 0.16/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.16/0.38  % Number of cores: 8
% 0.16/0.38  % Python version: Python 3.6.8
% 0.16/0.39  % Running in FO mode
% 0.46/0.67  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.46/0.67  % Solved by: fo/fo7.sh
% 0.46/0.67  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.46/0.67  % done 781 iterations in 0.180s
% 0.46/0.67  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.46/0.67  % SZS output start Refutation
% 0.46/0.67  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.46/0.67  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.46/0.67  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.46/0.67  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.46/0.67  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.46/0.67  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.46/0.67  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.46/0.67  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.46/0.67  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.46/0.67  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.46/0.67  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.46/0.67  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.46/0.67  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.46/0.67  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.46/0.67  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.46/0.67  thf(sk_A_type, type, sk_A: $i).
% 0.46/0.67  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.46/0.67  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.46/0.67  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.46/0.67  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.46/0.67  thf(d3_struct_0, axiom,
% 0.46/0.67    (![A:$i]:
% 0.46/0.67     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.46/0.67  thf('0', plain,
% 0.46/0.67      (![X46 : $i]:
% 0.46/0.67         (((k2_struct_0 @ X46) = (u1_struct_0 @ X46)) | ~ (l1_struct_0 @ X46))),
% 0.46/0.67      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.46/0.67  thf('1', plain,
% 0.46/0.67      (![X46 : $i]:
% 0.46/0.67         (((k2_struct_0 @ X46) = (u1_struct_0 @ X46)) | ~ (l1_struct_0 @ X46))),
% 0.46/0.67      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.46/0.67  thf(t4_subset_1, axiom,
% 0.46/0.67    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.46/0.67  thf('2', plain,
% 0.46/0.67      (![X36 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X36))),
% 0.46/0.67      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.46/0.67  thf(cc2_pre_topc, axiom,
% 0.46/0.67    (![A:$i]:
% 0.46/0.67     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.46/0.67       ( ![B:$i]:
% 0.46/0.67         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.46/0.67           ( ( v1_xboole_0 @ B ) => ( v4_pre_topc @ B @ A ) ) ) ) ))).
% 0.46/0.67  thf('3', plain,
% 0.46/0.67      (![X44 : $i, X45 : $i]:
% 0.46/0.67         (~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (u1_struct_0 @ X45)))
% 0.46/0.67          | (v4_pre_topc @ X44 @ X45)
% 0.46/0.67          | ~ (v1_xboole_0 @ X44)
% 0.46/0.67          | ~ (l1_pre_topc @ X45)
% 0.46/0.67          | ~ (v2_pre_topc @ X45))),
% 0.46/0.67      inference('cnf', [status(esa)], [cc2_pre_topc])).
% 0.46/0.67  thf('4', plain,
% 0.46/0.67      (![X0 : $i]:
% 0.46/0.67         (~ (v2_pre_topc @ X0)
% 0.46/0.67          | ~ (l1_pre_topc @ X0)
% 0.46/0.67          | ~ (v1_xboole_0 @ k1_xboole_0)
% 0.46/0.67          | (v4_pre_topc @ k1_xboole_0 @ X0))),
% 0.46/0.67      inference('sup-', [status(thm)], ['2', '3'])).
% 0.46/0.67  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.46/0.67  thf('5', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.46/0.67      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.46/0.67  thf('6', plain,
% 0.46/0.67      (![X0 : $i]:
% 0.46/0.67         (~ (v2_pre_topc @ X0)
% 0.46/0.67          | ~ (l1_pre_topc @ X0)
% 0.46/0.67          | (v4_pre_topc @ k1_xboole_0 @ X0))),
% 0.46/0.67      inference('demod', [status(thm)], ['4', '5'])).
% 0.46/0.67  thf('7', plain,
% 0.46/0.67      (![X36 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X36))),
% 0.46/0.67      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.46/0.67  thf(t52_pre_topc, axiom,
% 0.46/0.67    (![A:$i]:
% 0.46/0.67     ( ( l1_pre_topc @ A ) =>
% 0.46/0.67       ( ![B:$i]:
% 0.46/0.67         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.46/0.67           ( ( ( v4_pre_topc @ B @ A ) => ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) & 
% 0.46/0.67             ( ( ( v2_pre_topc @ A ) & ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) =>
% 0.46/0.67               ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 0.46/0.67  thf('8', plain,
% 0.46/0.67      (![X48 : $i, X49 : $i]:
% 0.46/0.67         (~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ (u1_struct_0 @ X49)))
% 0.46/0.67          | ~ (v4_pre_topc @ X48 @ X49)
% 0.46/0.67          | ((k2_pre_topc @ X49 @ X48) = (X48))
% 0.46/0.67          | ~ (l1_pre_topc @ X49))),
% 0.46/0.67      inference('cnf', [status(esa)], [t52_pre_topc])).
% 0.46/0.67  thf('9', plain,
% 0.46/0.67      (![X0 : $i]:
% 0.46/0.67         (~ (l1_pre_topc @ X0)
% 0.46/0.67          | ((k2_pre_topc @ X0 @ k1_xboole_0) = (k1_xboole_0))
% 0.46/0.67          | ~ (v4_pre_topc @ k1_xboole_0 @ X0))),
% 0.46/0.67      inference('sup-', [status(thm)], ['7', '8'])).
% 0.46/0.67  thf('10', plain,
% 0.46/0.67      (![X0 : $i]:
% 0.46/0.67         (~ (l1_pre_topc @ X0)
% 0.46/0.67          | ~ (v2_pre_topc @ X0)
% 0.46/0.67          | ((k2_pre_topc @ X0 @ k1_xboole_0) = (k1_xboole_0))
% 0.46/0.67          | ~ (l1_pre_topc @ X0))),
% 0.46/0.67      inference('sup-', [status(thm)], ['6', '9'])).
% 0.46/0.67  thf('11', plain,
% 0.46/0.67      (![X0 : $i]:
% 0.46/0.67         (((k2_pre_topc @ X0 @ k1_xboole_0) = (k1_xboole_0))
% 0.46/0.67          | ~ (v2_pre_topc @ X0)
% 0.46/0.67          | ~ (l1_pre_topc @ X0))),
% 0.46/0.67      inference('simplify', [status(thm)], ['10'])).
% 0.46/0.67  thf(t56_zfmisc_1, axiom,
% 0.46/0.67    (![A:$i,B:$i]:
% 0.46/0.67     ( ( ~( r2_hidden @ A @ B ) ) => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ))).
% 0.46/0.67  thf('12', plain,
% 0.46/0.67      (![X29 : $i, X30 : $i]:
% 0.46/0.67         ((r1_xboole_0 @ (k1_tarski @ X29) @ X30) | (r2_hidden @ X29 @ X30))),
% 0.46/0.67      inference('cnf', [status(esa)], [t56_zfmisc_1])).
% 0.46/0.67  thf(t80_zfmisc_1, axiom,
% 0.46/0.67    (![A:$i]: ( r1_tarski @ ( k1_tarski @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.46/0.67  thf('13', plain,
% 0.46/0.67      (![X31 : $i]: (r1_tarski @ (k1_tarski @ X31) @ (k1_zfmisc_1 @ X31))),
% 0.46/0.67      inference('cnf', [status(esa)], [t80_zfmisc_1])).
% 0.46/0.67  thf(l3_zfmisc_1, axiom,
% 0.46/0.67    (![A:$i,B:$i]:
% 0.46/0.67     ( ( r1_tarski @ A @ ( k1_tarski @ B ) ) <=>
% 0.46/0.67       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( A ) = ( k1_tarski @ B ) ) ) ))).
% 0.46/0.67  thf('14', plain,
% 0.46/0.67      (![X21 : $i, X22 : $i]:
% 0.46/0.67         ((r1_tarski @ X21 @ (k1_tarski @ X22)) | ((X21) != (k1_tarski @ X22)))),
% 0.46/0.67      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 0.46/0.67  thf('15', plain,
% 0.46/0.67      (![X22 : $i]: (r1_tarski @ (k1_tarski @ X22) @ (k1_tarski @ X22))),
% 0.46/0.67      inference('simplify', [status(thm)], ['14'])).
% 0.46/0.67  thf(t67_xboole_1, axiom,
% 0.46/0.67    (![A:$i,B:$i,C:$i]:
% 0.46/0.67     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ A @ C ) & 
% 0.46/0.67         ( r1_xboole_0 @ B @ C ) ) =>
% 0.46/0.67       ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.46/0.67  thf('16', plain,
% 0.46/0.67      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.46/0.67         (((X8) = (k1_xboole_0))
% 0.46/0.67          | ~ (r1_tarski @ X8 @ X9)
% 0.46/0.67          | ~ (r1_tarski @ X8 @ X10)
% 0.46/0.67          | ~ (r1_xboole_0 @ X9 @ X10))),
% 0.46/0.67      inference('cnf', [status(esa)], [t67_xboole_1])).
% 0.46/0.67  thf('17', plain,
% 0.46/0.67      (![X0 : $i, X1 : $i]:
% 0.46/0.67         (~ (r1_xboole_0 @ (k1_tarski @ X0) @ X1)
% 0.46/0.67          | ~ (r1_tarski @ (k1_tarski @ X0) @ X1)
% 0.46/0.67          | ((k1_tarski @ X0) = (k1_xboole_0)))),
% 0.46/0.67      inference('sup-', [status(thm)], ['15', '16'])).
% 0.46/0.67  thf(t20_zfmisc_1, axiom,
% 0.46/0.67    (![A:$i,B:$i]:
% 0.46/0.67     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.46/0.67         ( k1_tarski @ A ) ) <=>
% 0.46/0.67       ( ( A ) != ( B ) ) ))).
% 0.46/0.67  thf('18', plain,
% 0.46/0.67      (![X26 : $i, X27 : $i]:
% 0.46/0.67         (((X27) != (X26))
% 0.46/0.67          | ((k4_xboole_0 @ (k1_tarski @ X27) @ (k1_tarski @ X26))
% 0.46/0.67              != (k1_tarski @ X27)))),
% 0.46/0.67      inference('cnf', [status(esa)], [t20_zfmisc_1])).
% 0.46/0.67  thf('19', plain,
% 0.46/0.67      (![X26 : $i]:
% 0.46/0.67         ((k4_xboole_0 @ (k1_tarski @ X26) @ (k1_tarski @ X26))
% 0.46/0.67           != (k1_tarski @ X26))),
% 0.46/0.67      inference('simplify', [status(thm)], ['18'])).
% 0.46/0.67  thf(t3_boole, axiom,
% 0.46/0.67    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.46/0.67  thf('20', plain, (![X4 : $i]: ((k4_xboole_0 @ X4 @ k1_xboole_0) = (X4))),
% 0.46/0.67      inference('cnf', [status(esa)], [t3_boole])).
% 0.46/0.67  thf(t48_xboole_1, axiom,
% 0.46/0.67    (![A:$i,B:$i]:
% 0.46/0.67     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.46/0.67  thf('21', plain,
% 0.46/0.67      (![X5 : $i, X6 : $i]:
% 0.46/0.67         ((k4_xboole_0 @ X5 @ (k4_xboole_0 @ X5 @ X6))
% 0.46/0.67           = (k3_xboole_0 @ X5 @ X6))),
% 0.46/0.67      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.46/0.67  thf('22', plain,
% 0.46/0.67      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.46/0.67      inference('sup+', [status(thm)], ['20', '21'])).
% 0.46/0.67  thf(t2_boole, axiom,
% 0.46/0.67    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.46/0.67  thf('23', plain,
% 0.46/0.67      (![X3 : $i]: ((k3_xboole_0 @ X3 @ k1_xboole_0) = (k1_xboole_0))),
% 0.46/0.67      inference('cnf', [status(esa)], [t2_boole])).
% 0.46/0.67  thf('24', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.46/0.67      inference('demod', [status(thm)], ['22', '23'])).
% 0.46/0.67  thf('25', plain, (![X26 : $i]: ((k1_xboole_0) != (k1_tarski @ X26))),
% 0.46/0.67      inference('demod', [status(thm)], ['19', '24'])).
% 0.46/0.67  thf('26', plain,
% 0.46/0.67      (![X0 : $i, X1 : $i]:
% 0.46/0.67         (~ (r1_tarski @ (k1_tarski @ X0) @ X1)
% 0.46/0.67          | ~ (r1_xboole_0 @ (k1_tarski @ X0) @ X1))),
% 0.46/0.67      inference('clc', [status(thm)], ['17', '25'])).
% 0.46/0.67  thf('27', plain,
% 0.46/0.67      (![X0 : $i]: ~ (r1_xboole_0 @ (k1_tarski @ X0) @ (k1_zfmisc_1 @ X0))),
% 0.46/0.67      inference('sup-', [status(thm)], ['13', '26'])).
% 0.46/0.67  thf('28', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.46/0.67      inference('sup-', [status(thm)], ['12', '27'])).
% 0.46/0.67  thf(t1_subset, axiom,
% 0.46/0.67    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 0.46/0.67  thf('29', plain,
% 0.46/0.67      (![X37 : $i, X38 : $i]:
% 0.46/0.67         ((m1_subset_1 @ X37 @ X38) | ~ (r2_hidden @ X37 @ X38))),
% 0.46/0.67      inference('cnf', [status(esa)], [t1_subset])).
% 0.46/0.67  thf('30', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.46/0.67      inference('sup-', [status(thm)], ['28', '29'])).
% 0.46/0.67  thf(d1_tops_1, axiom,
% 0.46/0.67    (![A:$i]:
% 0.46/0.67     ( ( l1_pre_topc @ A ) =>
% 0.46/0.67       ( ![B:$i]:
% 0.46/0.67         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.46/0.67           ( ( k1_tops_1 @ A @ B ) =
% 0.46/0.67             ( k3_subset_1 @
% 0.46/0.67               ( u1_struct_0 @ A ) @ 
% 0.46/0.67               ( k2_pre_topc @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) ))).
% 0.46/0.67  thf('31', plain,
% 0.46/0.67      (![X50 : $i, X51 : $i]:
% 0.46/0.67         (~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ (u1_struct_0 @ X51)))
% 0.46/0.67          | ((k1_tops_1 @ X51 @ X50)
% 0.46/0.67              = (k3_subset_1 @ (u1_struct_0 @ X51) @ 
% 0.46/0.67                 (k2_pre_topc @ X51 @ (k3_subset_1 @ (u1_struct_0 @ X51) @ X50))))
% 0.46/0.67          | ~ (l1_pre_topc @ X51))),
% 0.46/0.67      inference('cnf', [status(esa)], [d1_tops_1])).
% 0.46/0.67  thf('32', plain,
% 0.46/0.67      (![X0 : $i]:
% 0.46/0.67         (~ (l1_pre_topc @ X0)
% 0.46/0.67          | ((k1_tops_1 @ X0 @ (u1_struct_0 @ X0))
% 0.46/0.67              = (k3_subset_1 @ (u1_struct_0 @ X0) @ 
% 0.46/0.67                 (k2_pre_topc @ X0 @ 
% 0.46/0.67                  (k3_subset_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0))))))),
% 0.46/0.67      inference('sup-', [status(thm)], ['30', '31'])).
% 0.46/0.67  thf('33', plain,
% 0.46/0.67      (![X36 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X36))),
% 0.46/0.67      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.46/0.67  thf(involutiveness_k3_subset_1, axiom,
% 0.46/0.67    (![A:$i,B:$i]:
% 0.46/0.67     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.46/0.67       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 0.46/0.67  thf('34', plain,
% 0.46/0.67      (![X34 : $i, X35 : $i]:
% 0.46/0.67         (((k3_subset_1 @ X35 @ (k3_subset_1 @ X35 @ X34)) = (X34))
% 0.46/0.67          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ X35)))),
% 0.46/0.67      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.46/0.67  thf('35', plain,
% 0.46/0.67      (![X0 : $i]:
% 0.46/0.67         ((k3_subset_1 @ X0 @ (k3_subset_1 @ X0 @ k1_xboole_0)) = (k1_xboole_0))),
% 0.46/0.67      inference('sup-', [status(thm)], ['33', '34'])).
% 0.46/0.67  thf('36', plain,
% 0.46/0.67      (![X36 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X36))),
% 0.46/0.67      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.46/0.67  thf(d5_subset_1, axiom,
% 0.46/0.67    (![A:$i,B:$i]:
% 0.46/0.67     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.46/0.67       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.46/0.67  thf('37', plain,
% 0.46/0.67      (![X32 : $i, X33 : $i]:
% 0.46/0.67         (((k3_subset_1 @ X32 @ X33) = (k4_xboole_0 @ X32 @ X33))
% 0.46/0.67          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ X32)))),
% 0.46/0.67      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.46/0.67  thf('38', plain,
% 0.46/0.67      (![X0 : $i]:
% 0.46/0.67         ((k3_subset_1 @ X0 @ k1_xboole_0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 0.46/0.67      inference('sup-', [status(thm)], ['36', '37'])).
% 0.46/0.67  thf('39', plain, (![X4 : $i]: ((k4_xboole_0 @ X4 @ k1_xboole_0) = (X4))),
% 0.46/0.67      inference('cnf', [status(esa)], [t3_boole])).
% 0.46/0.67  thf('40', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ k1_xboole_0) = (X0))),
% 0.46/0.67      inference('sup+', [status(thm)], ['38', '39'])).
% 0.46/0.67  thf('41', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k1_xboole_0))),
% 0.46/0.67      inference('demod', [status(thm)], ['35', '40'])).
% 0.46/0.67  thf('42', plain,
% 0.46/0.67      (![X0 : $i]:
% 0.46/0.67         (~ (l1_pre_topc @ X0)
% 0.46/0.67          | ((k1_tops_1 @ X0 @ (u1_struct_0 @ X0))
% 0.46/0.67              = (k3_subset_1 @ (u1_struct_0 @ X0) @ 
% 0.46/0.67                 (k2_pre_topc @ X0 @ k1_xboole_0))))),
% 0.46/0.67      inference('demod', [status(thm)], ['32', '41'])).
% 0.46/0.67  thf('43', plain,
% 0.46/0.67      (![X0 : $i]:
% 0.46/0.67         (((k1_tops_1 @ X0 @ (u1_struct_0 @ X0))
% 0.46/0.67            = (k3_subset_1 @ (u1_struct_0 @ X0) @ k1_xboole_0))
% 0.46/0.67          | ~ (l1_pre_topc @ X0)
% 0.46/0.67          | ~ (v2_pre_topc @ X0)
% 0.46/0.67          | ~ (l1_pre_topc @ X0))),
% 0.46/0.67      inference('sup+', [status(thm)], ['11', '42'])).
% 0.46/0.67  thf('44', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ k1_xboole_0) = (X0))),
% 0.46/0.67      inference('sup+', [status(thm)], ['38', '39'])).
% 0.46/0.67  thf('45', plain,
% 0.46/0.67      (![X0 : $i]:
% 0.46/0.67         (((k1_tops_1 @ X0 @ (u1_struct_0 @ X0)) = (u1_struct_0 @ X0))
% 0.46/0.67          | ~ (l1_pre_topc @ X0)
% 0.46/0.67          | ~ (v2_pre_topc @ X0)
% 0.46/0.67          | ~ (l1_pre_topc @ X0))),
% 0.46/0.67      inference('demod', [status(thm)], ['43', '44'])).
% 0.46/0.67  thf('46', plain,
% 0.46/0.67      (![X0 : $i]:
% 0.46/0.67         (~ (v2_pre_topc @ X0)
% 0.46/0.67          | ~ (l1_pre_topc @ X0)
% 0.46/0.67          | ((k1_tops_1 @ X0 @ (u1_struct_0 @ X0)) = (u1_struct_0 @ X0)))),
% 0.46/0.67      inference('simplify', [status(thm)], ['45'])).
% 0.46/0.67  thf('47', plain,
% 0.46/0.67      (![X0 : $i]:
% 0.46/0.67         (((k1_tops_1 @ X0 @ (k2_struct_0 @ X0)) = (u1_struct_0 @ X0))
% 0.46/0.67          | ~ (l1_struct_0 @ X0)
% 0.46/0.67          | ~ (l1_pre_topc @ X0)
% 0.46/0.67          | ~ (v2_pre_topc @ X0))),
% 0.46/0.67      inference('sup+', [status(thm)], ['1', '46'])).
% 0.46/0.67  thf(t43_tops_1, conjecture,
% 0.46/0.67    (![A:$i]:
% 0.46/0.67     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.46/0.67       ( ( k1_tops_1 @ A @ ( k2_struct_0 @ A ) ) = ( k2_struct_0 @ A ) ) ))).
% 0.46/0.67  thf(zf_stmt_0, negated_conjecture,
% 0.46/0.67    (~( ![A:$i]:
% 0.46/0.67        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.46/0.67          ( ( k1_tops_1 @ A @ ( k2_struct_0 @ A ) ) = ( k2_struct_0 @ A ) ) ) )),
% 0.46/0.67    inference('cnf.neg', [status(esa)], [t43_tops_1])).
% 0.46/0.67  thf('48', plain,
% 0.46/0.67      (((k1_tops_1 @ sk_A @ (k2_struct_0 @ sk_A)) != (k2_struct_0 @ sk_A))),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.67  thf('49', plain,
% 0.46/0.67      ((((u1_struct_0 @ sk_A) != (k2_struct_0 @ sk_A))
% 0.46/0.67        | ~ (v2_pre_topc @ sk_A)
% 0.46/0.67        | ~ (l1_pre_topc @ sk_A)
% 0.46/0.67        | ~ (l1_struct_0 @ sk_A))),
% 0.46/0.67      inference('sup-', [status(thm)], ['47', '48'])).
% 0.46/0.67  thf('50', plain, ((v2_pre_topc @ sk_A)),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.67  thf('51', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.67  thf('52', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.67  thf(dt_l1_pre_topc, axiom,
% 0.46/0.67    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.46/0.67  thf('53', plain,
% 0.46/0.67      (![X47 : $i]: ((l1_struct_0 @ X47) | ~ (l1_pre_topc @ X47))),
% 0.46/0.67      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.46/0.67  thf('54', plain, ((l1_struct_0 @ sk_A)),
% 0.46/0.67      inference('sup-', [status(thm)], ['52', '53'])).
% 0.46/0.67  thf('55', plain, (((u1_struct_0 @ sk_A) != (k2_struct_0 @ sk_A))),
% 0.46/0.67      inference('demod', [status(thm)], ['49', '50', '51', '54'])).
% 0.46/0.67  thf('56', plain,
% 0.46/0.67      ((((k2_struct_0 @ sk_A) != (k2_struct_0 @ sk_A)) | ~ (l1_struct_0 @ sk_A))),
% 0.46/0.67      inference('sup-', [status(thm)], ['0', '55'])).
% 0.46/0.67  thf('57', plain, ((l1_struct_0 @ sk_A)),
% 0.46/0.67      inference('sup-', [status(thm)], ['52', '53'])).
% 0.46/0.67  thf('58', plain, (((k2_struct_0 @ sk_A) != (k2_struct_0 @ sk_A))),
% 0.46/0.67      inference('demod', [status(thm)], ['56', '57'])).
% 0.46/0.67  thf('59', plain, ($false), inference('simplify', [status(thm)], ['58'])).
% 0.46/0.67  
% 0.46/0.67  % SZS output end Refutation
% 0.46/0.67  
% 0.46/0.68  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
