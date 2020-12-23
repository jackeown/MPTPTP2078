%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.oSjKY1tXK2

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:02:49 EST 2020

% Result     : Theorem 0.69s
% Output     : Refutation 0.69s
% Verified   : 
% Statistics : Number of formulae       :  108 ( 140 expanded)
%              Number of leaves         :   41 (  58 expanded)
%              Depth                    :   23
%              Number of atoms          :  684 ( 912 expanded)
%              Number of equality atoms :   52 (  75 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('0',plain,(
    ! [X54: $i] :
      ( ( ( k2_struct_0 @ X54 )
        = ( u1_struct_0 @ X54 ) )
      | ~ ( l1_struct_0 @ X54 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('1',plain,(
    ! [X54: $i] :
      ( ( ( k2_struct_0 @ X54 )
        = ( u1_struct_0 @ X54 ) )
      | ~ ( l1_struct_0 @ X54 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('2',plain,(
    ! [X48: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X48 ) ) ),
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
    ! [X52: $i,X53: $i] :
      ( ~ ( m1_subset_1 @ X52 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X53 ) ) )
      | ( v4_pre_topc @ X52 @ X53 )
      | ~ ( v1_xboole_0 @ X52 )
      | ~ ( l1_pre_topc @ X53 )
      | ~ ( v2_pre_topc @ X53 ) ) ),
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
    ! [X48: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X48 ) ) ),
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
    ! [X57: $i,X58: $i] :
      ( ~ ( m1_subset_1 @ X57 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X58 ) ) )
      | ~ ( v4_pre_topc @ X57 @ X58 )
      | ( ( k2_pre_topc @ X58 @ X57 )
        = X57 )
      | ~ ( l1_pre_topc @ X58 ) ) ),
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

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('12',plain,(
    ! [X19: $i] :
      ( r1_xboole_0 @ X19 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf(t88_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B )
        = A ) ) )).

thf('13',plain,(
    ! [X26: $i,X27: $i] :
      ( ( ( k4_xboole_0 @ ( k2_xboole_0 @ X26 @ X27 ) @ X27 )
        = X26 )
      | ~ ( r1_xboole_0 @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t88_xboole_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ k1_xboole_0 ) @ k1_xboole_0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('15',plain,(
    ! [X14: $i] :
      ( ( k2_xboole_0 @ X14 @ k1_xboole_0 )
      = X14 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['14','15'])).

thf(t82_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ B @ A ) ) )).

thf('17',plain,(
    ! [X24: $i,X25: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X24 @ X25 ) @ ( k4_xboole_0 @ X25 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t82_xboole_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ k1_xboole_0 @ X0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf(t4_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf('19',plain,(
    ! [X18: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X18 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t4_boole])).

thf('20',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X26: $i,X27: $i] :
      ( ( ( k4_xboole_0 @ ( k2_xboole_0 @ X26 @ X27 ) @ X27 )
        = X26 )
      | ~ ( r1_xboole_0 @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t88_xboole_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ k1_xboole_0 @ X0 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('24',plain,(
    ! [X14: $i] :
      ( ( k2_xboole_0 @ X14 @ k1_xboole_0 )
      = X14 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['22','25'])).

thf(l35_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B )
        = k1_xboole_0 )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('27',plain,(
    ! [X28: $i,X29: $i] :
      ( ( r2_hidden @ X28 @ X29 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X28 ) @ X29 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l35_zfmisc_1])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf(t80_zfmisc_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ ( k1_tarski @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('30',plain,(
    ! [X36: $i] :
      ( r1_tarski @ ( k1_tarski @ X36 ) @ ( k1_zfmisc_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t80_zfmisc_1])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('31',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ( r2_hidden @ X2 @ X4 )
      | ~ ( r1_tarski @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ ( k1_zfmisc_1 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['29','32'])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('34',plain,(
    ! [X37: $i,X38: $i] :
      ( ~ ( r2_hidden @ X37 @ X38 )
      | ( m1_subset_1 @ X37 @ X38 )
      | ( v1_xboole_0 @ X38 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('36',plain,(
    ! [X42: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X42 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('37',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(clc,[status(thm)],['35','36'])).

thf(d1_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k1_tops_1 @ A @ B )
            = ( k3_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) )).

thf('38',plain,(
    ! [X59: $i,X60: $i] :
      ( ~ ( m1_subset_1 @ X59 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X60 ) ) )
      | ( ( k1_tops_1 @ X60 @ X59 )
        = ( k3_subset_1 @ ( u1_struct_0 @ X60 ) @ ( k2_pre_topc @ X60 @ ( k3_subset_1 @ ( u1_struct_0 @ X60 ) @ X59 ) ) ) )
      | ~ ( l1_pre_topc @ X60 ) ) ),
    inference(cnf,[status(esa)],[d1_tops_1])).

thf('39',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( k1_tops_1 @ X0 @ ( u1_struct_0 @ X0 ) )
        = ( k3_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k2_pre_topc @ X0 @ ( k3_subset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X48: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X48 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('41',plain,(
    ! [X43: $i,X44: $i] :
      ( ( ( k3_subset_1 @ X44 @ ( k3_subset_1 @ X44 @ X43 ) )
        = X43 )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ X44 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ ( k3_subset_1 @ X0 @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X48: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X48 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('44',plain,(
    ! [X40: $i,X41: $i] :
      ( ( ( k3_subset_1 @ X40 @ X41 )
        = ( k4_xboole_0 @ X40 @ X41 ) )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ X40 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['42','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( k1_tops_1 @ X0 @ ( u1_struct_0 @ X0 ) )
        = ( k3_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k2_pre_topc @ X0 @ k1_xboole_0 ) ) ) ) ),
    inference(demod,[status(thm)],['39','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( ( k1_tops_1 @ X0 @ ( u1_struct_0 @ X0 ) )
        = ( k3_subset_1 @ ( u1_struct_0 @ X0 ) @ k1_xboole_0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup+',[status(thm)],['11','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( ( k1_tops_1 @ X0 @ ( u1_struct_0 @ X0 ) )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( k1_tops_1 @ X0 @ ( u1_struct_0 @ X0 ) )
        = ( u1_struct_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( ( k1_tops_1 @ X0 @ ( k2_struct_0 @ X0 ) )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( ( k1_tops_1 @ X0 @ ( k2_struct_0 @ X0 ) )
        = ( k2_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['0','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( ( k1_tops_1 @ X0 @ ( k2_struct_0 @ X0 ) )
        = ( k2_struct_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['55'])).

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

thf('57',plain,(
    ( k1_tops_1 @ sk_A @ ( k2_struct_0 @ sk_A ) )
 != ( k2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,
    ( ( ( k2_struct_0 @ sk_A )
     != ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('60',plain,(
    ! [X55: $i] :
      ( ( l1_struct_0 @ X55 )
      | ~ ( l1_pre_topc @ X55 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('61',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    ( k2_struct_0 @ sk_A )
 != ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['58','61','62','63'])).

thf('65',plain,(
    $false ),
    inference(simplify,[status(thm)],['64'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.oSjKY1tXK2
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:13:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.69/0.91  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.69/0.91  % Solved by: fo/fo7.sh
% 0.69/0.91  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.69/0.91  % done 1499 iterations in 0.457s
% 0.69/0.91  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.69/0.91  % SZS output start Refutation
% 0.69/0.91  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.69/0.91  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.69/0.91  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.69/0.91  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.69/0.91  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.69/0.91  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.69/0.91  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.69/0.91  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.69/0.91  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.69/0.91  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.69/0.91  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.69/0.91  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.69/0.91  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.69/0.91  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.69/0.91  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.69/0.91  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.69/0.91  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.69/0.91  thf(sk_A_type, type, sk_A: $i).
% 0.69/0.91  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.69/0.91  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.69/0.91  thf(d3_struct_0, axiom,
% 0.69/0.91    (![A:$i]:
% 0.69/0.91     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.69/0.91  thf('0', plain,
% 0.69/0.91      (![X54 : $i]:
% 0.69/0.91         (((k2_struct_0 @ X54) = (u1_struct_0 @ X54)) | ~ (l1_struct_0 @ X54))),
% 0.69/0.91      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.69/0.91  thf('1', plain,
% 0.69/0.91      (![X54 : $i]:
% 0.69/0.91         (((k2_struct_0 @ X54) = (u1_struct_0 @ X54)) | ~ (l1_struct_0 @ X54))),
% 0.69/0.91      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.69/0.91  thf(t4_subset_1, axiom,
% 0.69/0.91    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.69/0.91  thf('2', plain,
% 0.69/0.91      (![X48 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X48))),
% 0.69/0.91      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.69/0.91  thf(cc2_pre_topc, axiom,
% 0.69/0.91    (![A:$i]:
% 0.69/0.91     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.69/0.91       ( ![B:$i]:
% 0.69/0.91         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.69/0.91           ( ( v1_xboole_0 @ B ) => ( v4_pre_topc @ B @ A ) ) ) ) ))).
% 0.69/0.91  thf('3', plain,
% 0.69/0.91      (![X52 : $i, X53 : $i]:
% 0.69/0.91         (~ (m1_subset_1 @ X52 @ (k1_zfmisc_1 @ (u1_struct_0 @ X53)))
% 0.69/0.91          | (v4_pre_topc @ X52 @ X53)
% 0.69/0.91          | ~ (v1_xboole_0 @ X52)
% 0.69/0.91          | ~ (l1_pre_topc @ X53)
% 0.69/0.91          | ~ (v2_pre_topc @ X53))),
% 0.69/0.91      inference('cnf', [status(esa)], [cc2_pre_topc])).
% 0.69/0.91  thf('4', plain,
% 0.69/0.91      (![X0 : $i]:
% 0.69/0.91         (~ (v2_pre_topc @ X0)
% 0.69/0.91          | ~ (l1_pre_topc @ X0)
% 0.69/0.91          | ~ (v1_xboole_0 @ k1_xboole_0)
% 0.69/0.91          | (v4_pre_topc @ k1_xboole_0 @ X0))),
% 0.69/0.91      inference('sup-', [status(thm)], ['2', '3'])).
% 0.69/0.91  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.69/0.91  thf('5', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.69/0.91      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.69/0.91  thf('6', plain,
% 0.69/0.91      (![X0 : $i]:
% 0.69/0.91         (~ (v2_pre_topc @ X0)
% 0.69/0.91          | ~ (l1_pre_topc @ X0)
% 0.69/0.91          | (v4_pre_topc @ k1_xboole_0 @ X0))),
% 0.69/0.91      inference('demod', [status(thm)], ['4', '5'])).
% 0.69/0.91  thf('7', plain,
% 0.69/0.91      (![X48 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X48))),
% 0.69/0.91      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.69/0.91  thf(t52_pre_topc, axiom,
% 0.69/0.91    (![A:$i]:
% 0.69/0.91     ( ( l1_pre_topc @ A ) =>
% 0.69/0.91       ( ![B:$i]:
% 0.69/0.91         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.69/0.91           ( ( ( v4_pre_topc @ B @ A ) => ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) & 
% 0.69/0.91             ( ( ( v2_pre_topc @ A ) & ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) =>
% 0.69/0.91               ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 0.69/0.91  thf('8', plain,
% 0.69/0.91      (![X57 : $i, X58 : $i]:
% 0.69/0.91         (~ (m1_subset_1 @ X57 @ (k1_zfmisc_1 @ (u1_struct_0 @ X58)))
% 0.69/0.91          | ~ (v4_pre_topc @ X57 @ X58)
% 0.69/0.91          | ((k2_pre_topc @ X58 @ X57) = (X57))
% 0.69/0.91          | ~ (l1_pre_topc @ X58))),
% 0.69/0.91      inference('cnf', [status(esa)], [t52_pre_topc])).
% 0.69/0.91  thf('9', plain,
% 0.69/0.91      (![X0 : $i]:
% 0.69/0.91         (~ (l1_pre_topc @ X0)
% 0.69/0.91          | ((k2_pre_topc @ X0 @ k1_xboole_0) = (k1_xboole_0))
% 0.69/0.91          | ~ (v4_pre_topc @ k1_xboole_0 @ X0))),
% 0.69/0.91      inference('sup-', [status(thm)], ['7', '8'])).
% 0.69/0.91  thf('10', plain,
% 0.69/0.91      (![X0 : $i]:
% 0.69/0.91         (~ (l1_pre_topc @ X0)
% 0.69/0.91          | ~ (v2_pre_topc @ X0)
% 0.69/0.91          | ((k2_pre_topc @ X0 @ k1_xboole_0) = (k1_xboole_0))
% 0.69/0.91          | ~ (l1_pre_topc @ X0))),
% 0.69/0.91      inference('sup-', [status(thm)], ['6', '9'])).
% 0.69/0.91  thf('11', plain,
% 0.69/0.91      (![X0 : $i]:
% 0.69/0.91         (((k2_pre_topc @ X0 @ k1_xboole_0) = (k1_xboole_0))
% 0.69/0.91          | ~ (v2_pre_topc @ X0)
% 0.69/0.91          | ~ (l1_pre_topc @ X0))),
% 0.69/0.91      inference('simplify', [status(thm)], ['10'])).
% 0.69/0.91  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.69/0.91  thf('12', plain, (![X19 : $i]: (r1_xboole_0 @ X19 @ k1_xboole_0)),
% 0.69/0.91      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.69/0.91  thf(t88_xboole_1, axiom,
% 0.69/0.91    (![A:$i,B:$i]:
% 0.69/0.91     ( ( r1_xboole_0 @ A @ B ) =>
% 0.69/0.91       ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B ) = ( A ) ) ))).
% 0.69/0.91  thf('13', plain,
% 0.69/0.91      (![X26 : $i, X27 : $i]:
% 0.69/0.91         (((k4_xboole_0 @ (k2_xboole_0 @ X26 @ X27) @ X27) = (X26))
% 0.69/0.91          | ~ (r1_xboole_0 @ X26 @ X27))),
% 0.69/0.91      inference('cnf', [status(esa)], [t88_xboole_1])).
% 0.69/0.91  thf('14', plain,
% 0.69/0.91      (![X0 : $i]:
% 0.69/0.91         ((k4_xboole_0 @ (k2_xboole_0 @ X0 @ k1_xboole_0) @ k1_xboole_0) = (X0))),
% 0.69/0.91      inference('sup-', [status(thm)], ['12', '13'])).
% 0.69/0.91  thf(t1_boole, axiom,
% 0.69/0.91    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.69/0.91  thf('15', plain, (![X14 : $i]: ((k2_xboole_0 @ X14 @ k1_xboole_0) = (X14))),
% 0.69/0.91      inference('cnf', [status(esa)], [t1_boole])).
% 0.69/0.91  thf('16', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.69/0.91      inference('demod', [status(thm)], ['14', '15'])).
% 0.69/0.91  thf(t82_xboole_1, axiom,
% 0.69/0.91    (![A:$i,B:$i]:
% 0.69/0.91     ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ B @ A ) ))).
% 0.69/0.91  thf('17', plain,
% 0.69/0.91      (![X24 : $i, X25 : $i]:
% 0.69/0.91         (r1_xboole_0 @ (k4_xboole_0 @ X24 @ X25) @ (k4_xboole_0 @ X25 @ X24))),
% 0.69/0.91      inference('cnf', [status(esa)], [t82_xboole_1])).
% 0.69/0.91  thf('18', plain,
% 0.69/0.91      (![X0 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ k1_xboole_0 @ X0) @ X0)),
% 0.69/0.91      inference('sup+', [status(thm)], ['16', '17'])).
% 0.69/0.91  thf(t4_boole, axiom,
% 0.69/0.91    (![A:$i]: ( ( k4_xboole_0 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 0.69/0.91  thf('19', plain,
% 0.69/0.91      (![X18 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X18) = (k1_xboole_0))),
% 0.69/0.91      inference('cnf', [status(esa)], [t4_boole])).
% 0.69/0.91  thf('20', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.69/0.91      inference('demod', [status(thm)], ['18', '19'])).
% 0.69/0.91  thf('21', plain,
% 0.69/0.91      (![X26 : $i, X27 : $i]:
% 0.69/0.91         (((k4_xboole_0 @ (k2_xboole_0 @ X26 @ X27) @ X27) = (X26))
% 0.69/0.91          | ~ (r1_xboole_0 @ X26 @ X27))),
% 0.69/0.91      inference('cnf', [status(esa)], [t88_xboole_1])).
% 0.69/0.91  thf('22', plain,
% 0.69/0.91      (![X0 : $i]:
% 0.69/0.91         ((k4_xboole_0 @ (k2_xboole_0 @ k1_xboole_0 @ X0) @ X0) = (k1_xboole_0))),
% 0.69/0.91      inference('sup-', [status(thm)], ['20', '21'])).
% 0.69/0.91  thf(commutativity_k2_xboole_0, axiom,
% 0.69/0.91    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.69/0.91  thf('23', plain,
% 0.69/0.91      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.69/0.91      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.69/0.91  thf('24', plain, (![X14 : $i]: ((k2_xboole_0 @ X14 @ k1_xboole_0) = (X14))),
% 0.69/0.91      inference('cnf', [status(esa)], [t1_boole])).
% 0.69/0.91  thf('25', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.69/0.91      inference('sup+', [status(thm)], ['23', '24'])).
% 0.69/0.91  thf('26', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.69/0.91      inference('demod', [status(thm)], ['22', '25'])).
% 0.69/0.91  thf(l35_zfmisc_1, axiom,
% 0.69/0.91    (![A:$i,B:$i]:
% 0.69/0.91     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_xboole_0 ) ) <=>
% 0.69/0.91       ( r2_hidden @ A @ B ) ))).
% 0.69/0.91  thf('27', plain,
% 0.69/0.91      (![X28 : $i, X29 : $i]:
% 0.69/0.91         ((r2_hidden @ X28 @ X29)
% 0.69/0.91          | ((k4_xboole_0 @ (k1_tarski @ X28) @ X29) != (k1_xboole_0)))),
% 0.69/0.91      inference('cnf', [status(esa)], [l35_zfmisc_1])).
% 0.69/0.91  thf('28', plain,
% 0.69/0.91      (![X0 : $i]:
% 0.69/0.91         (((k1_xboole_0) != (k1_xboole_0))
% 0.69/0.91          | (r2_hidden @ X0 @ (k1_tarski @ X0)))),
% 0.69/0.91      inference('sup-', [status(thm)], ['26', '27'])).
% 0.69/0.91  thf('29', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.69/0.91      inference('simplify', [status(thm)], ['28'])).
% 0.69/0.91  thf(t80_zfmisc_1, axiom,
% 0.69/0.91    (![A:$i]: ( r1_tarski @ ( k1_tarski @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.69/0.91  thf('30', plain,
% 0.69/0.91      (![X36 : $i]: (r1_tarski @ (k1_tarski @ X36) @ (k1_zfmisc_1 @ X36))),
% 0.69/0.91      inference('cnf', [status(esa)], [t80_zfmisc_1])).
% 0.69/0.91  thf(d3_tarski, axiom,
% 0.69/0.91    (![A:$i,B:$i]:
% 0.69/0.91     ( ( r1_tarski @ A @ B ) <=>
% 0.69/0.91       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.69/0.91  thf('31', plain,
% 0.69/0.91      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.69/0.91         (~ (r2_hidden @ X2 @ X3)
% 0.69/0.91          | (r2_hidden @ X2 @ X4)
% 0.69/0.91          | ~ (r1_tarski @ X3 @ X4))),
% 0.69/0.91      inference('cnf', [status(esa)], [d3_tarski])).
% 0.69/0.91  thf('32', plain,
% 0.69/0.91      (![X0 : $i, X1 : $i]:
% 0.69/0.91         ((r2_hidden @ X1 @ (k1_zfmisc_1 @ X0))
% 0.69/0.91          | ~ (r2_hidden @ X1 @ (k1_tarski @ X0)))),
% 0.69/0.91      inference('sup-', [status(thm)], ['30', '31'])).
% 0.69/0.91  thf('33', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.69/0.91      inference('sup-', [status(thm)], ['29', '32'])).
% 0.69/0.91  thf(d2_subset_1, axiom,
% 0.69/0.91    (![A:$i,B:$i]:
% 0.69/0.91     ( ( ( v1_xboole_0 @ A ) =>
% 0.69/0.91         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.69/0.91       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.69/0.91         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.69/0.91  thf('34', plain,
% 0.69/0.91      (![X37 : $i, X38 : $i]:
% 0.69/0.91         (~ (r2_hidden @ X37 @ X38)
% 0.69/0.91          | (m1_subset_1 @ X37 @ X38)
% 0.69/0.91          | (v1_xboole_0 @ X38))),
% 0.69/0.91      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.69/0.91  thf('35', plain,
% 0.69/0.91      (![X0 : $i]:
% 0.69/0.91         ((v1_xboole_0 @ (k1_zfmisc_1 @ X0))
% 0.69/0.91          | (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0)))),
% 0.69/0.91      inference('sup-', [status(thm)], ['33', '34'])).
% 0.69/0.91  thf(fc1_subset_1, axiom,
% 0.69/0.91    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.69/0.91  thf('36', plain, (![X42 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X42))),
% 0.69/0.91      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.69/0.91  thf('37', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.69/0.91      inference('clc', [status(thm)], ['35', '36'])).
% 0.69/0.91  thf(d1_tops_1, axiom,
% 0.69/0.91    (![A:$i]:
% 0.69/0.91     ( ( l1_pre_topc @ A ) =>
% 0.69/0.91       ( ![B:$i]:
% 0.69/0.91         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.69/0.91           ( ( k1_tops_1 @ A @ B ) =
% 0.69/0.91             ( k3_subset_1 @
% 0.69/0.91               ( u1_struct_0 @ A ) @ 
% 0.69/0.91               ( k2_pre_topc @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) ))).
% 0.69/0.91  thf('38', plain,
% 0.69/0.91      (![X59 : $i, X60 : $i]:
% 0.69/0.91         (~ (m1_subset_1 @ X59 @ (k1_zfmisc_1 @ (u1_struct_0 @ X60)))
% 0.69/0.91          | ((k1_tops_1 @ X60 @ X59)
% 0.69/0.91              = (k3_subset_1 @ (u1_struct_0 @ X60) @ 
% 0.69/0.91                 (k2_pre_topc @ X60 @ (k3_subset_1 @ (u1_struct_0 @ X60) @ X59))))
% 0.69/0.91          | ~ (l1_pre_topc @ X60))),
% 0.69/0.91      inference('cnf', [status(esa)], [d1_tops_1])).
% 0.69/0.91  thf('39', plain,
% 0.69/0.91      (![X0 : $i]:
% 0.69/0.91         (~ (l1_pre_topc @ X0)
% 0.69/0.91          | ((k1_tops_1 @ X0 @ (u1_struct_0 @ X0))
% 0.69/0.91              = (k3_subset_1 @ (u1_struct_0 @ X0) @ 
% 0.69/0.91                 (k2_pre_topc @ X0 @ 
% 0.69/0.91                  (k3_subset_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0))))))),
% 0.69/0.91      inference('sup-', [status(thm)], ['37', '38'])).
% 0.69/0.91  thf('40', plain,
% 0.69/0.91      (![X48 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X48))),
% 0.69/0.91      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.69/0.91  thf(involutiveness_k3_subset_1, axiom,
% 0.69/0.91    (![A:$i,B:$i]:
% 0.69/0.91     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.69/0.91       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 0.69/0.91  thf('41', plain,
% 0.69/0.91      (![X43 : $i, X44 : $i]:
% 0.69/0.91         (((k3_subset_1 @ X44 @ (k3_subset_1 @ X44 @ X43)) = (X43))
% 0.69/0.91          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ X44)))),
% 0.69/0.91      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.69/0.91  thf('42', plain,
% 0.69/0.91      (![X0 : $i]:
% 0.69/0.91         ((k3_subset_1 @ X0 @ (k3_subset_1 @ X0 @ k1_xboole_0)) = (k1_xboole_0))),
% 0.69/0.91      inference('sup-', [status(thm)], ['40', '41'])).
% 0.69/0.91  thf('43', plain,
% 0.69/0.91      (![X48 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X48))),
% 0.69/0.91      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.69/0.91  thf(d5_subset_1, axiom,
% 0.69/0.91    (![A:$i,B:$i]:
% 0.69/0.91     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.69/0.91       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.69/0.91  thf('44', plain,
% 0.69/0.91      (![X40 : $i, X41 : $i]:
% 0.69/0.91         (((k3_subset_1 @ X40 @ X41) = (k4_xboole_0 @ X40 @ X41))
% 0.69/0.91          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ X40)))),
% 0.69/0.91      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.69/0.91  thf('45', plain,
% 0.69/0.91      (![X0 : $i]:
% 0.69/0.91         ((k3_subset_1 @ X0 @ k1_xboole_0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 0.69/0.91      inference('sup-', [status(thm)], ['43', '44'])).
% 0.69/0.91  thf('46', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.69/0.91      inference('demod', [status(thm)], ['14', '15'])).
% 0.69/0.91  thf('47', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ k1_xboole_0) = (X0))),
% 0.69/0.91      inference('sup+', [status(thm)], ['45', '46'])).
% 0.69/0.91  thf('48', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k1_xboole_0))),
% 0.69/0.91      inference('demod', [status(thm)], ['42', '47'])).
% 0.69/0.91  thf('49', plain,
% 0.69/0.91      (![X0 : $i]:
% 0.69/0.91         (~ (l1_pre_topc @ X0)
% 0.69/0.91          | ((k1_tops_1 @ X0 @ (u1_struct_0 @ X0))
% 0.69/0.91              = (k3_subset_1 @ (u1_struct_0 @ X0) @ 
% 0.69/0.91                 (k2_pre_topc @ X0 @ k1_xboole_0))))),
% 0.69/0.91      inference('demod', [status(thm)], ['39', '48'])).
% 0.69/0.91  thf('50', plain,
% 0.69/0.91      (![X0 : $i]:
% 0.69/0.91         (((k1_tops_1 @ X0 @ (u1_struct_0 @ X0))
% 0.69/0.91            = (k3_subset_1 @ (u1_struct_0 @ X0) @ k1_xboole_0))
% 0.69/0.91          | ~ (l1_pre_topc @ X0)
% 0.69/0.91          | ~ (v2_pre_topc @ X0)
% 0.69/0.91          | ~ (l1_pre_topc @ X0))),
% 0.69/0.91      inference('sup+', [status(thm)], ['11', '49'])).
% 0.69/0.91  thf('51', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ k1_xboole_0) = (X0))),
% 0.69/0.91      inference('sup+', [status(thm)], ['45', '46'])).
% 0.69/0.91  thf('52', plain,
% 0.69/0.91      (![X0 : $i]:
% 0.69/0.91         (((k1_tops_1 @ X0 @ (u1_struct_0 @ X0)) = (u1_struct_0 @ X0))
% 0.69/0.91          | ~ (l1_pre_topc @ X0)
% 0.69/0.91          | ~ (v2_pre_topc @ X0)
% 0.69/0.91          | ~ (l1_pre_topc @ X0))),
% 0.69/0.91      inference('demod', [status(thm)], ['50', '51'])).
% 0.69/0.91  thf('53', plain,
% 0.69/0.91      (![X0 : $i]:
% 0.69/0.91         (~ (v2_pre_topc @ X0)
% 0.69/0.91          | ~ (l1_pre_topc @ X0)
% 0.69/0.91          | ((k1_tops_1 @ X0 @ (u1_struct_0 @ X0)) = (u1_struct_0 @ X0)))),
% 0.69/0.91      inference('simplify', [status(thm)], ['52'])).
% 0.69/0.91  thf('54', plain,
% 0.69/0.91      (![X0 : $i]:
% 0.69/0.91         (((k1_tops_1 @ X0 @ (k2_struct_0 @ X0)) = (u1_struct_0 @ X0))
% 0.69/0.91          | ~ (l1_struct_0 @ X0)
% 0.69/0.91          | ~ (l1_pre_topc @ X0)
% 0.69/0.91          | ~ (v2_pre_topc @ X0))),
% 0.69/0.91      inference('sup+', [status(thm)], ['1', '53'])).
% 0.69/0.91  thf('55', plain,
% 0.69/0.91      (![X0 : $i]:
% 0.69/0.91         (((k1_tops_1 @ X0 @ (k2_struct_0 @ X0)) = (k2_struct_0 @ X0))
% 0.69/0.91          | ~ (l1_struct_0 @ X0)
% 0.69/0.91          | ~ (v2_pre_topc @ X0)
% 0.69/0.91          | ~ (l1_pre_topc @ X0)
% 0.69/0.91          | ~ (l1_struct_0 @ X0))),
% 0.69/0.91      inference('sup+', [status(thm)], ['0', '54'])).
% 0.69/0.91  thf('56', plain,
% 0.69/0.91      (![X0 : $i]:
% 0.69/0.91         (~ (l1_pre_topc @ X0)
% 0.69/0.91          | ~ (v2_pre_topc @ X0)
% 0.69/0.91          | ~ (l1_struct_0 @ X0)
% 0.69/0.91          | ((k1_tops_1 @ X0 @ (k2_struct_0 @ X0)) = (k2_struct_0 @ X0)))),
% 0.69/0.91      inference('simplify', [status(thm)], ['55'])).
% 0.69/0.91  thf(t43_tops_1, conjecture,
% 0.69/0.91    (![A:$i]:
% 0.69/0.91     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.69/0.91       ( ( k1_tops_1 @ A @ ( k2_struct_0 @ A ) ) = ( k2_struct_0 @ A ) ) ))).
% 0.69/0.91  thf(zf_stmt_0, negated_conjecture,
% 0.69/0.91    (~( ![A:$i]:
% 0.69/0.91        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.69/0.91          ( ( k1_tops_1 @ A @ ( k2_struct_0 @ A ) ) = ( k2_struct_0 @ A ) ) ) )),
% 0.69/0.91    inference('cnf.neg', [status(esa)], [t43_tops_1])).
% 0.69/0.91  thf('57', plain,
% 0.69/0.91      (((k1_tops_1 @ sk_A @ (k2_struct_0 @ sk_A)) != (k2_struct_0 @ sk_A))),
% 0.69/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.91  thf('58', plain,
% 0.69/0.91      ((((k2_struct_0 @ sk_A) != (k2_struct_0 @ sk_A))
% 0.69/0.91        | ~ (l1_struct_0 @ sk_A)
% 0.69/0.91        | ~ (v2_pre_topc @ sk_A)
% 0.69/0.91        | ~ (l1_pre_topc @ sk_A))),
% 0.69/0.91      inference('sup-', [status(thm)], ['56', '57'])).
% 0.69/0.91  thf('59', plain, ((l1_pre_topc @ sk_A)),
% 0.69/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.91  thf(dt_l1_pre_topc, axiom,
% 0.69/0.91    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.69/0.91  thf('60', plain,
% 0.69/0.91      (![X55 : $i]: ((l1_struct_0 @ X55) | ~ (l1_pre_topc @ X55))),
% 0.69/0.91      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.69/0.91  thf('61', plain, ((l1_struct_0 @ sk_A)),
% 0.69/0.91      inference('sup-', [status(thm)], ['59', '60'])).
% 0.69/0.91  thf('62', plain, ((v2_pre_topc @ sk_A)),
% 0.69/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.91  thf('63', plain, ((l1_pre_topc @ sk_A)),
% 0.69/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.91  thf('64', plain, (((k2_struct_0 @ sk_A) != (k2_struct_0 @ sk_A))),
% 0.69/0.91      inference('demod', [status(thm)], ['58', '61', '62', '63'])).
% 0.69/0.91  thf('65', plain, ($false), inference('simplify', [status(thm)], ['64'])).
% 0.69/0.91  
% 0.69/0.91  % SZS output end Refutation
% 0.69/0.91  
% 0.69/0.92  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
