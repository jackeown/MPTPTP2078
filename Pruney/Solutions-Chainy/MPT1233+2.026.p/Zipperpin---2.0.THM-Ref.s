%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.0idsNj5Gda

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:02:52 EST 2020

% Result     : Theorem 0.46s
% Output     : Refutation 0.46s
% Verified   : 
% Statistics : Number of formulae       :  111 ( 138 expanded)
%              Number of leaves         :   38 (  56 expanded)
%              Depth                    :   19
%              Number of atoms          :  858 (1035 expanded)
%              Number of equality atoms :   57 (  74 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_struct_0_type,type,(
    k1_struct_0: $i > $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('0',plain,(
    ! [X48: $i] :
      ( ( ( k2_struct_0 @ X48 )
        = ( u1_struct_0 @ X48 ) )
      | ~ ( l1_struct_0 @ X48 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('1',plain,(
    ! [X37: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(cc2_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v1_xboole_0 @ B )
           => ( v4_pre_topc @ B @ A ) ) ) ) )).

thf('2',plain,(
    ! [X46: $i,X47: $i] :
      ( ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X47 ) ) )
      | ( v4_pre_topc @ X46 @ X47 )
      | ~ ( v1_xboole_0 @ X46 )
      | ~ ( l1_pre_topc @ X47 )
      | ~ ( v2_pre_topc @ X47 ) ) ),
    inference(cnf,[status(esa)],[cc2_pre_topc])).

thf('3',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( v4_pre_topc @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('4',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('5',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v4_pre_topc @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X37: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X37 ) ) ),
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

thf('7',plain,(
    ! [X53: $i,X54: $i] :
      ( ~ ( m1_subset_1 @ X53 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X54 ) ) )
      | ~ ( v4_pre_topc @ X53 @ X54 )
      | ( ( k2_pre_topc @ X54 @ X53 )
        = X53 )
      | ~ ( l1_pre_topc @ X54 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('8',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( k2_pre_topc @ X0 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( v4_pre_topc @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( ( k2_pre_topc @ X0 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( ( k2_pre_topc @ X0 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf(fc3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( v1_xboole_0 @ ( k1_struct_0 @ A ) ) ) )).

thf('11',plain,(
    ! [X51: $i] :
      ( ( v1_xboole_0 @ ( k1_struct_0 @ X51 ) )
      | ~ ( l1_struct_0 @ X51 ) ) ),
    inference(cnf,[status(esa)],[fc3_struct_0])).

thf(t8_boole,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( v1_xboole_0 @ A )
        & ( A != B )
        & ( v1_xboole_0 @ B ) ) )).

thf('12',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v1_xboole_0 @ X3 )
      | ~ ( v1_xboole_0 @ X4 )
      | ( X3 = X4 ) ) ),
    inference(cnf,[status(esa)],[t8_boole])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( ( k1_struct_0 @ X0 )
        = X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X48: $i] :
      ( ( ( k2_struct_0 @ X48 )
        = ( u1_struct_0 @ X48 ) )
      | ~ ( l1_struct_0 @ X48 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(t27_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( k3_subset_1 @ ( u1_struct_0 @ A ) @ ( k1_struct_0 @ A ) ) ) ) )).

thf('15',plain,(
    ! [X52: $i] :
      ( ( ( k2_struct_0 @ X52 )
        = ( k3_subset_1 @ ( u1_struct_0 @ X52 ) @ ( k1_struct_0 @ X52 ) ) )
      | ~ ( l1_struct_0 @ X52 ) ) ),
    inference(cnf,[status(esa)],[t27_pre_topc])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( ( k2_struct_0 @ X0 )
        = ( k3_subset_1 @ ( k2_struct_0 @ X0 ) @ ( k1_struct_0 @ X0 ) ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( ( k2_struct_0 @ X0 )
        = ( k3_subset_1 @ ( k2_struct_0 @ X0 ) @ ( k1_struct_0 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_struct_0 @ X1 )
        = ( k3_subset_1 @ ( k2_struct_0 @ X1 ) @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( l1_struct_0 @ X1 )
      | ~ ( l1_struct_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['13','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_struct_0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 )
      | ( ( k2_struct_0 @ X1 )
        = ( k3_subset_1 @ ( k2_struct_0 @ X1 ) @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    ! [X37: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('21',plain,(
    ! [X33: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X33 ) @ ( k1_zfmisc_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('22',plain,(
    ! [X32: $i] :
      ( ( k2_subset_1 @ X32 )
      = X32 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('23',plain,(
    ! [X33: $i] :
      ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ X33 ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf(t36_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ( r1_tarski @ ( k3_subset_1 @ A @ B ) @ C )
           => ( r1_tarski @ ( k3_subset_1 @ A @ C ) @ B ) ) ) ) )).

thf('24',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ X35 ) )
      | ( r1_tarski @ ( k3_subset_1 @ X35 @ X34 ) @ X36 )
      | ~ ( r1_tarski @ ( k3_subset_1 @ X35 @ X36 ) @ X34 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[t36_subset_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) )
      | ~ ( r1_tarski @ ( k3_subset_1 @ X0 @ X1 ) @ X0 )
      | ( r1_tarski @ ( k3_subset_1 @ X0 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k3_subset_1 @ X0 @ X0 ) @ k1_xboole_0 )
      | ~ ( r1_tarski @ ( k3_subset_1 @ X0 @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_struct_0 @ X0 ) @ ( k2_struct_0 @ X0 ) )
      | ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( r1_tarski @ ( k3_subset_1 @ ( k2_struct_0 @ X0 ) @ ( k2_struct_0 @ X0 ) ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['19','26'])).

thf('28',plain,(
    ! [X33: $i] :
      ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ X33 ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('29',plain,(
    ! [X40: $i,X41: $i] :
      ( ( r1_tarski @ X40 @ X41 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ X41 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('30',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('32',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( r1_tarski @ ( k3_subset_1 @ ( k2_struct_0 @ X0 ) @ ( k2_struct_0 @ X0 ) ) @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['27','30','31'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = X0 )
      | ~ ( r1_tarski @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('34',plain,(
    ! [X38: $i,X39: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X38 @ X39 ) )
      = ( k3_xboole_0 @ X38 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) )
        = X0 )
      | ~ ( r1_tarski @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( ( k1_setfam_1 @ ( k2_tarski @ ( k3_subset_1 @ ( k2_struct_0 @ X0 ) @ ( k2_struct_0 @ X0 ) ) @ k1_xboole_0 ) )
        = ( k3_subset_1 @ ( k2_struct_0 @ X0 ) @ ( k2_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['32','35'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('37',plain,(
    ! [X2: $i] :
      ( ( k3_xboole_0 @ X2 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('38',plain,(
    ! [X38: $i,X39: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X38 @ X39 ) )
      = ( k3_xboole_0 @ X38 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('39',plain,(
    ! [X2: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X2 @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( k1_xboole_0
        = ( k3_subset_1 @ ( k2_struct_0 @ X0 ) @ ( k2_struct_0 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['36','39'])).

thf('41',plain,(
    ! [X48: $i] :
      ( ( ( k2_struct_0 @ X48 )
        = ( u1_struct_0 @ X48 ) )
      | ~ ( l1_struct_0 @ X48 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('42',plain,(
    ! [X48: $i] :
      ( ( ( k2_struct_0 @ X48 )
        = ( u1_struct_0 @ X48 ) )
      | ~ ( l1_struct_0 @ X48 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('43',plain,(
    ! [X33: $i] :
      ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ X33 ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf(d1_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k1_tops_1 @ A @ B )
            = ( k3_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) )).

thf('44',plain,(
    ! [X55: $i,X56: $i] :
      ( ~ ( m1_subset_1 @ X55 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X56 ) ) )
      | ( ( k1_tops_1 @ X56 @ X55 )
        = ( k3_subset_1 @ ( u1_struct_0 @ X56 ) @ ( k2_pre_topc @ X56 @ ( k3_subset_1 @ ( u1_struct_0 @ X56 ) @ X55 ) ) ) )
      | ~ ( l1_pre_topc @ X56 ) ) ),
    inference(cnf,[status(esa)],[d1_tops_1])).

thf('45',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( k1_tops_1 @ X0 @ ( u1_struct_0 @ X0 ) )
        = ( k3_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k2_pre_topc @ X0 @ ( k3_subset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( ( k1_struct_0 @ X0 )
        = X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('47',plain,(
    ! [X52: $i] :
      ( ( ( k2_struct_0 @ X52 )
        = ( k3_subset_1 @ ( u1_struct_0 @ X52 ) @ ( k1_struct_0 @ X52 ) ) )
      | ~ ( l1_struct_0 @ X52 ) ) ),
    inference(cnf,[status(esa)],[t27_pre_topc])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_struct_0 @ X1 )
        = ( k3_subset_1 @ ( u1_struct_0 @ X1 ) @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( l1_struct_0 @ X1 )
      | ~ ( l1_struct_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_struct_0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 )
      | ( ( k2_struct_0 @ X1 )
        = ( k3_subset_1 @ ( u1_struct_0 @ X1 ) @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( ( k2_struct_0 @ X0 )
        = ( k1_tops_1 @ X0 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_xboole_0 @ ( k2_pre_topc @ X0 @ ( k3_subset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['45','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_pre_topc @ X0 @ ( k3_subset_1 @ ( k2_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( k2_struct_0 @ X0 )
        = ( k1_tops_1 @ X0 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['42','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( ( k2_struct_0 @ X0 )
        = ( k1_tops_1 @ X0 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( v1_xboole_0 @ ( k2_pre_topc @ X0 @ ( k3_subset_1 @ ( k2_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_pre_topc @ X0 @ ( k3_subset_1 @ ( k2_struct_0 @ X0 ) @ ( k2_struct_0 @ X0 ) ) ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( k2_struct_0 @ X0 )
        = ( k1_tops_1 @ X0 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['41','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( ( k2_struct_0 @ X0 )
        = ( k1_tops_1 @ X0 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( v1_xboole_0 @ ( k2_pre_topc @ X0 @ ( k3_subset_1 @ ( k2_struct_0 @ X0 ) @ ( k2_struct_0 @ X0 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_pre_topc @ X0 @ k1_xboole_0 ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( k2_struct_0 @ X0 )
        = ( k1_tops_1 @ X0 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['40','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( ( k2_struct_0 @ X0 )
        = ( k1_tops_1 @ X0 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( v1_xboole_0 @ ( k2_pre_topc @ X0 @ k1_xboole_0 ) ) ) ),
    inference(simplify,[status(thm)],['55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( k2_struct_0 @ X0 )
        = ( k1_tops_1 @ X0 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['10','56'])).

thf('58',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('59',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( k2_struct_0 @ X0 )
        = ( k1_tops_1 @ X0 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( ( k2_struct_0 @ X0 )
        = ( k1_tops_1 @ X0 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( ( k2_struct_0 @ X0 )
        = ( k1_tops_1 @ X0 @ ( k2_struct_0 @ X0 ) ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['0','60'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( ( k2_struct_0 @ X0 )
        = ( k1_tops_1 @ X0 @ ( k2_struct_0 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['61'])).

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

thf('63',plain,(
    ( k1_tops_1 @ sk_A @ ( k2_struct_0 @ sk_A ) )
 != ( k2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,
    ( ( ( k2_struct_0 @ sk_A )
     != ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('66',plain,(
    ! [X50: $i] :
      ( ( l1_struct_0 @ X50 )
      | ~ ( l1_pre_topc @ X50 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('67',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    ( k2_struct_0 @ sk_A )
 != ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['64','67','68','69'])).

thf('71',plain,(
    $false ),
    inference(simplify,[status(thm)],['70'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.0idsNj5Gda
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 14:11:11 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.36  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.46/0.66  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.46/0.66  % Solved by: fo/fo7.sh
% 0.46/0.66  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.46/0.66  % done 317 iterations in 0.185s
% 0.46/0.66  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.46/0.66  % SZS output start Refutation
% 0.46/0.66  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.46/0.66  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.46/0.66  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.46/0.66  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.46/0.66  thf(k1_struct_0_type, type, k1_struct_0: $i > $i).
% 0.46/0.66  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.46/0.66  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.46/0.66  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.46/0.66  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.46/0.66  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.46/0.66  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.46/0.66  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.46/0.66  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.46/0.66  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.46/0.66  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.46/0.66  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.46/0.66  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.46/0.66  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.46/0.66  thf(sk_A_type, type, sk_A: $i).
% 0.46/0.66  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.46/0.66  thf(d3_struct_0, axiom,
% 0.46/0.66    (![A:$i]:
% 0.46/0.66     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.46/0.66  thf('0', plain,
% 0.46/0.66      (![X48 : $i]:
% 0.46/0.66         (((k2_struct_0 @ X48) = (u1_struct_0 @ X48)) | ~ (l1_struct_0 @ X48))),
% 0.46/0.66      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.46/0.66  thf(t4_subset_1, axiom,
% 0.46/0.66    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.46/0.66  thf('1', plain,
% 0.46/0.66      (![X37 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X37))),
% 0.46/0.66      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.46/0.66  thf(cc2_pre_topc, axiom,
% 0.46/0.66    (![A:$i]:
% 0.46/0.66     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.46/0.66       ( ![B:$i]:
% 0.46/0.66         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.46/0.66           ( ( v1_xboole_0 @ B ) => ( v4_pre_topc @ B @ A ) ) ) ) ))).
% 0.46/0.66  thf('2', plain,
% 0.46/0.66      (![X46 : $i, X47 : $i]:
% 0.46/0.66         (~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (u1_struct_0 @ X47)))
% 0.46/0.66          | (v4_pre_topc @ X46 @ X47)
% 0.46/0.66          | ~ (v1_xboole_0 @ X46)
% 0.46/0.66          | ~ (l1_pre_topc @ X47)
% 0.46/0.66          | ~ (v2_pre_topc @ X47))),
% 0.46/0.66      inference('cnf', [status(esa)], [cc2_pre_topc])).
% 0.46/0.66  thf('3', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         (~ (v2_pre_topc @ X0)
% 0.46/0.66          | ~ (l1_pre_topc @ X0)
% 0.46/0.66          | ~ (v1_xboole_0 @ k1_xboole_0)
% 0.46/0.66          | (v4_pre_topc @ k1_xboole_0 @ X0))),
% 0.46/0.66      inference('sup-', [status(thm)], ['1', '2'])).
% 0.46/0.66  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.46/0.66  thf('4', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.46/0.66      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.46/0.66  thf('5', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         (~ (v2_pre_topc @ X0)
% 0.46/0.66          | ~ (l1_pre_topc @ X0)
% 0.46/0.66          | (v4_pre_topc @ k1_xboole_0 @ X0))),
% 0.46/0.66      inference('demod', [status(thm)], ['3', '4'])).
% 0.46/0.66  thf('6', plain,
% 0.46/0.66      (![X37 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X37))),
% 0.46/0.66      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.46/0.66  thf(t52_pre_topc, axiom,
% 0.46/0.66    (![A:$i]:
% 0.46/0.66     ( ( l1_pre_topc @ A ) =>
% 0.46/0.66       ( ![B:$i]:
% 0.46/0.66         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.46/0.66           ( ( ( v4_pre_topc @ B @ A ) => ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) & 
% 0.46/0.66             ( ( ( v2_pre_topc @ A ) & ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) =>
% 0.46/0.66               ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 0.46/0.66  thf('7', plain,
% 0.46/0.66      (![X53 : $i, X54 : $i]:
% 0.46/0.66         (~ (m1_subset_1 @ X53 @ (k1_zfmisc_1 @ (u1_struct_0 @ X54)))
% 0.46/0.66          | ~ (v4_pre_topc @ X53 @ X54)
% 0.46/0.66          | ((k2_pre_topc @ X54 @ X53) = (X53))
% 0.46/0.66          | ~ (l1_pre_topc @ X54))),
% 0.46/0.66      inference('cnf', [status(esa)], [t52_pre_topc])).
% 0.46/0.66  thf('8', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         (~ (l1_pre_topc @ X0)
% 0.46/0.66          | ((k2_pre_topc @ X0 @ k1_xboole_0) = (k1_xboole_0))
% 0.46/0.66          | ~ (v4_pre_topc @ k1_xboole_0 @ X0))),
% 0.46/0.66      inference('sup-', [status(thm)], ['6', '7'])).
% 0.46/0.66  thf('9', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         (~ (l1_pre_topc @ X0)
% 0.46/0.66          | ~ (v2_pre_topc @ X0)
% 0.46/0.66          | ((k2_pre_topc @ X0 @ k1_xboole_0) = (k1_xboole_0))
% 0.46/0.66          | ~ (l1_pre_topc @ X0))),
% 0.46/0.66      inference('sup-', [status(thm)], ['5', '8'])).
% 0.46/0.66  thf('10', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         (((k2_pre_topc @ X0 @ k1_xboole_0) = (k1_xboole_0))
% 0.46/0.66          | ~ (v2_pre_topc @ X0)
% 0.46/0.66          | ~ (l1_pre_topc @ X0))),
% 0.46/0.66      inference('simplify', [status(thm)], ['9'])).
% 0.46/0.66  thf(fc3_struct_0, axiom,
% 0.46/0.66    (![A:$i]: ( ( l1_struct_0 @ A ) => ( v1_xboole_0 @ ( k1_struct_0 @ A ) ) ))).
% 0.46/0.66  thf('11', plain,
% 0.46/0.66      (![X51 : $i]:
% 0.46/0.66         ((v1_xboole_0 @ (k1_struct_0 @ X51)) | ~ (l1_struct_0 @ X51))),
% 0.46/0.66      inference('cnf', [status(esa)], [fc3_struct_0])).
% 0.46/0.66  thf(t8_boole, axiom,
% 0.46/0.66    (![A:$i,B:$i]:
% 0.46/0.66     ( ~( ( v1_xboole_0 @ A ) & ( ( A ) != ( B ) ) & ( v1_xboole_0 @ B ) ) ))).
% 0.46/0.66  thf('12', plain,
% 0.46/0.66      (![X3 : $i, X4 : $i]:
% 0.46/0.66         (~ (v1_xboole_0 @ X3) | ~ (v1_xboole_0 @ X4) | ((X3) = (X4)))),
% 0.46/0.66      inference('cnf', [status(esa)], [t8_boole])).
% 0.46/0.66  thf('13', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i]:
% 0.46/0.66         (~ (l1_struct_0 @ X0)
% 0.46/0.66          | ((k1_struct_0 @ X0) = (X1))
% 0.46/0.66          | ~ (v1_xboole_0 @ X1))),
% 0.46/0.66      inference('sup-', [status(thm)], ['11', '12'])).
% 0.46/0.66  thf('14', plain,
% 0.46/0.66      (![X48 : $i]:
% 0.46/0.66         (((k2_struct_0 @ X48) = (u1_struct_0 @ X48)) | ~ (l1_struct_0 @ X48))),
% 0.46/0.66      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.46/0.66  thf(t27_pre_topc, axiom,
% 0.46/0.66    (![A:$i]:
% 0.46/0.66     ( ( l1_struct_0 @ A ) =>
% 0.46/0.66       ( ( k2_struct_0 @ A ) =
% 0.46/0.66         ( k3_subset_1 @ ( u1_struct_0 @ A ) @ ( k1_struct_0 @ A ) ) ) ))).
% 0.46/0.66  thf('15', plain,
% 0.46/0.66      (![X52 : $i]:
% 0.46/0.66         (((k2_struct_0 @ X52)
% 0.46/0.66            = (k3_subset_1 @ (u1_struct_0 @ X52) @ (k1_struct_0 @ X52)))
% 0.46/0.66          | ~ (l1_struct_0 @ X52))),
% 0.46/0.66      inference('cnf', [status(esa)], [t27_pre_topc])).
% 0.46/0.66  thf('16', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         (((k2_struct_0 @ X0)
% 0.46/0.66            = (k3_subset_1 @ (k2_struct_0 @ X0) @ (k1_struct_0 @ X0)))
% 0.46/0.66          | ~ (l1_struct_0 @ X0)
% 0.46/0.66          | ~ (l1_struct_0 @ X0))),
% 0.46/0.66      inference('sup+', [status(thm)], ['14', '15'])).
% 0.46/0.66  thf('17', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         (~ (l1_struct_0 @ X0)
% 0.46/0.66          | ((k2_struct_0 @ X0)
% 0.46/0.66              = (k3_subset_1 @ (k2_struct_0 @ X0) @ (k1_struct_0 @ X0))))),
% 0.46/0.66      inference('simplify', [status(thm)], ['16'])).
% 0.46/0.66  thf('18', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i]:
% 0.46/0.66         (((k2_struct_0 @ X1) = (k3_subset_1 @ (k2_struct_0 @ X1) @ X0))
% 0.46/0.66          | ~ (v1_xboole_0 @ X0)
% 0.46/0.66          | ~ (l1_struct_0 @ X1)
% 0.46/0.66          | ~ (l1_struct_0 @ X1))),
% 0.46/0.66      inference('sup+', [status(thm)], ['13', '17'])).
% 0.46/0.66  thf('19', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i]:
% 0.46/0.66         (~ (l1_struct_0 @ X1)
% 0.46/0.66          | ~ (v1_xboole_0 @ X0)
% 0.46/0.66          | ((k2_struct_0 @ X1) = (k3_subset_1 @ (k2_struct_0 @ X1) @ X0)))),
% 0.46/0.66      inference('simplify', [status(thm)], ['18'])).
% 0.46/0.66  thf('20', plain,
% 0.46/0.66      (![X37 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X37))),
% 0.46/0.66      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.46/0.66  thf(dt_k2_subset_1, axiom,
% 0.46/0.66    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.46/0.66  thf('21', plain,
% 0.46/0.66      (![X33 : $i]: (m1_subset_1 @ (k2_subset_1 @ X33) @ (k1_zfmisc_1 @ X33))),
% 0.46/0.66      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 0.46/0.66  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.46/0.66  thf('22', plain, (![X32 : $i]: ((k2_subset_1 @ X32) = (X32))),
% 0.46/0.66      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.46/0.66  thf('23', plain, (![X33 : $i]: (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ X33))),
% 0.46/0.66      inference('demod', [status(thm)], ['21', '22'])).
% 0.46/0.66  thf(t36_subset_1, axiom,
% 0.46/0.66    (![A:$i,B:$i]:
% 0.46/0.66     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.46/0.66       ( ![C:$i]:
% 0.46/0.66         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.46/0.66           ( ( r1_tarski @ ( k3_subset_1 @ A @ B ) @ C ) =>
% 0.46/0.66             ( r1_tarski @ ( k3_subset_1 @ A @ C ) @ B ) ) ) ) ))).
% 0.46/0.66  thf('24', plain,
% 0.46/0.66      (![X34 : $i, X35 : $i, X36 : $i]:
% 0.46/0.66         (~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ X35))
% 0.46/0.66          | (r1_tarski @ (k3_subset_1 @ X35 @ X34) @ X36)
% 0.46/0.66          | ~ (r1_tarski @ (k3_subset_1 @ X35 @ X36) @ X34)
% 0.46/0.66          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ X35)))),
% 0.46/0.66      inference('cnf', [status(esa)], [t36_subset_1])).
% 0.46/0.66  thf('25', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i]:
% 0.46/0.66         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0))
% 0.46/0.66          | ~ (r1_tarski @ (k3_subset_1 @ X0 @ X1) @ X0)
% 0.46/0.66          | (r1_tarski @ (k3_subset_1 @ X0 @ X0) @ X1))),
% 0.46/0.66      inference('sup-', [status(thm)], ['23', '24'])).
% 0.46/0.66  thf('26', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         ((r1_tarski @ (k3_subset_1 @ X0 @ X0) @ k1_xboole_0)
% 0.46/0.66          | ~ (r1_tarski @ (k3_subset_1 @ X0 @ k1_xboole_0) @ X0))),
% 0.46/0.66      inference('sup-', [status(thm)], ['20', '25'])).
% 0.46/0.66  thf('27', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         (~ (r1_tarski @ (k2_struct_0 @ X0) @ (k2_struct_0 @ X0))
% 0.46/0.66          | ~ (v1_xboole_0 @ k1_xboole_0)
% 0.46/0.66          | ~ (l1_struct_0 @ X0)
% 0.46/0.66          | (r1_tarski @ 
% 0.46/0.66             (k3_subset_1 @ (k2_struct_0 @ X0) @ (k2_struct_0 @ X0)) @ 
% 0.46/0.66             k1_xboole_0))),
% 0.46/0.66      inference('sup-', [status(thm)], ['19', '26'])).
% 0.46/0.66  thf('28', plain, (![X33 : $i]: (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ X33))),
% 0.46/0.66      inference('demod', [status(thm)], ['21', '22'])).
% 0.46/0.66  thf(t3_subset, axiom,
% 0.46/0.66    (![A:$i,B:$i]:
% 0.46/0.66     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.46/0.66  thf('29', plain,
% 0.46/0.66      (![X40 : $i, X41 : $i]:
% 0.46/0.66         ((r1_tarski @ X40 @ X41) | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ X41)))),
% 0.46/0.66      inference('cnf', [status(esa)], [t3_subset])).
% 0.46/0.66  thf('30', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.46/0.66      inference('sup-', [status(thm)], ['28', '29'])).
% 0.46/0.66  thf('31', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.46/0.66      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.46/0.66  thf('32', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         (~ (l1_struct_0 @ X0)
% 0.46/0.66          | (r1_tarski @ 
% 0.46/0.66             (k3_subset_1 @ (k2_struct_0 @ X0) @ (k2_struct_0 @ X0)) @ 
% 0.46/0.66             k1_xboole_0))),
% 0.46/0.66      inference('demod', [status(thm)], ['27', '30', '31'])).
% 0.46/0.66  thf(t28_xboole_1, axiom,
% 0.46/0.66    (![A:$i,B:$i]:
% 0.46/0.66     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.46/0.66  thf('33', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i]:
% 0.46/0.66         (((k3_xboole_0 @ X0 @ X1) = (X0)) | ~ (r1_tarski @ X0 @ X1))),
% 0.46/0.66      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.46/0.66  thf(t12_setfam_1, axiom,
% 0.46/0.66    (![A:$i,B:$i]:
% 0.46/0.66     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.46/0.66  thf('34', plain,
% 0.46/0.66      (![X38 : $i, X39 : $i]:
% 0.46/0.66         ((k1_setfam_1 @ (k2_tarski @ X38 @ X39)) = (k3_xboole_0 @ X38 @ X39))),
% 0.46/0.66      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.46/0.66  thf('35', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i]:
% 0.46/0.66         (((k1_setfam_1 @ (k2_tarski @ X0 @ X1)) = (X0))
% 0.46/0.66          | ~ (r1_tarski @ X0 @ X1))),
% 0.46/0.66      inference('demod', [status(thm)], ['33', '34'])).
% 0.46/0.66  thf('36', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         (~ (l1_struct_0 @ X0)
% 0.46/0.66          | ((k1_setfam_1 @ 
% 0.46/0.66              (k2_tarski @ 
% 0.46/0.66               (k3_subset_1 @ (k2_struct_0 @ X0) @ (k2_struct_0 @ X0)) @ 
% 0.46/0.66               k1_xboole_0))
% 0.46/0.66              = (k3_subset_1 @ (k2_struct_0 @ X0) @ (k2_struct_0 @ X0))))),
% 0.46/0.66      inference('sup-', [status(thm)], ['32', '35'])).
% 0.46/0.66  thf(t2_boole, axiom,
% 0.46/0.66    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.46/0.66  thf('37', plain,
% 0.46/0.66      (![X2 : $i]: ((k3_xboole_0 @ X2 @ k1_xboole_0) = (k1_xboole_0))),
% 0.46/0.66      inference('cnf', [status(esa)], [t2_boole])).
% 0.46/0.66  thf('38', plain,
% 0.46/0.66      (![X38 : $i, X39 : $i]:
% 0.46/0.66         ((k1_setfam_1 @ (k2_tarski @ X38 @ X39)) = (k3_xboole_0 @ X38 @ X39))),
% 0.46/0.66      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.46/0.66  thf('39', plain,
% 0.46/0.66      (![X2 : $i]:
% 0.46/0.66         ((k1_setfam_1 @ (k2_tarski @ X2 @ k1_xboole_0)) = (k1_xboole_0))),
% 0.46/0.66      inference('demod', [status(thm)], ['37', '38'])).
% 0.46/0.66  thf('40', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         (~ (l1_struct_0 @ X0)
% 0.46/0.66          | ((k1_xboole_0)
% 0.46/0.66              = (k3_subset_1 @ (k2_struct_0 @ X0) @ (k2_struct_0 @ X0))))),
% 0.46/0.66      inference('demod', [status(thm)], ['36', '39'])).
% 0.46/0.66  thf('41', plain,
% 0.46/0.66      (![X48 : $i]:
% 0.46/0.66         (((k2_struct_0 @ X48) = (u1_struct_0 @ X48)) | ~ (l1_struct_0 @ X48))),
% 0.46/0.66      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.46/0.66  thf('42', plain,
% 0.46/0.66      (![X48 : $i]:
% 0.46/0.66         (((k2_struct_0 @ X48) = (u1_struct_0 @ X48)) | ~ (l1_struct_0 @ X48))),
% 0.46/0.66      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.46/0.66  thf('43', plain, (![X33 : $i]: (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ X33))),
% 0.46/0.66      inference('demod', [status(thm)], ['21', '22'])).
% 0.46/0.66  thf(d1_tops_1, axiom,
% 0.46/0.66    (![A:$i]:
% 0.46/0.66     ( ( l1_pre_topc @ A ) =>
% 0.46/0.66       ( ![B:$i]:
% 0.46/0.66         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.46/0.66           ( ( k1_tops_1 @ A @ B ) =
% 0.46/0.66             ( k3_subset_1 @
% 0.46/0.66               ( u1_struct_0 @ A ) @ 
% 0.46/0.66               ( k2_pre_topc @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) ))).
% 0.46/0.66  thf('44', plain,
% 0.46/0.66      (![X55 : $i, X56 : $i]:
% 0.46/0.66         (~ (m1_subset_1 @ X55 @ (k1_zfmisc_1 @ (u1_struct_0 @ X56)))
% 0.46/0.66          | ((k1_tops_1 @ X56 @ X55)
% 0.46/0.66              = (k3_subset_1 @ (u1_struct_0 @ X56) @ 
% 0.46/0.66                 (k2_pre_topc @ X56 @ (k3_subset_1 @ (u1_struct_0 @ X56) @ X55))))
% 0.46/0.66          | ~ (l1_pre_topc @ X56))),
% 0.46/0.66      inference('cnf', [status(esa)], [d1_tops_1])).
% 0.46/0.66  thf('45', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         (~ (l1_pre_topc @ X0)
% 0.46/0.66          | ((k1_tops_1 @ X0 @ (u1_struct_0 @ X0))
% 0.46/0.66              = (k3_subset_1 @ (u1_struct_0 @ X0) @ 
% 0.46/0.66                 (k2_pre_topc @ X0 @ 
% 0.46/0.66                  (k3_subset_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0))))))),
% 0.46/0.66      inference('sup-', [status(thm)], ['43', '44'])).
% 0.46/0.66  thf('46', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i]:
% 0.46/0.66         (~ (l1_struct_0 @ X0)
% 0.46/0.66          | ((k1_struct_0 @ X0) = (X1))
% 0.46/0.66          | ~ (v1_xboole_0 @ X1))),
% 0.46/0.66      inference('sup-', [status(thm)], ['11', '12'])).
% 0.46/0.66  thf('47', plain,
% 0.46/0.66      (![X52 : $i]:
% 0.46/0.66         (((k2_struct_0 @ X52)
% 0.46/0.66            = (k3_subset_1 @ (u1_struct_0 @ X52) @ (k1_struct_0 @ X52)))
% 0.46/0.66          | ~ (l1_struct_0 @ X52))),
% 0.46/0.66      inference('cnf', [status(esa)], [t27_pre_topc])).
% 0.46/0.66  thf('48', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i]:
% 0.46/0.66         (((k2_struct_0 @ X1) = (k3_subset_1 @ (u1_struct_0 @ X1) @ X0))
% 0.46/0.66          | ~ (v1_xboole_0 @ X0)
% 0.46/0.66          | ~ (l1_struct_0 @ X1)
% 0.46/0.66          | ~ (l1_struct_0 @ X1))),
% 0.46/0.66      inference('sup+', [status(thm)], ['46', '47'])).
% 0.46/0.66  thf('49', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i]:
% 0.46/0.66         (~ (l1_struct_0 @ X1)
% 0.46/0.66          | ~ (v1_xboole_0 @ X0)
% 0.46/0.66          | ((k2_struct_0 @ X1) = (k3_subset_1 @ (u1_struct_0 @ X1) @ X0)))),
% 0.46/0.66      inference('simplify', [status(thm)], ['48'])).
% 0.46/0.66  thf('50', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         (((k2_struct_0 @ X0) = (k1_tops_1 @ X0 @ (u1_struct_0 @ X0)))
% 0.46/0.66          | ~ (l1_pre_topc @ X0)
% 0.46/0.66          | ~ (v1_xboole_0 @ 
% 0.46/0.66               (k2_pre_topc @ X0 @ 
% 0.46/0.66                (k3_subset_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0))))
% 0.46/0.66          | ~ (l1_struct_0 @ X0))),
% 0.46/0.66      inference('sup+', [status(thm)], ['45', '49'])).
% 0.46/0.66  thf('51', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         (~ (v1_xboole_0 @ 
% 0.46/0.66             (k2_pre_topc @ X0 @ 
% 0.46/0.66              (k3_subset_1 @ (k2_struct_0 @ X0) @ (u1_struct_0 @ X0))))
% 0.46/0.66          | ~ (l1_struct_0 @ X0)
% 0.46/0.66          | ~ (l1_struct_0 @ X0)
% 0.46/0.66          | ~ (l1_pre_topc @ X0)
% 0.46/0.66          | ((k2_struct_0 @ X0) = (k1_tops_1 @ X0 @ (u1_struct_0 @ X0))))),
% 0.46/0.66      inference('sup-', [status(thm)], ['42', '50'])).
% 0.46/0.66  thf('52', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         (((k2_struct_0 @ X0) = (k1_tops_1 @ X0 @ (u1_struct_0 @ X0)))
% 0.46/0.66          | ~ (l1_pre_topc @ X0)
% 0.46/0.66          | ~ (l1_struct_0 @ X0)
% 0.46/0.66          | ~ (v1_xboole_0 @ 
% 0.46/0.66               (k2_pre_topc @ X0 @ 
% 0.46/0.66                (k3_subset_1 @ (k2_struct_0 @ X0) @ (u1_struct_0 @ X0)))))),
% 0.46/0.66      inference('simplify', [status(thm)], ['51'])).
% 0.46/0.66  thf('53', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         (~ (v1_xboole_0 @ 
% 0.46/0.66             (k2_pre_topc @ X0 @ 
% 0.46/0.66              (k3_subset_1 @ (k2_struct_0 @ X0) @ (k2_struct_0 @ X0))))
% 0.46/0.66          | ~ (l1_struct_0 @ X0)
% 0.46/0.66          | ~ (l1_struct_0 @ X0)
% 0.46/0.66          | ~ (l1_pre_topc @ X0)
% 0.46/0.66          | ((k2_struct_0 @ X0) = (k1_tops_1 @ X0 @ (u1_struct_0 @ X0))))),
% 0.46/0.66      inference('sup-', [status(thm)], ['41', '52'])).
% 0.46/0.66  thf('54', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         (((k2_struct_0 @ X0) = (k1_tops_1 @ X0 @ (u1_struct_0 @ X0)))
% 0.46/0.66          | ~ (l1_pre_topc @ X0)
% 0.46/0.66          | ~ (l1_struct_0 @ X0)
% 0.46/0.66          | ~ (v1_xboole_0 @ 
% 0.46/0.66               (k2_pre_topc @ X0 @ 
% 0.46/0.66                (k3_subset_1 @ (k2_struct_0 @ X0) @ (k2_struct_0 @ X0)))))),
% 0.46/0.66      inference('simplify', [status(thm)], ['53'])).
% 0.46/0.66  thf('55', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         (~ (v1_xboole_0 @ (k2_pre_topc @ X0 @ k1_xboole_0))
% 0.46/0.66          | ~ (l1_struct_0 @ X0)
% 0.46/0.66          | ~ (l1_struct_0 @ X0)
% 0.46/0.66          | ~ (l1_pre_topc @ X0)
% 0.46/0.66          | ((k2_struct_0 @ X0) = (k1_tops_1 @ X0 @ (u1_struct_0 @ X0))))),
% 0.46/0.66      inference('sup-', [status(thm)], ['40', '54'])).
% 0.46/0.66  thf('56', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         (((k2_struct_0 @ X0) = (k1_tops_1 @ X0 @ (u1_struct_0 @ X0)))
% 0.46/0.66          | ~ (l1_pre_topc @ X0)
% 0.46/0.66          | ~ (l1_struct_0 @ X0)
% 0.46/0.66          | ~ (v1_xboole_0 @ (k2_pre_topc @ X0 @ k1_xboole_0)))),
% 0.46/0.66      inference('simplify', [status(thm)], ['55'])).
% 0.46/0.66  thf('57', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.46/0.66          | ~ (l1_pre_topc @ X0)
% 0.46/0.66          | ~ (v2_pre_topc @ X0)
% 0.46/0.66          | ~ (l1_struct_0 @ X0)
% 0.46/0.66          | ~ (l1_pre_topc @ X0)
% 0.46/0.66          | ((k2_struct_0 @ X0) = (k1_tops_1 @ X0 @ (u1_struct_0 @ X0))))),
% 0.46/0.66      inference('sup-', [status(thm)], ['10', '56'])).
% 0.46/0.66  thf('58', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.46/0.66      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.46/0.66  thf('59', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         (~ (l1_pre_topc @ X0)
% 0.46/0.66          | ~ (v2_pre_topc @ X0)
% 0.46/0.66          | ~ (l1_struct_0 @ X0)
% 0.46/0.66          | ~ (l1_pre_topc @ X0)
% 0.46/0.66          | ((k2_struct_0 @ X0) = (k1_tops_1 @ X0 @ (u1_struct_0 @ X0))))),
% 0.46/0.66      inference('demod', [status(thm)], ['57', '58'])).
% 0.46/0.66  thf('60', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         (((k2_struct_0 @ X0) = (k1_tops_1 @ X0 @ (u1_struct_0 @ X0)))
% 0.46/0.66          | ~ (l1_struct_0 @ X0)
% 0.46/0.66          | ~ (v2_pre_topc @ X0)
% 0.46/0.66          | ~ (l1_pre_topc @ X0))),
% 0.46/0.66      inference('simplify', [status(thm)], ['59'])).
% 0.46/0.66  thf('61', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         (((k2_struct_0 @ X0) = (k1_tops_1 @ X0 @ (k2_struct_0 @ X0)))
% 0.46/0.66          | ~ (l1_struct_0 @ X0)
% 0.46/0.66          | ~ (l1_pre_topc @ X0)
% 0.46/0.66          | ~ (v2_pre_topc @ X0)
% 0.46/0.66          | ~ (l1_struct_0 @ X0))),
% 0.46/0.66      inference('sup+', [status(thm)], ['0', '60'])).
% 0.46/0.66  thf('62', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         (~ (v2_pre_topc @ X0)
% 0.46/0.66          | ~ (l1_pre_topc @ X0)
% 0.46/0.66          | ~ (l1_struct_0 @ X0)
% 0.46/0.66          | ((k2_struct_0 @ X0) = (k1_tops_1 @ X0 @ (k2_struct_0 @ X0))))),
% 0.46/0.66      inference('simplify', [status(thm)], ['61'])).
% 0.46/0.66  thf(t43_tops_1, conjecture,
% 0.46/0.66    (![A:$i]:
% 0.46/0.66     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.46/0.66       ( ( k1_tops_1 @ A @ ( k2_struct_0 @ A ) ) = ( k2_struct_0 @ A ) ) ))).
% 0.46/0.66  thf(zf_stmt_0, negated_conjecture,
% 0.46/0.66    (~( ![A:$i]:
% 0.46/0.66        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.46/0.66          ( ( k1_tops_1 @ A @ ( k2_struct_0 @ A ) ) = ( k2_struct_0 @ A ) ) ) )),
% 0.46/0.66    inference('cnf.neg', [status(esa)], [t43_tops_1])).
% 0.46/0.66  thf('63', plain,
% 0.46/0.66      (((k1_tops_1 @ sk_A @ (k2_struct_0 @ sk_A)) != (k2_struct_0 @ sk_A))),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('64', plain,
% 0.46/0.66      ((((k2_struct_0 @ sk_A) != (k2_struct_0 @ sk_A))
% 0.46/0.66        | ~ (l1_struct_0 @ sk_A)
% 0.46/0.66        | ~ (l1_pre_topc @ sk_A)
% 0.46/0.66        | ~ (v2_pre_topc @ sk_A))),
% 0.46/0.66      inference('sup-', [status(thm)], ['62', '63'])).
% 0.46/0.66  thf('65', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf(dt_l1_pre_topc, axiom,
% 0.46/0.66    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.46/0.66  thf('66', plain,
% 0.46/0.66      (![X50 : $i]: ((l1_struct_0 @ X50) | ~ (l1_pre_topc @ X50))),
% 0.46/0.66      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.46/0.66  thf('67', plain, ((l1_struct_0 @ sk_A)),
% 0.46/0.66      inference('sup-', [status(thm)], ['65', '66'])).
% 0.46/0.66  thf('68', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('69', plain, ((v2_pre_topc @ sk_A)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('70', plain, (((k2_struct_0 @ sk_A) != (k2_struct_0 @ sk_A))),
% 0.46/0.66      inference('demod', [status(thm)], ['64', '67', '68', '69'])).
% 0.46/0.66  thf('71', plain, ($false), inference('simplify', [status(thm)], ['70'])).
% 0.46/0.66  
% 0.46/0.66  % SZS output end Refutation
% 0.46/0.66  
% 0.46/0.67  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
