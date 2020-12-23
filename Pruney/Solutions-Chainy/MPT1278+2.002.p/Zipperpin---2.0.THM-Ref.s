%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.y5nJsTBO9D

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:04:39 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :  134 ( 229 expanded)
%              Number of leaves         :   37 (  84 expanded)
%              Depth                    :   14
%              Number of atoms          : 1004 (2111 expanded)
%              Number of equality atoms :   56 ( 130 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v1_tops_1_type,type,(
    v1_tops_1: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(v3_tops_1_type,type,(
    v3_tops_1: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('0',plain,(
    ! [X12: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(cc1_tops_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v1_xboole_0 @ B )
           => ( v3_pre_topc @ B @ A ) ) ) ) )).

thf('1',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ( v3_pre_topc @ X20 @ X21 )
      | ~ ( v1_xboole_0 @ X20 )
      | ~ ( l1_pre_topc @ X21 )
      | ~ ( v2_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[cc1_tops_1])).

thf('2',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( v3_pre_topc @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('3',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('4',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v3_pre_topc @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X12: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(t30_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v3_pre_topc @ B @ A )
          <=> ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) )).

thf('6',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
      | ~ ( v3_pre_topc @ X26 @ X27 )
      | ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ X27 ) @ X26 ) @ X27 )
      | ~ ( l1_pre_topc @ X27 ) ) ),
    inference(cnf,[status(esa)],[t30_tops_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ X0 ) @ k1_xboole_0 ) @ X0 )
      | ~ ( v3_pre_topc @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X12: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('9',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k3_subset_1 @ X5 @ X6 )
        = ( k4_xboole_0 @ X5 @ X6 ) )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('11',plain,(
    ! [X2: $i] :
      ( ( k3_xboole_0 @ X2 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('14',plain,(
    ! [X3: $i] :
      ( ( k5_xboole_0 @ X3 @ k1_xboole_0 )
      = X3 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['10','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v4_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( v3_pre_topc @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['7','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v4_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( v4_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('20',plain,(
    ! [X7: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X7 ) @ ( k1_zfmisc_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('21',plain,(
    ! [X4: $i] :
      ( ( k2_subset_1 @ X4 )
      = X4 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('22',plain,(
    ! [X7: $i] :
      ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X7 ) ) ),
    inference(demod,[status(thm)],['20','21'])).

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

thf('23',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( v4_pre_topc @ X18 @ X19 )
      | ( ( k2_pre_topc @ X19 @ X18 )
        = X18 )
      | ~ ( l1_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( k2_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( v4_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( ( k2_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['19','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( ( k2_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    ! [X12: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(cc3_tops_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v1_xboole_0 @ B )
           => ( v3_tops_1 @ B @ A ) ) ) ) )).

thf('28',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ( v3_tops_1 @ X22 @ X23 )
      | ~ ( v1_xboole_0 @ X22 )
      | ~ ( l1_pre_topc @ X23 )
      | ~ ( v2_pre_topc @ X23 ) ) ),
    inference(cnf,[status(esa)],[cc3_tops_1])).

thf('29',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( v3_tops_1 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('31',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v3_tops_1 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X12: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(t91_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v3_tops_1 @ B @ A )
           => ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) )).

thf('33',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) )
      | ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ X29 ) @ X28 ) @ X29 )
      | ~ ( v3_tops_1 @ X28 @ X29 )
      | ~ ( l1_pre_topc @ X29 ) ) ),
    inference(cnf,[status(esa)],[t91_tops_1])).

thf('34',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v3_tops_1 @ k1_xboole_0 @ X0 )
      | ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ X0 ) @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['10','15'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v3_tops_1 @ k1_xboole_0 @ X0 )
      | ( v1_tops_1 @ ( u1_struct_0 @ X0 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v1_tops_1 @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['31','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( v1_tops_1 @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,(
    ! [X7: $i] :
      ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X7 ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf(d3_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v1_tops_1 @ B @ A )
          <=> ( ( k2_pre_topc @ A @ B )
              = ( k2_struct_0 @ A ) ) ) ) ) )).

thf('40',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) )
      | ~ ( v1_tops_1 @ X24 @ X25 )
      | ( ( k2_pre_topc @ X25 @ X24 )
        = ( k2_struct_0 @ X25 ) )
      | ~ ( l1_pre_topc @ X25 ) ) ),
    inference(cnf,[status(esa)],[d3_tops_1])).

thf('41',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( k2_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) )
        = ( k2_struct_0 @ X0 ) )
      | ~ ( v1_tops_1 @ ( u1_struct_0 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( ( k2_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) )
        = ( k2_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['38','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( ( k2_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) )
        = ( k2_struct_0 @ X0 ) )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( ( u1_struct_0 @ X0 )
        = ( k2_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference('sup+',[status(thm)],['26','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( u1_struct_0 @ X0 )
        = ( k2_struct_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['44'])).

thf(t97_tops_1,conjecture,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( ( v3_pre_topc @ B @ A )
              & ( v3_tops_1 @ B @ A ) )
           => ( B = k1_xboole_0 ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( ( ( v3_pre_topc @ B @ A )
                & ( v3_tops_1 @ B @ A ) )
             => ( B = k1_xboole_0 ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t97_tops_1])).

thf('46',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('47',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k3_subset_1 @ X11 @ ( k3_subset_1 @ X11 @ X10 ) )
        = X10 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('48',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = sk_B ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k3_subset_1 @ X5 @ X6 )
        = ( k4_xboole_0 @ X5 @ X6 ) )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('51',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['48','51'])).

thf('53',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('54',plain,(
    ! [X8: $i,X9: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X8 @ X9 ) @ ( k1_zfmisc_1 @ X8 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('55',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('57',plain,(
    m1_subset_1 @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) )
      | ~ ( v1_tops_1 @ X24 @ X25 )
      | ( ( k2_pre_topc @ X25 @ X24 )
        = ( k2_struct_0 @ X25 ) )
      | ~ ( l1_pre_topc @ X25 ) ) ),
    inference(cnf,[status(esa)],[d3_tops_1])).

thf('59',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      = ( k2_struct_0 @ sk_A ) )
    | ~ ( v1_tops_1 @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      = ( k2_struct_0 @ sk_A ) )
    | ~ ( v1_tops_1 @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,(
    m1_subset_1 @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('63',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( v4_pre_topc @ X18 @ X19 )
      | ( ( k2_pre_topc @ X19 @ X18 )
        = X18 )
      | ~ ( l1_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('64',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    | ~ ( v4_pre_topc @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    | ~ ( v4_pre_topc @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
      | ~ ( v3_pre_topc @ X26 @ X27 )
      | ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ X27 ) @ X26 ) @ X27 )
      | ~ ( l1_pre_topc @ X27 ) ) ),
    inference(cnf,[status(esa)],[t30_tops_1])).

thf('69',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('72',plain,(
    v3_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    v4_pre_topc @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['69','70','71','72'])).

thf('74',plain,
    ( ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['66','73'])).

thf('75',plain,
    ( ( ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B )
      = ( k2_struct_0 @ sk_A ) )
    | ~ ( v1_tops_1 @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['61','74'])).

thf('76',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) )
      | ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ X29 ) @ X28 ) @ X29 )
      | ~ ( v3_tops_1 @ X28 @ X29 )
      | ~ ( l1_pre_topc @ X29 ) ) ),
    inference(cnf,[status(esa)],[t91_tops_1])).

thf('78',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v3_tops_1 @ sk_B @ sk_A )
    | ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    v3_tops_1 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('82',plain,(
    v1_tops_1 @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['78','79','80','81'])).

thf('83',plain,
    ( ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['75','82'])).

thf('84',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) )
    = sk_B ),
    inference(demod,[status(thm)],['52','83'])).

thf('85',plain,
    ( ( ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) )
      = sk_B )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A ) ),
    inference('sup+',[status(thm)],['45','84'])).

thf('86',plain,(
    ! [X12: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('87',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k3_subset_1 @ X11 @ ( k3_subset_1 @ X11 @ X10 ) )
        = X10 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('88',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ ( k3_subset_1 @ X0 @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['10','15'])).

thf('90',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['88','89'])).

thf('91',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    k1_xboole_0 = sk_B ),
    inference(demod,[status(thm)],['85','90','91','92'])).

thf('94',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['93','94'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.13/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.y5nJsTBO9D
% 0.14/0.36  % Computer   : n023.cluster.edu
% 0.14/0.36  % Model      : x86_64 x86_64
% 0.14/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.36  % Memory     : 8042.1875MB
% 0.14/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % DateTime   : Tue Dec  1 20:11:51 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.14/0.36  % Running portfolio for 600 s
% 0.14/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.37  % Number of cores: 8
% 0.14/0.37  % Python version: Python 3.6.8
% 0.14/0.37  % Running in FO mode
% 0.23/0.56  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.23/0.56  % Solved by: fo/fo7.sh
% 0.23/0.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.23/0.56  % done 248 iterations in 0.082s
% 0.23/0.56  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.23/0.56  % SZS output start Refutation
% 0.23/0.56  thf(sk_A_type, type, sk_A: $i).
% 0.23/0.56  thf(sk_B_type, type, sk_B: $i).
% 0.23/0.56  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.23/0.56  thf(v1_tops_1_type, type, v1_tops_1: $i > $i > $o).
% 0.23/0.56  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.23/0.56  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.23/0.56  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.23/0.56  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.23/0.56  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.23/0.56  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.23/0.56  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.23/0.56  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.23/0.56  thf(v3_tops_1_type, type, v3_tops_1: $i > $i > $o).
% 0.23/0.56  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.23/0.56  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.23/0.56  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.23/0.56  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.23/0.56  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.23/0.56  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.23/0.56  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.23/0.56  thf(t4_subset_1, axiom,
% 0.23/0.56    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.23/0.56  thf('0', plain,
% 0.23/0.56      (![X12 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X12))),
% 0.23/0.56      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.23/0.56  thf(cc1_tops_1, axiom,
% 0.23/0.56    (![A:$i]:
% 0.23/0.56     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.23/0.56       ( ![B:$i]:
% 0.23/0.56         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.23/0.56           ( ( v1_xboole_0 @ B ) => ( v3_pre_topc @ B @ A ) ) ) ) ))).
% 0.23/0.56  thf('1', plain,
% 0.23/0.56      (![X20 : $i, X21 : $i]:
% 0.23/0.56         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.23/0.56          | (v3_pre_topc @ X20 @ X21)
% 0.23/0.56          | ~ (v1_xboole_0 @ X20)
% 0.23/0.56          | ~ (l1_pre_topc @ X21)
% 0.23/0.56          | ~ (v2_pre_topc @ X21))),
% 0.23/0.56      inference('cnf', [status(esa)], [cc1_tops_1])).
% 0.23/0.56  thf('2', plain,
% 0.23/0.56      (![X0 : $i]:
% 0.23/0.56         (~ (v2_pre_topc @ X0)
% 0.23/0.56          | ~ (l1_pre_topc @ X0)
% 0.23/0.56          | ~ (v1_xboole_0 @ k1_xboole_0)
% 0.23/0.56          | (v3_pre_topc @ k1_xboole_0 @ X0))),
% 0.23/0.56      inference('sup-', [status(thm)], ['0', '1'])).
% 0.23/0.56  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.23/0.56  thf('3', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.23/0.56      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.23/0.56  thf('4', plain,
% 0.23/0.56      (![X0 : $i]:
% 0.23/0.56         (~ (v2_pre_topc @ X0)
% 0.23/0.56          | ~ (l1_pre_topc @ X0)
% 0.23/0.56          | (v3_pre_topc @ k1_xboole_0 @ X0))),
% 0.23/0.56      inference('demod', [status(thm)], ['2', '3'])).
% 0.23/0.56  thf('5', plain,
% 0.23/0.56      (![X12 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X12))),
% 0.23/0.56      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.23/0.56  thf(t30_tops_1, axiom,
% 0.23/0.56    (![A:$i]:
% 0.23/0.56     ( ( l1_pre_topc @ A ) =>
% 0.23/0.56       ( ![B:$i]:
% 0.23/0.56         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.23/0.56           ( ( v3_pre_topc @ B @ A ) <=>
% 0.23/0.56             ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) ))).
% 0.23/0.56  thf('6', plain,
% 0.23/0.56      (![X26 : $i, X27 : $i]:
% 0.23/0.56         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 0.23/0.56          | ~ (v3_pre_topc @ X26 @ X27)
% 0.23/0.56          | (v4_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ X27) @ X26) @ X27)
% 0.23/0.56          | ~ (l1_pre_topc @ X27))),
% 0.23/0.56      inference('cnf', [status(esa)], [t30_tops_1])).
% 0.23/0.56  thf('7', plain,
% 0.23/0.56      (![X0 : $i]:
% 0.23/0.56         (~ (l1_pre_topc @ X0)
% 0.23/0.56          | (v4_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ X0) @ k1_xboole_0) @ 
% 0.23/0.56             X0)
% 0.23/0.56          | ~ (v3_pre_topc @ k1_xboole_0 @ X0))),
% 0.23/0.56      inference('sup-', [status(thm)], ['5', '6'])).
% 0.23/0.56  thf('8', plain,
% 0.23/0.56      (![X12 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X12))),
% 0.23/0.56      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.23/0.56  thf(d5_subset_1, axiom,
% 0.23/0.56    (![A:$i,B:$i]:
% 0.23/0.56     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.23/0.56       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.23/0.56  thf('9', plain,
% 0.23/0.56      (![X5 : $i, X6 : $i]:
% 0.23/0.56         (((k3_subset_1 @ X5 @ X6) = (k4_xboole_0 @ X5 @ X6))
% 0.23/0.56          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X5)))),
% 0.23/0.56      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.23/0.56  thf('10', plain,
% 0.23/0.56      (![X0 : $i]:
% 0.23/0.56         ((k3_subset_1 @ X0 @ k1_xboole_0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 0.23/0.56      inference('sup-', [status(thm)], ['8', '9'])).
% 0.23/0.56  thf(t2_boole, axiom,
% 0.23/0.56    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.23/0.56  thf('11', plain,
% 0.23/0.56      (![X2 : $i]: ((k3_xboole_0 @ X2 @ k1_xboole_0) = (k1_xboole_0))),
% 0.23/0.56      inference('cnf', [status(esa)], [t2_boole])).
% 0.23/0.56  thf(t100_xboole_1, axiom,
% 0.23/0.56    (![A:$i,B:$i]:
% 0.23/0.56     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.23/0.56  thf('12', plain,
% 0.23/0.56      (![X0 : $i, X1 : $i]:
% 0.23/0.56         ((k4_xboole_0 @ X0 @ X1)
% 0.23/0.56           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.23/0.56      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.23/0.56  thf('13', plain,
% 0.23/0.56      (![X0 : $i]:
% 0.23/0.56         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.23/0.56      inference('sup+', [status(thm)], ['11', '12'])).
% 0.23/0.56  thf(t5_boole, axiom,
% 0.23/0.56    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.23/0.56  thf('14', plain, (![X3 : $i]: ((k5_xboole_0 @ X3 @ k1_xboole_0) = (X3))),
% 0.23/0.56      inference('cnf', [status(esa)], [t5_boole])).
% 0.23/0.56  thf('15', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.23/0.56      inference('sup+', [status(thm)], ['13', '14'])).
% 0.23/0.56  thf('16', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ k1_xboole_0) = (X0))),
% 0.23/0.56      inference('demod', [status(thm)], ['10', '15'])).
% 0.23/0.56  thf('17', plain,
% 0.23/0.56      (![X0 : $i]:
% 0.23/0.56         (~ (l1_pre_topc @ X0)
% 0.23/0.56          | (v4_pre_topc @ (u1_struct_0 @ X0) @ X0)
% 0.23/0.56          | ~ (v3_pre_topc @ k1_xboole_0 @ X0))),
% 0.23/0.56      inference('demod', [status(thm)], ['7', '16'])).
% 0.23/0.56  thf('18', plain,
% 0.23/0.56      (![X0 : $i]:
% 0.23/0.56         (~ (l1_pre_topc @ X0)
% 0.23/0.56          | ~ (v2_pre_topc @ X0)
% 0.23/0.56          | (v4_pre_topc @ (u1_struct_0 @ X0) @ X0)
% 0.23/0.56          | ~ (l1_pre_topc @ X0))),
% 0.23/0.56      inference('sup-', [status(thm)], ['4', '17'])).
% 0.23/0.56  thf('19', plain,
% 0.23/0.56      (![X0 : $i]:
% 0.23/0.56         ((v4_pre_topc @ (u1_struct_0 @ X0) @ X0)
% 0.23/0.56          | ~ (v2_pre_topc @ X0)
% 0.23/0.56          | ~ (l1_pre_topc @ X0))),
% 0.23/0.56      inference('simplify', [status(thm)], ['18'])).
% 0.23/0.56  thf(dt_k2_subset_1, axiom,
% 0.23/0.56    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.23/0.56  thf('20', plain,
% 0.23/0.56      (![X7 : $i]: (m1_subset_1 @ (k2_subset_1 @ X7) @ (k1_zfmisc_1 @ X7))),
% 0.23/0.56      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 0.23/0.56  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.23/0.56  thf('21', plain, (![X4 : $i]: ((k2_subset_1 @ X4) = (X4))),
% 0.23/0.56      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.23/0.56  thf('22', plain, (![X7 : $i]: (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X7))),
% 0.23/0.56      inference('demod', [status(thm)], ['20', '21'])).
% 0.23/0.56  thf(t52_pre_topc, axiom,
% 0.23/0.56    (![A:$i]:
% 0.23/0.56     ( ( l1_pre_topc @ A ) =>
% 0.23/0.56       ( ![B:$i]:
% 0.23/0.56         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.23/0.56           ( ( ( v4_pre_topc @ B @ A ) => ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) & 
% 0.23/0.56             ( ( ( v2_pre_topc @ A ) & ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) =>
% 0.23/0.56               ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 0.23/0.56  thf('23', plain,
% 0.23/0.56      (![X18 : $i, X19 : $i]:
% 0.23/0.56         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.23/0.56          | ~ (v4_pre_topc @ X18 @ X19)
% 0.23/0.56          | ((k2_pre_topc @ X19 @ X18) = (X18))
% 0.23/0.56          | ~ (l1_pre_topc @ X19))),
% 0.23/0.56      inference('cnf', [status(esa)], [t52_pre_topc])).
% 0.23/0.56  thf('24', plain,
% 0.23/0.56      (![X0 : $i]:
% 0.23/0.56         (~ (l1_pre_topc @ X0)
% 0.23/0.56          | ((k2_pre_topc @ X0 @ (u1_struct_0 @ X0)) = (u1_struct_0 @ X0))
% 0.23/0.56          | ~ (v4_pre_topc @ (u1_struct_0 @ X0) @ X0))),
% 0.23/0.56      inference('sup-', [status(thm)], ['22', '23'])).
% 0.23/0.56  thf('25', plain,
% 0.23/0.56      (![X0 : $i]:
% 0.23/0.56         (~ (l1_pre_topc @ X0)
% 0.23/0.56          | ~ (v2_pre_topc @ X0)
% 0.23/0.56          | ((k2_pre_topc @ X0 @ (u1_struct_0 @ X0)) = (u1_struct_0 @ X0))
% 0.23/0.56          | ~ (l1_pre_topc @ X0))),
% 0.23/0.56      inference('sup-', [status(thm)], ['19', '24'])).
% 0.23/0.56  thf('26', plain,
% 0.23/0.56      (![X0 : $i]:
% 0.23/0.56         (((k2_pre_topc @ X0 @ (u1_struct_0 @ X0)) = (u1_struct_0 @ X0))
% 0.23/0.56          | ~ (v2_pre_topc @ X0)
% 0.23/0.56          | ~ (l1_pre_topc @ X0))),
% 0.23/0.56      inference('simplify', [status(thm)], ['25'])).
% 0.23/0.56  thf('27', plain,
% 0.23/0.56      (![X12 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X12))),
% 0.23/0.56      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.23/0.56  thf(cc3_tops_1, axiom,
% 0.23/0.56    (![A:$i]:
% 0.23/0.56     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.23/0.56       ( ![B:$i]:
% 0.23/0.56         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.23/0.56           ( ( v1_xboole_0 @ B ) => ( v3_tops_1 @ B @ A ) ) ) ) ))).
% 0.23/0.56  thf('28', plain,
% 0.23/0.56      (![X22 : $i, X23 : $i]:
% 0.23/0.56         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 0.23/0.56          | (v3_tops_1 @ X22 @ X23)
% 0.23/0.56          | ~ (v1_xboole_0 @ X22)
% 0.23/0.56          | ~ (l1_pre_topc @ X23)
% 0.23/0.56          | ~ (v2_pre_topc @ X23))),
% 0.23/0.56      inference('cnf', [status(esa)], [cc3_tops_1])).
% 0.23/0.56  thf('29', plain,
% 0.23/0.56      (![X0 : $i]:
% 0.23/0.56         (~ (v2_pre_topc @ X0)
% 0.23/0.56          | ~ (l1_pre_topc @ X0)
% 0.23/0.56          | ~ (v1_xboole_0 @ k1_xboole_0)
% 0.23/0.56          | (v3_tops_1 @ k1_xboole_0 @ X0))),
% 0.23/0.56      inference('sup-', [status(thm)], ['27', '28'])).
% 0.23/0.56  thf('30', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.23/0.56      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.23/0.56  thf('31', plain,
% 0.23/0.56      (![X0 : $i]:
% 0.23/0.56         (~ (v2_pre_topc @ X0)
% 0.23/0.56          | ~ (l1_pre_topc @ X0)
% 0.23/0.56          | (v3_tops_1 @ k1_xboole_0 @ X0))),
% 0.23/0.56      inference('demod', [status(thm)], ['29', '30'])).
% 0.23/0.56  thf('32', plain,
% 0.23/0.56      (![X12 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X12))),
% 0.23/0.56      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.23/0.56  thf(t91_tops_1, axiom,
% 0.23/0.56    (![A:$i]:
% 0.23/0.56     ( ( l1_pre_topc @ A ) =>
% 0.23/0.56       ( ![B:$i]:
% 0.23/0.56         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.23/0.56           ( ( v3_tops_1 @ B @ A ) =>
% 0.23/0.56             ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) ))).
% 0.23/0.56  thf('33', plain,
% 0.23/0.56      (![X28 : $i, X29 : $i]:
% 0.23/0.56         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (u1_struct_0 @ X29)))
% 0.23/0.56          | (v1_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ X29) @ X28) @ X29)
% 0.23/0.56          | ~ (v3_tops_1 @ X28 @ X29)
% 0.23/0.56          | ~ (l1_pre_topc @ X29))),
% 0.23/0.56      inference('cnf', [status(esa)], [t91_tops_1])).
% 0.23/0.56  thf('34', plain,
% 0.23/0.56      (![X0 : $i]:
% 0.23/0.56         (~ (l1_pre_topc @ X0)
% 0.23/0.56          | ~ (v3_tops_1 @ k1_xboole_0 @ X0)
% 0.23/0.56          | (v1_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ X0) @ k1_xboole_0) @ X0))),
% 0.23/0.56      inference('sup-', [status(thm)], ['32', '33'])).
% 0.23/0.56  thf('35', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ k1_xboole_0) = (X0))),
% 0.23/0.56      inference('demod', [status(thm)], ['10', '15'])).
% 0.23/0.56  thf('36', plain,
% 0.23/0.56      (![X0 : $i]:
% 0.23/0.56         (~ (l1_pre_topc @ X0)
% 0.23/0.56          | ~ (v3_tops_1 @ k1_xboole_0 @ X0)
% 0.23/0.56          | (v1_tops_1 @ (u1_struct_0 @ X0) @ X0))),
% 0.23/0.56      inference('demod', [status(thm)], ['34', '35'])).
% 0.23/0.56  thf('37', plain,
% 0.23/0.56      (![X0 : $i]:
% 0.23/0.56         (~ (l1_pre_topc @ X0)
% 0.23/0.56          | ~ (v2_pre_topc @ X0)
% 0.23/0.56          | (v1_tops_1 @ (u1_struct_0 @ X0) @ X0)
% 0.23/0.56          | ~ (l1_pre_topc @ X0))),
% 0.23/0.56      inference('sup-', [status(thm)], ['31', '36'])).
% 0.23/0.56  thf('38', plain,
% 0.23/0.56      (![X0 : $i]:
% 0.23/0.56         ((v1_tops_1 @ (u1_struct_0 @ X0) @ X0)
% 0.23/0.56          | ~ (v2_pre_topc @ X0)
% 0.23/0.56          | ~ (l1_pre_topc @ X0))),
% 0.23/0.56      inference('simplify', [status(thm)], ['37'])).
% 0.23/0.56  thf('39', plain, (![X7 : $i]: (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X7))),
% 0.23/0.56      inference('demod', [status(thm)], ['20', '21'])).
% 0.23/0.56  thf(d3_tops_1, axiom,
% 0.23/0.56    (![A:$i]:
% 0.23/0.56     ( ( l1_pre_topc @ A ) =>
% 0.23/0.56       ( ![B:$i]:
% 0.23/0.56         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.23/0.56           ( ( v1_tops_1 @ B @ A ) <=>
% 0.23/0.56             ( ( k2_pre_topc @ A @ B ) = ( k2_struct_0 @ A ) ) ) ) ) ))).
% 0.23/0.56  thf('40', plain,
% 0.23/0.56      (![X24 : $i, X25 : $i]:
% 0.23/0.56         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 0.23/0.56          | ~ (v1_tops_1 @ X24 @ X25)
% 0.23/0.56          | ((k2_pre_topc @ X25 @ X24) = (k2_struct_0 @ X25))
% 0.23/0.56          | ~ (l1_pre_topc @ X25))),
% 0.23/0.56      inference('cnf', [status(esa)], [d3_tops_1])).
% 0.23/0.56  thf('41', plain,
% 0.23/0.56      (![X0 : $i]:
% 0.23/0.56         (~ (l1_pre_topc @ X0)
% 0.23/0.56          | ((k2_pre_topc @ X0 @ (u1_struct_0 @ X0)) = (k2_struct_0 @ X0))
% 0.23/0.56          | ~ (v1_tops_1 @ (u1_struct_0 @ X0) @ X0))),
% 0.23/0.56      inference('sup-', [status(thm)], ['39', '40'])).
% 0.23/0.56  thf('42', plain,
% 0.23/0.56      (![X0 : $i]:
% 0.23/0.56         (~ (l1_pre_topc @ X0)
% 0.23/0.56          | ~ (v2_pre_topc @ X0)
% 0.23/0.56          | ((k2_pre_topc @ X0 @ (u1_struct_0 @ X0)) = (k2_struct_0 @ X0))
% 0.23/0.56          | ~ (l1_pre_topc @ X0))),
% 0.23/0.56      inference('sup-', [status(thm)], ['38', '41'])).
% 0.23/0.56  thf('43', plain,
% 0.23/0.56      (![X0 : $i]:
% 0.23/0.56         (((k2_pre_topc @ X0 @ (u1_struct_0 @ X0)) = (k2_struct_0 @ X0))
% 0.23/0.56          | ~ (v2_pre_topc @ X0)
% 0.23/0.56          | ~ (l1_pre_topc @ X0))),
% 0.23/0.56      inference('simplify', [status(thm)], ['42'])).
% 0.23/0.56  thf('44', plain,
% 0.23/0.56      (![X0 : $i]:
% 0.23/0.56         (((u1_struct_0 @ X0) = (k2_struct_0 @ X0))
% 0.23/0.56          | ~ (l1_pre_topc @ X0)
% 0.23/0.56          | ~ (v2_pre_topc @ X0)
% 0.23/0.56          | ~ (l1_pre_topc @ X0)
% 0.23/0.56          | ~ (v2_pre_topc @ X0))),
% 0.23/0.56      inference('sup+', [status(thm)], ['26', '43'])).
% 0.23/0.56  thf('45', plain,
% 0.23/0.56      (![X0 : $i]:
% 0.23/0.56         (~ (v2_pre_topc @ X0)
% 0.23/0.56          | ~ (l1_pre_topc @ X0)
% 0.23/0.56          | ((u1_struct_0 @ X0) = (k2_struct_0 @ X0)))),
% 0.23/0.56      inference('simplify', [status(thm)], ['44'])).
% 0.23/0.56  thf(t97_tops_1, conjecture,
% 0.23/0.56    (![A:$i]:
% 0.23/0.56     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.23/0.56       ( ![B:$i]:
% 0.23/0.56         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.23/0.56           ( ( ( v3_pre_topc @ B @ A ) & ( v3_tops_1 @ B @ A ) ) =>
% 0.23/0.56             ( ( B ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 0.23/0.56  thf(zf_stmt_0, negated_conjecture,
% 0.23/0.56    (~( ![A:$i]:
% 0.23/0.56        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.23/0.56          ( ![B:$i]:
% 0.23/0.56            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.23/0.56              ( ( ( v3_pre_topc @ B @ A ) & ( v3_tops_1 @ B @ A ) ) =>
% 0.23/0.56                ( ( B ) = ( k1_xboole_0 ) ) ) ) ) ) )),
% 0.23/0.56    inference('cnf.neg', [status(esa)], [t97_tops_1])).
% 0.23/0.56  thf('46', plain,
% 0.23/0.56      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.23/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.56  thf(involutiveness_k3_subset_1, axiom,
% 0.23/0.56    (![A:$i,B:$i]:
% 0.23/0.56     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.23/0.56       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 0.23/0.56  thf('47', plain,
% 0.23/0.56      (![X10 : $i, X11 : $i]:
% 0.23/0.56         (((k3_subset_1 @ X11 @ (k3_subset_1 @ X11 @ X10)) = (X10))
% 0.23/0.56          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11)))),
% 0.23/0.56      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.23/0.56  thf('48', plain,
% 0.23/0.56      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.23/0.56         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)) = (sk_B))),
% 0.23/0.56      inference('sup-', [status(thm)], ['46', '47'])).
% 0.23/0.56  thf('49', plain,
% 0.23/0.56      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.23/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.56  thf('50', plain,
% 0.23/0.56      (![X5 : $i, X6 : $i]:
% 0.23/0.56         (((k3_subset_1 @ X5 @ X6) = (k4_xboole_0 @ X5 @ X6))
% 0.23/0.56          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X5)))),
% 0.23/0.56      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.23/0.56  thf('51', plain,
% 0.23/0.56      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 0.23/0.56         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 0.23/0.56      inference('sup-', [status(thm)], ['49', '50'])).
% 0.23/0.56  thf('52', plain,
% 0.23/0.56      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.23/0.56         (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)) = (sk_B))),
% 0.23/0.56      inference('demod', [status(thm)], ['48', '51'])).
% 0.23/0.56  thf('53', plain,
% 0.23/0.56      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.23/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.56  thf(dt_k3_subset_1, axiom,
% 0.23/0.56    (![A:$i,B:$i]:
% 0.23/0.56     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.23/0.56       ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.23/0.56  thf('54', plain,
% 0.23/0.56      (![X8 : $i, X9 : $i]:
% 0.23/0.56         ((m1_subset_1 @ (k3_subset_1 @ X8 @ X9) @ (k1_zfmisc_1 @ X8))
% 0.23/0.56          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X8)))),
% 0.23/0.56      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 0.23/0.56  thf('55', plain,
% 0.23/0.56      ((m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.23/0.56        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.23/0.56      inference('sup-', [status(thm)], ['53', '54'])).
% 0.23/0.56  thf('56', plain,
% 0.23/0.56      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 0.23/0.56         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 0.23/0.56      inference('sup-', [status(thm)], ['49', '50'])).
% 0.23/0.56  thf('57', plain,
% 0.23/0.56      ((m1_subset_1 @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.23/0.56        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.23/0.56      inference('demod', [status(thm)], ['55', '56'])).
% 0.23/0.56  thf('58', plain,
% 0.23/0.56      (![X24 : $i, X25 : $i]:
% 0.23/0.56         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 0.23/0.56          | ~ (v1_tops_1 @ X24 @ X25)
% 0.23/0.56          | ((k2_pre_topc @ X25 @ X24) = (k2_struct_0 @ X25))
% 0.23/0.56          | ~ (l1_pre_topc @ X25))),
% 0.23/0.56      inference('cnf', [status(esa)], [d3_tops_1])).
% 0.23/0.56  thf('59', plain,
% 0.23/0.56      ((~ (l1_pre_topc @ sk_A)
% 0.23/0.56        | ((k2_pre_topc @ sk_A @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.23/0.56            = (k2_struct_0 @ sk_A))
% 0.23/0.56        | ~ (v1_tops_1 @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A))),
% 0.23/0.56      inference('sup-', [status(thm)], ['57', '58'])).
% 0.23/0.56  thf('60', plain, ((l1_pre_topc @ sk_A)),
% 0.23/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.56  thf('61', plain,
% 0.23/0.56      ((((k2_pre_topc @ sk_A @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.23/0.56          = (k2_struct_0 @ sk_A))
% 0.23/0.56        | ~ (v1_tops_1 @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A))),
% 0.23/0.56      inference('demod', [status(thm)], ['59', '60'])).
% 0.23/0.56  thf('62', plain,
% 0.23/0.56      ((m1_subset_1 @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.23/0.56        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.23/0.56      inference('demod', [status(thm)], ['55', '56'])).
% 0.23/0.56  thf('63', plain,
% 0.23/0.56      (![X18 : $i, X19 : $i]:
% 0.23/0.56         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.23/0.56          | ~ (v4_pre_topc @ X18 @ X19)
% 0.23/0.56          | ((k2_pre_topc @ X19 @ X18) = (X18))
% 0.23/0.56          | ~ (l1_pre_topc @ X19))),
% 0.23/0.56      inference('cnf', [status(esa)], [t52_pre_topc])).
% 0.23/0.56  thf('64', plain,
% 0.23/0.56      ((~ (l1_pre_topc @ sk_A)
% 0.23/0.56        | ((k2_pre_topc @ sk_A @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.23/0.56            = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.23/0.56        | ~ (v4_pre_topc @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A))),
% 0.23/0.56      inference('sup-', [status(thm)], ['62', '63'])).
% 0.23/0.56  thf('65', plain, ((l1_pre_topc @ sk_A)),
% 0.23/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.56  thf('66', plain,
% 0.23/0.56      ((((k2_pre_topc @ sk_A @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.23/0.56          = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.23/0.56        | ~ (v4_pre_topc @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A))),
% 0.23/0.56      inference('demod', [status(thm)], ['64', '65'])).
% 0.23/0.56  thf('67', plain,
% 0.23/0.56      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.23/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.56  thf('68', plain,
% 0.23/0.56      (![X26 : $i, X27 : $i]:
% 0.23/0.56         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 0.23/0.56          | ~ (v3_pre_topc @ X26 @ X27)
% 0.23/0.56          | (v4_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ X27) @ X26) @ X27)
% 0.23/0.56          | ~ (l1_pre_topc @ X27))),
% 0.23/0.56      inference('cnf', [status(esa)], [t30_tops_1])).
% 0.23/0.56  thf('69', plain,
% 0.23/0.56      ((~ (l1_pre_topc @ sk_A)
% 0.23/0.56        | (v4_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 0.23/0.56        | ~ (v3_pre_topc @ sk_B @ sk_A))),
% 0.23/0.56      inference('sup-', [status(thm)], ['67', '68'])).
% 0.23/0.56  thf('70', plain, ((l1_pre_topc @ sk_A)),
% 0.23/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.56  thf('71', plain,
% 0.23/0.56      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 0.23/0.56         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 0.23/0.56      inference('sup-', [status(thm)], ['49', '50'])).
% 0.23/0.56  thf('72', plain, ((v3_pre_topc @ sk_B @ sk_A)),
% 0.23/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.56  thf('73', plain,
% 0.23/0.56      ((v4_pre_topc @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)),
% 0.23/0.56      inference('demod', [status(thm)], ['69', '70', '71', '72'])).
% 0.23/0.56  thf('74', plain,
% 0.23/0.56      (((k2_pre_topc @ sk_A @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.23/0.56         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 0.23/0.56      inference('demod', [status(thm)], ['66', '73'])).
% 0.23/0.56  thf('75', plain,
% 0.23/0.56      ((((k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B) = (k2_struct_0 @ sk_A))
% 0.23/0.56        | ~ (v1_tops_1 @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A))),
% 0.23/0.56      inference('demod', [status(thm)], ['61', '74'])).
% 0.23/0.56  thf('76', plain,
% 0.23/0.56      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.23/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.56  thf('77', plain,
% 0.23/0.56      (![X28 : $i, X29 : $i]:
% 0.23/0.56         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (u1_struct_0 @ X29)))
% 0.23/0.56          | (v1_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ X29) @ X28) @ X29)
% 0.23/0.56          | ~ (v3_tops_1 @ X28 @ X29)
% 0.23/0.56          | ~ (l1_pre_topc @ X29))),
% 0.23/0.56      inference('cnf', [status(esa)], [t91_tops_1])).
% 0.23/0.56  thf('78', plain,
% 0.23/0.56      ((~ (l1_pre_topc @ sk_A)
% 0.23/0.56        | ~ (v3_tops_1 @ sk_B @ sk_A)
% 0.23/0.56        | (v1_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A))),
% 0.23/0.56      inference('sup-', [status(thm)], ['76', '77'])).
% 0.23/0.56  thf('79', plain, ((l1_pre_topc @ sk_A)),
% 0.23/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.56  thf('80', plain, ((v3_tops_1 @ sk_B @ sk_A)),
% 0.23/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.56  thf('81', plain,
% 0.23/0.56      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 0.23/0.56         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 0.23/0.56      inference('sup-', [status(thm)], ['49', '50'])).
% 0.23/0.56  thf('82', plain,
% 0.23/0.56      ((v1_tops_1 @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)),
% 0.23/0.56      inference('demod', [status(thm)], ['78', '79', '80', '81'])).
% 0.23/0.56  thf('83', plain,
% 0.23/0.56      (((k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B) = (k2_struct_0 @ sk_A))),
% 0.23/0.56      inference('demod', [status(thm)], ['75', '82'])).
% 0.23/0.56  thf('84', plain,
% 0.23/0.56      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A)) = (sk_B))),
% 0.23/0.56      inference('demod', [status(thm)], ['52', '83'])).
% 0.23/0.56  thf('85', plain,
% 0.23/0.56      ((((k3_subset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A)) = (sk_B))
% 0.23/0.56        | ~ (l1_pre_topc @ sk_A)
% 0.23/0.56        | ~ (v2_pre_topc @ sk_A))),
% 0.23/0.56      inference('sup+', [status(thm)], ['45', '84'])).
% 0.23/0.56  thf('86', plain,
% 0.23/0.56      (![X12 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X12))),
% 0.23/0.56      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.23/0.56  thf('87', plain,
% 0.23/0.56      (![X10 : $i, X11 : $i]:
% 0.23/0.56         (((k3_subset_1 @ X11 @ (k3_subset_1 @ X11 @ X10)) = (X10))
% 0.23/0.56          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11)))),
% 0.23/0.56      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.23/0.56  thf('88', plain,
% 0.23/0.56      (![X0 : $i]:
% 0.23/0.56         ((k3_subset_1 @ X0 @ (k3_subset_1 @ X0 @ k1_xboole_0)) = (k1_xboole_0))),
% 0.23/0.56      inference('sup-', [status(thm)], ['86', '87'])).
% 0.23/0.56  thf('89', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ k1_xboole_0) = (X0))),
% 0.23/0.56      inference('demod', [status(thm)], ['10', '15'])).
% 0.23/0.56  thf('90', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k1_xboole_0))),
% 0.23/0.56      inference('demod', [status(thm)], ['88', '89'])).
% 0.23/0.56  thf('91', plain, ((l1_pre_topc @ sk_A)),
% 0.23/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.56  thf('92', plain, ((v2_pre_topc @ sk_A)),
% 0.23/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.56  thf('93', plain, (((k1_xboole_0) = (sk_B))),
% 0.23/0.56      inference('demod', [status(thm)], ['85', '90', '91', '92'])).
% 0.23/0.56  thf('94', plain, (((sk_B) != (k1_xboole_0))),
% 0.23/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.56  thf('95', plain, ($false),
% 0.23/0.56      inference('simplify_reflect-', [status(thm)], ['93', '94'])).
% 0.23/0.56  
% 0.23/0.56  % SZS output end Refutation
% 0.23/0.56  
% 0.41/0.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
