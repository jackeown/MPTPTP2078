%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ZeJPYVYsgj

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:14 EST 2020

% Result     : Theorem 5.79s
% Output     : Refutation 5.79s
% Verified   : 
% Statistics : Number of formulae       :  218 (1298 expanded)
%              Number of leaves         :   40 ( 433 expanded)
%              Depth                    :   22
%              Number of atoms          : 1768 (10571 expanded)
%              Number of equality atoms :  108 ( 674 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(t69_tops_1,conjecture,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v4_pre_topc @ B @ A )
           => ( r1_tarski @ ( k2_tops_1 @ A @ B ) @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_pre_topc @ A )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( ( v4_pre_topc @ B @ A )
             => ( r1_tarski @ ( k2_tops_1 @ A @ B ) @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t69_tops_1])).

thf('0',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_tops_1 @ A @ B )
            = ( k9_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ ( k2_pre_topc @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) )).

thf('1',plain,(
    ! [X53: $i,X54: $i] :
      ( ~ ( m1_subset_1 @ X53 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X54 ) ) )
      | ( ( k2_tops_1 @ X54 @ X53 )
        = ( k9_subset_1 @ ( u1_struct_0 @ X54 ) @ ( k2_pre_topc @ X54 @ X53 ) @ ( k2_pre_topc @ X54 @ ( k3_subset_1 @ ( u1_struct_0 @ X54 ) @ X53 ) ) ) )
      | ~ ( l1_pre_topc @ X54 ) ) ),
    inference(cnf,[status(esa)],[d2_tops_1])).

thf('2',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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

thf('5',plain,(
    ! [X51: $i,X52: $i] :
      ( ~ ( m1_subset_1 @ X51 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X52 ) ) )
      | ~ ( v4_pre_topc @ X51 @ X52 )
      | ( ( k2_pre_topc @ X52 @ X51 )
        = X51 )
      | ~ ( l1_pre_topc @ X52 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('6',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
      = sk_B )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    v4_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = sk_B ),
    inference(demod,[status(thm)],['6','7','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('11',plain,(
    ! [X33: $i,X34: $i] :
      ( ( ( k3_subset_1 @ X33 @ X34 )
        = ( k4_xboole_0 @ X33 @ X34 ) )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('12',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['2','3','9','12'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('15',plain,(
    ! [X19: $i,X20: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X19 @ X20 ) @ X19 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(t44_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('16',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( r1_tarski @ X25 @ ( k2_xboole_0 @ X26 @ X27 ) )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ X25 @ X26 ) @ X27 ) ) ),
    inference(cnf,[status(esa)],[t44_xboole_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('19',plain,(
    ! [X44: $i,X45: $i] :
      ( ( r1_tarski @ X44 @ X45 )
      | ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ X45 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('20',plain,(
    r1_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('21',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( r1_tarski @ X15 @ X16 )
      | ~ ( r1_tarski @ X16 @ X17 )
      | ( r1_tarski @ X15 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ~ ( r1_tarski @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( r1_tarski @ sk_B @ ( k2_xboole_0 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['17','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( r1_tarski @ sk_B @ ( k2_xboole_0 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['14','23'])).

thf(t43_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) )
     => ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ) )).

thf('25',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X22 @ X23 ) @ X24 )
      | ~ ( r1_tarski @ X22 @ ( k2_xboole_0 @ X23 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t43_xboole_1])).

thf('26',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ X0 ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('27',plain,(
    ! [X18: $i] :
      ( r1_tarski @ k1_xboole_0 @ X18 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('28',plain,(
    ! [X8: $i,X10: $i] :
      ( ( X8 = X10 )
      | ~ ( r1_tarski @ X10 @ X8 )
      | ~ ( r1_tarski @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('29',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,
    ( ( k4_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['26','29'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('31',plain,(
    ! [X28: $i,X29: $i] :
      ( ( k4_xboole_0 @ X28 @ ( k4_xboole_0 @ X28 @ X29 ) )
      = ( k3_xboole_0 @ X28 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('32',plain,
    ( ( k4_xboole_0 @ sk_B @ k1_xboole_0 )
    = ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('33',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('34',plain,(
    ! [X13: $i,X14: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X13 @ X14 ) @ X13 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('38',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ X12 )
      = ( k5_xboole_0 @ X11 @ ( k3_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,
    ( ( k5_xboole_0 @ sk_B @ k1_xboole_0 )
    = ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['32','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('42',plain,(
    ! [X21: $i] :
      ( ( k4_xboole_0 @ X21 @ k1_xboole_0 )
      = X21 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('44',plain,
    ( sk_B
    = ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['40','43'])).

thf('45',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('46',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ X12 )
      = ( k5_xboole_0 @ X11 @ ( k3_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('48',plain,
    ( ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['44','47'])).

thf('49',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_pre_topc @ sk_A @ ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['13','48'])).

thf('50',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k9_subset_1 @ A @ C @ B ) ) ) )).

thf('51',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( ( k9_subset_1 @ X30 @ X32 @ X31 )
        = ( k9_subset_1 @ X30 @ X31 @ X32 ) )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k9_subset_1])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_B )
      = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k9_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('54',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ( m1_subset_1 @ ( k9_subset_1 @ X35 @ X36 @ X37 ) @ ( k1_zfmisc_1 @ X35 ) )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k9_subset_1])).

thf('55',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['52','55'])).

thf('57',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['49','56'])).

thf('58',plain,(
    ! [X33: $i,X34: $i] :
      ( ( ( k3_subset_1 @ X33 @ X34 )
        = ( k4_xboole_0 @ X33 @ X34 ) )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('59',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(t31_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ( r1_tarski @ B @ C )
          <=> ( r1_tarski @ ( k3_subset_1 @ A @ C ) @ ( k3_subset_1 @ A @ B ) ) ) ) ) )).

thf('61',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ X39 ) )
      | ~ ( r1_tarski @ ( k3_subset_1 @ X39 @ X38 ) @ ( k3_subset_1 @ X39 @ X40 ) )
      | ( r1_tarski @ X40 @ X38 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ X39 ) ) ) ),
    inference(cnf,[status(esa)],[t31_subset_1])).

thf('62',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ X0 @ sk_B )
      | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ X0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,
    ( ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['44','47'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ X0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,
    ( ~ ( r1_tarski @ ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
    | ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
    | ~ ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['59','66'])).

thf('68',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['49','56'])).

thf('69',plain,
    ( ~ ( r1_tarski @ ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
    | ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('70',plain,(
    ~ ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    ~ ( r1_tarski @ ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['69','70'])).

thf('72',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_pre_topc @ sk_A @ ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['13','48'])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_B )
      = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('74',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('75',plain,(
    ! [X44: $i,X45: $i] :
      ( ( r1_tarski @ X44 @ X45 )
      | ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ X45 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('76',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['73','76'])).

thf('78',plain,(
    r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['72','77'])).

thf('79',plain,(
    ! [X21: $i] :
      ( ( k4_xboole_0 @ X21 @ k1_xboole_0 )
      = X21 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('80',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_tarski @ X8 @ X9 )
      | ( X8 != X9 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('81',plain,(
    ! [X9: $i] :
      ( r1_tarski @ X9 @ X9 ) ),
    inference(simplify,[status(thm)],['80'])).

thf('82',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X22 @ X23 ) @ X24 )
      | ~ ( r1_tarski @ X22 @ ( k2_xboole_0 @ X23 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t43_xboole_1])).

thf('83',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 ) @ X0 ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ k1_xboole_0 @ X0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['79','83'])).

thf('85',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('86',plain,(
    ! [X8: $i,X10: $i] :
      ( ( X8 = X10 )
      | ~ ( r1_tarski @ X10 @ X8 )
      | ~ ( r1_tarski @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('87',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 )
      | ( ( k2_xboole_0 @ X1 @ X0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['84','87'])).

thf('89',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('90',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['88','89'])).

thf('91',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X22 @ X23 ) @ X24 )
      | ~ ( r1_tarski @ X22 @ ( k2_xboole_0 @ X23 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t43_xboole_1])).

thf('92',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ X0 )
      | ( r1_tarski @ ( k4_xboole_0 @ X1 @ X0 ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,(
    r1_tarski @ ( k4_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['78','92'])).

thf('94',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('95',plain,
    ( ( k4_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,(
    ! [X28: $i,X29: $i] :
      ( ( k4_xboole_0 @ X28 @ ( k4_xboole_0 @ X28 @ X29 ) )
      = ( k3_xboole_0 @ X28 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('97',plain,
    ( ( k4_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ k1_xboole_0 )
    = ( k3_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['95','96'])).

thf('98',plain,(
    ! [X21: $i] :
      ( ( k4_xboole_0 @ X21 @ k1_xboole_0 )
      = X21 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('99',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('100',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k3_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['97','98','99'])).

thf('101',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ X12 )
      = ( k5_xboole_0 @ X11 @ ( k3_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('102',plain,
    ( ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['100','101'])).

thf('103',plain,(
    ~ ( r1_tarski @ ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['71','102'])).

thf('104',plain,(
    ! [X9: $i] :
      ( r1_tarski @ X9 @ X9 ) ),
    inference(simplify,[status(thm)],['80'])).

thf('105',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( r1_tarski @ X25 @ ( k2_xboole_0 @ X26 @ X27 ) )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ X25 @ X26 ) @ X27 ) ) ),
    inference(cnf,[status(esa)],[t44_xboole_1])).

thf('106',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X1 @ ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['104','105'])).

thf('107',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ~ ( r1_tarski @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('108',plain,(
    ! [X0: $i] :
      ( r1_tarski @ sk_B @ ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf('109',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('110',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X22 @ X23 ) @ X24 )
      | ~ ( r1_tarski @ X22 @ ( k2_xboole_0 @ X23 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t43_xboole_1])).

thf('111',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) )
      | ( r1_tarski @ ( k4_xboole_0 @ X2 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['109','110'])).

thf('112',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ sk_B @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) @ X0 ) ),
    inference('sup-',[status(thm)],['108','111'])).

thf('113',plain,(
    ! [X44: $i,X46: $i] :
      ( ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ X46 ) )
      | ~ ( r1_tarski @ X44 @ X46 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('114',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ sk_B @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['112','113'])).

thf('115',plain,
    ( ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['44','47'])).

thf('116',plain,(
    ! [X19: $i,X20: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X19 @ X20 ) @ X19 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('117',plain,(
    ! [X44: $i,X46: $i] :
      ( ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ X46 ) )
      | ~ ( r1_tarski @ X44 @ X46 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('118',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['116','117'])).

thf('119',plain,(
    m1_subset_1 @ ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['115','118'])).

thf(dt_k2_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('120',plain,(
    ! [X49: $i,X50: $i] :
      ( ~ ( l1_pre_topc @ X49 )
      | ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X49 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X49 @ X50 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X49 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('121',plain,
    ( ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['119','120'])).

thf('122',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['121','122'])).

thf(t42_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( r1_tarski @ ( k3_subset_1 @ A @ B ) @ ( k3_subset_1 @ A @ ( k9_subset_1 @ A @ B @ C ) ) ) ) ) )).

thf('124',plain,(
    ! [X41: $i,X42: $i,X43: $i] :
      ( ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ X42 ) )
      | ( r1_tarski @ ( k3_subset_1 @ X42 @ X43 ) @ ( k3_subset_1 @ X42 @ ( k9_subset_1 @ X42 @ X43 @ X41 ) ) )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ X42 ) ) ) ),
    inference(cnf,[status(esa)],[t42_subset_1])).

thf('125',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ ( k2_pre_topc @ sk_A @ ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['123','124'])).

thf('126',plain,(
    r1_tarski @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k4_xboole_0 @ sk_B @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k4_xboole_0 @ sk_B @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) @ ( k2_pre_topc @ sk_A @ ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['114','125'])).

thf('127',plain,(
    ! [X21: $i] :
      ( ( k4_xboole_0 @ X21 @ k1_xboole_0 )
      = X21 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('128',plain,(
    ! [X28: $i,X29: $i] :
      ( ( k4_xboole_0 @ X28 @ ( k4_xboole_0 @ X28 @ X29 ) )
      = ( k3_xboole_0 @ X28 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('129',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['127','128'])).

thf('130',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('131',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['129','130'])).

thf('132',plain,(
    ! [X28: $i,X29: $i] :
      ( ( k4_xboole_0 @ X28 @ ( k4_xboole_0 @ X28 @ X29 ) )
      = ( k3_xboole_0 @ X28 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('133',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['131','132'])).

thf('134',plain,(
    ! [X21: $i] :
      ( ( k4_xboole_0 @ X21 @ k1_xboole_0 )
      = X21 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('135',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['133','134'])).

thf('136',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ X12 )
      = ( k5_xboole_0 @ X11 @ ( k3_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('137',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['135','136'])).

thf('138',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['129','130'])).

thf('139',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['135','136'])).

thf('140',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['138','139'])).

thf('141',plain,(
    ! [X21: $i] :
      ( ( k4_xboole_0 @ X21 @ k1_xboole_0 )
      = X21 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('142',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('143',plain,
    ( ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['44','47'])).

thf('144',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['142','143'])).

thf('145',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['135','136'])).

thf('146',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['138','139'])).

thf('147',plain,(
    ! [X21: $i] :
      ( ( k4_xboole_0 @ X21 @ k1_xboole_0 )
      = X21 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('148',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_pre_topc @ sk_A @ ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['13','48'])).

thf('149',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k3_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['97','98','99'])).

thf('150',plain,(
    ! [X13: $i,X14: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X13 @ X14 ) @ X13 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('151',plain,(
    ! [X44: $i,X46: $i] :
      ( ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ X46 ) )
      | ~ ( r1_tarski @ X44 @ X46 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('152',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['150','151'])).

thf('153',plain,(
    ! [X33: $i,X34: $i] :
      ( ( ( k3_subset_1 @ X33 @ X34 )
        = ( k4_xboole_0 @ X33 @ X34 ) )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('154',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['152','153'])).

thf('155',plain,(
    ! [X13: $i,X14: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X13 @ X14 ) @ X13 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('156',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X22 @ X23 ) @ X24 )
      | ~ ( r1_tarski @ X22 @ ( k2_xboole_0 @ X23 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t43_xboole_1])).

thf('157',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ ( k3_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 ) @ X1 ) @ X0 ) ),
    inference('sup-',[status(thm)],['155','156'])).

thf('158',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('159',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ ( k2_xboole_0 @ X0 @ k1_xboole_0 ) @ X1 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['157','158'])).

thf('160',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['88','89'])).

thf('161',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['159','160'])).

thf('162',plain,(
    ! [X28: $i,X29: $i] :
      ( ( k4_xboole_0 @ X28 @ ( k4_xboole_0 @ X28 @ X29 ) )
      = ( k3_xboole_0 @ X28 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('163',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ k1_xboole_0 )
      = ( k3_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['161','162'])).

thf('164',plain,(
    ! [X21: $i] :
      ( ( k4_xboole_0 @ X21 @ k1_xboole_0 )
      = X21 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('165',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('166',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ X1 )
      = ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['163','164','165'])).

thf('167',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ X12 )
      = ( k5_xboole_0 @ X11 @ ( k3_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('168',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['166','167'])).

thf('169',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ X12 )
      = ( k5_xboole_0 @ X11 @ ( k3_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('170',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['168','169'])).

thf('171',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['154','170'])).

thf('172',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['149','171'])).

thf('173',plain,
    ( ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['100','101'])).

thf('174',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['172','173'])).

thf('175',plain,(
    r1_tarski @ ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['126','137','140','141','144','145','146','147','148','174'])).

thf('176',plain,(
    $false ),
    inference(demod,[status(thm)],['103','175'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ZeJPYVYsgj
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:50:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 5.79/6.00  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 5.79/6.00  % Solved by: fo/fo7.sh
% 5.79/6.00  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 5.79/6.00  % done 11267 iterations in 5.542s
% 5.79/6.00  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 5.79/6.00  % SZS output start Refutation
% 5.79/6.00  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 5.79/6.00  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 5.79/6.00  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 5.79/6.00  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 5.79/6.00  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 5.79/6.00  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 5.79/6.00  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 5.79/6.00  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 5.79/6.00  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 5.79/6.00  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 5.79/6.00  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 5.79/6.00  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 5.79/6.00  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 5.79/6.00  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 5.79/6.00  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 5.79/6.00  thf(sk_B_type, type, sk_B: $i).
% 5.79/6.00  thf(sk_A_type, type, sk_A: $i).
% 5.79/6.00  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 5.79/6.00  thf(t69_tops_1, conjecture,
% 5.79/6.00    (![A:$i]:
% 5.79/6.00     ( ( l1_pre_topc @ A ) =>
% 5.79/6.00       ( ![B:$i]:
% 5.79/6.00         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 5.79/6.00           ( ( v4_pre_topc @ B @ A ) =>
% 5.79/6.00             ( r1_tarski @ ( k2_tops_1 @ A @ B ) @ B ) ) ) ) ))).
% 5.79/6.00  thf(zf_stmt_0, negated_conjecture,
% 5.79/6.00    (~( ![A:$i]:
% 5.79/6.00        ( ( l1_pre_topc @ A ) =>
% 5.79/6.00          ( ![B:$i]:
% 5.79/6.00            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 5.79/6.00              ( ( v4_pre_topc @ B @ A ) =>
% 5.79/6.00                ( r1_tarski @ ( k2_tops_1 @ A @ B ) @ B ) ) ) ) ) )),
% 5.79/6.00    inference('cnf.neg', [status(esa)], [t69_tops_1])).
% 5.79/6.00  thf('0', plain,
% 5.79/6.00      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 5.79/6.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.79/6.00  thf(d2_tops_1, axiom,
% 5.79/6.00    (![A:$i]:
% 5.79/6.00     ( ( l1_pre_topc @ A ) =>
% 5.79/6.00       ( ![B:$i]:
% 5.79/6.00         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 5.79/6.00           ( ( k2_tops_1 @ A @ B ) =
% 5.79/6.00             ( k9_subset_1 @
% 5.79/6.00               ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 5.79/6.00               ( k2_pre_topc @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) ))).
% 5.79/6.00  thf('1', plain,
% 5.79/6.00      (![X53 : $i, X54 : $i]:
% 5.79/6.00         (~ (m1_subset_1 @ X53 @ (k1_zfmisc_1 @ (u1_struct_0 @ X54)))
% 5.79/6.00          | ((k2_tops_1 @ X54 @ X53)
% 5.79/6.00              = (k9_subset_1 @ (u1_struct_0 @ X54) @ 
% 5.79/6.00                 (k2_pre_topc @ X54 @ X53) @ 
% 5.79/6.00                 (k2_pre_topc @ X54 @ (k3_subset_1 @ (u1_struct_0 @ X54) @ X53))))
% 5.79/6.00          | ~ (l1_pre_topc @ X54))),
% 5.79/6.00      inference('cnf', [status(esa)], [d2_tops_1])).
% 5.79/6.00  thf('2', plain,
% 5.79/6.00      ((~ (l1_pre_topc @ sk_A)
% 5.79/6.00        | ((k2_tops_1 @ sk_A @ sk_B)
% 5.79/6.00            = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 5.79/6.00               (k2_pre_topc @ sk_A @ sk_B) @ 
% 5.79/6.00               (k2_pre_topc @ sk_A @ 
% 5.79/6.00                (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)))))),
% 5.79/6.00      inference('sup-', [status(thm)], ['0', '1'])).
% 5.79/6.00  thf('3', plain, ((l1_pre_topc @ sk_A)),
% 5.79/6.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.79/6.00  thf('4', plain,
% 5.79/6.00      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 5.79/6.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.79/6.00  thf(t52_pre_topc, axiom,
% 5.79/6.00    (![A:$i]:
% 5.79/6.00     ( ( l1_pre_topc @ A ) =>
% 5.79/6.00       ( ![B:$i]:
% 5.79/6.00         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 5.79/6.00           ( ( ( v4_pre_topc @ B @ A ) => ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) & 
% 5.79/6.00             ( ( ( v2_pre_topc @ A ) & ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) =>
% 5.79/6.00               ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 5.79/6.00  thf('5', plain,
% 5.79/6.00      (![X51 : $i, X52 : $i]:
% 5.79/6.00         (~ (m1_subset_1 @ X51 @ (k1_zfmisc_1 @ (u1_struct_0 @ X52)))
% 5.79/6.00          | ~ (v4_pre_topc @ X51 @ X52)
% 5.79/6.00          | ((k2_pre_topc @ X52 @ X51) = (X51))
% 5.79/6.00          | ~ (l1_pre_topc @ X52))),
% 5.79/6.00      inference('cnf', [status(esa)], [t52_pre_topc])).
% 5.79/6.00  thf('6', plain,
% 5.79/6.00      ((~ (l1_pre_topc @ sk_A)
% 5.79/6.00        | ((k2_pre_topc @ sk_A @ sk_B) = (sk_B))
% 5.79/6.00        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 5.79/6.00      inference('sup-', [status(thm)], ['4', '5'])).
% 5.79/6.01  thf('7', plain, ((l1_pre_topc @ sk_A)),
% 5.79/6.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.79/6.01  thf('8', plain, ((v4_pre_topc @ sk_B @ sk_A)),
% 5.79/6.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.79/6.01  thf('9', plain, (((k2_pre_topc @ sk_A @ sk_B) = (sk_B))),
% 5.79/6.01      inference('demod', [status(thm)], ['6', '7', '8'])).
% 5.79/6.01  thf('10', plain,
% 5.79/6.01      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 5.79/6.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.79/6.01  thf(d5_subset_1, axiom,
% 5.79/6.01    (![A:$i,B:$i]:
% 5.79/6.01     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 5.79/6.01       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 5.79/6.01  thf('11', plain,
% 5.79/6.01      (![X33 : $i, X34 : $i]:
% 5.79/6.01         (((k3_subset_1 @ X33 @ X34) = (k4_xboole_0 @ X33 @ X34))
% 5.79/6.01          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ X33)))),
% 5.79/6.01      inference('cnf', [status(esa)], [d5_subset_1])).
% 5.79/6.01  thf('12', plain,
% 5.79/6.01      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 5.79/6.01         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 5.79/6.01      inference('sup-', [status(thm)], ['10', '11'])).
% 5.79/6.01  thf('13', plain,
% 5.79/6.01      (((k2_tops_1 @ sk_A @ sk_B)
% 5.79/6.01         = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 5.79/6.01            (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 5.79/6.01      inference('demod', [status(thm)], ['2', '3', '9', '12'])).
% 5.79/6.01  thf(commutativity_k2_xboole_0, axiom,
% 5.79/6.01    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 5.79/6.01  thf('14', plain,
% 5.79/6.01      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 5.79/6.01      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 5.79/6.01  thf(t36_xboole_1, axiom,
% 5.79/6.01    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 5.79/6.01  thf('15', plain,
% 5.79/6.01      (![X19 : $i, X20 : $i]: (r1_tarski @ (k4_xboole_0 @ X19 @ X20) @ X19)),
% 5.79/6.01      inference('cnf', [status(esa)], [t36_xboole_1])).
% 5.79/6.01  thf(t44_xboole_1, axiom,
% 5.79/6.01    (![A:$i,B:$i,C:$i]:
% 5.79/6.01     ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) =>
% 5.79/6.01       ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 5.79/6.01  thf('16', plain,
% 5.79/6.01      (![X25 : $i, X26 : $i, X27 : $i]:
% 5.79/6.01         ((r1_tarski @ X25 @ (k2_xboole_0 @ X26 @ X27))
% 5.79/6.01          | ~ (r1_tarski @ (k4_xboole_0 @ X25 @ X26) @ X27))),
% 5.79/6.01      inference('cnf', [status(esa)], [t44_xboole_1])).
% 5.79/6.01  thf('17', plain,
% 5.79/6.01      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 5.79/6.01      inference('sup-', [status(thm)], ['15', '16'])).
% 5.79/6.01  thf('18', plain,
% 5.79/6.01      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 5.79/6.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.79/6.01  thf(t3_subset, axiom,
% 5.79/6.01    (![A:$i,B:$i]:
% 5.79/6.01     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 5.79/6.01  thf('19', plain,
% 5.79/6.01      (![X44 : $i, X45 : $i]:
% 5.79/6.01         ((r1_tarski @ X44 @ X45) | ~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ X45)))),
% 5.79/6.01      inference('cnf', [status(esa)], [t3_subset])).
% 5.79/6.01  thf('20', plain, ((r1_tarski @ sk_B @ (u1_struct_0 @ sk_A))),
% 5.79/6.01      inference('sup-', [status(thm)], ['18', '19'])).
% 5.79/6.01  thf(t1_xboole_1, axiom,
% 5.79/6.01    (![A:$i,B:$i,C:$i]:
% 5.79/6.01     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 5.79/6.01       ( r1_tarski @ A @ C ) ))).
% 5.79/6.01  thf('21', plain,
% 5.79/6.01      (![X15 : $i, X16 : $i, X17 : $i]:
% 5.79/6.01         (~ (r1_tarski @ X15 @ X16)
% 5.79/6.01          | ~ (r1_tarski @ X16 @ X17)
% 5.79/6.01          | (r1_tarski @ X15 @ X17))),
% 5.79/6.01      inference('cnf', [status(esa)], [t1_xboole_1])).
% 5.79/6.01  thf('22', plain,
% 5.79/6.01      (![X0 : $i]:
% 5.79/6.01         ((r1_tarski @ sk_B @ X0) | ~ (r1_tarski @ (u1_struct_0 @ sk_A) @ X0))),
% 5.79/6.01      inference('sup-', [status(thm)], ['20', '21'])).
% 5.79/6.01  thf('23', plain,
% 5.79/6.01      (![X0 : $i]:
% 5.79/6.01         (r1_tarski @ sk_B @ (k2_xboole_0 @ X0 @ (u1_struct_0 @ sk_A)))),
% 5.79/6.01      inference('sup-', [status(thm)], ['17', '22'])).
% 5.79/6.01  thf('24', plain,
% 5.79/6.01      (![X0 : $i]:
% 5.79/6.01         (r1_tarski @ sk_B @ (k2_xboole_0 @ (u1_struct_0 @ sk_A) @ X0))),
% 5.79/6.01      inference('sup+', [status(thm)], ['14', '23'])).
% 5.79/6.01  thf(t43_xboole_1, axiom,
% 5.79/6.01    (![A:$i,B:$i,C:$i]:
% 5.79/6.01     ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) =>
% 5.79/6.01       ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ))).
% 5.79/6.01  thf('25', plain,
% 5.79/6.01      (![X22 : $i, X23 : $i, X24 : $i]:
% 5.79/6.01         ((r1_tarski @ (k4_xboole_0 @ X22 @ X23) @ X24)
% 5.79/6.01          | ~ (r1_tarski @ X22 @ (k2_xboole_0 @ X23 @ X24)))),
% 5.79/6.01      inference('cnf', [status(esa)], [t43_xboole_1])).
% 5.79/6.01  thf('26', plain,
% 5.79/6.01      (![X0 : $i]:
% 5.79/6.01         (r1_tarski @ (k4_xboole_0 @ sk_B @ (u1_struct_0 @ sk_A)) @ X0)),
% 5.79/6.01      inference('sup-', [status(thm)], ['24', '25'])).
% 5.79/6.01  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 5.79/6.01  thf('27', plain, (![X18 : $i]: (r1_tarski @ k1_xboole_0 @ X18)),
% 5.79/6.01      inference('cnf', [status(esa)], [t2_xboole_1])).
% 5.79/6.01  thf(d10_xboole_0, axiom,
% 5.79/6.01    (![A:$i,B:$i]:
% 5.79/6.01     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 5.79/6.01  thf('28', plain,
% 5.79/6.01      (![X8 : $i, X10 : $i]:
% 5.79/6.01         (((X8) = (X10)) | ~ (r1_tarski @ X10 @ X8) | ~ (r1_tarski @ X8 @ X10))),
% 5.79/6.01      inference('cnf', [status(esa)], [d10_xboole_0])).
% 5.79/6.01  thf('29', plain,
% 5.79/6.01      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 5.79/6.01      inference('sup-', [status(thm)], ['27', '28'])).
% 5.79/6.01  thf('30', plain,
% 5.79/6.01      (((k4_xboole_0 @ sk_B @ (u1_struct_0 @ sk_A)) = (k1_xboole_0))),
% 5.79/6.01      inference('sup-', [status(thm)], ['26', '29'])).
% 5.79/6.01  thf(t48_xboole_1, axiom,
% 5.79/6.01    (![A:$i,B:$i]:
% 5.79/6.01     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 5.79/6.01  thf('31', plain,
% 5.79/6.01      (![X28 : $i, X29 : $i]:
% 5.79/6.01         ((k4_xboole_0 @ X28 @ (k4_xboole_0 @ X28 @ X29))
% 5.79/6.01           = (k3_xboole_0 @ X28 @ X29))),
% 5.79/6.01      inference('cnf', [status(esa)], [t48_xboole_1])).
% 5.79/6.01  thf('32', plain,
% 5.79/6.01      (((k4_xboole_0 @ sk_B @ k1_xboole_0)
% 5.79/6.01         = (k3_xboole_0 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 5.79/6.01      inference('sup+', [status(thm)], ['30', '31'])).
% 5.79/6.01  thf(commutativity_k3_xboole_0, axiom,
% 5.79/6.01    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 5.79/6.01  thf('33', plain,
% 5.79/6.01      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 5.79/6.01      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 5.79/6.01  thf(t17_xboole_1, axiom,
% 5.79/6.01    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 5.79/6.01  thf('34', plain,
% 5.79/6.01      (![X13 : $i, X14 : $i]: (r1_tarski @ (k3_xboole_0 @ X13 @ X14) @ X13)),
% 5.79/6.01      inference('cnf', [status(esa)], [t17_xboole_1])).
% 5.79/6.01  thf('35', plain,
% 5.79/6.01      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 5.79/6.01      inference('sup+', [status(thm)], ['33', '34'])).
% 5.79/6.01  thf('36', plain,
% 5.79/6.01      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 5.79/6.01      inference('sup-', [status(thm)], ['27', '28'])).
% 5.79/6.01  thf('37', plain,
% 5.79/6.01      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 5.79/6.01      inference('sup-', [status(thm)], ['35', '36'])).
% 5.79/6.01  thf(t100_xboole_1, axiom,
% 5.79/6.01    (![A:$i,B:$i]:
% 5.79/6.01     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 5.79/6.01  thf('38', plain,
% 5.79/6.01      (![X11 : $i, X12 : $i]:
% 5.79/6.01         ((k4_xboole_0 @ X11 @ X12)
% 5.79/6.01           = (k5_xboole_0 @ X11 @ (k3_xboole_0 @ X11 @ X12)))),
% 5.79/6.01      inference('cnf', [status(esa)], [t100_xboole_1])).
% 5.79/6.01  thf('39', plain,
% 5.79/6.01      (![X0 : $i]:
% 5.79/6.01         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 5.79/6.01      inference('sup+', [status(thm)], ['37', '38'])).
% 5.79/6.01  thf('40', plain,
% 5.79/6.01      (((k5_xboole_0 @ sk_B @ k1_xboole_0)
% 5.79/6.01         = (k3_xboole_0 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 5.79/6.01      inference('demod', [status(thm)], ['32', '39'])).
% 5.79/6.01  thf('41', plain,
% 5.79/6.01      (![X0 : $i]:
% 5.79/6.01         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 5.79/6.01      inference('sup+', [status(thm)], ['37', '38'])).
% 5.79/6.01  thf(t3_boole, axiom,
% 5.79/6.01    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 5.79/6.01  thf('42', plain, (![X21 : $i]: ((k4_xboole_0 @ X21 @ k1_xboole_0) = (X21))),
% 5.79/6.01      inference('cnf', [status(esa)], [t3_boole])).
% 5.79/6.01  thf('43', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 5.79/6.01      inference('sup+', [status(thm)], ['41', '42'])).
% 5.79/6.01  thf('44', plain, (((sk_B) = (k3_xboole_0 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 5.79/6.01      inference('demod', [status(thm)], ['40', '43'])).
% 5.79/6.01  thf('45', plain,
% 5.79/6.01      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 5.79/6.01      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 5.79/6.01  thf('46', plain,
% 5.79/6.01      (![X11 : $i, X12 : $i]:
% 5.79/6.01         ((k4_xboole_0 @ X11 @ X12)
% 5.79/6.01           = (k5_xboole_0 @ X11 @ (k3_xboole_0 @ X11 @ X12)))),
% 5.79/6.01      inference('cnf', [status(esa)], [t100_xboole_1])).
% 5.79/6.01  thf('47', plain,
% 5.79/6.01      (![X0 : $i, X1 : $i]:
% 5.79/6.01         ((k4_xboole_0 @ X0 @ X1)
% 5.79/6.01           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 5.79/6.01      inference('sup+', [status(thm)], ['45', '46'])).
% 5.79/6.01  thf('48', plain,
% 5.79/6.01      (((k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)
% 5.79/6.01         = (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 5.79/6.01      inference('sup+', [status(thm)], ['44', '47'])).
% 5.79/6.01  thf('49', plain,
% 5.79/6.01      (((k2_tops_1 @ sk_A @ sk_B)
% 5.79/6.01         = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 5.79/6.01            (k2_pre_topc @ sk_A @ (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 5.79/6.01      inference('demod', [status(thm)], ['13', '48'])).
% 5.79/6.01  thf('50', plain,
% 5.79/6.01      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 5.79/6.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.79/6.01  thf(commutativity_k9_subset_1, axiom,
% 5.79/6.01    (![A:$i,B:$i,C:$i]:
% 5.79/6.01     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 5.79/6.01       ( ( k9_subset_1 @ A @ B @ C ) = ( k9_subset_1 @ A @ C @ B ) ) ))).
% 5.79/6.01  thf('51', plain,
% 5.79/6.01      (![X30 : $i, X31 : $i, X32 : $i]:
% 5.79/6.01         (((k9_subset_1 @ X30 @ X32 @ X31) = (k9_subset_1 @ X30 @ X31 @ X32))
% 5.79/6.01          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ X30)))),
% 5.79/6.01      inference('cnf', [status(esa)], [commutativity_k9_subset_1])).
% 5.79/6.01  thf('52', plain,
% 5.79/6.01      (![X0 : $i]:
% 5.79/6.01         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_B)
% 5.79/6.01           = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0))),
% 5.79/6.01      inference('sup-', [status(thm)], ['50', '51'])).
% 5.79/6.01  thf('53', plain,
% 5.79/6.01      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 5.79/6.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.79/6.01  thf(dt_k9_subset_1, axiom,
% 5.79/6.01    (![A:$i,B:$i,C:$i]:
% 5.79/6.01     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 5.79/6.01       ( m1_subset_1 @ ( k9_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 5.79/6.01  thf('54', plain,
% 5.79/6.01      (![X35 : $i, X36 : $i, X37 : $i]:
% 5.79/6.01         ((m1_subset_1 @ (k9_subset_1 @ X35 @ X36 @ X37) @ (k1_zfmisc_1 @ X35))
% 5.79/6.01          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ X35)))),
% 5.79/6.01      inference('cnf', [status(esa)], [dt_k9_subset_1])).
% 5.79/6.01  thf('55', plain,
% 5.79/6.01      (![X0 : $i]:
% 5.79/6.01         (m1_subset_1 @ (k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_B) @ 
% 5.79/6.01          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 5.79/6.01      inference('sup-', [status(thm)], ['53', '54'])).
% 5.79/6.01  thf('56', plain,
% 5.79/6.01      (![X0 : $i]:
% 5.79/6.01         (m1_subset_1 @ (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0) @ 
% 5.79/6.01          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 5.79/6.01      inference('sup+', [status(thm)], ['52', '55'])).
% 5.79/6.01  thf('57', plain,
% 5.79/6.01      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 5.79/6.01        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 5.79/6.01      inference('sup+', [status(thm)], ['49', '56'])).
% 5.79/6.01  thf('58', plain,
% 5.79/6.01      (![X33 : $i, X34 : $i]:
% 5.79/6.01         (((k3_subset_1 @ X33 @ X34) = (k4_xboole_0 @ X33 @ X34))
% 5.79/6.01          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ X33)))),
% 5.79/6.01      inference('cnf', [status(esa)], [d5_subset_1])).
% 5.79/6.01  thf('59', plain,
% 5.79/6.01      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_tops_1 @ sk_A @ sk_B))
% 5.79/6.01         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ (k2_tops_1 @ sk_A @ sk_B)))),
% 5.79/6.01      inference('sup-', [status(thm)], ['57', '58'])).
% 5.79/6.01  thf('60', plain,
% 5.79/6.01      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 5.79/6.01         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 5.79/6.01      inference('sup-', [status(thm)], ['10', '11'])).
% 5.79/6.01  thf(t31_subset_1, axiom,
% 5.79/6.01    (![A:$i,B:$i]:
% 5.79/6.01     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 5.79/6.01       ( ![C:$i]:
% 5.79/6.01         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 5.79/6.01           ( ( r1_tarski @ B @ C ) <=>
% 5.79/6.01             ( r1_tarski @ ( k3_subset_1 @ A @ C ) @ ( k3_subset_1 @ A @ B ) ) ) ) ) ))).
% 5.79/6.01  thf('61', plain,
% 5.79/6.01      (![X38 : $i, X39 : $i, X40 : $i]:
% 5.79/6.01         (~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ X39))
% 5.79/6.01          | ~ (r1_tarski @ (k3_subset_1 @ X39 @ X38) @ 
% 5.79/6.01               (k3_subset_1 @ X39 @ X40))
% 5.79/6.01          | (r1_tarski @ X40 @ X38)
% 5.79/6.01          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ X39)))),
% 5.79/6.01      inference('cnf', [status(esa)], [t31_subset_1])).
% 5.79/6.01  thf('62', plain,
% 5.79/6.01      (![X0 : $i]:
% 5.79/6.01         (~ (r1_tarski @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 5.79/6.01             (k3_subset_1 @ (u1_struct_0 @ sk_A) @ X0))
% 5.79/6.01          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 5.79/6.01          | (r1_tarski @ X0 @ sk_B)
% 5.79/6.01          | ~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 5.79/6.01      inference('sup-', [status(thm)], ['60', '61'])).
% 5.79/6.01  thf('63', plain,
% 5.79/6.01      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 5.79/6.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.79/6.01  thf('64', plain,
% 5.79/6.01      (![X0 : $i]:
% 5.79/6.01         (~ (r1_tarski @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 5.79/6.01             (k3_subset_1 @ (u1_struct_0 @ sk_A) @ X0))
% 5.79/6.01          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 5.79/6.01          | (r1_tarski @ X0 @ sk_B))),
% 5.79/6.01      inference('demod', [status(thm)], ['62', '63'])).
% 5.79/6.01  thf('65', plain,
% 5.79/6.01      (((k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)
% 5.79/6.01         = (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 5.79/6.01      inference('sup+', [status(thm)], ['44', '47'])).
% 5.79/6.01  thf('66', plain,
% 5.79/6.01      (![X0 : $i]:
% 5.79/6.01         (~ (r1_tarski @ (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 5.79/6.01             (k3_subset_1 @ (u1_struct_0 @ sk_A) @ X0))
% 5.79/6.01          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 5.79/6.01          | (r1_tarski @ X0 @ sk_B))),
% 5.79/6.01      inference('demod', [status(thm)], ['64', '65'])).
% 5.79/6.01  thf('67', plain,
% 5.79/6.01      ((~ (r1_tarski @ (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 5.79/6.01           (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ (k2_tops_1 @ sk_A @ sk_B)))
% 5.79/6.01        | (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)
% 5.79/6.01        | ~ (m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 5.79/6.01             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 5.79/6.01      inference('sup-', [status(thm)], ['59', '66'])).
% 5.79/6.01  thf('68', plain,
% 5.79/6.01      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 5.79/6.01        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 5.79/6.01      inference('sup+', [status(thm)], ['49', '56'])).
% 5.79/6.01  thf('69', plain,
% 5.79/6.01      ((~ (r1_tarski @ (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 5.79/6.01           (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ (k2_tops_1 @ sk_A @ sk_B)))
% 5.79/6.01        | (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))),
% 5.79/6.01      inference('demod', [status(thm)], ['67', '68'])).
% 5.79/6.01  thf('70', plain, (~ (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)),
% 5.79/6.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.79/6.01  thf('71', plain,
% 5.79/6.01      (~ (r1_tarski @ (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 5.79/6.01          (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ (k2_tops_1 @ sk_A @ sk_B)))),
% 5.79/6.01      inference('clc', [status(thm)], ['69', '70'])).
% 5.79/6.01  thf('72', plain,
% 5.79/6.01      (((k2_tops_1 @ sk_A @ sk_B)
% 5.79/6.01         = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 5.79/6.01            (k2_pre_topc @ sk_A @ (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 5.79/6.01      inference('demod', [status(thm)], ['13', '48'])).
% 5.79/6.01  thf('73', plain,
% 5.79/6.01      (![X0 : $i]:
% 5.79/6.01         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_B)
% 5.79/6.01           = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0))),
% 5.79/6.01      inference('sup-', [status(thm)], ['50', '51'])).
% 5.79/6.01  thf('74', plain,
% 5.79/6.01      (![X0 : $i]:
% 5.79/6.01         (m1_subset_1 @ (k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_B) @ 
% 5.79/6.01          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 5.79/6.01      inference('sup-', [status(thm)], ['53', '54'])).
% 5.79/6.01  thf('75', plain,
% 5.79/6.01      (![X44 : $i, X45 : $i]:
% 5.79/6.01         ((r1_tarski @ X44 @ X45) | ~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ X45)))),
% 5.79/6.01      inference('cnf', [status(esa)], [t3_subset])).
% 5.79/6.01  thf('76', plain,
% 5.79/6.01      (![X0 : $i]:
% 5.79/6.01         (r1_tarski @ (k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_B) @ 
% 5.79/6.01          (u1_struct_0 @ sk_A))),
% 5.79/6.01      inference('sup-', [status(thm)], ['74', '75'])).
% 5.79/6.01  thf('77', plain,
% 5.79/6.01      (![X0 : $i]:
% 5.79/6.01         (r1_tarski @ (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0) @ 
% 5.79/6.01          (u1_struct_0 @ sk_A))),
% 5.79/6.01      inference('sup+', [status(thm)], ['73', '76'])).
% 5.79/6.01  thf('78', plain,
% 5.79/6.01      ((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A))),
% 5.79/6.01      inference('sup+', [status(thm)], ['72', '77'])).
% 5.79/6.01  thf('79', plain, (![X21 : $i]: ((k4_xboole_0 @ X21 @ k1_xboole_0) = (X21))),
% 5.79/6.01      inference('cnf', [status(esa)], [t3_boole])).
% 5.79/6.01  thf('80', plain,
% 5.79/6.01      (![X8 : $i, X9 : $i]: ((r1_tarski @ X8 @ X9) | ((X8) != (X9)))),
% 5.79/6.01      inference('cnf', [status(esa)], [d10_xboole_0])).
% 5.79/6.01  thf('81', plain, (![X9 : $i]: (r1_tarski @ X9 @ X9)),
% 5.79/6.01      inference('simplify', [status(thm)], ['80'])).
% 5.79/6.01  thf('82', plain,
% 5.79/6.01      (![X22 : $i, X23 : $i, X24 : $i]:
% 5.79/6.01         ((r1_tarski @ (k4_xboole_0 @ X22 @ X23) @ X24)
% 5.79/6.01          | ~ (r1_tarski @ X22 @ (k2_xboole_0 @ X23 @ X24)))),
% 5.79/6.01      inference('cnf', [status(esa)], [t43_xboole_1])).
% 5.79/6.01  thf('83', plain,
% 5.79/6.01      (![X0 : $i, X1 : $i]:
% 5.79/6.01         (r1_tarski @ (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1) @ X0)),
% 5.79/6.01      inference('sup-', [status(thm)], ['81', '82'])).
% 5.79/6.01  thf('84', plain,
% 5.79/6.01      (![X0 : $i]: (r1_tarski @ (k2_xboole_0 @ k1_xboole_0 @ X0) @ X0)),
% 5.79/6.01      inference('sup+', [status(thm)], ['79', '83'])).
% 5.79/6.01  thf('85', plain,
% 5.79/6.01      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 5.79/6.01      inference('sup-', [status(thm)], ['15', '16'])).
% 5.79/6.01  thf('86', plain,
% 5.79/6.01      (![X8 : $i, X10 : $i]:
% 5.79/6.01         (((X8) = (X10)) | ~ (r1_tarski @ X10 @ X8) | ~ (r1_tarski @ X8 @ X10))),
% 5.79/6.01      inference('cnf', [status(esa)], [d10_xboole_0])).
% 5.79/6.01  thf('87', plain,
% 5.79/6.01      (![X0 : $i, X1 : $i]:
% 5.79/6.01         (~ (r1_tarski @ (k2_xboole_0 @ X1 @ X0) @ X0)
% 5.79/6.01          | ((k2_xboole_0 @ X1 @ X0) = (X0)))),
% 5.79/6.01      inference('sup-', [status(thm)], ['85', '86'])).
% 5.79/6.01  thf('88', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 5.79/6.01      inference('sup-', [status(thm)], ['84', '87'])).
% 5.79/6.01  thf('89', plain,
% 5.79/6.01      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 5.79/6.01      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 5.79/6.01  thf('90', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 5.79/6.01      inference('sup+', [status(thm)], ['88', '89'])).
% 5.79/6.01  thf('91', plain,
% 5.79/6.01      (![X22 : $i, X23 : $i, X24 : $i]:
% 5.79/6.01         ((r1_tarski @ (k4_xboole_0 @ X22 @ X23) @ X24)
% 5.79/6.01          | ~ (r1_tarski @ X22 @ (k2_xboole_0 @ X23 @ X24)))),
% 5.79/6.01      inference('cnf', [status(esa)], [t43_xboole_1])).
% 5.79/6.01  thf('92', plain,
% 5.79/6.01      (![X0 : $i, X1 : $i]:
% 5.79/6.01         (~ (r1_tarski @ X1 @ X0)
% 5.79/6.01          | (r1_tarski @ (k4_xboole_0 @ X1 @ X0) @ k1_xboole_0))),
% 5.79/6.01      inference('sup-', [status(thm)], ['90', '91'])).
% 5.79/6.01  thf('93', plain,
% 5.79/6.01      ((r1_tarski @ 
% 5.79/6.01        (k4_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A)) @ 
% 5.79/6.01        k1_xboole_0)),
% 5.79/6.01      inference('sup-', [status(thm)], ['78', '92'])).
% 5.79/6.01  thf('94', plain,
% 5.79/6.01      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 5.79/6.01      inference('sup-', [status(thm)], ['27', '28'])).
% 5.79/6.01  thf('95', plain,
% 5.79/6.01      (((k4_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A))
% 5.79/6.01         = (k1_xboole_0))),
% 5.79/6.01      inference('sup-', [status(thm)], ['93', '94'])).
% 5.79/6.01  thf('96', plain,
% 5.79/6.01      (![X28 : $i, X29 : $i]:
% 5.79/6.01         ((k4_xboole_0 @ X28 @ (k4_xboole_0 @ X28 @ X29))
% 5.79/6.01           = (k3_xboole_0 @ X28 @ X29))),
% 5.79/6.01      inference('cnf', [status(esa)], [t48_xboole_1])).
% 5.79/6.01  thf('97', plain,
% 5.79/6.01      (((k4_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ k1_xboole_0)
% 5.79/6.01         = (k3_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 5.79/6.01      inference('sup+', [status(thm)], ['95', '96'])).
% 5.79/6.01  thf('98', plain, (![X21 : $i]: ((k4_xboole_0 @ X21 @ k1_xboole_0) = (X21))),
% 5.79/6.01      inference('cnf', [status(esa)], [t3_boole])).
% 5.79/6.01  thf('99', plain,
% 5.79/6.01      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 5.79/6.01      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 5.79/6.01  thf('100', plain,
% 5.79/6.01      (((k2_tops_1 @ sk_A @ sk_B)
% 5.79/6.01         = (k3_xboole_0 @ (u1_struct_0 @ sk_A) @ (k2_tops_1 @ sk_A @ sk_B)))),
% 5.79/6.01      inference('demod', [status(thm)], ['97', '98', '99'])).
% 5.79/6.01  thf('101', plain,
% 5.79/6.01      (![X11 : $i, X12 : $i]:
% 5.79/6.01         ((k4_xboole_0 @ X11 @ X12)
% 5.79/6.01           = (k5_xboole_0 @ X11 @ (k3_xboole_0 @ X11 @ X12)))),
% 5.79/6.01      inference('cnf', [status(esa)], [t100_xboole_1])).
% 5.79/6.01  thf('102', plain,
% 5.79/6.01      (((k4_xboole_0 @ (u1_struct_0 @ sk_A) @ (k2_tops_1 @ sk_A @ sk_B))
% 5.79/6.01         = (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ (k2_tops_1 @ sk_A @ sk_B)))),
% 5.79/6.01      inference('sup+', [status(thm)], ['100', '101'])).
% 5.79/6.01  thf('103', plain,
% 5.79/6.01      (~ (r1_tarski @ (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 5.79/6.01          (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ (k2_tops_1 @ sk_A @ sk_B)))),
% 5.79/6.01      inference('demod', [status(thm)], ['71', '102'])).
% 5.79/6.01  thf('104', plain, (![X9 : $i]: (r1_tarski @ X9 @ X9)),
% 5.79/6.01      inference('simplify', [status(thm)], ['80'])).
% 5.79/6.01  thf('105', plain,
% 5.79/6.01      (![X25 : $i, X26 : $i, X27 : $i]:
% 5.79/6.01         ((r1_tarski @ X25 @ (k2_xboole_0 @ X26 @ X27))
% 5.79/6.01          | ~ (r1_tarski @ (k4_xboole_0 @ X25 @ X26) @ X27))),
% 5.79/6.01      inference('cnf', [status(esa)], [t44_xboole_1])).
% 5.79/6.01  thf('106', plain,
% 5.79/6.01      (![X0 : $i, X1 : $i]:
% 5.79/6.01         (r1_tarski @ X1 @ (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 5.79/6.01      inference('sup-', [status(thm)], ['104', '105'])).
% 5.79/6.01  thf('107', plain,
% 5.79/6.01      (![X0 : $i]:
% 5.79/6.01         ((r1_tarski @ sk_B @ X0) | ~ (r1_tarski @ (u1_struct_0 @ sk_A) @ X0))),
% 5.79/6.01      inference('sup-', [status(thm)], ['20', '21'])).
% 5.79/6.01  thf('108', plain,
% 5.79/6.01      (![X0 : $i]:
% 5.79/6.01         (r1_tarski @ sk_B @ 
% 5.79/6.01          (k2_xboole_0 @ X0 @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ X0)))),
% 5.79/6.01      inference('sup-', [status(thm)], ['106', '107'])).
% 5.79/6.01  thf('109', plain,
% 5.79/6.01      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 5.79/6.01      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 5.79/6.01  thf('110', plain,
% 5.79/6.01      (![X22 : $i, X23 : $i, X24 : $i]:
% 5.79/6.01         ((r1_tarski @ (k4_xboole_0 @ X22 @ X23) @ X24)
% 5.79/6.01          | ~ (r1_tarski @ X22 @ (k2_xboole_0 @ X23 @ X24)))),
% 5.79/6.01      inference('cnf', [status(esa)], [t43_xboole_1])).
% 5.79/6.01  thf('111', plain,
% 5.79/6.01      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.79/6.01         (~ (r1_tarski @ X2 @ (k2_xboole_0 @ X1 @ X0))
% 5.79/6.01          | (r1_tarski @ (k4_xboole_0 @ X2 @ X0) @ X1))),
% 5.79/6.01      inference('sup-', [status(thm)], ['109', '110'])).
% 5.79/6.01  thf('112', plain,
% 5.79/6.01      (![X0 : $i]:
% 5.79/6.01         (r1_tarski @ 
% 5.79/6.01          (k4_xboole_0 @ sk_B @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ X0)) @ X0)),
% 5.79/6.01      inference('sup-', [status(thm)], ['108', '111'])).
% 5.79/6.01  thf('113', plain,
% 5.79/6.01      (![X44 : $i, X46 : $i]:
% 5.79/6.01         ((m1_subset_1 @ X44 @ (k1_zfmisc_1 @ X46)) | ~ (r1_tarski @ X44 @ X46))),
% 5.79/6.01      inference('cnf', [status(esa)], [t3_subset])).
% 5.79/6.01  thf('114', plain,
% 5.79/6.01      (![X0 : $i]:
% 5.79/6.01         (m1_subset_1 @ 
% 5.79/6.01          (k4_xboole_0 @ sk_B @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ X0)) @ 
% 5.79/6.01          (k1_zfmisc_1 @ X0))),
% 5.79/6.01      inference('sup-', [status(thm)], ['112', '113'])).
% 5.79/6.01  thf('115', plain,
% 5.79/6.01      (((k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)
% 5.79/6.01         = (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 5.79/6.01      inference('sup+', [status(thm)], ['44', '47'])).
% 5.79/6.01  thf('116', plain,
% 5.79/6.01      (![X19 : $i, X20 : $i]: (r1_tarski @ (k4_xboole_0 @ X19 @ X20) @ X19)),
% 5.79/6.01      inference('cnf', [status(esa)], [t36_xboole_1])).
% 5.79/6.01  thf('117', plain,
% 5.79/6.01      (![X44 : $i, X46 : $i]:
% 5.79/6.01         ((m1_subset_1 @ X44 @ (k1_zfmisc_1 @ X46)) | ~ (r1_tarski @ X44 @ X46))),
% 5.79/6.01      inference('cnf', [status(esa)], [t3_subset])).
% 5.79/6.01  thf('118', plain,
% 5.79/6.01      (![X0 : $i, X1 : $i]:
% 5.79/6.01         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 5.79/6.01      inference('sup-', [status(thm)], ['116', '117'])).
% 5.79/6.01  thf('119', plain,
% 5.79/6.01      ((m1_subset_1 @ (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 5.79/6.01        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 5.79/6.01      inference('sup+', [status(thm)], ['115', '118'])).
% 5.79/6.01  thf(dt_k2_pre_topc, axiom,
% 5.79/6.01    (![A:$i,B:$i]:
% 5.79/6.01     ( ( ( l1_pre_topc @ A ) & 
% 5.79/6.01         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 5.79/6.01       ( m1_subset_1 @
% 5.79/6.01         ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 5.79/6.01  thf('120', plain,
% 5.79/6.01      (![X49 : $i, X50 : $i]:
% 5.79/6.01         (~ (l1_pre_topc @ X49)
% 5.79/6.01          | ~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ (u1_struct_0 @ X49)))
% 5.79/6.01          | (m1_subset_1 @ (k2_pre_topc @ X49 @ X50) @ 
% 5.79/6.01             (k1_zfmisc_1 @ (u1_struct_0 @ X49))))),
% 5.79/6.01      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 5.79/6.01  thf('121', plain,
% 5.79/6.01      (((m1_subset_1 @ 
% 5.79/6.01         (k2_pre_topc @ sk_A @ (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)) @ 
% 5.79/6.01         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 5.79/6.01        | ~ (l1_pre_topc @ sk_A))),
% 5.79/6.01      inference('sup-', [status(thm)], ['119', '120'])).
% 5.79/6.01  thf('122', plain, ((l1_pre_topc @ sk_A)),
% 5.79/6.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.79/6.01  thf('123', plain,
% 5.79/6.01      ((m1_subset_1 @ 
% 5.79/6.01        (k2_pre_topc @ sk_A @ (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)) @ 
% 5.79/6.01        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 5.79/6.01      inference('demod', [status(thm)], ['121', '122'])).
% 5.79/6.01  thf(t42_subset_1, axiom,
% 5.79/6.01    (![A:$i,B:$i]:
% 5.79/6.01     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 5.79/6.01       ( ![C:$i]:
% 5.79/6.01         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 5.79/6.01           ( r1_tarski @
% 5.79/6.01             ( k3_subset_1 @ A @ B ) @ 
% 5.79/6.01             ( k3_subset_1 @ A @ ( k9_subset_1 @ A @ B @ C ) ) ) ) ) ))).
% 5.79/6.01  thf('124', plain,
% 5.79/6.01      (![X41 : $i, X42 : $i, X43 : $i]:
% 5.79/6.01         (~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ X42))
% 5.79/6.01          | (r1_tarski @ (k3_subset_1 @ X42 @ X43) @ 
% 5.79/6.01             (k3_subset_1 @ X42 @ (k9_subset_1 @ X42 @ X43 @ X41)))
% 5.79/6.01          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ X42)))),
% 5.79/6.01      inference('cnf', [status(esa)], [t42_subset_1])).
% 5.79/6.01  thf('125', plain,
% 5.79/6.01      (![X0 : $i]:
% 5.79/6.01         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 5.79/6.01          | (r1_tarski @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ X0) @ 
% 5.79/6.01             (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 5.79/6.01              (k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ 
% 5.79/6.01               (k2_pre_topc @ sk_A @ 
% 5.79/6.01                (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))))))),
% 5.79/6.01      inference('sup-', [status(thm)], ['123', '124'])).
% 5.79/6.01  thf('126', plain,
% 5.79/6.01      ((r1_tarski @ 
% 5.79/6.01        (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 5.79/6.01         (k4_xboole_0 @ sk_B @ 
% 5.79/6.01          (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A)))) @ 
% 5.79/6.01        (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 5.79/6.01         (k9_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 5.79/6.01          (k4_xboole_0 @ sk_B @ 
% 5.79/6.01           (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))) @ 
% 5.79/6.01          (k2_pre_topc @ sk_A @ (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)))))),
% 5.79/6.01      inference('sup-', [status(thm)], ['114', '125'])).
% 5.79/6.01  thf('127', plain, (![X21 : $i]: ((k4_xboole_0 @ X21 @ k1_xboole_0) = (X21))),
% 5.79/6.01      inference('cnf', [status(esa)], [t3_boole])).
% 5.79/6.01  thf('128', plain,
% 5.79/6.01      (![X28 : $i, X29 : $i]:
% 5.79/6.01         ((k4_xboole_0 @ X28 @ (k4_xboole_0 @ X28 @ X29))
% 5.79/6.01           = (k3_xboole_0 @ X28 @ X29))),
% 5.79/6.01      inference('cnf', [status(esa)], [t48_xboole_1])).
% 5.79/6.01  thf('129', plain,
% 5.79/6.01      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 5.79/6.01      inference('sup+', [status(thm)], ['127', '128'])).
% 5.79/6.01  thf('130', plain,
% 5.79/6.01      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 5.79/6.01      inference('sup-', [status(thm)], ['35', '36'])).
% 5.79/6.01  thf('131', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 5.79/6.01      inference('demod', [status(thm)], ['129', '130'])).
% 5.79/6.01  thf('132', plain,
% 5.79/6.01      (![X28 : $i, X29 : $i]:
% 5.79/6.01         ((k4_xboole_0 @ X28 @ (k4_xboole_0 @ X28 @ X29))
% 5.79/6.01           = (k3_xboole_0 @ X28 @ X29))),
% 5.79/6.01      inference('cnf', [status(esa)], [t48_xboole_1])).
% 5.79/6.01  thf('133', plain,
% 5.79/6.01      (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k3_xboole_0 @ X0 @ X0))),
% 5.79/6.01      inference('sup+', [status(thm)], ['131', '132'])).
% 5.79/6.01  thf('134', plain, (![X21 : $i]: ((k4_xboole_0 @ X21 @ k1_xboole_0) = (X21))),
% 5.79/6.01      inference('cnf', [status(esa)], [t3_boole])).
% 5.79/6.01  thf('135', plain, (![X0 : $i]: ((X0) = (k3_xboole_0 @ X0 @ X0))),
% 5.79/6.01      inference('demod', [status(thm)], ['133', '134'])).
% 5.79/6.01  thf('136', plain,
% 5.79/6.01      (![X11 : $i, X12 : $i]:
% 5.79/6.01         ((k4_xboole_0 @ X11 @ X12)
% 5.79/6.01           = (k5_xboole_0 @ X11 @ (k3_xboole_0 @ X11 @ X12)))),
% 5.79/6.01      inference('cnf', [status(esa)], [t100_xboole_1])).
% 5.79/6.01  thf('137', plain,
% 5.79/6.01      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 5.79/6.01      inference('sup+', [status(thm)], ['135', '136'])).
% 5.79/6.01  thf('138', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 5.79/6.01      inference('demod', [status(thm)], ['129', '130'])).
% 5.79/6.01  thf('139', plain,
% 5.79/6.01      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 5.79/6.01      inference('sup+', [status(thm)], ['135', '136'])).
% 5.79/6.01  thf('140', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 5.79/6.01      inference('demod', [status(thm)], ['138', '139'])).
% 5.79/6.01  thf('141', plain, (![X21 : $i]: ((k4_xboole_0 @ X21 @ k1_xboole_0) = (X21))),
% 5.79/6.01      inference('cnf', [status(esa)], [t3_boole])).
% 5.79/6.01  thf('142', plain,
% 5.79/6.01      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 5.79/6.01         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 5.79/6.01      inference('sup-', [status(thm)], ['10', '11'])).
% 5.79/6.01  thf('143', plain,
% 5.79/6.01      (((k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)
% 5.79/6.01         = (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 5.79/6.01      inference('sup+', [status(thm)], ['44', '47'])).
% 5.79/6.01  thf('144', plain,
% 5.79/6.01      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 5.79/6.01         = (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 5.79/6.01      inference('demod', [status(thm)], ['142', '143'])).
% 5.79/6.01  thf('145', plain,
% 5.79/6.01      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 5.79/6.01      inference('sup+', [status(thm)], ['135', '136'])).
% 5.79/6.01  thf('146', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 5.79/6.01      inference('demod', [status(thm)], ['138', '139'])).
% 5.79/6.01  thf('147', plain, (![X21 : $i]: ((k4_xboole_0 @ X21 @ k1_xboole_0) = (X21))),
% 5.79/6.01      inference('cnf', [status(esa)], [t3_boole])).
% 5.79/6.01  thf('148', plain,
% 5.79/6.01      (((k2_tops_1 @ sk_A @ sk_B)
% 5.79/6.01         = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 5.79/6.01            (k2_pre_topc @ sk_A @ (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 5.79/6.01      inference('demod', [status(thm)], ['13', '48'])).
% 5.79/6.01  thf('149', plain,
% 5.79/6.01      (((k2_tops_1 @ sk_A @ sk_B)
% 5.79/6.01         = (k3_xboole_0 @ (u1_struct_0 @ sk_A) @ (k2_tops_1 @ sk_A @ sk_B)))),
% 5.79/6.01      inference('demod', [status(thm)], ['97', '98', '99'])).
% 5.79/6.01  thf('150', plain,
% 5.79/6.01      (![X13 : $i, X14 : $i]: (r1_tarski @ (k3_xboole_0 @ X13 @ X14) @ X13)),
% 5.79/6.01      inference('cnf', [status(esa)], [t17_xboole_1])).
% 5.79/6.01  thf('151', plain,
% 5.79/6.01      (![X44 : $i, X46 : $i]:
% 5.79/6.01         ((m1_subset_1 @ X44 @ (k1_zfmisc_1 @ X46)) | ~ (r1_tarski @ X44 @ X46))),
% 5.79/6.01      inference('cnf', [status(esa)], [t3_subset])).
% 5.79/6.01  thf('152', plain,
% 5.79/6.01      (![X0 : $i, X1 : $i]:
% 5.79/6.01         (m1_subset_1 @ (k3_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 5.79/6.01      inference('sup-', [status(thm)], ['150', '151'])).
% 5.79/6.01  thf('153', plain,
% 5.79/6.01      (![X33 : $i, X34 : $i]:
% 5.79/6.01         (((k3_subset_1 @ X33 @ X34) = (k4_xboole_0 @ X33 @ X34))
% 5.79/6.01          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ X33)))),
% 5.79/6.01      inference('cnf', [status(esa)], [d5_subset_1])).
% 5.79/6.01  thf('154', plain,
% 5.79/6.01      (![X0 : $i, X1 : $i]:
% 5.79/6.01         ((k3_subset_1 @ X0 @ (k3_xboole_0 @ X0 @ X1))
% 5.79/6.01           = (k4_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 5.79/6.01      inference('sup-', [status(thm)], ['152', '153'])).
% 5.79/6.01  thf('155', plain,
% 5.79/6.01      (![X13 : $i, X14 : $i]: (r1_tarski @ (k3_xboole_0 @ X13 @ X14) @ X13)),
% 5.79/6.01      inference('cnf', [status(esa)], [t17_xboole_1])).
% 5.79/6.01  thf('156', plain,
% 5.79/6.01      (![X22 : $i, X23 : $i, X24 : $i]:
% 5.79/6.01         ((r1_tarski @ (k4_xboole_0 @ X22 @ X23) @ X24)
% 5.79/6.01          | ~ (r1_tarski @ X22 @ (k2_xboole_0 @ X23 @ X24)))),
% 5.79/6.01      inference('cnf', [status(esa)], [t43_xboole_1])).
% 5.79/6.01  thf('157', plain,
% 5.79/6.01      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.79/6.01         (r1_tarski @ 
% 5.79/6.01          (k4_xboole_0 @ (k3_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X2) @ X1) @ 
% 5.79/6.01          X0)),
% 5.79/6.01      inference('sup-', [status(thm)], ['155', '156'])).
% 5.79/6.01  thf('158', plain,
% 5.79/6.01      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 5.79/6.01      inference('sup-', [status(thm)], ['27', '28'])).
% 5.79/6.01  thf('159', plain,
% 5.79/6.01      (![X0 : $i, X1 : $i]:
% 5.79/6.01         ((k4_xboole_0 @ 
% 5.79/6.01           (k3_xboole_0 @ (k2_xboole_0 @ X0 @ k1_xboole_0) @ X1) @ X0)
% 5.79/6.01           = (k1_xboole_0))),
% 5.79/6.01      inference('sup-', [status(thm)], ['157', '158'])).
% 5.79/6.01  thf('160', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 5.79/6.01      inference('sup+', [status(thm)], ['88', '89'])).
% 5.79/6.01  thf('161', plain,
% 5.79/6.01      (![X0 : $i, X1 : $i]:
% 5.79/6.01         ((k4_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0) = (k1_xboole_0))),
% 5.79/6.01      inference('demod', [status(thm)], ['159', '160'])).
% 5.79/6.01  thf('162', plain,
% 5.79/6.01      (![X28 : $i, X29 : $i]:
% 5.79/6.01         ((k4_xboole_0 @ X28 @ (k4_xboole_0 @ X28 @ X29))
% 5.79/6.01           = (k3_xboole_0 @ X28 @ X29))),
% 5.79/6.01      inference('cnf', [status(esa)], [t48_xboole_1])).
% 5.79/6.01  thf('163', plain,
% 5.79/6.01      (![X0 : $i, X1 : $i]:
% 5.79/6.01         ((k4_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ k1_xboole_0)
% 5.79/6.01           = (k3_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0))),
% 5.79/6.01      inference('sup+', [status(thm)], ['161', '162'])).
% 5.79/6.01  thf('164', plain, (![X21 : $i]: ((k4_xboole_0 @ X21 @ k1_xboole_0) = (X21))),
% 5.79/6.01      inference('cnf', [status(esa)], [t3_boole])).
% 5.79/6.01  thf('165', plain,
% 5.79/6.01      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 5.79/6.01      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 5.79/6.01  thf('166', plain,
% 5.79/6.01      (![X0 : $i, X1 : $i]:
% 5.79/6.01         ((k3_xboole_0 @ X0 @ X1)
% 5.79/6.01           = (k3_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 5.79/6.01      inference('demod', [status(thm)], ['163', '164', '165'])).
% 5.79/6.01  thf('167', plain,
% 5.79/6.01      (![X11 : $i, X12 : $i]:
% 5.79/6.01         ((k4_xboole_0 @ X11 @ X12)
% 5.79/6.01           = (k5_xboole_0 @ X11 @ (k3_xboole_0 @ X11 @ X12)))),
% 5.79/6.01      inference('cnf', [status(esa)], [t100_xboole_1])).
% 5.79/6.01  thf('168', plain,
% 5.79/6.01      (![X0 : $i, X1 : $i]:
% 5.79/6.01         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 5.79/6.01           = (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))),
% 5.79/6.01      inference('sup+', [status(thm)], ['166', '167'])).
% 5.79/6.01  thf('169', plain,
% 5.79/6.01      (![X11 : $i, X12 : $i]:
% 5.79/6.01         ((k4_xboole_0 @ X11 @ X12)
% 5.79/6.01           = (k5_xboole_0 @ X11 @ (k3_xboole_0 @ X11 @ X12)))),
% 5.79/6.01      inference('cnf', [status(esa)], [t100_xboole_1])).
% 5.79/6.01  thf('170', plain,
% 5.79/6.01      (![X0 : $i, X1 : $i]:
% 5.79/6.01         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 5.79/6.01           = (k4_xboole_0 @ X1 @ X0))),
% 5.79/6.01      inference('demod', [status(thm)], ['168', '169'])).
% 5.79/6.01  thf('171', plain,
% 5.79/6.01      (![X0 : $i, X1 : $i]:
% 5.79/6.01         ((k3_subset_1 @ X0 @ (k3_xboole_0 @ X0 @ X1))
% 5.79/6.01           = (k4_xboole_0 @ X0 @ X1))),
% 5.79/6.01      inference('demod', [status(thm)], ['154', '170'])).
% 5.79/6.01  thf('172', plain,
% 5.79/6.01      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_tops_1 @ sk_A @ sk_B))
% 5.79/6.01         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ (k2_tops_1 @ sk_A @ sk_B)))),
% 5.79/6.01      inference('sup+', [status(thm)], ['149', '171'])).
% 5.79/6.01  thf('173', plain,
% 5.79/6.01      (((k4_xboole_0 @ (u1_struct_0 @ sk_A) @ (k2_tops_1 @ sk_A @ sk_B))
% 5.79/6.01         = (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ (k2_tops_1 @ sk_A @ sk_B)))),
% 5.79/6.01      inference('sup+', [status(thm)], ['100', '101'])).
% 5.79/6.01  thf('174', plain,
% 5.79/6.01      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_tops_1 @ sk_A @ sk_B))
% 5.79/6.01         = (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ (k2_tops_1 @ sk_A @ sk_B)))),
% 5.79/6.01      inference('demod', [status(thm)], ['172', '173'])).
% 5.79/6.01  thf('175', plain,
% 5.79/6.01      ((r1_tarski @ (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 5.79/6.01        (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ (k2_tops_1 @ sk_A @ sk_B)))),
% 5.79/6.01      inference('demod', [status(thm)],
% 5.79/6.01                ['126', '137', '140', '141', '144', '145', '146', '147', 
% 5.79/6.01                 '148', '174'])).
% 5.79/6.01  thf('176', plain, ($false), inference('demod', [status(thm)], ['103', '175'])).
% 5.79/6.01  
% 5.79/6.01  % SZS output end Refutation
% 5.79/6.01  
% 5.84/6.01  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
