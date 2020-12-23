%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ELuWutjn6G

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:38 EST 2020

% Result     : Theorem 8.86s
% Output     : Refutation 8.86s
% Verified   : 
% Statistics : Number of formulae       :  160 ( 768 expanded)
%              Number of leaves         :   33 ( 241 expanded)
%              Depth                    :   21
%              Number of atoms          : 1449 (9109 expanded)
%              Number of equality atoms :   88 ( 503 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(t77_tops_1,conjecture,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v4_pre_topc @ B @ A )
          <=> ( ( k2_tops_1 @ A @ B )
              = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( ( v4_pre_topc @ B @ A )
            <=> ( ( k2_tops_1 @ A @ B )
                = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t77_tops_1])).

thf('0',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l78_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_tops_1 @ A @ B )
            = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ ( k1_tops_1 @ A @ B ) ) ) ) ) )).

thf('1',plain,(
    ! [X40: $i,X41: $i] :
      ( ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X41 ) ) )
      | ( ( k2_tops_1 @ X41 @ X40 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X41 ) @ ( k2_pre_topc @ X41 @ X40 ) @ ( k1_tops_1 @ X41 @ X40 ) ) )
      | ~ ( l1_pre_topc @ X41 ) ) ),
    inference(cnf,[status(esa)],[l78_tops_1])).

thf('2',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('5',plain,(
    ! [X29: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('6',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['6'])).

thf('8',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t69_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v4_pre_topc @ B @ A )
           => ( r1_tarski @ ( k2_tops_1 @ A @ B ) @ B ) ) ) ) )).

thf('9',plain,(
    ! [X44: $i,X45: $i] :
      ( ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X45 ) ) )
      | ( r1_tarski @ ( k2_tops_1 @ X45 @ X44 ) @ X44 )
      | ~ ( v4_pre_topc @ X44 @ X45 )
      | ~ ( l1_pre_topc @ X45 ) ) ),
    inference(cnf,[status(esa)],[t69_tops_1])).

thf('10',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v4_pre_topc @ sk_B @ sk_A )
    | ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ~ ( v4_pre_topc @ sk_B @ sk_A )
    | ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,
    ( ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['7','12'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('14',plain,(
    ! [X32: $i,X34: $i] :
      ( ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ X34 ) )
      | ~ ( r1_tarski @ X32 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('15',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_B ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['16'])).

thf('18',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('19',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ X24 ) )
      | ( ( k7_subset_1 @ X24 @ X23 @ X25 )
        = ( k4_xboole_0 @ X23 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['6'])).

thf('22',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X29: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('24',plain,(
    ! [X9: $i,X10: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X9 @ X10 ) @ X9 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('25',plain,(
    ! [X32: $i,X34: $i] :
      ( ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ X34 ) )
      | ~ ( r1_tarski @ X32 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf(t33_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ( k3_subset_1 @ A @ ( k7_subset_1 @ A @ B @ C ) )
            = ( k4_subset_1 @ A @ ( k3_subset_1 @ A @ B ) @ C ) ) ) ) )).

thf('27',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ X27 ) )
      | ( ( k3_subset_1 @ X27 @ ( k7_subset_1 @ X27 @ X28 @ X26 ) )
        = ( k4_subset_1 @ X27 @ ( k3_subset_1 @ X27 @ X28 ) @ X26 ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[t33_subset_1])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X0 ) )
      | ( ( k3_subset_1 @ X0 @ ( k7_subset_1 @ X0 @ X2 @ ( k4_xboole_0 @ X0 @ X1 ) ) )
        = ( k4_subset_1 @ X0 @ ( k3_subset_1 @ X0 @ X2 ) @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k7_subset_1 @ X0 @ k1_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) ) )
      = ( k4_subset_1 @ X0 @ ( k3_subset_1 @ X0 @ k1_xboole_0 ) @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['23','28'])).

thf('30',plain,(
    ! [X29: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('31',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ X24 ) )
      | ( ( k7_subset_1 @ X24 @ X23 @ X25 )
        = ( k4_xboole_0 @ X23 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_subset_1 @ X0 @ k1_xboole_0 @ X1 )
      = ( k4_xboole_0 @ k1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X9: $i,X10: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X9 @ X10 ) @ X9 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('34',plain,(
    ! [X29: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('35',plain,(
    ! [X32: $i,X33: $i] :
      ( ( r1_tarski @ X32 @ X33 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('36',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('37',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('38',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['33','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_subset_1 @ X0 @ k1_xboole_0 @ X1 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['32','39'])).

thf('41',plain,(
    ! [X29: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('42',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k3_subset_1 @ X16 @ X17 )
        = ( k4_xboole_0 @ X16 @ X17 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('44',plain,(
    ! [X11: $i] :
      ( ( k4_xboole_0 @ X11 @ k1_xboole_0 )
      = X11 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('48',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,(
    ! [X32: $i,X34: $i] :
      ( ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ X34 ) )
      | ~ ( r1_tarski @ X32 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('50',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('51',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X21 ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ X21 ) )
      | ( ( k4_subset_1 @ X21 @ X20 @ X22 )
        = ( k2_xboole_0 @ X20 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_subset_1 @ X0 @ X0 @ X1 )
        = ( k2_xboole_0 @ X0 @ X1 ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_subset_1 @ X0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['46','52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['29','40','45','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,
    ( ( sk_B
      = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['22','56'])).

thf('58',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    ! [X32: $i,X33: $i] :
      ( ( r1_tarski @ X32 @ X33 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('60',plain,(
    r1_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('62',plain,(
    ! [X9: $i,X10: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X9 @ X10 ) @ X9 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('63',plain,
    ( ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['61','62'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('64',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r1_tarski @ X5 @ X6 )
      | ~ ( r1_tarski @ X6 @ X7 )
      | ( r1_tarski @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('65',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ X0 )
        | ~ ( r1_tarski @ sk_B @ X0 ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,
    ( ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['60','65'])).

thf('67',plain,(
    ! [X32: $i,X34: $i] :
      ( ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ X34 ) )
      | ~ ( r1_tarski @ X32 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('68',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X21 ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ X21 ) )
      | ( ( k4_subset_1 @ X21 @ X20 @ X22 )
        = ( k2_xboole_0 @ X20 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
        = ( k2_xboole_0 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,
    ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['68','71'])).

thf('73',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t65_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_pre_topc @ A @ B )
            = ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('74',plain,(
    ! [X42: $i,X43: $i] :
      ( ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X43 ) ) )
      | ( ( k2_pre_topc @ X43 @ X42 )
        = ( k4_subset_1 @ ( u1_struct_0 @ X43 ) @ X42 @ ( k2_tops_1 @ X43 @ X42 ) ) )
      | ~ ( l1_pre_topc @ X43 ) ) ),
    inference(cnf,[status(esa)],[t65_tops_1])).

thf('75',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
      = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['75','76'])).

thf('78',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B )
      = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['72','77'])).

thf('79',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['57','78'])).

thf('80',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc1_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v4_pre_topc @ ( k2_pre_topc @ A @ B ) @ A ) ) )).

thf('81',plain,(
    ! [X38: $i,X39: $i] :
      ( ~ ( l1_pre_topc @ X38 )
      | ~ ( v2_pre_topc @ X38 )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X38 ) ) )
      | ( v4_pre_topc @ ( k2_pre_topc @ X38 @ X39 ) @ X38 ) ) ),
    inference(cnf,[status(esa)],[fc1_tops_1])).

thf('82',plain,
    ( ( v4_pre_topc @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    v4_pre_topc @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['82','83','84'])).

thf('86',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['79','85'])).

thf('87',plain,
    ( ~ ( v4_pre_topc @ sk_B @ sk_A )
   <= ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['16'])).

thf('88',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['6'])).

thf('90',plain,(
    v4_pre_topc @ sk_B @ sk_A ),
    inference('sat_resolution*',[status(thm)],['17','88','89'])).

thf('91',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['15','90'])).

thf('92',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ X27 ) )
      | ( ( k3_subset_1 @ X27 @ ( k7_subset_1 @ X27 @ X28 @ X26 ) )
        = ( k4_subset_1 @ X27 @ ( k3_subset_1 @ X27 @ X28 ) @ X26 ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[t33_subset_1])).

thf('93',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_B ) )
      | ( ( k3_subset_1 @ sk_B @ ( k7_subset_1 @ sk_B @ X0 @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
        = ( k4_subset_1 @ sk_B @ ( k3_subset_1 @ sk_B @ X0 ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,
    ( ( k3_subset_1 @ sk_B @ ( k7_subset_1 @ sk_B @ k1_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
    = ( k4_subset_1 @ sk_B @ ( k3_subset_1 @ sk_B @ k1_xboole_0 ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['5','93'])).

thf('95',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_subset_1 @ X0 @ k1_xboole_0 @ X1 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['32','39'])).

thf('96',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('97',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('98',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_B ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('99',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_subset_1 @ X0 @ X0 @ X1 )
        = ( k2_xboole_0 @ X0 @ X1 ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('100',plain,
    ( ( ( k4_subset_1 @ sk_B @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,(
    v4_pre_topc @ sk_B @ sk_A ),
    inference('sat_resolution*',[status(thm)],['17','88','89'])).

thf('102',plain,
    ( ( k4_subset_1 @ sk_B @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(simpl_trail,[status(thm)],['100','101'])).

thf('103',plain,(
    r1_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('104',plain,
    ( ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['7','12'])).

thf('105',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r1_tarski @ X5 @ X6 )
      | ~ ( r1_tarski @ X6 @ X7 )
      | ( r1_tarski @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('106',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ X0 )
        | ~ ( r1_tarski @ sk_B @ X0 ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['104','105'])).

thf('107',plain,
    ( ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['103','106'])).

thf('108',plain,(
    ! [X32: $i,X34: $i] :
      ( ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ X34 ) )
      | ~ ( r1_tarski @ X32 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('109',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['107','108'])).

thf('110',plain,(
    v4_pre_topc @ sk_B @ sk_A ),
    inference('sat_resolution*',[status(thm)],['17','88','89'])).

thf('111',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simpl_trail,[status(thm)],['109','110'])).

thf('112',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
        = ( k2_xboole_0 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('113',plain,
    ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['111','112'])).

thf('114',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['75','76'])).

thf('115',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['113','114'])).

thf('116',plain,
    ( ( k4_subset_1 @ sk_B @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = ( k2_pre_topc @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['102','115'])).

thf('117',plain,
    ( sk_B
    = ( k2_pre_topc @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['94','95','96','97','116'])).

thf('118',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('119',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['4','117','118'])).

thf('120',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['16'])).

thf('121',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('122',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['120','121'])).

thf('123',plain,(
    ( k2_tops_1 @ sk_A @ sk_B )
 != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sat_resolution*',[status(thm)],['17','88'])).

thf('124',plain,(
    ( k2_tops_1 @ sk_A @ sk_B )
 != ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(simpl_trail,[status(thm)],['122','123'])).

thf('125',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['119','124'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ELuWutjn6G
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:14:45 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 8.86/9.07  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 8.86/9.07  % Solved by: fo/fo7.sh
% 8.86/9.07  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 8.86/9.07  % done 6567 iterations in 8.578s
% 8.86/9.07  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 8.86/9.07  % SZS output start Refutation
% 8.86/9.07  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 8.86/9.07  thf(sk_A_type, type, sk_A: $i).
% 8.86/9.07  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 8.86/9.07  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 8.86/9.07  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 8.86/9.07  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 8.86/9.07  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 8.86/9.07  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 8.86/9.07  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 8.86/9.07  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 8.86/9.07  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 8.86/9.07  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 8.86/9.07  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 8.86/9.07  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 8.86/9.07  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 8.86/9.07  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 8.86/9.07  thf(sk_B_type, type, sk_B: $i).
% 8.86/9.07  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 8.86/9.07  thf(t77_tops_1, conjecture,
% 8.86/9.07    (![A:$i]:
% 8.86/9.07     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 8.86/9.07       ( ![B:$i]:
% 8.86/9.07         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 8.86/9.07           ( ( v4_pre_topc @ B @ A ) <=>
% 8.86/9.07             ( ( k2_tops_1 @ A @ B ) =
% 8.86/9.07               ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ))).
% 8.86/9.07  thf(zf_stmt_0, negated_conjecture,
% 8.86/9.07    (~( ![A:$i]:
% 8.86/9.07        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 8.86/9.07          ( ![B:$i]:
% 8.86/9.07            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 8.86/9.07              ( ( v4_pre_topc @ B @ A ) <=>
% 8.86/9.07                ( ( k2_tops_1 @ A @ B ) =
% 8.86/9.07                  ( k7_subset_1 @
% 8.86/9.07                    ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ) )),
% 8.86/9.07    inference('cnf.neg', [status(esa)], [t77_tops_1])).
% 8.86/9.07  thf('0', plain,
% 8.86/9.07      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 8.86/9.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.86/9.07  thf(l78_tops_1, axiom,
% 8.86/9.07    (![A:$i]:
% 8.86/9.07     ( ( l1_pre_topc @ A ) =>
% 8.86/9.07       ( ![B:$i]:
% 8.86/9.07         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 8.86/9.07           ( ( k2_tops_1 @ A @ B ) =
% 8.86/9.07             ( k7_subset_1 @
% 8.86/9.07               ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 8.86/9.07               ( k1_tops_1 @ A @ B ) ) ) ) ) ))).
% 8.86/9.07  thf('1', plain,
% 8.86/9.07      (![X40 : $i, X41 : $i]:
% 8.86/9.07         (~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (u1_struct_0 @ X41)))
% 8.86/9.07          | ((k2_tops_1 @ X41 @ X40)
% 8.86/9.07              = (k7_subset_1 @ (u1_struct_0 @ X41) @ 
% 8.86/9.07                 (k2_pre_topc @ X41 @ X40) @ (k1_tops_1 @ X41 @ X40)))
% 8.86/9.07          | ~ (l1_pre_topc @ X41))),
% 8.86/9.07      inference('cnf', [status(esa)], [l78_tops_1])).
% 8.86/9.07  thf('2', plain,
% 8.86/9.07      ((~ (l1_pre_topc @ sk_A)
% 8.86/9.07        | ((k2_tops_1 @ sk_A @ sk_B)
% 8.86/9.07            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 8.86/9.07               (k2_pre_topc @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ sk_B))))),
% 8.86/9.07      inference('sup-', [status(thm)], ['0', '1'])).
% 8.86/9.07  thf('3', plain, ((l1_pre_topc @ sk_A)),
% 8.86/9.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.86/9.07  thf('4', plain,
% 8.86/9.07      (((k2_tops_1 @ sk_A @ sk_B)
% 8.86/9.07         = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 8.86/9.07            (k1_tops_1 @ sk_A @ sk_B)))),
% 8.86/9.07      inference('demod', [status(thm)], ['2', '3'])).
% 8.86/9.07  thf(t4_subset_1, axiom,
% 8.86/9.07    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 8.86/9.07  thf('5', plain,
% 8.86/9.07      (![X29 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X29))),
% 8.86/9.07      inference('cnf', [status(esa)], [t4_subset_1])).
% 8.86/9.07  thf('6', plain,
% 8.86/9.07      ((((k2_tops_1 @ sk_A @ sk_B)
% 8.86/9.07          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 8.86/9.07             (k1_tops_1 @ sk_A @ sk_B)))
% 8.86/9.07        | (v4_pre_topc @ sk_B @ sk_A))),
% 8.86/9.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.86/9.07  thf('7', plain,
% 8.86/9.07      (((v4_pre_topc @ sk_B @ sk_A)) <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 8.86/9.07      inference('split', [status(esa)], ['6'])).
% 8.86/9.07  thf('8', plain,
% 8.86/9.07      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 8.86/9.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.86/9.07  thf(t69_tops_1, axiom,
% 8.86/9.07    (![A:$i]:
% 8.86/9.07     ( ( l1_pre_topc @ A ) =>
% 8.86/9.07       ( ![B:$i]:
% 8.86/9.07         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 8.86/9.07           ( ( v4_pre_topc @ B @ A ) =>
% 8.86/9.07             ( r1_tarski @ ( k2_tops_1 @ A @ B ) @ B ) ) ) ) ))).
% 8.86/9.07  thf('9', plain,
% 8.86/9.07      (![X44 : $i, X45 : $i]:
% 8.86/9.07         (~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (u1_struct_0 @ X45)))
% 8.86/9.07          | (r1_tarski @ (k2_tops_1 @ X45 @ X44) @ X44)
% 8.86/9.07          | ~ (v4_pre_topc @ X44 @ X45)
% 8.86/9.07          | ~ (l1_pre_topc @ X45))),
% 8.86/9.07      inference('cnf', [status(esa)], [t69_tops_1])).
% 8.86/9.07  thf('10', plain,
% 8.86/9.07      ((~ (l1_pre_topc @ sk_A)
% 8.86/9.07        | ~ (v4_pre_topc @ sk_B @ sk_A)
% 8.86/9.07        | (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))),
% 8.86/9.07      inference('sup-', [status(thm)], ['8', '9'])).
% 8.86/9.07  thf('11', plain, ((l1_pre_topc @ sk_A)),
% 8.86/9.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.86/9.07  thf('12', plain,
% 8.86/9.07      ((~ (v4_pre_topc @ sk_B @ sk_A)
% 8.86/9.07        | (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))),
% 8.86/9.07      inference('demod', [status(thm)], ['10', '11'])).
% 8.86/9.07  thf('13', plain,
% 8.86/9.07      (((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))
% 8.86/9.07         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 8.86/9.07      inference('sup-', [status(thm)], ['7', '12'])).
% 8.86/9.07  thf(t3_subset, axiom,
% 8.86/9.07    (![A:$i,B:$i]:
% 8.86/9.07     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 8.86/9.07  thf('14', plain,
% 8.86/9.07      (![X32 : $i, X34 : $i]:
% 8.86/9.07         ((m1_subset_1 @ X32 @ (k1_zfmisc_1 @ X34)) | ~ (r1_tarski @ X32 @ X34))),
% 8.86/9.07      inference('cnf', [status(esa)], [t3_subset])).
% 8.86/9.07  thf('15', plain,
% 8.86/9.07      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_B)))
% 8.86/9.07         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 8.86/9.07      inference('sup-', [status(thm)], ['13', '14'])).
% 8.86/9.07  thf('16', plain,
% 8.86/9.07      ((((k2_tops_1 @ sk_A @ sk_B)
% 8.86/9.07          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 8.86/9.07              (k1_tops_1 @ sk_A @ sk_B)))
% 8.86/9.07        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 8.86/9.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.86/9.07  thf('17', plain,
% 8.86/9.07      (~
% 8.86/9.07       (((k2_tops_1 @ sk_A @ sk_B)
% 8.86/9.07          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 8.86/9.07             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 8.86/9.07       ~ ((v4_pre_topc @ sk_B @ sk_A))),
% 8.86/9.07      inference('split', [status(esa)], ['16'])).
% 8.86/9.07  thf('18', plain,
% 8.86/9.07      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 8.86/9.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.86/9.07  thf(redefinition_k7_subset_1, axiom,
% 8.86/9.07    (![A:$i,B:$i,C:$i]:
% 8.86/9.07     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 8.86/9.07       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 8.86/9.07  thf('19', plain,
% 8.86/9.07      (![X23 : $i, X24 : $i, X25 : $i]:
% 8.86/9.07         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ X24))
% 8.86/9.07          | ((k7_subset_1 @ X24 @ X23 @ X25) = (k4_xboole_0 @ X23 @ X25)))),
% 8.86/9.07      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 8.86/9.07  thf('20', plain,
% 8.86/9.07      (![X0 : $i]:
% 8.86/9.07         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 8.86/9.07           = (k4_xboole_0 @ sk_B @ X0))),
% 8.86/9.07      inference('sup-', [status(thm)], ['18', '19'])).
% 8.86/9.07  thf('21', plain,
% 8.86/9.07      ((((k2_tops_1 @ sk_A @ sk_B)
% 8.86/9.07          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 8.86/9.07             (k1_tops_1 @ sk_A @ sk_B))))
% 8.86/9.07         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 8.86/9.07                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 8.86/9.07                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 8.86/9.07      inference('split', [status(esa)], ['6'])).
% 8.86/9.07  thf('22', plain,
% 8.86/9.07      ((((k2_tops_1 @ sk_A @ sk_B)
% 8.86/9.07          = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 8.86/9.07         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 8.86/9.07                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 8.86/9.07                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 8.86/9.07      inference('sup+', [status(thm)], ['20', '21'])).
% 8.86/9.07  thf('23', plain,
% 8.86/9.07      (![X29 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X29))),
% 8.86/9.07      inference('cnf', [status(esa)], [t4_subset_1])).
% 8.86/9.07  thf(t36_xboole_1, axiom,
% 8.86/9.07    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 8.86/9.07  thf('24', plain,
% 8.86/9.07      (![X9 : $i, X10 : $i]: (r1_tarski @ (k4_xboole_0 @ X9 @ X10) @ X9)),
% 8.86/9.07      inference('cnf', [status(esa)], [t36_xboole_1])).
% 8.86/9.07  thf('25', plain,
% 8.86/9.07      (![X32 : $i, X34 : $i]:
% 8.86/9.07         ((m1_subset_1 @ X32 @ (k1_zfmisc_1 @ X34)) | ~ (r1_tarski @ X32 @ X34))),
% 8.86/9.07      inference('cnf', [status(esa)], [t3_subset])).
% 8.86/9.07  thf('26', plain,
% 8.86/9.07      (![X0 : $i, X1 : $i]:
% 8.86/9.07         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 8.86/9.07      inference('sup-', [status(thm)], ['24', '25'])).
% 8.86/9.07  thf(t33_subset_1, axiom,
% 8.86/9.07    (![A:$i,B:$i]:
% 8.86/9.07     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 8.86/9.07       ( ![C:$i]:
% 8.86/9.07         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 8.86/9.07           ( ( k3_subset_1 @ A @ ( k7_subset_1 @ A @ B @ C ) ) =
% 8.86/9.07             ( k4_subset_1 @ A @ ( k3_subset_1 @ A @ B ) @ C ) ) ) ) ))).
% 8.86/9.07  thf('27', plain,
% 8.86/9.07      (![X26 : $i, X27 : $i, X28 : $i]:
% 8.86/9.07         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ X27))
% 8.86/9.07          | ((k3_subset_1 @ X27 @ (k7_subset_1 @ X27 @ X28 @ X26))
% 8.86/9.07              = (k4_subset_1 @ X27 @ (k3_subset_1 @ X27 @ X28) @ X26))
% 8.86/9.07          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ X27)))),
% 8.86/9.07      inference('cnf', [status(esa)], [t33_subset_1])).
% 8.86/9.07  thf('28', plain,
% 8.86/9.07      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.86/9.07         (~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X0))
% 8.86/9.07          | ((k3_subset_1 @ X0 @ 
% 8.86/9.07              (k7_subset_1 @ X0 @ X2 @ (k4_xboole_0 @ X0 @ X1)))
% 8.86/9.07              = (k4_subset_1 @ X0 @ (k3_subset_1 @ X0 @ X2) @ 
% 8.86/9.07                 (k4_xboole_0 @ X0 @ X1))))),
% 8.86/9.07      inference('sup-', [status(thm)], ['26', '27'])).
% 8.86/9.07  thf('29', plain,
% 8.86/9.07      (![X0 : $i, X1 : $i]:
% 8.86/9.07         ((k3_subset_1 @ X0 @ 
% 8.86/9.07           (k7_subset_1 @ X0 @ k1_xboole_0 @ (k4_xboole_0 @ X0 @ X1)))
% 8.86/9.07           = (k4_subset_1 @ X0 @ (k3_subset_1 @ X0 @ k1_xboole_0) @ 
% 8.86/9.07              (k4_xboole_0 @ X0 @ X1)))),
% 8.86/9.07      inference('sup-', [status(thm)], ['23', '28'])).
% 8.86/9.07  thf('30', plain,
% 8.86/9.07      (![X29 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X29))),
% 8.86/9.07      inference('cnf', [status(esa)], [t4_subset_1])).
% 8.86/9.07  thf('31', plain,
% 8.86/9.07      (![X23 : $i, X24 : $i, X25 : $i]:
% 8.86/9.07         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ X24))
% 8.86/9.07          | ((k7_subset_1 @ X24 @ X23 @ X25) = (k4_xboole_0 @ X23 @ X25)))),
% 8.86/9.07      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 8.86/9.07  thf('32', plain,
% 8.86/9.07      (![X0 : $i, X1 : $i]:
% 8.86/9.07         ((k7_subset_1 @ X0 @ k1_xboole_0 @ X1)
% 8.86/9.07           = (k4_xboole_0 @ k1_xboole_0 @ X1))),
% 8.86/9.07      inference('sup-', [status(thm)], ['30', '31'])).
% 8.86/9.07  thf('33', plain,
% 8.86/9.07      (![X9 : $i, X10 : $i]: (r1_tarski @ (k4_xboole_0 @ X9 @ X10) @ X9)),
% 8.86/9.07      inference('cnf', [status(esa)], [t36_xboole_1])).
% 8.86/9.07  thf('34', plain,
% 8.86/9.07      (![X29 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X29))),
% 8.86/9.07      inference('cnf', [status(esa)], [t4_subset_1])).
% 8.86/9.07  thf('35', plain,
% 8.86/9.07      (![X32 : $i, X33 : $i]:
% 8.86/9.07         ((r1_tarski @ X32 @ X33) | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ X33)))),
% 8.86/9.07      inference('cnf', [status(esa)], [t3_subset])).
% 8.86/9.07  thf('36', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 8.86/9.07      inference('sup-', [status(thm)], ['34', '35'])).
% 8.86/9.07  thf(d10_xboole_0, axiom,
% 8.86/9.07    (![A:$i,B:$i]:
% 8.86/9.07     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 8.86/9.07  thf('37', plain,
% 8.86/9.07      (![X0 : $i, X2 : $i]:
% 8.86/9.07         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 8.86/9.07      inference('cnf', [status(esa)], [d10_xboole_0])).
% 8.86/9.07  thf('38', plain,
% 8.86/9.07      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 8.86/9.07      inference('sup-', [status(thm)], ['36', '37'])).
% 8.86/9.07  thf('39', plain,
% 8.86/9.07      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 8.86/9.07      inference('sup-', [status(thm)], ['33', '38'])).
% 8.86/9.07  thf('40', plain,
% 8.86/9.07      (![X0 : $i, X1 : $i]:
% 8.86/9.07         ((k7_subset_1 @ X0 @ k1_xboole_0 @ X1) = (k1_xboole_0))),
% 8.86/9.07      inference('demod', [status(thm)], ['32', '39'])).
% 8.86/9.07  thf('41', plain,
% 8.86/9.07      (![X29 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X29))),
% 8.86/9.07      inference('cnf', [status(esa)], [t4_subset_1])).
% 8.86/9.07  thf(d5_subset_1, axiom,
% 8.86/9.07    (![A:$i,B:$i]:
% 8.86/9.07     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 8.86/9.07       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 8.86/9.07  thf('42', plain,
% 8.86/9.07      (![X16 : $i, X17 : $i]:
% 8.86/9.07         (((k3_subset_1 @ X16 @ X17) = (k4_xboole_0 @ X16 @ X17))
% 8.86/9.07          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X16)))),
% 8.86/9.07      inference('cnf', [status(esa)], [d5_subset_1])).
% 8.86/9.07  thf('43', plain,
% 8.86/9.07      (![X0 : $i]:
% 8.86/9.07         ((k3_subset_1 @ X0 @ k1_xboole_0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 8.86/9.07      inference('sup-', [status(thm)], ['41', '42'])).
% 8.86/9.07  thf(t3_boole, axiom,
% 8.86/9.07    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 8.86/9.07  thf('44', plain, (![X11 : $i]: ((k4_xboole_0 @ X11 @ k1_xboole_0) = (X11))),
% 8.86/9.07      inference('cnf', [status(esa)], [t3_boole])).
% 8.86/9.07  thf('45', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ k1_xboole_0) = (X0))),
% 8.86/9.07      inference('sup+', [status(thm)], ['43', '44'])).
% 8.86/9.07  thf('46', plain,
% 8.86/9.07      (![X0 : $i, X1 : $i]:
% 8.86/9.07         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 8.86/9.07      inference('sup-', [status(thm)], ['24', '25'])).
% 8.86/9.07  thf('47', plain,
% 8.86/9.07      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 8.86/9.07      inference('cnf', [status(esa)], [d10_xboole_0])).
% 8.86/9.07  thf('48', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 8.86/9.07      inference('simplify', [status(thm)], ['47'])).
% 8.86/9.07  thf('49', plain,
% 8.86/9.07      (![X32 : $i, X34 : $i]:
% 8.86/9.07         ((m1_subset_1 @ X32 @ (k1_zfmisc_1 @ X34)) | ~ (r1_tarski @ X32 @ X34))),
% 8.86/9.07      inference('cnf', [status(esa)], [t3_subset])).
% 8.86/9.07  thf('50', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 8.86/9.07      inference('sup-', [status(thm)], ['48', '49'])).
% 8.86/9.07  thf(redefinition_k4_subset_1, axiom,
% 8.86/9.07    (![A:$i,B:$i,C:$i]:
% 8.86/9.07     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 8.86/9.07         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 8.86/9.07       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 8.86/9.07  thf('51', plain,
% 8.86/9.07      (![X20 : $i, X21 : $i, X22 : $i]:
% 8.86/9.07         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X21))
% 8.86/9.07          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ X21))
% 8.86/9.07          | ((k4_subset_1 @ X21 @ X20 @ X22) = (k2_xboole_0 @ X20 @ X22)))),
% 8.86/9.07      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 8.86/9.07  thf('52', plain,
% 8.86/9.07      (![X0 : $i, X1 : $i]:
% 8.86/9.07         (((k4_subset_1 @ X0 @ X0 @ X1) = (k2_xboole_0 @ X0 @ X1))
% 8.86/9.07          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0)))),
% 8.86/9.07      inference('sup-', [status(thm)], ['50', '51'])).
% 8.86/9.07  thf('53', plain,
% 8.86/9.07      (![X0 : $i, X1 : $i]:
% 8.86/9.07         ((k4_subset_1 @ X0 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 8.86/9.07           = (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))),
% 8.86/9.07      inference('sup-', [status(thm)], ['46', '52'])).
% 8.86/9.07  thf('54', plain,
% 8.86/9.07      (![X0 : $i, X1 : $i]:
% 8.86/9.07         ((k3_subset_1 @ X0 @ k1_xboole_0)
% 8.86/9.07           = (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))),
% 8.86/9.07      inference('demod', [status(thm)], ['29', '40', '45', '53'])).
% 8.86/9.07  thf('55', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ k1_xboole_0) = (X0))),
% 8.86/9.07      inference('sup+', [status(thm)], ['43', '44'])).
% 8.86/9.07  thf('56', plain,
% 8.86/9.07      (![X0 : $i, X1 : $i]:
% 8.86/9.07         ((X0) = (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))),
% 8.86/9.07      inference('demod', [status(thm)], ['54', '55'])).
% 8.86/9.07  thf('57', plain,
% 8.86/9.07      ((((sk_B) = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))
% 8.86/9.07         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 8.86/9.07                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 8.86/9.07                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 8.86/9.07      inference('sup+', [status(thm)], ['22', '56'])).
% 8.86/9.07  thf('58', plain,
% 8.86/9.07      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 8.86/9.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.86/9.07  thf('59', plain,
% 8.86/9.07      (![X32 : $i, X33 : $i]:
% 8.86/9.07         ((r1_tarski @ X32 @ X33) | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ X33)))),
% 8.86/9.07      inference('cnf', [status(esa)], [t3_subset])).
% 8.86/9.07  thf('60', plain, ((r1_tarski @ sk_B @ (u1_struct_0 @ sk_A))),
% 8.86/9.07      inference('sup-', [status(thm)], ['58', '59'])).
% 8.86/9.07  thf('61', plain,
% 8.86/9.07      ((((k2_tops_1 @ sk_A @ sk_B)
% 8.86/9.07          = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 8.86/9.07         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 8.86/9.07                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 8.86/9.07                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 8.86/9.07      inference('sup+', [status(thm)], ['20', '21'])).
% 8.86/9.07  thf('62', plain,
% 8.86/9.07      (![X9 : $i, X10 : $i]: (r1_tarski @ (k4_xboole_0 @ X9 @ X10) @ X9)),
% 8.86/9.07      inference('cnf', [status(esa)], [t36_xboole_1])).
% 8.86/9.07  thf('63', plain,
% 8.86/9.07      (((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))
% 8.86/9.07         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 8.86/9.07                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 8.86/9.07                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 8.86/9.07      inference('sup+', [status(thm)], ['61', '62'])).
% 8.86/9.07  thf(t1_xboole_1, axiom,
% 8.86/9.07    (![A:$i,B:$i,C:$i]:
% 8.86/9.07     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 8.86/9.07       ( r1_tarski @ A @ C ) ))).
% 8.86/9.07  thf('64', plain,
% 8.86/9.07      (![X5 : $i, X6 : $i, X7 : $i]:
% 8.86/9.07         (~ (r1_tarski @ X5 @ X6)
% 8.86/9.07          | ~ (r1_tarski @ X6 @ X7)
% 8.86/9.07          | (r1_tarski @ X5 @ X7))),
% 8.86/9.07      inference('cnf', [status(esa)], [t1_xboole_1])).
% 8.86/9.07  thf('65', plain,
% 8.86/9.07      ((![X0 : $i]:
% 8.86/9.07          ((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ X0)
% 8.86/9.07           | ~ (r1_tarski @ sk_B @ X0)))
% 8.86/9.07         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 8.86/9.07                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 8.86/9.07                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 8.86/9.07      inference('sup-', [status(thm)], ['63', '64'])).
% 8.86/9.07  thf('66', plain,
% 8.86/9.07      (((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A)))
% 8.86/9.07         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 8.86/9.07                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 8.86/9.07                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 8.86/9.07      inference('sup-', [status(thm)], ['60', '65'])).
% 8.86/9.07  thf('67', plain,
% 8.86/9.07      (![X32 : $i, X34 : $i]:
% 8.86/9.07         ((m1_subset_1 @ X32 @ (k1_zfmisc_1 @ X34)) | ~ (r1_tarski @ X32 @ X34))),
% 8.86/9.07      inference('cnf', [status(esa)], [t3_subset])).
% 8.86/9.07  thf('68', plain,
% 8.86/9.07      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 8.86/9.07         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 8.86/9.07         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 8.86/9.07                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 8.86/9.07                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 8.86/9.07      inference('sup-', [status(thm)], ['66', '67'])).
% 8.86/9.07  thf('69', plain,
% 8.86/9.07      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 8.86/9.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.86/9.07  thf('70', plain,
% 8.86/9.07      (![X20 : $i, X21 : $i, X22 : $i]:
% 8.86/9.07         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X21))
% 8.86/9.07          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ X21))
% 8.86/9.07          | ((k4_subset_1 @ X21 @ X20 @ X22) = (k2_xboole_0 @ X20 @ X22)))),
% 8.86/9.07      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 8.86/9.07  thf('71', plain,
% 8.86/9.07      (![X0 : $i]:
% 8.86/9.07         (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 8.86/9.07            = (k2_xboole_0 @ sk_B @ X0))
% 8.86/9.07          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 8.86/9.07      inference('sup-', [status(thm)], ['69', '70'])).
% 8.86/9.07  thf('72', plain,
% 8.86/9.07      ((((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 8.86/9.07          = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))
% 8.86/9.07         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 8.86/9.07                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 8.86/9.07                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 8.86/9.07      inference('sup-', [status(thm)], ['68', '71'])).
% 8.86/9.07  thf('73', plain,
% 8.86/9.07      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 8.86/9.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.86/9.07  thf(t65_tops_1, axiom,
% 8.86/9.07    (![A:$i]:
% 8.86/9.07     ( ( l1_pre_topc @ A ) =>
% 8.86/9.07       ( ![B:$i]:
% 8.86/9.07         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 8.86/9.07           ( ( k2_pre_topc @ A @ B ) =
% 8.86/9.07             ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 8.86/9.07  thf('74', plain,
% 8.86/9.07      (![X42 : $i, X43 : $i]:
% 8.86/9.07         (~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (u1_struct_0 @ X43)))
% 8.86/9.07          | ((k2_pre_topc @ X43 @ X42)
% 8.86/9.07              = (k4_subset_1 @ (u1_struct_0 @ X43) @ X42 @ 
% 8.86/9.07                 (k2_tops_1 @ X43 @ X42)))
% 8.86/9.07          | ~ (l1_pre_topc @ X43))),
% 8.86/9.07      inference('cnf', [status(esa)], [t65_tops_1])).
% 8.86/9.07  thf('75', plain,
% 8.86/9.07      ((~ (l1_pre_topc @ sk_A)
% 8.86/9.07        | ((k2_pre_topc @ sk_A @ sk_B)
% 8.86/9.07            = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 8.86/9.07               (k2_tops_1 @ sk_A @ sk_B))))),
% 8.86/9.07      inference('sup-', [status(thm)], ['73', '74'])).
% 8.86/9.07  thf('76', plain, ((l1_pre_topc @ sk_A)),
% 8.86/9.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.86/9.07  thf('77', plain,
% 8.86/9.07      (((k2_pre_topc @ sk_A @ sk_B)
% 8.86/9.07         = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 8.86/9.07            (k2_tops_1 @ sk_A @ sk_B)))),
% 8.86/9.07      inference('demod', [status(thm)], ['75', '76'])).
% 8.86/9.07  thf('78', plain,
% 8.86/9.07      ((((k2_pre_topc @ sk_A @ sk_B)
% 8.86/9.07          = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))
% 8.86/9.07         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 8.86/9.07                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 8.86/9.07                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 8.86/9.07      inference('sup+', [status(thm)], ['72', '77'])).
% 8.86/9.07  thf('79', plain,
% 8.86/9.07      ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B)))
% 8.86/9.07         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 8.86/9.07                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 8.86/9.07                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 8.86/9.07      inference('sup+', [status(thm)], ['57', '78'])).
% 8.86/9.07  thf('80', plain,
% 8.86/9.07      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 8.86/9.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.86/9.07  thf(fc1_tops_1, axiom,
% 8.86/9.07    (![A:$i,B:$i]:
% 8.86/9.07     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 8.86/9.07         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 8.86/9.07       ( v4_pre_topc @ ( k2_pre_topc @ A @ B ) @ A ) ))).
% 8.86/9.07  thf('81', plain,
% 8.86/9.07      (![X38 : $i, X39 : $i]:
% 8.86/9.07         (~ (l1_pre_topc @ X38)
% 8.86/9.07          | ~ (v2_pre_topc @ X38)
% 8.86/9.07          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (u1_struct_0 @ X38)))
% 8.86/9.07          | (v4_pre_topc @ (k2_pre_topc @ X38 @ X39) @ X38))),
% 8.86/9.07      inference('cnf', [status(esa)], [fc1_tops_1])).
% 8.86/9.07  thf('82', plain,
% 8.86/9.07      (((v4_pre_topc @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A)
% 8.86/9.07        | ~ (v2_pre_topc @ sk_A)
% 8.86/9.07        | ~ (l1_pre_topc @ sk_A))),
% 8.86/9.07      inference('sup-', [status(thm)], ['80', '81'])).
% 8.86/9.07  thf('83', plain, ((v2_pre_topc @ sk_A)),
% 8.86/9.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.86/9.07  thf('84', plain, ((l1_pre_topc @ sk_A)),
% 8.86/9.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.86/9.07  thf('85', plain, ((v4_pre_topc @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A)),
% 8.86/9.07      inference('demod', [status(thm)], ['82', '83', '84'])).
% 8.86/9.07  thf('86', plain,
% 8.86/9.07      (((v4_pre_topc @ sk_B @ sk_A))
% 8.86/9.07         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 8.86/9.07                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 8.86/9.07                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 8.86/9.07      inference('sup+', [status(thm)], ['79', '85'])).
% 8.86/9.07  thf('87', plain,
% 8.86/9.07      ((~ (v4_pre_topc @ sk_B @ sk_A)) <= (~ ((v4_pre_topc @ sk_B @ sk_A)))),
% 8.86/9.07      inference('split', [status(esa)], ['16'])).
% 8.86/9.07  thf('88', plain,
% 8.86/9.07      (((v4_pre_topc @ sk_B @ sk_A)) | 
% 8.86/9.07       ~
% 8.86/9.07       (((k2_tops_1 @ sk_A @ sk_B)
% 8.86/9.07          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 8.86/9.07             (k1_tops_1 @ sk_A @ sk_B))))),
% 8.86/9.07      inference('sup-', [status(thm)], ['86', '87'])).
% 8.86/9.07  thf('89', plain,
% 8.86/9.07      (((v4_pre_topc @ sk_B @ sk_A)) | 
% 8.86/9.07       (((k2_tops_1 @ sk_A @ sk_B)
% 8.86/9.07          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 8.86/9.07             (k1_tops_1 @ sk_A @ sk_B))))),
% 8.86/9.07      inference('split', [status(esa)], ['6'])).
% 8.86/9.07  thf('90', plain, (((v4_pre_topc @ sk_B @ sk_A))),
% 8.86/9.07      inference('sat_resolution*', [status(thm)], ['17', '88', '89'])).
% 8.86/9.07  thf('91', plain,
% 8.86/9.07      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_B))),
% 8.86/9.07      inference('simpl_trail', [status(thm)], ['15', '90'])).
% 8.86/9.07  thf('92', plain,
% 8.86/9.07      (![X26 : $i, X27 : $i, X28 : $i]:
% 8.86/9.07         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ X27))
% 8.86/9.07          | ((k3_subset_1 @ X27 @ (k7_subset_1 @ X27 @ X28 @ X26))
% 8.86/9.07              = (k4_subset_1 @ X27 @ (k3_subset_1 @ X27 @ X28) @ X26))
% 8.86/9.07          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ X27)))),
% 8.86/9.07      inference('cnf', [status(esa)], [t33_subset_1])).
% 8.86/9.07  thf('93', plain,
% 8.86/9.07      (![X0 : $i]:
% 8.86/9.07         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_B))
% 8.86/9.07          | ((k3_subset_1 @ sk_B @ 
% 8.86/9.07              (k7_subset_1 @ sk_B @ X0 @ (k2_tops_1 @ sk_A @ sk_B)))
% 8.86/9.07              = (k4_subset_1 @ sk_B @ (k3_subset_1 @ sk_B @ X0) @ 
% 8.86/9.07                 (k2_tops_1 @ sk_A @ sk_B))))),
% 8.86/9.07      inference('sup-', [status(thm)], ['91', '92'])).
% 8.86/9.07  thf('94', plain,
% 8.86/9.07      (((k3_subset_1 @ sk_B @ 
% 8.86/9.07         (k7_subset_1 @ sk_B @ k1_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B)))
% 8.86/9.07         = (k4_subset_1 @ sk_B @ (k3_subset_1 @ sk_B @ k1_xboole_0) @ 
% 8.86/9.07            (k2_tops_1 @ sk_A @ sk_B)))),
% 8.86/9.07      inference('sup-', [status(thm)], ['5', '93'])).
% 8.86/9.07  thf('95', plain,
% 8.86/9.07      (![X0 : $i, X1 : $i]:
% 8.86/9.07         ((k7_subset_1 @ X0 @ k1_xboole_0 @ X1) = (k1_xboole_0))),
% 8.86/9.07      inference('demod', [status(thm)], ['32', '39'])).
% 8.86/9.07  thf('96', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ k1_xboole_0) = (X0))),
% 8.86/9.07      inference('sup+', [status(thm)], ['43', '44'])).
% 8.86/9.07  thf('97', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ k1_xboole_0) = (X0))),
% 8.86/9.07      inference('sup+', [status(thm)], ['43', '44'])).
% 8.86/9.07  thf('98', plain,
% 8.86/9.07      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_B)))
% 8.86/9.07         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 8.86/9.07      inference('sup-', [status(thm)], ['13', '14'])).
% 8.86/9.07  thf('99', plain,
% 8.86/9.07      (![X0 : $i, X1 : $i]:
% 8.86/9.07         (((k4_subset_1 @ X0 @ X0 @ X1) = (k2_xboole_0 @ X0 @ X1))
% 8.86/9.07          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0)))),
% 8.86/9.07      inference('sup-', [status(thm)], ['50', '51'])).
% 8.86/9.07  thf('100', plain,
% 8.86/9.07      ((((k4_subset_1 @ sk_B @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 8.86/9.07          = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))
% 8.86/9.07         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 8.86/9.07      inference('sup-', [status(thm)], ['98', '99'])).
% 8.86/9.07  thf('101', plain, (((v4_pre_topc @ sk_B @ sk_A))),
% 8.86/9.07      inference('sat_resolution*', [status(thm)], ['17', '88', '89'])).
% 8.86/9.07  thf('102', plain,
% 8.86/9.07      (((k4_subset_1 @ sk_B @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 8.86/9.07         = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 8.86/9.07      inference('simpl_trail', [status(thm)], ['100', '101'])).
% 8.86/9.07  thf('103', plain, ((r1_tarski @ sk_B @ (u1_struct_0 @ sk_A))),
% 8.86/9.07      inference('sup-', [status(thm)], ['58', '59'])).
% 8.86/9.07  thf('104', plain,
% 8.86/9.07      (((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))
% 8.86/9.07         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 8.86/9.07      inference('sup-', [status(thm)], ['7', '12'])).
% 8.86/9.07  thf('105', plain,
% 8.86/9.07      (![X5 : $i, X6 : $i, X7 : $i]:
% 8.86/9.07         (~ (r1_tarski @ X5 @ X6)
% 8.86/9.07          | ~ (r1_tarski @ X6 @ X7)
% 8.86/9.07          | (r1_tarski @ X5 @ X7))),
% 8.86/9.07      inference('cnf', [status(esa)], [t1_xboole_1])).
% 8.86/9.07  thf('106', plain,
% 8.86/9.07      ((![X0 : $i]:
% 8.86/9.07          ((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ X0)
% 8.86/9.07           | ~ (r1_tarski @ sk_B @ X0)))
% 8.86/9.07         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 8.86/9.07      inference('sup-', [status(thm)], ['104', '105'])).
% 8.86/9.07  thf('107', plain,
% 8.86/9.07      (((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A)))
% 8.86/9.07         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 8.86/9.07      inference('sup-', [status(thm)], ['103', '106'])).
% 8.86/9.07  thf('108', plain,
% 8.86/9.07      (![X32 : $i, X34 : $i]:
% 8.86/9.07         ((m1_subset_1 @ X32 @ (k1_zfmisc_1 @ X34)) | ~ (r1_tarski @ X32 @ X34))),
% 8.86/9.07      inference('cnf', [status(esa)], [t3_subset])).
% 8.86/9.07  thf('109', plain,
% 8.86/9.07      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 8.86/9.07         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 8.86/9.07         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 8.86/9.07      inference('sup-', [status(thm)], ['107', '108'])).
% 8.86/9.07  thf('110', plain, (((v4_pre_topc @ sk_B @ sk_A))),
% 8.86/9.07      inference('sat_resolution*', [status(thm)], ['17', '88', '89'])).
% 8.86/9.07  thf('111', plain,
% 8.86/9.07      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 8.86/9.07        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 8.86/9.07      inference('simpl_trail', [status(thm)], ['109', '110'])).
% 8.86/9.07  thf('112', plain,
% 8.86/9.07      (![X0 : $i]:
% 8.86/9.07         (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 8.86/9.07            = (k2_xboole_0 @ sk_B @ X0))
% 8.86/9.07          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 8.86/9.07      inference('sup-', [status(thm)], ['69', '70'])).
% 8.86/9.07  thf('113', plain,
% 8.86/9.07      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 8.86/9.07         = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 8.86/9.07      inference('sup-', [status(thm)], ['111', '112'])).
% 8.86/9.07  thf('114', plain,
% 8.86/9.07      (((k2_pre_topc @ sk_A @ sk_B)
% 8.86/9.07         = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 8.86/9.07            (k2_tops_1 @ sk_A @ sk_B)))),
% 8.86/9.07      inference('demod', [status(thm)], ['75', '76'])).
% 8.86/9.07  thf('115', plain,
% 8.86/9.07      (((k2_pre_topc @ sk_A @ sk_B)
% 8.86/9.07         = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 8.86/9.07      inference('sup+', [status(thm)], ['113', '114'])).
% 8.86/9.07  thf('116', plain,
% 8.86/9.07      (((k4_subset_1 @ sk_B @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 8.86/9.07         = (k2_pre_topc @ sk_A @ sk_B))),
% 8.86/9.07      inference('demod', [status(thm)], ['102', '115'])).
% 8.86/9.07  thf('117', plain, (((sk_B) = (k2_pre_topc @ sk_A @ sk_B))),
% 8.86/9.07      inference('demod', [status(thm)], ['94', '95', '96', '97', '116'])).
% 8.86/9.07  thf('118', plain,
% 8.86/9.07      (![X0 : $i]:
% 8.86/9.07         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 8.86/9.07           = (k4_xboole_0 @ sk_B @ X0))),
% 8.86/9.07      inference('sup-', [status(thm)], ['18', '19'])).
% 8.86/9.07  thf('119', plain,
% 8.86/9.07      (((k2_tops_1 @ sk_A @ sk_B)
% 8.86/9.07         = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))),
% 8.86/9.07      inference('demod', [status(thm)], ['4', '117', '118'])).
% 8.86/9.07  thf('120', plain,
% 8.86/9.07      ((((k2_tops_1 @ sk_A @ sk_B)
% 8.86/9.07          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 8.86/9.07              (k1_tops_1 @ sk_A @ sk_B))))
% 8.86/9.07         <= (~
% 8.86/9.07             (((k2_tops_1 @ sk_A @ sk_B)
% 8.86/9.07                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 8.86/9.07                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 8.86/9.07      inference('split', [status(esa)], ['16'])).
% 8.86/9.07  thf('121', plain,
% 8.86/9.07      (![X0 : $i]:
% 8.86/9.07         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 8.86/9.07           = (k4_xboole_0 @ sk_B @ X0))),
% 8.86/9.07      inference('sup-', [status(thm)], ['18', '19'])).
% 8.86/9.07  thf('122', plain,
% 8.86/9.07      ((((k2_tops_1 @ sk_A @ sk_B)
% 8.86/9.07          != (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 8.86/9.07         <= (~
% 8.86/9.07             (((k2_tops_1 @ sk_A @ sk_B)
% 8.86/9.07                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 8.86/9.07                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 8.86/9.07      inference('demod', [status(thm)], ['120', '121'])).
% 8.86/9.07  thf('123', plain,
% 8.86/9.07      (~
% 8.86/9.07       (((k2_tops_1 @ sk_A @ sk_B)
% 8.86/9.07          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 8.86/9.07             (k1_tops_1 @ sk_A @ sk_B))))),
% 8.86/9.07      inference('sat_resolution*', [status(thm)], ['17', '88'])).
% 8.86/9.07  thf('124', plain,
% 8.86/9.07      (((k2_tops_1 @ sk_A @ sk_B)
% 8.86/9.07         != (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))),
% 8.86/9.07      inference('simpl_trail', [status(thm)], ['122', '123'])).
% 8.86/9.07  thf('125', plain, ($false),
% 8.86/9.07      inference('simplify_reflect-', [status(thm)], ['119', '124'])).
% 8.86/9.07  
% 8.86/9.07  % SZS output end Refutation
% 8.86/9.07  
% 8.86/9.08  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
