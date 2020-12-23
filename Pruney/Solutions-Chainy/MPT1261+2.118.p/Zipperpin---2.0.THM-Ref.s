%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.djqszQjL8c

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:55 EST 2020

% Result     : Theorem 0.50s
% Output     : Refutation 0.50s
% Verified   : 
% Statistics : Number of formulae       :  150 ( 460 expanded)
%              Number of leaves         :   34 ( 145 expanded)
%              Depth                    :   14
%              Number of atoms          : 1626 (6372 expanded)
%              Number of equality atoms :  120 ( 366 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

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

thf('0',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t69_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v4_pre_topc @ B @ A )
           => ( r1_tarski @ ( k2_tops_1 @ A @ B ) @ B ) ) ) ) )).

thf('5',plain,(
    ! [X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X33 ) ) )
      | ( r1_tarski @ ( k2_tops_1 @ X33 @ X32 ) @ X32 )
      | ~ ( v4_pre_topc @ X32 @ X33 )
      | ~ ( l1_pre_topc @ X33 ) ) ),
    inference(cnf,[status(esa)],[t69_tops_1])).

thf('6',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v4_pre_topc @ sk_B @ sk_A )
    | ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ~ ( v4_pre_topc @ sk_B @ sk_A )
    | ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,
    ( ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['3','8'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('10',plain,(
    ! [X23: $i,X25: $i] :
      ( ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ X25 ) )
      | ~ ( r1_tarski @ X23 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('11',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_B ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('12',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k3_subset_1 @ X12 @ ( k3_subset_1 @ X12 @ X11 ) )
        = X11 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('13',plain,
    ( ( ( k3_subset_1 @ sk_B @ ( k3_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
      = ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t74_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k1_tops_1 @ A @ B )
            = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('15',plain,(
    ! [X34: $i,X35: $i] :
      ( ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X35 ) ) )
      | ( ( k1_tops_1 @ X35 @ X34 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X35 ) @ X34 @ ( k2_tops_1 @ X35 @ X34 ) ) )
      | ~ ( l1_pre_topc @ X35 ) ) ),
    inference(cnf,[status(esa)],[t74_tops_1])).

thf('16',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('19',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X17 ) )
      | ( ( k7_subset_1 @ X17 @ X16 @ X18 )
        = ( k4_xboole_0 @ X16 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['16','17','20'])).

thf('22',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_B ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('23',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k3_subset_1 @ X9 @ X10 )
        = ( k4_xboole_0 @ X9 @ X10 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('24',plain,
    ( ( ( k3_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,
    ( ( ( k3_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k1_tops_1 @ sk_A @ sk_B ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['21','24'])).

thf('26',plain,
    ( ( ( k3_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
      = ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['13','25'])).

thf('27',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['16','17','20'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('28',plain,(
    ! [X4: $i,X5: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X4 @ X5 ) @ X4 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('29',plain,(
    ! [X23: $i,X25: $i] :
      ( ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ X25 ) )
      | ~ ( r1_tarski @ X23 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k3_subset_1 @ X9 @ X10 )
        = ( k4_xboole_0 @ X9 @ X10 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,
    ( ( k3_subset_1 @ sk_B @ ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
    = ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['27','32'])).

thf('34',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['16','17','20'])).

thf('35',plain,
    ( ( k3_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('37',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('38',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k3_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['35','38'])).

thf('40',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( ( ( k2_tops_1 @ sk_A @ sk_B )
       != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
      & ( v4_pre_topc @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['26','39'])).

thf('41',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('43',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['16','17','20'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('45',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('47',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['2'])).

thf('48',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('50',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('51',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X14 ) )
      | ( ( k4_subset_1 @ X14 @ X13 @ X15 )
        = ( k2_xboole_0 @ X13 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('52',plain,
    ( ! [X0: $i] :
        ( ( ( k4_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) @ X0 )
          = ( k2_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ X0 ) )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,
    ( ( ( k4_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) )
      = ( k2_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['45','52'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('55',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['16','17','20'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('56',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ X6 @ ( k4_xboole_0 @ X7 @ X6 ) )
      = ( k2_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('57',plain,
    ( ( k2_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k2_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup+',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('60',plain,
    ( ( k2_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['57','58','59'])).

thf('61',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('62',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( l1_pre_topc @ X28 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ( m1_subset_1 @ ( k2_tops_1 @ X28 @ X29 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_1])).

thf('63',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('66',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X14 ) )
      | ( ( k4_subset_1 @ X14 @ X13 @ X15 )
        = ( k2_xboole_0 @ X13 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
        = ( k2_xboole_0 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,
    ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['65','68'])).

thf('70',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t65_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_pre_topc @ A @ B )
            = ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('71',plain,(
    ! [X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X31 ) ) )
      | ( ( k2_pre_topc @ X31 @ X30 )
        = ( k4_subset_1 @ ( u1_struct_0 @ X31 ) @ X30 @ ( k2_tops_1 @ X31 @ X30 ) ) )
      | ~ ( l1_pre_topc @ X31 ) ) ),
    inference(cnf,[status(esa)],[t65_tops_1])).

thf('72',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
      = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('75',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['69','74'])).

thf('76',plain,
    ( ( k2_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = ( k2_pre_topc @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['60','75'])).

thf('77',plain,
    ( ( ( k4_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) )
      = ( k2_pre_topc @ sk_A @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['53','54','76'])).

thf('78',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf(t25_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k4_subset_1 @ A @ B @ ( k3_subset_1 @ A @ B ) )
        = ( k2_subset_1 @ A ) ) ) )).

thf('80',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k4_subset_1 @ X19 @ X20 @ ( k3_subset_1 @ X19 @ X20 ) )
        = ( k2_subset_1 @ X19 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t25_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('81',plain,(
    ! [X8: $i] :
      ( ( k2_subset_1 @ X8 )
      = X8 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('82',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k4_subset_1 @ X19 @ X20 @ ( k3_subset_1 @ X19 @ X20 ) )
        = X19 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X19 ) ) ) ),
    inference(demod,[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_subset_1 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k3_subset_1 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) )
      = X0 ) ),
    inference('sup-',[status(thm)],['79','82'])).

thf('84',plain,
    ( ( ( k4_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k3_subset_1 @ sk_B @ ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['78','83'])).

thf('85',plain,
    ( ( k3_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('86',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf('87',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('88',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k3_subset_1 @ X12 @ ( k3_subset_1 @ X12 @ X11 ) )
        = X11 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('89',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k3_subset_1 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,
    ( ( ( k3_subset_1 @ sk_B @ ( k3_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
      = ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['86','89'])).

thf('91',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf('92',plain,
    ( ( ( k3_subset_1 @ sk_B @ ( k3_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
      = ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['90','91'])).

thf('93',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['16','17','20'])).

thf('94',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf('95',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('96',plain,
    ( ( ( k3_subset_1 @ sk_B @ ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
      = ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['94','95'])).

thf('97',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf('98',plain,
    ( ( ( k3_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['96','97'])).

thf('99',plain,
    ( ( ( k3_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k1_tops_1 @ sk_A @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['93','98'])).

thf('100',plain,
    ( ( ( k3_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
      = ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['92','99'])).

thf('101',plain,
    ( ( ( k3_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k1_tops_1 @ sk_A @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['93','98'])).

thf('102',plain,
    ( ( ( k4_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['84','85','100','101'])).

thf('103',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['77','102'])).

thf('104',plain,(
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

thf('105',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
      | ~ ( v2_pre_topc @ X27 )
      | ( ( k2_pre_topc @ X27 @ X26 )
       != X26 )
      | ( v4_pre_topc @ X26 @ X27 )
      | ~ ( l1_pre_topc @ X27 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('106',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v4_pre_topc @ sk_B @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
     != sk_B )
    | ~ ( v2_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['104','105'])).

thf('107',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
     != sk_B ) ),
    inference(demod,[status(thm)],['106','107','108'])).

thf('110',plain,
    ( ( ( sk_B != sk_B )
      | ( v4_pre_topc @ sk_B @ sk_A ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['103','109'])).

thf('111',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['110'])).

thf('112',plain,
    ( ~ ( v4_pre_topc @ sk_B @ sk_A )
   <= ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('113',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['111','112'])).

thf('114',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','41','42','113'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.djqszQjL8c
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:11:33 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.50/0.71  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.50/0.71  % Solved by: fo/fo7.sh
% 0.50/0.71  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.50/0.71  % done 482 iterations in 0.255s
% 0.50/0.71  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.50/0.71  % SZS output start Refutation
% 0.50/0.71  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.50/0.71  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.50/0.71  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.50/0.71  thf(sk_B_type, type, sk_B: $i).
% 0.50/0.71  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.50/0.71  thf(sk_A_type, type, sk_A: $i).
% 0.50/0.71  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 0.50/0.71  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.50/0.71  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.50/0.71  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.50/0.71  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 0.50/0.71  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.50/0.71  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.50/0.71  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.50/0.71  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.50/0.71  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.50/0.71  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.50/0.71  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 0.50/0.71  thf(t77_tops_1, conjecture,
% 0.50/0.71    (![A:$i]:
% 0.50/0.71     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.50/0.71       ( ![B:$i]:
% 0.50/0.71         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.50/0.71           ( ( v4_pre_topc @ B @ A ) <=>
% 0.50/0.71             ( ( k2_tops_1 @ A @ B ) =
% 0.50/0.71               ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ))).
% 0.50/0.71  thf(zf_stmt_0, negated_conjecture,
% 0.50/0.71    (~( ![A:$i]:
% 0.50/0.71        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.50/0.71          ( ![B:$i]:
% 0.50/0.71            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.50/0.71              ( ( v4_pre_topc @ B @ A ) <=>
% 0.50/0.71                ( ( k2_tops_1 @ A @ B ) =
% 0.50/0.71                  ( k7_subset_1 @
% 0.50/0.71                    ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ) )),
% 0.50/0.71    inference('cnf.neg', [status(esa)], [t77_tops_1])).
% 0.50/0.71  thf('0', plain,
% 0.50/0.71      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.50/0.71          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.50/0.71              (k1_tops_1 @ sk_A @ sk_B)))
% 0.50/0.71        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.50/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.71  thf('1', plain,
% 0.50/0.71      (~
% 0.50/0.71       (((k2_tops_1 @ sk_A @ sk_B)
% 0.50/0.71          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.50/0.71             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 0.50/0.71       ~ ((v4_pre_topc @ sk_B @ sk_A))),
% 0.50/0.71      inference('split', [status(esa)], ['0'])).
% 0.50/0.71  thf('2', plain,
% 0.50/0.71      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.50/0.71          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.50/0.71             (k1_tops_1 @ sk_A @ sk_B)))
% 0.50/0.71        | (v4_pre_topc @ sk_B @ sk_A))),
% 0.50/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.71  thf('3', plain,
% 0.50/0.71      (((v4_pre_topc @ sk_B @ sk_A)) <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.50/0.71      inference('split', [status(esa)], ['2'])).
% 0.50/0.71  thf('4', plain,
% 0.50/0.71      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.50/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.71  thf(t69_tops_1, axiom,
% 0.50/0.71    (![A:$i]:
% 0.50/0.71     ( ( l1_pre_topc @ A ) =>
% 0.50/0.71       ( ![B:$i]:
% 0.50/0.71         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.50/0.71           ( ( v4_pre_topc @ B @ A ) =>
% 0.50/0.71             ( r1_tarski @ ( k2_tops_1 @ A @ B ) @ B ) ) ) ) ))).
% 0.50/0.71  thf('5', plain,
% 0.50/0.71      (![X32 : $i, X33 : $i]:
% 0.50/0.71         (~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (u1_struct_0 @ X33)))
% 0.50/0.71          | (r1_tarski @ (k2_tops_1 @ X33 @ X32) @ X32)
% 0.50/0.71          | ~ (v4_pre_topc @ X32 @ X33)
% 0.50/0.71          | ~ (l1_pre_topc @ X33))),
% 0.50/0.71      inference('cnf', [status(esa)], [t69_tops_1])).
% 0.50/0.71  thf('6', plain,
% 0.50/0.71      ((~ (l1_pre_topc @ sk_A)
% 0.50/0.71        | ~ (v4_pre_topc @ sk_B @ sk_A)
% 0.50/0.71        | (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))),
% 0.50/0.71      inference('sup-', [status(thm)], ['4', '5'])).
% 0.50/0.71  thf('7', plain, ((l1_pre_topc @ sk_A)),
% 0.50/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.71  thf('8', plain,
% 0.50/0.71      ((~ (v4_pre_topc @ sk_B @ sk_A)
% 0.50/0.71        | (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))),
% 0.50/0.71      inference('demod', [status(thm)], ['6', '7'])).
% 0.50/0.71  thf('9', plain,
% 0.50/0.71      (((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))
% 0.50/0.71         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.50/0.71      inference('sup-', [status(thm)], ['3', '8'])).
% 0.50/0.71  thf(t3_subset, axiom,
% 0.50/0.71    (![A:$i,B:$i]:
% 0.50/0.71     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.50/0.71  thf('10', plain,
% 0.50/0.71      (![X23 : $i, X25 : $i]:
% 0.50/0.71         ((m1_subset_1 @ X23 @ (k1_zfmisc_1 @ X25)) | ~ (r1_tarski @ X23 @ X25))),
% 0.50/0.71      inference('cnf', [status(esa)], [t3_subset])).
% 0.50/0.71  thf('11', plain,
% 0.50/0.71      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_B)))
% 0.50/0.71         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.50/0.71      inference('sup-', [status(thm)], ['9', '10'])).
% 0.50/0.71  thf(involutiveness_k3_subset_1, axiom,
% 0.50/0.71    (![A:$i,B:$i]:
% 0.50/0.71     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.50/0.71       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 0.50/0.71  thf('12', plain,
% 0.50/0.71      (![X11 : $i, X12 : $i]:
% 0.50/0.71         (((k3_subset_1 @ X12 @ (k3_subset_1 @ X12 @ X11)) = (X11))
% 0.50/0.71          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12)))),
% 0.50/0.71      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.50/0.71  thf('13', plain,
% 0.50/0.71      ((((k3_subset_1 @ sk_B @ (k3_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))
% 0.50/0.71          = (k2_tops_1 @ sk_A @ sk_B)))
% 0.50/0.71         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.50/0.71      inference('sup-', [status(thm)], ['11', '12'])).
% 0.50/0.71  thf('14', plain,
% 0.50/0.71      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.50/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.71  thf(t74_tops_1, axiom,
% 0.50/0.71    (![A:$i]:
% 0.50/0.71     ( ( l1_pre_topc @ A ) =>
% 0.50/0.71       ( ![B:$i]:
% 0.50/0.71         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.50/0.71           ( ( k1_tops_1 @ A @ B ) =
% 0.50/0.71             ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.50/0.71  thf('15', plain,
% 0.50/0.71      (![X34 : $i, X35 : $i]:
% 0.50/0.71         (~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (u1_struct_0 @ X35)))
% 0.50/0.71          | ((k1_tops_1 @ X35 @ X34)
% 0.50/0.71              = (k7_subset_1 @ (u1_struct_0 @ X35) @ X34 @ 
% 0.50/0.71                 (k2_tops_1 @ X35 @ X34)))
% 0.50/0.71          | ~ (l1_pre_topc @ X35))),
% 0.50/0.71      inference('cnf', [status(esa)], [t74_tops_1])).
% 0.50/0.71  thf('16', plain,
% 0.50/0.71      ((~ (l1_pre_topc @ sk_A)
% 0.50/0.71        | ((k1_tops_1 @ sk_A @ sk_B)
% 0.50/0.71            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.50/0.71               (k2_tops_1 @ sk_A @ sk_B))))),
% 0.50/0.71      inference('sup-', [status(thm)], ['14', '15'])).
% 0.50/0.71  thf('17', plain, ((l1_pre_topc @ sk_A)),
% 0.50/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.71  thf('18', plain,
% 0.50/0.71      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.50/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.71  thf(redefinition_k7_subset_1, axiom,
% 0.50/0.71    (![A:$i,B:$i,C:$i]:
% 0.50/0.71     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.50/0.71       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 0.50/0.71  thf('19', plain,
% 0.50/0.71      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.50/0.71         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X17))
% 0.50/0.71          | ((k7_subset_1 @ X17 @ X16 @ X18) = (k4_xboole_0 @ X16 @ X18)))),
% 0.50/0.71      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 0.50/0.71  thf('20', plain,
% 0.50/0.71      (![X0 : $i]:
% 0.50/0.71         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.50/0.71           = (k4_xboole_0 @ sk_B @ X0))),
% 0.50/0.71      inference('sup-', [status(thm)], ['18', '19'])).
% 0.50/0.71  thf('21', plain,
% 0.50/0.71      (((k1_tops_1 @ sk_A @ sk_B)
% 0.50/0.71         = (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.50/0.71      inference('demod', [status(thm)], ['16', '17', '20'])).
% 0.50/0.71  thf('22', plain,
% 0.50/0.71      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_B)))
% 0.50/0.71         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.50/0.71      inference('sup-', [status(thm)], ['9', '10'])).
% 0.50/0.71  thf(d5_subset_1, axiom,
% 0.50/0.71    (![A:$i,B:$i]:
% 0.50/0.71     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.50/0.71       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.50/0.71  thf('23', plain,
% 0.50/0.71      (![X9 : $i, X10 : $i]:
% 0.50/0.71         (((k3_subset_1 @ X9 @ X10) = (k4_xboole_0 @ X9 @ X10))
% 0.50/0.71          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X9)))),
% 0.50/0.71      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.50/0.71  thf('24', plain,
% 0.50/0.71      ((((k3_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.50/0.71          = (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))
% 0.50/0.71         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.50/0.71      inference('sup-', [status(thm)], ['22', '23'])).
% 0.50/0.71  thf('25', plain,
% 0.50/0.71      ((((k3_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.50/0.71          = (k1_tops_1 @ sk_A @ sk_B)))
% 0.50/0.71         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.50/0.71      inference('sup+', [status(thm)], ['21', '24'])).
% 0.50/0.71  thf('26', plain,
% 0.50/0.71      ((((k3_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 0.50/0.71          = (k2_tops_1 @ sk_A @ sk_B)))
% 0.50/0.71         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.50/0.71      inference('demod', [status(thm)], ['13', '25'])).
% 0.50/0.71  thf('27', plain,
% 0.50/0.71      (((k1_tops_1 @ sk_A @ sk_B)
% 0.50/0.71         = (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.50/0.71      inference('demod', [status(thm)], ['16', '17', '20'])).
% 0.50/0.71  thf(t36_xboole_1, axiom,
% 0.50/0.71    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.50/0.71  thf('28', plain,
% 0.50/0.71      (![X4 : $i, X5 : $i]: (r1_tarski @ (k4_xboole_0 @ X4 @ X5) @ X4)),
% 0.50/0.71      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.50/0.71  thf('29', plain,
% 0.50/0.71      (![X23 : $i, X25 : $i]:
% 0.50/0.71         ((m1_subset_1 @ X23 @ (k1_zfmisc_1 @ X25)) | ~ (r1_tarski @ X23 @ X25))),
% 0.50/0.71      inference('cnf', [status(esa)], [t3_subset])).
% 0.50/0.71  thf('30', plain,
% 0.50/0.71      (![X0 : $i, X1 : $i]:
% 0.50/0.71         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 0.50/0.71      inference('sup-', [status(thm)], ['28', '29'])).
% 0.50/0.71  thf('31', plain,
% 0.50/0.71      (![X9 : $i, X10 : $i]:
% 0.50/0.71         (((k3_subset_1 @ X9 @ X10) = (k4_xboole_0 @ X9 @ X10))
% 0.50/0.71          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X9)))),
% 0.50/0.71      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.50/0.71  thf('32', plain,
% 0.50/0.71      (![X0 : $i, X1 : $i]:
% 0.50/0.71         ((k3_subset_1 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 0.50/0.71           = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))),
% 0.50/0.71      inference('sup-', [status(thm)], ['30', '31'])).
% 0.50/0.71  thf('33', plain,
% 0.50/0.71      (((k3_subset_1 @ sk_B @ (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))
% 0.50/0.71         = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))),
% 0.50/0.71      inference('sup+', [status(thm)], ['27', '32'])).
% 0.50/0.71  thf('34', plain,
% 0.50/0.71      (((k1_tops_1 @ sk_A @ sk_B)
% 0.50/0.71         = (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.50/0.71      inference('demod', [status(thm)], ['16', '17', '20'])).
% 0.50/0.71  thf('35', plain,
% 0.50/0.71      (((k3_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 0.50/0.71         = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))),
% 0.50/0.71      inference('demod', [status(thm)], ['33', '34'])).
% 0.50/0.71  thf('36', plain,
% 0.50/0.71      (![X0 : $i]:
% 0.50/0.71         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.50/0.71           = (k4_xboole_0 @ sk_B @ X0))),
% 0.50/0.71      inference('sup-', [status(thm)], ['18', '19'])).
% 0.50/0.71  thf('37', plain,
% 0.50/0.71      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.50/0.71          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.50/0.71              (k1_tops_1 @ sk_A @ sk_B))))
% 0.50/0.71         <= (~
% 0.50/0.71             (((k2_tops_1 @ sk_A @ sk_B)
% 0.50/0.71                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.50/0.71                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.50/0.71      inference('split', [status(esa)], ['0'])).
% 0.50/0.71  thf('38', plain,
% 0.50/0.71      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.50/0.71          != (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.50/0.71         <= (~
% 0.50/0.71             (((k2_tops_1 @ sk_A @ sk_B)
% 0.50/0.71                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.50/0.71                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.50/0.71      inference('sup-', [status(thm)], ['36', '37'])).
% 0.50/0.71  thf('39', plain,
% 0.50/0.71      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.50/0.71          != (k3_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.50/0.71         <= (~
% 0.50/0.71             (((k2_tops_1 @ sk_A @ sk_B)
% 0.50/0.71                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.50/0.71                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.50/0.71      inference('sup-', [status(thm)], ['35', '38'])).
% 0.50/0.71  thf('40', plain,
% 0.50/0.71      ((((k2_tops_1 @ sk_A @ sk_B) != (k2_tops_1 @ sk_A @ sk_B)))
% 0.50/0.71         <= (~
% 0.50/0.71             (((k2_tops_1 @ sk_A @ sk_B)
% 0.50/0.71                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.50/0.71                   (k1_tops_1 @ sk_A @ sk_B)))) & 
% 0.50/0.71             ((v4_pre_topc @ sk_B @ sk_A)))),
% 0.50/0.71      inference('sup-', [status(thm)], ['26', '39'])).
% 0.50/0.71  thf('41', plain,
% 0.50/0.71      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.50/0.71          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.50/0.71             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 0.50/0.71       ~ ((v4_pre_topc @ sk_B @ sk_A))),
% 0.50/0.71      inference('simplify', [status(thm)], ['40'])).
% 0.50/0.71  thf('42', plain,
% 0.50/0.71      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.50/0.71          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.50/0.71             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 0.50/0.71       ((v4_pre_topc @ sk_B @ sk_A))),
% 0.50/0.71      inference('split', [status(esa)], ['2'])).
% 0.50/0.71  thf('43', plain,
% 0.50/0.71      (((k1_tops_1 @ sk_A @ sk_B)
% 0.50/0.71         = (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.50/0.71      inference('demod', [status(thm)], ['16', '17', '20'])).
% 0.50/0.71  thf('44', plain,
% 0.50/0.71      (![X0 : $i, X1 : $i]:
% 0.50/0.71         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 0.50/0.71      inference('sup-', [status(thm)], ['28', '29'])).
% 0.50/0.71  thf('45', plain,
% 0.50/0.71      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_B))),
% 0.50/0.71      inference('sup+', [status(thm)], ['43', '44'])).
% 0.50/0.71  thf('46', plain,
% 0.50/0.71      (![X0 : $i]:
% 0.50/0.71         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.50/0.71           = (k4_xboole_0 @ sk_B @ X0))),
% 0.50/0.71      inference('sup-', [status(thm)], ['18', '19'])).
% 0.50/0.71  thf('47', plain,
% 0.50/0.71      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.50/0.71          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.50/0.71             (k1_tops_1 @ sk_A @ sk_B))))
% 0.50/0.71         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.50/0.71                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.50/0.71                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.50/0.71      inference('split', [status(esa)], ['2'])).
% 0.50/0.71  thf('48', plain,
% 0.50/0.71      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.50/0.71          = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.50/0.71         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.50/0.71                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.50/0.71                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.50/0.71      inference('sup+', [status(thm)], ['46', '47'])).
% 0.50/0.71  thf('49', plain,
% 0.50/0.71      (![X0 : $i, X1 : $i]:
% 0.50/0.71         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 0.50/0.71      inference('sup-', [status(thm)], ['28', '29'])).
% 0.50/0.71  thf('50', plain,
% 0.50/0.71      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_B)))
% 0.50/0.71         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.50/0.71                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.50/0.71                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.50/0.71      inference('sup+', [status(thm)], ['48', '49'])).
% 0.50/0.71  thf(redefinition_k4_subset_1, axiom,
% 0.50/0.71    (![A:$i,B:$i,C:$i]:
% 0.50/0.71     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 0.50/0.71         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.50/0.71       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 0.50/0.71  thf('51', plain,
% 0.50/0.71      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.50/0.71         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14))
% 0.50/0.71          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X14))
% 0.50/0.71          | ((k4_subset_1 @ X14 @ X13 @ X15) = (k2_xboole_0 @ X13 @ X15)))),
% 0.50/0.71      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 0.50/0.71  thf('52', plain,
% 0.50/0.71      ((![X0 : $i]:
% 0.50/0.71          (((k4_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B) @ X0)
% 0.50/0.71             = (k2_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ X0))
% 0.50/0.71           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_B))))
% 0.50/0.71         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.50/0.71                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.50/0.71                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.50/0.71      inference('sup-', [status(thm)], ['50', '51'])).
% 0.50/0.71  thf('53', plain,
% 0.50/0.71      ((((k4_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.50/0.71          (k1_tops_1 @ sk_A @ sk_B))
% 0.50/0.71          = (k2_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.50/0.71             (k1_tops_1 @ sk_A @ sk_B))))
% 0.50/0.71         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.50/0.71                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.50/0.71                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.50/0.71      inference('sup-', [status(thm)], ['45', '52'])).
% 0.50/0.71  thf(commutativity_k2_xboole_0, axiom,
% 0.50/0.71    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.50/0.71  thf('54', plain,
% 0.50/0.71      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.50/0.71      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.50/0.71  thf('55', plain,
% 0.50/0.71      (((k1_tops_1 @ sk_A @ sk_B)
% 0.50/0.71         = (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.50/0.71      inference('demod', [status(thm)], ['16', '17', '20'])).
% 0.50/0.71  thf(t39_xboole_1, axiom,
% 0.50/0.71    (![A:$i,B:$i]:
% 0.50/0.71     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.50/0.71  thf('56', plain,
% 0.50/0.71      (![X6 : $i, X7 : $i]:
% 0.50/0.71         ((k2_xboole_0 @ X6 @ (k4_xboole_0 @ X7 @ X6))
% 0.50/0.71           = (k2_xboole_0 @ X6 @ X7))),
% 0.50/0.71      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.50/0.71  thf('57', plain,
% 0.50/0.71      (((k2_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ sk_B))
% 0.50/0.71         = (k2_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))),
% 0.50/0.71      inference('sup+', [status(thm)], ['55', '56'])).
% 0.50/0.71  thf('58', plain,
% 0.50/0.71      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.50/0.71      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.50/0.71  thf('59', plain,
% 0.50/0.71      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.50/0.71      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.50/0.71  thf('60', plain,
% 0.50/0.71      (((k2_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ (k2_tops_1 @ sk_A @ sk_B))
% 0.50/0.71         = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.50/0.71      inference('demod', [status(thm)], ['57', '58', '59'])).
% 0.50/0.71  thf('61', plain,
% 0.50/0.71      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.50/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.71  thf(dt_k2_tops_1, axiom,
% 0.50/0.71    (![A:$i,B:$i]:
% 0.50/0.71     ( ( ( l1_pre_topc @ A ) & 
% 0.50/0.71         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.50/0.71       ( m1_subset_1 @
% 0.50/0.71         ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.50/0.71  thf('62', plain,
% 0.50/0.71      (![X28 : $i, X29 : $i]:
% 0.50/0.71         (~ (l1_pre_topc @ X28)
% 0.50/0.71          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 0.50/0.71          | (m1_subset_1 @ (k2_tops_1 @ X28 @ X29) @ 
% 0.50/0.71             (k1_zfmisc_1 @ (u1_struct_0 @ X28))))),
% 0.50/0.71      inference('cnf', [status(esa)], [dt_k2_tops_1])).
% 0.50/0.71  thf('63', plain,
% 0.50/0.71      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.50/0.71         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.50/0.71        | ~ (l1_pre_topc @ sk_A))),
% 0.50/0.71      inference('sup-', [status(thm)], ['61', '62'])).
% 0.50/0.71  thf('64', plain, ((l1_pre_topc @ sk_A)),
% 0.50/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.71  thf('65', plain,
% 0.50/0.71      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.50/0.71        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.50/0.71      inference('demod', [status(thm)], ['63', '64'])).
% 0.50/0.71  thf('66', plain,
% 0.50/0.71      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.50/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.71  thf('67', plain,
% 0.50/0.71      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.50/0.71         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14))
% 0.50/0.71          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X14))
% 0.50/0.71          | ((k4_subset_1 @ X14 @ X13 @ X15) = (k2_xboole_0 @ X13 @ X15)))),
% 0.50/0.71      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 0.50/0.71  thf('68', plain,
% 0.50/0.71      (![X0 : $i]:
% 0.50/0.71         (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.50/0.71            = (k2_xboole_0 @ sk_B @ X0))
% 0.50/0.71          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.50/0.71      inference('sup-', [status(thm)], ['66', '67'])).
% 0.50/0.71  thf('69', plain,
% 0.50/0.71      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.50/0.71         = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.50/0.71      inference('sup-', [status(thm)], ['65', '68'])).
% 0.50/0.71  thf('70', plain,
% 0.50/0.71      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.50/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.71  thf(t65_tops_1, axiom,
% 0.50/0.71    (![A:$i]:
% 0.50/0.71     ( ( l1_pre_topc @ A ) =>
% 0.50/0.71       ( ![B:$i]:
% 0.50/0.71         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.50/0.71           ( ( k2_pre_topc @ A @ B ) =
% 0.50/0.71             ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.50/0.71  thf('71', plain,
% 0.50/0.71      (![X30 : $i, X31 : $i]:
% 0.50/0.71         (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ X31)))
% 0.50/0.71          | ((k2_pre_topc @ X31 @ X30)
% 0.50/0.71              = (k4_subset_1 @ (u1_struct_0 @ X31) @ X30 @ 
% 0.50/0.71                 (k2_tops_1 @ X31 @ X30)))
% 0.50/0.71          | ~ (l1_pre_topc @ X31))),
% 0.50/0.71      inference('cnf', [status(esa)], [t65_tops_1])).
% 0.50/0.71  thf('72', plain,
% 0.50/0.71      ((~ (l1_pre_topc @ sk_A)
% 0.50/0.71        | ((k2_pre_topc @ sk_A @ sk_B)
% 0.50/0.71            = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.50/0.71               (k2_tops_1 @ sk_A @ sk_B))))),
% 0.50/0.71      inference('sup-', [status(thm)], ['70', '71'])).
% 0.50/0.71  thf('73', plain, ((l1_pre_topc @ sk_A)),
% 0.50/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.71  thf('74', plain,
% 0.50/0.71      (((k2_pre_topc @ sk_A @ sk_B)
% 0.50/0.71         = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.50/0.71            (k2_tops_1 @ sk_A @ sk_B)))),
% 0.50/0.71      inference('demod', [status(thm)], ['72', '73'])).
% 0.50/0.71  thf('75', plain,
% 0.50/0.71      (((k2_pre_topc @ sk_A @ sk_B)
% 0.50/0.71         = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.50/0.71      inference('sup+', [status(thm)], ['69', '74'])).
% 0.50/0.71  thf('76', plain,
% 0.50/0.71      (((k2_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ (k2_tops_1 @ sk_A @ sk_B))
% 0.50/0.71         = (k2_pre_topc @ sk_A @ sk_B))),
% 0.50/0.71      inference('demod', [status(thm)], ['60', '75'])).
% 0.50/0.71  thf('77', plain,
% 0.50/0.71      ((((k4_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.50/0.71          (k1_tops_1 @ sk_A @ sk_B)) = (k2_pre_topc @ sk_A @ sk_B)))
% 0.50/0.71         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.50/0.71                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.50/0.71                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.50/0.71      inference('demod', [status(thm)], ['53', '54', '76'])).
% 0.50/0.71  thf('78', plain,
% 0.50/0.71      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.50/0.71          = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.50/0.71         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.50/0.71                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.50/0.71                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.50/0.71      inference('sup+', [status(thm)], ['46', '47'])).
% 0.50/0.71  thf('79', plain,
% 0.50/0.71      (![X0 : $i, X1 : $i]:
% 0.50/0.71         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 0.50/0.71      inference('sup-', [status(thm)], ['28', '29'])).
% 0.50/0.71  thf(t25_subset_1, axiom,
% 0.50/0.71    (![A:$i,B:$i]:
% 0.50/0.71     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.50/0.71       ( ( k4_subset_1 @ A @ B @ ( k3_subset_1 @ A @ B ) ) =
% 0.50/0.71         ( k2_subset_1 @ A ) ) ))).
% 0.50/0.71  thf('80', plain,
% 0.50/0.71      (![X19 : $i, X20 : $i]:
% 0.50/0.71         (((k4_subset_1 @ X19 @ X20 @ (k3_subset_1 @ X19 @ X20))
% 0.50/0.71            = (k2_subset_1 @ X19))
% 0.50/0.71          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X19)))),
% 0.50/0.71      inference('cnf', [status(esa)], [t25_subset_1])).
% 0.50/0.71  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.50/0.71  thf('81', plain, (![X8 : $i]: ((k2_subset_1 @ X8) = (X8))),
% 0.50/0.71      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.50/0.71  thf('82', plain,
% 0.50/0.71      (![X19 : $i, X20 : $i]:
% 0.50/0.71         (((k4_subset_1 @ X19 @ X20 @ (k3_subset_1 @ X19 @ X20)) = (X19))
% 0.50/0.71          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X19)))),
% 0.50/0.71      inference('demod', [status(thm)], ['80', '81'])).
% 0.50/0.71  thf('83', plain,
% 0.50/0.71      (![X0 : $i, X1 : $i]:
% 0.50/0.71         ((k4_subset_1 @ X0 @ (k4_xboole_0 @ X0 @ X1) @ 
% 0.50/0.71           (k3_subset_1 @ X0 @ (k4_xboole_0 @ X0 @ X1))) = (X0))),
% 0.50/0.71      inference('sup-', [status(thm)], ['79', '82'])).
% 0.50/0.71  thf('84', plain,
% 0.50/0.71      ((((k4_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.50/0.71          (k3_subset_1 @ sk_B @ 
% 0.50/0.71           (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.50/0.71          = (sk_B)))
% 0.50/0.71         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.50/0.71                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.50/0.71                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.50/0.71      inference('sup+', [status(thm)], ['78', '83'])).
% 0.50/0.71  thf('85', plain,
% 0.50/0.71      (((k3_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 0.50/0.71         = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))),
% 0.50/0.71      inference('demod', [status(thm)], ['33', '34'])).
% 0.50/0.71  thf('86', plain,
% 0.50/0.71      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.50/0.71          = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.50/0.71         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.50/0.71                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.50/0.71                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.50/0.71      inference('sup+', [status(thm)], ['46', '47'])).
% 0.50/0.71  thf('87', plain,
% 0.50/0.71      (![X0 : $i, X1 : $i]:
% 0.50/0.71         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 0.50/0.71      inference('sup-', [status(thm)], ['28', '29'])).
% 0.50/0.71  thf('88', plain,
% 0.50/0.71      (![X11 : $i, X12 : $i]:
% 0.50/0.71         (((k3_subset_1 @ X12 @ (k3_subset_1 @ X12 @ X11)) = (X11))
% 0.50/0.71          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12)))),
% 0.50/0.71      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.50/0.71  thf('89', plain,
% 0.50/0.71      (![X0 : $i, X1 : $i]:
% 0.50/0.71         ((k3_subset_1 @ X0 @ (k3_subset_1 @ X0 @ (k4_xboole_0 @ X0 @ X1)))
% 0.50/0.71           = (k4_xboole_0 @ X0 @ X1))),
% 0.50/0.71      inference('sup-', [status(thm)], ['87', '88'])).
% 0.50/0.71  thf('90', plain,
% 0.50/0.71      ((((k3_subset_1 @ sk_B @ (k3_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))
% 0.50/0.71          = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.50/0.71         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.50/0.71                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.50/0.71                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.50/0.71      inference('sup+', [status(thm)], ['86', '89'])).
% 0.50/0.71  thf('91', plain,
% 0.50/0.71      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.50/0.71          = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.50/0.71         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.50/0.71                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.50/0.71                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.50/0.71      inference('sup+', [status(thm)], ['46', '47'])).
% 0.50/0.71  thf('92', plain,
% 0.50/0.71      ((((k3_subset_1 @ sk_B @ (k3_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))
% 0.50/0.71          = (k2_tops_1 @ sk_A @ sk_B)))
% 0.50/0.71         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.50/0.71                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.50/0.71                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.50/0.71      inference('demod', [status(thm)], ['90', '91'])).
% 0.50/0.71  thf('93', plain,
% 0.50/0.71      (((k1_tops_1 @ sk_A @ sk_B)
% 0.50/0.71         = (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.50/0.71      inference('demod', [status(thm)], ['16', '17', '20'])).
% 0.50/0.71  thf('94', plain,
% 0.50/0.71      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.50/0.71          = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.50/0.71         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.50/0.71                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.50/0.71                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.50/0.71      inference('sup+', [status(thm)], ['46', '47'])).
% 0.50/0.71  thf('95', plain,
% 0.50/0.71      (![X0 : $i, X1 : $i]:
% 0.50/0.71         ((k3_subset_1 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 0.50/0.71           = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))),
% 0.50/0.71      inference('sup-', [status(thm)], ['30', '31'])).
% 0.50/0.71  thf('96', plain,
% 0.50/0.71      ((((k3_subset_1 @ sk_B @ (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))
% 0.50/0.71          = (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))
% 0.50/0.71         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.50/0.71                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.50/0.71                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.50/0.71      inference('sup+', [status(thm)], ['94', '95'])).
% 0.50/0.71  thf('97', plain,
% 0.50/0.71      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.50/0.71          = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.50/0.71         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.50/0.71                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.50/0.71                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.50/0.71      inference('sup+', [status(thm)], ['46', '47'])).
% 0.50/0.71  thf('98', plain,
% 0.50/0.71      ((((k3_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.50/0.71          = (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))
% 0.50/0.71         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.50/0.71                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.50/0.71                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.50/0.71      inference('demod', [status(thm)], ['96', '97'])).
% 0.50/0.71  thf('99', plain,
% 0.50/0.71      ((((k3_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.50/0.71          = (k1_tops_1 @ sk_A @ sk_B)))
% 0.50/0.71         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.50/0.71                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.50/0.71                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.50/0.71      inference('sup+', [status(thm)], ['93', '98'])).
% 0.50/0.71  thf('100', plain,
% 0.50/0.71      ((((k3_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 0.50/0.71          = (k2_tops_1 @ sk_A @ sk_B)))
% 0.50/0.71         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.50/0.71                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.50/0.71                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.50/0.71      inference('demod', [status(thm)], ['92', '99'])).
% 0.50/0.71  thf('101', plain,
% 0.50/0.71      ((((k3_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.50/0.71          = (k1_tops_1 @ sk_A @ sk_B)))
% 0.50/0.71         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.50/0.71                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.50/0.71                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.50/0.71      inference('sup+', [status(thm)], ['93', '98'])).
% 0.50/0.71  thf('102', plain,
% 0.50/0.71      ((((k4_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.50/0.71          (k1_tops_1 @ sk_A @ sk_B)) = (sk_B)))
% 0.50/0.71         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.50/0.71                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.50/0.71                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.50/0.71      inference('demod', [status(thm)], ['84', '85', '100', '101'])).
% 0.50/0.71  thf('103', plain,
% 0.50/0.71      ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B)))
% 0.50/0.71         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.50/0.71                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.50/0.71                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.50/0.71      inference('sup+', [status(thm)], ['77', '102'])).
% 0.50/0.71  thf('104', plain,
% 0.50/0.71      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.50/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.71  thf(t52_pre_topc, axiom,
% 0.50/0.71    (![A:$i]:
% 0.50/0.71     ( ( l1_pre_topc @ A ) =>
% 0.50/0.71       ( ![B:$i]:
% 0.50/0.71         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.50/0.71           ( ( ( v4_pre_topc @ B @ A ) => ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) & 
% 0.50/0.71             ( ( ( v2_pre_topc @ A ) & ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) =>
% 0.50/0.71               ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 0.50/0.71  thf('105', plain,
% 0.50/0.71      (![X26 : $i, X27 : $i]:
% 0.50/0.71         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 0.50/0.71          | ~ (v2_pre_topc @ X27)
% 0.50/0.71          | ((k2_pre_topc @ X27 @ X26) != (X26))
% 0.50/0.71          | (v4_pre_topc @ X26 @ X27)
% 0.50/0.71          | ~ (l1_pre_topc @ X27))),
% 0.50/0.71      inference('cnf', [status(esa)], [t52_pre_topc])).
% 0.50/0.71  thf('106', plain,
% 0.50/0.71      ((~ (l1_pre_topc @ sk_A)
% 0.50/0.71        | (v4_pre_topc @ sk_B @ sk_A)
% 0.50/0.71        | ((k2_pre_topc @ sk_A @ sk_B) != (sk_B))
% 0.50/0.71        | ~ (v2_pre_topc @ sk_A))),
% 0.50/0.71      inference('sup-', [status(thm)], ['104', '105'])).
% 0.50/0.71  thf('107', plain, ((l1_pre_topc @ sk_A)),
% 0.50/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.71  thf('108', plain, ((v2_pre_topc @ sk_A)),
% 0.50/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.71  thf('109', plain,
% 0.50/0.71      (((v4_pre_topc @ sk_B @ sk_A) | ((k2_pre_topc @ sk_A @ sk_B) != (sk_B)))),
% 0.50/0.71      inference('demod', [status(thm)], ['106', '107', '108'])).
% 0.50/0.71  thf('110', plain,
% 0.50/0.71      (((((sk_B) != (sk_B)) | (v4_pre_topc @ sk_B @ sk_A)))
% 0.50/0.71         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.50/0.71                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.50/0.71                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.50/0.71      inference('sup-', [status(thm)], ['103', '109'])).
% 0.50/0.71  thf('111', plain,
% 0.50/0.71      (((v4_pre_topc @ sk_B @ sk_A))
% 0.50/0.71         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.50/0.71                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.50/0.71                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.50/0.71      inference('simplify', [status(thm)], ['110'])).
% 0.50/0.71  thf('112', plain,
% 0.50/0.71      ((~ (v4_pre_topc @ sk_B @ sk_A)) <= (~ ((v4_pre_topc @ sk_B @ sk_A)))),
% 0.50/0.71      inference('split', [status(esa)], ['0'])).
% 0.50/0.71  thf('113', plain,
% 0.50/0.71      (~
% 0.50/0.71       (((k2_tops_1 @ sk_A @ sk_B)
% 0.50/0.71          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.50/0.71             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 0.50/0.71       ((v4_pre_topc @ sk_B @ sk_A))),
% 0.50/0.71      inference('sup-', [status(thm)], ['111', '112'])).
% 0.50/0.71  thf('114', plain, ($false),
% 0.50/0.71      inference('sat_resolution*', [status(thm)], ['1', '41', '42', '113'])).
% 0.50/0.71  
% 0.50/0.71  % SZS output end Refutation
% 0.50/0.71  
% 0.50/0.72  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
