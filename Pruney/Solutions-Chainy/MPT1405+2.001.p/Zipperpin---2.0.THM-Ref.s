%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.8EPPB6IZfo

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:07:14 EST 2020

% Result     : Theorem 1.94s
% Output     : Refutation 1.94s
% Verified   : 
% Statistics : Number of formulae       :  155 ( 795 expanded)
%              Number of leaves         :   40 ( 280 expanded)
%              Depth                    :   16
%              Number of atoms          : 1095 (6099 expanded)
%              Number of equality atoms :   44 ( 216 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m2_connsp_2_type,type,(
    m2_connsp_2: $i > $i > $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('0',plain,(
    ! [X14: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X14 ) @ ( k1_zfmisc_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('1',plain,(
    ! [X13: $i] :
      ( ( k2_subset_1 @ X13 )
      = X13 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('2',plain,(
    ! [X14: $i] :
      ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X14 ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('3',plain,(
    ! [X31: $i] :
      ( ( ( k2_struct_0 @ X31 )
        = ( u1_struct_0 @ X31 ) )
      | ~ ( l1_struct_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(t35_connsp_2,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( m2_connsp_2 @ ( k2_struct_0 @ A ) @ A @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( m2_connsp_2 @ ( k2_struct_0 @ A ) @ A @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t35_connsp_2])).

thf('4',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_connsp_2,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( m2_connsp_2 @ C @ A @ B )
              <=> ( r1_tarski @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) )).

thf('5',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X38 ) ) )
      | ~ ( r1_tarski @ X37 @ ( k1_tops_1 @ X38 @ X39 ) )
      | ( m2_connsp_2 @ X39 @ X38 @ X37 )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X38 ) ) )
      | ~ ( l1_pre_topc @ X38 )
      | ~ ( v2_pre_topc @ X38 ) ) ),
    inference(cnf,[status(esa)],[d2_connsp_2])).

thf('6',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( m2_connsp_2 @ X0 @ sk_A @ sk_B_1 )
      | ~ ( r1_tarski @ sk_B_1 @ ( k1_tops_1 @ sk_A @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( m2_connsp_2 @ X0 @ sk_A @ sk_B_1 )
      | ~ ( r1_tarski @ sk_B_1 @ ( k1_tops_1 @ sk_A @ X0 ) ) ) ),
    inference(demod,[status(thm)],['6','7','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) )
      | ~ ( l1_struct_0 @ sk_A )
      | ~ ( r1_tarski @ sk_B_1 @ ( k1_tops_1 @ sk_A @ X0 ) )
      | ( m2_connsp_2 @ X0 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['3','9'])).

thf('11',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('12',plain,(
    ! [X32: $i] :
      ( ( l1_struct_0 @ X32 )
      | ~ ( l1_pre_topc @ X32 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('13',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) )
      | ~ ( r1_tarski @ sk_B_1 @ ( k1_tops_1 @ sk_A @ X0 ) )
      | ( m2_connsp_2 @ X0 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['10','13'])).

thf('15',plain,
    ( ( m2_connsp_2 @ ( k2_struct_0 @ sk_A ) @ sk_A @ sk_B_1 )
    | ~ ( r1_tarski @ sk_B_1 @ ( k1_tops_1 @ sk_A @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['2','14'])).

thf('16',plain,(
    ~ ( m2_connsp_2 @ ( k2_struct_0 @ sk_A ) @ sk_A @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    ~ ( r1_tarski @ sk_B_1 @ ( k1_tops_1 @ sk_A @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X31: $i] :
      ( ( ( k2_struct_0 @ X31 )
        = ( u1_struct_0 @ X31 ) )
      | ~ ( l1_struct_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('19',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('20',plain,(
    ! [X23: $i,X24: $i] :
      ( ( r1_tarski @ X23 @ X24 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('21',plain,(
    r1_tarski @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X14: $i] :
      ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X14 ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(dt_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('23',plain,(
    ! [X15: $i,X16: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X15 @ X16 ) @ ( k1_zfmisc_1 @ X15 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k3_subset_1 @ X0 @ X0 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X23: $i,X24: $i] :
      ( ( r1_tarski @ X23 @ X24 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('26',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k3_subset_1 @ X0 @ X0 ) @ X0 ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('27',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( r1_tarski @ X10 @ X11 )
      | ~ ( r1_tarski @ X11 @ X12 )
      | ( r1_tarski @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k3_subset_1 @ X0 @ X0 ) @ X1 )
      | ~ ( r1_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    r1_tarski @ ( k3_subset_1 @ sk_B_1 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['21','28'])).

thf('30',plain,(
    ! [X23: $i,X25: $i] :
      ( ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ X25 ) )
      | ~ ( r1_tarski @ X23 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('31',plain,(
    m1_subset_1 @ ( k3_subset_1 @ sk_B_1 @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X15: $i,X16: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X15 @ X16 ) @ ( k1_zfmisc_1 @ X15 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('33',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ sk_B_1 @ sk_B_1 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,
    ( ( m1_subset_1 @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k3_subset_1 @ sk_B_1 @ sk_B_1 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['18','33'])).

thf('35',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['11','12'])).

thf('36',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k3_subset_1 @ sk_B_1 @ sk_B_1 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('37',plain,(
    ! [X17: $i,X18: $i] :
      ( ( ( k3_subset_1 @ X18 @ ( k3_subset_1 @ X18 @ X17 ) )
        = X17 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('38',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k3_subset_1 @ sk_B_1 @ sk_B_1 ) ) ) )
    = ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k3_subset_1 @ sk_B_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X31: $i] :
      ( ( ( k2_struct_0 @ X31 )
        = ( u1_struct_0 @ X31 ) )
      | ~ ( l1_struct_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('40',plain,(
    m1_subset_1 @ ( k3_subset_1 @ sk_B_1 @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('41',plain,(
    ! [X17: $i,X18: $i] :
      ( ( ( k3_subset_1 @ X18 @ ( k3_subset_1 @ X18 @ X17 ) )
        = X17 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('42',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ sk_B_1 @ sk_B_1 ) ) )
    = ( k3_subset_1 @ sk_B_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,
    ( ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k3_subset_1 @ sk_B_1 @ sk_B_1 ) ) )
      = ( k3_subset_1 @ sk_B_1 @ sk_B_1 ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['39','42'])).

thf('44',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['11','12'])).

thf('45',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k3_subset_1 @ sk_B_1 @ sk_B_1 ) ) )
    = ( k3_subset_1 @ sk_B_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ sk_B_1 @ sk_B_1 ) )
    = ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k3_subset_1 @ sk_B_1 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['38','45'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('47',plain,(
    ! [X22: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('48',plain,(
    ! [X17: $i,X18: $i] :
      ( ( ( k3_subset_1 @ X18 @ ( k3_subset_1 @ X18 @ X17 ) )
        = X17 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ ( k3_subset_1 @ X0 @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X22: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('51',plain,(
    ! [X15: $i,X16: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X15 @ X16 ) @ ( k1_zfmisc_1 @ X15 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('52',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k3_subset_1 @ X0 @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X23: $i,X24: $i] :
      ( ( r1_tarski @ X23 @ X24 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('54',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k3_subset_1 @ X0 @ k1_xboole_0 ) @ X0 ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('55',plain,(
    ! [X7: $i,X9: $i] :
      ( ( X7 = X9 )
      | ~ ( r1_tarski @ X9 @ X7 )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('56',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k3_subset_1 @ X0 @ k1_xboole_0 ) )
      | ( X0
        = ( k3_subset_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ ( k3_subset_1 @ X0 @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('58',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k3_subset_1 @ X0 @ X0 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf(t36_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ( r1_tarski @ ( k3_subset_1 @ A @ B ) @ C )
           => ( r1_tarski @ ( k3_subset_1 @ A @ C ) @ B ) ) ) ) )).

thf('59',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X20 ) )
      | ( r1_tarski @ ( k3_subset_1 @ X20 @ X19 ) @ X21 )
      | ~ ( r1_tarski @ ( k3_subset_1 @ X20 @ X21 ) @ X19 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t36_subset_1])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) )
      | ~ ( r1_tarski @ ( k3_subset_1 @ X0 @ X1 ) @ ( k3_subset_1 @ X0 @ X0 ) )
      | ( r1_tarski @ ( k3_subset_1 @ X0 @ ( k3_subset_1 @ X0 @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X14: $i] :
      ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X14 ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('62',plain,(
    ! [X17: $i,X18: $i] :
      ( ( ( k3_subset_1 @ X18 @ ( k3_subset_1 @ X18 @ X17 ) )
        = X17 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ ( k3_subset_1 @ X0 @ X0 ) )
      = X0 ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) )
      | ~ ( r1_tarski @ ( k3_subset_1 @ X0 @ X1 ) @ ( k3_subset_1 @ X0 @ X0 ) )
      | ( r1_tarski @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['60','63'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ k1_xboole_0 @ ( k3_subset_1 @ X0 @ X0 ) )
      | ( r1_tarski @ X0 @ ( k3_subset_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( m1_subset_1 @ ( k3_subset_1 @ X0 @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['57','64'])).

thf('66',plain,(
    ! [X22: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('67',plain,(
    ! [X23: $i,X24: $i] :
      ( ( r1_tarski @ X23 @ X24 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('68',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k3_subset_1 @ X0 @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('70',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ ( k3_subset_1 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['65','68','69'])).

thf('71',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_subset_1 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['56','70'])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['49','71'])).

thf('73',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_subset_1 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['56','70'])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['49','71'])).

thf('75',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_subset_1 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['56','70'])).

thf('76',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['46','72','73','74','75'])).

thf('77',plain,(
    ! [X14: $i] :
      ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X14 ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(d1_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k1_tops_1 @ A @ B )
            = ( k3_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) )).

thf('78',plain,(
    ! [X35: $i,X36: $i] :
      ( ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X36 ) ) )
      | ( ( k1_tops_1 @ X36 @ X35 )
        = ( k3_subset_1 @ ( u1_struct_0 @ X36 ) @ ( k2_pre_topc @ X36 @ ( k3_subset_1 @ ( u1_struct_0 @ X36 ) @ X35 ) ) ) )
      | ~ ( l1_pre_topc @ X36 ) ) ),
    inference(cnf,[status(esa)],[d1_tops_1])).

thf('79',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( k1_tops_1 @ X0 @ ( u1_struct_0 @ X0 ) )
        = ( k3_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k2_pre_topc @ X0 @ ( k3_subset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['49','71'])).

thf('81',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( k1_tops_1 @ X0 @ ( u1_struct_0 @ X0 ) )
        = ( k3_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k2_pre_topc @ X0 @ k1_xboole_0 ) ) ) ) ),
    inference(demod,[status(thm)],['79','80'])).

thf('82',plain,
    ( ( ( k1_tops_1 @ sk_A @ ( u1_struct_0 @ sk_A ) )
      = ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ k1_xboole_0 ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup+',[status(thm)],['76','81'])).

thf('83',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['46','72','73','74','75'])).

thf('84',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('85',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('86',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('87',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X23: $i,X25: $i] :
      ( ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ X25 ) )
      | ~ ( r1_tarski @ X23 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('89',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf(cc2_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v1_xboole_0 @ B )
           => ( v4_pre_topc @ B @ A ) ) ) ) )).

thf('90',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X30 ) ) )
      | ( v4_pre_topc @ X29 @ X30 )
      | ~ ( v1_xboole_0 @ X29 )
      | ~ ( l1_pre_topc @ X30 )
      | ~ ( v2_pre_topc @ X30 ) ) ),
    inference(cnf,[status(esa)],[cc2_pre_topc])).

thf('91',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_xboole_0 @ X1 )
      | ( v4_pre_topc @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v4_pre_topc @ X1 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['91'])).

thf('93',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v4_pre_topc @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['84','92'])).

thf('94',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v4_pre_topc @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['93','94'])).

thf('96',plain,(
    ! [X22: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X22 ) ) ),
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

thf('97',plain,(
    ! [X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X34 ) ) )
      | ~ ( v4_pre_topc @ X33 @ X34 )
      | ( ( k2_pre_topc @ X34 @ X33 )
        = X33 )
      | ~ ( l1_pre_topc @ X34 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('98',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( k2_pre_topc @ X0 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( v4_pre_topc @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( ( k2_pre_topc @ sk_A @ k1_xboole_0 )
      = k1_xboole_0 )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['95','98'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('100',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('101',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,
    ( ( k2_pre_topc @ sk_A @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['99','100','101'])).

thf('103',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_subset_1 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['56','70'])).

thf('104',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,
    ( ( k1_tops_1 @ sk_A @ ( k2_struct_0 @ sk_A ) )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['82','83','102','103','104'])).

thf('106',plain,(
    ! [X31: $i] :
      ( ( ( k2_struct_0 @ X31 )
        = ( u1_struct_0 @ X31 ) )
      | ~ ( l1_struct_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('107',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,
    ( ( m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['106','107'])).

thf('109',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['11','12'])).

thf('110',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['108','109'])).

thf('111',plain,(
    ! [X23: $i,X24: $i] :
      ( ( r1_tarski @ X23 @ X24 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('112',plain,(
    r1_tarski @ sk_B_1 @ ( k2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['110','111'])).

thf('113',plain,(
    $false ),
    inference(demod,[status(thm)],['17','105','112'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.09/0.16  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.09/0.17  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.8EPPB6IZfo
% 0.17/0.37  % Computer   : n008.cluster.edu
% 0.17/0.37  % Model      : x86_64 x86_64
% 0.17/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.17/0.37  % Memory     : 8042.1875MB
% 0.17/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.17/0.37  % CPULimit   : 60
% 0.17/0.37  % DateTime   : Tue Dec  1 11:35:45 EST 2020
% 0.17/0.38  % CPUTime    : 
% 0.17/0.38  % Running portfolio for 600 s
% 0.17/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.17/0.38  % Number of cores: 8
% 0.17/0.38  % Python version: Python 3.6.8
% 0.17/0.38  % Running in FO mode
% 1.94/2.15  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.94/2.15  % Solved by: fo/fo7.sh
% 1.94/2.15  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.94/2.15  % done 4116 iterations in 1.660s
% 1.94/2.15  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.94/2.15  % SZS output start Refutation
% 1.94/2.15  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 1.94/2.15  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.94/2.15  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 1.94/2.15  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.94/2.15  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.94/2.15  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 1.94/2.15  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 1.94/2.15  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 1.94/2.15  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.94/2.15  thf(sk_B_1_type, type, sk_B_1: $i).
% 1.94/2.15  thf(sk_A_type, type, sk_A: $i).
% 1.94/2.15  thf(m2_connsp_2_type, type, m2_connsp_2: $i > $i > $i > $o).
% 1.94/2.15  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 1.94/2.15  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 1.94/2.15  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 1.94/2.15  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 1.94/2.15  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.94/2.15  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.94/2.15  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 1.94/2.15  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 1.94/2.15  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 1.94/2.15  thf(dt_k2_subset_1, axiom,
% 1.94/2.15    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 1.94/2.15  thf('0', plain,
% 1.94/2.15      (![X14 : $i]: (m1_subset_1 @ (k2_subset_1 @ X14) @ (k1_zfmisc_1 @ X14))),
% 1.94/2.15      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 1.94/2.15  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 1.94/2.15  thf('1', plain, (![X13 : $i]: ((k2_subset_1 @ X13) = (X13))),
% 1.94/2.15      inference('cnf', [status(esa)], [d4_subset_1])).
% 1.94/2.15  thf('2', plain, (![X14 : $i]: (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X14))),
% 1.94/2.15      inference('demod', [status(thm)], ['0', '1'])).
% 1.94/2.15  thf(d3_struct_0, axiom,
% 1.94/2.15    (![A:$i]:
% 1.94/2.15     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 1.94/2.15  thf('3', plain,
% 1.94/2.15      (![X31 : $i]:
% 1.94/2.15         (((k2_struct_0 @ X31) = (u1_struct_0 @ X31)) | ~ (l1_struct_0 @ X31))),
% 1.94/2.15      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.94/2.15  thf(t35_connsp_2, conjecture,
% 1.94/2.15    (![A:$i]:
% 1.94/2.15     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.94/2.15       ( ![B:$i]:
% 1.94/2.15         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.94/2.15           ( m2_connsp_2 @ ( k2_struct_0 @ A ) @ A @ B ) ) ) ))).
% 1.94/2.15  thf(zf_stmt_0, negated_conjecture,
% 1.94/2.15    (~( ![A:$i]:
% 1.94/2.15        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 1.94/2.15            ( l1_pre_topc @ A ) ) =>
% 1.94/2.15          ( ![B:$i]:
% 1.94/2.15            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.94/2.15              ( m2_connsp_2 @ ( k2_struct_0 @ A ) @ A @ B ) ) ) ) )),
% 1.94/2.15    inference('cnf.neg', [status(esa)], [t35_connsp_2])).
% 1.94/2.15  thf('4', plain,
% 1.94/2.15      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.94/2.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.94/2.15  thf(d2_connsp_2, axiom,
% 1.94/2.15    (![A:$i]:
% 1.94/2.15     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.94/2.15       ( ![B:$i]:
% 1.94/2.15         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.94/2.15           ( ![C:$i]:
% 1.94/2.15             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.94/2.15               ( ( m2_connsp_2 @ C @ A @ B ) <=>
% 1.94/2.15                 ( r1_tarski @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 1.94/2.15  thf('5', plain,
% 1.94/2.15      (![X37 : $i, X38 : $i, X39 : $i]:
% 1.94/2.15         (~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (u1_struct_0 @ X38)))
% 1.94/2.15          | ~ (r1_tarski @ X37 @ (k1_tops_1 @ X38 @ X39))
% 1.94/2.15          | (m2_connsp_2 @ X39 @ X38 @ X37)
% 1.94/2.15          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (u1_struct_0 @ X38)))
% 1.94/2.15          | ~ (l1_pre_topc @ X38)
% 1.94/2.15          | ~ (v2_pre_topc @ X38))),
% 1.94/2.15      inference('cnf', [status(esa)], [d2_connsp_2])).
% 1.94/2.15  thf('6', plain,
% 1.94/2.15      (![X0 : $i]:
% 1.94/2.15         (~ (v2_pre_topc @ sk_A)
% 1.94/2.15          | ~ (l1_pre_topc @ sk_A)
% 1.94/2.15          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.94/2.15          | (m2_connsp_2 @ X0 @ sk_A @ sk_B_1)
% 1.94/2.15          | ~ (r1_tarski @ sk_B_1 @ (k1_tops_1 @ sk_A @ X0)))),
% 1.94/2.15      inference('sup-', [status(thm)], ['4', '5'])).
% 1.94/2.15  thf('7', plain, ((v2_pre_topc @ sk_A)),
% 1.94/2.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.94/2.15  thf('8', plain, ((l1_pre_topc @ sk_A)),
% 1.94/2.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.94/2.15  thf('9', plain,
% 1.94/2.15      (![X0 : $i]:
% 1.94/2.15         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.94/2.15          | (m2_connsp_2 @ X0 @ sk_A @ sk_B_1)
% 1.94/2.15          | ~ (r1_tarski @ sk_B_1 @ (k1_tops_1 @ sk_A @ X0)))),
% 1.94/2.15      inference('demod', [status(thm)], ['6', '7', '8'])).
% 1.94/2.15  thf('10', plain,
% 1.94/2.15      (![X0 : $i]:
% 1.94/2.15         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))
% 1.94/2.15          | ~ (l1_struct_0 @ sk_A)
% 1.94/2.15          | ~ (r1_tarski @ sk_B_1 @ (k1_tops_1 @ sk_A @ X0))
% 1.94/2.15          | (m2_connsp_2 @ X0 @ sk_A @ sk_B_1))),
% 1.94/2.15      inference('sup-', [status(thm)], ['3', '9'])).
% 1.94/2.15  thf('11', plain, ((l1_pre_topc @ sk_A)),
% 1.94/2.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.94/2.15  thf(dt_l1_pre_topc, axiom,
% 1.94/2.15    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 1.94/2.15  thf('12', plain,
% 1.94/2.15      (![X32 : $i]: ((l1_struct_0 @ X32) | ~ (l1_pre_topc @ X32))),
% 1.94/2.15      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 1.94/2.15  thf('13', plain, ((l1_struct_0 @ sk_A)),
% 1.94/2.15      inference('sup-', [status(thm)], ['11', '12'])).
% 1.94/2.15  thf('14', plain,
% 1.94/2.15      (![X0 : $i]:
% 1.94/2.15         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))
% 1.94/2.15          | ~ (r1_tarski @ sk_B_1 @ (k1_tops_1 @ sk_A @ X0))
% 1.94/2.15          | (m2_connsp_2 @ X0 @ sk_A @ sk_B_1))),
% 1.94/2.15      inference('demod', [status(thm)], ['10', '13'])).
% 1.94/2.15  thf('15', plain,
% 1.94/2.15      (((m2_connsp_2 @ (k2_struct_0 @ sk_A) @ sk_A @ sk_B_1)
% 1.94/2.15        | ~ (r1_tarski @ sk_B_1 @ (k1_tops_1 @ sk_A @ (k2_struct_0 @ sk_A))))),
% 1.94/2.15      inference('sup-', [status(thm)], ['2', '14'])).
% 1.94/2.15  thf('16', plain, (~ (m2_connsp_2 @ (k2_struct_0 @ sk_A) @ sk_A @ sk_B_1)),
% 1.94/2.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.94/2.15  thf('17', plain,
% 1.94/2.15      (~ (r1_tarski @ sk_B_1 @ (k1_tops_1 @ sk_A @ (k2_struct_0 @ sk_A)))),
% 1.94/2.15      inference('clc', [status(thm)], ['15', '16'])).
% 1.94/2.15  thf('18', plain,
% 1.94/2.15      (![X31 : $i]:
% 1.94/2.15         (((k2_struct_0 @ X31) = (u1_struct_0 @ X31)) | ~ (l1_struct_0 @ X31))),
% 1.94/2.15      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.94/2.15  thf('19', plain,
% 1.94/2.15      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.94/2.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.94/2.15  thf(t3_subset, axiom,
% 1.94/2.15    (![A:$i,B:$i]:
% 1.94/2.15     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 1.94/2.15  thf('20', plain,
% 1.94/2.15      (![X23 : $i, X24 : $i]:
% 1.94/2.15         ((r1_tarski @ X23 @ X24) | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ X24)))),
% 1.94/2.15      inference('cnf', [status(esa)], [t3_subset])).
% 1.94/2.15  thf('21', plain, ((r1_tarski @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 1.94/2.15      inference('sup-', [status(thm)], ['19', '20'])).
% 1.94/2.15  thf('22', plain, (![X14 : $i]: (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X14))),
% 1.94/2.15      inference('demod', [status(thm)], ['0', '1'])).
% 1.94/2.15  thf(dt_k3_subset_1, axiom,
% 1.94/2.15    (![A:$i,B:$i]:
% 1.94/2.15     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.94/2.15       ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 1.94/2.15  thf('23', plain,
% 1.94/2.15      (![X15 : $i, X16 : $i]:
% 1.94/2.15         ((m1_subset_1 @ (k3_subset_1 @ X15 @ X16) @ (k1_zfmisc_1 @ X15))
% 1.94/2.15          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X15)))),
% 1.94/2.15      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 1.94/2.15  thf('24', plain,
% 1.94/2.15      (![X0 : $i]: (m1_subset_1 @ (k3_subset_1 @ X0 @ X0) @ (k1_zfmisc_1 @ X0))),
% 1.94/2.15      inference('sup-', [status(thm)], ['22', '23'])).
% 1.94/2.15  thf('25', plain,
% 1.94/2.15      (![X23 : $i, X24 : $i]:
% 1.94/2.15         ((r1_tarski @ X23 @ X24) | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ X24)))),
% 1.94/2.15      inference('cnf', [status(esa)], [t3_subset])).
% 1.94/2.15  thf('26', plain, (![X0 : $i]: (r1_tarski @ (k3_subset_1 @ X0 @ X0) @ X0)),
% 1.94/2.15      inference('sup-', [status(thm)], ['24', '25'])).
% 1.94/2.15  thf(t1_xboole_1, axiom,
% 1.94/2.15    (![A:$i,B:$i,C:$i]:
% 1.94/2.15     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 1.94/2.15       ( r1_tarski @ A @ C ) ))).
% 1.94/2.15  thf('27', plain,
% 1.94/2.15      (![X10 : $i, X11 : $i, X12 : $i]:
% 1.94/2.15         (~ (r1_tarski @ X10 @ X11)
% 1.94/2.15          | ~ (r1_tarski @ X11 @ X12)
% 1.94/2.15          | (r1_tarski @ X10 @ X12))),
% 1.94/2.15      inference('cnf', [status(esa)], [t1_xboole_1])).
% 1.94/2.15  thf('28', plain,
% 1.94/2.15      (![X0 : $i, X1 : $i]:
% 1.94/2.15         ((r1_tarski @ (k3_subset_1 @ X0 @ X0) @ X1) | ~ (r1_tarski @ X0 @ X1))),
% 1.94/2.15      inference('sup-', [status(thm)], ['26', '27'])).
% 1.94/2.15  thf('29', plain,
% 1.94/2.15      ((r1_tarski @ (k3_subset_1 @ sk_B_1 @ sk_B_1) @ (u1_struct_0 @ sk_A))),
% 1.94/2.15      inference('sup-', [status(thm)], ['21', '28'])).
% 1.94/2.15  thf('30', plain,
% 1.94/2.15      (![X23 : $i, X25 : $i]:
% 1.94/2.15         ((m1_subset_1 @ X23 @ (k1_zfmisc_1 @ X25)) | ~ (r1_tarski @ X23 @ X25))),
% 1.94/2.15      inference('cnf', [status(esa)], [t3_subset])).
% 1.94/2.15  thf('31', plain,
% 1.94/2.15      ((m1_subset_1 @ (k3_subset_1 @ sk_B_1 @ sk_B_1) @ 
% 1.94/2.15        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.94/2.15      inference('sup-', [status(thm)], ['29', '30'])).
% 1.94/2.15  thf('32', plain,
% 1.94/2.15      (![X15 : $i, X16 : $i]:
% 1.94/2.15         ((m1_subset_1 @ (k3_subset_1 @ X15 @ X16) @ (k1_zfmisc_1 @ X15))
% 1.94/2.15          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X15)))),
% 1.94/2.15      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 1.94/2.15  thf('33', plain,
% 1.94/2.15      ((m1_subset_1 @ 
% 1.94/2.15        (k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k3_subset_1 @ sk_B_1 @ sk_B_1)) @ 
% 1.94/2.15        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.94/2.15      inference('sup-', [status(thm)], ['31', '32'])).
% 1.94/2.15  thf('34', plain,
% 1.94/2.15      (((m1_subset_1 @ 
% 1.94/2.15         (k3_subset_1 @ (k2_struct_0 @ sk_A) @ (k3_subset_1 @ sk_B_1 @ sk_B_1)) @ 
% 1.94/2.15         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.94/2.15        | ~ (l1_struct_0 @ sk_A))),
% 1.94/2.15      inference('sup+', [status(thm)], ['18', '33'])).
% 1.94/2.15  thf('35', plain, ((l1_struct_0 @ sk_A)),
% 1.94/2.15      inference('sup-', [status(thm)], ['11', '12'])).
% 1.94/2.15  thf('36', plain,
% 1.94/2.15      ((m1_subset_1 @ 
% 1.94/2.15        (k3_subset_1 @ (k2_struct_0 @ sk_A) @ (k3_subset_1 @ sk_B_1 @ sk_B_1)) @ 
% 1.94/2.15        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.94/2.15      inference('demod', [status(thm)], ['34', '35'])).
% 1.94/2.15  thf(involutiveness_k3_subset_1, axiom,
% 1.94/2.15    (![A:$i,B:$i]:
% 1.94/2.15     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.94/2.15       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 1.94/2.15  thf('37', plain,
% 1.94/2.15      (![X17 : $i, X18 : $i]:
% 1.94/2.15         (((k3_subset_1 @ X18 @ (k3_subset_1 @ X18 @ X17)) = (X17))
% 1.94/2.15          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X18)))),
% 1.94/2.15      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 1.94/2.15  thf('38', plain,
% 1.94/2.15      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.94/2.15         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.94/2.15          (k3_subset_1 @ (k2_struct_0 @ sk_A) @ (k3_subset_1 @ sk_B_1 @ sk_B_1))))
% 1.94/2.15         = (k3_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 1.94/2.15            (k3_subset_1 @ sk_B_1 @ sk_B_1)))),
% 1.94/2.15      inference('sup-', [status(thm)], ['36', '37'])).
% 1.94/2.15  thf('39', plain,
% 1.94/2.15      (![X31 : $i]:
% 1.94/2.15         (((k2_struct_0 @ X31) = (u1_struct_0 @ X31)) | ~ (l1_struct_0 @ X31))),
% 1.94/2.15      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.94/2.15  thf('40', plain,
% 1.94/2.15      ((m1_subset_1 @ (k3_subset_1 @ sk_B_1 @ sk_B_1) @ 
% 1.94/2.15        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.94/2.15      inference('sup-', [status(thm)], ['29', '30'])).
% 1.94/2.15  thf('41', plain,
% 1.94/2.15      (![X17 : $i, X18 : $i]:
% 1.94/2.15         (((k3_subset_1 @ X18 @ (k3_subset_1 @ X18 @ X17)) = (X17))
% 1.94/2.15          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X18)))),
% 1.94/2.15      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 1.94/2.15  thf('42', plain,
% 1.94/2.15      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.94/2.15         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k3_subset_1 @ sk_B_1 @ sk_B_1)))
% 1.94/2.15         = (k3_subset_1 @ sk_B_1 @ sk_B_1))),
% 1.94/2.15      inference('sup-', [status(thm)], ['40', '41'])).
% 1.94/2.15  thf('43', plain,
% 1.94/2.15      ((((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.94/2.15          (k3_subset_1 @ (k2_struct_0 @ sk_A) @ (k3_subset_1 @ sk_B_1 @ sk_B_1)))
% 1.94/2.15          = (k3_subset_1 @ sk_B_1 @ sk_B_1))
% 1.94/2.15        | ~ (l1_struct_0 @ sk_A))),
% 1.94/2.15      inference('sup+', [status(thm)], ['39', '42'])).
% 1.94/2.15  thf('44', plain, ((l1_struct_0 @ sk_A)),
% 1.94/2.15      inference('sup-', [status(thm)], ['11', '12'])).
% 1.94/2.15  thf('45', plain,
% 1.94/2.15      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.94/2.15         (k3_subset_1 @ (k2_struct_0 @ sk_A) @ (k3_subset_1 @ sk_B_1 @ sk_B_1)))
% 1.94/2.15         = (k3_subset_1 @ sk_B_1 @ sk_B_1))),
% 1.94/2.15      inference('demod', [status(thm)], ['43', '44'])).
% 1.94/2.15  thf('46', plain,
% 1.94/2.15      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k3_subset_1 @ sk_B_1 @ sk_B_1))
% 1.94/2.15         = (k3_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 1.94/2.15            (k3_subset_1 @ sk_B_1 @ sk_B_1)))),
% 1.94/2.15      inference('demod', [status(thm)], ['38', '45'])).
% 1.94/2.15  thf(t4_subset_1, axiom,
% 1.94/2.15    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 1.94/2.15  thf('47', plain,
% 1.94/2.15      (![X22 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X22))),
% 1.94/2.15      inference('cnf', [status(esa)], [t4_subset_1])).
% 1.94/2.15  thf('48', plain,
% 1.94/2.15      (![X17 : $i, X18 : $i]:
% 1.94/2.15         (((k3_subset_1 @ X18 @ (k3_subset_1 @ X18 @ X17)) = (X17))
% 1.94/2.15          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X18)))),
% 1.94/2.15      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 1.94/2.15  thf('49', plain,
% 1.94/2.15      (![X0 : $i]:
% 1.94/2.15         ((k3_subset_1 @ X0 @ (k3_subset_1 @ X0 @ k1_xboole_0)) = (k1_xboole_0))),
% 1.94/2.15      inference('sup-', [status(thm)], ['47', '48'])).
% 1.94/2.15  thf('50', plain,
% 1.94/2.15      (![X22 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X22))),
% 1.94/2.15      inference('cnf', [status(esa)], [t4_subset_1])).
% 1.94/2.15  thf('51', plain,
% 1.94/2.15      (![X15 : $i, X16 : $i]:
% 1.94/2.15         ((m1_subset_1 @ (k3_subset_1 @ X15 @ X16) @ (k1_zfmisc_1 @ X15))
% 1.94/2.15          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X15)))),
% 1.94/2.15      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 1.94/2.15  thf('52', plain,
% 1.94/2.15      (![X0 : $i]:
% 1.94/2.15         (m1_subset_1 @ (k3_subset_1 @ X0 @ k1_xboole_0) @ (k1_zfmisc_1 @ X0))),
% 1.94/2.15      inference('sup-', [status(thm)], ['50', '51'])).
% 1.94/2.15  thf('53', plain,
% 1.94/2.15      (![X23 : $i, X24 : $i]:
% 1.94/2.15         ((r1_tarski @ X23 @ X24) | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ X24)))),
% 1.94/2.15      inference('cnf', [status(esa)], [t3_subset])).
% 1.94/2.15  thf('54', plain,
% 1.94/2.15      (![X0 : $i]: (r1_tarski @ (k3_subset_1 @ X0 @ k1_xboole_0) @ X0)),
% 1.94/2.15      inference('sup-', [status(thm)], ['52', '53'])).
% 1.94/2.15  thf(d10_xboole_0, axiom,
% 1.94/2.15    (![A:$i,B:$i]:
% 1.94/2.15     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.94/2.15  thf('55', plain,
% 1.94/2.15      (![X7 : $i, X9 : $i]:
% 1.94/2.15         (((X7) = (X9)) | ~ (r1_tarski @ X9 @ X7) | ~ (r1_tarski @ X7 @ X9))),
% 1.94/2.15      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.94/2.15  thf('56', plain,
% 1.94/2.15      (![X0 : $i]:
% 1.94/2.15         (~ (r1_tarski @ X0 @ (k3_subset_1 @ X0 @ k1_xboole_0))
% 1.94/2.15          | ((X0) = (k3_subset_1 @ X0 @ k1_xboole_0)))),
% 1.94/2.15      inference('sup-', [status(thm)], ['54', '55'])).
% 1.94/2.15  thf('57', plain,
% 1.94/2.15      (![X0 : $i]:
% 1.94/2.15         ((k3_subset_1 @ X0 @ (k3_subset_1 @ X0 @ k1_xboole_0)) = (k1_xboole_0))),
% 1.94/2.15      inference('sup-', [status(thm)], ['47', '48'])).
% 1.94/2.15  thf('58', plain,
% 1.94/2.15      (![X0 : $i]: (m1_subset_1 @ (k3_subset_1 @ X0 @ X0) @ (k1_zfmisc_1 @ X0))),
% 1.94/2.15      inference('sup-', [status(thm)], ['22', '23'])).
% 1.94/2.15  thf(t36_subset_1, axiom,
% 1.94/2.15    (![A:$i,B:$i]:
% 1.94/2.15     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.94/2.15       ( ![C:$i]:
% 1.94/2.15         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 1.94/2.15           ( ( r1_tarski @ ( k3_subset_1 @ A @ B ) @ C ) =>
% 1.94/2.15             ( r1_tarski @ ( k3_subset_1 @ A @ C ) @ B ) ) ) ) ))).
% 1.94/2.15  thf('59', plain,
% 1.94/2.15      (![X19 : $i, X20 : $i, X21 : $i]:
% 1.94/2.15         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ X20))
% 1.94/2.15          | (r1_tarski @ (k3_subset_1 @ X20 @ X19) @ X21)
% 1.94/2.15          | ~ (r1_tarski @ (k3_subset_1 @ X20 @ X21) @ X19)
% 1.94/2.15          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ X20)))),
% 1.94/2.15      inference('cnf', [status(esa)], [t36_subset_1])).
% 1.94/2.15  thf('60', plain,
% 1.94/2.15      (![X0 : $i, X1 : $i]:
% 1.94/2.15         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0))
% 1.94/2.15          | ~ (r1_tarski @ (k3_subset_1 @ X0 @ X1) @ (k3_subset_1 @ X0 @ X0))
% 1.94/2.15          | (r1_tarski @ (k3_subset_1 @ X0 @ (k3_subset_1 @ X0 @ X0)) @ X1))),
% 1.94/2.15      inference('sup-', [status(thm)], ['58', '59'])).
% 1.94/2.15  thf('61', plain, (![X14 : $i]: (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X14))),
% 1.94/2.15      inference('demod', [status(thm)], ['0', '1'])).
% 1.94/2.15  thf('62', plain,
% 1.94/2.15      (![X17 : $i, X18 : $i]:
% 1.94/2.15         (((k3_subset_1 @ X18 @ (k3_subset_1 @ X18 @ X17)) = (X17))
% 1.94/2.15          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X18)))),
% 1.94/2.15      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 1.94/2.15  thf('63', plain,
% 1.94/2.15      (![X0 : $i]: ((k3_subset_1 @ X0 @ (k3_subset_1 @ X0 @ X0)) = (X0))),
% 1.94/2.15      inference('sup-', [status(thm)], ['61', '62'])).
% 1.94/2.15  thf('64', plain,
% 1.94/2.15      (![X0 : $i, X1 : $i]:
% 1.94/2.15         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0))
% 1.94/2.15          | ~ (r1_tarski @ (k3_subset_1 @ X0 @ X1) @ (k3_subset_1 @ X0 @ X0))
% 1.94/2.15          | (r1_tarski @ X0 @ X1))),
% 1.94/2.15      inference('demod', [status(thm)], ['60', '63'])).
% 1.94/2.15  thf('65', plain,
% 1.94/2.15      (![X0 : $i]:
% 1.94/2.15         (~ (r1_tarski @ k1_xboole_0 @ (k3_subset_1 @ X0 @ X0))
% 1.94/2.15          | (r1_tarski @ X0 @ (k3_subset_1 @ X0 @ k1_xboole_0))
% 1.94/2.15          | ~ (m1_subset_1 @ (k3_subset_1 @ X0 @ k1_xboole_0) @ 
% 1.94/2.15               (k1_zfmisc_1 @ X0)))),
% 1.94/2.15      inference('sup-', [status(thm)], ['57', '64'])).
% 1.94/2.15  thf('66', plain,
% 1.94/2.15      (![X22 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X22))),
% 1.94/2.15      inference('cnf', [status(esa)], [t4_subset_1])).
% 1.94/2.15  thf('67', plain,
% 1.94/2.15      (![X23 : $i, X24 : $i]:
% 1.94/2.15         ((r1_tarski @ X23 @ X24) | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ X24)))),
% 1.94/2.15      inference('cnf', [status(esa)], [t3_subset])).
% 1.94/2.15  thf('68', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 1.94/2.15      inference('sup-', [status(thm)], ['66', '67'])).
% 1.94/2.15  thf('69', plain,
% 1.94/2.15      (![X0 : $i]:
% 1.94/2.15         (m1_subset_1 @ (k3_subset_1 @ X0 @ k1_xboole_0) @ (k1_zfmisc_1 @ X0))),
% 1.94/2.15      inference('sup-', [status(thm)], ['50', '51'])).
% 1.94/2.15  thf('70', plain,
% 1.94/2.15      (![X0 : $i]: (r1_tarski @ X0 @ (k3_subset_1 @ X0 @ k1_xboole_0))),
% 1.94/2.15      inference('demod', [status(thm)], ['65', '68', '69'])).
% 1.94/2.15  thf('71', plain, (![X0 : $i]: ((X0) = (k3_subset_1 @ X0 @ k1_xboole_0))),
% 1.94/2.15      inference('demod', [status(thm)], ['56', '70'])).
% 1.94/2.15  thf('72', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k1_xboole_0))),
% 1.94/2.15      inference('demod', [status(thm)], ['49', '71'])).
% 1.94/2.15  thf('73', plain, (![X0 : $i]: ((X0) = (k3_subset_1 @ X0 @ k1_xboole_0))),
% 1.94/2.15      inference('demod', [status(thm)], ['56', '70'])).
% 1.94/2.15  thf('74', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k1_xboole_0))),
% 1.94/2.15      inference('demod', [status(thm)], ['49', '71'])).
% 1.94/2.15  thf('75', plain, (![X0 : $i]: ((X0) = (k3_subset_1 @ X0 @ k1_xboole_0))),
% 1.94/2.15      inference('demod', [status(thm)], ['56', '70'])).
% 1.94/2.15  thf('76', plain, (((u1_struct_0 @ sk_A) = (k2_struct_0 @ sk_A))),
% 1.94/2.15      inference('demod', [status(thm)], ['46', '72', '73', '74', '75'])).
% 1.94/2.15  thf('77', plain, (![X14 : $i]: (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X14))),
% 1.94/2.15      inference('demod', [status(thm)], ['0', '1'])).
% 1.94/2.15  thf(d1_tops_1, axiom,
% 1.94/2.15    (![A:$i]:
% 1.94/2.15     ( ( l1_pre_topc @ A ) =>
% 1.94/2.15       ( ![B:$i]:
% 1.94/2.15         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.94/2.15           ( ( k1_tops_1 @ A @ B ) =
% 1.94/2.15             ( k3_subset_1 @
% 1.94/2.15               ( u1_struct_0 @ A ) @ 
% 1.94/2.15               ( k2_pre_topc @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) ))).
% 1.94/2.15  thf('78', plain,
% 1.94/2.15      (![X35 : $i, X36 : $i]:
% 1.94/2.15         (~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (u1_struct_0 @ X36)))
% 1.94/2.15          | ((k1_tops_1 @ X36 @ X35)
% 1.94/2.15              = (k3_subset_1 @ (u1_struct_0 @ X36) @ 
% 1.94/2.15                 (k2_pre_topc @ X36 @ (k3_subset_1 @ (u1_struct_0 @ X36) @ X35))))
% 1.94/2.15          | ~ (l1_pre_topc @ X36))),
% 1.94/2.15      inference('cnf', [status(esa)], [d1_tops_1])).
% 1.94/2.15  thf('79', plain,
% 1.94/2.15      (![X0 : $i]:
% 1.94/2.15         (~ (l1_pre_topc @ X0)
% 1.94/2.15          | ((k1_tops_1 @ X0 @ (u1_struct_0 @ X0))
% 1.94/2.15              = (k3_subset_1 @ (u1_struct_0 @ X0) @ 
% 1.94/2.15                 (k2_pre_topc @ X0 @ 
% 1.94/2.15                  (k3_subset_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0))))))),
% 1.94/2.15      inference('sup-', [status(thm)], ['77', '78'])).
% 1.94/2.15  thf('80', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k1_xboole_0))),
% 1.94/2.15      inference('demod', [status(thm)], ['49', '71'])).
% 1.94/2.15  thf('81', plain,
% 1.94/2.15      (![X0 : $i]:
% 1.94/2.15         (~ (l1_pre_topc @ X0)
% 1.94/2.15          | ((k1_tops_1 @ X0 @ (u1_struct_0 @ X0))
% 1.94/2.15              = (k3_subset_1 @ (u1_struct_0 @ X0) @ 
% 1.94/2.15                 (k2_pre_topc @ X0 @ k1_xboole_0))))),
% 1.94/2.15      inference('demod', [status(thm)], ['79', '80'])).
% 1.94/2.15  thf('82', plain,
% 1.94/2.15      ((((k1_tops_1 @ sk_A @ (u1_struct_0 @ sk_A))
% 1.94/2.15          = (k3_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 1.94/2.15             (k2_pre_topc @ sk_A @ k1_xboole_0)))
% 1.94/2.15        | ~ (l1_pre_topc @ sk_A))),
% 1.94/2.15      inference('sup+', [status(thm)], ['76', '81'])).
% 1.94/2.15  thf('83', plain, (((u1_struct_0 @ sk_A) = (k2_struct_0 @ sk_A))),
% 1.94/2.15      inference('demod', [status(thm)], ['46', '72', '73', '74', '75'])).
% 1.94/2.15  thf('84', plain, ((l1_pre_topc @ sk_A)),
% 1.94/2.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.94/2.15  thf(d3_tarski, axiom,
% 1.94/2.15    (![A:$i,B:$i]:
% 1.94/2.15     ( ( r1_tarski @ A @ B ) <=>
% 1.94/2.15       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 1.94/2.15  thf('85', plain,
% 1.94/2.15      (![X4 : $i, X6 : $i]:
% 1.94/2.15         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 1.94/2.15      inference('cnf', [status(esa)], [d3_tarski])).
% 1.94/2.15  thf(d1_xboole_0, axiom,
% 1.94/2.15    (![A:$i]:
% 1.94/2.15     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 1.94/2.15  thf('86', plain,
% 1.94/2.15      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 1.94/2.15      inference('cnf', [status(esa)], [d1_xboole_0])).
% 1.94/2.15  thf('87', plain,
% 1.94/2.15      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 1.94/2.15      inference('sup-', [status(thm)], ['85', '86'])).
% 1.94/2.15  thf('88', plain,
% 1.94/2.15      (![X23 : $i, X25 : $i]:
% 1.94/2.15         ((m1_subset_1 @ X23 @ (k1_zfmisc_1 @ X25)) | ~ (r1_tarski @ X23 @ X25))),
% 1.94/2.15      inference('cnf', [status(esa)], [t3_subset])).
% 1.94/2.15  thf('89', plain,
% 1.94/2.15      (![X0 : $i, X1 : $i]:
% 1.94/2.15         (~ (v1_xboole_0 @ X1) | (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0)))),
% 1.94/2.15      inference('sup-', [status(thm)], ['87', '88'])).
% 1.94/2.15  thf(cc2_pre_topc, axiom,
% 1.94/2.15    (![A:$i]:
% 1.94/2.15     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.94/2.15       ( ![B:$i]:
% 1.94/2.15         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.94/2.15           ( ( v1_xboole_0 @ B ) => ( v4_pre_topc @ B @ A ) ) ) ) ))).
% 1.94/2.15  thf('90', plain,
% 1.94/2.15      (![X29 : $i, X30 : $i]:
% 1.94/2.15         (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X30)))
% 1.94/2.15          | (v4_pre_topc @ X29 @ X30)
% 1.94/2.15          | ~ (v1_xboole_0 @ X29)
% 1.94/2.15          | ~ (l1_pre_topc @ X30)
% 1.94/2.15          | ~ (v2_pre_topc @ X30))),
% 1.94/2.15      inference('cnf', [status(esa)], [cc2_pre_topc])).
% 1.94/2.15  thf('91', plain,
% 1.94/2.15      (![X0 : $i, X1 : $i]:
% 1.94/2.15         (~ (v1_xboole_0 @ X1)
% 1.94/2.15          | ~ (v2_pre_topc @ X0)
% 1.94/2.15          | ~ (l1_pre_topc @ X0)
% 1.94/2.15          | ~ (v1_xboole_0 @ X1)
% 1.94/2.15          | (v4_pre_topc @ X1 @ X0))),
% 1.94/2.15      inference('sup-', [status(thm)], ['89', '90'])).
% 1.94/2.15  thf('92', plain,
% 1.94/2.15      (![X0 : $i, X1 : $i]:
% 1.94/2.15         ((v4_pre_topc @ X1 @ X0)
% 1.94/2.15          | ~ (l1_pre_topc @ X0)
% 1.94/2.15          | ~ (v2_pre_topc @ X0)
% 1.94/2.15          | ~ (v1_xboole_0 @ X1))),
% 1.94/2.15      inference('simplify', [status(thm)], ['91'])).
% 1.94/2.15  thf('93', plain,
% 1.94/2.15      (![X0 : $i]:
% 1.94/2.15         (~ (v1_xboole_0 @ X0)
% 1.94/2.15          | ~ (v2_pre_topc @ sk_A)
% 1.94/2.15          | (v4_pre_topc @ X0 @ sk_A))),
% 1.94/2.15      inference('sup-', [status(thm)], ['84', '92'])).
% 1.94/2.15  thf('94', plain, ((v2_pre_topc @ sk_A)),
% 1.94/2.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.94/2.15  thf('95', plain,
% 1.94/2.15      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | (v4_pre_topc @ X0 @ sk_A))),
% 1.94/2.15      inference('demod', [status(thm)], ['93', '94'])).
% 1.94/2.15  thf('96', plain,
% 1.94/2.15      (![X22 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X22))),
% 1.94/2.15      inference('cnf', [status(esa)], [t4_subset_1])).
% 1.94/2.15  thf(t52_pre_topc, axiom,
% 1.94/2.15    (![A:$i]:
% 1.94/2.15     ( ( l1_pre_topc @ A ) =>
% 1.94/2.15       ( ![B:$i]:
% 1.94/2.15         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.94/2.15           ( ( ( v4_pre_topc @ B @ A ) => ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) & 
% 1.94/2.15             ( ( ( v2_pre_topc @ A ) & ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) =>
% 1.94/2.15               ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 1.94/2.15  thf('97', plain,
% 1.94/2.15      (![X33 : $i, X34 : $i]:
% 1.94/2.15         (~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (u1_struct_0 @ X34)))
% 1.94/2.15          | ~ (v4_pre_topc @ X33 @ X34)
% 1.94/2.15          | ((k2_pre_topc @ X34 @ X33) = (X33))
% 1.94/2.15          | ~ (l1_pre_topc @ X34))),
% 1.94/2.15      inference('cnf', [status(esa)], [t52_pre_topc])).
% 1.94/2.15  thf('98', plain,
% 1.94/2.15      (![X0 : $i]:
% 1.94/2.15         (~ (l1_pre_topc @ X0)
% 1.94/2.15          | ((k2_pre_topc @ X0 @ k1_xboole_0) = (k1_xboole_0))
% 1.94/2.15          | ~ (v4_pre_topc @ k1_xboole_0 @ X0))),
% 1.94/2.15      inference('sup-', [status(thm)], ['96', '97'])).
% 1.94/2.15  thf('99', plain,
% 1.94/2.15      ((~ (v1_xboole_0 @ k1_xboole_0)
% 1.94/2.15        | ((k2_pre_topc @ sk_A @ k1_xboole_0) = (k1_xboole_0))
% 1.94/2.15        | ~ (l1_pre_topc @ sk_A))),
% 1.94/2.15      inference('sup-', [status(thm)], ['95', '98'])).
% 1.94/2.15  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 1.94/2.15  thf('100', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.94/2.15      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.94/2.15  thf('101', plain, ((l1_pre_topc @ sk_A)),
% 1.94/2.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.94/2.15  thf('102', plain, (((k2_pre_topc @ sk_A @ k1_xboole_0) = (k1_xboole_0))),
% 1.94/2.15      inference('demod', [status(thm)], ['99', '100', '101'])).
% 1.94/2.15  thf('103', plain, (![X0 : $i]: ((X0) = (k3_subset_1 @ X0 @ k1_xboole_0))),
% 1.94/2.15      inference('demod', [status(thm)], ['56', '70'])).
% 1.94/2.15  thf('104', plain, ((l1_pre_topc @ sk_A)),
% 1.94/2.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.94/2.15  thf('105', plain,
% 1.94/2.15      (((k1_tops_1 @ sk_A @ (k2_struct_0 @ sk_A)) = (k2_struct_0 @ sk_A))),
% 1.94/2.15      inference('demod', [status(thm)], ['82', '83', '102', '103', '104'])).
% 1.94/2.15  thf('106', plain,
% 1.94/2.15      (![X31 : $i]:
% 1.94/2.15         (((k2_struct_0 @ X31) = (u1_struct_0 @ X31)) | ~ (l1_struct_0 @ X31))),
% 1.94/2.15      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.94/2.15  thf('107', plain,
% 1.94/2.15      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.94/2.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.94/2.15  thf('108', plain,
% 1.94/2.15      (((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))
% 1.94/2.15        | ~ (l1_struct_0 @ sk_A))),
% 1.94/2.15      inference('sup+', [status(thm)], ['106', '107'])).
% 1.94/2.15  thf('109', plain, ((l1_struct_0 @ sk_A)),
% 1.94/2.15      inference('sup-', [status(thm)], ['11', '12'])).
% 1.94/2.15  thf('110', plain,
% 1.94/2.15      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))),
% 1.94/2.15      inference('demod', [status(thm)], ['108', '109'])).
% 1.94/2.15  thf('111', plain,
% 1.94/2.15      (![X23 : $i, X24 : $i]:
% 1.94/2.15         ((r1_tarski @ X23 @ X24) | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ X24)))),
% 1.94/2.15      inference('cnf', [status(esa)], [t3_subset])).
% 1.94/2.15  thf('112', plain, ((r1_tarski @ sk_B_1 @ (k2_struct_0 @ sk_A))),
% 1.94/2.15      inference('sup-', [status(thm)], ['110', '111'])).
% 1.94/2.15  thf('113', plain, ($false),
% 1.94/2.15      inference('demod', [status(thm)], ['17', '105', '112'])).
% 1.94/2.15  
% 1.94/2.15  % SZS output end Refutation
% 1.94/2.15  
% 1.94/2.16  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
