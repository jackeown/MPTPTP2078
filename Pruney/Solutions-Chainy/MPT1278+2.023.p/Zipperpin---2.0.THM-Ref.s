%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.VuBC98lNIP

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:04:42 EST 2020

% Result     : Theorem 0.54s
% Output     : Refutation 0.54s
% Verified   : 
% Statistics : Number of formulae       :  165 ( 435 expanded)
%              Number of leaves         :   40 ( 154 expanded)
%              Depth                    :   17
%              Number of atoms          : 1152 (4003 expanded)
%              Number of equality atoms :   63 ( 218 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(v2_tops_1_type,type,(
    v2_tops_1: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(v1_tops_1_type,type,(
    v1_tops_1: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v3_tops_1_type,type,(
    v3_tops_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

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

thf('0',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('1',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k3_subset_1 @ X12 @ ( k3_subset_1 @ X12 @ X11 ) )
        = X11 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('2',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) )
    = sk_B_1 ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('4',plain,(
    ! [X9: $i,X10: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X9 @ X10 ) @ ( k1_zfmisc_1 @ X9 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('5',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

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

thf('6',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ~ ( v4_pre_topc @ X19 @ X20 )
      | ( ( k2_pre_topc @ X20 @ X19 )
        = X19 )
      | ~ ( l1_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('7',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) )
      = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) )
    | ~ ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) )
      = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) )
    | ~ ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_A ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(d3_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v1_tops_1 @ B @ A )
          <=> ( ( k2_pre_topc @ A @ B )
              = ( k2_struct_0 @ A ) ) ) ) ) )).

thf('11',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ~ ( v1_tops_1 @ X21 @ X22 )
      | ( ( k2_pre_topc @ X22 @ X21 )
        = ( k2_struct_0 @ X22 ) )
      | ~ ( l1_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[d3_tops_1])).

thf('12',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) )
      = ( k2_struct_0 @ sk_A ) )
    | ~ ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) )
      = ( k2_struct_0 @ sk_A ) )
    | ~ ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_A ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d4_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v2_tops_1 @ B @ A )
          <=> ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) )).

thf('16',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ~ ( v2_tops_1 @ X23 @ X24 )
      | ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ X24 ) @ X23 ) @ X24 )
      | ~ ( l1_pre_topc @ X24 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_1])).

thf('17',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_A )
    | ~ ( v2_tops_1 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t92_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v3_tops_1 @ B @ A )
           => ( v2_tops_1 @ B @ A ) ) ) ) )).

thf('20',plain,(
    ! [X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X34 ) ) )
      | ( v2_tops_1 @ X33 @ X34 )
      | ~ ( v3_tops_1 @ X33 @ X34 )
      | ~ ( l1_pre_topc @ X34 ) ) ),
    inference(cnf,[status(esa)],[t92_tops_1])).

thf('21',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v3_tops_1 @ sk_B_1 @ sk_A )
    | ( v2_tops_1 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    v3_tops_1 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    v2_tops_1 @ sk_B_1 @ sk_A ),
    inference(demod,[status(thm)],['21','22','23'])).

thf('25',plain,(
    v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_A ),
    inference(demod,[status(thm)],['17','18','24'])).

thf('26',plain,
    ( ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['14','25'])).

thf('27',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) )
    | ~ ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_A ) ),
    inference(demod,[status(thm)],['9','26'])).

thf('28',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(t29_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v4_pre_topc @ B @ A )
          <=> ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) )).

thf('29',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X30 ) ) )
      | ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ X30 ) @ X29 ) @ X30 )
      | ( v4_pre_topc @ X29 @ X30 )
      | ~ ( l1_pre_topc @ X30 ) ) ),
    inference(cnf,[status(esa)],[t29_tops_1])).

thf('30',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_A )
    | ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) )
    = sk_B_1 ),
    inference('sup-',[status(thm)],['0','1'])).

thf('33',plain,(
    v3_pre_topc @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_A ),
    inference(demod,[status(thm)],['30','31','32','33'])).

thf('35',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) ),
    inference(demod,[status(thm)],['27','34'])).

thf('36',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) )
    = sk_B_1 ),
    inference(demod,[status(thm)],['2','35'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('37',plain,(
    ! [X15: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('38',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k3_subset_1 @ X12 @ ( k3_subset_1 @ X12 @ X11 ) )
        = X11 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ ( k3_subset_1 @ X0 @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('40',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf(t39_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( r1_tarski @ ( k3_subset_1 @ A @ B ) @ B )
      <=> ( B
          = ( k2_subset_1 @ A ) ) ) ) )).

thf('43',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( r1_tarski @ ( k3_subset_1 @ X13 @ X14 ) @ X14 )
      | ( X14
        = ( k2_subset_1 @ X13 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t39_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('44',plain,(
    ! [X7: $i] :
      ( ( k2_subset_1 @ X7 )
      = X7 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('45',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( r1_tarski @ ( k3_subset_1 @ X13 @ X14 ) @ X14 )
      | ( X14 = X13 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X13 ) ) ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ ( k3_subset_1 @ X1 @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( X0 = X1 ) ) ),
    inference('sup-',[status(thm)],['42','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
        = X0 )
      | ~ ( m1_subset_1 @ ( k3_subset_1 @ X0 @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['39','46'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('48',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('49',plain,(
    ! [X15: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('50',plain,(
    ! [X9: $i,X10: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X9 @ X10 ) @ ( k1_zfmisc_1 @ X9 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('51',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k3_subset_1 @ X0 @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['47','48','51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ ( k3_subset_1 @ X1 @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( X0 = X1 ) ) ),
    inference('sup-',[status(thm)],['42','45'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( k1_xboole_0 = X0 )
      | ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X15: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('56',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( k1_xboole_0 = X0 ) ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc9_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ) )).

thf('58',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( l1_pre_topc @ X25 )
      | ~ ( v2_pre_topc @ X25 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) )
      | ( v3_pre_topc @ ( k1_tops_1 @ X25 @ X26 ) @ X25 ) ) ),
    inference(cnf,[status(esa)],[fc9_tops_1])).

thf('59',plain,
    ( ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_B_1 ) @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
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
    ! [X31: $i,X32: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X32 ) ) )
      | ~ ( v2_tops_1 @ X31 @ X32 )
      | ( ( k1_tops_1 @ X32 @ X31 )
        = k1_xboole_0 )
      | ~ ( l1_pre_topc @ X32 ) ) ),
    inference(cnf,[status(esa)],[t84_tops_1])).

thf('62',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 )
    | ~ ( v2_tops_1 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    v2_tops_1 @ sk_B_1 @ sk_A ),
    inference(demod,[status(thm)],['21','22','23'])).

thf('65',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B_1 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['62','63','64'])).

thf('66',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    v3_pre_topc @ k1_xboole_0 @ sk_A ),
    inference(demod,[status(thm)],['59','65','66','67'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( v3_pre_topc @ X0 @ sk_A )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['56','68'])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('70',plain,(
    ! [X8: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X8 ) @ ( k1_zfmisc_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf('71',plain,(
    ! [X7: $i] :
      ( ( k2_subset_1 @ X7 )
      = X7 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('72',plain,(
    ! [X8: $i] :
      ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X8 ) ) ),
    inference(demod,[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X30 ) ) )
      | ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ X30 ) @ X29 ) @ X30 )
      | ( v4_pre_topc @ X29 @ X30 )
      | ~ ( l1_pre_topc @ X30 ) ) ),
    inference(cnf,[status(esa)],[t29_tops_1])).

thf('74',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v4_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ ( k3_subset_1 @ X0 @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['47','48','51'])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v4_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( v3_pre_topc @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['74','77'])).

thf('79',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( v4_pre_topc @ ( u1_struct_0 @ sk_A ) @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['69','78'])).

thf('80',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('81',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    v4_pre_topc @ ( u1_struct_0 @ sk_A ) @ sk_A ),
    inference(demod,[status(thm)],['79','80','81'])).

thf('83',plain,(
    ! [X8: $i] :
      ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X8 ) ) ),
    inference(demod,[status(thm)],['70','71'])).

thf('84',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ~ ( v4_pre_topc @ X19 @ X20 )
      | ( ( k2_pre_topc @ X20 @ X19 )
        = X19 )
      | ~ ( l1_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('85',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( k2_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( v4_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( u1_struct_0 @ sk_A ) )
      = ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['82','85'])).

thf('87',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( k1_xboole_0 = X0 ) ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('88',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(projectivity_k1_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( ( k1_tops_1 @ A @ ( k1_tops_1 @ A @ B ) )
        = ( k1_tops_1 @ A @ B ) ) ) )).

thf('89',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( l1_pre_topc @ X27 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
      | ( ( k1_tops_1 @ X27 @ ( k1_tops_1 @ X27 @ X28 ) )
        = ( k1_tops_1 @ X27 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[projectivity_k1_tops_1])).

thf('90',plain,
    ( ( ( k1_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B_1 ) )
      = ( k1_tops_1 @ sk_A @ sk_B_1 ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B_1 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['62','63','64'])).

thf('92',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B_1 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['62','63','64'])).

thf('93',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,
    ( ( k1_tops_1 @ sk_A @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['90','91','92','93'])).

thf('95',plain,(
    ! [X15: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('96',plain,(
    ! [X31: $i,X32: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X32 ) ) )
      | ( ( k1_tops_1 @ X32 @ X31 )
       != k1_xboole_0 )
      | ( v2_tops_1 @ X31 @ X32 )
      | ~ ( l1_pre_topc @ X32 ) ) ),
    inference(cnf,[status(esa)],[t84_tops_1])).

thf('97',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v2_tops_1 @ k1_xboole_0 @ X0 )
      | ( ( k1_tops_1 @ X0 @ k1_xboole_0 )
       != k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( v2_tops_1 @ k1_xboole_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['94','97'])).

thf('99',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( v2_tops_1 @ k1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['98','99'])).

thf('101',plain,(
    v2_tops_1 @ k1_xboole_0 @ sk_A ),
    inference(simplify,[status(thm)],['100'])).

thf('102',plain,(
    ! [X0: $i] :
      ( ( v2_tops_1 @ X0 @ sk_A )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['87','101'])).

thf('103',plain,(
    ! [X15: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('104',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ~ ( v2_tops_1 @ X23 @ X24 )
      | ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ X24 ) @ X23 ) @ X24 )
      | ~ ( l1_pre_topc @ X24 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_1])).

thf('105',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ X0 ) @ k1_xboole_0 ) @ X0 )
      | ~ ( v2_tops_1 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['47','48','51'])).

thf('107',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v1_tops_1 @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( v2_tops_1 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['105','106'])).

thf('108',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( v1_tops_1 @ ( u1_struct_0 @ sk_A ) @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['102','107'])).

thf('109',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('110',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,(
    v1_tops_1 @ ( u1_struct_0 @ sk_A ) @ sk_A ),
    inference(demod,[status(thm)],['108','109','110'])).

thf('112',plain,(
    ! [X8: $i] :
      ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X8 ) ) ),
    inference(demod,[status(thm)],['70','71'])).

thf('113',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ~ ( v1_tops_1 @ X21 @ X22 )
      | ( ( k2_pre_topc @ X22 @ X21 )
        = ( k2_struct_0 @ X22 ) )
      | ~ ( l1_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[d3_tops_1])).

thf('114',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( k2_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) )
        = ( k2_struct_0 @ X0 ) )
      | ~ ( v1_tops_1 @ ( u1_struct_0 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['112','113'])).

thf('115',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( u1_struct_0 @ sk_A ) )
      = ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['111','114'])).

thf('116',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,
    ( ( k2_pre_topc @ sk_A @ ( u1_struct_0 @ sk_A ) )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['115','116'])).

thf('118',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['86','117','118'])).

thf('120',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['75','76'])).

thf('121',plain,(
    k1_xboole_0 = sk_B_1 ),
    inference(demod,[status(thm)],['36','119','120'])).

thf('122',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['121','122'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.VuBC98lNIP
% 0.13/0.35  % Computer   : n016.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 16:24:19 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.54/0.71  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.54/0.71  % Solved by: fo/fo7.sh
% 0.54/0.71  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.54/0.71  % done 392 iterations in 0.254s
% 0.54/0.71  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.54/0.71  % SZS output start Refutation
% 0.54/0.71  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.54/0.71  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.54/0.71  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.54/0.71  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.54/0.71  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.54/0.71  thf(v2_tops_1_type, type, v2_tops_1: $i > $i > $o).
% 0.54/0.71  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.54/0.71  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.54/0.71  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.54/0.71  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.54/0.71  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.54/0.71  thf(v1_tops_1_type, type, v1_tops_1: $i > $i > $o).
% 0.54/0.71  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.54/0.71  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.54/0.71  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.54/0.71  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.54/0.71  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.54/0.71  thf(v3_tops_1_type, type, v3_tops_1: $i > $i > $o).
% 0.54/0.71  thf(sk_A_type, type, sk_A: $i).
% 0.54/0.71  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.54/0.71  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.54/0.71  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.54/0.71  thf(t97_tops_1, conjecture,
% 0.54/0.71    (![A:$i]:
% 0.54/0.71     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.54/0.71       ( ![B:$i]:
% 0.54/0.71         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.54/0.71           ( ( ( v3_pre_topc @ B @ A ) & ( v3_tops_1 @ B @ A ) ) =>
% 0.54/0.71             ( ( B ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 0.54/0.71  thf(zf_stmt_0, negated_conjecture,
% 0.54/0.71    (~( ![A:$i]:
% 0.54/0.71        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.54/0.71          ( ![B:$i]:
% 0.54/0.71            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.54/0.71              ( ( ( v3_pre_topc @ B @ A ) & ( v3_tops_1 @ B @ A ) ) =>
% 0.54/0.71                ( ( B ) = ( k1_xboole_0 ) ) ) ) ) ) )),
% 0.54/0.71    inference('cnf.neg', [status(esa)], [t97_tops_1])).
% 0.54/0.71  thf('0', plain,
% 0.54/0.71      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.54/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.71  thf(involutiveness_k3_subset_1, axiom,
% 0.54/0.71    (![A:$i,B:$i]:
% 0.54/0.71     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.54/0.71       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 0.54/0.71  thf('1', plain,
% 0.54/0.71      (![X11 : $i, X12 : $i]:
% 0.54/0.71         (((k3_subset_1 @ X12 @ (k3_subset_1 @ X12 @ X11)) = (X11))
% 0.54/0.71          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12)))),
% 0.54/0.71      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.54/0.71  thf('2', plain,
% 0.54/0.71      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.54/0.71         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1)) = (sk_B_1))),
% 0.54/0.71      inference('sup-', [status(thm)], ['0', '1'])).
% 0.54/0.71  thf('3', plain,
% 0.54/0.71      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.54/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.71  thf(dt_k3_subset_1, axiom,
% 0.54/0.71    (![A:$i,B:$i]:
% 0.54/0.71     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.54/0.71       ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.54/0.71  thf('4', plain,
% 0.54/0.71      (![X9 : $i, X10 : $i]:
% 0.54/0.71         ((m1_subset_1 @ (k3_subset_1 @ X9 @ X10) @ (k1_zfmisc_1 @ X9))
% 0.54/0.71          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X9)))),
% 0.54/0.71      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 0.54/0.71  thf('5', plain,
% 0.54/0.71      ((m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.54/0.71        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.54/0.71      inference('sup-', [status(thm)], ['3', '4'])).
% 0.54/0.71  thf(t52_pre_topc, axiom,
% 0.54/0.71    (![A:$i]:
% 0.54/0.71     ( ( l1_pre_topc @ A ) =>
% 0.54/0.71       ( ![B:$i]:
% 0.54/0.71         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.54/0.71           ( ( ( v4_pre_topc @ B @ A ) => ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) & 
% 0.54/0.71             ( ( ( v2_pre_topc @ A ) & ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) =>
% 0.54/0.71               ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 0.54/0.71  thf('6', plain,
% 0.54/0.71      (![X19 : $i, X20 : $i]:
% 0.54/0.71         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.54/0.71          | ~ (v4_pre_topc @ X19 @ X20)
% 0.54/0.71          | ((k2_pre_topc @ X20 @ X19) = (X19))
% 0.54/0.71          | ~ (l1_pre_topc @ X20))),
% 0.54/0.71      inference('cnf', [status(esa)], [t52_pre_topc])).
% 0.54/0.71  thf('7', plain,
% 0.54/0.71      ((~ (l1_pre_topc @ sk_A)
% 0.54/0.71        | ((k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1))
% 0.54/0.71            = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1))
% 0.54/0.71        | ~ (v4_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ sk_A))),
% 0.54/0.71      inference('sup-', [status(thm)], ['5', '6'])).
% 0.54/0.71  thf('8', plain, ((l1_pre_topc @ sk_A)),
% 0.54/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.71  thf('9', plain,
% 0.54/0.71      ((((k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1))
% 0.54/0.71          = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1))
% 0.54/0.71        | ~ (v4_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ sk_A))),
% 0.54/0.71      inference('demod', [status(thm)], ['7', '8'])).
% 0.54/0.71  thf('10', plain,
% 0.54/0.71      ((m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.54/0.71        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.54/0.71      inference('sup-', [status(thm)], ['3', '4'])).
% 0.54/0.71  thf(d3_tops_1, axiom,
% 0.54/0.71    (![A:$i]:
% 0.54/0.71     ( ( l1_pre_topc @ A ) =>
% 0.54/0.71       ( ![B:$i]:
% 0.54/0.71         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.54/0.71           ( ( v1_tops_1 @ B @ A ) <=>
% 0.54/0.71             ( ( k2_pre_topc @ A @ B ) = ( k2_struct_0 @ A ) ) ) ) ) ))).
% 0.54/0.71  thf('11', plain,
% 0.54/0.71      (![X21 : $i, X22 : $i]:
% 0.54/0.71         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 0.54/0.71          | ~ (v1_tops_1 @ X21 @ X22)
% 0.54/0.71          | ((k2_pre_topc @ X22 @ X21) = (k2_struct_0 @ X22))
% 0.54/0.71          | ~ (l1_pre_topc @ X22))),
% 0.54/0.71      inference('cnf', [status(esa)], [d3_tops_1])).
% 0.54/0.71  thf('12', plain,
% 0.54/0.71      ((~ (l1_pre_topc @ sk_A)
% 0.54/0.71        | ((k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1))
% 0.54/0.71            = (k2_struct_0 @ sk_A))
% 0.54/0.71        | ~ (v1_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ sk_A))),
% 0.54/0.71      inference('sup-', [status(thm)], ['10', '11'])).
% 0.54/0.71  thf('13', plain, ((l1_pre_topc @ sk_A)),
% 0.54/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.71  thf('14', plain,
% 0.54/0.71      ((((k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1))
% 0.54/0.71          = (k2_struct_0 @ sk_A))
% 0.54/0.71        | ~ (v1_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ sk_A))),
% 0.54/0.71      inference('demod', [status(thm)], ['12', '13'])).
% 0.54/0.71  thf('15', plain,
% 0.54/0.71      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.54/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.71  thf(d4_tops_1, axiom,
% 0.54/0.71    (![A:$i]:
% 0.54/0.71     ( ( l1_pre_topc @ A ) =>
% 0.54/0.71       ( ![B:$i]:
% 0.54/0.71         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.54/0.71           ( ( v2_tops_1 @ B @ A ) <=>
% 0.54/0.71             ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) ))).
% 0.54/0.71  thf('16', plain,
% 0.54/0.71      (![X23 : $i, X24 : $i]:
% 0.54/0.71         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 0.54/0.71          | ~ (v2_tops_1 @ X23 @ X24)
% 0.54/0.71          | (v1_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ X24) @ X23) @ X24)
% 0.54/0.71          | ~ (l1_pre_topc @ X24))),
% 0.54/0.71      inference('cnf', [status(esa)], [d4_tops_1])).
% 0.54/0.71  thf('17', plain,
% 0.54/0.71      ((~ (l1_pre_topc @ sk_A)
% 0.54/0.71        | (v1_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ sk_A)
% 0.54/0.71        | ~ (v2_tops_1 @ sk_B_1 @ sk_A))),
% 0.54/0.71      inference('sup-', [status(thm)], ['15', '16'])).
% 0.54/0.71  thf('18', plain, ((l1_pre_topc @ sk_A)),
% 0.54/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.71  thf('19', plain,
% 0.54/0.71      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.54/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.71  thf(t92_tops_1, axiom,
% 0.54/0.71    (![A:$i]:
% 0.54/0.71     ( ( l1_pre_topc @ A ) =>
% 0.54/0.71       ( ![B:$i]:
% 0.54/0.71         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.54/0.71           ( ( v3_tops_1 @ B @ A ) => ( v2_tops_1 @ B @ A ) ) ) ) ))).
% 0.54/0.71  thf('20', plain,
% 0.54/0.71      (![X33 : $i, X34 : $i]:
% 0.54/0.71         (~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (u1_struct_0 @ X34)))
% 0.54/0.71          | (v2_tops_1 @ X33 @ X34)
% 0.54/0.71          | ~ (v3_tops_1 @ X33 @ X34)
% 0.54/0.71          | ~ (l1_pre_topc @ X34))),
% 0.54/0.71      inference('cnf', [status(esa)], [t92_tops_1])).
% 0.54/0.71  thf('21', plain,
% 0.54/0.71      ((~ (l1_pre_topc @ sk_A)
% 0.54/0.71        | ~ (v3_tops_1 @ sk_B_1 @ sk_A)
% 0.54/0.71        | (v2_tops_1 @ sk_B_1 @ sk_A))),
% 0.54/0.71      inference('sup-', [status(thm)], ['19', '20'])).
% 0.54/0.71  thf('22', plain, ((l1_pre_topc @ sk_A)),
% 0.54/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.71  thf('23', plain, ((v3_tops_1 @ sk_B_1 @ sk_A)),
% 0.54/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.71  thf('24', plain, ((v2_tops_1 @ sk_B_1 @ sk_A)),
% 0.54/0.71      inference('demod', [status(thm)], ['21', '22', '23'])).
% 0.54/0.71  thf('25', plain,
% 0.54/0.71      ((v1_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ sk_A)),
% 0.54/0.71      inference('demod', [status(thm)], ['17', '18', '24'])).
% 0.54/0.71  thf('26', plain,
% 0.54/0.71      (((k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1))
% 0.54/0.71         = (k2_struct_0 @ sk_A))),
% 0.54/0.71      inference('demod', [status(thm)], ['14', '25'])).
% 0.54/0.71  thf('27', plain,
% 0.54/0.71      ((((k2_struct_0 @ sk_A) = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1))
% 0.54/0.71        | ~ (v4_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ sk_A))),
% 0.54/0.71      inference('demod', [status(thm)], ['9', '26'])).
% 0.54/0.71  thf('28', plain,
% 0.54/0.71      ((m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.54/0.71        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.54/0.71      inference('sup-', [status(thm)], ['3', '4'])).
% 0.54/0.71  thf(t29_tops_1, axiom,
% 0.54/0.71    (![A:$i]:
% 0.54/0.71     ( ( l1_pre_topc @ A ) =>
% 0.54/0.71       ( ![B:$i]:
% 0.54/0.71         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.54/0.71           ( ( v4_pre_topc @ B @ A ) <=>
% 0.54/0.71             ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) ))).
% 0.54/0.71  thf('29', plain,
% 0.54/0.71      (![X29 : $i, X30 : $i]:
% 0.54/0.71         (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X30)))
% 0.54/0.71          | ~ (v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ X30) @ X29) @ X30)
% 0.54/0.71          | (v4_pre_topc @ X29 @ X30)
% 0.54/0.71          | ~ (l1_pre_topc @ X30))),
% 0.54/0.71      inference('cnf', [status(esa)], [t29_tops_1])).
% 0.54/0.71  thf('30', plain,
% 0.54/0.71      ((~ (l1_pre_topc @ sk_A)
% 0.54/0.71        | (v4_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ sk_A)
% 0.54/0.71        | ~ (v3_pre_topc @ 
% 0.54/0.71             (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.54/0.71              (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1)) @ 
% 0.54/0.71             sk_A))),
% 0.54/0.71      inference('sup-', [status(thm)], ['28', '29'])).
% 0.54/0.71  thf('31', plain, ((l1_pre_topc @ sk_A)),
% 0.54/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.71  thf('32', plain,
% 0.54/0.71      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.54/0.71         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1)) = (sk_B_1))),
% 0.54/0.71      inference('sup-', [status(thm)], ['0', '1'])).
% 0.54/0.71  thf('33', plain, ((v3_pre_topc @ sk_B_1 @ sk_A)),
% 0.54/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.71  thf('34', plain,
% 0.54/0.71      ((v4_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ sk_A)),
% 0.54/0.71      inference('demod', [status(thm)], ['30', '31', '32', '33'])).
% 0.54/0.71  thf('35', plain,
% 0.54/0.71      (((k2_struct_0 @ sk_A) = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1))),
% 0.54/0.71      inference('demod', [status(thm)], ['27', '34'])).
% 0.54/0.71  thf('36', plain,
% 0.54/0.71      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A)) = (sk_B_1))),
% 0.54/0.71      inference('demod', [status(thm)], ['2', '35'])).
% 0.54/0.71  thf(t4_subset_1, axiom,
% 0.54/0.71    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.54/0.71  thf('37', plain,
% 0.54/0.71      (![X15 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X15))),
% 0.54/0.71      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.54/0.71  thf('38', plain,
% 0.54/0.71      (![X11 : $i, X12 : $i]:
% 0.54/0.71         (((k3_subset_1 @ X12 @ (k3_subset_1 @ X12 @ X11)) = (X11))
% 0.54/0.71          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12)))),
% 0.54/0.71      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.54/0.71  thf('39', plain,
% 0.54/0.71      (![X0 : $i]:
% 0.54/0.71         ((k3_subset_1 @ X0 @ (k3_subset_1 @ X0 @ k1_xboole_0)) = (k1_xboole_0))),
% 0.54/0.71      inference('sup-', [status(thm)], ['37', '38'])).
% 0.54/0.71  thf(d3_tarski, axiom,
% 0.54/0.71    (![A:$i,B:$i]:
% 0.54/0.71     ( ( r1_tarski @ A @ B ) <=>
% 0.54/0.71       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.54/0.71  thf('40', plain,
% 0.54/0.71      (![X4 : $i, X6 : $i]:
% 0.54/0.71         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 0.54/0.71      inference('cnf', [status(esa)], [d3_tarski])).
% 0.54/0.71  thf(d1_xboole_0, axiom,
% 0.54/0.71    (![A:$i]:
% 0.54/0.71     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.54/0.71  thf('41', plain,
% 0.54/0.71      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.54/0.71      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.54/0.71  thf('42', plain,
% 0.54/0.71      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 0.54/0.71      inference('sup-', [status(thm)], ['40', '41'])).
% 0.54/0.71  thf(t39_subset_1, axiom,
% 0.54/0.71    (![A:$i,B:$i]:
% 0.54/0.71     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.54/0.72       ( ( r1_tarski @ ( k3_subset_1 @ A @ B ) @ B ) <=>
% 0.54/0.72         ( ( B ) = ( k2_subset_1 @ A ) ) ) ))).
% 0.54/0.72  thf('43', plain,
% 0.54/0.72      (![X13 : $i, X14 : $i]:
% 0.54/0.72         (~ (r1_tarski @ (k3_subset_1 @ X13 @ X14) @ X14)
% 0.54/0.72          | ((X14) = (k2_subset_1 @ X13))
% 0.54/0.72          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X13)))),
% 0.54/0.72      inference('cnf', [status(esa)], [t39_subset_1])).
% 0.54/0.72  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.54/0.72  thf('44', plain, (![X7 : $i]: ((k2_subset_1 @ X7) = (X7))),
% 0.54/0.72      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.54/0.72  thf('45', plain,
% 0.54/0.72      (![X13 : $i, X14 : $i]:
% 0.54/0.72         (~ (r1_tarski @ (k3_subset_1 @ X13 @ X14) @ X14)
% 0.54/0.72          | ((X14) = (X13))
% 0.54/0.72          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X13)))),
% 0.54/0.72      inference('demod', [status(thm)], ['43', '44'])).
% 0.54/0.72  thf('46', plain,
% 0.54/0.72      (![X0 : $i, X1 : $i]:
% 0.54/0.72         (~ (v1_xboole_0 @ (k3_subset_1 @ X1 @ X0))
% 0.54/0.72          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.54/0.72          | ((X0) = (X1)))),
% 0.54/0.72      inference('sup-', [status(thm)], ['42', '45'])).
% 0.54/0.72  thf('47', plain,
% 0.54/0.72      (![X0 : $i]:
% 0.54/0.72         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.54/0.72          | ((k3_subset_1 @ X0 @ k1_xboole_0) = (X0))
% 0.54/0.72          | ~ (m1_subset_1 @ (k3_subset_1 @ X0 @ k1_xboole_0) @ 
% 0.54/0.72               (k1_zfmisc_1 @ X0)))),
% 0.54/0.72      inference('sup-', [status(thm)], ['39', '46'])).
% 0.54/0.72  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.54/0.72  thf('48', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.54/0.72      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.54/0.72  thf('49', plain,
% 0.54/0.72      (![X15 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X15))),
% 0.54/0.72      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.54/0.72  thf('50', plain,
% 0.54/0.72      (![X9 : $i, X10 : $i]:
% 0.54/0.72         ((m1_subset_1 @ (k3_subset_1 @ X9 @ X10) @ (k1_zfmisc_1 @ X9))
% 0.54/0.72          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X9)))),
% 0.54/0.72      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 0.54/0.72  thf('51', plain,
% 0.54/0.72      (![X0 : $i]:
% 0.54/0.72         (m1_subset_1 @ (k3_subset_1 @ X0 @ k1_xboole_0) @ (k1_zfmisc_1 @ X0))),
% 0.54/0.72      inference('sup-', [status(thm)], ['49', '50'])).
% 0.54/0.72  thf('52', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ k1_xboole_0) = (X0))),
% 0.54/0.72      inference('demod', [status(thm)], ['47', '48', '51'])).
% 0.54/0.72  thf('53', plain,
% 0.54/0.72      (![X0 : $i, X1 : $i]:
% 0.54/0.72         (~ (v1_xboole_0 @ (k3_subset_1 @ X1 @ X0))
% 0.54/0.72          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.54/0.72          | ((X0) = (X1)))),
% 0.54/0.72      inference('sup-', [status(thm)], ['42', '45'])).
% 0.54/0.72  thf('54', plain,
% 0.54/0.72      (![X0 : $i]:
% 0.54/0.72         (~ (v1_xboole_0 @ X0)
% 0.54/0.72          | ((k1_xboole_0) = (X0))
% 0.54/0.72          | ~ (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0)))),
% 0.54/0.72      inference('sup-', [status(thm)], ['52', '53'])).
% 0.54/0.72  thf('55', plain,
% 0.54/0.72      (![X15 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X15))),
% 0.54/0.72      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.54/0.72  thf('56', plain,
% 0.54/0.72      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((k1_xboole_0) = (X0)))),
% 0.54/0.72      inference('demod', [status(thm)], ['54', '55'])).
% 0.54/0.72  thf('57', plain,
% 0.54/0.72      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.54/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.72  thf(fc9_tops_1, axiom,
% 0.54/0.72    (![A:$i,B:$i]:
% 0.54/0.72     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 0.54/0.72         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.54/0.72       ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ))).
% 0.54/0.72  thf('58', plain,
% 0.54/0.72      (![X25 : $i, X26 : $i]:
% 0.54/0.72         (~ (l1_pre_topc @ X25)
% 0.54/0.72          | ~ (v2_pre_topc @ X25)
% 0.54/0.72          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 0.54/0.72          | (v3_pre_topc @ (k1_tops_1 @ X25 @ X26) @ X25))),
% 0.54/0.72      inference('cnf', [status(esa)], [fc9_tops_1])).
% 0.54/0.72  thf('59', plain,
% 0.54/0.72      (((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_B_1) @ sk_A)
% 0.54/0.72        | ~ (v2_pre_topc @ sk_A)
% 0.54/0.72        | ~ (l1_pre_topc @ sk_A))),
% 0.54/0.72      inference('sup-', [status(thm)], ['57', '58'])).
% 0.54/0.72  thf('60', plain,
% 0.54/0.72      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.54/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.72  thf(t84_tops_1, axiom,
% 0.54/0.72    (![A:$i]:
% 0.54/0.72     ( ( l1_pre_topc @ A ) =>
% 0.54/0.72       ( ![B:$i]:
% 0.54/0.72         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.54/0.72           ( ( v2_tops_1 @ B @ A ) <=>
% 0.54/0.72             ( ( k1_tops_1 @ A @ B ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 0.54/0.72  thf('61', plain,
% 0.54/0.72      (![X31 : $i, X32 : $i]:
% 0.54/0.72         (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (u1_struct_0 @ X32)))
% 0.54/0.72          | ~ (v2_tops_1 @ X31 @ X32)
% 0.54/0.72          | ((k1_tops_1 @ X32 @ X31) = (k1_xboole_0))
% 0.54/0.72          | ~ (l1_pre_topc @ X32))),
% 0.54/0.72      inference('cnf', [status(esa)], [t84_tops_1])).
% 0.54/0.72  thf('62', plain,
% 0.54/0.72      ((~ (l1_pre_topc @ sk_A)
% 0.54/0.72        | ((k1_tops_1 @ sk_A @ sk_B_1) = (k1_xboole_0))
% 0.54/0.72        | ~ (v2_tops_1 @ sk_B_1 @ sk_A))),
% 0.54/0.72      inference('sup-', [status(thm)], ['60', '61'])).
% 0.54/0.72  thf('63', plain, ((l1_pre_topc @ sk_A)),
% 0.54/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.72  thf('64', plain, ((v2_tops_1 @ sk_B_1 @ sk_A)),
% 0.54/0.72      inference('demod', [status(thm)], ['21', '22', '23'])).
% 0.54/0.72  thf('65', plain, (((k1_tops_1 @ sk_A @ sk_B_1) = (k1_xboole_0))),
% 0.54/0.72      inference('demod', [status(thm)], ['62', '63', '64'])).
% 0.54/0.72  thf('66', plain, ((v2_pre_topc @ sk_A)),
% 0.54/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.72  thf('67', plain, ((l1_pre_topc @ sk_A)),
% 0.54/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.72  thf('68', plain, ((v3_pre_topc @ k1_xboole_0 @ sk_A)),
% 0.54/0.72      inference('demod', [status(thm)], ['59', '65', '66', '67'])).
% 0.54/0.72  thf('69', plain,
% 0.54/0.72      (![X0 : $i]: ((v3_pre_topc @ X0 @ sk_A) | ~ (v1_xboole_0 @ X0))),
% 0.54/0.72      inference('sup+', [status(thm)], ['56', '68'])).
% 0.54/0.72  thf(dt_k2_subset_1, axiom,
% 0.54/0.72    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.54/0.72  thf('70', plain,
% 0.54/0.72      (![X8 : $i]: (m1_subset_1 @ (k2_subset_1 @ X8) @ (k1_zfmisc_1 @ X8))),
% 0.54/0.72      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 0.54/0.72  thf('71', plain, (![X7 : $i]: ((k2_subset_1 @ X7) = (X7))),
% 0.54/0.72      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.54/0.72  thf('72', plain, (![X8 : $i]: (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X8))),
% 0.54/0.72      inference('demod', [status(thm)], ['70', '71'])).
% 0.54/0.72  thf('73', plain,
% 0.54/0.72      (![X29 : $i, X30 : $i]:
% 0.54/0.72         (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X30)))
% 0.54/0.72          | ~ (v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ X30) @ X29) @ X30)
% 0.54/0.72          | (v4_pre_topc @ X29 @ X30)
% 0.54/0.72          | ~ (l1_pre_topc @ X30))),
% 0.54/0.72      inference('cnf', [status(esa)], [t29_tops_1])).
% 0.54/0.72  thf('74', plain,
% 0.54/0.72      (![X0 : $i]:
% 0.54/0.72         (~ (l1_pre_topc @ X0)
% 0.54/0.72          | (v4_pre_topc @ (u1_struct_0 @ X0) @ X0)
% 0.54/0.72          | ~ (v3_pre_topc @ 
% 0.54/0.72               (k3_subset_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0)) @ X0))),
% 0.54/0.72      inference('sup-', [status(thm)], ['72', '73'])).
% 0.54/0.72  thf('75', plain,
% 0.54/0.72      (![X0 : $i]:
% 0.54/0.72         ((k3_subset_1 @ X0 @ (k3_subset_1 @ X0 @ k1_xboole_0)) = (k1_xboole_0))),
% 0.54/0.72      inference('sup-', [status(thm)], ['37', '38'])).
% 0.54/0.72  thf('76', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ k1_xboole_0) = (X0))),
% 0.54/0.72      inference('demod', [status(thm)], ['47', '48', '51'])).
% 0.54/0.72  thf('77', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k1_xboole_0))),
% 0.54/0.72      inference('demod', [status(thm)], ['75', '76'])).
% 0.54/0.72  thf('78', plain,
% 0.54/0.72      (![X0 : $i]:
% 0.54/0.72         (~ (l1_pre_topc @ X0)
% 0.54/0.72          | (v4_pre_topc @ (u1_struct_0 @ X0) @ X0)
% 0.54/0.72          | ~ (v3_pre_topc @ k1_xboole_0 @ X0))),
% 0.54/0.72      inference('demod', [status(thm)], ['74', '77'])).
% 0.54/0.72  thf('79', plain,
% 0.54/0.72      ((~ (v1_xboole_0 @ k1_xboole_0)
% 0.54/0.72        | (v4_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A)
% 0.54/0.72        | ~ (l1_pre_topc @ sk_A))),
% 0.54/0.72      inference('sup-', [status(thm)], ['69', '78'])).
% 0.54/0.72  thf('80', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.54/0.72      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.54/0.72  thf('81', plain, ((l1_pre_topc @ sk_A)),
% 0.54/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.72  thf('82', plain, ((v4_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A)),
% 0.54/0.72      inference('demod', [status(thm)], ['79', '80', '81'])).
% 0.54/0.72  thf('83', plain, (![X8 : $i]: (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X8))),
% 0.54/0.72      inference('demod', [status(thm)], ['70', '71'])).
% 0.54/0.72  thf('84', plain,
% 0.54/0.72      (![X19 : $i, X20 : $i]:
% 0.54/0.72         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.54/0.72          | ~ (v4_pre_topc @ X19 @ X20)
% 0.54/0.72          | ((k2_pre_topc @ X20 @ X19) = (X19))
% 0.54/0.72          | ~ (l1_pre_topc @ X20))),
% 0.54/0.72      inference('cnf', [status(esa)], [t52_pre_topc])).
% 0.54/0.72  thf('85', plain,
% 0.54/0.72      (![X0 : $i]:
% 0.54/0.72         (~ (l1_pre_topc @ X0)
% 0.54/0.72          | ((k2_pre_topc @ X0 @ (u1_struct_0 @ X0)) = (u1_struct_0 @ X0))
% 0.54/0.72          | ~ (v4_pre_topc @ (u1_struct_0 @ X0) @ X0))),
% 0.54/0.72      inference('sup-', [status(thm)], ['83', '84'])).
% 0.54/0.72  thf('86', plain,
% 0.54/0.72      ((((k2_pre_topc @ sk_A @ (u1_struct_0 @ sk_A)) = (u1_struct_0 @ sk_A))
% 0.54/0.72        | ~ (l1_pre_topc @ sk_A))),
% 0.54/0.72      inference('sup-', [status(thm)], ['82', '85'])).
% 0.54/0.72  thf('87', plain,
% 0.54/0.72      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((k1_xboole_0) = (X0)))),
% 0.54/0.72      inference('demod', [status(thm)], ['54', '55'])).
% 0.54/0.72  thf('88', plain,
% 0.54/0.72      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.54/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.72  thf(projectivity_k1_tops_1, axiom,
% 0.54/0.72    (![A:$i,B:$i]:
% 0.54/0.72     ( ( ( l1_pre_topc @ A ) & 
% 0.54/0.72         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.54/0.72       ( ( k1_tops_1 @ A @ ( k1_tops_1 @ A @ B ) ) = ( k1_tops_1 @ A @ B ) ) ))).
% 0.54/0.72  thf('89', plain,
% 0.54/0.72      (![X27 : $i, X28 : $i]:
% 0.54/0.72         (~ (l1_pre_topc @ X27)
% 0.54/0.72          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 0.54/0.72          | ((k1_tops_1 @ X27 @ (k1_tops_1 @ X27 @ X28))
% 0.54/0.72              = (k1_tops_1 @ X27 @ X28)))),
% 0.54/0.72      inference('cnf', [status(esa)], [projectivity_k1_tops_1])).
% 0.54/0.72  thf('90', plain,
% 0.54/0.72      ((((k1_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B_1))
% 0.54/0.72          = (k1_tops_1 @ sk_A @ sk_B_1))
% 0.54/0.72        | ~ (l1_pre_topc @ sk_A))),
% 0.54/0.72      inference('sup-', [status(thm)], ['88', '89'])).
% 0.54/0.72  thf('91', plain, (((k1_tops_1 @ sk_A @ sk_B_1) = (k1_xboole_0))),
% 0.54/0.72      inference('demod', [status(thm)], ['62', '63', '64'])).
% 0.54/0.72  thf('92', plain, (((k1_tops_1 @ sk_A @ sk_B_1) = (k1_xboole_0))),
% 0.54/0.72      inference('demod', [status(thm)], ['62', '63', '64'])).
% 0.54/0.72  thf('93', plain, ((l1_pre_topc @ sk_A)),
% 0.54/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.72  thf('94', plain, (((k1_tops_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))),
% 0.54/0.72      inference('demod', [status(thm)], ['90', '91', '92', '93'])).
% 0.54/0.72  thf('95', plain,
% 0.54/0.72      (![X15 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X15))),
% 0.54/0.72      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.54/0.72  thf('96', plain,
% 0.54/0.72      (![X31 : $i, X32 : $i]:
% 0.54/0.72         (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (u1_struct_0 @ X32)))
% 0.54/0.72          | ((k1_tops_1 @ X32 @ X31) != (k1_xboole_0))
% 0.54/0.72          | (v2_tops_1 @ X31 @ X32)
% 0.54/0.72          | ~ (l1_pre_topc @ X32))),
% 0.54/0.72      inference('cnf', [status(esa)], [t84_tops_1])).
% 0.54/0.72  thf('97', plain,
% 0.54/0.72      (![X0 : $i]:
% 0.54/0.72         (~ (l1_pre_topc @ X0)
% 0.54/0.72          | (v2_tops_1 @ k1_xboole_0 @ X0)
% 0.54/0.72          | ((k1_tops_1 @ X0 @ k1_xboole_0) != (k1_xboole_0)))),
% 0.54/0.72      inference('sup-', [status(thm)], ['95', '96'])).
% 0.54/0.72  thf('98', plain,
% 0.54/0.72      ((((k1_xboole_0) != (k1_xboole_0))
% 0.54/0.72        | (v2_tops_1 @ k1_xboole_0 @ sk_A)
% 0.54/0.72        | ~ (l1_pre_topc @ sk_A))),
% 0.54/0.72      inference('sup-', [status(thm)], ['94', '97'])).
% 0.54/0.72  thf('99', plain, ((l1_pre_topc @ sk_A)),
% 0.54/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.72  thf('100', plain,
% 0.54/0.72      ((((k1_xboole_0) != (k1_xboole_0)) | (v2_tops_1 @ k1_xboole_0 @ sk_A))),
% 0.54/0.72      inference('demod', [status(thm)], ['98', '99'])).
% 0.54/0.72  thf('101', plain, ((v2_tops_1 @ k1_xboole_0 @ sk_A)),
% 0.54/0.72      inference('simplify', [status(thm)], ['100'])).
% 0.54/0.72  thf('102', plain,
% 0.54/0.72      (![X0 : $i]: ((v2_tops_1 @ X0 @ sk_A) | ~ (v1_xboole_0 @ X0))),
% 0.54/0.72      inference('sup+', [status(thm)], ['87', '101'])).
% 0.54/0.72  thf('103', plain,
% 0.54/0.72      (![X15 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X15))),
% 0.54/0.72      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.54/0.72  thf('104', plain,
% 0.54/0.72      (![X23 : $i, X24 : $i]:
% 0.54/0.72         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 0.54/0.72          | ~ (v2_tops_1 @ X23 @ X24)
% 0.54/0.72          | (v1_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ X24) @ X23) @ X24)
% 0.54/0.72          | ~ (l1_pre_topc @ X24))),
% 0.54/0.72      inference('cnf', [status(esa)], [d4_tops_1])).
% 0.54/0.72  thf('105', plain,
% 0.54/0.72      (![X0 : $i]:
% 0.54/0.72         (~ (l1_pre_topc @ X0)
% 0.54/0.72          | (v1_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ X0) @ k1_xboole_0) @ X0)
% 0.54/0.72          | ~ (v2_tops_1 @ k1_xboole_0 @ X0))),
% 0.54/0.72      inference('sup-', [status(thm)], ['103', '104'])).
% 0.54/0.72  thf('106', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ k1_xboole_0) = (X0))),
% 0.54/0.72      inference('demod', [status(thm)], ['47', '48', '51'])).
% 0.54/0.72  thf('107', plain,
% 0.54/0.72      (![X0 : $i]:
% 0.54/0.72         (~ (l1_pre_topc @ X0)
% 0.54/0.72          | (v1_tops_1 @ (u1_struct_0 @ X0) @ X0)
% 0.54/0.72          | ~ (v2_tops_1 @ k1_xboole_0 @ X0))),
% 0.54/0.72      inference('demod', [status(thm)], ['105', '106'])).
% 0.54/0.72  thf('108', plain,
% 0.54/0.72      ((~ (v1_xboole_0 @ k1_xboole_0)
% 0.54/0.72        | (v1_tops_1 @ (u1_struct_0 @ sk_A) @ sk_A)
% 0.54/0.72        | ~ (l1_pre_topc @ sk_A))),
% 0.54/0.72      inference('sup-', [status(thm)], ['102', '107'])).
% 0.54/0.72  thf('109', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.54/0.72      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.54/0.72  thf('110', plain, ((l1_pre_topc @ sk_A)),
% 0.54/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.72  thf('111', plain, ((v1_tops_1 @ (u1_struct_0 @ sk_A) @ sk_A)),
% 0.54/0.72      inference('demod', [status(thm)], ['108', '109', '110'])).
% 0.54/0.72  thf('112', plain, (![X8 : $i]: (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X8))),
% 0.54/0.72      inference('demod', [status(thm)], ['70', '71'])).
% 0.54/0.72  thf('113', plain,
% 0.54/0.72      (![X21 : $i, X22 : $i]:
% 0.54/0.72         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 0.54/0.72          | ~ (v1_tops_1 @ X21 @ X22)
% 0.54/0.72          | ((k2_pre_topc @ X22 @ X21) = (k2_struct_0 @ X22))
% 0.54/0.72          | ~ (l1_pre_topc @ X22))),
% 0.54/0.72      inference('cnf', [status(esa)], [d3_tops_1])).
% 0.54/0.72  thf('114', plain,
% 0.54/0.72      (![X0 : $i]:
% 0.54/0.72         (~ (l1_pre_topc @ X0)
% 0.54/0.72          | ((k2_pre_topc @ X0 @ (u1_struct_0 @ X0)) = (k2_struct_0 @ X0))
% 0.54/0.72          | ~ (v1_tops_1 @ (u1_struct_0 @ X0) @ X0))),
% 0.54/0.72      inference('sup-', [status(thm)], ['112', '113'])).
% 0.54/0.72  thf('115', plain,
% 0.54/0.72      ((((k2_pre_topc @ sk_A @ (u1_struct_0 @ sk_A)) = (k2_struct_0 @ sk_A))
% 0.54/0.72        | ~ (l1_pre_topc @ sk_A))),
% 0.54/0.72      inference('sup-', [status(thm)], ['111', '114'])).
% 0.54/0.72  thf('116', plain, ((l1_pre_topc @ sk_A)),
% 0.54/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.72  thf('117', plain,
% 0.54/0.72      (((k2_pre_topc @ sk_A @ (u1_struct_0 @ sk_A)) = (k2_struct_0 @ sk_A))),
% 0.54/0.72      inference('demod', [status(thm)], ['115', '116'])).
% 0.54/0.72  thf('118', plain, ((l1_pre_topc @ sk_A)),
% 0.54/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.72  thf('119', plain, (((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))),
% 0.54/0.72      inference('demod', [status(thm)], ['86', '117', '118'])).
% 0.54/0.72  thf('120', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k1_xboole_0))),
% 0.54/0.72      inference('demod', [status(thm)], ['75', '76'])).
% 0.54/0.72  thf('121', plain, (((k1_xboole_0) = (sk_B_1))),
% 0.54/0.72      inference('demod', [status(thm)], ['36', '119', '120'])).
% 0.54/0.72  thf('122', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.54/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.72  thf('123', plain, ($false),
% 0.54/0.72      inference('simplify_reflect-', [status(thm)], ['121', '122'])).
% 0.54/0.72  
% 0.54/0.72  % SZS output end Refutation
% 0.54/0.72  
% 0.54/0.72  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
