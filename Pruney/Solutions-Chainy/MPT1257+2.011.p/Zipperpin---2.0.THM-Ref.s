%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.7SbWs3Zk9H

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:19 EST 2020

% Result     : Theorem 7.36s
% Output     : Refutation 7.36s
% Verified   : 
% Statistics : Number of formulae       :  110 ( 208 expanded)
%              Number of leaves         :   31 (  73 expanded)
%              Depth                    :   14
%              Number of atoms          : 1071 (2217 expanded)
%              Number of equality atoms :   39 (  48 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(t73_tops_1,conjecture,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_xboole_0 @ ( k1_tops_1 @ A @ B ) @ ( k2_tops_1 @ A @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_pre_topc @ A )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( r1_xboole_0 @ ( k1_tops_1 @ A @ B ) @ ( k2_tops_1 @ A @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t73_tops_1])).

thf('0',plain,(
    ~ ( r1_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k1_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('2',plain,(
    ! [X32: $i,X33: $i] :
      ( ~ ( l1_pre_topc @ X32 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X32 ) ) )
      | ( m1_subset_1 @ ( k1_tops_1 @ X32 @ X33 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X32 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tops_1])).

thf('3',plain,
    ( ( m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf(dt_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('6',plain,(
    ! [X3: $i,X4: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X3 @ X4 ) @ ( k1_zfmisc_1 @ X3 ) )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('7',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(t42_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( r1_tarski @ ( k3_subset_1 @ A @ B ) @ ( k3_subset_1 @ A @ ( k9_subset_1 @ A @ B @ C ) ) ) ) ) )).

thf('9',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ X23 ) )
      | ( r1_tarski @ ( k3_subset_1 @ X23 @ X24 ) @ ( k3_subset_1 @ X23 @ ( k9_subset_1 @ X23 @ X24 @ X22 ) ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t42_subset_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    r1_tarski @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['7','10'])).

thf('12',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('13',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k3_subset_1 @ X12 @ ( k3_subset_1 @ X12 @ X11 ) )
        = X11 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('14',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    = ( k1_tops_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ! [X3: $i,X4: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X3 @ X4 ) @ ( k1_zfmisc_1 @ X3 ) )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('17',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X3: $i,X4: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X3 @ X4 ) @ ( k1_zfmisc_1 @ X3 ) )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('19',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf(idempotence_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ B )
        = B ) ) )).

thf('20',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( ( k9_subset_1 @ X9 @ X8 @ X8 )
        = X8 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[idempotence_k9_subset_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    = ( k1_tops_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('23',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['11','14','21','22'])).

thf('24',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('26',plain,(
    ! [X34: $i,X35: $i] :
      ( ~ ( l1_pre_topc @ X34 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X34 ) ) )
      | ( m1_subset_1 @ ( k2_tops_1 @ X34 @ X35 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X34 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_1])).

thf('27',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf(t33_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ( k3_subset_1 @ A @ ( k7_subset_1 @ A @ B @ C ) )
            = ( k4_subset_1 @ A @ ( k3_subset_1 @ A @ B ) @ C ) ) ) ) )).

thf('30',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X20 ) )
      | ( ( k3_subset_1 @ X20 @ ( k7_subset_1 @ X20 @ X21 @ X19 ) )
        = ( k4_subset_1 @ X20 @ ( k3_subset_1 @ X20 @ X21 ) @ X19 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t33_subset_1])).

thf('31',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
        = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
    = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['24','31'])).

thf('33',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('34',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) )
      | ( ( k7_subset_1 @ X14 @ X13 @ X15 )
        = ( k4_xboole_0 @ X13 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf(t65_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_pre_topc @ A @ B )
            = ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('37',plain,(
    ! [X38: $i,X39: $i] :
      ( ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X39 ) ) )
      | ( ( k2_pre_topc @ X39 @ X38 )
        = ( k4_subset_1 @ ( u1_struct_0 @ X39 ) @ X38 @ ( k2_tops_1 @ X39 @ X38 ) ) )
      | ~ ( l1_pre_topc @ X39 ) ) ),
    inference(cnf,[status(esa)],[t65_tops_1])).

thf('38',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k2_tops_1 @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf(t62_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_tops_1 @ A @ B )
            = ( k2_tops_1 @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) )).

thf('41',plain,(
    ! [X36: $i,X37: $i] :
      ( ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X37 ) ) )
      | ( ( k2_tops_1 @ X37 @ X36 )
        = ( k2_tops_1 @ X37 @ ( k3_subset_1 @ ( u1_struct_0 @ X37 ) @ X36 ) ) )
      | ~ ( l1_pre_topc @ X37 ) ) ),
    inference(cnf,[status(esa)],[t62_tops_1])).

thf('42',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      = ( k2_tops_1 @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k3_subset_1 @ X12 @ ( k3_subset_1 @ X12 @ X11 ) )
        = X11 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('46',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = sk_B ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,
    ( ( k2_tops_1 @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = ( k2_tops_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['42','43','46'])).

thf('48',plain,
    ( ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['38','39','47'])).

thf('49',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf(dt_k2_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('50',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( l1_pre_topc @ X25 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X25 @ X26 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('51',plain,
    ( ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k3_subset_1 @ X12 @ ( k3_subset_1 @ X12 @ X11 ) )
        = X11 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('55',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) )
    = ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d1_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k1_tops_1 @ A @ B )
            = ( k3_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) )).

thf('57',plain,(
    ! [X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X31 ) ) )
      | ( ( k1_tops_1 @ X31 @ X30 )
        = ( k3_subset_1 @ ( u1_struct_0 @ X31 ) @ ( k2_pre_topc @ X31 @ ( k3_subset_1 @ ( u1_struct_0 @ X31 ) @ X30 ) ) ) )
      | ~ ( l1_pre_topc @ X31 ) ) ),
    inference(cnf,[status(esa)],[d1_tops_1])).

thf('58',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
      = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['55','60'])).

thf('62',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['48','61'])).

thf('63',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
    = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['32','35','62'])).

thf('64',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k7_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('65',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X6 ) )
      | ( m1_subset_1 @ ( k7_subset_1 @ X6 @ X5 @ X7 ) @ ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_subset_1])).

thf('66',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('68',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k3_subset_1 @ X12 @ ( k3_subset_1 @ X12 @ X11 ) )
        = X11 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k4_xboole_0 @ sk_B @ X0 ) ) )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    = ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['63','70'])).

thf('72',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    = ( k1_tops_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('73',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = ( k1_tops_1 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['71','72'])).

thf(t106_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) )
     => ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ A @ C ) ) ) )).

thf('74',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r1_tarski @ X0 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t106_xboole_1])).

thf('75',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k1_tops_1 @ sk_A @ sk_B ) )
      | ( r1_xboole_0 @ X0 @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    r1_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['23','75'])).

thf('77',plain,(
    $false ),
    inference(demod,[status(thm)],['0','76'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.7SbWs3Zk9H
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 10:49:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.20/0.35  % Number of cores: 8
% 0.20/0.35  % Python version: Python 3.6.8
% 0.20/0.36  % Running in FO mode
% 7.36/7.58  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 7.36/7.58  % Solved by: fo/fo7.sh
% 7.36/7.58  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 7.36/7.58  % done 3472 iterations in 7.113s
% 7.36/7.58  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 7.36/7.58  % SZS output start Refutation
% 7.36/7.58  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 7.36/7.58  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 7.36/7.58  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 7.36/7.58  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 7.36/7.58  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 7.36/7.58  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 7.36/7.58  thf(sk_B_type, type, sk_B: $i).
% 7.36/7.58  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 7.36/7.58  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 7.36/7.58  thf(sk_A_type, type, sk_A: $i).
% 7.36/7.58  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 7.36/7.58  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 7.36/7.58  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 7.36/7.58  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 7.36/7.58  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 7.36/7.58  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 7.36/7.58  thf(t73_tops_1, conjecture,
% 7.36/7.58    (![A:$i]:
% 7.36/7.58     ( ( l1_pre_topc @ A ) =>
% 7.36/7.58       ( ![B:$i]:
% 7.36/7.58         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 7.36/7.58           ( r1_xboole_0 @ ( k1_tops_1 @ A @ B ) @ ( k2_tops_1 @ A @ B ) ) ) ) ))).
% 7.36/7.58  thf(zf_stmt_0, negated_conjecture,
% 7.36/7.58    (~( ![A:$i]:
% 7.36/7.58        ( ( l1_pre_topc @ A ) =>
% 7.36/7.58          ( ![B:$i]:
% 7.36/7.58            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 7.36/7.58              ( r1_xboole_0 @ ( k1_tops_1 @ A @ B ) @ ( k2_tops_1 @ A @ B ) ) ) ) ) )),
% 7.36/7.58    inference('cnf.neg', [status(esa)], [t73_tops_1])).
% 7.36/7.58  thf('0', plain,
% 7.36/7.58      (~ (r1_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ (k2_tops_1 @ sk_A @ sk_B))),
% 7.36/7.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.36/7.58  thf('1', plain,
% 7.36/7.58      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 7.36/7.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.36/7.58  thf(dt_k1_tops_1, axiom,
% 7.36/7.58    (![A:$i,B:$i]:
% 7.36/7.58     ( ( ( l1_pre_topc @ A ) & 
% 7.36/7.58         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 7.36/7.58       ( m1_subset_1 @
% 7.36/7.58         ( k1_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 7.36/7.58  thf('2', plain,
% 7.36/7.58      (![X32 : $i, X33 : $i]:
% 7.36/7.58         (~ (l1_pre_topc @ X32)
% 7.36/7.58          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (u1_struct_0 @ X32)))
% 7.36/7.58          | (m1_subset_1 @ (k1_tops_1 @ X32 @ X33) @ 
% 7.36/7.58             (k1_zfmisc_1 @ (u1_struct_0 @ X32))))),
% 7.36/7.58      inference('cnf', [status(esa)], [dt_k1_tops_1])).
% 7.36/7.58  thf('3', plain,
% 7.36/7.58      (((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 7.36/7.58         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 7.36/7.58        | ~ (l1_pre_topc @ sk_A))),
% 7.36/7.58      inference('sup-', [status(thm)], ['1', '2'])).
% 7.36/7.58  thf('4', plain, ((l1_pre_topc @ sk_A)),
% 7.36/7.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.36/7.58  thf('5', plain,
% 7.36/7.58      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 7.36/7.58        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 7.36/7.58      inference('demod', [status(thm)], ['3', '4'])).
% 7.36/7.58  thf(dt_k3_subset_1, axiom,
% 7.36/7.58    (![A:$i,B:$i]:
% 7.36/7.58     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 7.36/7.58       ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 7.36/7.58  thf('6', plain,
% 7.36/7.58      (![X3 : $i, X4 : $i]:
% 7.36/7.58         ((m1_subset_1 @ (k3_subset_1 @ X3 @ X4) @ (k1_zfmisc_1 @ X3))
% 7.36/7.58          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X3)))),
% 7.36/7.58      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 7.36/7.58  thf('7', plain,
% 7.36/7.58      ((m1_subset_1 @ 
% 7.36/7.58        (k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B)) @ 
% 7.36/7.58        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 7.36/7.58      inference('sup-', [status(thm)], ['5', '6'])).
% 7.36/7.58  thf('8', plain,
% 7.36/7.58      ((m1_subset_1 @ 
% 7.36/7.58        (k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B)) @ 
% 7.36/7.58        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 7.36/7.58      inference('sup-', [status(thm)], ['5', '6'])).
% 7.36/7.58  thf(t42_subset_1, axiom,
% 7.36/7.58    (![A:$i,B:$i]:
% 7.36/7.58     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 7.36/7.58       ( ![C:$i]:
% 7.36/7.58         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 7.36/7.58           ( r1_tarski @
% 7.36/7.58             ( k3_subset_1 @ A @ B ) @ 
% 7.36/7.58             ( k3_subset_1 @ A @ ( k9_subset_1 @ A @ B @ C ) ) ) ) ) ))).
% 7.36/7.58  thf('9', plain,
% 7.36/7.58      (![X22 : $i, X23 : $i, X24 : $i]:
% 7.36/7.58         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ X23))
% 7.36/7.58          | (r1_tarski @ (k3_subset_1 @ X23 @ X24) @ 
% 7.36/7.58             (k3_subset_1 @ X23 @ (k9_subset_1 @ X23 @ X24 @ X22)))
% 7.36/7.58          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ X23)))),
% 7.36/7.58      inference('cnf', [status(esa)], [t42_subset_1])).
% 7.36/7.58  thf('10', plain,
% 7.36/7.58      (![X0 : $i]:
% 7.36/7.58         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 7.36/7.58          | (r1_tarski @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ X0) @ 
% 7.36/7.58             (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 7.36/7.58              (k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ 
% 7.36/7.58               (k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B))))))),
% 7.36/7.58      inference('sup-', [status(thm)], ['8', '9'])).
% 7.36/7.58  thf('11', plain,
% 7.36/7.58      ((r1_tarski @ 
% 7.36/7.58        (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 7.36/7.58         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B))) @ 
% 7.36/7.58        (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 7.36/7.58         (k9_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 7.36/7.58          (k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B)) @ 
% 7.36/7.58          (k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B)))))),
% 7.36/7.58      inference('sup-', [status(thm)], ['7', '10'])).
% 7.36/7.58  thf('12', plain,
% 7.36/7.58      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 7.36/7.58        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 7.36/7.58      inference('demod', [status(thm)], ['3', '4'])).
% 7.36/7.58  thf(involutiveness_k3_subset_1, axiom,
% 7.36/7.58    (![A:$i,B:$i]:
% 7.36/7.58     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 7.36/7.58       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 7.36/7.58  thf('13', plain,
% 7.36/7.58      (![X11 : $i, X12 : $i]:
% 7.36/7.58         (((k3_subset_1 @ X12 @ (k3_subset_1 @ X12 @ X11)) = (X11))
% 7.36/7.58          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12)))),
% 7.36/7.58      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 7.36/7.58  thf('14', plain,
% 7.36/7.58      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 7.36/7.58         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B)))
% 7.36/7.58         = (k1_tops_1 @ sk_A @ sk_B))),
% 7.36/7.58      inference('sup-', [status(thm)], ['12', '13'])).
% 7.36/7.58  thf('15', plain,
% 7.36/7.58      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 7.36/7.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.36/7.58  thf('16', plain,
% 7.36/7.58      (![X3 : $i, X4 : $i]:
% 7.36/7.58         ((m1_subset_1 @ (k3_subset_1 @ X3 @ X4) @ (k1_zfmisc_1 @ X3))
% 7.36/7.58          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X3)))),
% 7.36/7.58      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 7.36/7.58  thf('17', plain,
% 7.36/7.58      ((m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 7.36/7.58        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 7.36/7.58      inference('sup-', [status(thm)], ['15', '16'])).
% 7.36/7.58  thf('18', plain,
% 7.36/7.58      (![X3 : $i, X4 : $i]:
% 7.36/7.58         ((m1_subset_1 @ (k3_subset_1 @ X3 @ X4) @ (k1_zfmisc_1 @ X3))
% 7.36/7.58          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X3)))),
% 7.36/7.58      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 7.36/7.58  thf('19', plain,
% 7.36/7.58      ((m1_subset_1 @ 
% 7.36/7.58        (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 7.36/7.58         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)) @ 
% 7.36/7.58        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 7.36/7.58      inference('sup-', [status(thm)], ['17', '18'])).
% 7.36/7.58  thf(idempotence_k9_subset_1, axiom,
% 7.36/7.58    (![A:$i,B:$i,C:$i]:
% 7.36/7.58     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 7.36/7.58       ( ( k9_subset_1 @ A @ B @ B ) = ( B ) ) ))).
% 7.36/7.58  thf('20', plain,
% 7.36/7.58      (![X8 : $i, X9 : $i, X10 : $i]:
% 7.36/7.58         (((k9_subset_1 @ X9 @ X8 @ X8) = (X8))
% 7.36/7.58          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X9)))),
% 7.36/7.58      inference('cnf', [status(esa)], [idempotence_k9_subset_1])).
% 7.36/7.58  thf('21', plain,
% 7.36/7.58      (![X0 : $i]: ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ X0) = (X0))),
% 7.36/7.58      inference('sup-', [status(thm)], ['19', '20'])).
% 7.36/7.58  thf('22', plain,
% 7.36/7.58      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 7.36/7.58         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B)))
% 7.36/7.58         = (k1_tops_1 @ sk_A @ sk_B))),
% 7.36/7.58      inference('sup-', [status(thm)], ['12', '13'])).
% 7.36/7.58  thf('23', plain,
% 7.36/7.58      ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ sk_B))),
% 7.36/7.58      inference('demod', [status(thm)], ['11', '14', '21', '22'])).
% 7.36/7.58  thf('24', plain,
% 7.36/7.58      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 7.36/7.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.36/7.58  thf('25', plain,
% 7.36/7.58      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 7.36/7.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.36/7.58  thf(dt_k2_tops_1, axiom,
% 7.36/7.58    (![A:$i,B:$i]:
% 7.36/7.58     ( ( ( l1_pre_topc @ A ) & 
% 7.36/7.58         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 7.36/7.58       ( m1_subset_1 @
% 7.36/7.58         ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 7.36/7.58  thf('26', plain,
% 7.36/7.58      (![X34 : $i, X35 : $i]:
% 7.36/7.58         (~ (l1_pre_topc @ X34)
% 7.36/7.58          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (u1_struct_0 @ X34)))
% 7.36/7.58          | (m1_subset_1 @ (k2_tops_1 @ X34 @ X35) @ 
% 7.36/7.58             (k1_zfmisc_1 @ (u1_struct_0 @ X34))))),
% 7.36/7.58      inference('cnf', [status(esa)], [dt_k2_tops_1])).
% 7.36/7.58  thf('27', plain,
% 7.36/7.58      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 7.36/7.58         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 7.36/7.58        | ~ (l1_pre_topc @ sk_A))),
% 7.36/7.58      inference('sup-', [status(thm)], ['25', '26'])).
% 7.36/7.58  thf('28', plain, ((l1_pre_topc @ sk_A)),
% 7.36/7.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.36/7.58  thf('29', plain,
% 7.36/7.58      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 7.36/7.58        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 7.36/7.58      inference('demod', [status(thm)], ['27', '28'])).
% 7.36/7.58  thf(t33_subset_1, axiom,
% 7.36/7.58    (![A:$i,B:$i]:
% 7.36/7.58     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 7.36/7.58       ( ![C:$i]:
% 7.36/7.58         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 7.36/7.58           ( ( k3_subset_1 @ A @ ( k7_subset_1 @ A @ B @ C ) ) =
% 7.36/7.58             ( k4_subset_1 @ A @ ( k3_subset_1 @ A @ B ) @ C ) ) ) ) ))).
% 7.36/7.58  thf('30', plain,
% 7.36/7.58      (![X19 : $i, X20 : $i, X21 : $i]:
% 7.36/7.58         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ X20))
% 7.36/7.58          | ((k3_subset_1 @ X20 @ (k7_subset_1 @ X20 @ X21 @ X19))
% 7.36/7.58              = (k4_subset_1 @ X20 @ (k3_subset_1 @ X20 @ X21) @ X19))
% 7.36/7.58          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ X20)))),
% 7.36/7.58      inference('cnf', [status(esa)], [t33_subset_1])).
% 7.36/7.58  thf('31', plain,
% 7.36/7.58      (![X0 : $i]:
% 7.36/7.58         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 7.36/7.58          | ((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 7.36/7.58              (k7_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ 
% 7.36/7.58               (k2_tops_1 @ sk_A @ sk_B)))
% 7.36/7.58              = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 7.36/7.58                 (k3_subset_1 @ (u1_struct_0 @ sk_A) @ X0) @ 
% 7.36/7.58                 (k2_tops_1 @ sk_A @ sk_B))))),
% 7.36/7.58      inference('sup-', [status(thm)], ['29', '30'])).
% 7.36/7.58  thf('32', plain,
% 7.36/7.58      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 7.36/7.58         (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))
% 7.36/7.58         = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 7.36/7.58            (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 7.36/7.58            (k2_tops_1 @ sk_A @ sk_B)))),
% 7.36/7.58      inference('sup-', [status(thm)], ['24', '31'])).
% 7.36/7.58  thf('33', plain,
% 7.36/7.58      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 7.36/7.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.36/7.58  thf(redefinition_k7_subset_1, axiom,
% 7.36/7.58    (![A:$i,B:$i,C:$i]:
% 7.36/7.58     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 7.36/7.58       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 7.36/7.58  thf('34', plain,
% 7.36/7.58      (![X13 : $i, X14 : $i, X15 : $i]:
% 7.36/7.58         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14))
% 7.36/7.58          | ((k7_subset_1 @ X14 @ X13 @ X15) = (k4_xboole_0 @ X13 @ X15)))),
% 7.36/7.58      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 7.36/7.58  thf('35', plain,
% 7.36/7.58      (![X0 : $i]:
% 7.36/7.58         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 7.36/7.58           = (k4_xboole_0 @ sk_B @ X0))),
% 7.36/7.58      inference('sup-', [status(thm)], ['33', '34'])).
% 7.36/7.58  thf('36', plain,
% 7.36/7.58      ((m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 7.36/7.58        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 7.36/7.58      inference('sup-', [status(thm)], ['15', '16'])).
% 7.36/7.58  thf(t65_tops_1, axiom,
% 7.36/7.58    (![A:$i]:
% 7.36/7.58     ( ( l1_pre_topc @ A ) =>
% 7.36/7.58       ( ![B:$i]:
% 7.36/7.58         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 7.36/7.58           ( ( k2_pre_topc @ A @ B ) =
% 7.36/7.58             ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 7.36/7.58  thf('37', plain,
% 7.36/7.58      (![X38 : $i, X39 : $i]:
% 7.36/7.58         (~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (u1_struct_0 @ X39)))
% 7.36/7.58          | ((k2_pre_topc @ X39 @ X38)
% 7.36/7.58              = (k4_subset_1 @ (u1_struct_0 @ X39) @ X38 @ 
% 7.36/7.58                 (k2_tops_1 @ X39 @ X38)))
% 7.36/7.58          | ~ (l1_pre_topc @ X39))),
% 7.36/7.58      inference('cnf', [status(esa)], [t65_tops_1])).
% 7.36/7.58  thf('38', plain,
% 7.36/7.58      ((~ (l1_pre_topc @ sk_A)
% 7.36/7.58        | ((k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 7.36/7.58            = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 7.36/7.58               (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 7.36/7.58               (k2_tops_1 @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)))))),
% 7.36/7.58      inference('sup-', [status(thm)], ['36', '37'])).
% 7.36/7.58  thf('39', plain, ((l1_pre_topc @ sk_A)),
% 7.36/7.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.36/7.58  thf('40', plain,
% 7.36/7.58      ((m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 7.36/7.58        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 7.36/7.58      inference('sup-', [status(thm)], ['15', '16'])).
% 7.36/7.58  thf(t62_tops_1, axiom,
% 7.36/7.58    (![A:$i]:
% 7.36/7.58     ( ( l1_pre_topc @ A ) =>
% 7.36/7.58       ( ![B:$i]:
% 7.36/7.58         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 7.36/7.58           ( ( k2_tops_1 @ A @ B ) =
% 7.36/7.58             ( k2_tops_1 @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ))).
% 7.36/7.58  thf('41', plain,
% 7.36/7.58      (![X36 : $i, X37 : $i]:
% 7.36/7.58         (~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (u1_struct_0 @ X37)))
% 7.36/7.58          | ((k2_tops_1 @ X37 @ X36)
% 7.36/7.58              = (k2_tops_1 @ X37 @ (k3_subset_1 @ (u1_struct_0 @ X37) @ X36)))
% 7.36/7.58          | ~ (l1_pre_topc @ X37))),
% 7.36/7.58      inference('cnf', [status(esa)], [t62_tops_1])).
% 7.36/7.58  thf('42', plain,
% 7.36/7.58      ((~ (l1_pre_topc @ sk_A)
% 7.36/7.58        | ((k2_tops_1 @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 7.36/7.58            = (k2_tops_1 @ sk_A @ 
% 7.36/7.58               (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 7.36/7.58                (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)))))),
% 7.36/7.58      inference('sup-', [status(thm)], ['40', '41'])).
% 7.36/7.58  thf('43', plain, ((l1_pre_topc @ sk_A)),
% 7.36/7.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.36/7.58  thf('44', plain,
% 7.36/7.58      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 7.36/7.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.36/7.58  thf('45', plain,
% 7.36/7.58      (![X11 : $i, X12 : $i]:
% 7.36/7.58         (((k3_subset_1 @ X12 @ (k3_subset_1 @ X12 @ X11)) = (X11))
% 7.36/7.58          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12)))),
% 7.36/7.58      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 7.36/7.58  thf('46', plain,
% 7.36/7.58      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 7.36/7.58         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)) = (sk_B))),
% 7.36/7.58      inference('sup-', [status(thm)], ['44', '45'])).
% 7.36/7.58  thf('47', plain,
% 7.36/7.58      (((k2_tops_1 @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 7.36/7.58         = (k2_tops_1 @ sk_A @ sk_B))),
% 7.36/7.58      inference('demod', [status(thm)], ['42', '43', '46'])).
% 7.36/7.58  thf('48', plain,
% 7.36/7.58      (((k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 7.36/7.58         = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 7.36/7.58            (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 7.36/7.58            (k2_tops_1 @ sk_A @ sk_B)))),
% 7.36/7.58      inference('demod', [status(thm)], ['38', '39', '47'])).
% 7.36/7.58  thf('49', plain,
% 7.36/7.58      ((m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 7.36/7.58        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 7.36/7.58      inference('sup-', [status(thm)], ['15', '16'])).
% 7.36/7.58  thf(dt_k2_pre_topc, axiom,
% 7.36/7.58    (![A:$i,B:$i]:
% 7.36/7.58     ( ( ( l1_pre_topc @ A ) & 
% 7.36/7.58         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 7.36/7.58       ( m1_subset_1 @
% 7.36/7.58         ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 7.36/7.58  thf('50', plain,
% 7.36/7.58      (![X25 : $i, X26 : $i]:
% 7.36/7.58         (~ (l1_pre_topc @ X25)
% 7.36/7.58          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 7.36/7.58          | (m1_subset_1 @ (k2_pre_topc @ X25 @ X26) @ 
% 7.36/7.58             (k1_zfmisc_1 @ (u1_struct_0 @ X25))))),
% 7.36/7.58      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 7.36/7.58  thf('51', plain,
% 7.36/7.58      (((m1_subset_1 @ 
% 7.36/7.58         (k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)) @ 
% 7.36/7.58         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 7.36/7.58        | ~ (l1_pre_topc @ sk_A))),
% 7.36/7.58      inference('sup-', [status(thm)], ['49', '50'])).
% 7.36/7.58  thf('52', plain, ((l1_pre_topc @ sk_A)),
% 7.36/7.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.36/7.58  thf('53', plain,
% 7.36/7.58      ((m1_subset_1 @ 
% 7.36/7.58        (k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)) @ 
% 7.36/7.58        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 7.36/7.58      inference('demod', [status(thm)], ['51', '52'])).
% 7.36/7.58  thf('54', plain,
% 7.36/7.58      (![X11 : $i, X12 : $i]:
% 7.36/7.58         (((k3_subset_1 @ X12 @ (k3_subset_1 @ X12 @ X11)) = (X11))
% 7.36/7.58          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12)))),
% 7.36/7.58      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 7.36/7.58  thf('55', plain,
% 7.36/7.58      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 7.36/7.58         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 7.36/7.58          (k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))))
% 7.36/7.58         = (k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 7.36/7.58      inference('sup-', [status(thm)], ['53', '54'])).
% 7.36/7.58  thf('56', plain,
% 7.36/7.58      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 7.36/7.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.36/7.58  thf(d1_tops_1, axiom,
% 7.36/7.58    (![A:$i]:
% 7.36/7.58     ( ( l1_pre_topc @ A ) =>
% 7.36/7.58       ( ![B:$i]:
% 7.36/7.58         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 7.36/7.58           ( ( k1_tops_1 @ A @ B ) =
% 7.36/7.58             ( k3_subset_1 @
% 7.36/7.58               ( u1_struct_0 @ A ) @ 
% 7.36/7.58               ( k2_pre_topc @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) ))).
% 7.36/7.58  thf('57', plain,
% 7.36/7.58      (![X30 : $i, X31 : $i]:
% 7.36/7.58         (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ X31)))
% 7.36/7.58          | ((k1_tops_1 @ X31 @ X30)
% 7.36/7.58              = (k3_subset_1 @ (u1_struct_0 @ X31) @ 
% 7.36/7.58                 (k2_pre_topc @ X31 @ (k3_subset_1 @ (u1_struct_0 @ X31) @ X30))))
% 7.36/7.58          | ~ (l1_pre_topc @ X31))),
% 7.36/7.58      inference('cnf', [status(esa)], [d1_tops_1])).
% 7.36/7.58  thf('58', plain,
% 7.36/7.58      ((~ (l1_pre_topc @ sk_A)
% 7.36/7.58        | ((k1_tops_1 @ sk_A @ sk_B)
% 7.36/7.58            = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 7.36/7.58               (k2_pre_topc @ sk_A @ 
% 7.36/7.58                (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)))))),
% 7.36/7.58      inference('sup-', [status(thm)], ['56', '57'])).
% 7.36/7.58  thf('59', plain, ((l1_pre_topc @ sk_A)),
% 7.36/7.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.36/7.58  thf('60', plain,
% 7.36/7.58      (((k1_tops_1 @ sk_A @ sk_B)
% 7.36/7.58         = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 7.36/7.58            (k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 7.36/7.58      inference('demod', [status(thm)], ['58', '59'])).
% 7.36/7.58  thf('61', plain,
% 7.36/7.58      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B))
% 7.36/7.58         = (k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 7.36/7.58      inference('demod', [status(thm)], ['55', '60'])).
% 7.36/7.58  thf('62', plain,
% 7.36/7.58      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B))
% 7.36/7.58         = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 7.36/7.58            (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 7.36/7.58            (k2_tops_1 @ sk_A @ sk_B)))),
% 7.36/7.58      inference('demod', [status(thm)], ['48', '61'])).
% 7.36/7.58  thf('63', plain,
% 7.36/7.58      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 7.36/7.58         (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))
% 7.36/7.58         = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B)))),
% 7.36/7.58      inference('demod', [status(thm)], ['32', '35', '62'])).
% 7.36/7.58  thf('64', plain,
% 7.36/7.58      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 7.36/7.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.36/7.58  thf(dt_k7_subset_1, axiom,
% 7.36/7.58    (![A:$i,B:$i,C:$i]:
% 7.36/7.58     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 7.36/7.58       ( m1_subset_1 @ ( k7_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 7.36/7.58  thf('65', plain,
% 7.36/7.58      (![X5 : $i, X6 : $i, X7 : $i]:
% 7.36/7.58         (~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6))
% 7.36/7.58          | (m1_subset_1 @ (k7_subset_1 @ X6 @ X5 @ X7) @ (k1_zfmisc_1 @ X6)))),
% 7.36/7.58      inference('cnf', [status(esa)], [dt_k7_subset_1])).
% 7.36/7.58  thf('66', plain,
% 7.36/7.58      (![X0 : $i]:
% 7.36/7.58         (m1_subset_1 @ (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0) @ 
% 7.36/7.58          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 7.36/7.58      inference('sup-', [status(thm)], ['64', '65'])).
% 7.36/7.58  thf('67', plain,
% 7.36/7.58      (![X0 : $i]:
% 7.36/7.58         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 7.36/7.58           = (k4_xboole_0 @ sk_B @ X0))),
% 7.36/7.58      inference('sup-', [status(thm)], ['33', '34'])).
% 7.36/7.58  thf('68', plain,
% 7.36/7.58      (![X0 : $i]:
% 7.36/7.58         (m1_subset_1 @ (k4_xboole_0 @ sk_B @ X0) @ 
% 7.36/7.58          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 7.36/7.58      inference('demod', [status(thm)], ['66', '67'])).
% 7.36/7.58  thf('69', plain,
% 7.36/7.58      (![X11 : $i, X12 : $i]:
% 7.36/7.58         (((k3_subset_1 @ X12 @ (k3_subset_1 @ X12 @ X11)) = (X11))
% 7.36/7.58          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12)))),
% 7.36/7.58      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 7.36/7.58  thf('70', plain,
% 7.36/7.58      (![X0 : $i]:
% 7.36/7.58         ((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 7.36/7.58           (k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k4_xboole_0 @ sk_B @ X0)))
% 7.36/7.58           = (k4_xboole_0 @ sk_B @ X0))),
% 7.36/7.58      inference('sup-', [status(thm)], ['68', '69'])).
% 7.36/7.58  thf('71', plain,
% 7.36/7.58      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 7.36/7.58         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B)))
% 7.36/7.58         = (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 7.36/7.58      inference('sup+', [status(thm)], ['63', '70'])).
% 7.36/7.58  thf('72', plain,
% 7.36/7.58      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 7.36/7.58         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B)))
% 7.36/7.58         = (k1_tops_1 @ sk_A @ sk_B))),
% 7.36/7.58      inference('sup-', [status(thm)], ['12', '13'])).
% 7.36/7.58  thf('73', plain,
% 7.36/7.58      (((k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 7.36/7.58         = (k1_tops_1 @ sk_A @ sk_B))),
% 7.36/7.58      inference('sup+', [status(thm)], ['71', '72'])).
% 7.36/7.58  thf(t106_xboole_1, axiom,
% 7.36/7.58    (![A:$i,B:$i,C:$i]:
% 7.36/7.58     ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) =>
% 7.36/7.58       ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ))).
% 7.36/7.58  thf('74', plain,
% 7.36/7.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.36/7.58         ((r1_xboole_0 @ X0 @ X2)
% 7.36/7.58          | ~ (r1_tarski @ X0 @ (k4_xboole_0 @ X1 @ X2)))),
% 7.36/7.58      inference('cnf', [status(esa)], [t106_xboole_1])).
% 7.36/7.58  thf('75', plain,
% 7.36/7.58      (![X0 : $i]:
% 7.36/7.58         (~ (r1_tarski @ X0 @ (k1_tops_1 @ sk_A @ sk_B))
% 7.36/7.58          | (r1_xboole_0 @ X0 @ (k2_tops_1 @ sk_A @ sk_B)))),
% 7.36/7.58      inference('sup-', [status(thm)], ['73', '74'])).
% 7.36/7.58  thf('76', plain,
% 7.36/7.58      ((r1_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ (k2_tops_1 @ sk_A @ sk_B))),
% 7.36/7.58      inference('sup-', [status(thm)], ['23', '75'])).
% 7.36/7.58  thf('77', plain, ($false), inference('demod', [status(thm)], ['0', '76'])).
% 7.36/7.58  
% 7.36/7.58  % SZS output end Refutation
% 7.36/7.58  
% 7.36/7.59  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
