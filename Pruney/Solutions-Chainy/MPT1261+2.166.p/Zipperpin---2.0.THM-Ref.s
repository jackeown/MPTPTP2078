%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.wJ3bP8hPsS

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:04:03 EST 2020

% Result     : Theorem 0.45s
% Output     : Refutation 0.45s
% Verified   : 
% Statistics : Number of formulae       :  153 ( 925 expanded)
%              Number of leaves         :   36 ( 329 expanded)
%              Depth                    :   17
%              Number of atoms          : 1443 (9226 expanded)
%              Number of equality atoms :  108 ( 806 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

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
    ! [X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X34 ) ) )
      | ( r1_tarski @ ( k2_tops_1 @ X34 @ X33 ) @ X33 )
      | ~ ( v4_pre_topc @ X33 @ X34 )
      | ~ ( l1_pre_topc @ X34 ) ) ),
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
    ! [X24: $i,X26: $i] :
      ( ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ X26 ) )
      | ~ ( r1_tarski @ X24 @ X26 ) ) ),
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
    ! [X12: $i,X13: $i] :
      ( ( ( k3_subset_1 @ X13 @ ( k3_subset_1 @ X13 @ X12 ) )
        = X12 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('13',plain,
    ( ( ( k3_subset_1 @ sk_B @ ( k3_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
      = ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_B ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('15',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k3_subset_1 @ X8 @ X9 )
        = ( k4_xboole_0 @ X8 @ X9 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf(redefinition_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k6_subset_1 @ A @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('16',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k6_subset_1 @ X17 @ X18 )
      = ( k4_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('17',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k3_subset_1 @ X8 @ X9 )
        = ( k6_subset_1 @ X8 @ X9 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,
    ( ( ( k3_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k6_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['14','17'])).

thf('19',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t74_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k1_tops_1 @ A @ B )
            = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('20',plain,(
    ! [X35: $i,X36: $i] :
      ( ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X36 ) ) )
      | ( ( k1_tops_1 @ X36 @ X35 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X36 ) @ X35 @ ( k2_tops_1 @ X36 @ X35 ) ) )
      | ~ ( l1_pre_topc @ X36 ) ) ),
    inference(cnf,[status(esa)],[t74_tops_1])).

thf('21',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('24',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X20 ) )
      | ( ( k7_subset_1 @ X20 @ X19 @ X21 )
        = ( k4_xboole_0 @ X19 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('25',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k6_subset_1 @ X17 @ X18 )
      = ( k4_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('26',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X20 ) )
      | ( ( k7_subset_1 @ X20 @ X19 @ X21 )
        = ( k6_subset_1 @ X19 @ X21 ) ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k6_subset_1 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['23','26'])).

thf('28',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k6_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['21','22','27'])).

thf('29',plain,
    ( ( ( k3_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k1_tops_1 @ sk_A @ sk_B ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['18','28'])).

thf('30',plain,
    ( ( ( k3_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
      = ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['13','29'])).

thf('31',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k6_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['21','22','27'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('32',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ X4 @ ( k4_xboole_0 @ X4 @ X5 ) )
      = ( k3_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('33',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k6_subset_1 @ X17 @ X18 )
      = ( k4_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('34',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k6_subset_1 @ X17 @ X18 )
      = ( k4_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('35',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k6_subset_1 @ X4 @ ( k6_subset_1 @ X4 @ X5 ) )
      = ( k3_xboole_0 @ X4 @ X5 ) ) ),
    inference(demod,[status(thm)],['32','33','34'])).

thf(dt_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( m1_subset_1 @ ( k6_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('36',plain,(
    ! [X10: $i,X11: $i] :
      ( m1_subset_1 @ ( k6_subset_1 @ X10 @ X11 ) @ ( k1_zfmisc_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_subset_1])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k3_subset_1 @ X13 @ ( k3_subset_1 @ X13 @ X12 ) )
        = X12 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k3_subset_1 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('41',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k3_subset_1 @ X8 @ X9 )
        = ( k6_subset_1 @ X8 @ X9 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k6_subset_1 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k6_subset_1 @ X4 @ ( k6_subset_1 @ X4 @ X5 ) )
      = ( k3_xboole_0 @ X4 @ X5 ) ) ),
    inference(demod,[status(thm)],['32','33','34'])).

thf('44',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k6_subset_1 @ X4 @ ( k6_subset_1 @ X4 @ X5 ) )
      = ( k3_xboole_0 @ X4 @ X5 ) ) ),
    inference(demod,[status(thm)],['32','33','34'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_subset_1 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k6_subset_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k3_xboole_0 @ X0 @ ( k6_subset_1 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['42','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k3_xboole_0 @ X0 @ ( k6_subset_1 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['42','45'])).

thf('48',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k6_subset_1 @ X4 @ ( k6_subset_1 @ X4 @ X5 ) )
      = ( k3_xboole_0 @ X4 @ X5 ) ) ),
    inference(demod,[status(thm)],['32','33','34'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['39','46','47','48'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('51',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k6_subset_1 @ X17 @ X18 )
      = ( k4_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_subset_1 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_subset_1 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['49','52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_subset_1 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_subset_1 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k6_subset_1 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_subset_1 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k6_subset_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_subset_1 @ X1 @ X0 )
      = ( k3_xboole_0 @ X1 @ ( k6_subset_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['55','56'])).

thf('58',plain,
    ( ( k6_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = ( k3_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['31','57'])).

thf('59',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k6_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['21','22','27'])).

thf('60',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k3_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k3_xboole_0 @ X0 @ ( k6_subset_1 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['42','45'])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_subset_1 @ X1 @ X0 )
      = ( k3_xboole_0 @ X1 @ ( k6_subset_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['55','56'])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k6_subset_1 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,
    ( ( k3_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k6_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['60','63'])).

thf('65',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k3_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_subset_1 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('67',plain,
    ( ( k6_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k5_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['65','66'])).

thf('68',plain,
    ( ( k3_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k5_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['64','67'])).

thf('69',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k5_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['30','68'])).

thf('70',plain,
    ( ( k6_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k5_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['65','66'])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k6_subset_1 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['23','26'])).

thf('72',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('73',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k6_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k5_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['70','73'])).

thf('75',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( ( ( k2_tops_1 @ sk_A @ sk_B )
       != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
      & ( v4_pre_topc @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['69','74'])).

thf('76',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['75'])).

thf('77',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('78',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('79',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( l1_pre_topc @ X27 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
      | ( m1_subset_1 @ ( k2_tops_1 @ X27 @ X28 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_1])).

thf('80',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['80','81'])).

thf('83',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('84',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X15 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X15 ) )
      | ( ( k4_subset_1 @ X15 @ X14 @ X16 )
        = ( k2_xboole_0 @ X14 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('85',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
        = ( k2_xboole_0 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,
    ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['82','85'])).

thf('87',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t65_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_pre_topc @ A @ B )
            = ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('88',plain,(
    ! [X31: $i,X32: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X32 ) ) )
      | ( ( k2_pre_topc @ X32 @ X31 )
        = ( k4_subset_1 @ ( u1_struct_0 @ X32 ) @ X31 @ ( k2_tops_1 @ X32 @ X31 ) ) )
      | ~ ( l1_pre_topc @ X32 ) ) ),
    inference(cnf,[status(esa)],[t65_tops_1])).

thf('89',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
      = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['89','90'])).

thf('92',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['86','91'])).

thf('93',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k6_subset_1 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['23','26'])).

thf('94',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['2'])).

thf('95',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k6_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['93','94'])).

thf('96',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k6_subset_1 @ X4 @ ( k6_subset_1 @ X4 @ X5 ) )
      = ( k3_xboole_0 @ X4 @ X5 ) ) ),
    inference(demod,[status(thm)],['32','33','34'])).

thf('97',plain,
    ( ( ( k6_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k3_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['95','96'])).

thf('98',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_subset_1 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k6_subset_1 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('99',plain,
    ( ( ( k6_subset_1 @ sk_B @ ( k6_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
      = ( k6_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['97','98'])).

thf('100',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k6_subset_1 @ X4 @ ( k6_subset_1 @ X4 @ X5 ) )
      = ( k3_xboole_0 @ X4 @ X5 ) ) ),
    inference(demod,[status(thm)],['32','33','34'])).

thf('101',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k6_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['93','94'])).

thf('102',plain,
    ( ( ( k3_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['99','100','101'])).

thf(t22_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = A ) )).

thf('103',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ X2 @ ( k3_xboole_0 @ X2 @ X3 ) )
      = X2 ) ),
    inference(cnf,[status(esa)],[t22_xboole_1])).

thf('104',plain,
    ( ( ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['102','103'])).

thf('105',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['92','104'])).

thf('106',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc1_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v4_pre_topc @ ( k2_pre_topc @ A @ B ) @ A ) ) )).

thf('107',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( l1_pre_topc @ X29 )
      | ~ ( v2_pre_topc @ X29 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) )
      | ( v4_pre_topc @ ( k2_pre_topc @ X29 @ X30 ) @ X29 ) ) ),
    inference(cnf,[status(esa)],[fc1_tops_1])).

thf('108',plain,
    ( ( v4_pre_topc @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf('109',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,(
    v4_pre_topc @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['108','109','110'])).

thf('112',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['105','111'])).

thf('113',plain,
    ( ~ ( v4_pre_topc @ sk_B @ sk_A )
   <= ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('114',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['112','113'])).

thf('115',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','76','77','114'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.wJ3bP8hPsS
% 0.13/0.35  % Computer   : n002.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 19:10:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.45/0.66  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.45/0.66  % Solved by: fo/fo7.sh
% 0.45/0.66  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.45/0.66  % done 589 iterations in 0.216s
% 0.45/0.66  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.45/0.66  % SZS output start Refutation
% 0.45/0.66  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.45/0.66  thf(sk_A_type, type, sk_A: $i).
% 0.45/0.66  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.45/0.66  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.45/0.66  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.45/0.66  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.45/0.66  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.45/0.66  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.45/0.66  thf(sk_B_type, type, sk_B: $i).
% 0.45/0.66  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.45/0.66  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 0.45/0.66  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.45/0.66  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.45/0.66  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.45/0.66  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 0.45/0.66  thf(k6_subset_1_type, type, k6_subset_1: $i > $i > $i).
% 0.45/0.66  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.45/0.66  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 0.45/0.66  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.45/0.66  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.45/0.66  thf(t77_tops_1, conjecture,
% 0.45/0.66    (![A:$i]:
% 0.45/0.66     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.45/0.66       ( ![B:$i]:
% 0.45/0.66         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.45/0.66           ( ( v4_pre_topc @ B @ A ) <=>
% 0.45/0.66             ( ( k2_tops_1 @ A @ B ) =
% 0.45/0.66               ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ))).
% 0.45/0.66  thf(zf_stmt_0, negated_conjecture,
% 0.45/0.66    (~( ![A:$i]:
% 0.45/0.66        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.45/0.66          ( ![B:$i]:
% 0.45/0.66            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.45/0.66              ( ( v4_pre_topc @ B @ A ) <=>
% 0.45/0.66                ( ( k2_tops_1 @ A @ B ) =
% 0.45/0.66                  ( k7_subset_1 @
% 0.45/0.66                    ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ) )),
% 0.45/0.66    inference('cnf.neg', [status(esa)], [t77_tops_1])).
% 0.45/0.66  thf('0', plain,
% 0.45/0.66      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.45/0.66          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.45/0.66              (k1_tops_1 @ sk_A @ sk_B)))
% 0.45/0.66        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('1', plain,
% 0.45/0.66      (~
% 0.45/0.66       (((k2_tops_1 @ sk_A @ sk_B)
% 0.45/0.66          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.45/0.66             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 0.45/0.66       ~ ((v4_pre_topc @ sk_B @ sk_A))),
% 0.45/0.66      inference('split', [status(esa)], ['0'])).
% 0.45/0.66  thf('2', plain,
% 0.45/0.66      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.45/0.66          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.45/0.66             (k1_tops_1 @ sk_A @ sk_B)))
% 0.45/0.66        | (v4_pre_topc @ sk_B @ sk_A))),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('3', plain,
% 0.45/0.66      (((v4_pre_topc @ sk_B @ sk_A)) <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.45/0.66      inference('split', [status(esa)], ['2'])).
% 0.45/0.66  thf('4', plain,
% 0.45/0.66      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf(t69_tops_1, axiom,
% 0.45/0.66    (![A:$i]:
% 0.45/0.66     ( ( l1_pre_topc @ A ) =>
% 0.45/0.66       ( ![B:$i]:
% 0.45/0.66         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.45/0.66           ( ( v4_pre_topc @ B @ A ) =>
% 0.45/0.66             ( r1_tarski @ ( k2_tops_1 @ A @ B ) @ B ) ) ) ) ))).
% 0.45/0.66  thf('5', plain,
% 0.45/0.66      (![X33 : $i, X34 : $i]:
% 0.45/0.66         (~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (u1_struct_0 @ X34)))
% 0.45/0.66          | (r1_tarski @ (k2_tops_1 @ X34 @ X33) @ X33)
% 0.45/0.66          | ~ (v4_pre_topc @ X33 @ X34)
% 0.45/0.66          | ~ (l1_pre_topc @ X34))),
% 0.45/0.66      inference('cnf', [status(esa)], [t69_tops_1])).
% 0.45/0.66  thf('6', plain,
% 0.45/0.66      ((~ (l1_pre_topc @ sk_A)
% 0.45/0.66        | ~ (v4_pre_topc @ sk_B @ sk_A)
% 0.45/0.66        | (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))),
% 0.45/0.66      inference('sup-', [status(thm)], ['4', '5'])).
% 0.45/0.66  thf('7', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('8', plain,
% 0.45/0.66      ((~ (v4_pre_topc @ sk_B @ sk_A)
% 0.45/0.66        | (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))),
% 0.45/0.66      inference('demod', [status(thm)], ['6', '7'])).
% 0.45/0.66  thf('9', plain,
% 0.45/0.66      (((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))
% 0.45/0.66         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.45/0.66      inference('sup-', [status(thm)], ['3', '8'])).
% 0.45/0.66  thf(t3_subset, axiom,
% 0.45/0.66    (![A:$i,B:$i]:
% 0.45/0.66     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.45/0.66  thf('10', plain,
% 0.45/0.66      (![X24 : $i, X26 : $i]:
% 0.45/0.66         ((m1_subset_1 @ X24 @ (k1_zfmisc_1 @ X26)) | ~ (r1_tarski @ X24 @ X26))),
% 0.45/0.66      inference('cnf', [status(esa)], [t3_subset])).
% 0.45/0.66  thf('11', plain,
% 0.45/0.66      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_B)))
% 0.45/0.66         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.45/0.66      inference('sup-', [status(thm)], ['9', '10'])).
% 0.45/0.66  thf(involutiveness_k3_subset_1, axiom,
% 0.45/0.66    (![A:$i,B:$i]:
% 0.45/0.66     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.45/0.66       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 0.45/0.66  thf('12', plain,
% 0.45/0.66      (![X12 : $i, X13 : $i]:
% 0.45/0.66         (((k3_subset_1 @ X13 @ (k3_subset_1 @ X13 @ X12)) = (X12))
% 0.45/0.66          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13)))),
% 0.45/0.66      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.45/0.66  thf('13', plain,
% 0.45/0.66      ((((k3_subset_1 @ sk_B @ (k3_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))
% 0.45/0.66          = (k2_tops_1 @ sk_A @ sk_B)))
% 0.45/0.66         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.45/0.66      inference('sup-', [status(thm)], ['11', '12'])).
% 0.45/0.66  thf('14', plain,
% 0.45/0.66      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_B)))
% 0.45/0.66         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.45/0.66      inference('sup-', [status(thm)], ['9', '10'])).
% 0.45/0.66  thf(d5_subset_1, axiom,
% 0.45/0.66    (![A:$i,B:$i]:
% 0.45/0.66     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.45/0.66       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.45/0.66  thf('15', plain,
% 0.45/0.66      (![X8 : $i, X9 : $i]:
% 0.45/0.66         (((k3_subset_1 @ X8 @ X9) = (k4_xboole_0 @ X8 @ X9))
% 0.45/0.66          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X8)))),
% 0.45/0.66      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.45/0.66  thf(redefinition_k6_subset_1, axiom,
% 0.45/0.66    (![A:$i,B:$i]: ( ( k6_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.45/0.66  thf('16', plain,
% 0.45/0.66      (![X17 : $i, X18 : $i]:
% 0.45/0.66         ((k6_subset_1 @ X17 @ X18) = (k4_xboole_0 @ X17 @ X18))),
% 0.45/0.66      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.45/0.66  thf('17', plain,
% 0.45/0.66      (![X8 : $i, X9 : $i]:
% 0.45/0.66         (((k3_subset_1 @ X8 @ X9) = (k6_subset_1 @ X8 @ X9))
% 0.45/0.66          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X8)))),
% 0.45/0.66      inference('demod', [status(thm)], ['15', '16'])).
% 0.45/0.66  thf('18', plain,
% 0.45/0.66      ((((k3_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.45/0.66          = (k6_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))
% 0.45/0.66         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.45/0.66      inference('sup-', [status(thm)], ['14', '17'])).
% 0.45/0.66  thf('19', plain,
% 0.45/0.66      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf(t74_tops_1, axiom,
% 0.45/0.66    (![A:$i]:
% 0.45/0.66     ( ( l1_pre_topc @ A ) =>
% 0.45/0.66       ( ![B:$i]:
% 0.45/0.66         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.45/0.66           ( ( k1_tops_1 @ A @ B ) =
% 0.45/0.66             ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.45/0.66  thf('20', plain,
% 0.45/0.66      (![X35 : $i, X36 : $i]:
% 0.45/0.66         (~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (u1_struct_0 @ X36)))
% 0.45/0.66          | ((k1_tops_1 @ X36 @ X35)
% 0.45/0.66              = (k7_subset_1 @ (u1_struct_0 @ X36) @ X35 @ 
% 0.45/0.66                 (k2_tops_1 @ X36 @ X35)))
% 0.45/0.66          | ~ (l1_pre_topc @ X36))),
% 0.45/0.66      inference('cnf', [status(esa)], [t74_tops_1])).
% 0.45/0.66  thf('21', plain,
% 0.45/0.66      ((~ (l1_pre_topc @ sk_A)
% 0.45/0.66        | ((k1_tops_1 @ sk_A @ sk_B)
% 0.45/0.66            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.45/0.66               (k2_tops_1 @ sk_A @ sk_B))))),
% 0.45/0.66      inference('sup-', [status(thm)], ['19', '20'])).
% 0.45/0.66  thf('22', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('23', plain,
% 0.45/0.66      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf(redefinition_k7_subset_1, axiom,
% 0.45/0.66    (![A:$i,B:$i,C:$i]:
% 0.45/0.66     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.45/0.66       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 0.45/0.66  thf('24', plain,
% 0.45/0.66      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.45/0.66         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ X20))
% 0.45/0.66          | ((k7_subset_1 @ X20 @ X19 @ X21) = (k4_xboole_0 @ X19 @ X21)))),
% 0.45/0.66      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 0.45/0.66  thf('25', plain,
% 0.45/0.66      (![X17 : $i, X18 : $i]:
% 0.45/0.66         ((k6_subset_1 @ X17 @ X18) = (k4_xboole_0 @ X17 @ X18))),
% 0.45/0.66      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.45/0.66  thf('26', plain,
% 0.45/0.66      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.45/0.66         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ X20))
% 0.45/0.66          | ((k7_subset_1 @ X20 @ X19 @ X21) = (k6_subset_1 @ X19 @ X21)))),
% 0.45/0.66      inference('demod', [status(thm)], ['24', '25'])).
% 0.45/0.66  thf('27', plain,
% 0.45/0.66      (![X0 : $i]:
% 0.45/0.66         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.45/0.66           = (k6_subset_1 @ sk_B @ X0))),
% 0.45/0.66      inference('sup-', [status(thm)], ['23', '26'])).
% 0.45/0.66  thf('28', plain,
% 0.45/0.66      (((k1_tops_1 @ sk_A @ sk_B)
% 0.45/0.66         = (k6_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.45/0.66      inference('demod', [status(thm)], ['21', '22', '27'])).
% 0.45/0.66  thf('29', plain,
% 0.45/0.66      ((((k3_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.45/0.66          = (k1_tops_1 @ sk_A @ sk_B)))
% 0.45/0.66         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.45/0.66      inference('demod', [status(thm)], ['18', '28'])).
% 0.45/0.66  thf('30', plain,
% 0.45/0.66      ((((k3_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 0.45/0.66          = (k2_tops_1 @ sk_A @ sk_B)))
% 0.45/0.66         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.45/0.66      inference('demod', [status(thm)], ['13', '29'])).
% 0.45/0.66  thf('31', plain,
% 0.45/0.66      (((k1_tops_1 @ sk_A @ sk_B)
% 0.45/0.66         = (k6_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.45/0.66      inference('demod', [status(thm)], ['21', '22', '27'])).
% 0.45/0.66  thf(t48_xboole_1, axiom,
% 0.45/0.66    (![A:$i,B:$i]:
% 0.45/0.66     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.45/0.66  thf('32', plain,
% 0.45/0.66      (![X4 : $i, X5 : $i]:
% 0.45/0.66         ((k4_xboole_0 @ X4 @ (k4_xboole_0 @ X4 @ X5))
% 0.45/0.66           = (k3_xboole_0 @ X4 @ X5))),
% 0.45/0.66      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.45/0.66  thf('33', plain,
% 0.45/0.66      (![X17 : $i, X18 : $i]:
% 0.45/0.66         ((k6_subset_1 @ X17 @ X18) = (k4_xboole_0 @ X17 @ X18))),
% 0.45/0.66      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.45/0.66  thf('34', plain,
% 0.45/0.66      (![X17 : $i, X18 : $i]:
% 0.45/0.66         ((k6_subset_1 @ X17 @ X18) = (k4_xboole_0 @ X17 @ X18))),
% 0.45/0.66      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.45/0.66  thf('35', plain,
% 0.45/0.66      (![X4 : $i, X5 : $i]:
% 0.45/0.66         ((k6_subset_1 @ X4 @ (k6_subset_1 @ X4 @ X5))
% 0.45/0.66           = (k3_xboole_0 @ X4 @ X5))),
% 0.45/0.66      inference('demod', [status(thm)], ['32', '33', '34'])).
% 0.45/0.66  thf(dt_k6_subset_1, axiom,
% 0.45/0.66    (![A:$i,B:$i]:
% 0.45/0.66     ( m1_subset_1 @ ( k6_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.45/0.66  thf('36', plain,
% 0.45/0.66      (![X10 : $i, X11 : $i]:
% 0.45/0.66         (m1_subset_1 @ (k6_subset_1 @ X10 @ X11) @ (k1_zfmisc_1 @ X10))),
% 0.45/0.66      inference('cnf', [status(esa)], [dt_k6_subset_1])).
% 0.45/0.66  thf('37', plain,
% 0.45/0.66      (![X0 : $i, X1 : $i]:
% 0.45/0.66         (m1_subset_1 @ (k3_xboole_0 @ X1 @ X0) @ (k1_zfmisc_1 @ X1))),
% 0.45/0.66      inference('sup+', [status(thm)], ['35', '36'])).
% 0.45/0.66  thf('38', plain,
% 0.45/0.66      (![X12 : $i, X13 : $i]:
% 0.45/0.66         (((k3_subset_1 @ X13 @ (k3_subset_1 @ X13 @ X12)) = (X12))
% 0.45/0.66          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13)))),
% 0.45/0.66      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.45/0.66  thf('39', plain,
% 0.45/0.66      (![X0 : $i, X1 : $i]:
% 0.45/0.66         ((k3_subset_1 @ X0 @ (k3_subset_1 @ X0 @ (k3_xboole_0 @ X0 @ X1)))
% 0.45/0.66           = (k3_xboole_0 @ X0 @ X1))),
% 0.45/0.66      inference('sup-', [status(thm)], ['37', '38'])).
% 0.45/0.66  thf('40', plain,
% 0.45/0.66      (![X0 : $i, X1 : $i]:
% 0.45/0.66         (m1_subset_1 @ (k3_xboole_0 @ X1 @ X0) @ (k1_zfmisc_1 @ X1))),
% 0.45/0.66      inference('sup+', [status(thm)], ['35', '36'])).
% 0.45/0.66  thf('41', plain,
% 0.45/0.66      (![X8 : $i, X9 : $i]:
% 0.45/0.66         (((k3_subset_1 @ X8 @ X9) = (k6_subset_1 @ X8 @ X9))
% 0.45/0.66          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X8)))),
% 0.45/0.66      inference('demod', [status(thm)], ['15', '16'])).
% 0.45/0.66  thf('42', plain,
% 0.45/0.66      (![X0 : $i, X1 : $i]:
% 0.45/0.66         ((k3_subset_1 @ X0 @ (k3_xboole_0 @ X0 @ X1))
% 0.45/0.66           = (k6_subset_1 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.45/0.66      inference('sup-', [status(thm)], ['40', '41'])).
% 0.45/0.66  thf('43', plain,
% 0.45/0.66      (![X4 : $i, X5 : $i]:
% 0.45/0.66         ((k6_subset_1 @ X4 @ (k6_subset_1 @ X4 @ X5))
% 0.45/0.66           = (k3_xboole_0 @ X4 @ X5))),
% 0.45/0.66      inference('demod', [status(thm)], ['32', '33', '34'])).
% 0.45/0.66  thf('44', plain,
% 0.45/0.66      (![X4 : $i, X5 : $i]:
% 0.45/0.66         ((k6_subset_1 @ X4 @ (k6_subset_1 @ X4 @ X5))
% 0.45/0.66           = (k3_xboole_0 @ X4 @ X5))),
% 0.45/0.66      inference('demod', [status(thm)], ['32', '33', '34'])).
% 0.45/0.66  thf('45', plain,
% 0.45/0.66      (![X0 : $i, X1 : $i]:
% 0.45/0.66         ((k6_subset_1 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 0.45/0.66           = (k3_xboole_0 @ X1 @ (k6_subset_1 @ X1 @ X0)))),
% 0.45/0.66      inference('sup+', [status(thm)], ['43', '44'])).
% 0.45/0.66  thf('46', plain,
% 0.45/0.66      (![X0 : $i, X1 : $i]:
% 0.45/0.66         ((k3_subset_1 @ X0 @ (k3_xboole_0 @ X0 @ X1))
% 0.45/0.66           = (k3_xboole_0 @ X0 @ (k6_subset_1 @ X0 @ X1)))),
% 0.45/0.66      inference('demod', [status(thm)], ['42', '45'])).
% 0.45/0.66  thf('47', plain,
% 0.45/0.66      (![X0 : $i, X1 : $i]:
% 0.45/0.66         ((k3_subset_1 @ X0 @ (k3_xboole_0 @ X0 @ X1))
% 0.45/0.66           = (k3_xboole_0 @ X0 @ (k6_subset_1 @ X0 @ X1)))),
% 0.45/0.66      inference('demod', [status(thm)], ['42', '45'])).
% 0.45/0.66  thf('48', plain,
% 0.45/0.66      (![X4 : $i, X5 : $i]:
% 0.45/0.66         ((k6_subset_1 @ X4 @ (k6_subset_1 @ X4 @ X5))
% 0.45/0.66           = (k3_xboole_0 @ X4 @ X5))),
% 0.45/0.66      inference('demod', [status(thm)], ['32', '33', '34'])).
% 0.45/0.66  thf('49', plain,
% 0.45/0.66      (![X0 : $i, X1 : $i]:
% 0.45/0.66         ((k3_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1))
% 0.45/0.66           = (k3_xboole_0 @ X0 @ X1))),
% 0.45/0.66      inference('demod', [status(thm)], ['39', '46', '47', '48'])).
% 0.45/0.66  thf(t100_xboole_1, axiom,
% 0.45/0.66    (![A:$i,B:$i]:
% 0.45/0.66     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.45/0.66  thf('50', plain,
% 0.45/0.66      (![X0 : $i, X1 : $i]:
% 0.45/0.66         ((k4_xboole_0 @ X0 @ X1)
% 0.45/0.66           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.45/0.66      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.45/0.66  thf('51', plain,
% 0.45/0.66      (![X17 : $i, X18 : $i]:
% 0.45/0.66         ((k6_subset_1 @ X17 @ X18) = (k4_xboole_0 @ X17 @ X18))),
% 0.45/0.66      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.45/0.66  thf('52', plain,
% 0.45/0.66      (![X0 : $i, X1 : $i]:
% 0.45/0.66         ((k6_subset_1 @ X0 @ X1)
% 0.45/0.66           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.45/0.66      inference('demod', [status(thm)], ['50', '51'])).
% 0.45/0.66  thf('53', plain,
% 0.45/0.66      (![X0 : $i, X1 : $i]:
% 0.45/0.66         ((k6_subset_1 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 0.45/0.66           = (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.45/0.66      inference('sup+', [status(thm)], ['49', '52'])).
% 0.45/0.66  thf('54', plain,
% 0.45/0.66      (![X0 : $i, X1 : $i]:
% 0.45/0.66         ((k6_subset_1 @ X0 @ X1)
% 0.45/0.66           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.45/0.66      inference('demod', [status(thm)], ['50', '51'])).
% 0.45/0.66  thf('55', plain,
% 0.45/0.66      (![X0 : $i, X1 : $i]:
% 0.45/0.66         ((k6_subset_1 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 0.45/0.66           = (k6_subset_1 @ X1 @ X0))),
% 0.45/0.66      inference('demod', [status(thm)], ['53', '54'])).
% 0.45/0.66  thf('56', plain,
% 0.45/0.66      (![X0 : $i, X1 : $i]:
% 0.45/0.66         ((k6_subset_1 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 0.45/0.66           = (k3_xboole_0 @ X1 @ (k6_subset_1 @ X1 @ X0)))),
% 0.45/0.66      inference('sup+', [status(thm)], ['43', '44'])).
% 0.45/0.66  thf('57', plain,
% 0.45/0.66      (![X0 : $i, X1 : $i]:
% 0.45/0.66         ((k6_subset_1 @ X1 @ X0)
% 0.45/0.66           = (k3_xboole_0 @ X1 @ (k6_subset_1 @ X1 @ X0)))),
% 0.45/0.66      inference('sup+', [status(thm)], ['55', '56'])).
% 0.45/0.66  thf('58', plain,
% 0.45/0.66      (((k6_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.45/0.66         = (k3_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))),
% 0.45/0.66      inference('sup+', [status(thm)], ['31', '57'])).
% 0.45/0.66  thf('59', plain,
% 0.45/0.66      (((k1_tops_1 @ sk_A @ sk_B)
% 0.45/0.66         = (k6_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.45/0.66      inference('demod', [status(thm)], ['21', '22', '27'])).
% 0.45/0.66  thf('60', plain,
% 0.45/0.66      (((k1_tops_1 @ sk_A @ sk_B)
% 0.45/0.66         = (k3_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))),
% 0.45/0.66      inference('demod', [status(thm)], ['58', '59'])).
% 0.45/0.66  thf('61', plain,
% 0.45/0.66      (![X0 : $i, X1 : $i]:
% 0.45/0.66         ((k3_subset_1 @ X0 @ (k3_xboole_0 @ X0 @ X1))
% 0.45/0.66           = (k3_xboole_0 @ X0 @ (k6_subset_1 @ X0 @ X1)))),
% 0.45/0.66      inference('demod', [status(thm)], ['42', '45'])).
% 0.45/0.66  thf('62', plain,
% 0.45/0.66      (![X0 : $i, X1 : $i]:
% 0.45/0.66         ((k6_subset_1 @ X1 @ X0)
% 0.45/0.66           = (k3_xboole_0 @ X1 @ (k6_subset_1 @ X1 @ X0)))),
% 0.45/0.66      inference('sup+', [status(thm)], ['55', '56'])).
% 0.45/0.66  thf('63', plain,
% 0.45/0.66      (![X0 : $i, X1 : $i]:
% 0.45/0.66         ((k3_subset_1 @ X0 @ (k3_xboole_0 @ X0 @ X1))
% 0.45/0.66           = (k6_subset_1 @ X0 @ X1))),
% 0.45/0.66      inference('demod', [status(thm)], ['61', '62'])).
% 0.45/0.66  thf('64', plain,
% 0.45/0.66      (((k3_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 0.45/0.66         = (k6_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))),
% 0.45/0.66      inference('sup+', [status(thm)], ['60', '63'])).
% 0.45/0.66  thf('65', plain,
% 0.45/0.66      (((k1_tops_1 @ sk_A @ sk_B)
% 0.45/0.66         = (k3_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))),
% 0.45/0.66      inference('demod', [status(thm)], ['58', '59'])).
% 0.45/0.66  thf('66', plain,
% 0.45/0.66      (![X0 : $i, X1 : $i]:
% 0.45/0.66         ((k6_subset_1 @ X0 @ X1)
% 0.45/0.66           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.45/0.66      inference('demod', [status(thm)], ['50', '51'])).
% 0.45/0.66  thf('67', plain,
% 0.45/0.66      (((k6_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 0.45/0.66         = (k5_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))),
% 0.45/0.66      inference('sup+', [status(thm)], ['65', '66'])).
% 0.45/0.66  thf('68', plain,
% 0.45/0.66      (((k3_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 0.45/0.66         = (k5_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))),
% 0.45/0.66      inference('demod', [status(thm)], ['64', '67'])).
% 0.45/0.66  thf('69', plain,
% 0.45/0.66      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.45/0.66          = (k5_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.45/0.66         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.45/0.66      inference('sup+', [status(thm)], ['30', '68'])).
% 0.45/0.66  thf('70', plain,
% 0.45/0.66      (((k6_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 0.45/0.66         = (k5_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))),
% 0.45/0.66      inference('sup+', [status(thm)], ['65', '66'])).
% 0.45/0.66  thf('71', plain,
% 0.45/0.66      (![X0 : $i]:
% 0.45/0.66         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.45/0.66           = (k6_subset_1 @ sk_B @ X0))),
% 0.45/0.66      inference('sup-', [status(thm)], ['23', '26'])).
% 0.45/0.66  thf('72', plain,
% 0.45/0.66      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.45/0.66          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.45/0.66              (k1_tops_1 @ sk_A @ sk_B))))
% 0.45/0.66         <= (~
% 0.45/0.66             (((k2_tops_1 @ sk_A @ sk_B)
% 0.45/0.66                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.45/0.66                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.45/0.66      inference('split', [status(esa)], ['0'])).
% 0.45/0.66  thf('73', plain,
% 0.45/0.66      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.45/0.66          != (k6_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.45/0.66         <= (~
% 0.45/0.66             (((k2_tops_1 @ sk_A @ sk_B)
% 0.45/0.66                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.45/0.66                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.45/0.66      inference('sup-', [status(thm)], ['71', '72'])).
% 0.45/0.66  thf('74', plain,
% 0.45/0.66      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.45/0.66          != (k5_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.45/0.66         <= (~
% 0.45/0.66             (((k2_tops_1 @ sk_A @ sk_B)
% 0.45/0.66                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.45/0.66                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.45/0.66      inference('sup-', [status(thm)], ['70', '73'])).
% 0.45/0.66  thf('75', plain,
% 0.45/0.66      ((((k2_tops_1 @ sk_A @ sk_B) != (k2_tops_1 @ sk_A @ sk_B)))
% 0.45/0.66         <= (~
% 0.45/0.66             (((k2_tops_1 @ sk_A @ sk_B)
% 0.45/0.66                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.45/0.66                   (k1_tops_1 @ sk_A @ sk_B)))) & 
% 0.45/0.66             ((v4_pre_topc @ sk_B @ sk_A)))),
% 0.45/0.66      inference('sup-', [status(thm)], ['69', '74'])).
% 0.45/0.66  thf('76', plain,
% 0.45/0.66      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.45/0.66          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.45/0.66             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 0.45/0.66       ~ ((v4_pre_topc @ sk_B @ sk_A))),
% 0.45/0.66      inference('simplify', [status(thm)], ['75'])).
% 0.45/0.66  thf('77', plain,
% 0.45/0.66      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.45/0.66          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.45/0.66             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 0.45/0.66       ((v4_pre_topc @ sk_B @ sk_A))),
% 0.45/0.66      inference('split', [status(esa)], ['2'])).
% 0.45/0.66  thf('78', plain,
% 0.45/0.66      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf(dt_k2_tops_1, axiom,
% 0.45/0.66    (![A:$i,B:$i]:
% 0.45/0.66     ( ( ( l1_pre_topc @ A ) & 
% 0.45/0.66         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.45/0.66       ( m1_subset_1 @
% 0.45/0.66         ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.45/0.66  thf('79', plain,
% 0.45/0.66      (![X27 : $i, X28 : $i]:
% 0.45/0.66         (~ (l1_pre_topc @ X27)
% 0.45/0.66          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 0.45/0.66          | (m1_subset_1 @ (k2_tops_1 @ X27 @ X28) @ 
% 0.45/0.66             (k1_zfmisc_1 @ (u1_struct_0 @ X27))))),
% 0.45/0.66      inference('cnf', [status(esa)], [dt_k2_tops_1])).
% 0.45/0.66  thf('80', plain,
% 0.45/0.66      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.45/0.66         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.45/0.66        | ~ (l1_pre_topc @ sk_A))),
% 0.45/0.66      inference('sup-', [status(thm)], ['78', '79'])).
% 0.45/0.66  thf('81', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('82', plain,
% 0.45/0.66      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.45/0.66        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.66      inference('demod', [status(thm)], ['80', '81'])).
% 0.45/0.66  thf('83', plain,
% 0.45/0.66      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf(redefinition_k4_subset_1, axiom,
% 0.45/0.66    (![A:$i,B:$i,C:$i]:
% 0.45/0.66     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 0.45/0.66         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.45/0.66       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 0.45/0.66  thf('84', plain,
% 0.45/0.66      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.45/0.66         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X15))
% 0.45/0.66          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X15))
% 0.45/0.66          | ((k4_subset_1 @ X15 @ X14 @ X16) = (k2_xboole_0 @ X14 @ X16)))),
% 0.45/0.66      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 0.45/0.66  thf('85', plain,
% 0.45/0.66      (![X0 : $i]:
% 0.45/0.66         (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.45/0.66            = (k2_xboole_0 @ sk_B @ X0))
% 0.45/0.66          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.45/0.66      inference('sup-', [status(thm)], ['83', '84'])).
% 0.45/0.66  thf('86', plain,
% 0.45/0.66      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.45/0.66         = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.45/0.66      inference('sup-', [status(thm)], ['82', '85'])).
% 0.45/0.66  thf('87', plain,
% 0.45/0.66      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf(t65_tops_1, axiom,
% 0.45/0.66    (![A:$i]:
% 0.45/0.66     ( ( l1_pre_topc @ A ) =>
% 0.45/0.66       ( ![B:$i]:
% 0.45/0.66         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.45/0.66           ( ( k2_pre_topc @ A @ B ) =
% 0.45/0.66             ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.45/0.66  thf('88', plain,
% 0.45/0.66      (![X31 : $i, X32 : $i]:
% 0.45/0.66         (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (u1_struct_0 @ X32)))
% 0.45/0.66          | ((k2_pre_topc @ X32 @ X31)
% 0.45/0.66              = (k4_subset_1 @ (u1_struct_0 @ X32) @ X31 @ 
% 0.45/0.66                 (k2_tops_1 @ X32 @ X31)))
% 0.45/0.66          | ~ (l1_pre_topc @ X32))),
% 0.45/0.66      inference('cnf', [status(esa)], [t65_tops_1])).
% 0.45/0.66  thf('89', plain,
% 0.45/0.66      ((~ (l1_pre_topc @ sk_A)
% 0.45/0.66        | ((k2_pre_topc @ sk_A @ sk_B)
% 0.45/0.66            = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.45/0.66               (k2_tops_1 @ sk_A @ sk_B))))),
% 0.45/0.66      inference('sup-', [status(thm)], ['87', '88'])).
% 0.45/0.66  thf('90', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('91', plain,
% 0.45/0.66      (((k2_pre_topc @ sk_A @ sk_B)
% 0.45/0.66         = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.45/0.66            (k2_tops_1 @ sk_A @ sk_B)))),
% 0.45/0.66      inference('demod', [status(thm)], ['89', '90'])).
% 0.45/0.66  thf('92', plain,
% 0.45/0.66      (((k2_pre_topc @ sk_A @ sk_B)
% 0.45/0.66         = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.45/0.66      inference('sup+', [status(thm)], ['86', '91'])).
% 0.45/0.66  thf('93', plain,
% 0.45/0.66      (![X0 : $i]:
% 0.45/0.66         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.45/0.66           = (k6_subset_1 @ sk_B @ X0))),
% 0.45/0.66      inference('sup-', [status(thm)], ['23', '26'])).
% 0.45/0.66  thf('94', plain,
% 0.45/0.66      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.45/0.66          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.45/0.66             (k1_tops_1 @ sk_A @ sk_B))))
% 0.45/0.66         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.45/0.66                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.45/0.66                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.45/0.66      inference('split', [status(esa)], ['2'])).
% 0.45/0.66  thf('95', plain,
% 0.45/0.66      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.45/0.66          = (k6_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.45/0.66         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.45/0.66                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.45/0.66                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.45/0.66      inference('sup+', [status(thm)], ['93', '94'])).
% 0.45/0.66  thf('96', plain,
% 0.45/0.66      (![X4 : $i, X5 : $i]:
% 0.45/0.66         ((k6_subset_1 @ X4 @ (k6_subset_1 @ X4 @ X5))
% 0.45/0.66           = (k3_xboole_0 @ X4 @ X5))),
% 0.45/0.66      inference('demod', [status(thm)], ['32', '33', '34'])).
% 0.45/0.66  thf('97', plain,
% 0.45/0.66      ((((k6_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.45/0.66          = (k3_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.45/0.66         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.45/0.66                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.45/0.66                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.45/0.66      inference('sup+', [status(thm)], ['95', '96'])).
% 0.45/0.66  thf('98', plain,
% 0.45/0.66      (![X0 : $i, X1 : $i]:
% 0.45/0.66         ((k6_subset_1 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 0.45/0.66           = (k6_subset_1 @ X1 @ X0))),
% 0.45/0.66      inference('demod', [status(thm)], ['53', '54'])).
% 0.45/0.66  thf('99', plain,
% 0.45/0.66      ((((k6_subset_1 @ sk_B @ (k6_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))
% 0.45/0.66          = (k6_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.45/0.66         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.45/0.66                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.45/0.66                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.45/0.66      inference('sup+', [status(thm)], ['97', '98'])).
% 0.45/0.66  thf('100', plain,
% 0.45/0.66      (![X4 : $i, X5 : $i]:
% 0.45/0.66         ((k6_subset_1 @ X4 @ (k6_subset_1 @ X4 @ X5))
% 0.45/0.66           = (k3_xboole_0 @ X4 @ X5))),
% 0.45/0.66      inference('demod', [status(thm)], ['32', '33', '34'])).
% 0.45/0.66  thf('101', plain,
% 0.45/0.66      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.45/0.66          = (k6_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.45/0.66         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.45/0.66                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.45/0.66                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.45/0.66      inference('sup+', [status(thm)], ['93', '94'])).
% 0.45/0.66  thf('102', plain,
% 0.45/0.66      ((((k3_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.45/0.66          = (k2_tops_1 @ sk_A @ sk_B)))
% 0.45/0.66         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.45/0.66                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.45/0.66                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.45/0.66      inference('demod', [status(thm)], ['99', '100', '101'])).
% 0.45/0.66  thf(t22_xboole_1, axiom,
% 0.45/0.66    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( A ) ))).
% 0.45/0.66  thf('103', plain,
% 0.45/0.66      (![X2 : $i, X3 : $i]:
% 0.45/0.66         ((k2_xboole_0 @ X2 @ (k3_xboole_0 @ X2 @ X3)) = (X2))),
% 0.45/0.66      inference('cnf', [status(esa)], [t22_xboole_1])).
% 0.45/0.66  thf('104', plain,
% 0.45/0.66      ((((k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)) = (sk_B)))
% 0.45/0.66         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.45/0.66                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.45/0.66                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.45/0.66      inference('sup+', [status(thm)], ['102', '103'])).
% 0.45/0.66  thf('105', plain,
% 0.45/0.66      ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B)))
% 0.45/0.66         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.45/0.66                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.45/0.66                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.45/0.66      inference('sup+', [status(thm)], ['92', '104'])).
% 0.45/0.66  thf('106', plain,
% 0.45/0.66      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf(fc1_tops_1, axiom,
% 0.45/0.66    (![A:$i,B:$i]:
% 0.45/0.66     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 0.45/0.66         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.45/0.66       ( v4_pre_topc @ ( k2_pre_topc @ A @ B ) @ A ) ))).
% 0.45/0.66  thf('107', plain,
% 0.45/0.66      (![X29 : $i, X30 : $i]:
% 0.45/0.66         (~ (l1_pre_topc @ X29)
% 0.45/0.66          | ~ (v2_pre_topc @ X29)
% 0.45/0.66          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ X29)))
% 0.45/0.66          | (v4_pre_topc @ (k2_pre_topc @ X29 @ X30) @ X29))),
% 0.45/0.66      inference('cnf', [status(esa)], [fc1_tops_1])).
% 0.45/0.66  thf('108', plain,
% 0.45/0.66      (((v4_pre_topc @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A)
% 0.45/0.66        | ~ (v2_pre_topc @ sk_A)
% 0.45/0.66        | ~ (l1_pre_topc @ sk_A))),
% 0.45/0.66      inference('sup-', [status(thm)], ['106', '107'])).
% 0.45/0.66  thf('109', plain, ((v2_pre_topc @ sk_A)),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('110', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('111', plain, ((v4_pre_topc @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A)),
% 0.45/0.66      inference('demod', [status(thm)], ['108', '109', '110'])).
% 0.45/0.66  thf('112', plain,
% 0.45/0.66      (((v4_pre_topc @ sk_B @ sk_A))
% 0.45/0.66         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.45/0.66                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.45/0.66                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.45/0.66      inference('sup+', [status(thm)], ['105', '111'])).
% 0.45/0.66  thf('113', plain,
% 0.45/0.66      ((~ (v4_pre_topc @ sk_B @ sk_A)) <= (~ ((v4_pre_topc @ sk_B @ sk_A)))),
% 0.45/0.66      inference('split', [status(esa)], ['0'])).
% 0.45/0.66  thf('114', plain,
% 0.45/0.66      (~
% 0.45/0.66       (((k2_tops_1 @ sk_A @ sk_B)
% 0.45/0.66          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.45/0.66             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 0.45/0.66       ((v4_pre_topc @ sk_B @ sk_A))),
% 0.45/0.66      inference('sup-', [status(thm)], ['112', '113'])).
% 0.45/0.66  thf('115', plain, ($false),
% 0.45/0.66      inference('sat_resolution*', [status(thm)], ['1', '76', '77', '114'])).
% 0.45/0.66  
% 0.45/0.66  % SZS output end Refutation
% 0.45/0.66  
% 0.45/0.67  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
