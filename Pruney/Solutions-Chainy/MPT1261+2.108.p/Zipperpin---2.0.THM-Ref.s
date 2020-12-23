%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.8dFKLsiM10

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:54 EST 2020

% Result     : Theorem 0.39s
% Output     : Refutation 0.39s
% Verified   : 
% Statistics : Number of formulae       :  127 ( 211 expanded)
%              Number of leaves         :   35 (  73 expanded)
%              Depth                    :   14
%              Number of atoms          : 1197 (2662 expanded)
%              Number of equality atoms :   94 ( 175 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

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
    ! [X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) )
      | ~ ( v4_pre_topc @ X24 @ X25 )
      | ( ( k2_pre_topc @ X25 @ X24 )
        = X24 )
      | ~ ( l1_pre_topc @ X25 ) ) ),
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

thf('8',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B )
      = sk_B )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B )
      = sk_B )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['3','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l78_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_tops_1 @ A @ B )
            = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ ( k1_tops_1 @ A @ B ) ) ) ) ) )).

thf('11',plain,(
    ! [X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X31 ) ) )
      | ( ( k2_tops_1 @ X31 @ X30 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X31 ) @ ( k2_pre_topc @ X31 @ X30 ) @ ( k1_tops_1 @ X31 @ X30 ) ) )
      | ~ ( l1_pre_topc @ X31 ) ) ),
    inference(cnf,[status(esa)],[l78_tops_1])).

thf('12',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['9','14'])).

thf('16',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('17',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X18 ) )
      | ( ( k7_subset_1 @ X18 @ X17 @ X19 )
        = ( k4_xboole_0 @ X17 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['15','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('21',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('22',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( ( ( k2_tops_1 @ sk_A @ sk_B )
       != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
      & ( v4_pre_topc @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['19','22'])).

thf('24',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('27',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['2'])).

thf('28',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('30',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k2_xboole_0 @ X3 @ ( k4_xboole_0 @ X4 @ X3 ) )
      = ( k2_xboole_0 @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('31',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X5 @ X6 ) @ X7 )
      = ( k4_xboole_0 @ X5 @ ( k2_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X5 @ X6 ) @ X7 )
      = ( k4_xboole_0 @ X5 @ ( k2_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,
    ( ! [X0: $i] :
        ( ( k4_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k4_xboole_0 @ X0 @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
        = ( k4_xboole_0 @ ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) @ X0 ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['29','34'])).

thf('36',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('37',plain,
    ( ! [X0: $i] :
        ( ( k4_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k4_xboole_0 @ X0 @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
        = ( k4_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ X0 ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,
    ( ( ( k4_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k4_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['28','37'])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('39',plain,(
    ! [X11: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X11 ) @ ( k1_zfmisc_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('40',plain,(
    ! [X8: $i] :
      ( ( k2_subset_1 @ X8 )
      = X8 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('41',plain,(
    ! [X11: $i] :
      ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X11 ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('42',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k3_subset_1 @ X9 @ X10 )
        = ( k4_xboole_0 @ X9 @ X10 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('44',plain,(
    ! [X20: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('45',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k3_subset_1 @ X13 @ ( k3_subset_1 @ X13 @ X12 ) )
        = X12 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ ( k3_subset_1 @ X0 @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X20: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('48',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k3_subset_1 @ X9 @ X10 )
        = ( k4_xboole_0 @ X9 @ X10 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k2_xboole_0 @ X3 @ ( k4_xboole_0 @ X4 @ X3 ) )
      = ( k2_xboole_0 @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('52',plain,(
    ! [X2: $i] :
      ( ( k2_xboole_0 @ X2 @ k1_xboole_0 )
      = X2 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['50','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['49','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['46','57'])).

thf('59',plain,
    ( ( k1_xboole_0
      = ( k4_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['38','43','58'])).

thf('60',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k2_xboole_0 @ X3 @ ( k4_xboole_0 @ X4 @ X3 ) )
      = ( k2_xboole_0 @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('61',plain,
    ( ( ( k2_xboole_0 @ sk_B @ k1_xboole_0 )
      = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf('64',plain,
    ( ( sk_B
      = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['61','62','63'])).

thf('65',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('66',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( l1_pre_topc @ X26 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) )
      | ( m1_subset_1 @ ( k2_tops_1 @ X26 @ X27 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_1])).

thf('67',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('70',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('71',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X15 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X15 ) )
      | ( ( k4_subset_1 @ X15 @ X14 @ X16 )
        = ( k2_xboole_0 @ X14 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
        = ( k2_xboole_0 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,
    ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['69','72'])).

thf('74',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t65_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_pre_topc @ A @ B )
            = ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('75',plain,(
    ! [X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X33 ) ) )
      | ( ( k2_pre_topc @ X33 @ X32 )
        = ( k4_subset_1 @ ( u1_struct_0 @ X33 ) @ X32 @ ( k2_tops_1 @ X33 @ X32 ) ) )
      | ~ ( l1_pre_topc @ X33 ) ) ),
    inference(cnf,[status(esa)],[t65_tops_1])).

thf('76',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
      = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('79',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['73','78'])).

thf('80',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['64','79'])).

thf('81',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc1_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v4_pre_topc @ ( k2_pre_topc @ A @ B ) @ A ) ) )).

thf('82',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( l1_pre_topc @ X28 )
      | ~ ( v2_pre_topc @ X28 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ( v4_pre_topc @ ( k2_pre_topc @ X28 @ X29 ) @ X28 ) ) ),
    inference(cnf,[status(esa)],[fc1_tops_1])).

thf('83',plain,
    ( ( v4_pre_topc @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    v4_pre_topc @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['83','84','85'])).

thf('87',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['80','86'])).

thf('88',plain,
    ( ~ ( v4_pre_topc @ sk_B @ sk_A )
   <= ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('89',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','24','25','89'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.8dFKLsiM10
% 0.16/0.37  % Computer   : n014.cluster.edu
% 0.16/0.37  % Model      : x86_64 x86_64
% 0.16/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.37  % Memory     : 8042.1875MB
% 0.16/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.37  % CPULimit   : 60
% 0.16/0.37  % DateTime   : Tue Dec  1 09:34:08 EST 2020
% 0.16/0.37  % CPUTime    : 
% 0.16/0.37  % Running portfolio for 600 s
% 0.16/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.16/0.37  % Number of cores: 8
% 0.16/0.38  % Python version: Python 3.6.8
% 0.16/0.38  % Running in FO mode
% 0.39/0.59  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.39/0.59  % Solved by: fo/fo7.sh
% 0.39/0.59  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.39/0.59  % done 233 iterations in 0.108s
% 0.39/0.59  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.39/0.59  % SZS output start Refutation
% 0.39/0.59  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.39/0.59  thf(sk_A_type, type, sk_A: $i).
% 0.39/0.59  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.39/0.59  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.39/0.59  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.39/0.59  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.39/0.59  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 0.39/0.59  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.39/0.59  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.39/0.59  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.39/0.59  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.39/0.59  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.39/0.59  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 0.39/0.59  thf(sk_B_type, type, sk_B: $i).
% 0.39/0.59  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 0.39/0.59  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.39/0.59  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.39/0.59  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.39/0.59  thf(t77_tops_1, conjecture,
% 0.39/0.59    (![A:$i]:
% 0.39/0.59     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.39/0.59       ( ![B:$i]:
% 0.39/0.59         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.39/0.59           ( ( v4_pre_topc @ B @ A ) <=>
% 0.39/0.59             ( ( k2_tops_1 @ A @ B ) =
% 0.39/0.59               ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ))).
% 0.39/0.59  thf(zf_stmt_0, negated_conjecture,
% 0.39/0.59    (~( ![A:$i]:
% 0.39/0.59        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.39/0.59          ( ![B:$i]:
% 0.39/0.59            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.39/0.59              ( ( v4_pre_topc @ B @ A ) <=>
% 0.39/0.59                ( ( k2_tops_1 @ A @ B ) =
% 0.39/0.59                  ( k7_subset_1 @
% 0.39/0.59                    ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ) )),
% 0.39/0.59    inference('cnf.neg', [status(esa)], [t77_tops_1])).
% 0.39/0.59  thf('0', plain,
% 0.39/0.59      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.39/0.59          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.39/0.59              (k1_tops_1 @ sk_A @ sk_B)))
% 0.39/0.59        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('1', plain,
% 0.39/0.59      (~
% 0.39/0.59       (((k2_tops_1 @ sk_A @ sk_B)
% 0.39/0.59          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.39/0.59             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 0.39/0.59       ~ ((v4_pre_topc @ sk_B @ sk_A))),
% 0.39/0.59      inference('split', [status(esa)], ['0'])).
% 0.39/0.59  thf('2', plain,
% 0.39/0.59      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.39/0.59          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.39/0.59             (k1_tops_1 @ sk_A @ sk_B)))
% 0.39/0.59        | (v4_pre_topc @ sk_B @ sk_A))),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('3', plain,
% 0.39/0.59      (((v4_pre_topc @ sk_B @ sk_A)) <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.39/0.59      inference('split', [status(esa)], ['2'])).
% 0.39/0.59  thf('4', plain,
% 0.39/0.59      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf(t52_pre_topc, axiom,
% 0.39/0.59    (![A:$i]:
% 0.39/0.59     ( ( l1_pre_topc @ A ) =>
% 0.39/0.59       ( ![B:$i]:
% 0.39/0.59         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.39/0.59           ( ( ( v4_pre_topc @ B @ A ) => ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) & 
% 0.39/0.59             ( ( ( v2_pre_topc @ A ) & ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) =>
% 0.39/0.59               ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 0.39/0.59  thf('5', plain,
% 0.39/0.59      (![X24 : $i, X25 : $i]:
% 0.39/0.59         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 0.39/0.59          | ~ (v4_pre_topc @ X24 @ X25)
% 0.39/0.59          | ((k2_pre_topc @ X25 @ X24) = (X24))
% 0.39/0.59          | ~ (l1_pre_topc @ X25))),
% 0.39/0.59      inference('cnf', [status(esa)], [t52_pre_topc])).
% 0.39/0.59  thf('6', plain,
% 0.39/0.59      ((~ (l1_pre_topc @ sk_A)
% 0.39/0.59        | ((k2_pre_topc @ sk_A @ sk_B) = (sk_B))
% 0.39/0.59        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.39/0.59      inference('sup-', [status(thm)], ['4', '5'])).
% 0.39/0.59  thf('7', plain, ((l1_pre_topc @ sk_A)),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('8', plain,
% 0.39/0.59      ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B)) | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.39/0.59      inference('demod', [status(thm)], ['6', '7'])).
% 0.39/0.59  thf('9', plain,
% 0.39/0.59      ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B)))
% 0.39/0.59         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.39/0.59      inference('sup-', [status(thm)], ['3', '8'])).
% 0.39/0.59  thf('10', plain,
% 0.39/0.59      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf(l78_tops_1, axiom,
% 0.39/0.59    (![A:$i]:
% 0.39/0.59     ( ( l1_pre_topc @ A ) =>
% 0.39/0.59       ( ![B:$i]:
% 0.39/0.59         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.39/0.59           ( ( k2_tops_1 @ A @ B ) =
% 0.39/0.59             ( k7_subset_1 @
% 0.39/0.59               ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 0.39/0.59               ( k1_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.39/0.59  thf('11', plain,
% 0.39/0.59      (![X30 : $i, X31 : $i]:
% 0.39/0.59         (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ X31)))
% 0.39/0.59          | ((k2_tops_1 @ X31 @ X30)
% 0.39/0.59              = (k7_subset_1 @ (u1_struct_0 @ X31) @ 
% 0.39/0.59                 (k2_pre_topc @ X31 @ X30) @ (k1_tops_1 @ X31 @ X30)))
% 0.39/0.59          | ~ (l1_pre_topc @ X31))),
% 0.39/0.59      inference('cnf', [status(esa)], [l78_tops_1])).
% 0.39/0.59  thf('12', plain,
% 0.39/0.59      ((~ (l1_pre_topc @ sk_A)
% 0.39/0.59        | ((k2_tops_1 @ sk_A @ sk_B)
% 0.39/0.59            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.39/0.59               (k2_pre_topc @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ sk_B))))),
% 0.39/0.59      inference('sup-', [status(thm)], ['10', '11'])).
% 0.39/0.59  thf('13', plain, ((l1_pre_topc @ sk_A)),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('14', plain,
% 0.39/0.59      (((k2_tops_1 @ sk_A @ sk_B)
% 0.39/0.59         = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.39/0.59            (k1_tops_1 @ sk_A @ sk_B)))),
% 0.39/0.59      inference('demod', [status(thm)], ['12', '13'])).
% 0.39/0.59  thf('15', plain,
% 0.39/0.59      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.39/0.59          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.39/0.59             (k1_tops_1 @ sk_A @ sk_B))))
% 0.39/0.59         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.39/0.59      inference('sup+', [status(thm)], ['9', '14'])).
% 0.39/0.59  thf('16', plain,
% 0.39/0.59      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf(redefinition_k7_subset_1, axiom,
% 0.39/0.59    (![A:$i,B:$i,C:$i]:
% 0.39/0.59     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.39/0.59       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 0.39/0.59  thf('17', plain,
% 0.39/0.59      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.39/0.59         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X18))
% 0.39/0.59          | ((k7_subset_1 @ X18 @ X17 @ X19) = (k4_xboole_0 @ X17 @ X19)))),
% 0.39/0.59      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 0.39/0.59  thf('18', plain,
% 0.39/0.59      (![X0 : $i]:
% 0.39/0.59         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.39/0.59           = (k4_xboole_0 @ sk_B @ X0))),
% 0.39/0.59      inference('sup-', [status(thm)], ['16', '17'])).
% 0.39/0.59  thf('19', plain,
% 0.39/0.59      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.39/0.59          = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.39/0.59         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.39/0.59      inference('demod', [status(thm)], ['15', '18'])).
% 0.39/0.59  thf('20', plain,
% 0.39/0.59      (![X0 : $i]:
% 0.39/0.59         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.39/0.59           = (k4_xboole_0 @ sk_B @ X0))),
% 0.39/0.59      inference('sup-', [status(thm)], ['16', '17'])).
% 0.39/0.59  thf('21', plain,
% 0.39/0.59      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.39/0.59          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.39/0.59              (k1_tops_1 @ sk_A @ sk_B))))
% 0.39/0.59         <= (~
% 0.39/0.59             (((k2_tops_1 @ sk_A @ sk_B)
% 0.39/0.59                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.39/0.59                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.39/0.59      inference('split', [status(esa)], ['0'])).
% 0.39/0.59  thf('22', plain,
% 0.39/0.59      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.39/0.59          != (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.39/0.59         <= (~
% 0.39/0.59             (((k2_tops_1 @ sk_A @ sk_B)
% 0.39/0.59                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.39/0.59                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.39/0.59      inference('sup-', [status(thm)], ['20', '21'])).
% 0.39/0.59  thf('23', plain,
% 0.39/0.59      ((((k2_tops_1 @ sk_A @ sk_B) != (k2_tops_1 @ sk_A @ sk_B)))
% 0.39/0.59         <= (~
% 0.39/0.59             (((k2_tops_1 @ sk_A @ sk_B)
% 0.39/0.59                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.39/0.59                   (k1_tops_1 @ sk_A @ sk_B)))) & 
% 0.39/0.59             ((v4_pre_topc @ sk_B @ sk_A)))),
% 0.39/0.59      inference('sup-', [status(thm)], ['19', '22'])).
% 0.39/0.59  thf('24', plain,
% 0.39/0.59      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.39/0.59          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.39/0.59             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 0.39/0.59       ~ ((v4_pre_topc @ sk_B @ sk_A))),
% 0.39/0.59      inference('simplify', [status(thm)], ['23'])).
% 0.39/0.59  thf('25', plain,
% 0.39/0.59      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.39/0.59          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.39/0.59             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 0.39/0.59       ((v4_pre_topc @ sk_B @ sk_A))),
% 0.39/0.59      inference('split', [status(esa)], ['2'])).
% 0.39/0.59  thf('26', plain,
% 0.39/0.59      (![X0 : $i]:
% 0.39/0.59         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.39/0.59           = (k4_xboole_0 @ sk_B @ X0))),
% 0.39/0.59      inference('sup-', [status(thm)], ['16', '17'])).
% 0.39/0.59  thf('27', plain,
% 0.39/0.59      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.39/0.59          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.39/0.59             (k1_tops_1 @ sk_A @ sk_B))))
% 0.39/0.59         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.39/0.59                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.39/0.59                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.39/0.59      inference('split', [status(esa)], ['2'])).
% 0.39/0.59  thf('28', plain,
% 0.39/0.59      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.39/0.59          = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.39/0.59         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.39/0.59                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.39/0.59                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.39/0.59      inference('sup+', [status(thm)], ['26', '27'])).
% 0.39/0.59  thf('29', plain,
% 0.39/0.59      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.39/0.59          = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.39/0.59         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.39/0.59                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.39/0.59                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.39/0.59      inference('sup+', [status(thm)], ['26', '27'])).
% 0.39/0.59  thf(t39_xboole_1, axiom,
% 0.39/0.59    (![A:$i,B:$i]:
% 0.39/0.59     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.39/0.59  thf('30', plain,
% 0.39/0.59      (![X3 : $i, X4 : $i]:
% 0.39/0.59         ((k2_xboole_0 @ X3 @ (k4_xboole_0 @ X4 @ X3))
% 0.39/0.59           = (k2_xboole_0 @ X3 @ X4))),
% 0.39/0.59      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.39/0.59  thf(t41_xboole_1, axiom,
% 0.39/0.59    (![A:$i,B:$i,C:$i]:
% 0.39/0.59     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 0.39/0.59       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 0.39/0.59  thf('31', plain,
% 0.39/0.59      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.39/0.59         ((k4_xboole_0 @ (k4_xboole_0 @ X5 @ X6) @ X7)
% 0.39/0.59           = (k4_xboole_0 @ X5 @ (k2_xboole_0 @ X6 @ X7)))),
% 0.39/0.59      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.39/0.59  thf('32', plain,
% 0.39/0.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.39/0.59         ((k4_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ (k4_xboole_0 @ X0 @ X1))
% 0.39/0.59           = (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.39/0.59      inference('sup+', [status(thm)], ['30', '31'])).
% 0.39/0.59  thf('33', plain,
% 0.39/0.59      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.39/0.59         ((k4_xboole_0 @ (k4_xboole_0 @ X5 @ X6) @ X7)
% 0.39/0.59           = (k4_xboole_0 @ X5 @ (k2_xboole_0 @ X6 @ X7)))),
% 0.39/0.59      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.39/0.59  thf('34', plain,
% 0.39/0.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.39/0.59         ((k4_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ (k4_xboole_0 @ X0 @ X1))
% 0.39/0.59           = (k4_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0))),
% 0.39/0.59      inference('demod', [status(thm)], ['32', '33'])).
% 0.39/0.59  thf('35', plain,
% 0.39/0.59      ((![X0 : $i]:
% 0.39/0.59          ((k4_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.39/0.59            (k4_xboole_0 @ X0 @ (k1_tops_1 @ sk_A @ sk_B)))
% 0.39/0.59            = (k4_xboole_0 @ 
% 0.39/0.59               (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)) @ X0)))
% 0.39/0.59         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.39/0.59                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.39/0.59                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.39/0.59      inference('sup+', [status(thm)], ['29', '34'])).
% 0.39/0.59  thf('36', plain,
% 0.39/0.59      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.39/0.59          = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.39/0.59         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.39/0.59                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.39/0.59                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.39/0.59      inference('sup+', [status(thm)], ['26', '27'])).
% 0.39/0.59  thf('37', plain,
% 0.39/0.59      ((![X0 : $i]:
% 0.39/0.59          ((k4_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.39/0.59            (k4_xboole_0 @ X0 @ (k1_tops_1 @ sk_A @ sk_B)))
% 0.39/0.59            = (k4_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ X0)))
% 0.39/0.59         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.39/0.59                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.39/0.59                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.39/0.59      inference('demod', [status(thm)], ['35', '36'])).
% 0.39/0.59  thf('38', plain,
% 0.39/0.59      ((((k4_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ (k2_tops_1 @ sk_A @ sk_B))
% 0.39/0.59          = (k4_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)))
% 0.39/0.59         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.39/0.59                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.39/0.59                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.39/0.59      inference('sup+', [status(thm)], ['28', '37'])).
% 0.39/0.59  thf(dt_k2_subset_1, axiom,
% 0.39/0.59    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.39/0.59  thf('39', plain,
% 0.39/0.59      (![X11 : $i]: (m1_subset_1 @ (k2_subset_1 @ X11) @ (k1_zfmisc_1 @ X11))),
% 0.39/0.59      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 0.39/0.59  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.39/0.59  thf('40', plain, (![X8 : $i]: ((k2_subset_1 @ X8) = (X8))),
% 0.39/0.59      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.39/0.59  thf('41', plain, (![X11 : $i]: (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X11))),
% 0.39/0.59      inference('demod', [status(thm)], ['39', '40'])).
% 0.39/0.59  thf(d5_subset_1, axiom,
% 0.39/0.59    (![A:$i,B:$i]:
% 0.39/0.59     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.39/0.59       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.39/0.59  thf('42', plain,
% 0.39/0.59      (![X9 : $i, X10 : $i]:
% 0.39/0.59         (((k3_subset_1 @ X9 @ X10) = (k4_xboole_0 @ X9 @ X10))
% 0.39/0.59          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X9)))),
% 0.39/0.59      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.39/0.59  thf('43', plain,
% 0.39/0.59      (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 0.39/0.59      inference('sup-', [status(thm)], ['41', '42'])).
% 0.39/0.59  thf(t4_subset_1, axiom,
% 0.39/0.59    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.39/0.59  thf('44', plain,
% 0.39/0.59      (![X20 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X20))),
% 0.39/0.59      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.39/0.59  thf(involutiveness_k3_subset_1, axiom,
% 0.39/0.59    (![A:$i,B:$i]:
% 0.39/0.59     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.39/0.59       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 0.39/0.59  thf('45', plain,
% 0.39/0.59      (![X12 : $i, X13 : $i]:
% 0.39/0.59         (((k3_subset_1 @ X13 @ (k3_subset_1 @ X13 @ X12)) = (X12))
% 0.39/0.59          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13)))),
% 0.39/0.59      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.39/0.59  thf('46', plain,
% 0.39/0.59      (![X0 : $i]:
% 0.39/0.59         ((k3_subset_1 @ X0 @ (k3_subset_1 @ X0 @ k1_xboole_0)) = (k1_xboole_0))),
% 0.39/0.59      inference('sup-', [status(thm)], ['44', '45'])).
% 0.39/0.59  thf('47', plain,
% 0.39/0.59      (![X20 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X20))),
% 0.39/0.59      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.39/0.59  thf('48', plain,
% 0.39/0.59      (![X9 : $i, X10 : $i]:
% 0.39/0.59         (((k3_subset_1 @ X9 @ X10) = (k4_xboole_0 @ X9 @ X10))
% 0.39/0.59          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X9)))),
% 0.39/0.59      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.39/0.59  thf('49', plain,
% 0.39/0.59      (![X0 : $i]:
% 0.39/0.59         ((k3_subset_1 @ X0 @ k1_xboole_0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 0.39/0.59      inference('sup-', [status(thm)], ['47', '48'])).
% 0.39/0.59  thf('50', plain,
% 0.39/0.59      (![X3 : $i, X4 : $i]:
% 0.39/0.59         ((k2_xboole_0 @ X3 @ (k4_xboole_0 @ X4 @ X3))
% 0.39/0.59           = (k2_xboole_0 @ X3 @ X4))),
% 0.39/0.59      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.39/0.59  thf(commutativity_k2_xboole_0, axiom,
% 0.39/0.59    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.39/0.59  thf('51', plain,
% 0.39/0.59      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.39/0.59      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.39/0.59  thf(t1_boole, axiom,
% 0.39/0.59    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.39/0.59  thf('52', plain, (![X2 : $i]: ((k2_xboole_0 @ X2 @ k1_xboole_0) = (X2))),
% 0.39/0.59      inference('cnf', [status(esa)], [t1_boole])).
% 0.39/0.59  thf('53', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.39/0.59      inference('sup+', [status(thm)], ['51', '52'])).
% 0.39/0.59  thf('54', plain,
% 0.39/0.59      (![X0 : $i]:
% 0.39/0.59         ((k2_xboole_0 @ k1_xboole_0 @ X0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 0.39/0.59      inference('sup+', [status(thm)], ['50', '53'])).
% 0.39/0.59  thf('55', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.39/0.59      inference('sup+', [status(thm)], ['51', '52'])).
% 0.39/0.59  thf('56', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.39/0.59      inference('sup+', [status(thm)], ['54', '55'])).
% 0.39/0.59  thf('57', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ k1_xboole_0) = (X0))),
% 0.39/0.59      inference('sup+', [status(thm)], ['49', '56'])).
% 0.39/0.59  thf('58', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k1_xboole_0))),
% 0.39/0.59      inference('demod', [status(thm)], ['46', '57'])).
% 0.39/0.59  thf('59', plain,
% 0.39/0.59      ((((k1_xboole_0) = (k4_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)))
% 0.39/0.59         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.39/0.59                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.39/0.59                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.39/0.59      inference('demod', [status(thm)], ['38', '43', '58'])).
% 0.39/0.59  thf('60', plain,
% 0.39/0.59      (![X3 : $i, X4 : $i]:
% 0.39/0.59         ((k2_xboole_0 @ X3 @ (k4_xboole_0 @ X4 @ X3))
% 0.39/0.59           = (k2_xboole_0 @ X3 @ X4))),
% 0.39/0.59      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.39/0.59  thf('61', plain,
% 0.39/0.59      ((((k2_xboole_0 @ sk_B @ k1_xboole_0)
% 0.39/0.59          = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))
% 0.39/0.59         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.39/0.59                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.39/0.59                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.39/0.59      inference('sup+', [status(thm)], ['59', '60'])).
% 0.39/0.59  thf('62', plain,
% 0.39/0.59      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.39/0.59      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.39/0.59  thf('63', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.39/0.59      inference('sup+', [status(thm)], ['51', '52'])).
% 0.39/0.59  thf('64', plain,
% 0.39/0.59      ((((sk_B) = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))
% 0.39/0.59         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.39/0.59                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.39/0.59                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.39/0.59      inference('demod', [status(thm)], ['61', '62', '63'])).
% 0.39/0.59  thf('65', plain,
% 0.39/0.59      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf(dt_k2_tops_1, axiom,
% 0.39/0.59    (![A:$i,B:$i]:
% 0.39/0.59     ( ( ( l1_pre_topc @ A ) & 
% 0.39/0.59         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.39/0.59       ( m1_subset_1 @
% 0.39/0.59         ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.39/0.59  thf('66', plain,
% 0.39/0.59      (![X26 : $i, X27 : $i]:
% 0.39/0.59         (~ (l1_pre_topc @ X26)
% 0.39/0.59          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ X26)))
% 0.39/0.59          | (m1_subset_1 @ (k2_tops_1 @ X26 @ X27) @ 
% 0.39/0.59             (k1_zfmisc_1 @ (u1_struct_0 @ X26))))),
% 0.39/0.59      inference('cnf', [status(esa)], [dt_k2_tops_1])).
% 0.39/0.59  thf('67', plain,
% 0.39/0.59      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.39/0.59         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.39/0.59        | ~ (l1_pre_topc @ sk_A))),
% 0.39/0.59      inference('sup-', [status(thm)], ['65', '66'])).
% 0.39/0.59  thf('68', plain, ((l1_pre_topc @ sk_A)),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('69', plain,
% 0.39/0.59      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.39/0.59        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.39/0.59      inference('demod', [status(thm)], ['67', '68'])).
% 0.39/0.59  thf('70', plain,
% 0.39/0.59      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf(redefinition_k4_subset_1, axiom,
% 0.39/0.59    (![A:$i,B:$i,C:$i]:
% 0.39/0.59     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 0.39/0.59         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.39/0.59       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 0.39/0.59  thf('71', plain,
% 0.39/0.59      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.39/0.59         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X15))
% 0.39/0.60          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X15))
% 0.39/0.60          | ((k4_subset_1 @ X15 @ X14 @ X16) = (k2_xboole_0 @ X14 @ X16)))),
% 0.39/0.60      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 0.39/0.60  thf('72', plain,
% 0.39/0.60      (![X0 : $i]:
% 0.39/0.60         (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.39/0.60            = (k2_xboole_0 @ sk_B @ X0))
% 0.39/0.60          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.39/0.60      inference('sup-', [status(thm)], ['70', '71'])).
% 0.39/0.60  thf('73', plain,
% 0.39/0.60      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.39/0.60         = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.39/0.60      inference('sup-', [status(thm)], ['69', '72'])).
% 0.39/0.60  thf('74', plain,
% 0.39/0.60      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.39/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.60  thf(t65_tops_1, axiom,
% 0.39/0.60    (![A:$i]:
% 0.39/0.60     ( ( l1_pre_topc @ A ) =>
% 0.39/0.60       ( ![B:$i]:
% 0.39/0.60         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.39/0.60           ( ( k2_pre_topc @ A @ B ) =
% 0.39/0.60             ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.39/0.60  thf('75', plain,
% 0.39/0.60      (![X32 : $i, X33 : $i]:
% 0.39/0.60         (~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (u1_struct_0 @ X33)))
% 0.39/0.60          | ((k2_pre_topc @ X33 @ X32)
% 0.39/0.60              = (k4_subset_1 @ (u1_struct_0 @ X33) @ X32 @ 
% 0.39/0.60                 (k2_tops_1 @ X33 @ X32)))
% 0.39/0.60          | ~ (l1_pre_topc @ X33))),
% 0.39/0.60      inference('cnf', [status(esa)], [t65_tops_1])).
% 0.39/0.60  thf('76', plain,
% 0.39/0.60      ((~ (l1_pre_topc @ sk_A)
% 0.39/0.60        | ((k2_pre_topc @ sk_A @ sk_B)
% 0.39/0.60            = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.39/0.60               (k2_tops_1 @ sk_A @ sk_B))))),
% 0.39/0.60      inference('sup-', [status(thm)], ['74', '75'])).
% 0.39/0.60  thf('77', plain, ((l1_pre_topc @ sk_A)),
% 0.39/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.60  thf('78', plain,
% 0.39/0.60      (((k2_pre_topc @ sk_A @ sk_B)
% 0.39/0.60         = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.39/0.60            (k2_tops_1 @ sk_A @ sk_B)))),
% 0.39/0.60      inference('demod', [status(thm)], ['76', '77'])).
% 0.39/0.60  thf('79', plain,
% 0.39/0.60      (((k2_pre_topc @ sk_A @ sk_B)
% 0.39/0.60         = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.39/0.60      inference('sup+', [status(thm)], ['73', '78'])).
% 0.39/0.60  thf('80', plain,
% 0.39/0.60      ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B)))
% 0.39/0.60         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.39/0.60                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.39/0.60                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.39/0.60      inference('sup+', [status(thm)], ['64', '79'])).
% 0.39/0.60  thf('81', plain,
% 0.39/0.60      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.39/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.60  thf(fc1_tops_1, axiom,
% 0.39/0.60    (![A:$i,B:$i]:
% 0.39/0.60     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 0.39/0.60         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.39/0.60       ( v4_pre_topc @ ( k2_pre_topc @ A @ B ) @ A ) ))).
% 0.39/0.60  thf('82', plain,
% 0.39/0.60      (![X28 : $i, X29 : $i]:
% 0.39/0.60         (~ (l1_pre_topc @ X28)
% 0.39/0.60          | ~ (v2_pre_topc @ X28)
% 0.39/0.60          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 0.39/0.60          | (v4_pre_topc @ (k2_pre_topc @ X28 @ X29) @ X28))),
% 0.39/0.60      inference('cnf', [status(esa)], [fc1_tops_1])).
% 0.39/0.60  thf('83', plain,
% 0.39/0.60      (((v4_pre_topc @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A)
% 0.39/0.60        | ~ (v2_pre_topc @ sk_A)
% 0.39/0.60        | ~ (l1_pre_topc @ sk_A))),
% 0.39/0.60      inference('sup-', [status(thm)], ['81', '82'])).
% 0.39/0.60  thf('84', plain, ((v2_pre_topc @ sk_A)),
% 0.39/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.60  thf('85', plain, ((l1_pre_topc @ sk_A)),
% 0.39/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.60  thf('86', plain, ((v4_pre_topc @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A)),
% 0.39/0.60      inference('demod', [status(thm)], ['83', '84', '85'])).
% 0.39/0.60  thf('87', plain,
% 0.39/0.60      (((v4_pre_topc @ sk_B @ sk_A))
% 0.39/0.60         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.39/0.60                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.39/0.60                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.39/0.60      inference('sup+', [status(thm)], ['80', '86'])).
% 0.39/0.60  thf('88', plain,
% 0.39/0.60      ((~ (v4_pre_topc @ sk_B @ sk_A)) <= (~ ((v4_pre_topc @ sk_B @ sk_A)))),
% 0.39/0.60      inference('split', [status(esa)], ['0'])).
% 0.39/0.60  thf('89', plain,
% 0.39/0.60      (~
% 0.39/0.60       (((k2_tops_1 @ sk_A @ sk_B)
% 0.39/0.60          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.39/0.60             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 0.39/0.60       ((v4_pre_topc @ sk_B @ sk_A))),
% 0.39/0.60      inference('sup-', [status(thm)], ['87', '88'])).
% 0.39/0.60  thf('90', plain, ($false),
% 0.39/0.60      inference('sat_resolution*', [status(thm)], ['1', '24', '25', '89'])).
% 0.39/0.60  
% 0.39/0.60  % SZS output end Refutation
% 0.39/0.60  
% 0.39/0.60  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
