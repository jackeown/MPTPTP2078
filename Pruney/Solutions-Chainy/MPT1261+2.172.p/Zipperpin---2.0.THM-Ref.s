%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.7KGg6A3tF8

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:04:04 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 181 expanded)
%              Number of leaves         :   27 (  61 expanded)
%              Depth                    :   13
%              Number of atoms          : 1018 (2569 expanded)
%              Number of equality atoms :   72 ( 150 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

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
    ! [X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ~ ( v4_pre_topc @ X14 @ X15 )
      | ( ( k2_pre_topc @ X15 @ X14 )
        = X14 )
      | ~ ( l1_pre_topc @ X15 ) ) ),
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
    ! [X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ( ( k2_tops_1 @ X21 @ X20 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X21 ) @ ( k2_pre_topc @ X21 @ X20 ) @ ( k1_tops_1 @ X21 @ X20 ) ) )
      | ~ ( l1_pre_topc @ X21 ) ) ),
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
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) )
      | ( ( k7_subset_1 @ X10 @ X9 @ X11 )
        = ( k4_xboole_0 @ X9 @ X11 ) ) ) ),
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
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t74_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k1_tops_1 @ A @ B )
            = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('27',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) )
      | ( ( k1_tops_1 @ X25 @ X24 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X25 ) @ X24 @ ( k2_tops_1 @ X25 @ X24 ) ) )
      | ~ ( l1_pre_topc @ X25 ) ) ),
    inference(cnf,[status(esa)],[t74_tops_1])).

thf('28',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('31',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['28','29','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('33',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['2'])).

thf('34',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('35',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ ( k4_xboole_0 @ X2 @ X3 ) )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('36',plain,
    ( ( ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k3_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('37',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = ( k3_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['31','36'])).

thf('38',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ ( k4_xboole_0 @ X2 @ X3 ) )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('39',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ ( k4_xboole_0 @ X2 @ X3 ) )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('41',plain,
    ( ( ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
      = ( k3_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['37','40'])).

thf('42',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('43',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('44',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k3_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['41','42','43'])).

thf(t22_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = A ) )).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = X0 ) ),
    inference(cnf,[status(esa)],[t22_xboole_1])).

thf('46',plain,
    ( ( ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('47',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t65_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_pre_topc @ A @ B )
            = ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('48',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ( ( k2_pre_topc @ X23 @ X22 )
        = ( k4_subset_1 @ ( u1_struct_0 @ X23 ) @ X22 @ ( k2_tops_1 @ X23 @ X22 ) ) )
      | ~ ( l1_pre_topc @ X23 ) ) ),
    inference(cnf,[status(esa)],[t65_tops_1])).

thf('49',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
      = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('52',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( l1_pre_topc @ X16 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ( m1_subset_1 @ ( k2_tops_1 @ X16 @ X17 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_1])).

thf('53',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('57',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X7 ) )
      | ( ( k4_subset_1 @ X7 @ X6 @ X8 )
        = ( k2_xboole_0 @ X6 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
        = ( k2_xboole_0 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,
    ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['55','58'])).

thf('60',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['49','50','59'])).

thf('61',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['46','60'])).

thf('62',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc1_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v4_pre_topc @ ( k2_pre_topc @ A @ B ) @ A ) ) )).

thf('63',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( l1_pre_topc @ X18 )
      | ~ ( v2_pre_topc @ X18 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ( v4_pre_topc @ ( k2_pre_topc @ X18 @ X19 ) @ X18 ) ) ),
    inference(cnf,[status(esa)],[fc1_tops_1])).

thf('64',plain,
    ( ( v4_pre_topc @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    v4_pre_topc @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['64','65','66'])).

thf('68',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['61','67'])).

thf('69',plain,
    ( ~ ( v4_pre_topc @ sk_B @ sk_A )
   <= ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('70',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','24','25','70'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.7KGg6A3tF8
% 0.12/0.34  % Computer   : n003.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 12:44:27 EST 2020
% 0.12/0.35  % CPUTime    : 
% 0.12/0.35  % Running portfolio for 600 s
% 0.12/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.35  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.21/0.50  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.50  % Solved by: fo/fo7.sh
% 0.21/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.50  % done 90 iterations in 0.045s
% 0.21/0.50  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.50  % SZS output start Refutation
% 0.21/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.50  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.50  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 0.21/0.50  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 0.21/0.50  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.21/0.50  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.21/0.50  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 0.21/0.50  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.21/0.50  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.50  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.21/0.50  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.21/0.50  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.21/0.50  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.50  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.21/0.50  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.21/0.50  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.50  thf(t77_tops_1, conjecture,
% 0.21/0.50    (![A:$i]:
% 0.21/0.50     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.50       ( ![B:$i]:
% 0.21/0.50         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.50           ( ( v4_pre_topc @ B @ A ) <=>
% 0.21/0.50             ( ( k2_tops_1 @ A @ B ) =
% 0.21/0.50               ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ))).
% 0.21/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.50    (~( ![A:$i]:
% 0.21/0.50        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.50          ( ![B:$i]:
% 0.21/0.50            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.50              ( ( v4_pre_topc @ B @ A ) <=>
% 0.21/0.50                ( ( k2_tops_1 @ A @ B ) =
% 0.21/0.50                  ( k7_subset_1 @
% 0.21/0.50                    ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ) )),
% 0.21/0.50    inference('cnf.neg', [status(esa)], [t77_tops_1])).
% 0.21/0.50  thf('0', plain,
% 0.21/0.50      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.21/0.50          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.21/0.50              (k1_tops_1 @ sk_A @ sk_B)))
% 0.21/0.50        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('1', plain,
% 0.21/0.50      (~
% 0.21/0.50       (((k2_tops_1 @ sk_A @ sk_B)
% 0.21/0.50          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.21/0.50             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 0.21/0.50       ~ ((v4_pre_topc @ sk_B @ sk_A))),
% 0.21/0.50      inference('split', [status(esa)], ['0'])).
% 0.21/0.50  thf('2', plain,
% 0.21/0.50      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.21/0.50          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.21/0.50             (k1_tops_1 @ sk_A @ sk_B)))
% 0.21/0.50        | (v4_pre_topc @ sk_B @ sk_A))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('3', plain,
% 0.21/0.50      (((v4_pre_topc @ sk_B @ sk_A)) <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.21/0.50      inference('split', [status(esa)], ['2'])).
% 0.21/0.50  thf('4', plain,
% 0.21/0.50      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf(t52_pre_topc, axiom,
% 0.21/0.50    (![A:$i]:
% 0.21/0.50     ( ( l1_pre_topc @ A ) =>
% 0.21/0.50       ( ![B:$i]:
% 0.21/0.50         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.50           ( ( ( v4_pre_topc @ B @ A ) => ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) & 
% 0.21/0.50             ( ( ( v2_pre_topc @ A ) & ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) =>
% 0.21/0.50               ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 0.21/0.50  thf('5', plain,
% 0.21/0.50      (![X14 : $i, X15 : $i]:
% 0.21/0.50         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.21/0.50          | ~ (v4_pre_topc @ X14 @ X15)
% 0.21/0.50          | ((k2_pre_topc @ X15 @ X14) = (X14))
% 0.21/0.50          | ~ (l1_pre_topc @ X15))),
% 0.21/0.50      inference('cnf', [status(esa)], [t52_pre_topc])).
% 0.21/0.50  thf('6', plain,
% 0.21/0.50      ((~ (l1_pre_topc @ sk_A)
% 0.21/0.50        | ((k2_pre_topc @ sk_A @ sk_B) = (sk_B))
% 0.21/0.50        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.21/0.50      inference('sup-', [status(thm)], ['4', '5'])).
% 0.21/0.50  thf('7', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('8', plain,
% 0.21/0.50      ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B)) | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.21/0.50      inference('demod', [status(thm)], ['6', '7'])).
% 0.21/0.50  thf('9', plain,
% 0.21/0.50      ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B)))
% 0.21/0.50         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['3', '8'])).
% 0.21/0.50  thf('10', plain,
% 0.21/0.50      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf(l78_tops_1, axiom,
% 0.21/0.50    (![A:$i]:
% 0.21/0.50     ( ( l1_pre_topc @ A ) =>
% 0.21/0.50       ( ![B:$i]:
% 0.21/0.50         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.50           ( ( k2_tops_1 @ A @ B ) =
% 0.21/0.50             ( k7_subset_1 @
% 0.21/0.50               ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 0.21/0.50               ( k1_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.21/0.50  thf('11', plain,
% 0.21/0.50      (![X20 : $i, X21 : $i]:
% 0.21/0.50         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.21/0.50          | ((k2_tops_1 @ X21 @ X20)
% 0.21/0.50              = (k7_subset_1 @ (u1_struct_0 @ X21) @ 
% 0.21/0.50                 (k2_pre_topc @ X21 @ X20) @ (k1_tops_1 @ X21 @ X20)))
% 0.21/0.50          | ~ (l1_pre_topc @ X21))),
% 0.21/0.50      inference('cnf', [status(esa)], [l78_tops_1])).
% 0.21/0.50  thf('12', plain,
% 0.21/0.50      ((~ (l1_pre_topc @ sk_A)
% 0.21/0.50        | ((k2_tops_1 @ sk_A @ sk_B)
% 0.21/0.50            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.50               (k2_pre_topc @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ sk_B))))),
% 0.21/0.50      inference('sup-', [status(thm)], ['10', '11'])).
% 0.21/0.50  thf('13', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('14', plain,
% 0.21/0.50      (((k2_tops_1 @ sk_A @ sk_B)
% 0.21/0.50         = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.21/0.50            (k1_tops_1 @ sk_A @ sk_B)))),
% 0.21/0.50      inference('demod', [status(thm)], ['12', '13'])).
% 0.21/0.50  thf('15', plain,
% 0.21/0.50      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.21/0.50          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.21/0.50             (k1_tops_1 @ sk_A @ sk_B))))
% 0.21/0.50         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.21/0.50      inference('sup+', [status(thm)], ['9', '14'])).
% 0.21/0.50  thf('16', plain,
% 0.21/0.50      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf(redefinition_k7_subset_1, axiom,
% 0.21/0.50    (![A:$i,B:$i,C:$i]:
% 0.21/0.50     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.50       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 0.21/0.50  thf('17', plain,
% 0.21/0.50      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.21/0.50         (~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10))
% 0.21/0.50          | ((k7_subset_1 @ X10 @ X9 @ X11) = (k4_xboole_0 @ X9 @ X11)))),
% 0.21/0.50      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 0.21/0.50  thf('18', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.21/0.50           = (k4_xboole_0 @ sk_B @ X0))),
% 0.21/0.50      inference('sup-', [status(thm)], ['16', '17'])).
% 0.21/0.50  thf('19', plain,
% 0.21/0.50      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.21/0.50          = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.21/0.50         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.21/0.50      inference('demod', [status(thm)], ['15', '18'])).
% 0.21/0.50  thf('20', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.21/0.50           = (k4_xboole_0 @ sk_B @ X0))),
% 0.21/0.50      inference('sup-', [status(thm)], ['16', '17'])).
% 0.21/0.50  thf('21', plain,
% 0.21/0.50      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.21/0.50          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.21/0.50              (k1_tops_1 @ sk_A @ sk_B))))
% 0.21/0.50         <= (~
% 0.21/0.50             (((k2_tops_1 @ sk_A @ sk_B)
% 0.21/0.50                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.21/0.50                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.21/0.50      inference('split', [status(esa)], ['0'])).
% 0.21/0.50  thf('22', plain,
% 0.21/0.50      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.21/0.50          != (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.21/0.50         <= (~
% 0.21/0.50             (((k2_tops_1 @ sk_A @ sk_B)
% 0.21/0.50                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.21/0.50                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.21/0.50      inference('sup-', [status(thm)], ['20', '21'])).
% 0.21/0.50  thf('23', plain,
% 0.21/0.50      ((((k2_tops_1 @ sk_A @ sk_B) != (k2_tops_1 @ sk_A @ sk_B)))
% 0.21/0.50         <= (~
% 0.21/0.50             (((k2_tops_1 @ sk_A @ sk_B)
% 0.21/0.50                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.21/0.50                   (k1_tops_1 @ sk_A @ sk_B)))) & 
% 0.21/0.50             ((v4_pre_topc @ sk_B @ sk_A)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['19', '22'])).
% 0.21/0.50  thf('24', plain,
% 0.21/0.50      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.21/0.50          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.21/0.50             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 0.21/0.50       ~ ((v4_pre_topc @ sk_B @ sk_A))),
% 0.21/0.50      inference('simplify', [status(thm)], ['23'])).
% 0.21/0.50  thf('25', plain,
% 0.21/0.50      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.21/0.50          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.21/0.50             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 0.21/0.50       ((v4_pre_topc @ sk_B @ sk_A))),
% 0.21/0.50      inference('split', [status(esa)], ['2'])).
% 0.21/0.50  thf('26', plain,
% 0.21/0.50      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf(t74_tops_1, axiom,
% 0.21/0.50    (![A:$i]:
% 0.21/0.50     ( ( l1_pre_topc @ A ) =>
% 0.21/0.50       ( ![B:$i]:
% 0.21/0.50         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.50           ( ( k1_tops_1 @ A @ B ) =
% 0.21/0.50             ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.21/0.50  thf('27', plain,
% 0.21/0.50      (![X24 : $i, X25 : $i]:
% 0.21/0.50         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 0.21/0.50          | ((k1_tops_1 @ X25 @ X24)
% 0.21/0.50              = (k7_subset_1 @ (u1_struct_0 @ X25) @ X24 @ 
% 0.21/0.50                 (k2_tops_1 @ X25 @ X24)))
% 0.21/0.50          | ~ (l1_pre_topc @ X25))),
% 0.21/0.50      inference('cnf', [status(esa)], [t74_tops_1])).
% 0.21/0.50  thf('28', plain,
% 0.21/0.50      ((~ (l1_pre_topc @ sk_A)
% 0.21/0.50        | ((k1_tops_1 @ sk_A @ sk_B)
% 0.21/0.50            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.21/0.50               (k2_tops_1 @ sk_A @ sk_B))))),
% 0.21/0.50      inference('sup-', [status(thm)], ['26', '27'])).
% 0.21/0.50  thf('29', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('30', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.21/0.50           = (k4_xboole_0 @ sk_B @ X0))),
% 0.21/0.50      inference('sup-', [status(thm)], ['16', '17'])).
% 0.21/0.50  thf('31', plain,
% 0.21/0.50      (((k1_tops_1 @ sk_A @ sk_B)
% 0.21/0.50         = (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.21/0.50      inference('demod', [status(thm)], ['28', '29', '30'])).
% 0.21/0.50  thf('32', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.21/0.50           = (k4_xboole_0 @ sk_B @ X0))),
% 0.21/0.50      inference('sup-', [status(thm)], ['16', '17'])).
% 0.21/0.50  thf('33', plain,
% 0.21/0.50      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.21/0.50          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.21/0.50             (k1_tops_1 @ sk_A @ sk_B))))
% 0.21/0.50         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.21/0.50                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.21/0.50                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.21/0.50      inference('split', [status(esa)], ['2'])).
% 0.21/0.50  thf('34', plain,
% 0.21/0.50      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.21/0.50          = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.21/0.50         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.21/0.50                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.21/0.50                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.21/0.50      inference('sup+', [status(thm)], ['32', '33'])).
% 0.21/0.50  thf(t48_xboole_1, axiom,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.21/0.50  thf('35', plain,
% 0.21/0.50      (![X2 : $i, X3 : $i]:
% 0.21/0.50         ((k4_xboole_0 @ X2 @ (k4_xboole_0 @ X2 @ X3))
% 0.21/0.50           = (k3_xboole_0 @ X2 @ X3))),
% 0.21/0.50      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.21/0.50  thf('36', plain,
% 0.21/0.50      ((((k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.21/0.50          = (k3_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.21/0.50         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.21/0.50                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.21/0.50                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.21/0.50      inference('sup+', [status(thm)], ['34', '35'])).
% 0.21/0.50  thf('37', plain,
% 0.21/0.50      ((((k1_tops_1 @ sk_A @ sk_B)
% 0.21/0.50          = (k3_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.21/0.50         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.21/0.50                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.21/0.50                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.21/0.50      inference('sup+', [status(thm)], ['31', '36'])).
% 0.21/0.50  thf('38', plain,
% 0.21/0.50      (![X2 : $i, X3 : $i]:
% 0.21/0.50         ((k4_xboole_0 @ X2 @ (k4_xboole_0 @ X2 @ X3))
% 0.21/0.50           = (k3_xboole_0 @ X2 @ X3))),
% 0.21/0.50      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.21/0.50  thf('39', plain,
% 0.21/0.50      (![X2 : $i, X3 : $i]:
% 0.21/0.50         ((k4_xboole_0 @ X2 @ (k4_xboole_0 @ X2 @ X3))
% 0.21/0.50           = (k3_xboole_0 @ X2 @ X3))),
% 0.21/0.50      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.21/0.50  thf('40', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]:
% 0.21/0.50         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 0.21/0.50           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.21/0.50      inference('sup+', [status(thm)], ['38', '39'])).
% 0.21/0.50  thf('41', plain,
% 0.21/0.50      ((((k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 0.21/0.50          = (k3_xboole_0 @ sk_B @ 
% 0.21/0.50             (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))))
% 0.21/0.50         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.21/0.50                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.21/0.50                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.21/0.50      inference('sup+', [status(thm)], ['37', '40'])).
% 0.21/0.50  thf('42', plain,
% 0.21/0.50      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.21/0.50          = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.21/0.50         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.21/0.50                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.21/0.50                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.21/0.50      inference('sup+', [status(thm)], ['32', '33'])).
% 0.21/0.50  thf('43', plain,
% 0.21/0.50      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.21/0.50          = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.21/0.50         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.21/0.50                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.21/0.50                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.21/0.50      inference('sup+', [status(thm)], ['32', '33'])).
% 0.21/0.50  thf('44', plain,
% 0.21/0.50      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.21/0.50          = (k3_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))
% 0.21/0.50         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.21/0.50                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.21/0.50                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.21/0.50      inference('demod', [status(thm)], ['41', '42', '43'])).
% 0.21/0.50  thf(t22_xboole_1, axiom,
% 0.21/0.50    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( A ) ))).
% 0.21/0.50  thf('45', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]:
% 0.21/0.50         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)) = (X0))),
% 0.21/0.50      inference('cnf', [status(esa)], [t22_xboole_1])).
% 0.21/0.50  thf('46', plain,
% 0.21/0.50      ((((k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)) = (sk_B)))
% 0.21/0.50         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.21/0.50                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.21/0.50                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.21/0.50      inference('sup+', [status(thm)], ['44', '45'])).
% 0.21/0.50  thf('47', plain,
% 0.21/0.50      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf(t65_tops_1, axiom,
% 0.21/0.50    (![A:$i]:
% 0.21/0.50     ( ( l1_pre_topc @ A ) =>
% 0.21/0.50       ( ![B:$i]:
% 0.21/0.50         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.50           ( ( k2_pre_topc @ A @ B ) =
% 0.21/0.50             ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.21/0.50  thf('48', plain,
% 0.21/0.50      (![X22 : $i, X23 : $i]:
% 0.21/0.50         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 0.21/0.50          | ((k2_pre_topc @ X23 @ X22)
% 0.21/0.50              = (k4_subset_1 @ (u1_struct_0 @ X23) @ X22 @ 
% 0.21/0.50                 (k2_tops_1 @ X23 @ X22)))
% 0.21/0.50          | ~ (l1_pre_topc @ X23))),
% 0.21/0.50      inference('cnf', [status(esa)], [t65_tops_1])).
% 0.21/0.50  thf('49', plain,
% 0.21/0.50      ((~ (l1_pre_topc @ sk_A)
% 0.21/0.50        | ((k2_pre_topc @ sk_A @ sk_B)
% 0.21/0.50            = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.21/0.50               (k2_tops_1 @ sk_A @ sk_B))))),
% 0.21/0.50      inference('sup-', [status(thm)], ['47', '48'])).
% 0.21/0.50  thf('50', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('51', plain,
% 0.21/0.50      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf(dt_k2_tops_1, axiom,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( ( l1_pre_topc @ A ) & 
% 0.21/0.50         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.21/0.50       ( m1_subset_1 @
% 0.21/0.50         ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.21/0.50  thf('52', plain,
% 0.21/0.50      (![X16 : $i, X17 : $i]:
% 0.21/0.50         (~ (l1_pre_topc @ X16)
% 0.21/0.50          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.21/0.50          | (m1_subset_1 @ (k2_tops_1 @ X16 @ X17) @ 
% 0.21/0.50             (k1_zfmisc_1 @ (u1_struct_0 @ X16))))),
% 0.21/0.50      inference('cnf', [status(esa)], [dt_k2_tops_1])).
% 0.21/0.50  thf('53', plain,
% 0.21/0.50      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.21/0.50         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.50        | ~ (l1_pre_topc @ sk_A))),
% 0.21/0.50      inference('sup-', [status(thm)], ['51', '52'])).
% 0.21/0.50  thf('54', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('55', plain,
% 0.21/0.50      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.21/0.50        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.50      inference('demod', [status(thm)], ['53', '54'])).
% 0.21/0.50  thf('56', plain,
% 0.21/0.50      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf(redefinition_k4_subset_1, axiom,
% 0.21/0.50    (![A:$i,B:$i,C:$i]:
% 0.21/0.50     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 0.21/0.50         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.21/0.50       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 0.21/0.50  thf('57', plain,
% 0.21/0.50      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.21/0.50         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7))
% 0.21/0.50          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X7))
% 0.21/0.50          | ((k4_subset_1 @ X7 @ X6 @ X8) = (k2_xboole_0 @ X6 @ X8)))),
% 0.21/0.50      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 0.21/0.50  thf('58', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.21/0.50            = (k2_xboole_0 @ sk_B @ X0))
% 0.21/0.50          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.21/0.50      inference('sup-', [status(thm)], ['56', '57'])).
% 0.21/0.50  thf('59', plain,
% 0.21/0.50      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.21/0.50         = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['55', '58'])).
% 0.21/0.50  thf('60', plain,
% 0.21/0.50      (((k2_pre_topc @ sk_A @ sk_B)
% 0.21/0.50         = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.21/0.50      inference('demod', [status(thm)], ['49', '50', '59'])).
% 0.21/0.50  thf('61', plain,
% 0.21/0.50      ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B)))
% 0.21/0.50         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.21/0.50                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.21/0.50                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.21/0.50      inference('sup+', [status(thm)], ['46', '60'])).
% 0.21/0.50  thf('62', plain,
% 0.21/0.50      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf(fc1_tops_1, axiom,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 0.21/0.50         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.21/0.50       ( v4_pre_topc @ ( k2_pre_topc @ A @ B ) @ A ) ))).
% 0.21/0.50  thf('63', plain,
% 0.21/0.50      (![X18 : $i, X19 : $i]:
% 0.21/0.50         (~ (l1_pre_topc @ X18)
% 0.21/0.50          | ~ (v2_pre_topc @ X18)
% 0.21/0.50          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.21/0.50          | (v4_pre_topc @ (k2_pre_topc @ X18 @ X19) @ X18))),
% 0.21/0.50      inference('cnf', [status(esa)], [fc1_tops_1])).
% 0.21/0.50  thf('64', plain,
% 0.21/0.50      (((v4_pre_topc @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A)
% 0.21/0.50        | ~ (v2_pre_topc @ sk_A)
% 0.21/0.50        | ~ (l1_pre_topc @ sk_A))),
% 0.21/0.50      inference('sup-', [status(thm)], ['62', '63'])).
% 0.21/0.50  thf('65', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('66', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('67', plain, ((v4_pre_topc @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A)),
% 0.21/0.50      inference('demod', [status(thm)], ['64', '65', '66'])).
% 0.21/0.50  thf('68', plain,
% 0.21/0.50      (((v4_pre_topc @ sk_B @ sk_A))
% 0.21/0.50         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.21/0.50                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.21/0.50                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.21/0.50      inference('sup+', [status(thm)], ['61', '67'])).
% 0.21/0.50  thf('69', plain,
% 0.21/0.50      ((~ (v4_pre_topc @ sk_B @ sk_A)) <= (~ ((v4_pre_topc @ sk_B @ sk_A)))),
% 0.21/0.50      inference('split', [status(esa)], ['0'])).
% 0.21/0.50  thf('70', plain,
% 0.21/0.50      (~
% 0.21/0.50       (((k2_tops_1 @ sk_A @ sk_B)
% 0.21/0.50          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.21/0.50             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 0.21/0.50       ((v4_pre_topc @ sk_B @ sk_A))),
% 0.21/0.50      inference('sup-', [status(thm)], ['68', '69'])).
% 0.21/0.50  thf('71', plain, ($false),
% 0.21/0.50      inference('sat_resolution*', [status(thm)], ['1', '24', '25', '70'])).
% 0.21/0.50  
% 0.21/0.50  % SZS output end Refutation
% 0.21/0.50  
% 0.21/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
