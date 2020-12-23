%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.4n1CUrUDJZ

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:04:15 EST 2020

% Result     : Theorem 0.56s
% Output     : Refutation 0.60s
% Verified   : 
% Statistics : Number of formulae       :  139 ( 988 expanded)
%              Number of leaves         :   27 ( 299 expanded)
%              Depth                    :   22
%              Number of atoms          : 1160 (9346 expanded)
%              Number of equality atoms :   82 ( 634 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(v2_tops_1_type,type,(
    v2_tops_1: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_tops_1_type,type,(
    v1_tops_1: $i > $i > $o )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(t84_tops_1,conjecture,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v2_tops_1 @ B @ A )
          <=> ( ( k1_tops_1 @ A @ B )
              = k1_xboole_0 ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_pre_topc @ A )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( ( v2_tops_1 @ B @ A )
            <=> ( ( k1_tops_1 @ A @ B )
                = k1_xboole_0 ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t84_tops_1])).

thf('0',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
     != k1_xboole_0 )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
     != k1_xboole_0 )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( v2_tops_1 @ sk_B @ sk_A )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d4_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v2_tops_1 @ B @ A )
          <=> ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) )).

thf('5',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ~ ( v2_tops_1 @ X19 @ X20 )
      | ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ X20 ) @ X19 ) @ X20 )
      | ~ ( l1_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_1])).

thf('6',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('9',plain,(
    ! [X1: $i,X2: $i] :
      ( ( ( k3_subset_1 @ X1 @ X2 )
        = ( k4_xboole_0 @ X1 @ X2 ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('10',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('11',plain,(
    ! [X11: $i] :
      ( ( ( k2_struct_0 @ X11 )
        = ( u1_struct_0 @ X11 ) )
      | ~ ( l1_struct_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('12',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('13',plain,
    ( ( ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B )
      = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('15',plain,(
    ! [X14: $i] :
      ( ( l1_struct_0 @ X14 )
      | ~ ( l1_pre_topc @ X14 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('16',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,
    ( ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['13','16'])).

thf('18',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['10','17'])).

thf('19',plain,(
    ! [X11: $i] :
      ( ( ( k2_struct_0 @ X11 )
        = ( u1_struct_0 @ X11 ) )
      | ~ ( l1_struct_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('20',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['14','15'])).

thf('23',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X1: $i,X2: $i] :
      ( ( ( k3_subset_1 @ X1 @ X2 )
        = ( k4_xboole_0 @ X1 @ X2 ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('25',plain,
    ( ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['18','25'])).

thf('27',plain,
    ( ( v1_tops_1 @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['6','7','26'])).

thf('28',plain,
    ( ( v1_tops_1 @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['3','27'])).

thf('29',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('30',plain,(
    ! [X3: $i,X4: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X3 @ X4 ) @ ( k1_zfmisc_1 @ X3 ) )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('31',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['18','25'])).

thf('33',plain,(
    m1_subset_1 @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf(d3_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v1_tops_1 @ B @ A )
          <=> ( ( k2_pre_topc @ A @ B )
              = ( k2_struct_0 @ A ) ) ) ) ) )).

thf('34',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( v1_tops_1 @ X17 @ X18 )
      | ( ( k2_pre_topc @ X18 @ X17 )
        = ( k2_struct_0 @ X18 ) )
      | ~ ( l1_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[d3_tops_1])).

thf('35',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      = ( k2_struct_0 @ sk_A ) )
    | ~ ( v1_tops_1 @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      = ( k2_struct_0 @ sk_A ) )
    | ~ ( v1_tops_1 @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      = ( k2_struct_0 @ sk_A ) )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['28','37'])).

thf('39',plain,(
    m1_subset_1 @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf(dt_k2_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('40',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( l1_pre_topc @ X12 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X12 @ X13 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('41',plain,
    ( ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,
    ( ( m1_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['38','43'])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('45',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k3_subset_1 @ X6 @ ( k3_subset_1 @ X6 @ X5 ) )
        = X5 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('46',plain,
    ( ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) ) )
      = ( k2_struct_0 @ sk_A ) )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,
    ( ( m1_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['38','43'])).

thf('48',plain,(
    ! [X1: $i,X2: $i] :
      ( ( ( k3_subset_1 @ X1 @ X2 )
        = ( k4_xboole_0 @ X1 @ X2 ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('49',plain,
    ( ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) )
      = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) ) )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X11: $i] :
      ( ( ( k2_struct_0 @ X11 )
        = ( u1_struct_0 @ X11 ) )
      | ~ ( l1_struct_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('51',plain,
    ( ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) )
      = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) ) )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('52',plain,
    ( ( ( ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) )
        = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) ) )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('53',plain,(
    ! [X7: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('54',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k3_subset_1 @ X6 @ ( k3_subset_1 @ X6 @ X5 ) )
        = X5 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ ( k3_subset_1 @ X0 @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X7: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('57',plain,(
    ! [X1: $i,X2: $i] :
      ( ( ( k3_subset_1 @ X1 @ X2 )
        = ( k4_xboole_0 @ X1 @ X2 ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('59',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['55','60'])).

thf('62',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['14','15'])).

thf('63',plain,
    ( ( k1_xboole_0
      = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) ) )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['52','61','62'])).

thf('64',plain,
    ( ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) )
      = k1_xboole_0 )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['49','63'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('66',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = ( k2_struct_0 @ sk_A ) )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['46','64','65'])).

thf('67',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d1_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k1_tops_1 @ A @ B )
            = ( k3_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) )).

thf('68',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ( ( k1_tops_1 @ X16 @ X15 )
        = ( k3_subset_1 @ ( u1_struct_0 @ X16 ) @ ( k2_pre_topc @ X16 @ ( k3_subset_1 @ ( u1_struct_0 @ X16 ) @ X15 ) ) ) )
      | ~ ( l1_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[d1_tops_1])).

thf('69',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
      = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['18','25'])).

thf('72',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['69','70','71'])).

thf('73',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['66','72'])).

thf('74',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      = ( k2_struct_0 @ sk_A ) )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['28','37'])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['55','60'])).

thf('76',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['73','74','75'])).

thf('77',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
     != k1_xboole_0 )
   <= ( ( k1_tops_1 @ sk_A @ sk_B )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('78',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( ( k1_tops_1 @ sk_A @ sk_B )
       != k1_xboole_0 )
      & ( v2_tops_1 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['78'])).

thf('80',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('81',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
   <= ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['2'])).

thf('82',plain,(
    ! [X11: $i] :
      ( ( ( k2_struct_0 @ X11 )
        = ( u1_struct_0 @ X11 ) )
      | ~ ( l1_struct_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('83',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('84',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k3_subset_1 @ X6 @ ( k3_subset_1 @ X6 @ X5 ) )
        = X5 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('85',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) )
    = ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['69','70','71'])).

thf('87',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['85','86'])).

thf('88',plain,
    ( ( ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B ) )
      = ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['82','87'])).

thf('89',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['14','15'])).

thf('90',plain,
    ( ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['88','89'])).

thf('91',plain,
    ( ( ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ k1_xboole_0 )
      = ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
   <= ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['81','90'])).

thf('92',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('93',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
   <= ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['91','92'])).

thf('94',plain,(
    m1_subset_1 @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('95',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ( ( k2_pre_topc @ X18 @ X17 )
       != ( k2_struct_0 @ X18 ) )
      | ( v1_tops_1 @ X17 @ X18 )
      | ~ ( l1_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[d3_tops_1])).

thf('96',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v1_tops_1 @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,
    ( ( v1_tops_1 @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['96','97'])).

thf('99',plain,
    ( ( ( ( k2_struct_0 @ sk_A )
       != ( k2_struct_0 @ sk_A ) )
      | ( v1_tops_1 @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) )
   <= ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['93','98'])).

thf('100',plain,
    ( ( v1_tops_1 @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
   <= ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['99'])).

thf('101',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ~ ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ X20 ) @ X19 ) @ X20 )
      | ( v2_tops_1 @ X19 @ X20 )
      | ~ ( l1_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_1])).

thf('103',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v2_tops_1 @ sk_B @ sk_A )
    | ~ ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['18','25'])).

thf('106',plain,
    ( ( v2_tops_1 @ sk_B @ sk_A )
    | ~ ( v1_tops_1 @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['103','104','105'])).

thf('107',plain,
    ( ( v2_tops_1 @ sk_B @ sk_A )
   <= ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['100','106'])).

thf('108',plain,
    ( ~ ( v2_tops_1 @ sk_B @ sk_A )
   <= ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('109',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
     != k1_xboole_0 )
    | ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['107','108'])).

thf('110',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','79','80','109'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.4n1CUrUDJZ
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:08:29 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.34  % Running in FO mode
% 0.56/0.76  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.56/0.76  % Solved by: fo/fo7.sh
% 0.56/0.76  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.56/0.76  % done 800 iterations in 0.309s
% 0.56/0.76  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.56/0.76  % SZS output start Refutation
% 0.56/0.76  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.56/0.76  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.56/0.76  thf(v2_tops_1_type, type, v2_tops_1: $i > $i > $o).
% 0.56/0.76  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.56/0.76  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.56/0.76  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.56/0.76  thf(sk_B_type, type, sk_B: $i).
% 0.56/0.76  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.56/0.76  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.56/0.76  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.56/0.76  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.56/0.76  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.56/0.76  thf(sk_A_type, type, sk_A: $i).
% 0.56/0.76  thf(v1_tops_1_type, type, v1_tops_1: $i > $i > $o).
% 0.56/0.76  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.56/0.76  thf(t84_tops_1, conjecture,
% 0.56/0.76    (![A:$i]:
% 0.56/0.76     ( ( l1_pre_topc @ A ) =>
% 0.56/0.76       ( ![B:$i]:
% 0.56/0.76         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.56/0.76           ( ( v2_tops_1 @ B @ A ) <=>
% 0.56/0.76             ( ( k1_tops_1 @ A @ B ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 0.56/0.76  thf(zf_stmt_0, negated_conjecture,
% 0.56/0.76    (~( ![A:$i]:
% 0.56/0.76        ( ( l1_pre_topc @ A ) =>
% 0.56/0.76          ( ![B:$i]:
% 0.56/0.76            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.56/0.76              ( ( v2_tops_1 @ B @ A ) <=>
% 0.56/0.76                ( ( k1_tops_1 @ A @ B ) = ( k1_xboole_0 ) ) ) ) ) ) )),
% 0.56/0.76    inference('cnf.neg', [status(esa)], [t84_tops_1])).
% 0.56/0.76  thf('0', plain,
% 0.56/0.76      ((((k1_tops_1 @ sk_A @ sk_B) != (k1_xboole_0))
% 0.56/0.76        | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 0.56/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.56/0.76  thf('1', plain,
% 0.56/0.76      (~ (((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))) | 
% 0.56/0.76       ~ ((v2_tops_1 @ sk_B @ sk_A))),
% 0.56/0.76      inference('split', [status(esa)], ['0'])).
% 0.56/0.76  thf('2', plain,
% 0.56/0.76      ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0)) | (v2_tops_1 @ sk_B @ sk_A))),
% 0.56/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.56/0.76  thf('3', plain,
% 0.56/0.76      (((v2_tops_1 @ sk_B @ sk_A)) <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.56/0.76      inference('split', [status(esa)], ['2'])).
% 0.56/0.76  thf('4', plain,
% 0.56/0.76      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.56/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.56/0.76  thf(d4_tops_1, axiom,
% 0.56/0.76    (![A:$i]:
% 0.56/0.76     ( ( l1_pre_topc @ A ) =>
% 0.56/0.76       ( ![B:$i]:
% 0.56/0.76         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.56/0.76           ( ( v2_tops_1 @ B @ A ) <=>
% 0.56/0.76             ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) ))).
% 0.56/0.76  thf('5', plain,
% 0.56/0.76      (![X19 : $i, X20 : $i]:
% 0.56/0.76         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.56/0.76          | ~ (v2_tops_1 @ X19 @ X20)
% 0.56/0.76          | (v1_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ X20) @ X19) @ X20)
% 0.56/0.76          | ~ (l1_pre_topc @ X20))),
% 0.56/0.76      inference('cnf', [status(esa)], [d4_tops_1])).
% 0.56/0.76  thf('6', plain,
% 0.56/0.76      ((~ (l1_pre_topc @ sk_A)
% 0.56/0.76        | (v1_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 0.56/0.76        | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 0.56/0.76      inference('sup-', [status(thm)], ['4', '5'])).
% 0.56/0.76  thf('7', plain, ((l1_pre_topc @ sk_A)),
% 0.56/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.56/0.76  thf('8', plain,
% 0.56/0.76      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.56/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.56/0.76  thf(d5_subset_1, axiom,
% 0.56/0.76    (![A:$i,B:$i]:
% 0.56/0.76     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.56/0.76       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.56/0.76  thf('9', plain,
% 0.56/0.76      (![X1 : $i, X2 : $i]:
% 0.56/0.76         (((k3_subset_1 @ X1 @ X2) = (k4_xboole_0 @ X1 @ X2))
% 0.56/0.76          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X1)))),
% 0.56/0.76      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.56/0.76  thf('10', plain,
% 0.56/0.76      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 0.56/0.76         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 0.56/0.76      inference('sup-', [status(thm)], ['8', '9'])).
% 0.56/0.76  thf(d3_struct_0, axiom,
% 0.56/0.76    (![A:$i]:
% 0.56/0.76     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.56/0.76  thf('11', plain,
% 0.56/0.76      (![X11 : $i]:
% 0.56/0.76         (((k2_struct_0 @ X11) = (u1_struct_0 @ X11)) | ~ (l1_struct_0 @ X11))),
% 0.56/0.76      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.56/0.76  thf('12', plain,
% 0.56/0.76      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 0.56/0.76         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 0.56/0.76      inference('sup-', [status(thm)], ['8', '9'])).
% 0.56/0.76  thf('13', plain,
% 0.56/0.76      ((((k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B)
% 0.56/0.76          = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.56/0.76        | ~ (l1_struct_0 @ sk_A))),
% 0.56/0.76      inference('sup+', [status(thm)], ['11', '12'])).
% 0.56/0.76  thf('14', plain, ((l1_pre_topc @ sk_A)),
% 0.56/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.56/0.76  thf(dt_l1_pre_topc, axiom,
% 0.56/0.76    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.56/0.76  thf('15', plain,
% 0.56/0.76      (![X14 : $i]: ((l1_struct_0 @ X14) | ~ (l1_pre_topc @ X14))),
% 0.56/0.76      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.56/0.76  thf('16', plain, ((l1_struct_0 @ sk_A)),
% 0.56/0.76      inference('sup-', [status(thm)], ['14', '15'])).
% 0.56/0.76  thf('17', plain,
% 0.56/0.76      (((k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B)
% 0.56/0.76         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 0.56/0.76      inference('demod', [status(thm)], ['13', '16'])).
% 0.56/0.76  thf('18', plain,
% 0.56/0.76      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 0.56/0.76         = (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B))),
% 0.56/0.76      inference('demod', [status(thm)], ['10', '17'])).
% 0.56/0.76  thf('19', plain,
% 0.56/0.76      (![X11 : $i]:
% 0.56/0.76         (((k2_struct_0 @ X11) = (u1_struct_0 @ X11)) | ~ (l1_struct_0 @ X11))),
% 0.56/0.76      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.56/0.76  thf('20', plain,
% 0.56/0.76      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.56/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.56/0.76  thf('21', plain,
% 0.56/0.76      (((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))
% 0.56/0.76        | ~ (l1_struct_0 @ sk_A))),
% 0.56/0.76      inference('sup+', [status(thm)], ['19', '20'])).
% 0.56/0.76  thf('22', plain, ((l1_struct_0 @ sk_A)),
% 0.56/0.76      inference('sup-', [status(thm)], ['14', '15'])).
% 0.56/0.76  thf('23', plain,
% 0.56/0.76      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))),
% 0.56/0.76      inference('demod', [status(thm)], ['21', '22'])).
% 0.56/0.76  thf('24', plain,
% 0.56/0.76      (![X1 : $i, X2 : $i]:
% 0.56/0.76         (((k3_subset_1 @ X1 @ X2) = (k4_xboole_0 @ X1 @ X2))
% 0.56/0.76          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X1)))),
% 0.56/0.76      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.56/0.76  thf('25', plain,
% 0.56/0.76      (((k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B)
% 0.56/0.76         = (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))),
% 0.56/0.76      inference('sup-', [status(thm)], ['23', '24'])).
% 0.56/0.76  thf('26', plain,
% 0.56/0.76      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 0.56/0.76         = (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))),
% 0.56/0.76      inference('demod', [status(thm)], ['18', '25'])).
% 0.56/0.76  thf('27', plain,
% 0.56/0.76      (((v1_tops_1 @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 0.56/0.76        | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 0.56/0.76      inference('demod', [status(thm)], ['6', '7', '26'])).
% 0.56/0.76  thf('28', plain,
% 0.56/0.76      (((v1_tops_1 @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A))
% 0.56/0.76         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.56/0.76      inference('sup-', [status(thm)], ['3', '27'])).
% 0.56/0.76  thf('29', plain,
% 0.56/0.76      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.56/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.56/0.76  thf(dt_k3_subset_1, axiom,
% 0.56/0.76    (![A:$i,B:$i]:
% 0.56/0.76     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.56/0.76       ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.56/0.76  thf('30', plain,
% 0.56/0.76      (![X3 : $i, X4 : $i]:
% 0.56/0.76         ((m1_subset_1 @ (k3_subset_1 @ X3 @ X4) @ (k1_zfmisc_1 @ X3))
% 0.56/0.76          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X3)))),
% 0.56/0.76      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 0.56/0.76  thf('31', plain,
% 0.56/0.76      ((m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.56/0.76        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.56/0.76      inference('sup-', [status(thm)], ['29', '30'])).
% 0.56/0.76  thf('32', plain,
% 0.56/0.76      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 0.56/0.76         = (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))),
% 0.56/0.76      inference('demod', [status(thm)], ['18', '25'])).
% 0.56/0.76  thf('33', plain,
% 0.56/0.76      ((m1_subset_1 @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ 
% 0.56/0.76        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.56/0.76      inference('demod', [status(thm)], ['31', '32'])).
% 0.56/0.76  thf(d3_tops_1, axiom,
% 0.56/0.76    (![A:$i]:
% 0.56/0.76     ( ( l1_pre_topc @ A ) =>
% 0.56/0.76       ( ![B:$i]:
% 0.56/0.76         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.56/0.76           ( ( v1_tops_1 @ B @ A ) <=>
% 0.56/0.76             ( ( k2_pre_topc @ A @ B ) = ( k2_struct_0 @ A ) ) ) ) ) ))).
% 0.56/0.76  thf('34', plain,
% 0.56/0.76      (![X17 : $i, X18 : $i]:
% 0.56/0.76         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.56/0.76          | ~ (v1_tops_1 @ X17 @ X18)
% 0.56/0.76          | ((k2_pre_topc @ X18 @ X17) = (k2_struct_0 @ X18))
% 0.56/0.76          | ~ (l1_pre_topc @ X18))),
% 0.56/0.76      inference('cnf', [status(esa)], [d3_tops_1])).
% 0.56/0.76  thf('35', plain,
% 0.56/0.76      ((~ (l1_pre_topc @ sk_A)
% 0.56/0.76        | ((k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.56/0.76            = (k2_struct_0 @ sk_A))
% 0.56/0.76        | ~ (v1_tops_1 @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A))),
% 0.56/0.76      inference('sup-', [status(thm)], ['33', '34'])).
% 0.56/0.76  thf('36', plain, ((l1_pre_topc @ sk_A)),
% 0.56/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.56/0.76  thf('37', plain,
% 0.56/0.76      ((((k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.56/0.76          = (k2_struct_0 @ sk_A))
% 0.56/0.76        | ~ (v1_tops_1 @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A))),
% 0.56/0.76      inference('demod', [status(thm)], ['35', '36'])).
% 0.56/0.76  thf('38', plain,
% 0.56/0.76      ((((k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.56/0.76          = (k2_struct_0 @ sk_A)))
% 0.56/0.76         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.56/0.76      inference('sup-', [status(thm)], ['28', '37'])).
% 0.56/0.76  thf('39', plain,
% 0.56/0.76      ((m1_subset_1 @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ 
% 0.56/0.76        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.56/0.76      inference('demod', [status(thm)], ['31', '32'])).
% 0.56/0.76  thf(dt_k2_pre_topc, axiom,
% 0.56/0.76    (![A:$i,B:$i]:
% 0.56/0.76     ( ( ( l1_pre_topc @ A ) & 
% 0.56/0.76         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.56/0.76       ( m1_subset_1 @
% 0.56/0.76         ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.56/0.76  thf('40', plain,
% 0.56/0.76      (![X12 : $i, X13 : $i]:
% 0.56/0.76         (~ (l1_pre_topc @ X12)
% 0.56/0.76          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.56/0.76          | (m1_subset_1 @ (k2_pre_topc @ X12 @ X13) @ 
% 0.56/0.76             (k1_zfmisc_1 @ (u1_struct_0 @ X12))))),
% 0.56/0.76      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 0.56/0.76  thf('41', plain,
% 0.56/0.76      (((m1_subset_1 @ 
% 0.56/0.76         (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)) @ 
% 0.56/0.76         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.56/0.76        | ~ (l1_pre_topc @ sk_A))),
% 0.56/0.76      inference('sup-', [status(thm)], ['39', '40'])).
% 0.56/0.76  thf('42', plain, ((l1_pre_topc @ sk_A)),
% 0.56/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.56/0.76  thf('43', plain,
% 0.56/0.76      ((m1_subset_1 @ 
% 0.56/0.76        (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)) @ 
% 0.56/0.76        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.56/0.76      inference('demod', [status(thm)], ['41', '42'])).
% 0.56/0.76  thf('44', plain,
% 0.56/0.76      (((m1_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 0.56/0.76         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.56/0.76         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.56/0.76      inference('sup+', [status(thm)], ['38', '43'])).
% 0.56/0.76  thf(involutiveness_k3_subset_1, axiom,
% 0.56/0.76    (![A:$i,B:$i]:
% 0.56/0.76     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.56/0.76       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 0.56/0.76  thf('45', plain,
% 0.56/0.76      (![X5 : $i, X6 : $i]:
% 0.56/0.76         (((k3_subset_1 @ X6 @ (k3_subset_1 @ X6 @ X5)) = (X5))
% 0.56/0.76          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6)))),
% 0.56/0.76      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.56/0.76  thf('46', plain,
% 0.56/0.76      ((((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.56/0.76          (k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A)))
% 0.56/0.76          = (k2_struct_0 @ sk_A)))
% 0.56/0.76         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.56/0.76      inference('sup-', [status(thm)], ['44', '45'])).
% 0.56/0.76  thf('47', plain,
% 0.56/0.76      (((m1_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 0.56/0.76         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.56/0.76         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.56/0.76      inference('sup+', [status(thm)], ['38', '43'])).
% 0.56/0.76  thf('48', plain,
% 0.56/0.76      (![X1 : $i, X2 : $i]:
% 0.56/0.76         (((k3_subset_1 @ X1 @ X2) = (k4_xboole_0 @ X1 @ X2))
% 0.56/0.76          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X1)))),
% 0.56/0.76      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.56/0.76  thf('49', plain,
% 0.56/0.76      ((((k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A))
% 0.56/0.76          = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A))))
% 0.56/0.76         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.56/0.76      inference('sup-', [status(thm)], ['47', '48'])).
% 0.60/0.76  thf('50', plain,
% 0.60/0.76      (![X11 : $i]:
% 0.60/0.76         (((k2_struct_0 @ X11) = (u1_struct_0 @ X11)) | ~ (l1_struct_0 @ X11))),
% 0.60/0.76      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.60/0.76  thf('51', plain,
% 0.60/0.76      ((((k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A))
% 0.60/0.76          = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A))))
% 0.60/0.76         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.60/0.76      inference('sup-', [status(thm)], ['47', '48'])).
% 0.60/0.76  thf('52', plain,
% 0.60/0.76      (((((k3_subset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A))
% 0.60/0.76           = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A)))
% 0.60/0.76         | ~ (l1_struct_0 @ sk_A))) <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.60/0.76      inference('sup+', [status(thm)], ['50', '51'])).
% 0.60/0.76  thf(t4_subset_1, axiom,
% 0.60/0.76    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.60/0.76  thf('53', plain,
% 0.60/0.76      (![X7 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X7))),
% 0.60/0.76      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.60/0.76  thf('54', plain,
% 0.60/0.76      (![X5 : $i, X6 : $i]:
% 0.60/0.76         (((k3_subset_1 @ X6 @ (k3_subset_1 @ X6 @ X5)) = (X5))
% 0.60/0.76          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6)))),
% 0.60/0.76      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.60/0.76  thf('55', plain,
% 0.60/0.76      (![X0 : $i]:
% 0.60/0.76         ((k3_subset_1 @ X0 @ (k3_subset_1 @ X0 @ k1_xboole_0)) = (k1_xboole_0))),
% 0.60/0.76      inference('sup-', [status(thm)], ['53', '54'])).
% 0.60/0.76  thf('56', plain,
% 0.60/0.76      (![X7 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X7))),
% 0.60/0.76      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.60/0.76  thf('57', plain,
% 0.60/0.76      (![X1 : $i, X2 : $i]:
% 0.60/0.76         (((k3_subset_1 @ X1 @ X2) = (k4_xboole_0 @ X1 @ X2))
% 0.60/0.76          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X1)))),
% 0.60/0.76      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.60/0.76  thf('58', plain,
% 0.60/0.76      (![X0 : $i]:
% 0.60/0.76         ((k3_subset_1 @ X0 @ k1_xboole_0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 0.60/0.76      inference('sup-', [status(thm)], ['56', '57'])).
% 0.60/0.76  thf(t3_boole, axiom,
% 0.60/0.76    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.60/0.76  thf('59', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.60/0.76      inference('cnf', [status(esa)], [t3_boole])).
% 0.60/0.76  thf('60', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ k1_xboole_0) = (X0))),
% 0.60/0.76      inference('demod', [status(thm)], ['58', '59'])).
% 0.60/0.76  thf('61', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k1_xboole_0))),
% 0.60/0.76      inference('demod', [status(thm)], ['55', '60'])).
% 0.60/0.76  thf('62', plain, ((l1_struct_0 @ sk_A)),
% 0.60/0.76      inference('sup-', [status(thm)], ['14', '15'])).
% 0.60/0.76  thf('63', plain,
% 0.60/0.76      ((((k1_xboole_0)
% 0.60/0.76          = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A))))
% 0.60/0.76         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.60/0.76      inference('demod', [status(thm)], ['52', '61', '62'])).
% 0.60/0.76  thf('64', plain,
% 0.60/0.76      ((((k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A))
% 0.60/0.76          = (k1_xboole_0)))
% 0.60/0.76         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.60/0.76      inference('demod', [status(thm)], ['49', '63'])).
% 0.60/0.76  thf('65', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ k1_xboole_0) = (X0))),
% 0.60/0.76      inference('demod', [status(thm)], ['58', '59'])).
% 0.60/0.76  thf('66', plain,
% 0.60/0.76      ((((u1_struct_0 @ sk_A) = (k2_struct_0 @ sk_A)))
% 0.60/0.76         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.60/0.76      inference('demod', [status(thm)], ['46', '64', '65'])).
% 0.60/0.76  thf('67', plain,
% 0.60/0.76      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.60/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.76  thf(d1_tops_1, axiom,
% 0.60/0.76    (![A:$i]:
% 0.60/0.76     ( ( l1_pre_topc @ A ) =>
% 0.60/0.76       ( ![B:$i]:
% 0.60/0.76         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.60/0.76           ( ( k1_tops_1 @ A @ B ) =
% 0.60/0.76             ( k3_subset_1 @
% 0.60/0.76               ( u1_struct_0 @ A ) @ 
% 0.60/0.76               ( k2_pre_topc @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) ))).
% 0.60/0.76  thf('68', plain,
% 0.60/0.76      (![X15 : $i, X16 : $i]:
% 0.60/0.76         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.60/0.76          | ((k1_tops_1 @ X16 @ X15)
% 0.60/0.76              = (k3_subset_1 @ (u1_struct_0 @ X16) @ 
% 0.60/0.76                 (k2_pre_topc @ X16 @ (k3_subset_1 @ (u1_struct_0 @ X16) @ X15))))
% 0.60/0.76          | ~ (l1_pre_topc @ X16))),
% 0.60/0.76      inference('cnf', [status(esa)], [d1_tops_1])).
% 0.60/0.76  thf('69', plain,
% 0.60/0.76      ((~ (l1_pre_topc @ sk_A)
% 0.60/0.76        | ((k1_tops_1 @ sk_A @ sk_B)
% 0.60/0.76            = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.60/0.76               (k2_pre_topc @ sk_A @ 
% 0.60/0.76                (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)))))),
% 0.60/0.76      inference('sup-', [status(thm)], ['67', '68'])).
% 0.60/0.76  thf('70', plain, ((l1_pre_topc @ sk_A)),
% 0.60/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.76  thf('71', plain,
% 0.60/0.76      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 0.60/0.76         = (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))),
% 0.60/0.76      inference('demod', [status(thm)], ['18', '25'])).
% 0.60/0.76  thf('72', plain,
% 0.60/0.76      (((k1_tops_1 @ sk_A @ sk_B)
% 0.60/0.76         = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.60/0.76            (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))))),
% 0.60/0.76      inference('demod', [status(thm)], ['69', '70', '71'])).
% 0.60/0.76  thf('73', plain,
% 0.60/0.76      ((((k1_tops_1 @ sk_A @ sk_B)
% 0.60/0.76          = (k3_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 0.60/0.76             (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)))))
% 0.60/0.76         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.60/0.76      inference('sup+', [status(thm)], ['66', '72'])).
% 0.60/0.76  thf('74', plain,
% 0.60/0.76      ((((k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.60/0.76          = (k2_struct_0 @ sk_A)))
% 0.60/0.76         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.60/0.76      inference('sup-', [status(thm)], ['28', '37'])).
% 0.60/0.76  thf('75', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k1_xboole_0))),
% 0.60/0.76      inference('demod', [status(thm)], ['55', '60'])).
% 0.60/0.76  thf('76', plain,
% 0.60/0.76      ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0)))
% 0.60/0.76         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.60/0.76      inference('demod', [status(thm)], ['73', '74', '75'])).
% 0.60/0.76  thf('77', plain,
% 0.60/0.76      ((((k1_tops_1 @ sk_A @ sk_B) != (k1_xboole_0)))
% 0.60/0.76         <= (~ (((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.60/0.76      inference('split', [status(esa)], ['0'])).
% 0.60/0.76  thf('78', plain,
% 0.60/0.76      ((((k1_xboole_0) != (k1_xboole_0)))
% 0.60/0.76         <= (~ (((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))) & 
% 0.60/0.76             ((v2_tops_1 @ sk_B @ sk_A)))),
% 0.60/0.76      inference('sup-', [status(thm)], ['76', '77'])).
% 0.60/0.76  thf('79', plain,
% 0.60/0.76      ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))) | 
% 0.60/0.76       ~ ((v2_tops_1 @ sk_B @ sk_A))),
% 0.60/0.76      inference('simplify', [status(thm)], ['78'])).
% 0.60/0.76  thf('80', plain,
% 0.60/0.76      ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))) | 
% 0.60/0.76       ((v2_tops_1 @ sk_B @ sk_A))),
% 0.60/0.76      inference('split', [status(esa)], ['2'])).
% 0.60/0.76  thf('81', plain,
% 0.60/0.76      ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0)))
% 0.60/0.76         <= ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.60/0.76      inference('split', [status(esa)], ['2'])).
% 0.60/0.76  thf('82', plain,
% 0.60/0.76      (![X11 : $i]:
% 0.60/0.76         (((k2_struct_0 @ X11) = (u1_struct_0 @ X11)) | ~ (l1_struct_0 @ X11))),
% 0.60/0.76      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.60/0.76  thf('83', plain,
% 0.60/0.76      ((m1_subset_1 @ 
% 0.60/0.76        (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)) @ 
% 0.60/0.76        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.60/0.76      inference('demod', [status(thm)], ['41', '42'])).
% 0.60/0.76  thf('84', plain,
% 0.60/0.76      (![X5 : $i, X6 : $i]:
% 0.60/0.76         (((k3_subset_1 @ X6 @ (k3_subset_1 @ X6 @ X5)) = (X5))
% 0.60/0.76          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6)))),
% 0.60/0.76      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.60/0.76  thf('85', plain,
% 0.60/0.76      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.60/0.76         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.60/0.76          (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))))
% 0.60/0.76         = (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 0.60/0.76      inference('sup-', [status(thm)], ['83', '84'])).
% 0.60/0.76  thf('86', plain,
% 0.60/0.76      (((k1_tops_1 @ sk_A @ sk_B)
% 0.60/0.76         = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.60/0.76            (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))))),
% 0.60/0.76      inference('demod', [status(thm)], ['69', '70', '71'])).
% 0.60/0.76  thf('87', plain,
% 0.60/0.76      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B))
% 0.60/0.76         = (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 0.60/0.76      inference('demod', [status(thm)], ['85', '86'])).
% 0.60/0.76  thf('88', plain,
% 0.60/0.76      ((((k3_subset_1 @ (k2_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B))
% 0.60/0.76          = (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)))
% 0.60/0.76        | ~ (l1_struct_0 @ sk_A))),
% 0.60/0.76      inference('sup+', [status(thm)], ['82', '87'])).
% 0.60/0.76  thf('89', plain, ((l1_struct_0 @ sk_A)),
% 0.60/0.76      inference('sup-', [status(thm)], ['14', '15'])).
% 0.60/0.76  thf('90', plain,
% 0.60/0.76      (((k3_subset_1 @ (k2_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B))
% 0.60/0.76         = (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 0.60/0.76      inference('demod', [status(thm)], ['88', '89'])).
% 0.60/0.76  thf('91', plain,
% 0.60/0.76      ((((k3_subset_1 @ (k2_struct_0 @ sk_A) @ k1_xboole_0)
% 0.60/0.76          = (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))))
% 0.60/0.76         <= ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.60/0.76      inference('sup+', [status(thm)], ['81', '90'])).
% 0.60/0.76  thf('92', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ k1_xboole_0) = (X0))),
% 0.60/0.76      inference('demod', [status(thm)], ['58', '59'])).
% 0.60/0.76  thf('93', plain,
% 0.60/0.76      ((((k2_struct_0 @ sk_A)
% 0.60/0.76          = (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))))
% 0.60/0.76         <= ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.60/0.76      inference('demod', [status(thm)], ['91', '92'])).
% 0.60/0.76  thf('94', plain,
% 0.60/0.76      ((m1_subset_1 @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ 
% 0.60/0.76        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.60/0.76      inference('demod', [status(thm)], ['31', '32'])).
% 0.60/0.76  thf('95', plain,
% 0.60/0.76      (![X17 : $i, X18 : $i]:
% 0.60/0.76         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.60/0.76          | ((k2_pre_topc @ X18 @ X17) != (k2_struct_0 @ X18))
% 0.60/0.76          | (v1_tops_1 @ X17 @ X18)
% 0.60/0.76          | ~ (l1_pre_topc @ X18))),
% 0.60/0.76      inference('cnf', [status(esa)], [d3_tops_1])).
% 0.60/0.76  thf('96', plain,
% 0.60/0.76      ((~ (l1_pre_topc @ sk_A)
% 0.60/0.76        | (v1_tops_1 @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 0.60/0.76        | ((k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.60/0.76            != (k2_struct_0 @ sk_A)))),
% 0.60/0.76      inference('sup-', [status(thm)], ['94', '95'])).
% 0.60/0.76  thf('97', plain, ((l1_pre_topc @ sk_A)),
% 0.60/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.76  thf('98', plain,
% 0.60/0.76      (((v1_tops_1 @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 0.60/0.76        | ((k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.60/0.76            != (k2_struct_0 @ sk_A)))),
% 0.60/0.76      inference('demod', [status(thm)], ['96', '97'])).
% 0.60/0.76  thf('99', plain,
% 0.60/0.76      (((((k2_struct_0 @ sk_A) != (k2_struct_0 @ sk_A))
% 0.60/0.76         | (v1_tops_1 @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A)))
% 0.60/0.76         <= ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.60/0.76      inference('sup-', [status(thm)], ['93', '98'])).
% 0.60/0.76  thf('100', plain,
% 0.60/0.76      (((v1_tops_1 @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A))
% 0.60/0.76         <= ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.60/0.76      inference('simplify', [status(thm)], ['99'])).
% 0.60/0.76  thf('101', plain,
% 0.60/0.76      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.60/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.76  thf('102', plain,
% 0.60/0.76      (![X19 : $i, X20 : $i]:
% 0.60/0.76         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.60/0.76          | ~ (v1_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ X20) @ X19) @ X20)
% 0.60/0.76          | (v2_tops_1 @ X19 @ X20)
% 0.60/0.76          | ~ (l1_pre_topc @ X20))),
% 0.60/0.76      inference('cnf', [status(esa)], [d4_tops_1])).
% 0.60/0.76  thf('103', plain,
% 0.60/0.76      ((~ (l1_pre_topc @ sk_A)
% 0.60/0.76        | (v2_tops_1 @ sk_B @ sk_A)
% 0.60/0.76        | ~ (v1_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A))),
% 0.60/0.76      inference('sup-', [status(thm)], ['101', '102'])).
% 0.60/0.76  thf('104', plain, ((l1_pre_topc @ sk_A)),
% 0.60/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.76  thf('105', plain,
% 0.60/0.76      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 0.60/0.76         = (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))),
% 0.60/0.76      inference('demod', [status(thm)], ['18', '25'])).
% 0.60/0.76  thf('106', plain,
% 0.60/0.76      (((v2_tops_1 @ sk_B @ sk_A)
% 0.60/0.76        | ~ (v1_tops_1 @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A))),
% 0.60/0.76      inference('demod', [status(thm)], ['103', '104', '105'])).
% 0.60/0.76  thf('107', plain,
% 0.60/0.76      (((v2_tops_1 @ sk_B @ sk_A))
% 0.60/0.76         <= ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.60/0.76      inference('sup-', [status(thm)], ['100', '106'])).
% 0.60/0.76  thf('108', plain,
% 0.60/0.76      ((~ (v2_tops_1 @ sk_B @ sk_A)) <= (~ ((v2_tops_1 @ sk_B @ sk_A)))),
% 0.60/0.76      inference('split', [status(esa)], ['0'])).
% 0.60/0.76  thf('109', plain,
% 0.60/0.76      (~ (((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))) | 
% 0.60/0.76       ((v2_tops_1 @ sk_B @ sk_A))),
% 0.60/0.76      inference('sup-', [status(thm)], ['107', '108'])).
% 0.60/0.76  thf('110', plain, ($false),
% 0.60/0.76      inference('sat_resolution*', [status(thm)], ['1', '79', '80', '109'])).
% 0.60/0.76  
% 0.60/0.76  % SZS output end Refutation
% 0.60/0.76  
% 0.60/0.77  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
