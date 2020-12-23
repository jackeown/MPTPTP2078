%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.TWYFVutOsX

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:02:43 EST 2020

% Result     : Theorem 0.45s
% Output     : Refutation 0.45s
% Verified   : 
% Statistics : Number of formulae       :  120 ( 858 expanded)
%              Number of leaves         :   28 ( 272 expanded)
%              Depth                    :   18
%              Number of atoms          : 1004 (7628 expanded)
%              Number of equality atoms :   43 ( 318 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(t29_tops_1,conjecture,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v4_pre_topc @ B @ A )
          <=> ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_pre_topc @ A )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( ( v4_pre_topc @ B @ A )
            <=> ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t29_tops_1])).

thf('0',plain,
    ( ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('2',plain,(
    ! [X14: $i] :
      ( ( ( k2_struct_0 @ X14 )
        = ( u1_struct_0 @ X14 ) )
      | ~ ( l1_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('3',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('5',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('6',plain,(
    ! [X17: $i] :
      ( ( l1_struct_0 @ X17 )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('7',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['4','7'])).

thf(dt_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('9',plain,(
    ! [X4: $i,X5: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X4 @ X5 ) @ ( k1_zfmisc_1 @ X4 ) )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('10',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['4','7'])).

thf('12',plain,(
    ! [X14: $i] :
      ( ( ( k2_struct_0 @ X14 )
        = ( u1_struct_0 @ X14 ) )
      | ~ ( l1_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('13',plain,(
    ! [X14: $i] :
      ( ( ( k2_struct_0 @ X14 )
        = ( u1_struct_0 @ X14 ) )
      | ~ ( l1_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('14',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t25_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k4_subset_1 @ A @ B @ ( k3_subset_1 @ A @ B ) )
        = ( k2_subset_1 @ A ) ) ) )).

thf('15',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k4_subset_1 @ X6 @ X7 @ ( k3_subset_1 @ X6 @ X7 ) )
        = ( k2_subset_1 @ X6 ) )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t25_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('16',plain,(
    ! [X2: $i] :
      ( ( k2_subset_1 @ X2 )
      = X2 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('17',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k4_subset_1 @ X6 @ X7 @ ( k3_subset_1 @ X6 @ X7 ) )
        = X6 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,
    ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['14','17'])).

thf('19',plain,
    ( ( ( k4_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      = ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['13','18'])).

thf('20',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['5','6'])).

thf('21',plain,
    ( ( k4_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,
    ( ( ( k4_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      = ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['12','21'])).

thf('23',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['4','7'])).

thf('24',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k4_subset_1 @ X6 @ X7 @ ( k3_subset_1 @ X6 @ X7 ) )
        = X6 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('25',plain,
    ( ( k4_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
    = ( k2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['5','6'])).

thf('27',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['22','25','26'])).

thf(t25_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( ( ( k2_struct_0 @ A )
                    = ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) )
                  & ( r1_xboole_0 @ B @ C ) )
               => ( C
                  = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_struct_0 @ A ) @ B ) ) ) ) ) ) )).

thf('28',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ( ( k2_struct_0 @ X19 )
       != ( k4_subset_1 @ ( u1_struct_0 @ X19 ) @ X18 @ X20 ) )
      | ~ ( r1_xboole_0 @ X18 @ X20 )
      | ( X20
        = ( k7_subset_1 @ ( u1_struct_0 @ X19 ) @ ( k2_struct_0 @ X19 ) @ X18 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( l1_struct_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t25_pre_topc])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) )
      | ~ ( l1_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( X1
        = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ X0 ) )
      | ~ ( r1_xboole_0 @ X0 @ X1 )
      | ( ( k2_struct_0 @ sk_A )
       != ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['5','6'])).

thf('31',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['22','25','26'])).

thf('32',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['22','25','26'])).

thf('33',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['22','25','26'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) )
      | ( X1
        = ( k7_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ X0 ) )
      | ~ ( r1_xboole_0 @ X0 @ X1 )
      | ( ( k2_struct_0 @ sk_A )
       != ( k4_subset_1 @ ( k2_struct_0 @ sk_A ) @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['29','30','31','32','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( ( k2_struct_0 @ sk_A )
       != ( k4_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B @ X0 ) )
      | ~ ( r1_xboole_0 @ sk_B @ X0 )
      | ( X0
        = ( k7_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['11','34'])).

thf('36',plain,
    ( ( ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B )
      = ( k7_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
    | ~ ( r1_xboole_0 @ sk_B @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
    | ( ( k2_struct_0 @ sk_A )
     != ( k4_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['10','35'])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('37',plain,(
    ! [X3: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X3 ) @ ( k1_zfmisc_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf('38',plain,(
    ! [X2: $i] :
      ( ( k2_subset_1 @ X2 )
      = X2 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('39',plain,(
    ! [X3: $i] :
      ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X3 ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('40',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r1_tarski @ X11 @ X12 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('41',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['4','7'])).

thf(t43_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ( r1_xboole_0 @ B @ C )
          <=> ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) ) ) ) ) )).

thf('43',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) )
      | ~ ( r1_tarski @ X10 @ ( k3_subset_1 @ X9 @ X8 ) )
      | ( r1_xboole_0 @ X10 @ X8 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t43_subset_1])).

thf('44',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) )
      | ( r1_xboole_0 @ X0 @ sk_B )
      | ~ ( r1_tarski @ X0 @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,
    ( ( r1_xboole_0 @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_B )
    | ~ ( m1_subset_1 @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['41','44'])).

thf('46',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('47',plain,(
    r1_xboole_0 @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_B ),
    inference(demod,[status(thm)],['45','46'])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('49',plain,(
    r1_xboole_0 @ sk_B @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,
    ( ( k4_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
    = ( k2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('51',plain,
    ( ( ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B )
      = ( k7_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
    | ( ( k2_struct_0 @ sk_A )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['36','49','50'])).

thf('52',plain,
    ( ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B )
    = ( k7_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ sk_B ) ),
    inference(simplify,[status(thm)],['51'])).

thf('53',plain,
    ( ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['53'])).

thf('55',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['4','7'])).

thf('56',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['22','25','26'])).

thf(d6_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v4_pre_topc @ B @ A )
          <=> ( v3_pre_topc @ ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_struct_0 @ A ) @ B ) @ A ) ) ) ) )).

thf('57',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( v4_pre_topc @ X15 @ X16 )
      | ( v3_pre_topc @ ( k7_subset_1 @ ( u1_struct_0 @ X16 ) @ ( k2_struct_0 @ X16 ) @ X15 ) @ X16 )
      | ~ ( l1_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[d6_pre_topc])).

thf('58',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v3_pre_topc @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ X0 ) @ sk_A )
      | ~ ( v4_pre_topc @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['22','25','26'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) )
      | ( v3_pre_topc @ ( k7_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ X0 ) @ sk_A )
      | ~ ( v4_pre_topc @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['58','59','60'])).

thf('62',plain,
    ( ~ ( v4_pre_topc @ sk_B @ sk_A )
    | ( v3_pre_topc @ ( k7_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['55','61'])).

thf('63',plain,
    ( ( v3_pre_topc @ ( k7_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['54','62'])).

thf('64',plain,
    ( ( v3_pre_topc @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['52','63'])).

thf('65',plain,(
    ! [X14: $i] :
      ( ( ( k2_struct_0 @ X14 )
        = ( u1_struct_0 @ X14 ) )
      | ~ ( l1_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('66',plain,
    ( ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
   <= ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('67',plain,
    ( ( ~ ( v3_pre_topc @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['5','6'])).

thf('69',plain,
    ( ~ ( v3_pre_topc @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
   <= ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('70',plain,
    ( ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['64','69'])).

thf('71',plain,
    ( ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['53'])).

thf('72',plain,(
    ! [X14: $i] :
      ( ( ( k2_struct_0 @ X14 )
        = ( u1_struct_0 @ X14 ) )
      | ~ ( l1_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('73',plain,
    ( ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
   <= ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference(split,[status(esa)],['53'])).

thf('74',plain,
    ( ( ( v3_pre_topc @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference('sup+',[status(thm)],['72','73'])).

thf('75',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['5','6'])).

thf('76',plain,
    ( ( v3_pre_topc @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
   <= ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['74','75'])).

thf('77',plain,
    ( ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B )
    = ( k7_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ sk_B ) ),
    inference(simplify,[status(thm)],['51'])).

thf('78',plain,(
    ! [X14: $i] :
      ( ( ( k2_struct_0 @ X14 )
        = ( u1_struct_0 @ X14 ) )
      | ~ ( l1_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('79',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( v3_pre_topc @ ( k7_subset_1 @ ( u1_struct_0 @ X16 ) @ ( k2_struct_0 @ X16 ) @ X15 ) @ X16 )
      | ( v4_pre_topc @ X15 @ X16 )
      | ~ ( l1_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[d6_pre_topc])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_pre_topc @ ( k7_subset_1 @ ( k2_struct_0 @ X0 ) @ ( k2_struct_0 @ X0 ) @ X1 ) @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v4_pre_topc @ X1 @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,
    ( ~ ( v3_pre_topc @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v4_pre_topc @ sk_B @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['77','80'])).

thf('82',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['22','25','26'])).

thf('83',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['4','7'])).

thf('84',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['5','6'])).

thf('86',plain,
    ( ~ ( v3_pre_topc @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['81','82','83','84','85'])).

thf('87',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
   <= ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['76','86'])).

thf('88',plain,
    ( ~ ( v4_pre_topc @ sk_B @ sk_A )
   <= ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('89',plain,
    ( ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','70','71','89'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.TWYFVutOsX
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 17:23:49 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running portfolio for 600 s
% 0.12/0.33  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.33  % Number of cores: 8
% 0.12/0.33  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.45/0.71  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.45/0.71  % Solved by: fo/fo7.sh
% 0.45/0.71  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.45/0.71  % done 363 iterations in 0.298s
% 0.45/0.71  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.45/0.71  % SZS output start Refutation
% 0.45/0.71  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.45/0.71  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.45/0.71  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.45/0.71  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.45/0.71  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 0.45/0.71  thf(sk_A_type, type, sk_A: $i).
% 0.45/0.71  thf(sk_B_type, type, sk_B: $i).
% 0.45/0.71  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.45/0.71  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.45/0.71  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.45/0.71  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 0.45/0.71  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.45/0.71  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.45/0.71  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.45/0.71  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.45/0.71  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.45/0.71  thf(t29_tops_1, conjecture,
% 0.45/0.71    (![A:$i]:
% 0.45/0.71     ( ( l1_pre_topc @ A ) =>
% 0.45/0.71       ( ![B:$i]:
% 0.45/0.71         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.45/0.71           ( ( v4_pre_topc @ B @ A ) <=>
% 0.45/0.71             ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) ))).
% 0.45/0.71  thf(zf_stmt_0, negated_conjecture,
% 0.45/0.71    (~( ![A:$i]:
% 0.45/0.71        ( ( l1_pre_topc @ A ) =>
% 0.45/0.71          ( ![B:$i]:
% 0.45/0.71            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.45/0.71              ( ( v4_pre_topc @ B @ A ) <=>
% 0.45/0.71                ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) ) )),
% 0.45/0.71    inference('cnf.neg', [status(esa)], [t29_tops_1])).
% 0.45/0.71  thf('0', plain,
% 0.45/0.71      ((~ (v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 0.45/0.71        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.45/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.71  thf('1', plain,
% 0.45/0.71      (~ ((v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)) | 
% 0.45/0.71       ~ ((v4_pre_topc @ sk_B @ sk_A))),
% 0.45/0.71      inference('split', [status(esa)], ['0'])).
% 0.45/0.71  thf(d3_struct_0, axiom,
% 0.45/0.71    (![A:$i]:
% 0.45/0.71     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.45/0.71  thf('2', plain,
% 0.45/0.71      (![X14 : $i]:
% 0.45/0.71         (((k2_struct_0 @ X14) = (u1_struct_0 @ X14)) | ~ (l1_struct_0 @ X14))),
% 0.45/0.71      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.45/0.71  thf('3', plain,
% 0.45/0.71      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.71  thf('4', plain,
% 0.45/0.71      (((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))
% 0.45/0.71        | ~ (l1_struct_0 @ sk_A))),
% 0.45/0.71      inference('sup+', [status(thm)], ['2', '3'])).
% 0.45/0.71  thf('5', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.71  thf(dt_l1_pre_topc, axiom,
% 0.45/0.71    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.45/0.71  thf('6', plain, (![X17 : $i]: ((l1_struct_0 @ X17) | ~ (l1_pre_topc @ X17))),
% 0.45/0.71      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.45/0.71  thf('7', plain, ((l1_struct_0 @ sk_A)),
% 0.45/0.71      inference('sup-', [status(thm)], ['5', '6'])).
% 0.45/0.71  thf('8', plain,
% 0.45/0.71      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))),
% 0.45/0.71      inference('demod', [status(thm)], ['4', '7'])).
% 0.45/0.71  thf(dt_k3_subset_1, axiom,
% 0.45/0.71    (![A:$i,B:$i]:
% 0.45/0.71     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.45/0.71       ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.45/0.71  thf('9', plain,
% 0.45/0.71      (![X4 : $i, X5 : $i]:
% 0.45/0.71         ((m1_subset_1 @ (k3_subset_1 @ X4 @ X5) @ (k1_zfmisc_1 @ X4))
% 0.45/0.71          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X4)))),
% 0.45/0.71      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 0.45/0.71  thf('10', plain,
% 0.45/0.71      ((m1_subset_1 @ (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B) @ 
% 0.45/0.71        (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))),
% 0.45/0.71      inference('sup-', [status(thm)], ['8', '9'])).
% 0.45/0.71  thf('11', plain,
% 0.45/0.71      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))),
% 0.45/0.71      inference('demod', [status(thm)], ['4', '7'])).
% 0.45/0.71  thf('12', plain,
% 0.45/0.71      (![X14 : $i]:
% 0.45/0.71         (((k2_struct_0 @ X14) = (u1_struct_0 @ X14)) | ~ (l1_struct_0 @ X14))),
% 0.45/0.71      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.45/0.71  thf('13', plain,
% 0.45/0.71      (![X14 : $i]:
% 0.45/0.71         (((k2_struct_0 @ X14) = (u1_struct_0 @ X14)) | ~ (l1_struct_0 @ X14))),
% 0.45/0.71      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.45/0.71  thf('14', plain,
% 0.45/0.71      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.71  thf(t25_subset_1, axiom,
% 0.45/0.71    (![A:$i,B:$i]:
% 0.45/0.71     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.45/0.71       ( ( k4_subset_1 @ A @ B @ ( k3_subset_1 @ A @ B ) ) =
% 0.45/0.71         ( k2_subset_1 @ A ) ) ))).
% 0.45/0.71  thf('15', plain,
% 0.45/0.71      (![X6 : $i, X7 : $i]:
% 0.45/0.71         (((k4_subset_1 @ X6 @ X7 @ (k3_subset_1 @ X6 @ X7))
% 0.45/0.71            = (k2_subset_1 @ X6))
% 0.45/0.71          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X6)))),
% 0.45/0.71      inference('cnf', [status(esa)], [t25_subset_1])).
% 0.45/0.71  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.45/0.71  thf('16', plain, (![X2 : $i]: ((k2_subset_1 @ X2) = (X2))),
% 0.45/0.71      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.45/0.71  thf('17', plain,
% 0.45/0.71      (![X6 : $i, X7 : $i]:
% 0.45/0.71         (((k4_subset_1 @ X6 @ X7 @ (k3_subset_1 @ X6 @ X7)) = (X6))
% 0.45/0.71          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X6)))),
% 0.45/0.71      inference('demod', [status(thm)], ['15', '16'])).
% 0.45/0.71  thf('18', plain,
% 0.45/0.71      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.45/0.71         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)) = (u1_struct_0 @ sk_A))),
% 0.45/0.71      inference('sup-', [status(thm)], ['14', '17'])).
% 0.45/0.71  thf('19', plain,
% 0.45/0.71      ((((k4_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B @ 
% 0.45/0.71          (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)) = (u1_struct_0 @ sk_A))
% 0.45/0.71        | ~ (l1_struct_0 @ sk_A))),
% 0.45/0.71      inference('sup+', [status(thm)], ['13', '18'])).
% 0.45/0.71  thf('20', plain, ((l1_struct_0 @ sk_A)),
% 0.45/0.71      inference('sup-', [status(thm)], ['5', '6'])).
% 0.45/0.71  thf('21', plain,
% 0.45/0.71      (((k4_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B @ 
% 0.45/0.71         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)) = (u1_struct_0 @ sk_A))),
% 0.45/0.71      inference('demod', [status(thm)], ['19', '20'])).
% 0.45/0.71  thf('22', plain,
% 0.45/0.71      ((((k4_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B @ 
% 0.45/0.71          (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B)) = (u1_struct_0 @ sk_A))
% 0.45/0.71        | ~ (l1_struct_0 @ sk_A))),
% 0.45/0.71      inference('sup+', [status(thm)], ['12', '21'])).
% 0.45/0.71  thf('23', plain,
% 0.45/0.71      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))),
% 0.45/0.71      inference('demod', [status(thm)], ['4', '7'])).
% 0.45/0.71  thf('24', plain,
% 0.45/0.71      (![X6 : $i, X7 : $i]:
% 0.45/0.71         (((k4_subset_1 @ X6 @ X7 @ (k3_subset_1 @ X6 @ X7)) = (X6))
% 0.45/0.71          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X6)))),
% 0.45/0.71      inference('demod', [status(thm)], ['15', '16'])).
% 0.45/0.71  thf('25', plain,
% 0.45/0.71      (((k4_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B @ 
% 0.45/0.71         (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B)) = (k2_struct_0 @ sk_A))),
% 0.45/0.71      inference('sup-', [status(thm)], ['23', '24'])).
% 0.45/0.71  thf('26', plain, ((l1_struct_0 @ sk_A)),
% 0.45/0.71      inference('sup-', [status(thm)], ['5', '6'])).
% 0.45/0.71  thf('27', plain, (((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))),
% 0.45/0.71      inference('demod', [status(thm)], ['22', '25', '26'])).
% 0.45/0.71  thf(t25_pre_topc, axiom,
% 0.45/0.71    (![A:$i]:
% 0.45/0.71     ( ( l1_struct_0 @ A ) =>
% 0.45/0.71       ( ![B:$i]:
% 0.45/0.71         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.45/0.71           ( ![C:$i]:
% 0.45/0.71             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.45/0.71               ( ( ( ( k2_struct_0 @ A ) =
% 0.45/0.71                     ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) ) & 
% 0.45/0.71                   ( r1_xboole_0 @ B @ C ) ) =>
% 0.45/0.71                 ( ( C ) =
% 0.45/0.71                   ( k7_subset_1 @
% 0.45/0.71                     ( u1_struct_0 @ A ) @ ( k2_struct_0 @ A ) @ B ) ) ) ) ) ) ) ))).
% 0.45/0.71  thf('28', plain,
% 0.45/0.71      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.45/0.71         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.45/0.71          | ((k2_struct_0 @ X19)
% 0.45/0.71              != (k4_subset_1 @ (u1_struct_0 @ X19) @ X18 @ X20))
% 0.45/0.71          | ~ (r1_xboole_0 @ X18 @ X20)
% 0.45/0.71          | ((X20)
% 0.45/0.71              = (k7_subset_1 @ (u1_struct_0 @ X19) @ (k2_struct_0 @ X19) @ X18))
% 0.45/0.71          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.45/0.71          | ~ (l1_struct_0 @ X19))),
% 0.45/0.71      inference('cnf', [status(esa)], [t25_pre_topc])).
% 0.45/0.71  thf('29', plain,
% 0.45/0.71      (![X0 : $i, X1 : $i]:
% 0.45/0.71         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))
% 0.45/0.71          | ~ (l1_struct_0 @ sk_A)
% 0.45/0.71          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.45/0.71          | ((X1)
% 0.45/0.71              = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A) @ X0))
% 0.45/0.71          | ~ (r1_xboole_0 @ X0 @ X1)
% 0.45/0.71          | ((k2_struct_0 @ sk_A)
% 0.45/0.71              != (k4_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ X1)))),
% 0.45/0.71      inference('sup-', [status(thm)], ['27', '28'])).
% 0.45/0.71  thf('30', plain, ((l1_struct_0 @ sk_A)),
% 0.45/0.71      inference('sup-', [status(thm)], ['5', '6'])).
% 0.45/0.71  thf('31', plain, (((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))),
% 0.45/0.71      inference('demod', [status(thm)], ['22', '25', '26'])).
% 0.45/0.71  thf('32', plain, (((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))),
% 0.45/0.71      inference('demod', [status(thm)], ['22', '25', '26'])).
% 0.45/0.71  thf('33', plain, (((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))),
% 0.45/0.71      inference('demod', [status(thm)], ['22', '25', '26'])).
% 0.45/0.71  thf('34', plain,
% 0.45/0.71      (![X0 : $i, X1 : $i]:
% 0.45/0.71         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))
% 0.45/0.71          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))
% 0.45/0.71          | ((X1)
% 0.45/0.71              = (k7_subset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A) @ X0))
% 0.45/0.71          | ~ (r1_xboole_0 @ X0 @ X1)
% 0.45/0.71          | ((k2_struct_0 @ sk_A)
% 0.45/0.71              != (k4_subset_1 @ (k2_struct_0 @ sk_A) @ X0 @ X1)))),
% 0.45/0.71      inference('demod', [status(thm)], ['29', '30', '31', '32', '33'])).
% 0.45/0.71  thf('35', plain,
% 0.45/0.71      (![X0 : $i]:
% 0.45/0.71         (((k2_struct_0 @ sk_A)
% 0.45/0.71            != (k4_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B @ X0))
% 0.45/0.71          | ~ (r1_xboole_0 @ sk_B @ X0)
% 0.45/0.71          | ((X0)
% 0.45/0.71              = (k7_subset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A) @ 
% 0.45/0.71                 sk_B))
% 0.45/0.71          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A))))),
% 0.45/0.71      inference('sup-', [status(thm)], ['11', '34'])).
% 0.45/0.71  thf('36', plain,
% 0.45/0.71      ((((k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B)
% 0.45/0.71          = (k7_subset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.45/0.71        | ~ (r1_xboole_0 @ sk_B @ (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.45/0.71        | ((k2_struct_0 @ sk_A)
% 0.45/0.71            != (k4_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B @ 
% 0.45/0.71                (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B))))),
% 0.45/0.71      inference('sup-', [status(thm)], ['10', '35'])).
% 0.45/0.71  thf(dt_k2_subset_1, axiom,
% 0.45/0.71    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.45/0.71  thf('37', plain,
% 0.45/0.71      (![X3 : $i]: (m1_subset_1 @ (k2_subset_1 @ X3) @ (k1_zfmisc_1 @ X3))),
% 0.45/0.71      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 0.45/0.71  thf('38', plain, (![X2 : $i]: ((k2_subset_1 @ X2) = (X2))),
% 0.45/0.71      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.45/0.71  thf('39', plain, (![X3 : $i]: (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X3))),
% 0.45/0.71      inference('demod', [status(thm)], ['37', '38'])).
% 0.45/0.71  thf(t3_subset, axiom,
% 0.45/0.71    (![A:$i,B:$i]:
% 0.45/0.71     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.45/0.71  thf('40', plain,
% 0.45/0.71      (![X11 : $i, X12 : $i]:
% 0.45/0.71         ((r1_tarski @ X11 @ X12) | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12)))),
% 0.45/0.71      inference('cnf', [status(esa)], [t3_subset])).
% 0.45/0.71  thf('41', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.45/0.71      inference('sup-', [status(thm)], ['39', '40'])).
% 0.45/0.71  thf('42', plain,
% 0.45/0.71      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))),
% 0.45/0.71      inference('demod', [status(thm)], ['4', '7'])).
% 0.45/0.71  thf(t43_subset_1, axiom,
% 0.45/0.71    (![A:$i,B:$i]:
% 0.45/0.71     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.45/0.71       ( ![C:$i]:
% 0.45/0.71         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.45/0.71           ( ( r1_xboole_0 @ B @ C ) <=>
% 0.45/0.71             ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) ) ) ) ) ))).
% 0.45/0.71  thf('43', plain,
% 0.45/0.71      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.45/0.71         (~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9))
% 0.45/0.71          | ~ (r1_tarski @ X10 @ (k3_subset_1 @ X9 @ X8))
% 0.45/0.71          | (r1_xboole_0 @ X10 @ X8)
% 0.45/0.71          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X9)))),
% 0.45/0.71      inference('cnf', [status(esa)], [t43_subset_1])).
% 0.45/0.71  thf('44', plain,
% 0.45/0.71      (![X0 : $i]:
% 0.45/0.71         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))
% 0.45/0.71          | (r1_xboole_0 @ X0 @ sk_B)
% 0.45/0.71          | ~ (r1_tarski @ X0 @ (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 0.45/0.71      inference('sup-', [status(thm)], ['42', '43'])).
% 0.45/0.71  thf('45', plain,
% 0.45/0.71      (((r1_xboole_0 @ (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_B)
% 0.45/0.71        | ~ (m1_subset_1 @ (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B) @ 
% 0.45/0.71             (k1_zfmisc_1 @ (k2_struct_0 @ sk_A))))),
% 0.45/0.71      inference('sup-', [status(thm)], ['41', '44'])).
% 0.45/0.71  thf('46', plain,
% 0.45/0.71      ((m1_subset_1 @ (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B) @ 
% 0.45/0.71        (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))),
% 0.45/0.71      inference('sup-', [status(thm)], ['8', '9'])).
% 0.45/0.71  thf('47', plain,
% 0.45/0.71      ((r1_xboole_0 @ (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_B)),
% 0.45/0.71      inference('demod', [status(thm)], ['45', '46'])).
% 0.45/0.71  thf(symmetry_r1_xboole_0, axiom,
% 0.45/0.71    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 0.45/0.71  thf('48', plain,
% 0.45/0.71      (![X0 : $i, X1 : $i]:
% 0.45/0.71         ((r1_xboole_0 @ X0 @ X1) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.45/0.71      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.45/0.71  thf('49', plain,
% 0.45/0.71      ((r1_xboole_0 @ sk_B @ (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B))),
% 0.45/0.71      inference('sup-', [status(thm)], ['47', '48'])).
% 0.45/0.71  thf('50', plain,
% 0.45/0.71      (((k4_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B @ 
% 0.45/0.71         (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B)) = (k2_struct_0 @ sk_A))),
% 0.45/0.71      inference('sup-', [status(thm)], ['23', '24'])).
% 0.45/0.71  thf('51', plain,
% 0.45/0.71      ((((k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B)
% 0.45/0.71          = (k7_subset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.45/0.71        | ((k2_struct_0 @ sk_A) != (k2_struct_0 @ sk_A)))),
% 0.45/0.71      inference('demod', [status(thm)], ['36', '49', '50'])).
% 0.45/0.71  thf('52', plain,
% 0.45/0.71      (((k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B)
% 0.45/0.71         = (k7_subset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A) @ sk_B))),
% 0.45/0.71      inference('simplify', [status(thm)], ['51'])).
% 0.45/0.71  thf('53', plain,
% 0.45/0.71      (((v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 0.45/0.71        | (v4_pre_topc @ sk_B @ sk_A))),
% 0.45/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.71  thf('54', plain,
% 0.45/0.71      (((v4_pre_topc @ sk_B @ sk_A)) <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.45/0.71      inference('split', [status(esa)], ['53'])).
% 0.45/0.71  thf('55', plain,
% 0.45/0.71      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))),
% 0.45/0.71      inference('demod', [status(thm)], ['4', '7'])).
% 0.45/0.71  thf('56', plain, (((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))),
% 0.45/0.71      inference('demod', [status(thm)], ['22', '25', '26'])).
% 0.45/0.71  thf(d6_pre_topc, axiom,
% 0.45/0.71    (![A:$i]:
% 0.45/0.71     ( ( l1_pre_topc @ A ) =>
% 0.45/0.71       ( ![B:$i]:
% 0.45/0.71         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.45/0.71           ( ( v4_pre_topc @ B @ A ) <=>
% 0.45/0.71             ( v3_pre_topc @
% 0.45/0.71               ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_struct_0 @ A ) @ B ) @ 
% 0.45/0.71               A ) ) ) ) ))).
% 0.45/0.71  thf('57', plain,
% 0.45/0.71      (![X15 : $i, X16 : $i]:
% 0.45/0.71         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.45/0.71          | ~ (v4_pre_topc @ X15 @ X16)
% 0.45/0.71          | (v3_pre_topc @ 
% 0.45/0.71             (k7_subset_1 @ (u1_struct_0 @ X16) @ (k2_struct_0 @ X16) @ X15) @ 
% 0.45/0.71             X16)
% 0.45/0.71          | ~ (l1_pre_topc @ X16))),
% 0.45/0.71      inference('cnf', [status(esa)], [d6_pre_topc])).
% 0.45/0.71  thf('58', plain,
% 0.45/0.71      (![X0 : $i]:
% 0.45/0.71         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))
% 0.45/0.71          | ~ (l1_pre_topc @ sk_A)
% 0.45/0.71          | (v3_pre_topc @ 
% 0.45/0.71             (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A) @ X0) @ 
% 0.45/0.71             sk_A)
% 0.45/0.71          | ~ (v4_pre_topc @ X0 @ sk_A))),
% 0.45/0.71      inference('sup-', [status(thm)], ['56', '57'])).
% 0.45/0.71  thf('59', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.71  thf('60', plain, (((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))),
% 0.45/0.71      inference('demod', [status(thm)], ['22', '25', '26'])).
% 0.45/0.71  thf('61', plain,
% 0.45/0.71      (![X0 : $i]:
% 0.45/0.71         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))
% 0.45/0.71          | (v3_pre_topc @ 
% 0.45/0.71             (k7_subset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A) @ X0) @ 
% 0.45/0.71             sk_A)
% 0.45/0.71          | ~ (v4_pre_topc @ X0 @ sk_A))),
% 0.45/0.71      inference('demod', [status(thm)], ['58', '59', '60'])).
% 0.45/0.71  thf('62', plain,
% 0.45/0.71      ((~ (v4_pre_topc @ sk_B @ sk_A)
% 0.45/0.71        | (v3_pre_topc @ 
% 0.45/0.71           (k7_subset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A) @ sk_B) @ 
% 0.45/0.71           sk_A))),
% 0.45/0.71      inference('sup-', [status(thm)], ['55', '61'])).
% 0.45/0.71  thf('63', plain,
% 0.45/0.71      (((v3_pre_topc @ 
% 0.45/0.71         (k7_subset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A) @ sk_B) @ 
% 0.45/0.71         sk_A)) <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.45/0.71      inference('sup-', [status(thm)], ['54', '62'])).
% 0.45/0.71  thf('64', plain,
% 0.45/0.71      (((v3_pre_topc @ (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A))
% 0.45/0.71         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.45/0.71      inference('sup+', [status(thm)], ['52', '63'])).
% 0.45/0.71  thf('65', plain,
% 0.45/0.71      (![X14 : $i]:
% 0.45/0.71         (((k2_struct_0 @ X14) = (u1_struct_0 @ X14)) | ~ (l1_struct_0 @ X14))),
% 0.45/0.71      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.45/0.71  thf('66', plain,
% 0.45/0.71      ((~ (v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A))
% 0.45/0.71         <= (~
% 0.45/0.71             ((v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)))),
% 0.45/0.71      inference('split', [status(esa)], ['0'])).
% 0.45/0.71  thf('67', plain,
% 0.45/0.71      (((~ (v3_pre_topc @ (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 0.45/0.71         | ~ (l1_struct_0 @ sk_A)))
% 0.45/0.71         <= (~
% 0.45/0.71             ((v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)))),
% 0.45/0.71      inference('sup-', [status(thm)], ['65', '66'])).
% 0.45/0.71  thf('68', plain, ((l1_struct_0 @ sk_A)),
% 0.45/0.71      inference('sup-', [status(thm)], ['5', '6'])).
% 0.45/0.71  thf('69', plain,
% 0.45/0.71      ((~ (v3_pre_topc @ (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A))
% 0.45/0.71         <= (~
% 0.45/0.71             ((v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)))),
% 0.45/0.71      inference('demod', [status(thm)], ['67', '68'])).
% 0.45/0.71  thf('70', plain,
% 0.45/0.71      (((v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)) | 
% 0.45/0.71       ~ ((v4_pre_topc @ sk_B @ sk_A))),
% 0.45/0.71      inference('sup-', [status(thm)], ['64', '69'])).
% 0.45/0.71  thf('71', plain,
% 0.45/0.71      (((v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)) | 
% 0.45/0.71       ((v4_pre_topc @ sk_B @ sk_A))),
% 0.45/0.71      inference('split', [status(esa)], ['53'])).
% 0.45/0.71  thf('72', plain,
% 0.45/0.71      (![X14 : $i]:
% 0.45/0.71         (((k2_struct_0 @ X14) = (u1_struct_0 @ X14)) | ~ (l1_struct_0 @ X14))),
% 0.45/0.71      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.45/0.71  thf('73', plain,
% 0.45/0.71      (((v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A))
% 0.45/0.71         <= (((v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)))),
% 0.45/0.71      inference('split', [status(esa)], ['53'])).
% 0.45/0.71  thf('74', plain,
% 0.45/0.71      ((((v3_pre_topc @ (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 0.45/0.71         | ~ (l1_struct_0 @ sk_A)))
% 0.45/0.71         <= (((v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)))),
% 0.45/0.71      inference('sup+', [status(thm)], ['72', '73'])).
% 0.45/0.71  thf('75', plain, ((l1_struct_0 @ sk_A)),
% 0.45/0.71      inference('sup-', [status(thm)], ['5', '6'])).
% 0.45/0.71  thf('76', plain,
% 0.45/0.71      (((v3_pre_topc @ (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A))
% 0.45/0.71         <= (((v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)))),
% 0.45/0.71      inference('demod', [status(thm)], ['74', '75'])).
% 0.45/0.71  thf('77', plain,
% 0.45/0.71      (((k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B)
% 0.45/0.71         = (k7_subset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A) @ sk_B))),
% 0.45/0.71      inference('simplify', [status(thm)], ['51'])).
% 0.45/0.71  thf('78', plain,
% 0.45/0.71      (![X14 : $i]:
% 0.45/0.71         (((k2_struct_0 @ X14) = (u1_struct_0 @ X14)) | ~ (l1_struct_0 @ X14))),
% 0.45/0.71      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.45/0.71  thf('79', plain,
% 0.45/0.71      (![X15 : $i, X16 : $i]:
% 0.45/0.71         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.45/0.71          | ~ (v3_pre_topc @ 
% 0.45/0.71               (k7_subset_1 @ (u1_struct_0 @ X16) @ (k2_struct_0 @ X16) @ X15) @ 
% 0.45/0.71               X16)
% 0.45/0.71          | (v4_pre_topc @ X15 @ X16)
% 0.45/0.71          | ~ (l1_pre_topc @ X16))),
% 0.45/0.71      inference('cnf', [status(esa)], [d6_pre_topc])).
% 0.45/0.71  thf('80', plain,
% 0.45/0.71      (![X0 : $i, X1 : $i]:
% 0.45/0.71         (~ (v3_pre_topc @ 
% 0.45/0.71             (k7_subset_1 @ (k2_struct_0 @ X0) @ (k2_struct_0 @ X0) @ X1) @ X0)
% 0.45/0.71          | ~ (l1_struct_0 @ X0)
% 0.45/0.71          | ~ (l1_pre_topc @ X0)
% 0.45/0.71          | (v4_pre_topc @ X1 @ X0)
% 0.45/0.71          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.45/0.71      inference('sup-', [status(thm)], ['78', '79'])).
% 0.45/0.71  thf('81', plain,
% 0.45/0.71      ((~ (v3_pre_topc @ (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 0.45/0.71        | ~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.45/0.71        | (v4_pre_topc @ sk_B @ sk_A)
% 0.45/0.71        | ~ (l1_pre_topc @ sk_A)
% 0.45/0.71        | ~ (l1_struct_0 @ sk_A))),
% 0.45/0.71      inference('sup-', [status(thm)], ['77', '80'])).
% 0.45/0.71  thf('82', plain, (((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))),
% 0.45/0.71      inference('demod', [status(thm)], ['22', '25', '26'])).
% 0.45/0.71  thf('83', plain,
% 0.45/0.71      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))),
% 0.45/0.71      inference('demod', [status(thm)], ['4', '7'])).
% 0.45/0.71  thf('84', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.71  thf('85', plain, ((l1_struct_0 @ sk_A)),
% 0.45/0.71      inference('sup-', [status(thm)], ['5', '6'])).
% 0.45/0.71  thf('86', plain,
% 0.45/0.71      ((~ (v3_pre_topc @ (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 0.45/0.71        | (v4_pre_topc @ sk_B @ sk_A))),
% 0.45/0.71      inference('demod', [status(thm)], ['81', '82', '83', '84', '85'])).
% 0.45/0.71  thf('87', plain,
% 0.45/0.71      (((v4_pre_topc @ sk_B @ sk_A))
% 0.45/0.71         <= (((v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)))),
% 0.45/0.71      inference('sup-', [status(thm)], ['76', '86'])).
% 0.45/0.71  thf('88', plain,
% 0.45/0.71      ((~ (v4_pre_topc @ sk_B @ sk_A)) <= (~ ((v4_pre_topc @ sk_B @ sk_A)))),
% 0.45/0.71      inference('split', [status(esa)], ['0'])).
% 0.45/0.71  thf('89', plain,
% 0.45/0.71      (~ ((v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)) | 
% 0.45/0.71       ((v4_pre_topc @ sk_B @ sk_A))),
% 0.45/0.71      inference('sup-', [status(thm)], ['87', '88'])).
% 0.45/0.71  thf('90', plain, ($false),
% 0.45/0.71      inference('sat_resolution*', [status(thm)], ['1', '70', '71', '89'])).
% 0.45/0.71  
% 0.45/0.71  % SZS output end Refutation
% 0.45/0.71  
% 0.55/0.72  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
